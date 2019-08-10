package main

import "fmt"
import "sort"
import "strings"
import "io/ioutil"
import "github.com/golang-collections/go-datastructures/queue"

type Automata interface {
	GetStart() string
	SetStart(string)
	GetFinish() Set
	TransTable() [][]string
}

type State interface {
}

type Set map[string]byte

func NewSet() Set {
	var s Set
	s = make(Set)
	return s
}

func (s Set) Has(v string) bool {
	_, ok := s[v]
	return ok
}

func (s Set) Insert(v string) {
	_, ok := s[v]
	if !ok {
		s[v] = 0
	}
}

type DFA struct {
	States  map[string]*DFAstate
	Start   string
	Finish  Set
	Symbols map[string]interface{} // as set
}

func NewDFA() *DFA {
	var dfa DFA
	dfa.States = make(map[string]*DFAstate)
	dfa.Finish = NewSet()
	dfa.Symbols = make(map[string]interface{})
	return &dfa
}

func (dfa *DFA) GetStart() string {
	return dfa.Start
}

func (dfa *DFA) SetStart(s string) {
	dfa.Start = s
}

func (dfa *DFA) GetFinish() Set {
	return dfa.Finish
}

type DFAstate struct {
	Id    string
	Attr  map[string]string
	Trans map[string]string // return the id of state
}

func NewDFAstate() *DFAstate {
	var s DFAstate
	s.Trans = make(map[string]string)
	s.Attr = make(map[string]string)
	return &s
}

func (dfa *DFA) Trans(fromstate string, symbols []string) string {
	if len(symbols) == 0 {
		return fromstate
	}

	state, ok := dfa.States[fromstate].Trans[symbols[0]]
	if !ok {
		return ""
	}

	return dfa.Trans(state, symbols[1:])
}

func (dfa *DFA) TransTable() [][]string { // from_state symbol to_state Startstate or Finstate?
	var transtable [][]string

	for state, state_obj := range dfa.States {
		for sb, dst := range state_obj.Trans {
			transtable = append(transtable, []string{state, sb, dst})
		}
	}
	return transtable
}

type NFAstate struct {
	Id    string
	Attr  map[string]string
	Trans map[string]Set
}

func NewNFAstate() *NFAstate {
	var s NFAstate
	s.Trans = make(map[string]Set)
	s.Attr = make(map[string]string)
	return &s
}

type NFA struct {
	States  map[string]*NFAstate
	Start   string
	Finish  Set
	Symbols map[string]interface{}
}

func NewNFA() *NFA {
	var nfa NFA
	nfa.States = make(map[string]*NFAstate)
	nfa.Finish = NewSet()
	nfa.Symbols = make(map[string]interface{})
	return &nfa
}

func (nfa *NFA) GetStart() string {
	return nfa.Start
}

func (nfa *NFA) SetStart(s string) {
	nfa.Start = s
}

func (nfa *NFA) GetFinish() Set {
	return nfa.Finish
}

func (nfa *NFA) Trans(fromstate string, symbols []string) Set {
	if len(symbols) == 0 {
		s := NewSet()
		s.Insert(fromstate)
		return s
	}

	states, ok := nfa.States[fromstate].Trans[symbols[0]] // no way to go && also fine if fromstate is empty
	if !ok {
		return NewSet()
	}
	return nfa.TransFromStates(states, symbols[1:])

}

func (nfa *NFA) TransFromStates(fromstates Set, symbols []string) Set {
	if len(symbols) == 0 {
		return fromstates
	}
	if len(fromstates) == 0 {
		return NewSet() // empty set
	}
	next_states := NewSet()
	for state, _ := range fromstates {
		dst_states, ok := nfa.States[state].Trans[symbols[0]]
		if !ok {
			continue
		}
		for dst_state, _ := range dst_states {
			next_states.Insert(dst_state)
		}
	}
	return nfa.TransFromStates(next_states, symbols[1:])
}

func (nfa *NFA) TransTable() [][]string { // from_state symbol to_state Startstate or Finstate?
	var transtable [][]string

	for state, state_obj := range nfa.States {
		for sb, dsts := range state_obj.Trans {
			for dst, _ := range dsts {
				transtable = append(transtable, []string{state, sb, dst})
			}
		}
	}
	return transtable
}

func Print(at Automata) {
	s := Serialize(at)
	fmt.Print(s)
}

func Serialize(at Automata) string {
	var sb strings.Builder
	fmt.Fprintf(&sb, "%s\n", at.GetStart())

	var tmp []string
	for fs, _ := range at.GetFinish() {
		tmp = append(tmp, fs)
	}
	fmt.Fprintf(&sb, "%s\n", strings.Join(tmp, " "))
	trans_table := at.TransTable()
	for _, record := range trans_table {
		fmt.Fprintf(&sb, "%s\n", strings.Join(record, " "))
	}
	return sb.String()

}

func Desearialize(s string, at Automata, insert func(string, string, string, Automata)) {
	s = strings.Trim(s, "\n")
	lines := strings.Split(s, "\n")
	if len(lines) <= 2 {
		panic("bad automata format")
	}
	at.SetStart(lines[0])
	for _, s := range strings.Split(lines[1], " ") {
		at.GetFinish().Insert(s)
	}
	for _, s := range lines[2:] {

		l := strings.Split(s, " ")
		from, symbol, to := l[0], l[1], l[2]
		insert(from, symbol, to, at)
	}

}

func DFADeserialize(s string) *DFA {

	insert := func(from string, symbol string, to string, at Automata) {
		dfa := at.(*DFA)
		_, ok := dfa.States[from]
		if !ok {
			dfa.States[from] = NewDFAstate()
			dfa.States[from].Id = from
		}
		state_obj := dfa.States[from]
		state_obj.Trans[symbol] = to

	}
	dfa := NewDFA()
	Desearialize(s, dfa, insert)
	return dfa
}

func NFADeserialize(s string) *NFA {

	insert := func(from string, symbol string, to string, at Automata) {
		nfa := at.(*NFA)
		_, ok := nfa.States[from]
		if !ok {
			nfa.States[from] = NewNFAstate()
			nfa.States[from].Id = from
		}
		_, ok = nfa.States[to]
		if !ok { // state may only apper in dst part
			nfa.States[to] = NewNFAstate()
			nfa.States[to].Id = to
		}
		state_obj := nfa.States[from]
		trans := state_obj.Trans
		_, ok = trans[symbol]
		if !ok {
			tmp := NewSet()
			tmp.Insert(to)
			trans[symbol] = tmp
		} else {
			trans[symbol].Insert(to)
		}
	}
	nfa := NewNFA()
	Desearialize(s, nfa, insert)
	return nfa

}

func Accept(at Automata, symbols []string) bool {
	stop_states := NewSet()
	start := at.GetStart()
	finish := at.GetFinish()
	switch a := at.(type) {
	case *DFA:
		s := a.Trans(start, symbols)
		stop_states.Insert(s)
	case *NFA:
		stop_states = a.Trans(start, symbols)
	default:
		panic("Unknown automata type")
	}
	if len(stop_states) == 0 {
		return false //can not consume all symbols
	}
	fmt.Println(stop_states)
	for stop_state, _ := range stop_states {
		if finish.Has(stop_state) {
			return true
		}
	}
	return false
}

func (nfa *NFA) ToDFA() *DFA {

	StatesToString := func(states Set) string {
		var state_list []string
		for s, _ := range states {
			state_list = append(state_list, s)
		}
		sort.Strings(state_list)
		return strings.Join(state_list, ",")
	}

	DFAStates := NewSet()
	var DFATrans map[string]map[string]Set
	DFATrans = make(map[string]map[string]Set) //trans[states][symbols] -> statesSet
	DFAStart := nfa.Start
	DFAFinish := NewSet()

	q := queue.New(10)
	DFA_start_state := NewSet()
	DFA_start_state.Insert(nfa.Start)
	DFAStates.Insert(nfa.Start)
	q.Put(DFA_start_state)
	for !q.Empty() {
		_states, _ := q.Get(1) //get a dfa states
		states := _states[0].(Set)
		states_str := StatesToString(states)

		DFATrans[states_str] = make(map[string]Set)
		trans_for_the_state := DFATrans[states_str]
		for state, _ := range states {
			trans := nfa.States[state].Trans
			for sb, dsts := range trans {
				_, ok := trans_for_the_state[sb]
				if !ok {
					trans_for_the_state[sb] = NewSet()
				}
				for dst, _ := range dsts {
					trans_for_the_state[sb].Insert(dst)
				}
			}
		}
		for _, states := range trans_for_the_state {
			states_str := StatesToString(states)
			if !DFAStates.Has(states_str) { //if never seen, put into the queue
				q.Put(states)
				DFAStates.Insert(states_str)
				// check whether is a finish state
				for s, _ := range nfa.Finish {
					if states.Has(s) {
						DFAFinish.Insert(states_str)
					}
				}
			}
		}
	}

	dfa := NewDFA()
	for state, _ := range DFAStates {
		s := NewDFAstate()
		s.Id = state
		dfa.States[state] = s
	}
	for state_str, trans := range DFATrans {
		s := dfa.States[state_str]
		for sb, dsts := range trans {
			dst_state := StatesToString(dsts)
			s.Trans[sb] = dst_state
		}
	}
	dfa.Start = DFAStart
	dfa.Finish = DFAFinish
	return dfa
}

func main() {
	dat, err := ioutil.ReadFile("./nfa.txt")

	if err != nil {
		panic(err)
	}
	nfa := NFADeserialize(string(dat))
	dfa := nfa.ToDFA()
	s := Serialize(dfa)
	fmt.Println(s)

	// test_str := "1111010"
	// sb_list := make([]string, 0, 5)
	// for _, char := range test_str {
	// 	sb_list = append(sb_list, string(char))
	// }
	//
	// fmt.Println(Accept(dfa, sb_list))

}

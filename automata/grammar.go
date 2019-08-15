package automata

import "strings"
import "fmt"
import "github.com/golang-collections/go-datastructures/queue"

type Symbol interface {
	Printsymbol() string
}

type Terminal struct {
	value string
}

func (t *Terminal) Printsymbol() string {
	return t.value
}

type Variable struct {
	Id          string
	Productions [][]Symbol // one production is a list of symbol
}

func (v *Variable) Printsymbol() string {
	return v.Id
}

type CFG struct {
	Variable map[string]*Variable
	Start    string
}

func NewCFG() *CFG {
	var cfg CFG
	cfg.Variable = make(map[string]*Variable)
	return &cfg
}

func NewVariable(id string) *Variable {
	var v Variable
	v.Id = id
	return &v
}

func NewTerminal(s string) *Terminal {
	return &Terminal{value: s}
}

func (cfg *CFG) Print() {
	fmt.Println(CFGSerialize(cfg))
}

func CFGSerialize(cfg *CFG) string { //print by BFS order
	s := NewSet()
	q := queue.New(10)
	s.Insert(cfg.Start)
	q.Put(cfg.Start)
	var vars []string

	for !q.Empty() {
		_v, _ := q.Get(1)
		v := _v[0].(string)
		vars = append(vars, v)

		for _, prod := range cfg.Variable[v].Productions {
			tmp_str := []string{v, "->"} //each production is a line
			for _, symbol := range prod {
				var_str := symbol.Printsymbol()
				switch symbol.(type) {
				case *Variable:
					if !s.Has(var_str) { //visited
						s.Insert(var_str)
						q.Put(var_str)
					}
				case *Terminal: //terminal is like "term"
					var_str = "\"" + var_str + "\""
				}
				tmp_str = append(tmp_str, var_str)
			}
			vars = append(vars, strings.Join(tmp_str, " "))
		}
	}
	return strings.Join(vars, "\n")
}

func CFGDeserialize(s string) *CFG {
	cfg := NewCFG()
	splits := strings.Split(strings.Trim(s, "\n"), "\n")
	if len(splits) == 0 {
		return cfg
	}

	getstart := true
	for _, line := range splits { //create variables
		var_str := strings.Split(strings.Trim(line, " "), " ")[0]
		if getstart { //just get start symbol. The fist line
			getstart = !getstart
			cfg.Start = var_str
		}
		cfg.Variable[var_str] = NewVariable(var_str)
	}

	for _, line := range splits { //add production
		var product []Symbol
		sb_list := strings.Split(strings.Trim(line, " "), " ")
		if len(sb_list) < 3 { //V->A len=3
			panic("bad product: " + line)
		}

		v := cfg.Variable[sb_list[0]]
		for i := 2; i < len(sb_list); i++ {
			stripped := strings.Trim(sb_list[i], "\"")
			if stripped == sb_list[i] { //is var
				product = append(product, cfg.Variable[stripped])
			} else {
				product = append(product, NewTerminal(stripped))
			}
		}
		v.Productions = append(v.Productions, product)
	}
	return cfg

}

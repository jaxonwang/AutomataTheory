package automata

import "strings"
import "fmt"
import "strconv"
import "github.com/golang-collections/go-datastructures/queue"

type Symbol interface {
	Printsymbol() string
}

type Terminal struct {
	Value string
}

func (t *Terminal) Printsymbol() string {
	return t.Value
}

type Variable struct {
	Id          string
	Productions [][]Symbol // one production is a list of symbol
}

func (v *Variable) Printsymbol() string {
	return v.Id
}

type CFG struct {
	Variables map[string]*Variable
	Start     string
}

func NewCFG() *CFG {
	var cfg CFG
	cfg.Variables = make(map[string]*Variable)
	return &cfg
}

func NewVariable(id string) *Variable {
	var v Variable
	v.Id = id
	return &v
}

func NewTerminal(s string) *Terminal {
	return &Terminal{Value: s}
}

func (cfg *CFG) Print() { //print everything
	for var_str, v := range cfg.Variables {
		if len(v.Productions) == 0 {
			fmt.Printf("%s ->\n", var_str) //also print empty production
			continue
		}
		for _, product := range v.Productions {
			fmt.Printf("%s ->", var_str)
			for _, sb := range product {
				switch sb.(type) {
				case *Variable:
					fmt.Printf(" %s", sb.Printsymbol())
				case *Terminal:
					fmt.Printf(" \"%s\"", sb.Printsymbol())
				}
			}
			fmt.Println()
		}
	}
	fmt.Println("****************")
}

func (cfg *CFG) Initvarsfrom(fromcfg *CFG) {
	create_var := func(var_str string) {
		_, ok := cfg.Variables[var_str]
		if !ok {
			cfg.Variables[var_str] = NewVariable(var_str)
		}
	}
	for var_str, v := range fromcfg.Variables {
		create_var(var_str)
		for _, product := range v.Productions {
			for _, symbol := range product {
				switch sb := symbol.(type) {
				case *Variable:
					create_var(sb.Id)
				}
			}
		}
	}
}

func EliminateUnreachable(cfg *CFG) *CFG {
	return CFGDeserialize(CFGSerialize(cfg))
}

func EliminateNongenerating(cfg *CFG) *CFG {
	generating := NewSet()

	direct_gen := func(product []Symbol) bool {
		if len(product) == 0 {
			return false
		}
		for _, sb := range product {
			_, ok := sb.(*Terminal)
			if !ok {
				return false
			}
		}
		return true
	}

	Inferfromdecendent(cfg, generating, direct_gen)

	product_is_gen := func(symbols []Symbol) bool {
		for _, symbol := range symbols {
			switch sb := symbol.(type) {
			case *Variable: //only check the variable
				if !generating.Has(sb.Id) {
					return false
				}
			}
		}
		return true
	}

	newcfg := NewCFG()
	for var_str, v := range cfg.Variables {
		if !generating.Has(var_str) {
			continue
		}
		newcfg.Variables[var_str] = NewVariable(var_str)
		for _, product := range v.Productions {
			tmp_v := newcfg.Variables[var_str]
			if product_is_gen(product) {
				tmp_v.Productions = append(tmp_v.Productions, product)
			}
		}
	}
	if generating.Has(cfg.Start) {
		newcfg.Start = cfg.Start
	}

	return newcfg

}

func EliminateUseless(cfg *CFG) *CFG {
	return EliminateUnreachable(EliminateNongenerating(cfg))
}

func Inferfromdecendent(cfg *CFG, traitset Set, direct_production func([]Symbol) bool) {
	// trait set: the set each element has certian trait
	// direct_production: the func to determin if a production has the trait
	appearing_list := make(map[string][]([2]interface{}))
	counts := make(map[string][]int) // counts[var_str][product_index] = number

	q := queue.New(5)
	for var_str, v := range cfg.Variables { //init counts and appearing_list
		counts[var_str] = make([]int, len(v.Productions))
		once := true //only put once
		for i, product := range v.Productions {
			counts[var_str][i] = 0 //init counts
			for _, sb := range product {
				sb_v, ok := sb.(*Variable)
				if ok {
					counts[var_str][i]++
					appearing_list[sb_v.Id] = append(appearing_list[sb_v.Id], [2]interface{}{var_str, i})
				}
			}
			if once && direct_production(product) {
				q.Put(var_str) //add to queue if the product is gen
				traitset.Insert(var_str)
				once = false
			}
		}
	}

	//time to count
	for !q.Empty() {
		_v, _ := q.Get(1)
		var_str := _v[0].(string)
		for _, appear := range appearing_list[var_str] {
			v_appear := appear[0].(string)
			counts_for_appear := counts[v_appear]
			p_index := appear[1].(int)
			counts_for_appear[p_index]--
			if counts_for_appear[p_index] == 0 && !traitset.Has(v_appear) {
				q.Put(v_appear)
				traitset.Insert(v_appear)
			} else if counts_for_appear[p_index] < 0 {
				panic("Count can not be small than 0")
			}
		}
	}
}

func EliminateEpsilon(cfg *CFG) *CFG { //doesnt ensure all is generating and nullable

	nullable := NewSet()

	//clean eplison in product like P -> "epsilon" A
	tmp_cfg := NewCFG() //
	tmp_cfg.Start = cfg.Start
	tmp_cfg.Initvarsfrom(cfg)
	for var_str, v := range cfg.Variables {
		for _, product := range v.Productions {
			var p []Symbol
			for _, sb := range product {
				t, ok := sb.(*Terminal)
				if ok && t.Value == epsilon {
					continue
				}
				p = append(p, sb)
			}
			if len(p) == 0 { // P -> "epsilon" "epsilon" shoule become "epsilon"
				p = append(p, &Terminal{epsilon})
			}
			tmp_cfg.Variables[var_str].Productions = append(tmp_cfg.Variables[var_str].Productions, p)
		}
	}
	cfg = tmp_cfg //no change to the origin

	direct_null := func(product []Symbol) bool {
		if len(product) == 0 {
			return false
		}
		for _, sb := range product { // all term is epsilon
			t, ok := sb.(*Terminal)
			if !(ok && t.Value == epsilon) { //not epsilon
				return false
			}
		}
		return true
	}
	Inferfromdecendent(cfg, nullable, direct_null)

	// time to eliminate

	gen_expo := func(nullablelist []bool) [][]bool {
		expo_list := [][]bool{}
		if len(nullablelist) == 0 {
			return expo_list
		}
		if len(nullablelist) == 1 && nullablelist[0] == true { // A->epsilon
			return expo_list
		}
		expo_list = append(expo_list, []bool{})
		for i := 0; i < len(nullablelist); i++ {
			if nullablelist[i] == false {
				for j := 0; j < len(expo_list); j++ {
					expo_list[j] = append(expo_list[j], false) //extend 1 bit by false
				}
			} else {
				length := len(expo_list) //fix length
				for j := 0; j < length; j++ {
					new_l := make([]bool, i+1)
					copy(new_l, expo_list[j])
					new_l[i] = true
					expo_list[j] = append(expo_list[j], false) //extend 1 bit by false
					if i == len(nullablelist)-1 {              //can not be all true
						all_true := true //if only A->epsilon then also work
						for k := 0; k < i; k++ {
							if expo_list[j][k] == false {
								all_true = false
								break
							}
						}
						if all_true {
							continue //no append
						}
					}
					expo_list = append(expo_list, new_l)
				}
			}
		}
		return expo_list //return list whose list containselements indicating it should be absent
	}

	eliminate_for_production := func(symbols []Symbol) [][]Symbol {
		nullablelist := make([]bool, len(symbols))
		for i, symbol := range symbols {
			switch sb := symbol.(type) {
			case *Terminal:
				if sb.Value == epsilon {
					nullablelist[i] = true
				}
			case *Variable:
				if nullable.Has(sb.Id) {
					nullablelist[i] = true
				}
			}
		}
		gen_list := gen_expo(nullablelist)
		var expo_sb_list [][]Symbol
		for _, l := range gen_list {
			var sb_list []Symbol
			for i, absent := range l {
				if !absent {
					sb_list = append(sb_list, symbols[i])
				}
			}
			expo_sb_list = append(expo_sb_list, sb_list)
		}
		return expo_sb_list
	}

	newcfg := NewCFG()
	newcfg.Start = cfg.Start
	newcfg.Initvarsfrom(cfg)

	for var_str, v := range cfg.Variables {
		newcfg_var := newcfg.Variables[var_str]
		for _, production := range v.Productions {
			expo_list := eliminate_for_production(production)
			newcfg_var.Productions = append(newcfg_var.Productions, expo_list...)
		}
	}
	if nullable.Has(cfg.Start) { // start nullable them append S -> "epsilon"
		v := newcfg.Variables[newcfg.Start]
		v.Productions = append(v.Productions, []Symbol{&Terminal{Value: epsilon}})
	}
	return newcfg

}

func EliminateUnitPair(cfg *CFG) *CFG {
	var unitpairs struct {
		pairs         map[string]Set
		inverse_pairs map[string]Set
	}
	var nonunitproduct map[string][][]Symbol

	unitpairs.pairs = make(map[string]Set)
	unitpairs.inverse_pairs = make(map[string]Set)
	nonunitproduct = make(map[string][][]Symbol)

	get_dst := func(src string) Set {
		return unitpairs.pairs[src]
	}
	get_src := func(dst string) Set {
		return unitpairs.inverse_pairs[dst]
	}
	new_pair := func(src string, dst string) {
		_, ok1 := unitpairs.pairs[src]
		_, ok2 := unitpairs.inverse_pairs[dst]
		if !ok1 {
			unitpairs.pairs[src] = NewSet()
		}
		if !ok2 {
			unitpairs.inverse_pairs[dst] = NewSet()
		}
		unitpairs.pairs[src].Insert(dst)
		unitpairs.inverse_pairs[dst].Insert(src)
	}

	for var_str, _ := range cfg.Variables {
		new_pair(var_str, var_str)
	}

	for var_str, v := range cfg.Variables { //find unit pairs
		for _, product := range v.Productions {
			dst, ok := product[0].(*Variable) //must be var
			if len(product) == 1 && ok {
				new_pair(var_str, dst.Id)
			} else if len(product) == 0 {
				panic("zero length production!")
			} else {
				_, ok := nonunitproduct[var_str]
				if !ok {
					nonunitproduct[var_str] = [][]Symbol{product}
				} else {
					nonunitproduct[var_str] = append(nonunitproduct[var_str], product)
				}
			}
		}
	}
	// warshall algorithm find the closure O(V^3) time
	for var_str, _ := range cfg.Variables {
		srcs := get_src(var_str)
		dsts := get_dst(var_str)
		for src, _ := range srcs {
			for dst, _ := range dsts {
				new_pair(src, dst)
			}
		}
	}
	newcfg := NewCFG()
	newcfg.Initvarsfrom(cfg)
	newcfg.Start = cfg.Start

	for var_str, v := range newcfg.Variables {
		dsts := get_dst(var_str)
		for dst, _ := range dsts {
			prdcts, ok := nonunitproduct[dst]
			if !ok {
				continue
			}
			for _, product := range prdcts {
				v.Productions = append(v.Productions, product)
			}
		}
	}
	return newcfg
}

func ToNormalForm(cfg *CFG) *CFG {

	newcfg := NewCFG()
	newcfg.Initvarsfrom(cfg)
	newcfg.Start = cfg.Start

	count := 0
	NewVar := func() *Variable {
		count++
		return NewVariable("V" + strconv.Itoa(count)) //possible conflict, let's assume it won't
	}

	for var_str, v := range cfg.Variables {
		for _, product := range v.Productions {
			cur_var := newcfg.Variables[var_str]
			i := 0
			for ; i < len(product)-2; i++ { //break when len <=2
				newvar := NewVar()
				newcfg.Variables[newvar.Id] = newvar
				cur_var.Productions = append(cur_var.Productions, []Symbol{product[i], newvar})
				cur_var = newvar
			}
			p := make([]Symbol, len(product)-i)
			copy(p, product[i:])
			cur_var.Productions = append(cur_var.Productions, p)
		}
	}
	newcfg = EliminateEpsilon(newcfg)
	newcfg = EliminateUnitPair(newcfg)
	newcfg = EliminateUseless(newcfg)
	return newcfg
}

func (cfg *CFG) OrderProductions(var_str string) {
	productions := cfg.Variables[var_str].Productions

	swap := func(i, j int) {
		tmp := productions[j]
		productions[j] = productions[i]
		productions[i] = tmp
	}
	isless := func(i, j int) bool { //just total order
		a := productions[i]
		b := productions[j]
		if len(a) > len(b) {
			return true
		}
		if len(a) < len(b) {
			return false
		}
		for k := 0; k < len(a); k++ {
			if a[k].Printsymbol() < b[k].Printsymbol() {
				return true
			} else {
				return false
			}
		}
		return false
	}
	for i := 0; i < len(productions); i++ { //bubble sort
		for j := i; j >= 1; j-- {
			if isless(j, j-1) {
				swap(j, j-1)
			} else {
				break
			}
		}

	}
}

func CFGSerialize(cfg *CFG) string { //print by BFS order, remove unreachable
	if len(cfg.Variables) == 0 {
		return ""
	}
	s := NewSet()
	q := queue.New(10)
	s.Insert(cfg.Start)
	q.Put(cfg.Start)
	for var_str, _ := range cfg.Variables {
		cfg.OrderProductions(var_str) //order to make stable
	}
	var vars []string

	for !q.Empty() {
		_v, _ := q.Get(1)
		v := _v[0].(string)

		for _, prod := range cfg.Variables[v].Productions {
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

	get_variable := func(sb_list []string) []string {
		var var_strs []string
		for _, str := range sb_list {
			switch str {
			case "->":
				continue
			case strings.Trim(str, "\""): // is var
				var_strs = append(var_strs, str)
			}
		}
		return var_strs
	}

	getstart := true
	for _, line := range splits { //create variables
		var_strs := strings.Split(strings.Trim(line, " "), " ")
		if getstart { //just get start symbol. The fist line
			getstart = !getstart
			cfg.Start = var_strs[0]
		}

		s := NewSet()                                    // mark visited
		for _, var_str := range get_variable(var_strs) { // generate all var visited
			if s.Has(var_str) {
				continue
			}
			cfg.Variables[var_str] = NewVariable(var_str) // vars in production
			s.Insert(var_str)
		}

	}

	for _, line := range splits { //add production
		var product []Symbol
		sb_list := strings.Split(strings.Trim(line, " "), " ")
		if len(sb_list) < 3 { //V->A len=3
			panic("bad product: " + line)
		}

		v := cfg.Variables[sb_list[0]]
		for i := 2; i < len(sb_list); i++ {
			stripped := strings.Trim(sb_list[i], "\"")
			if stripped == sb_list[i] { //is var
				product = append(product, cfg.Variables[stripped])
			} else {
				product = append(product, NewTerminal(stripped))
			}
		}
		v.Productions = append(v.Productions, product)
	}
	return cfg

}

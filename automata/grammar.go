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
	return &Terminal{value: s}
}

func (cfg *CFG) Print() {
	fmt.Println(CFGSerialize(cfg))
}

func EliminateUnreachable(cfg *CFG) *CFG {
	return CFGDeserialize(CFGSerialize(cfg))
}

func EliminateNongenerating(cfg *CFG) *CFG {
	non_generating := NewSet()
	generating := NewSet()
	visited := NewSet()
	var mark_non_generating func(string)
	mark_non_generating = func(var_str string) {
		//basis case
		if generating.Has(var_str) || non_generating.Has(var_str) {
			return //marked
		}
		all_products_non_gen := true

		for _, product := range cfg.Variables[var_str].Productions {
			the_product_is_gen := true
			//derect non gen is like A -> emptyset, won't go inside the loop
			for _, symbol := range product {
				switch sb := symbol.(type) {
				case *Variable: //only check the variable
					mark_non_generating(sb.Id)
					if non_generating.Has(sb.Id) { //any var is non gen, then product is non gen
						the_product_is_gen = false
						break
					}
				}
			}
			if the_product_is_gen { //is gengeratin. done
				all_products_non_gen = false
				break
			}
		}
		if all_products_non_gen {
			non_generating.Insert(var_str)
		} else {
			generating.Insert(var_str)
		}
	}

	product_is_gen := func(symbols []Symbol) bool {
		for _, symbol := range symbols {
			switch sb := symbol.(type) {
			case *Variable: //only check the variable
				if non_generating.Has(sb.Id) {
					return false
				}
			}
		}
		return true
	}

	for var_str, _ := range cfg.Variables {
		if visited.Has(var_str) {
			continue
		}
		mark_non_generating(var_str)
	}

	newcfg := NewCFG()
	for var_str, v := range cfg.Variables {
		if non_generating.Has(var_str) {
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

func CFGSerialize(cfg *CFG) string { //print by BFS order
	if len(cfg.Variables) == 0 {
		return ""
	}
	s := NewSet()
	q := queue.New(10)
	s.Insert(cfg.Start)
	q.Put(cfg.Start)
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

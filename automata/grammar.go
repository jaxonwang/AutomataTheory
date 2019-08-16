package automata

import "strings"
import "fmt"
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

func (cfg *CFG) Print() {
	fmt.Println(CFGSerialize(cfg))
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

func EliminateEpsilon(cfg *CFG) *CFG { //doesnt ensure all is generating and nullable

	nullable := NewSet()
	nonnullable := NewSet()

	var mark_nullable func(string)
	mark_nullable = func(var_str string) {
		if nullable.Has(var_str) || nonnullable.Has(var_str) {
			return
		}
		var var_nullable = false

		for _, product := range cfg.Variables[var_str].Productions {
			production_nullable := true
			for _, symbol := range product {
				switch sb := symbol.(type) {
				case *Terminal:
					{
						if sb.Value != epsilon { //non nullable
							production_nullable = false // any sb non nullable, then production nonnullable
							break
						}
					}
				case *Variable:
					mark_nullable(sb.Id)
					if nonnullable.Has(sb.Id) {
						production_nullable = false
						break
					}
				}
			}
			if production_nullable { //any production nullable, the varialbe nuallble
				var_nullable = true
				break
			}
		}
		if var_nullable {
			nullable.Insert(var_str)
		} else {
			nonnullable.Insert(var_str)
		}
	}
	for var_str, _ := range cfg.Variables {
		mark_nullable(var_str)
	}

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

func CFGSerialize(cfg *CFG) string { //print by BFS order
	if len(cfg.Variables) == 0 {
		return ""
	}
	s := NewSet()
	q := queue.New(10)
	s.Insert(cfg.Start)
	q.Put(cfg.Start)
	cfg.OrderProductions(cfg.Start) //order the start and everything ordered
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

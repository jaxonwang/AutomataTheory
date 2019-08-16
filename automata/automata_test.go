package automata

import "testing"
import "io/ioutil"
import "strings"
import "sort"

// import "fmt"

func Makelist(s string) []string {
	sb_list := make([]string, 0, 5)
	for _, char := range s {
		sb_list = append(sb_list, string(char))
	}
	return sb_list
}

var decimial_cases = []struct {
	in   string
	want bool
}{
	{"1111010", false},
	{"1.111010", true},
	{"+1.111010", true},
	{"-1.111010", true},
	{"1111.010", true},
	{".1111010", true},
	{"123455.1111010", true},
	{"+123455.1111010", true},
	{"-123455.1111010", true},
	{"a123455.1111010", false},
	{"12.3455.1111010", false},
	{"12.345519999999999111010", true},
	{"a12.345519999999999111010", false},
	{"12.3ff45519999999999111010", false},
}

func TestENFA(t *testing.T) {
	dat_path := "../resources/decimal.enfa"
	dat, err := ioutil.ReadFile(dat_path)

	if err != nil {
		t.Errorf("Can not find %s", dat_path)
	}

	enfa := eNFADeserialize(string(dat))
	for _, c := range decimial_cases {
		if Accept(enfa, Makelist(c.in)) != c.want {
			t.Errorf("test for %s, expect %t", c.in, c.want)
		}
	}
}

func TestENFAtoDFA(t *testing.T) {
	dat_path := "../resources/decimal.enfa"
	dat, _ := ioutil.ReadFile(dat_path)
	enfa := eNFADeserialize(string(dat))
	dfa := ToDFA(enfa)
	for _, c := range decimial_cases {
		if Accept(dfa, Makelist(c.in)) != c.want {
			t.Errorf("test for %s, expect %t", c.in, c.want)
		}
	}
}

func TestNFA(t *testing.T) {
	dat_path := "../resources/01stringendwith01.nfa"
	dat, err := ioutil.ReadFile(dat_path)
	if err != nil {
		t.Errorf("Can not find %s", dat_path)
	}
	cases := []struct {
		in   string
		want bool
	}{
		{"0", false},
		{"1", false},
		{"", false},
		{"1111010", false},
		{"11110101", true},
		{"111101", true},
		{"00000001", true},
		{"00000010", false},
		{"11111111101010100101001010100000010", false},
		{"111111111010101001010010101000000101", true},
		{"ab01", false},
		{"01a", false},
	}
	nfa := NFADeserialize(string(dat))
	for _, c := range cases {
		if Accept(nfa, Makelist(c.in)) != c.want {
			t.Errorf("test for %s, expect %t", c.in, c.want)
		}
	}
}

func SortLines(s string) []string {
	s = strings.Trim(s, "\n\t ")
	l := strings.Split(s, "\n")
	sort.Strings(l)
	return l
}

func CompareStrings(str1 string, str2 string, t *testing.T) {
	s1 := SortLines(str1)
	s2 := SortLines(str2)
	if len(s1) != len(s2) {
		t.Errorf("Unmatched length %d, %d", len(s1), len(s2))
	}
	for i := 0; i < len(s1); i++ {
		if s1[i] != s2[i] {
			t.Errorf("Unmatched at line %d: %s-->%s", i, s1[i], s2[i])
		}
	}
}

func TestNFASerialize(t *testing.T) {
	dat_path := "../resources/decimal.enfa"
	dat, _ := ioutil.ReadFile(dat_path)
	nfa := NFADeserialize(string(dat))
	s := Serialize(nfa)
	CompareStrings(string(dat), s, t)

}

func DFAequal(dfa1 *DFA, dfa2 *DFA, t *testing.T) {
	if dfa1.Start != dfa2.Start {
		t.Errorf("Unmatched start state: %s-->%s", dfa1.Start, dfa2.Start)
	}
	if !IsSetEqual(dfa1.Finish, dfa2.Finish) {
		t.Errorf("Unmatched finish state: %s-->%s", dfa1.Finish.String(), dfa2.Finish.String())
	}
	for s, _ := range dfa1.States {
		_, ok := dfa2.States[s]
		if !ok {
			t.Errorf("Unmatched state: %s", s)
		}
	}
	for s, _ := range dfa2.States {
		_, ok := dfa1.States[s]
		if !ok {
			t.Errorf("Unmatched state: %s", s)
		}
		for sb, dst1 := range dfa1.States[s].Trans {
			dst2, ok := dfa2.States[s].Trans[sb]
			if !ok {
				t.Errorf("Symbol %s not in the other for state %s", sb, s)
			}
			if dst2 != dst1 {
				t.Errorf("Distination state unmatched: %s, %s for symbol %s, state:%s", dst1, dst2, sb, s)
			}

		}
	}

}

func TestTONFAandDFASerialize(t *testing.T) {
	//also test DFADeserialize and Serialize
	dat_path := "../resources/exponentialdfa.nfa"
	dat, err := ioutil.ReadFile(dat_path)
	if err != nil {
		t.Errorf("Can not find %s", dat_path)
	}
	nfa := NFADeserialize(string(dat))
	dfa := ToDFA(nfa)
	s1 := Serialize(dfa)
	dfa1 := DFADeserialize(s1)
	DFAequal(dfa, dfa1, t)
}

const palindrome = `S -> "epsilon"
S -> "0"
S -> "1"
S -> "0" S "0"
S -> "1" S "1"`

const expression = `E -> I
E -> E "+" E
E -> E "*" E
E -> "(" E ")"
I -> "a"
I -> "b"
I -> I "a"
I -> I "b"
I -> I "0"
I -> I "1"
`

func TestCFGDeserialize(t *testing.T) {

	test_func := func(testcase string) {
		cfg := CFGDeserialize(testcase)
		str1 := CFGSerialize(cfg)
		cfg1 := CFGDeserialize(str1)
		str2 := CFGSerialize(cfg1)
		if str1 != str2 {
			t.Errorf("serialized unmatch %s\n\n%s\n", str1, str2)
		}
	}
	test_func(palindrome)
	test_func(expression)

}

func TestEliminateUnreachable(t *testing.T) {

	const unreachable = `A -> B D
B -> C
B -> D E
F -> K B
K -> I
F -> "a"
E -> J
`

	const reachable = `A -> B D
B -> C
B -> D E
E -> J
`

	cfg := CFGDeserialize(unreachable)
	cfg = EliminateUnreachable(cfg)
	str1 := CFGSerialize(cfg)
	str2 := CFGSerialize(CFGDeserialize(reachable))
	if str1 != str2 {
		t.Errorf("serialized unmatch %s\n\n%s\n", str1, str2)
	}
}

func TestEliminateNongenerating(t *testing.T) {
	const gen = `A -> B C D E
A -> B D E
B -> G "a" H
G -> "b"
H -> "c"
B -> H K
B -> HH FJ KL
C -> Q W R
Q -> "f"
W -> "w"
D -> I
D -> O
D -> P
I -> "i"
O -> "o"
P -> "p"
E -> B
JJ -> E
KK -> JJ
B -> KK
`
	const target = `A -> B D E
B -> G "a" H
B -> KK
D -> I
D -> O
D -> P
E -> B
G -> "b"
H -> "c"
KK -> JJ
I -> "i"
O -> "o"
P -> "p"
JJ -> E`
	cfg := CFGDeserialize(gen)
	cfg = EliminateNongenerating(cfg)
	str1 := CFGSerialize(cfg)
	str2 := CFGSerialize(CFGDeserialize(target))
	if str1 != str2 {
		t.Errorf("serialized unmatch %s\n\n%s\n", str1, str2)
	}
}

func TestEliminateUseless(t *testing.T) {
	const test = `S -> A B
S -> "a"
A -> "b"`
	const target = `S -> "a"
A -> "b"`
	cfg := CFGDeserialize(target)
	cfg = EliminateNongenerating(cfg)
	str1 := CFGSerialize(cfg)
	str2 := CFGSerialize(CFGDeserialize(target))
	if str1 != str2 {
		t.Errorf("serialized unmatch %s\n\n%s\n", str1, str2)
	}

}

func TestEliminateEpsilon(t *testing.T) {
	const ep1 = `A -> B D E
A -> D F H
B -> "epsilon"
B -> "b"
D -> "epsilon"
E -> F G H
G -> "g"
F -> "a"
F -> "epsilon"
H -> "epsilon"
`
	const ep1_target = `
A -> B D E
A -> D E
A -> B E
A -> E
A -> D F H
A -> F H
A -> D H
A -> H
A -> D F
A -> F
A -> D
A -> "epsilon"
B -> "b"
E -> F G H
E -> G H
E -> F G
E -> G
F -> "a"
G -> "g"
`

	const ep2_target = `
A -> B C D E
A -> "epsilon"
A -> C D E
A -> B D E
A -> D E
A -> B C E
A -> C E
A -> B E
A -> E
A -> B C D
A -> C D
A -> B D
A -> D
A -> B C
A -> C
A -> B
B -> "b"
C -> "c"
D -> "d"
E -> "e"
`
	const ep2 = `A -> B C D E
B -> "b"
B -> "epsilon"
C -> "c"
C -> "epsilon"
D -> "d"
D -> "epsilon"
E -> "e"
E -> "epsilon"
`
	test := func(ep string, tar string) {
		cfg1 := CFGDeserialize(ep)
		cfg2 := CFGDeserialize(tar)
		cfg1 = EliminateEpsilon(cfg1)
		str1 := CFGSerialize(cfg1)
		str2 := CFGSerialize(cfg2)
		if str1 != str2 {
			t.Errorf("serialized unmatch %s\n\n%s\n", str1, str2)
		}
	}
	test(ep1, ep1_target)
	test(ep2, ep2_target)
}

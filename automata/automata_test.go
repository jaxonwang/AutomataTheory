package automata

import "testing"
import "io/ioutil"
import "strings"
import "sort"
import "fmt"

func Makelist(s string) []string {
	sb_list := make([]string, 0, 5)
	for _, char := range s {
		sb_list = append(sb_list, string(char))
	}
	return sb_list
}

func TestENFA(t *testing.T) {
	dat_path := "../resources/decimal.enfa"
	dat, err := ioutil.ReadFile(dat_path)
	cases := []struct {
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

	if err != nil {
		t.Errorf("Can not find %s", dat_path)
	}

	enfa := eNFADeserialize(string(dat))
	for _, c := range cases {
		if Accept(enfa, Makelist(c.in)) != c.want {
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
	dfa := nfa.ToDFA()
	s1 := Serialize(dfa)
	dfa1 := DFADeserialize(s1)
	DFAequal(dfa, dfa1, t)
	fmt.Println()
}
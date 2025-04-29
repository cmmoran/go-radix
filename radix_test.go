package radix

import (
	crand "crypto/rand"
	"fmt"
	"reflect"
	"sort"
	"strconv"
	"testing"
)

func TestRadix(t *testing.T) {
	var cmin, cmax string
	inp := make(map[string]interface{})
	for i := 0; i < 1000; i++ {
		gen := generateUUID()
		inp[gen] = i
		if gen < cmin || i == 0 {
			cmin = gen
		}
		if gen > cmax || i == 0 {
			cmax = gen
		}
	}

	r := NewFromMap(inp)
	if r.Len() != len(inp) {
		t.Fatalf("bad length: %v %v", r.Len(), len(inp))
	}

	r.Walk(func(k string, v interface{}) bool {
		println(k)
		return false
	})

	for k, v := range inp {
		out, ok := r.Get(k)
		if !ok {
			t.Fatalf("missing key: %v", k)
		}
		if out != v {
			t.Fatalf("value mis-match: %v %v", out, v)
		}
	}

	// Check min and max
	outMin, _, _ := r.Minimum()
	if outMin != cmin {
		t.Fatalf("bad minimum: %v %v", outMin, cmin)
	}
	outMax, _, _ := r.Maximum()
	if outMax != cmax {
		t.Fatalf("bad maximum: %v %v", outMax, cmax)
	}

	for k, v := range inp {
		out, ok := r.Delete(k)
		if !ok {
			t.Fatalf("missing key: %v", k)
		}
		if out != v {
			t.Fatalf("value mis-match: %v %v", out, v)
		}
	}
	if r.Len() != 0 {
		t.Fatalf("bad length: %v", r.Len())
	}
}

func TestRoot(t *testing.T) {
	r := New[bool]()
	_, ok := r.Delete("")
	if ok {
		t.Fatalf("bad")
	}
	_, ok = r.Insert("", true)
	if ok {
		t.Fatalf("bad")
	}
	val, ok := r.Get("")
	if !ok || val != true {
		t.Fatalf("bad: %v", val)
	}
	val, ok = r.Delete("")
	if !ok || val != true {
		t.Fatalf("bad: %v", val)
	}
}

func TestDelete(t *testing.T) {

	r := New[bool]()

	s := []string{"", "A", "AB"}

	for _, ss := range s {
		r.Insert(ss, true)
	}

	for _, ss := range s {
		_, ok := r.Delete(ss)
		if !ok {
			t.Fatalf("bad %q", ss)
		}
	}
}

func TestDeletePrefix(t *testing.T) {
	type exp struct {
		inp        []string
		prefix     string
		out        []string
		numDeleted int
	}

	cases := []exp{
		{[]string{"", "A", "AB", "ABC", "R", "S"}, "A", []string{"", "R", "S"}, 3},
		{[]string{"", "A", "AB", "ABC", "R", "S"}, "ABC", []string{"", "A", "AB", "R", "S"}, 1},
		{[]string{"", "A", "AB", "ABC", "R", "S"}, "", []string{}, 6},
		{[]string{"", "A", "AB", "ABC", "R", "S"}, "S", []string{"", "A", "AB", "ABC", "R"}, 1},
		{[]string{"", "A", "AB", "ABC", "R", "S"}, "SS", []string{"", "A", "AB", "ABC", "R", "S"}, 0},
	}

	for _, test := range cases {
		r := New[bool]()
		for _, ss := range test.inp {
			r.Insert(ss, true)
		}

		deleted := r.DeletePrefix(test.prefix)
		if deleted != test.numDeleted {
			t.Fatalf("Bad delete, expected %v to be deleted but got %v", test.numDeleted, deleted)
		}

		out := make([]string, 0)
		fn := func(s string, v bool) bool {
			out = append(out, s)
			return false
		}
		r.Walk(fn)

		if !reflect.DeepEqual(out, test.out) {
			t.Fatalf("mis-match: %v %v", out, test.out)
		}
	}
}

func TestLongestPrefix(t *testing.T) {
	r := New[bool]()

	keys := []string{
		"",
		"foo",
		"foobar",
		"foobarbaz",
		"foobarbazzip",
		"foozip",
	}
	for _, k := range keys {
		r.Insert(k, true)
	}
	if r.Len() != len(keys) {
		t.Fatalf("bad len: %v %v", r.Len(), len(keys))
	}

	type exp struct {
		inp string
		out string
	}
	cases := []exp{
		{"a", ""},
		{"abc", ""},
		{"fo", ""},
		{"foo", "foo"},
		{"foob", "foo"},
		{"foobar", "foobar"},
		{"foobarba", "foobar"},
		{"foobarbaz", "foobarbaz"},
		{"foobarbazzi", "foobarbaz"},
		{"foobarbazzip", "foobarbazzip"},
		{"foozi", "foo"},
		{"foozip", "foozip"},
		{"foozipzap", "foozip"},
	}
	for _, test := range cases {
		m, _, ok := r.LongestPrefix(test.inp)
		if !ok {
			t.Fatalf("no match: %v", test)
		}
		if m != test.out {
			t.Fatalf("mis-match: %v %v", m, test)
		}
	}
}

func TestWalkPrefix(t *testing.T) {
	r := New[bool]()

	keys := []string{
		"foobar",
		"foo/bar/baz",
		"foo/baz/bar",
		"foo/zip/zap",
		"zipzap",
	}
	for _, k := range keys {
		r.Insert(k, true)
	}
	if r.Len() != len(keys) {
		t.Fatalf("bad len: %v %v", r.Len(), len(keys))
	}

	type exp struct {
		inp string
		out []string
	}
	cases := []exp{
		{
			"f",
			[]string{"foobar", "foo/bar/baz", "foo/baz/bar", "foo/zip/zap"},
		},
		{
			"foo",
			[]string{"foobar", "foo/bar/baz", "foo/baz/bar", "foo/zip/zap"},
		},
		{
			"foob",
			[]string{"foobar"},
		},
		{
			"foo/",
			[]string{"foo/bar/baz", "foo/baz/bar", "foo/zip/zap"},
		},
		{
			"foo/b",
			[]string{"foo/bar/baz", "foo/baz/bar"},
		},
		{
			"foo/ba",
			[]string{"foo/bar/baz", "foo/baz/bar"},
		},
		{
			"foo/bar",
			[]string{"foo/bar/baz"},
		},
		{
			"foo/bar/baz",
			[]string{"foo/bar/baz"},
		},
		{
			"foo/bar/bazoo",
			[]string{},
		},
		{
			"z",
			[]string{"zipzap"},
		},
	}

	for _, test := range cases {
		out := make([]string, 0)
		fn := func(s string, v bool) bool {
			out = append(out, s)
			return false
		}
		r.WalkPrefix(test.inp, fn)
		sort.Strings(out)
		sort.Strings(test.out)
		if !reflect.DeepEqual(out, test.out) {
			t.Fatalf("mis-match: %v %v", out, test.out)
		}
	}
}

func TestWalkPath(t *testing.T) {
	r := New[bool]()

	keys := []string{
		"foo",
		"foo/bar",
		"foo/bar/baz",
		"foo/baz/bar",
		"foo/zip/zap",
		"zipzap",
	}
	for _, k := range keys {
		r.Insert(k, true)
	}
	if r.Len() != len(keys) {
		t.Fatalf("bad len: %v %v", r.Len(), len(keys))
	}

	type exp struct {
		inp string
		out []string
	}
	cases := []exp{
		{
			"f",
			[]string{},
		},
		{
			"foo",
			[]string{"foo"},
		},
		{
			"foo/",
			[]string{"foo"},
		},
		{
			"foo/ba",
			[]string{"foo"},
		},
		{
			"foo/bar",
			[]string{"foo", "foo/bar"},
		},
		{
			"foo/bar/baz",
			[]string{"foo", "foo/bar", "foo/bar/baz"},
		},
		{
			"foo/bar/bazoo",
			[]string{"foo", "foo/bar", "foo/bar/baz"},
		},
		{
			"z",
			[]string{},
		},
	}

	for _, test := range cases {
		out := make([]string, 0)
		fn := func(s string, v bool) bool {
			out = append(out, s)
			return false
		}
		r.WalkPath(test.inp, fn)
		sort.Strings(out)
		sort.Strings(test.out)
		if !reflect.DeepEqual(out, test.out) {
			t.Fatalf("mis-match: %v %v", out, test.out)
		}
	}
}

func TestWalkDelete(t *testing.T) {
	r := New[bool]()
	r.Insert("init0/0", true)
	r.Insert("init0/1", true)
	r.Insert("init0/2", true)
	r.Insert("init0/3", true)
	r.Insert("init1/0", true)
	r.Insert("init1/1", true)
	r.Insert("init1/2", true)
	r.Insert("init1/3", true)
	r.Insert("init2", true)

	deleteFn := func(s string, v bool) bool {
		r.Delete(s)
		return false
	}

	r.WalkPrefix("init1", deleteFn)

	for _, s := range []string{"init0/0", "init0/1", "init0/2", "init0/3", "init2"} {
		if _, ok := r.Get(s); !ok {
			t.Fatalf("expecting to still find %q", s)
		}
	}
	if n := r.Len(); n != 5 {
		t.Fatalf("expected to find exactly 5 nodes, instead found %d: %v", n, r.ToMap())
	}

	r.Walk(deleteFn)
	if n := r.Len(); n != 0 {
		t.Fatalf("expected to find exactly 0 nodes, instead found %d: %v", n, r.ToMap())
	}
}

// generateUUID is used to generate a random UUID
func generateUUID() string {
	buf := make([]byte, 16)
	if _, err := crand.Read(buf); err != nil {
		panic(fmt.Errorf("failed to read random bytes: %v", err))
	}

	return fmt.Sprintf("%08x-%04x-%04x-%04x-%12x",
		buf[0:4],
		buf[4:6],
		buf[6:8],
		buf[8:10],
		buf[10:16])
}

const (
	benchmarkTreeSize = 10000
)

// setupTree creates a tree with n elements for benchmarking
func setupTree[T any](n int, value T) *Tree[T] {
	r := New[T]()
	for i := 0; i < n; i++ {
		r.Insert(fmt.Sprintf("key%d", i), value)
	}
	return r
}

// generateKeys creates n keys for benchmarking
func generateKeys(n int) []string {
	keys := make([]string, n)
	for i := 0; i < n; i++ {
		keys[i] = fmt.Sprintf("key%d", i)
	}
	return keys
}

// BenchmarkTree_Insert measures insertion performance
func BenchmarkTree_Insert(b *testing.B) {
	r := New[int]()
	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		r.Insert(strconv.Itoa(n), n)
	}
}

// BenchmarkTree_InsertExisting measures performance of inserting existing keys
func BenchmarkTree_InsertExisting(b *testing.B) {
	r := setupTree(benchmarkTreeSize, 42)
	keys := generateKeys(benchmarkTreeSize)

	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		idx := n % benchmarkTreeSize
		r.Insert(keys[idx], 100)
	}
}

// BenchmarkTree_Get measures lookup performance
func BenchmarkTree_Get(b *testing.B) {
	r := setupTree(benchmarkTreeSize, 42)
	keys := generateKeys(benchmarkTreeSize)

	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		idx := n % benchmarkTreeSize
		r.Get(keys[idx])
	}
}

// BenchmarkTree_GetNonexistent measures lookup performance for missing keys
func BenchmarkTree_GetNonexistent(b *testing.B) {
	r := setupTree(benchmarkTreeSize, 42)

	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		r.Get(fmt.Sprintf("missing%d", n))
	}
}

// BenchmarkTree_LongestPrefix measures longest prefix lookup performance
func BenchmarkTree_LongestPrefix(b *testing.B) {
	r := setupTree(benchmarkTreeSize, 42)

	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		idx := n % benchmarkTreeSize
		r.LongestPrefix(fmt.Sprintf("key%d-suffix", idx))
	}
}

// BenchmarkTree_Delete measures deletion performance
func BenchmarkTree_Delete(b *testing.B) {
	b.StopTimer()
	r := setupTree(b.N, 42)
	keys := make([]string, b.N)
	for i := 0; i < b.N; i++ {
		keys[i] = fmt.Sprintf("key%d", i)
	}

	b.StartTimer()
	for i := 0; i < b.N; i++ {
		r.Delete(keys[i])
	}
}

// BenchmarkTree_DeletePrefix measures prefix deletion performance
func BenchmarkTree_DeletePrefix(b *testing.B) {
	prefixLen := 100
	size := prefixLen * b.N

	b.StopTimer()
	r := New[int]()
	for i := 0; i < size; i++ {
		prefix := i / prefixLen
		r.Insert(fmt.Sprintf("prefix%d-key%d", prefix, i), i)
	}

	b.StartTimer()
	for i := 0; i < b.N; i++ {
		r.DeletePrefix(fmt.Sprintf("prefix%d-", i))
	}
}

// BenchmarkTree_Walk measures full tree traversal performance
func BenchmarkTree_Walk(b *testing.B) {
	r := setupTree(benchmarkTreeSize, 42)

	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		count := 0
		r.Walk(func(s string, v int) bool {
			count++
			return false
		})
	}
}

// BenchmarkTree_WalkPrefix measures prefix walking performance
func BenchmarkTree_WalkPrefix(b *testing.B) {
	// Create a tree with key0, key1, ... and also subkey0, subkey1, ...
	r := New[int]()
	for i := 0; i < benchmarkTreeSize; i++ {
		r.Insert(fmt.Sprintf("key%d", i), i)
		r.Insert(fmt.Sprintf("subkey%d", i), i)
	}

	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		count := 0
		prefix := "sub"
		r.WalkPrefix(prefix, func(s string, v int) bool {
			count++
			return false
		})
	}
}

// BenchmarkTree_WalkPath measures path walking performance
func BenchmarkTree_WalkPath(b *testing.B) {
	// Create a hierarchical path structure
	r := New[int]()
	for i := 0; i < 100; i++ {
		path := fmt.Sprintf("root/level1-%d/level2-%d/level3-%d", i, i, i)
		r.Insert(path, i)
	}

	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		idx := n % 100
		path := fmt.Sprintf("root/level1-%d/level2-%d/level3-%d", idx, idx, idx)
		r.WalkPath(path, func(s string, v int) bool {
			return false
		})
	}
}

// BenchmarkTree_Minimum measures minimum key lookup performance
func BenchmarkTree_Minimum(b *testing.B) {
	r := setupTree(benchmarkTreeSize, 42)

	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		r.Minimum()
	}
}

// BenchmarkTree_Maximum measures maximum key lookup performance
func BenchmarkTree_Maximum(b *testing.B) {
	r := setupTree(benchmarkTreeSize, 42)

	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		r.Maximum()
	}
}

// BenchmarkTree_ToMap measures the performance of converting to a map
func BenchmarkTree_ToMap(b *testing.B) {
	r := setupTree(benchmarkTreeSize, 42)

	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		r.ToMap()
	}
}

/-!
# S-DES: key-independent structural recovery, formalized in Lean 4
Models the cipher and attack in sdes_enc_dec.py and adaptive_breaker.py.
Correspondence with the Python implementations is not formally proved.
No Mathlib required (Lean core only).
-/

namespace SDES

abbrev Bits := List Bool

/-! ## Cipher (port of sdes_enc_dec.py) -/

def P10    : List Nat := [3,5,2,7,4,10,1,9,8,6]
def P8     : List Nat := [6,3,7,4,8,5,10,9]
def P4     : List Nat := [2,4,3,1]
def IP     : List Nat := [2,6,3,1,4,8,5,7]
def IPINV  : List Nat := [4,1,3,5,7,2,8,6]
def EP     : List Nat := [4,1,2,3,2,3,4,1]

/-- Standard S-boxes from sdes_enc_dec.py. -/
def S0tab : List (List Nat) := [[1,0,3,2],[3,2,1,0],[0,2,1,3],[3,1,3,2]]
def S1tab : List (List Nat) := [[0,1,2,3],[2,0,1,3],[3,0,1,0],[2,1,0,3]]

def perm (b : Bits) (t : List Nat) : Bits := t.map fun i => b.getD (i - 1) false
def lshift (b : Bits) (n : Nat) : Bits := b.drop n ++ b.take n
def xorL (a b : Bits) : Bits := List.zipWith Bool.xor a b

/-- A 4-bit -> 2-bit S-box, given as a table (row = b0 b3, col = b1 b2). -/
def sboxOf (S : List (List Nat)) (b : Bits) : Bool × Bool :=
  let bit : Nat → Nat := fun i => if b.getD i false then 1 else 0
  let v := ((S.getD (bit 0 * 2 + bit 3) []).getD (bit 1 * 2 + bit 2) 0)
  (v / 2 % 2 == 1, v % 2 == 1)

def genKeys (key : Bits) : Bits × Bits :=
  let p  := perm key P10
  let l1 := lshift (p.take 5) 1
  let r1 := lshift (p.drop 5) 1
  let l2 := lshift l1 2
  let r2 := lshift r1 2
  (perm (l1 ++ r1) P8, perm (l2 ++ r2) P8)

/-- Feistel function; S-boxes are arbitrary functions Bits → Bool × Bool. -/
def fk (S0 S1 : Bits → Bool × Bool) (bits sub : Bits) : Bits :=
  let l := bits.take 4
  let r := bits.drop 4
  let x := xorL (perm r EP) sub
  let a := S0 (x.take 4)
  let b := S1 (x.drop 4)
  xorL l (perm [a.1, a.2, b.1, b.2] P4) ++ r

def sw (b : Bits) : Bits := b.drop 4 ++ b.take 4

/-- Core cipher on explicit subkeys (this is where the key leaves the picture). -/
def encSub (S0 S1 : Bits → Bool × Bool) (k1 k2 pt : Bits) : Bits :=
  perm (fk S0 S1 (sw (fk S0 S1 (perm pt IP) k1)) k2) IPINV

def enc (S0 S1 : Bits → Bool × Bool) (key pt : Bits) : Bits :=
  let (k1, k2) := genKeys key
  encSub S0 S1 k1 k2 pt

/-! ## Theorem 1: the structural identity (paper, Section 2)
For ANY S-boxes and ANY subkeys, every ciphertext bit is one plaintext bit
XORed with exactly one S-box output bit. The subkeys appear only inside the
S-box arguments. -/

theorem structural (S0 S1 : Bits → Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     p1 p2 p3 p4 p5 p6 p7 p8 : Bool) :
    let s  := S0 [xor p7 a1, xor p4 a2, xor p8 a3, xor p5 a4]   -- (s00, s01)
    let s' := S1 [xor p8 a5, xor p5 a6, xor p7 a7, xor p4 a8]   -- (s10, s11)
    let t  := S0 [xor (xor p1 s.1) b1, xor (xor p2 s.2) b2,
                  xor (xor p6 s'.2) b3, xor (xor p3 s'.1) b4]   -- (t00, t01)
    let t' := S1 [xor (xor p6 s'.2) b5, xor (xor p3 s'.1) b6,
                  xor (xor p1 s.1) b7, xor (xor p2 s.2) b8]     -- (t10, t11)
    encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8] [b1,b2,b3,b4,b5,b6,b7,b8]
        [p1,p2,p3,p4,p5,p6,p7,p8]
      = [xor p7 t.1, xor p4 t.2, xor p5 t'.1, xor p2 s.2,
         xor p3 s'.1, xor p8 t'.2, xor p1 s.1, xor p6 s'.2] := by
  intros
  rfl

/-! ## The attack (port of adaptive_breaker.py)
attack receives ONLY an oracle Bits → Bits. It cannot see the key. -/

def natBits (n len : Nat) : Bits :=
  (List.range len).map fun i => (n >>> (len - 1 - i)) % 2 == 1

def bitsNat (b : Bits) : Nat := b.foldl (fun a x => 2 * a + (if x then 1 else 0)) 0

/-- make_pt(l, r) from the Python. -/
def makePt (l r : Nat) : Bits :=
  let L := natBits l 4
  let R := natBits r 4
  [L.getD 3 false, L.getD 0 false, L.getD 2 false, R.getD 0 false,
   R.getD 2 false, L.getD 1 false, R.getD 3 false, R.getD 1 false]

structure Tables where
  r1s0 : List (Nat × Bits) := []
  r1s1 : List (Nat × Bits) := []
  r2s0 : List (Nat × Bits) := []
  r2s1 : List (Nat × Bits) := []

def look (t : List (Nat × Bits)) (k : Nat) : Bits :=
  match t.find? (fun e => e.1 == k) with
  | some e => e.2
  | none   => [false, false]

def has (t : List (Nat × Bits)) (k : Nat) : Bool := t.any (fun e => e.1 == k)

/-- Every entry in a recovered table agrees with its effective function. -/
def TableValid (table : List (Nat × Bits)) (f : Nat -> Bits) : Prop :=
  forall entry, entry ∈ table -> entry.2 = f entry.1

/-- Adding a correct entry preserves the table-value invariant. -/
theorem tableValid_cons (table : List (Nat × Bits)) (f : Nat -> Bits)
    (index : Nat) (value : Bits) (hv : value = f index)
    (ht : TableValid table f) : TableValid ((index,value) :: table) f := by
  intro entry he
  simp only [List.mem_cons] at he
  rcases he with he | he
  · subst entry
    exact hv
  · exact ht entry he

/-- A present index in a valid table returns the effective value, even when
    the association list contains duplicate indices. -/
theorem look_of_valid (table : List (Nat × Bits)) (f : Nat -> Bits)
    (i : Nat) (hvalid : TableValid table f) (hpresent : has table i = true) :
    look table i = f i := by
  induction table with
  | nil => simp [has] at hpresent
  | cons entry rest ih =>
    have hv : entry.2 = f entry.1 := hvalid entry (by simp)
    have ht : TableValid rest f := by
      intro e he
      exact hvalid e (by simp [he])
    simp only [has, List.any_cons, Bool.or_eq_true] at hpresent
    simp only [look, List.find?_cons]
    by_cases h : entry.1 == i
    · simp only [h]
      have heq : entry.1 = i := by simpa using h
      simpa [heq] using hv
    · simp only [h]
      apply ih ht
      exact hpresent.resolve_left h

/-- extract_and_store; returns updated tables and the round-1 outputs. -/
def extract (oracle : Bits → Bits) (T : Tables) (pt : Bits) :
    Tables × (Bool × Bool × Bool × Bool) :=
  let c := oracle pt
  let p := fun i => pt.getD i false
  let q := fun i => c.getD i false
  let t00 := xor (q 0) (p 6)
  let t01 := xor (q 1) (p 3)
  let t10 := xor (q 2) (p 4)
  let s01 := xor (q 3) (p 1)
  let s10 := xor (q 4) (p 2)
  let t11 := xor (q 5) (p 7)
  let s00 := xor (q 6) (p 0)
  let s11 := xor (q 7) (p 5)
  let idx1 := bitsNat [p 6, p 3, p 7, p 4]
  let idx2 := bitsNat [p 7, p 4, p 6, p 3]
  let j0 := bitsNat [xor (p 0) s00, xor (p 1) s01, xor (p 5) s11, xor (p 2) s10]
  let j1 := bitsNat [xor (p 5) s11, xor (p 2) s10, xor (p 0) s00, xor (p 1) s01]
  ({ r1s0 := (idx1, [s00, s01]) :: T.r1s0
     r1s1 := (idx2, [s10, s11]) :: T.r1s1
     r2s0 := (j0, [t00, t01]) :: T.r2s0
     r2s1 := (j1, [t10, t11]) :: T.r2s1 }, (s00, s01, s10, s11))

/-- An invariant preserved by every step is preserved by a left fold. -/
theorem foldl_preserves {State Item : Type} (P : State -> Prop)
    (step : State -> Item -> State) (items : List Item) (initial : State)
    (hinit : P initial)
    (hstep : forall state item, P state -> P (step state item)) :
    P (items.foldl step initial) := by
  induction items generalizing initial with
  | nil => exact hinit
  | cons item rest ih =>
    exact ih (step initial item) (hstep initial item hinit)

/-- Extracting another query cannot remove any previously observed index. -/
theorem extract_preserves_indices (oracle : Bits -> Bits) (T : Tables)
    (pt : Bits) (i : Nat) :
    (has T.r1s0 i = true -> has (extract oracle T pt).1.r1s0 i = true) /\
    (has T.r1s1 i = true -> has (extract oracle T pt).1.r1s1 i = true) /\
    (has T.r2s0 i = true -> has (extract oracle T pt).1.r2s0 i = true) /\
    (has T.r2s1 i = true -> has (extract oracle T pt).1.r2s1 i = true) := by
  simp only [extract, has, List.any_cons, Bool.or_eq_true]
  exact ⟨fun h => Or.inr h, fun h => Or.inr h, fun h => Or.inr h, fun h => Or.inr h⟩

/-- Any sequence of extracted queries preserves the indices already present,
    including the adaptive phase-two fold, regardless of its target selection. -/
theorem extract_fold_preserves_indices (oracle : Bits -> Bits)
    (query : Nat -> Bits) (targets : List Nat) (initial : Tables) (i : Nat)
    (h0 : has initial.r1s0 i = true) (h1 : has initial.r1s1 i = true)
    (h2 : has initial.r2s0 i = true) (h3 : has initial.r2s1 i = true) :
    let final := targets.foldl (fun T target => (extract oracle T (query target)).1) initial
    has final.r1s0 i = true /\ has final.r1s1 i = true /\
      has final.r2s0 i = true /\ has final.r2s1 i = true := by
  dsimp only
  apply foldl_preserves
    (P := fun (T : Tables) => has T.r1s0 i = true /\ has T.r1s1 i = true /\
      has T.r2s0 i = true /\ has T.r2s1 i = true)
  · exact ⟨h0, h1, h2, h3⟩
  · intro T target h
    have hp := extract_preserves_indices oracle T (query target) i
    exact ⟨hp.1 h.1, hp.2.1 h.2.1, hp.2.2.1 h.2.2.1,
      hp.2.2.2 h.2.2.2⟩

/-- If each extraction preserves the value invariant for the first
    second-round table, a fold of extractions preserves it as well. -/
theorem extract_fold_valid_r2s0 (oracle : Bits -> Bits)
    (query : Nat -> Bits) (targets : List Nat) (initial : Tables)
    (f : Nat -> Bits) (hinit : TableValid initial.r2s0 f)
    (hstep : forall T target, TableValid T.r2s0 f ->
      TableValid (extract oracle T (query target)).1.r2s0 f) :
    TableValid (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r2s0 f := by
  exact foldl_preserves (fun T : Tables => TableValid T.r2s0 f)
    (fun T target => (extract oracle T (query target)).1)
    targets initial hinit hstep

/-- Presence plus the fold's value invariant yields the effective output. -/
theorem extract_fold_lookup_r2s0 (oracle : Bits -> Bits)
    (query : Nat -> Bits) (targets : List Nat) (initial : Tables)
    (f : Nat -> Bits) (i : Nat) (hinit : TableValid initial.r2s0 f)
    (hstep : forall T target, TableValid T.r2s0 f ->
      TableValid (extract oracle T (query target)).1.r2s0 f)
    (hpresent : has (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r2s0 i = true) :
    look (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r2s0 i = f i := by
  exact look_of_valid _ f i
    (extract_fold_valid_r2s0 oracle query targets initial f hinit hstep) hpresent

/-- If each extraction preserves the value invariant for the first-round S0 table, a fold of extractions preserves it as well. -/
theorem extract_fold_valid_r1s0 (oracle : Bits -> Bits)
    (query : Nat -> Bits) (targets : List Nat) (initial : Tables)
    (f : Nat -> Bits) (hinit : TableValid initial.r1s0 f)
    (hstep : forall T target, TableValid T.r1s0 f ->
      TableValid (extract oracle T (query target)).1.r1s0 f) :
    TableValid (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r1s0 f := by
  exact foldl_preserves (fun T : Tables => TableValid T.r1s0 f)
    (fun T target => (extract oracle T (query target)).1)
    targets initial hinit hstep

/-- Presence plus the fold's value invariant yields the effective output. -/
theorem extract_fold_lookup_r1s0 (oracle : Bits -> Bits)
    (query : Nat -> Bits) (targets : List Nat) (initial : Tables)
    (f : Nat -> Bits) (i : Nat) (hinit : TableValid initial.r1s0 f)
    (hstep : forall T target, TableValid T.r1s0 f ->
      TableValid (extract oracle T (query target)).1.r1s0 f)
    (hpresent : has (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r1s0 i = true) :
    look (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r1s0 i = f i := by
  exact look_of_valid _ f i
    (extract_fold_valid_r1s0 oracle query targets initial f hinit hstep) hpresent

/-- If each extraction preserves the value invariant for the first-round S1 table, a fold of extractions preserves it as well. -/
theorem extract_fold_valid_r1s1 (oracle : Bits -> Bits)
    (query : Nat -> Bits) (targets : List Nat) (initial : Tables)
    (f : Nat -> Bits) (hinit : TableValid initial.r1s1 f)
    (hstep : forall T target, TableValid T.r1s1 f ->
      TableValid (extract oracle T (query target)).1.r1s1 f) :
    TableValid (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r1s1 f := by
  exact foldl_preserves (fun T : Tables => TableValid T.r1s1 f)
    (fun T target => (extract oracle T (query target)).1)
    targets initial hinit hstep

/-- Presence plus the fold's value invariant yields the effective output. -/
theorem extract_fold_lookup_r1s1 (oracle : Bits -> Bits)
    (query : Nat -> Bits) (targets : List Nat) (initial : Tables)
    (f : Nat -> Bits) (i : Nat) (hinit : TableValid initial.r1s1 f)
    (hstep : forall T target, TableValid T.r1s1 f ->
      TableValid (extract oracle T (query target)).1.r1s1 f)
    (hpresent : has (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r1s1 i = true) :
    look (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r1s1 i = f i := by
  exact look_of_valid _ f i
    (extract_fold_valid_r1s1 oracle query targets initial f hinit hstep) hpresent

/-- If each extraction preserves the value invariant for the second-round S1 table, a fold of extractions preserves it as well. -/
theorem extract_fold_valid_r2s1 (oracle : Bits -> Bits)
    (query : Nat -> Bits) (targets : List Nat) (initial : Tables)
    (f : Nat -> Bits) (hinit : TableValid initial.r2s1 f)
    (hstep : forall T target, TableValid T.r2s1 f ->
      TableValid (extract oracle T (query target)).1.r2s1 f) :
    TableValid (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r2s1 f := by
  exact foldl_preserves (fun T : Tables => TableValid T.r2s1 f)
    (fun T target => (extract oracle T (query target)).1)
    targets initial hinit hstep

/-- Presence plus the fold's value invariant yields the effective output. -/
theorem extract_fold_lookup_r2s1 (oracle : Bits -> Bits)
    (query : Nat -> Bits) (targets : List Nat) (initial : Tables)
    (f : Nat -> Bits) (i : Nat) (hinit : TableValid initial.r2s1 f)
    (hstep : forall T target, TableValid T.r2s1 f ->
      TableValid (extract oracle T (query target)).1.r2s1 f)
    (hpresent : has (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r2s1 i = true) :
    look (targets.foldl (fun T target =>
      (extract oracle T (query target)).1) initial).r2s1 i = f i := by
  exact look_of_valid _ f i
    (extract_fold_valid_r2s1 oracle query targets initial f hinit hstep) hpresent

/-- The second phase schedules exactly the unobserved round-two S0 indices. -/
theorem missing_indices_iff (T : Tables) (i : Nat) :
    i ∈ (List.range 16).filter (fun j => !(has T.r2s0 j)) <->
      i < 16 /\ has T.r2s0 i = false := by
  simp

private theorem xor_cancel (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

private theorem xor_cancel_right (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

/-- For arbitrary S-boxes and explicit eight-bit subkeys, extraction records
    the effective outputs of both rounds for an eight-bit query. -/
theorem extract_symbolic (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     p1 p2 p3 p4 p5 p6 p7 p8 : Bool) (T : Tables) :
    let s := S0 [xor p7 a1, xor p4 a2, xor p8 a3, xor p5 a4]
    let s' := S1 [xor p8 a5, xor p5 a6, xor p7 a7, xor p4 a8]
    let j0 := [xor p1 s.1, xor p2 s.2, xor p6 s'.2, xor p3 s'.1]
    let j1 := [xor p6 s'.2, xor p3 s'.1, xor p1 s.1, xor p2 s.2]
    let t := S0 (xorL j0 [b1,b2,b3,b4])
    let t' := S1 (xorL j1 [b5,b6,b7,b8])
    extract (encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
      [b1,b2,b3,b4,b5,b6,b7,b8]) T [p1,p2,p3,p4,p5,p6,p7,p8] =
    ({ r1s0 := (bitsNat [p7,p4,p8,p5], [s.1,s.2]) :: T.r1s0
       r1s1 := (bitsNat [p8,p5,p7,p4], [s'.1,s'.2]) :: T.r1s1
       r2s0 := (bitsNat j0, [t.1,t.2]) :: T.r2s0
       r2s1 := (bitsNat j1, [t'.1,t'.2]) :: T.r2s1 },
     (s.1,s.2,s'.1,s'.2)) := by
  simp only [extract, structural, List.getD_cons_zero, List.getD_cons_succ,
    xorL, List.zipWith, Bool.xor_comm, xor_cancel]

/-- Four-bit conversion recovers the original bits. -/
theorem natBits_bitsNat_four (a b c d : Bool) :
    natBits (bitsNat [a,b,c,d]) 4 = [a,b,c,d] := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- Effective S-box table with its four subkey bits folded into the function. -/
def effectiveTable (S0 : Bits -> Bool × Bool) (a1 a2 a3 a4 : Bool)
    (i : Nat) : Bits :=
  let out := S0 (xorL (natBits i 4) [a1,a2,a3,a4])
  [out.1, out.2]

/-- Extracting any eight-bit query from the actual cipher preserves
    correctness of the first round's S0 table. -/
theorem extract_valid_r1s0 (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     p1 p2 p3 p4 p5 p6 p7 p8 : Bool) (T : Tables)
    (h : TableValid T.r1s0 (effectiveTable S0 a1 a2 a3 a4)) :
    TableValid
      (extract (encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
        [b1,b2,b3,b4,b5,b6,b7,b8]) T [p1,p2,p3,p4,p5,p6,p7,p8]).1.r1s0
      (effectiveTable S0 a1 a2 a3 a4) := by
  rw [extract_symbolic]
  apply tableValid_cons
  · simp only [effectiveTable, natBits_bitsNat_four, xorL, List.zipWith]
  · exact h

/-- Extracting any eight-bit query from the actual cipher preserves
    correctness of r1s1 table. -/
theorem extract_valid_r1s1 (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     p1 p2 p3 p4 p5 p6 p7 p8 : Bool) (T : Tables)
    (h : TableValid T.r1s1 (effectiveTable S1 a5 a6 a7 a8)) :
    TableValid
      (extract (encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
        [b1,b2,b3,b4,b5,b6,b7,b8]) T [p1,p2,p3,p4,p5,p6,p7,p8]).1.r1s1
      (effectiveTable S1 a5 a6 a7 a8) := by
  rw [extract_symbolic]
  apply tableValid_cons
  · simp only [effectiveTable, natBits_bitsNat_four, xorL, List.zipWith]
  · exact h

/-- Extracting any eight-bit query from the actual cipher preserves
    correctness of r2s0 table. -/
theorem extract_valid_r2s0 (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     p1 p2 p3 p4 p5 p6 p7 p8 : Bool) (T : Tables)
    (h : TableValid T.r2s0 (effectiveTable S0 b1 b2 b3 b4)) :
    TableValid
      (extract (encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
        [b1,b2,b3,b4,b5,b6,b7,b8]) T [p1,p2,p3,p4,p5,p6,p7,p8]).1.r2s0
      (effectiveTable S0 b1 b2 b3 b4) := by
  rw [extract_symbolic]
  apply tableValid_cons
  · simp only [effectiveTable, natBits_bitsNat_four, xorL, List.zipWith]
  · exact h

/-- Extracting any eight-bit query from the actual cipher preserves
    correctness of r2s1 table. -/
theorem extract_valid_r2s1 (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     p1 p2 p3 p4 p5 p6 p7 p8 : Bool) (T : Tables)
    (h : TableValid T.r2s1 (effectiveTable S1 b5 b6 b7 b8)) :
    TableValid
      (extract (encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
        [b1,b2,b3,b4,b5,b6,b7,b8]) T [p1,p2,p3,p4,p5,p6,p7,p8]).1.r2s1
      (effectiveTable S1 b5 b6 b7 b8) := by
  rw [extract_symbolic]
  apply tableValid_cons
  · simp only [effectiveTable, natBits_bitsNat_four, xorL, List.zipWith]
  · exact h

/-- All four tables agree with the effective keyed S-box functions. -/
def TablesValid (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 : Bool)
    (T : Tables) : Prop :=
    TableValid T.r1s0 (effectiveTable S0 a1 a2 a3 a4) /\
    TableValid T.r1s1 (effectiveTable S1 a5 a6 a7 a8) /\
    TableValid T.r2s0 (effectiveTable S0 b1 b2 b3 b4) /\
    TableValid T.r2s1 (effectiveTable S1 b5 b6 b7 b8)

theorem extract_valid_all (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     p1 p2 p3 p4 p5 p6 p7 p8 : Bool) (T : Tables)
    (h : TablesValid S0 S1 a1 a2 a3 a4 a5 a6 a7 a8
      b1 b2 b3 b4 b5 b6 b7 b8 T) :
    TablesValid S0 S1 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
      (extract (encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
        [b1,b2,b3,b4,b5,b6,b7,b8]) T [p1,p2,p3,p4,p5,p6,p7,p8]).1 := by
  exact ⟨extract_valid_r1s0 S0 S1 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 p1 p2 p3 p4 p5 p6 p7 p8 T h.1,
    extract_valid_r1s1 S0 S1 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 p1 p2 p3 p4 p5 p6 p7 p8 T h.2.1,
    extract_valid_r2s0 S0 S1 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 p1 p2 p3 p4 p5 p6 p7 p8 T h.2.2.1,
    extract_valid_r2s1 S0 S1 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 p1 p2 p3 p4 p5 p6 p7 p8 T h.2.2.2⟩

/-- The phase-two plaintext constructor sets the four controllable bits
    while fixing the first-round input to zero. -/
theorem forge_plaintext (p1 p2 p3 p6 : Bool) :
    makePt (bitsNat [p2,p6,p3,p1]) 0 =
      [p1,p2,p3,false,false,p6,false,false] := by
  cases p1 <;> cases p2 <;> cases p3 <;> cases p6 <;> rfl

/-- Given the round-one outputs at R0 = 0, the phase-two forgery
    targets the requested four bits; the second index is their half-swap. -/
theorem forge_targets (u0 u1 u2 u3 s00 s01 s10 s11 : Bool) :
    let pt := makePt (bitsNat [xor u1 s01, xor u2 s11,
      xor u3 s10, xor u0 s00]) 0
    let j0 := [xor (pt.getD 0 false) s00, xor (pt.getD 1 false) s01,
      xor (pt.getD 5 false) s11, xor (pt.getD 2 false) s10]
    let j1 := [xor (pt.getD 5 false) s11, xor (pt.getD 2 false) s10,
      xor (pt.getD 0 false) s00, xor (pt.getD 1 false) s01]
    (j0, j1) = ([u0,u1,u2,u3], [u2,u3,u0,u1]) := by
  simp only [forge_plaintext, List.getD_cons_zero, List.getD_cons_succ,
    xor_cancel_right]

/-- Swap the two halves of a four-bit table index. -/
def swapIndex (i : Nat) : Nat :=
  let b := natBits i 4
  bitsNat [b.getD 2 false, b.getD 3 false, b.getD 0 false, b.getD 1 false]

theorem swapIndex_bits (a b c d : Bool) :
    swapIndex (bitsNat [a,b,c,d]) = bitsNat [c,d,a,b] := by
  simp only [swapIndex, natBits_bitsNat_four, List.getD_cons_zero, List.getD_cons_succ]

def PairedIndices (T : Tables) : Prop :=
  forall i, has T.r2s0 i = true -> has T.r2s1 (swapIndex i) = true

/-- One extraction preserves the relationship between paired indices. -/
theorem extract_preserves_pairing (oracle : Bits -> Bits) (T : Tables)
    (pt : Bits) (h : PairedIndices T) : PairedIndices (extract oracle T pt).1 := by
  intro i hi
  simp only [extract, has, List.any_cons, Bool.or_eq_true] at hi ⊢
  rcases hi with heq | hprev
  · simp only [beq_iff_eq] at heq
    left
    rw [← heq]
    simp only [swapIndex_bits, beq_self_eq_true]
  · right
    exact h i hprev

/-- A fold reaches a property when its triggering item occurs, provided
    later steps preserve that property. -/
theorem foldl_mem_establishes {State Item : Type} (P : State -> Prop)
    (step : State -> Item -> State) (items : List Item) (initial : State)
    (target : Item) (hmem : target ∈ items)
    (hinsert : forall state, P (step state target))
    (hkeep : forall state item, P state -> P (step state item)) :
    P (items.foldl step initial) := by
  induction items generalizing initial with
  | nil => simp at hmem
  | cons head tail ih =>
    simp only [List.mem_cons] at hmem
    simp only [List.foldl_cons]
    rcases hmem with heq | htail
    · subst head
      exact foldl_preserves P step tail (step initial target) (hinsert initial) hkeep
    · exact ih (step initial head) htail

/-- If each scheduled step inserts its target and preserves old indices,
    processing the missing indices makes the selected table complete. -/
theorem fill_missing_indices (select : Tables -> List (Nat × Bits))
    (step : Tables -> Nat -> Tables) (initial : Tables)
    (hinsert : forall T i, i < 16 -> has (select (step T i)) i = true)
    (hkeep : forall T j i, has (select T) i = true ->
      has (select (step T j)) i = true)
    (i : Nat) (hi : i < 16) :
    has (select ((List.range 16).filter (fun j => !(has (select initial) j)) |>.foldl step initial)) i = true := by
  cases h : has (select initial) i with
  | true =>
    exact foldl_preserves (fun T => has (select T) i = true) step _ initial h
      (fun T j hp => hkeep T j i hp)
  | false =>
    have hm : i ∈ (List.range 16).filter (fun j => !(has (select initial) j)) := by
      simp [hi, h]
    exact foldl_mem_establishes (fun T => has (select T) i = true) step _ initial i hm
      (fun T => hinsert T i hi) (fun T j hp => hkeep T j i hp)

/-- State produced by the first phase of the attack. -/
def phase1State (oracle : Bits -> Bits) : Tables × (Bool × Bool × Bool × Bool) :=
  (List.range 16).foldl
    (fun (acc : Tables × (Bool × Bool × Bool × Bool)) r =>
      let (T, b) := acc
      let (T', o) := extract oracle T (makePt 0 r)
      (T', if r == 0 then o else b))
    ({}, (false, false, false, false))

theorem phase1_coverage (oracle : Bits -> Bits) (i : Nat) (hi : i < 16) :
    has (phase1State oracle).1.r1s0 i = true /\
    has (phase1State oracle).1.r1s1 i = true := by
  have hr : List.range 16 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := by rfl
  simp only [phase1State, hr, List.foldl_cons, List.foldl_nil, extract,
    has, List.any_cons]
  have h : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
      i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst i <;> constructor <;> rfl

/-- The initial query supplies the base used by phase two. -/
theorem phase1_base (oracle : Bits -> Bits) :
    (phase1State oracle).2 = (extract oracle {} (makePt 0 0)).2 := by
  rfl

/-- The saved base is exactly the round-one output at zero input. -/
theorem phase1_cipher_base (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) :
    let s := S0 [xor false a1, xor false a2, xor false a3, xor false a4]
    let t := S1 [xor false a5, xor false a6, xor false a7, xor false a8]
    (phase1State (encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
      [b1,b2,b3,b4,b5,b6,b7,b8])).2 = (s.1,s.2,t.1,t.2) := by
  rw [phase1_base]
  change (extract (encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
    [b1,b2,b3,b4,b5,b6,b7,b8]) {}
      [false,false,false,false,false,false,false,false]).2 = _
  rw [extract_symbolic]

theorem phase1_paired (oracle : Bits -> Bits) : PairedIndices (phase1State oracle).1 := by
  unfold phase1State
  apply foldl_preserves (P := fun (acc : Tables × (Bool × Bool × Bool × Bool)) => PairedIndices acc.1)
  · intro i h
    simp [has] at h
  · intro acc r h
    exact extract_preserves_pairing oracle acc.1 (makePt 0 r) h

/-- Converting a four-bit natural to bits and back preserves it. -/
theorem bitsNat_natBits_four (i : Nat) (hi : i < 16) :
    bitsNat (natBits i 4) = i := by
  have h : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
      i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst i <;> rfl

/-- A phase-two forgery inserts both the target and its half-swap. -/
theorem forge_inserts (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     u0 u1 u2 u3 : Bool) (T : Tables) :
    let s := S0 [xor false a1, xor false a2, xor false a3, xor false a4]
    let s' := S1 [xor false a5, xor false a6, xor false a7, xor false a8]
    let pt := makePt (bitsNat [xor u1 s.2, xor u2 s'.2,
      xor u3 s'.1, xor u0 s.1]) 0
    let newT := (extract (encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
      [b1,b2,b3,b4,b5,b6,b7,b8]) T pt).1
    has newT.r2s0 (bitsNat [u0,u1,u2,u3]) = true /\
      has newT.r2s1 (bitsNat [u2,u3,u0,u1]) = true := by
  simp only [forge_plaintext, extract_symbolic, has, List.any_cons,
    xor_cancel_right, beq_self_eq_true, Bool.true_or, true_and]

/-- One phase-two query for the supplied saved base and target. -/
def phase2Step (oracle : Bits -> Bits) (base : Bool × Bool × Bool × Bool)
    (T : Tables) (target : Nat) : Tables :=
  let (s00, s01, s10, s11) := base
  let tb := natBits target 4
  let p1 := xor (tb.getD 0 false) s00
  let p2 := xor (tb.getD 1 false) s01
  let p6 := xor (tb.getD 2 false) s11
  let p3 := xor (tb.getD 3 false) s10
  (extract oracle T (makePt (bitsNat [p2, p6, p3, p1]) 0)).1

/-- The actual phase-two step inserts its target and its half-swap. -/
theorem phase2Step_inserts (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     u0 u1 u2 u3 : Bool) (T : Tables) :
    let oracle := encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
      [b1,b2,b3,b4,b5,b6,b7,b8]
    let T' := phase2Step oracle (phase1State oracle).2 T (bitsNat [u0,u1,u2,u3])
    has T'.r2s0 (bitsNat [u0,u1,u2,u3]) = true /\
      has T'.r2s1 (bitsNat [u2,u3,u0,u1]) = true := by
  simp only [phase2Step, phase1_cipher_base, natBits_bitsNat_four,
    List.getD_cons_zero, List.getD_cons_succ]
  exact forge_inserts S0 S1 a1 a2 a3 a4 a5 a6 a7 a8
    b1 b2 b3 b4 b5 b6 b7 b8 u0 u1 u2 u3 T

theorem phase2Step_inserts_index (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 : Bool)
    (i : Nat) (hi : i < 16) (T : Tables) :
    let oracle := encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
      [b1,b2,b3,b4,b5,b6,b7,b8]
    has (phase2Step oracle (phase1State oracle).2 T i).r2s0 i = true := by
  have hb : [ (natBits i 4).getD 0 false, (natBits i 4).getD 1 false,
    (natBits i 4).getD 2 false, (natBits i 4).getD 3 false ] = natBits i 4 := by rfl
  have h := phase2Step_inserts S0 S1 a1 a2 a3 a4 a5 a6 a7 a8
    b1 b2 b3 b4 b5 b6 b7 b8 ((natBits i 4).getD 0 false)
    ((natBits i 4).getD 1 false) ((natBits i 4).getD 2 false)
    ((natBits i 4).getD 3 false) T
  rw [hb, bitsNat_natBits_four i hi] at h
  exact h.1

/-- Two-phase attack. Returns the recovered tables and the query count. -/
def attack (oracle : Bits → Bits) : Tables × Nat :=
  -- Phase 1: sweep R0 with L0 = 0000 (16 queries)
  let (T1, base) := phase1State oracle
  let missing := (List.range 16).filter fun i => !(has T1.r2s0 i)
  let T2 := missing.foldl (phase2Step oracle base) T1
  (T2, 16 + missing.length)

/-- Phase two covers every round-two S0 index. -/
theorem attack_r2s0_coverage (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 : Bool)
    (i : Nat) (hi : i < 16) :
    let oracle := encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
      [b1,b2,b3,b4,b5,b6,b7,b8]
    has (attack oracle).1.r2s0 i = true := by
  dsimp only [attack]
  apply fill_missing_indices (fun T => T.r2s0)
  · intro T j hj
    exact phase2Step_inserts_index S0 S1 a1 a2 a3 a4 a5 a6 a7 a8
      b1 b2 b3 b4 b5 b6 b7 b8 j hj T
  · intro T j k hk
    simp only [phase2Step]
    exact (extract_preserves_indices _ _ _ k).2.2.1 hk
  · exact hi

theorem attack_paired (oracle : Bits -> Bits) : PairedIndices (attack oracle).1 := by
  dsimp only [attack]
  apply foldl_preserves (P := PairedIndices)
  · exact phase1_paired oracle
  · intro T j h
    simp only [phase2Step]
    exact extract_preserves_pairing oracle T _ h

theorem swapIndex_properties (i : Nat) (hi : i < 16) :
    swapIndex i < 16 /\ swapIndex (swapIndex i) = i := by
  have h : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
      i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst i <;> constructor <;> simp [swapIndex, natBits, bitsNat]

theorem attack_r2s1_coverage (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 : Bool)
    (i : Nat) (hi : i < 16) :
    let oracle := encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
      [b1,b2,b3,b4,b5,b6,b7,b8]
    has (attack oracle).1.r2s1 i = true := by
  have hp := swapIndex_properties i hi
  have hc := attack_r2s0_coverage S0 S1 a1 a2 a3 a4 a5 a6 a7 a8
    b1 b2 b3 b4 b5 b6 b7 b8 (swapIndex i) hp.1
  have h := attack_paired (encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
    [b1,b2,b3,b4,b5,b6,b7,b8]) (swapIndex i) hc
  simpa only [hp.2] using h

/-- The second phase preserves the round-one coverage established by phase one. -/
theorem attack_r1_coverage (oracle : Bits -> Bits) (i : Nat) (hi : i < 16) :
    has (attack oracle).1.r1s0 i = true /\ has (attack oracle).1.r1s1 i = true := by
  dsimp only [attack]
  apply foldl_preserves (P := fun (T : Tables) => has T.r1s0 i = true /\ has T.r1s1 i = true)
  · exact phase1_coverage oracle i hi
  · intro T j h
    simp only [phase2Step]
    constructor
    · exact (extract_preserves_indices oracle T _ i).1 h.1
    · exact (extract_preserves_indices oracle T _ i).2.1 h.2

/-- Both phases preserve correctness of all four effective tables. -/
theorem attack_tables_valid (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) :
    let oracle := encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
      [b1,b2,b3,b4,b5,b6,b7,b8]
    TablesValid S0 S1 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
      (attack oracle).1 := by
  let oracle := encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8] [b1,b2,b3,b4,b5,b6,b7,b8]
  let P := TablesValid S0 S1 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
  have hphase1 : P (phase1State oracle).1 := by
    unfold phase1State
    apply foldl_preserves (P := fun (acc : Tables × (Bool × Bool × Bool × Bool)) => P acc.1)
    · simp [P, TablesValid, TableValid]
    · intro acc r h
      change P (extract oracle acc.1 (makePt 0 r)).1
      unfold oracle P makePt
      exact extract_valid_all S0 S1 a1 a2 a3 a4 a5 a6 a7 a8
        b1 b2 b3 b4 b5 b6 b7 b8 _ _ _ _ _ _ _ _ acc.1 h
  change P (attack oracle).1
  dsimp only [attack]
  apply foldl_preserves (P := P)
  · exact hphase1
  · intro T j h
    simp only [phase2Step]
    unfold oracle P makePt
    exact extract_valid_all S0 S1 a1 a2 a3 a4 a5 a6 a7 a8
      b1 b2 b3 b4 b5 b6 b7 b8 _ _ _ _ _ _ _ _ T h

/-- emulate_cipher from the Python: uses only the recovered tables. -/
def emulate (T : Tables) (pt : Bits) : Bits :=
  let p := fun i => pt.getD i false
  let idx1 := bitsNat [p 6, p 3, p 7, p 4]
  let idx2 := bitsNat [p 7, p 4, p 6, p 3]
  let a := look T.r1s0 idx1
  let b := look T.r1s1 idx2
  let s00 := a.getD 0 false; let s01 := a.getD 1 false
  let s10 := b.getD 0 false; let s11 := b.getD 1 false
  let j0 := bitsNat [xor (p 0) s00, xor (p 1) s01, xor (p 5) s11, xor (p 2) s10]
  let j1 := bitsNat [xor (p 5) s11, xor (p 2) s10, xor (p 0) s00, xor (p 1) s01]
  let c := look T.r2s0 j0
  let d := look T.r2s1 j1
  [xor (p 6) (c.getD 0 false), xor (p 3) (c.getD 1 false),
   xor (p 4) (d.getD 0 false), xor (p 1) s01,
   xor (p 2) s10,              xor (p 7) (d.getD 1 false),
   xor (p 0) s00,              xor (p 5) s11]

/-- Correct table entries at the four indices used by a plaintext suffice for
    the table emulator to reproduce the structural cipher identity. -/
theorem emulate_of_lookups (S0 S1 : Bits -> Bool × Bool) (T : Tables)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     p1 p2 p3 p4 p5 p6 p7 p8 : Bool)
    (h0 : look T.r1s0 (bitsNat [p7,p4,p8,p5]) =
      let s := S0 [xor p7 a1,xor p4 a2,xor p8 a3,xor p5 a4]; [s.1,s.2])
    (h1 : look T.r1s1 (bitsNat [p8,p5,p7,p4]) =
      let s := S1 [xor p8 a5,xor p5 a6,xor p7 a7,xor p4 a8]; [s.1,s.2])
    (h2 : let s := S0 [xor p7 a1,xor p4 a2,xor p8 a3,xor p5 a4]
          let s' := S1 [xor p8 a5,xor p5 a6,xor p7 a7,xor p4 a8]
          let j := [xor p1 s.1,xor p2 s.2,xor p6 s'.2,xor p3 s'.1]
          let t := S0 (xorL j [b1,b2,b3,b4])
          look T.r2s0 (bitsNat j) = [t.1,t.2])
    (h3 : let s := S0 [xor p7 a1,xor p4 a2,xor p8 a3,xor p5 a4]
          let s' := S1 [xor p8 a5,xor p5 a6,xor p7 a7,xor p4 a8]
          let j := [xor p6 s'.2,xor p3 s'.1,xor p1 s.1,xor p2 s.2]
          let t := S1 (xorL j [b5,b6,b7,b8])
          look T.r2s1 (bitsNat j) = [t.1,t.2]) :
    emulate T [p1,p2,p3,p4,p5,p6,p7,p8] =
      encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8] [b1,b2,b3,b4,b5,b6,b7,b8]
        [p1,p2,p3,p4,p5,p6,p7,p8] := by
  simp only [emulate, structural, List.getD_cons_zero, List.getD_cons_succ,
    h0, h1, h2, h3, xorL, List.zipWith]

/-- Correct and present entries in all four tables imply emulation correctness. -/
theorem emulate_of_table_validity (S0 S1 : Bits -> Bool × Bool) (T : Tables)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     p1 p2 p3 p4 p5 p6 p7 p8 : Bool)
    (f0 f1 f2 f3 : Nat -> Bits)
    (v0 : TableValid T.r1s0 f0) (v1 : TableValid T.r1s1 f1)
    (v2 : TableValid T.r2s0 f2) (v3 : TableValid T.r2s1 f3)
    (c0 : has T.r1s0 (bitsNat [p7,p4,p8,p5]) = true)
    (c1 : has T.r1s1 (bitsNat [p8,p5,p7,p4]) = true)
    (c2 : let s := S0 [xor p7 a1,xor p4 a2,xor p8 a3,xor p5 a4]
          let s' := S1 [xor p8 a5,xor p5 a6,xor p7 a7,xor p4 a8]
          has T.r2s0 (bitsNat [xor p1 s.1,xor p2 s.2,xor p6 s'.2,xor p3 s'.1]) = true)
    (c3 : let s := S0 [xor p7 a1,xor p4 a2,xor p8 a3,xor p5 a4]
          let s' := S1 [xor p8 a5,xor p5 a6,xor p7 a7,xor p4 a8]
          has T.r2s1 (bitsNat [xor p6 s'.2,xor p3 s'.1,xor p1 s.1,xor p2 s.2]) = true)
    (h0 : f0 (bitsNat [p7,p4,p8,p5]) =
      let s := S0 [xor p7 a1,xor p4 a2,xor p8 a3,xor p5 a4]; [s.1,s.2])
    (h1 : f1 (bitsNat [p8,p5,p7,p4]) =
      let s := S1 [xor p8 a5,xor p5 a6,xor p7 a7,xor p4 a8]; [s.1,s.2])
    (h2 : let s := S0 [xor p7 a1,xor p4 a2,xor p8 a3,xor p5 a4]
          let s' := S1 [xor p8 a5,xor p5 a6,xor p7 a7,xor p4 a8]
          let j := [xor p1 s.1,xor p2 s.2,xor p6 s'.2,xor p3 s'.1]
          let t := S0 (xorL j [b1,b2,b3,b4])
          f2 (bitsNat j) = [t.1,t.2])
    (h3 : let s := S0 [xor p7 a1,xor p4 a2,xor p8 a3,xor p5 a4]
          let s' := S1 [xor p8 a5,xor p5 a6,xor p7 a7,xor p4 a8]
          let j := [xor p6 s'.2,xor p3 s'.1,xor p1 s.1,xor p2 s.2]
          let t := S1 (xorL j [b5,b6,b7,b8])
          f3 (bitsNat j) = [t.1,t.2]) :
    emulate T [p1,p2,p3,p4,p5,p6,p7,p8] =
      encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8] [b1,b2,b3,b4,b5,b6,b7,b8]
        [p1,p2,p3,p4,p5,p6,p7,p8] := by
  apply emulate_of_lookups S0 S1 T a1 a2 a3 a4 a5 a6 a7 a8
    b1 b2 b3 b4 b5 b6 b7 b8 p1 p2 p3 p4 p5 p6 p7 p8
  · exact (look_of_valid _ f0 _ v0 c0).trans h0
  · exact (look_of_valid _ f1 _ v1 c1).trans h1
  · exact (look_of_valid _ f2 _ v2 c2).trans h2
  · exact (look_of_valid _ f3 _ v3 c3).trans h3

theorem bitsNat_four_lt (a b c d : Bool) : bitsNat [a,b,c,d] < 16 := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [bitsNat]

/-- Symbolic recovery for arbitrary S-boxes, explicit subkeys, and plaintext. -/
theorem attack_correct_bits (S0 S1 : Bits -> Bool × Bool)
    (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
     p1 p2 p3 p4 p5 p6 p7 p8 : Bool) :
    let oracle := encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8]
      [b1,b2,b3,b4,b5,b6,b7,b8]
    emulate (attack oracle).1 [p1,p2,p3,p4,p5,p6,p7,p8] =
      oracle [p1,p2,p3,p4,p5,p6,p7,p8] := by
  let oracle := encSub S0 S1 [a1,a2,a3,a4,a5,a6,a7,a8] [b1,b2,b3,b4,b5,b6,b7,b8]
  let T := (attack oracle).1
  have hv := attack_tables_valid S0 S1 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
  change emulate T [p1,p2,p3,p4,p5,p6,p7,p8] = oracle [p1,p2,p3,p4,p5,p6,p7,p8]
  apply emulate_of_table_validity S0 S1 T a1 a2 a3 a4 a5 a6 a7 a8
    b1 b2 b3 b4 b5 b6 b7 b8 p1 p2 p3 p4 p5 p6 p7 p8
    (effectiveTable S0 a1 a2 a3 a4) (effectiveTable S1 a5 a6 a7 a8)
    (effectiveTable S0 b1 b2 b3 b4) (effectiveTable S1 b5 b6 b7 b8)
  · exact hv.1
  · exact hv.2.1
  · exact hv.2.2.1
  · exact hv.2.2.2
  · exact (attack_r1_coverage oracle _ (bitsNat_four_lt _ _ _ _)).1
  · exact (attack_r1_coverage oracle _ (bitsNat_four_lt _ _ _ _)).2
  · exact attack_r2s0_coverage S0 S1 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 _ (bitsNat_four_lt _ _ _ _)
  · exact attack_r2s1_coverage S0 S1 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 _ (bitsNat_four_lt _ _ _ _)
  all_goals simp only [effectiveTable, natBits_bitsNat_four, xorL, List.zipWith]

theorem bits_length_eight (bits : Bits) (h : bits.length = 8) :
    ∃ a b c d e f g h, bits = [a,b,c,d,e,f,g,h] := by
  cases bits with
  | nil => simp at h
  | cons a bits =>
    simp only [List.length_cons, Nat.succ.injEq] at h
    cases bits with
    | nil => simp at h
    | cons b bits =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      cases bits with
      | nil => simp at h
      | cons c bits =>
        simp only [List.length_cons, Nat.succ.injEq] at h
        cases bits with
        | nil => simp at h
        | cons d bits =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          cases bits with
          | nil => simp at h
          | cons e bits =>
            simp only [List.length_cons, Nat.succ.injEq] at h
            cases bits with
            | nil => simp at h
            | cons f bits =>
              simp only [List.length_cons, Nat.succ.injEq] at h
              cases bits with
              | nil => simp at h
              | cons g bits =>
                simp only [List.length_cons, Nat.succ.injEq] at h
                cases bits with
                | nil => simp at h
                | cons z bits =>
                  simp only [List.length_cons, Nat.succ.injEq] at h
                  have he : bits = [] := List.length_eq_zero_iff.mp h
                  subst bits
                  exact ⟨a,b,c,d,e,f,g,z,rfl⟩

/-- Universal correctness for lists of the required lengths. -/
theorem attack_correct_universal (S0 S1 : Bits -> Bool × Bool)
    (k1 k2 pt : Bits) (hk1 : k1.length = 8) (hk2 : k2.length = 8)
    (hpt : pt.length = 8) :
    emulate (attack (encSub S0 S1 k1 k2)).1 pt = encSub S0 S1 k1 k2 pt := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,rfl⟩ := bits_length_eight k1 hk1
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,rfl⟩ := bits_length_eight k2 hk2
  obtain ⟨p1,p2,p3,p4,p5,p6,p7,p8,rfl⟩ := bits_length_eight pt hpt
  exact attack_correct_bits S0 S1 a1 a2 a3 a4 a5 a6 a7 a8
    b1 b2 b3 b4 b5 b6 b7 b8 p1 p2 p3 p4 p5 p6 p7 p8

/-! ## Finite verification for the standard S-boxes -/

def stdEnc (k : Nat) : Bits → Bits :=
  enc (sboxOf S0tab) (sboxOf S1tab) (natBits k 10)

/-- Attack succeeds for key k: emulator agrees with cipher on all 256 plaintexts. -/
def keyOK (k : Nat) : Bool :=
  let T := (attack (stdEnc k)).1
  (List.range 256).all fun p => emulate T (natBits p 8) == stdEnc k (natBits p 8)

def queries (k : Nat) : Nat := (attack (stdEnc k)).2



/-! ## Theorem 2: symbolic correctness and the standard-key corollary -/

theorem natBits_length (n len : Nat) : (natBits n len).length = len := by
  simp [natBits]

theorem genKeys_lengths (key : Bits) :
    (genKeys key).1.length = 8 /\ (genKeys key).2.length = 8 := by
  simp [genKeys, perm, P8]

theorem attack_correct_all_keys : (List.range 1024).all keyOK = true := by
  apply List.all_eq_true.mpr
  intro k hk
  unfold keyOK
  apply List.all_eq_true.mpr
  intro p hp
  apply beq_iff_eq.mpr
  have hkeys := genKeys_lengths (natBits k 10)
  have h := attack_correct_universal (sboxOf S0tab) (sboxOf S1tab)
    (genKeys (natBits k 10)).1 (genKeys (natBits k 10)).2 (natBits p 8)
    hkeys.1 hkeys.2 (natBits_length p 8)
  have horacle : stdEnc k = encSub (sboxOf S0tab) (sboxOf S1tab)
      (genKeys (natBits k 10)).1 (genKeys (natBits k 10)).2 := by
    funext pt
    rfl
  rw [horacle]
  exact h

/-! ## Theorem 3: query-count claims from the paper (Table 1, standard S-boxes) -/

theorem total_queries :
    (List.range 1024).foldl (fun a k => a + queries k) 0 = 20288 := by   -- 20288/1024 = 19.8125
  native_decide

theorem max_queries :
    (List.range 1024).foldl (fun a k => max a (queries k)) 0 = 21 := by
  native_decide

theorem min_queries :
    (List.range 1024).foldl (fun a k => min a (queries k)) 1000 = 18 := by
  native_decide

#print axioms tableValid_cons
#print axioms look_of_valid
#print axioms foldl_preserves
#print axioms extract_preserves_indices
#print axioms extract_fold_preserves_indices
#print axioms extract_fold_valid_r2s0
#print axioms extract_fold_lookup_r2s0
#print axioms extract_fold_valid_r1s0
#print axioms extract_fold_lookup_r1s0
#print axioms extract_fold_valid_r1s1
#print axioms extract_fold_lookup_r1s1
#print axioms extract_fold_valid_r2s1
#print axioms extract_fold_lookup_r2s1
#print axioms foldl_mem_establishes
#print axioms fill_missing_indices
#print axioms phase2Step_inserts
#print axioms phase2Step_inserts_index
#print axioms attack_r1_coverage
#print axioms attack_r2s0_coverage
#print axioms extract_preserves_pairing
#print axioms phase1_paired
#print axioms attack_paired
#print axioms swapIndex_properties
#print axioms attack_r2s1_coverage
#print axioms phase1_coverage
#print axioms phase1_base
#print axioms phase1_cipher_base
#print axioms bitsNat_natBits_four
#print axioms forge_inserts
#print axioms missing_indices_iff
#print axioms natBits_bitsNat_four
#print axioms extract_valid_r1s0
#print axioms extract_valid_r1s1
#print axioms extract_valid_r2s0
#print axioms extract_valid_r2s1
#print axioms extract_symbolic
#print axioms forge_plaintext
#print axioms forge_targets
#print axioms attack_tables_valid
#print axioms attack_correct_bits
#print axioms attack_correct_universal
#print axioms emulate_of_lookups
#print axioms emulate_of_table_validity
#print axioms structural
#print axioms attack_correct_all_keys

end SDES

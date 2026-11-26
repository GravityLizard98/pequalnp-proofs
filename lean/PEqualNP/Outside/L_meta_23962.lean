import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23962

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

def dg : Gate := ⟨GateOp.or, []⟩

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_last {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k = l.length) :
    (l ++ [b]).getD k d = b := by
  subst hk; simp [List.getD_eq_getElem?_getD]

theorem getD_left {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k < l.length) :
    (l ++ [b]).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem snoc_fold (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl stp x =
      gs.foldl stp x ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stp x).getD i false)] := by
  simp [List.foldl_append, stp]

theorem pre (gs hs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length + gs.length) :
    ((gs ++ hs).foldl stp x).getD w false = (gs.foldl stp x).getD w false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, snoc_fold, getD_snoc, len, ifp (by simp; omega), ih]

theorem inp (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (gs.foldl stp x).getD w false = x.getD w false := by
  have := pre [] gs x w (by simpa using hw)
  simpa using this

theorem top (gs : List Gate) (g : Gate) (x : List Bool) :
    ((gs ++ [g]).foldl stp x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl stp x).getD i false) := by
  rw [snoc_fold, getD_snoc, len, ifn (by omega), ifp rfl]

theorem beyond (gs : List Gate) (x : List Bool) (w : ℕ) (hw : x.length + gs.length ≤ w) :
    (gs.foldl stp x).getD w false = false := by
  apply List.getD_eq_default
  rw [len]; exact hw

theorem wire_at (gs : List Gate) (x : List Bool) : ∀ i, i < gs.length →
    (gs.foldl stp x).getD (x.length + i) false =
      (gs.getD i dg).op.eval ((gs.getD i dg).inputs.map fun w =>
        if w < x.length + i then (gs.foldl stp x).getD w false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; simp at hi
  | append_singleton gs g ih =>
    intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases h : i < gs.length
    · rw [pre gs [g] x _ (by omega), ih i h, getD_left gs g dg i h]
      congr 1
      apply List.map_congr_left
      intro w _
      split_ifs with hw
      · rw [pre gs [g] x _ (by omega)]
      · rfl
    · have hi' : i = gs.length := by omega
      subst hi'
      rw [top, getD_last gs g dg _ rfl]
      congr 1
      apply List.map_congr_left
      intro w _
      split_ifs with hw
      · rw [pre gs [g] x _ hw]
      · rw [beyond gs x w (by omega)]

theorem wire_ok (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < gs.length)
    (hin : ∀ w ∈ (gs.getD i dg).inputs, w < x.length + i) :
    (gs.foldl stp x).getD (x.length + i) false =
      (gs.getD i dg).op.eval ((gs.getD i dg).inputs.map fun w => (gs.foldl stp x).getD w false) := by
  rw [wire_at gs x i hi]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [ifp (hin w hw)]

theorem wire_okN (N : ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = N) (i : ℕ)
    (hi : i < gs.length) (hin : ∀ w ∈ (gs.getD i dg).inputs, w < N + i) :
    (gs.foldl stp x).getD (N + i) false =
      (gs.getD i dg).op.eval ((gs.getD i dg).inputs.map fun w => (gs.foldl stp x).getD w false) := by
  subst hx
  exact wire_ok gs x i hi hin

theorem set_ne (gs : List Gate) (a b : ℕ) (g : Gate) (h : a ≠ b) :
    (gs.set a g).getD b dg = gs.getD b dg := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem set_eq (gs : List Gate) (a : ℕ) (g : Gate) (h : a < gs.length) :
    (gs.set a g).getD a dg = g := by
  simp [List.getD_eq_getElem?_getD, h]

def rho (N j B : ℕ) (i : ℕ) : ℕ := if i < N + j then i else if i = N + j then B else i - 1

def rg (N j B : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho N j B)⟩

theorem phase1 (N j B : ℕ) (x : List Bool) (hx : x.length = N) (hB : N + j ≤ B) :
    ∀ A : List Gate, A.length ≤ j → (A.map (rg N j B)).foldl stp x = A.foldl stp x := by
  intro A
  induction A using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton A g ih =>
    intro hA
    rw [List.length_append, List.length_singleton] at hA
    rw [List.map_append, List.map_singleton, snoc_fold, snoc_fold, ih (by omega)]
    congr 2
    show g.op.eval ((g.inputs.map (rho N j B)).map fun i => (A.foldl stp x).getD i false) = _
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    show (A.foldl stp x).getD (rho N j B i) false = (A.foldl stp x).getD i false
    unfold rho
    split_ifs with h1 h2
    · rfl
    · rw [beyond _ _ _ (by omega), beyond _ _ _ (by omega)]
    · rw [beyond _ _ _ (by omega), beyond _ _ _ (by omega)]

theorem phase2 (N j B : ℕ) (wA : List Bool) (hw : wA.length = N + j) :
    ∀ Bs : List Gate, N + j + Bs.length ≤ B → ∀ i,
      ((Bs.map (rg N j B)).foldl stp wA).getD (rho N j B i) false =
        (Bs.foldl stp (wA ++ [false])).getD i false := by
  intro Bs
  induction Bs using List.reverseRecOn with
  | nil =>
    intro hB i
    simp only [List.map_nil, List.foldl_nil]
    unfold rho
    split_ifs with h1 h2
    · rw [getD_left _ _ _ _ (by omega)]
    · rw [getD_last _ _ _ _ (by omega)]
      exact List.getD_eq_default _ _ (by omega)
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
  | append_singleton Bs g ih =>
    intro hB i
    rw [List.length_append, List.length_singleton] at hB
    have ih' := ih (by omega)
    have hv : (rg N j B g).op.eval ((rg N j B g).inputs.map fun i =>
        ((Bs.map (rg N j B)).foldl stp wA).getD i false) =
        g.op.eval (g.inputs.map fun i => (Bs.foldl stp (wA ++ [false])).getD i false) := by
      show g.op.eval ((g.inputs.map (rho N j B)).map fun i =>
        ((Bs.map (rg N j B)).foldl stp wA).getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ih' i
    rw [List.map_append, List.map_singleton, snoc_fold, snoc_fold, hv, getD_snoc, getD_snoc,
      len, len, List.length_map, List.length_append, List.length_singleton]
    simp only [hw]
    have hi := ih' i
    rcases Nat.lt_trichotomy i (N + j) with h | h | h
    · have hr : rho N j B i = i := by unfold rho; rw [ifp h]
      rw [hr] at hi ⊢
      rw [ifp (by omega), ifp (by omega)]
      exact hi
    · have hr : rho N j B i = B := by unfold rho; rw [ifn (by omega), ifp h]
      rw [hr] at hi ⊢
      rw [ifn (by omega), ifn (by omega), ifp (by omega), ← hi]
      symm
      exact List.getD_eq_default _ _ (by rw [len, hw, List.length_map]; omega)
    · have hr : rho N j B i = i - 1 := by unfold rho; rw [ifn (by omega), ifn (by omega)]
      rw [hr] at hi ⊢
      by_cases h2 : i < N + j + 1 + Bs.length
      · rw [ifp (by omega), ifp h2]
        exact hi
      · by_cases h3 : i = N + j + 1 + Bs.length
        · rw [ifn (by omega), ifp (by omega), ifn h2, ifp h3]
        · rw [ifn (by omega), ifn (by omega), ifn h2, ifn h3]

theorem elim (N j : ℕ) (gs : List Gate) (hj : j < gs.length) (out : ℕ) (x : List Bool)
    (hx : x.length = N) :
    (((gs.take j ++ gs.drop (j + 1)).map (rg N j (N + gs.length))).foldl stp x).getD
        (rho N j (N + gs.length) out) false =
      ((gs.set j dg).foldl stp x).getD out false := by
  rw [List.set_eq_take_append_cons_drop, ifp hj, List.map_append, List.foldl_append,
    List.foldl_append, List.foldl_cons,
    phase1 N j _ x hx (by omega) (gs.take j) (by rw [List.length_take]; omega)]
  have hd : stp ((gs.take j).foldl stp x) dg = (gs.take j).foldl stp x ++ [false] := rfl
  rw [hd]
  exact phase2 N j _ _ (by rw [len, hx, List.length_take]; omega) (gs.drop (j + 1))
    (by rw [List.length_drop]; omega) out

theorem agree (N : ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = N) (j0 : ℕ)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (bad : ℕ → Prop) (st : ℕ)
    (hbad0 : j0 ≠ st → bad (N + j0))
    (hread : ∀ j < gs.length, j ≠ st → ¬ bad (N + j) → ∀ i ∈ (gs.getD j dg).inputs, ¬ bad i)
    (hst : st < gs.length → (∀ w < N + st, ¬ bad w →
        (gs.foldl stp x).getD w false = ((gs.set j0 dg).foldl stp x).getD w false) →
      (gs.foldl stp x).getD (N + st) false = ((gs.set j0 dg).foldl stp x).getD (N + st) false) :
    ∀ w, ¬ bad w →
      (gs.foldl stp x).getD w false = ((gs.set j0 dg).foldl stp x).getD w false := by
  subst hx
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hb
    by_cases h1 : w < x.length
    · rw [inp _ _ _ h1, inp _ _ _ h1]
    · by_cases h2 : x.length + gs.length ≤ w
      · rw [beyond _ _ _ h2, beyond _ _ _ (by rw [List.length_set]; exact h2)]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h1)
        have hj : j < gs.length := by omega
        by_cases hs : j = st
        · subst hs; exact hst hj (fun w hw hb => ih w hw hb)
        · have hj0 : j0 ≠ j := by
            intro e; subst e; exact hb (hbad0 hs)
          have e := set_ne gs j0 j dg hj0
          rw [wire_ok gs x j hj (RB j hj), wire_ok (gs.set j0 dg) x j
            (by rw [List.length_set]; exact hj) (by rw [e]; exact RB j hj), e]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact ih i (RB j hj i hi) (hread j hj hs hb i hi)

theorem cnt_reads (C : Circuit) (n : ℕ) (w g1 : ℕ) (h1 : g1 < n) :
    (gateAt C g1).inputs.count w ≤ readsIn C (Finset.range n) w := by
  unfold readsIn
  exact Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count w)
    (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr h1)

theorem two_reads (C : Circuit) (n : ℕ) (w g1 g2 : ℕ) (h1 : g1 < n) (h2 : g2 < n) (hne : g1 ≠ g2)
    (m1 : w ∈ (gateAt C g1).inputs) (m2 : w ∈ (gateAt C g2).inputs) :
    2 ≤ readsIn C (Finset.range n) w := by
  unfold readsIn
  have hs : ({g1, g2} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr ‹_›
  have := Finset.sum_le_sum_of_subset (f := fun j => (gateAt C j).inputs.count w) hs
  rw [Finset.sum_pair hne] at this
  have a1 := List.count_pos_iff.mpr m1
  have a2 := List.count_pos_iff.mpr m2
  omega

theorem main : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents A C →
  (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
    PEqualNP.Represents.Represents A D → C.size ≤ D.size) →
  ∀ (p : List ℕ) (i2 i3 qa qb qc : ℕ) (Pa Pb Pc : Finset ℕ),
  0 < i2 → i2 < i3 → i3 < p.length →
  (∀ k < p.length, p.getD k 0 < C.size) →
  (∀ k, k + 1 < p.length →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + m + p.getD k 0) = 1 ∧
    C.output ≠ n + m + p.getD k 0 ∧
    n + m + p.getD k 0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD (k + 1) 0)).inputs) →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD 0 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  qa ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD 0 0)).inputs →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).inputs = [n + m + p.getD (i2 - 1) 0, qb] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).inputs = [qb, n + m + p.getD (i2 - 1) 0]) →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).inputs = [n + m + p.getD (i3 - 1) 0, qc] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).inputs = [qc, n + m + p.getD (i3 - 1) 0]) →
  Disjoint Pa Pb → Disjoint Pa Pc → Disjoint Pb Pc →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qa false = true →
    (u : ℕ) ∈ Pa ∨ n + (v : ℕ) ∈ Pa) →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qb false = true →
    (u : ℕ) ∈ Pb ∨ n + (v : ℕ) ∈ Pb) →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qc false = true →
    (u : ℕ) ∈ Pc ∨ n + (v : ℕ) ∈ Pc) →
  False := by
  intro n m A C hF hRB hrep hmin p i2 i3 qa qb qc Pa Pb Pc h0 h23 h3L hpl hch hopa hqa hopb hinb hopc hinc dab dac dbc hPa hPb hPc
  have RB : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j dg).inputs, i < n + m + j := hRB
  have hmono1 : ∀ k, k + 1 < p.length → p.getD k 0 < p.getD (k + 1) 0 := by
    intro k hk
    have := RB _ (hpl (k + 1) hk) _ (hch k hk).2.2
    omega
  have hmono : ∀ l k, k < l → l < p.length → p.getD k 0 < p.getD l 0 := by
    intro l
    induction l with
    | zero => intro k hk; omega
    | succ l ih =>
      intro k hk hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact lt_trans (ih k h (by omega)) (hmono1 l hl)
      · subst h; exact hmono1 k hl
  have hr1 : ∀ k, k + 1 < p.length → ∀ j < C.gates.length,
      (n + m + p.getD k 0) ∈ (C.gates.getD j dg).inputs → j = p.getD (k + 1) 0 := by
    intro k hk j hj hmem
    by_contra hne
    have h2 := two_reads C C.size _ j (p.getD (k + 1) 0) hj (hpl _ hk) hne hmem (hch k hk).2.2
    have h1 := (hch k hk).1
    omega
  have hxl : ∀ (u : Fin n) (v : Fin m), (oneEach u v).length = n + m := by
    intro u v; simp [oneEach]
  have hCA : ∀ (u : Fin n) (v : Fin m) (t : ℕ), t < p.length →
      ((∀ w < n + m + p.getD t 0, (¬ ∃ k < t, w = n + m + p.getD k 0) →
        (C.gates.foldl stp (oneEach u v)).getD w false =
          ((C.gates.set (p.getD 0 0) dg).foldl stp (oneEach u v)).getD w false) →
        (C.gates.foldl stp (oneEach u v)).getD (n + m + p.getD t 0) false =
          ((C.gates.set (p.getD 0 0) dg).foldl stp (oneEach u v)).getD (n + m + p.getD t 0) false) →
      (C.gates.foldl stp (oneEach u v)).getD C.output false =
        ((C.gates.set (p.getD 0 0) dg).foldl stp (oneEach u v)).getD C.output false := by
    intro u v t ht hst
    refine agree (n + m) C.gates (oneEach u v) (hxl u v) (p.getD 0 0) RB
      (fun w => ∃ k < t, w = n + m + p.getD k 0) (p.getD t 0) ?_ ?_ (fun _ => hst) C.output ?_
    · intro hne
      refine ⟨0, ?_, rfl⟩
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact absurd rfl hne
      · exact h
    · intro j hj hjt hnb i hi hbi
      obtain ⟨k, hk, rfl⟩ := hbi
      have hjk := hr1 k (by omega) j hj hi
      rcases Nat.lt_or_ge (k + 1) t with h | h
      · exact hnb ⟨k + 1, h, by rw [hjk]⟩
      · have hkt : k + 1 = t := by omega
        subst hkt
        exact hjt hjk
    · intro hbo
      obtain ⟨k, hk, hout⟩ := hbo
      exact (hch k (by omega)).2.1 hout
  have hAND : ∀ (u : Fin n) (v : Fin m) (t q : ℕ), 0 < t → t < p.length →
      (C.gates.getD (p.getD t 0) dg).op = GateOp.and →
      ((C.gates.getD (p.getD t 0) dg).inputs = [n + m + p.getD (t - 1) 0, q] ∨
        (C.gates.getD (p.getD t 0) dg).inputs = [q, n + m + p.getD (t - 1) 0]) →
      (C.gates.foldl stp (oneEach u v)).getD q false = false →
      (C.gates.foldl stp (oneEach u v)).getD C.output false =
        ((C.gates.set (p.getD 0 0) dg).foldl stp (oneEach u v)).getD C.output false := by
    intro u v t q ht0 ht hop hin hq
    apply hCA u v t ht
    intro ih
    have hjt := hpl t ht
    have hqin : q ∈ (C.gates.getD (p.getD t 0) dg).inputs := by
      rcases hin with h | h <;> (rw [h]; simp)
    have hqlt := RB _ hjt q hqin
    have hqnb : ¬ ∃ k < t, q = n + m + p.getD k 0 := by
      intro hex
      obtain ⟨k, hk, hqk⟩ := hex
      subst hqk
      have hk1 : k + 1 < p.length := by omega
      have hjk := hr1 k hk1 _ hjt hqin
      rcases Nat.lt_or_ge (k + 1) t with h | h
      · have := hmono t (k + 1) h ht
        omega
      · have hkt : k + 1 = t := by omega
        subst hkt
        have hc2 : 2 ≤ (C.gates.getD (p.getD (k + 1) 0) dg).inputs.count (n + m + p.getD k 0) := by
          rcases hin with h | h <;> (rw [h]; simp)
        have h3 := cnt_reads C C.size (n + m + p.getD k 0) (p.getD (k + 1) 0) hjt
        have h1 := (hch k hk1).1
        have h3' : (C.gates.getD (p.getD (k + 1) 0) dg).inputs.count (n + m + p.getD k 0) ≤
          readsIn C (Finset.range C.size) (n + m + p.getD k 0) := h3
        omega
    have hq' := ih q hqlt hqnb
    have hne : p.getD 0 0 ≠ p.getD t 0 := by
      have := hmono t 0 ht0 ht
      omega
    have e := set_ne C.gates (p.getD 0 0) (p.getD t 0) dg hne
    rw [wire_okN (n + m) C.gates _ (hxl u v) _ hjt (RB _ hjt),
      wire_okN (n + m) (C.gates.set _ dg) _ (hxl u v) _ (by rw [List.length_set]; exact hjt)
        (by rw [e]; exact RB _ hjt), e, hop]
    have hq2 := hq'.symm.trans hq
    rcases hin with h | h <;> (rw [h]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, hq, hq2, Bool.and_false, Bool.false_and, Bool.and_true])
  have hA0 : ∀ (u : Fin n) (v : Fin m),
      (C.gates.foldl stp (oneEach u v)).getD qa false = false →
      (C.gates.foldl stp (oneEach u v)).getD C.output false =
        ((C.gates.set (p.getD 0 0) dg).foldl stp (oneEach u v)).getD C.output false := by
    intro u v hq
    apply hCA u v 0 (by omega)
    intro _
    have hj0 := hpl 0 (by omega)
    have e0 := set_eq C.gates (p.getD 0 0) dg hj0
    have hopa' : (C.gates.getD (p.getD 0 0) dg).op = GateOp.and := hopa
    have hqa' : qa ∈ (C.gates.getD (p.getD 0 0) dg).inputs := hqa
    rw [wire_okN (n + m) C.gates _ (hxl u v) _ hj0 (RB _ hj0),
      wire_okN (n + m) (C.gates.set _ dg) _ (hxl u v) _ (by rw [List.length_set]; exact hj0)
        (by rw [e0]; intro w hw; simp [dg] at hw), e0, hopa']
    show GateOp.and.eval _ = GateOp.or.eval []
    show List.all _ id = false
    rw [List.all_eq_false]
    exact ⟨false, List.mem_map.mpr ⟨qa, hqa', hq⟩, by simp⟩
  have hj0 := hpl 0 (by omega)
  have hj0' : p.getD 0 0 < C.gates.length := hj0
  have hFD : PEqualNP.MetaComplexity.FanInTwo
      (⟨(C.gates.take (p.getD 0 0) ++ C.gates.drop (p.getD 0 0 + 1)).map
        (rg (n + m) (p.getD 0 0) (n + m + C.gates.length)),
        rho (n + m) (p.getD 0 0) (n + m + C.gates.length) C.output⟩ : Circuit) := by
    intro g hg
    have hg' : g ∈ (C.gates.take (p.getD 0 0) ++ C.gates.drop (p.getD 0 0 + 1)).map
        (rg (n + m) (p.getD 0 0) (n + m + C.gates.length)) := hg
    rw [List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    rw [List.mem_append] at hg0
    have hm : g0 ∈ C.gates := by
      rcases hg0 with h | h
      · exact List.mem_of_mem_take h
      · exact List.mem_of_mem_drop h
    have hf := hF g0 hm
    refine ⟨hf.1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact hf.2
  have hRD : Represents A
      (⟨(C.gates.take (p.getD 0 0) ++ C.gates.drop (p.getD 0 0 + 1)).map
        (rg (n + m) (p.getD 0 0) (n + m + C.gates.length)),
        rho (n + m) (p.getD 0 0) (n + m + C.gates.length) C.output⟩ : Circuit) := by
    intro u v
    show (((C.gates.take (p.getD 0 0) ++ C.gates.drop (p.getD 0 0 + 1)).map
        (rg (n + m) (p.getD 0 0) (n + m + C.gates.length))).foldl stp (oneEach u v)).getD
        (rho (n + m) (p.getD 0 0) (n + m + C.gates.length) C.output) false = A u v
    rw [elim (n + m) (p.getD 0 0) C.gates hj0' C.output (oneEach u v) (hxl u v)]
    have hr : (C.gates.foldl stp (oneEach u v)).getD C.output false = A u v := hrep u v
    rw [← hr]
    symm
    by_cases hc : (C.gates.foldl stp (oneEach u v)).getD qc false = false
    · exact hAND u v i3 qc (by omega) h3L hopc hinc hc
    · by_cases hb : (C.gates.foldl stp (oneEach u v)).getD qb false = false
      · exact hAND u v i2 qb h0 (by omega) hopb hinb hb
      · apply hA0 u v
        by_contra ha
        have a1 := hPa u v (show (C.gates.foldl stp (oneEach u v)).getD qa false = true from by revert ha; cases (C.gates.foldl stp (oneEach u v)).getD qa false <;> simp)
        have b1 := hPb u v (show (C.gates.foldl stp (oneEach u v)).getD qb false = true from by revert hb; cases (C.gates.foldl stp (oneEach u v)).getD qb false <;> simp)
        have c1 := hPc u v (show (C.gates.foldl stp (oneEach u v)).getD qc false = true from by revert hc; cases (C.gates.foldl stp (oneEach u v)).getD qc false <;> simp)
        rw [Finset.disjoint_left] at dab dac dbc
        rcases a1 with a1 | a1 <;> rcases b1 with b1 | b1 <;> rcases c1 with c1 | c1 <;>
          first | exact dab a1 b1 | exact dac a1 c1 | exact dbc b1 c1
  have hsz := hmin _ hFD hRD
  have hsz' : C.gates.length ≤ ((C.gates.take (p.getD 0 0) ++ C.gates.drop (p.getD 0 0 + 1)).map
        (rg (n + m) (p.getD 0 0) (n + m + C.gates.length))).length := hsz
  rw [List.length_map, List.length_append, List.length_take, List.length_drop] at hsz'
  omega

end PEqualNP.Outside.L_meta_23962

theorem PEqualNP.Outside.L_meta_23962 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents A C →
  (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
    PEqualNP.Represents.Represents A D → C.size ≤ D.size) →
  ∀ (p : List ℕ) (i2 i3 qa qb qc : ℕ) (Pa Pb Pc : Finset ℕ),
  0 < i2 → i2 < i3 → i3 < p.length →
  (∀ k < p.length, p.getD k 0 < C.size) →
  (∀ k, k + 1 < p.length →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + m + p.getD k 0) = 1 ∧
    C.output ≠ n + m + p.getD k 0 ∧
    n + m + p.getD k 0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD (k + 1) 0)).inputs) →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD 0 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  qa ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD 0 0)).inputs →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).inputs = [n + m + p.getD (i2 - 1) 0, qb] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).inputs = [qb, n + m + p.getD (i2 - 1) 0]) →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).inputs = [n + m + p.getD (i3 - 1) 0, qc] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).inputs = [qc, n + m + p.getD (i3 - 1) 0]) →
  Disjoint Pa Pb → Disjoint Pa Pc → Disjoint Pb Pc →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qa false = true →
    (u : ℕ) ∈ Pa ∨ n + (v : ℕ) ∈ Pa) →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qb false = true →
    (u : ℕ) ∈ Pb ∨ n + (v : ℕ) ∈ Pb) →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qc false = true →
    (u : ℕ) ∈ Pc ∨ n + (v : ℕ) ∈ Pc) →
  False :=
  PEqualNP.Outside.L_meta_23962.main

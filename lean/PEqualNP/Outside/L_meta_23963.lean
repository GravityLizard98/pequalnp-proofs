import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23963

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def dg : Gate := ⟨GateOp.or, []⟩

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def M2 (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

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

def leafF (i : ℕ) : ℕ → List Gate × ℕ := fun _ => ([], i)

def nodeF (op : GateOp) (f g : ℕ → List Gate × ℕ) : ℕ → List Gate × ℕ := fun base =>
  ((f base).1 ++ (g (base + (f base).1.length)).1 ++
      [⟨op, [(f base).2, (g (base + (f base).1.length)).2]⟩],
    base + (f base).1.length + (g (base + (f base).1.length)).1.length)

def cnt (G : List Gate) (w : ℕ) : ℕ := (G.map (fun g => g.inputs.count w)).sum

def Spec (m : ℕ) (f : ℕ → List Gate × ℕ) (L : List ℕ) (ev : List Bool → Bool) (sz : ℕ) : Prop :=
  L.length = sz + 1 ∧ (∀ i ∈ L, i < m) ∧
  (∀ W W' : List Bool, (∀ i < m, W.getD i false = W'.getD i false) → ev W = ev W') ∧
  ∀ base, m ≤ base →
    (f base).1.length = sz ∧
    (∀ g ∈ (f base).1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    (∀ k < sz, ∀ i ∈ ((f base).1.getD k dg).inputs, i < base + k) ∧
    (f base).2 < base + sz ∧ (1 ≤ sz → (f base).2 + 1 = base + sz) ∧
    (∀ w, cnt (f base).1 w + (if (f base).2 = w then 1 else 0) =
      if (w ∈ L ∨ (base ≤ w ∧ w < base + sz)) then 1 else 0) ∧
    (∀ W : List Bool, W.length = base → ((f base).1.foldl stp W).getD (f base).2 false = ev W)

theorem gA {α : Type} (l1 l2 : List α) (k : ℕ) (d : α) (h : k < l1.length) :
    (l1 ++ l2).getD k d = l1.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gB {α : Type} (l1 l2 : List α) (k : ℕ) (d : α) (h : l1.length ≤ k) :
    (l1 ++ l2).getD k d = l2.getD (k - l1.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem spec_leaf (m i : ℕ) (hi : i < m) : Spec m (leafF i) [i] (fun W => W.getD i false) 0 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro k hk
    rw [List.mem_singleton] at hk
    omega
  · intro W W' h
    exact h i hi
  · intro base hb
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp [leafF] at hg
    · intro k hk
      omega
    · show i < base + 0
      omega
    · intro h
      omega
    · intro w
      show cnt [] w + (if i = w then 1 else 0) = _
      by_cases h : i = w
      · subst h
        simp [cnt]
      · have h' : ¬ w = i := fun e => h e.symm
        simp [cnt, h, h']
    · intro W _
      rfl

theorem spec_node (m : ℕ) (op : GateOp) (f g : ℕ → List Gate × ℕ) (L1 L2 : List ℕ)
    (e1 e2 : List Bool → Bool) (s1 s2 : ℕ) (hop : op = GateOp.and ∨ op = GateOp.or)
    (h1 : Spec m f L1 e1 s1) (h2 : Spec m g L2 e2 s2) (hd : ∀ i, i ∈ L1 → i ∈ L2 → False) :
    Spec m (nodeF op f g) (L1 ++ L2) (fun W => op.eval [e1 W, e2 W]) (s1 + s2 + 1) := by
  obtain ⟨l1, m1, d1, S1⟩ := h1
  obtain ⟨l2, m2, d2, S2⟩ := h2
  refine ⟨by rw [List.length_append]; omega, ?_, ?_, ?_⟩
  · intro i hi
    rw [List.mem_append] at hi
    rcases hi with h | h
    · exact m1 i h
    · exact m2 i h
  · intro W W' h
    show op.eval [e1 W, e2 W] = op.eval [e1 W', e2 W']
    rw [d1 W W' h, d2 W W' h]
  · intro base hb
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := S1 base hb
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := S2 (base + s1) (by omega)
    have eN : nodeF op f g base = ((f base).1 ++ (g (base + s1)).1 ++
        [(Gate.mk op [(f base).2, (g (base + s1)).2])], base + s1 + s2) := by
      unfold nodeF
      rw [a1, b1]
    rw [eN]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show ((f base).1 ++ (g (base + s1)).1 ++ [_]).length = _
      rw [List.length_append, List.length_append, a1, b1]
      rfl
    · intro q hq
      change q ∈ (f base).1 ++ (g (base + s1)).1 ++ [_] at hq
      rw [List.mem_append, List.mem_append, List.mem_singleton] at hq
      rcases hq with (hq | hq) | hq
      · exact a2 q hq
      · exact b2 q hq
      · rw [hq]
        exact ⟨hop, rfl⟩
    · intro k hk i hi
      change i ∈ (((f base).1 ++ (g (base + s1)).1 ++ [_]).getD k dg).inputs at hi
      by_cases hk1 : k < s1
      · rw [List.append_assoc, gA _ _ k dg (by omega)] at hi
        exact a3 k hk1 i hi
      · by_cases hk2 : k < s1 + s2
        · rw [gA _ _ k dg (by rw [List.length_append]; omega), gB _ _ k dg (by omega), a1] at hi
          have := b3 (k - s1) (by omega) i hi
          omega
        · have hk3 : k = ((f base).1 ++ (g (base + s1)).1).length := by
            rw [List.length_append]; omega
          rw [getD_last _ _ _ _ hk3] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
    · show base + s1 + s2 < base + (s1 + s2 + 1)
      omega
    · intro _
      show base + s1 + s2 + 1 = base + (s1 + s2 + 1)
      omega
    · intro w
      show cnt ((f base).1 ++ (g (base + s1)).1 ++ [(Gate.mk op [(f base).2, (g (base + s1)).2])]) w +
        (if base + s1 + s2 = w then 1 else 0) = _
      have ec : cnt ((f base).1 ++ (g (base + s1)).1 ++ [(Gate.mk op [(f base).2, (g (base + s1)).2])]) w =
          cnt (f base).1 w + cnt (g (base + s1)).1 w +
            ((if (f base).2 = w then 1 else 0) + (if (g (base + s1)).2 = w then 1 else 0)) := by
        unfold cnt
        rw [List.map_append, List.map_append, List.sum_append, List.sum_append]
        simp [List.count_cons]
        omega
      rw [ec]
      have e6 := a6 w
      have f6 := b6 w
      have q1 : w ∈ L1 → w < m := m1 w
      have q2 : w ∈ L2 → w < m := m2 w
      by_cases c1 : w ∈ L1 <;> by_cases c2 : w ∈ L2
      · exact (hd w c1 c2).elim
      · have := q1 c1
        simp only [c1, c2, List.mem_append, true_or, false_or, ite_true] at e6 f6 ⊢
        split_ifs at e6 f6 ⊢ <;> omega
      · have := q2 c2
        simp only [c1, c2, List.mem_append, true_or, false_or, or_true, ite_true] at e6 f6 ⊢
        split_ifs at e6 f6 ⊢ <;> omega
      · simp only [c1, c2, List.mem_append, false_or, or_self] at e6 f6 ⊢
        split_ifs at e6 f6 ⊢ <;> omega
    · intro W hW
      show (((f base).1 ++ (g (base + s1)).1 ++ [(Gate.mk op [(f base).2, (g (base + s1)).2])]).foldl stp W).getD
        (base + s1 + s2) false = op.eval [e1 W, e2 W]
      have hW1 : ((f base).1.foldl stp W).length = base + s1 := by rw [len, hW, a1]
      have hW2 : ((g (base + s1)).1.foldl stp ((f base).1.foldl stp W)).length = base + s1 + s2 := by
        rw [len, hW1, b1]
      rw [snoc_fold, List.foldl_append, getD_last _ _ _ _ hW2.symm]
      show op.eval [((g (base + s1)).1.foldl stp ((f base).1.foldl stp W)).getD (f base).2 false,
        ((g (base + s1)).1.foldl stp ((f base).1.foldl stp W)).getD (g (base + s1)).2 false] =
        op.eval [e1 W, e2 W]
      have v2 := b7 _ hW1
      have v1 := a7 W hW
      rw [v2, inp _ _ _ (by rw [hW1]; exact a4), v1]
      rw [d2 ((f base).1.foldl stp W) W (fun i hi => inp _ W i (by omega))]

def rd (gs : List Gate) (G : Finset ℕ) (w : ℕ) : ℕ := ∑ j ∈ G, (gs.getD j dg).inputs.count w

def fd (m : ℕ) (gs : List Gate) (a c : ℕ) : Prop :=
  ∃ j, j < gs.length ∧ c = m + j ∧ a ∈ (gs.getD j dg).inputs

theorem uniqR (gs : List Gate) (G : Finset ℕ) (w j1 j2 : ℕ) (h : rd gs G w ≤ 1) (h1 : j1 ∈ G)
    (h2 : j2 ∈ G) (m1 : w ∈ (gs.getD j1 dg).inputs) (m2 : w ∈ (gs.getD j2 dg).inputs) : j1 = j2 := by
  by_contra hne
  have hsub : ({j1, j2} : Finset ℕ) ⊆ G := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset (f := fun j => ((gs.getD j dg).inputs.count w)) hsub
  rw [Finset.sum_pair hne] at hle
  have p1 : 0 < (gs.getD j1 dg).inputs.count w := List.count_pos_iff.2 m1
  have p2 : 0 < (gs.getD j2 dg).inputs.count w := List.count_pos_iff.2 m2
  have h' : ∑ j ∈ G, (gs.getD j dg).inputs.count w ≤ 1 := h
  omega

theorem exreader (gs : List Gate) (G : Finset ℕ) (w : ℕ) (h : 1 ≤ rd gs G w) :
    ∃ j ∈ G, w ∈ (gs.getD j dg).inputs := by
  by_contra hno
  have : rd gs G w = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact List.count_eq_zero.2 (fun hm => hno ⟨j, hj, hm⟩)
  omega

theorem valgate (m : ℕ) (gs : List Gate) (j a b : ℕ) (hj : j < gs.length)
    (hab : (gs.getD j dg).inputs = [a, b]) (ha : a < m + j) (hb : b < m + j)
    (x : List Bool) (hx : x.length = m) :
    (gs.foldl stp x).getD (m + j) false =
      (gs.getD j dg).op.eval [(gs.foldl stp x).getD a false, (gs.foldl stp x).getD b false] := by
  have e := wire_at gs x j hj
  rw [hx] at e
  rw [e, hab, List.map_cons, List.map_cons, List.map_nil, ifp ha, ifp hb]

theorem depC (m : ℕ) (gs : List Gate) (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < m + j)
    (x y : List Bool) (hx : x.length = m) (hy : y.length = m) :
    ∀ w, (∀ k < m, Relation.ReflTransGen (fd m gs) k w → x.getD k false = y.getD k false) →
      (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h1 : w < m
    · rw [inp gs x w (by omega), inp gs y w (by omega)]
      exact h w h1 Relation.ReflTransGen.refl
    · by_cases h2 : m + gs.length ≤ w
      · rw [beyond gs x w (by omega), beyond gs y w (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, w = m + j := ⟨w - m, by omega⟩
        have hj : j < gs.length := by omega
        have e1 := wire_at gs x j hj
        have e2 := wire_at gs y j hj
        rw [hx] at e1
        rw [hy] at e2
        rw [e1, e2]
        congr 1
        apply List.map_congr_left
        intro c hc
        have hlt := hrb j hj c hc
        rw [ifp hlt, ifp hlt]
        exact ih c hlt (fun k hk hr => h k hk (Relation.ReflTransGen.tail hr ⟨j, hj, rfl, hc⟩))

theorem sum_getD (l : List Gate) (w : ℕ) :
    ∑ j ∈ Finset.range l.length, (l.getD j dg).inputs.count w = cnt l w := by
  induction l using List.reverseRecOn with
  | nil => simp [cnt]
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ, getD_last l a dg _ rfl]
    have e : ∑ j ∈ Finset.range l.length, ((l ++ [a]).getD j dg).inputs.count w =
        ∑ j ∈ Finset.range l.length, (l.getD j dg).inputs.count w := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [getD_left l a dg j (Finset.mem_range.1 hj)]
    rw [e, ih]
    simp [cnt]

theorem ofFn_get (m : ℕ) (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem evor (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by
  simp [GateOp.eval]

theorem evand (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by
  simp [GateOp.eval]


def V (gs : List Gate) (w : ℕ) (W : List Bool) : Bool := (gs.foldl stp W).getD w false

def Hyp2 (N : ℕ) (gs : List Gate) (j0 : ℕ) : Prop :=
  (∀ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j) ∧
  j0 < gs.length ∧
  (∀ j < gs.length, ((gs.getD j dg).op = GateOp.not ↔ j = j0)) ∧
  (∀ i < N, rd gs (Finset.range gs.length) i ≤ 1) ∧
  (∀ j < gs.length, rd gs (Finset.range gs.length) (N + j) = if j + 1 = gs.length then 0 else 1)

theorem gmem (gs : List Gate) (j : ℕ) (hj : j < gs.length) : gs.getD j dg ∈ gs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

theorem rd1 (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) (a c : ℕ) (h : fd N gs a c) :
    rd gs (Finset.range gs.length) a ≤ 1 := by
  obtain ⟨j, hj, rfl, ha⟩ := h
  have hlt := H.2.1 j hj a ha
  by_cases h1 : a < N
  · exact H.2.2.2.2.1 a h1
  · have e : a = N + (a - N) := by omega
    rw [e, H.2.2.2.2.2 (a - N) (by omega)]
    split_ifs <;> omega

theorem fdU (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) : Relator.RightUnique (fd N gs) := by
  intro a c c' h h'
  have hle := rd1 N gs j0 H a c h
  obtain ⟨j, hj, rfl, ha⟩ := h
  obtain ⟨j', hj', rfl, ha'⟩ := h'
  rw [uniqR gs (Finset.range gs.length) a j j' hle (Finset.mem_range.2 hj) (Finset.mem_range.2 hj') ha ha']

theorem fd_lt (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) (a c : ℕ) (h : fd N gs a c) :
    a < c := by
  obtain ⟨j, hj, rfl, ha⟩ := h
  exact H.2.1 j hj a ha

theorem rt_le (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) (a c : ℕ)
    (h : Relation.ReflTransGen (fd N gs) a c) : a ≤ c := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hf ih =>
    have := fd_lt N gs j0 H _ _ hf
    omega

theorem shape (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) (j : ℕ) (hj : j < gs.length)
    (hne : j ≠ j0) : ∃ a b, (gs.getD j dg).inputs = [a, b] ∧ a < N + j ∧ b < N + j ∧ a ≠ b ∧
      ((gs.getD j dg).op = GateOp.and ∨ (gs.getD j dg).op = GateOp.or) := by
  rcases H.1 _ (gmem gs j hj) with ⟨hop, hl⟩ | ⟨hop, _⟩
  · obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hl
    have ha := H.2.1 j hj a (by rw [hab]; simp)
    have hb := H.2.1 j hj b (by rw [hab]; simp)
    refine ⟨a, b, hab, ha, hb, ?_, hop⟩
    intro e
    subst e
    have hle := rd1 N gs j0 H a (N + j) ⟨j, hj, rfl, by rw [hab]; simp⟩
    have h1 := Finset.single_le_sum (f := fun j => ((gs.getD j dg).inputs.count a))
      (fun i _ => Nat.zero_le _) (Finset.mem_range.2 hj)
    simp only [hab] at h1
    have : [a, a].count a = 2 := by simp
    have hle' : ∑ j ∈ Finset.range gs.length, (gs.getD j dg).inputs.count a ≤ 1 := hle
    omega
  · exact (hne ((H.2.2.2.1 j hj).1 hop)).elim

theorem shape0 (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) :
    ∃ h0, (gs.getD j0 dg).inputs = [h0] ∧ h0 < N + j0 ∧ (gs.getD j0 dg).op = GateOp.not := by
  have hj := H.2.2.1
  have hop := (H.2.2.2.1 j0 hj).2 rfl
  rcases H.1 _ (gmem gs j0 hj) with ⟨hop', _⟩ | ⟨_, hl⟩
  · rcases hop' with h | h <;> rw [h] at hop <;> cases hop
  · obtain ⟨h0, hh⟩ := List.length_eq_one_iff.1 hl
    exact ⟨h0, hh, H.2.1 j0 hj h0 (by rw [hh]; simp), hop⟩

theorem disj (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) (j a b : ℕ) (hj : j < gs.length)
    (hab : (gs.getD j dg).inputs = [a, b]) (ha : a < N + j) (hb : b < N + j) (hne : a ≠ b) (k : ℕ)
    (h1 : Relation.ReflTransGen (fd N gs) k a) (h2 : Relation.ReflTransGen (fd N gs) k b) : False := by
  have hU := fdU N gs j0 H
  have key : ∀ c d, c ∈ (gs.getD j dg).inputs → d < N + j → c ≠ d →
      Relation.ReflTransGen (fd N gs) c d → False := by
    intro c d hc hd hcd hbl
    rcases Relation.ReflTransGen.cases_head hbl with e | ⟨q, hq, hqd⟩
    · exact hcd e
    · have hrf : fd N gs c (N + j) := ⟨j, hj, rfl, hc⟩
      have := hU hq hrf
      subst this
      have := rt_le N gs j0 H _ _ hqd
      omega
  rcases Relation.ReflTransGen.total_of_right_unique hU h1 h2 with h | h
  · exact key a b (by rw [hab]; simp) hb hne h
  · exact key b a (by rw [hab]; simp) ha (Ne.symm hne) h

theorem set_ne (gs : List Gate) (g' : Gate) (j i : ℕ) (h : j ≠ i) :
    (gs.set j g').getD i dg = gs.getD i dg := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem set_self (gs : List Gate) (g' : Gate) (j : ℕ) (h : j < gs.length) :
    (gs.set j g').getD j dg = g' := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

theorem vgate (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) (g' : Gate) (j a b : ℕ)
    (hj : j < gs.length) (hne : j ≠ j0) (hab : (gs.getD j dg).inputs = [a, b]) (ha : a < N + j)
    (hb : b < N + j) (W : List Bool) (hW : W.length = N) :
    V (gs.set j0 g') (N + j) W = (gs.getD j dg).op.eval [V (gs.set j0 g') a W, V (gs.set j0 g') b W] := by
  have e := valgate N (gs.set j0 g') j a b (by rw [List.length_set]; exact hj)
    (by rw [set_ne gs g' j0 j (Ne.symm hne)]; exact hab) ha hb W hW
  rw [set_ne gs g' j0 j (Ne.symm hne)] at e
  exact e

theorem vconst (N : ℕ) (gs : List Gate) (j0 : ℕ) (hj : j0 < gs.length) (g' : Gate)
    (hg : g'.inputs = []) (W : List Bool) (hW : W.length = N) :
    V (gs.set j0 g') (N + j0) W = g'.op.eval [] := by
  have e := wire_at (gs.set j0 g') W j0 (by rw [List.length_set]; exact hj)
  rw [hW, set_self gs g' j0 hj, hg] at e
  exact e

theorem vnot (N : ℕ) (gs : List Gate) (j0 h0 : ℕ) (hj : j0 < gs.length)
    (hh : (gs.getD j0 dg).inputs = [h0]) (hlt : h0 < N + j0) (hop : (gs.getD j0 dg).op = GateOp.not)
    (W : List Bool) (hW : W.length = N) : V gs (N + j0) W = !V gs h0 W := by
  have e := wire_at gs W j0 hj
  rw [hW, hh, hop, List.map_cons, List.map_nil, ifp hlt] at e
  exact e

theorem vbelow (N : ℕ) (gs : List Gate) (j0 : ℕ) (g' : Gate) (W : List Bool) (hW : W.length = N) :
    ∀ w, w < N + j0 → V (gs.set j0 g') w W = V gs w W := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < N
    · unfold V
      rw [inp _ W w (by omega), inp _ W w (by omega)]
    · by_cases h2 : N + gs.length ≤ w
      · unfold V
        rw [beyond _ W w (by rw [List.length_set]; omega), beyond _ W w (by omega)]
      · obtain ⟨i, rfl⟩ : ∃ i, w = N + i := ⟨w - N, by omega⟩
        have e1 := wire_at (gs.set j0 g') W i (by rw [List.length_set]; omega)
        have e2 := wire_at gs W i (by omega)
        rw [hW] at e1 e2
        unfold V
        rw [e1, e2, set_ne gs g' j0 i (by omega)]
        congr 1
        apply List.map_congr_left
        intro c _
        split_ifs with hc
        · exact ih c hc (by omega)
        · rfl

def RS (N : ℕ) (gs : List Gate) (j0 h0 w : ℕ) : Prop :=
  (Relation.ReflTransGen (fd N gs) (N + j0) w ∧
    ∀ W : List Bool, W.length = N → V (gs.set j0 ⟨GateOp.and, []⟩) w W = true) ∨
  (∃ (f : ℕ → List Gate × ℕ) (L : List ℕ) (ev : List Bool → Bool) (sz : ℕ),
    Spec N f L ev sz ∧ L.Nodup ∧
    (∀ i ∈ L, Relation.ReflTransGen (fd N gs) i w ∧
      (Relation.ReflTransGen (fd N gs) i h0 → Relation.ReflTransGen (fd N gs) w h0)) ∧
    (∀ W W' : List Bool, (∀ i ∈ L, W.getD i false = W'.getD i false) → ev W = ev W') ∧
    ∀ W : List Bool, W.length = N → V (gs.set j0 ⟨GateOp.and, []⟩) w W = ev W)

theorem extractR (N : ℕ) (gs : List Gate) (j0 h0 : ℕ) (H : Hyp2 N gs j0)
    (hh : (gs.getD j0 dg).inputs = [h0]) : ∀ w, w < N + gs.length → RS N gs j0 h0 w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    have hj0 := H.2.2.1
    have hU := fdU N gs j0 H
    have fh0 : fd N gs h0 (N + j0) := ⟨j0, hj0, rfl, by rw [hh]; simp⟩
    by_cases h1 : w < N
    · right
      refine ⟨leafF w, [w], fun W => W.getD w false, 0, spec_leaf N w h1, List.nodup_singleton w,
        ?_, ?_, ?_⟩
      · intro i hi
        rw [List.mem_singleton] at hi
        subst hi
        exact ⟨Relation.ReflTransGen.refl, fun h => h⟩
      · intro W W' h
        exact h w (by simp)
      · intro W hW
        unfold V
        rw [inp _ W w (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < gs.length := by omega
      by_cases hjj : j = j0
      · left
        subst hjj
        refine ⟨Relation.ReflTransGen.refl, fun W hW => ?_⟩
        rw [vconst N gs j hj _ rfl W hW]
        rfl
      · obtain ⟨a, b, hab, ha, hb, hne, hop⟩ := shape N gs j0 H j hj hjj
        have fa : fd N gs a (N + j) := ⟨j, hj, rfl, by rw [hab]; simp⟩
        have fb : fd N gs b (N + j) := ⟨j, hj, rfl, by rw [hab]; simp⟩
        have hv := fun (W : List Bool) (hW : W.length = N) =>
          vgate N gs j0 H ⟨GateOp.and, []⟩ j a b hj hjj hab ha hb W hW
        have lift : ∀ c, fd N gs c (N + j) → ∀ i,
            (Relation.ReflTransGen (fd N gs) i c ∧
              (Relation.ReflTransGen (fd N gs) i h0 → Relation.ReflTransGen (fd N gs) c h0)) →
            (Relation.ReflTransGen (fd N gs) i (N + j) ∧
              (Relation.ReflTransGen (fd N gs) i h0 → Relation.ReflTransGen (fd N gs) (N + j) h0)) := by
          intro c fc i hi
          refine ⟨Relation.ReflTransGen.tail hi.1 fc, fun h => ?_⟩
          have hc := hi.2 h
          rcases Relation.ReflTransGen.cases_head hc with e | ⟨q, hq, hqd⟩
          · exfalso
            rw [e] at fc
            have := hU fc fh0
            omega
          · have := hU hq fc
            rw [this] at hqd
            exact hqd
        rcases ih a ha (by omega) with ⟨ra, va⟩ | ⟨f1, L1, e1, s1, sp1, nd1, inv1, dl1, v1⟩
        · rcases ih b hb (by omega) with ⟨rb, vb⟩ | ⟨f2, L2, e2, s2, sp2, nd2, inv2, dl2, v2⟩
          · left
            refine ⟨Relation.ReflTransGen.tail ra fa, fun W hW => ?_⟩
            rw [hv W hW, va W hW, vb W hW]
            rcases hop with ho | ho <;> rw [ho] <;> rfl
          · rcases hop with ho | ho
            · right
              refine ⟨f2, L2, e2, s2, sp2, nd2, fun i hi => lift b fb i (inv2 i hi), dl2, fun W hW => ?_⟩
              rw [hv W hW, va W hW, v2 W hW, ho, evand]
              rfl
            · left
              refine ⟨Relation.ReflTransGen.tail ra fa, fun W hW => ?_⟩
              rw [hv W hW, va W hW, ho, evor]
              rfl
        · rcases ih b hb (by omega) with ⟨rb, vb⟩ | ⟨f2, L2, e2, s2, sp2, nd2, inv2, dl2, v2⟩
          · rcases hop with ho | ho
            · right
              refine ⟨f1, L1, e1, s1, sp1, nd1, fun i hi => lift a fa i (inv1 i hi), dl1, fun W hW => ?_⟩
              rw [hv W hW, vb W hW, v1 W hW, ho, evand, Bool.and_true]
            · left
              refine ⟨Relation.ReflTransGen.tail rb fb, fun W hW => ?_⟩
              rw [hv W hW, vb W hW, ho, evor, Bool.or_true]
          · right
            have hdis : ∀ i, i ∈ L1 → i ∈ L2 → False := by
              intro i h1 h2
              exact disj N gs j0 H j a b hj hab ha hb hne i (inv1 i h1).1 (inv2 i h2).1
            refine ⟨nodeF (gs.getD j dg).op f1 f2, L1 ++ L2,
              fun W => (gs.getD j dg).op.eval [e1 W, e2 W], s1 + s2 + 1,
              spec_node N _ f1 f2 L1 L2 e1 e2 s1 s2 hop sp1 sp2 hdis, ?_, ?_, ?_, ?_⟩
            · rw [List.nodup_append]
              exact ⟨nd1, nd2, fun x h1 y h2 e => hdis x h1 (e ▸ h2)⟩
            · intro i hi
              rw [List.mem_append] at hi
              rcases hi with h | h
              · exact lift a fa i (inv1 i h)
              · exact lift b fb i (inv2 i h)
            · intro W W' h
              show (gs.getD j dg).op.eval [e1 W, e2 W] = (gs.getD j dg).op.eval [e1 W', e2 W']
              rw [dl1 W W' (fun i hi => h i (List.mem_append_left _ hi)),
                dl2 W W' (fun i hi => h i (List.mem_append_right _ hi))]
            · intro W hW
              show _ = (gs.getD j dg).op.eval [e1 W, e2 W]
              rw [hv W hW, v1 W hW, v2 W hW]

theorem andid : ∀ (ba aa bb ab z : Bool), (ba = true → aa = true) → (bb = true → ab = true) →
    ((ba || (z && aa)) && (bb || (z && ab))) = ((ba && bb) || (z && (aa && ab))) := by
  decide

theorem orid : ∀ (ba aa bb ab z : Bool),
    ((ba || (z && aa)) || (bb || (z && ab))) = ((ba || bb) || (z && (aa || ab))) := by
  decide

theorem le01 (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) (W : List Bool) (hW : W.length = N) :
    ∀ w, V (gs.set j0 ⟨GateOp.or, []⟩) w W = true → V (gs.set j0 ⟨GateOp.and, []⟩) w W = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < N
    · unfold V
      rw [inp _ W w (by omega), inp _ W w (by omega)]
      exact fun h => h
    · by_cases h2 : N + gs.length ≤ w
      · unfold V
        rw [beyond _ W w (by rw [List.length_set]; omega)]
        intro h
        exact Bool.noConfusion h
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < gs.length := by omega
        by_cases hjj : j = j0
        · subst hjj
          intro _
          rw [vconst N gs j hj _ rfl W hW]
          rfl
        · obtain ⟨a, b, hab, ha, hb, _, hop⟩ := shape N gs j0 H j hj hjj
          rw [vgate N gs j0 H _ j a b hj hjj hab ha hb W hW, vgate N gs j0 H _ j a b hj hjj hab ha hb W hW]
          have ia := ih a ha
          have ib := ih b hb
          rcases hop with ho | ho
          · rw [ho, evand, evand, Bool.and_eq_true, Bool.and_eq_true]
            exact fun h => ⟨ia h.1, ib h.2⟩
          · rw [ho, evor, evor, Bool.or_eq_true, Bool.or_eq_true]
            exact fun h => h.elim (fun q => Or.inl (ia q)) (fun q => Or.inr (ib q))

theorem monoS (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) (g' : Gate) (hg : g'.inputs = [])
    (W W' : List Bool) (hW : W.length = N) (hW' : W'.length = N)
    (hm : ∀ k < N, W.getD k false = true → W'.getD k false = true) :
    ∀ w, V (gs.set j0 g') w W = true → V (gs.set j0 g') w W' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < N
    · unfold V
      rw [inp _ W w (by omega), inp _ W' w (by omega)]
      exact hm w h1
    · by_cases h2 : N + gs.length ≤ w
      · unfold V
        rw [beyond _ W w (by rw [List.length_set]; omega)]
        intro h
        exact Bool.noConfusion h
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < gs.length := by omega
        by_cases hjj : j = j0
        · subst hjj
          rw [vconst N gs j hj _ hg W hW, vconst N gs j hj _ hg W' hW']
          exact fun h => h
        · obtain ⟨a, b, hab, ha, hb, _, hop⟩ := shape N gs j0 H j hj hjj
          rw [vgate N gs j0 H _ j a b hj hjj hab ha hb W hW, vgate N gs j0 H _ j a b hj hjj hab ha hb W' hW']
          have ia := ih a ha
          have ib := ih b hb
          rcases hop with ho | ho
          · rw [ho, evand, evand, Bool.and_eq_true, Bool.and_eq_true]
            exact fun h => ⟨ia h.1, ib h.2⟩
          · rw [ho, evor, evor, Bool.or_eq_true, Bool.or_eq_true]
            exact fun h => h.elim (fun q => Or.inl (ia q)) (fun q => Or.inr (ib q))

theorem zeroB (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) (W : List Bool) (hW : W.length = N)
    (hz : ∀ k < N, W.getD k false = false) : ∀ w, w < N + j0 → V gs w W = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < N
    · unfold V
      rw [inp _ W w (by omega)]
      exact hz w h1
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < gs.length := by have := H.2.2.1; omega
      obtain ⟨a, b, hab, ha, hb, _, hop⟩ := shape N gs j0 H j hj (by omega)
      have e := valgate N gs j a b hj hab ha hb W hW
      unfold V
      rw [e]
      have ia := ih a ha (by omega)
      have ib := ih b hb (by omega)
      unfold V at ia ib
      rw [ia, ib]
      rcases hop with ho | ho <;> rw [ho] <;> rfl

theorem ident (N : ℕ) (gs : List Gate) (j0 h0 : ℕ) (H : Hyp2 N gs j0)
    (hh : (gs.getD j0 dg).inputs = [h0]) (hlt : h0 < N + j0) (hop0 : (gs.getD j0 dg).op = GateOp.not)
    (W : List Bool) (hW : W.length = N) :
    ∀ w, V gs w W = (V (gs.set j0 ⟨GateOp.or, []⟩) w W ||
      (!V gs h0 W && V (gs.set j0 ⟨GateOp.and, []⟩) w W)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < N
    · have e0 : V (gs.set j0 ⟨GateOp.or, []⟩) w W = V gs w W := by
        unfold V
        rw [inp _ W w (by omega), inp _ W w (by omega)]
      have e1 : V (gs.set j0 ⟨GateOp.and, []⟩) w W = V gs w W := by
        unfold V
        rw [inp _ W w (by omega), inp _ W w (by omega)]
      rw [e0, e1]
      cases V gs w W <;> cases V gs h0 W <;> rfl
    · by_cases h2 : N + gs.length ≤ w
      · have e : ∀ q : List Gate, q.length = gs.length → V q w W = false := by
          intro q hq
          unfold V
          rw [beyond _ W w (by omega)]
        rw [e gs rfl, e _ (List.length_set), e _ (List.length_set)]
        cases V gs h0 W <;> rfl
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < gs.length := by omega
        by_cases hjj : j = j0
        · subst hjj
          rw [vnot N gs j h0 hj hh hlt hop0 W hW, vconst N gs j hj _ rfl W hW,
            vconst N gs j hj _ rfl W hW]
          cases V gs h0 W <;> rfl
        · obtain ⟨a, b, hab, ha, hb, _, hop⟩ := shape N gs j0 H j hj hjj
          have e := valgate N gs j a b hj hab ha hb W hW
          have e' : V gs (N + j) W = (gs.getD j dg).op.eval [V gs a W, V gs b W] := e
          rw [e', vgate N gs j0 H _ j a b hj hjj hab ha hb W hW,
            vgate N gs j0 H _ j a b hj hjj hab ha hb W hW, ih a ha, ih b hb]
          rcases hop with ho | ho
          · rw [ho, evand, evand, evand]
            exact andid _ _ _ _ _ (le01 N gs j0 H W hW a) (le01 N gs j0 H W hW b)
          · rw [ho, evor, evor, evor]
            exact orid _ _ _ _ _

theorem nopath (N : ℕ) (gs : List Gate) (j0 h0 : ℕ) (H : Hyp2 N gs j0)
    (hh : (gs.getD j0 dg).inputs = [h0]) (g' : Gate) (hg : g'.inputs = []) (i : ℕ)
    (hi : Relation.ReflTransGen (fd N gs) i h0) :
    ∀ w, Relation.ReflTransGen (fd N (gs.set j0 g')) i w → Relation.ReflTransGen (fd N gs) w h0 := by
  intro w hr
  have hU := fdU N gs j0 H
  have hj0 := H.2.2.1
  have fh0 : fd N gs h0 (N + j0) := ⟨j0, hj0, rfl, by rw [hh]; simp⟩
  induction hr with
  | refl => exact hi
  | tail _ hf ih =>
    obtain ⟨j, hj, rfl, hb⟩ := hf
    rw [List.length_set] at hj
    by_cases hjj : j = j0
    · subst hjj
      rw [set_self gs g' j hj, hg] at hb
      simp at hb
    · rw [set_ne gs g' j0 j (Ne.symm hjj)] at hb
      rename_i b _
      have fb : fd N gs b (N + j) := ⟨j, hj, rfl, hb⟩
      rcases Relation.ReflTransGen.cases_head ih with e | ⟨q, hq, hqd⟩
      · exfalso
        rw [e] at fb
        have := hU fb fh0
        omega
      · have := hU hq fb
        rw [this] at hqd
        exact hqd

theorem gdef (gs : List Gate) (j : ℕ) (h : j < gs.length) (d1 d2 : Gate) : gs.getD j d1 = gs.getD j d2 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem rbS (N : ℕ) (gs : List Gate) (j0 : ℕ) (H : Hyp2 N gs j0) (g' : Gate) (hg : g'.inputs = []) :
    ∀ j < (gs.set j0 g').length, ∀ i ∈ ((gs.set j0 g').getD j dg).inputs, i < N + j := by
  intro j hj i hi
  rw [List.length_set] at hj
  by_cases hjj : j = j0
  · subst hjj
    rw [set_self gs g' j hj, hg] at hi
    simp at hi
  · rw [set_ne gs g' j0 j (Ne.symm hjj)] at hi
    exact H.2.1 j hj i hi

theorem frag_circ (N : ℕ) (f : ℕ → List Gate × ℕ) (L : List ℕ) (ev : List Bool → Bool) (sz : ℕ)
    (sp : Spec N f L ev sz) :
    ((∀ g ∈ (Circuit.mk (f N).1 (f N).2).gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack N (Circuit.mk (f N).1 (f N).2) ∧
      ((Circuit.mk (f N).1 (f N).2).output + 1 = N + (Circuit.mk (f N).1 (f N).2).size ∨
        ((Circuit.mk (f N).1 (f N).2).size = 0 ∧ (Circuit.mk (f N).1 (f N).2).output < N)) ∧
      (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn (Circuit.mk (f N).1 (f N).2)
        (Finset.range (Circuit.mk (f N).1 (f N).2).size) i ≤ 1) ∧
      (∀ j < (Circuit.mk (f N).1 (f N).2).size,
        PEqualNP.MetaComplexity.NestedCover.readsIn (Circuit.mk (f N).1 (f N).2)
          (Finset.range (Circuit.mk (f N).1 (f N).2).size) (N + j) =
          if j + 1 = (Circuit.mk (f N).1 (f N).2).size then 0 else 1)) ∧
    (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn (Circuit.mk (f N).1 (f N).2)
        (Finset.range (Circuit.mk (f N).1 (f N).2).size) i = 1 → i ∈ L) ∧
    (∀ W : List Bool, W.length = N → (Circuit.mk (f N).1 (f N).2).eval W = ev W) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := sp.2.2.2 N (Nat.le_refl N)
  refine ⟨⟨a2, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j hj i hi
    have hj' : j < (f N).1.length := hj
    exact a3 j (by omega) i hi
  · by_cases hs : sz = 0
    · right
      refine ⟨?_, ?_⟩
      · show (f N).1.length = 0
        omega
      · show (f N).2 < N
        omega
    · left
      show (f N).2 + 1 = N + (f N).1.length
      have := a5 (by omega)
      omega
  · intro i hi
    show ∑ j ∈ Finset.range (f N).1.length, ((f N).1.getD j dg).inputs.count i ≤ 1
    rw [sum_getD]
    have h := a6 i
    split_ifs at h <;> omega
  · intro j hj
    have hj' : j < (f N).1.length := hj
    show ∑ k ∈ Finset.range (f N).1.length, ((f N).1.getD k dg).inputs.count (N + j) =
      if j + 1 = (f N).1.length then 0 else 1
    rw [sum_getD]
    have h := a6 (N + j)
    rw [ifp (Or.inr ⟨by omega, by omega⟩)] at h
    have ho := a5 (by omega)
    split_ifs at h ⊢ <;> omega
  · intro i hi hr
    have hr' : ∑ j ∈ Finset.range (f N).1.length, ((f N).1.getD j dg).inputs.count i = 1 := hr
    rw [sum_getD] at hr'
    have h := a6 i
    by_contra hn
    rw [ifn (not_or.2 ⟨hn, by omega⟩)] at h
    omega
  · intro W hW
    exact a7 W hW

theorem main : ∀ (N : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ D.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.MetaComplexity.NestedCover.ReadsBack N D → 0 < D.size → D.output + 1 = N + D.size → (∃ j0 < D.size, ∀ j < D.size, (D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = j0) → (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) i ≤ 1) → (∀ j < D.size, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) (N + j) = if j + 1 = D.size then 0 else 1) → ∃ (Nset : Finset (Fin N)) (H α β : Finset (Fin N) → Bool), Nset.Nonempty ∧ H ∅ = false ∧ (∀ S T : Finset (Fin N), S ⊆ T → H S = true → H T = true) ∧ (∀ S T : Finset (Fin N), S ⊆ T → α S = true → α T = true) ∧ (∀ S T : Finset (Fin N), S ⊆ T → β S = true → β T = true) ∧ (∀ S : Finset (Fin N), β S = true → α S = true) ∧ (∀ x : Fin N → Bool, D.eval (List.ofFn x) = (β ((Finset.univ.filter (fun i : Fin N => x i = true)) \ Nset) || (!H ((Finset.univ.filter (fun i : Fin N => x i = true)) ∩ Nset) && α ((Finset.univ.filter (fun i : Fin N => x i = true)) \ Nset)))) ∧ (∃ FH : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g ∈ FH.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N FH ∧ (FH.output + 1 = N + FH.size ∨ (FH.size = 0 ∧ FH.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) i ≤ 1) ∧ (∀ j < FH.size, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) (N + j) = if j + 1 = FH.size then 0 else 1)) ∧ (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) i.val = 1 → i ∈ Nset) ∧ ∀ S : Finset (Fin N), H S = FH.eval (List.ofFn fun k : Fin N => decide (k ∈ S))) ∧ ((∃ c : Bool, ∀ S : Finset (Fin N), α S = c) ∨ ∃ Fα : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g ∈ Fα.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N Fα ∧ (Fα.output + 1 = N + Fα.size ∨ (Fα.size = 0 ∧ Fα.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) i ≤ 1) ∧ (∀ j < Fα.size, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) (N + j) = if j + 1 = Fα.size then 0 else 1)) ∧ (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) i.val = 1 → i ∉ Nset) ∧ ∀ S : Finset (Fin N), α S = Fα.eval (List.ofFn fun k : Fin N => decide (k ∈ S))) := by
  intro N D hg hrb hpos hout hnot hin hgt
  obtain ⟨gs, o⟩ := D
  obtain ⟨j0, hj0, hj0u⟩ := hnot
  have hj0' : j0 < gs.length := hj0
  have H : Hyp2 N gs j0 := ⟨hg, hrb, hj0', fun j hj => by
    have := hj0u j hj
    rw [gdef gs j hj dg ⟨GateOp.and, []⟩]
    exact this, hin, hgt⟩
  have ho : o + 1 = N + gs.length := hout
  obtain ⟨h0, hh, hlt, hop0⟩ := shape0 N gs j0 H
  have fh0 : fd N gs h0 (N + j0) := ⟨j0, hj0', rfl, by rw [hh]; simp⟩
  rcases extractR N gs j0 h0 H hh h0 (by omega) with ⟨rbad, _⟩ | ⟨fh, Lh, eh, sh, sph, ndh, invh, dlh, vh⟩
  · exfalso
    have := rt_le N gs j0 H _ _ rbad
    omega
  have lenind : ∀ S : Finset (Fin N), (List.ofFn (fun k : Fin N => decide (k ∈ S))).length = N := by
    intro S
    simp
  have getind : ∀ (S : Finset (Fin N)) (k : ℕ) (hk : k < N),
      (List.ofFn (fun k : Fin N => decide (k ∈ S))).getD k false = decide ((⟨k, hk⟩ : Fin N) ∈ S) :=
    fun S k hk => ofFn_get N _ k hk
  have ehV : ∀ W : List Bool, W.length = N → eh W = V gs h0 W := by
    intro W hW
    rw [← vh W hW, vbelow N gs j0 _ W hW h0 hlt]
  have subm : ∀ S T : Finset (Fin N), S ⊆ T → ∀ k < N,
      (List.ofFn (fun k : Fin N => decide (k ∈ S))).getD k false = true →
      (List.ofFn (fun k : Fin N => decide (k ∈ T))).getD k false = true := by
    intro S T hST k hk h
    rw [getind S k hk] at h
    rw [getind T k hk]
    exact decide_eq_true (hST (of_decide_eq_true h))
  have notroot : ∀ k, k ∈ Lh → ∀ g' : Gate, g'.inputs = [] →
      Relation.ReflTransGen (fd N (gs.set j0 g')) k o → False := by
    intro k hk g' hg' hr
    have := nopath N gs j0 h0 H hh g' hg' k (invh k hk).1 o hr
    have := rt_le N gs j0 H _ _ this
    omega
  have indep : ∀ (g' : Gate), g'.inputs = [] → ∀ x : Fin N → Bool,
      V (gs.set j0 g') o (List.ofFn x) = V (gs.set j0 g') o
        (List.ofFn (fun k : Fin N => decide (k ∈ (Finset.univ.filter (fun i : Fin N => x i = true)) \
          (Finset.univ.filter (fun i : Fin N => i.val ∈ Lh))))) := by
    intro g' hg' x
    apply depC N (gs.set j0 g') (rbS N gs j0 H g' hg') _ _ (by simp) (lenind _)
    intro k hk hr
    have hkL : k ∉ Lh := fun q => notroot k q g' hg' hr
    rw [ofFn_get N x k hk, getind _ k hk]
    simp [hkL]
  refine ⟨Finset.univ.filter (fun i : Fin N => i.val ∈ Lh),
    fun S => eh (List.ofFn (fun k : Fin N => decide (k ∈ S))),
    fun S => V (gs.set j0 ⟨GateOp.and, []⟩) o (List.ofFn (fun k : Fin N => decide (k ∈ S))),
    fun S => V (gs.set j0 ⟨GateOp.or, []⟩) o (List.ofFn (fun k : Fin N => decide (k ∈ S))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl := sph.1
    have hm := sph.2.1
    obtain ⟨i, hi⟩ : ∃ i, i ∈ Lh := List.exists_mem_of_length_pos (by omega)
    exact ⟨⟨i, hm i hi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  · show eh (List.ofFn (fun k : Fin N => decide (k ∈ (∅ : Finset (Fin N))))) = false
    rw [ehV _ (lenind _)]
    apply zeroB N gs j0 H _ (lenind _) _ h0 hlt
    intro k hk
    rw [getind _ k hk]
    simp
  · intro S T hST h
    have h' : eh (List.ofFn (fun k : Fin N => decide (k ∈ S))) = true := h
    show eh (List.ofFn (fun k : Fin N => decide (k ∈ T))) = true
    rw [← vh _ (lenind _)] at h' ⊢
    exact monoS N gs j0 H _ rfl _ _ (lenind S) (lenind T) (subm S T hST) h0 h'
  · intro S T hST h
    exact monoS N gs j0 H _ rfl _ _ (lenind S) (lenind T) (subm S T hST) o h
  · intro S T hST h
    exact monoS N gs j0 H _ rfl _ _ (lenind S) (lenind T) (subm S T hST) o h
  · intro S h
    exact le01 N gs j0 H _ (lenind S) o h
  · intro x
    have hxl : (List.ofFn x).length = N := by simp
    show V gs o (List.ofFn x) = _
    rw [ident N gs j0 h0 H hh hlt hop0 (List.ofFn x) hxl o, indep _ rfl x, indep _ rfl x,
      ← ehV _ hxl]
    have e3 : eh (List.ofFn x) = eh (List.ofFn (fun k : Fin N =>
        decide (k ∈ (Finset.univ.filter (fun i : Fin N => x i = true)) ∩
          (Finset.univ.filter (fun i : Fin N => i.val ∈ Lh))))) := by
      apply dlh
      intro i hi
      have hiN := sph.2.1 i hi
      rw [ofFn_get N x i hiN, getind _ i hiN]
      simp [hi]
    rw [e3]
  · obtain ⟨c1, c2, c3⟩ := frag_circ N fh Lh eh sh sph
    refine ⟨⟨(fh N).1, (fh N).2⟩, c1, ?_, ?_⟩
    · intro i hr
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, c2 i.val i.isLt hr⟩
    · intro S
      exact (c3 _ (lenind S)).symm
  · rcases extractR N gs j0 h0 H hh o (by omega) with ⟨_, vt⟩ | ⟨f2, L2, e2, s2, sp2, nd2, inv2, dl2, v2⟩
    · left
      exact ⟨true, fun S => vt _ (lenind S)⟩
    · right
      obtain ⟨c1, c2, c3⟩ := frag_circ N f2 L2 e2 s2 sp2
      refine ⟨⟨(f2 N).1, (f2 N).2⟩, c1, ?_, ?_⟩
      · intro i hr hiN
        have hiL := (Finset.mem_filter.1 hiN).2
        have h2 := c2 i.val i.isLt hr
        have := (inv2 i.val h2).2 (invh i.val hiL).1
        have := rt_le N gs j0 H _ _ this
        omega
      · intro S
        show V (gs.set j0 ⟨GateOp.and, []⟩) o (List.ofFn (fun k : Fin N => decide (k ∈ S))) = _
        rw [v2 _ (lenind S)]
        exact (c3 _ (lenind S)).symm

end PEqualNP.Outside.L_meta_23963

theorem PEqualNP.Outside.L_meta_23963 : ∀ (N : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ D.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.MetaComplexity.NestedCover.ReadsBack N D → 0 < D.size → D.output + 1 = N + D.size → (∃ j0 < D.size, ∀ j < D.size, (D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = j0) → (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) i ≤ 1) → (∀ j < D.size, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) (N + j) = if j + 1 = D.size then 0 else 1) → ∃ (Nset : Finset (Fin N)) (H α β : Finset (Fin N) → Bool), Nset.Nonempty ∧ H ∅ = false ∧ (∀ S T : Finset (Fin N), S ⊆ T → H S = true → H T = true) ∧ (∀ S T : Finset (Fin N), S ⊆ T → α S = true → α T = true) ∧ (∀ S T : Finset (Fin N), S ⊆ T → β S = true → β T = true) ∧ (∀ S : Finset (Fin N), β S = true → α S = true) ∧ (∀ x : Fin N → Bool, D.eval (List.ofFn x) = (β ((Finset.univ.filter (fun i : Fin N => x i = true)) \ Nset) || (!H ((Finset.univ.filter (fun i : Fin N => x i = true)) ∩ Nset) && α ((Finset.univ.filter (fun i : Fin N => x i = true)) \ Nset)))) ∧ (∃ FH : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g ∈ FH.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N FH ∧ (FH.output + 1 = N + FH.size ∨ (FH.size = 0 ∧ FH.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) i ≤ 1) ∧ (∀ j < FH.size, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) (N + j) = if j + 1 = FH.size then 0 else 1)) ∧ (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) i.val = 1 → i ∈ Nset) ∧ ∀ S : Finset (Fin N), H S = FH.eval (List.ofFn fun k : Fin N => decide (k ∈ S))) ∧ ((∃ c : Bool, ∀ S : Finset (Fin N), α S = c) ∨ ∃ Fα : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g ∈ Fα.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N Fα ∧ (Fα.output + 1 = N + Fα.size ∨ (Fα.size = 0 ∧ Fα.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) i ≤ 1) ∧ (∀ j < Fα.size, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) (N + j) = if j + 1 = Fα.size then 0 else 1)) ∧ (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) i.val = 1 → i ∉ Nset) ∧ ∀ S : Finset (Fin N), α S = Fα.eval (List.ofFn fun k : Fin N => decide (k ∈ S))) :=
  PEqualNP.Outside.L_meta_23963.main


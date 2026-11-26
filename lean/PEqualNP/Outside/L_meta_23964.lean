import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23964

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

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (gs.foldl stp x).getD i false = true → (gs.foldl stp y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa using hxy
  | append_singleton gs g ih =>
    have ih := ih fun g' h => hg g' (by simp [h])
    intro i
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [getD_snoc, getD_snoc, len, len, hl]
    split_ifs
    · exact ih i
    · rcases hg g (by simp) with h | h
      · simp only [h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
        exact fun hh a ha => ih a (hh a ha)
      · simp only [h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact fun ⟨a, ha, hh⟩ => ⟨a, ha, ih a hh⟩
    · simp

theorem ofFn_getD {m : ℕ} (f : Fin m → Bool) (w : ℕ) (h : w < m) :
    (List.ofFn f).getD w false = f ⟨w, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem sumcount (l : List ℕ) (S : Finset ℕ) (h : ∀ i ∈ l, i ∈ S) :
    ∑ w ∈ S, l.count w = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons]
    rw [ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]
    simp [ha]

def rd (gs : List Gate) (w : ℕ) : ℕ := ∑ j ∈ Finset.range gs.length, (gs.getD j dg).inputs.count w

theorem cnt_reads (gs : List Gate) (w g1 : ℕ) (h1 : g1 < gs.length) :
    (gs.getD g1 dg).inputs.count w ≤ rd gs w := by
  unfold rd
  exact Finset.single_le_sum (f := fun j => (gs.getD j dg).inputs.count w)
    (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr h1)

theorem two_reads (gs : List Gate) (w g1 g2 : ℕ) (h1 : g1 < gs.length) (h2 : g2 < gs.length)
    (hne : g1 ≠ g2) (m1 : w ∈ (gs.getD g1 dg).inputs) (m2 : w ∈ (gs.getD g2 dg).inputs) :
    2 ≤ rd gs w := by
  unfold rd
  have hs : ({g1, g2} : Finset ℕ) ⊆ Finset.range gs.length := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr ‹_›
  have := Finset.sum_le_sum_of_subset (f := fun j => (gs.getD j dg).inputs.count w) hs
  rw [Finset.sum_pair hne] at this
  have a1 := List.count_pos_iff.mpr m1
  have a2 := List.count_pos_iff.mpr m2
  omega

def val (gs : List Gate) (N : ℕ) (X : Finset (Fin N)) (w : ℕ) : Bool :=
  (gs.foldl stp (List.ofFn fun k : Fin N => decide (k ∈ X))).getD w false

theorem val_in (gs : List Gate) (N : ℕ) (X : Finset (Fin N)) (w : ℕ) (h : w < N) :
    val gs N X w = decide ((⟨w, h⟩ : Fin N) ∈ X) := by
  unfold val
  rw [inp _ _ _ (by rw [List.length_ofFn]; exact h), ofFn_getD _ w h]

theorem val_beyond (gs : List Gate) (N : ℕ) (X : Finset (Fin N)) (w : ℕ)
    (h : N + gs.length ≤ w) : val gs N X w = false := by
  unfold val
  exact beyond _ _ _ (by rw [List.length_ofFn]; exact h)

theorem val_gate (gs : List Gate) (N : ℕ) (X : Finset (Fin N)) (j i1 i2 : ℕ)
    (hj : j < gs.length) (hin : (gs.getD j dg).inputs = [i1, i2])
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j) :
    val gs N X (N + j) = (gs.getD j dg).op.eval [val gs N X i1, val gs N X i2] := by
  unfold val
  rw [wire_okN N gs _ (List.length_ofFn) j hj (RB j hj), hin]
  rfl

theorem val_and (gs : List Gate) (N : ℕ) (X : Finset (Fin N)) (j i1 i2 : ℕ)
    (hj : j < gs.length) (hin : (gs.getD j dg).inputs = [i1, i2])
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (hop : (gs.getD j dg).op = GateOp.and) :
    val gs N X (N + j) = (val gs N X i1 && val gs N X i2) := by
  rw [val_gate gs N X j i1 i2 hj hin RB, hop]
  simp [GateOp.eval]

theorem val_or (gs : List Gate) (N : ℕ) (X : Finset (Fin N)) (j i1 i2 : ℕ)
    (hj : j < gs.length) (hin : (gs.getD j dg).inputs = [i1, i2])
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (hop : (gs.getD j dg).op = GateOp.or) :
    val gs N X (N + j) = (val gs N X i1 || val gs N X i2) := by
  rw [val_gate gs N X j i1 i2 hj hin RB, hop]
  simp [GateOp.eval]

theorem gmem (gs : List Gate) (j : ℕ) (hj : j < gs.length) : gs.getD j dg ∈ gs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

theorem shape (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < gs.length) :
    ∃ i1 i2, (gs.getD j dg).inputs = [i1, i2] ∧
      ((gs.getD j dg).op = GateOp.and ∨ (gs.getD j dg).op = GateOp.or) := by
  have h := hg _ (gmem gs j hj)
  obtain ⟨i1, i2, h12⟩ := List.length_eq_two.mp h.2
  exact ⟨i1, i2, h12, h.1⟩

def step (gs : List Gate) (N : ℕ) (i w : ℕ) : Prop :=
  ∃ j, j < gs.length ∧ w = N + j ∧ i ∈ (gs.getD j dg).inputs

theorem reach_le (gs : List Gate) (N : ℕ)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j) (a b : ℕ)
    (h : Relation.ReflTransGen (step gs N) a b) : a ≤ b := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hs ih =>
    obtain ⟨j, hj, rfl, hi⟩ := hs
    have := RB j hj _ hi
    omega

theorem step_uniq (gs : List Gate) (N : ℕ)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (hR : ∀ w, w < N + gs.length → rd gs w ≤ 1) (i w w' : ℕ)
    (h : step gs N i w) (h' : step gs N i w') : w = w' := by
  obtain ⟨j, hj, rfl, hi⟩ := h
  obtain ⟨j', hj', rfl, hi'⟩ := h'
  by_contra hne
  have h2 := two_reads gs i j j' hj hj' (by omega) hi hi'
  have h1 := hR i (by have := RB j hj i hi; omega)
  omega

theorem linear (gs : List Gate) (N : ℕ)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (hR : ∀ w, w < N + gs.length → rd gs w ≤ 1) (z a b : ℕ)
    (ha : Relation.ReflTransGen (step gs N) z a) (hb : Relation.ReflTransGen (step gs N) z b) :
    Relation.ReflTransGen (step gs N) a b ∨ Relation.ReflTransGen (step gs N) b a := by
  induction ha with
  | refl => exact Or.inl hb
  | tail _ hs ih =>
    rcases ih with h | h
    · rcases Relation.ReflTransGen.cases_head h with e | ⟨y, hy, hyb⟩
      · subst e
        exact Or.inr (Relation.ReflTransGen.single hs)
      · have := step_uniq gs N RB hR _ _ _ hs hy
        subst this
        exact Or.inl hyb
    · exact Or.inr (h.tail hs)

theorem disj (gs : List Gate) (N : ℕ)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (hR : ∀ w, w < N + gs.length → rd gs w ≤ 1) (j i1 i2 : ℕ) (hj : j < gs.length)
    (hin : (gs.getD j dg).inputs = [i1, i2]) :
    i1 ≠ i2 ∧ ∀ z, Relation.ReflTransGen (step gs N) z i1 →
      Relation.ReflTransGen (step gs N) z i2 → False := by
  have h1 : i1 ∈ (gs.getD j dg).inputs := by rw [hin]; simp
  have h2 : i2 ∈ (gs.getD j dg).inputs := by rw [hin]; simp
  have l1 := RB j hj i1 h1
  have l2 := RB j hj i2 h2
  have hne : i1 ≠ i2 := by
    intro e
    subst e
    have hc := cnt_reads gs i1 j hj
    rw [hin] at hc
    have := hR i1 (by omega)
    simp at hc
    omega
  refine ⟨hne, ?_⟩
  intro z hz1 hz2
  rcases linear gs N RB hR z i1 i2 hz1 hz2 with h | h
  · rcases Relation.ReflTransGen.cases_head h with e | ⟨y, hy, hyb⟩
    · exact hne e
    · have := step_uniq gs N RB hR _ _ _ hy ⟨j, hj, rfl, h1⟩
      subst this
      have := reach_le gs N RB _ _ hyb
      omega
  · rcases Relation.ReflTransGen.cases_head h with e | ⟨y, hy, hyb⟩
    · exact hne e.symm
    · have := step_uniq gs N RB hR _ _ _ hy ⟨j, hj, rfl, h2⟩
      subst this
      have := reach_le gs N RB _ _ hyb
      omega

theorem agr (gs : List Gate) (N : ℕ)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (X Y : Finset (Fin N)) : ∀ w,
    (∀ k : Fin N, Relation.ReflTransGen (step gs N) k.val w → (k ∈ X ↔ k ∈ Y)) →
    val gs N X w = val gs N Y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h1 : w < N
    · rw [val_in _ _ _ _ h1, val_in _ _ _ _ h1]
      have := h ⟨w, h1⟩ Relation.ReflTransGen.refl
      simp [this]
    · by_cases h2 : N + gs.length ≤ w
      · rw [val_beyond _ _ _ _ h2, val_beyond _ _ _ _ h2]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h1)
        have hj : j < gs.length := by omega
        unfold val
        rw [wire_okN N gs _ (List.length_ofFn) j hj (RB j hj),
          wire_okN N gs _ (List.length_ofFn) j hj (RB j hj)]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih i (RB j hj i hi) (fun k hk => h k (hk.tail ⟨j, hj, rfl, hi⟩))

theorem val_empty (gs : List Gate) (N : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j) :
    ∀ w, val gs N ∅ w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < N
    · rw [val_in _ _ _ _ h1]
      simp
    · by_cases h2 : N + gs.length ≤ w
      · exact val_beyond _ _ _ _ h2
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h1)
        have hj : j < gs.length := by omega
        obtain ⟨i1, i2, hin, hop⟩ := shape gs hg j hj
        have l1 := RB j hj i1 (by rw [hin]; simp)
        have l2 := RB j hj i2 (by rw [hin]; simp)
        rcases hop with hop | hop
        · rw [val_and gs N _ j i1 i2 hj hin RB hop, ih i1 l1]
          rfl
        · rw [val_or gs N _ j i1 i2 hj hin RB hop, ih i1 l1, ih i2 l2]
          rfl

theorem nr (gs : List Gate) (N : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (X : Finset (Fin N)) (w : ℕ)
    (h : ∀ k ∈ X, ¬ Relation.ReflTransGen (step gs N) k.val w) : val gs N X w = false := by
  rw [agr gs N RB X ∅ w (fun k hk => ⟨fun hx => absurd hk (h k hx), fun hx => by simp at hx⟩)]
  exact val_empty gs N hg RB w

theorem reach1 (gs : List Gate) (N : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (x : Fin N) (w : ℕ) (h : val gs N {x} w = true) :
    Relation.ReflTransGen (step gs N) x.val w := by
  by_contra hn
  rw [nr gs N hg RB {x} w (fun k hk => by rw [Finset.mem_singleton] at hk; subst hk; exact hn)] at h
  exact absurd h (by simp)

theorem dropR (gs : List Gate) (N : ℕ)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (a b : Fin N) (w : ℕ) (h : ¬ Relation.ReflTransGen (step gs N) b.val w) :
    val gs N {a, b} w = val gs N {a} w := by
  apply agr gs N RB
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (e | e)
    · exact e
    · subst e; exact absurd hk h
  · exact fun e => Or.inl e

theorem dropL (gs : List Gate) (N : ℕ)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (a b : Fin N) (w : ℕ) (h : ¬ Relation.ReflTransGen (step gs N) a.val w) :
    val gs N {a, b} w = val gs N {b} w := by
  apply agr gs N RB
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (e | e)
    · subst e; exact absurd hk h
    · exact e
  · exact fun e => Or.inr e

theorem vmono (gs : List Gate) (N : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (X Y : Finset (Fin N)) (hXY : X ⊆ Y) (w : ℕ) (h : val gs N X w = true) :
    val gs N Y w = true := by
  unfold val at h ⊢
  refine mono gs (fun g hgm => (hg g hgm).1) _ _ (by rw [List.length_ofFn, List.length_ofFn]) ?_ w h
  intro i hi
  by_cases h1 : i < N
  · rw [ofFn_getD _ i h1] at hi ⊢
    simp only [decide_eq_true_eq] at hi ⊢
    exact hXY hi
  · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hi
    exact absurd hi (by simp)

theorem bic (gs : List Gate) (N : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (hR : ∀ w, w < N + gs.length → rd gs w ≤ 1) : ∀ w,
    (∀ a : Fin N, val gs N {a} w = false) → ∀ a b c d : Fin N,
    val gs N {a, b} w = true → val gs N {c, b} w = true → val gs N {c, d} w = true →
    val gs N {a, d} w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hs a b c d hab hcb hcd
    by_cases h1 : w < N
    · have := hs ⟨w, h1⟩
      rw [val_in _ _ _ _ h1] at this
      simp at this
    · by_cases h2 : N + gs.length ≤ w
      · rw [val_beyond _ _ _ _ h2] at hab
        exact absurd hab (by simp)
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h1)
        have hj : j < gs.length := by omega
        obtain ⟨i1, i2, hin, hop⟩ := shape gs hg j hj
        have l1 := RB j hj i1 (by rw [hin]; simp)
        have l2 := RB j hj i2 (by rw [hin]; simp)
        obtain ⟨_, hdis⟩ := disj gs N RB hR j i1 i2 hj hin
        have excl : ∀ x : Fin N, val gs N {x} i1 = true → val gs N {x} i2 = true → False :=
          fun x h1' h2' => hdis x.val (reach1 gs N hg RB x i1 h1') (reach1 gs N hg RB x i2 h2')
        rcases hop with hop | hop
        · have pair : ∀ p q : Fin N, val gs N {p, q} (N + j) = true →
              (val gs N {p} i1 = true ∧ val gs N {q} i2 = true) ∨
              (val gs N {q} i1 = true ∧ val gs N {p} i2 = true) := by
            intro p q hpq
            rw [val_and gs N _ j i1 i2 hj hin RB hop, Bool.and_eq_true] at hpq
            obtain ⟨v1, v2⟩ := hpq
            by_cases rp1 : Relation.ReflTransGen (step gs N) p.val i1
            · have rp2 : ¬ Relation.ReflTransGen (step gs N) p.val i2 := fun h => hdis _ rp1 h
              rw [dropL gs N RB p q i2 rp2] at v2
              have rq1 : ¬ Relation.ReflTransGen (step gs N) q.val i1 :=
                fun h => hdis _ h (reach1 gs N hg RB q i2 v2)
              rw [dropR gs N RB p q i1 rq1] at v1
              exact Or.inl ⟨v1, v2⟩
            · rw [dropL gs N RB p q i1 rp1] at v1
              have rq2 : ¬ Relation.ReflTransGen (step gs N) q.val i2 :=
                fun h => hdis _ (reach1 gs N hg RB q i1 v1) h
              rw [dropR gs N RB p q i2 rq2] at v2
              exact Or.inr ⟨v1, v2⟩
          rw [val_and gs N _ j i1 i2 hj hin RB hop, Bool.and_eq_true]
          have sa : ({a} : Finset (Fin N)) ⊆ {a, d} := by simp
          have sd : ({d} : Finset (Fin N)) ⊆ {a, d} := by simp
          rcases pair a b hab with ⟨a1, b2⟩ | ⟨b1, a2⟩
          · rcases pair c b hcb with ⟨c1, _⟩ | ⟨b1, _⟩
            · rcases pair c d hcd with ⟨_, d2⟩ | ⟨_, c2⟩
              · exact ⟨vmono gs N hg _ _ sa i1 a1, vmono gs N hg _ _ sd i2 d2⟩
              · exact absurd (excl c c1 c2) id
            · exact absurd (excl b b1 b2) id
          · rcases pair c b hcb with ⟨_, b2⟩ | ⟨_, c2⟩
            · exact absurd (excl b b1 b2) id
            · rcases pair c d hcd with ⟨c1, _⟩ | ⟨d1, _⟩
              · exact absurd (excl c c1 c2) id
              · exact ⟨vmono gs N hg _ _ sd i1 d1, vmono gs N hg _ _ sa i2 a2⟩
        · have hs1 : ∀ x : Fin N, val gs N {x} i1 = false ∧ val gs N {x} i2 = false := by
            intro x
            have := hs x
            rw [val_or gs N _ j i1 i2 hj hin RB hop, Bool.or_eq_false_iff] at this
            exact this
          have pair : ∀ p q : Fin N, val gs N {p, q} (N + j) = true →
              (val gs N {p, q} i1 = true ∧ Relation.ReflTransGen (step gs N) q.val i1 ∧
                Relation.ReflTransGen (step gs N) p.val i1) ∨
              (val gs N {p, q} i2 = true ∧ Relation.ReflTransGen (step gs N) q.val i2 ∧
                Relation.ReflTransGen (step gs N) p.val i2) := by
            intro p q hpq
            rw [val_or gs N _ j i1 i2 hj hin RB hop, Bool.or_eq_true] at hpq
            rcases hpq with v | v
            · refine Or.inl ⟨v, ?_, ?_⟩
              · by_contra hn
                rw [dropR gs N RB p q i1 hn, (hs1 p).1] at v
                exact absurd v (by simp)
              · by_contra hn
                rw [dropL gs N RB p q i1 hn, (hs1 q).1] at v
                exact absurd v (by simp)
            · refine Or.inr ⟨v, ?_, ?_⟩
              · by_contra hn
                rw [dropR gs N RB p q i2 hn, (hs1 p).2] at v
                exact absurd v (by simp)
              · by_contra hn
                rw [dropL gs N RB p q i2 hn, (hs1 q).2] at v
                exact absurd v (by simp)
          rw [val_or gs N _ j i1 i2 hj hin RB hop, Bool.or_eq_true]
          rcases pair a b hab with ⟨vab, rb, _⟩ | ⟨vab, rb, _⟩
          · rcases pair c b hcb with ⟨vcb, _, rc⟩ | ⟨_, rb', _⟩
            · rcases pair c d hcd with ⟨vcd, _, _⟩ | ⟨_, _, rc'⟩
              · exact Or.inl (ih i1 l1 (fun x => (hs1 x).1) a b c d vab vcb vcd)
              · exact absurd (hdis _ rc rc') id
            · exact absurd (hdis _ rb rb') id
          · rcases pair c b hcb with ⟨_, rb', _⟩ | ⟨vcb, _, rc⟩
            · exact absurd (hdis _ rb' rb) id
            · rcases pair c d hcd with ⟨_, _, rc'⟩ | ⟨vcd, _, _⟩
              · exact absurd (hdis _ rc' rc) id
              · exact Or.inr (ih i2 l2 (fun x => (hs1 x).2) a b c d vab vcb vcd)

theorem cnt1 (s : ℕ) (hs : 0 < s) :
    (∑ j ∈ Finset.range s, (if j + 1 = s then 0 else 1)) + 1 = s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hs)
  rw [Finset.sum_range_succ]
  have h : ∀ j ∈ Finset.range t, (if j + 1 = t + 1 then 0 else 1) = 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [ifn (by omega)]
  rw [Finset.sum_congr rfl h]
  simp

theorem main : ∀ (N : ℕ) (F : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g ∈ F.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N F ∧ (F.output + 1 = N + F.size ∨ (F.size = 0 ∧ F.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i ≤ 1) ∧ (∀ j < F.size, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (N + j) = if j + 1 = F.size then 0 else 1)) → ((F.eval (List.ofFn fun k : Fin N => decide (k ∈ (∅ : Finset (Fin N)))) = false → (∀ a : Fin N, F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a} : Finset (Fin N)))) = false) → ∀ a b c d : Fin N, F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a, b} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({c, b} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({c, d} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a, d} : Finset (Fin N)))) = true) ∧ (∀ a b : Fin N, a ≠ b → (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i.val = 1 ↔ (i = a ∨ i = b)) → (∀ x : Fin N → Bool, F.eval (List.ofFn x) = (x a && x b)) ∨ (∀ x : Fin N → Bool, F.eval (List.ofFn x) = (x a || x b)))) := by
  intro N F hF
  obtain ⟨hg, hRB, hout, hRi, hRg⟩ := hF
  have RB : ∀ j < F.gates.length, ∀ i ∈ (F.gates.getD j dg).inputs, i < N + j := hRB
  have hRi' : ∀ i < N, rd F.gates i ≤ 1 := hRi
  have hRg' : ∀ j < F.gates.length, rd F.gates (N + j) = if j + 1 = F.gates.length then 0 else 1 :=
    hRg
  have hR : ∀ w, w < N + F.gates.length → rd F.gates w ≤ 1 := by
    intro w hw
    by_cases h1 : w < N
    · exact hRi' w h1
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h1)
      rw [hRg' j (by omega)]
      split_ifs <;> omega
  refine ⟨?_, ?_⟩
  · intro _ hs a b c d hab hcb hcd
    exact bic F.gates N hg RB hR F.output hs a b c d hab hcb hcd
  · intro a b hab hrd
    have hrd' : ∀ i : Fin N, rd F.gates i.val = 1 ↔ (i = a ∨ i = b) := hrd
    have hlen : ∀ j < F.gates.length, (F.gates.getD j dg).inputs.length = 2 :=
      fun j hj => (hg _ (gmem F.gates j hj)).2
    have e2 : ∑ w ∈ Finset.range (N + F.gates.length), rd F.gates w =
        ∑ j ∈ Finset.range F.gates.length, (F.gates.getD j dg).inputs.length := by
      unfold rd
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      apply sumcount
      intro i hi
      have := RB j hj i hi
      rw [Finset.mem_range]
      omega
    have e3 : ∑ j ∈ Finset.range F.gates.length, (F.gates.getD j dg).inputs.length =
        2 * F.gates.length := by
      rw [Finset.sum_congr rfl (fun j hj => hlen j (Finset.mem_range.mp hj))]
      simp [mul_comm]
    have e1 : ∑ w ∈ Finset.range (N + F.gates.length), rd F.gates w =
        ∑ w ∈ Finset.range N, rd F.gates w +
          ∑ j ∈ Finset.range F.gates.length, rd F.gates (N + j) :=
      Finset.sum_range_add _ N _
    have e4 : ∑ w ∈ Finset.range N, rd F.gates w = 2 := by
      rw [Finset.sum_range (fun w => rd F.gates w)]
      have hi : ∀ i : Fin N, rd F.gates i.val = if i = a ∨ i = b then 1 else 0 := by
        intro i
        have h1 := hRi' i.val i.isLt
        have h2 := hrd' i
        split_ifs with hc
        · exact h2.mpr hc
        · have h3 : rd F.gates i.val ≠ 1 := fun e => hc (h2.mp e)
          omega
      rw [Finset.sum_congr rfl (fun i _ => hi i), ← Finset.card_filter]
      have hf : Finset.univ.filter (fun i : Fin N => i = a ∨ i = b) = {a, b} := by
        ext i
        simp
      rw [hf, Finset.card_pair hab]
    have hpos : 0 < F.gates.length := by
      rcases Nat.eq_zero_or_pos F.gates.length with h0 | h0
      · exfalso
        rw [e2, e3, e4] at e1
        rw [h0] at e1
        simp at e1
      · exact h0
    have e5 : ∑ j ∈ Finset.range F.gates.length, rd F.gates (N + j) + 1 = F.gates.length := by
      rw [Finset.sum_congr rfl (fun j hj => hRg' j (Finset.mem_range.mp hj))]
      exact cnt1 _ hpos
    have hl1 : F.gates.length = 1 := by omega
    obtain ⟨i1, i2, hin, hop⟩ := shape F.gates hg 0 hpos
    have m1 : i1 ∈ (F.gates.getD 0 dg).inputs := by rw [hin]; simp
    have m2 : i2 ∈ (F.gates.getD 0 dg).inputs := by rw [hin]; simp
    have p1 : i1 < N := by have := RB 0 hpos i1 m1; omega
    have p2 : i2 < N := by have := RB 0 hpos i2 m2; omega
    obtain ⟨hne, _⟩ := disj F.gates N RB hR 0 i1 i2 hpos hin
    have r1 : rd F.gates i1 = 1 := by
      have := cnt_reads F.gates i1 0 hpos
      have := List.count_pos_iff.mpr m1
      have := hRi' i1 p1
      omega
    have r2 : rd F.gates i2 = 1 := by
      have := cnt_reads F.gates i2 0 hpos
      have := List.count_pos_iff.mpr m2
      have := hRi' i2 p2
      omega
    have h1 := (hrd' ⟨i1, p1⟩).mp r1
    have h2 := (hrd' ⟨i2, p2⟩).mp r2
    have hx12 : (⟨i1, p1⟩ : Fin N) ≠ ⟨i2, p2⟩ := fun e => hne (congrArg Fin.val e)
    have hoN : F.output = N := by
      have hsz : F.size = 1 := hl1
      rcases hout with h | ⟨h, _⟩ <;> omega
    have key : ∀ x : Fin N → Bool, F.eval (List.ofFn x) =
        (F.gates.getD 0 dg).op.eval [x ⟨i1, p1⟩, x ⟨i2, p2⟩] := by
      intro x
      show (F.gates.foldl stp (List.ofFn x)).getD F.output false = _
      rw [hoN]
      have hw := wire_okN N F.gates (List.ofFn x) (List.length_ofFn) 0 hpos (RB 0 hpos)
      rw [Nat.add_zero] at hw
      rw [hw, hin]
      show (F.gates.getD 0 dg).op.eval [(F.gates.foldl stp (List.ofFn x)).getD i1 false,
        (F.gates.foldl stp (List.ofFn x)).getD i2 false] = _
      rw [inp _ _ _ (by rw [List.length_ofFn]; exact p1), inp _ _ _ (by rw [List.length_ofFn]; exact p2),
        ofFn_getD _ i1 p1, ofFn_getD _ i2 p2]
    rcases hop with hop | hop
    · left
      intro x
      rw [key x, hop]
      show ([x ⟨i1, p1⟩, x ⟨i2, p2⟩].all id) = (x a && x b)
      rcases h1 with e1' | e1' <;> rcases h2 with e2' | e2'
      · exact absurd (e1'.trans e2'.symm) hx12
      · rw [e1', e2']; simp
      · rw [e1', e2']; simp [Bool.and_comm]
      · exact absurd (e1'.trans e2'.symm) hx12
    · right
      intro x
      rw [key x, hop]
      show ([x ⟨i1, p1⟩, x ⟨i2, p2⟩].any id) = (x a || x b)
      rcases h1 with e1' | e1' <;> rcases h2 with e2' | e2'
      · exact absurd (e1'.trans e2'.symm) hx12
      · rw [e1', e2']; simp
      · rw [e1', e2']; simp [Bool.or_comm]
      · exact absurd (e1'.trans e2'.symm) hx12

end PEqualNP.Outside.L_meta_23964

theorem PEqualNP.Outside.L_meta_23964 : ∀ (N : ℕ) (F : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g ∈ F.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N F ∧ (F.output + 1 = N + F.size ∨ (F.size = 0 ∧ F.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i ≤ 1) ∧ (∀ j < F.size, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (N + j) = if j + 1 = F.size then 0 else 1)) → ((F.eval (List.ofFn fun k : Fin N => decide (k ∈ (∅ : Finset (Fin N)))) = false → (∀ a : Fin N, F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a} : Finset (Fin N)))) = false) → ∀ a b c d : Fin N, F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a, b} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({c, b} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({c, d} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a, d} : Finset (Fin N)))) = true) ∧ (∀ a b : Fin N, a ≠ b → (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i.val = 1 ↔ (i = a ∨ i = b)) → (∀ x : Fin N → Bool, F.eval (List.ofFn x) = (x a && x b)) ∨ (∀ x : Fin N → Bool, F.eval (List.ofFn x) = (x a || x b)))) :=
  PEqualNP.Outside.L_meta_23964.main

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24697

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

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega


def phi (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (w : ℕ) : ℕ :=
  if h : w < n then (π.symm ⟨w, h⟩).val
  else if h2 : w - n < m then n + (ρ.symm ⟨w - n, h2⟩).val else w

def mg (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (phi n m π ρ)⟩

theorem phi_row (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (w : ℕ) (h : w < n) :
    phi n m π ρ w = (π.symm ⟨w, h⟩).val := by
  unfold phi
  rw [dif_pos h]

theorem phi_col (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (w : ℕ) (h : ¬ w < n)
    (h2 : w - n < m) : phi n m π ρ w = n + (ρ.symm ⟨w - n, h2⟩).val := by
  unfold phi
  rw [dif_neg h, dif_pos h2]

theorem phi_big (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (w : ℕ) (h : n + m ≤ w) :
    phi n m π ρ w = w := by
  unfold phi
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem phi_lt (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (w i : ℕ) :
    phi n m π ρ w < n + m + i ↔ w < n + m + i := by
  by_cases h : w < n
  · rw [phi_row n m π ρ w h]
    have := (π.symm ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · by_cases h2 : w - n < m
    · rw [phi_col n m π ρ w h h2]
      have := (ρ.symm ⟨w - n, h2⟩).isLt
      constructor <;> intro <;> omega
    · rw [phi_big n m π ρ w (by omega)]

theorem phi_in (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (u : Fin n) (v : Fin m)
    (w : ℕ) (hw : w < n + m) :
    (phi n m π ρ w = u.val ∨ phi n m π ρ w = n + v.val) ↔ (w = (π u).val ∨ w = n + (ρ v).val) := by
  by_cases h : w < n
  · rw [phi_row n m π ρ w h]
    have h1 := (π.symm ⟨w, h⟩).isLt
    have h3 := (π u).isLt
    have e : (π.symm ⟨w, h⟩).val = u.val ↔ w = (π u).val := by
      constructor
      · intro q
        have q' : π.symm ⟨w, h⟩ = u := Fin.ext q
        have := congrArg π q'
        rw [Equiv.apply_symm_apply] at this
        exact (congrArg Fin.val this)
      · intro q
        have q' : (⟨w, h⟩ : Fin n) = π u := Fin.ext q
        rw [q', Equiv.symm_apply_apply]
    constructor
    · rintro (q | q)
      · exact Or.inl (e.1 q)
      · omega
    · rintro (q | q)
      · exact Or.inl (e.2 q)
      · omega
  · have h2 : w - n < m := by omega
    rw [phi_col n m π ρ w h h2]
    have h1 := (ρ.symm ⟨w - n, h2⟩).isLt
    have h3 := (ρ v).isLt
    have h4 := (π u).isLt
    have e : (ρ.symm ⟨w - n, h2⟩).val = v.val ↔ w - n = (ρ v).val := by
      constructor
      · intro q
        have q' : ρ.symm ⟨w - n, h2⟩ = v := Fin.ext q
        have := congrArg ρ q'
        rw [Equiv.apply_symm_apply] at this
        exact (congrArg Fin.val this)
      · intro q
        have q' : (⟨w - n, h2⟩ : Fin m) = ρ v := Fin.ext q
        rw [q', Equiv.symm_apply_apply]
    have := u.isLt
    constructor
    · rintro (q | q)
      · omega
      · have := e.1 (by omega)
        exact Or.inr (by omega)
    · rintro (q | q)
      · omega
      · have := e.2 (by omega)
        exact Or.inr (by omega)

theorem map_getD (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (gs : List Gate) (i : ℕ)
    (hi : i < gs.length) : (gs.map (mg n m π ρ)).getD i dg = mg n m π ρ (gs.getD i dg) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  rfl

theorem sim (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (gs : List Gate)
    (u : Fin n) (v : Fin m) :
    ∀ w, ((gs.map (mg n m π ρ)).foldl stp (oneEach u v)).getD (phi n m π ρ w) false =
      (gs.foldl stp (oneEach (π u) (ρ v))).getD w false := by
  have hx : (oneEach u v).length = n + m := by simp [oneEach]
  have hx' : (oneEach (π u) (ρ v)).length = n + m := by simp [oneEach]
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < n + m
    · have hp := (phi_lt n m π ρ w 0).2 (by omega)
      rw [inp _ _ _ (by omega), inp _ _ _ (by omega), Bool.eq_iff_iff, oe, oe]
      exact phi_in n m π ρ u v w h1
    · by_cases h2 : n + m + gs.length ≤ w
      · rw [phi_big n m π ρ w (by omega), beyond _ _ _ (by rw [List.length_map]; omega),
          beyond _ _ _ (by omega)]
      · obtain ⟨i, rfl⟩ : ∃ i, w = n + m + i := ⟨w - (n + m), by omega⟩
        have hi : i < gs.length := by omega
        rw [phi_big n m π ρ _ (by omega)]
        have e1 := wire_at (gs.map (mg n m π ρ)) (oneEach u v) i (by rw [List.length_map]; exact hi)
        have e2 := wire_at gs (oneEach (π u) (ρ v)) i hi
        rw [hx] at e1
        rw [hx'] at e2
        rw [e1, e2, map_getD n m π ρ gs i hi]
        show (gs.getD i dg).op.eval (List.map _ ((gs.getD i dg).inputs.map (phi n m π ρ))) = _
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro w' _
        show (if phi n m π ρ w' < n + m + i then
          ((gs.map (mg n m π ρ)).foldl stp (oneEach u v)).getD (phi n m π ρ w') false else false) = _
        by_cases hc : w' < n + m + i
        · rw [ifp hc, ifp ((phi_lt n m π ρ w' i).2 hc)]
          exact ih w' (by omega)
        · rw [ifn hc, ifn (fun q => hc ((phi_lt n m π ρ w' i).1 q))]

theorem phi_row_inv (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (u : Fin n) (w : ℕ)
    (h : phi n m π ρ w = u.val) : w = (π u).val := by
  have hu := u.isLt
  by_cases h1 : w < n
  · rw [phi_row n m π ρ w h1] at h
    have q' : π.symm ⟨w, h1⟩ = u := Fin.ext h
    have := congrArg π q'
    rw [Equiv.apply_symm_apply] at this
    exact (congrArg Fin.val this)
  · by_cases h2 : w - n < m
    · rw [phi_col n m π ρ w h1 h2] at h
      omega
    · rw [phi_big n m π ρ w (by omega)] at h
      omega

theorem phi_col_inv (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (v : Fin m) (w : ℕ)
    (h : phi n m π ρ w = n + v.val) : w = n + (ρ v).val := by
  have hv := v.isLt
  by_cases h1 : w < n
  · rw [phi_row n m π ρ w h1] at h
    have := (π.symm ⟨w, h1⟩).isLt
    omega
  · by_cases h2 : w - n < m
    · rw [phi_col n m π ρ w h1 h2] at h
      have q' : ρ.symm ⟨w - n, h2⟩ = v := Fin.ext (by omega)
      have := congrArg ρ q'
      rw [Equiv.apply_symm_apply] at this
      have := congrArg Fin.val this
      simp only at this
      omega
    · rw [phi_big n m π ρ w (by omega)] at h
      omega

theorem phi_eq_big (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (w k : ℕ)
    (hk : n + m ≤ k) : phi n m π ρ w = k ↔ w = k := by
  by_cases h : w < n + m
  · have := (phi_lt n m π ρ w 0).2 (by omega)
    constructor <;> intro <;> omega
  · rw [phi_big n m π ρ w (by omega)]

theorem count_phi (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (l : List ℕ) (k : ℕ)
    (hk : n + m ≤ k) : (l.map (phi n m π ρ)).count k = l.count k := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.count_cons, List.count_cons, ih]
    by_cases h : a = k
    · have h' : phi n m π ρ k = k := (phi_eq_big n m π ρ k k hk).2 rfl
      simp [h, h']
    · have h' : ¬ phi n m π ρ a = k := fun e => h ((phi_eq_big n m π ρ a k hk).1 e)
      simp [h, h']

theorem red (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (gs : List Gate) (o : ℕ)
    (h : ((∀ g ∈ (Circuit.mk gs o).gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) (Circuit.mk gs o) ∧ 0 < (Circuit.mk gs o).size ∧ (Circuit.mk gs o).output + 1 = (n + m) + (Circuit.mk gs o).size ∧ (∀ j < (Circuit.mk gs o).size, (PEqualNP.MetaComplexity.NestedCover.readsIn (Circuit.mk gs o) (Finset.range (Circuit.mk gs o).size) ((n + m) + j) = 0 ↔ j + 1 = (Circuit.mk gs o).size)) ∨ ((Circuit.mk gs o).size = 0 ∧ (Circuit.mk gs o).output < (n + m)))) : ((∀ g ∈ (Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)).gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) (Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)) ∧ 0 < (Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)).size ∧ (Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)).output + 1 = (n + m) + (Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)).size ∧ (∀ j < (Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)).size, (PEqualNP.MetaComplexity.NestedCover.readsIn (Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)) (Finset.range (Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)).size) ((n + m) + j) = 0 ↔ j + 1 = (Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)).size)) ∨ ((Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)).size = 0 ∧ (Circuit.mk (gs.map (mg n m π ρ)) (phi n m π ρ o)).output < (n + m))) := by
  have hl : (gs.map (mg n m π ρ)).length = gs.length := List.length_map _
  rcases h with ⟨hAr, hRB, hpos, hout, hreads⟩ | ⟨hs0, ho⟩
  · left
    have hpos' : 0 < gs.length := hpos
    have hout' : o + 1 = (n + m) + gs.length := hout
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ gs.map (mg n m π ρ) at hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have := hAr g0 hg0
      show ((g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ (g0.inputs.map (phi n m π ρ)).length = 2) ∨
        (g0.op = GateOp.not ∧ (g0.inputs.map (phi n m π ρ)).length = 1)
      rw [List.length_map]
      exact this
    · intro j hj i hi
      have hj' : j < gs.length := by
        have : j < (gs.map (mg n m π ρ)).length := hj
        omega
      change i ∈ ((gs.map (mg n m π ρ)).getD j dg).inputs at hi
      rw [map_getD n m π ρ gs j hj'] at hi
      change i ∈ (gs.getD j dg).inputs.map (phi n m π ρ) at hi
      rw [List.mem_map] at hi
      obtain ⟨w, hw, rfl⟩ := hi
      exact (phi_lt n m π ρ w j).2 (hRB j hj' w hw)
    · show 0 < (gs.map (mg n m π ρ)).length
      omega
    · show phi n m π ρ o + 1 = (n + m) + (gs.map (mg n m π ρ)).length
      rw [phi_big n m π ρ o (by omega)]
      omega
    · intro j hj
      have hj' : j < gs.length := by
        have : j < (gs.map (mg n m π ρ)).length := hj
        omega
      show (∑ i ∈ Finset.range (gs.map (mg n m π ρ)).length,
        ((gs.map (mg n m π ρ)).getD i dg).inputs.count ((n + m) + j)) = 0 ↔
        j + 1 = (gs.map (mg n m π ρ)).length
      rw [hl]
      have key : (∑ i ∈ Finset.range gs.length,
          ((gs.map (mg n m π ρ)).getD i dg).inputs.count ((n + m) + j)) =
          ∑ i ∈ Finset.range gs.length, (gs.getD i dg).inputs.count ((n + m) + j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_getD n m π ρ gs i (Finset.mem_range.1 hi)]
        exact count_phi n m π ρ _ _ (by omega)
      rw [key]
      exact hreads j hj'
  · right
    have hs0' : gs.length = 0 := hs0
    refine ⟨?_, ?_⟩
    · show (gs.map (mg n m π ρ)).length = 0
      omega
    · show phi n m π ρ o < n + m
      have := (phi_lt n m π ρ o 0).2 (by
        have : o < n + m := ho
        omega)
      omega

theorem main : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.Represents.Represents A C → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo C2) ∧ (PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 C2) ∧ (((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + m))) → ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m)))) ∧ PEqualNP.Represents.Represents (fun u v => A (π u) (ρ v)) C2 ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (π u).val ∈ g.inputs) ∨ C.output = (π u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (ρ v).val) ∈ g.inputs) ∨ C.output = (n + (ρ v).val))) := by
  intro n m A π ρ C hrep
  obtain ⟨gs, o⟩ := C
  refine ⟨⟨gs.map (mg n m π ρ), phi n m π ρ o⟩, ?_, ?_, ?_, red n m π ρ gs o, ?_, ?_, ?_⟩
  · show (gs.map (mg n m π ρ)).length = gs.length
    rw [List.length_map]
  · intro hF g hg
    change g ∈ gs.map (mg n m π ρ) at hg
    rw [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hF g0 hg0
    refine ⟨this.1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact this.2
  · intro hF g hg
    change g ∈ gs.map (mg n m π ρ) at hg
    rw [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hF g0 hg0
    refine ⟨this.1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact this.2
  · intro u v
    show ((gs.map (mg n m π ρ)).foldl stp (oneEach u v)).getD (phi n m π ρ o) false = A (π u) (ρ v)
    rw [sim n m π ρ gs u v o]
    exact hrep (π u) (ρ v)
  · intro u h
    rcases h with ⟨g, hg, hu⟩ | h
    · change g ∈ gs.map (mg n m π ρ) at hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      change u.val ∈ g0.inputs.map (phi n m π ρ) at hu
      rw [List.mem_map] at hu
      obtain ⟨w, hw, hwu⟩ := hu
      exact Or.inl ⟨g0, hg0, (phi_row_inv n m π ρ u w hwu) ▸ hw⟩
    · exact Or.inr (phi_row_inv n m π ρ u o h)
  · intro v h
    rcases h with ⟨g, hg, hu⟩ | h
    · change g ∈ gs.map (mg n m π ρ) at hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      change n + v.val ∈ g0.inputs.map (phi n m π ρ) at hu
      rw [List.mem_map] at hu
      obtain ⟨w, hw, hwu⟩ := hu
      exact Or.inl ⟨g0, hg0, (phi_col_inv n m π ρ v w hwu) ▸ hw⟩
    · exact Or.inr (phi_col_inv n m π ρ v o h)

end PEqualNP.Outside.L_meta_24697

theorem PEqualNP.Outside.L_meta_24697 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.Represents.Represents A C → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo C2) ∧ (PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 C2) ∧ (((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + m))) → ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m)))) ∧ PEqualNP.Represents.Represents (fun u v => A (π u) (ρ v)) C2 ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (π u).val ∈ g.inputs) ∨ C.output = (π u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (ρ v).val) ∈ g.inputs) ∨ C.output = (n + (ρ v).val))) :=
  PEqualNP.Outside.L_meta_24697.main

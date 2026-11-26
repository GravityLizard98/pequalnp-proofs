import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20815

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


def phi (N j s w : ℕ) : ℕ := if w < N + j then w else if w = N + j then N + s else w - 1

def mg (N j s : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi N j s)⟩

def hs (N j : ℕ) (gs : List Gate) : List Gate := (gs.eraseIdx j).map (mg N j gs.length)

theorem phi_lt (N j s w : ℕ) (h : w < N + j) : phi N j s w = w := by
  unfold phi; rw [ifp h]

theorem phi_eq (N j s : ℕ) : phi N j s (N + j) = N + s := by
  unfold phi; rw [ifn (by omega), ifp rfl]

theorem phi_gt (N j s w : ℕ) (h : N + j < w) : phi N j s w = w - 1 := by
  unfold phi; rw [ifn (by omega), ifn (by omega)]

theorem hs_len (N j : ℕ) (gs : List Gate) (hj : j < gs.length) : (hs N j gs).length + 1 = gs.length := by
  unfold hs
  rw [List.length_map, List.length_eraseIdx, ifp hj]
  omega

theorem hs_lt (N j : ℕ) (gs : List Gate) (i : ℕ) (hi : i < j) (hj : j < gs.length) :
    (hs N j gs).getD i dg = mg N j gs.length (gs.getD i dg) := by
  unfold hs
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eraseIdx, ifp hi, List.getElem?_eq_getElem (by omega)]
  rfl

theorem hs_ge (N j : ℕ) (gs : List Gate) (i : ℕ) (hi : j ≤ i) (hj : i + 1 < gs.length) :
    (hs N j gs).getD i dg = mg N j gs.length (gs.getD (i + 1) dg) := by
  unfold hs
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eraseIdx, ifn (by omega), List.getElem?_eq_getElem hj]
  rfl

theorem set_ne (gs : List Gate) (j i : ℕ) (h : j ≠ i) : (gs.set j dg).getD i dg = gs.getD i dg := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem set_self (gs : List Gate) (j : ℕ) (h : j < gs.length) : (gs.set j dg).getD j dg = dg := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

theorem sim (N j : ℕ) (gs : List Gate) (hj : j < gs.length) (x : List Bool) (hx : x.length = N) :
    ∀ w, ((hs N j gs).foldl stp x).getD (phi N j gs.length w) false =
      ((gs.set j dg).foldl stp x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    have hl1 := hs_len N j gs hj
    have hl2 : (gs.set j dg).length = gs.length := List.length_set
    by_cases h1 : w < N
    · rw [phi_lt _ _ _ _ (by omega), inp _ _ _ (by omega), inp _ _ _ (by omega)]
    · by_cases h2 : N + gs.length ≤ w
      · rw [phi_gt _ _ _ _ (by omega), beyond _ _ _ (by omega), beyond _ _ _ (by omega)]
      · obtain ⟨i, rfl⟩ : ∃ i, w = N + i := ⟨w - N, by omega⟩
        by_cases h3 : i = j
        · subst h3
          rw [phi_eq, beyond _ _ _ (by omega)]
          have e := wire_at (gs.set i dg) x i (by omega)
          rw [hx] at e
          rw [e, set_self gs i hj]
          rfl
        · by_cases h4 : i < j
          · rw [phi_lt _ _ _ _ (by omega)]
            have e1 := wire_at (hs N j gs) x i (by omega)
            have e2 := wire_at (gs.set j dg) x i (by omega)
            rw [hx] at e1 e2
            rw [e1, e2, hs_lt N j gs i h4 hj, set_ne gs j i (by omega)]
            show (gs.getD i dg).op.eval (List.map _ ((gs.getD i dg).inputs.map (phi N j gs.length))) = _
            rw [List.map_map]
            congr 1
            apply List.map_congr_left
            intro w' _
            show (if phi N j gs.length w' < N + i then
              ((hs N j gs).foldl stp x).getD (phi N j gs.length w') false else false) = _
            by_cases hc : w' < N + i
            · rw [ifp hc, ← ih w' (by omega), phi_lt _ _ _ _ (by omega), ifp hc]
            · rw [ifn hc]
              by_cases hc1 : w' < N + j
              · rw [phi_lt _ _ _ _ hc1, ifn hc]
              · by_cases hc2 : w' = N + j
                · rw [hc2, phi_eq, ifn (by omega)]
                · rw [phi_gt _ _ _ _ (by omega), ifn (by omega)]
          · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
            rw [phi_gt _ _ _ _ (by omega)]
            have ek : N + (k + 1) - 1 = N + k := by omega
            rw [ek]
            have e1 := wire_at (hs N j gs) x k (by omega)
            have e2 := wire_at (gs.set j dg) x (k + 1) (by omega)
            rw [hx] at e1 e2
            rw [e1, e2, hs_ge N j gs k (by omega) (by omega), set_ne gs j (k + 1) (by omega)]
            show (gs.getD (k + 1) dg).op.eval
              (List.map _ ((gs.getD (k + 1) dg).inputs.map (phi N j gs.length))) = _
            rw [List.map_map]
            congr 1
            apply List.map_congr_left
            intro w' _
            show (if phi N j gs.length w' < N + k then
              ((hs N j gs).foldl stp x).getD (phi N j gs.length w') false else false) = _
            by_cases hc : w' < N + (k + 1)
            · rw [ifp hc, ← ih w' (by omega)]
              by_cases hc1 : w' < N + j
              · rw [phi_lt _ _ _ _ hc1, ifp (by omega)]
              · by_cases hc2 : w' = N + j
                · rw [hc2, phi_eq, ifn (by omega), beyond _ _ _ (by omega)]
                · rw [phi_gt _ _ _ _ (by omega), ifp (by omega)]
            · rw [ifn hc, phi_gt _ _ _ _ (by omega), ifn (by omega)]

theorem main : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
    PEqualNP.Represents.Represents A D → C.size ≤ D.size) →
  ∀ j < C.size, ¬ PEqualNP.Represents.Represents A
    (⟨C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, C.output⟩ :
      PEqualNP.CircuitLowerBounds.Circuit) := by
  intro n m A C hF _ hmin j hj hrep
  obtain ⟨gs, o⟩ := C
  have hj' : j < gs.length := hj
  have hD := hmin ⟨hs (n + m) j gs, phi (n + m) j gs.length o⟩
    (by
      intro g hg
      unfold hs at hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have := hF g0 (List.mem_of_mem_eraseIdx hg0)
      refine ⟨this.1, ?_⟩
      show (g0.inputs.map _).length ≤ 2
      rw [List.length_map]
      exact this.2)
    (by
      intro u v
      have hx : (oneEach u v).length = n + m := by simp [oneEach]
      have := sim (n + m) j gs hj' (oneEach u v) hx o
      rw [← hrep u v]
      exact this)
  have hl := hs_len (n + m) j gs hj'
  have hD' : gs.length ≤ (hs (n + m) j gs).length := hD
  omega

end PEqualNP.Outside.L_meta_20815

theorem PEqualNP.Outside.L_meta_20815 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
    PEqualNP.Represents.Represents A D → C.size ≤ D.size) →
  ∀ j < C.size, ¬ PEqualNP.Represents.Represents A
    (⟨C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, C.output⟩ :
      PEqualNP.CircuitLowerBounds.Circuit) :=
  PEqualNP.Outside.L_meta_20815.main

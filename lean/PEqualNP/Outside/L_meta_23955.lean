import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23955

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


def finv {a b : ℕ} (f : Fin a → Fin b) (i : Fin b) : Option (Fin a) :=
  (List.finRange a).find? (fun u => decide (f u = i))

theorem finv_some {a b : ℕ} (f : Fin a → Fin b) (i : Fin b) (u : Fin a) (h : finv f i = some u) :
    f u = i := by
  have := List.find?_some h
  exact of_decide_eq_true this

theorem finv_none {a b : ℕ} (f : Fin a → Fin b) (i : Fin b) (h : finv f i = none) (u : Fin a) :
    f u ≠ i := by
  unfold finv at h
  rw [List.find?_eq_none] at h
  have := h u (List.mem_finRange u)
  intro e
  exact this (decide_eq_true e)

def phi (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (finv f ⟨w, h⟩).elim B (fun u => u.val)
  else if h2 : w - n < m then (finv g ⟨w - n, h2⟩).elim B (fun v => n' + v.val)
  else n' + m' + (w - (n + m))

def mg (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (q : Gate) : Gate :=
  ⟨q.op, q.inputs.map (phi n m n' m' B f g)⟩

theorem phi_row (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (w : ℕ) (h : w < n) :
    phi n m n' m' B f g w = (finv f ⟨w, h⟩).elim B (fun u => u.val) := by
  unfold phi
  rw [dif_pos h]

theorem phi_col (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (w : ℕ) (h : ¬ w < n)
    (h2 : w - n < m) :
    phi n m n' m' B f g w = (finv g ⟨w - n, h2⟩).elim B (fun v => n' + v.val) := by
  unfold phi
  rw [dif_neg h, dif_pos h2]

theorem phi_big (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (w : ℕ) (h : n + m ≤ w) :
    phi n m n' m' B f g w = n' + m' + (w - (n + m)) := by
  unfold phi
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem phi_small (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (w : ℕ) (h : w < n + m) :
    phi n m n' m' B f g w < n' + m' ∨ phi n m n' m' B f g w = B := by
  by_cases h1 : w < n
  · rw [phi_row n m n' m' B f g w h1]
    cases hf : finv f ⟨w, h1⟩ with
    | none => exact Or.inr rfl
    | some u =>
      left
      show u.val < n' + m'
      have := u.isLt
      omega
  · have h2 : w - n < m := by omega
    rw [phi_col n m n' m' B f g w h1 h2]
    cases hf : finv g ⟨w - n, h2⟩ with
    | none => exact Or.inr rfl
    | some v =>
      left
      show n' + v.val < n' + m'
      have := v.isLt
      omega

theorem map_getD (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (gs : List Gate) (i : ℕ)
    (hi : i < gs.length) :
    (gs.map (mg n m n' m' B f g)).getD i dg = mg n m n' m' B f g (gs.getD i dg) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  rfl

theorem sim (n m n' m' : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (hf : Function.Injective f)
    (hg : Function.Injective g) (gs : List Gate) (u : Fin n') (v : Fin m') :
    ∀ w, ((gs.map (mg n m n' m' (n' + m' + gs.length) f g)).foldl stp (oneEach u v)).getD
        (phi n m n' m' (n' + m' + gs.length) f g w) false =
      (gs.foldl stp (oneEach (f u) (g v))).getD w false := by
  have hx : (oneEach u v).length = n' + m' := by simp [oneEach]
  have hx' : (oneEach (f u) (g v)).length = n + m := by simp [oneEach]
  have hB : ∀ (y : List Bool), y.length = n' + m' →
      ((gs.map (mg n m n' m' (n' + m' + gs.length) f g)).foldl stp y).getD (n' + m' + gs.length) false = false := by
    intro y hy
    exact beyond _ _ _ (by rw [List.length_map]; omega)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < n + m
    · rw [inp gs _ w (by omega)]
      by_cases h : w < n
      · rw [phi_row n m n' m' _ f g w h]
        cases hfi : finv f ⟨w, h⟩ with
        | none =>
          show _ = _
          simp only [Option.elim]
          rw [hB _ hx]
          symm
          rw [← Bool.not_eq_true, oe]
          rintro (q | q)
          · exact finv_none f _ hfi u (Fin.ext q.symm)
          · omega
        | some u2 =>
          simp only [Option.elim]
          have hu2 := u2.isLt
          have hfu := finv_some f _ u2 hfi
          have hfu' : (f u2).val = w := congrArg Fin.val hfu
          rw [inp _ _ _ (by omega), Bool.eq_iff_iff, oe, oe]
          constructor
          · rintro (q | q)
            · have : u2 = u := Fin.ext q
              rw [this] at hfu'
              exact Or.inl hfu'.symm
            · omega
          · rintro (q | q)
            · have : f u2 = f u := Fin.ext (by omega)
              exact Or.inl (congrArg Fin.val (hf this))
            · omega
      · have h2 : w - n < m := by omega
        rw [phi_col n m n' m' _ f g w h h2]
        cases hfi : finv g ⟨w - n, h2⟩ with
        | none =>
          simp only [Option.elim]
          rw [hB _ hx]
          symm
          rw [← Bool.not_eq_true, oe]
          rintro (q | q)
          · have := (f u).isLt
            omega
          · exact finv_none g _ hfi v (Fin.ext (by show (g v).val = w - n; omega))
        | some v2 =>
          simp only [Option.elim]
          have hv2 := v2.isLt
          have hfv := finv_some g _ v2 hfi
          have hfv' : (g v2).val = w - n := congrArg Fin.val hfv
          rw [inp _ _ _ (by omega), Bool.eq_iff_iff, oe, oe]
          have := (f u).isLt
          have := u.isLt
          constructor
          · rintro (q | q)
            · omega
            · have : v2 = v := Fin.ext (by omega)
              rw [this] at hfv'
              exact Or.inr (by omega)
          · rintro (q | q)
            · omega
            · have : g v2 = g v := Fin.ext (by omega)
              have := congrArg Fin.val (hg this)
              exact Or.inr (by omega)
    · rw [phi_big n m n' m' _ f g w (by omega)]
      by_cases h2 : n + m + gs.length ≤ w
      · rw [beyond _ _ _ (by rw [List.length_map]; omega), beyond _ _ _ (by omega)]
      · obtain ⟨i, rfl⟩ : ∃ i, w = n + m + i := ⟨w - (n + m), by omega⟩
        have hi : i < gs.length := by omega
        have ei : n + m + i - (n + m) = i := by omega
        rw [ei]
        have e1 := wire_at (gs.map (mg n m n' m' (n' + m' + gs.length) f g)) (oneEach u v) i
          (by rw [List.length_map]; exact hi)
        have e2 := wire_at gs (oneEach (f u) (g v)) i hi
        rw [hx] at e1
        rw [hx'] at e2
        rw [e1, e2, map_getD n m n' m' _ f g gs i hi]
        show (gs.getD i dg).op.eval (List.map _
          ((gs.getD i dg).inputs.map (phi n m n' m' (n' + m' + gs.length) f g))) = _
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro w' _
        show (if phi n m n' m' (n' + m' + gs.length) f g w' < n' + m' + i then
          ((gs.map (mg n m n' m' (n' + m' + gs.length) f g)).foldl stp (oneEach u v)).getD
            (phi n m n' m' (n' + m' + gs.length) f g w') false else false) = _
        by_cases hc : w' < n + m + i
        · rw [ifp hc, ← ih w' (by omega)]
          by_cases hp : phi n m n' m' (n' + m' + gs.length) f g w' < n' + m' + i
          · rw [ifp hp]
          · rw [ifn hp]
            by_cases hw' : w' < n + m
            · rcases phi_small n m n' m' (n' + m' + gs.length) f g w' hw' with q | q
              · omega
              · rw [q, hB _ hx]
            · rw [phi_big n m n' m' _ f g w' (by omega)] at hp
              omega
        · rw [ifn hc, phi_big n m n' m' _ f g w' (by omega), ifn (by omega)]

theorem main : ∀ (n m n' m' : ℕ) (A : Fin n → Fin m → Bool) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit), Function.Injective f → Function.Injective g → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ C.size ∧ PEqualNP.Represents.Represents (fun (u : Fin n') (v : Fin m') => A (f u) (g v)) C' := by
  intro n m n' m' A f g C hf hg hF hrep
  obtain ⟨gs, o⟩ := C
  refine ⟨⟨gs.map (mg n m n' m' (n' + m' + gs.length) f g),
    phi n m n' m' (n' + m' + gs.length) f g o⟩, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ gs.map (mg n m n' m' (n' + m' + gs.length) f g) at hq
    rw [List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    have := hF q0 hq0
    refine ⟨this.1, ?_⟩
    show (q0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact this.2
  · show (gs.map (mg n m n' m' (n' + m' + gs.length) f g)).length ≤ gs.length
    rw [List.length_map]
  · intro u v
    show ((gs.map (mg n m n' m' (n' + m' + gs.length) f g)).foldl stp (oneEach u v)).getD
      (phi n m n' m' (n' + m' + gs.length) f g o) false = A (f u) (g v)
    rw [sim n m n' m' f g hf hg gs u v o]
    exact hrep (f u) (g v)

end PEqualNP.Outside.L_meta_23955

theorem PEqualNP.Outside.L_meta_23955 : ∀ (n m n' m' : ℕ) (A : Fin n → Fin m → Bool) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit), Function.Injective f → Function.Injective g → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ C.size ∧ PEqualNP.Represents.Represents (fun (u : Fin n') (v : Fin m') => A (f u) (g v)) C' :=
  PEqualNP.Outside.L_meta_23955.main


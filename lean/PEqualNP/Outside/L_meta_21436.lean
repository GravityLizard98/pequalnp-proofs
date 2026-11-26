import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21436

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

def cg (c : Bool) : Gate := if c then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

theorem cg_inputs (c : Bool) : (cg c).inputs = [] := by cases c <;> rfl

theorem cg_eval (c : Bool) (f : ℕ → Bool) : (cg c).op.eval ((cg c).inputs.map f) = c := by
  cases c <;> rfl

theorem ofFn_getD {m : ℕ} (f : Fin m → Bool) (w : ℕ) (h : w < m) :
    (List.ofFn f).getD w false = f ⟨w, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem agree2 (m : ℕ) (gs gs' : List Gate) (X X0 : List Bool) (hX : X.length = m)
    (hX0 : X0.length = m) (tj : ℕ) (hlen : gs'.length = gs.length)
    (hsame : ∀ j, j ≠ tj → gs'.getD j dg = gs.getD j dg)
    (RB : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < m + j)
    (bad : ℕ → Prop)
    (hin : ∀ w < m, ¬ bad w → X.getD w false = X0.getD w false)
    (hread : ∀ j < gs.length, j ≠ tj → ¬ bad (m + j) → ∀ i ∈ (gs.getD j dg).inputs, ¬ bad i)
    (htj : tj < gs.length →
      (gs.foldl stp X).getD (m + tj) false = (gs'.foldl stp X0).getD (m + tj) false) :
    ∀ w, ¬ bad w → (gs.foldl stp X).getD w false = (gs'.foldl stp X0).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hb
    by_cases h1 : w < m
    · rw [inp _ _ _ (by rw [hX]; exact h1), inp _ _ _ (by rw [hX0]; exact h1)]
      exact hin w h1 hb
    · by_cases h2 : m + gs.length ≤ w
      · rw [beyond _ _ _ (by rw [hX]; exact h2), beyond _ _ _ (by rw [hX0, hlen]; exact h2)]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h1)
        have hj : j < gs.length := by omega
        by_cases hs : j = tj
        · subst hs; exact htj hj
        · have e := hsame j hs
          rw [wire_okN m gs X hX j hj (RB j hj), wire_okN m gs' X0 hX0 j
            (by rw [hlen]; exact hj) (by rw [e]; exact RB j hj), e]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact ih i (RB j hj i hi) (hread j hj hs hb i hi)

theorem main : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (S Rg : Finset ℕ) (tj : ℕ),
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C → tj ∈ Rg → (∀ j ∈ Rg, j < C.size) →
  (∀ j < C.size, ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
    (w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg ∧ w ≠ m + tj)) → j ∈ Rg) →
  C.output ∉ S → (∀ j ∈ Rg, j ≠ tj → C.output ≠ m + j) →
  ∃ G : Bool → (Fin m → Bool) → Bool,
    (∀ (c : Bool) (x y : Fin m → Bool), (∀ i : Fin m, (i : ℕ) ∉ S → x i = y i) → G c x = G c y) ∧
    ∀ x : Fin m → Bool,
      C.eval (List.ofFn x) = G ((C.wires (List.ofFn x)).getD (m + tj) false) x := by
  intro m C S Rg tj hRB htR hRlt H hoS hoR
  have RB : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j dg).inputs, i < m + j := hRB
  refine ⟨fun c x => ((C.gates.set tj (cg c)).foldl stp
    (List.ofFn fun i : Fin m => if (i : ℕ) ∈ S then false else x i)).getD C.output false, ?_, ?_⟩
  · intro c x y h
    have e : (fun i : Fin m => if (i : ℕ) ∈ S then false else x i) =
        (fun i : Fin m => if (i : ℕ) ∈ S then false else y i) := by
      funext i
      by_cases hi : (i : ℕ) ∈ S
      · rw [ifp hi, ifp hi]
      · rw [ifn hi, ifn hi]; exact h i hi
    show ((C.gates.set tj (cg c)).foldl stp (List.ofFn fun i : Fin m => if (i : ℕ) ∈ S then false else x i)).getD C.output false = ((C.gates.set tj (cg c)).foldl stp (List.ofFn fun i : Fin m => if (i : ℕ) ∈ S then false else y i)).getD C.output false
    rw [e]
  · intro x
    show (C.gates.foldl stp (List.ofFn x)).getD C.output false =
      ((C.gates.set tj (cg ((C.gates.foldl stp (List.ofFn x)).getD (m + tj) false))).foldl stp
        (List.ofFn fun i : Fin m => if (i : ℕ) ∈ S then false else x i)).getD C.output false
    have htj : tj < C.gates.length := hRlt tj htR
    refine agree2 m C.gates _ (List.ofFn x) _ (List.length_ofFn) (List.length_ofFn) tj
      (List.length_set) (fun j hj => set_ne C.gates tj j _ (Ne.symm hj)) RB
      (fun w => w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg ∧ w ≠ m + tj)) ?_ ?_ ?_ C.output ?_
    · intro w hw hb
      rw [ofFn_getD _ w hw, ofFn_getD _ w hw]
      have hwS : w ∉ S := fun h => hb (Or.inl h)
      rw [ifn hwS]
    · intro j hj hjt hnb i hi hbi
      have hjR := H j hj i hi hbi
      exact hnb (Or.inr ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact hjR, by omega⟩)
    · intro _
      rw [wire_okN m (C.gates.set tj _) _ (List.length_ofFn) tj (by rw [List.length_set]; exact htj)
        (by rw [set_eq _ _ _ htj, cg_inputs]; intro w hw; simp at hw),
        set_eq _ _ _ htj]
      exact (cg_eval _ _).symm
    · intro hb
      rcases hb with hb | ⟨h1, h2, h3⟩
      · exact hoS hb
      · exact hoR (C.output - m) h2 (by omega) (by omega)

end PEqualNP.Outside.L_meta_21436

theorem PEqualNP.Outside.L_meta_21436 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (S Rg : Finset ℕ) (tj : ℕ),
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C → tj ∈ Rg → (∀ j ∈ Rg, j < C.size) →
  (∀ j < C.size, ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
    (w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg ∧ w ≠ m + tj)) → j ∈ Rg) →
  C.output ∉ S → (∀ j ∈ Rg, j ≠ tj → C.output ≠ m + j) →
  ∃ G : Bool → (Fin m → Bool) → Bool,
    (∀ (c : Bool) (x y : Fin m → Bool), (∀ i : Fin m, (i : ℕ) ∉ S → x i = y i) → G c x = G c y) ∧
    ∀ x : Fin m → Bool,
      C.eval (List.ofFn x) = G ((C.wires (List.ofFn x)).getD (m + tj) false) x :=
  PEqualNP.Outside.L_meta_21436.main

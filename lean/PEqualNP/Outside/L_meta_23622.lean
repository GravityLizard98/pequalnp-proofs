import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23622

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

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem sa_val {m : ℕ} (k : Fin (m + 1)) (v : Fin m) :
    (k.succAbove v).val = if v.val < k.val then v.val else v.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (by simp [Fin.lt_def] at h2 ⊢; omega)
  · exact absurd h2 (by simp [Fin.lt_def] at h1 ⊢; omega)
  · rfl

def rho (p B : ℕ) (i : ℕ) : ℕ := if i < p then i else if i = p then B else i - 1

def rg (p B : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho p B)⟩

theorem sim (p B : ℕ) (X X' : List Bool) (hl : X.length = X'.length + 1) (hp : p ≤ X'.length)
    (hbase : ∀ i, X'.getD (rho p B i) false = X.getD i false) :
    ∀ Bs : List Gate, X'.length + Bs.length ≤ B → ∀ i,
      ((Bs.map (rg p B)).foldl stp X').getD (rho p B i) false =
        (Bs.foldl stp X).getD i false := by
  intro Bs
  induction Bs using List.reverseRecOn with
  | nil =>
    intro _ i
    exact hbase i
  | append_singleton Bs g ih =>
    intro hB i
    rw [List.length_append, List.length_singleton] at hB
    have ih' := ih (by omega)
    have hv : (rg p B g).op.eval ((rg p B g).inputs.map fun i =>
        ((Bs.map (rg p B)).foldl stp X').getD i false) =
        g.op.eval (g.inputs.map fun i => (Bs.foldl stp X).getD i false) := by
      show g.op.eval ((g.inputs.map (rho p B)).map fun i =>
        ((Bs.map (rg p B)).foldl stp X').getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ih' i
    rw [List.map_append, List.map_singleton, snoc_fold, snoc_fold, hv, getD_snoc, getD_snoc,
      len, len, List.length_map]
    simp only [hl]
    have hi := ih' i
    rcases Nat.lt_trichotomy i p with h | h | h
    · have hr : rho p B i = i := by unfold rho; rw [ifp h]
      rw [hr] at hi ⊢
      rw [ifp (by omega), ifp (by omega)]
      exact hi
    · have hr : rho p B i = B := by unfold rho; rw [ifn (by omega), ifp h]
      rw [hr] at hi ⊢
      rw [ifn (by omega), ifn (by omega), ifp (by omega), ← hi]
      symm
      exact List.getD_eq_default _ _ (by rw [len, List.length_map]; omega)
    · have hr : rho p B i = i - 1 := by unfold rho; rw [ifn (by omega), ifn (by omega)]
      rw [hr] at hi ⊢
      by_cases h2 : i < X'.length + 1 + Bs.length
      · rw [ifp (by omega), ifp h2]
        exact hi
      · by_cases h3 : i = X'.length + 1 + Bs.length
        · rw [ifn (by omega), ifp (by omega), ifn h2, ifp h3]
        · rw [ifn (by omega), ifn (by omega), ifn h2, ifn h3]

theorem bool_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp at h ⊢

theorem main : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.Represents.Represents A C → (∀ g ∈ C.gates, n + k.val ∉ g.inputs) → C.output ≠ n + k.val → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, C'.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo C') ∧ PEqualNP.Represents.Represents (fun u v => A u (k.succAbove v)) C' ∧ (∀ u : Fin n, ((∃ g ∈ C'.gates, u.val ∈ g.inputs) ∨ C'.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C'.gates, n + v.val ∈ g.inputs) ∨ C'.output = n + v.val) → ((∃ g ∈ C.gates, n + (k.succAbove v).val ∈ g.inputs) ∨ C.output = n + (k.succAbove v).val)) := by
  intro n m A k C hrep _ _
  have hk : k.val ≤ m := Nat.lt_succ_iff.mp k.isLt
  refine ⟨⟨C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)),
    rho (n + k.val) (n + m + 1 + C.gates.length) C.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show (C.gates.map _).length = C.gates.length
    rw [List.length_map]
  · intro hF g hg
    have hg' : g ∈ C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
    rw [List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    have hf := hF g0 hg0
    refine ⟨hf.1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact hf.2
  · intro u v
    have hr : (C.gates.foldl stp (oneEach u (k.succAbove v))).getD C.output false =
      A u (k.succAbove v) := hrep u (k.succAbove v)
    show ((C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length))).foldl stp (oneEach u v)).getD
      (rho (n + k.val) (n + m + 1 + C.gates.length) C.output) false = A u (k.succAbove v)
    rw [← hr]
    have hlx : (oneEach u v).length = n + m := by simp [oneEach]
    have hlx2 : (oneEach u (k.succAbove v)).length = n + m + 1 := by simp [oneEach]; omega
    refine sim (n + k.val) (n + m + 1 + C.gates.length) (oneEach u (k.succAbove v)) (oneEach u v)
      (by rw [hlx, hlx2]) (by rw [hlx]; omega) ?_ C.gates (by rw [hlx]; omega) C.output
    intro i
    apply bool_iff
    rw [oe, oe, sa_val]
    have hu := u.isLt
    have hv := v.isLt
    unfold rho
    split_ifs <;> omega
  · intro u hu
    have hul := u.isLt
    have key : ∀ i, rho (n + k.val) (n + m + 1 + C.gates.length) i = u.val → i = u.val := by
      intro i
      unfold rho
      split_ifs <;> omega
    rcases hu with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      have hmem' : u.val ∈ g0.inputs.map (rho (n + k.val) (n + m + 1 + C.gates.length)) := hmem
      rw [List.mem_map] at hmem'
      obtain ⟨i, hi, hiu⟩ := hmem'
      have := key i hiu
      subst this
      exact Or.inl ⟨g0, hg0, hi⟩
    · exact Or.inr (key _ ho)
  · intro v hv
    have hvl := v.isLt
    have key : ∀ i, rho (n + k.val) (n + m + 1 + C.gates.length) i = n + v.val →
        i = n + (k.succAbove v).val := by
      intro i
      rw [sa_val]
      unfold rho
      split_ifs <;> omega
    rcases hv with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      have hmem' : n + v.val ∈ g0.inputs.map (rho (n + k.val) (n + m + 1 + C.gates.length)) := hmem
      rw [List.mem_map] at hmem'
      obtain ⟨i, hi, hiu⟩ := hmem'
      have := key i hiu
      subst this
      exact Or.inl ⟨g0, hg0, hi⟩
    · exact Or.inr (key _ ho)

end PEqualNP.Outside.L_meta_23622

theorem PEqualNP.Outside.L_meta_23622 : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.Represents.Represents A C → (∀ g ∈ C.gates, n + k.val ∉ g.inputs) → C.output ≠ n + k.val → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, C'.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo C') ∧ PEqualNP.Represents.Represents (fun u v => A u (k.succAbove v)) C' ∧ (∀ u : Fin n, ((∃ g ∈ C'.gates, u.val ∈ g.inputs) ∨ C'.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C'.gates, n + v.val ∈ g.inputs) ∨ C'.output = n + v.val) → ((∃ g ∈ C.gates, n + (k.succAbove v).val ∈ g.inputs) ∨ C.output = n + (k.succAbove v).val)) :=
  PEqualNP.Outside.L_meta_23622.main

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17832

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rg (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ren (ρ : ℕ → ℕ) (gs : List Gate) : ∀ (w w' : List Bool) (m : ℕ), w.length = m →
    w'.length = m → (∀ i, i < m → ρ i < m) → (∀ i, m ≤ i → ρ i = i) →
    (∀ i, w'.getD (ρ i) false = w.getD i false) →
    ∀ i, ((gs.map (rg ρ)).foldl step w').getD (ρ i) false = (gs.foldl step w).getD i false := by
  induction gs with
  | nil => intro w w' m _ _ _ _ h i; simpa using h i
  | cons g gs ih =>
    intro w w' m hw hw' hlt hfix hrel
    simp only [List.map_cons, List.foldl_cons]
    apply ih (step w g) (step w' (rg ρ g)) (m + 1)
    · simp [step, hw]
    · simp [step, hw']
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact Nat.lt_succ_of_lt (hlt i h)
      · rw [h, hfix m le_rfl]; exact Nat.lt_succ_self m
    · intro i hi; exact hfix i (Nat.le_of_succ_le hi)
    · intro i
      have hv : (rg ρ g).op.eval ((rg ρ g).inputs.map fun i => w'.getD i false)
          = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [rg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hrel a
      simp only [step, hv]
      rcases Nat.lt_or_ge i m with h | h
      · have h2 := hlt i h
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hrel i
      · rw [hfix i h]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
          hw, hw']

def r (n : ℕ) (ρ : Fin n → Fin n) (i : ℕ) : ℕ := if h : i < n then (ρ ⟨i, h⟩ : ℕ) else i

theorem main (n : ℕ) (ρ : Fin n → Fin n) (C : Circuit) (hC : FanInTwo C) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size ∧ ∀ (x : Fin n → Bool) (b : Bool) (k : ℕ),
      (C'.wires (List.ofFn x ++ [b])).getD (n + k) false
        = (C.wires (List.ofFn (x ∘ ρ) ++ [b])).getD (n + k) false := by
  refine ⟨⟨C.gates.map (rg (r n ρ)), C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h := hC g0 hg0
    simpa [rg] using h
  · simp [Circuit.size]
  · intro x b k
    have h := ren (r n ρ) C.gates (List.ofFn (x ∘ ρ) ++ [b]) (List.ofFn x ++ [b]) (n + 1)
      (by simp) (by simp)
      (by
        intro i hi
        unfold r
        split_ifs with h1
        · exact Nat.lt_succ_of_lt (ρ ⟨i, h1⟩).isLt
        · exact hi)
      (by
        intro i hi
        unfold r
        rw [dif_neg (by omega)])
      (by
        intro i
        unfold r
        split_ifs with h1
        · rw [List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simpa using h1),
            List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using h1)]
          simp
        · rw [List.getD_append_right _ _ _ _ (by simpa using h1),
            List.getD_append_right _ _ _ _ (by simpa using h1)]
          simp)
      (n + k)
    have hr : r n ρ (n + k) = n + k := by
      unfold r
      rw [dif_neg (by omega)]
    rw [hr] at h
    exact h

end PEqualNP.Outside.L_meta_17832

theorem PEqualNP.Outside.L_meta_17832 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : Bool) (x8 : ℕ), (x5.wires (List.ofFn x6 ++ [x7])).getD (x1 + x8) Bool.false = (x3.wires (List.ofFn (x6 ∘ x2) ++ [x7])).getD (x1 + x8) Bool.false := by
  intro n ρ C hC
  exact PEqualNP.Outside.L_meta_17832.main n ρ C hC

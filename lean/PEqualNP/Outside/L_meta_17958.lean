import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17958

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem run_len (gs : List Gate) : ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih]
    simp [step]
    omega

theorem main (n : ℕ) (C : Circuit) (a b : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hnd : ∀ g ∈ C.gates, g.inputs.Nodup) (hab : a ≠ b) (ha : a < n + C.size) (hb : b < n + C.size) :
    PEqualNP.TopForm.IsAO2 n ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ ∧
    (∀ g ∈ (⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ : Circuit).gates, g.inputs.Nodup) ∧
    ∀ (x : Fin n → Bool), ∀ k, k < n + C.size →
      PEqualNP.BlindGate.wireValue ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ n x k
        = PEqualNP.BlindGate.wireValue C n x k := by
  obtain ⟨h1, h2, h3⟩ := hC
  have hsz : C.size = C.gates.length := rfl
  rw [hsz] at ha hb
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h1 g hg
    · exact Or.inl rfl
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · have e : gateAt ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ j = gateAt C j := by
        simp [gateAt, List.getElem?_append_left hlt]
      rw [e] at hi
      exact h2 j hlt i hi
    · subst heq
      have e : gateAt ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ C.gates.length
          = ⟨GateOp.and, [a, b]⟩ := by
        simp [gateAt]
      rw [e] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h3 g hg
    · rfl
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hnd g hg
    · simp [hab]
  · intro x k hk
    rw [hsz] at hk
    unfold PEqualNP.BlindGate.wireValue
    show ((C.gates ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).foldl step (List.ofFn x)).getD k false
      = (C.gates.foldl step (List.ofFn x)).getD k false
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact List.getD_append _ _ _ _ (by rw [run_len]; simpa using hk)

end PEqualNP.Outside.L_meta_17958

theorem PEqualNP.Outside.L_meta_17958 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) → x2 ≠ x3 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x9.size ≤ x1.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x9 ∧ (∀ x11 ∈ x9.gates, x11.inputs.Nodup) ∧ x9.output = (26 : ℕ) + x10 ∧ x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), ∀ x12 < (26 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x11 x12 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 x12 := by
  intro C a b hC hnd hab ha hb
  obtain ⟨h1, h2, h3⟩ := PEqualNP.Outside.L_meta_17958.main 26 C a b hC hnd hab ha hb
  refine ⟨⟨C.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩], 26 + C.size⟩, C.size, ?_, h1, h2, rfl, ?_, h3⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]

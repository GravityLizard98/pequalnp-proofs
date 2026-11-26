import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17844

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

end PEqualNP.Outside.L_meta_17844

theorem PEqualNP.Outside.L_meta_17844 : ∀ (x1 x2 : Fin (10 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)) (x6 : Fin (10 : ℕ) → Bool), { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate }] ++ x3.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(10 : ℕ) + ↑x4, (10 : ℕ) + ↑x5] : PEqualNP.CircuitLowerBounds.Gate }], output := (11 : ℕ) + x3.gates.length : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x6) = ((x3.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate }], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x6))).getD ((10 : ℕ) + ↑x4) Bool.false || (x3.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate }], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x6))).getD ((10 : ℕ) + ↑x5) Bool.false) := by
  intro a b C p q x
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
    List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [List.getD_append_right _ _ _ _ (by
    rw [PEqualNP.Outside.L_meta_17844.len]; simp)]
  rw [PEqualNP.Outside.L_meta_17844.len]
  simp [PEqualNP.CircuitLowerBounds.GateOp.eval]

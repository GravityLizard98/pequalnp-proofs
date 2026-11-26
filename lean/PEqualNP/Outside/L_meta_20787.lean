import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20787
open PEqualNP.CircuitLowerBounds

def C : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.or, [9, 2]⟩, ⟨GateOp.and, [9, 2]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [13, 3]⟩, ⟨GateOp.and, [13, 3]⟩, ⟨GateOp.not, [15]⟩, ⟨GateOp.and, [14, 16]⟩, ⟨GateOp.or, [17, 4]⟩, ⟨GateOp.and, [17, 4]⟩, ⟨GateOp.not, [19]⟩, ⟨GateOp.and, [18, 20]⟩, ⟨GateOp.or, [21, 5]⟩, ⟨GateOp.and, [21, 5]⟩, ⟨GateOp.not, [23]⟩, ⟨GateOp.and, [22, 24]⟩], 25⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def vec (k : ℕ) : Fin 6 → Bool := fun i => k.testBit i.val

set_option maxRecDepth 100000 in
theorem tab : ∀ k : Fin 64, C.eval (List.ofFn (vec k.val)) = (7608434000728254870 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex (vec k.val)) := by
  decide +kernel

theorem vec_surj (x : Fin 6 → Bool) : ∃ k : Fin 64, vec k.val = x := by
  refine ⟨⟨PEqualNP.MetaComplexity.tableIndex x, ?_⟩, ?_⟩
  · revert x; decide +kernel
  · revert x; decide +kernel

theorem main : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (7608434000728254870 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 20 := by
  refine ⟨C, fan, by decide, ?_⟩
  intro x
  obtain ⟨k, rfl⟩ := vec_surj x
  exact tab k

end PEqualNP.Outside.L_meta_20787

theorem PEqualNP.Outside.L_meta_20787 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (7608434000728254870 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 20 :=
  PEqualNP.Outside.L_meta_20787.main

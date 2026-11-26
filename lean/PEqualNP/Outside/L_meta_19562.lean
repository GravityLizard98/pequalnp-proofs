import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19562

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [6, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_19562

theorem PEqualNP.Outside.L_meta_19562 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236082 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19562.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19562.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

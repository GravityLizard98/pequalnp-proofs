import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19544

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [4, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [10, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_19544

theorem PEqualNP.Outside.L_meta_19544 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4590 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19544.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19544.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

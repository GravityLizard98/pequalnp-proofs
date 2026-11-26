import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19538

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩], 11⟩

end PEqualNP.Outside.L_meta_19538

theorem PEqualNP.Outside.L_meta_19538 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (279 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19538.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19538.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

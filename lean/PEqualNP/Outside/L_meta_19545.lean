import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19545

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.and, [1, 4]⟩, ⟨.or, [1, 4]⟩, ⟨.not, [8]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_19545

theorem PEqualNP.Outside.L_meta_19545 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4591 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19545.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19545.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

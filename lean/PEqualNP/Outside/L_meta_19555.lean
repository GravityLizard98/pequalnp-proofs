import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19555

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.and, [12, 2]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [6, 21]⟩, ⟨.or, [19, 12]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [25, 2]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [2, 21]⟩, ⟨.or, [22, 11]⟩, ⟨.or, [6, 27]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [20, 31]⟩, ⟨.and, [29, 26]⟩, ⟨.or, [31, 23]⟩, ⟨.or, [11, 24]⟩, ⟨.or, [24, 20]⟩, ⟨.and, [30, 32]⟩, ⟨.and, [35, 28]⟩, ⟨.and, [34, 36]⟩, ⟨.or, [33, 38]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [39, 41]⟩], 42⟩

end PEqualNP.Outside.L_meta_19555

theorem PEqualNP.Outside.L_meta_19555 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x2e87c9d235786996 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨PEqualNP.Outside.L_meta_19555.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19555.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

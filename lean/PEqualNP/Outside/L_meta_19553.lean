import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19553

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [11, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [14, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [23, 19]⟩, ⟨.or, [20, 24]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [24, 16]⟩, ⟨.or, [29, 16]⟩, ⟨.and, [31, 2]⟩, ⟨.or, [32, 22]⟩, ⟨.and, [26, 1]⟩, ⟨.and, [27, 6]⟩, ⟨.or, [29, 18]⟩, ⟨.and, [4, 36]⟩, ⟨.and, [3, 25]⟩, ⟨.and, [28, 5]⟩, ⟨.or, [38, 34]⟩, ⟨.and, [30, 7]⟩, ⟨.or, [33, 35]⟩, ⟨.or, [42, 40]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [39, 37]⟩, ⟨.or, [45, 44]⟩], 46⟩

end PEqualNP.Outside.L_meta_19553

theorem PEqualNP.Outside.L_meta_19553 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x2e87c9d235786996 : ℕ).testBit (8 * u.val + v.val)) 32) := by
  refine ⟨PEqualNP.Outside.L_meta_19553.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19553.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

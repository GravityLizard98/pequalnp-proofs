import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19552

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [9, 4]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [2, 14]⟩, ⟨.and, [6, 18]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [23, 1]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [24, 16]⟩, ⟨.or, [6, 29]⟩, ⟨.or, [30, 3]⟩, ⟨.and, [27, 28]⟩, ⟨.or, [24, 17]⟩, ⟨.or, [25, 3]⟩, ⟨.and, [26, 33]⟩, ⟨.and, [31, 10]⟩, ⟨.or, [32, 35]⟩, ⟨.or, [30, 19]⟩, ⟨.and, [34, 38]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [39, 22]⟩, ⟨.or, [41, 40]⟩], 42⟩

end PEqualNP.Outside.L_meta_19552

theorem PEqualNP.Outside.L_meta_19552 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0xc3b478740f9a8b65 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨PEqualNP.Outside.L_meta_19552.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19552.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

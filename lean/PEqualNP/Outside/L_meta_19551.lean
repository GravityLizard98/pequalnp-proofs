import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19551

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [11, 9]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [14, 13]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [8, 21]⟩, ⟨.or, [24, 16]⟩, ⟨.and, [20, 0]⟩, ⟨.or, [14, 24]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [18, 30]⟩, ⟨.and, [29, 2]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [26, 32]⟩, ⟨.and, [22, 3]⟩, ⟨.or, [15, 13]⟩, ⟨.and, [5, 23]⟩, ⟨.or, [30, 36]⟩, ⟨.and, [27, 7]⟩, ⟨.or, [35, 37]⟩, ⟨.or, [34, 28]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [42, 33]⟩, ⟨.and, [38, 6]⟩, ⟨.or, [44, 43]⟩, ⟨.or, [45, 39]⟩], 46⟩

end PEqualNP.Outside.L_meta_19551

theorem PEqualNP.Outside.L_meta_19551 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0xc3b478740f9a8b65 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨PEqualNP.Outside.L_meta_19551.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19551.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

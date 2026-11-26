import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19892

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [10, 8]⟩, ⟨.or, [16, 9]⟩, ⟨.and, [0, 17]⟩, ⟨.or, [16, 13]⟩, ⟨.and, [1, 19]⟩, ⟨.or, [14, 11]⟩, ⟨.or, [21, 10]⟩, ⟨.and, [2, 22]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [24, 15]⟩, ⟨.and, [25, 3]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [21, 9]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [15, 30]⟩, ⟨.and, [31, 5]⟩, ⟨.or, [18, 29]⟩, ⟨.or, [9, 30]⟩, ⟨.and, [6, 34]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [36, 15]⟩, ⟨.and, [37, 7]⟩, ⟨.or, [32, 20]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [33, 27]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [42, 40]⟩], 43⟩

end PEqualNP.Outside.L_meta_19892

theorem PEqualNP.Outside.L_meta_19892 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9886157967400379655 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨PEqualNP.Outside.L_meta_19892.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19892.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

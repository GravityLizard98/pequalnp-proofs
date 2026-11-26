import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19922

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [20, 14]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [19, 13]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [18, 15]⟩, ⟨.and, [0, 25]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [3, 24]⟩, ⟨.and, [22, 1]⟩, ⟨.and, [27, 4]⟩, ⟨.or, [12, 17]⟩, ⟨.and, [31, 5]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [32, 26]⟩, ⟨.or, [28, 34]⟩, ⟨.and, [23, 2]⟩, ⟨.and, [6, 33]⟩, ⟨.and, [7, 21]⟩, ⟨.or, [29, 35]⟩, ⟨.or, [30, 36]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 37]⟩], 43⟩

end PEqualNP.Outside.L_meta_19922

theorem PEqualNP.Outside.L_meta_19922 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5515944280522376865 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨PEqualNP.Outside.L_meta_19922.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19922.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

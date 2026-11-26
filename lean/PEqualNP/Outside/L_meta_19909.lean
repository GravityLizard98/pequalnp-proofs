import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19909

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.and, [2, 13]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [19, 2]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [12, 21]⟩, ⟨.or, [10, 26]⟩, ⟨.and, [4, 27]⟩, ⟨.or, [12, 25]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [26, 24]⟩, ⟨.or, [13, 22]⟩, ⟨.and, [18, 29]⟩, ⟨.and, [23, 30]⟩, ⟨.or, [34, 33]⟩, ⟨.and, [20, 24]⟩, ⟨.and, [32, 31]⟩, ⟨.or, [36, 28]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [39, 35]⟩], 40⟩

end PEqualNP.Outside.L_meta_19909

theorem PEqualNP.Outside.L_meta_19909 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10998964658842522050 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨PEqualNP.Outside.L_meta_19909.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19909.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

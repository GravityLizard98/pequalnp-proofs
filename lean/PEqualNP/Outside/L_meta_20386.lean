import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20386

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [4, 13]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [15, 0]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [12, 23]⟩, ⟨.or, [21, 15]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [22, 14]⟩, ⟨.or, [26, 19]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [16, 10]⟩, ⟨.or, [30, 19]⟩, ⟨.or, [25, 30]⟩, ⟨.or, [25, 26]⟩, ⟨.and, [32, 24]⟩, ⟨.and, [31, 7]⟩, ⟨.and, [28, 27]⟩, ⟨.and, [33, 6]⟩, ⟨.or, [35, 37]⟩, ⟨.and, [29, 20]⟩, ⟨.or, [39, 36]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [38, 41]⟩], 42⟩

end PEqualNP.Outside.L_meta_20386

theorem PEqualNP.Outside.L_meta_20386 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4361677255813263645 : ℕ).testBit (8 * u.val + v.val)) 27) := by
  refine ⟨PEqualNP.Outside.L_meta_20386.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_20386.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

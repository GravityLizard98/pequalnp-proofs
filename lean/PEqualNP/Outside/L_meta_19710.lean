import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19710

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [15, 8]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [21, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [23, 13]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [12, 27]⟩, ⟨.or, [18, 10]⟩, ⟨.and, [29, 30]⟩, ⟨.or, [27, 30]⟩, ⟨.and, [32, 25]⟩, ⟨.and, [6, 28]⟩, ⟨.or, [33, 22]⟩, ⟨.or, [29, 13]⟩, ⟨.and, [7, 36]⟩, ⟨.or, [35, 37]⟩, ⟨.or, [38, 26]⟩, ⟨.or, [34, 31]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [20, 41]⟩], 42⟩

end PEqualNP.Outside.L_meta_19710

theorem PEqualNP.Outside.L_meta_19710 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4081470838034108865 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨PEqualNP.Outside.L_meta_19710.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19710.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

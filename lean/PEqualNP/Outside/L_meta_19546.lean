import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19546

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [22, 17]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [24, 19]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [21, 16]⟩, ⟨.and, [22, 17]⟩, ⟨.and, [23, 18]⟩, ⟨.and, [24, 19]⟩, ⟨.and, [25, 20]⟩, ⟨.or, [26, 27]⟩, ⟨.or, [32, 28]⟩, ⟨.or, [33, 29]⟩, ⟨.or, [34, 30]⟩, ⟨.or, [35, 31]⟩], 36⟩

end PEqualNP.Outside.L_meta_19546

theorem PEqualNP.Outside.L_meta_19546 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 7 => decide (u ≠ v)) 23 := by
  refine ⟨PEqualNP.Outside.L_meta_19546.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19546.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

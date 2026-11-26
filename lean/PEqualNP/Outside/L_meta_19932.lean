import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19932

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [14, 10]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [21, 8]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [19, 16]⟩, ⟨.and, [24, 2]⟩, ⟨.and, [23, 1]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [26, 25]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [12, 20]⟩, ⟨.or, [30, 14]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [22, 10]⟩, ⟨.or, [20, 29]⟩, ⟨.and, [33, 5]⟩, ⟨.or, [30, 19]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [29, 18]⟩, ⟨.and, [0, 27]⟩, ⟨.and, [38, 7]⟩, ⟨.and, [3, 34]⟩, ⟨.or, [39, 35]⟩, ⟨.or, [41, 42]⟩, ⟨.or, [32, 43]⟩, ⟨.or, [44, 28]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [40, 46]⟩], 47⟩

end PEqualNP.Outside.L_meta_19932

theorem PEqualNP.Outside.L_meta_19932 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16436895475263517410 : ℕ).testBit (8 * u.val + v.val)) 33) := by
  refine ⟨PEqualNP.Outside.L_meta_19932.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19932.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19712

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [10, 14]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [2, 0]⟩, ⟨.and, [20, 6]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [4, 1]⟩, ⟨.and, [25, 18]⟩, ⟨.or, [4, 24]⟩, ⟨.or, [21, 12]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [21, 9]⟩, ⟨.and, [15, 27]⟩, ⟨.and, [29, 10]⟩, ⟨.or, [30, 33]⟩, ⟨.and, [17, 5]⟩, ⟨.or, [34, 32]⟩, ⟨.and, [19, 22]⟩, ⟨.and, [31, 7]⟩, ⟨.or, [23, 37]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [26, 35]⟩, ⟨.or, [36, 41]⟩, ⟨.or, [42, 40]⟩], 43⟩

end PEqualNP.Outside.L_meta_19712

theorem PEqualNP.Outside.L_meta_19712 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (838035264769107540 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨PEqualNP.Outside.L_meta_19712.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19712.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19548

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [4, 14]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [18, 11]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [17, 11]⟩, ⟨.or, [21, 5]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [8, 24]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [22, 28]⟩, ⟨.and, [26, 24]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [22, 1]⟩, ⟨.and, [32, 21]⟩, ⟨.and, [29, 23]⟩, ⟨.or, [22, 27]⟩, ⟨.or, [31, 33]⟩, ⟨.and, [35, 0]⟩, ⟨.or, [25, 19]⟩, ⟨.and, [36, 38]⟩, ⟨.or, [37, 30]⟩, ⟨.or, [39, 34]⟩, ⟨.or, [41, 40]⟩], 42⟩

end PEqualNP.Outside.L_meta_19548

theorem PEqualNP.Outside.L_meta_19548 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x4eb463b8a3475c99 : ℕ).testBit (8 * u.val + v.val)) 30) := by
  refine ⟨PEqualNP.Outside.L_meta_19548.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19548.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

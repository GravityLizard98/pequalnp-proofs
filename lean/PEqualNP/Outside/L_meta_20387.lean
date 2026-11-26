import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20387

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [9, 2]⟩, ⟨.or, [3, 1]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [19, 14]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [20, 5]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [11, 24]⟩, ⟨.or, [28, 7]⟩, ⟨.or, [16, 27]⟩, ⟨.or, [4, 23]⟩, ⟨.or, [29, 26]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [25, 22]⟩, ⟨.or, [21, 4]⟩, ⟨.and, [33, 34]⟩, ⟨.or, [1, 24]⟩, ⟨.or, [37, 22]⟩, ⟨.or, [29, 3]⟩, ⟨.and, [32, 35]⟩, ⟨.and, [38, 31]⟩, ⟨.or, [41, 36]⟩, ⟨.and, [39, 30]⟩, ⟨.or, [40, 42]⟩, ⟨.or, [43, 44]⟩], 45⟩

end PEqualNP.Outside.L_meta_20387

theorem PEqualNP.Outside.L_meta_20387 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16399645806311595450 : ℕ).testBit (8 * u.val + v.val)) 30) := by
  refine ⟨PEqualNP.Outside.L_meta_20387.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_20387.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

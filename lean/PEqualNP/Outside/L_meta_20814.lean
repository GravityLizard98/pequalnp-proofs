import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20814

theorem hA (s : Finset ℕ) (R : ℕ → ℕ) (d1 : DecidablePred fun w => 2 ≤ R w)
    (d3 : DecidablePred fun w => 1 ≤ R w) :
    (∑ w ∈ @Finset.filter ℕ (fun w => 2 ≤ R w) d1 s, R w) +
      2 * (@Finset.filter ℕ (fun w => 1 ≤ R w) d3 s).card ≤ 2 * ∑ w ∈ s, R w := by
  rw [Finset.sum_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  split_ifs <;> omega

theorem hB (n m : ℕ) (R : ℕ → ℕ) (isNot : ℕ → Prop)
    (d2 : DecidablePred fun j => isNot j ∨ 2 ≤ R (m + j))
    (d4 : DecidablePred fun i => i + 1 < n) (d5 : DecidablePred isNot)
    (h : ∀ j < n, (R (m + j) = 0 ↔ j + 1 = n)) :
    (∑ j ∈ @Finset.filter ℕ (fun j => isNot j ∨ 2 ≤ R (m + j)) d2 (Finset.range n), R (m + j)) ≤
      2 * (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < n) d4 (Finset.range n), (R (m + j) - 1)) +
      2 * (@Finset.filter ℕ isNot d5 (Finset.range n)).card := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hjn := Finset.mem_range.mp hj
  have hj' := h j hjn
  split_ifs with h1 h2 h3 <;> try omega
  rcases h1 with h1 | h1 <;> first | omega | exact absurd h1 h3

end PEqualNP.Outside.L_meta_20814

theorem PEqualNP.Outside.L_meta_20814 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
  (∑ w ∈ @Finset.filter ℕ
        (fun w1 => 2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w1)
        (fun d1 => Classical.propDecidable _) (Finset.range m),
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
    (∑ j ∈ @Finset.filter ℕ
        (fun j1 => (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).op =
            PEqualNP.CircuitLowerBounds.GateOp.not ∨
          2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j1))
        (fun d2 => Classical.propDecidable _) (Finset.range C.size),
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) +
    2 * (@Finset.filter ℕ
        (fun w2 => 1 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w2)
        (fun d3 => Classical.propDecidable _) (Finset.range m)).card ≤
  2 * ((∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d4 => Classical.propDecidable _)
          (Finset.range C.size),
        (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1)) +
      (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d5 => Classical.propDecidable _)
          (Finset.range C.size)).card) := by
  intro m C _ _ _ h
  have a := PEqualNP.Outside.L_meta_20814.hA (Finset.range m)
    (fun w => PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w)
    (fun _ => Classical.propDecidable _) (fun _ => Classical.propDecidable _)
  have b := PEqualNP.Outside.L_meta_20814.hB C.size m
    (fun w => PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w)
    (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun _ => Classical.propDecidable _) (fun _ => Classical.propDecidable _)
    (fun _ => Classical.propDecidable _) h
  omega

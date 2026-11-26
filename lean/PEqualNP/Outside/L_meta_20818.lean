import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20818

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem part1 (m N : ℕ) (C : Circuit)
    (hlen : ∀ g < C.size, (gateAt C g).inputs.length ≤ 2) (root special : ℕ → Prop)
    (d5 : DecidablePred root) (d6 : DecidablePred fun g => special (m + g))
    (hroot : ∀ w, root w → w = C.output ∨
      ∃ g, (g < C.size ∧ w ∈ (gateAt C g).inputs) ∧ special (m + g)) :
    (@Finset.filter ℕ root d5 (Finset.range N)).card ≤
      2 * (@Finset.filter ℕ (fun g => special (m + g)) d6 (Finset.range C.size)).card + 1 := by
  have h1 : @Finset.filter ℕ root d5 (Finset.range N) ⊆
      insert C.output ((@Finset.filter ℕ (fun g => special (m + g)) d6
        (Finset.range C.size)).biUnion (fun g => (gateAt C g).inputs.toFinset)) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rcases hroot w hw.2 with h | ⟨g, hf, hs⟩
    · rw [h]; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_biUnion]
      refine ⟨g, ?_, List.mem_toFinset.mpr hf.2⟩
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hf.1, hs⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.card_insert_le C.output ((@Finset.filter ℕ (fun g => special (m + g)) d6
        (Finset.range C.size)).biUnion (fun g => (gateAt C g).inputs.toFinset))
  have h4 := Finset.card_biUnion_le_card_mul (@Finset.filter ℕ (fun g => special (m + g)) d6
        (Finset.range C.size)) (fun g => (gateAt C g).inputs.toFinset) 2 (by
    intro g hg
    rw [Finset.mem_filter, Finset.mem_range] at hg
    exact le_trans (List.toFinset_card_le _) (hlen g hg.1))
  omega

theorem part2 (n m : ℕ) (R : ℕ → ℕ) (isNot sp : ℕ → Prop)
    (d2 : DecidablePred sp)
    (d4 : DecidablePred fun i => i + 1 < n) (d5 : DecidablePred isNot)
    (hs : ∀ g < n, sp g → isNot g ∨ 2 ≤ R (m + g))
    (h : ∀ j < n, (R (m + j) = 0 ↔ j + 1 = n)) :
    (@Finset.filter ℕ sp d2 (Finset.range n)).card ≤
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < n) d4 (Finset.range n), (R (m + j) - 1)) +
      (@Finset.filter ℕ isNot d5 (Finset.range n)).card := by
  rw [Finset.sum_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hjn := Finset.mem_range.mp hj
  have hj' := h j hjn
  split_ifs with h1 h2 h3 <;> try omega
  all_goals (rcases hs j hjn h1 with h1 | h1 <;> first | omega | exact absurd h1 ‹_›)

theorem hlen (C : Circuit)
    (hg : ∀ g ∈ C.gates,
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ g < C.size, (gateAt C g).inputs.length ≤ 2 := by
  intro g hgs
  have hgl : g < C.gates.length := hgs
  have hm : gateAt C g ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hgl]
    exact List.getElem_mem hgl
  rcases hg _ hm with h | h <;> omega

end PEqualNP.Outside.L_meta_20818

theorem PEqualNP.Outside.L_meta_20818 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size → C.output + 1 = m + C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
let R : ℕ → ℕ := fun w => PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w
let special : ℕ → Prop := fun w => (w < m ∧ 2 ≤ R w) ∨
  (m ≤ w ∧ w < m + C.size ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).op = PEqualNP.CircuitLowerBounds.GateOp.not ∨ 2 ≤ R w))
let ordinary : ℕ → Prop := fun w => (w < m ∧ R w = 1) ∨
  (m ≤ w ∧ w < m + C.size ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ R w ≤ 1)
let feeds : ℕ → ℕ → Prop := fun w g => g < C.size ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs
let edge : ℕ → ℕ → Prop := fun w w' => ordinary w ∧ ordinary w' ∧ m ≤ w' ∧ feeds w (w' - m)
let root : ℕ → Prop := fun w => ordinary w ∧ (w = C.output ∨ ∃ g, feeds w g ∧ special (m + g))
let skel : ℕ → Prop := fun w => ordinary w ∧ m ≤ w ∧
  ∃ g w0, ordinary (m + g) ∧ feeds w0 g ∧ special w0 ∧ Relation.ReflTransGen edge (m + g) w
let chainGate : ℕ → Prop := fun w => skel w ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).inputs.countP
    (fun i => @decide (special i ∨ skel i) (Classical.propDecidable _)) = 1
let chainTop : ℕ → Prop := fun w => chainGate w ∧ (root w ∨ ∃ g, feeds w g ∧ ¬ chainGate (m + g))
let ext : ℕ := ∑ g ∈ @Finset.filter ℕ (fun g1 => ordinary (m + g1)) (fun d1 => Classical.propDecidable _)
    (Finset.range C.size),
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.countP
    (fun i => @decide (special i) (Classical.propDecidable _))
let Fin_ : ℕ := ∑ w ∈ Finset.range m, R w
let X : ℕ := ∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
    (Finset.range C.size), (R (m + j) - 1)
let t : ℕ := (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
    PEqualNP.CircuitLowerBounds.GateOp.not) (fun d3 => Classical.propDecidable _) (Finset.range C.size)).card
let r : ℕ := (@Finset.filter ℕ (fun w => 1 ≤ R w) (fun d4 => Classical.propDecidable _) (Finset.range m)).card
(@Finset.filter ℕ root (fun d5 => Classical.propDecidable _) (Finset.range (m + C.size))).card ≤
    2 * (@Finset.filter ℕ (fun g2 => special (m + g2)) (fun d6 => Classical.propDecidable _)
      (Finset.range C.size)).card + 1 ∧
  (@Finset.filter ℕ (fun g3 => special (m + g3)) (fun d7 => Classical.propDecidable _)
      (Finset.range C.size)).card ≤ X + t := by
  intro m C hg _ _ _ hlast R special ordinary feeds edge root skel chainGate chainTop ext Fin_ X t r
  refine ⟨PEqualNP.Outside.L_meta_20818.part1 m (m + C.size) C
    (PEqualNP.Outside.L_meta_20818.hlen C hg) root special _ _ ?_,
    PEqualNP.Outside.L_meta_20818.part2 C.size m R
      (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun g => special (m + g)) _ _ _ ?_ hlast⟩
  · intro w hw
    have hw2 : ordinary w ∧ (w = C.output ∨ ∃ g, feeds w g ∧ special (m + g)) := hw
    exact hw2.2
  · intro g _ hs
    have hs2 : (m + g < m ∧ 2 ≤ R (m + g)) ∨ (m ≤ m + g ∧ m + g < m + C.size ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C (m + g - m)).op =
        PEqualNP.CircuitLowerBounds.GateOp.not ∨ 2 ≤ R (m + g))) := hs
    rcases hs2 with h | ⟨_, _, h⟩
    · omega
    · rwa [Nat.add_sub_cancel_left] at h

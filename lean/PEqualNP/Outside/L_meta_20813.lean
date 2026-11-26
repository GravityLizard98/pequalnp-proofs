import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20813

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem sumcount (l : List ℕ) (S : Finset ℕ) (h : ∀ i ∈ l, i ∈ S) :
    ∑ w ∈ S, l.count w = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons]
    rw [ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]
    simp [ha]

theorem gmem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

theorem dc (m : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hrb : ReadsBack m C) (inst : DecidablePred fun k => (gateAt C k).op = GateOp.not) :
    C.size + C.size = (∑ w ∈ Finset.range m, readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size, readsIn C (Finset.range C.size) (m + j)) +
      (@Finset.filter ℕ (fun k => (gateAt C k).op = GateOp.not) inst (Finset.range C.size)).card := by
  have e1 : ∑ w ∈ Finset.range (m + C.size), readsIn C (Finset.range C.size) w =
      (∑ w ∈ Finset.range m, readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size, readsIn C (Finset.range C.size) (m + j)) :=
    Finset.sum_range_add _ m C.size
  have e2 : ∑ w ∈ Finset.range (m + C.size), readsIn C (Finset.range C.size) w =
      ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length := by
    unfold readsIn
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    apply sumcount
    intro i hi
    have hj' : j < C.gates.length := hj
    have := hrb j hj' i hi
    rw [Finset.mem_range]
    show i < m + C.gates.length
    omega
  have e3 : (@Finset.filter ℕ (fun k => (gateAt C k).op = GateOp.not) inst (Finset.range C.size)).card =
      ∑ j ∈ Finset.range C.size, if (gateAt C j).op = GateOp.not then 1 else 0 :=
    Finset.card_filter _ _
  have e4 : ∑ j ∈ Finset.range C.size,
      ((gateAt C j).inputs.length + if (gateAt C j).op = GateOp.not then 1 else 0) =
      ∑ j ∈ Finset.range C.size, 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rcases hg _ (gmem C j hj) with ⟨h, hl⟩ | ⟨h, hl⟩
    · have hne : ¬ (gateAt C j).op = GateOp.not := by
        intro e
        rcases h with h | h <;> rw [h] at e <;> cases e
      rw [if_neg hne, hl]
    · rw [if_pos h, hl]
  rw [Finset.sum_add_distrib] at e4
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at e4
  omega

theorem count2 (s : ℕ) (f : ℕ → ℕ) (inst : DecidablePred fun i => i + 1 < s) (hs : 0 < s)
    (h : ∀ j < s, (f j = 0 ↔ j + 1 = s)) :
    ∑ j ∈ Finset.range s, f j =
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < s) inst (Finset.range s), (f j - 1)) + (s - 1) := by
  have e : @Finset.filter ℕ (fun i => i + 1 < s) inst (Finset.range s) = Finset.range (s - 1) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    omega
  rw [e]
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [Finset.sum_range_succ, (h k (by omega)).2 rfl]
  have e5 : ∑ j ∈ Finset.range k, f j = ∑ j ∈ Finset.range k, ((f j - 1) + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have := h j (by omega)
    omega
  rw [e5, Finset.sum_add_distrib]
  simp

theorem main : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
  (C.size + C.size =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size,
        PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) +
      (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d1 => Classical.propDecidable _)
          (Finset.range C.size)).card) ∧
  (C.size + 1 =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
          (Finset.range C.size),
        (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1)) +
      (@Finset.filter ℕ (fun k2 => (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d3 => Classical.propDecidable _)
          (Finset.range C.size)).card) := by
  intro m C hg hrb hs hlast
  have h1 := dc m C hg hrb (fun d3 => Classical.propDecidable _)
  have h2 := count2 C.size (fun j => readsIn C (Finset.range C.size) (m + j))
    (fun d2 => Classical.propDecidable _) hs hlast
  refine ⟨h1, ?_⟩
  omega

end PEqualNP.Outside.L_meta_20813

theorem PEqualNP.Outside.L_meta_20813 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
  (C.size + C.size =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size,
        PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) +
      (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d1 => Classical.propDecidable _)
          (Finset.range C.size)).card) ∧
  (C.size + 1 =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
          (Finset.range C.size),
        (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1)) +
      (@Finset.filter ℕ (fun k2 => (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d3 => Classical.propDecidable _)
          (Finset.range C.size)).card) :=
  PEqualNP.Outside.L_meta_20813.main

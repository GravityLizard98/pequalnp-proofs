import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20819

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem cp (l : List ℕ) (T : Finset ℕ) (p : ℕ → Prop) (dp : ∀ i, Decidable (p i))
    (h : ∀ i ∈ l, i ∈ T) :
    l.countP (fun i => @decide (p i) (dp i)) = ∑ w ∈ T, if p w then l.count w else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have e : ∀ w, (if p w then (a :: l).count w else 0) =
        (if p w then l.count w else 0) + (if a = w then (if p a then 1 else 0) else 0) := by
      intro w
      rw [List.count_cons]
      by_cases h1 : a = w
      · subst h1
        by_cases h2 : p a <;> simp [h2]
      · by_cases h2 : p w <;> simp [h1, h2]
    rw [Finset.sum_congr rfl (fun w _ => e w), Finset.sum_add_distrib,
      ← ih (fun i hi => h i (List.mem_cons_of_mem _ hi)), List.countP_cons]
    simp [ha]

theorem core (m s : ℕ) (R : ℕ → ℕ) (inp : ℕ → List ℕ) (isnot : ℕ → Prop) (special ordinary : ℕ → Prop)
    (dS : ∀ i, Decidable (special i)) (dO : DecidablePred fun g => ordinary (m + g))
    (d2 : DecidablePred fun i => i + 1 < s) (d3 : DecidablePred isnot)
    (d4 : DecidablePred fun w => 1 ≤ R w)
    (hR : ∀ w, R w = ∑ j ∈ Finset.range s, (inp j).count w)
    (hrb : ∀ j < s, ∀ i ∈ inp j, i < m + s)
    (hlast : ∀ j < s, (R (m + j) = 0 ↔ j + 1 = s))
    (hs1 : ∀ w < m, special w → 2 ≤ R w)
    (hs2 : ∀ j < s, special (m + j) → isnot j ∨ 2 ≤ R (m + j)) :
    (∑ g ∈ @Finset.filter ℕ (fun g1 => ordinary (m + g1)) dO (Finset.range s),
        (inp g).countP (fun i => @decide (special i) (dS i))) +
      2 * (@Finset.filter ℕ (fun w => 1 ≤ R w) d4 (Finset.range m)).card ≤
    2 * ((∑ w ∈ Finset.range m, R w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < s) d2 (Finset.range s), (R (m + j) - 1)) +
      (@Finset.filter ℕ isnot d3 (Finset.range s)).card) := by
  have hA : (∑ g ∈ @Finset.filter ℕ (fun g1 => ordinary (m + g1)) dO (Finset.range s),
        (inp g).countP (fun i => @decide (special i) (dS i))) ≤
      ∑ g ∈ Finset.range s, (inp g).countP (fun i => @decide (special i) (dS i)) :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hB : ∑ g ∈ Finset.range s, (inp g).countP (fun i => @decide (special i) (dS i)) =
      ∑ g ∈ Finset.range s, ∑ w ∈ Finset.range (m + s), if special w then (inp g).count w else 0 := by
    apply Finset.sum_congr rfl
    intro g hg
    rw [Finset.mem_range] at hg
    exact cp _ _ _ _ (fun i hi => Finset.mem_range.2 (hrb g hg i hi))
  have hC : ∑ g ∈ Finset.range s, ∑ w ∈ Finset.range (m + s), (if special w then (inp g).count w else 0) =
      ∑ w ∈ Finset.range (m + s), if special w then R w else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : special w
    · simp [h, hR]
    · simp [h]
  have hD : ∑ w ∈ Finset.range (m + s), (if special w then R w else 0) =
      (∑ w ∈ Finset.range m, if special w then R w else 0) +
      (∑ j ∈ Finset.range s, if special (m + j) then R (m + j) else 0) :=
    Finset.sum_range_add _ m s
  have hE : ∑ w ∈ Finset.range m, ((if special w then R w else 0) + 2 * (if 1 ≤ R w then 1 else 0)) ≤
      ∑ w ∈ Finset.range m, 2 * R w := by
    apply Finset.sum_le_sum
    intro w hw
    rw [Finset.mem_range] at hw
    by_cases h : special w
    · have := hs1 w hw h
      rw [ifp h]
      split_ifs <;> omega
    · rw [ifn h]
      split_ifs <;> omega
  have hF : ∑ j ∈ Finset.range s, (if special (m + j) then R (m + j) else 0) ≤
      ∑ j ∈ Finset.range s, (2 * (if j + 1 < s then R (m + j) - 1 else 0) + 2 * (if isnot j then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hl := hlast j hj
    by_cases h : special (m + j)
    · have := hs2 j hj h
      rw [ifp h]
      by_cases h1 : j + 1 < s
      · rw [ifp h1]
        rcases this with h2 | h2
        · rw [ifp h2]; omega
        · split_ifs <;> omega
      · rw [ifn h1]
        have : R (m + j) = 0 := hl.2 (by omega)
        omega
    · rw [ifn h]
      exact Nat.zero_le _
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hE hF
  have e1 : (@Finset.filter ℕ (fun w => 1 ≤ R w) d4 (Finset.range m)).card =
      ∑ w ∈ Finset.range m, if 1 ≤ R w then 1 else 0 := Finset.card_filter _ _
  have e2 : (@Finset.filter ℕ isnot d3 (Finset.range s)).card =
      ∑ j ∈ Finset.range s, if isnot j then 1 else 0 := Finset.card_filter _ _
  have e3 : (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < s) d2 (Finset.range s), (R (m + j) - 1)) =
      ∑ j ∈ Finset.range s, if j + 1 < s then R (m + j) - 1 else 0 := Finset.sum_filter _ _
  omega

theorem main : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
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
ext + 2 * r ≤ 2 * (Fin_ + X + t) := by
  intro m C hg hrb hs hout hlast R special ordinary feeds edge root skel chainGate chainTop ext Fin_ X t r
  exact core m C.size R (fun j => (gateAt C j).inputs)
    (fun k => (gateAt C k).op = GateOp.not) special ordinary _ _ _ _ _
    (fun w => rfl)
    (fun j hj i hi => by
      have hj' : j < C.gates.length := hj
      have := hrb j hj' i hi
      show i < m + C.gates.length
      omega)
    hlast
    (fun w hw h => by
      rcases h with h | h
      · exact h.2
      · omega)
    (fun j hj h => by
      rcases h with h | h
      · omega
      · have e : m + j - m = j := by omega
        have h2 := h.2.2
        rw [e] at h2
        exact h2)

end PEqualNP.Outside.L_meta_20819

theorem PEqualNP.Outside.L_meta_20819 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
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
ext + 2 * r ≤ 2 * (Fin_ + X + t) :=
  PEqualNP.Outside.L_meta_20819.main

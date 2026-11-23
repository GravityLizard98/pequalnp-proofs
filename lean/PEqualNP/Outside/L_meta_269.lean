import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_269

lemma edgeCons (x : Fin 5 → Bool) (a b : ℕ) (ha : a < 5) (hb : b < 5) (es : List (ℕ × ℕ)) :
    (∃ u v : Fin 5, (u.val, v.val) ∈ (a, b) :: es ∧ x u = true ∧ x v = true) ↔
    (x ⟨a, ha⟩ = true ∧ x ⟨b, hb⟩ = true) ∨
      ∃ u v : Fin 5, (u.val, v.val) ∈ es ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Or.inl ⟨(show u = ⟨a, ha⟩ from Fin.ext h1) ▸ hu, (show v = ⟨b, hb⟩ from Fin.ext h2) ▸ hv⟩
    · exact Or.inr ⟨u, v, h, hu, hv⟩
  · rintro (⟨h1, h2⟩ | ⟨u, v, h, hu, hv⟩)
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, List.mem_cons_self, h1, h2⟩
    · exact ⟨u, v, List.mem_cons_of_mem _ h, hu, hv⟩

end PEqualNP.Outside.L_meta_269

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_269 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 14]⟩], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) → (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · refine ⟨{0, 5, 10}, by decide, ?_⟩
    intro j
    by_cases hj : j < 11
    · interval_cases j <;> simp
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hj)]
      simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    rw [PEqualNP.Outside.L_meta_269.edgeCons x 0 1 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_269.edgeCons x 0 2 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_269.edgeCons x 0 3 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_269.edgeCons x 0 4 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_269.edgeCons x 1 2 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_269.edgeCons x 1 3 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_269.edgeCons x 1 4 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_269.edgeCons x 2 3 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_269.edgeCons x 2 4 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_269.edgeCons x 3 4 (by decide) (by decide)]
    simp only [List.not_mem_nil, false_and, exists_false, or_false]
    have e0 : x 0 = x ⟨0, by decide⟩ := rfl
    have e1 : x 1 = x ⟨1, by decide⟩ := rfl
    have e2 : x 2 = x ⟨2, by decide⟩ := rfl
    have e3 : x 3 = x ⟨3, by decide⟩ := rfl
    have e4 : x 4 = x ⟨4, by decide⟩ := rfl
    rw [e0, e1, e2, e3, e4]
    generalize x ⟨0, by decide⟩ = a
    generalize x ⟨1, by decide⟩ = b
    generalize x ⟨2, by decide⟩ = c
    generalize x ⟨3, by decide⟩ = d
    generalize x ⟨4, by decide⟩ = e
    clear e0 e1 e2 e3 e4
    revert a b c d e
    decide

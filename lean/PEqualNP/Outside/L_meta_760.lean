import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_760

def G : SimpleGraph (Fin 6) where
  Adj := fun a b => a.val / 2 = b.val / 2 ∧ a ≠ b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

theorem acyc : G.IsAcyclic := by
  intro v p hp
  have h1 := p.adj_snd hp.not_nil
  have h2 := p.adj_penultimate hp.not_nil
  have h3 := hp.snd_ne_penultimate
  have key : ∀ a b c : Fin 6, (a.val / 2 = b.val / 2 ∧ a ≠ b) →
      (c.val / 2 = a.val / 2 ∧ c ≠ a) → b = c := by decide
  exact h3 (key _ _ _ h1 h2)

theorem three (T : Finset (Fin 6)) (a b c : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) : 3 ≤ T.card := by
  have hsub : ({a, b, c} : Finset (Fin 6)) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Finset (Fin 6)).card = 3 :=
    Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
  have := Finset.card_le_card hsub
  omega

theorem a01 : G.Adj 0 1 := ⟨by decide, by decide⟩
theorem a23 : G.Adj 2 3 := ⟨by decide, by decide⟩
theorem a45 : G.Adj 4 5 := ⟨by decide, by decide⟩

theorem cover (T : Finset (Fin 6)) (hT : ∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) :
    3 ≤ T.card := by
  rcases hT 0 1 a01 with h1 | h1 <;> rcases hT 2 3 a23 with h2 | h2 <;>
    rcases hT 4 5 a45 with h3 | h3 <;>
    exact three T _ _ _ (by decide) (by decide) (by decide) h1 h2 h3

theorem lower (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 6
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) s) : 5 ≤ s := by
  let _ : DecidableRel G.Adj := Classical.decRel _
  have h3 := PEqualNP.MetaComplexity.L104 6 3 s G acyc ⟨0, 1, a01⟩ cover (by
    convert h using 2
    rename_i x
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨i, j, hadj, hi, hj⟩
      have key : ∀ i j : Fin 6, (i.val / 2 = j.val / 2 ∧ i ≠ j) →
          (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
          (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by decide
      rcases key i j hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> simp [hi, hj]
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · exact ⟨0, 1, a01, h1, h2⟩
      · exact ⟨2, 3, a23, h1, h2⟩
      · exact ⟨4, 5, a45, h1, h2⟩)
  have hsub : ({s(0, 1), s(2, 3), s(4, 5)} : Finset (Sym2 (Fin 6))) ⊆ G.edgeFinset := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    · exact a01
    · exact a23
    · exact a45
  have hc : ({s(0, 1), s(2, 3), s(4, 5)} : Finset (Sym2 (Fin 6))).card = 3 := by decide
  have := Finset.card_le_card hsub
  omega

theorem upper (s : ℕ) (hs : 5 ≤ s) : PEqualNP.MetaComplexity.HasCircuitSize 6
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) s := by
  refine ⟨{ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 8]⟩], output := 10 }, ?_, ?_, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · exact hs
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := rfl
    rw [hx]
    beta_reduce
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl

end PEqualNP.Outside.L_meta_760

theorem PEqualNP.Outside.L_meta_760 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  intro s
  exact ⟨PEqualNP.Outside.L_meta_760.lower s, PEqualNP.Outside.L_meta_760.upper s⟩

import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25501 :
    ∀ (n m a gap : ℕ) (G : Fin n → Fin n → Bool)
    (rowPair : (Fin m × Bool) ↪ Fin n)
    (π : Equiv.Perm (Fin n)) (kept : Finset (Fin n)),
  let rowDistance := fun (firstRow secondRow : Fin n) =>
    (Finset.univ.filter (fun col : Fin n => G firstRow col ≠ G secondRow col)).card
  let colDistance := fun (firstCol secondCol : Fin n) =>
    (Finset.univ.filter (fun row : Fin n => G row firstCol ≠ G row secondCol)).card
  let minority := fun (line : Fin n) =>
    min (Finset.univ.filter (fun onCol : Fin n => G line onCol = true)).card
        (Finset.univ.filter (fun offCol : Fin n => G line offCol = false)).card
  (∀ i, rowDistance (rowPair (i, false)) (rowPair (i, true)) ≤ a) →
  (∀ b c, b ≠ c → a + gap ≤ colDistance b c) →
  (∀ u ∈ kept, ∀ v ∈ kept, G u (π v) = G v (π u)) →
  gap * m ≤ gap * (n - kept.card) +
    ∑ u ∈ Finset.univ \ kept, minority u := by
  intro n m a gap G rowPair π kept rowDistance colDistance minority hrow hcol hsym
  have hinj : ∀ i j : Fin m, ∀ b c : Bool, π (rowPair (i, b)) = π (rowPair (j, c)) → i = j ∧ b = c := by
    intro i j b c h
    have := rowPair.injective (π.injective h)
    exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj this).2⟩
  have hinj2 : ∀ i j : Fin m, ∀ b c : Bool, rowPair (i, b) = rowPair (j, c) → i = j ∧ b = c := by
    intro i j b c h
    have := rowPair.injective h
    exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj this).2⟩
  let P := Finset.univ.filter (fun i : Fin m => rowPair (i, false) ∈ kept ∧ rowPair (i, true) ∈ kept)
  let Q := Finset.univ.filter (fun i : Fin m => ¬ (rowPair (i, false) ∈ kept ∧ rowPair (i, true) ∈ kept))
  have hPQ : P.card + Q.card = m := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m)))
      (fun i : Fin m => rowPair (i, false) ∈ kept ∧ rowPair (i, true) ∈ kept)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hQ : Q.card ≤ n - kept.card := by
    have hc : (Finset.univ \ kept).card = n - kept.card := by
      rw [Finset.card_univ_diff, Fintype.card_fin]
    rw [← hc]
    apply Finset.card_le_card_of_injOn
      (fun i => rowPair (i, decide (rowPair (i, false) ∈ kept)))
    · intro i hi
      simp only [Q, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
      simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ, true_and,
        Finset.mem_coe]
      by_cases h : rowPair (i, false) ∈ kept
      · simp only [h, decide_true]
        exact fun h2 => hi ⟨h, h2⟩
      · simp only [h, decide_false]
        exact not_false
    · intro i _ j _ h
      exact (hinj2 _ _ _ _ h).1
  have hstep2 : ∀ i ∈ P, gap ≤ ∑ u ∈ Finset.univ \ kept,
      (if G u (π (rowPair (i, false))) ≠ G u (π (rowPair (i, true))) then 1 else 0) := by
    intro i hi
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hp, hq⟩ := hi
    have hne : π (rowPair (i, false)) ≠ π (rowPair (i, true)) := by
      intro h
      have := (hinj _ _ _ _ h).2
      exact absurd this (by decide)
    have h1 := hcol _ _ hne
    have h2 := hrow i
    let D := Finset.univ.filter (fun r : Fin n => G r (π (rowPair (i, false))) ≠ G r (π (rowPair (i, true))))
    have hsplit := Finset.card_filter_add_card_filter_not (s := D) (fun r => r ∈ kept)
    have hA : (D.filter (fun r => r ∈ kept)).card ≤ rowDistance (rowPair (i, false)) (rowPair (i, true)) := by
      apply Finset.card_le_card_of_injOn (fun r => π r)
      · intro r hr
        simp only [D, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at hr
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        obtain ⟨hr1, hr2⟩ := hr
        rw [hsym r hr2 _ hp, hsym r hr2 _ hq] at hr1
        exact hr1
      · intro r _ s _ h
        exact π.injective h
    have hB : (D.filter (fun r => ¬ r ∈ kept)).card = ∑ u ∈ Finset.univ \ kept,
        (if G u (π (rowPair (i, false))) ≠ G u (π (rowPair (i, true))) then 1 else 0) := by
      rw [← Finset.card_filter]
      congr 1
      ext r
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      tauto
    have hDc : D.card = colDistance (π (rowPair (i, false))) (π (rowPair (i, true))) := rfl
    omega
  have hstep3 : ∀ u : Fin n, (P.filter (fun i =>
      G u (π (rowPair (i, false))) ≠ G u (π (rowPair (i, true))))).card ≤ minority u := by
    intro u
    apply le_min
    · apply Finset.card_le_card_of_injOn
        (fun i => π (rowPair (i, !G u (π (rowPair (i, false))))))
      · intro i hi
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at hi
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        obtain ⟨_, hi⟩ := hi
        cases h : G u (π (rowPair (i, false)))
        · rw [h] at hi
          simp only [Bool.not_false]
          cases h2 : G u (π (rowPair (i, true)))
          · rw [h2] at hi; exact absurd rfl hi
          · rfl
        · simpa using h
      · intro i _ j _ h
        exact (hinj _ _ _ _ h).1
    · apply Finset.card_le_card_of_injOn
        (fun i => π (rowPair (i, G u (π (rowPair (i, false))))))
      · intro i hi
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at hi
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        obtain ⟨_, hi⟩ := hi
        cases h : G u (π (rowPair (i, false)))
        · simpa using h
        · rw [h] at hi
          cases h2 : G u (π (rowPair (i, true)))
          · rfl
          · rw [h2] at hi; exact absurd rfl hi
      · intro i _ j _ h
        exact (hinj _ _ _ _ h).1
  have hP : gap * P.card ≤ ∑ u ∈ Finset.univ \ kept, minority u := by
    calc gap * P.card = ∑ i ∈ P, gap := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ P, ∑ u ∈ Finset.univ \ kept,
          (if G u (π (rowPair (i, false))) ≠ G u (π (rowPair (i, true))) then 1 else 0) :=
          Finset.sum_le_sum hstep2
      _ = ∑ u ∈ Finset.univ \ kept, ∑ i ∈ P,
          (if G u (π (rowPair (i, false))) ≠ G u (π (rowPair (i, true))) then 1 else 0) :=
          Finset.sum_comm
      _ ≤ ∑ u ∈ Finset.univ \ kept, minority u := by
          apply Finset.sum_le_sum
          intro u _
          rw [← Finset.card_filter]
          exact hstep3 u
  have hQ' : gap * Q.card ≤ gap * (n - kept.card) := Nat.mul_le_mul_left _ hQ
  have hm : gap * m = gap * P.card + gap * Q.card := by rw [← Nat.mul_add, hPQ]
  omega

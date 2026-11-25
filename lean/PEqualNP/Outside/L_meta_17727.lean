import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17727

def cov {n : ℕ} (L : List (Fin n × List (Fin n))) (c : ℕ) : Bool :=
  L.any fun p => c.testBit p.1 && p.2.any fun j => c.testBit j

def cost {n : ℕ} (L : List (Fin n × List (Fin n))) : ℕ := (L.map fun p => p.2.length + 1).sum

theorem key {n : ℕ} (J : ℕ → Fin n → Fin n) (A0 B : List ℕ)
    (hJ : ∀ a ∈ A0, ∀ i : Fin n, a.testBit i = true →
      ∀ c ∈ B, (c.testBit i && c.testBit (J a i)) = decide (c = a))
    (hJa : ∀ a ∈ A0, ∀ i : Fin n, a.testBit i = true → a.testBit (J a i) = true)
    (hAB : ∀ a ∈ A0, a ∉ B) :
    ∀ (S : Finset (Fin n)) (A : List ℕ), (∀ a ∈ A, a ∈ A0) →
      (∀ a ∈ A, ∃ s ∈ S, a.testBit s = true) →
      ∃ L : List (Fin n × List (Fin n)), (∀ p ∈ L, 2 ≤ p.2.length) ∧
        cost L + 2 * (A.filter fun c => !cov L c).length ≤ A.length + S.card ∧
        ∀ b ∈ B, cov L b = false := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro A _ hS
    have hA : A = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro a ha
      obtain ⟨s, hs, _⟩ := hS a ha
      simp at hs
    subst hA
    exact ⟨[], by simp, by simp [cost], by simp [cov]⟩
  | insert s S' hs ih =>
    intro A hA0 hS
    obtain ⟨L', h2, hc, hB⟩ := ih (A.filter fun a => !a.testBit s)
      (fun a ha => hA0 a (List.mem_filter.mp ha).1)
      (by
        intro a ha
        obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha
        obtain ⟨t, ht, hat⟩ := hS a ha1
        rcases Finset.mem_insert.mp ht with h | h
        · subst h
          rw [hat] at ha2
          simp at ha2
        · exact ⟨t, h, hat⟩)
    have hlen := List.length_eq_length_filter_add (l := A) (fun a => a.testBit s)
    have hcard : (insert s S').card = S'.card + 1 := Finset.card_insert_of_notMem hs
    rw [← List.countP_eq_length_filter] at hc
    rw [List.countP_filter] at hc
    by_cases hbig : 2 ≤ (A.filter fun a => a.testBit s).length
    · refine ⟨(s, (A.filter fun a => a.testBit s).map fun a => J a s) :: L', ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with h | h
        · subst h
          simpa using hbig
        · exact h2 p h
      · have hle : A.countP (fun c => !cov ((s, (A.filter fun a => a.testBit s).map fun a => J a s) :: L') c)
            ≤ A.countP (fun a => (!cov L' a) && !a.testBit s) := by
          apply List.countP_mono_left
          intro a ha hna
          have hna' : cov ((s, (A.filter fun a => a.testBit s).map fun a => J a s) :: L') a = false := by
            simpa using hna
          simp only [cov, List.any_cons, Bool.or_eq_false_iff] at hna'
          obtain ⟨h1, h3⟩ := hna'
          have hs' : a.testBit s = false := by
            by_contra hne
            have hat : a.testBit s = true := by simpa using hne
            have hmem : a ∈ A.filter fun a => a.testBit s := List.mem_filter.mpr ⟨ha, hat⟩
            have hj := hJa a (hA0 a ha) s hat
            have : (a.testBit s && ((A.filter fun a => a.testBit s).map fun a => J a s).any
                fun j => a.testBit j) = true := by
              rw [hat, Bool.true_and, List.any_eq_true]
              exact ⟨J a s, List.mem_map.mpr ⟨a, hmem, rfl⟩, hj⟩
            rw [this] at h1
            exact Bool.noConfusion h1
          have h3' : cov L' a = false := h3
          simp [h3', hs']
        have hcost : cost ((s, (A.filter fun a => a.testBit s).map fun a => J a s) :: L')
            = (A.filter fun a => a.testBit s).length + 1 + cost L' := by
          simp [cost]
        have e1 := List.countP_eq_length_filter (l := A)
          (p := fun c => !cov ((s, (A.filter fun a => a.testBit s).map fun a => J a s) :: L') c)
        rw [hcost, hcard, ← e1]
        omega
      · intro b hb
        simp only [cov, List.any_cons, Bool.or_eq_false_iff]
        refine ⟨?_, hB b hb⟩
        by_contra hne
        have ht : (b.testBit s && ((A.filter fun a => a.testBit s).map fun a => J a s).any
            fun j => b.testBit j) = true := by simpa using hne
        rw [Bool.and_eq_true, List.any_eq_true] at ht
        obtain ⟨hbs, j, hj, hbj⟩ := ht
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hj
        obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha
        have h := hJ a (hA0 a ha1) s ha2 b hb
        rw [hbs, hbj] at h
        have hba : b = a := by simpa using h.symm
        subst hba
        exact hAB b (hA0 b ha1) hb
    · refine ⟨L', h2, ?_, hB⟩
      have hsplit := List.countP_eq_countP_filter_add A (fun c => !cov L' c) (fun a => a.testBit s)
      have h1 : (A.filter fun a => a.testBit s).countP (fun c => !cov L' c)
          ≤ (A.filter fun a => a.testBit s).length := List.countP_le_length
      simp only [List.countP_filter] at hsplit h1
      have e1 := List.countP_eq_length_filter (l := A) (p := fun c => !cov L' c)
      rw [hcard, ← e1]
      omega

end PEqualNP.Outside.L_meta_17727

theorem PEqualNP.Outside.L_meta_17727 : ∀ (x1 : ℕ) (x2 x3 : List ℕ) (x4 : Finset (Fin x1)),   (∀ x5 ∈ x2, x5 ∉ x3) →     (∀ x6 ∈ x2, ∃ x8 ∈ x4, x6.testBit ↑x8 = Bool.true) →       (∀ x7 ∈ x2, ∀ (x9 : Fin x1), x7.testBit ↑x9 = Bool.true → ∃ (x11 : Fin x1), ∀ x12 ∈ x2 ++ x3, (x12.testBit ↑x9 && x12.testBit ↑x11) = Decidable.decide (x12 = x7)) →         ∃ (x8 : List (Fin x1 × List (Fin x1))),           (∀ x9 ∈ x8, (2 : ℕ) ≤ x9.2.length) ∧             have x9 : ℕ → Bool := fun (x9 : ℕ) => x8.any fun (x10 : Fin x1 × List (Fin x1)) => x9.testBit ↑x10.1 && x10.2.any fun (x11 : Fin x1) => x9.testBit ↑x11;             (List.map (fun (x10 : Fin x1 × List (Fin x1)) => x10.2.length + (1 : ℕ)) x8).sum + (2 : ℕ) * (List.filter (fun (x10 : ℕ) => !x9 x10) x2).length ≤ x2.length + x4.card ∧ ∀ x10 ∈ x3, x9 x10 = Bool.false := by
  intro n A B S hAB hS hP
  have hex : ∀ (a : ℕ) (i : Fin n), ∃ j : Fin n, (a ∈ A ∧ a.testBit i = true) →
      ∀ c ∈ A ++ B, (c.testBit i && c.testBit j) = decide (c = a) := by
    intro a i
    by_cases h : a ∈ A ∧ a.testBit i = true
    · obtain ⟨j, hj⟩ := hP a h.1 i h.2
      exact ⟨j, fun _ => hj⟩
    · exact ⟨i, fun h' => absurd h' h⟩
  choose J hJ using hex
  obtain ⟨L, h2, hc, hB⟩ := PEqualNP.Outside.L_meta_17727.key J A B
    (fun a ha i hi c hc => hJ a i ⟨ha, hi⟩ c (List.mem_append_right _ hc))
    (fun a ha i hi => by
      have h := hJ a i ⟨ha, hi⟩ a (List.mem_append_left _ ha)
      rw [hi] at h
      simpa using h)
    hAB S A (fun a ha => ha) hS
  exact ⟨L, h2, hc, hB⟩

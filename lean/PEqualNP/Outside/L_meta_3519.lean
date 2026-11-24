import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3519

def Lp {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2)) (p : Fin x1) : Finset (Fin x2) :=
  Finset.univ.filter fun l => (p, l) ∈ x3

def Pl {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (l : Fin x2) :
    Finset (Fin x1) :=
  Finset.univ.filter fun p => (p, l) ∈ x3 ∧ p ∉ x4

def A {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) : Finset (Fin x1) :=
  x4.filter fun p => (Lp x3 p).Nonempty

def B {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)) :
    Finset (Fin x2) :=
  x5.filter fun l => (Pl x3 x4 l).Nonempty

noncomputable def S1 {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) : List (ℕ × List ℕ) :=
  (A x3 x4).toList.map fun p => (p.1, (Lp x3 p).toList.map fun l => x1 + l.1)

noncomputable def S2 {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)) :
    List (ℕ × List ℕ) :=
  (B x3 x4 x5).toList.map fun l => (x1 + l.1, (Pl x3 x4 l).toList.map fun p => p.1)

theorem sum1 {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) :
    ((S1 x3 x4).map fun s => s.2.length).sum =
      (((A x3 x4) ×ˢ (Finset.univ : Finset (Fin x2))).filter fun e => e ∈ x3).card := by
  have e1 : ((S1 x3 x4).map fun s => s.2.length).sum = ∑ p ∈ A x3 x4, (Lp x3 p).card := by
    rw [← Finset.sum_map_toList (A x3 x4) (fun p => (Lp x3 p).card)]
    simp [S1, Function.comp_def]
  rw [e1, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p _
  rw [Lp, Finset.card_filter]

theorem sum2 {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1))
    (x5 : Finset (Fin x2)) :
    ((S2 x3 x4 x5).map fun s => s.2.length).sum =
      (((Finset.univ : Finset (Fin x1)) ×ˢ (B x3 x4 x5)).filter
        fun e => e ∈ x3 ∧ e.1 ∉ x4).card := by
  have e1 : ((S2 x3 x4 x5).map fun s => s.2.length).sum =
      ∑ l ∈ B x3 x4 x5, (Pl x3 x4 l).card := by
    rw [← Finset.sum_map_toList (B x3 x4 x5) (fun l => (Pl x3 x4 l).card)]
    simp [S2, Function.comp_def]
  rw [e1, Finset.card_filter, Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro l _
  rw [Pl, Finset.card_filter]

theorem main (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1))
    (x5 : Finset (Fin x2)) (hc : ∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) :
    ∃ (x7 : List (ℕ × List ℕ)), (∀ x8 ∈ x7, x8.2 ≠ [] ∧ ((x8.1 < x1 ∧ ∀ x10 ∈ x8.2, x1 ≤ x10 ∧ x10 < x1 + x2) ∨ x1 ≤ x8.1 ∧ x8.1 < x1 + x2 ∧ ∀ x10 ∈ x8.2, x10 < x1)) ∧ (∀ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ↔ ∃ x10 ∈ x7, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) ∧ (List.map (fun (x8 : ℕ × List ℕ) => x8.2.length) x7).sum + x7.length - 1 ≤ x3.card + x4.card + x5.card - 1 := by
  refine ⟨S1 x3 x4 ++ S2 x3 x4 x5, ?_, ?_, ?_⟩
  · intro s hs
    rcases List.mem_append.1 hs with h | h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      have hp2 := (Finset.mem_filter.1 (Finset.mem_toList.1 hp)).2
      obtain ⟨l, hl⟩ := hp2
      refine ⟨?_, Or.inl ⟨p.2, ?_⟩⟩
      · intro h0
        have hm : x1 + l.1 ∈ (Lp x3 p).toList.map fun l => x1 + l.1 :=
          List.mem_map.2 ⟨l, Finset.mem_toList.2 hl, rfl⟩
        simp only at h0
        rw [h0] at hm
        simp at hm
      · intro u hu
        obtain ⟨l', _, rfl⟩ := List.mem_map.1 hu
        have := l'.2
        constructor <;> omega
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
      have hl2 := (Finset.mem_filter.1 (Finset.mem_toList.1 hl)).2
      obtain ⟨p, hp⟩ := hl2
      have hlt := l.2
      refine ⟨?_, Or.inr ⟨by simp, by simp, ?_⟩⟩
      · intro h0
        have hm : p.1 ∈ (Pl x3 x4 l).toList.map fun p => p.1 :=
          List.mem_map.2 ⟨p, Finset.mem_toList.2 hp, rfl⟩
        simp only at h0
        rw [h0] at hm
        simp at hm
      · intro u hu
        obtain ⟨p', _, rfl⟩ := List.mem_map.1 hu
        exact p'.2
  · intro p l
    constructor
    · intro he
      by_cases hp : p ∈ x4
      · have hm : l ∈ Lp x3 p := by simp [Lp, he]
        refine ⟨(p.1, (Lp x3 p).toList.map fun l => x1 + l.1),
          List.mem_append_left _ (List.mem_map.2 ⟨p, Finset.mem_toList.2
            (Finset.mem_filter.2 ⟨hp, ⟨l, hm⟩⟩), rfl⟩),
          Or.inl ⟨rfl, List.mem_map.2 ⟨l, Finset.mem_toList.2 hm, rfl⟩⟩⟩
      · have hl : l ∈ x5 := (hc _ he).resolve_left hp
        have hm : p ∈ Pl x3 x4 l := by simp [Pl, he, hp]
        refine ⟨(x1 + l.1, (Pl x3 x4 l).toList.map fun p => p.1),
          List.mem_append_right _ (List.mem_map.2 ⟨l, Finset.mem_toList.2
            (Finset.mem_filter.2 ⟨hl, ⟨p, hm⟩⟩), rfl⟩),
          Or.inr ⟨rfl, List.mem_map.2 ⟨p, Finset.mem_toList.2 hm, rfl⟩⟩⟩
    · rintro ⟨s, hs, h⟩
      rcases List.mem_append.1 hs with h1 | h1
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 h1
        rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · obtain ⟨l', hl', e⟩ := List.mem_map.1 e2
          have hl : l' = l := Fin.ext (by omega)
          have hpp : p' = p := Fin.ext e1
          subst hl
          subst hpp
          have := Finset.mem_toList.1 hl'
          simpa [Lp] using this
        · exfalso
          have := p'.2
          simp only at e1
          omega
      · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h1
        rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exfalso
          have := p.2
          simp only at e1
          omega
        · obtain ⟨p', hp', e⟩ := List.mem_map.1 e2
          have hl : l' = l := Fin.ext (by simp only at e1; omega)
          have hpp : p' = p := Fin.ext e
          subst hl
          subst hpp
          have := Finset.mem_toList.1 hp'
          simp [Pl] at this
          exact this.1
  · have hlen : (S1 x3 x4 ++ S2 x3 x4 x5).length ≤ x4.card + x5.card := by
      have h1 : (A x3 x4).card ≤ x4.card := Finset.card_filter_le _ _
      have h2 : (B x3 x4 x5).card ≤ x5.card := Finset.card_filter_le _ _
      simp [S1, S2]
      omega
    have hsum : ((S1 x3 x4 ++ S2 x3 x4 x5).map fun s => s.2.length).sum ≤ x3.card := by
      rw [List.map_append, List.sum_append, sum1, sum2, ← Finset.card_union_of_disjoint]
      · apply Finset.card_le_card
        intro e he
        rcases Finset.mem_union.1 he with h | h
        · exact (Finset.mem_filter.1 h).2
        · exact (Finset.mem_filter.1 h).2.1
      · rw [Finset.disjoint_left]
        intro e h1 h2
        have a1 := (Finset.mem_filter.1 h1).1
        have a2 := (Finset.mem_filter.1 h2).2.2
        rw [Finset.mem_product] at a1
        exact a2 (Finset.mem_filter.1 a1.1).1
    omega

end PEqualNP.Outside.L_meta_3519

theorem PEqualNP.Outside.L_meta_3519 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : List (ℕ × List ℕ)), (∀ x8 ∈ x7, x8.2 ≠ [] ∧ ((x8.1 < x1 ∧ ∀ x10 ∈ x8.2, x1 ≤ x10 ∧ x10 < x1 + x2) ∨ x1 ≤ x8.1 ∧ x8.1 < x1 + x2 ∧ ∀ x10 ∈ x8.2, x10 < x1)) ∧ (∀ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ↔ ∃ x10 ∈ x7, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) ∧ (List.map (fun (x8 : ℕ × List ℕ) => x8.2.length) x7).sum + x7.length - (1 : ℕ) ≤ x3.card + x4.card + x5.card - (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hc
  exact L_meta_3519.main x1 x2 x3 x4 x5 hc

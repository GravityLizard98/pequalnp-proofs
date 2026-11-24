import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328

def D (L : List ℕ) (v : ℕ) : Prop := ∃ a ∈ L, ∃ b ∈ L, v = a &&& b ∨ v = a ||| b

def V (base L : List ℕ) : Prop := ∀ (i : ℕ) (h : i < L.length), D (base ++ L.take i) L[i]

theorem D_mono {L L' : List ℕ} {v : ℕ} (h : ∀ a ∈ L, a ∈ L') : D L v → D L' v := by
  rintro ⟨a, ha, b, hb, hv⟩
  exact ⟨a, h a ha, b, h b hb, hv⟩

theorem V_snoc (base L : List ℕ) (v : ℕ) : V base (L ++ [v]) ↔ V base L ∧ D (base ++ L) v := by
  constructor
  · intro h
    constructor
    · intro i hi
      have h1 := h i (by simp; omega)
      rw [List.take_append_of_le_length (Nat.le_of_lt hi), List.getElem_append_left hi] at h1
      exact h1
    · have h1 := h L.length (by simp)
      simpa using h1
  · rintro ⟨h1, h2⟩ i hi
    by_cases hlt : i < L.length
    · rw [List.take_append_of_le_length (Nat.le_of_lt hlt), List.getElem_append_left hlt]
      exact h1 i hlt
    · have hi' : i = L.length := by
        simp at hi
        omega
      subst hi'
      simpa using h2

theorem V_cons (base L : List ℕ) (a : ℕ) (h1 : D base a) (h2 : V (a :: base) L) :
    V base (a :: L) := by
  intro i hi
  cases i with
  | zero => simpa using h1
  | succ j =>
    have h3 := h2 j (by simpa using hi)
    simp only [List.take_succ_cons, List.getElem_cons_succ]
    refine D_mono ?_ h3
    intro x hx
    simp at hx ⊢
    tauto

theorem clean (base : List ℕ) : ∀ P : List ℕ, V base P →
    ∃ Q : List ℕ, Q.length ≤ P.length ∧ Q.Nodup ∧ (∀ q ∈ Q, q ∉ base) ∧
      (∀ v ∈ P, v ∈ base ∨ v ∈ Q) ∧ V base Q := by
  intro P
  induction P using List.reverseRecOn with
  | nil =>
    intro _
    exact ⟨[], by simp, by simp, by simp, by simp, by intro i hi; simp at hi⟩
  | append_singleton P v ih =>
    intro h
    obtain ⟨hP, hv⟩ := (V_snoc base P v).1 h
    obtain ⟨Q, hl, hnd, hdis, hcov, hV⟩ := ih hP
    by_cases hm : v ∈ base ∨ v ∈ Q
    · refine ⟨Q, by simp; omega, hnd, hdis, ?_, hV⟩
      intro w hw
      simp at hw
      rcases hw with hw | rfl
      · exact hcov w hw
      · exact hm
    · have hm1 : v ∉ base := fun hh => hm (Or.inl hh)
      have hm2 : v ∉ Q := fun hh => hm (Or.inr hh)
      refine ⟨Q ++ [v], by simp; omega, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton v, ?_⟩
        intro a ha b hb
        simp at hb
        subst hb
        intro hab
        subst hab
        exact hm2 ha
      · intro q hq
        simp at hq
        rcases hq with hq | rfl
        · exact hdis q hq
        · exact hm1
      · intro w hw
        simp at hw
        rcases hw with hw | rfl
        · rcases hcov w hw with hh | hh
          · exact Or.inl hh
          · exact Or.inr (by simp [hh])
        · exact Or.inr (by simp)
      · refine (V_snoc base Q v).2 ⟨hV, D_mono ?_ hv⟩
        intro a ha
        simp at ha ⊢
        rcases ha with ha | ha
        · exact Or.inl ha
        · exact hcov a ha

theorem main (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ) (h5 : x5 ∉ x3) (h4 : D x3 x4)
    (h6 : V (x4 :: x3) x6) (h7 : D (x4 :: x3 ++ x6) x5) :
    ∃ x11 : List ℕ, x11.length ≤ x6.length + 2 ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧
      x5 ∈ x11 ∧ V x3 x11 := by
  have hP : V x3 (x4 :: (x6 ++ [x5])) :=
    V_cons x3 _ x4 h4 ((V_snoc (x4 :: x3) x6 x5).2 ⟨h6, h7⟩)
  obtain ⟨Q, hl, hnd, hdis, hcov, hV⟩ := clean x3 _ hP
  refine ⟨Q, by simpa using hl, hnd, hdis, ?_, hV⟩
  rcases hcov x5 (by simp) with hh | hh
  · exact absurd hh h5
  · exact hh

end PEqualNP.Outside.L_meta_3328

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro x1 x2 x3 x4 x5 x6 h5 h4 h6 h7
  obtain ⟨Q, hl, hnd, hdis, hmem, hV⟩ :=
    L_meta_3328.main x3 x4 x5 x6 h5 h4 (fun i hi => h6 ⟨i, hi⟩) h7
  exact ⟨Q, hl, hnd, hdis, hmem, fun i => hV i.1 i.2⟩

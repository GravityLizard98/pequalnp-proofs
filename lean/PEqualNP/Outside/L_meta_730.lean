import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_730

def OC {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) (w : ℕ → Fin n) : Prop :=
  2 ≤ m ∧ (∀ i, w i = w (i % m)) ∧ ∀ i, H.Adj (w i) (w (i + 1))

theorem cut {n : ℕ} (H : SimpleGraph (Fin n)) (g : ℕ → Fin n) (L : ℕ) (hL : 2 ≤ L)
    (h1 : ∀ r, r + 1 < L → H.Adj (g r) (g (r + 1))) (h2 : H.Adj (g (L - 1)) (g 0)) :
    OC H L (fun k => g (k % L)) := by
  refine ⟨hL, fun i => by simp, fun i => ?_⟩
  have hr : i % L < L := Nat.mod_lt _ (by omega)
  by_cases h : i % L + 1 < L
  · have e : (i + 1) % L = i % L + 1 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < L by omega)]
      exact Nat.mod_eq_of_lt h
    simp only [e]
    exact h1 _ h
  · have h' : i % L + 1 = L := by omega
    have e : (i + 1) % L = 0 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < L by omega), h', Nat.mod_self]
    have e2 : i % L = L - 1 := by omega
    simp only [e, e2]
    exact h2

theorem shortenA {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) (w : ℕ → Fin n) (hw : OC H m w)
    (hodd : Odd m) (a b : ℕ) (hab : a < b) (hb : b < m) (he : w a = w b) :
    ∃ m' w', m' < m ∧ Odd m' ∧ OC H m' w' := by
  obtain ⟨hm, hmod, hadj⟩ := hw
  have hwm : ∀ i, w (i + m) = w i := fun i => by
    rw [hmod (i + m), Nat.add_mod_right, ← hmod]
  have h1 : 2 ≤ b - a := by
    by_contra hh
    have h3 := hadj a
    rw [show a + 1 = b by omega, ← he] at h3
    exact (H.ne_of_adj h3) rfl
  have h2 : 2 ≤ m - (b - a) := by
    by_contra hh
    have h3 := hadj b
    rw [show b + 1 = a + m by omega, hwm, he] at h3
    exact (H.ne_of_adj h3) rfl
  have hpar : Odd (b - a) ∨ Odd (m - (b - a)) := by
    have hm2 : m % 2 = 1 := Nat.odd_iff.1 hodd
    rw [Nat.odd_iff, Nat.odd_iff]
    omega
  rcases hpar with ho | ho
  · refine ⟨b - a, _, by omega, ho, cut H (fun r => w (a + r)) (b - a) h1
      (fun r _ => hadj (a + r)) ?_⟩
    have h3 := hadj (b - 1)
    rw [show b - 1 + 1 = b by omega, ← he] at h3
    have e1 : a + (b - a - 1) = b - 1 := by omega
    show H.Adj (w (a + (b - a - 1))) (w (a + 0))
    rw [e1]
    exact h3
  · refine ⟨m - (b - a), _, by omega, ho, cut H (fun r => w (b + r)) (m - (b - a)) h2
      (fun r _ => hadj (b + r)) ?_⟩
    have h3 := hadj (a + m - 1)
    rw [show a + m - 1 + 1 = a + m by omega, hwm, he] at h3
    have e1 : b + (m - (b - a) - 1) = a + m - 1 := by omega
    show H.Adj (w (b + (m - (b - a) - 1))) (w (b + 0))
    rw [e1]
    exact h3

theorem shortenB {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) (w : ℕ → Fin n) (hw : OC H m w)
    (hodd : Odd m) (a b : ℕ) (hab : a < b) (hb : b < m) (he : H.Adj (w a) (w b))
    (hn1 : b ≠ a + 1) (hn2 : ¬ (a = 0 ∧ b = m - 1)) :
    ∃ m' w', m' < m ∧ Odd m' ∧ OC H m' w' := by
  obtain ⟨hm, hmod, hadj⟩ := hw
  have hwm : ∀ i, w (i + m) = w i := fun i => by
    rw [hmod (i + m), Nat.add_mod_right, ← hmod]
  have hpar : Odd (b - a + 1) ∨ Odd (m - (b - a) + 1) := by
    have hm2 : m % 2 = 1 := Nat.odd_iff.1 hodd
    rw [Nat.odd_iff, Nat.odd_iff]
    omega
  rcases hpar with ho | ho
  · refine ⟨b - a + 1, _, by omega, ho, cut H (fun r => w (a + r)) (b - a + 1) (by omega)
      (fun r _ => hadj (a + r)) ?_⟩
    have e1 : a + (b - a + 1 - 1) = b := by omega
    show H.Adj (w (a + (b - a + 1 - 1))) (w (a + 0))
    rw [e1]
    exact he.symm
  · refine ⟨m - (b - a) + 1, _, by omega, ho, cut H (fun r => w (b + r)) (m - (b - a) + 1)
      (by omega) (fun r _ => hadj (b + r)) ?_⟩
    have e1 : b + (m - (b - a) + 1 - 1) = a + m := by omega
    have h3 := he
    rw [← hwm a] at h3
    show H.Adj (w (b + (m - (b - a) + 1 - 1))) (w (b + 0))
    rw [e1]
    exact h3

theorem build {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) (w : ℕ → Fin n) (hw : OC H m w)
    (hodd : Odd m) (hA : ∀ a b, a < b → b < m → w a ≠ w b)
    (hB : ∀ a b, a < b → b < m → H.Adj (w a) (w b) → b = a + 1 ∨ (a = 0 ∧ b = m - 1)) :
    ∃ D : Fin n → Fin n → Prop, (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) ∧
      (∀ u v, D u v → ¬ D v u) ∧
      ¬ ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  obtain ⟨hm, hmod, hadj⟩ := hw
  have hlt : ∀ i, i % m < m := fun i => Nat.mod_lt _ (by omega)
  have hAf : ∀ i j, w i = w j → i % m = j % m := by
    intro i j h
    rw [hmod i, hmod j] at h
    rcases Nat.lt_trichotomy (i % m) (j % m) with h1 | h1 | h1
    · exact absurd h (hA _ _ h1 (hlt j))
    · exact h1
    · exact absurd h.symm (hA _ _ h1 (hlt i))
  have hsucc : ∀ i j, w i = w j → w (i + 1) = w (j + 1) := by
    intro i j h
    have e := hAf i j h
    have e2 : (i + 1) % m = (j + 1) % m := by
      rw [Nat.add_mod i 1, Nat.add_mod j 1, e]
    rw [hmod (i + 1), hmod (j + 1), e2]
  have hwm : w m = w 0 := by rw [hmod m, Nat.mod_self]
  have hBf : ∀ i j, H.Adj (w i) (w j) →
      (∃ k, w i = w k ∧ w j = w (k + 1)) ∨ (∃ k, w j = w k ∧ w i = w (k + 1)) := by
    intro i j h
    have h' := h
    rw [hmod i, hmod j] at h'
    rcases Nat.lt_trichotomy (i % m) (j % m) with h1 | h1 | h1
    · rcases hB _ _ h1 (hlt j) h' with h2 | ⟨h2, h3⟩
      · left
        exact ⟨i % m, hmod i, by rw [← h2]; exact hmod j⟩
      · right
        refine ⟨j % m, hmod j, ?_⟩
        rw [h3, show m - 1 + 1 = m by omega, hwm, hmod i, h2]
    · rw [h1] at h'
      exact absurd rfl (H.ne_of_adj h')
    · rcases hB _ _ h1 (hlt i) h'.symm with h2 | ⟨h2, h3⟩
      · right
        exact ⟨j % m, hmod j, by rw [← h2]; exact hmod i⟩
      · left
        refine ⟨i % m, hmod i, ?_⟩
        rw [h3, show m - 1 + 1 = m by omega, hwm, hmod j, h2]
  have hC : ∀ i j, w i = w (j + 1) → w (i + 1) = w j → False := by
    intro i j h1 h2
    have e1 := hAf _ _ h1
    have e2 := hAf _ _ h2
    have e3 : (j + 1 + 1) % m = (i + 1) % m := by
      rw [Nat.add_mod (j + 1) 1, ← e1, ← Nat.add_mod]
    have e4 : j + 2 ≡ j + 0 [MOD m] := e3.trans e2
    have e5 : 2 ≡ 0 [MOD m] := Nat.ModEq.add_left_cancel' j e4
    have e6 : m ∣ 2 := (Nat.modEq_zero_iff_dvd).1 e5
    have e7 : m ≤ 2 := Nat.le_of_dvd (by omega) e6
    rw [Nat.odd_iff] at hodd
    omega
  refine ⟨fun u v => H.Adj u v ∧ ((∃ i, u = w i ∧ v = w (i + 1)) ∨
    ((¬ ∃ i, u = w i) ∧ (∃ i, v = w i)) ∨
    ((¬ ∃ i, u = w i) ∧ (¬ ∃ i, v = w i) ∧ u < v)), ?_, ?_, ?_⟩
  · intro u v
    constructor
    · intro h
      by_cases hu : ∃ i, u = w i <;> by_cases hv : ∃ i, v = w i
      · obtain ⟨i, rfl⟩ := hu
        obtain ⟨j, rfl⟩ := hv
        rcases hBf i j h with c | c
        · exact Or.inl ⟨h, Or.inl c⟩
        · exact Or.inr ⟨h.symm, Or.inl c⟩
      · exact Or.inr ⟨h.symm, Or.inr (Or.inl ⟨hv, hu⟩)⟩
      · exact Or.inl ⟨h, Or.inr (Or.inl ⟨hu, hv⟩)⟩
      · rcases lt_or_gt_of_ne (H.ne_of_adj h) with l | l
        · exact Or.inl ⟨h, Or.inr (Or.inr ⟨hu, hv, l⟩)⟩
        · exact Or.inr ⟨h.symm, Or.inr (Or.inr ⟨hv, hu, l⟩)⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1.symm
  · rintro u v ⟨_, h1⟩ ⟨_, h2⟩
    rcases h1 with ⟨i, hi1, hi2⟩ | ⟨a, b⟩ | ⟨a, b, c⟩ <;>
      rcases h2 with ⟨j, hj1, hj2⟩ | ⟨a', b'⟩ | ⟨a', b', c'⟩
    · exact hC i j (hi1.symm.trans hj2) (hi2.symm.trans hj1)
    · exact a' ⟨_, hi2⟩
    · exact a' ⟨_, hi2⟩
    · exact a ⟨_, hj2⟩
    · exact a' b
    · exact a' b
    · exact a ⟨_, hj2⟩
    · exact a b'
    · exact lt_asymm c c'
  · rintro ⟨K, hind, habs⟩
    have step : ∀ i, w (i + 1) ∈ K ↔ w i ∉ K := by
      intro i
      constructor
      · intro h1 h0
        exact hind _ h0 _ h1 (hadj i)
      · intro h0
        obtain ⟨k, hk, hD⟩ := habs _ h0
        rcases hD.2 with ⟨j, hj1, hj2⟩ | ⟨a, _⟩ | ⟨a, _⟩
        · rw [hsucc i j hj1, ← hj2]
          exact hk
        · exact absurd ⟨i, rfl⟩ a
        · exact absurd ⟨i, rfl⟩ a
    have par : ∀ k, w k ∈ K ↔ (w 0 ∈ K ↔ Even k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [step, ih, Nat.even_add_one]
        tauto
    have hp := par m
    rw [hwm] at hp
    have hne : ¬ Even m := Nat.not_even_iff_odd.2 hodd
    tauto

theorem key {n : ℕ} (H : SimpleGraph (Fin n)) : ∀ m : ℕ, Odd m → ∀ w : ℕ → Fin n, OC H m w →
    ∃ D : Fin n → Fin n → Prop, (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) ∧
      (∀ u v, D u v → ¬ D v u) ∧
      ¬ ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hodd w hw
    by_cases hA : ∃ a b, a < b ∧ b < m ∧ w a = w b
    · obtain ⟨a, b, h1, h2, h3⟩ := hA
      obtain ⟨m', w', hlt, ho, hoc⟩ := shortenA H m w hw hodd a b h1 h2 h3
      exact ih m' hlt ho w' hoc
    · by_cases hB : ∃ a b, a < b ∧ b < m ∧ H.Adj (w a) (w b) ∧ b ≠ a + 1 ∧ ¬ (a = 0 ∧ b = m - 1)
      · obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := hB
        obtain ⟨m', w', hlt, ho, hoc⟩ := shortenB H m w hw hodd a b h1 h2 h3 h4 h5
        exact ih m' hlt ho w' hoc
      · refine build H m w hw hodd (fun a b h1 h2 h3 => hA ⟨a, b, h1, h2, h3⟩) ?_
        intro a b h1 h2 h3
        by_contra hh
        exact hB ⟨a, b, h1, h2, h3, fun e => hh (Or.inl e), fun e => hh (Or.inr e)⟩

theorem fwd {n : ℕ} (H : SimpleGraph (Fin n))
    (h : ∀ D : Fin n → Fin n → Prop,
      (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k) :
    H.Colorable 2 := by
  by_contra hc
  have hnb : ¬ H.IsBipartite := hc
  rw [SimpleGraph.isBipartite_iff_forall_walk_even_length] at hnb
  push Not at hnb
  obtain ⟨v, p, hp⟩ := hnb
  have hodd : Odd p.length := hp
  have h2 : 2 ≤ p.length := by
    by_contra h2
    have h1 : p.length = 1 := by
      rw [Nat.odd_iff] at hodd
      omega
    have h3 := p.adj_getVert_succ (i := 0) (by omega)
    rw [show 0 + 1 = p.length by omega, p.getVert_length, p.getVert_zero] at h3
    exact (H.ne_of_adj h3) rfl
  have hwrap : H.Adj (p.getVert (p.length - 1)) (p.getVert 0) := by
    have h3 := p.adj_getVert_succ (i := p.length - 1) (by omega)
    rw [show p.length - 1 + 1 = p.length by omega, p.getVert_length] at h3
    rw [p.getVert_zero]
    exact h3
  have hoc := cut H p.getVert p.length h2 (fun r hr => p.adj_getVert_succ (by omega)) hwrap
  obtain ⟨D, d1, d2, d3⟩ := key H p.length hodd _ hoc
  exact d3 (h D d1 d2)

def kf {n : ℕ} (D : Fin n → Fin n → Prop) (c : Fin n → Fin 2) : Set (Fin n) →o Set (Fin n) where
  toFun := fun A => {x | c x = 0 ∧ ∀ y, (∀ a ∈ A, ¬ D y a) → ¬ D x y}
  monotone' := by
    intro A B hAB x hx
    exact ⟨hx.1, fun y hy => hx.2 y (fun a ha => hy a (hAB ha))⟩

theorem bwd {n : ℕ} (H : SimpleGraph (Fin n)) (hc : H.Colorable 2)
    (D : Fin n → Fin n → Prop) (d1 : ∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) :
    ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  obtain ⟨c⟩ := hc
  have hfix : kf D c (OrderHom.lfp (kf D c)) = OrderHom.lfp (kf D c) := OrderHom.map_lfp _
  generalize OrderHom.lfp (kf D c) = A at hfix
  have hA : ∀ x, x ∈ A ↔ (c x = 0 ∧ ∀ y, (∀ a ∈ A, ¬ D y a) → ¬ D x y) := by
    intro x
    have e : x ∈ kf D c A ↔ x ∈ A := by rw [hfix]
    exact e.symm
  have k1 : ∀ a b : Fin 2, a = 0 → a ≠ b → b = 1 := by decide
  have k2 : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide
  refine ⟨A ∪ {y | c y = 1 ∧ ∀ a ∈ A, ¬ D y a}, ?_, ?_⟩
  · rintro u (hu | ⟨hu1, hu2⟩) v (hv | ⟨hv1, hv2⟩) hadj
    · exact c.valid hadj (((hA u).1 hu).1.trans ((hA v).1 hv).1.symm)
    · rcases (d1 u v).1 hadj with h | h
      · exact ((hA u).1 hu).2 v hv2 h
      · exact hv2 u hu h
    · rcases (d1 u v).1 hadj with h | h
      · exact hu2 v hv h
      · exact ((hA v).1 hv).2 u hu2 h
    · exact c.valid hadj (hu1.trans hv1.symm)
  · intro v hv
    have hvA : v ∉ A := fun h => hv (Or.inl h)
    have hvC : ¬ (c v = 1 ∧ ∀ a ∈ A, ¬ D v a) := fun h => hv (Or.inr h)
    by_cases h0 : c v = 0
    · rw [hA] at hvA
      push Not at hvA
      obtain ⟨y, hy1, hy2⟩ := hvA h0
      have hne : c v ≠ c y := c.valid ((d1 v y).2 (Or.inl hy2))
      exact ⟨y, Or.inr ⟨k1 _ _ h0 hne, hy1⟩, hy2⟩
    · have h1 : c v = 1 := k2 _ h0
      push Not at hvC
      obtain ⟨a, ha, hD⟩ := hvC h1
      exact ⟨a, Or.inl ha, hD⟩

end PEqualNP.Outside.L_meta_730

theorem PEqualNP.Outside.L_meta_730 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
  (∀ D : Fin n → Fin n → Prop,
      (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k) ↔
  H.Colorable 2 := by
  intro n H
  exact ⟨fun h => PEqualNP.Outside.L_meta_730.fwd H h,
    fun hc D d1 _ => PEqualNP.Outside.L_meta_730.bwd H hc D d1⟩

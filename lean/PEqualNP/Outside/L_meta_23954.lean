import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23954

theorem sd_yy (N : Finset (Fin 8)) (a b : Fin 8) (ha : a ∈ N) (hb : b ∈ N) :
    ({a, b} : Finset (Fin 8)) \ N = ∅ := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty]
  constructor <;> intro hx <;> aesop

theorem in_yy (N : Finset (Fin 8)) (a b : Fin 8) (ha : a ∈ N) (hb : b ∈ N) :
    ({a, b} : Finset (Fin 8)) ∩ N = {a, b} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty]
  constructor <;> intro hx <;> aesop

theorem sd_yn (N : Finset (Fin 8)) (a b : Fin 8) (ha : a ∈ N) (hb : b ∉ N) :
    ({a, b} : Finset (Fin 8)) \ N = {b} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty]
  constructor <;> intro hx <;> aesop

theorem in_yn (N : Finset (Fin 8)) (a b : Fin 8) (ha : a ∈ N) (hb : b ∉ N) :
    ({a, b} : Finset (Fin 8)) ∩ N = {a} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty]
  constructor <;> intro hx <;> aesop

theorem sd_ny (N : Finset (Fin 8)) (a b : Fin 8) (ha : a ∉ N) (hb : b ∈ N) :
    ({a, b} : Finset (Fin 8)) \ N = {a} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty]
  constructor <;> intro hx <;> aesop

theorem in_ny (N : Finset (Fin 8)) (a b : Fin 8) (ha : a ∉ N) (hb : b ∈ N) :
    ({a, b} : Finset (Fin 8)) ∩ N = {b} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty]
  constructor <;> intro hx <;> aesop

theorem sd_nn (N : Finset (Fin 8)) (a b : Fin 8) (ha : a ∉ N) (hb : b ∉ N) :
    ({a, b} : Finset (Fin 8)) \ N = {a, b} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty]
  constructor <;> intro hx <;> aesop

theorem in_nn (N : Finset (Fin 8)) (a b : Fin 8) (ha : a ∉ N) (hb : b ∉ N) :
    ({a, b} : Finset (Fin 8)) ∩ N = ∅ := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty]
  constructor <;> intro hx <;> aesop

theorem c2 (a b : Fin 8) : ({a, b} : Finset (Fin 8)).card ≤ 2 := Finset.card_le_two

theorem c1 (a : Fin 8) : ({a} : Finset (Fin 8)).card ≤ 2 := by simp

def e (u v : Fin 4) : Bool := decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % 4)

theorem e_diag : ∀ u : Fin 4, e u u = false := by decide

theorem e_r2 : ∀ u : Fin 4, e u (u + 2) = true := by decide

theorem e_r3 : ∀ u : Fin 4, e u (u + 3) = true := by decide

theorem e_runiq : ∀ u u' : Fin 4, e u' (u + 2) = true → e u' (u + 3) = true → u' = u := by decide

theorem e_c1 : ∀ v : Fin 4, e (v + 1) v = true := by decide

theorem e_c2 : ∀ v : Fin 4, e (v + 2) v = true := by decide

theorem e_cuniq : ∀ v v' : Fin 4, e (v + 1) v' = true → e (v + 2) v' = true → v' = v := by decide

theorem split8 : ∀ x : Fin 8, (∃ u : Fin 4, x = Fin.castAdd 4 u) ∨ (∃ v : Fin 4, x = Fin.natAdd 4 v) := by
  decide

theorem boolA (p q r s b0 x a0 h1 b1 a1 h2 : Bool) (hp : p = false) (hq : q = true)
    (hr : r = false) (hs : s = true) : p = (b0 || (!x && a0)) → q = (b0 || (!h1 && a0)) →
    r = (b1 || (!h1 && a1)) → s = (b1 || (!h2 && a1)) → False := by
  subst hp hq hr hs
  revert b0 x a0 h1 b1 a1 h2
  decide

theorem bf (b : Bool) (h : ¬ b = true) : b = false := by cases b <;> simp at h ⊢

theorem main : ∀ (N : Finset (Fin 8)) (H α β : Finset (Fin 8) → Bool),
  N.Nonempty → Nᶜ.Nonempty → H ∅ = false →
  (∀ S T : Finset (Fin 8), S ⊆ T → T.card ≤ 2 → H S = true → H T = true) →
  (∀ S T : Finset (Fin 8), S ⊆ T → T.card ≤ 2 → α S = true → α T = true) →
  (∀ S T : Finset (Fin 8), S ⊆ T → T.card ≤ 2 → β S = true → β T = true) →
  (∀ S : Finset (Fin 8), S.card ≤ 2 → β S = true → α S = true) →
  (N.card = 2 → ∀ a ∈ N, ∀ b ∈ N, H {a} = H {b}) →
  ((∀ a, a ∉ N → α {a} = false) → ∀ a b c d, a ∉ N → b ∉ N → c ∉ N → d ∉ N →
      α {a, b} = true → α {c, b} = true → α {c, d} = true → α {a, d} = true) →
  ¬ (∀ u v : Fin 4,
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % 4) =
        (β ({Fin.castAdd 4 u, Fin.natAdd 4 v} \ N) ||
          (!H ({Fin.castAdd 4 u, Fin.natAdd 4 v} ∩ N) && α ({Fin.castAdd 4 u, Fin.natAdd 4 v} \ N)))) := by
  intro N H α β hN hNc hH0 hHm hαm hβm hβα _ _ hE
  have hE' : ∀ u v : Fin 4, e u v = (β ({Fin.castAdd 4 u, Fin.natAdd 4 v} \ N) ||
      (!H ({Fin.castAdd 4 u, Fin.natAdd 4 v} ∩ N) && α ({Fin.castAdd 4 u, Fin.natAdd 4 v} \ N))) := hE
  have Fyy : ∀ u v : Fin 4, Fin.castAdd 4 u ∈ N → Fin.natAdd 4 v ∈ N →
      e u v = (β ∅ || (!H {Fin.castAdd 4 u, Fin.natAdd 4 v} && α ∅)) := by
    intro u v ha hb
    rw [hE' u v, sd_yy N _ _ ha hb, in_yy N _ _ ha hb]
  have Fyn : ∀ u v : Fin 4, Fin.castAdd 4 u ∈ N → Fin.natAdd 4 v ∉ N →
      e u v = (β {Fin.natAdd 4 v} || (!H {Fin.castAdd 4 u} && α {Fin.natAdd 4 v})) := by
    intro u v ha hb
    rw [hE' u v, sd_yn N _ _ ha hb, in_yn N _ _ ha hb]
  have Fny : ∀ u v : Fin 4, Fin.castAdd 4 u ∉ N → Fin.natAdd 4 v ∈ N →
      e u v = (β {Fin.castAdd 4 u} || (!H {Fin.natAdd 4 v} && α {Fin.castAdd 4 u})) := by
    intro u v ha hb
    rw [hE' u v, sd_ny N _ _ ha hb, in_ny N _ _ ha hb]
  have Fnn : ∀ u v : Fin 4, Fin.castAdd 4 u ∉ N → Fin.natAdd 4 v ∉ N →
      e u v = (β {Fin.castAdd 4 u, Fin.natAdd 4 v} || (!H ∅ && α {Fin.castAdd 4 u, Fin.natAdd 4 v})) := by
    intro u v ha hb
    rw [hE' u v, sd_nn N _ _ ha hb, in_nn N _ _ ha hb]
  have hb0 : β ∅ = false := by
    apply bf
    intro hb
    have h1 := hE' 0 0
    rw [hβm ∅ _ (Finset.empty_subset _)
      (le_trans (Finset.card_le_card Finset.sdiff_subset) (c2 _ _)) hb, e_diag] at h1
    simp at h1
  cases ha0 : α ∅ with
  | true =>
    have hαall : ∀ S : Finset (Fin 8), S.card ≤ 2 → α S = true :=
      fun S hS => hαm ∅ S (Finset.empty_subset _) hS ha0
    have s1c : ∀ v : Fin 4, Fin.natAdd 4 v ∉ N → β {Fin.natAdd 4 v} = false := by
      intro v hv
      apply bf
      intro hb
      by_cases hr : Fin.castAdd 4 v ∈ N
      · have h1 := Fyn v v hr hv
        rw [e_diag, hb] at h1
        simp at h1
      · have h1 := Fnn v v hr hv
        rw [e_diag, hβm {Fin.natAdd 4 v} {Fin.castAdd 4 v, Fin.natAdd 4 v} (by simp) (c2 _ _) hb] at h1
        simp at h1
    have s1r : ∀ u : Fin 4, Fin.castAdd 4 u ∉ N → β {Fin.castAdd 4 u} = false := by
      intro u hu
      apply bf
      intro hb
      by_cases hc : Fin.natAdd 4 u ∈ N
      · have h1 := Fny u u hu hc
        rw [e_diag, hb] at h1
        simp at h1
      · have h1 := Fnn u u hu hc
        rw [e_diag, hβm {Fin.castAdd 4 u} {Fin.castAdd 4 u, Fin.natAdd 4 u} (by simp) (c2 _ _) hb] at h1
        simp at h1
    have s2r : ∀ u : Fin 4, Fin.castAdd 4 u ∈ N → H {Fin.castAdd 4 u} = false := by
      intro u hu
      apply bf
      intro hh
      by_cases hc : (Fin.natAdd 4 (u + 2 : Fin 4) : Fin 8) ∈ N
      · have h1 := Fyy u (u + 2) hu hc
        rw [e_r2, hb0, hHm {Fin.castAdd 4 u} {Fin.castAdd 4 u, (Fin.natAdd 4 (u + 2 : Fin 4) : Fin 8)} (by simp) (c2 _ _) hh] at h1
        simp at h1
      · have h1 := Fyn u (u + 2) hu hc
        rw [e_r2, s1c _ hc, hh] at h1
        simp at h1
    have s2c : ∀ v : Fin 4, Fin.natAdd 4 v ∈ N → H {Fin.natAdd 4 v} = false := by
      intro v hv
      apply bf
      intro hh
      by_cases hr : (Fin.castAdd 4 (v + 1 : Fin 4) : Fin 8) ∈ N
      · have h1 := Fyy (v + 1) v hr hv
        rw [e_c1, hb0, hHm {Fin.natAdd 4 v} {(Fin.castAdd 4 (v + 1 : Fin 4) : Fin 8), Fin.natAdd 4 v} (by simp) (c2 _ _) hh] at h1
        simp at h1
      · have h1 := Fny (v + 1) v hr hv
        rw [e_c1, s1r _ hr, hh] at h1
        simp at h1
    obtain ⟨x, hx⟩ := hNc
    rw [Finset.mem_compl] at hx
    rcases split8 x with ⟨u, rfl⟩ | ⟨v, rfl⟩
    · by_cases hc : Fin.natAdd 4 u ∈ N
      · have h1 := Fny u u hx hc
        rw [e_diag, s2c u hc, hαall _ (c1 _)] at h1
        simp at h1
      · have h1 := Fnn u u hx hc
        rw [e_diag, hH0, hαall _ (c2 _ _)] at h1
        simp at h1
    · by_cases hr : Fin.castAdd 4 v ∈ N
      · have h1 := Fyn v v hr hx
        rw [e_diag, s2r v hr, hαall _ (c1 _)] at h1
        simp at h1
      · have h1 := Fnn v v hr hx
        rw [e_diag, hH0, hαall _ (c2 _ _)] at h1
        simp at h1
  | false =>
    have hin : ∀ u v : Fin 4, Fin.castAdd 4 u ∈ N → Fin.natAdd 4 v ∈ N → e u v = false := by
      intro u v ha hb
      rw [Fyy u v ha hb, hb0, ha0]
      simp
    have act_c : ∀ u v : Fin 4, Fin.castAdd 4 u ∈ N → e u v = true →
        Fin.natAdd 4 v ∉ N ∧ α {Fin.natAdd 4 v} = true := by
      intro u v hu he
      have hc : Fin.natAdd 4 v ∉ N := by
        intro hc
        rw [hin u v hu hc] at he
        exact absurd he (by simp)
      refine ⟨hc, ?_⟩
      have h1 := Fyn u v hu hc
      rw [he] at h1
      by_contra hα
      have hα' := bf _ hα
      have hβ : β {Fin.natAdd 4 v} = false := by
        apply bf
        intro hβ'
        exact hα (hβα _ (c1 _) hβ')
      rw [hα', hβ] at h1
      simp at h1
    have act_r : ∀ u v : Fin 4, Fin.natAdd 4 v ∈ N → e u v = true →
        Fin.castAdd 4 u ∉ N ∧ α {Fin.castAdd 4 u} = true := by
      intro u v hv he
      have hc : Fin.castAdd 4 u ∉ N := by
        intro hc
        rw [hin u v hc hv] at he
        exact absurd he (by simp)
      refine ⟨hc, ?_⟩
      have h1 := Fny u v hc hv
      rw [he] at h1
      by_contra hα
      have hα' := bf _ hα
      have hβ : β {Fin.castAdd 4 u} = false := by
        apply bf
        intro hβ'
        exact hα (hβα _ (c1 _) hβ')
      rw [hα', hβ] at h1
      simp at h1
    have out_c : ∀ u v : Fin 4, Fin.castAdd 4 u ∉ N → Fin.natAdd 4 v ∉ N → α {Fin.natAdd 4 v} = true →
        e u v = true := by
      intro u v hu hv ha
      rw [Fnn u v hu hv, hH0, hαm {Fin.natAdd 4 v} {Fin.castAdd 4 u, Fin.natAdd 4 v} (by simp) (c2 _ _) ha]
      simp
    have out_r : ∀ u v : Fin 4, Fin.castAdd 4 u ∉ N → Fin.natAdd 4 v ∉ N → α {Fin.castAdd 4 u} = true →
        e u v = true := by
      intro u v hu hv ha
      rw [Fnn u v hu hv, hH0, hαm {Fin.castAdd 4 u} {Fin.castAdd 4 u, Fin.natAdd 4 v} (by simp) (c2 _ _) ha]
      simp
    have allr : ∀ u : Fin 4, Fin.castAdd 4 u ∈ N → ∀ u' : Fin 4, Fin.castAdd 4 u' ∈ N := by
      intro u hu u'
      by_contra hu'
      obtain ⟨h2, a2⟩ := act_c u (u + 2) hu (e_r2 u)
      obtain ⟨h3, a3⟩ := act_c u (u + 3) hu (e_r3 u)
      have hh := e_runiq u u' (out_c u' (u + 2) hu' h2 a2) (out_c u' (u + 3) hu' h3 a3)
      subst hh
      exact hu' hu
    have allc : ∀ v : Fin 4, Fin.natAdd 4 v ∈ N → ∀ v' : Fin 4, Fin.natAdd 4 v' ∈ N := by
      intro v hv v'
      by_contra hv'
      obtain ⟨h1, a1⟩ := act_r (v + 1) v hv (e_c1 v)
      obtain ⟨h2, a2⟩ := act_r (v + 2) v hv (e_c2 v)
      have hh := e_cuniq v v' (out_r (v + 1) v' h1 hv' a1) (out_r (v + 2) v' h2 hv' a2)
      subst hh
      exact hv' hv
    obtain ⟨y, hy⟩ := hN
    obtain ⟨x, hx⟩ := hNc
    rw [Finset.mem_compl] at hx
    rcases split8 y with ⟨u, rfl⟩ | ⟨v, rfl⟩
    · have hr := allr u hy
      have hcol : ∀ v : Fin 4, Fin.natAdd 4 v ∉ N := by
        intro v hv
        rcases split8 x with ⟨u', rfl⟩ | ⟨v', rfl⟩
        · exact hx (hr u')
        · exact hx (allc v hv v')
      exact boolA _ _ _ _ _ _ _ _ _ _ _ (by decide : e 0 0 = false) (by decide : e 1 0 = true)
        (by decide : e 1 1 = false) (by decide : e 2 1 = true)
        (Fyn 0 0 (hr 0) (hcol 0)) (Fyn 1 0 (hr 1) (hcol 0)) (Fyn 1 1 (hr 1) (hcol 1))
        (Fyn 2 1 (hr 2) (hcol 1))
    · have hc := allc v hy
      have hrow : ∀ u : Fin 4, Fin.castAdd 4 u ∉ N := by
        intro u hu
        rcases split8 x with ⟨u', rfl⟩ | ⟨v', rfl⟩
        · exact hx (allr u hu u')
        · exact hx (hc v')
      exact boolA _ _ _ _ _ _ _ _ _ _ _ (by decide : e 0 0 = false) (by decide : e 0 2 = true)
        (by decide : e 1 2 = false) (by decide : e 1 3 = true)
        (Fny 0 0 (hrow 0) (hc 0)) (Fny 0 2 (hrow 0) (hc 2)) (Fny 1 2 (hrow 1) (hc 2))
        (Fny 1 3 (hrow 1) (hc 3))

end PEqualNP.Outside.L_meta_23954

theorem PEqualNP.Outside.L_meta_23954 : ∀ (N : Finset (Fin 8)) (H α β : Finset (Fin 8) → Bool),
  N.Nonempty → Nᶜ.Nonempty → H ∅ = false →
  (∀ S T : Finset (Fin 8), S ⊆ T → T.card ≤ 2 → H S = true → H T = true) →
  (∀ S T : Finset (Fin 8), S ⊆ T → T.card ≤ 2 → α S = true → α T = true) →
  (∀ S T : Finset (Fin 8), S ⊆ T → T.card ≤ 2 → β S = true → β T = true) →
  (∀ S : Finset (Fin 8), S.card ≤ 2 → β S = true → α S = true) →
  (N.card = 2 → ∀ a ∈ N, ∀ b ∈ N, H {a} = H {b}) →
  ((∀ a, a ∉ N → α {a} = false) → ∀ a b c d, a ∉ N → b ∉ N → c ∉ N → d ∉ N →
      α {a, b} = true → α {c, b} = true → α {c, d} = true → α {a, d} = true) →
  ¬ (∀ u v : Fin 4,
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % 4) =
        (β ({Fin.castAdd 4 u, Fin.natAdd 4 v} \ N) ||
          (!H ({Fin.castAdd 4 u, Fin.natAdd 4 v} ∩ N) && α ({Fin.castAdd 4 u, Fin.natAdd 4 v} \ N)))) :=
  PEqualNP.Outside.L_meta_23954.main

import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25499 :
    ∀ (k b : ℕ) (f : BitVec k → Bool) (d : BitVec k) (s : BitVec b),
  let slice := fun label : BitVec b =>
    Finset.univ.filter (fun key : BitVec k => key.setWidth b = label)
  let bias := fun t : BitVec b =>
    (slice t).sum (fun word => if f word then (-1 : ℤ) else 1)
  let agreements := (slice s).filter (fun x => f x = f (x ^^^ d))
  (bias s + bias (s ^^^ d.setWidth b)).natAbs ≤ 2 * agreements.card := by
  intro k b f d s slice bias agreements
  have hsw : ∀ x : BitVec k, (x ^^^ d).setWidth b = x.setWidth b ^^^ d.setWidth b := by
    intro x
    exact BitVec.setWidth_xor
  have hinv : ∀ x : BitVec k, x ^^^ d ^^^ d = x := by
    intro x
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  have h1 : bias (s ^^^ d.setWidth b) =
      (slice s).sum (fun x => if f (x ^^^ d) then (-1 : ℤ) else 1) := by
    symm
    apply Finset.sum_nbij' (fun x => x ^^^ d) (fun x => x ^^^ d)
    · intro a ha
      simp only [slice, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter,
        Set.mem_setOf_eq] at ha ⊢
      rw [hsw, ha]
    · intro a ha
      simp only [slice, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter,
        Set.mem_setOf_eq] at ha ⊢
      rw [hsw, ha, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    · intro a _
      exact hinv a
    · intro a _
      exact hinv a
    · intro a _
      rfl
  have h2 : bias s + bias (s ^^^ d.setWidth b) =
      (slice s).sum (fun x => (if f x then (-1 : ℤ) else 1) + (if f (x ^^^ d) then (-1 : ℤ) else 1)) := by
    rw [h1, Finset.sum_add_distrib]
  have h3 : ∀ x : BitVec k, |(if f x then (-1 : ℤ) else 1) + (if f (x ^^^ d) then (-1 : ℤ) else 1)| =
      if f x = f (x ^^^ d) then (2 : ℤ) else 0 := by
    intro x
    cases f x <;> cases f (x ^^^ d) <;> simp <;> norm_num
  have h4 : |bias s + bias (s ^^^ d.setWidth b)| ≤ 2 * (agreements.card : ℤ) := by
    rw [h2]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    rw [Finset.sum_congr rfl (fun x _ => h3 x), ← Finset.sum_filter]
    simp [agreements, Finset.sum_const, mul_comm]
  have h5 : ((bias s + bias (s ^^^ d.setWidth b)).natAbs : ℤ) = |bias s + bias (s ^^^ d.setWidth b)| :=
    Int.natCast_natAbs _
  have h6 : ((bias s + bias (s ^^^ d.setWidth b)).natAbs : ℤ) ≤ ((2 * agreements.card : ℕ) : ℤ) := by
    rw [h5]; push_cast; exact h4
  exact_mod_cast h6

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3801

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def D : Finset (Fin 13) := {(0 : Fin 13), (1 : Fin 13), (3 : Fin 13), (9 : Fin 13)}

def rg (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rc (ρ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (rg ρ), ρ C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem ren (ρ : ℕ → ℕ) (gs : List Gate) : ∀ (w w' : List Bool) (m : ℕ), w.length = m →
    w'.length = m → (∀ i, i < m → ρ i < m) → (∀ i, m ≤ i → ρ i = i) →
    (∀ i, w'.getD (ρ i) false = w.getD i false) →
    ∀ i, ((gs.map (rg ρ)).foldl step w').getD (ρ i) false = (gs.foldl step w).getD i false := by
  induction gs with
  | nil => intro w w' m _ _ _ _ h i; simpa using h i
  | cons g gs ih =>
    intro w w' m hw hw' hlt hfix hrel
    simp only [List.map_cons, List.foldl_cons]
    apply ih (step w g) (step w' (rg ρ g)) (m + 1)
    · simp [step, hw]
    · simp [step, hw']
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact Nat.lt_succ_of_lt (hlt i h)
      · rw [h, hfix m le_rfl]; exact Nat.lt_succ_self m
    · intro i hi; exact hfix i (Nat.le_of_succ_le hi)
    · intro i
      have hv : (rg ρ g).op.eval ((rg ρ g).inputs.map fun i => w'.getD i false)
          = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [rg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hrel a
      simp only [step, hv]
      rcases Nat.lt_or_ge i m with h | h
      · have h2 := hlt i h
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hrel i
      · rw [hfix i h]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
          hw, hw']

theorem ren_eval (ρ : ℕ → ℕ) (C : Circuit) (w w' : List Bool) (m : ℕ) (hw : w.length = m)
    (hw' : w'.length = m) (hlt : ∀ i, i < m → ρ i < m) (hfix : ∀ i, m ≤ i → ρ i = i)
    (hrel : ∀ i, w'.getD (ρ i) false = w.getD i false) : (rc ρ C).eval w' = C.eval w := by
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  exact ren ρ C.gates w w' m hw hw' hlt hfix hrel C.output

def Topo (C : Circuit) : Prop :=
  ∀ k : Fin C.gates.length, ∀ i ∈ (C.gates.get k).inputs, i < 27 + (k : ℕ)

theorem mono_rc (ρ : ℕ → ℕ) (C : Circuit) (hC : Monotone2 C) : Monotone2 (rc ρ C) := by
  intro g hg
  simp only [rc, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := hC g0 hg0
  simpa [rg] using this

theorem get_map (ρ : ℕ → ℕ) (gs : List Gate) (k : Fin (gs.map (rg ρ)).length) :
    (gs.map (rg ρ)).get k = rg ρ (gs.get ⟨k.val, by simpa using k.isLt⟩) := by
  simp

theorem topo_rc (ρ : ℕ → ℕ) (h26 : ∀ i, i < 26 → ρ i < 26) (hfix : ∀ i, 26 ≤ i → ρ i = i)
    (C : Circuit) (hC : Topo C) : Topo (rc ρ C) := by
  intro k i hi
  have hk : k.val < C.gates.length := by have := k.isLt; simpa [rc] using this
  have e : (rc ρ C).gates.get k = rg ρ (C.gates.get ⟨k.val, hk⟩) := get_map ρ C.gates k
  rw [e] at hi
  simp only [rg, List.mem_map] at hi
  obtain ⟨a, ha, rfl⟩ := hi
  have h3 := hC ⟨k.val, hk⟩ a ha
  simp only at h3
  rcases Nat.lt_or_ge a 26 with h | h
  · have := h26 a h; omega
  · rw [hfix a h]; exact h3

def two (f g : Fin 13 → Bool) : List Bool := List.ofFn f ++ List.ofFn g

theorem two_len (f g : Fin 13 → Bool) : (two f g).length = 26 := by simp [two]

theorem two_getD (f g : Fin 13 → Bool) (i : ℕ) : (two f g).getD i false =
    if i < 13 then f (Fin.ofNat 13 i) else if i < 26 then g (Fin.ofNat 13 (i - 13)) else false := by
  unfold two
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ (by simpa using h1), List.getD_eq_getElem _ _ (by simpa using h1),
      List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt h1]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.ofNat]
    omega
  · exact List.getD_eq_default _ _ (by simp; omega)

def rho (s t : Fin 13 → Fin 13) (i : ℕ) : ℕ :=
  if i < 13 then (s (Fin.ofNat 13 i)).val
  else if i < 26 then 13 + (t (Fin.ofNat 13 (i - 13))).val else i

theorem rho_lt (s t : Fin 13 → Fin 13) (i : ℕ) (h : i < 26) : rho s t i < 26 := by
  unfold rho
  split_ifs with h1
  · have := (s (Fin.ofNat 13 i)).isLt; omega
  · have := (t (Fin.ofNat 13 (i - 13))).isLt; omega

theorem rho_ge (s t : Fin 13 → Fin 13) (i : ℕ) (h : 26 ≤ i) : rho s t i = i := by
  unfold rho
  rw [if_neg (by omega), if_neg (by omega)]

theorem ofNat_val (a : Fin 13) : Fin.ofNat 13 a.val = a := by
  apply Fin.ext
  simp [Fin.ofNat, Nat.mod_eq_of_lt a.isLt]

theorem two_rel (s t : Fin 13 → Fin 13) (f g f' g' : Fin 13 → Bool) (hf : ∀ a, f a = f' (s a))
    (hg : ∀ a, g a = g' (t a)) (i : ℕ) :
    (two f' g').getD (rho s t i) false = (two f g).getD i false := by
  rw [two_getD, two_getD]
  unfold rho
  by_cases h1 : i < 13
  · have := (s (Fin.ofNat 13 i)).isLt
    rw [if_pos h1, if_pos h1, if_pos this, ofNat_val, hf]
  · by_cases h2 : i < 26
    · have := (t (Fin.ofNat 13 (i - 13))).isLt
      rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega),
        Nat.add_sub_cancel_left, ofNat_val, hg]
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, if_neg h1, if_neg h2]

def ext (L : List ℕ) (z : List Bool) : List Bool := z ++ [L.any fun i => z.getD i false]

def inpI (p l : Fin 13) : List Bool :=
  (List.ofFn fun x : Fin 13 => decide (x = p)) ++ List.ofFn fun x : Fin 13 => decide (x = l)

def inpQ (S : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun x : Fin 13 => decide (x ∈ S)) ++
    List.ofFn fun x : Fin 13 => decide (∀ y ∈ S, y - x ∉ D)

def Quad (S : Finset (Fin 13)) : Prop :=
  S.card = 4 ∧ ∀ l : Fin 13, {y ∈ S | y - l ∈ D}.card ≤ 2

def Good (C : Circuit) (L : List ℕ) : Prop :=
  (∀ p l : Fin 13, p - l ∈ D → C.eval (ext L (inpI p l)) = true) ∧
    ∀ S : Finset (Fin 13), Quad S → C.eval (ext L (inpQ S)) = false

def R (n : ℕ) (L : List ℕ) : Prop :=
  ∃ C : Circuit, C.size = n ∧ Monotone2 C ∧ Topo C ∧ Good C L

theorem ext_rel (s t : Fin 13 → Fin 13) (C : Circuit) (L : List ℕ) (f g f' g' : Fin 13 → Bool)
    (hf : ∀ a, f a = f' (s a)) (hg : ∀ a, g a = g' (t a)) :
    (rc (rho s t) C).eval (ext (L.map (rho s t)) (two f' g')) = C.eval (ext L (two f g)) := by
  have hrel := two_rel s t f g f' g' hf hg
  have he : ((L.map (rho s t)).any fun i => (two f' g').getD i false)
      = (L.any fun i => (two f g).getD i false) := by
    rw [List.any_map]
    congr 1
    funext i
    exact hrel i
  unfold ext
  rw [he]
  apply ren_eval (rho s t) C _ _ 27
  · simp [two_len]
  · simp [two_len]
  · intro i hi
    rcases Nat.lt_or_ge i 26 with h | h
    · have := rho_lt s t i h; omega
    · rw [rho_ge s t i h]; exact hi
  · intro i hi; exact rho_ge s t i (by omega)
  · intro i
    rcases Nat.lt_or_ge i 26 with h | h
    · have := rho_lt s t i h
      rw [List.getD_append _ _ _ _ (by rw [two_len]; exact this),
        List.getD_append _ _ _ _ (by rw [two_len]; exact h)]
      exact hrel i
    · rw [rho_ge s t i h, List.getD_append_right _ _ _ _ (by rw [two_len]; exact h),
        List.getD_append_right _ _ _ _ (by rw [two_len]; exact h), two_len, two_len]

theorem transfer (s t s' t' : Fin 13 → Fin 13) (hs : ∀ a, s (s' a) = a) (hs' : ∀ a, s' (s a) = a)
    (ht : ∀ a, t (t' a) = a) (ht' : ∀ a, t' (t a) = a) (hinc : ∀ p l, p - l ∈ D ↔ s p - t l ∈ D)
    (n : ℕ) (L : List ℕ) (h : R n L) : R n (L.map (rho s t)) := by
  obtain ⟨C, hsz, hmono, htopo, hinc1, hq1⟩ := h
  refine ⟨rc (rho s t) C, ?_, mono_rc _ C hmono,
    topo_rc _ (rho_lt s t) (rho_ge s t) C htopo, ?_, ?_⟩
  · simpa [rc, Circuit.size] using hsz
  · intro p' l' hpl
    have h1 : s' p' - t' l' ∈ D := by rw [hinc, hs, ht]; exact hpl
    have h2 := hinc1 (s' p') (t' l') h1
    have h3 := ext_rel s t C L (fun x => decide (x = s' p')) (fun x => decide (x = t' l'))
      (fun x => decide (x = p')) (fun x => decide (x = l'))
      (by
        intro a
        have : (a = s' p') ↔ (s a = p') := ⟨fun e => by rw [e, hs], fun e => by rw [← e, hs']⟩
        exact decide_eq_decide.mpr this)
      (by
        intro a
        have : (a = t' l') ↔ (t a = l') := ⟨fun e => by rw [e, ht], fun e => by rw [← e, ht']⟩
        exact decide_eq_decide.mpr this)
    exact h3.trans h2
  · intro S' hS'
    have hinj : Function.Injective s' := fun a b e => by rw [← hs a, ← hs b, e]
    have hmem : ∀ a, a ∈ S'.image s' ↔ s a ∈ S' := by
      intro a
      rw [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩; rw [hs]; exact hx
      · intro h; exact ⟨s a, h, hs' a⟩
    have hQ : Quad (S'.image s') := by
      refine ⟨by rw [Finset.card_image_of_injective _ hinj]; exact hS'.1, ?_⟩
      intro l
      have hsub : {y ∈ S'.image s' | y - l ∈ D} ⊆ ({x ∈ S' | x - t l ∈ D}).image s' := by
        intro y hy
        rw [Finset.mem_filter] at hy
        rw [Finset.mem_image]
        refine ⟨s y, ?_, hs' y⟩
        rw [Finset.mem_filter]
        exact ⟨(hmem y).mp hy.1, (hinc y l).mp hy.2⟩
      exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (hS'.2 (t l)))
    have h2 := hq1 _ hQ
    have h3 := ext_rel s t C L (fun x => decide (x ∈ S'.image s'))
      (fun x => decide (∀ y ∈ S'.image s', y - x ∉ D))
      (fun x => decide (x ∈ S')) (fun x => decide (∀ y ∈ S', y - x ∉ D))
      (by intro a; exact decide_eq_decide.mpr (hmem a))
      (by
        intro a
        have : (∀ y ∈ S'.image s', y - a ∉ D) ↔ (∀ y ∈ S', y - t a ∉ D) := by
          constructor
          · intro h y hy
            have h5 := h (s' y) (by rw [hmem, hs]; exact hy)
            rw [hinc, hs] at h5
            exact h5
          · intro h y hy
            rw [hinc]
            exact h (s y) ((hmem y).mp hy)
        exact decide_eq_decide.mpr this)
    exact h3.trans h2

theorem good_congr (C : Circuit) (L L' : List ℕ)
    (h : ∀ z : List Bool, z.length = 26 →
      (L.any fun i => z.getD i false) = (L'.any fun i => z.getD i false))
    (hg : Good C L) : Good C L' := by
  have e : ∀ z : List Bool, z.length = 26 → ext L' z = ext L z := by
    intro z hz
    unfold ext
    rw [h z hz]
  refine ⟨fun p l hpl => ?_, fun S hS => ?_⟩
  · have hl : (inpI p l).length = 26 := by simp [inpI]
    rw [e _ hl]
    exact hg.1 p l hpl
  · have hl : (inpQ S).length = 26 := by simp [inpQ]
    rw [e _ hl]
    exact hg.2 S hS

theorem R_congr (n : ℕ) (L L' : List ℕ)
    (h : ∀ z : List Bool, z.length = 26 →
      (L.any fun i => z.getD i false) = (L'.any fun i => z.getD i false))
    (hR : R n L) : R n L' := by
  obtain ⟨C, h1, h2, h3, h4⟩ := hR
  exact ⟨C, h1, h2, h3, good_congr C L L' h h4⟩

theorem gd (z : List Bool) (hz : z.length = 26) (i : ℕ) (h : 26 ≤ i) : z.getD i false = false :=
  List.getD_eq_default _ _ (by omega)

theorem R1 (n i : ℕ) (h : 26 ≤ i) (hR : R n [i]) : R n [] :=
  R_congr n _ _ (by intro z hz; simp only [List.any_cons, List.any_nil, gd z hz i h, Bool.or_false, Bool.false_or]) hR

theorem R2a (n i j : ℕ) (h : 26 ≤ i) (hR : R n [i, j]) : R n [j] :=
  R_congr n _ _ (by intro z hz; simp only [List.any_cons, List.any_nil, gd z hz i h, Bool.or_false, Bool.false_or]) hR

theorem R2b (n i j : ℕ) (h : 26 ≤ j) (hR : R n [i, j]) : R n [i] :=
  R_congr n _ _ (by intro z hz; simp only [List.any_cons, List.any_nil, gd z hz j h, Bool.or_false, Bool.false_or]) hR

theorem Rdup (n i : ℕ) (hR : R n [i, i]) : R n [i] :=
  R_congr n _ _ (by intro z hz; simp) hR

theorem Rswap (n i j : ℕ) (hR : R n [i, j]) : R n [j, i] :=
  R_congr n _ _ (by intro z hz; simp [Bool.or_comm]) hR

theorem shift (c : Fin 13) (n : ℕ) (L : List ℕ) (h : R n L) :
    R n (L.map (rho (fun a => a - c) (fun a => a - c))) :=
  transfer (fun a => a - c) (fun a => a - c) (fun a => a + c) (fun a => a + c)
    (by intro a; simp) (by intro a; simp) (by intro a; simp) (by intro a; simp)
    (by intro p l; simp) n L h

theorem rho_shift_pt (i : ℕ) (h : i < 13) :
    rho (fun a => a - Fin.ofNat 13 i) (fun a => a - Fin.ofNat 13 i) i = 0 := by
  simp [rho, h]

theorem rho_shift_ln (i : ℕ) (h1 : 13 ≤ i) (h2 : i < 26) :
    rho (fun a => a - Fin.ofNat 13 (i - 13)) (fun a => a - Fin.ofNat 13 (i - 13)) i = 13 := by
  unfold rho
  rw [if_neg (by omega), if_pos h2]
  simp

def fn (l : List ℕ) (a : Fin 13) : Fin 13 := Fin.ofNat 13 (l.getD a.val 0)

def A1 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 2, 1, 8, 4, 5, 11, 7, 3, 12, 10, 6, 9],
   [0, 3, 2, 1, 5, 4, 6, 7, 12, 9, 11, 10, 8],
   [0, 2, 4, 8, 1, 9, 6, 3, 7, 12, 10, 11, 5],
   [0, 2, 5, 8, 3, 1, 10, 9, 4, 12, 11, 6, 7],
   [0, 2, 5, 12, 11, 10, 1, 6, 4, 8, 3, 9, 7],
   [0, 2, 5, 12, 3, 9, 6, 1, 7, 8, 11, 10, 4],
   [0, 2, 3, 8, 11, 10, 4, 6, 1, 12, 5, 7, 9],
   [0, 3, 2, 9, 5, 7, 10, 4, 8, 1, 11, 6, 12],
   [0, 2, 4, 8, 10, 11, 3, 6, 5, 12, 1, 9, 7],
   [0, 2, 5, 8, 11, 6, 9, 10, 7, 12, 3, 1, 4],
   [0, 2, 3, 8, 5, 7, 6, 4, 9, 12, 11, 10, 1],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 3, 2, 1, 5, 4, 6, 7, 12, 9, 11, 10, 8],
   [0, 3, 5, 1, 2, 8, 10, 12, 7, 9, 11, 6, 4],
   [0, 2, 4, 8, 1, 9, 6, 3, 7, 12, 10, 11, 5],
   [0, 1, 5, 3, 8, 2, 10, 12, 4, 9, 6, 11, 7],
   [0, 3, 2, 9, 5, 7, 10, 4, 8, 1, 11, 6, 12],
   [0, 3, 5, 1, 11, 6, 12, 10, 4, 9, 2, 8, 7],
   [0, 3, 5, 9, 2, 12, 6, 8, 4, 1, 11, 10, 7],
   [0, 3, 5, 9, 11, 10, 8, 6, 7, 1, 2, 12, 4],
   [0, 2, 4, 8, 10, 11, 3, 6, 5, 12, 1, 9, 7],
   [0, 1, 5, 3, 6, 11, 12, 10, 7, 9, 8, 2, 4],
   [0, 2, 1, 8, 4, 5, 11, 7, 3, 12, 10, 6, 9]]

def A2 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [12, 1, 5, 8, 4, 2, 11, 7, 3, 9, 10, 6, 0],
   [0, 2, 1, 5, 4, 3, 6, 11, 9, 8, 10, 7, 12],
   [12, 1, 8, 5, 0, 6, 3, 7, 11, 9, 10, 2, 4],
   [12, 2, 5, 7, 0, 1, 9, 8, 3, 11, 10, 6, 4],
   [12, 2, 9, 11, 10, 1, 5, 3, 8, 7, 0, 6, 4],
   [12, 2, 9, 3, 0, 6, 5, 11, 7, 8, 10, 1, 4],
   [12, 2, 7, 8, 10, 1, 3, 5, 11, 9, 4, 6, 0],
   [0, 2, 6, 9, 4, 7, 1, 8, 5, 11, 10, 3, 12],
   [12, 1, 8, 7, 10, 2, 3, 5, 9, 11, 0, 6, 4],
   [12, 2, 5, 8, 10, 6, 9, 7, 11, 3, 0, 1, 4],
   [12, 2, 7, 5, 4, 6, 3, 8, 9, 11, 10, 1, 0],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 2, 1, 5, 4, 3, 6, 11, 9, 8, 10, 7, 12],
   [0, 2, 5, 1, 12, 7, 9, 11, 6, 8, 10, 3, 4],
   [12, 1, 8, 5, 0, 6, 3, 7, 11, 9, 10, 2, 4],
   [0, 5, 2, 7, 12, 1, 9, 3, 8, 6, 10, 11, 4],
   [0, 2, 6, 9, 4, 7, 1, 8, 5, 11, 10, 3, 12],
   [0, 2, 5, 11, 10, 3, 9, 1, 8, 6, 12, 7, 4],
   [0, 2, 9, 6, 12, 3, 5, 8, 1, 11, 10, 7, 4],
   [0, 2, 9, 8, 10, 7, 5, 6, 11, 1, 12, 3, 4],
   [12, 1, 8, 7, 10, 2, 3, 5, 9, 11, 0, 6, 4],
   [0, 5, 2, 3, 10, 11, 9, 7, 6, 8, 12, 1, 4],
   [12, 1, 5, 8, 4, 2, 11, 7, 3, 9, 10, 6, 0]]

def A3 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 2, 1, 8, 4, 5, 11, 7, 3, 12, 10, 6, 9],
   [0, 3, 2, 1, 5, 4, 6, 7, 12, 9, 11, 10, 8],
   [0, 4, 1, 7, 2, 12, 6, 8, 3, 5, 10, 11, 9],
   [0, 5, 1, 4, 8, 2, 11, 12, 3, 7, 6, 10, 9],
   [0, 6, 1, 10, 8, 2, 7, 12, 9, 11, 5, 4, 3],
   [0, 7, 1, 4, 12, 2, 6, 8, 9, 5, 11, 10, 3],
   [0, 8, 1, 2, 6, 10, 7, 11, 3, 12, 5, 4, 9],
   [0, 9, 2, 1, 7, 4, 11, 5, 8, 3, 6, 10, 12],
   [0, 10, 1, 6, 2, 8, 7, 12, 3, 11, 4, 5, 9],
   [0, 11, 1, 10, 12, 2, 5, 8, 3, 6, 7, 4, 9],
   [0, 12, 1, 2, 7, 4, 6, 5, 3, 8, 11, 10, 9],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 3, 2, 1, 5, 4, 6, 7, 12, 9, 11, 10, 8],
   [0, 3, 4, 1, 12, 2, 11, 8, 5, 9, 6, 10, 7],
   [0, 4, 1, 7, 2, 12, 6, 8, 3, 5, 10, 11, 9],
   [0, 1, 5, 3, 8, 2, 10, 12, 4, 9, 6, 11, 7],
   [0, 9, 2, 1, 7, 4, 11, 5, 8, 3, 6, 10, 12],
   [0, 3, 10, 1, 8, 2, 5, 12, 11, 9, 7, 4, 6],
   [0, 9, 4, 1, 8, 2, 6, 12, 7, 3, 11, 10, 5],
   [0, 9, 10, 1, 12, 2, 7, 8, 6, 3, 5, 4, 11],
   [0, 10, 1, 6, 2, 8, 7, 12, 3, 11, 4, 5, 9],
   [0, 1, 11, 3, 12, 2, 4, 8, 10, 9, 7, 5, 6],
   [0, 2, 1, 8, 4, 5, 11, 7, 3, 12, 10, 6, 9]]

def A4 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [12, 1, 5, 8, 4, 2, 11, 7, 3, 9, 10, 6, 0],
   [0, 2, 1, 5, 4, 3, 6, 11, 9, 8, 10, 7, 12],
   [4, 1, 11, 6, 12, 3, 5, 7, 2, 9, 10, 8, 0],
   [4, 5, 1, 8, 12, 2, 11, 3, 7, 6, 10, 9, 0],
   [10, 5, 1, 7, 12, 6, 11, 9, 8, 2, 4, 3, 0],
   [4, 11, 1, 3, 12, 6, 5, 8, 9, 2, 10, 7, 0],
   [12, 5, 1, 6, 10, 7, 11, 2, 3, 9, 4, 8, 0],
   [0, 6, 1, 11, 4, 8, 2, 5, 7, 3, 10, 9, 12],
   [10, 1, 5, 6, 12, 7, 11, 3, 2, 8, 4, 9, 0],
   [10, 11, 1, 9, 12, 2, 5, 7, 3, 6, 4, 8, 0],
   [12, 11, 1, 6, 4, 3, 5, 2, 7, 8, 10, 9, 0],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 2, 1, 5, 4, 3, 6, 11, 9, 8, 10, 7, 12],
   [0, 3, 1, 11, 12, 2, 8, 5, 9, 6, 10, 7, 4],
   [4, 1, 11, 6, 12, 3, 5, 7, 2, 9, 10, 8, 0],
   [0, 5, 2, 7, 12, 1, 9, 3, 8, 6, 10, 11, 4],
   [0, 6, 1, 11, 4, 8, 2, 5, 7, 3, 10, 9, 12],
   [0, 7, 1, 5, 12, 2, 9, 11, 8, 6, 4, 3, 10],
   [0, 8, 1, 5, 12, 6, 3, 11, 7, 2, 10, 9, 4],
   [0, 9, 1, 11, 12, 6, 7, 5, 3, 2, 4, 8, 10],
   [10, 1, 5, 6, 12, 7, 11, 3, 2, 8, 4, 9, 0],
   [0, 11, 2, 3, 12, 1, 8, 7, 9, 6, 4, 5, 10],
   [12, 1, 5, 8, 4, 2, 11, 7, 3, 9, 10, 6, 0]]

def B1 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 3, 2, 1, 5, 4, 6, 7, 12, 9, 11, 10, 8],
   [0, 3, 5, 1, 2, 8, 10, 12, 7, 9, 11, 6, 4],
   [1, 0, 5, 3, 4, 2, 12, 10, 8, 9, 7, 11, 6],
   [0, 1, 5, 3, 8, 2, 10, 12, 4, 9, 6, 11, 7],
   [0, 3, 2, 9, 5, 7, 10, 4, 8, 1, 11, 6, 12],
   [0, 3, 5, 1, 11, 6, 12, 10, 4, 9, 2, 8, 7],
   [0, 3, 5, 9, 2, 12, 6, 8, 4, 1, 11, 10, 7],
   [0, 3, 5, 9, 11, 10, 8, 6, 7, 1, 2, 12, 4],
   [1, 0, 5, 3, 7, 11, 10, 12, 6, 9, 4, 2, 8],
   [0, 1, 5, 3, 6, 11, 12, 10, 7, 9, 8, 2, 4],
   [1, 0, 2, 3, 8, 5, 7, 6, 4, 9, 12, 11, 10]]

def B2 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 2, 1, 5, 4, 3, 6, 11, 9, 8, 10, 7, 12],
   [0, 2, 5, 1, 12, 7, 9, 11, 6, 8, 10, 3, 4],
   [0, 4, 2, 3, 1, 12, 9, 7, 8, 6, 11, 10, 5],
   [0, 5, 2, 7, 12, 1, 9, 3, 8, 6, 10, 11, 4],
   [0, 2, 6, 9, 4, 7, 1, 8, 5, 11, 10, 3, 12],
   [0, 2, 5, 11, 10, 3, 9, 1, 8, 6, 12, 7, 4],
   [0, 2, 9, 6, 12, 3, 5, 8, 1, 11, 10, 7, 4],
   [0, 2, 9, 8, 10, 7, 5, 6, 11, 1, 12, 3, 4],
   [0, 4, 2, 7, 11, 10, 9, 3, 6, 8, 1, 12, 5],
   [0, 5, 2, 3, 10, 11, 9, 7, 6, 8, 12, 1, 4],
   [0, 12, 2, 7, 5, 4, 6, 3, 8, 9, 11, 10, 1]]

def B3 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 3, 2, 1, 5, 4, 6, 7, 12, 9, 11, 10, 8],
   [0, 3, 4, 1, 12, 2, 11, 8, 5, 9, 6, 10, 7],
   [1, 0, 5, 3, 4, 2, 12, 10, 8, 9, 7, 11, 6],
   [0, 1, 5, 3, 8, 2, 10, 12, 4, 9, 6, 11, 7],
   [0, 9, 2, 1, 7, 4, 11, 5, 8, 3, 6, 10, 12],
   [0, 3, 10, 1, 8, 2, 5, 12, 11, 9, 7, 4, 6],
   [0, 9, 4, 1, 8, 2, 6, 12, 7, 3, 11, 10, 5],
   [0, 9, 10, 1, 12, 2, 7, 8, 6, 3, 5, 4, 11],
   [1, 0, 11, 3, 10, 2, 8, 4, 12, 9, 6, 5, 7],
   [0, 1, 11, 3, 12, 2, 4, 8, 10, 9, 7, 5, 6],
   [1, 0, 2, 3, 8, 5, 7, 6, 4, 9, 12, 11, 10]]

def B4 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
   [0, 2, 1, 5, 4, 3, 6, 11, 9, 8, 10, 7, 12],
   [0, 3, 1, 11, 12, 2, 8, 5, 9, 6, 10, 7, 4],
   [0, 4, 2, 3, 1, 12, 9, 7, 8, 6, 11, 10, 5],
   [0, 5, 2, 7, 12, 1, 9, 3, 8, 6, 10, 11, 4],
   [0, 6, 1, 11, 4, 8, 2, 5, 7, 3, 10, 9, 12],
   [0, 7, 1, 5, 12, 2, 9, 11, 8, 6, 4, 3, 10],
   [0, 8, 1, 5, 12, 6, 3, 11, 7, 2, 10, 9, 4],
   [0, 9, 1, 11, 12, 6, 7, 5, 3, 2, 4, 8, 10],
   [0, 10, 2, 7, 1, 12, 8, 3, 9, 6, 5, 4, 11],
   [0, 11, 2, 3, 12, 1, 8, 7, 9, 6, 4, 5, 10],
   [0, 12, 2, 7, 5, 4, 6, 3, 8, 9, 11, 10, 1]]

set_option maxRecDepth 100000 in
theorem tabA : ∀ j : Fin 26,
    (∀ a, fn (A1.getD j.val []) (fn (A3.getD j.val []) a) = a) ∧
    (∀ a, fn (A3.getD j.val []) (fn (A1.getD j.val []) a) = a) ∧
    (∀ a, fn (A2.getD j.val []) (fn (A4.getD j.val []) a) = a) ∧
    (∀ a, fn (A4.getD j.val []) (fn (A2.getD j.val []) a) = a) ∧
    (∀ p l : Fin 13, p - l ∈ D ↔ fn (A1.getD j.val []) p - fn (A2.getD j.val []) l ∈ D) ∧
    rho (fn (A1.getD j.val [])) (fn (A2.getD j.val [])) 0 = 0 ∧
    (j.val = 0 ∨ rho (fn (A1.getD j.val [])) (fn (A2.getD j.val [])) j.val = 1 ∨
      rho (fn (A1.getD j.val [])) (fn (A2.getD j.val [])) j.val = 13 ∨
      rho (fn (A1.getD j.val [])) (fn (A2.getD j.val [])) j.val = 14) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tabB : ∀ j : Fin 13,
    (∀ a, fn (B1.getD j.val []) (fn (B3.getD j.val []) a) = a) ∧
    (∀ a, fn (B3.getD j.val []) (fn (B1.getD j.val []) a) = a) ∧
    (∀ a, fn (B2.getD j.val []) (fn (B4.getD j.val []) a) = a) ∧
    (∀ a, fn (B4.getD j.val []) (fn (B2.getD j.val []) a) = a) ∧
    (∀ p l : Fin 13, p - l ∈ D ↔ fn (B1.getD j.val []) p - fn (B2.getD j.val []) l ∈ D) ∧
    rho (fn (B1.getD j.val [])) (fn (B2.getD j.val [])) 13 = 13 ∧
    (j.val = 0 ∨ rho (fn (B1.getD j.val [])) (fn (B2.getD j.val [])) (13 + j.val) = 14) := by
  decide +kernel

def canon : List (List ℕ) := [[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]]

theorem pairP (n j : ℕ) (h : R n [0, j]) : ∃ L' ∈ canon, R n L' := by
  rcases Nat.lt_or_ge j 26 with hj | hj
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := tabA ⟨j, hj⟩
    have h8 := transfer _ _ _ _ h1 h2 h3 h4 h5 n _ h
    simp only [List.map_cons, List.map_nil] at h8
    rw [h6] at h8
    rcases h7 with h7 | h7 | h7 | h7
    · simp only at h7
      subst h7
      exact ⟨[0], by simp [canon], Rdup n 0 h⟩
    · rw [h7] at h8
      exact ⟨[0, 1], by simp [canon], h8⟩
    · rw [h7] at h8
      exact ⟨[0, 13], by simp [canon], h8⟩
    · rw [h7] at h8
      exact ⟨[0, 14], by simp [canon], h8⟩
  · exact ⟨[0], by simp [canon], R2b n 0 j hj h⟩

theorem pairL (n j : ℕ) (h : R n [13, j]) : ∃ L' ∈ canon, R n L' := by
  rcases Nat.lt_or_ge j 13 with hj | hj
  · have h2 := shift (Fin.ofNat 13 j) n _ (Rswap n 13 j h)
    simp only [List.map_cons, List.map_nil] at h2
    rw [rho_shift_pt j hj] at h2
    exact pairP n _ h2
  · rcases Nat.lt_or_ge j 26 with hj2 | hj2
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := tabB ⟨j - 13, by omega⟩
      have h8 := transfer _ _ _ _ h1 h2 h3 h4 h5 n _ h
      simp only [List.map_cons, List.map_nil] at h8
      rw [h6] at h8
      have e : 13 + (j - 13) = j := by omega
      rcases h7 with h7 | h7
      · simp only at h7
        have e2 : j = 13 := by omega
        subst e2
        exact ⟨[13], by simp [canon], Rdup n 13 h⟩
      · simp only [e] at h7
        rw [h7] at h8
        exact ⟨[13, 14], by simp [canon], h8⟩
    · exact ⟨[13], by simp [canon], R2b n 13 j hj2 h⟩

theorem single (n i : ℕ) (h : R n [i]) : ∃ L' ∈ canon, R n L' := by
  rcases Nat.lt_or_ge i 13 with hi | hi
  · have h2 := shift (Fin.ofNat 13 i) n _ h
    simp only [List.map_cons, List.map_nil] at h2
    rw [rho_shift_pt i hi] at h2
    exact ⟨[0], by simp [canon], h2⟩
  · rcases Nat.lt_or_ge i 26 with hi2 | hi2
    · have h2 := shift (Fin.ofNat 13 (i - 13)) n _ h
      simp only [List.map_cons, List.map_nil] at h2
      rw [rho_shift_ln i hi hi2] at h2
      exact ⟨[13], by simp [canon], h2⟩
    · exact ⟨[], by simp [canon], R1 n i hi2 h⟩

theorem main (C : Circuit) (L : List ℕ) (hlen : L.length ≤ 2) (hm : Monotone2 C) (ht : Topo C)
    (hg : Good C L) :
    ∃ C' : Circuit, ∃ L' ∈ canon, C'.size = C.size ∧ Monotone2 C' ∧ Topo C' ∧ Good C' L' := by
  have hR : R C.size L := ⟨C, rfl, hm, ht, hg⟩
  have key : ∃ L' ∈ canon, R C.size L' := by
    match L, hlen, hR with
    | [], _, hR => exact ⟨[], by simp [canon], hR⟩
    | [i], _, hR => exact single _ i hR
    | [i, j], _, hR =>
      rcases Nat.lt_or_ge i 13 with hi | hi
      · have h2 := shift (Fin.ofNat 13 i) _ _ hR
        simp only [List.map_cons, List.map_nil] at h2
        rw [rho_shift_pt i hi] at h2
        exact pairP _ _ h2
      · rcases Nat.lt_or_ge i 26 with hi2 | hi2
        · have h2 := shift (Fin.ofNat 13 (i - 13)) _ _ hR
          simp only [List.map_cons, List.map_nil] at h2
          rw [rho_shift_ln i hi hi2] at h2
          exact pairL _ _ h2
        · exact single _ j (R2a _ i j hi2 hR)
    | _ :: _ :: _ :: _, hl, _ => simp at hl
  obtain ⟨L', hL', C', h1, h2, h3, h4⟩ := key
  exact ⟨C', L', hL', h1, h2, h3, h4⟩

end PEqualNP.Outside.L_meta_3801

theorem PEqualNP.Outside.L_meta_3801 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : List ℕ) =>   have x7 : List Bool → List Bool := fun (x7 : List Bool) => x7 ++ [x6.any fun (x8 : ℕ) => x7.getD x8 Bool.false];   (∀ (x8 x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 → x5.eval (x7 (x2 x8 x9)) = Bool.true) ∧ ∀ (x8 : Finset (Fin (13 : ℕ))), x4 x8 → x5.eval (x7 (x3 x8)) = Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List ℕ), x7.length ≤ (2 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x10 : Fin x6.gates.length), ∀ x11 ∈ (x6.gates.get x10).inputs, x11 < (27 : ℕ) + ↑x10) → x5 x6 x7 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), ∃ x13 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]], x12.size = x6.size ∧ PEqualNP.MetaComplexity.Monotone2 x12 ∧ (∀ (x14 : Fin x12.gates.length), ∀ x15 ∈ (x12.gates.get x14).inputs, x15 < (27 : ℕ) + ↑x14) ∧ x5 x12 x13 := by
  intro x1 x2 x3 x4 x5 C L hlen hm ht hg
  exact L_meta_3801.main C L hlen hm ht hg

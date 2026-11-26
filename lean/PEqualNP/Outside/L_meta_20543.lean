import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20543

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def truthMask : Nat := 2 ^ 16 - 1

def negD (d w : Nat) : Nat := (w ^^^ truthMask) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then orD d a b else andD d a b

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      negD d a ≠ 0 → negD d a ≠ d → negD d a ∉ (a :: r) →
      P s (negD d a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then andD d a b else orD d a b) ≠ 0 →
      (if c then andD d a b else orD d a b) ≠ d →
      (if c then andD d a b else orD d a b) ∉ (a :: b :: r) →
      P s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {d y : Nat}

theorem Run.done : RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD d y s xs) :
    RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem Run.one {s a r} (save : Bool)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
    (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))) :
    RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem Run.fold {P : ∀ t ws, RunD d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
      (h : RunD d y s (negD d a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then andD d a b else orD d a b) ≠ 0)
      (hd : (if c then andD d a b else orD d a b) ≠ d)
      (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
      (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h0 hd hm h))
    {t ws} (h : RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem run_len {d y s xs} (h : RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {d y t ws} (h : RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def NatReach (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    (∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
    (∃ b a c op, bank = binD d op a c :: b ∧ NatReach d roots p b ∧ Avail d b a ∧ Avail d b c)

theorem truthMask_bit (i : Nat) : truthMask.testBit i = decide (i < 16) := by
  rw [truthMask, Nat.testBit_two_pow_sub_one]

theorem negD_const {d : Nat} (hd : d &&& truthMask = d) {a : Nat} (hc : IsConst d a) :
    IsConst d (negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : IsConst d a) :
    (binD d op a b &&& d = 0) ∨ (binD d op a b &&& d = d) ∨ (binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_comm (d : Nat) (op : Bool) (a b : Nat) : binD d op a b = binD d op b a := by
  cases op <;> simp [binD, andD, orD, Nat.and_comm, Nat.or_comm]

theorem avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail d bank w) :
    Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail d bank v) : Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem negD_mask (d a : Nat) : negD d (a &&& d) = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem andD_mask (d a b : Nat) : andD d (a &&& d) (b &&& d) = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem orD_mask (d a b : Nat) : orD d (a &&& d) (b &&& d) = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem pull_one {d Y k ws} (hd : d &&& truthMask = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : Avail d b a) (hsub : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hc
        rcases negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h1)
      obtain ⟨v, hv, hve⟩ := ha.resolve_left ha_nc
      set a' := a &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨v, hv, hve⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : negD d a' = z := negD_mask d a
      have h1 : RunD d Y k (negD d a' :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      have hne0 : negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : RunD d Y k (negD d a' :: kept true a' (rest.erase a')) :=
          Run.perm (hp2.cons _) h1
        have hnm : negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact Run.perm hp2.symm (Run.one true hne0 hned hnm h2)
      · have h2 : RunD d Y k (negD d a' :: kept false a' rest) := h1
        have hnm : negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Run.one false hne0 hned hnm h2⟩
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_prop
          · exact hrest_prop w hw
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_mem
          · exact hrest_sub w hw
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : Avail d b a) (hc : Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, binD, andD, orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hca
        rcases binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hz' : z = binD d op c a := binD_comm d op a c
        rcases binD_const_left op hcc with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans (by rw [hz']; exact h0))
        · exact hzp.2 (hz_mask.symm.trans (by rw [hz']; exact h1))
        · rcases ha with hca | ⟨v, hv, hve⟩
          · exact absurd hca ha_nc
          · have he' : z &&& d = a &&& d := hz'.symm ▸ he
            exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he'.symm.trans hz_mask)⟩)
      obtain ⟨va, hva, hvae⟩ := ha.resolve_left ha_nc
      obtain ⟨vc, hvc, hvce⟩ := hc.resolve_left hc_nc
      set a' := a &&& d
      set c' := c &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨va, hva, hvae⟩
      have hc'_mem : c' ∈ b.map (· &&& d) := List.mem_map.2 ⟨vc, hvc, hvce⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := ⟨fun e => hc_nc (Or.inl e), fun e => hc_nc (Or.inr e)⟩
      have hne_ac : a' ≠ c' := by
        intro heq
        dsimp only [a', c'] at heq
        have hz_eq : z = a' := by
          cases op
          · simp only [z, binD, Bool.false_eq_true, ite_false]; rw [← andD_mask, ← heq]; simp [andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, binD, ite_true]; rw [← orD_mask, ← heq]; simp [orD, a', Nat.and_assoc, Nat.and_self]
        exact hzb (hz_eq ▸ ha'_mem)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : (if !op then andD d a' c' else orD d a' c') = z := by
        cases op
        · simp [z, binD, a', c', andD_mask]
        · simp [z, binD, a', c', orD_mask]
      have h1 : RunD d Y k ((if !op then andD d a' c' else orD d a' c') :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail := by
        rw [mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept, mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then andD d a' c' else orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then andD d a' c' else orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then andD d a' c' else orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD d Y (k + 1) (a' :: c' :: tail) := Run.two (!op) ka kb hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac, hna_tail], List.nodup_cons.2 ⟨hnc_tail, htail_nd⟩⟩
      refine ⟨k + 1, a' :: c' :: tail, le_rfl, hnd3, ?_, ?_, h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem reach_to_run_aux {d : Nat} {roots : List Nat} {p bank} (hd : d &&& truthMask = d)
    (hr : NatReach d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (· &&& d)) ∧ RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : binD d op a c &&& d = binD d op a c := by cases op <;> simp [binD, andD, orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {d : Nat} {roots : List Nat} {T : Nat} {p bank} (hd : d &&& truthMask = d)
    (hnc : ¬ IsConst d T) (hr : NatReach d roots p bank) (ha : Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

theorem runD_bits {d y s ws} (hd : d &&& truthMask = d) (h : RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : truthMask.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : truthMask.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [andD, orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem runD_bits_le {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [andD, orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

def coversP (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {d T s : Nat} (hd : d &&& truthMask = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : coversP pairs s ws = true := by
  unfold coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : negD dm a ≠ 0) (hd : negD dm a ≠ dm) (hnm : negD dm a ∉ (a :: rest))
    (h : RunD dm y s (negD dm a :: kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  have hnc : ws.contains (negD dm a) = false := by
    cases h : ws.contains (negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true => simp [kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then andD dm a b else orD dm a b) = false := by
    cases h : ws.contains (if conj then andD dm a b else orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then andD dm a b else orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then andD dm a b else orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then andD dm a b else orD dm a b) = (if conj then andD dm b a else orD dm b a) := by
      cases conj <;> simp [andD, orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then andD dm b a else orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {dm y t ws} (h : RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD dm y s ys → f ys = true) →
      nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two p h0 hd hnm h f hf

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => andD truthMask (w.getD i 0) acc) truthMask
  | .or  => g.inputs.foldr (fun i acc => orD truthMask (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => truthMask | i :: _ => negD truthMask (w.getD i 0)
  | _ => 0

def execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gvN l g]) w

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 16)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : truthMask.testBit r = true := by simp [truthMask_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 16)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem execN_reach (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), NatReach truthMask roots p bank →
      (∀ v ∈ w, Avail truthMask bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ NatReach truthMask roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail truthMask bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail truthMask bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))

    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ NatReach truthMask roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail truthMask bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD truthMask a truthMask &&& truthMask = a &&& truthMask := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD truthMask a 0 &&& truthMask = a &&& truthMask := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail truthMask (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD truthMask false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [binD, andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD truthMask true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [binD, orD]; cases truthMask.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · refine ⟨p + 1, negD truthMask (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def roots : List Nat := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]
def target : Nat := 29628
def goal : Nat := target &&& truthMask

def pairs : List (Nat × Nat) := [(6, 4), (0, 2), (15, 13), (0, 3), (10, 14), (11, 7), (0, 12), (1, 9), (6, 7), (6, 14), (1, 5), (10, 9), (11, 8), (15, 7), (11, 3), (15, 14), (10, 2), (6, 2), (15, 3), (6, 5), (11, 9), (1, 13), (10, 8), (15, 12), (0, 4), (0, 8), (1, 2), (1, 3), (10, 3), (11, 2), (10, 7), (10, 12), (11, 5), (11, 14), (6, 8), (6, 12), (15, 4), (15, 8), (10, 13), (11, 4), (6, 13), (15, 5), (0, 7), (0, 14), (6, 3), (6, 9), (10, 4), (11, 12), (15, 2), (15, 9)]

def key (ws : List Nat) : Nat := ws.sum % 512

theorem key_lt (ws : List Nat) : key ws < 512 := Nat.mod_lt _ (by decide)

set_option maxRecDepth 200000 in
def rowsOf : Nat → List (List (List Nat))
  | 2 => [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[36088, 65348], [36672, 64764], [36856, 64580]], [], [], [], [], [], [[13299, 16463], [14323, 17487]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 35916], [16399, 52300]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[32624, 62259]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[143, 36044], [16527, 52428]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[13299, 49072]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 29619], [143, 29491], [13107, 16527], [13235, 16399], [32911, 62259], [34959, 64307]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
  | 3 => [[], [], [], [], [], [], [], [], [], [], [], [[240, 16463, 52428], [240, 17487, 51404], [1264, 17487, 52428], [4080, 20303, 52428]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[20303, 52428, 61455]], [[4080, 30711, 62532]], [], [], [], [], [], [], [[4080, 13299, 17487]], [[8177, 13299, 17487]], [[12274, 13299, 17487]], [[13299, 16371, 17487]], [], [], [], [], [], [[255, 1092, 35064], [255, 17476, 36088], [255, 17476, 51448], [1279, 17476, 36088], [16639, 17476, 35064], [35064, 61695, 62532]], [[1024, 35064, 65348], [1092, 35064, 65280], [2048, 36856, 62532], [3840, 32832, 64764], [3840, 35064, 62532], [3840, 35064, 64580], [3840, 36088, 62532], [3952, 34952, 62532], [4080, 34824, 62532], [17476, 35064, 48896], [17476, 36088, 65280], [17476, 36856, 63488], [17476, 51448, 65280], [19524, 36856, 61440], [20292, 36088, 61440], [32624, 52428, 61440], [35064, 36608, 62532]], [], [], [], [], [], [[15, 13299, 16448], [1024, 13299, 17487], [3840, 13299, 20303]], [], [], [], [[15, 13299, 16452], [15, 14323, 17476], [13299, 16399, 17476]], [], [], [], [[15, 1092, 30711], [15, 14327, 17476], [143, 34952, 62259], [16399, 17476, 30711], [30471, 61695, 62532], [30711, 61455, 62532]], [[3840, 30471, 62532]], [], [], [], [], [], [[13299, 17487, 61455]], [[4369, 8946, 16463], [4369, 9970, 17487], [5393, 8946, 17487]], [], [], [], [], [], [], [], [], [[15, 1092, 34824], [15, 16384, 52300], [15, 17476, 51208], [3276, 3840, 34959], [16399, 17476, 34824], [34824, 61455, 62532]], [], [], [], [], [], [], [[4593, 8738, 16463], [4593, 9762, 17487], [5617, 8738, 17487]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[240, 13107, 16463], [240, 14131, 17487], [1264, 13107, 17487], [4080, 13107, 20303]], [], [], [], [], [], [], [], [], [], [[3904, 35064, 62532], [35064, 36672, 62532]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[13107, 20303, 61455]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[3840, 13299, 48048], [4369, 32624, 61986], [8738, 32624, 61713], [13107, 32624, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 32631, 62259]], [], [], [[240, 35976, 65348], [240, 36744, 64580], [1264, 34952, 65348], [4080, 34952, 64580]], [], [], [], [], [[255, 34959, 62259], [34959, 61695, 62259]], [[3840, 34959, 62259], [34959, 62259, 65280]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[143, 34952, 64443]], [[7953, 34959, 62259], [34959, 62259, 65297]], [], [], [], [], [], [], [], [[34952, 61455, 64580], [34952, 63503, 64580]], [], [], [], [], [], [], [], [], [[12066, 34959, 62259], [34959, 62259, 65314]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[16179, 34959, 62259], [34959, 62259, 65331]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[3952, 30583, 62532]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[4080, 34952, 62660]], [], [], [], [], [[13299, 17487, 61695]], [[3840, 13299, 17487]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[7953, 13299, 17487]], [], [], [], [], [], [], [[255, 36751, 52428]], [[15, 128, 36044], [15, 1220, 34952], [15, 16512, 52428], [15, 17604, 51336], [128, 16399, 52428], [143, 1092, 34952], [143, 16384, 52428], [143, 17476, 51336], [3840, 17487, 52236], [16399, 17604, 34952], [16527, 17476, 34952], [17612, 34959, 61440], [32911, 52428, 61440], [34952, 61455, 62660], [34952, 61583, 62532], [34959, 50380, 61440], [34959, 52428, 63488], [36751, 52428, 65280]], [], [], [], [], [], [], [], [], [[12066, 13299, 17487]], [], [], [], [], [], [], [], [[240, 49072, 52428]], [], [], [], [], [], [], [], [], [[13299, 16179, 17487]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[3840, 30576, 62259]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[255, 35064, 64443], [3003, 35064, 61695]], [[3003, 3840, 35064], [4369, 8946, 49072], [35064, 48059, 48896], [35064, 64443, 65280]], [], [], [], [], [], [], [], [[3840, 13119, 17652, 63624]], [], [[15, 13299, 49083]], [], [], [], [[15, 30711, 64443], [255, 13107, 36751]], [[15, 128, 29491], [15, 4369, 25250], [15, 4497, 25122], [15, 8738, 20881], [15, 8866, 20753], [15, 13107, 16512], [15, 13235, 16384], [15, 32896, 62259], [128, 13107, 16399], [143, 4369, 25122], [143, 8738, 20753], [143, 13107, 16384], [2048, 34959, 62259], [3003, 3840, 30471], [3840, 36751, 62259], [4369, 8738, 16527], [4369, 8866, 16399], [4369, 32911, 61986], [4369, 34959, 64034], [4497, 8738, 16399], [6417, 34959, 61986], [8738, 32911, 61713], [8738, 34959, 63761], [10786, 34959, 61713], [13107, 32911, 61440], [13107, 34959, 63488], [13107, 36751, 65280], [15155, 34959, 61440]], [[4593, 8738, 49072]], [], [], [], [], [], [], [[15, 32904, 62259], [15, 34952, 64307]], [[240, 17487, 51340]], [], [], [], [], [], [], [[15, 34824, 64443], [15, 34952, 64315]], [[240, 13107, 49072]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
  | 4 => [[[4080, 17476, 34952, 65348], [4080, 17476, 52428, 65280], [4080, 20292, 34952, 62532], [4080, 20292, 52428, 61440], [4080, 34952, 62532, 65348], [20292, 52428, 61440, 65520]], [], [], [], [], [], [[15, 13235, 17476, 61440], [143, 13107, 17476, 61440], [7953, 17476, 34959, 61986], [16179, 17476, 34959, 61440]], [], [], [], [], [[15, 240, 16448, 52428], [15, 240, 17476, 36040], [15, 240, 17476, 51400], [240, 1024, 17487, 52428], [240, 3072, 17487, 52428], [240, 3840, 20303, 52428], [240, 16452, 17487, 34952], [240, 16463, 17476, 34952], [240, 17476, 17487, 35976], [1264, 17476, 17487, 34952], [3840, 4080, 17487, 52428], [4080, 17476, 20303, 34952], [4080, 17487, 20292, 34952]], [[3840, 4593, 17487, 52428]], [], [], [[15, 240, 1092, 36044], [15, 240, 16452, 52428], [15, 240, 17476, 36044], [15, 240, 17476, 51404], [15, 1264, 17476, 52428], [15, 4080, 20292, 52428], [240, 16399, 17476, 52428], [3855, 4080, 17476, 52428], [17476, 52428, 61455, 61680]], [], [], [], [], [], [], [], [], [], [[3840, 35064, 56797, 62532]], [[240, 17487, 52428, 61455]], [[15, 3840, 35016, 62532], [15, 3904, 34952, 62532]], [[240, 4080, 35064, 62532], [4080, 17476, 35064, 61680]], [], [[15, 4095, 20292, 52428], [255, 17476, 52428, 61455]], [[15, 20292, 49152, 52428], [15, 20292, 52428, 61440], [17476, 34952, 61455, 65348], [17476, 52428, 61455, 65280], [20292, 34952, 61455, 62532], [20292, 52428, 61440, 61455], [34952, 61455, 62532, 65348]], [], [], [], [], [], [], [], [[3840, 13299, 17476, 61680], [4080, 13299, 17476, 61440], [13299, 17476, 61440, 65520]], [], [], [[15, 20303, 52428, 61440], [3840, 17487, 52428, 61455], [17476, 20303, 34952, 61455], [17487, 20292, 34952, 61455]], [[240, 3840, 30711, 62532], [255, 4080, 17476, 35064], [4080, 17476, 30711, 61440], [17476, 30711, 61440, 65520]], [[3840, 4080, 35064, 62532], [3840, 35064, 62532, 65520], [4080, 17476, 35064, 65280]], [[3840, 4593, 35064, 62532]], [[15, 20292, 52428, 61455], [3855, 17476, 52428, 61455]], [], [[15, 24405, 52428, 61440]], [[15, 240, 30583, 64443]], [[240, 255, 34952, 64443], [240, 3003, 34952, 61695], [240, 3840, 13299, 17487], [255, 34952, 48059, 61680], [3840, 4593, 8946, 17487]], [[240, 3003, 3840, 34952], [240, 34952, 48059, 48896], [240, 34952, 64443, 65280], [255, 17476, 35064, 36856], [34952, 48059, 61680, 65280]], [[3840, 8946, 13299, 17487], [3840, 35064, 36856, 62532], [4080, 34952, 52428, 61680], [17476, 35064, 36856, 65280]], [[3840, 35064, 39417, 62532]], [[15, 4080, 13299, 17476]], [[15, 8177, 13299, 17476], [15, 13299, 17476, 61937]], [[15, 12274, 13299, 17476]], [[15, 13299, 16371, 17476], [15, 13299, 17476, 62451]], [[15, 4080, 17476, 30711], [255, 4095, 17476, 35064], [4095, 17476, 35064, 61695]], [[15, 240, 1092, 35064], [15, 240, 17476, 36088], [15, 240, 17476, 51448], [15, 1264, 17476, 35064], [15, 1264, 17476, 36088], [15, 16624, 17476, 35064], [15, 35064, 61680, 62532], [240, 16399, 17476, 35064], [240, 35064, 61455, 62532], [255, 1024, 17476, 35064], [255, 16384, 17476, 35064], [255, 17476, 35064, 61440], [255, 35064, 61440, 62532], [1092, 3840, 4095, 35064], [3003, 3840, 34952, 35064], [3840, 4095, 17476, 35064], [3840, 4095, 35064, 62532], [3840, 17476, 20479, 35064], [3855, 4080, 17476, 35064], [4095, 17476, 35064, 65280], [17476, 35064, 61440, 61695], [17476, 35064, 61455, 61680], [35064, 61440, 61695, 62532], [35064, 61695, 62532]], [[112, 3840, 34952, 62532], [240, 3840, 34824, 62532], [512, 3840, 35064, 62532], [1024, 3840, 35064, 62532], [1024, 17476, 35064, 65280], [1024, 20292, 35064, 61440], [1092, 3840, 35064, 61440], [2048, 3840, 35064, 62532], [2048, 17476, 36856, 61440], [3840, 4096, 35064, 62532], [3840, 8192, 35064, 62532], [3840, 16384, 35064, 62532], [3840, 17476, 35064, 45056], [3840, 17476, 35064, 61440], [3840, 17476, 35064, 61952], [3840, 17476, 35064, 62464], [3840, 17476, 35064, 63488], [3840, 17476, 36088, 61440], [3840, 17476, 51448, 61440], [3840, 19524, 35064, 61440], [3840, 21572, 35064, 61440], [3840, 25668, 35064, 61440], [3840, 32768, 35064, 62532], [3840, 35064, 50244, 61440], [3840, 35064, 61440, 62532], [3840, 35064, 62532], [3952, 17476, 34952, 61440], [4080, 17476, 34824, 61440], [7936, 17476, 35064, 61440], [12032, 17476, 35064, 61440], [16384, 17476, 35064, 65280], [17476, 20224, 35064, 61440], [17476, 32624, 34952, 61440], [17476, 34824, 61440, 65520], [17476, 34952, 61440, 65392], [17476, 35064, 36608, 61440], [17476, 35064, 61440, 65280], [35064, 61440, 62532, 65280]], [[1, 3840, 35064, 62532]], [[2, 3840, 35064, 62532]], [], [[4, 3840, 35064, 62532], [3840, 17476, 35064, 61444]], [[15, 20292, 52428, 61986], [15, 28518, 52428, 61440]], [[15, 240, 28791, 52428], [4080, 4369, 8946, 17487]], [[15, 4593, 34952, 64443], [240, 255, 36744, 52428], [255, 4080, 34952, 52428]], [[8, 3840, 35064, 62532], [240, 36744, 52428, 65280], [4080, 34952, 52428, 65280], [4369, 8946, 12274, 17487]], [[15, 4095, 13299, 17476]], [[15, 1024, 13299, 17476], [15, 3840, 13299, 20292], [15, 13299, 16384, 17476], [15, 13299, 17476, 61440], [3840, 3855, 13299, 17476], [13299, 17476, 61440, 61455]], [], [], [[15, 4095, 17476, 30711]], [[15, 128, 34952, 62259], [15, 4497, 34952, 61986], [15, 8866, 34952, 61713], [15, 13235, 34952, 61440], [15, 16384, 17476, 30711], [15, 17476, 28672, 30711], [15, 17476, 30711, 61440], [15, 17604, 30583, 61440], [15, 30711, 61440, 62532], [15, 35064, 61695, 62532], [143, 4369, 34952, 61986], [143, 8738, 34952, 61713], [143, 13107, 34952, 61440], [143, 17476, 30583, 61440], [255, 17476, 30471, 61440], [255, 17476, 35064, 61455], [3840, 4095, 17476, 30471], [17476, 30471, 61440, 61695], [17476, 30711, 61440, 61455], [17476, 32631, 34959, 61440]], [[15, 3840, 35064, 50244], [15, 3840, 35064, 62532], [15, 4080, 17476, 34824], [15, 17476, 35064, 36608], [3840, 17476, 30471, 61440], [3840, 30471, 61440, 62532], [3840, 30471, 62532], [3840, 35064, 61455, 62532], [17476, 30471, 61440, 65280], [17476, 35064, 61455, 65280]], [[16, 3840, 35064, 62532]], [], [], [[15, 20292, 52476, 61440]], [], [[15, 13299, 17487, 61440], [255, 3855, 34952, 48059]], [[15, 4369, 8946, 16448], [15, 32631, 52428, 61440], [15, 34952, 46011, 61440], [15, 34952, 48059, 63488], [1024, 4369, 8946, 17487], [3003, 3840, 34952, 65295], [3840, 4369, 8946, 20303], [3855, 34952, 48059, 65280], [4080, 4593, 8738, 17487]], [[15, 240, 3276, 34952], [15, 240, 34952, 36044], [15, 240, 35976, 52428], [15, 1264, 34952, 52428], [240, 16399, 34952, 52428], [3840, 4369, 13299, 17487], [3855, 4080, 34952, 52428], [4593, 8177, 8738, 17487], [34952, 52428, 61455, 61680]], [[15, 4593, 36744, 52428]], [[15, 13299, 17476, 61455]], [[15, 4369, 8946, 16452], [15, 4369, 9970, 17476], [15, 5393, 8946, 17476], [15, 8946, 17476, 20753], [4369, 8946, 16399, 17476]], [[15, 17652, 52428, 63624], [4080, 13107, 17476, 61680]], [], [[15, 17476, 30711, 61455]], [[15, 3840, 30471, 62532], [15, 3855, 35064, 62532], [15, 4095, 17476, 34824], [255, 17476, 34952, 63631], [255, 17476, 34959, 63624], [255, 34959, 52428, 61440], [3840, 4095, 34959, 52428], [3855, 17476, 35064, 61455], [34959, 52428, 61440, 61695]], [[15, 16384, 17476, 34824], [15, 17476, 34824, 61440], [15, 34824, 61440, 62532], [3840, 34824, 62532, 65295], [3840, 34952, 62532, 63631], [3840, 34959, 49152, 52428], [3840, 34959, 52428, 61440], [3840, 34959, 61440, 64716], [3840, 34959, 62532, 63624], [17476, 34824, 61440, 61455], [17476, 34952, 63631, 65280], [17476, 34959, 63624, 65280], [34959, 52428, 61440, 65280]], [[32, 3840, 35064, 62532]], [[255, 17476, 35064, 61986], [8738, 35064, 61695, 62532]], [[3840, 8738, 35064, 62532], [3840, 35064, 61986, 62532], [17476, 35064, 61986, 65280]], [[15, 17476, 52236, 61440]], [], [[4369, 8946, 17487, 61455]], [[15, 4593, 8738, 16448], [240, 4080, 13107, 17487], [255, 34952, 52428, 61455], [1024, 4593, 8738, 17487], [3840, 4593, 8738, 20303]], [[15, 3276, 3840, 34952], [15, 17476, 34824, 63496], [15, 34824, 52300, 61440], [34952, 52428, 61455, 65280]], [], [], [[15, 4593, 8738, 16452], [15, 4593, 9762, 17476], [15, 4593, 17476, 25122], [15, 5617, 8738, 17476], [255, 4080, 13107, 17476], [4593, 8738, 16399, 17476]], [[4080, 13107, 17476, 65280], [4080, 13107, 20292, 61440], [13107, 20292, 61440, 65520]], [[15, 13299, 17476, 61986]], [], [[15, 17476, 34824, 61455]], [[3840, 8751, 35064, 62532]], [[15, 17476, 30711, 61986], [15, 17604, 34952, 61713], [143, 17476, 34952, 61713], [240, 3840, 48048, 52428], [7953, 34959, 52428, 61440]], [[3840, 8738, 30471, 62532]], [], [], [], [[4593, 8738, 17487, 61455]], [[15, 240, 13107, 16448], [240, 1024, 13107, 17487], [240, 3840, 13107, 20303], [240, 4369, 8738, 16463], [240, 4369, 9762, 17487], [240, 5393, 8738, 17487], [1264, 4369, 8738, 17487], [3840, 4080, 13107, 17487], [3855, 34952, 52428, 61455], [4080, 4369, 8738, 20303]], [[3840, 4593, 13107, 17487]], [], [[3840, 13107, 13299, 17487]], [[15, 240, 13107, 16452], [15, 240, 14131, 17476], [15, 240, 17476, 29491], [15, 1264, 13107, 17476], [15, 4080, 13107, 20292], [240, 13107, 16399, 17476], [3855, 4080, 13107, 17476], [13107, 17476, 61455, 61680]], [], [], [], [], [], [[64, 3840, 35064, 62532], [3840, 17476, 35064, 61504], [3840, 32832, 35064, 62532], [3904, 17476, 35064, 61440]], [[15, 17476, 34824, 61986], [3549, 3840, 4369, 34959], [3840, 34959, 52428, 61986], [3840, 34959, 56797, 61713], [12066, 34959, 52428, 61440]], [], [[17476, 35064, 61695, 62532]], [[3840, 17476, 35064, 62532]], [[240, 13107, 17487, 61455]], [], [], [], [[15, 4095, 13107, 20292], [255, 13107, 17476, 61455]], [[15, 13107, 20292, 61440], [13107, 17476, 61455, 65280], [13107, 20292, 61440, 61455]], [], [[15, 4593, 26214, 61986]], [], [], [[3840, 17487, 35064, 62532], [3840, 35064, 62532, 62543]], [], [], [], [[3840, 17476, 30471, 62532]], [], [[15, 13107, 20303, 61440], [3840, 13107, 17487, 61455], [4369, 8738, 20303, 61455]], [], [], [], [[15, 13107, 20292, 61455], [3855, 13107, 17476, 61455]], [], [[15, 8738, 24405, 61713], [15, 13107, 24405, 61440]], [], [], [], [[240, 4080, 30583, 62532], [240, 34952, 62259, 65520], [4080, 13107, 34952, 61680], [4080, 17476, 30583, 61680]], [], [], [], [[15, 17476, 52300, 61440], [3822, 3840, 8738, 34959], [3840, 34959, 61166, 61986]], [], [], [[3840, 26214, 35064, 62532], [3840, 35064, 62532, 63078]], [[240, 3003, 3840, 35064], [4369, 8738, 32624, 61440]], [], [], [], [], [[15, 4369, 28518, 61986], [15, 13107, 20292, 61986], [15, 13107, 28518, 61440]], [[15, 240, 13107, 28791]], [[240, 255, 13107, 36744], [255, 4080, 13107, 34952], [255, 4080, 17476, 30583]], [[240, 13107, 36744, 65280], [3840, 4080, 30583, 62532], [3840, 34952, 62259, 65520], [4080, 13107, 34952, 65280], [4080, 17476, 30583, 65280]], [], [[4080, 4593, 34952, 62532]], [], [], [], [], [[255, 3840, 35064, 48059]], [[3840, 4369, 8946, 48048], [3840, 35064, 48059, 65280]], [], [], [], [], [], [[15, 4369, 32631, 61986], [15, 8738, 32631, 61713], [15, 13107, 32631, 61440], [15, 16179, 17476, 62259]], [[15, 240, 1092, 30583], [15, 240, 13107, 35976], [15, 240, 14199, 17476], [15, 240, 17476, 29559], [15, 240, 29491, 34952], [15, 240, 34952, 62259], [15, 1264, 13107, 34952], [15, 1264, 17476, 30583], [15, 34952, 61680, 62259], [240, 13107, 16399, 34952], [240, 16399, 17476, 30583], [240, 30583, 61455, 62532], [3855, 4080, 13107, 34952], [3855, 4080, 17476, 30583], [13107, 34952, 61455, 61680], [17476, 30583, 61455, 61680]], [[15, 4593, 13107, 36744], [240, 255, 1092, 34952], [240, 255, 17476, 35976], [240, 255, 17476, 51336], [240, 16639, 17476, 34952], [240, 34952, 61695, 62532], [255, 1264, 17476, 34952], [255, 16624, 17476, 34952], [255, 17476, 34952, 61680], [255, 34952, 61680, 62532], [1264, 1279, 17476, 34952]], [[15, 8946, 34952, 62259], [15, 8946, 43690, 61713], [15, 34952, 62194, 62259], [128, 3840, 35064, 62532], [240, 1024, 34952, 65348], [240, 1092, 34952, 65280], [240, 2048, 36744, 62532], [240, 3840, 34952, 62532], [240, 3840, 34952, 64580], [240, 3840, 35976, 62532], [240, 17476, 34952, 48896], [240, 17476, 35976, 65280], [240, 17476, 36608, 63624], [240, 17476, 36744, 63488], [240, 17476, 51336, 65280], [240, 19524, 36744, 61440], [240, 20292, 35976, 61440], [240, 34952, 36608, 62532], [752, 3840, 34952, 62532], [1264, 3840, 34952, 62532], [1264, 17476, 34952, 65280], [1264, 20292, 34952, 61440], [2048, 4080, 34952, 62532], [2288, 3840, 34952, 62532], [3840, 33008, 34952, 62532], [3904, 17652, 34952, 61440], [4080, 17476, 34952, 63488], [4080, 19524, 34952, 61440], [16624, 17476, 34952, 65280], [17476, 34952, 61680, 65280], [17476, 34952, 63488, 65520], [19524, 34952, 61440, 65520], [34952, 61680, 62532, 65280]], [[15, 3840, 13299, 48059], [15, 13107, 13299, 36744]], [[15, 13107, 17652, 63624], [15, 17652, 34952, 62259]], [], [], [[15, 240, 34959, 62259], [255, 4369, 34959, 61986], [255, 8738, 34959, 61713], [255, 13107, 34959, 61440], [3840, 4095, 13107, 34959], [4369, 34959, 61695, 61986], [8738, 34959, 61695, 61713], [13107, 34959, 61440, 61695]], [[3840, 4369, 34959, 61986], [3840, 8738, 34959, 61713], [3840, 13107, 34959, 61440], [3840, 34959, 61440, 62259], [3840, 34959, 61713, 61986], [3840, 34959, 62259], [4369, 34959, 61986, 65280], [8738, 34959, 61713, 65280], [13107, 34959, 61440, 65280]], [[255, 17476, 34952, 63736], [255, 17476, 35064, 63624], [3840, 4593, 8738, 48048], [34952, 35064, 61695, 62532]], [[248, 3840, 34952, 62532], [3003, 3840, 4369, 35064], [3840, 34952, 35064, 62532], [3840, 35064, 62532, 63624], [17476, 34952, 63736, 65280], [17476, 35064, 63624, 65280]], [], [], [], [], [[15, 255, 34952, 62259], [15, 34952, 61695, 62259], [255, 13107, 34952, 61455], [255, 17476, 30583, 61455]], [[15, 3840, 34952, 62259], [15, 34952, 62259, 65280], [3840, 30583, 61455, 62532], [13107, 34952, 61455, 65280], [17476, 30583, 61455, 65280]], [[15, 240, 20292, 35976], [15, 1264, 20292, 34952], [15, 1520, 17476, 34952], [15, 2032, 17476, 34952], [15, 3904, 17652, 34952], [15, 4080, 19524, 34952], [240, 3840, 17484, 34959], [248, 3840, 17476, 34959], [2063, 4080, 17476, 34952], [3840, 34959, 35064, 62532]], [[15, 1092, 4593, 34952], [15, 4593, 17476, 35976], [15, 4593, 17476, 51336], [15, 5617, 17476, 34952], [240, 3840, 34968, 62532], [240, 3856, 34952, 62532], [4593, 16399, 17476, 34952], [4593, 34952, 61455, 62532]], [], [[15, 13299, 17476, 63624]], [], [], [[15, 3840, 34959, 62259]], [[15, 128, 34952, 64443], [15, 2039, 17476, 34952], [15, 17476, 30711, 63624], [143, 34952, 48059, 61440]], [[240, 3840, 13107, 48048], [3840, 30471, 34952, 62532], [4369, 7953, 34959, 61986], [7953, 8738, 34959, 61713], [7953, 13107, 34959, 61440], [8738, 34959, 61713, 65297]], [], [], [], [], [], [[15, 3855, 34952, 62259], [15, 34952, 62259, 65295], [3855, 13107, 34952, 61455], [3855, 17476, 30583, 61455]], [[15, 2047, 17476, 34952], [15, 4095, 19524, 34952], [255, 3855, 17476, 34952], [255, 3855, 34952, 62532], [7953, 8946, 17487, 34952], [34952, 61695, 62532, 65295]], [[15, 7953, 34952, 62259], [15, 17476, 34816, 63624], [15, 17476, 34952, 63488], [15, 17476, 34952, 64000], [15, 19524, 34952, 61440], [15, 19524, 34952, 63488], [15, 34952, 52292, 61440], [15, 34952, 61440, 64580], [15, 34952, 62259, 65297], [15, 34952, 62532, 63488], [15, 34952, 63488, 64580], [192, 3840, 17487, 52428], [2048, 34952, 61455, 62532], [2063, 17476, 34952, 63488], [2063, 19524, 34952, 61440], [3840, 34952, 62532, 65295], [3855, 17476, 34952, 65280], [3855, 34952, 62532, 65280], [17476, 34952, 61455, 63488], [17476, 34952, 63488, 63503], [19524, 34952, 61440, 61455]], [[240, 3840, 34984, 62532], [240, 3872, 34952, 62532]], [], [], [], [], [], [], [[15, 17476, 34824, 63624], [15, 17476, 34952, 63496], [15, 19532, 34952, 61440], [15, 34952, 52300, 61440]], [[3840, 8738, 34959, 62259], [3840, 13107, 34959, 61986], [3840, 34959, 61986, 62259], [4369, 12066, 34959, 61986], [4369, 34959, 61986, 65314], [8738, 12066, 34959, 61713], [12066, 13107, 34959, 61440]], [], [[3840, 35064, 43690, 62532]], [], [], [], [[15, 17476, 34952, 63503], [15, 19524, 34952, 61455], [2063, 17476, 34952, 61455]], [], [[15, 12066, 34952, 62259], [15, 34952, 62259, 65314]], [], [], [], [], [], [], [], [], [[13107, 16179, 34959, 61440]], [], [], [], [], [[240, 16179, 17487, 34952]], [], [[240, 3840, 35016, 62532], [240, 3904, 34952, 62532]], [[15, 16179, 34952, 62259], [15, 17476, 34952, 64034], [15, 19524, 34952, 61986], [15, 34952, 62259, 65331]], [], [[255, 17476, 52428, 61680]], [[17476, 52428, 61680, 65280]], [], [[15, 176, 34952, 64443]], [], [], [], [[3840, 17476, 34959, 62259], [12066, 17476, 34959, 61713]], [], [[3840, 35064, 52428, 62532], [3840, 35064, 62532, 64716]], [], [[240, 17487, 52428, 61695]], [[240, 3840, 17487, 52428]], [], [[3840, 8946, 17487, 52428]], [[15, 20292, 34952, 62259]], [], [], [], [], [], [], [], [], [], [], [], [], [], [[240, 7953, 17487, 52428]], [[3840, 4593, 17487, 56797]], [[255, 3855, 17476, 52428]], [[15, 17476, 52428, 63488], [15, 19524, 52428, 61440], [3855, 17476, 52428, 65280]], [], [], [[240, 3003, 3840, 30583]], [[15, 192, 36744, 52428], [240, 3003, 4080, 34952], [240, 34952, 64443, 65520], [4080, 34952, 48059, 61680]], [], [], [], [[3840, 13299, 17476, 65520]], [], [], [[3840, 17487, 52428, 65295], [3840, 35064, 61166, 62532]], [[112, 3840, 30583, 62532], [240, 35064, 61695, 62532], [255, 17476, 35064, 61680], [3952, 17476, 30583, 61440]], [[240, 3840, 35064, 62532], [3840, 35064, 61680, 62532], [17476, 35064, 61680, 65280]], [[240, 12066, 17487, 52428]], [[3840, 8946, 35064, 62532]], [[3840, 8946, 17487, 61166]], [[15, 20292, 52428, 61713], [3840, 17652, 35064, 62532], [3840, 35064, 62532, 62708]], [], [[255, 4080, 34952, 48059]], [[255, 17476, 35064, 63736], [3003, 3840, 4080, 34952], [3840, 4593, 13299, 17487], [4080, 34952, 48059, 65280]], [[240, 36744, 52428, 65520], [3840, 35064, 62532, 63736], [17476, 35064, 63736, 65280]], [], [[15, 13299, 17476, 61680], [3840, 35064, 43770, 62532]], [], [[15, 13299, 17476, 62194], [3840, 35064, 52476, 62532], [3840, 35064, 62532, 64764]], [], [[255, 17476, 35064, 61695]], [[240, 3840, 17487, 52476], [240, 3840, 30471, 62532], [255, 3840, 17476, 35064], [255, 3840, 35064, 62532], [3840, 17476, 17663, 35064], [3840, 17487, 17652, 35064], [3840, 35064, 35071, 62532], [3840, 35064, 61695, 62532], [17476, 35064, 61695, 65280]], [[128, 4080, 34952, 62532], [240, 3840, 34952, 62660], [240, 3968, 34952, 62532], [256, 3840, 35064, 62532], [3840, 17476, 35064, 61696], [3840, 17476, 35064, 65280], [3840, 30576, 52428, 61440], [3840, 35064, 62532, 65280], [4080, 17476, 34952, 61568], [4080, 17604, 34952, 61440], [17604, 34952, 61440, 65520]], [], [], [], [], [], [[15, 240, 34952, 64443], [15, 240, 35976, 48059], [15, 240, 48059, 51336], [15, 1264, 34952, 48059], [240, 3003, 34952, 61455], [240, 16399, 34952, 48059], [3840, 13299, 17487], [3840, 13299, 17487, 61440], [3855, 4080, 34952, 48059], [34952, 48059, 61455, 61680]], [[255, 34952, 52428, 61680], [3840, 30471, 35064, 62532]], [[15, 8946, 34952, 64443], [34952, 52428, 61680, 65280]], [[15, 13299, 17476, 61695]], [[15, 3840, 13299, 17476], [15, 17652, 34952, 64443]], [], [], [], [[255, 3840, 17476, 30471], [255, 3855, 17476, 35064], [3840, 34952, 34959, 62259]], [[15, 4080, 17604, 34952], [15, 17476, 35064, 63488], [15, 19524, 35064, 61440], [143, 4080, 17476, 34952], [3840, 3855, 35064, 62532], [3840, 17476, 30471, 65280], [3840, 35064, 62532, 65295], [3855, 17476, 35064, 65280]], [[255, 7953, 17476, 35064], [255, 17476, 35064, 61713], [4369, 35064, 61695, 62532]], [[3840, 4369, 35064, 62532], [3840, 7953, 35064, 62532], [3840, 35064, 61713, 62532], [7953, 17476, 35064, 65280], [17476, 35064, 61713, 65280]], [], [], [], [[15, 255, 34952, 64443], [15, 3840, 13299, 17487], [255, 34952, 48059, 61455], [4369, 8946, 17487, 61695]], [[15, 34952, 48059, 64256], [15, 34952, 64443, 65280], [3003, 3840, 34952, 61455], [3840, 4369, 8946, 17487], [34952, 48059, 61455, 65280]], [[15, 240, 36744, 52428], [15, 240, 36744, 64716]], [], [[15, 3855, 13299, 17476], [15, 8946, 36744, 52428]], [], [[15, 7953, 13299, 17476], [15, 13299, 17476, 61713]], [], [], [[15, 240, 36751, 52428], [15, 4095, 17604, 34952], [143, 4095, 17476, 34952], [255, 3840, 34959, 52428], [255, 17476, 34952, 36751], [255, 17476, 34959, 36744]], [[15, 128, 1092, 34952], [15, 128, 16384, 52428], [15, 128, 17476, 51336], [15, 16384, 17604, 34952], [15, 16512, 17476, 34952], [15, 17476, 30711, 61713], [15, 17604, 34952, 61440], [15, 32896, 52428, 61440], [15, 34952, 50372, 61440], [15, 34952, 61440, 62660], [15, 34952, 61568, 62532], [128, 16399, 17476, 34952], [128, 34952, 61455, 62532], [136, 17476, 34959, 61440], [143, 16384, 17476, 34952], [143, 17476, 34952, 61440], [143, 34952, 61440, 62532], [2048, 34959, 52428, 61440], [3072, 34959, 52428, 61440], [3840, 4383, 35064, 62532], [3840, 34952, 62532, 65423], [3840, 34959, 52428, 65280], [3840, 36751, 52428, 61440], [17476, 32904, 34959, 61440], [17476, 32911, 34952, 61440], [17476, 34952, 34959, 63488], [17476, 34952, 36751, 65280], [17476, 34952, 61440, 61583], [17476, 34952, 61455, 61568], [17476, 34959, 36744, 65280], [17604, 34952, 61440, 61455], [19524, 34952, 34959, 61440]], [[3840, 4369, 30471, 62532]], [[255, 12066, 17476, 35064]], [[3840, 12066, 35064, 62532], [12066, 17476, 35064, 65280]], [[15, 3840, 17476, 52236]], [], [[15, 34952, 64443, 65295], [3855, 34952, 48059, 61455], [4593, 8738, 17487, 61695]], [[15, 255, 36744, 52428], [255, 3855, 34952, 52428], [3840, 4593, 8738, 17487]], [[15, 17612, 34952, 61440], [15, 32904, 52428, 61440], [15, 34952, 50380, 61440], [15, 34952, 52428, 63488], [15, 36744, 52428, 65280], [3855, 34952, 52428, 65280], [4369, 7953, 8946, 17487]], [[15, 240, 40857, 52428], [3840, 8738, 13299, 17487]], [], [[255, 13107, 17476, 61680]], [[15, 8946, 21845, 61713], [13107, 17476, 61680, 65280]], [[15, 12066, 13299, 17476]], [], [[15, 17604, 34952, 61455], [143, 17476, 34952, 61455]], [], [[15, 17476, 34824, 61713], [240, 17476, 34952, 49072], [3840, 34959, 52428, 61713]], [[3840, 4369, 17487, 56589]], [], [[3840, 13107, 35064, 62532]], [], [[240, 13107, 17487, 61695]], [[15, 36744, 52428, 65295], [240, 3840, 13107, 17487]], [[4593, 7953, 8738, 17487]], [[3840, 8946, 13107, 17487], [4369, 8946, 12066, 17487]], [[15, 240, 44970, 52428]], [], [], [], [[15, 13299, 16179, 17476], [15, 13299, 17476, 62259]], [], [], [], [[15, 17604, 34952, 61986], [143, 17476, 34952, 61986]], [], [[3840, 8738, 17487, 60942]], [[3840, 17476, 35064, 65348], [3840, 20292, 35064, 62532], [3840, 35064, 62532, 65348]], [], [[240, 17487, 34952, 49083]], [[240, 7953, 13107, 17487]], [[4593, 8738, 12066, 17487]], [[255, 3855, 13107, 17476]], [[15, 240, 49083, 52428], [15, 13107, 17476, 63488], [15, 13107, 19524, 61440], [3840, 13299, 17476, 17487], [3855, 13107, 17476, 65280]], [], [], [], [], [], [], [], [], [], [], [[3840, 13107, 17487, 65295], [3840, 21845, 35064, 62532], [3840, 35064, 62532, 62805]], [], [], [[240, 12066, 13107, 17487]], [], [[15, 45243, 52428, 61440]], [[15, 13107, 20292, 61713]], [], [], [], [[240, 13107, 36744, 65520]], [], [], [], [[143, 17476, 52428, 61440]], [], [], [], [[3840, 4369, 30576, 61986], [3840, 8738, 30576, 61713], [3840, 13107, 30576, 61440]], [], [[240, 13107, 16179, 17487]], [], [], [], [[15, 240, 30583, 62259]], [[240, 255, 34952, 62259], [240, 30583, 61695, 62532], [255, 13107, 34952, 61680], [255, 17476, 30583, 61680]], [[240, 3840, 30583, 62532], [240, 34952, 62259, 65280], [3840, 34952, 61680, 62259], [13107, 34952, 61680, 65280], [17476, 30583, 61680, 65280]], [[240, 1092, 34952, 65520], [240, 4080, 34952, 62532], [240, 17476, 34952, 49136], [240, 17476, 35976, 65520], [240, 17476, 51336, 65520], [1264, 17476, 34952, 65520], [4080, 17476, 34952, 61680], [4080, 34952, 61680, 62532]], [], [[4080, 8946, 34952, 62532]], [], [[4080, 17476, 34952, 62708], [4080, 17652, 34952, 62532], [4080, 34952, 62532, 62708]], [], [[15, 240, 35064, 64443], [240, 3840, 34959, 62259], [255, 35064, 48059, 61440], [3840, 4095, 35064, 48059], [35064, 48059, 61440, 61695]], [[3003, 3840, 35064], [3003, 3840, 35064, 61440], [3840, 30583, 35064, 62532], [3840, 35064, 45056, 48059], [3840, 35064, 48059, 61440], [3840, 35064, 61440, 64443], [35064, 48059, 61440, 65280]], [], [], [], [], [], [[15, 3840, 30583, 62259], [15, 13107, 20292, 62259]], [[15, 240, 13107, 36744], [15, 2032, 17476, 30583]], [[15, 4593, 8738, 40857], [15, 4593, 34952, 62259], [15, 4593, 39321, 61986], [15, 34952, 61937, 62259], [255, 4080, 17476, 34952], [255, 4080, 34952, 62532], [3840, 13119, 17652, 34952, 61440], [4080, 17476, 17663, 34952], [4080, 17487, 17652, 34952], [4080, 34952, 61695, 62532]], [[15, 4369, 8946, 44970], [15, 8946, 13107, 36744], [496, 3840, 34952, 62532], [3840, 4080, 34952, 62532], [3840, 4369, 8751, 17652, 63624], [4080, 17476, 34952, 65280], [4080, 34952, 62532, 65280]], [[15, 13299, 16179, 34952], [15, 13299, 34952, 62259], [15, 13299, 48059, 61440], [15, 34952, 62259, 62451], [3840, 4383, 8738, 17652, 63624]], [[15, 3840, 13107, 17652, 63624]], [], [], [[15, 240, 13107, 36751], [15, 30711, 48059, 61440], [255, 3840, 13107, 34959], [255, 4369, 8738, 36751]], [[15, 128, 4369, 25122], [15, 128, 8738, 20753], [15, 128, 13107, 16384], [15, 3003, 3840, 35064], [15, 4369, 8738, 16512], [15, 4369, 8866, 16384], [15, 4369, 32896, 61986], [15, 4497, 8738, 16384], [15, 8738, 32896, 61713], [15, 13107, 32896, 61440], [128, 4369, 8738, 16399], [143, 4369, 8738, 16384], [2048, 4369, 34959, 61986], [2048, 8738, 34959, 61713], [2048, 13107, 34959, 61440], [3840, 4369, 36751, 61986], [3840, 8738, 36751, 61713], [3840, 13107, 34959, 65280], [3840, 13107, 36751, 61440], [3840, 30471, 48059, 61440], [4369, 8738, 32911, 61440], [4369, 8738, 34959, 63488], [4369, 8738, 36751, 65280], [4369, 10786, 34959, 61440], [6417, 8738, 34959, 61440]], [[255, 17476, 34952, 36856], [255, 17476, 35064, 36744]], [[3840, 34952, 36856, 62532], [3840, 35064, 36744, 62532], [17476, 34952, 36856, 65280], [17476, 35064, 36744, 65280]], [], [], [], [], [[15, 255, 13107, 36744], [255, 3855, 13107, 34952], [255, 3855, 17476, 30583]], [[15, 2048, 34952, 62259], [15, 3840, 36744, 62259], [15, 4369, 32904, 61986], [15, 4369, 34952, 64034], [15, 6417, 34952, 61986], [15, 8738, 32904, 61713], [15, 8738, 34952, 63761], [15, 10786, 34952, 61713], [15, 13107, 32904, 61440], [15, 13107, 34952, 63488], [15, 13107, 36744, 65280], [15, 15155, 34952, 61440], [15, 17476, 30583, 63488], [15, 19524, 30583, 61440], [3840, 3855, 34952, 62259], [3840, 13299, 17487, 34952], [3840, 30583, 62532, 65295], [3855, 13107, 34952, 65280], [3855, 17476, 30583, 65280]], [[15, 240, 1092, 34952], [15, 240, 13107, 40857], [15, 240, 17476, 35976], [15, 240, 17476, 51336], [15, 240, 35976, 62532], [15, 1088, 17652, 34952], [15, 1264, 17476, 34952], [15, 1264, 17476, 35976], [15, 1264, 34952, 62532], [15, 1776, 17476, 34952], [15, 16624, 17476, 51336], [240, 1039, 17476, 35976], [240, 16388, 17487, 34952], [240, 16399, 17476, 34952], [240, 16399, 17476, 51336], [240, 17484, 34959, 61440], [240, 17487, 34952, 61444], [240, 17487, 34956, 61440], [240, 34952, 61455, 62532], [248, 17476, 34959, 61440], [1039, 1264, 17476, 34952], [3855, 4080, 17476, 34952], [3855, 4080, 34952, 62532], [4080, 34952, 62532, 65295], [16399, 16624, 17476, 34952], [17476, 34952, 61455, 61680], [34952, 61455, 61680, 62532]], [], [[15, 1092, 8946, 34952], [15, 4369, 8946, 49083], [15, 8946, 17476, 35976], [15, 8946, 17476, 51336], [15, 9970, 17476, 34952], [4080, 7953, 34952, 62532], [8946, 16399, 17476, 34952], [8946, 34952, 61455, 62532]], [[15, 13299, 17476, 36744]], [[15, 240, 17476, 35980], [15, 240, 17476, 51340], [15, 1092, 1268, 34952], [15, 1092, 17652, 34952], [15, 1268, 17476, 34952], [15, 17476, 17652, 51336], [16399, 17476, 17652, 34952], [17476, 34952, 61455, 62708], [17652, 34952, 61455, 62532], [34952, 61455, 62532, 62708]], [], [], [[15, 34824, 48059, 61440], [15, 34952, 47931, 61440]], [[240, 4369, 8738, 49072], [3840, 4369, 34959, 62259], [3840, 13107, 34959, 61713], [3840, 34959, 61713, 62259]], [], [[3003, 3840, 8738, 35064], [3840, 35064, 39321, 62532]], [], [], [], [[15, 13107, 36744, 65295]], [[15, 255, 1092, 34952], [15, 255, 17476, 35976], [15, 255, 17476, 51336], [15, 1279, 17476, 34952], [255, 1039, 17476, 34952], [255, 16399, 17476, 34952], [255, 17476, 34952, 61455], [255, 34952, 61455, 62532], [16399, 16639, 17476, 34952], [17476, 17663, 34952, 61455], [17487, 17652, 34952, 61455], [34952, 61455, 61695, 62532]], [[15, 1092, 34952, 65280], [15, 17476, 34952, 63744], [15, 17476, 34952, 64256], [15, 17476, 35976, 65280], [15, 17476, 36608, 63624], [15, 17476, 36744, 63488], [15, 17476, 51336, 65280], [15, 17604, 34952, 61568], [15, 19524, 36744, 61440], [143, 17476, 34952, 61568], [143, 17604, 34952, 61440], [1039, 17476, 34952, 65280], [3840, 17487, 34952, 61444], [3840, 17487, 34956, 61440], [3840, 34952, 61455, 62532], [16399, 17476, 34952, 65280], [17476, 34952, 61455, 65280], [34952, 61455, 62532, 65280]], [[15, 240, 13107, 44970]], [[15, 4593, 8738, 49083]], [[4080, 12066, 34952, 62532]], [], [], [], [], [[15, 17604, 34952, 63624], [143, 17476, 34952, 63624], [143, 34952, 52428, 61440]], [], [], [[15, 17476, 34952, 64267]], [], [], [], [[15, 1092, 34952, 65295], [15, 17476, 34952, 64271], [15, 17476, 35976, 65295], [15, 17476, 51336, 65295], [143, 17476, 34952, 61583], [3855, 17476, 34952, 61455], [3855, 34952, 61455, 62532], [4593, 12066, 17487, 34952], [16399, 17476, 34952, 65295], [34952, 61455, 62532, 65295]], [], [[15, 17476, 34952, 63761], [15, 19524, 34952, 61713], [7953, 34952, 61455, 62532]], [[15, 240, 13107, 49083]], [], [], [[4080, 17476, 52428, 61680]], [], [], [], [], [[3840, 13107, 34959, 62259]], [], [[3003, 3840, 17476, 35064], [3003, 3840, 35064, 62532], [3840, 35064, 48059, 62532]], [], [], [], [[240, 3840, 13119, 17476, 63624], [240, 4080, 17487, 52428], [240, 13119, 17476, 36744, 61440], [240, 13119, 20292, 34952, 61440]], [], [[15, 13107, 45243, 61440], [12066, 34952, 61455, 62532]], [], [[255, 4080, 17476, 52428]]]
  | 5 => [[[240, 3840, 17476, 34952, 65348], [240, 3840, 17476, 52428, 65280], [240, 3840, 20292, 34952, 62532], [240, 3840, 20292, 52428, 61440], [240, 3840, 34952, 62532, 65348], [3840, 4080, 17476, 34952, 62532], [3840, 4080, 17476, 52428, 61440], [3840, 17476, 52428, 61440, 65520], [4080, 17476, 20292, 34952, 61440], [17476, 20292, 34952, 61440, 65520]], [], [], [], [], [], [[15, 128, 13107, 17476, 61440], [15, 4369, 8866, 17476, 61440], [15, 4497, 8738, 17476, 61440], [143, 4369, 8738, 17476, 61440], [7953, 8738, 17476, 34959, 61440]], [], [], [], [[15, 3840, 17476, 34952, 61999], [15, 12079, 17476, 34952, 61440], [15, 17476, 34952, 61440, 65327]], [[15, 240, 1088, 17476, 34952], [15, 240, 16448, 17476, 34952], [15, 240, 17476, 34952, 61504], [15, 240, 17476, 35016, 61440], [79, 240, 17476, 34952, 61440], [240, 1024, 17476, 17487, 34952], [240, 3840, 17476, 20303, 34952], [240, 3840, 17487, 20292, 34952], [3840, 4080, 17476, 17487, 34952]], [[15, 3855, 17476, 34952, 61986], [15, 12066, 17476, 34952, 61455], [15, 17476, 34952, 61986, 65295], [3840, 4593, 17476, 17487, 34952], [3855, 8738, 17476, 34952, 61455]], [], [[15, 240, 4095, 17476, 52428], [15, 7953, 17476, 34952, 61986], [15, 16179, 17476, 34952, 61440]], [[15, 240, 1024, 17476, 52428], [15, 240, 1092, 17476, 34952], [15, 240, 3072, 17476, 52428], [15, 240, 3840, 20292, 52428], [15, 240, 16384, 17476, 52428], [15, 240, 16452, 17476, 34952], [15, 240, 17476, 49152, 52428], [15, 240, 17476, 52428, 61440], [15, 240, 26214, 34952, 61986], [15, 240, 26214, 43690, 61440], [15, 240, 34952, 61986, 63078], [15, 3840, 4080, 17476, 52428], [15, 4080, 17476, 20292, 34952], [15, 17476, 52428, 61440, 61680], [240, 3840, 3855, 17476, 52428], [240, 17476, 34952, 61455, 62532], [240, 17476, 52428, 61440, 61455]], [[15, 3840, 4593, 17476, 52428]], [[15, 8946, 17476, 52428, 61440], [240, 3840, 21845, 34952, 62532], [240, 3840, 21845, 52428, 61440], [240, 3840, 34952, 62532, 62805]], [], [[15, 17476, 17652, 52428, 61440]], [], [], [], [], [], [[3840, 17476, 35064, 56797, 61440]], [[15, 240, 17487, 52428, 61440], [240, 17476, 17487, 34952, 61455]], [[15, 64, 3840, 34952, 62532], [15, 3840, 17476, 35016, 61440], [15, 3904, 17476, 34952, 61440]], [[240, 3840, 4369, 17487, 52428], [240, 3840, 17476, 35064, 61680], [240, 4080, 17476, 35064, 61440], [240, 17476, 35064, 61440, 65520]], [], [[15, 240, 17476, 52428, 61455], [15, 255, 17476, 52428, 61440], [15, 3840, 4095, 17476, 52428], [15, 4095, 17476, 20292, 34952], [15, 17476, 52428, 61440, 61695]], [[15, 3840, 17476, 49152, 52428], [15, 3840, 17476, 52428, 61440], [15, 3840, 26214, 34952, 61986], [15, 3840, 26214, 43690, 61440], [15, 3840, 34952, 61986, 63078], [15, 12066, 17476, 34952, 61986], [15, 17476, 20292, 34952, 61440], [15, 17476, 34952, 61440, 65348], [15, 17476, 34952, 61986, 65314], [15, 17476, 52428, 61440, 65280], [15, 20292, 34952, 61440, 62532], [15, 20292, 52428, 61440], [15, 34952, 61440, 62532, 65348], [3840, 17476, 34952, 61455, 62532], [3840, 17476, 52428, 61440, 61455], [17476, 20292, 34952, 61440, 61455]], [[15, 240, 3840, 21845, 52428]], [[15, 4593, 17476, 56797, 61440]], [], [[15, 192, 34952, 52428, 61440], [240, 3840, 34952, 48059, 65520]], [], [], [], [[240, 3840, 13299, 17476, 61440], [3840, 4593, 8946, 17476, 61440]], [], [], [[15, 3840, 17487, 52428, 61440], [15, 17476, 20303, 34952, 61440], [15, 17476, 34952, 61440, 65359], [15, 17487, 20292, 34952, 61440], [3840, 17476, 17487, 34952, 61455]], [[15, 240, 4080, 17476, 35064], [240, 255, 3840, 17476, 35064], [240, 3840, 17476, 30711, 61440]], [[240, 3840, 17476, 35064, 65280], [3840, 4080, 17476, 35064, 61440], [3840, 17476, 35064, 61440, 65520]], [[3840, 4593, 17476, 35064, 61440]], [[15, 3840, 17476, 52428, 61455], [15, 3855, 17476, 52428, 61440], [15, 17476, 20292, 34952, 61455], [15, 17476, 52428, 61440, 65295]], [], [[15, 7953, 17476, 52428, 61440], [15, 17476, 24405, 34952, 61440]], [[15, 240, 17476, 52428, 61986], [15, 240, 26214, 52428, 61440], [15, 240, 30583, 48059, 61440]], [[15, 240, 34952, 48059, 61680], [240, 255, 34952, 48059, 61440], [240, 3840, 4095, 34952, 48059], [240, 34952, 48059, 61440, 61695]], [[15, 240, 17476, 35064, 36856], [15, 8946, 17476, 61166, 61440], [240, 3003, 3840, 34952], [240, 3003, 3840, 34952, 61440], [240, 3840, 30583, 34952, 62532], [240, 3840, 30583, 52428, 61440], [240, 3840, 34952, 45056, 48059], [240, 3840, 34952, 48059, 61440], [240, 3840, 34952, 61440, 64443], [240, 3840, 39321, 43690, 61440], [240, 34952, 48059, 61440, 65280], [3840, 34952, 48059, 61440, 61680]], [[240, 3840, 34952, 52428, 61680], [240, 4080, 34952, 52428, 61440], [240, 17476, 34952, 63624, 65520], [240, 34952, 52428, 61440, 65520], [3840, 17476, 35064, 36856, 61440]], [[3840, 17476, 35064, 39417, 61440]], [[15, 240, 3840, 13299, 17476], [15, 3840, 4593, 8946, 17476]], [[15, 4593, 13299, 17476, 61440], [3840, 4369, 8946, 17476, 61680], [4080, 4369, 8946, 17476, 61440], [4369, 8946, 17476, 61440, 65520]], [[15, 3840, 8946, 13299, 17476]], [], [[15, 240, 3840, 17476, 30711], [15, 240, 4095, 17476, 35064]], [[15, 240, 1024, 17476, 35064], [15, 240, 16384, 17476, 35064], [15, 240, 17476, 35064, 61440], [15, 240, 35064, 61440, 62532], [15, 3840, 4080, 17476, 35064], [15, 17476, 35064, 61440, 61680], [240, 3840, 3855, 17476, 35064], [240, 17476, 35064, 61440, 61455], [255, 17476, 35064, 61440], [3840, 4095, 17476, 35064], [3840, 4095, 17476, 35064, 61440], [3840, 34952, 35064, 48059, 61440], [17476, 35064, 61440, 61695]], [[15, 3840, 4593, 17476, 35064], [112, 3840, 17476, 34952, 61440], [240, 3840, 17476, 34824, 61440], [512, 3840, 17476, 35064, 61440], [1024, 3840, 17476, 35064, 61440], [2048, 3840, 17476, 35064, 61440], [3840, 4096, 17476, 35064, 61440], [3840, 8192, 17476, 35064, 61440], [3840, 16384, 17476, 35064, 61440], [3840, 17476, 32768, 35064, 61440], [3840, 17476, 35064, 61440], [3840, 35064, 61440, 62532], [3840, 35064, 62532], [17476, 35064, 61440, 65280]], [[1, 3840, 17476, 35064, 61440], [15, 4593, 17476, 39417, 61440], [15, 8946, 17476, 35064, 61440], [240, 3840, 4369, 35064, 62532]], [[2, 3840, 17476, 35064, 61440], [11, 240, 3840, 34952, 48059]], [[15, 240, 17476, 52476, 61440], [15, 8946, 17476, 43770, 61440], [15, 17476, 17652, 35064, 61440]], [[4, 3840, 17476, 35064, 61440]], [[15, 240, 34952, 48059, 61695], [15, 3840, 17476, 52428, 61986], [15, 3840, 26214, 52428, 61440], [15, 3840, 30583, 48059, 61440], [15, 4369, 20292, 56797, 61440], [15, 8738, 20292, 52428, 61440], [15, 12066, 17476, 52428, 61440], [15, 17476, 20292, 34952, 61986], [15, 17476, 28518, 34952, 61440]], [[15, 240, 3003, 3840, 34952], [15, 240, 3840, 30583, 52428], [15, 240, 3840, 34952, 48059], [15, 240, 3840, 34952, 64443], [15, 240, 3840, 39321, 43690], [15, 240, 13107, 34952, 36744], [15, 240, 17476, 28791, 34952], [15, 240, 17476, 30583, 36744], [240, 3840, 4369, 8946, 17487]], [[15, 240, 4080, 34952, 52428], [15, 4593, 34952, 48059, 61440], [15, 17476, 17652, 52476, 61440], [240, 255, 3840, 34952, 52428], [240, 255, 17476, 34952, 36744]], [[8, 3840, 17476, 35064, 61440], [15, 3840, 8946, 34952, 48059], [240, 3840, 34952, 36744, 62532], [240, 3840, 34952, 52428, 65280], [240, 3840, 36744, 52428, 61440], [240, 17476, 34952, 36744, 65280], [3840, 4080, 34952, 52428, 61440], [3840, 34952, 52428, 61440, 65520]], [], [[15, 4080, 4369, 8946, 17476], [15, 13299, 17476, 61440]], [[3840, 4593, 8738, 17476, 61680], [4080, 4593, 8738, 17476, 61440], [4593, 8738, 17476, 61440, 65520]], [[15, 4369, 8946, 12274, 17476]], [], [[15, 128, 4369, 34952, 61986], [15, 128, 8738, 34952, 61713], [15, 128, 13107, 34952, 61440], [15, 128, 17476, 30583, 61440], [15, 240, 17476, 30471, 61440], [15, 240, 17476, 35064, 61455], [15, 255, 17476, 35064, 61440], [15, 3840, 4095, 17476, 35064], [15, 4369, 8866, 34952, 61440], [15, 4497, 8738, 34952, 61440], [15, 17476, 30711, 61440], [15, 17476, 35064, 61440, 61695], [143, 4369, 8738, 34952, 61440]], [[15, 240, 3840, 17476, 34824], [15, 240, 17476, 34952, 61568], [15, 240, 17604, 34952, 61440], [15, 3840, 17476, 32768, 35064], [15, 3840, 17476, 35064, 61440], [15, 3840, 35064, 61440, 62532], [15, 3840, 35064, 62532], [15, 17476, 35064, 61440, 65280], [143, 240, 17476, 34952, 61440], [3840, 17476, 30471, 61440], [3840, 17476, 35064, 61440, 61455]], [[16, 3840, 17476, 35064, 61440], [255, 3840, 4369, 17476, 35064]], [[3840, 4369, 17476, 35064, 65280]], [], [[15, 3840, 17476, 52476, 61440]], [], [[15, 240, 3855, 34952, 48059], [15, 255, 3840, 34952, 48059]], [[15, 240, 4095, 34952, 52428], [15, 2048, 34952, 48059, 61440], [15, 3840, 34952, 48059, 65280], [15, 17476, 32631, 34952, 61440], [240, 3840, 4593, 8738, 17487], [3840, 3855, 34952, 48059, 61440], [3840, 34952, 48059, 61440, 65295]], [[15, 240, 1024, 34952, 52428], [15, 240, 3072, 34952, 52428], [15, 240, 3840, 36744, 52428], [15, 240, 4369, 34952, 64443], [15, 240, 7953, 34952, 48059], [15, 240, 16384, 34952, 52428], [15, 240, 17476, 34952, 35976], [15, 240, 17476, 34952, 51336], [15, 240, 17476, 34952, 63624], [15, 240, 34952, 48059, 61713], [15, 240, 34952, 49152, 52428], [15, 240, 34952, 52428, 61440], [15, 240, 34952, 61440, 64716], [15, 240, 34952, 62532, 63624], [15, 3840, 4080, 34952, 52428], [15, 34952, 52428, 61440, 61680], [240, 3840, 3855, 34952, 52428], [240, 34952, 52428, 61440, 61455]], [[15, 3840, 4593, 34952, 52428], [15, 4593, 17476, 34952, 36744]], [[15, 4095, 4369, 8946, 17476], [15, 8946, 17476, 34952, 63624], [15, 8946, 34952, 52428, 61440], [240, 3003, 3840, 8738, 34952], [240, 3840, 34952, 39321, 62532], [240, 3840, 39321, 52428, 61440]], [[15, 1024, 4369, 8946, 17476], [15, 3840, 4369, 8946, 20292], [15, 4080, 4593, 8738, 17476], [15, 4369, 8946, 16384, 17476], [15, 4369, 8946, 17476, 61440], [3840, 3855, 4369, 8946, 17476], [4369, 8946, 17476, 61440, 61455]], [[15, 3840, 4369, 13299, 17476], [15, 4593, 8177, 8738, 17476], [15, 4593, 8738, 17476, 61937], [15, 17476, 17652, 34952, 63624], [15, 17652, 34952, 52428, 61440], [240, 3840, 13107, 17476, 61680], [240, 4080, 13107, 17476, 61440], [240, 13107, 17476, 61440, 65520], [4080, 4369, 8738, 17476, 61680]], [], [], [[15, 240, 17476, 34952, 63631], [15, 240, 17476, 34959, 63624], [15, 240, 34959, 52428, 61440], [15, 3840, 17476, 30471, 61440], [15, 3840, 17476, 35064, 61455], [15, 3855, 17476, 35064, 61440], [15, 4369, 17476, 26358, 61440], [15, 17476, 34952, 61440, 65407], [15, 17476, 35064, 61440, 65295], [255, 17476, 34952, 34959, 61440], [3840, 4095, 17476, 34952, 34959], [17476, 34952, 34959, 61440, 61695]], [[15, 3840, 17604, 34952, 61440], [15, 17476, 34824, 61440], [143, 3840, 17476, 34952, 61440], [3840, 17476, 34824, 61440, 65295], [3840, 17476, 34952, 34959, 61440], [3840, 17476, 34952, 61440, 63631], [3840, 17476, 34959, 61440, 63624], [3840, 34952, 34959, 61440, 62532], [3840, 34959, 52428, 61440], [17476, 34952, 34959, 61440, 65280]], [[32, 3840, 17476, 35064, 61440]], [[15, 240, 17476, 35064, 61986], [255, 8738, 17476, 35064, 61440], [3840, 4095, 8738, 17476, 35064], [8738, 17476, 35064, 61440, 61695]], [[3840, 4369, 21845, 35064, 61440], [3840, 8738, 17476, 35064, 61440], [3840, 8738, 35064, 61440, 62532], [3840, 8738, 35064, 62532], [3840, 17476, 35064, 61440, 61986], [8738, 17476, 35064, 61440, 65280]], [], [], [[15, 3840, 34952, 48059, 65295], [15, 4369, 8946, 17487, 61440]], [[15, 240, 34952, 52428, 61455], [15, 255, 17476, 34952, 63624], [15, 255, 34952, 52428, 61440], [15, 3840, 4095, 34952, 52428], [15, 34952, 52428, 61440, 61695], [240, 4080, 4369, 8738, 17487]], [[15, 3840, 34952, 48059, 61713], [15, 3840, 34952, 49152, 52428], [15, 3840, 34952, 52428, 61440], [15, 3840, 34952, 61440, 64716], [15, 3840, 34952, 62532, 63624], [15, 8738, 20292, 61166, 61440], [15, 17476, 20292, 52428, 61440], [15, 17476, 34952, 63624, 65280], [15, 34952, 52428, 61440, 65280], [3840, 34952, 52428, 61440, 61455]], [[15, 240, 3840, 39321, 52428], [15, 240, 4369, 36744, 52428], [15, 240, 12066, 34952, 48059]], [[15, 4095, 4593, 8738, 17476], [15, 4369, 8946, 17476, 61455]], [[15, 240, 4080, 13107, 17476], [15, 1024, 4593, 8738, 17476], [15, 3840, 4593, 8738, 20292], [15, 4593, 8738, 16384, 17476], [15, 4593, 8738, 17476, 61440], [240, 255, 3840, 13107, 17476], [255, 4080, 4369, 8738, 17476], [3840, 3855, 4593, 8738, 17476], [4593, 8738, 17476, 61440, 61455]], [[15, 3840, 4369, 8946, 21845], [240, 3840, 13107, 17476, 65280], [240, 3840, 13107, 20292, 61440], [3840, 4080, 13107, 17476, 61440], [3840, 13107, 17476, 61440, 65520], [4080, 4369, 8738, 17476, 65280], [4080, 4369, 8738, 20292, 61440], [4369, 8738, 20292, 61440, 65520]], [[15, 8738, 13299, 17476, 61440]], [], [[15, 3840, 17476, 34824, 65295], [15, 3840, 34959, 52428, 61440], [15, 8738, 17476, 22005, 61440]], [[3840, 8751, 17476, 35064, 61440]], [[15, 128, 17476, 34952, 61713], [15, 4369, 17604, 34952, 61440], [15, 4497, 17476, 34952, 61440], [15, 8738, 17476, 30711, 61440], [143, 4369, 17476, 34952, 61440], [240, 3840, 17476, 34952, 48048], [7953, 17476, 34952, 34959, 61440]], [[15, 3840, 8738, 35064, 62532], [3840, 8738, 17476, 30471, 61440]], [], [], [], [[15, 4369, 17476, 56589, 61440], [15, 4593, 8738, 17487, 61440]], [[15, 240, 4369, 8738, 16448], [15, 3840, 34952, 52428, 61455], [15, 3855, 34952, 52428, 61440], [15, 17476, 34952, 63624, 65295], [15, 34952, 52428, 61440, 65295], [240, 1024, 4369, 8738, 17487], [240, 3840, 4369, 8738, 20303], [3840, 4080, 4369, 8738, 17487]], [[3840, 4369, 4593, 8738, 17487]], [[15, 7953, 34952, 52428, 61440]], [[15, 240, 3549, 4369, 34952], [15, 240, 4095, 13107, 17476], [15, 240, 17476, 34952, 64170], [15, 240, 34952, 52428, 61986], [15, 240, 34952, 56797, 61713], [15, 240, 43690, 52428, 61440], [15, 4593, 8738, 17476, 61455]], [[15, 240, 1024, 13107, 17476], [15, 240, 3840, 13107, 20292], [15, 240, 4369, 8738, 16452], [15, 240, 4369, 9762, 17476], [15, 240, 4369, 17476, 25122], [15, 240, 5393, 8738, 17476], [15, 240, 8738, 17476, 20753], [15, 240, 13107, 16384, 17476], [15, 240, 13107, 17476, 61440], [15, 1264, 4369, 8738, 17476], [15, 3840, 4080, 13107, 17476], [15, 4080, 4369, 8738, 20292], [15, 13107, 17476, 61440, 61680], [240, 3840, 3855, 13107, 17476], [240, 4369, 8738, 16399, 17476], [240, 13107, 17476, 61440, 61455], [3855, 4080, 4369, 8738, 17476], [4369, 8738, 17476, 61455, 61680]], [[15, 3840, 4593, 13107, 17476], [240, 3003, 3840, 17476, 34952], [240, 3003, 3840, 34952, 62532], [240, 3840, 34952, 48059, 62532], [240, 3840, 48059, 52428, 61440]], [[15, 4369, 8946, 17476, 61986], [15, 8946, 13107, 17476, 61440], [240, 3840, 13107, 21845, 61440]], [[15, 3840, 13107, 13299, 17476]], [[15, 13107, 17476, 17652, 61440]], [], [[64, 3840, 17476, 35064, 61440]], [[15, 8738, 17476, 34824, 61440], [3840, 4369, 34959, 56797, 61440], [3840, 8738, 34959, 52428, 61440], [3840, 17476, 34952, 34959, 61986], [12066, 17476, 34952, 34959, 61440]], [], [], [[3840, 8738, 26214, 35064, 61440], [3840, 17476, 35064, 61440, 62532], [3840, 17476, 35064, 62532]], [[15, 240, 13107, 17487, 61440], [240, 4369, 8738, 17487, 61455]], [[240, 3840, 17487, 34952, 48059]], [[15, 8738, 17476, 60942, 61440], [240, 3840, 4369, 13107, 17487]], [], [[15, 240, 13107, 17476, 61455], [15, 255, 13107, 17476, 61440], [15, 3549, 3840, 4369, 34952], [15, 3840, 4095, 13107, 17476], [15, 3840, 34952, 52428, 61986], [15, 3840, 34952, 56797, 61713], [15, 3840, 43690, 52428, 61440], [15, 4095, 4369, 8738, 20292], [15, 12066, 34952, 52428, 61440], [15, 13107, 17476, 61440, 61695], [255, 4369, 8738, 17476, 61455]], [[15, 240, 3840, 48059, 52428], [15, 3840, 13107, 17476, 61440], [15, 4369, 8738, 20292, 61440], [15, 13107, 17476, 61440, 65280], [15, 13107, 20292, 61440], [3840, 13107, 17476, 61440, 61455], [4369, 8738, 17476, 61455, 65280], [4369, 8738, 20292, 61440, 61455]], [[15, 240, 3840, 13107, 21845]], [[15, 4593, 8738, 17476, 61986], [15, 4593, 8738, 26214, 61440]], [], [], [[3840, 17476, 17487, 35064, 61440]], [], [], [], [[15, 3840, 17476, 35064, 62532], [15, 17476, 20292, 35064, 61440]], [], [[15, 3840, 13107, 17487, 61440], [15, 4369, 8738, 20303, 61440], [3840, 4369, 8738, 17487, 61455]], [], [], [], [[15, 3840, 13107, 17476, 61455], [15, 3855, 13107, 17476, 61440], [15, 4369, 8738, 20292, 61455], [15, 13107, 17476, 61440, 65295], [3855, 4369, 8738, 17476, 61455]], [], [[15, 240, 3822, 8738, 34952], [15, 240, 17476, 52428, 63624], [15, 240, 34952, 61166, 61986], [15, 4369, 8738, 24405, 61440], [15, 7953, 8738, 17476, 61713], [15, 7953, 13107, 17476, 61440]], [[15, 240, 4369, 26214, 61986], [15, 240, 13107, 17476, 61986], [15, 240, 13107, 26214, 61440]], [[240, 3840, 34952, 56797, 62532]], [[15, 8946, 17476, 21845, 61440], [240, 3840, 13107, 30583, 61440]], [[15, 192, 3840, 17476, 34952], [240, 3840, 13107, 34952, 61680], [240, 3840, 17476, 30583, 61680], [240, 4080, 13107, 34952, 61440], [240, 4080, 17476, 30583, 61440], [240, 4369, 34952, 61986, 65520], [240, 8738, 34952, 61713, 65520], [240, 13107, 34952, 61440, 65520], [240, 17476, 30583, 61440, 65520], [4080, 4369, 8738, 34952, 61680]], [[240, 4080, 17476, 34952, 61680], [240, 17476, 34952, 61680, 65520]], [], [], [[3840, 8738, 34959, 61166, 61440], [3840, 17476, 34959, 52428, 61440], [17476, 20292, 34952, 34959, 61440]], [], [], [[3840, 8738, 17476, 35064, 62532], [3840, 17476, 26214, 35064, 61440]], [[240, 3840, 35064, 48059, 61440]], [], [], [], [[15, 3822, 3840, 8738, 34952], [15, 3840, 34952, 61166, 61986], [15, 20292, 34952, 52428, 61440]], [[15, 240, 17476, 34952, 53469], [15, 3840, 4369, 26214, 61986], [15, 3840, 13107, 17476, 61986], [15, 3840, 13107, 26214, 61440], [15, 4369, 8738, 20292, 61986], [15, 4369, 8738, 28518, 61440], [15, 4369, 12066, 17476, 61986], [15, 8738, 13107, 20292, 61440], [15, 12066, 13107, 17476, 61440]], [[15, 240, 3840, 13107, 30583], [15, 240, 4369, 8738, 28791]], [[15, 240, 4080, 13107, 34952], [15, 240, 4080, 17476, 30583], [15, 4593, 17476, 26214, 61440], [240, 255, 3840, 13107, 34952], [240, 255, 3840, 17476, 30583], [240, 255, 4369, 8738, 36744], [255, 4080, 4369, 8738, 34952]], [[15, 208, 3840, 17476, 34952], [240, 255, 4080, 17476, 34952], [240, 3840, 13107, 34952, 65280], [240, 3840, 13107, 36744, 61440], [240, 3840, 17476, 30583, 65280], [240, 4369, 8738, 36744, 65280], [240, 17476, 34952, 61695, 65520], [3840, 4080, 13107, 34952, 61440], [3840, 4080, 17476, 30583, 61440], [3840, 4369, 34952, 61986, 65520], [3840, 8738, 34952, 61713, 65520], [3840, 13107, 34952, 61440, 65520], [3840, 17476, 30583, 61440, 65520], [4080, 4369, 8738, 34952, 65280]], [[240, 3840, 4080, 34952, 62532], [240, 3840, 17476, 34952, 65520], [240, 3840, 34952, 62532, 65520], [240, 4080, 17476, 34952, 65280], [3840, 4080, 17476, 34952, 61680]], [[240, 3840, 4593, 34952, 62532], [3840, 4593, 17476, 34952, 61680], [4080, 4593, 17476, 34952, 61440], [4593, 17476, 34952, 61440, 65520]], [[3840, 8946, 17476, 34952, 65520]], [], [[240, 3840, 17476, 34952, 65524]], [], [[15, 240, 3840, 35064, 48059]], [], [], [], [], [], [], [[15, 240, 3822, 17476, 34952], [15, 240, 4095, 13107, 34952], [15, 240, 4095, 17476, 30583], [15, 240, 17476, 34952, 57582], [15, 4369, 8738, 32631, 61440], [15, 13107, 16179, 17476, 61440]], [[15, 240, 1024, 13107, 34952], [15, 240, 1024, 17476, 30583], [15, 240, 3840, 13107, 36744], [15, 240, 4369, 8738, 35976], [15, 240, 4369, 25122, 34952], [15, 240, 4369, 34952, 61986], [15, 240, 8738, 20753, 34952], [15, 240, 8738, 34952, 61713], [15, 240, 13107, 16384, 34952], [15, 240, 13107, 34952, 61440], [15, 240, 16384, 17476, 30583], [15, 240, 17476, 28672, 30583], [15, 240, 17476, 30583, 61440], [15, 240, 21845, 26214, 61440], [15, 240, 30583, 61440, 62532], [15, 240, 34952, 61440, 62259], [15, 240, 34952, 61713, 61986], [15, 240, 34952, 62259], [15, 1264, 4369, 8738, 34952], [15, 3840, 4080, 13107, 34952], [15, 3840, 4080, 17476, 30583], [15, 4369, 34952, 61680, 61986], [15, 8738, 34952, 61680, 61713], [15, 13107, 34952, 61440, 61680], [15, 17476, 30583, 61440, 61680], [240, 255, 4095, 17476, 34952], [240, 3840, 3855, 13107, 34952], [240, 3840, 3855, 17476, 30583], [240, 4095, 17476, 34952, 61695], [240, 4369, 8738, 16399, 34952], [240, 13107, 34952, 61440, 61455], [240, 17476, 30583, 61440, 61455], [3855, 4080, 4369, 8738, 34952], [4369, 8738, 34952, 61455, 61680]], [[15, 224, 3840, 17476, 34952], [15, 240, 1264, 17476, 34952], [15, 240, 16624, 17476, 34952], [15, 240, 17476, 34952, 61680], [15, 240, 34952, 61680, 62532], [15, 3840, 4593, 8738, 39321], [15, 3840, 4593, 13107, 34952], [15, 3840, 4593, 17476, 30583], [15, 4369, 4593, 8738, 36744], [240, 255, 1024, 17476, 34952], [240, 255, 16384, 17476, 34952], [240, 255, 17476, 34952, 61440], [240, 255, 34952, 61440, 62532], [240, 1092, 3840, 4095, 34952], [240, 3840, 4095, 17476, 34952], [240, 3840, 4095, 34952, 62532], [240, 3840, 17476, 20479, 34952], [240, 3855, 4080, 17476, 34952], [240, 3855, 17476, 34952, 65520], [240, 4095, 17476, 34952, 65280], [240, 17476, 34952, 61440, 61695], [240, 17476, 34952, 61455, 61680], [240, 34952, 61440, 61695, 62532], [240, 34952, 61695, 62532], [255, 3840, 4080, 17476, 34952], [255, 3840, 17476, 34952, 65520], [255, 17476, 34952, 61440, 61680], [255, 17476, 34952, 61680], [3840, 4095, 17476, 34952, 61680], [17476, 34952, 61440, 61680, 61695]], [[15, 4080, 4593, 17476, 34952], [15, 4369, 8946, 34952, 61986], [15, 4369, 8946, 43690, 61440], [15, 4369, 34952, 61986, 62194], [15, 8738, 8946, 34952, 61713], [15, 8946, 13107, 34952, 61440], [15, 8946, 17476, 30583, 61440], [64, 3840, 17652, 34952, 61440], [128, 3840, 17476, 35064, 61440], [240, 512, 3840, 34952, 62532], [240, 1024, 3840, 34952, 62532], [240, 1024, 17476, 34952, 65280], [240, 1024, 20292, 34952, 61440], [240, 1092, 3840, 34952, 61440], [240, 2048, 3840, 34952, 62532], [240, 2048, 17476, 36744, 61440], [240, 3840, 4096, 34952, 62532], [240, 3840, 4369, 30583, 62532], [240, 3840, 8192, 34952, 62532], [240, 3840, 13107, 39321, 61440], [240, 3840, 16384, 34952, 62532], [240, 3840, 17476, 32768, 63624], [240, 3840, 17476, 34952, 45056], [240, 3840, 17476, 34952, 61440], [240, 3840, 17476, 34952, 61952], [240, 3840, 17476, 34952, 62464], [240, 3840, 17476, 34952, 63488], [240, 3840, 17476, 35976, 61440], [240, 3840, 17476, 51336, 61440], [240, 3840, 19524, 34952, 61440], [240, 3840, 21572, 34952, 61440], [240, 3840, 25668, 34952, 61440], [240, 3840, 32768, 34952, 62532], [240, 3840, 34952, 50244, 61440], [240, 3840, 34952, 61440, 62532], [240, 3840, 34952, 62532], [240, 7936, 17476, 34952, 61440], [240, 12032, 17476, 34952, 61440], [240, 16384, 17476, 34952, 65280], [240, 17476, 20224, 34952, 61440], [240, 17476, 34952, 36608, 61440], [240, 17476, 34952, 61440, 65280], [240, 34952, 61440, 62532, 65280], [752, 3840, 17476, 34952, 61440], [1264, 3840, 17476, 34952, 61440], [2048, 4080, 17476, 34952, 61440], [2048, 17476, 34952, 61440, 65520], [2288, 3840, 17476, 34952, 61440], [3840, 4080, 17476, 34952, 65280], [3840, 4336, 17476, 34952, 61440], [3840, 8432, 17476, 34952, 61440], [3840, 16624, 17476, 34952, 61440], [3840, 17476, 33008, 34952, 61440], [3840, 17476, 34952, 61440, 61680], [3840, 17476, 34952, 65280, 65520], [3840, 34952, 61440, 61680, 62532], [17476, 34952, 61440, 61680, 65280], [17476, 34952, 61680, 65280]], [[1, 240, 3840, 34952, 62532], [15, 240, 17476, 34952, 62194], [15, 3840, 13107, 13299, 34952], [15, 4593, 8177, 17476, 34952], [15, 4593, 17476, 34952, 61937], [15, 8946, 17476, 34952, 61680], [240, 4080, 4369, 34952, 62532], [240, 7953, 17476, 34952, 65520], [240, 17476, 34952, 61713, 65520], [4080, 4369, 17476, 34952, 61680]], [[2, 240, 3840, 34952, 62532], [15, 4369, 8738, 17652, 63624], [15, 4369, 17652, 34952, 61986], [15, 8738, 17652, 34952, 61713], [15, 13107, 17652, 34952, 61440], [15, 17476, 17652, 30583, 61440]], [[15, 8946, 17476, 34952, 62194]], [[4, 240, 3840, 34952, 62532], [240, 3840, 17476, 34952, 61444], [240, 3840, 17476, 34956, 61440]], [[15, 240, 4369, 34959, 61986], [15, 240, 8738, 34959, 61713], [15, 240, 13107, 34959, 61440], [255, 4369, 8738, 34959, 61440], [3840, 4095, 4369, 8738, 34959], [4369, 8738, 34959, 61440, 61695]], [[7, 3840, 17476, 30583, 61440], [3840, 4369, 8738, 34959, 61440], [3840, 4369, 34959, 61440, 61986], [3840, 4369, 34959, 61986], [3840, 8738, 34959, 61440, 61713], [3840, 8738, 34959, 61713], [3840, 13107, 34959, 61440], [4369, 8738, 34959, 61440, 65280]], [[15, 240, 17476, 34952, 63736], [15, 240, 17476, 35064, 63624], [255, 17476, 34952, 35064, 61440], [3840, 4095, 17476, 34952, 35064], [17476, 34952, 35064, 61440, 61695]], [[8, 240, 3840, 34952, 62532], [240, 3840, 17484, 34952, 61440], [248, 3840, 17476, 34952, 61440], [3840, 4369, 35064, 48059, 61440], [3840, 17476, 34952, 35064, 61440], [3840, 17476, 34952, 61440, 63736], [3840, 17476, 35064, 61440, 63624], [3840, 34952, 35064, 61440, 62532], [3840, 34952, 35064, 62532], [17476, 34952, 35064, 61440, 65280]], [], [], [[11, 240, 3840, 17476, 34952]], [], [[15, 240, 13107, 34952, 61455], [15, 240, 17476, 30583, 61455], [15, 255, 4369, 34952, 61986], [15, 255, 8738, 34952, 61713], [15, 255, 13107, 34952, 61440], [15, 255, 17476, 30583, 61440], [15, 3822, 3840, 17476, 34952], [15, 3840, 4095, 13107, 34952], [15, 3840, 4095, 17476, 30583], [15, 4369, 34952, 61695, 61986], [15, 8738, 34952, 61695, 61713], [15, 13107, 34952, 61440, 61695], [15, 17476, 30583, 61440, 61695], [255, 4369, 8738, 34952, 61455]], [[15, 240, 17476, 34952, 61695], [15, 240, 17476, 34952, 62207], [15, 240, 17476, 34952, 63743], [15, 240, 34952, 36744, 48059], [15, 240, 34952, 61695, 62532], [15, 255, 17476, 34952, 61680], [15, 3840, 4369, 34952, 61986], [15, 3840, 8738, 34952, 61713], [15, 3840, 13107, 34952, 61440], [15, 3840, 17476, 30583, 61440], [15, 3840, 21845, 26214, 61440], [15, 3840, 30583, 61440, 62532], [15, 3840, 34952, 61440, 62259], [15, 3840, 34952, 61713, 61986], [15, 3840, 34952, 62259], [15, 4369, 34952, 61986, 65280], [15, 8738, 34952, 61713, 65280], [15, 13107, 17476, 20292, 61440], [15, 13107, 34952, 61440, 65280], [15, 17476, 30583, 61440, 65280], [240, 255, 17476, 34952, 61455], [3840, 13107, 34952, 61440, 61455], [3840, 17476, 30583, 61440, 61455], [4369, 8738, 34952, 61455, 65280]], [[8, 240, 3840, 17476, 34959], [15, 64, 3840, 17652, 34952], [15, 240, 1024, 20292, 34952], [15, 240, 1092, 3840, 34952], [15, 240, 1280, 17476, 34952], [15, 240, 1792, 17476, 34952], [15, 240, 3328, 17476, 34952], [15, 240, 3840, 13107, 39321], [15, 240, 3840, 17476, 34952], [15, 240, 3840, 17476, 35976], [15, 240, 3840, 17476, 51336], [15, 240, 3840, 19524, 34952], [15, 240, 3840, 21572, 34952], [15, 240, 3840, 25668, 34952], [15, 240, 3840, 34952, 50244], [15, 240, 3840, 34952, 62532], [15, 240, 4369, 13107, 36744], [15, 240, 7936, 17476, 34952], [15, 240, 12032, 17476, 34952], [15, 240, 17476, 34952, 36608], [15, 240, 17476, 34952, 61696], [15, 496, 17476, 34952, 61440], [15, 752, 3840, 17476, 34952], [15, 1264, 3840, 17476, 34952], [15, 2048, 4080, 17476, 34952], [15, 2288, 3840, 17476, 34952], [15, 3840, 4336, 17476, 34952], [15, 3840, 8432, 17476, 34952], [15, 4095, 4593, 17476, 34952], [15, 17476, 34952, 61680, 65280], [240, 527, 3840, 17476, 34952], [240, 1039, 3840, 17476, 34952], [240, 2063, 3840, 17476, 34952], [240, 3840, 16399, 17476, 34952], [240, 3840, 34952, 61455, 62532], [240, 17476, 34952, 61455, 65280], [3840, 3855, 4080, 17476, 34952], [3840, 17476, 34952, 61455, 61680], [3840, 17476, 34952, 65295, 65520], [3840, 17476, 34959, 35064, 61440]], [[15, 240, 3841, 17476, 34952], [15, 241, 3840, 17476, 34952], [15, 1024, 4593, 17476, 34952], [15, 4593, 16384, 17476, 34952], [15, 4593, 17476, 34952, 61440], [15, 4593, 34952, 61440, 62532], [15, 8946, 17476, 34952, 61695], [15, 17476, 34952, 61440, 61937], [16, 240, 3840, 34952, 62532], [240, 3840, 17476, 34952, 61456], [240, 3840, 17476, 34968, 61440], [240, 3856, 17476, 34952, 61440], [255, 4080, 4369, 17476, 34952], [3840, 3855, 4593, 17476, 34952], [4593, 17476, 34952, 61440, 61455]], [[15, 240, 3842, 17476, 34952], [15, 242, 3840, 17476, 34952], [15, 3840, 4369, 8946, 48059], [15, 3840, 8946, 17476, 34952], [3840, 4080, 4369, 34952, 62532], [3840, 17476, 34952, 61713, 65520], [4080, 4369, 17476, 34952, 65280]], [[15, 13299, 17476, 34952, 61440], [240, 12066, 17476, 34952, 65520]], [[15, 240, 3840, 17476, 34956], [15, 240, 3844, 17476, 34952], [15, 244, 3840, 17476, 34952], [15, 17652, 20292, 34952, 61440]], [[15, 17476, 22005, 34952, 61440]], [[15, 3840, 4369, 34959, 61986], [15, 3840, 8738, 34959, 61713], [15, 3840, 13107, 34959, 61440]], [[15, 128, 34952, 48059, 61440], [15, 17476, 30711, 34952, 61440]], [[15, 240, 3840, 17484, 34952], [15, 240, 3848, 17476, 34952], [15, 248, 3840, 17476, 34952], [15, 3840, 34952, 35064, 62532], [240, 3840, 4369, 8738, 48048], [3840, 17476, 30471, 34952, 61440], [4369, 7953, 8738, 34959, 61440]], [], [], [], [], [], [[15, 255, 17476, 34952, 61695], [15, 3840, 13107, 34952, 61455], [15, 3840, 17476, 30583, 61455], [15, 3855, 4369, 34952, 61986], [15, 3855, 8738, 34952, 61713], [15, 3855, 13107, 34952, 61440], [15, 3855, 17476, 30583, 61440], [15, 4369, 34952, 61986, 65295], [15, 8738, 34952, 61713, 65295], [15, 13107, 34952, 61440, 65295], [15, 17476, 30583, 61440, 65295], [3855, 4369, 8738, 34952, 61455]], [[15, 240, 3855, 17476, 34952], [15, 240, 3855, 34952, 62532], [15, 255, 3840, 17476, 34952], [15, 255, 3840, 34952, 62532], [15, 2048, 4095, 17476, 34952], [15, 3840, 8959, 17476, 34952], [15, 4607, 17476, 34952, 61440], [15, 17476, 34952, 61440, 61951], [15, 17476, 34952, 61440, 63487], [15, 17476, 34952, 61680, 65295], [15, 17476, 34952, 61695, 65280], [240, 3855, 17476, 34952, 61455], [255, 3840, 17476, 34952, 61455], [255, 3855, 17476, 34952], [255, 3855, 17476, 34952, 61440], [255, 17476, 34952, 61440, 65295], [3840, 3855, 4095, 17476, 34952], [3840, 4095, 17476, 34952, 65295], [3855, 17476, 34952, 61440, 61695], [17476, 34952, 61440, 61695, 65295]], [[15, 240, 3840, 17476, 34968], [15, 240, 3856, 17476, 34952], [15, 240, 34952, 52428, 63624], [15, 240, 34952, 63624, 64716], [15, 2048, 17476, 34952, 61440], [15, 2048, 17476, 34952, 63488], [15, 2048, 19524, 34952, 61440], [15, 2048, 34952, 61440, 62532], [15, 2560, 17476, 34952, 61440], [15, 3072, 17476, 34952, 61440], [15, 3584, 17476, 34952, 61440], [15, 3840, 17476, 34952, 61696], [15, 3840, 17476, 34952, 65280], [15, 3840, 34952, 62532, 65280], [15, 4369, 7953, 34952, 61986], [15, 4593, 17476, 34952, 61455], [15, 7953, 8738, 34952, 61713], [15, 7953, 13107, 34952, 61440], [15, 7953, 17476, 30583, 61440], [15, 8738, 34952, 61713, 65297], [15, 17476, 34816, 34952, 61440], [15, 17476, 34952, 61440, 63488], [15, 17476, 34952, 63488], [15, 19524, 34952, 61440], [31, 240, 3840, 17476, 34952], [271, 3840, 17476, 34952, 61440], [2048, 2063, 17476, 34952, 61440], [2048, 17476, 34952, 61440, 61455], [3840, 3855, 17476, 34952, 61440], [3840, 3855, 34952, 61440, 62532], [3840, 17476, 34952, 61440, 65295], [3840, 17476, 34952, 61455, 65280], [3840, 34952, 61440, 62532, 65295], [3840, 34952, 62532, 65295], [3855, 17476, 34952, 61440, 65280], [3855, 17476, 34952, 65280], [17476, 34952, 61440, 65280, 65295]], [[15, 240, 1092, 4369, 34952], [15, 240, 4369, 17476, 35976], [15, 240, 4369, 17476, 51336], [15, 240, 5393, 17476, 34952], [15, 240, 7953, 17476, 34952], [15, 240, 8738, 34952, 62259], [15, 240, 8738, 43690, 61713], [15, 240, 13107, 34952, 61986], [15, 240, 13107, 43690, 61440], [15, 240, 17476, 20753, 34952], [15, 240, 17476, 30583, 61986], [15, 240, 17476, 34952, 61713], [15, 240, 34952, 61713, 62532], [15, 240, 34952, 61986, 62259], [15, 1264, 4369, 17476, 34952], [15, 3855, 8946, 17476, 34952], [15, 17476, 34952, 61680, 61713], [32, 240, 3840, 34952, 62532], [240, 3840, 17476, 34952, 61472], [240, 3840, 17476, 34984, 61440], [240, 3872, 17476, 34952, 61440], [240, 4369, 16399, 17476, 34952], [240, 4369, 34952, 61455, 62532], [3855, 4080, 4369, 17476, 34952], [4369, 17476, 34952, 61455, 61680]], [[15, 3840, 4593, 8738, 48059], [15, 3840, 4593, 17476, 39321], [240, 255, 17476, 34952, 61986], [240, 8738, 34952, 61695, 62532], [255, 8738, 17476, 34952, 61680]], [[15, 4369, 8946, 17476, 63624], [15, 7953, 8946, 17476, 34952], [15, 8946, 17476, 34952, 61713], [240, 3840, 4369, 39321, 62532], [240, 3840, 8738, 34952, 62532], [240, 3840, 13107, 48059, 61440], [240, 3840, 21845, 39321, 61440], [240, 3840, 34952, 61986, 62532], [240, 17476, 34952, 61986, 65280], [3840, 17476, 34952, 61680, 61986], [8738, 17476, 34952, 61680, 65280]], [[15, 192, 3840, 17476, 52428]], [[15, 17476, 17652, 34952, 61713]], [], [], [[15, 2056, 17476, 34952, 61440], [15, 17476, 34824, 34952, 61440], [3840, 34952, 34959, 52428, 61440]], [[3840, 4369, 8738, 34959, 61986], [3840, 8738, 13107, 34959, 61440], [4369, 8738, 12066, 34959, 61440]], [], [[3840, 8738, 34952, 35064, 62532], [3840, 17476, 35064, 43690, 61440]], [], [[15, 3840, 17476, 34952, 56589]], [[15, 255, 3855, 17476, 34952], [15, 17476, 34952, 60942, 61440], [15, 17476, 34952, 61695, 65295]], [[15, 240, 7967, 17476, 34952], [15, 240, 17476, 34952, 61727], [15, 2048, 17476, 34952, 61455], [15, 2063, 17476, 34952, 61440], [15, 3840, 17476, 34952, 65295], [15, 3840, 34952, 62532, 65295], [15, 3855, 17476, 34952, 65280], [3840, 3855, 17476, 34952, 61455]], [[15, 240, 3840, 17476, 34984], [15, 240, 3872, 17476, 34952], [15, 255, 7953, 17476, 34952], [15, 255, 17476, 34952, 61713], [15, 17476, 34952, 61695, 61713], [47, 240, 3840, 17476, 34952], [240, 3840, 8751, 34952, 62532], [255, 4369, 17476, 34952, 61455]], [[15, 3840, 8738, 34952, 62259], [15, 3840, 8738, 43690, 61713], [15, 3840, 13107, 34952, 61986], [15, 3840, 13107, 43690, 61440], [15, 3840, 17476, 30583, 61986], [15, 3840, 17476, 34952, 61713], [15, 3840, 17476, 34952, 65297], [15, 3840, 34952, 61713, 62532], [15, 3840, 34952, 61986, 62259], [15, 4369, 12066, 34952, 61986], [15, 4369, 34952, 61986, 65314], [15, 7953, 17476, 34952, 65280], [15, 8738, 12066, 34952, 61713], [15, 12066, 13107, 34952, 61440], [15, 12066, 17476, 30583, 61440], [15, 17476, 34952, 61713, 65280], [3840, 4369, 34952, 61455, 62532], [4369, 17476, 34952, 61455, 65280]], [[15, 240, 3840, 13107, 48059], [15, 240, 3840, 21845, 39321], [15, 240, 12066, 17476, 34952]], [[15, 4593, 8738, 17476, 63624], [15, 4593, 17476, 34952, 61986]], [[15, 3840, 8946, 17476, 43690], [15, 8946, 12066, 17476, 34952]], [[240, 3840, 17476, 52428, 65520]], [], [], [], [], [], [], [], [], [[15, 3855, 17476, 34952, 65295]], [[15, 240, 12079, 17476, 34952], [15, 3840, 17476, 34952, 61727], [15, 3840, 17476, 34952, 65311], [240, 7953, 8738, 17487, 34952]], [[15, 3855, 17476, 34952, 61713], [15, 7953, 17476, 34952, 65295], [15, 17476, 34952, 61713, 65295], [3855, 4369, 17476, 34952, 61455]], [[15, 255, 12066, 17476, 34952], [64, 240, 3840, 34952, 62532], [240, 3840, 17476, 34952, 61504], [240, 3840, 17476, 35016, 61440], [240, 3904, 17476, 34952, 61440], [255, 3855, 8738, 17476, 34952]], [[15, 240, 34952, 48059, 49083], [15, 240, 34952, 48059, 64443], [15, 2048, 17476, 34952, 61986], [15, 3840, 17476, 34952, 65314], [15, 7953, 17476, 34952, 61713], [15, 7953, 17476, 34952, 65297], [15, 8738, 17476, 34952, 63488], [15, 8738, 19524, 34952, 61440], [15, 10786, 17476, 34952, 61440], [15, 12066, 17476, 34952, 65280], [15, 13107, 16179, 34952, 61440], [15, 17476, 34952, 61713, 65297], [3840, 3855, 17476, 34952, 61986], [3840, 8738, 34952, 62532, 65295], [3855, 8738, 17476, 34952, 65280]], [[15, 240, 13107, 17476, 63624], [15, 240, 16179, 17476, 34952], [15, 240, 17476, 34952, 62259]], [[15, 240, 17476, 52428, 61680], [240, 255, 17476, 52428, 61440], [240, 3840, 4095, 17476, 52428], [240, 17476, 34952, 61695, 62532], [240, 17476, 52428, 61440, 61695]], [[240, 3840, 8738, 43690, 62532], [240, 3840, 17476, 34952, 62532], [240, 3840, 17476, 52428, 61440], [240, 3840, 26214, 43690, 61440], [240, 17476, 52428, 61440, 65280], [3840, 17476, 52428, 61440, 61680]], [], [[15, 176, 34952, 48059, 61440]], [], [], [], [[3840, 4369, 17476, 34959, 61986], [3840, 8738, 17476, 34959, 61713], [3840, 13107, 17476, 34959, 61440], [4369, 12066, 17476, 34959, 61440]], [], [[3840, 17476, 34952, 35064, 62532], [3840, 17476, 35064, 52428, 61440]], [], [[15, 3840, 17476, 34952, 65327], [240, 17476, 17487, 34952, 61695]], [[15, 240, 3840, 17476, 35016], [15, 240, 3904, 17476, 34952], [79, 240, 3840, 17476, 34952], [240, 3840, 17476, 17487, 34952], [240, 3840, 17487, 34952, 62532], [240, 3840, 17487, 52428], [240, 3840, 17487, 52428, 61440], [240, 3840, 34952, 62532, 62543]], [[15, 12066, 17476, 34952, 65295]], [[3840, 8946, 17476, 17487, 34952]], [[15, 240, 17476, 52428, 61695], [15, 3840, 17476, 34952, 62259], [15, 4369, 20292, 34952, 61986], [15, 8738, 20292, 34952, 61713], [15, 12066, 17476, 34952, 61713], [15, 13107, 20292, 34952, 61440], [15, 17476, 20292, 30583, 61440]], [[15, 240, 3840, 17476, 52428], [15, 240, 3840, 26214, 43690], [15, 240, 20292, 52428, 61440]], [[15, 4593, 17476, 52428, 61440]], [[15, 3840, 8946, 17476, 52428]], [], [], [], [], [], [], [], [], [[15, 240, 3840, 17487, 52428]], [], [[240, 3840, 17476, 35064, 65520], [240, 7953, 17476, 17487, 34952]], [], [[15, 240, 3855, 17476, 52428], [15, 255, 3840, 17476, 52428]], [[15, 2048, 17476, 52428, 61440], [15, 3072, 17476, 52428, 61440], [15, 3840, 17476, 52428, 65280], [15, 3840, 20292, 52428, 61440], [15, 12066, 17476, 34952, 65314], [15, 17476, 19524, 34952, 61440], [3840, 3855, 17476, 52428, 61440], [3840, 17476, 34952, 62532, 65295], [3840, 17476, 52428, 61440, 65295]], [[15, 240, 7953, 17476, 52428], [15, 240, 17476, 52428, 61713], [15, 240, 21845, 52428, 61440]], [[15, 3840, 4593, 17476, 56797]], [[240, 3840, 26214, 34952, 62532], [240, 3840, 26214, 52428, 61440], [240, 3840, 30583, 48059, 61440], [240, 3840, 34952, 62532, 63078]], [[15, 192, 3840, 34952, 52428], [240, 3840, 34952, 48059, 61680], [240, 4080, 34952, 48059, 61440], [240, 34952, 48059, 61440, 65520]], [], [], [], [], [], [], [[3840, 17476, 17487, 34952, 65295], [3840, 17476, 35064, 61166, 61440]], [[15, 240, 17476, 35064, 61680], [112, 3840, 17476, 30583, 61440], [240, 255, 17476, 35064, 61440], [240, 3840, 4095, 17476, 35064], [240, 17476, 35064, 61440, 61695]], [[240, 3840, 17476, 35064, 61440], [240, 3840, 35064, 61440, 62532], [240, 3840, 35064, 62532], [240, 17476, 35064, 61440, 65280], [3840, 17476, 35064, 61440, 61680]], [[240, 3840, 4369, 17487, 56797], [240, 3840, 8738, 17487, 52428], [240, 12066, 17476, 17487, 34952]], [[15, 3840, 17476, 52428, 65295], [3840, 8946, 17476, 35064, 61440]], [], [[15, 3840, 17476, 52428, 61713], [15, 3840, 21845, 52428, 61440], [15, 4369, 20292, 52428, 61440], [15, 17476, 20292, 34952, 61713], [240, 3840, 17476, 52476, 61440], [3840, 17476, 17652, 35064, 61440]], [[15, 240, 3840, 26214, 52428], [15, 240, 3840, 30583, 48059], [15, 240, 12066, 17476, 52428]], [[15, 240, 4080, 34952, 48059], [240, 255, 3840, 34952, 48059]], [[15, 240, 17476, 35064, 63736], [15, 3840, 8946, 17476, 61166], [240, 3840, 34952, 48059, 65280], [3840, 4080, 34952, 48059, 61440], [3840, 34952, 48059, 61440, 65520]], [[240, 3840, 34952, 52428, 65520], [240, 17476, 34952, 36744, 65520], [3840, 17476, 35064, 61440, 63736]], [], [[15, 240, 13299, 17476, 61440], [15, 4593, 8946, 17476, 61440], [3840, 17476, 35064, 43770, 61440]], [[15, 3840, 4593, 13299, 17476], [3840, 4369, 8946, 17476, 65520]], [[15, 8946, 13299, 17476, 61440], [3840, 17476, 35064, 52476, 61440]], [], [[15, 240, 17476, 30711, 61440], [15, 240, 17476, 35064, 61695]], [[15, 240, 3840, 17476, 35064], [15, 240, 3840, 35064, 62532], [240, 3840, 17476, 30471, 61440], [255, 3840, 17476, 35064], [255, 3840, 17476, 35064, 61440], [3840, 17476, 35064, 35071, 61440], [3840, 17476, 35064, 61440, 61695]], [[15, 4593, 17476, 35064, 61440], [128, 240, 3840, 34952, 62532], [128, 4080, 17476, 34952, 61440], [128, 17476, 34952, 61440, 65520], [240, 3840, 17476, 34952, 61568], [240, 3840, 17604, 34952, 61440], [240, 3968, 17476, 34952, 61440], [256, 3840, 17476, 35064, 61440], [3840, 17476, 30576, 34952, 61440], [3840, 17476, 35064, 61440, 65280], [3840, 17476, 35064, 65280]], [[15, 3840, 4593, 17476, 39417], [15, 3840, 8946, 17476, 35064]], [], [[15, 240, 3840, 17476, 52476], [15, 3840, 8946, 17476, 43770], [15, 3840, 17476, 17652, 35064]], [], [[15, 240, 4095, 34952, 48059], [15, 17476, 30583, 32631, 61440]], [[15, 240, 1024, 34952, 48059], [15, 240, 1911, 17476, 34952], [15, 240, 3003, 34952, 61440], [15, 240, 4369, 34952, 64170], [15, 240, 8738, 34952, 63897], [15, 240, 13107, 34952, 63624], [15, 240, 16384, 34952, 48059], [15, 240, 17476, 30583, 63624], [15, 240, 30583, 52428, 61440], [15, 240, 34952, 39321, 61986], [15, 240, 34952, 43690, 61713], [15, 240, 34952, 48059, 61440], [15, 240, 34952, 61440, 64443], [15, 240, 34952, 64443], [15, 240, 39321, 43690, 61440], [15, 3840, 4080, 34952, 48059], [15, 34952, 48059, 61440, 61680], [240, 3840, 3855, 34952, 48059], [240, 34952, 48059, 61440, 61455]], [[15, 240, 34952, 52428, 61680], [15, 3840, 4593, 34952, 48059], [240, 255, 17476, 34952, 63624], [240, 255, 34952, 52428, 61440], [240, 3840, 4095, 34952, 52428], [240, 34952, 52428, 61440, 61695], [3840, 17476, 30471, 35064, 61440]], [[15, 8946, 34952, 48059, 61440], [240, 3003, 3840, 4369, 34952], [240, 3840, 17476, 52428, 62532], [240, 3840, 34952, 52428, 61440], [240, 3840, 34952, 61440, 64716], [240, 3840, 34952, 62532, 63624], [240, 17476, 34952, 63624, 65280], [240, 34952, 52428, 61440, 65280], [3840, 34952, 52428, 61440, 61680]], [], [[15, 3840, 13299, 17476], [15, 3840, 13299, 17476, 61440], [15, 4369, 8946, 17476, 61680], [15, 17652, 34952, 48059, 61440]], [[3840, 4593, 8738, 17476, 65520]], [[15, 4369, 8946, 17476, 62194]], [], [[15, 240, 3840, 17476, 30471], [15, 240, 3855, 17476, 35064], [15, 255, 3840, 17476, 35064], [15, 3840, 17476, 30711, 61440], [3840, 4369, 34952, 34959, 61986], [3840, 8738, 34952, 34959, 61713], [3840, 13107, 34952, 34959, 61440], [3840, 17476, 30583, 34959, 61440]], [[15, 128, 4080, 17476, 34952], [15, 240, 3840, 17604, 34952], [15, 240, 3968, 17476, 34952], [15, 240, 17476, 34824, 61440], [15, 2048, 17476, 35064, 61440], [15, 3840, 17476, 35064, 65280], [143, 240, 3840, 17476, 34952], [240, 3840, 34952, 34959, 62532], [240, 3840, 34959, 52428, 61440], [3840, 3855, 17476, 35064, 61440], [3840, 17476, 35064, 61440, 65295]], [[15, 240, 7953, 17476, 35064], [15, 240, 17476, 35064, 61713], [255, 4369, 17476, 35064, 61440], [3840, 4095, 4369, 17476, 35064], [3840, 34952, 35064, 52428, 61440], [4369, 17476, 35064, 61440, 61695]], [[3840, 4369, 17476, 35064, 61440], [3840, 4369, 35064, 61440, 62532], [3840, 4369, 35064, 62532], [3840, 7953, 17476, 35064, 61440], [3840, 17476, 35064, 61440, 61713], [4369, 17476, 35064, 61440, 65280]], [[240, 3840, 8738, 35064, 62532]], [[240, 3840, 8738, 17487, 61166], [240, 3840, 17476, 17487, 52428]], [], [[15, 240, 34952, 48059, 61455], [15, 255, 34952, 48059, 61440], [15, 3840, 4095, 34952, 48059], [15, 34952, 48059, 61440, 61695]], [[15, 240, 34952, 52428, 61695], [15, 2816, 34952, 48059, 61440], [15, 3003, 3840, 34952, 61440], [15, 3840, 30583, 52428, 61440], [15, 3840, 34952, 39321, 61986], [15, 3840, 34952, 43690, 61713], [15, 3840, 34952, 48059, 61440], [15, 3840, 34952, 61440, 64443], [15, 3840, 39321, 43690, 61440], [15, 34952, 48059, 61440, 65280], [3840, 4369, 8946, 17487], [3840, 4369, 8946, 17487, 61440], [3840, 34952, 48059, 61440, 61455]], [[15, 240, 3840, 34952, 52428], [15, 240, 3840, 34952, 64716], [15, 240, 17476, 34952, 36744], [15, 240, 17476, 36744, 63624], [15, 240, 34952, 36744, 62532], [15, 240, 36744, 52428], [15, 240, 36744, 52428, 61440]], [[15, 4593, 17476, 34952, 63624], [15, 4593, 34952, 52428, 61440]], [[15, 3840, 8946, 34952, 52428], [15, 4369, 8946, 17476, 61695], [15, 8946, 17476, 34952, 36744]], [[15, 3840, 4369, 8946, 17476], [15, 4593, 8738, 17476, 61680]], [[15, 4369, 13299, 17476, 61440], [240, 3840, 13107, 17476, 65520]], [], [], [[15, 128, 4095, 17476, 34952], [15, 240, 3840, 34959, 52428], [15, 240, 17476, 34952, 36751], [15, 240, 17476, 34959, 36744], [15, 3840, 17476, 35064, 65295], [255, 3840, 17476, 34952, 34959]], [[15, 128, 16384, 17476, 34952], [15, 128, 17476, 34952, 61440], [15, 128, 34952, 61440, 62532], [15, 3840, 17476, 34824, 61440], [15, 4369, 17476, 30711, 61440], [15, 17476, 32896, 34952, 61440], [15, 17476, 34952, 61440, 61568], [15, 17604, 34952, 61440], [128, 17476, 34952, 61440, 61455], [143, 17476, 34952, 61440], [2048, 17476, 34952, 34959, 61440], [3840, 4383, 17476, 35064, 61440], [3840, 17476, 34952, 34959, 65280], [3840, 17476, 34952, 36751, 61440], [3840, 17476, 34952, 61440, 65423], [3840, 17476, 34959, 36744, 61440]], [[15, 3840, 4369, 35064, 62532], [3840, 4369, 17476, 30471, 61440]], [[15, 240, 12066, 17476, 35064], [255, 3840, 8738, 17476, 35064]], [[3840, 8738, 17476, 35064, 65280], [3840, 12066, 17476, 35064, 61440]], [], [], [[15, 3840, 4369, 8946, 17487], [15, 3840, 34952, 48059, 61455], [15, 3855, 34952, 48059, 61440], [15, 34952, 48059, 61440, 65295]], [[15, 240, 3855, 34952, 52428], [15, 255, 3840, 34952, 52428], [15, 255, 17476, 34952, 36744], [3840, 4593, 8738, 17487], [3840, 4593, 8738, 17487, 61440]], [[15, 136, 17476, 34952, 61440], [15, 2048, 34952, 52428, 61440], [15, 3072, 34952, 52428, 61440], [15, 3840, 34952, 52428, 65280], [15, 3840, 36744, 52428, 61440], [15, 7953, 34952, 48059, 61440], [15, 17476, 32904, 34952, 61440], [15, 17476, 34952, 36744, 65280], [3840, 3855, 34952, 52428, 61440], [3840, 34952, 52428, 61440, 65295]], [[15, 240, 7953, 34952, 52428], [15, 240, 8738, 34952, 64443], [15, 240, 17476, 34952, 40857], [15, 240, 17476, 34952, 63897], [15, 240, 34952, 48059, 61986], [15, 240, 34952, 52428, 61713], [15, 240, 39321, 52428, 61440]], [[15, 3855, 4369, 8946, 17476], [15, 4593, 8738, 17476, 61695]], [[15, 240, 13107, 17476, 61680], [15, 3840, 4593, 8738, 17476], [240, 255, 13107, 17476, 61440], [240, 3840, 4095, 13107, 17476], [240, 3840, 34952, 43690, 62532], [240, 3840, 43690, 52428, 61440], [240, 13107, 17476, 61440, 61695], [255, 4369, 8738, 17476, 61680]], [[15, 4369, 7953, 8946, 17476], [15, 4369, 8946, 17476, 61713], [15, 4369, 8946, 21845, 61440], [240, 3840, 13107, 17476, 61440], [240, 13107, 17476, 61440, 65280], [3840, 13107, 17476, 61440, 61680], [4369, 8738, 17476, 61680, 65280]], [[15, 3840, 8738, 13299, 17476]], [], [[15, 128, 17476, 34952, 61455], [15, 143, 17476, 34952, 61440], [15, 17476, 34824, 61440, 65295]], [[15, 144, 17476, 34952, 61440]], [[15, 4369, 17476, 34824, 61440], [3840, 4369, 34959, 52428, 61440], [3840, 17476, 34952, 34959, 61713]], [], [], [[3840, 4369, 8738, 35064, 62532], [3840, 13107, 17476, 35064, 61440]], [[240, 3840, 17476, 35064, 62532]], [[15, 3840, 4369, 17476, 56589], [15, 3840, 4593, 8738, 17487], [240, 4369, 8738, 17487, 61695]], [[15, 3840, 34952, 52428, 65295], [15, 17476, 34952, 36744, 65295], [240, 3840, 4369, 8738, 17487], [240, 3840, 13107, 17487], [240, 3840, 13107, 17487, 61440]], [], [[15, 3840, 34952, 48059, 61986], [15, 3840, 34952, 52428, 61713], [15, 3840, 39321, 52428, 61440], [15, 12066, 34952, 48059, 61440], [3840, 4369, 8738, 8946, 17487]], [[15, 240, 3840, 43690, 52428], [15, 240, 4369, 36744, 56797], [15, 240, 8738, 36744, 52428], [15, 240, 12066, 34952, 52428], [15, 240, 13107, 17476, 61695], [15, 240, 17476, 34952, 44970], [15, 3855, 4593, 8738, 17476]], [[15, 240, 3840, 13107, 17476], [15, 240, 13107, 20292, 61440]], [[15, 4593, 7953, 8738, 17476], [15, 4593, 8738, 17476, 61713], [15, 4593, 13107, 17476, 61440]], [[15, 3840, 8946, 13107, 17476], [15, 4369, 8946, 12066, 17476]], [[15, 13107, 13299, 17476, 61440]], [], [[15, 160, 17476, 34952, 61440], [240, 3840, 17476, 17487, 35064]], [], [[15, 128, 17476, 34952, 61986], [15, 8738, 17604, 34952, 61440], [15, 8866, 17476, 34952, 61440], [143, 8738, 17476, 34952, 61440]], [], [], [[3840, 17476, 20292, 35064, 61440]], [[15, 240, 3840, 13107, 17487]], [], [[15, 3840, 8738, 17476, 60942], [240, 4369, 7953, 8738, 17487]], [], [[15, 240, 3855, 13107, 17476], [15, 255, 3840, 13107, 17476], [255, 3855, 4369, 8738, 17476]], [[15, 240, 17476, 34952, 49083], [15, 240, 17476, 34952, 64443], [15, 240, 48059, 52428, 61440], [15, 2048, 13107, 17476, 61440], [15, 3840, 13107, 17476, 65280], [15, 3840, 13107, 20292, 61440], [15, 4369, 8738, 17476, 63488], [15, 4369, 8738, 19524, 61440], [3840, 3855, 13107, 17476, 61440], [3840, 13107, 17476, 61440, 65295], [3855, 4369, 8738, 17476, 65280]], [[15, 240, 7953, 13107, 17476], [15, 240, 8738, 21845, 61713], [15, 240, 13107, 17476, 61713], [15, 240, 13107, 21845, 61440]], [[15, 3840, 4593, 8738, 26214], [15, 4593, 8738, 12066, 17476], [240, 3840, 34952, 52428, 62532], [240, 3840, 34952, 62532, 64716]], [[240, 3840, 13107, 26214, 61440]], [], [[15, 176, 17476, 34952, 61440]], [], [], [], [], [], [[3840, 4369, 8738, 17487, 65295], [3840, 4369, 17476, 35064, 62532], [3840, 17476, 21845, 35064, 61440]], [], [[240, 3840, 17487, 34952, 52428], [240, 17476, 17487, 34952, 36744]], [[240, 3840, 8738, 13107, 17487], [240, 4369, 8738, 12066, 17487]], [[15, 3840, 13107, 17476, 65295]], [[15, 3840, 48059, 52428, 61440], [15, 17476, 34952, 45243, 61440], [15, 20292, 34952, 48059, 61440], [3840, 4369, 8946, 17476, 17487]], [[15, 240, 8738, 36744, 61166], [15, 240, 17476, 36744, 52428], [15, 3840, 8738, 21845, 61713], [15, 3840, 13107, 17476, 61713], [15, 3840, 13107, 21845, 61440], [15, 4369, 8738, 20292, 61713], [15, 4369, 13107, 20292, 61440]], [[15, 240, 3840, 13107, 26214], [15, 240, 12066, 13107, 17476]], [], [[15, 3840, 8946, 17476, 21845]], [[15, 192, 17476, 34952, 61440], [240, 3840, 13107, 34952, 65520], [240, 3840, 17476, 30583, 65520], [240, 4369, 8738, 36744, 65520]], [[240, 4080, 17476, 34952, 65520]], [], [], [[15, 128, 17476, 52428, 61440], [15, 17476, 17604, 34952, 61440]], [], [], [], [[3840, 4369, 8738, 30576, 61440]], [], [], [[3840, 4593, 8738, 17476, 17487]], [], [[15, 240, 3549, 17476, 34952]], [[15, 240, 4369, 30583, 61986], [15, 240, 8738, 30583, 61713], [15, 240, 13107, 16179, 17476], [15, 240, 13107, 17476, 62259], [15, 240, 13107, 30583, 61440]], [[15, 240, 13107, 34952, 61680], [15, 240, 17476, 30583, 61680], [15, 3840, 4593, 17476, 26214], [240, 255, 4369, 34952, 61986], [240, 255, 8738, 34952, 61713], [240, 255, 13107, 34952, 61440], [240, 255, 17476, 30583, 61440], [240, 3840, 4095, 13107, 34952], [240, 3840, 4095, 17476, 30583], [240, 3840, 34952, 61166, 62532], [240, 13107, 34952, 61440, 61695], [240, 17476, 30583, 61440, 61695], [255, 4369, 8738, 34952, 61680]], [[15, 208, 17476, 34952, 61440], [240, 255, 17476, 34952, 61680], [240, 3840, 4369, 26214, 62532], [240, 3840, 8738, 21845, 62532], [240, 3840, 13107, 17476, 62532], [240, 3840, 13107, 34952, 61440], [240, 3840, 17476, 30583, 61440], [240, 3840, 21845, 26214, 61440], [240, 3840, 30583, 61440, 62532], [240, 3840, 30583, 62532], [240, 3840, 34952, 61440, 62259], [240, 3840, 34952, 61713, 61986], [240, 4080, 4095, 17476, 34952], [240, 4095, 17476, 34952, 65520], [240, 4369, 34952, 61986, 65280], [240, 8738, 34952, 61713, 65280], [240, 13107, 34952, 61440, 65280], [240, 17476, 30583, 61440, 65280], [240, 17476, 34952, 61680, 61695], [3840, 4369, 34952, 61680, 61986], [3840, 8738, 34952, 61680, 61713], [3840, 13107, 34952, 61440, 61680], [3840, 17476, 30583, 61440, 61680], [4369, 8738, 34952, 61680, 65280]], [[240, 1024, 17476, 34952, 65520], [240, 3840, 17476, 34952, 61680], [240, 3840, 34952, 61680, 62532], [240, 4080, 17476, 34952, 61440], [240, 4080, 34952, 61440, 62532], [240, 4080, 34952, 62532], [240, 16384, 17476, 34952, 65520], [240, 17476, 34952, 61440, 65520], [240, 17476, 34952, 61680, 65280], [240, 34952, 61440, 62532, 65520], [3840, 4080, 17476, 34952, 65520], [4080, 17476, 34952, 61440, 61680], [4080, 17476, 34952, 61680], [17476, 34952, 61440, 61680, 65520]], [[3840, 4593, 17476, 34952, 65520]], [[240, 3840, 8946, 34952, 62532], [3840, 8946, 17476, 34952, 61680], [4080, 8946, 17476, 34952, 61440], [8946, 17476, 34952, 61440, 65520]], [], [[240, 3840, 17476, 34952, 62708], [240, 3840, 17652, 34952, 62532], [240, 3840, 34952, 62532, 62708], [4080, 17476, 17652, 34952, 61440], [17476, 17652, 34952, 61440, 65520]], [], [[15, 240, 35064, 48059, 61440], [240, 3840, 4369, 34959, 61986], [240, 3840, 8738, 34959, 61713], [240, 3840, 13107, 34959, 61440]], [[3840, 4369, 35064, 43690, 61440], [3840, 8738, 35064, 39321, 61440], [3840, 13107, 34952, 35064, 61440], [3840, 17476, 30583, 35064, 61440], [3840, 35064, 48059, 61440]], [[240, 3840, 34952, 35064, 62532]], [], [[240, 3840, 13107, 17476, 17487]], [], [[15, 3549, 3840, 17476, 34952], [15, 17476, 34952, 53469, 61440]], [[15, 240, 13107, 34952, 61695], [15, 240, 17476, 30583, 61695], [15, 3840, 4369, 30583, 61986], [15, 3840, 8738, 30583, 61713], [15, 3840, 13107, 17476, 62259], [15, 3840, 13107, 30583, 61440]], [[15, 240, 1792, 17476, 30583], [15, 240, 3840, 13107, 34952], [15, 240, 3840, 17476, 30583], [15, 240, 3840, 21845, 26214], [15, 240, 3840, 30583, 62532], [15, 240, 3840, 34952, 62259], [15, 240, 4369, 8738, 36744], [15, 240, 13107, 36744], [15, 240, 13107, 36744, 61440], [240, 255, 17476, 34952, 61695]], [[15, 224, 17476, 34952, 61440], [15, 240, 4080, 17476, 34952], [15, 240, 4080, 34952, 62532], [15, 4080, 17476, 34952, 61680], [15, 4369, 4593, 34952, 61986], [15, 4593, 7953, 8738, 34952], [15, 4593, 8738, 34952, 61713], [15, 4593, 8738, 39321, 61440], [15, 4593, 13107, 34952, 61440], [15, 4593, 17476, 30583, 61440], [15, 8738, 34952, 61713, 61937], [240, 255, 3840, 17476, 34952], [240, 255, 3840, 34952, 62532], [240, 3840, 17476, 17663, 34952], [240, 3840, 17487, 17652, 34952], [240, 3840, 34952, 61695, 62532], [240, 17476, 34952, 61455, 65520], [240, 17476, 34952, 61695, 65280], [255, 3840, 17476, 34952, 61680], [255, 4080, 17476, 34952], [255, 4080, 17476, 34952, 61440], [255, 17476, 34952, 61440, 65520], [3840, 4080, 4095, 17476, 34952], [3840, 4095, 17476, 34952, 65520], [4080, 17476, 34952, 61440, 61695], [17476, 34952, 61440, 61695, 65520]], [[15, 240, 8177, 17476, 34952], [15, 240, 17476, 34952, 61937], [15, 3840, 4369, 8946, 43690], [15, 3840, 8946, 13107, 34952], [15, 3840, 8946, 17476, 30583], [15, 4369, 8738, 8946, 36744], [15, 4369, 8946, 12066, 34952], [15, 4593, 17476, 34952, 61680], [240, 256, 3840, 34952, 62532], [240, 3840, 17476, 34952, 61696], [240, 3840, 17476, 34952, 65280], [240, 3840, 34952, 62532, 65280], [496, 3840, 17476, 34952, 61440], [3840, 4080, 17476, 34952, 61440], [3840, 4080, 34952, 61440, 62532], [3840, 4080, 34952, 62532], [3840, 4369, 8751, 17652, 34952, 61440], [3840, 17476, 34952, 61440, 65520], [3840, 17476, 34952, 61680, 65280], [3840, 34952, 61440, 62532, 65520], [4080, 17476, 34952, 61440, 65280], [4080, 17476, 34952, 65280], [17476, 34952, 61440, 65280, 65520]], [[15, 240, 12274, 17476, 34952], [15, 4080, 8946, 17476, 34952], [15, 13107, 13299, 34952, 61440], [3840, 4383, 8738, 17652, 34952, 61440]], [[15, 3840, 4369, 8738, 17652, 63624], [15, 3840, 13107, 17652, 34952, 61440]], [[15, 4080, 17476, 17652, 34952], [15, 8946, 12274, 17476, 34952]], [], [[15, 240, 3840, 13107, 34959], [15, 240, 4369, 8738, 36751], [15, 17476, 30583, 30711, 61440], [255, 3840, 4369, 8738, 34959]], [[15, 128, 4369, 8738, 16384], [15, 3840, 35064, 48059, 61440], [15, 4369, 8738, 32896, 61440], [2048, 4369, 8738, 34959, 61440], [3840, 4369, 8738, 34959, 65280], [3840, 4369, 8738, 36751, 61440]], [[15, 240, 17476, 34952, 36856], [15, 240, 17476, 35064, 36744], [255, 3840, 17476, 34952, 35064]], [[3840, 17476, 34952, 35064, 65280], [3840, 17476, 34952, 36856, 61440], [3840, 17476, 34952, 61440, 65528], [3840, 17476, 35064, 36744, 61440]], [], [], [], [], [[15, 240, 3855, 13107, 34952], [15, 240, 3855, 17476, 30583], [15, 255, 3840, 13107, 34952], [15, 255, 3840, 17476, 30583], [15, 255, 4369, 8738, 36744], [15, 17476, 34952, 57582, 61440], [255, 3855, 4369, 8738, 34952]], [[15, 240, 1092, 4095, 34952], [15, 240, 4095, 17476, 34952], [15, 240, 4095, 34952, 62532], [15, 240, 8191, 17476, 34952], [15, 240, 12287, 17476, 34952], [15, 240, 17476, 34952, 36863], [15, 240, 17476, 34952, 49151], [15, 240, 17476, 34952, 61951], [15, 240, 17476, 34952, 64511], [15, 240, 34952, 48059, 63624], [15, 255, 4080, 17476, 34952], [15, 2048, 4369, 34952, 61986], [15, 2048, 8738, 34952, 61713], [15, 2048, 13107, 34952, 61440], [15, 2048, 17476, 30583, 61440], [15, 3840, 4369, 36744, 61986], [15, 3840, 8738, 36744, 61713], [15, 3840, 13107, 34952, 65280], [15, 3840, 13107, 36744, 61440], [15, 3840, 17476, 30583, 65280], [15, 4080, 17476, 34952, 61695], [15, 4095, 17476, 34952, 61680], [15, 4369, 8738, 32904, 61440], [15, 4369, 8738, 34952, 63488], [15, 4369, 8738, 36744, 65280], [15, 4369, 10786, 34952, 61440], [15, 6417, 8738, 34952, 61440], [240, 255, 3855, 17476, 34952], [240, 3855, 17476, 34952, 61695], [240, 4095, 17476, 34952, 61455], [3840, 3855, 4369, 34952, 61986], [3840, 3855, 8738, 34952, 61713], [3840, 3855, 13107, 34952, 61440], [3840, 3855, 17476, 30583, 61440], [3840, 13107, 34952, 61440, 65295], [3840, 17476, 30583, 61440, 65295], [3855, 4369, 8738, 34952, 65280]], [[4, 240, 17487, 34952, 61440], [8, 240, 17476, 34959, 61440], [15, 240, 1024, 17476, 34952], [15, 240, 1024, 17476, 35976], [15, 240, 1024, 34952, 62532], [15, 240, 1092, 34952], [15, 240, 1092, 34952, 61440], [15, 240, 1536, 17476, 34952], [15, 240, 3072, 17476, 34952], [15, 240, 3584, 17476, 34952], [15, 240, 4369, 8738, 40857], [15, 240, 4369, 34952, 62259], [15, 240, 4369, 39321, 61986], [15, 240, 7953, 13107, 34952], [15, 240, 7953, 17476, 30583], [15, 240, 13107, 34952, 61713], [15, 240, 13107, 39321, 61440], [15, 240, 16384, 17476, 34952], [15, 240, 16384, 17476, 51336], [15, 240, 17476, 20480, 34952], [15, 240, 17476, 24576, 34952], [15, 240, 17476, 28672, 34952], [15, 240, 17476, 30583, 61713], [15, 240, 17476, 34952, 49152], [15, 240, 17476, 34952, 53248], [15, 240, 17476, 34952, 57344], [15, 240, 17476, 34952, 61440], [15, 240, 17476, 34952, 61952], [15, 240, 17476, 34952, 63488], [15, 240, 17476, 35976], [15, 240, 17476, 35976, 61440], [15, 240, 17476, 51336], [15, 240, 17476, 51336, 61440], [15, 240, 19524, 34952, 61440], [15, 240, 21572, 34952, 61440], [15, 240, 25668, 34952, 61440], [15, 240, 34952, 50244, 61440], [15, 240, 34952, 61440, 62532], [15, 240, 34952, 61713, 62259], [15, 496, 3840, 17476, 34952], [15, 752, 17476, 34952, 61440], [15, 1024, 1264, 17476, 34952], [15, 1264, 17476, 34952], [15, 1264, 17476, 34952, 61440], [15, 3840, 4080, 17476, 34952], [15, 3840, 4080, 34952, 62532], [15, 4080, 17476, 34952, 65280], [15, 4336, 17476, 34952, 61440], [15, 4593, 17476, 34952, 61695], [15, 8432, 17476, 34952, 61440], [15, 16384, 16624, 17476, 34952], [15, 16624, 17476, 34952, 61440], [15, 17476, 33008, 34952, 61440], [15, 17476, 34952, 61440, 61680], [15, 34952, 61440, 61680, 62532], [240, 271, 3840, 17476, 34952], [240, 1024, 1039, 17476, 34952], [240, 3840, 3855, 17476, 34952], [240, 3840, 3855, 34952, 62532], [240, 3840, 34952, 62532, 65295], [240, 3855, 17476, 34952, 65280], [240, 4111, 17476, 34952, 61440], [240, 8207, 17476, 34952, 61440], [240, 16384, 16399, 17476, 34952], [240, 16399, 17476, 34952], [240, 16399, 17476, 34952, 61440], [240, 17476, 32783, 34952, 61440], [240, 17476, 34952, 61440, 61455], [240, 34952, 61440, 61455, 62532], [240, 34952, 61455, 62532], [3840, 17476, 34952, 61455, 65520], [3840, 17476, 34952, 61680, 65295], [3855, 4080, 17476, 34952], [3855, 4080, 17476, 34952, 61440], [3855, 17476, 34952, 61440, 65520], [4080, 17476, 34952, 61440, 65295], [17476, 34952, 61440, 61455, 61680], [17476, 34952, 61440, 65295, 65520], [17476, 34952, 61455, 61680]], [[15, 240, 17476, 34952, 61441], [15, 241, 17476, 34952, 61440], [15, 3840, 4593, 17476, 34952], [15, 3840, 8177, 17476, 34952], [15, 4095, 8946, 17476, 34952], [240, 255, 7953, 17476, 34952], [240, 255, 17476, 34952, 61713], [240, 4369, 34952, 61695, 62532], [255, 4369, 17476, 34952, 61680]], [[15, 240, 17476, 34952, 61442], [15, 242, 17476, 34952, 61440], [15, 1024, 8946, 17476, 34952], [15, 3840, 12274, 17476, 34952], [15, 4369, 8946, 48059, 61440], [15, 8946, 16384, 17476, 34952], [15, 8946, 17476, 34952, 61440], [15, 8946, 34952, 61440, 62532], [15, 17476, 34952, 61440, 62194], [240, 3840, 4369, 34952, 62532], [240, 3840, 7953, 34952, 62532], [240, 3840, 8738, 30583, 62532], [240, 3840, 13107, 43690, 61440], [240, 3840, 34952, 61713, 62532], [240, 7953, 17476, 34952, 65280], [240, 17476, 34952, 61713, 65280], [3840, 3855, 8946, 17476, 34952], [3840, 17476, 34952, 61680, 61713], [4080, 7953, 17476, 34952, 61440], [4369, 17476, 34952, 61680, 65280], [7953, 17476, 34952, 61440, 65520], [8946, 17476, 34952, 61440, 61455]], [[15, 3840, 13299, 17476, 34952], [15, 4095, 17476, 17652, 34952], [240, 4080, 8738, 34952, 62532], [240, 17476, 34952, 61986, 65520], [4080, 8738, 17476, 34952, 61680]], [[15, 240, 1028, 17476, 34952], [15, 240, 16388, 17476, 34952], [15, 240, 17476, 34952, 61444], [15, 240, 17476, 34956, 61440], [15, 244, 17476, 34952, 61440], [15, 16384, 17476, 17652, 34952], [15, 17476, 17652, 34952, 61440], [15, 17476, 34952, 61440, 62708], [15, 17652, 34952, 61440, 62532], [15, 34952, 61440, 62532, 62708], [17476, 17652, 34952, 61440, 61455]], [], [[15, 17476, 26358, 34952, 61440]], [[3840, 34952, 34959, 48059, 61440]], [[7, 3840, 17476, 34952, 61440], [15, 240, 17476, 34952, 61448], [15, 240, 17484, 34952, 61440], [15, 248, 17476, 34952, 61440], [3840, 4369, 8738, 34959, 61713], [3840, 4369, 13107, 34959, 61440]], [], [[3840, 4369, 34952, 35064, 62532], [3840, 8738, 35064, 48059, 61440], [3840, 17476, 35064, 39321, 61440]], [], [], [], [[15, 255, 4095, 17476, 34952], [15, 3840, 13107, 34952, 65295], [15, 3840, 17476, 30583, 65295], [15, 4095, 17476, 34952, 61695], [15, 4369, 8738, 36744, 65295]], [[15, 240, 1039, 17476, 34952], [15, 240, 16399, 17476, 34952], [15, 240, 17476, 34952, 61455], [15, 240, 34952, 61455, 62532], [15, 255, 1024, 17476, 34952], [15, 255, 16384, 17476, 34952], [15, 255, 17476, 34952, 61440], [15, 255, 34952, 61440, 62532], [15, 1092, 3840, 4095, 34952], [15, 3840, 4095, 17476, 34952], [15, 3840, 4095, 34952, 62532], [15, 3840, 4607, 17476, 34952], [15, 3840, 8191, 17476, 34952], [15, 3840, 12287, 17476, 34952], [15, 3855, 4080, 17476, 34952], [15, 4080, 17476, 34952, 65295], [15, 4095, 17476, 34952, 65280], [15, 8959, 17476, 34952, 61440], [15, 17476, 17663, 34952, 61440], [15, 17476, 34952, 61440, 61695], [15, 17476, 34952, 61440, 62207], [15, 17476, 34952, 61440, 62719], [15, 17476, 34952, 61455, 61680], [15, 17487, 17652, 34952, 61440], [15, 34952, 61440, 61695, 62532], [255, 3840, 3855, 17476, 34952], [255, 3840, 17476, 34952, 65295], [255, 17476, 34952, 61440, 61455], [255, 17476, 34952, 61455], [3840, 4095, 17476, 34952, 61455], [3840, 4369, 8946, 17487, 34952], [17476, 34952, 61440, 61455, 61695]], [[4, 3840, 17487, 34952, 61440], [15, 128, 17476, 34952, 61568], [15, 128, 17604, 34952, 61440], [15, 240, 17476, 34952, 61456], [15, 240, 17476, 34968, 61440], [15, 240, 34952, 36744, 52428], [15, 1024, 17476, 34952, 65280], [15, 1092, 3840, 34952, 61440], [15, 2048, 17476, 36744, 61440], [15, 2304, 17476, 34952, 61440], [15, 2816, 17476, 34952, 61440], [15, 3328, 17476, 34952, 61440], [15, 3840, 4369, 34952, 62259], [15, 3840, 4369, 39321, 61986], [15, 3840, 13107, 34952, 61713], [15, 3840, 13107, 39321, 61440], [15, 3840, 17476, 30583, 61713], [15, 3840, 17476, 32768, 63624], [15, 3840, 17476, 34952, 49152], [15, 3840, 17476, 34952, 53248], [15, 3840, 17476, 34952, 57344], [15, 3840, 17476, 34952, 61440], [15, 3840, 17476, 34952, 61952], [15, 3840, 17476, 34952, 62464], [15, 3840, 17476, 34952, 63488], [15, 3840, 17476, 35976, 61440], [15, 3840, 17476, 51336, 61440], [15, 3840, 19524, 34952, 61440], [15, 3840, 21572, 34952, 61440], [15, 3840, 25668, 34952, 61440], [15, 3840, 34952, 50244, 61440], [15, 3840, 34952, 61440, 62532], [15, 3840, 34952, 61713, 62259], [15, 3855, 4593, 17476, 34952], [15, 7936, 17476, 34952, 61440], [15, 12032, 17476, 34952, 61440], [15, 16384, 17476, 34952, 65280], [15, 17476, 20224, 34952, 61440], [15, 17476, 34952, 36608, 61440], [15, 17476, 34952, 61440, 65280], [15, 34952, 61440, 62532, 65280], [31, 240, 17476, 34952, 61440], [128, 143, 17476, 34952, 61440], [240, 3840, 4383, 34952, 62532], [527, 3840, 17476, 34952, 61440], [1039, 3840, 17476, 34952, 61440], [2063, 3840, 17476, 34952, 61440], [3840, 3855, 17476, 34952, 65280], [3840, 4111, 17476, 34952, 61440], [3840, 8207, 17476, 34952, 61440], [3840, 16399, 17476, 34952, 61440], [3840, 17476, 32783, 34952, 61440], [3840, 17476, 34952, 61440, 61455], [3840, 17476, 34952, 65280, 65295], [3840, 34952, 61440, 61455, 62532], [3840, 34952, 61455, 62532], [17476, 34952, 61440, 61455, 65280], [17476, 34952, 61455, 65280]], [[15, 240, 3840, 13107, 43690], [15, 240, 4369, 8738, 44970], [15, 240, 8738, 13107, 36744], [15, 240, 12066, 13107, 34952], [15, 240, 12066, 17476, 30583], [15, 3840, 17476, 34952, 61441], [15, 3841, 17476, 34952, 61440], [15, 4080, 7953, 17476, 34952], [15, 8946, 17476, 34952, 61455]], [[15, 3840, 17476, 34952, 61442], [15, 3842, 17476, 34952, 61440], [15, 4593, 7953, 17476, 34952], [15, 4593, 8738, 48059, 61440], [15, 4593, 17476, 34952, 61713], [15, 4593, 17476, 39321, 61440], [15, 7953, 8177, 17476, 34952], [15, 17476, 34952, 61713, 61937], [240, 255, 12066, 17476, 34952], [255, 4080, 8738, 17476, 34952]], [[15, 4369, 8946, 17476, 36744], [15, 17476, 17652, 34952, 61455], [240, 3840, 12066, 34952, 62532], [240, 12066, 17476, 34952, 65280], [3840, 4080, 8738, 34952, 62532], [3840, 17476, 34952, 61986, 65520], [4080, 8738, 17476, 34952, 65280], [4080, 12066, 17476, 34952, 61440], [12066, 17476, 34952, 61440, 65520]], [[15, 192, 17476, 52428, 61440], [15, 3840, 17476, 34952, 61444], [15, 3840, 17476, 34956, 61440], [15, 3844, 17476, 34952, 61440]], [], [], [], [[15, 128, 17476, 34952, 63624], [15, 128, 34952, 52428, 61440], [15, 3840, 17476, 34952, 61448], [15, 3840, 17484, 34952, 61440], [15, 3848, 17476, 34952, 61440]], [], [], [[15, 17476, 34952, 47883, 61440]], [], [[15, 17476, 34952, 56589, 61440]], [[15, 255, 17476, 34952, 61455], [15, 3840, 17476, 34952, 60942], [15, 3855, 4095, 17476, 34952], [15, 4095, 17476, 34952, 65295], [15, 17476, 34952, 61455, 61695]], [[15, 1024, 17476, 34952, 65295], [15, 3840, 17476, 34952, 61455], [15, 3840, 34952, 61455, 62532], [15, 3855, 17476, 34952, 61440], [15, 3855, 34952, 61440, 62532], [15, 16384, 17476, 34952, 65295], [15, 17476, 34952, 61440, 65295], [15, 17476, 34952, 61455, 65280], [15, 34952, 61440, 62532, 65295], [3840, 3855, 17476, 34952, 65295], [3840, 4593, 8738, 17487, 34952], [3855, 17476, 34952, 61440, 61455], [3855, 17476, 34952, 61455], [17476, 34952, 61440, 61455, 65295]], [[15, 240, 17476, 34952, 61472], [15, 240, 17476, 34984, 61440], [15, 3840, 17476, 34952, 61456], [15, 3840, 17476, 34968, 61440], [15, 3856, 17476, 34952, 61440], [15, 4095, 7953, 17476, 34952], [47, 240, 17476, 34952, 61440], [255, 3855, 4369, 17476, 34952]], [[15, 2048, 17476, 34952, 61713], [15, 4369, 17476, 34952, 63488], [15, 4369, 19524, 34952, 61440], [15, 6417, 17476, 34952, 61440], [15, 7953, 17476, 34952, 61440], [15, 7953, 34952, 61440, 62532], [15, 17476, 34952, 61440, 65297], [3840, 3855, 17476, 34952, 61713], [3840, 4369, 34952, 62532, 65295], [3855, 4369, 17476, 34952, 65280], [7953, 17476, 34952, 61440, 61455]], [[15, 240, 1092, 8738, 34952], [15, 240, 4369, 8738, 49083], [15, 240, 8738, 17476, 35976], [15, 240, 8738, 17476, 51336], [15, 240, 9762, 17476, 34952], [15, 240, 13107, 16179, 34952], [15, 240, 13107, 34952, 62259], [15, 240, 13107, 48059, 61440], [15, 240, 17476, 25122, 34952], [15, 240, 17476, 34952, 61986], [15, 240, 21845, 34952, 61713], [15, 240, 21845, 39321, 61440], [15, 240, 34952, 61713, 62805], [15, 240, 34952, 61986, 62532], [15, 1264, 8738, 17476, 34952], [15, 4080, 12066, 17476, 34952], [15, 17476, 34952, 61680, 61986], [240, 8738, 16399, 17476, 34952], [240, 8738, 34952, 61455, 62532], [3855, 4080, 8738, 17476, 34952], [8738, 17476, 34952, 61455, 61680]], [[15, 4593, 8738, 17476, 36744], [15, 4593, 12066, 17476, 34952]], [[15, 8946, 17476, 34952, 61986], [15, 8946, 17476, 43690, 61440], [15, 12066, 12274, 17476, 34952], [15, 17476, 34952, 61986, 62194], [240, 3840, 13107, 34952, 62532], [240, 3840, 17476, 30583, 62532]], [[240, 3840, 17476, 52428, 61680], [240, 4080, 17476, 34952, 62532], [240, 4080, 17476, 52428, 61440], [240, 17476, 52428, 61440, 65520]], [[15, 17476, 17652, 34952, 61986]], [], [], [], [], [], [[3840, 17476, 35064, 48059, 61440]], [], [[15, 3855, 17476, 34952, 61455], [15, 17476, 34952, 61455, 65295]], [[15, 240, 17476, 34952, 61999], [15, 7967, 17476, 34952, 61440], [15, 17476, 34952, 61440, 65311], [240, 3840, 13107, 17487, 34952], [240, 3840, 17476, 17487, 30583], [240, 4369, 12066, 17487, 34952]], [[15, 3840, 17476, 34952, 61472], [15, 3840, 17476, 34984, 61440], [15, 3872, 17476, 34952, 61440], [15, 7953, 17476, 34952, 61455], [240, 3840, 13119, 17476, 34952, 61440], [240, 4080, 17476, 17487, 34952]], [[15, 255, 17476, 34952, 61986], [15, 4095, 12066, 17476, 34952], [15, 17476, 34952, 61695, 61986], [240, 3840, 4369, 8751, 17476, 63624], [240, 4369, 8751, 17476, 36744, 61440], [240, 4369, 8751, 20292, 34952, 61440], [255, 8738, 17476, 34952, 61455]], [[15, 3840, 13107, 34952, 62259], [15, 3840, 13107, 48059, 61440], [15, 3840, 17476, 34952, 61986], [15, 3840, 21845, 34952, 61713], [15, 3840, 21845, 39321, 61440], [15, 3840, 34952, 61713, 62805], [15, 3840, 34952, 61986, 62532], [15, 4369, 8738, 45243, 61440], [15, 12066, 17476, 34952, 61440], [15, 12066, 34952, 61440, 62532], [15, 17476, 34952, 61440, 65314], [15, 17476, 34952, 61986, 65280], [240, 3840, 4383, 8738, 17476, 63624], [240, 4383, 8738, 17476, 36744, 61440], [240, 4383, 8738, 20292, 34952, 61440], [3840, 8738, 34952, 61455, 62532], [8738, 17476, 34952, 61455, 65280], [12066, 17476, 34952, 61440, 61455]], [[15, 240, 3840, 13107, 17476, 63624], [15, 240, 13107, 17476, 36744], [15, 240, 13107, 17476, 36744, 61440], [15, 240, 13107, 20292, 34952, 61440]], [[15, 240, 4080, 17476, 52428], [240, 255, 3840, 17476, 52428]]]
  | 6 => [[[240, 3840, 17476, 20292, 34952, 61440]], [], [], [], [], [], [[15, 128, 4369, 8738, 17476, 61440]], [], [], [], [[15, 3840, 8751, 17476, 34952, 61440]], [[15, 64, 240, 17476, 34952, 61440]], [[15, 3840, 8738, 17476, 34952, 61455], [15, 3855, 8738, 17476, 34952, 61440], [15, 8738, 17476, 34952, 61440, 65295]], [], [[15, 7953, 8738, 17476, 34952, 61440]], [[15, 240, 3840, 17476, 20292, 34952], [15, 240, 8738, 17476, 34952, 61986], [15, 240, 8738, 17476, 43690, 61440], [15, 240, 8738, 26214, 34952, 61440], [15, 240, 17476, 34952, 61440, 62532], [15, 240, 17476, 52428, 61440]], [], [[240, 3840, 4369, 17476, 34952, 62532], [240, 3840, 4369, 17476, 52428, 61440], [240, 3840, 17476, 21845, 34952, 61440]], [], [], [], [], [], [], [], [], [[15, 240, 17476, 17487, 34952, 61440]], [[15, 64, 3840, 17476, 34952, 61440]], [[240, 3840, 4369, 17476, 17487, 34952]], [], [], [[15, 3840, 8738, 17476, 34952, 61986], [15, 3840, 8738, 17476, 43690, 61440], [15, 3840, 8738, 26214, 34952, 61440], [15, 3840, 17476, 34952, 61440, 62532], [15, 3840, 17476, 52428, 61440], [15, 8738, 12066, 17476, 34952, 61440], [15, 17476, 20292, 34952, 61440]], [[15, 240, 3840, 4369, 17476, 52428], [15, 240, 3840, 17476, 21845, 34952]], [], [], [], [], [], [], [], [], [], [[15, 3840, 17476, 17487, 34952, 61440]], [], [], [], [], [], [], [[15, 240, 4369, 17476, 56797, 61440], [15, 240, 8738, 17476, 52428, 61440], [15, 240, 17476, 26214, 34952, 61440]], [], [[240, 3840, 4369, 34952, 43690, 61440], [240, 3840, 8738, 34952, 39321, 61440], [240, 3840, 17476, 30583, 34952, 61440], [240, 3840, 34952, 48059, 61440]], [], [], [], [[240, 3840, 4369, 8946, 17476, 61440]], [], [], [], [[15, 240, 17476, 35064, 61440]], [[3840, 17476, 35064, 61440]], [[240, 3840, 4369, 17476, 35064, 61440]], [], [], [], [[15, 3840, 4369, 17476, 56797, 61440], [15, 3840, 8738, 17476, 52428, 61440], [15, 3840, 17476, 26214, 34952, 61440], [15, 8738, 17476, 20292, 34952, 61440]], [[15, 240, 3840, 4369, 34952, 43690], [15, 240, 3840, 8738, 34952, 39321], [15, 240, 3840, 17476, 30583, 34952], [15, 240, 3840, 34952, 48059], [15, 240, 3840, 34952, 48059, 61440], [15, 240, 4369, 8738, 34952, 36744]], [], [[240, 3840, 17476, 34952, 36744, 61440]], [], [[15, 240, 3840, 4369, 8946, 17476]], [[240, 3840, 4593, 8738, 17476, 61440]], [], [], [[15, 128, 4369, 8738, 34952, 61440]], [[15, 128, 240, 17476, 34952, 61440], [15, 3840, 17476, 35064, 61440]], [[15, 240, 3840, 4369, 17476, 35064]], [], [], [], [], [], [], [[15, 240, 3840, 17476, 34952, 36744], [15, 240, 4369, 34952, 48059, 61440], [15, 240, 8738, 17476, 61166, 61440], [15, 240, 17476, 34952, 61440, 63624], [15, 240, 17476, 34952, 63624], [15, 240, 34952, 52428, 61440]], [], [[240, 3840, 4369, 34952, 52428, 61440], [240, 3840, 8738, 34952, 48059, 61440], [240, 3840, 17476, 34952, 39321, 61440]], [[15, 240, 3840, 4593, 8738, 17476], [15, 4369, 8946, 17476, 61440]], [[240, 3840, 4369, 8738, 17476, 61680], [240, 4080, 4369, 8738, 17476, 61440], [240, 4369, 8738, 17476, 61440, 65520]], [], [], [[15, 240, 17476, 34952, 34959, 61440]], [[15, 128, 3840, 17476, 34952, 61440], [3840, 17476, 34952, 34959, 61440]], [], [[15, 240, 8738, 17476, 35064, 61440]], [[3840, 8738, 17476, 35064, 61440]], [], [], [], [], [[15, 3840, 4369, 34952, 48059, 61440], [15, 3840, 8738, 17476, 61166, 61440], [15, 3840, 17476, 34952, 61440, 63624], [15, 3840, 34952, 52428, 61440]], [[15, 240, 3840, 4369, 34952, 52428], [15, 240, 3840, 8738, 34952, 48059], [15, 240, 3840, 17476, 34952, 39321], [15, 240, 4369, 17476, 34952, 36744]], [], [[15, 240, 4080, 4369, 8738, 17476], [15, 4593, 8738, 17476, 61440], [240, 255, 3840, 4369, 8738, 17476]], [[240, 3840, 4369, 8738, 17476, 65280], [240, 3840, 4369, 8738, 20292, 61440], [3840, 4080, 4369, 8738, 17476, 61440], [3840, 4369, 8738, 17476, 61440, 65520]], [], [], [[15, 3840, 17476, 34952, 34959, 61440]], [], [[15, 128, 4369, 17476, 34952, 61440]], [[15, 3840, 8738, 17476, 35064, 61440]], [], [], [], [], [], [], [], [[15, 240, 4095, 4369, 8738, 17476], [15, 240, 4369, 34952, 56797, 61440], [15, 240, 8738, 17476, 34952, 63624], [15, 240, 8738, 34952, 52428, 61440], [15, 240, 17476, 34952, 43690, 61440]], [[15, 240, 1024, 4369, 8738, 17476], [15, 240, 3840, 4369, 8738, 20292], [15, 240, 4369, 8738, 16384, 17476], [15, 240, 4369, 8738, 17476, 61440], [15, 240, 13107, 17476, 61440], [15, 3840, 4080, 4369, 8738, 17476], [15, 4369, 8738, 17476, 61440, 61680], [240, 3840, 3855, 4369, 8738, 17476], [240, 4369, 8738, 17476, 61440, 61455]], [[15, 3840, 4369, 4593, 8738, 17476], [240, 3840, 17476, 34952, 48059, 61440]], [[15, 4369, 8738, 8946, 17476, 61440], [240, 3840, 4369, 8738, 21845, 61440], [240, 3840, 4369, 13107, 17476, 61440]], [], [[15, 4369, 8738, 17476, 17652, 61440]], [], [], [[3840, 8738, 17476, 34952, 34959, 61440]], [], [], [], [[15, 240, 4369, 8738, 17487, 61440]], [], [], [], [[15, 240, 4369, 8738, 17476, 61455], [15, 255, 4369, 8738, 17476, 61440], [15, 3840, 4095, 4369, 8738, 17476], [15, 3840, 4369, 34952, 56797, 61440], [15, 3840, 8738, 34952, 52428, 61440], [15, 3840, 17476, 34952, 43690, 61440], [15, 4369, 8738, 17476, 61440, 61695]], [[15, 240, 3840, 17476, 34952, 48059], [15, 3840, 4369, 8738, 17476, 61440], [15, 3840, 13107, 17476, 61440], [15, 4369, 8738, 17476, 61440, 65280], [15, 4369, 8738, 20292, 61440], [3840, 4369, 8738, 17476, 61440, 61455]], [[15, 240, 3840, 4369, 8738, 21845], [15, 240, 3840, 4369, 13107, 17476]], [], [], [], [], [], [], [], [], [], [[15, 3840, 4369, 8738, 17487, 61440]], [], [], [], [[15, 3840, 4369, 8738, 17476, 61455], [15, 3855, 4369, 8738, 17476, 61440], [15, 4369, 8738, 17476, 61440, 65295]], [], [[15, 240, 8738, 34952, 61166, 61440], [15, 240, 17476, 34952, 52428, 61440], [15, 4369, 7953, 8738, 17476, 61440]], [[15, 240, 4369, 8738, 17476, 61986], [15, 240, 4369, 8738, 26214, 61440], [15, 240, 8738, 13107, 17476, 61440]], [[240, 3840, 17476, 34952, 56797, 61440]], [[240, 3840, 4369, 8738, 30583, 61440]], [[240, 3840, 4369, 8738, 34952, 61680], [240, 4080, 4369, 8738, 34952, 61440], [240, 4369, 8738, 34952, 61440, 65520]], [], [], [], [], [], [], [], [], [], [], [], [[15, 3840, 8738, 34952, 61166, 61440], [15, 3840, 17476, 34952, 52428, 61440]], [[15, 240, 3840, 17476, 34952, 56797], [15, 3840, 4369, 8738, 17476, 61986], [15, 3840, 4369, 8738, 26214, 61440], [15, 3840, 8738, 13107, 17476, 61440], [15, 4369, 8738, 12066, 17476, 61440]], [[15, 240, 3840, 4369, 8738, 30583]], [[15, 240, 4080, 4369, 8738, 34952], [240, 255, 3840, 4369, 8738, 34952]], [[240, 3840, 4369, 8738, 34952, 65280], [240, 3840, 4369, 8738, 36744, 61440], [3840, 4080, 4369, 8738, 34952, 61440], [3840, 4369, 8738, 34952, 61440, 65520]], [[240, 3840, 4080, 17476, 34952, 61440], [240, 3840, 17476, 34952, 61440, 65520], [240, 3840, 17476, 34952, 65520]], [[240, 3840, 4593, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 4095, 4369, 8738, 34952], [15, 240, 17476, 34952, 61166, 61440]], [[15, 240, 1024, 4369, 8738, 34952], [15, 240, 3840, 4369, 8738, 36744], [15, 240, 4369, 8738, 16384, 34952], [15, 240, 4369, 8738, 34952, 61440], [15, 240, 4369, 17476, 26214, 61440], [15, 240, 4369, 34952, 61440, 61986], [15, 240, 4369, 34952, 61986], [15, 240, 8738, 17476, 21845, 61440], [15, 240, 8738, 34952, 61440, 61713], [15, 240, 8738, 34952, 61713], [15, 240, 13107, 34952, 61440], [15, 240, 17476, 30583, 61440], [15, 3840, 4080, 4369, 8738, 34952], [15, 4369, 8738, 34952, 61440, 61680], [240, 3840, 3855, 4369, 8738, 34952], [240, 4369, 8738, 34952, 61440, 61455]], [[15, 240, 3840, 4080, 17476, 34952], [15, 240, 3840, 17476, 34952, 65520], [15, 240, 17476, 34952, 61440, 61680], [15, 240, 17476, 34952, 61680], [15, 3840, 4369, 4593, 8738, 34952], [240, 255, 17476, 34952, 61440], [240, 3840, 4095, 17476, 34952], [240, 3840, 4095, 17476, 34952, 61440], [240, 17476, 34952, 61440, 61695]], [[15, 240, 3840, 4593, 17476, 34952], [15, 4369, 8738, 8946, 34952, 61440], [240, 512, 3840, 17476, 34952, 61440], [240, 1024, 3840, 17476, 34952, 61440], [240, 2048, 3840, 17476, 34952, 61440], [240, 3840, 4096, 17476, 34952, 61440], [240, 3840, 4369, 8738, 39321, 61440], [240, 3840, 4369, 13107, 34952, 61440], [240, 3840, 4369, 17476, 30583, 61440], [240, 3840, 8192, 17476, 34952, 61440], [240, 3840, 16384, 17476, 34952, 61440], [240, 3840, 17476, 32768, 34952, 61440], [240, 3840, 17476, 34952, 61440], [240, 3840, 34952, 61440, 62532], [240, 3840, 34952, 62532], [240, 17476, 34952, 61440, 65280], [3840, 17476, 34952, 61440, 61680]], [[1, 240, 3840, 17476, 34952, 61440], [15, 240, 8946, 17476, 34952, 61440], [240, 3840, 4369, 17476, 34952, 61680], [240, 4080, 4369, 17476, 34952, 61440], [240, 4369, 17476, 34952, 61440, 65520]], [[2, 240, 3840, 17476, 34952, 61440], [15, 4369, 8738, 17652, 34952, 61440]], [[15, 240, 17476, 17652, 34952, 61440]], [[4, 240, 3840, 17476, 34952, 61440]], [[15, 240, 4369, 8738, 34959, 61440]], [[3840, 4369, 8738, 34959, 61440]], [[15, 240, 17476, 34952, 35064, 61440]], [[8, 240, 3840, 17476, 34952, 61440], [3840, 17476, 34952, 35064, 61440]], [], [], [], [], [[15, 240, 4369, 8738, 34952, 61455], [15, 255, 4369, 8738, 34952, 61440], [15, 3840, 4095, 4369, 8738, 34952], [15, 3840, 17476, 34952, 61166, 61440], [15, 4369, 8738, 34952, 61440, 61695]], [[15, 240, 255, 17476, 34952, 61440], [15, 240, 3840, 4095, 17476, 34952], [15, 240, 17476, 34952, 61440, 61695], [15, 240, 17476, 34952, 61695], [15, 3840, 4369, 8738, 34952, 61440], [15, 3840, 4369, 17476, 26214, 61440], [15, 3840, 4369, 34952, 61440, 61986], [15, 3840, 4369, 34952, 61986], [15, 3840, 8738, 17476, 21845, 61440], [15, 3840, 8738, 34952, 61440, 61713], [15, 3840, 8738, 34952, 61713], [15, 3840, 13107, 34952, 61440], [15, 3840, 17476, 30583, 61440], [15, 4369, 8738, 17476, 20292, 61440], [15, 4369, 8738, 34952, 61440, 65280], [3840, 4369, 8738, 34952, 61440, 61455]], [[15, 240, 256, 17476, 34952, 61440], [15, 240, 512, 3840, 17476, 34952], [15, 240, 1024, 3840, 17476, 34952], [15, 240, 2048, 3840, 17476, 34952], [15, 240, 3840, 4096, 17476, 34952], [15, 240, 3840, 4369, 8738, 39321], [15, 240, 3840, 4369, 13107, 34952], [15, 240, 3840, 4369, 17476, 30583], [15, 240, 3840, 8192, 17476, 34952], [15, 240, 3840, 16384, 17476, 34952], [15, 240, 3840, 17476, 32768, 34952], [15, 240, 3840, 17476, 34952], [15, 240, 3840, 17476, 34952, 61440], [15, 240, 3840, 34952, 61440, 62532], [15, 240, 3840, 34952, 62532], [15, 240, 17476, 34952, 61440, 65280], [15, 3840, 17476, 34952, 61440, 61680], [240, 3840, 17476, 34952, 61440, 61455]], [[1, 15, 240, 3840, 17476, 34952], [15, 240, 4080, 4369, 17476, 34952], [15, 4593, 17476, 34952, 61440], [16, 240, 3840, 17476, 34952, 61440], [240, 255, 3840, 4369, 17476, 34952]], [[2, 15, 240, 3840, 17476, 34952], [15, 3840, 8946, 17476, 34952], [15, 3840, 8946, 17476, 34952, 61440], [240, 3840, 4369, 17476, 34952, 65280], [3840, 4080, 4369, 17476, 34952, 61440], [3840, 4369, 17476, 34952, 61440, 65520]], [[240, 3840, 8738, 17476, 34952, 65520]], [[4, 15, 240, 3840, 17476, 34952], [15, 3840, 17476, 17652, 34952, 61440]], [], [[15, 3840, 4369, 8738, 34959, 61440]], [], [[8, 15, 240, 3840, 17476, 34952], [15, 3840, 17476, 34952, 35064, 61440]], [], [], [], [], [], [[15, 3840, 4369, 8738, 34952, 61455], [15, 3855, 4369, 8738, 34952, 61440], [15, 4369, 8738, 34952, 61440, 65295]], [[15, 240, 3840, 17476, 34952, 61455], [15, 240, 3855, 17476, 34952], [15, 240, 3855, 17476, 34952, 61440], [15, 240, 17476, 34952, 61440, 65295], [15, 255, 3840, 17476, 34952], [15, 255, 3840, 17476, 34952, 61440], [15, 3840, 17476, 34952, 61440, 61695]], [[15, 16, 240, 3840, 17476, 34952], [15, 240, 4095, 4369, 17476, 34952], [15, 256, 3840, 17476, 34952, 61440], [15, 2048, 17476, 34952, 61440], [15, 3840, 17476, 34952, 61440, 65280], [15, 3840, 17476, 34952, 65280], [15, 4369, 7953, 8738, 34952, 61440], [3840, 3855, 17476, 34952, 61440], [3840, 17476, 34952, 61440, 65295]], [[15, 240, 1024, 4369, 17476, 34952], [15, 240, 4369, 8738, 34952, 61986], [15, 240, 4369, 8738, 43690, 61440], [15, 240, 4369, 16384, 17476, 34952], [15, 240, 4369, 17476, 34952, 61440], [15, 240, 4369, 34952, 61440, 62532], [15, 240, 7953, 17476, 34952], [15, 240, 7953, 17476, 34952, 61440], [15, 240, 8738, 13107, 34952, 61440], [15, 240, 8738, 17476, 30583, 61440], [15, 240, 17476, 34952, 61440, 61713], [15, 240, 17476, 34952, 61713], [15, 3840, 4080, 4369, 17476, 34952], [15, 4369, 17476, 34952, 61440, 61680], [32, 240, 3840, 17476, 34952, 61440], [240, 3840, 3855, 4369, 17476, 34952], [240, 4369, 17476, 34952, 61440, 61455]], [[15, 240, 8738, 17476, 34952, 61680], [15, 3840, 4369, 4593, 17476, 34952], [240, 255, 8738, 17476, 34952, 61440], [240, 3840, 4095, 8738, 17476, 34952], [240, 8738, 17476, 34952, 61440, 61695]], [[15, 4369, 8946, 17476, 34952, 61440], [240, 3840, 4369, 8738, 48059, 61440], [240, 3840, 4369, 17476, 39321, 61440], [240, 3840, 4369, 21845, 34952, 61440], [240, 3840, 8738, 17476, 34952, 61440], [240, 3840, 8738, 34952, 61440, 62532], [240, 3840, 8738, 34952, 62532], [240, 3840, 17476, 34952, 61440, 61986], [240, 8738, 17476, 34952, 61440, 65280], [3840, 8738, 17476, 34952, 61440, 61680]], [], [[15, 4369, 17476, 17652, 34952, 61440]], [], [], [], [], [], [[3840, 8738, 17476, 34952, 35064, 61440]], [], [], [], [[15, 240, 4383, 17476, 34952, 61440], [15, 3840, 3855, 17476, 34952, 61440], [15, 3840, 17476, 34952, 61440, 65295], [15, 3840, 17476, 34952, 65295]], [[15, 32, 240, 3840, 17476, 34952], [15, 240, 4369, 17476, 34952, 61455], [15, 255, 4369, 17476, 34952, 61440], [15, 3840, 4095, 4369, 17476, 34952], [15, 4369, 17476, 34952, 61440, 61695], [240, 3840, 8751, 17476, 34952, 61440]], [[15, 240, 8738, 17476, 34952, 61695], [15, 3840, 4369, 8738, 34952, 61986], [15, 3840, 4369, 8738, 43690, 61440], [15, 3840, 4369, 17476, 34952, 61440], [15, 3840, 4369, 34952, 61440, 62532], [15, 3840, 7953, 17476, 34952, 61440], [15, 3840, 8738, 13107, 34952, 61440], [15, 3840, 8738, 17476, 30583, 61440], [15, 3840, 17476, 34952, 61440, 61713], [15, 3840, 17476, 34952, 61713], [15, 4369, 8738, 12066, 34952, 61440], [15, 4369, 17476, 34952, 61440, 65280], [3840, 4369, 17476, 34952, 61440, 61455]], [[15, 240, 3840, 4369, 8738, 48059], [15, 240, 3840, 4369, 17476, 39321], [15, 240, 3840, 4369, 21845, 34952], [15, 240, 3840, 8738, 17476, 34952], [15, 240, 3840, 8738, 34952, 62532], [15, 240, 3840, 17476, 34952, 61986], [15, 240, 12066, 17476, 34952], [15, 240, 12066, 17476, 34952, 61440]], [[15, 4593, 8738, 17476, 34952, 61440]], [[15, 3840, 8738, 8946, 17476, 34952]], [], [], [], [], [], [], [], [], [], [], [[15, 240, 3840, 8751, 17476, 34952], [15, 3840, 4383, 17476, 34952, 61440]], [[15, 3840, 4369, 17476, 34952, 61455], [15, 3855, 4369, 17476, 34952, 61440], [15, 4369, 17476, 34952, 61440, 65295]], [[15, 240, 3855, 8738, 17476, 34952], [15, 255, 3840, 8738, 17476, 34952], [64, 240, 3840, 17476, 34952, 61440]], [[15, 2048, 8738, 17476, 34952, 61440], [15, 3840, 8738, 17476, 34952, 65280], [15, 3840, 12066, 17476, 34952, 61440], [15, 4369, 7953, 17476, 34952, 61440], [3840, 3855, 8738, 17476, 34952, 61440], [3840, 8738, 17476, 34952, 61440, 65295]], [[15, 240, 4369, 8738, 17476, 63624], [15, 240, 4369, 17476, 34952, 61986], [15, 240, 7953, 8738, 17476, 34952], [15, 240, 8738, 17476, 34952, 61713], [15, 240, 13107, 17476, 34952, 61440]], [], [[240, 3840, 8738, 17476, 43690, 61440], [240, 3840, 8738, 26214, 34952, 61440], [240, 3840, 17476, 34952, 61440, 62532], [240, 3840, 17476, 34952, 62532], [240, 3840, 17476, 52428, 61440]], [], [], [], [], [], [[3840, 4369, 8738, 17476, 34959, 61440]], [], [], [], [], [[15, 64, 240, 3840, 17476, 34952], [240, 3840, 17476, 17487, 34952], [240, 3840, 17476, 17487, 34952, 61440]], [[15, 3840, 8738, 17476, 34952, 65295]], [], [[15, 3840, 4369, 17476, 34952, 61986], [15, 3840, 8738, 17476, 34952, 61713], [15, 3840, 13107, 17476, 34952, 61440], [15, 4369, 8738, 20292, 34952, 61440], [15, 4369, 12066, 17476, 34952, 61440]], [[15, 240, 3840, 8738, 17476, 43690], [15, 240, 3840, 8738, 26214, 34952], [15, 240, 3840, 17476, 34952, 62532], [15, 240, 3840, 17476, 52428], [15, 240, 3840, 17476, 52428, 61440], [15, 240, 8738, 12066, 17476, 34952], [15, 240, 17476, 20292, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [[15, 240, 3840, 17476, 17487, 34952]], [], [], [], [], [[15, 3840, 17476, 20292, 34952, 61440]], [[15, 240, 4369, 17476, 52428, 61440], [15, 240, 17476, 21845, 34952, 61440]], [], [[240, 3840, 4369, 17476, 56797, 61440], [240, 3840, 8738, 17476, 34952, 62532], [240, 3840, 8738, 17476, 52428, 61440], [240, 3840, 17476, 26214, 34952, 61440]], [], [], [], [], [], [], [], [], [], [[240, 3840, 17476, 35064, 61440]], [[240, 3840, 8738, 17476, 17487, 34952]], [], [], [[15, 3840, 4369, 17476, 52428, 61440], [15, 3840, 17476, 21845, 34952, 61440], [15, 4369, 17476, 20292, 34952, 61440]], [[15, 240, 3840, 4369, 17476, 56797], [15, 240, 3840, 8738, 17476, 52428], [15, 240, 3840, 17476, 26214, 34952]], [], [], [], [], [], [], [], [], [], [[15, 240, 3840, 17476, 35064], [15, 240, 3840, 17476, 35064, 61440]], [[128, 240, 3840, 17476, 34952, 61440]], [], [], [], [], [], [[15, 240, 4369, 8738, 34952, 63624], [15, 240, 4369, 34952, 43690, 61440], [15, 240, 8738, 34952, 39321, 61440], [15, 240, 17476, 30583, 34952, 61440], [15, 240, 34952, 48059, 61440]], [], [[240, 3840, 4369, 34952, 48059, 61440], [240, 3840, 8738, 17476, 61166, 61440], [240, 3840, 17476, 34952, 61440, 63624], [240, 3840, 34952, 52428, 61440]], [], [[15, 240, 4369, 8946, 17476, 61440]], [], [], [], [[3840, 4369, 8738, 34952, 34959, 61440]], [[15, 128, 240, 3840, 17476, 34952], [240, 3840, 17476, 34952, 34959, 61440]], [[15, 240, 4369, 17476, 35064, 61440]], [[3840, 4369, 17476, 35064, 61440]], [[240, 3840, 8738, 17476, 35064, 61440]], [], [], [], [[15, 3840, 4369, 34952, 43690, 61440], [15, 3840, 8738, 34952, 39321, 61440], [15, 3840, 17476, 30583, 34952, 61440], [15, 3840, 34952, 48059, 61440]], [[15, 240, 3840, 4369, 34952, 48059], [15, 240, 3840, 8738, 17476, 61166], [15, 240, 3840, 17476, 34952, 63624], [15, 240, 3840, 34952, 52428], [15, 240, 3840, 34952, 52428, 61440], [15, 240, 17476, 34952, 36744], [15, 240, 17476, 34952, 36744, 61440]], [], [], [[15, 240, 4593, 8738, 17476, 61440], [15, 3840, 4369, 8946, 17476], [15, 3840, 4369, 8946, 17476, 61440]], [[240, 3840, 4369, 8738, 17476, 65520]], [], [], [[15, 240, 3840, 17476, 34952, 34959]], [[15, 128, 17476, 34952, 61440]], [[15, 3840, 4369, 17476, 35064, 61440]], [[15, 240, 3840, 8738, 17476, 35064]], [], [], [], [], [], [[15, 3840, 17476, 34952, 36744, 61440]], [[15, 240, 4369, 17476, 34952, 63624], [15, 240, 4369, 34952, 52428, 61440], [15, 240, 8738, 34952, 48059, 61440], [15, 240, 17476, 34952, 39321, 61440]], [], [[15, 240, 4369, 8738, 17476, 61680], [15, 3840, 4593, 8738, 17476], [15, 3840, 4593, 8738, 17476, 61440], [240, 255, 4369, 8738, 17476, 61440], [240, 3840, 4095, 4369, 8738, 17476], [240, 3840, 4369, 34952, 56797, 61440], [240, 3840, 8738, 34952, 52428, 61440], [240, 3840, 17476, 34952, 43690, 61440], [240, 4369, 8738, 17476, 61440, 61695]], [[240, 3840, 4369, 8738, 17476, 61440], [240, 3840, 13107, 17476, 61440], [240, 4369, 8738, 17476, 61440, 65280], [3840, 4369, 8738, 17476, 61440, 61680]], [], [], [], [], [[3840, 4369, 17476, 34952, 34959, 61440]], [], [], [[3840, 4369, 8738, 17476, 35064, 61440]], [], [], [[240, 3840, 4369, 8738, 17487], [240, 3840, 4369, 8738, 17487, 61440]], [], [[15, 3840, 4369, 34952, 52428, 61440], [15, 3840, 8738, 34952, 48059, 61440], [15, 3840, 17476, 34952, 39321, 61440]], [[15, 240, 3840, 4369, 34952, 56797], [15, 240, 3840, 8738, 34952, 52428], [15, 240, 3840, 17476, 34952, 43690], [15, 240, 4369, 8738, 17476, 61695], [15, 240, 8738, 17476, 34952, 36744]], [[15, 240, 3840, 4369, 8738, 17476], [15, 240, 3840, 13107, 17476], [15, 240, 3840, 13107, 17476, 61440], [15, 240, 4369, 8738, 20292, 61440]], [[15, 4369, 4593, 8738, 17476, 61440]], [[15, 3840, 4369, 8738, 8946, 17476]], [], [], [], [], [[15, 128, 8738, 17476, 34952, 61440]], [], [], [], [[15, 240, 3840, 4369, 8738, 17487]], [], [], [], [[15, 240, 3855, 4369, 8738, 17476], [15, 255, 3840, 4369, 8738, 17476]], [[15, 240, 17476, 34952, 48059, 61440], [15, 2048, 4369, 8738, 17476, 61440], [15, 3840, 4369, 8738, 17476, 65280], [15, 3840, 4369, 8738, 20292, 61440], [3840, 3855, 4369, 8738, 17476, 61440], [3840, 4369, 8738, 17476, 61440, 65295]], [[15, 240, 4369, 7953, 8738, 17476], [15, 240, 4369, 8738, 17476, 61713], [15, 240, 4369, 8738, 21845, 61440], [15, 240, 4369, 13107, 17476, 61440]], [[240, 3840, 8738, 34952, 61166, 61440], [240, 3840, 17476, 34952, 52428, 61440]], [[240, 3840, 4369, 8738, 26214, 61440], [240, 3840, 8738, 13107, 17476, 61440]], [], [], [], [], [], [], [], [], [], [], [], [[15, 3840, 4369, 8738, 17476, 65295]], [[15, 3840, 17476, 34952, 48059, 61440]], [[15, 240, 3840, 8738, 34952, 61166], [15, 240, 3840, 17476, 34952, 52428], [15, 3840, 4369, 8738, 17476, 61713], [15, 3840, 4369, 8738, 21845, 61440], [15, 3840, 4369, 13107, 17476, 61440]], [[15, 240, 3840, 4369, 8738, 26214], [15, 240, 3840, 8738, 13107, 17476], [15, 240, 4369, 8738, 12066, 17476]], [], [], [[240, 3840, 4369, 8738, 34952, 65520]], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 17476, 34952, 56797, 61440]], [[15, 240, 4369, 8738, 30583, 61440]], [[15, 240, 4369, 8738, 34952, 61680], [240, 255, 4369, 8738, 34952, 61440], [240, 3840, 4095, 4369, 8738, 34952], [240, 3840, 17476, 34952, 61166, 61440], [240, 4369, 8738, 34952, 61440, 61695]], [[240, 3840, 4369, 8738, 17476, 62532], [240, 3840, 4369, 8738, 34952, 61440], [240, 3840, 4369, 17476, 26214, 61440], [240, 3840, 4369, 34952, 61440, 61986], [240, 3840, 8738, 17476, 21845, 61440], [240, 3840, 8738, 34952, 61440, 61713], [240, 3840, 13107, 34952, 61440], [240, 3840, 17476, 30583, 61440], [240, 4369, 8738, 34952, 61440, 65280], [3840, 4369, 8738, 34952, 61440, 61680]], [[240, 3840, 17476, 34952, 61440, 61680], [240, 3840, 17476, 34952, 61680], [240, 4080, 17476, 34952, 61440], [240, 17476, 34952, 61440, 65520]], [], [[240, 3840, 8946, 17476, 34952, 61440]], [], [[240, 3840, 17476, 17652, 34952, 61440]], [], [[240, 3840, 4369, 8738, 34959, 61440]], [[3840, 4369, 8738, 34952, 35064, 61440]], [[240, 3840, 17476, 34952, 35064, 61440]], [], [[240, 3840, 4369, 8738, 17476, 17487]], [], [[15, 3840, 17476, 34952, 56797, 61440]], [[15, 240, 3840, 17476, 34952, 61166], [15, 240, 4369, 8738, 34952, 61695], [15, 3840, 4369, 8738, 30583, 61440]], [[15, 240, 3840, 4369, 8738, 34952], [15, 240, 3840, 4369, 17476, 26214], [15, 240, 3840, 4369, 34952, 61986], [15, 240, 3840, 8738, 17476, 21845], [15, 240, 3840, 8738, 34952, 61713], [15, 240, 3840, 13107, 34952], [15, 240, 3840, 13107, 34952, 61440], [15, 240, 3840, 17476, 30583], [15, 240, 3840, 17476, 30583, 61440], [15, 240, 4369, 8738, 36744], [15, 240, 4369, 8738, 36744, 61440]], [[15, 240, 3840, 17476, 34952, 61680], [15, 240, 4080, 17476, 34952], [15, 240, 4080, 17476, 34952, 61440], [15, 240, 17476, 34952, 61440, 65520], [15, 4369, 4593, 8738, 34952, 61440], [240, 255, 3840, 17476, 34952], [240, 255, 3840, 17476, 34952, 61440], [240, 3840, 17476, 34952, 61440, 61695]], [[15, 240, 4593, 17476, 34952, 61440], [15, 3840, 4369, 8738, 8946, 34952], [240, 256, 3840, 17476, 34952, 61440], [240, 3840, 17476, 34952, 61440, 65280], [240, 3840, 17476, 34952, 65280], [3840, 4080, 17476, 34952, 61440], [3840, 17476, 34952, 61440, 65520]], [[15, 240, 3840, 8946, 17476, 34952], [240, 3840, 4369, 17476, 34952, 65520]], [[15, 3840, 4369, 8738, 17652, 34952, 61440]], [[15, 240, 3840, 17476, 17652, 34952]], [], [[15, 240, 3840, 4369, 8738, 34959]], [], [[15, 240, 3840, 17476, 34952, 35064]], [], [], [], [], [], [[15, 240, 3855, 4369, 8738, 34952], [15, 255, 3840, 4369, 8738, 34952]], [[15, 240, 255, 3840, 17476, 34952], [15, 240, 3840, 17476, 34952, 61695], [15, 240, 4095, 17476, 34952], [15, 240, 4095, 17476, 34952, 61440], [15, 2048, 4369, 8738, 34952, 61440], [15, 3840, 4369, 8738, 34952, 65280], [15, 3840, 4369, 8738, 36744, 61440], [3840, 3855, 4369, 8738, 34952, 61440], [3840, 4369, 8738, 34952, 61440, 65295]], [[15, 240, 256, 3840, 17476, 34952], [15, 240, 512, 17476, 34952, 61440], [15, 240, 1024, 17476, 34952], [15, 240, 1024, 17476, 34952, 61440], [15, 240, 2048, 17476, 34952, 61440], [15, 240, 3840, 17476, 34952, 65280], [15, 240, 4096, 17476, 34952, 61440], [15, 240, 4369, 7953, 8738, 34952], [15, 240, 4369, 8738, 34952, 61713], [15, 240, 4369, 8738, 39321, 61440], [15, 240, 4369, 13107, 34952, 61440], [15, 240, 4369, 17476, 30583, 61440], [15, 240, 8192, 17476, 34952, 61440], [15, 240, 16384, 17476, 34952], [15, 240, 16384, 17476, 34952, 61440], [15, 240, 17476, 32768, 34952, 61440], [15, 240, 17476, 34952, 61440], [15, 240, 34952, 61440, 62532], [15, 3840, 4080, 17476, 34952], [15, 3840, 4080, 17476, 34952, 61440], [15, 3840, 17476, 34952, 61440, 65520], [15, 17476, 34952, 61440, 61680], [240, 3840, 3855, 17476, 34952], [240, 3840, 3855, 17476, 34952, 61440], [240, 3840, 17476, 34952, 61440, 65295], [240, 17476, 34952, 61440, 61455]], [[1, 15, 240, 17476, 34952, 61440], [15, 240, 4369, 17476, 34952, 61680], [15, 3840, 4593, 17476, 34952], [15, 3840, 4593, 17476, 34952, 61440], [240, 255, 4369, 17476, 34952, 61440], [240, 3840, 4095, 4369, 17476, 34952], [240, 4369, 17476, 34952, 61440, 61695]], [[2, 15, 240, 17476, 34952, 61440], [15, 8946, 17476, 34952, 61440], [240, 3840, 4369, 8738, 43690, 61440], [240, 3840, 4369, 17476, 34952, 61440], [240, 3840, 4369, 34952, 61440, 62532], [240, 3840, 4369, 34952, 62532], [240, 3840, 7953, 17476, 34952, 61440], [240, 3840, 8738, 13107, 34952, 61440], [240, 3840, 8738, 17476, 30583, 61440], [240, 3840, 17476, 34952, 61440, 61713], [240, 4369, 17476, 34952, 61440, 65280], [3840, 4369, 17476, 34952, 61440, 61680]], [[240, 3840, 8738, 17476, 34952, 61680], [240, 4080, 8738, 17476, 34952, 61440], [240, 8738, 17476, 34952, 61440, 65520]], [[4, 15, 240, 17476, 34952, 61440], [15, 17476, 17652, 34952, 61440]], [], [], [], [[8, 15, 240, 17476, 34952, 61440]], [], [[3840, 4369, 17476, 34952, 35064, 61440]], [], [], [], [[15, 3840, 4369, 8738, 34952, 65295]], [[15, 240, 3840, 3855, 17476, 34952], [15, 240, 3840, 17476, 34952, 65295], [15, 240, 17476, 34952, 61440, 61455], [15, 240, 17476, 34952, 61455], [15, 255, 17476, 34952, 61440], [15, 3840, 4095, 17476, 34952], [15, 3840, 4095, 17476, 34952, 61440], [15, 17476, 34952, 61440, 61695]], [[15, 16, 240, 17476, 34952, 61440], [15, 240, 4369, 17476, 34952, 61695], [15, 512, 3840, 17476, 34952, 61440], [15, 1024, 3840, 17476, 34952, 61440], [15, 2048, 3840, 17476, 34952, 61440], [15, 3840, 4096, 17476, 34952, 61440], [15, 3840, 4369, 8738, 34952, 61713], [15, 3840, 4369, 8738, 39321, 61440], [15, 3840, 4369, 13107, 34952, 61440], [15, 3840, 4369, 17476, 30583, 61440], [15, 3840, 8192, 17476, 34952, 61440], [15, 3840, 16384, 17476, 34952, 61440], [15, 3840, 17476, 32768, 34952, 61440], [15, 3840, 17476, 34952, 61440], [15, 3840, 34952, 61440, 62532], [15, 17476, 34952, 61440, 65280], [240, 3840, 4383, 17476, 34952, 61440], [3840, 17476, 34952, 61440, 61455]], [[1, 15, 3840, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 43690], [15, 240, 3840, 4369, 17476, 34952], [15, 240, 3840, 4369, 34952, 62532], [15, 240, 3840, 7953, 17476, 34952], [15, 240, 3840, 8738, 13107, 34952], [15, 240, 3840, 8738, 17476, 30583], [15, 240, 3840, 17476, 34952, 61713], [15, 240, 4369, 8738, 12066, 34952]], [[2, 15, 3840, 17476, 34952, 61440], [15, 240, 4080, 8738, 17476, 34952], [15, 4369, 4593, 17476, 34952, 61440], [240, 255, 3840, 8738, 17476, 34952]], [[15, 3840, 4369, 8946, 17476, 34952], [240, 3840, 8738, 17476, 34952, 65280], [240, 3840, 12066, 17476, 34952, 61440], [3840, 4080, 8738, 17476, 34952, 61440], [3840, 8738, 17476, 34952, 61440, 65520]], [[4, 15, 3840, 17476, 34952, 61440]], [], [], [], [[8, 15, 3840, 17476, 34952, 61440]], [], [], [], [], [], [], [[15, 240, 3840, 4383, 17476, 34952], [15, 3840, 17476, 34952, 61440, 61455], [15, 3840, 17476, 34952, 61455], [15, 3855, 17476, 34952, 61440], [15, 17476, 34952, 61440, 65295]], [[15, 16, 3840, 17476, 34952, 61440], [15, 32, 240, 17476, 34952, 61440], [15, 240, 3855, 4369, 17476, 34952], [15, 255, 3840, 4369, 17476, 34952]], [[15, 240, 4095, 8738, 17476, 34952], [15, 2048, 4369, 17476, 34952, 61440], [15, 3840, 4369, 17476, 34952, 65280], [15, 7953, 17476, 34952, 61440], [3840, 3855, 4369, 17476, 34952, 61440], [3840, 4369, 17476, 34952, 61440, 65295]], [[15, 240, 1024, 8738, 17476, 34952], [15, 240, 3840, 12066, 17476, 34952], [15, 240, 4369, 7953, 17476, 34952], [15, 240, 4369, 8738, 48059, 61440], [15, 240, 4369, 17476, 34952, 61713], [15, 240, 4369, 17476, 39321, 61440], [15, 240, 4369, 21845, 34952, 61440], [15, 240, 8738, 16384, 17476, 34952], [15, 240, 8738, 17476, 34952, 61440], [15, 240, 8738, 34952, 61440, 62532], [15, 240, 17476, 34952, 61440, 61986], [15, 240, 17476, 34952, 61986], [15, 3840, 4080, 8738, 17476, 34952], [15, 8738, 17476, 34952, 61440, 61680], [240, 3840, 3855, 8738, 17476, 34952], [240, 8738, 17476, 34952, 61440, 61455]], [[15, 3840, 4593, 8738, 17476, 34952]], [[15, 8738, 8946, 17476, 34952, 61440], [240, 3840, 4369, 8738, 34952, 62532], [240, 3840, 13107, 17476, 34952, 61440]], [], [[15, 8738, 17476, 17652, 34952, 61440]], [], [], [], [], [], [], [], [], [[15, 240, 8751, 17476, 34952, 61440], [240, 3840, 4369, 8738, 17487, 34952]], [[15, 32, 3840, 17476, 34952, 61440], [15, 3840, 4369, 17476, 34952, 65295]], [[15, 240, 8738, 17476, 34952, 61455], [15, 255, 8738, 17476, 34952, 61440], [15, 3840, 4095, 8738, 17476, 34952], [15, 8738, 17476, 34952, 61440, 61695], [240, 3840, 4369, 8751, 17476, 34952, 61440]], [[15, 3840, 4369, 8738, 48059, 61440], [15, 3840, 4369, 17476, 34952, 61713], [15, 3840, 4369, 17476, 39321, 61440], [15, 3840, 4369, 21845, 34952, 61440], [15, 3840, 8738, 17476, 34952, 61440], [15, 3840, 8738, 34952, 61440, 62532], [15, 3840, 17476, 34952, 61440, 61986], [15, 3840, 17476, 34952, 61986], [15, 8738, 17476, 34952, 61440, 65280], [15, 12066, 17476, 34952, 61440], [240, 3840, 4383, 8738, 17476, 34952, 61440], [3840, 8738, 17476, 34952, 61440, 61455]], [[15, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 13107, 17476, 34952], [15, 240, 3840, 13107, 17476, 34952, 61440], [15, 240, 4369, 8738, 17476, 36744], [15, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 4369, 12066, 17476, 34952]], []]
  | 7 => [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 4369, 8738, 17476, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 3840, 4369, 8738, 17476, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 4369, 8738, 34952, 61440]], [], [[240, 3840, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 3840, 4369, 8738, 34952, 61440]], [[15, 240, 3840, 17476, 34952], [15, 240, 3840, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 4369, 17476, 34952, 61440]], [], [[240, 3840, 8738, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 3840, 4369, 17476, 34952, 61440]], [[15, 240, 3840, 8738, 17476, 34952], [15, 240, 3840, 8738, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 4369, 8738, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 3840, 4369, 8738, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[240, 3840, 4369, 8738, 17476, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 3840, 4369, 8738, 17476], [15, 240, 3840, 4369, 8738, 17476, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[240, 3840, 4369, 8738, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 3840, 4369, 8738, 34952], [15, 240, 3840, 4369, 8738, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 17476, 34952, 61440]], [], [[240, 3840, 4369, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 3840, 17476, 34952, 61440]], [[15, 240, 3840, 4369, 17476, 34952], [15, 240, 3840, 4369, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 8738, 17476, 34952, 61440]], [], [[240, 3840, 4369, 8738, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 3840, 8738, 17476, 34952, 61440]], [[15, 240, 3840, 4369, 8738, 17476, 34952], [15, 240, 3840, 4369, 8738, 17476, 34952, 61440]], []]
  | _ => []

def listed (s : Nat) (ws : List Nat) : Bool := ((rowsOf s).getD (key ws) []).any (fun listedWs => ws.isPerm listedWs)

def blocked (s : Nat) (ws : List Nat) : Bool :=
  match s with
  | 0 => ws != [goal]
  | s + 1 => !(nextD truthMask (s + 2 - ws.length) ws
      (fun ys => coversP pairs s ys && !(listed s ys)))

private theorem validPairs :
    pairs.all (fun p => truthMask.testBit p.1 && truthMask.testBit p.2 &&
                      !goal.testBit p.1 && goal.testBit p.2) = true := by decide +kernel

def cellCheck (s i : Nat) : Bool := ((rowsOf s).getD i []).all (blocked s)

private theorem lvl_0 : ∀ i, 0 ≤ i → i < 512 → cellCheck 0 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf]
private theorem lvl_1 : ∀ i, 0 ≤ i → i < 512 → cellCheck 1 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_0 : ∀ i, 0 ≤ i → i < 4 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_4 : ∀ i, 4 ≤ i → i < 8 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_8 : ∀ i, 8 ≤ i → i < 12 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_12 : ∀ i, 12 ≤ i → i < 16 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_16 : ∀ i, 16 ≤ i → i < 20 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_20 : ∀ i, 20 ≤ i → i < 24 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_24 : ∀ i, 24 ≤ i → i < 28 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_28 : ∀ i, 28 ≤ i → i < 32 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_32 : ∀ i, 32 ≤ i → i < 36 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_36 : ∀ i, 36 ≤ i → i < 40 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_40 : ∀ i, 40 ≤ i → i < 44 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_44 : ∀ i, 44 ≤ i → i < 48 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_48 : ∀ i, 48 ≤ i → i < 52 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_52 : ∀ i, 52 ≤ i → i < 56 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_56 : ∀ i, 56 ≤ i → i < 60 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_60 : ∀ i, 60 ≤ i → i < 64 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_64 : ∀ i, 64 ≤ i → i < 68 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_68 : ∀ i, 68 ≤ i → i < 72 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_72 : ∀ i, 72 ≤ i → i < 76 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_76 : ∀ i, 76 ≤ i → i < 80 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_80 : ∀ i, 80 ≤ i → i < 84 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_84 : ∀ i, 84 ≤ i → i < 88 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_88 : ∀ i, 88 ≤ i → i < 92 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_92 : ∀ i, 92 ≤ i → i < 96 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_96 : ∀ i, 96 ≤ i → i < 100 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_100 : ∀ i, 100 ≤ i → i < 104 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_104 : ∀ i, 104 ≤ i → i < 108 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_108 : ∀ i, 108 ≤ i → i < 112 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_112 : ∀ i, 112 ≤ i → i < 116 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_116 : ∀ i, 116 ≤ i → i < 120 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_120 : ∀ i, 120 ≤ i → i < 124 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_124 : ∀ i, 124 ≤ i → i < 128 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_128 : ∀ i, 128 ≤ i → i < 132 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_132 : ∀ i, 132 ≤ i → i < 136 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 132 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_136 : ∀ i, 136 ≤ i → i < 140 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_140 : ∀ i, 140 ≤ i → i < 144 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 140 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_144 : ∀ i, 144 ≤ i → i < 148 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_148 : ∀ i, 148 ≤ i → i < 152 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 148 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_152 : ∀ i, 152 ≤ i → i < 156 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_156 : ∀ i, 156 ≤ i → i < 160 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 156 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_160 : ∀ i, 160 ≤ i → i < 164 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_164 : ∀ i, 164 ≤ i → i < 168 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 164 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_168 : ∀ i, 168 ≤ i → i < 172 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_172 : ∀ i, 172 ≤ i → i < 176 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 172 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_176 : ∀ i, 176 ≤ i → i < 180 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_180 : ∀ i, 180 ≤ i → i < 184 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 180 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_184 : ∀ i, 184 ≤ i → i < 188 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_188 : ∀ i, 188 ≤ i → i < 192 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 188 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_192 : ∀ i, 192 ≤ i → i < 196 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_196 : ∀ i, 196 ≤ i → i < 200 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 196 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_200 : ∀ i, 200 ≤ i → i < 204 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_204 : ∀ i, 204 ≤ i → i < 208 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 204 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_208 : ∀ i, 208 ≤ i → i < 212 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_212 : ∀ i, 212 ≤ i → i < 216 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 212 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_216 : ∀ i, 216 ≤ i → i < 220 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_220 : ∀ i, 220 ≤ i → i < 224 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 220 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_224 : ∀ i, 224 ≤ i → i < 228 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_228 : ∀ i, 228 ≤ i → i < 232 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 228 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_232 : ∀ i, 232 ≤ i → i < 236 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_236 : ∀ i, 236 ≤ i → i < 240 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 236 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_240 : ∀ i, 240 ≤ i → i < 244 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_244 : ∀ i, 244 ≤ i → i < 248 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 244 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_248 : ∀ i, 248 ≤ i → i < 252 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_252 : ∀ i, 252 ≤ i → i < 256 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 252 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_256 : ∀ i, 256 ≤ i → i < 260 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_260 : ∀ i, 260 ≤ i → i < 264 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 260 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_264 : ∀ i, 264 ≤ i → i < 268 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_268 : ∀ i, 268 ≤ i → i < 272 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 268 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_272 : ∀ i, 272 ≤ i → i < 276 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_276 : ∀ i, 276 ≤ i → i < 280 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 276 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_280 : ∀ i, 280 ≤ i → i < 284 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_284 : ∀ i, 284 ≤ i → i < 288 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 284 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_288 : ∀ i, 288 ≤ i → i < 292 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_292 : ∀ i, 292 ≤ i → i < 296 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 292 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_296 : ∀ i, 296 ≤ i → i < 300 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_300 : ∀ i, 300 ≤ i → i < 304 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 300 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_304 : ∀ i, 304 ≤ i → i < 308 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_308 : ∀ i, 308 ≤ i → i < 312 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 308 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_312 : ∀ i, 312 ≤ i → i < 316 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_316 : ∀ i, 316 ≤ i → i < 320 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 316 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_320 : ∀ i, 320 ≤ i → i < 324 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_324 : ∀ i, 324 ≤ i → i < 328 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 324 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_328 : ∀ i, 328 ≤ i → i < 332 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_332 : ∀ i, 332 ≤ i → i < 336 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 332 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_336 : ∀ i, 336 ≤ i → i < 340 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_340 : ∀ i, 340 ≤ i → i < 344 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 340 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_344 : ∀ i, 344 ≤ i → i < 348 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_348 : ∀ i, 348 ≤ i → i < 352 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 348 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_352 : ∀ i, 352 ≤ i → i < 356 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_356 : ∀ i, 356 ≤ i → i < 360 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 356 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_360 : ∀ i, 360 ≤ i → i < 364 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_364 : ∀ i, 364 ≤ i → i < 368 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 364 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_368 : ∀ i, 368 ≤ i → i < 372 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_372 : ∀ i, 372 ≤ i → i < 376 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 372 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_376 : ∀ i, 376 ≤ i → i < 380 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_380 : ∀ i, 380 ≤ i → i < 384 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 380 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_384 : ∀ i, 384 ≤ i → i < 388 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_388 : ∀ i, 388 ≤ i → i < 392 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 388 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_392 : ∀ i, 392 ≤ i → i < 396 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_396 : ∀ i, 396 ≤ i → i < 400 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 396 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_400 : ∀ i, 400 ≤ i → i < 404 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_404 : ∀ i, 404 ≤ i → i < 408 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 404 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_408 : ∀ i, 408 ≤ i → i < 412 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_412 : ∀ i, 412 ≤ i → i < 416 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 412 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_416 : ∀ i, 416 ≤ i → i < 420 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_420 : ∀ i, 420 ≤ i → i < 424 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 420 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_424 : ∀ i, 424 ≤ i → i < 428 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_428 : ∀ i, 428 ≤ i → i < 432 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 428 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_432 : ∀ i, 432 ≤ i → i < 436 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_436 : ∀ i, 436 ≤ i → i < 440 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 436 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_440 : ∀ i, 440 ≤ i → i < 444 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_444 : ∀ i, 444 ≤ i → i < 448 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 444 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_448 : ∀ i, 448 ≤ i → i < 452 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_452 : ∀ i, 452 ≤ i → i < 456 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 452 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_456 : ∀ i, 456 ≤ i → i < 460 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_460 : ∀ i, 460 ≤ i → i < 464 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 460 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_464 : ∀ i, 464 ≤ i → i < 468 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_468 : ∀ i, 468 ≤ i → i < 472 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 468 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_472 : ∀ i, 472 ≤ i → i < 476 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_476 : ∀ i, 476 ≤ i → i < 480 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 476 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_480 : ∀ i, 480 ≤ i → i < 484 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_484 : ∀ i, 484 ≤ i → i < 488 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 484 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_488 : ∀ i, 488 ≤ i → i < 492 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_492 : ∀ i, 492 ≤ i → i < 496 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 492 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_496 : ∀ i, 496 ≤ i → i < 500 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_500 : ∀ i, 500 ≤ i → i < 504 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 500 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_504 : ∀ i, 504 ≤ i → i < 508 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_2_508 : ∀ i, 508 ≤ i → i < 512 → cellCheck 2 i = true :=
  span_ok (by decide +kernel : span (cellCheck 2) 4 508 = true)
private theorem lvl_2 : ∀ i, 0 ≤ i → i < 512 → cellCheck 2 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_2_0 cell_2_4) (range_split cell_2_8 cell_2_12)) (range_split (range_split cell_2_16 cell_2_20) (range_split cell_2_24 cell_2_28))) (range_split (range_split (range_split cell_2_32 cell_2_36) (range_split cell_2_40 cell_2_44)) (range_split (range_split cell_2_48 cell_2_52) (range_split cell_2_56 cell_2_60)))) (range_split (range_split (range_split (range_split cell_2_64 cell_2_68) (range_split cell_2_72 cell_2_76)) (range_split (range_split cell_2_80 cell_2_84) (range_split cell_2_88 cell_2_92))) (range_split (range_split (range_split cell_2_96 cell_2_100) (range_split cell_2_104 cell_2_108)) (range_split (range_split cell_2_112 cell_2_116) (range_split cell_2_120 cell_2_124))))) (range_split (range_split (range_split (range_split (range_split cell_2_128 cell_2_132) (range_split cell_2_136 cell_2_140)) (range_split (range_split cell_2_144 cell_2_148) (range_split cell_2_152 cell_2_156))) (range_split (range_split (range_split cell_2_160 cell_2_164) (range_split cell_2_168 cell_2_172)) (range_split (range_split cell_2_176 cell_2_180) (range_split cell_2_184 cell_2_188)))) (range_split (range_split (range_split (range_split cell_2_192 cell_2_196) (range_split cell_2_200 cell_2_204)) (range_split (range_split cell_2_208 cell_2_212) (range_split cell_2_216 cell_2_220))) (range_split (range_split (range_split cell_2_224 cell_2_228) (range_split cell_2_232 cell_2_236)) (range_split (range_split cell_2_240 cell_2_244) (range_split cell_2_248 cell_2_252)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_2_256 cell_2_260) (range_split cell_2_264 cell_2_268)) (range_split (range_split cell_2_272 cell_2_276) (range_split cell_2_280 cell_2_284))) (range_split (range_split (range_split cell_2_288 cell_2_292) (range_split cell_2_296 cell_2_300)) (range_split (range_split cell_2_304 cell_2_308) (range_split cell_2_312 cell_2_316)))) (range_split (range_split (range_split (range_split cell_2_320 cell_2_324) (range_split cell_2_328 cell_2_332)) (range_split (range_split cell_2_336 cell_2_340) (range_split cell_2_344 cell_2_348))) (range_split (range_split (range_split cell_2_352 cell_2_356) (range_split cell_2_360 cell_2_364)) (range_split (range_split cell_2_368 cell_2_372) (range_split cell_2_376 cell_2_380))))) (range_split (range_split (range_split (range_split (range_split cell_2_384 cell_2_388) (range_split cell_2_392 cell_2_396)) (range_split (range_split cell_2_400 cell_2_404) (range_split cell_2_408 cell_2_412))) (range_split (range_split (range_split cell_2_416 cell_2_420) (range_split cell_2_424 cell_2_428)) (range_split (range_split cell_2_432 cell_2_436) (range_split cell_2_440 cell_2_444)))) (range_split (range_split (range_split (range_split cell_2_448 cell_2_452) (range_split cell_2_456 cell_2_460)) (range_split (range_split cell_2_464 cell_2_468) (range_split cell_2_472 cell_2_476))) (range_split (range_split (range_split cell_2_480 cell_2_484) (range_split cell_2_488 cell_2_492)) (range_split (range_split cell_2_496 cell_2_500) (range_split cell_2_504 cell_2_508)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_0 : ∀ i, 0 ≤ i → i < 4 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_4 : ∀ i, 4 ≤ i → i < 8 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_8 : ∀ i, 8 ≤ i → i < 12 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_12 : ∀ i, 12 ≤ i → i < 16 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_16 : ∀ i, 16 ≤ i → i < 20 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_20 : ∀ i, 20 ≤ i → i < 24 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_24 : ∀ i, 24 ≤ i → i < 28 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_28 : ∀ i, 28 ≤ i → i < 32 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_32 : ∀ i, 32 ≤ i → i < 36 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_36 : ∀ i, 36 ≤ i → i < 40 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_40 : ∀ i, 40 ≤ i → i < 44 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_44 : ∀ i, 44 ≤ i → i < 48 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_48 : ∀ i, 48 ≤ i → i < 52 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_52 : ∀ i, 52 ≤ i → i < 56 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_56 : ∀ i, 56 ≤ i → i < 60 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_60 : ∀ i, 60 ≤ i → i < 64 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_64 : ∀ i, 64 ≤ i → i < 68 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_68 : ∀ i, 68 ≤ i → i < 72 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_72 : ∀ i, 72 ≤ i → i < 76 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_76 : ∀ i, 76 ≤ i → i < 80 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_80 : ∀ i, 80 ≤ i → i < 84 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_84 : ∀ i, 84 ≤ i → i < 88 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_88 : ∀ i, 88 ≤ i → i < 92 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_92 : ∀ i, 92 ≤ i → i < 96 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_96 : ∀ i, 96 ≤ i → i < 100 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_100 : ∀ i, 100 ≤ i → i < 104 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_104 : ∀ i, 104 ≤ i → i < 108 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_108 : ∀ i, 108 ≤ i → i < 112 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_112 : ∀ i, 112 ≤ i → i < 116 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_116 : ∀ i, 116 ≤ i → i < 120 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_120 : ∀ i, 120 ≤ i → i < 124 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_124 : ∀ i, 124 ≤ i → i < 128 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_128 : ∀ i, 128 ≤ i → i < 132 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_132 : ∀ i, 132 ≤ i → i < 136 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 132 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_136 : ∀ i, 136 ≤ i → i < 140 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_140 : ∀ i, 140 ≤ i → i < 144 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 140 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_144 : ∀ i, 144 ≤ i → i < 148 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_148 : ∀ i, 148 ≤ i → i < 152 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 148 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_152 : ∀ i, 152 ≤ i → i < 156 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_156 : ∀ i, 156 ≤ i → i < 160 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 156 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_160 : ∀ i, 160 ≤ i → i < 164 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_164 : ∀ i, 164 ≤ i → i < 168 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 164 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_168 : ∀ i, 168 ≤ i → i < 172 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_172 : ∀ i, 172 ≤ i → i < 176 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 172 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_176 : ∀ i, 176 ≤ i → i < 180 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_180 : ∀ i, 180 ≤ i → i < 184 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 180 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_184 : ∀ i, 184 ≤ i → i < 188 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_188 : ∀ i, 188 ≤ i → i < 192 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 188 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_192 : ∀ i, 192 ≤ i → i < 196 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_196 : ∀ i, 196 ≤ i → i < 200 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 196 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_200 : ∀ i, 200 ≤ i → i < 204 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_204 : ∀ i, 204 ≤ i → i < 208 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 204 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_208 : ∀ i, 208 ≤ i → i < 212 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_212 : ∀ i, 212 ≤ i → i < 216 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 212 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_216 : ∀ i, 216 ≤ i → i < 220 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_220 : ∀ i, 220 ≤ i → i < 224 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 220 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_224 : ∀ i, 224 ≤ i → i < 228 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_228 : ∀ i, 228 ≤ i → i < 232 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 228 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_232 : ∀ i, 232 ≤ i → i < 236 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_236 : ∀ i, 236 ≤ i → i < 240 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 236 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_240 : ∀ i, 240 ≤ i → i < 244 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_244 : ∀ i, 244 ≤ i → i < 248 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 244 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_248 : ∀ i, 248 ≤ i → i < 252 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_252 : ∀ i, 252 ≤ i → i < 256 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 252 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_256 : ∀ i, 256 ≤ i → i < 260 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_260 : ∀ i, 260 ≤ i → i < 264 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 260 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_264 : ∀ i, 264 ≤ i → i < 268 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_268 : ∀ i, 268 ≤ i → i < 272 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 268 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_272 : ∀ i, 272 ≤ i → i < 276 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_276 : ∀ i, 276 ≤ i → i < 280 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 276 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_280 : ∀ i, 280 ≤ i → i < 284 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_284 : ∀ i, 284 ≤ i → i < 288 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 284 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_288 : ∀ i, 288 ≤ i → i < 292 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_292 : ∀ i, 292 ≤ i → i < 296 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 292 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_296 : ∀ i, 296 ≤ i → i < 300 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_300 : ∀ i, 300 ≤ i → i < 304 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 300 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_304 : ∀ i, 304 ≤ i → i < 308 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_308 : ∀ i, 308 ≤ i → i < 312 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 308 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_312 : ∀ i, 312 ≤ i → i < 316 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_316 : ∀ i, 316 ≤ i → i < 320 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 316 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_320 : ∀ i, 320 ≤ i → i < 324 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_324 : ∀ i, 324 ≤ i → i < 328 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 324 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_328 : ∀ i, 328 ≤ i → i < 332 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_332 : ∀ i, 332 ≤ i → i < 336 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 332 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_336 : ∀ i, 336 ≤ i → i < 340 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_340 : ∀ i, 340 ≤ i → i < 344 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 340 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_344 : ∀ i, 344 ≤ i → i < 348 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_348 : ∀ i, 348 ≤ i → i < 352 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 348 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_352 : ∀ i, 352 ≤ i → i < 356 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_356 : ∀ i, 356 ≤ i → i < 360 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 356 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_360 : ∀ i, 360 ≤ i → i < 364 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_364 : ∀ i, 364 ≤ i → i < 368 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 364 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_368 : ∀ i, 368 ≤ i → i < 372 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_372 : ∀ i, 372 ≤ i → i < 376 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 372 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_376 : ∀ i, 376 ≤ i → i < 380 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_380 : ∀ i, 380 ≤ i → i < 384 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 380 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_384 : ∀ i, 384 ≤ i → i < 388 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_388 : ∀ i, 388 ≤ i → i < 392 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 388 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_392 : ∀ i, 392 ≤ i → i < 396 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_396 : ∀ i, 396 ≤ i → i < 400 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 396 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_400 : ∀ i, 400 ≤ i → i < 404 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_404 : ∀ i, 404 ≤ i → i < 408 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 404 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_408 : ∀ i, 408 ≤ i → i < 412 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_412 : ∀ i, 412 ≤ i → i < 416 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 412 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_416 : ∀ i, 416 ≤ i → i < 420 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_420 : ∀ i, 420 ≤ i → i < 424 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 420 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_424 : ∀ i, 424 ≤ i → i < 428 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_428 : ∀ i, 428 ≤ i → i < 432 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 428 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_432 : ∀ i, 432 ≤ i → i < 436 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_436 : ∀ i, 436 ≤ i → i < 440 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 436 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_440 : ∀ i, 440 ≤ i → i < 444 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_444 : ∀ i, 444 ≤ i → i < 448 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 444 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_448 : ∀ i, 448 ≤ i → i < 452 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_452 : ∀ i, 452 ≤ i → i < 456 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 452 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_456 : ∀ i, 456 ≤ i → i < 460 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_460 : ∀ i, 460 ≤ i → i < 464 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 460 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_464 : ∀ i, 464 ≤ i → i < 468 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_468 : ∀ i, 468 ≤ i → i < 472 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 468 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_472 : ∀ i, 472 ≤ i → i < 476 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_476 : ∀ i, 476 ≤ i → i < 480 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 476 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_480 : ∀ i, 480 ≤ i → i < 484 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_484 : ∀ i, 484 ≤ i → i < 488 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 484 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_488 : ∀ i, 488 ≤ i → i < 492 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_492 : ∀ i, 492 ≤ i → i < 496 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 492 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_496 : ∀ i, 496 ≤ i → i < 500 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_500 : ∀ i, 500 ≤ i → i < 504 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 500 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_504 : ∀ i, 504 ≤ i → i < 508 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_508 : ∀ i, 508 ≤ i → i < 512 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 4 508 = true)
private theorem lvl_3 : ∀ i, 0 ≤ i → i < 512 → cellCheck 3 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_3_0 cell_3_4) (range_split cell_3_8 cell_3_12)) (range_split (range_split cell_3_16 cell_3_20) (range_split cell_3_24 cell_3_28))) (range_split (range_split (range_split cell_3_32 cell_3_36) (range_split cell_3_40 cell_3_44)) (range_split (range_split cell_3_48 cell_3_52) (range_split cell_3_56 cell_3_60)))) (range_split (range_split (range_split (range_split cell_3_64 cell_3_68) (range_split cell_3_72 cell_3_76)) (range_split (range_split cell_3_80 cell_3_84) (range_split cell_3_88 cell_3_92))) (range_split (range_split (range_split cell_3_96 cell_3_100) (range_split cell_3_104 cell_3_108)) (range_split (range_split cell_3_112 cell_3_116) (range_split cell_3_120 cell_3_124))))) (range_split (range_split (range_split (range_split (range_split cell_3_128 cell_3_132) (range_split cell_3_136 cell_3_140)) (range_split (range_split cell_3_144 cell_3_148) (range_split cell_3_152 cell_3_156))) (range_split (range_split (range_split cell_3_160 cell_3_164) (range_split cell_3_168 cell_3_172)) (range_split (range_split cell_3_176 cell_3_180) (range_split cell_3_184 cell_3_188)))) (range_split (range_split (range_split (range_split cell_3_192 cell_3_196) (range_split cell_3_200 cell_3_204)) (range_split (range_split cell_3_208 cell_3_212) (range_split cell_3_216 cell_3_220))) (range_split (range_split (range_split cell_3_224 cell_3_228) (range_split cell_3_232 cell_3_236)) (range_split (range_split cell_3_240 cell_3_244) (range_split cell_3_248 cell_3_252)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_3_256 cell_3_260) (range_split cell_3_264 cell_3_268)) (range_split (range_split cell_3_272 cell_3_276) (range_split cell_3_280 cell_3_284))) (range_split (range_split (range_split cell_3_288 cell_3_292) (range_split cell_3_296 cell_3_300)) (range_split (range_split cell_3_304 cell_3_308) (range_split cell_3_312 cell_3_316)))) (range_split (range_split (range_split (range_split cell_3_320 cell_3_324) (range_split cell_3_328 cell_3_332)) (range_split (range_split cell_3_336 cell_3_340) (range_split cell_3_344 cell_3_348))) (range_split (range_split (range_split cell_3_352 cell_3_356) (range_split cell_3_360 cell_3_364)) (range_split (range_split cell_3_368 cell_3_372) (range_split cell_3_376 cell_3_380))))) (range_split (range_split (range_split (range_split (range_split cell_3_384 cell_3_388) (range_split cell_3_392 cell_3_396)) (range_split (range_split cell_3_400 cell_3_404) (range_split cell_3_408 cell_3_412))) (range_split (range_split (range_split cell_3_416 cell_3_420) (range_split cell_3_424 cell_3_428)) (range_split (range_split cell_3_432 cell_3_436) (range_split cell_3_440 cell_3_444)))) (range_split (range_split (range_split (range_split cell_3_448 cell_3_452) (range_split cell_3_456 cell_3_460)) (range_split (range_split cell_3_464 cell_3_468) (range_split cell_3_472 cell_3_476))) (range_split (range_split (range_split cell_3_480 cell_3_484) (range_split cell_3_488 cell_3_492)) (range_split (range_split cell_3_496 cell_3_500) (range_split cell_3_504 cell_3_508)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_0 : ∀ i, 0 ≤ i → i < 4 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_4 : ∀ i, 4 ≤ i → i < 8 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_8 : ∀ i, 8 ≤ i → i < 12 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_12 : ∀ i, 12 ≤ i → i < 16 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_16 : ∀ i, 16 ≤ i → i < 20 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_20 : ∀ i, 20 ≤ i → i < 24 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_24 : ∀ i, 24 ≤ i → i < 28 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_28 : ∀ i, 28 ≤ i → i < 32 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_32 : ∀ i, 32 ≤ i → i < 36 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_36 : ∀ i, 36 ≤ i → i < 40 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_40 : ∀ i, 40 ≤ i → i < 44 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_44 : ∀ i, 44 ≤ i → i < 48 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_48 : ∀ i, 48 ≤ i → i < 52 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_52 : ∀ i, 52 ≤ i → i < 56 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_56 : ∀ i, 56 ≤ i → i < 60 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_60 : ∀ i, 60 ≤ i → i < 64 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_64 : ∀ i, 64 ≤ i → i < 68 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_68 : ∀ i, 68 ≤ i → i < 72 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_72 : ∀ i, 72 ≤ i → i < 76 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_76 : ∀ i, 76 ≤ i → i < 80 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_80 : ∀ i, 80 ≤ i → i < 84 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_84 : ∀ i, 84 ≤ i → i < 88 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_88 : ∀ i, 88 ≤ i → i < 92 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_92 : ∀ i, 92 ≤ i → i < 96 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_96 : ∀ i, 96 ≤ i → i < 100 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_100 : ∀ i, 100 ≤ i → i < 104 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_104 : ∀ i, 104 ≤ i → i < 108 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_108 : ∀ i, 108 ≤ i → i < 112 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_112 : ∀ i, 112 ≤ i → i < 116 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_116 : ∀ i, 116 ≤ i → i < 120 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_120 : ∀ i, 120 ≤ i → i < 124 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_124 : ∀ i, 124 ≤ i → i < 128 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_128 : ∀ i, 128 ≤ i → i < 132 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_132 : ∀ i, 132 ≤ i → i < 136 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 132 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_136 : ∀ i, 136 ≤ i → i < 140 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_140 : ∀ i, 140 ≤ i → i < 144 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 140 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_144 : ∀ i, 144 ≤ i → i < 148 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_148 : ∀ i, 148 ≤ i → i < 152 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 148 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_152 : ∀ i, 152 ≤ i → i < 156 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_156 : ∀ i, 156 ≤ i → i < 160 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 156 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_160 : ∀ i, 160 ≤ i → i < 164 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_164 : ∀ i, 164 ≤ i → i < 168 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 164 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_168 : ∀ i, 168 ≤ i → i < 172 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_172 : ∀ i, 172 ≤ i → i < 176 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 172 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_176 : ∀ i, 176 ≤ i → i < 180 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_180 : ∀ i, 180 ≤ i → i < 184 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 180 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_184 : ∀ i, 184 ≤ i → i < 188 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_188 : ∀ i, 188 ≤ i → i < 192 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 188 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_192 : ∀ i, 192 ≤ i → i < 196 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_196 : ∀ i, 196 ≤ i → i < 200 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 196 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_200 : ∀ i, 200 ≤ i → i < 204 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_204 : ∀ i, 204 ≤ i → i < 208 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 204 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_208 : ∀ i, 208 ≤ i → i < 212 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_212 : ∀ i, 212 ≤ i → i < 216 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 212 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_216 : ∀ i, 216 ≤ i → i < 220 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_220 : ∀ i, 220 ≤ i → i < 224 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 220 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_224 : ∀ i, 224 ≤ i → i < 228 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_228 : ∀ i, 228 ≤ i → i < 232 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 228 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_232 : ∀ i, 232 ≤ i → i < 236 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_236 : ∀ i, 236 ≤ i → i < 240 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 236 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_240 : ∀ i, 240 ≤ i → i < 244 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_244 : ∀ i, 244 ≤ i → i < 248 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 244 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_248 : ∀ i, 248 ≤ i → i < 252 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_252 : ∀ i, 252 ≤ i → i < 256 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 252 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_256 : ∀ i, 256 ≤ i → i < 260 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_260 : ∀ i, 260 ≤ i → i < 264 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 260 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_264 : ∀ i, 264 ≤ i → i < 268 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_268 : ∀ i, 268 ≤ i → i < 272 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 268 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_272 : ∀ i, 272 ≤ i → i < 276 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_276 : ∀ i, 276 ≤ i → i < 280 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 276 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_280 : ∀ i, 280 ≤ i → i < 284 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_284 : ∀ i, 284 ≤ i → i < 288 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 284 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_288 : ∀ i, 288 ≤ i → i < 292 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_292 : ∀ i, 292 ≤ i → i < 296 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 292 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_296 : ∀ i, 296 ≤ i → i < 300 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_300 : ∀ i, 300 ≤ i → i < 304 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 300 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_304 : ∀ i, 304 ≤ i → i < 308 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_308 : ∀ i, 308 ≤ i → i < 312 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 308 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_312 : ∀ i, 312 ≤ i → i < 316 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_316 : ∀ i, 316 ≤ i → i < 320 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 316 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_320 : ∀ i, 320 ≤ i → i < 324 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_324 : ∀ i, 324 ≤ i → i < 328 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 324 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_328 : ∀ i, 328 ≤ i → i < 332 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_332 : ∀ i, 332 ≤ i → i < 336 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 332 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_336 : ∀ i, 336 ≤ i → i < 340 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_340 : ∀ i, 340 ≤ i → i < 344 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 340 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_344 : ∀ i, 344 ≤ i → i < 348 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_348 : ∀ i, 348 ≤ i → i < 352 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 348 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_352 : ∀ i, 352 ≤ i → i < 356 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_356 : ∀ i, 356 ≤ i → i < 360 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 356 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_360 : ∀ i, 360 ≤ i → i < 364 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_364 : ∀ i, 364 ≤ i → i < 368 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 364 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_368 : ∀ i, 368 ≤ i → i < 372 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_372 : ∀ i, 372 ≤ i → i < 376 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 372 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_376 : ∀ i, 376 ≤ i → i < 380 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_380 : ∀ i, 380 ≤ i → i < 384 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 380 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_384 : ∀ i, 384 ≤ i → i < 388 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_388 : ∀ i, 388 ≤ i → i < 392 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 388 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_392 : ∀ i, 392 ≤ i → i < 396 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_396 : ∀ i, 396 ≤ i → i < 400 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 396 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_400 : ∀ i, 400 ≤ i → i < 404 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_404 : ∀ i, 404 ≤ i → i < 408 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 404 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_408 : ∀ i, 408 ≤ i → i < 412 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_412 : ∀ i, 412 ≤ i → i < 416 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 412 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_416 : ∀ i, 416 ≤ i → i < 420 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_420 : ∀ i, 420 ≤ i → i < 424 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 420 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_424 : ∀ i, 424 ≤ i → i < 428 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_428 : ∀ i, 428 ≤ i → i < 432 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 428 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_432 : ∀ i, 432 ≤ i → i < 436 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_436 : ∀ i, 436 ≤ i → i < 440 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 436 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_440 : ∀ i, 440 ≤ i → i < 444 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_444 : ∀ i, 444 ≤ i → i < 448 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 444 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_448 : ∀ i, 448 ≤ i → i < 452 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_452 : ∀ i, 452 ≤ i → i < 456 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 452 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_456 : ∀ i, 456 ≤ i → i < 460 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_460 : ∀ i, 460 ≤ i → i < 464 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 460 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_464 : ∀ i, 464 ≤ i → i < 468 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_468 : ∀ i, 468 ≤ i → i < 472 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 468 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_472 : ∀ i, 472 ≤ i → i < 476 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_476 : ∀ i, 476 ≤ i → i < 480 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 476 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_480 : ∀ i, 480 ≤ i → i < 484 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_484 : ∀ i, 484 ≤ i → i < 488 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 484 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_488 : ∀ i, 488 ≤ i → i < 492 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_492 : ∀ i, 492 ≤ i → i < 496 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 492 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_496 : ∀ i, 496 ≤ i → i < 500 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_500 : ∀ i, 500 ≤ i → i < 504 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 500 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_504 : ∀ i, 504 ≤ i → i < 508 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_508 : ∀ i, 508 ≤ i → i < 512 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 4 508 = true)
private theorem lvl_4 : ∀ i, 0 ≤ i → i < 512 → cellCheck 4 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_4_0 cell_4_4) (range_split cell_4_8 cell_4_12)) (range_split (range_split cell_4_16 cell_4_20) (range_split cell_4_24 cell_4_28))) (range_split (range_split (range_split cell_4_32 cell_4_36) (range_split cell_4_40 cell_4_44)) (range_split (range_split cell_4_48 cell_4_52) (range_split cell_4_56 cell_4_60)))) (range_split (range_split (range_split (range_split cell_4_64 cell_4_68) (range_split cell_4_72 cell_4_76)) (range_split (range_split cell_4_80 cell_4_84) (range_split cell_4_88 cell_4_92))) (range_split (range_split (range_split cell_4_96 cell_4_100) (range_split cell_4_104 cell_4_108)) (range_split (range_split cell_4_112 cell_4_116) (range_split cell_4_120 cell_4_124))))) (range_split (range_split (range_split (range_split (range_split cell_4_128 cell_4_132) (range_split cell_4_136 cell_4_140)) (range_split (range_split cell_4_144 cell_4_148) (range_split cell_4_152 cell_4_156))) (range_split (range_split (range_split cell_4_160 cell_4_164) (range_split cell_4_168 cell_4_172)) (range_split (range_split cell_4_176 cell_4_180) (range_split cell_4_184 cell_4_188)))) (range_split (range_split (range_split (range_split cell_4_192 cell_4_196) (range_split cell_4_200 cell_4_204)) (range_split (range_split cell_4_208 cell_4_212) (range_split cell_4_216 cell_4_220))) (range_split (range_split (range_split cell_4_224 cell_4_228) (range_split cell_4_232 cell_4_236)) (range_split (range_split cell_4_240 cell_4_244) (range_split cell_4_248 cell_4_252)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_4_256 cell_4_260) (range_split cell_4_264 cell_4_268)) (range_split (range_split cell_4_272 cell_4_276) (range_split cell_4_280 cell_4_284))) (range_split (range_split (range_split cell_4_288 cell_4_292) (range_split cell_4_296 cell_4_300)) (range_split (range_split cell_4_304 cell_4_308) (range_split cell_4_312 cell_4_316)))) (range_split (range_split (range_split (range_split cell_4_320 cell_4_324) (range_split cell_4_328 cell_4_332)) (range_split (range_split cell_4_336 cell_4_340) (range_split cell_4_344 cell_4_348))) (range_split (range_split (range_split cell_4_352 cell_4_356) (range_split cell_4_360 cell_4_364)) (range_split (range_split cell_4_368 cell_4_372) (range_split cell_4_376 cell_4_380))))) (range_split (range_split (range_split (range_split (range_split cell_4_384 cell_4_388) (range_split cell_4_392 cell_4_396)) (range_split (range_split cell_4_400 cell_4_404) (range_split cell_4_408 cell_4_412))) (range_split (range_split (range_split cell_4_416 cell_4_420) (range_split cell_4_424 cell_4_428)) (range_split (range_split cell_4_432 cell_4_436) (range_split cell_4_440 cell_4_444)))) (range_split (range_split (range_split (range_split cell_4_448 cell_4_452) (range_split cell_4_456 cell_4_460)) (range_split (range_split cell_4_464 cell_4_468) (range_split cell_4_472 cell_4_476))) (range_split (range_split (range_split cell_4_480 cell_4_484) (range_split cell_4_488 cell_4_492)) (range_split (range_split cell_4_496 cell_4_500) (range_split cell_4_504 cell_4_508)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_0 : ∀ i, 0 ≤ i → i < 4 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_4 : ∀ i, 4 ≤ i → i < 8 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_8 : ∀ i, 8 ≤ i → i < 12 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_12 : ∀ i, 12 ≤ i → i < 16 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_16 : ∀ i, 16 ≤ i → i < 20 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_20 : ∀ i, 20 ≤ i → i < 24 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_24 : ∀ i, 24 ≤ i → i < 28 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_28 : ∀ i, 28 ≤ i → i < 32 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_32 : ∀ i, 32 ≤ i → i < 36 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_36 : ∀ i, 36 ≤ i → i < 40 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_40 : ∀ i, 40 ≤ i → i < 44 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_44 : ∀ i, 44 ≤ i → i < 48 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_48 : ∀ i, 48 ≤ i → i < 52 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_52 : ∀ i, 52 ≤ i → i < 56 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_56 : ∀ i, 56 ≤ i → i < 60 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_60 : ∀ i, 60 ≤ i → i < 64 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_64 : ∀ i, 64 ≤ i → i < 68 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_68 : ∀ i, 68 ≤ i → i < 72 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_72 : ∀ i, 72 ≤ i → i < 76 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_76 : ∀ i, 76 ≤ i → i < 80 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_80 : ∀ i, 80 ≤ i → i < 84 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_84 : ∀ i, 84 ≤ i → i < 88 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_88 : ∀ i, 88 ≤ i → i < 92 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_92 : ∀ i, 92 ≤ i → i < 96 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_96 : ∀ i, 96 ≤ i → i < 100 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_100 : ∀ i, 100 ≤ i → i < 104 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_104 : ∀ i, 104 ≤ i → i < 108 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_108 : ∀ i, 108 ≤ i → i < 112 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_112 : ∀ i, 112 ≤ i → i < 116 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_116 : ∀ i, 116 ≤ i → i < 120 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_120 : ∀ i, 120 ≤ i → i < 124 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_124 : ∀ i, 124 ≤ i → i < 128 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_128 : ∀ i, 128 ≤ i → i < 132 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_132 : ∀ i, 132 ≤ i → i < 136 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 132 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_136 : ∀ i, 136 ≤ i → i < 140 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_140 : ∀ i, 140 ≤ i → i < 144 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 140 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_144 : ∀ i, 144 ≤ i → i < 148 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_148 : ∀ i, 148 ≤ i → i < 152 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 148 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_152 : ∀ i, 152 ≤ i → i < 156 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_156 : ∀ i, 156 ≤ i → i < 160 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 156 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_160 : ∀ i, 160 ≤ i → i < 164 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_164 : ∀ i, 164 ≤ i → i < 168 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 164 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_168 : ∀ i, 168 ≤ i → i < 172 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_172 : ∀ i, 172 ≤ i → i < 176 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 172 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_176 : ∀ i, 176 ≤ i → i < 180 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_180 : ∀ i, 180 ≤ i → i < 184 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 180 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_184 : ∀ i, 184 ≤ i → i < 188 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_188 : ∀ i, 188 ≤ i → i < 192 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 188 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_192 : ∀ i, 192 ≤ i → i < 196 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_196 : ∀ i, 196 ≤ i → i < 200 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 196 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_200 : ∀ i, 200 ≤ i → i < 204 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_204 : ∀ i, 204 ≤ i → i < 208 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 204 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_208 : ∀ i, 208 ≤ i → i < 212 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_212 : ∀ i, 212 ≤ i → i < 216 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 212 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_216 : ∀ i, 216 ≤ i → i < 220 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_220 : ∀ i, 220 ≤ i → i < 224 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 220 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_224 : ∀ i, 224 ≤ i → i < 228 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_228 : ∀ i, 228 ≤ i → i < 232 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 228 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_232 : ∀ i, 232 ≤ i → i < 236 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_236 : ∀ i, 236 ≤ i → i < 240 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 236 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_240 : ∀ i, 240 ≤ i → i < 244 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_244 : ∀ i, 244 ≤ i → i < 248 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 244 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_248 : ∀ i, 248 ≤ i → i < 252 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_252 : ∀ i, 252 ≤ i → i < 256 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 252 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_256 : ∀ i, 256 ≤ i → i < 260 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_260 : ∀ i, 260 ≤ i → i < 264 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 260 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_264 : ∀ i, 264 ≤ i → i < 268 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_268 : ∀ i, 268 ≤ i → i < 272 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 268 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_272 : ∀ i, 272 ≤ i → i < 276 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_276 : ∀ i, 276 ≤ i → i < 280 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 276 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_280 : ∀ i, 280 ≤ i → i < 284 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_284 : ∀ i, 284 ≤ i → i < 288 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 284 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_288 : ∀ i, 288 ≤ i → i < 292 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_292 : ∀ i, 292 ≤ i → i < 296 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 292 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_296 : ∀ i, 296 ≤ i → i < 300 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_300 : ∀ i, 300 ≤ i → i < 304 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 300 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_304 : ∀ i, 304 ≤ i → i < 308 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_308 : ∀ i, 308 ≤ i → i < 312 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 308 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_312 : ∀ i, 312 ≤ i → i < 316 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_316 : ∀ i, 316 ≤ i → i < 320 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 316 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_320 : ∀ i, 320 ≤ i → i < 324 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_324 : ∀ i, 324 ≤ i → i < 328 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 324 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_328 : ∀ i, 328 ≤ i → i < 332 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_332 : ∀ i, 332 ≤ i → i < 336 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 332 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_336 : ∀ i, 336 ≤ i → i < 340 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_340 : ∀ i, 340 ≤ i → i < 344 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 340 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_344 : ∀ i, 344 ≤ i → i < 348 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_348 : ∀ i, 348 ≤ i → i < 352 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 348 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_352 : ∀ i, 352 ≤ i → i < 356 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_356 : ∀ i, 356 ≤ i → i < 360 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 356 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_360 : ∀ i, 360 ≤ i → i < 364 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_364 : ∀ i, 364 ≤ i → i < 368 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 364 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_368 : ∀ i, 368 ≤ i → i < 372 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_372 : ∀ i, 372 ≤ i → i < 376 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 372 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_376 : ∀ i, 376 ≤ i → i < 380 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_380 : ∀ i, 380 ≤ i → i < 384 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 380 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_384 : ∀ i, 384 ≤ i → i < 388 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_388 : ∀ i, 388 ≤ i → i < 392 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 388 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_392 : ∀ i, 392 ≤ i → i < 396 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_396 : ∀ i, 396 ≤ i → i < 400 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 396 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_400 : ∀ i, 400 ≤ i → i < 404 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_404 : ∀ i, 404 ≤ i → i < 408 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 404 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_408 : ∀ i, 408 ≤ i → i < 412 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_412 : ∀ i, 412 ≤ i → i < 416 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 412 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_416 : ∀ i, 416 ≤ i → i < 420 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_420 : ∀ i, 420 ≤ i → i < 424 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 420 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_424 : ∀ i, 424 ≤ i → i < 428 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_428 : ∀ i, 428 ≤ i → i < 432 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 428 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_432 : ∀ i, 432 ≤ i → i < 436 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_436 : ∀ i, 436 ≤ i → i < 440 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 436 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_440 : ∀ i, 440 ≤ i → i < 444 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_444 : ∀ i, 444 ≤ i → i < 448 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 444 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_448 : ∀ i, 448 ≤ i → i < 452 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_452 : ∀ i, 452 ≤ i → i < 456 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 452 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_456 : ∀ i, 456 ≤ i → i < 460 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_460 : ∀ i, 460 ≤ i → i < 464 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 460 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_464 : ∀ i, 464 ≤ i → i < 468 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_468 : ∀ i, 468 ≤ i → i < 472 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 468 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_472 : ∀ i, 472 ≤ i → i < 476 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_476 : ∀ i, 476 ≤ i → i < 480 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 476 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_480 : ∀ i, 480 ≤ i → i < 484 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_484 : ∀ i, 484 ≤ i → i < 488 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 484 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_488 : ∀ i, 488 ≤ i → i < 492 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_492 : ∀ i, 492 ≤ i → i < 496 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 492 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_496 : ∀ i, 496 ≤ i → i < 500 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_500 : ∀ i, 500 ≤ i → i < 504 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 500 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_504 : ∀ i, 504 ≤ i → i < 508 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_508 : ∀ i, 508 ≤ i → i < 512 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 4 508 = true)
private theorem lvl_5 : ∀ i, 0 ≤ i → i < 512 → cellCheck 5 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_5_0 cell_5_4) (range_split cell_5_8 cell_5_12)) (range_split (range_split cell_5_16 cell_5_20) (range_split cell_5_24 cell_5_28))) (range_split (range_split (range_split cell_5_32 cell_5_36) (range_split cell_5_40 cell_5_44)) (range_split (range_split cell_5_48 cell_5_52) (range_split cell_5_56 cell_5_60)))) (range_split (range_split (range_split (range_split cell_5_64 cell_5_68) (range_split cell_5_72 cell_5_76)) (range_split (range_split cell_5_80 cell_5_84) (range_split cell_5_88 cell_5_92))) (range_split (range_split (range_split cell_5_96 cell_5_100) (range_split cell_5_104 cell_5_108)) (range_split (range_split cell_5_112 cell_5_116) (range_split cell_5_120 cell_5_124))))) (range_split (range_split (range_split (range_split (range_split cell_5_128 cell_5_132) (range_split cell_5_136 cell_5_140)) (range_split (range_split cell_5_144 cell_5_148) (range_split cell_5_152 cell_5_156))) (range_split (range_split (range_split cell_5_160 cell_5_164) (range_split cell_5_168 cell_5_172)) (range_split (range_split cell_5_176 cell_5_180) (range_split cell_5_184 cell_5_188)))) (range_split (range_split (range_split (range_split cell_5_192 cell_5_196) (range_split cell_5_200 cell_5_204)) (range_split (range_split cell_5_208 cell_5_212) (range_split cell_5_216 cell_5_220))) (range_split (range_split (range_split cell_5_224 cell_5_228) (range_split cell_5_232 cell_5_236)) (range_split (range_split cell_5_240 cell_5_244) (range_split cell_5_248 cell_5_252)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_5_256 cell_5_260) (range_split cell_5_264 cell_5_268)) (range_split (range_split cell_5_272 cell_5_276) (range_split cell_5_280 cell_5_284))) (range_split (range_split (range_split cell_5_288 cell_5_292) (range_split cell_5_296 cell_5_300)) (range_split (range_split cell_5_304 cell_5_308) (range_split cell_5_312 cell_5_316)))) (range_split (range_split (range_split (range_split cell_5_320 cell_5_324) (range_split cell_5_328 cell_5_332)) (range_split (range_split cell_5_336 cell_5_340) (range_split cell_5_344 cell_5_348))) (range_split (range_split (range_split cell_5_352 cell_5_356) (range_split cell_5_360 cell_5_364)) (range_split (range_split cell_5_368 cell_5_372) (range_split cell_5_376 cell_5_380))))) (range_split (range_split (range_split (range_split (range_split cell_5_384 cell_5_388) (range_split cell_5_392 cell_5_396)) (range_split (range_split cell_5_400 cell_5_404) (range_split cell_5_408 cell_5_412))) (range_split (range_split (range_split cell_5_416 cell_5_420) (range_split cell_5_424 cell_5_428)) (range_split (range_split cell_5_432 cell_5_436) (range_split cell_5_440 cell_5_444)))) (range_split (range_split (range_split (range_split cell_5_448 cell_5_452) (range_split cell_5_456 cell_5_460)) (range_split (range_split cell_5_464 cell_5_468) (range_split cell_5_472 cell_5_476))) (range_split (range_split (range_split cell_5_480 cell_5_484) (range_split cell_5_488 cell_5_492)) (range_split (range_split cell_5_496 cell_5_500) (range_split cell_5_504 cell_5_508)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_0 : ∀ i, 0 ≤ i → i < 4 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_4 : ∀ i, 4 ≤ i → i < 8 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_8 : ∀ i, 8 ≤ i → i < 12 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_12 : ∀ i, 12 ≤ i → i < 16 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_16 : ∀ i, 16 ≤ i → i < 20 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_20 : ∀ i, 20 ≤ i → i < 24 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_24 : ∀ i, 24 ≤ i → i < 28 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_28 : ∀ i, 28 ≤ i → i < 32 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_32 : ∀ i, 32 ≤ i → i < 36 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_36 : ∀ i, 36 ≤ i → i < 40 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_40 : ∀ i, 40 ≤ i → i < 44 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_44 : ∀ i, 44 ≤ i → i < 48 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_48 : ∀ i, 48 ≤ i → i < 52 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_52 : ∀ i, 52 ≤ i → i < 56 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_56 : ∀ i, 56 ≤ i → i < 60 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_60 : ∀ i, 60 ≤ i → i < 64 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_64 : ∀ i, 64 ≤ i → i < 68 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_68 : ∀ i, 68 ≤ i → i < 72 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_72 : ∀ i, 72 ≤ i → i < 76 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_76 : ∀ i, 76 ≤ i → i < 80 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_80 : ∀ i, 80 ≤ i → i < 84 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_84 : ∀ i, 84 ≤ i → i < 88 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_88 : ∀ i, 88 ≤ i → i < 92 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_92 : ∀ i, 92 ≤ i → i < 96 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_96 : ∀ i, 96 ≤ i → i < 100 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_100 : ∀ i, 100 ≤ i → i < 104 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_104 : ∀ i, 104 ≤ i → i < 108 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_108 : ∀ i, 108 ≤ i → i < 112 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_112 : ∀ i, 112 ≤ i → i < 116 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_116 : ∀ i, 116 ≤ i → i < 120 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_120 : ∀ i, 120 ≤ i → i < 124 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_124 : ∀ i, 124 ≤ i → i < 128 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_128 : ∀ i, 128 ≤ i → i < 132 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_132 : ∀ i, 132 ≤ i → i < 136 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 132 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_136 : ∀ i, 136 ≤ i → i < 140 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_140 : ∀ i, 140 ≤ i → i < 144 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 140 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_144 : ∀ i, 144 ≤ i → i < 148 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_148 : ∀ i, 148 ≤ i → i < 152 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 148 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_152 : ∀ i, 152 ≤ i → i < 156 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_156 : ∀ i, 156 ≤ i → i < 160 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 156 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_160 : ∀ i, 160 ≤ i → i < 164 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_164 : ∀ i, 164 ≤ i → i < 168 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 164 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_168 : ∀ i, 168 ≤ i → i < 172 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_172 : ∀ i, 172 ≤ i → i < 176 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 172 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_176 : ∀ i, 176 ≤ i → i < 180 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_180 : ∀ i, 180 ≤ i → i < 184 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 180 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_184 : ∀ i, 184 ≤ i → i < 188 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_188 : ∀ i, 188 ≤ i → i < 192 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 188 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_192 : ∀ i, 192 ≤ i → i < 196 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_196 : ∀ i, 196 ≤ i → i < 200 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 196 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_200 : ∀ i, 200 ≤ i → i < 204 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_204 : ∀ i, 204 ≤ i → i < 208 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 204 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_208 : ∀ i, 208 ≤ i → i < 212 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_212 : ∀ i, 212 ≤ i → i < 216 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 212 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_216 : ∀ i, 216 ≤ i → i < 220 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_220 : ∀ i, 220 ≤ i → i < 224 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 220 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_224 : ∀ i, 224 ≤ i → i < 228 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_228 : ∀ i, 228 ≤ i → i < 232 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 228 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_232 : ∀ i, 232 ≤ i → i < 236 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_236 : ∀ i, 236 ≤ i → i < 240 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 236 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_240 : ∀ i, 240 ≤ i → i < 244 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_244 : ∀ i, 244 ≤ i → i < 248 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 244 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_248 : ∀ i, 248 ≤ i → i < 252 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_252 : ∀ i, 252 ≤ i → i < 256 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 252 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_256 : ∀ i, 256 ≤ i → i < 260 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_260 : ∀ i, 260 ≤ i → i < 264 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 260 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_264 : ∀ i, 264 ≤ i → i < 268 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_268 : ∀ i, 268 ≤ i → i < 272 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 268 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_272 : ∀ i, 272 ≤ i → i < 276 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_276 : ∀ i, 276 ≤ i → i < 280 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 276 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_280 : ∀ i, 280 ≤ i → i < 284 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_284 : ∀ i, 284 ≤ i → i < 288 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 284 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_288 : ∀ i, 288 ≤ i → i < 292 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_292 : ∀ i, 292 ≤ i → i < 296 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 292 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_296 : ∀ i, 296 ≤ i → i < 300 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_300 : ∀ i, 300 ≤ i → i < 304 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 300 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_304 : ∀ i, 304 ≤ i → i < 308 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_308 : ∀ i, 308 ≤ i → i < 312 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 308 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_312 : ∀ i, 312 ≤ i → i < 316 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_316 : ∀ i, 316 ≤ i → i < 320 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 316 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_320 : ∀ i, 320 ≤ i → i < 324 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_324 : ∀ i, 324 ≤ i → i < 328 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 324 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_328 : ∀ i, 328 ≤ i → i < 332 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_332 : ∀ i, 332 ≤ i → i < 336 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 332 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_336 : ∀ i, 336 ≤ i → i < 340 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_340 : ∀ i, 340 ≤ i → i < 344 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 340 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_344 : ∀ i, 344 ≤ i → i < 348 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_348 : ∀ i, 348 ≤ i → i < 352 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 348 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_352 : ∀ i, 352 ≤ i → i < 356 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_356 : ∀ i, 356 ≤ i → i < 360 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 356 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_360 : ∀ i, 360 ≤ i → i < 364 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_364 : ∀ i, 364 ≤ i → i < 368 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 364 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_368 : ∀ i, 368 ≤ i → i < 372 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_372 : ∀ i, 372 ≤ i → i < 376 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 372 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_376 : ∀ i, 376 ≤ i → i < 380 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_380 : ∀ i, 380 ≤ i → i < 384 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 380 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_384 : ∀ i, 384 ≤ i → i < 388 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_388 : ∀ i, 388 ≤ i → i < 392 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 388 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_392 : ∀ i, 392 ≤ i → i < 396 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_396 : ∀ i, 396 ≤ i → i < 400 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 396 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_400 : ∀ i, 400 ≤ i → i < 404 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_404 : ∀ i, 404 ≤ i → i < 408 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 404 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_408 : ∀ i, 408 ≤ i → i < 412 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_412 : ∀ i, 412 ≤ i → i < 416 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 412 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_416 : ∀ i, 416 ≤ i → i < 420 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_420 : ∀ i, 420 ≤ i → i < 424 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 420 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_424 : ∀ i, 424 ≤ i → i < 428 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_428 : ∀ i, 428 ≤ i → i < 432 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 428 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_432 : ∀ i, 432 ≤ i → i < 436 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_436 : ∀ i, 436 ≤ i → i < 440 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 436 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_440 : ∀ i, 440 ≤ i → i < 444 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_444 : ∀ i, 444 ≤ i → i < 448 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 444 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_448 : ∀ i, 448 ≤ i → i < 452 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_452 : ∀ i, 452 ≤ i → i < 456 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 452 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_456 : ∀ i, 456 ≤ i → i < 460 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_460 : ∀ i, 460 ≤ i → i < 464 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 460 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_464 : ∀ i, 464 ≤ i → i < 468 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_468 : ∀ i, 468 ≤ i → i < 472 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 468 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_472 : ∀ i, 472 ≤ i → i < 476 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_476 : ∀ i, 476 ≤ i → i < 480 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 476 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_480 : ∀ i, 480 ≤ i → i < 484 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_484 : ∀ i, 484 ≤ i → i < 488 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 484 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_488 : ∀ i, 488 ≤ i → i < 492 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_492 : ∀ i, 492 ≤ i → i < 496 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 492 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_496 : ∀ i, 496 ≤ i → i < 500 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_500 : ∀ i, 500 ≤ i → i < 504 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 500 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_504 : ∀ i, 504 ≤ i → i < 508 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_508 : ∀ i, 508 ≤ i → i < 512 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 4 508 = true)
private theorem lvl_6 : ∀ i, 0 ≤ i → i < 512 → cellCheck 6 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_6_0 cell_6_4) (range_split cell_6_8 cell_6_12)) (range_split (range_split cell_6_16 cell_6_20) (range_split cell_6_24 cell_6_28))) (range_split (range_split (range_split cell_6_32 cell_6_36) (range_split cell_6_40 cell_6_44)) (range_split (range_split cell_6_48 cell_6_52) (range_split cell_6_56 cell_6_60)))) (range_split (range_split (range_split (range_split cell_6_64 cell_6_68) (range_split cell_6_72 cell_6_76)) (range_split (range_split cell_6_80 cell_6_84) (range_split cell_6_88 cell_6_92))) (range_split (range_split (range_split cell_6_96 cell_6_100) (range_split cell_6_104 cell_6_108)) (range_split (range_split cell_6_112 cell_6_116) (range_split cell_6_120 cell_6_124))))) (range_split (range_split (range_split (range_split (range_split cell_6_128 cell_6_132) (range_split cell_6_136 cell_6_140)) (range_split (range_split cell_6_144 cell_6_148) (range_split cell_6_152 cell_6_156))) (range_split (range_split (range_split cell_6_160 cell_6_164) (range_split cell_6_168 cell_6_172)) (range_split (range_split cell_6_176 cell_6_180) (range_split cell_6_184 cell_6_188)))) (range_split (range_split (range_split (range_split cell_6_192 cell_6_196) (range_split cell_6_200 cell_6_204)) (range_split (range_split cell_6_208 cell_6_212) (range_split cell_6_216 cell_6_220))) (range_split (range_split (range_split cell_6_224 cell_6_228) (range_split cell_6_232 cell_6_236)) (range_split (range_split cell_6_240 cell_6_244) (range_split cell_6_248 cell_6_252)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_6_256 cell_6_260) (range_split cell_6_264 cell_6_268)) (range_split (range_split cell_6_272 cell_6_276) (range_split cell_6_280 cell_6_284))) (range_split (range_split (range_split cell_6_288 cell_6_292) (range_split cell_6_296 cell_6_300)) (range_split (range_split cell_6_304 cell_6_308) (range_split cell_6_312 cell_6_316)))) (range_split (range_split (range_split (range_split cell_6_320 cell_6_324) (range_split cell_6_328 cell_6_332)) (range_split (range_split cell_6_336 cell_6_340) (range_split cell_6_344 cell_6_348))) (range_split (range_split (range_split cell_6_352 cell_6_356) (range_split cell_6_360 cell_6_364)) (range_split (range_split cell_6_368 cell_6_372) (range_split cell_6_376 cell_6_380))))) (range_split (range_split (range_split (range_split (range_split cell_6_384 cell_6_388) (range_split cell_6_392 cell_6_396)) (range_split (range_split cell_6_400 cell_6_404) (range_split cell_6_408 cell_6_412))) (range_split (range_split (range_split cell_6_416 cell_6_420) (range_split cell_6_424 cell_6_428)) (range_split (range_split cell_6_432 cell_6_436) (range_split cell_6_440 cell_6_444)))) (range_split (range_split (range_split (range_split cell_6_448 cell_6_452) (range_split cell_6_456 cell_6_460)) (range_split (range_split cell_6_464 cell_6_468) (range_split cell_6_472 cell_6_476))) (range_split (range_split (range_split cell_6_480 cell_6_484) (range_split cell_6_488 cell_6_492)) (range_split (range_split cell_6_496 cell_6_500) (range_split cell_6_504 cell_6_508)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_0 : ∀ i, 0 ≤ i → i < 4 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_4 : ∀ i, 4 ≤ i → i < 8 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_8 : ∀ i, 8 ≤ i → i < 12 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_12 : ∀ i, 12 ≤ i → i < 16 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_16 : ∀ i, 16 ≤ i → i < 20 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_20 : ∀ i, 20 ≤ i → i < 24 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_24 : ∀ i, 24 ≤ i → i < 28 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_28 : ∀ i, 28 ≤ i → i < 32 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_32 : ∀ i, 32 ≤ i → i < 36 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_36 : ∀ i, 36 ≤ i → i < 40 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_40 : ∀ i, 40 ≤ i → i < 44 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_44 : ∀ i, 44 ≤ i → i < 48 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_48 : ∀ i, 48 ≤ i → i < 52 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_52 : ∀ i, 52 ≤ i → i < 56 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_56 : ∀ i, 56 ≤ i → i < 60 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_60 : ∀ i, 60 ≤ i → i < 64 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_64 : ∀ i, 64 ≤ i → i < 68 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_68 : ∀ i, 68 ≤ i → i < 72 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_72 : ∀ i, 72 ≤ i → i < 76 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_76 : ∀ i, 76 ≤ i → i < 80 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_80 : ∀ i, 80 ≤ i → i < 84 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_84 : ∀ i, 84 ≤ i → i < 88 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_88 : ∀ i, 88 ≤ i → i < 92 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_92 : ∀ i, 92 ≤ i → i < 96 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_96 : ∀ i, 96 ≤ i → i < 100 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_100 : ∀ i, 100 ≤ i → i < 104 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_104 : ∀ i, 104 ≤ i → i < 108 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_108 : ∀ i, 108 ≤ i → i < 112 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_112 : ∀ i, 112 ≤ i → i < 116 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_116 : ∀ i, 116 ≤ i → i < 120 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_120 : ∀ i, 120 ≤ i → i < 124 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_124 : ∀ i, 124 ≤ i → i < 128 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_128 : ∀ i, 128 ≤ i → i < 132 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_132 : ∀ i, 132 ≤ i → i < 136 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 132 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_136 : ∀ i, 136 ≤ i → i < 140 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_140 : ∀ i, 140 ≤ i → i < 144 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 140 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_144 : ∀ i, 144 ≤ i → i < 148 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_148 : ∀ i, 148 ≤ i → i < 152 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 148 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_152 : ∀ i, 152 ≤ i → i < 156 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_156 : ∀ i, 156 ≤ i → i < 160 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 156 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_160 : ∀ i, 160 ≤ i → i < 164 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_164 : ∀ i, 164 ≤ i → i < 168 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 164 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_168 : ∀ i, 168 ≤ i → i < 172 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_172 : ∀ i, 172 ≤ i → i < 176 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 172 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_176 : ∀ i, 176 ≤ i → i < 180 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_180 : ∀ i, 180 ≤ i → i < 184 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 180 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_184 : ∀ i, 184 ≤ i → i < 188 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_188 : ∀ i, 188 ≤ i → i < 192 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 188 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_192 : ∀ i, 192 ≤ i → i < 196 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_196 : ∀ i, 196 ≤ i → i < 200 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 196 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_200 : ∀ i, 200 ≤ i → i < 204 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_204 : ∀ i, 204 ≤ i → i < 208 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 204 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_208 : ∀ i, 208 ≤ i → i < 212 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_212 : ∀ i, 212 ≤ i → i < 216 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 212 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_216 : ∀ i, 216 ≤ i → i < 220 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_220 : ∀ i, 220 ≤ i → i < 224 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 220 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_224 : ∀ i, 224 ≤ i → i < 228 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_228 : ∀ i, 228 ≤ i → i < 232 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 228 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_232 : ∀ i, 232 ≤ i → i < 236 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_236 : ∀ i, 236 ≤ i → i < 240 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 236 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_240 : ∀ i, 240 ≤ i → i < 244 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_244 : ∀ i, 244 ≤ i → i < 248 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 244 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_248 : ∀ i, 248 ≤ i → i < 252 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_252 : ∀ i, 252 ≤ i → i < 256 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 252 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_256 : ∀ i, 256 ≤ i → i < 260 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_260 : ∀ i, 260 ≤ i → i < 264 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 260 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_264 : ∀ i, 264 ≤ i → i < 268 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_268 : ∀ i, 268 ≤ i → i < 272 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 268 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_272 : ∀ i, 272 ≤ i → i < 276 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_276 : ∀ i, 276 ≤ i → i < 280 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 276 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_280 : ∀ i, 280 ≤ i → i < 284 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_284 : ∀ i, 284 ≤ i → i < 288 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 284 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_288 : ∀ i, 288 ≤ i → i < 292 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_292 : ∀ i, 292 ≤ i → i < 296 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 292 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_296 : ∀ i, 296 ≤ i → i < 300 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_300 : ∀ i, 300 ≤ i → i < 304 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 300 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_304 : ∀ i, 304 ≤ i → i < 308 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_308 : ∀ i, 308 ≤ i → i < 312 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 308 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_312 : ∀ i, 312 ≤ i → i < 316 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_316 : ∀ i, 316 ≤ i → i < 320 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 316 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_320 : ∀ i, 320 ≤ i → i < 324 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_324 : ∀ i, 324 ≤ i → i < 328 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 324 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_328 : ∀ i, 328 ≤ i → i < 332 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_332 : ∀ i, 332 ≤ i → i < 336 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 332 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_336 : ∀ i, 336 ≤ i → i < 340 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_340 : ∀ i, 340 ≤ i → i < 344 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 340 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_344 : ∀ i, 344 ≤ i → i < 348 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_348 : ∀ i, 348 ≤ i → i < 352 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 348 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_352 : ∀ i, 352 ≤ i → i < 356 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_356 : ∀ i, 356 ≤ i → i < 360 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 356 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_360 : ∀ i, 360 ≤ i → i < 364 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_364 : ∀ i, 364 ≤ i → i < 368 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 364 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_368 : ∀ i, 368 ≤ i → i < 372 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_372 : ∀ i, 372 ≤ i → i < 376 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 372 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_376 : ∀ i, 376 ≤ i → i < 380 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_380 : ∀ i, 380 ≤ i → i < 384 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 380 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_384 : ∀ i, 384 ≤ i → i < 388 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_388 : ∀ i, 388 ≤ i → i < 392 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 388 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_392 : ∀ i, 392 ≤ i → i < 396 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_396 : ∀ i, 396 ≤ i → i < 400 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 396 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_400 : ∀ i, 400 ≤ i → i < 404 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_404 : ∀ i, 404 ≤ i → i < 408 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 404 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_408 : ∀ i, 408 ≤ i → i < 412 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_412 : ∀ i, 412 ≤ i → i < 416 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 412 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_416 : ∀ i, 416 ≤ i → i < 420 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_420 : ∀ i, 420 ≤ i → i < 424 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 420 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_424 : ∀ i, 424 ≤ i → i < 428 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_428 : ∀ i, 428 ≤ i → i < 432 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 428 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_432 : ∀ i, 432 ≤ i → i < 436 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_436 : ∀ i, 436 ≤ i → i < 440 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 436 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_440 : ∀ i, 440 ≤ i → i < 444 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_444 : ∀ i, 444 ≤ i → i < 448 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 444 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_448 : ∀ i, 448 ≤ i → i < 452 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_452 : ∀ i, 452 ≤ i → i < 456 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 452 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_456 : ∀ i, 456 ≤ i → i < 460 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_460 : ∀ i, 460 ≤ i → i < 464 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 460 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_464 : ∀ i, 464 ≤ i → i < 468 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_468 : ∀ i, 468 ≤ i → i < 472 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 468 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_472 : ∀ i, 472 ≤ i → i < 476 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_476 : ∀ i, 476 ≤ i → i < 480 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 476 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_480 : ∀ i, 480 ≤ i → i < 484 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_484 : ∀ i, 484 ≤ i → i < 488 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 484 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_488 : ∀ i, 488 ≤ i → i < 492 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_492 : ∀ i, 492 ≤ i → i < 496 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 492 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_496 : ∀ i, 496 ≤ i → i < 500 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_500 : ∀ i, 500 ≤ i → i < 504 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 500 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_504 : ∀ i, 504 ≤ i → i < 508 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_508 : ∀ i, 508 ≤ i → i < 512 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 4 508 = true)
private theorem lvl_7 : ∀ i, 0 ≤ i → i < 512 → cellCheck 7 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_7_0 cell_7_4) (range_split cell_7_8 cell_7_12)) (range_split (range_split cell_7_16 cell_7_20) (range_split cell_7_24 cell_7_28))) (range_split (range_split (range_split cell_7_32 cell_7_36) (range_split cell_7_40 cell_7_44)) (range_split (range_split cell_7_48 cell_7_52) (range_split cell_7_56 cell_7_60)))) (range_split (range_split (range_split (range_split cell_7_64 cell_7_68) (range_split cell_7_72 cell_7_76)) (range_split (range_split cell_7_80 cell_7_84) (range_split cell_7_88 cell_7_92))) (range_split (range_split (range_split cell_7_96 cell_7_100) (range_split cell_7_104 cell_7_108)) (range_split (range_split cell_7_112 cell_7_116) (range_split cell_7_120 cell_7_124))))) (range_split (range_split (range_split (range_split (range_split cell_7_128 cell_7_132) (range_split cell_7_136 cell_7_140)) (range_split (range_split cell_7_144 cell_7_148) (range_split cell_7_152 cell_7_156))) (range_split (range_split (range_split cell_7_160 cell_7_164) (range_split cell_7_168 cell_7_172)) (range_split (range_split cell_7_176 cell_7_180) (range_split cell_7_184 cell_7_188)))) (range_split (range_split (range_split (range_split cell_7_192 cell_7_196) (range_split cell_7_200 cell_7_204)) (range_split (range_split cell_7_208 cell_7_212) (range_split cell_7_216 cell_7_220))) (range_split (range_split (range_split cell_7_224 cell_7_228) (range_split cell_7_232 cell_7_236)) (range_split (range_split cell_7_240 cell_7_244) (range_split cell_7_248 cell_7_252)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_7_256 cell_7_260) (range_split cell_7_264 cell_7_268)) (range_split (range_split cell_7_272 cell_7_276) (range_split cell_7_280 cell_7_284))) (range_split (range_split (range_split cell_7_288 cell_7_292) (range_split cell_7_296 cell_7_300)) (range_split (range_split cell_7_304 cell_7_308) (range_split cell_7_312 cell_7_316)))) (range_split (range_split (range_split (range_split cell_7_320 cell_7_324) (range_split cell_7_328 cell_7_332)) (range_split (range_split cell_7_336 cell_7_340) (range_split cell_7_344 cell_7_348))) (range_split (range_split (range_split cell_7_352 cell_7_356) (range_split cell_7_360 cell_7_364)) (range_split (range_split cell_7_368 cell_7_372) (range_split cell_7_376 cell_7_380))))) (range_split (range_split (range_split (range_split (range_split cell_7_384 cell_7_388) (range_split cell_7_392 cell_7_396)) (range_split (range_split cell_7_400 cell_7_404) (range_split cell_7_408 cell_7_412))) (range_split (range_split (range_split cell_7_416 cell_7_420) (range_split cell_7_424 cell_7_428)) (range_split (range_split cell_7_432 cell_7_436) (range_split cell_7_440 cell_7_444)))) (range_split (range_split (range_split (range_split cell_7_448 cell_7_452) (range_split cell_7_456 cell_7_460)) (range_split (range_split cell_7_464 cell_7_468) (range_split cell_7_472 cell_7_476))) (range_split (range_split (range_split cell_7_480 cell_7_484) (range_split cell_7_488 cell_7_492)) (range_split (range_split cell_7_496 cell_7_500) (range_split cell_7_504 cell_7_508)))))))

private theorem checkedCells (s : Nat) (hs : s ≤ 7) (i : Nat) (hi : i < 512) : cellCheck s i = true := by
  interval_cases s <;> first | exact lvl_0 i (Nat.zero_le i) hi | exact lvl_1 i (Nat.zero_le i) hi | exact lvl_2 i (Nat.zero_le i) hi | exact lvl_3 i (Nat.zero_le i) hi | exact lvl_4 i (Nat.zero_le i) hi | exact lvl_5 i (Nat.zero_le i) hi | exact lvl_6 i (Nat.zero_le i) hi | exact lvl_7 i (Nat.zero_le i) hi

private theorem impossibleState : ∀ s ≤ 7, ∀ i < 512, ∀ ws ∈ (rowsOf s).getD i [], ¬ RunD truthMask goal s ws := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi ws hw hrun
    have hc := List.all_eq_true.1 (show ((rowsOf s).getD i []).all (blocked s) = true from checkedCells s hs i hi) ws hw
    cases s with
    | zero => simp [blocked, zero_done hrun rfl] at hc
    | succ s =>
      have good (ys : List Nat) (h : RunD truthMask goal s ys) :
          (coversP pairs s ys && !(listed s ys)) = true := by
        have hcov := coversP_ok (by decide +kernel : truthMask &&& truthMask = truthMask) pairs validPairs h
        rw [hcov, Bool.true_and, Bool.not_eq_true', listed, List.any_eq_false]
        intro zs hzs
        by_contra! hb
        exact ih s (by omega) (by omega) (key ys) (key_lt ys) zs hzs (Run.perm (List.isPerm_iff.1 hb) h)
      have hn := nextD_complete hrun s rfl ws (List.Perm.refl _) _ good
      simp [blocked, hn] at hc

def rootCheck (s : Nat) (ws : List Nat) : Bool :=
  decide (s + 1 < ws.length) || !(coversP pairs s ws) || listed s ws

def inputSubsets : List (List Nat) := roots.sublists

def rootCheckAt (i : Nat) : Bool :=
  (List.range 8).all (fun s => rootCheck s (inputSubsets.getD i []))

private theorem subsetCount : inputSubsets.length = 256 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_0 : ∀ i, 0 ≤ i → i < 32 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 32 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_32 : ∀ i, 32 ≤ i → i < 64 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 32 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_64 : ∀ i, 64 ≤ i → i < 96 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 32 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_96 : ∀ i, 96 ≤ i → i < 128 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 32 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_128 : ∀ i, 128 ≤ i → i < 160 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 32 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_160 : ∀ i, 160 ≤ i → i < 192 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 32 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_192 : ∀ i, 192 ≤ i → i < 224 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 32 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_224 : ∀ i, 224 ≤ i → i < 256 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 32 224 = true)
private theorem checkedRoots : ∀ i, 0 ≤ i → i < 256 → rootCheckAt i = true :=
  (range_split (range_split (range_split rootBlock_0 rootBlock_32) (range_split rootBlock_64 rootBlock_96)) (range_split (range_split rootBlock_128 rootBlock_160) (range_split rootBlock_192 rootBlock_224)))

private theorem impossibleRoot {s : Nat} {ws : List Nat} (hs : s ≤ 7)
    (hsub : ws.Sublist roots) (hrun : RunD truthMask goal s ws) : False := by
  obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.1 (show ws ∈ inputSubsets from List.mem_sublists.2 hsub)
  have hc : rootCheck s ws = true := by
    have hv := checkedRoots i (Nat.zero_le i) (subsetCount ▸ hi)
    have hv' := List.all_eq_true.1 hv s (List.mem_range.2 (by omega))
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, h] using hv'
  have hcov := coversP_ok (by decide +kernel : truthMask &&& truthMask = truthMask) pairs validPairs hrun
  have hlen := run_len hrun
  have hblocked : listed s ws = true := by
    simpa [rootCheck, hcov, Nat.not_lt.mpr hlen] using hc
  obtain ⟨zs, hzs, hz⟩ := List.any_eq_true.1 hblocked
  exact impossibleState s hs (key ws) (key_lt ws) zs hzs (Run.perm (List.isPerm_iff.1 hz) hrun)

private theorem rootsAgree : ∀ r : Fin 16,
    roots.map (·.testBit r.val) = PEqualNP.Represents.oneEach
      (Fin.ofNat 4 (r.val / 4)) (Fin.ofNat 4 (r.val % 4)) := by decide +kernel

private theorem domainRows : ∀ r : Fin 16, truthMask.testBit r.val = true := by decide +kernel
private theorem targetIndex : ∀ r : Fin 16, 4 * (r.val / 4) + (r.val % 4) = r.val := by decide

private theorem rulesOut (C : Circuit) (hfan : FanInTwo C) (hs : C.size ≤ 7)
    (hrep : PEqualNP.Represents.Represents
      (fun u v : Fin 4 => target.testBit (4 * u.val + v.val)) C) : False := by
  have hsup0 : ∀ v ∈ roots, Avail truthMask roots v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots hfan 0 roots roots rfl hsup0
  set out := (execN C.gates roots).getD C.output 0
  have hout : out &&& truthMask = target &&& truthMask := by
    apply Nat.eq_of_testBit_eq
    intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 16
    · rw [domainRows ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [rootsAgree ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots).map (·.testBit r)).getD C.output false = out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have hr5 : r / 4 < 4 := by omega
      have hcol : r % 4 < 4 := Nat.mod_lt _ (by decide)
      have hv := hrep (Fin.ofNat 4 (r / 4)) (Fin.ofNat 4 (r % 4))
      simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hr5, Nat.mod_eq_of_lt hcol] at hv
      rw [targetIndex ⟨r, hlt⟩] at hv
      exact h2.trans hv
    · have hd : truthMask.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h25 : truthMask < 2 ^ 16 := by decide
        exact lt_of_lt_of_le h25 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail truthMask bank out := by
    by_cases hi : C.output < (execN C.gates roots).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]
      exact Or.inl (Or.inl (by simp))
  have hn : ¬ IsConst truthMask target := by unfold IsConst target truthMask; decide
  obtain ⟨s, ws, hsp, hnd, hrin, hrun⟩ :=
    reach_to_run (by decide +kernel : truthMask &&& truthMask = truthMask) hn hr (avail_of_eq hout hav_out)
  have hmask : roots.map (· &&& truthMask) = roots := by decide
  rw [hmask] at hrin
  have hrnd : roots.Nodup := by decide
  let sub := roots.filter (fun x => decide (x ∈ ws))
  have hsub : sub.Sublist roots := List.filter_sublist
  have hp' : ws.Perm sub := by
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hrnd)).2 ?_
    intro x
    simp only [sub, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hrin x hx, hx⟩, fun h => h.2⟩
  have hz : C.gates.length ≤ 7 := hs
  exact impossibleRoot (by omega) hsub (Run.perm hp' hrun)

def e_stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem e_len (gs : List Gate) (x : List Bool) : (gs.foldl e_stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, e_stp, ih]; omega

theorem e_getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem e_ev (C : Circuit) (x : List Bool) : C.eval x = (C.gates.foldl e_stp x).getD C.output false := rfl

def e_rho (c w' : ℕ) (i : ℕ) : ℕ := if i < c then i else if i = c then w' else i - 1

def e_rg (c w' : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (e_rho c w')⟩

def e_Inv (c w' : ℕ) (Wo Wn : List Bool) : Prop :=
  Wo.length = Wn.length + 1 ∧ ∀ i, Wn.getD (e_rho c w' i) false = Wo.getD i false

theorem e_sim (c w' K : ℕ) (hw : w' < c ∨ K ≤ w') : ∀ (post : List Gate) (Wo Wn : List Bool),
    e_Inv c w' Wo Wn → c < Wo.length → Wn.length + post.length ≤ K →
    e_Inv c w' (post.foldl e_stp Wo) ((post.map (e_rg c w')).foldl e_stp Wn) := by
  intro post
  induction post with
  | nil => intro Wo Wn h _ _; simpa using h
  | cons g post ih =>
    intro Wo Wn h hc hK
    simp only [List.foldl_cons, List.map_cons]
    simp only [List.length_cons] at hK
    obtain ⟨hl, hv⟩ := h
    have hb : (e_rg c w' g).op.eval ((e_rg c w' g).inputs.map fun i => Wn.getD i false) =
        g.op.eval (g.inputs.map fun i => Wo.getD i false) := by
      simp only [e_rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hv i
    apply ih
    · refine ⟨by simp [e_stp, hl], ?_⟩
      intro i
      simp only [e_stp]
      rw [hb, e_getD_snoc, e_getD_snoc]
      have hvi := hv i
      by_cases h1 : i < c
      · have e : e_rho c w' i = i := by simp [e_rho, h1]
        rw [e] at hvi ⊢
        rw [if_pos (by omega), if_pos (by omega)]; exact hvi
      · by_cases h2 : i = c
        · have e : e_rho c w' i = w' := by simp [e_rho, h2]
          rw [e] at hvi ⊢
          rw [if_pos (by omega : i < Wo.length)]
          rcases hw with hw | hw
          · rw [if_pos (by omega)]; exact hvi
          · rw [if_neg (by omega), if_neg (by omega)]
            rw [← hvi, List.getD_eq_default _ _ (by omega)]
        · have e : e_rho c w' i = i - 1 := by simp [e_rho, h1, h2]
          rw [e] at hvi ⊢
          by_cases h3 : i < Wo.length
          · rw [if_pos h3, if_pos (by omega)]; exact hvi
          · by_cases h4 : i = Wo.length
            · rw [if_neg h3, if_pos h4, if_neg (by omega), if_pos (by omega)]
            · rw [if_neg h3, if_neg h4, if_neg (by omega), if_neg (by omega)]
    · simp [e_stp]; omega
    · simp [e_stp]; omega

theorem e_alias (g : Gate) (c K : ℕ) (hcK : c ≤ K)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length ≤ 2) (hd : K ∈ g.inputs) :
    ∃ w', (w' < c ∨ K ≤ w') ∧ ∀ L : List Bool, L.length = c →
      g.op.eval (g.inputs.map fun i => L.getD i false) = L.getD w' false := by
  have dead : ∀ L : List Bool, L.length = c → L.getD K false = false :=
    fun L hL => List.getD_eq_default _ _ (by omega)
  obtain ⟨op, l⟩ := g
  simp only at hop hl hd
  rcases hop with rfl | rfl
  · refine ⟨K, Or.inr le_rfl, fun L hL => ?_⟩
    rw [dead L hL]
    simp only [GateOp.eval]
    rw [List.all_eq_false]
    exact ⟨false, List.mem_map.2 ⟨K, hd, dead L hL⟩, by simp⟩
  · match l, hl, hd with
    | [], _, hd => simp at hd
    | [a], _, hd =>
      obtain rfl : K = a := by simpa using hd
      refine ⟨K, Or.inr le_rfl, fun L hL => ?_⟩
      change (L.getD K false || false) = L.getD K false
      simp
    | [a, b], _, hd =>
      have hab : a = K ∨ b = K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      rcases hab with rfl | rfl
      · by_cases hb : b < c
        · refine ⟨b, Or.inl hb, fun L hL => ?_⟩
          change (L.getD a false || (L.getD b false || false)) = L.getD b false
          rw [dead L hL]; simp
        · refine ⟨a, Or.inr le_rfl, fun L hL => ?_⟩
          change (L.getD a false || (L.getD b false || false)) = L.getD a false
          rw [dead L hL, List.getD_eq_default L false (by omega : L.length ≤ b)]; rfl
      · by_cases ha : a < c
        · refine ⟨a, Or.inl ha, fun L hL => ?_⟩
          change (L.getD a false || (L.getD b false || false)) = L.getD a false
          rw [dead L hL]; simp
        · refine ⟨b, Or.inr le_rfl, fun L hL => ?_⟩
          change (L.getD a false || (L.getD b false || false)) = L.getD b false
          rw [dead L hL, List.getD_eq_default L false (by omega : L.length ≤ a)]; rfl
    | _ :: _ :: _ :: _, hl, _ => simp at hl

theorem e_elim (C : Circuit) (N p : ℕ) (hp : p < N) (hM : Monotone2 C) (g : Gate)
    (hg : g ∈ C.gates) (hpg : p ∈ g.inputs) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size + 1 = C.size ∧
      ∀ x y : List Bool, x.length = N → e_Inv p (N - 1 + C.size) x y → C'.eval y = C.eval x := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
  have hsz : C.size = pre.length + post.length + 1 := by
    simp [Circuit.size, hsplit]; omega
  obtain ⟨w', hw', hal⟩ := e_alias (e_rg p (N - 1 + C.size) g) (N - 1 + pre.length) (N - 1 + C.size)
    (by omega) (by simpa [e_rg, hsplit] using (hM g hg).1) (by simpa [e_rg] using (hM g hg).2)
    (by
      simp only [e_rg, List.mem_map]
      exact ⟨p, hpg, by simp [e_rho]⟩)
  refine ⟨⟨pre.map (e_rg p (N - 1 + C.size)) ++
      (post.map (e_rg p (N - 1 + C.size))).map (e_rg (N - 1 + pre.length) w'),
      e_rho (N - 1 + pre.length) w' (e_rho p (N - 1 + C.size) C.output)⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_map] at hg'
    rcases hg' with ⟨a, ha, rfl⟩ | ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    · have := hM a (by rw [hsplit]; simp [ha])
      simpa [e_rg] using this
    · have := hM a (by rw [hsplit]; simp [ha])
      simpa [e_rg] using this
  · have := hsz
    simp only [Circuit.size] at this ⊢
    simp only [List.length_append, List.length_map]
    omega
  · intro x y hx hI
    have hy : y.length = N - 1 := by have := hI.1; omega
    have h1 := e_sim p (N - 1 + C.size) (N - 1 + C.size) (Or.inr le_rfl) C.gates x y hI (by omega)
      (by simp [Circuit.size, hy])
    rw [e_ev, e_ev]
    simp only
    rw [← h1.2 C.output]
    rw [hsplit]
    simp only [List.map_append, List.map_cons, List.foldl_append, List.foldl_cons]
    set L := (pre.map (e_rg p (N - 1 + C.size))).foldl e_stp y with hL
    have hLl : L.length = N - 1 + pre.length := by rw [hL, e_len, hy]; simp
    have h2 := e_sim (N - 1 + pre.length) w' (N - 1 + C.size) hw'
      (post.map (e_rg p (N - 1 + C.size))) (e_stp L (e_rg p (N - 1 + C.size) g)) L
      (by
        refine ⟨by simp [e_stp], ?_⟩
        intro i
        simp only [e_stp]
        rw [hal L hLl, e_getD_snoc]
        by_cases h1 : i < N - 1 + pre.length
        · rw [if_pos (by omega)]; simp [e_rho, h1]
        · by_cases h2 : i = N - 1 + pre.length
          · rw [if_neg (by omega), if_pos (by omega)]; simp [e_rho, h2]
          · rw [if_neg (by omega), if_neg (by omega)]
            simp only [e_rho, if_neg h1, if_neg h2]
            exact List.getD_eq_default _ _ (by omega))
      (by simp [e_stp]; omega) (by simp [hLl]; omega)
    exact h2.2 _

theorem e_dep (N : ℕ) (P : ℕ → Prop) (gs : List Gate)
    (hP : ∀ j (h : j < gs.length), P (N + j) → ∀ i ∈ (gs[j]).inputs, i < N + j → P i)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, P i → x.getD i false = y.getD i false) :
    ∀ w, P w → (gs.foldl e_stp x).getD w false = (gs.foldl e_stp y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil => simpa using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun j h hj i hi hlt => hP j (by simp; omega) hj i (by
      rw [List.getElem_append_left h]; exact hi) hlt)
    intro w hw
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, e_stp]
    rw [e_getD_snoc, e_getD_snoc, e_len, e_len, hx, hy]
    split_ifs with h1 h3
    · exact ih w hw
    · congr 1
      refine List.map_congr_left fun i hi => ?_
      by_cases hlt : i < N + gs.length
      · exact ih i (hP gs.length (by simp) (h3 ▸ hw) i (by simpa using hi) hlt)
      · rw [List.getD_eq_default _ _ (by rw [e_len, hx]; omega),
          List.getD_eq_default _ _ (by rw [e_len, hy]; omega)]
    · rfl

theorem e_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (gs.foldl e_stp x).getD i false = true → (gs.foldl e_stp y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa using hxy
  | append_singleton gs g ih =>
    have ih := ih fun g' h => hg g' (by simp [h])
    intro i
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, e_stp]
    rw [e_getD_snoc, e_getD_snoc, e_len, e_len, hl]
    split_ifs
    · exact ih i
    · rcases hg g (by simp) with h | h
      · simp only [h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
        exact fun hh a ha => ih a (hh a ha)
      · simp only [h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact fun ⟨a, ha, hh⟩ => ⟨a, ha, ih a hh⟩
    · simp

theorem e_pre (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl e_stp x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, e_stp]
    rw [e_getD_snoc, e_len, if_pos (by omega)]
    exact ih

theorem e_oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [PEqualNP.Represents.oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem e_setD (x : List Bool) (k : ℕ) : ∀ i, (x.set k false).getD i false =
    if i = k then false else x.getD i false := by
  intro i
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases h : k = i
  · subst h; simp only [ite_true]; split_ifs <;> rfl
  · simp [h, Ne.symm h]

theorem e_rm (C : Circuit) (N p : ℕ) (hp : p < N) (hM : Monotone2 C) (x1 x2 x3 : List Bool)
    (l1 : x1.length = N) (l2 : x2.length = N) (l3 : x3.length = N)
    (h1 : C.eval x1 = true) (h2 : C.eval x2 = false)
    (h12 : ∀ i, i ≠ p → x1.getD i false = true → x2.getD i false = true)
    (h3 : C.eval x3 = true) (h3p : x3.getD p false = false) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size + 1 = C.size ∧
      ∀ x y : List Bool, x.length = N → e_Inv p (N - 1 + C.size) x y → C'.eval y = C.eval x := by
  by_cases hr : ∃ g ∈ C.gates, p ∈ g.inputs
  · obtain ⟨g, hg, hpg⟩ := hr
    exact e_elim C N p hp hM g hg hpg
  · exfalso
    have hr' : ∀ g ∈ C.gates, p ∉ g.inputs := fun g hg hpg => hr ⟨g, hg, hpg⟩
    by_cases ho : C.output = p
    · rw [e_ev, ho, e_pre _ _ _ (by omega), h3p] at h3
      exact absurd h3 (by simp)
    · have eq := e_dep N (fun i => i ≠ p) C.gates
        (fun j h _ i hi _ hip => hr' _ (List.getElem_mem h) (hip ▸ hi))
        x1 (x1.set p false) l1 (by simp [l1])
        (fun i hi => by rw [e_setD, if_neg hi]) C.output ho
      rw [e_ev] at h1 h2
      rw [eq] at h1
      have := e_mono C.gates (fun g hg => by simpa using (hM g hg).1) (x1.set p false) x2
        (by simp [l1, l2]) (fun i hi => by
          rw [e_setD] at hi
          split_ifs at hi with h
          exact h12 i h hi) C.output h1
      rw [h2] at this
      exact absurd this (by simp)

def e_A (n : ℕ) : Fin n → Fin n → Bool :=
  fun u v => decide ((u.val = 0 ∧ 2 ≤ v.val) ∨ (u.val = 1 ∧ (v.val ≤ 1 ∨ 3 ≤ v.val)) ∨ (u.val = 2 ∧ v.val ≤ 1) ∨ (3 ≤ u.val ∧ v.val ≤ 2))

theorem e_base (C : Circuit) (hM : Monotone2 C) (hR : PEqualNP.Represents.Represents (e_A 4) C) :
    8 ≤ C.size := by
  by_contra hs
  have hfan : FanInTwo C := by
    intro g hg
    obtain ⟨h1, h2⟩ := hM g hg
    refine ⟨?_, h2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
    tauto
  have e : e_A 4 = (fun u v : Fin 4 => target.testBit (4 * u.val + v.val)) := by
    funext u v
    fin_cases u <;> fin_cases v <;> decide
  rw [e] at hR
  exact rulesOut C hfan (by omega) hR

theorem e_step (n : ℕ) (hn : 4 ≤ n) (C : Circuit) (hM : Monotone2 C)
    (hR : PEqualNP.Represents.Represents (e_A (n + 1)) C) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size + 2 = C.size ∧ PEqualNP.Represents.Represents (e_A n) C' := by
  have r1 := hR ⟨n, by omega⟩ ⟨0, by omega⟩
  have r2 := hR ⟨0, by omega⟩ ⟨0, by omega⟩
  have r3 := hR ⟨0, by omega⟩ ⟨2, by omega⟩
  obtain ⟨C1, hM1, hs1, hC1⟩ := e_rm C (n + 1 + (n + 1)) n (by omega) hM _ _ _
    (by simp [PEqualNP.Represents.oneEach] <;> omega) (by simp [PEqualNP.Represents.oneEach] <;> omega)
    (by simp [PEqualNP.Represents.oneEach] <;> omega)
    (r1.trans (by simp [e_A] <;> omega))
    (r2.trans (by simp [e_A] <;> omega))
    (fun i hi h => by
      rw [e_oe] at h ⊢
      simp only at h ⊢
      omega)
    (r3.trans (by simp [e_A] <;> omega))
    (by
      rw [Bool.eq_false_iff, Ne, e_oe]
      simp only
      omega)
  have hR1 : ∀ (u : Fin n) (v : Fin (n + 1)), C1.eval (PEqualNP.Represents.oneEach u v) =
      e_A (n + 1) ⟨u.val, by omega⟩ v := by
    intro u v
    rw [← hR ⟨u.val, by omega⟩ v]
    apply hC1 _ _ (by simp [PEqualNP.Represents.oneEach] <;> omega)
    refine ⟨by simp [PEqualNP.Represents.oneEach] <;> omega, fun i => ?_⟩
    rw [Bool.eq_iff_iff, e_oe, e_oe]
    have := u.isLt
    have := v.isLt
    simp only [e_rho]
    split_ifs <;> omega
  have q1 := hR1 ⟨0, by omega⟩ ⟨n - 1, by omega⟩
  have q2 := hR1 ⟨0, by omega⟩ ⟨0, by omega⟩
  have q3 := hR1 ⟨0, by omega⟩ ⟨n, by omega⟩
  obtain ⟨C2, hM2, hs2, hC2⟩ := e_rm C1 (n + (n + 1)) (n + (n - 1)) (by omega) hM1 _ _ _
    (by simp [PEqualNP.Represents.oneEach] <;> omega) (by simp [PEqualNP.Represents.oneEach] <;> omega)
    (by simp [PEqualNP.Represents.oneEach] <;> omega)
    (q1.trans (by simp [e_A] <;> omega))
    (q2.trans (by simp [e_A] <;> omega))
    (fun i hi h => by
      rw [e_oe] at h ⊢
      simp only at h ⊢
      omega)
    (q3.trans (by simp [e_A] <;> omega))
    (by
      rw [Bool.eq_false_iff, Ne, e_oe]
      simp only
      omega)
  refine ⟨C2, hM2, by omega, ?_⟩
  intro u v
  have hv := v.isLt
  have hu := u.isLt
  have key := hC2 (PEqualNP.Represents.oneEach u (⟨if v.val < n - 1 then v.val else v.val + 1, by split_ifs <;> omega⟩ : Fin (n + 1)))
    (PEqualNP.Represents.oneEach u v) (by simp [PEqualNP.Represents.oneEach] <;> omega) (by
      refine ⟨by simp [PEqualNP.Represents.oneEach] <;> omega, fun i => ?_⟩
      rw [Bool.eq_iff_iff, e_oe, e_oe]
      simp only [e_rho]
      split_ifs <;> omega)
  rw [key, hR1]
  simp only [e_A]
  rw [decide_eq_decide]
  by_cases hvn : v.val < n - 1 <;> simp only [hvn, if_true, if_false] <;> constructor <;> intro hh <;> omega

theorem e_main : ∀ n, 4 ≤ n → ∀ C : Circuit, Monotone2 C →
    PEqualNP.Represents.Represents (e_A n) C → 2 * n ≤ C.size := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro C hM hR; exact e_base C hM hR
  | succ n hn ih =>
    intro C hM hR
    obtain ⟨C', hM', hs, hR'⟩ := e_step n hn C hM hR
    have := ih C' hM' hR'
    omega


end PEqualNP.Outside.L_meta_20543

theorem PEqualNP.Outside.L_meta_20543 : ∀ n s : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u.val = 0 ∧ 2 ≤ v.val) ∨ (u.val = 1 ∧ (v.val ≤ 1 ∨ 3 ≤ v.val)) ∨ (u.val = 2 ∧ v.val ≤ 1) ∨ (3 ≤ u.val ∧ v.val ≤ 2))) s → 2 * n ≤ s := by
  intro n s hn h
  obtain ⟨C, hM, hs, hR⟩ := h
  have := PEqualNP.Outside.L_meta_20543.e_main n hn C hM hR
  omega

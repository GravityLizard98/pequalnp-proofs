import PEqualNP.Defs
import PEqualNP.Library.LRAT.PromiseN

namespace PEqualNP.Outside.L_meta_23965

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
def target : Nat := 25500
def goal : Nat := target &&& truthMask

def pairs : List (Nat × Nat) := [(5, 13), (6, 7), (12, 8), (12, 14), (10, 9), (5, 4), (1, 13), (0, 3), (11, 3), (11, 9), (11, 7), (6, 2), (12, 4), (0, 2), (10, 14), (1, 2), (15, 3), (15, 14), (5, 7), (11, 8), (6, 4), (0, 8), (6, 14), (1, 3), (5, 9), (0, 4), (10, 2), (15, 7), (12, 13), (10, 8), (1, 9), (15, 13), (12, 2), (0, 14), (12, 3), (1, 8), (11, 14), (15, 9), (6, 8), (10, 3), (0, 13), (12, 7), (11, 13), (1, 7), (1, 14), (6, 9), (6, 13), (15, 2), (1, 4), (10, 4), (11, 2), (11, 4), (0, 9), (5, 2), (5, 3), (10, 13), (12, 9), (15, 4)]

def key (ws : List Nat) : Nat := ws.sum % 128

theorem key_lt (ws : List Nat) : key ws < 128 := Nat.mod_lt _ (by decide)

def rowsOf : Nat → List (List (List Nat))
  | 3 => [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[255, 39321, 64250]], [], [], [], [], [], [], [], [], [], [], [[15, 1525, 39321], [255, 1285, 39321]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[175, 26214, 64170]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[255, 13107, 44975]], [], [], [], [], [], [], [], [], [[15, 1525, 26214], [255, 1285, 26214]], [], [], [], [], [], [], [], [[175, 39321, 64170]], [], [], [], [], [], [], [], [], [], [], [], [], []]
  | 4 => [[], [], [[15, 240, 4369, 29298], [255, 8751, 36744, 52428]], [], [[15, 255, 44970, 52428], [255, 3855, 43690, 52428]], [], [[15, 4369, 28484, 61986]], [[15, 1520, 13107, 21845], [15, 4080, 13107, 24405]], [[15, 4593, 26214, 61986], [255, 4080, 13107, 26214]], [], [[4383, 4593, 8946, 36744]], [], [], [[5, 13107, 24405, 61440], [15, 4080, 22005, 39321]], [], [], [], [[15, 4593, 26223, 61986]], [[15, 240, 39321, 64250]], [[15, 1911, 17652, 39321]], [], [], [[15, 4095, 13107, 24405], [15, 8754, 20292, 61713], [255, 3855, 13107, 21845]], [], [[15, 240, 28518, 62259]], [], [[15, 240, 4883, 36744], [15, 754, 4369, 36744], [15, 4369, 8946, 44936]], [], [[15, 4095, 22005, 39321]], [[15, 240, 1285, 39321], [15, 240, 4369, 36237]], [[15, 255, 26214, 64170]], [], [[15, 1520, 21845, 52428], [15, 4080, 24405, 52428]], [[15, 240, 4883, 36751], [15, 754, 4369, 36751]], [], [[15, 3067, 7953, 34952]], [], [], [[5, 24405, 52428, 61440]], [[255, 3855, 13107, 26214]], [], [], [], [], [[15, 7953, 35016, 62532]], [], [], [[15, 4095, 24405, 52428], [255, 3855, 21845, 52428]], [], [], [], [[4593, 7953, 34959, 61986]], [], [], [], [], [], [], [[15, 240, 1365, 26214], [15, 1520, 21845, 26214], [15, 4497, 35064, 61986]], [[255, 4080, 13107, 39321]], [], [], [], [], [[255, 3855, 26214, 52428]], [[4383, 4593, 34959, 61986]], [[15, 240, 39321, 64170]], [[15, 3549, 4593, 26214]], [], [], [], [], [], [[255, 3855, 21845, 26214]], [[4383, 8751, 17652, 63624]], [], [], [], [], [], [], [[15, 255, 39321, 64170]], [], [], [[255, 12066, 35064, 48059]], [], [], [], [], [], [[15, 4080, 22005, 26214], [255, 3855, 13107, 39321]], [], [[15, 240, 13107, 44970]], [], [[15, 8946, 20292, 36744, 61713]], [], [[15, 1911, 17652, 26214]], [[15, 240, 13107, 44975]], [], [[255, 12066, 13107, 34959]], [[15, 240, 40857, 64716]], [], [], [], [], [[15, 4095, 22005, 26214], [255, 8751, 13107, 36744]], [[15, 240, 1285, 26214], [15, 4593, 34952, 62050]], [[15, 255, 13107, 44970], [255, 3855, 13107, 43690]], [], [[15, 240, 1365, 39321], [15, 240, 12066, 19532], [15, 1520, 21845, 39321], [15, 2296, 12066, 17476], [15, 8946, 17508, 63624], [15, 12130, 17652, 34952]], [], [], [], [[15, 17652, 26214, 63624], [255, 8751, 48059, 63624]], [], [[15, 3838, 8738, 20292], [255, 3855, 39321, 52428]], [], [], [[15, 3549, 4593, 39321]], [], [], [], [[15, 240, 12079, 19532], [15, 2296, 12079, 17476], [15, 17652, 26223, 63624]], [], [[255, 3855, 21845, 39321], [255, 12066, 34959, 52428]], [[4383, 20292, 35064, 61986]], [], []]
  | 5 => [[], [], [[15, 240, 8751, 36744, 52428], [15, 240, 12079, 34952, 52428]], [], [[13, 4369, 8738, 20292, 61440], [15, 240, 3855, 43690, 52428], [15, 255, 3840, 43690, 52428], [15, 255, 4369, 36744, 56797], [15, 255, 8738, 36744, 52428], [15, 255, 12066, 34952, 52428]], [[15, 255, 8738, 20292, 61713], [15, 4095, 8738, 20292, 61713]], [[1, 4383, 8738, 20292, 61440], [15, 240, 3549, 4369, 39321], [15, 240, 4095, 13107, 21845], [15, 240, 4369, 44970, 52428], [15, 240, 12066, 39321, 52428], [15, 240, 13107, 43690, 44970], [15, 240, 13107, 43690, 64170], [15, 3840, 4369, 25668, 61986]], [[15, 240, 3840, 13107, 21845], [15, 240, 3840, 13107, 24405], [15, 240, 4369, 10018, 21845], [15, 240, 4369, 21845, 29218], [15, 240, 7953, 13107, 20292], [15, 4080, 7953, 13107, 17476]], [[15, 240, 4080, 13107, 26214], [15, 3840, 4593, 26214, 61986], [15, 4593, 26214, 61986]], [[15, 255, 8751, 17476, 63624]], [[15, 240, 4369, 8946, 36744], [15, 240, 4369, 34952, 62194], [15, 4080, 4369, 8946, 36744], [15, 4095, 4369, 17652, 30583]], [[15, 240, 3840, 13299, 39321], [15, 240, 4369, 13299, 36744], [15, 3840, 4593, 8946, 39321], [15, 4369, 4593, 8946, 36744]], [[15, 240, 7953, 34952, 62708]], [[5, 3840, 13107, 21845, 61440], [5, 4369, 8738, 24405, 61440], [15, 240, 3840, 22005, 39321], [15, 3840, 4593, 17652, 39321]], [[15, 240, 4095, 26214, 43690], [15, 3840, 4369, 8946, 17652, 63624], [15, 4369, 8946, 17652, 36744], [15, 4369, 8946, 17652, 63624]], [[15, 240, 12066, 13107, 48059], [15, 240, 12066, 21845, 39321], [15, 240, 13107, 21845, 36744], [15, 240, 13107, 21845, 63624]], [[15, 240, 4080, 21845, 52428]], [[15, 240, 3840, 13107, 21855], [15, 240, 4369, 8946, 36751], [15, 240, 4369, 34959, 62194], [15, 4080, 4593, 17476, 56797]], [[15, 240, 4369, 34952, 64250], [15, 4369, 8946, 35064, 36744], [15, 4369, 8946, 35064, 63624], [15, 4369, 8946, 36744, 36856]], [], [[15, 240, 4369, 36744, 52476], [15, 4369, 17652, 35064, 36744]], [[15, 240, 3581, 4369, 34952], [15, 240, 4369, 36744, 56829]], [[15, 240, 3855, 13107, 21845], [15, 255, 3840, 13107, 21845], [15, 3840, 4095, 13107, 21845]], [[15, 240, 1911, 17476, 56797], [15, 240, 4095, 13107, 26214], [15, 240, 4369, 44970, 56797], [15, 240, 8738, 36744, 61166], [15, 240, 12066, 43690, 52428], [15, 240, 12066, 44970, 52428], [15, 240, 13107, 36744, 56797]], [[15, 240, 3840, 13107, 26214], [15, 240, 3840, 13107, 28518], [15, 240, 3840, 26214, 62259], [15, 240, 4369, 26214, 61986], [15, 240, 4369, 28518, 61986], [15, 240, 8738, 20292, 62259], [15, 240, 12066, 13107, 20292]], [[15, 255, 4369, 8946, 36744], [15, 4095, 4369, 8946, 36744]], [[15, 3840, 4369, 8946, 43144], [15, 4080, 4383, 17652, 34952]], [[15, 240, 4369, 39321, 62194]], [[15, 240, 3840, 4369, 35980]], [[15, 240, 1285, 4369, 34952]], [[15, 240, 3855, 26214, 43690], [15, 240, 8738, 36751, 61166], [15, 255, 3840, 26214, 43690], [15, 255, 26214, 34952, 61986]], [[15, 240, 4095, 21845, 52428]], [[15, 240, 1911, 17476, 26214], [15, 240, 4369, 26214, 64170], [15, 240, 7953, 20292, 52428], [15, 240, 13107, 26214, 36744], [15, 4080, 4369, 20292, 52428], [15, 4095, 4593, 17476, 56797]], [[15, 240, 3840, 13107, 26223], [15, 240, 4080, 26214, 52428], [15, 240, 4369, 26223, 61986]], [[15, 240, 4369, 30576, 61986], [15, 4369, 8946, 36744, 65416]], [], [], [[15, 240, 4369, 36744, 56589]], [[5, 3840, 21845, 52428, 61440], [5, 17476, 24405, 34952, 61440], [15, 255, 8738, 36744, 61166], [15, 255, 34952, 61166, 61986]], [[15, 240, 3855, 13107, 26214], [15, 255, 3840, 13107, 26214], [15, 255, 4369, 26214, 61986], [15, 255, 12066, 13107, 17476], [15, 3840, 4095, 13107, 26214]], [[15, 240, 12066, 48059, 52428], [15, 240, 13107, 36744, 61166], [15, 240, 21845, 36744, 52428]], [[15, 240, 3855, 4883, 34952], [15, 240, 4369, 29218, 30583], [15, 240, 4369, 30583, 61986], [15, 240, 4369, 32631, 61986], [15, 240, 12066, 13107, 21845], [15, 4095, 4383, 17652, 34952]], [[15, 240, 4080, 21845, 26214], [15, 3840, 4593, 26214, 62532]], [[15, 240, 3855, 4369, 35980], [15, 240, 4593, 39321, 61986], [15, 4080, 4593, 8738, 39321]], [], [], [], [[15, 240, 3855, 21845, 52428], [15, 255, 3840, 21845, 52428]], [[15, 240, 4095, 26214, 52428], [15, 240, 36744, 52428, 56797]], [[15, 240, 1911, 8738, 39321], [15, 240, 4369, 17476, 36317], [15, 240, 4369, 30583, 64170], [15, 240, 4369, 30591, 61986], [15, 240, 12066, 20292, 52428], [15, 240, 12066, 26214, 43690], [15, 240, 20292, 56797, 61713], [15, 4080, 4369, 20292, 56797]], [[15, 240, 3840, 8738, 37265], [15, 240, 4080, 39321, 43690], [15, 4383, 17652, 34952, 63624]], [], [], [], [], [[15, 255, 17476, 56797, 63624]], [[15, 255, 4369, 30583, 61986]], [[15, 240, 4095, 21845, 26214], [15, 240, 8738, 44970, 61166]], [[1, 240, 4383, 34952, 61986], [15, 240, 1365, 8738, 17476], [15, 240, 3840, 21845, 26214], [15, 240, 3840, 26214, 62805], [15, 240, 4369, 8738, 36232], [15, 240, 4369, 8738, 36744], [15, 240, 4369, 8866, 36744], [15, 240, 4369, 8994, 36744], [15, 240, 4369, 12066, 35976], [15, 240, 4369, 12834, 36744], [15, 240, 4369, 25122, 36744], [15, 240, 4369, 25122, 63624], [15, 240, 4369, 29218, 34952], [15, 240, 4369, 34952, 61986], [15, 240, 4369, 34952, 62114], [15, 240, 4369, 35208, 61986], [15, 240, 4369, 35976, 61986], [15, 240, 4369, 39048, 61986], [15, 240, 4497, 8738, 36744], [15, 240, 4497, 34952, 61986], [15, 240, 4881, 8738, 36744], [15, 240, 6417, 34952, 61986], [15, 240, 7953, 8994, 34952], [15, 240, 8738, 12561, 36744], [15, 240, 12066, 13107, 26214], [15, 240, 12066, 13107, 28518], [15, 496, 7953, 8738, 34952]], [[15, 240, 4080, 13107, 39321], [15, 240, 4369, 8738, 36745], [15, 240, 4369, 8739, 36744], [15, 240, 4369, 34952, 61987], [15, 240, 4369, 34953, 61986], [15, 4593, 7953, 34952, 61986]], [[15, 240, 4369, 8738, 36746], [15, 240, 4369, 34954, 61986], [15, 240, 4371, 8738, 36744], [15, 240, 4371, 34952, 61986]], [[4, 240, 4383, 8738, 36744]], [[15, 240, 4369, 8738, 36748], [15, 240, 4369, 34956, 61986]], [[13, 4369, 20292, 56797, 61440]], [[5, 3840, 21845, 26214, 61440], [15, 240, 3855, 26214, 52428], [15, 255, 3840, 26214, 52428], [15, 255, 12066, 17476, 52428], [15, 255, 17476, 26214, 63624], [15, 4095, 4369, 20292, 56797]], [[15, 240, 4095, 39321, 43690], [15, 240, 4369, 8738, 36751], [15, 240, 4369, 34959, 61986], [15, 240, 36744, 52428, 61166]], [[15, 240, 4369, 8746, 36744], [15, 240, 4369, 34952, 61994], [15, 240, 4377, 8738, 36744], [15, 240, 4377, 34952, 61986], [15, 240, 12066, 21845, 52428], [15, 240, 39321, 64170], [15, 4369, 4593, 34959, 61986]], [], [], [], [], [], [], [[15, 240, 3855, 21845, 26214], [15, 255, 3840, 21845, 26214], [15, 3840, 4095, 21845, 26214], [15, 4383, 4593, 34952, 61986]], [[15, 240, 3549, 26214, 34952], [15, 240, 4095, 13107, 39321], [15, 240, 4369, 8738, 36760], [15, 240, 4369, 8754, 36744], [15, 240, 4369, 34968, 61986], [15, 240, 34952, 39321, 64170], [15, 240, 36744, 39321, 43690]], [[15, 240, 3840, 13107, 39321], [15, 240, 3840, 13107, 40857], [15, 240, 3840, 39321, 62259], [15, 240, 4369, 10103, 17476], [15, 240, 4369, 13107, 36744], [15, 240, 4369, 39321, 61986], [15, 240, 7953, 13107, 36744], [15, 240, 7953, 30583, 62532], [15, 240, 12066, 13107, 30583], [15, 3840, 4369, 8751, 17652, 63624], [15, 4080, 7953, 17476, 30583], [15, 4369, 8751, 17652, 63624]], [[15, 240, 4080, 13107, 43690]], [[15, 4080, 4593, 8738, 48059], [15, 4080, 4593, 17476, 39321]], [[1, 240, 7953, 34952, 62532]], [], [[15, 255, 4369, 34959, 61986]], [[15, 240, 3840, 13107, 39327], [15, 240, 3855, 39321, 43690], [15, 240, 4369, 39327, 61986], [15, 255, 3840, 39321, 43690], [15, 255, 8738, 39321, 63624]], [[15, 240, 3549, 34952, 61166], [15, 240, 4369, 13107, 36751], [15, 240, 36744, 56797, 61166]], [[7, 7953, 17476, 30583, 61440], [15, 240, 1911, 8738, 48059], [15, 240, 1911, 17476, 39321], [15, 240, 3003, 7953, 34952], [15, 240, 3549, 4369, 26214], [15, 240, 3822, 8738, 20292], [15, 240, 4369, 39321, 64170], [15, 240, 12066, 26214, 52428], [15, 240, 12066, 28518, 52428], [15, 240, 12066, 30583, 48059], [15, 240, 13107, 36744, 39321], [15, 240, 13107, 36744, 40857], [15, 240, 13107, 39321, 63624], [15, 4080, 7953, 34952, 48059], [15, 4080, 8738, 20292, 61166]], [[15, 240, 4080, 39321, 52428], [15, 240, 12066, 35064, 48059]], [], [[15, 240, 8738, 20292, 61937]], [], [[15, 240, 3840, 13299, 26214], [15, 3840, 4593, 8946, 26214], [15, 4593, 8946, 12066, 17476], [15, 4593, 8946, 17476, 61986]], [[15, 240, 4383, 13107, 36744], [15, 4593, 13299, 17476, 61986]], [[15, 240, 3840, 22005, 26214], [15, 240, 3855, 13107, 39321], [15, 240, 4369, 34984, 61986], [15, 240, 4401, 8738, 36744], [15, 240, 4401, 34952, 61986], [15, 255, 3840, 13107, 39321], [15, 255, 4369, 13107, 36744], [15, 255, 4369, 39321, 61986], [15, 3840, 4095, 13107, 39321], [15, 3840, 4593, 17652, 26214], [15, 4095, 7953, 17476, 30583]], [[15, 240, 4095, 13107, 43690]], [[15, 240, 1911, 8738, 17476], [15, 240, 2039, 8738, 17476], [15, 240, 3840, 13107, 43690], [15, 240, 3840, 13107, 44970], [15, 240, 4369, 17476, 36232], [15, 240, 4369, 20292, 35976], [15, 240, 4369, 25668, 63624], [15, 240, 4369, 35976, 62532], [15, 240, 5393, 34952, 62532], [15, 240, 7953, 34952, 62532], [15, 240, 8738, 13107, 36744], [15, 240, 12066, 13107, 34952], [15, 240, 12066, 13107, 36744], [15, 240, 12066, 21845, 26214], [15, 240, 13107, 44970], [15, 752, 4369, 17476, 36744], [15, 4080, 7953, 34952, 62532], [15, 4095, 4593, 8738, 48059]], [[15, 240, 4080, 21845, 39321], [15, 4080, 12066, 17476, 35064], [15, 4593, 7953, 34952, 62532], [15, 4593, 34952, 61713, 62532]], [[15, 3840, 4369, 8946, 17476, 63624], [15, 7953, 8946, 17476, 63624]], [[15, 4593, 17476, 39417, 61986]], [], [[15, 240, 3840, 13107, 43695], [15, 240, 4369, 8738, 44975], [15, 4080, 4593, 8738, 17487], [15, 4080, 17652, 26214, 34952]], [[5, 7953, 17476, 34952, 61440]], [[15, 240, 4095, 39321, 52428], [15, 240, 8738, 13107, 36751], [15, 240, 12066, 13107, 34959]], [[7, 7953, 17476, 34952, 61440], [15, 240, 3549, 4369, 30583], [15, 240, 4369, 36744, 52428], [15, 240, 4369, 36744, 64716], [15, 240, 7953, 34952, 64716], [15, 240, 7953, 36744, 52428], [15, 240, 8738, 39321, 64170], [15, 240, 12066, 30583, 52428], [15, 240, 12066, 34952, 48059], [15, 240, 12066, 39321, 43690], [15, 240, 13107, 34952, 44970], [15, 240, 13107, 36744, 43690], [15, 240, 13107, 36744, 44970], [15, 240, 13107, 43690, 63624]], [[15, 240, 4080, 43690, 52428]], [], [], [[15, 240, 4369, 26214, 62194]], [[15, 240, 1911, 8751, 17476], [15, 240, 8751, 13107, 36744], [15, 240, 12079, 13107, 34952], [15, 4080, 17652, 34952, 61166]], [[13, 7953, 17476, 34952, 61440], [15, 240, 1285, 8738, 17476], [15, 3840, 4369, 34984, 61986], [15, 4080, 4369, 17652, 26214]], [[15, 240, 3855, 13107, 43690], [15, 240, 4369, 36751, 52428], [15, 255, 3840, 13107, 43690], [15, 255, 7953, 34952, 62532], [15, 255, 8738, 13107, 36744], [15, 255, 12066, 13107, 34952], [15, 255, 12066, 17476, 30583], [15, 3840, 4095, 13107, 43690], [15, 4095, 7953, 34952, 62532]], [[4, 7953, 17487, 34952, 61440], [15, 240, 4095, 21845, 39321], [15, 240, 34952, 44970, 48059], [15, 240, 36744, 39321, 52428], [15, 240, 36744, 40857, 52428], [15, 240, 39321, 43690, 44970], [15, 240, 39321, 43690, 64170], [15, 255, 12066, 17476, 35064], [15, 4095, 12066, 17476, 35064]], [[4, 240, 8738, 17487, 63624], [15, 240, 1365, 4369, 34952], [15, 240, 3840, 8738, 19532], [15, 240, 3840, 21845, 39321], [15, 240, 3840, 39321, 62805], [15, 240, 4369, 13107, 44970], [15, 240, 4369, 21845, 36232], [15, 240, 4369, 21845, 55432], [15, 240, 8738, 20292, 35976], [15, 240, 12066, 13107, 39321], [15, 240, 12066, 19524, 34952], [15, 1264, 8738, 20292, 34952]], [], [[15, 3840, 8946, 26214, 63624]], [[15, 4095, 4593, 8738, 17487]], [[15, 240, 8751, 48059, 63624], [15, 240, 12079, 34952, 48059], [15, 17652, 26214, 63624]], [[15, 240, 3840, 4369, 25186], [15, 240, 4383, 36744, 52428]], [[5, 3840, 21845, 39321, 61440], [15, 240, 3855, 39321, 52428], [15, 255, 3840, 39321, 52428], [15, 255, 4369, 36744, 52428], [15, 255, 8738, 48059, 63624], [15, 255, 12066, 34952, 48059], [15, 255, 17476, 39321, 63624]], [[15, 240, 4095, 43690, 52428]], [[15, 240, 3549, 4369, 34952], [15, 240, 3855, 8995, 17476], [15, 240, 4369, 36232, 56797], [15, 240, 4369, 36744, 56797], [15, 240, 4369, 36744, 64989], [15, 240, 8738, 36744, 52428], [15, 240, 12066, 34952, 52428], [15, 240, 12066, 36744, 52428], [15, 240, 21845, 36744, 39321], [15, 4593, 17476, 34959, 61986]], [[15, 240, 4369, 10018, 17476], [15, 240, 4369, 12066, 19524], [15, 240, 4369, 20292, 25122], [15, 240, 4369, 25122, 62532], [15, 240, 8738, 17732, 61713], [15, 240, 8738, 20292, 61713], [15, 2288, 4369, 12066, 17476], [15, 3840, 4369, 8946, 17508], [15, 4080, 8738, 20292, 61713]], [[15, 240, 4080, 13107, 21845]], [[15, 240, 4593, 26214, 61986], [15, 3840, 8946, 26214, 61713], [15, 4095, 17652, 34952, 61166]], [[15, 240, 4369, 30583, 62194]], [[15, 240, 4369, 8802, 36744], [15, 240, 4369, 34952, 62050]], [[15, 4080, 4369, 17652, 30583]], [[5, 4369, 8738, 20292, 61440], [15, 240, 3549, 4369, 34959], [15, 240, 3855, 8738, 19532], [15, 240, 3855, 21845, 39321], [15, 240, 4369, 36751, 56797], [15, 240, 8738, 36751, 52428], [15, 240, 12066, 34959, 52428], [15, 255, 3840, 21845, 39321], [15, 3840, 4095, 21845, 39321]], [[15, 240, 3549, 34952, 39321], [15, 240, 36744, 43690, 52428], [15, 240, 36744, 44970, 52428]], [[7, 4369, 8738, 20292, 61440], [15, 240, 1911, 8738, 26214], [15, 240, 8738, 13107, 44970], [15, 240, 8738, 20292, 34952, 61713], [15, 240, 8738, 20292, 36744, 61713], [15, 240, 12066, 13107, 43690], [15, 240, 12066, 13107, 44970], [15, 4369, 20292, 35064, 61986]], [[15, 240, 4080, 26214, 43690]]]
  | 6 => [[[15, 240, 4095, 4369, 8738, 17487]], [[15, 240, 3840, 4369, 8738, 17487], [15, 240, 3840, 4369, 8738, 20303], [15, 240, 3840, 8738, 17487, 61713]], [], [[13, 3840, 4369, 34952, 56797, 61440]], [[13, 3840, 4369, 8738, 17476, 61440], [15, 240, 3855, 4369, 34952, 56797], [15, 240, 3855, 8738, 34952, 52428], [15, 240, 3855, 17476, 34952, 43690], [15, 255, 3840, 8738, 34952, 52428]], [[15, 240, 3855, 4369, 8738, 20292], [15, 240, 3855, 8738, 17476, 61713], [15, 240, 4369, 12066, 17476, 34959]], [[1, 3840, 4383, 8738, 17476, 61440], [15, 240, 3840, 4369, 8738, 17492], [15, 240, 3840, 4369, 8754, 17476], [15, 240, 3840, 4369, 39321, 56797], [15, 240, 3840, 4369, 43690, 52428], [15, 240, 3840, 8738, 30583, 61166], [15, 240, 3840, 8738, 39321, 52428], [15, 240, 3840, 8738, 43690, 48059], [15, 240, 4095, 4369, 13107, 17476], [15, 240, 4369, 8738, 36744, 52428], [15, 240, 4369, 8738, 36744, 53196], [15, 240, 8738, 12066, 34952, 48059]], [[1, 15, 4369, 8738, 20292, 61440], [15, 240, 3840, 4369, 8738, 21845], [15, 240, 3840, 4369, 8738, 24405], [15, 240, 3840, 4369, 13107, 17476], [15, 240, 3840, 4369, 13107, 20292], [15, 240, 3840, 7953, 13107, 17476], [15, 240, 3840, 13107, 21845], [15, 240, 3840, 13107, 21845, 61440], [15, 240, 4080, 8738, 34952, 61166], [15, 240, 4369, 7953, 8738, 20292]], [[15, 240, 4080, 4369, 8738, 26214], [15, 240, 4080, 8738, 13107, 17476]], [[15, 240, 3855, 8751, 17476, 34952], [15, 240, 3855, 12079, 17476, 34952], [15, 240, 4095, 4369, 8946, 34952], [15, 240, 4369, 8738, 17487, 36744], [15, 240, 4369, 8738, 17487, 63624]], [[4, 15, 4369, 8738, 20292, 61440], [15, 240, 3840, 4369, 8946, 34952], [15, 240, 3840, 4369, 8946, 36744], [15, 240, 3840, 4369, 34952, 62194], [15, 240, 4369, 8946, 36744], [15, 240, 4369, 34952, 62194]], [[15, 240, 3840, 4369, 8751, 17476, 63624], [15, 240, 3840, 4369, 13299, 34952], [15, 240, 4095, 4369, 17652, 34952], [15, 240, 4369, 8751, 17476, 36744], [15, 240, 4369, 8751, 17476, 63624]], [[15, 240, 3840, 4383, 8738, 17476, 63624]], [[5, 3840, 4369, 8738, 21845, 61440], [15, 240, 3840, 4369, 22005, 34952]], [[15, 240, 4095, 8738, 26214, 34952]], [[4, 3840, 4369, 8946, 34952, 61440], [15, 240, 3840, 8738, 13107, 48059], [15, 240, 3840, 8738, 21845, 39321], [15, 240, 3840, 8738, 26214, 63624], [15, 240, 4369, 12066, 17476, 39321], [15, 240, 4369, 13107, 17476, 36744], [15, 240, 4369, 13107, 17476, 63624]], [[15, 240, 3855, 4369, 8738, 17487], [15, 240, 3855, 4369, 8738, 20303], [15, 240, 4080, 4369, 17476, 52428]], [[15, 240, 3840, 4369, 8738, 21855], [15, 240, 3840, 4369, 8946, 34959], [15, 240, 3840, 4593, 17476, 56797]], [[15, 240, 3840, 4369, 13107, 17487], [15, 240, 4369, 8946, 34952, 36744], [15, 240, 4369, 8946, 34952, 63624]], [[15, 240, 3840, 4369, 34952, 48123]], [[15, 240, 4369, 17652, 34952, 36744]], [[15, 240, 3840, 4383, 13107, 17476]], [[15, 240, 3840, 4369, 8738, 17508], [15, 240, 3840, 4401, 8738, 17476], [15, 240, 3855, 4369, 8738, 21845], [15, 240, 3855, 4369, 13107, 17476], [15, 240, 4095, 8738, 34952, 61166], [15, 255, 3840, 4369, 13107, 17476]], [[15, 240, 3549, 4369, 8738, 34952], [15, 240, 3549, 4369, 34952, 61986], [15, 240, 3840, 4369, 43690, 56797], [15, 240, 3840, 4369, 48059, 52428], [15, 240, 3840, 8738, 43690, 52428], [15, 240, 4369, 8738, 36744, 56797], [15, 240, 8738, 12066, 34952, 52428], [15, 240, 8738, 36744, 61166]], [[15, 240, 3840, 4369, 8738, 26214], [15, 240, 3840, 4369, 8738, 28518], [15, 240, 3840, 4369, 13107, 21845], [15, 240, 3840, 4369, 26214, 61986], [15, 240, 3840, 8738, 13107, 17476], [15, 240, 3840, 8738, 13107, 20292], [15, 240, 3840, 8738, 17476, 62259], [15, 240, 3840, 8738, 26214, 61713], [15, 240, 3840, 13107, 26214], [15, 240, 3840, 13107, 26214, 61440], [15, 240, 4080, 17476, 34952, 56797], [15, 240, 4369, 8738, 12066, 20292], [15, 240, 4369, 12066, 17476, 61986], [15, 240, 4369, 26214, 61986]], [[15, 240, 3855, 4369, 8946, 34952], [15, 240, 4080, 4369, 8738, 30583]], [[15, 240, 3840, 4593, 17476, 26214]], [[15, 240, 3840, 4369, 8946, 39321], [15, 240, 3855, 4369, 17652, 34952]], [[15, 240, 3840, 4369, 17476, 35016]], [[15, 240, 3840, 4369, 17652, 39321]], [[15, 240, 3855, 8738, 26214, 34952]], [[15, 240, 4095, 4369, 17476, 52428], [15, 240, 8738, 34952, 36744, 61166]], [[4, 15, 4369, 17652, 34952, 61440], [15, 240, 3840, 4369, 17476, 52428], [15, 240, 3840, 4369, 20292, 52428], [15, 240, 3840, 4369, 26214, 43690], [15, 240, 3840, 7953, 17476, 52428], [15, 240, 4369, 26214, 34952, 61986], [15, 240, 4369, 34952, 61986, 63078]], [[15, 240, 3840, 4369, 8738, 26223], [15, 240, 4080, 4369, 17476, 56797], [15, 240, 4080, 17476, 26214, 34952]], [], [[15, 240, 3840, 8738, 13107, 17487], [15, 240, 4369, 8738, 12066, 17487], [15, 240, 4369, 8738, 17487, 61986]], [], [[15, 240, 4369, 8751, 12066, 17476], [15, 240, 4369, 8751, 17476, 61986]], [[5, 3840, 17476, 21845, 34952, 61440], [15, 240, 3855, 8738, 34952, 61166], [15, 255, 3840, 8738, 34952, 61166]], [[15, 240, 3855, 4369, 8738, 26214], [15, 240, 3855, 8738, 13107, 17476]], [[15, 240, 3840, 4369, 48059, 56797], [15, 240, 3840, 8738, 39321, 61166], [15, 240, 3840, 8738, 48059, 52428], [15, 240, 4095, 4369, 8738, 30583], [15, 240, 4369, 8738, 36744, 61166], [15, 240, 4369, 17476, 36744, 52428], [15, 240, 4369, 34952, 61166, 61986]], [[15, 240, 3840, 4369, 8738, 30583], [15, 240, 3840, 4369, 8738, 32631], [15, 240, 3840, 4369, 13107, 26214], [15, 240, 3840, 4369, 30583, 61986], [15, 240, 3840, 8738, 13107, 21845], [15, 240, 4080, 17476, 34952, 61166], [15, 240, 4369, 12066, 13107, 17476], [15, 240, 4369, 30583, 61986]], [[15, 240, 4080, 4369, 8738, 36744], [15, 240, 4080, 4369, 17476, 26214], [15, 240, 4080, 4369, 34952, 61986]], [[15, 240, 3840, 4369, 17487, 52428], [15, 240, 3840, 4593, 8738, 39321], [15, 240, 4369, 4593, 8738, 36744], [15, 240, 4369, 4593, 34952, 61986]], [[15, 240, 4369, 8946, 12066, 34952], [15, 240, 4369, 8946, 34952, 61986], [15, 240, 4369, 34952, 61986, 62194]], [], [[15, 240, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4383, 17476, 52428], [15, 240, 4369, 8738, 17652, 36744], [15, 240, 4369, 8738, 17652, 63624], [15, 240, 4369, 12066, 17652, 34952], [15, 240, 4369, 17652, 34952, 61986]], [[15, 240, 3855, 4369, 17476, 52428], [15, 255, 3840, 4369, 17476, 52428]], [[15, 240, 4095, 4369, 17476, 56797]], [[7, 3840, 4369, 8738, 30583, 61440], [15, 240, 1911, 4369, 8738, 34952], [15, 240, 3840, 4369, 8738, 30591], [15, 240, 3840, 4369, 17476, 56797], [15, 240, 3840, 4369, 20292, 56797], [15, 240, 3840, 4369, 21845, 52428], [15, 240, 3840, 4369, 26214, 48059], [15, 240, 3840, 4369, 30583, 43690], [15, 240, 3840, 8738, 20292, 52428], [15, 240, 3840, 8738, 21845, 48059], [15, 240, 3840, 8738, 26214, 43690], [15, 240, 3840, 8738, 30583, 39321], [15, 240, 4080, 4369, 8738, 34959], [15, 240, 4369, 30583, 34952, 61986], [15, 240, 8738, 12066, 26214, 34952]], [[15, 240, 4080, 8738, 34952, 39321], [15, 240, 4369, 8738, 36744, 36856], [15, 240, 4369, 34952, 35064, 61986]], [], [], [], [[13, 3840, 17476, 34952, 56797, 61440], [15, 240, 3840, 4369, 8802, 17476], [15, 240, 3840, 4433, 8738, 17476]], [[15, 240, 3855, 17476, 34952, 56797]], [[15, 240, 3855, 4369, 8738, 30583], [15, 240, 4095, 17476, 34952, 61166]], [[15, 240, 255, 4369, 8738, 36744], [15, 240, 255, 4369, 34952, 61986], [15, 240, 3840, 8738, 43690, 61166], [15, 240, 4095, 4369, 8738, 36744], [15, 240, 4095, 4369, 17476, 26214], [15, 240, 4095, 4369, 34952, 61986], [15, 240, 4369, 17476, 36744, 56797], [15, 240, 8738, 12066, 34952, 61166]], [[1, 240, 4383, 8738, 34952, 61440], [15, 240, 3840, 4369, 8738, 34952], [15, 240, 3840, 4369, 8738, 35208], [15, 240, 3840, 4369, 8738, 35464], [15, 240, 3840, 4369, 8738, 35976], [15, 240, 3840, 4369, 8738, 36744], [15, 240, 3840, 4369, 8738, 39048], [15, 240, 3840, 4369, 8738, 43144], [15, 240, 3840, 4369, 8866, 34952], [15, 240, 3840, 4369, 8994, 34952], [15, 240, 3840, 4369, 10786, 34952], [15, 240, 3840, 4369, 12834, 34952], [15, 240, 3840, 4369, 13107, 30583], [15, 240, 3840, 4369, 17476, 26214], [15, 240, 3840, 4369, 25122, 34952], [15, 240, 3840, 4369, 26214, 62532], [15, 240, 3840, 4369, 34952, 61986], [15, 240, 3840, 4369, 36744, 61986], [15, 240, 3840, 8738, 13107, 26214], [15, 240, 3840, 8738, 17476, 21845], [15, 240, 3840, 8738, 17476, 62805], [15, 240, 3840, 21845, 26214], [15, 240, 4369, 8738, 12066, 28518], [15, 240, 4369, 8738, 36744], [15, 240, 4369, 34952, 61986]], [[1, 15, 240, 4369, 8738, 36744], [1, 15, 240, 4369, 34952, 61986], [15, 240, 3840, 4369, 8738, 34953], [15, 240, 3840, 4369, 8739, 34952], [15, 240, 4080, 4369, 8738, 39321], [15, 240, 4080, 4369, 13107, 34952], [15, 240, 4080, 4369, 17476, 30583]], [[15, 240, 3840, 4369, 8738, 34954], [15, 240, 3840, 4369, 17487, 56797], [15, 240, 3840, 8738, 17487, 52428]], [[4, 240, 3840, 4383, 8738, 34952]], [[4, 15, 240, 4369, 8738, 36744], [4, 15, 240, 4369, 34952, 61986], [15, 240, 3840, 4369, 8738, 34956]], [[13, 3840, 4369, 17476, 56797, 61440]], [[5, 3840, 4369, 8738, 34952, 61440], [5, 3840, 8738, 17476, 21845, 61440], [15, 240, 3855, 4369, 17476, 56797], [15, 240, 3855, 8738, 17476, 52428], [15, 240, 3855, 17476, 26214, 34952], [15, 240, 4095, 4369, 8738, 34959], [15, 255, 3840, 4369, 17476, 56797], [15, 3840, 4095, 4369, 17476, 56797]], [[15, 240, 3840, 4369, 8738, 34959], [15, 240, 3840, 4369, 8738, 36751], [15, 240, 3840, 4369, 34959, 61986], [15, 240, 4095, 8738, 34952, 39321], [15, 240, 4369, 8738, 36751], [15, 240, 4369, 34959, 61986]], [[7, 3840, 4369, 8738, 34952, 61440], [15, 240, 3840, 4369, 8746, 34952], [15, 240, 3840, 4369, 21845, 56797], [15, 240, 3840, 4369, 26214, 52428], [15, 240, 3840, 4369, 30583, 48059], [15, 240, 3840, 8738, 21845, 52428], [15, 240, 3840, 8738, 39321, 63624], [15, 240, 4369, 12066, 17476, 52428]], [[15, 240, 4080, 4369, 34952, 48059], [15, 240, 4080, 8738, 17476, 61166]], [], [], [[15, 240, 4080, 4593, 8738, 17476]], [], [[13, 3840, 4369, 8738, 34952, 61440], [15, 240, 3855, 17476, 34952, 61166]], [[15, 240, 3855, 4369, 8738, 36744], [15, 240, 3855, 4369, 17476, 26214], [15, 240, 3855, 4369, 34952, 61986], [15, 240, 3855, 8738, 17476, 21845], [15, 240, 4369, 8738, 36744, 36751], [15, 255, 3840, 4369, 17476, 26214]], [[15, 240, 3840, 4369, 8738, 34968], [15, 240, 3840, 4369, 8754, 34952], [15, 240, 3840, 8738, 48059, 61166], [15, 240, 4095, 4369, 17476, 30583], [15, 240, 8738, 34952, 36744, 39321]], [[15, 240, 3840, 4369, 8738, 39321], [15, 240, 3840, 4369, 8738, 40857], [15, 240, 3840, 4369, 13107, 34952], [15, 240, 3840, 4369, 13107, 36744], [15, 240, 3840, 4369, 17476, 30583], [15, 240, 3840, 4369, 21845, 26214], [15, 240, 3840, 4369, 30583, 62532], [15, 240, 3840, 4369, 34952, 62259], [15, 240, 3840, 4369, 39321, 61986], [15, 240, 3840, 7953, 17476, 30583], [15, 240, 3840, 8738, 13107, 30583], [15, 240, 3840, 8738, 39321, 61713], [15, 240, 3840, 13107, 39321], [15, 240, 4369, 7953, 8738, 36744], [15, 240, 4369, 7953, 34952, 61986], [15, 240, 4369, 13107, 36744], [15, 240, 4369, 39321, 61986]], [[4, 3840, 4369, 8751, 34952, 61440], [15, 240, 4080, 4369, 34952, 62532], [15, 240, 4080, 7953, 17476, 34952], [15, 240, 4080, 8738, 13107, 34952], [15, 240, 4080, 8738, 17476, 30583]], [[15, 240, 3840, 4593, 8738, 48059], [15, 240, 3840, 4593, 17476, 39321], [15, 240, 4080, 8738, 17476, 35064]], [[15, 240, 3840, 4369, 8946, 17476, 63624]], [], [[15, 240, 3855, 4369, 8738, 34959], [15, 240, 3855, 4369, 8738, 36751]], [[4, 240, 3840, 4369, 34952, 62532], [15, 240, 3840, 4369, 8738, 39327], [15, 240, 3855, 4369, 34952, 43690], [15, 240, 3855, 8738, 34952, 39321]], [[15, 240, 3840, 4369, 13107, 34959], [15, 240, 4095, 4369, 34952, 48059]], [[7, 3840, 4369, 17476, 30583, 61440], [15, 240, 1911, 4369, 17476, 34952], [15, 240, 3003, 3840, 4369, 34952], [15, 240, 3003, 4369, 34952, 61440], [15, 240, 3549, 4369, 8738, 17476], [15, 240, 3840, 4369, 26214, 56797], [15, 240, 3840, 4369, 30583, 52428], [15, 240, 3840, 4369, 34952, 48059], [15, 240, 3840, 4369, 34952, 64443], [15, 240, 3840, 4369, 39321, 43690], [15, 240, 3840, 8738, 20292, 61166], [15, 240, 3840, 8738, 26214, 52428], [15, 240, 3840, 8738, 30583, 48059], [15, 240, 4369, 12066, 17476, 56797], [15, 240, 4369, 17476, 30583, 36744]], [[15, 240, 4080, 4369, 34952, 52428], [15, 240, 4080, 8738, 34952, 48059]], [[15, 240, 4095, 4593, 8738, 17476]], [[15, 240, 3840, 4593, 8738, 17476], [15, 240, 3840, 4593, 8738, 20292], [15, 240, 3840, 8738, 17476, 61937]], [], [[1, 3840, 4593, 8738, 17476, 61440], [15, 240, 3840, 8738, 13299, 17476]], [[15, 240, 3840, 4383, 17476, 30583], [15, 240, 4369, 4383, 8738, 36744], [15, 240, 4369, 4383, 34952, 61986]], [[15, 240, 3840, 4369, 8738, 34984], [15, 240, 3840, 8738, 17476, 22005], [15, 240, 3855, 4369, 8738, 39321], [15, 240, 3855, 4369, 13107, 34952], [15, 240, 3855, 4369, 17476, 30583], [15, 240, 4080, 4383, 17476, 34952], [15, 255, 3840, 4369, 17476, 30583], [15, 3840, 4095, 4369, 17476, 30583]], [[15, 240, 4095, 4369, 34952, 62532], [15, 240, 4095, 7953, 17476, 34952], [15, 240, 4095, 8738, 13107, 34952], [15, 240, 4095, 8738, 17476, 30583]], [[1, 240, 3840, 4383, 17476, 34952], [4, 240, 4369, 17487, 34952, 61440], [15, 240, 1911, 3840, 8738, 17476], [15, 240, 1911, 8738, 17476], [15, 240, 3840, 4369, 8738, 43690], [15, 240, 3840, 4369, 8738, 44970], [15, 240, 3840, 4369, 13107, 39321], [15, 240, 3840, 4369, 17476, 35208], [15, 240, 3840, 4369, 17476, 35976], [15, 240, 3840, 4369, 17476, 39048], [15, 240, 3840, 4369, 17476, 51336], [15, 240, 3840, 4369, 21572, 34952], [15, 240, 3840, 4369, 21845, 30583], [15, 240, 3840, 8738, 17476, 30583], [15, 240, 3840, 8738, 17476, 30711], [15, 240, 3840, 8738, 17476, 63351], [15, 240, 3840, 8738, 21845, 26214], [15, 240, 3840, 13107, 43690], [15, 240, 4095, 8738, 17476, 35064], [15, 240, 4369, 8738, 12066, 36744], [15, 240, 4369, 12066, 17476, 26214], [15, 240, 4369, 12066, 34952, 61986], [15, 240, 7953, 34952, 62532], [15, 240, 8738, 13107, 36744], [15, 240, 12066, 13107, 34952]], [[15, 240, 3840, 4369, 17476, 34953], [15, 240, 4080, 4369, 8738, 48059], [15, 240, 4080, 4369, 17476, 39321], [15, 240, 4080, 8738, 17476, 63624], [15, 240, 4080, 12066, 17476, 34952]], [[15, 240, 3840, 8738, 17487, 61166], [15, 3840, 4369, 8946, 17476, 63624]], [[1, 3840, 8738, 17476, 35064, 61440]], [[15, 240, 3840, 4369, 17476, 34956]], [[15, 240, 3840, 4369, 8738, 43695], [15, 240, 3840, 4593, 8738, 17487]], [[5, 3840, 4369, 17476, 34952, 61440], [15, 240, 3855, 4369, 34952, 48059], [15, 240, 3855, 8738, 17476, 61166]], [[15, 240, 4095, 8738, 34952, 48059], [15, 240, 4369, 8738, 12066, 34959]], [[7, 3840, 4369, 17476, 34952, 61440], [7, 3840, 8738, 17476, 30583, 61440], [15, 240, 1911, 8738, 17476, 34952], [15, 240, 1911, 8738, 17476, 63624], [15, 240, 3840, 4369, 30583, 56797], [15, 240, 3840, 4369, 36744, 52428], [15, 240, 3840, 4369, 39321, 48059], [15, 240, 3840, 8738, 21845, 61166], [15, 240, 3840, 8738, 30583, 52428], [15, 240, 3840, 8738, 39321, 43690], [15, 240, 3840, 8738, 48059, 63624], [15, 240, 4369, 17476, 36744, 63624], [15, 240, 4369, 36744, 52428], [15, 240, 8738, 12066, 34952, 39321], [15, 240, 8738, 13107, 34952, 36744], [15, 240, 8738, 13107, 34952, 63624], [15, 240, 12066, 34952, 48059]], [[15, 240, 3855, 4593, 8738, 17476], [15, 240, 4080, 4369, 34952, 56797], [15, 240, 4080, 8738, 34952, 52428]], [[15, 240, 4080, 4369, 8738, 20292], [15, 240, 4080, 8738, 17476, 61713]], [[1, 15, 4593, 8738, 17476, 61440]], [[1, 240, 3840, 8738, 17476, 61713], [15, 240, 3840, 4369, 8946, 26214]], [[15, 240, 4095, 4383, 17476, 34952], [15, 240, 4369, 8738, 8751, 36744], [15, 240, 4369, 8751, 12066, 34952], [15, 240, 4369, 8751, 34952, 61986], [15, 240, 4369, 34952, 61986, 61999]], [[1, 240, 3840, 8738, 17487, 34952], [13, 3840, 4369, 17476, 34952, 61440], [15, 240, 3840, 4369, 17652, 26214], [15, 240, 4080, 8751, 17476, 34952]], [[15, 240, 3840, 4369, 34959, 52428], [15, 240, 3855, 4369, 8738, 43690], [15, 240, 3855, 4369, 34952, 62532], [15, 240, 3855, 7953, 17476, 34952], [15, 240, 3855, 8738, 13107, 34952], [15, 240, 3855, 8738, 17476, 30583], [15, 240, 4369, 17476, 34959, 36744], [15, 240, 4369, 17476, 34959, 63624], [15, 255, 3840, 8738, 13107, 34952]], [[4, 3840, 4369, 17487, 34952, 61440], [15, 240, 3840, 4369, 17476, 34968], [15, 240, 3855, 8738, 17476, 35064], [15, 240, 4095, 4369, 8738, 48059], [15, 240, 4095, 4369, 17476, 39321], [15, 240, 4095, 8738, 17476, 63624], [15, 240, 4095, 12066, 17476, 34952], [15, 240, 8738, 34952, 36744, 48059]], [[1, 15, 7953, 17476, 34952, 61440], [4, 240, 8738, 17487, 34952, 61440], [15, 240, 3840, 4369, 8738, 48059], [15, 240, 3840, 4369, 8738, 49083], [15, 240, 3840, 4369, 13107, 43690], [15, 240, 3840, 4369, 17476, 39321], [15, 240, 3840, 4369, 21845, 34952], [15, 240, 3840, 4369, 34952, 62805], [15, 240, 3840, 4369, 39321, 62532], [15, 240, 3840, 8738, 13107, 39321], [15, 240, 3840, 8738, 48059, 61713], [15, 240, 3840, 21845, 39321], [15, 240, 4369, 7953, 34952, 62532], [15, 240, 4369, 12066, 17476, 30583]], [[1, 15, 240, 8738, 17476, 63624], [1, 15, 240, 12066, 17476, 34952], [15, 240, 4369, 12066, 17476, 35064]], [], [[4, 15, 7953, 17476, 34952, 61440]], [[4, 15, 240, 8738, 17476, 63624], [4, 15, 240, 12066, 17476, 34952], [15, 240, 3840, 4369, 8738, 48063], [15, 240, 4080, 4369, 8738, 17487]], [], [[5, 3840, 4369, 21845, 34952, 61440], [5, 3840, 8738, 17476, 34952, 61440], [15, 240, 3855, 4369, 34952, 52428], [15, 240, 3855, 8738, 34952, 48059], [15, 240, 3855, 17476, 34952, 39321], [15, 255, 3840, 8738, 34952, 48059]], [[15, 240, 4095, 4369, 34952, 56797], [15, 240, 4095, 8738, 34952, 52428]], [[7, 3840, 8738, 17476, 34952, 61440], [15, 240, 3549, 4369, 34952], [15, 240, 3840, 4369, 36744, 56797], [15, 240, 3840, 4369, 39321, 52428], [15, 240, 3840, 8738, 26214, 61166], [15, 240, 4095, 4369, 8738, 20292], [15, 240, 4095, 8738, 17476, 61713], [15, 240, 4369, 17476, 36744, 39321], [15, 240, 4369, 36744, 56797], [15, 240, 8738, 36744, 52428], [15, 240, 12066, 34952, 52428]], [[1, 240, 4383, 8738, 17476, 61440], [4, 240, 3840, 4369, 8738, 17487], [15, 240, 3840, 4369, 8738, 17476], [15, 240, 3840, 4369, 8738, 17732], [15, 240, 3840, 4369, 8738, 17988], [15, 240, 3840, 4369, 8738, 19524], [15, 240, 3840, 4369, 8738, 20292], [15, 240, 3840, 4369, 8738, 21572], [15, 240, 3840, 4369, 8738, 25668], [15, 240, 3840, 4369, 8994, 17476], [15, 240, 3840, 4369, 9762, 17476], [15, 240, 3840, 4369, 12834, 17476], [15, 240, 3840, 4369, 17476, 25122], [15, 240, 3840, 4497, 8738, 17476], [15, 240, 3840, 4881, 8738, 17476], [15, 240, 3840, 5393, 8738, 17476], [15, 240, 3840, 8738, 12561, 17476], [15, 240, 3840, 8738, 17476, 20753], [15, 240, 3840, 8738, 17476, 37137], [15, 240, 3840, 8738, 17476, 61713], [15, 240, 3840, 8738, 20292, 61713], [15, 240, 8738, 20292, 61713]], [[15, 240, 3840, 4369, 8738, 17477], [15, 240, 3840, 4369, 8739, 17476], [15, 240, 4080, 4369, 13107, 17476]], [[15, 240, 3840, 4369, 8738, 17478], [15, 240, 3840, 4371, 8738, 17476], [15, 240, 3840, 4593, 8738, 26214]], [[15, 240, 3840, 4369, 8946, 30583], [15, 240, 3855, 4383, 17476, 34952], [15, 240, 3855, 7967, 17476, 34952], [15, 240, 4095, 8751, 17476, 34952]], [[15, 240, 3840, 4369, 8742, 17476], [15, 240, 3840, 4369, 8802, 34952], [15, 240, 3840, 4373, 8738, 17476], [15, 240, 4080, 4369, 8946, 34952]], [[13, 3840, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 17652, 30583]], [[5, 3840, 4369, 8738, 17476, 61440], [15, 240, 3840, 4369, 34959, 56797], [15, 240, 3855, 4369, 8738, 48059], [15, 240, 3855, 4369, 17476, 39321], [15, 240, 3855, 4369, 21845, 34952], [15, 240, 3855, 8738, 17476, 63624], [15, 240, 3855, 12066, 17476, 34952], [15, 240, 4080, 4369, 17652, 34952], [15, 240, 4369, 8946, 12274, 34952], [15, 240, 4369, 8946, 34952, 62194], [15, 255, 3840, 4369, 17476, 39321]], [[15, 240, 8738, 34952, 36744, 52428]], [[7, 3840, 4369, 8738, 17476, 61440], [15, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17484], [15, 240, 3840, 4369, 13107, 48059], [15, 240, 3840, 4369, 21845, 39321], [15, 240, 3840, 8738, 13107, 43690], [15, 240, 3840, 8738, 17476, 61713, 63624], [15, 240, 3840, 8738, 26214, 30583], [15, 240, 4369, 8738, 12066, 44970], [15, 240, 4369, 8738, 20292, 36744], [15, 240, 4369, 8738, 36744, 62532], [15, 240, 4369, 20292, 34952, 61986], [15, 240, 7953, 8738, 34952, 62532], [15, 240, 8738, 12066, 13107, 34952], [15, 240, 8738, 20292, 34952, 61713], [15, 3840, 4369, 17476, 35064, 61986]], [[15, 240, 4080, 8738, 26214, 34952]]]
  | 7 => [[], [[15, 240, 3840, 4369, 8738, 17487], [15, 240, 3840, 4369, 8738, 17487, 61440]], [], [], [], [[15, 240, 3840, 3855, 4369, 8738, 17476], [15, 240, 3840, 4369, 8738, 17476, 34959]], [[15, 240, 3840, 4369, 8738, 34952, 52428]], [[1, 15, 3840, 4369, 8738, 17476, 61440], [15, 240, 3840, 4369, 7953, 8738, 17476], [15, 240, 3840, 4369, 8738, 21845], [15, 240, 3840, 4369, 8738, 21845, 61440], [15, 240, 3840, 4369, 13107, 17476], [15, 240, 3840, 4369, 13107, 17476, 61440]], [], [[15, 240, 3840, 4369, 8738, 17487, 34952]], [[15, 240, 3840, 4369, 8946, 34952]], [], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 39321], [15, 240, 3840, 4369, 8738, 21845, 34952]], [], [], [], [], [], [[15, 240, 3840, 4369, 4383, 8738, 17476]], [], [[15, 240, 3840, 4369, 8738, 34952, 56797]], [[15, 240, 3840, 4369, 8738, 26214], [15, 240, 3840, 4369, 8738, 26214, 61440], [15, 240, 3840, 8738, 13107, 17476]], [], [], [], [], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 43690], [15, 240, 3840, 4369, 8738, 26214, 34952], [15, 240, 3840, 4369, 17476, 52428]], [], [], [], [], [[15, 240, 3840, 4369, 8738, 8751, 17476]], [], [], [[15, 240, 3840, 4369, 8738, 34952, 61166]], [[15, 240, 3840, 4369, 8738, 30583], [15, 240, 3840, 4369, 8738, 30583, 61440]], [], [[15, 240, 3840, 4369, 4593, 8738, 34952]], [], [], [[15, 240, 3840, 4369, 8738, 17652, 34952]], [[4, 240, 3840, 4369, 8738, 34952, 61440]], [], [[15, 240, 3840, 4369, 8738, 17476, 48059], [15, 240, 3840, 4369, 8738, 30583, 34952], [15, 240, 3840, 4369, 17476, 56797]], [], [], [], [], [], [], [], [[15, 240, 255, 3840, 4369, 8738, 34952], [15, 240, 3840, 4095, 4369, 8738, 34952]], [[15, 240, 3840, 4369, 8738, 34952], [15, 240, 3840, 4369, 8738, 36744], [15, 240, 3840, 4369, 17476, 26214], [15, 240, 3840, 4369, 34952, 61986], [15, 240, 3840, 8738, 17476, 21845], [15, 240, 4369, 8738, 36744], [15, 240, 4369, 34952, 61986]], [[1, 15, 240, 3840, 4369, 8738, 34952], [1, 15, 240, 4369, 8738, 34952, 61440]], [], [], [[4, 15, 240, 3840, 4369, 8738, 34952], [4, 15, 240, 4369, 8738, 34952, 61440]], [], [], [[15, 240, 3840, 4369, 8738, 34959]], [[15, 240, 3840, 4369, 8738, 17476, 52428]], [], [], [[15, 240, 3840, 4369, 8738, 17476, 17487]], [], [], [], [[15, 240, 3840, 3855, 4369, 8738, 34952]], [], [[15, 240, 3840, 4369, 8738, 39321], [15, 240, 3840, 4369, 13107, 34952], [15, 240, 3840, 4369, 17476, 30583], [15, 240, 3840, 4369, 17476, 30583, 61440]], [], [[15, 240, 3840, 4369, 4593, 17476, 34952]], [[4, 15, 3840, 4369, 8738, 34952, 61440]], [], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 56797], [15, 240, 3840, 4369, 34952, 48059]], [], [], [[15, 240, 3840, 4593, 8738, 17476]], [], [], [[15, 240, 3840, 4369, 4383, 8738, 34952]], [], [[15, 240, 255, 3840, 4369, 17476, 34952]], [[15, 240, 3840, 4369, 8738, 43690], [15, 240, 3840, 8738, 17476, 30583]], [[1, 15, 240, 3840, 4369, 17476, 34952]], [], [[1, 240, 3840, 8738, 17476, 34952, 61440]], [[4, 15, 240, 3840, 4369, 17476, 34952], [4, 15, 240, 4369, 17476, 34952, 61440]], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 61166]], [], [], [[15, 240, 3840, 4369, 4593, 8738, 17476]], [[15, 240, 3840, 4369, 8738, 8946, 17476]], [[15, 240, 3840, 4369, 8738, 8751, 34952]], [], [], [[15, 240, 255, 3840, 8738, 17476, 34952]], [[15, 240, 3840, 4369, 7953, 17476, 34952], [15, 240, 3840, 4369, 8738, 48059], [15, 240, 3840, 4369, 17476, 39321], [15, 240, 3840, 4369, 21845, 34952]], [[1, 15, 240, 3840, 8738, 17476, 34952], [1, 15, 240, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 35064]], [], [[4, 15, 3840, 4369, 17476, 34952, 61440]], [[4, 15, 240, 3840, 8738, 17476, 34952], [4, 15, 240, 8738, 17476, 34952, 61440]], [], [], [], [[15, 240, 255, 3840, 4369, 8738, 17476], [15, 240, 3840, 4095, 4369, 8738, 17476]], [[15, 240, 3840, 4369, 8738, 17476], [15, 240, 3840, 4369, 8738, 20292], [15, 240, 3840, 4369, 8738, 20292, 61440], [15, 240, 3840, 8738, 17476, 61713]], [[1, 15, 240, 3840, 4369, 8738, 17476], [1, 15, 240, 4369, 8738, 17476, 61440]], [], [], [[4, 15, 240, 3840, 4369, 8738, 17476]], [[15, 240, 3840, 4369, 4383, 17476, 34952]], [], [], [[1, 15, 3840, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952], [15, 240, 3840, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 36744], [15, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 20292, 34952], [15, 240, 3840, 4369, 8738, 34952, 62532]], []]
  | 8 => [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 3840, 4369, 8738, 34952]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 3840, 4369, 8738, 17476]], [], [], [], [], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 34952], [15, 240, 3840, 4369, 8738, 17476, 34952, 61440]], []]
  | _ => []

def ap : List Nat → Nat → Nat
  | [], _ => 0
  | j :: p, w => (w.testBit j).toNat + 2 * ap p w

theorem ap_bit : ∀ (p : List Nat) (w i : Nat),
    (ap p w).testBit i = (match p[i]? with | some j => w.testBit j | none => false)
  | [], w, i => by simp [ap]
  | j :: p, w, 0 => by
      simp only [ap, Nat.testBit_zero, List.getElem?_cons_zero]
      cases w.testBit j <;> simp <;> omega
  | j :: p, w, i + 1 => by
      have h : ((w.testBit j).toNat + 2 * ap p w) / 2 = ap p w := by
        cases w.testBit j <;> simp <;> omega
      rw [ap, Nat.testBit_succ, h, ap_bit p w i]; simp

theorem ap_lt : ∀ (p : List Nat) (w : Nat), ap p w < 2 ^ p.length
  | [], w => by simp [ap]
  | j :: p, w => by
      have h := ap_lt p w
      rw [ap, List.length_cons, Nat.pow_succ]
      cases w.testBit j <;> simp <;> omega

def okPerm (pq : List Nat × List Nat) : Bool :=
  pq.1.length == 16 && pq.1.all (fun j => decide (j < 16)) &&
    (List.range 16).all (fun j => pq.1[pq.2.getD j 0]? == some j) &&
    ap pq.1 goal == goal && ap pq.1 truthMask == truthMask

theorem ok_len {pq} (h : okPerm pq = true) : pq.1.length = 16 := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1

theorem ok_lt {pq} (h : okPerm pq = true) : ∀ j ∈ pq.1, j < 16 := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem ok_inv {pq} (h : okPerm pq = true) : ∀ j, j < 16 → pq.1[pq.2.getD j 0]? = some j := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact h.1.1.2

theorem ok_goal {pq} (h : okPerm pq = true) : ap pq.1 goal = goal := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2

theorem ok_mask {pq} (h : okPerm pq = true) : ap pq.1 truthMask = truthMask := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq] at h; exact h.2

theorem perm_cases {pq} (h : okPerm pq = true) (i : Nat) :
    (pq.1[i]? = none ∧ ¬ i < 16) ∨ (∃ j, pq.1[i]? = some j ∧ i < 16 ∧ j < 16) := by
  have hl := ok_len h
  cases hpi : pq.1[i]? with
  | none =>
    left; refine ⟨rfl, ?_⟩
    have := List.getElem?_eq_none_iff.1 hpi; omega
  | some j =>
    right
    obtain ⟨hi, hj⟩ := List.getElem?_eq_some_iff.1 hpi
    exact ⟨j, rfl, by omega, ok_lt h j (hj ▸ List.getElem_mem hi)⟩

theorem high_bit {a : Nat} (ha : a < 2 ^ 16) {j : Nat} (hj : ¬ j < 16) : a.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))

theorem ap_inj {pq} (h : okPerm pq = true) {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16)
    (he : ap pq.1 a = ap pq.1 b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 16
  · have hq := ok_inv h j hj
    have h1 := ap_bit pq.1 a (pq.2.getD j 0)
    have h2 := ap_bit pq.1 b (pq.2.getD j 0)
    rw [hq] at h1 h2
    simp only at h1 h2
    rw [← h1, ← h2, he]
  · rw [high_bit ha hj, high_bit hb hj]

theorem ap_neg {pq} (h : okPerm pq = true) (a : Nat) :
    ap pq.1 (negD truthMask a) = negD truthMask (ap pq.1 a) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor, truthMask_bit, ap_bit]
  rcases perm_cases h i with ⟨h1, h2⟩ | ⟨j, h1, h2, h3⟩
  · simp [h1, h2]
  · simp [h1, h2, h3]

theorem ap_and {pq} (h : okPerm pq = true) (a b : Nat) :
    ap pq.1 (andD truthMask a b) = andD truthMask (ap pq.1 a) (ap pq.1 b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [andD, Nat.testBit_and, truthMask_bit, ap_bit]
  rcases perm_cases h i with ⟨h1, h2⟩ | ⟨j, h1, h2, h3⟩
  · simp [h1, h2]
  · simp [h1, h2, h3]

theorem ap_or {pq} (h : okPerm pq = true) (a b : Nat) :
    ap pq.1 (orD truthMask a b) = orD truthMask (ap pq.1 a) (ap pq.1 b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or, truthMask_bit, ap_bit]
  rcases perm_cases h i with ⟨h1, h2⟩ | ⟨j, h1, h2, h3⟩
  · simp [h1, h2]
  · simp [h1, h2, h3]

theorem ap_bin {pq} (h : okPerm pq = true) (c : Bool) (a b : Nat) :
    ap pq.1 (if c then andD truthMask a b else orD truthMask a b) =
      (if c then andD truthMask (ap pq.1 a) (ap pq.1 b) else orD truthMask (ap pq.1 a) (ap pq.1 b)) := by
  cases c
  · simpa using ap_or h a b
  · simpa using ap_and h a b

theorem mask_lt : truthMask < 2 ^ 16 := by decide

theorem negD_lt (a : Nat) : negD truthMask a < 2 ^ 16 :=
  Nat.lt_of_le_of_lt Nat.and_le_right mask_lt

theorem bin_lt (c : Bool) (a b : Nat) :
    (if c then andD truthMask a b else orD truthMask a b) < 2 ^ 16 := by
  cases c
  · exact Nat.lt_of_le_of_lt Nat.and_le_right mask_lt
  · exact Nat.lt_of_le_of_lt Nat.and_le_right mask_lt

theorem ap_zero (pq : List Nat × List Nat) : ap pq.1 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [ap_bit]
  cases pq.1[i]? <;> simp

theorem map_kept (f : Nat → Nat) (b : Bool) (x : Nat) (xs : List Nat) :
    (kept b x xs).map f = kept b (f x) (xs.map f) := by cases b <;> rfl

theorem ap_new {pq} (h : okPerm pq = true) {w : Nat} {xs : List Nat} (hw : w < 2 ^ 16)
    (hb : ∀ x ∈ xs, x < 2 ^ 16) (h0 : w ≠ 0) (hd : w ≠ truthMask) (hm : w ∉ xs) :
    ap pq.1 w ≠ 0 ∧ ap pq.1 w ≠ truthMask ∧ ap pq.1 w ∉ xs.map (ap pq.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    exact h0 (ap_inj h hw (by decide) (he.trans (ap_zero pq).symm))
  · intro he
    exact hd (ap_inj h hw mask_lt (he.trans (ok_mask h).symm))
  · intro hmem
    obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hmem
    exact hm ((ap_inj h (hb x hx) hw hxe) ▸ hx)

theorem run_sym {pq} (hp : okPerm pq = true) {y s ws} (h : RunD truthMask y s ws) :
    (∀ w ∈ ws, w < 2 ^ 16) → RunD truthMask (ap pq.1 y) s (ws.map (ap pq.1)) := by
  induction h using Run.fold with
  | done => intro _; exact Run.done
  | perm p _ ih =>
    intro hb
    exact Run.perm (p.map _) (ih (fun w hw => hb w (p.mem_iff.1 hw)))
  | @one s a r save h0 hd hnm h ih =>
    intro hb
    obtain ⟨n0, nd, nm⟩ := ap_new hp (negD_lt a) hb h0 hd hnm
    have hb' : ∀ w ∈ negD truthMask a :: kept save a r, w < 2 ^ 16 := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact negD_lt a
      · rcases (mem_kept save a w r).1 hw with ⟨_, rfl⟩ | hw
        · exact hb _ (List.mem_cons_self ..)
        · exact hb _ (List.mem_cons_of_mem _ hw)
    have ih' := ih hb'
    rw [List.map_cons, map_kept, ap_neg hp] at ih'
    rw [ap_neg hp] at n0 nd nm
    exact Run.one save n0 nd nm ih'
  | @two s a b r c ka kb h0 hd hnm h ih =>
    intro hb
    obtain ⟨n0, nd, nm⟩ := ap_new hp (bin_lt c a b) hb h0 hd hnm
    have hb' : ∀ w ∈ (if c then andD truthMask a b else orD truthMask a b) :: kept ka a (kept kb b r), w < 2 ^ 16 := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact bin_lt c a b
      · rcases (mem_kept ka a w _).1 hw with ⟨_, rfl⟩ | hw
        · exact hb _ (List.mem_cons_self ..)
        · rcases (mem_kept kb b w _).1 hw with ⟨_, rfl⟩ | hw
          · exact hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          · exact hb _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
    have ih' := ih hb'
    rw [List.map_cons, map_kept, map_kept, ap_bin hp] at ih'
    rw [ap_bin hp] at n0 nd nm
    exact Run.two c ka kb n0 nd nm ih'

def grp : List (List Nat × List Nat) := [([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), ([0, 12, 8, 4, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5], [0, 12, 8, 4, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5]), ([1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6], [1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6]), ([1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 0, 4, 8, 12], [12, 0, 4, 8, 13, 1, 5, 9, 14, 2, 6, 10, 15, 3, 7, 11]), ([5, 1, 13, 9, 4, 0, 12, 8, 7, 3, 15, 11, 6, 2, 14, 10], [5, 1, 13, 9, 4, 0, 12, 8, 7, 3, 15, 11, 6, 2, 14, 10]), ([5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12, 1, 2, 3, 0], [15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10]), ([6, 5, 4, 7, 2, 1, 0, 3, 14, 13, 12, 15, 10, 9, 8, 11], [6, 5, 4, 7, 2, 1, 0, 3, 14, 13, 12, 15, 10, 9, 8, 11]), ([6, 10, 14, 2, 7, 11, 15, 3, 4, 8, 12, 0, 5, 9, 13, 1], [11, 15, 3, 7, 8, 12, 0, 4, 9, 13, 1, 5, 10, 14, 2, 6]), ([10, 6, 2, 14, 9, 5, 1, 13, 8, 4, 0, 12, 11, 7, 3, 15], [10, 6, 2, 14, 9, 5, 1, 13, 8, 4, 0, 12, 11, 7, 3, 15]), ([10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], [10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5]), ([11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12], [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12]), ([11, 15, 3, 7, 8, 12, 0, 4, 9, 13, 1, 5, 10, 14, 2, 6], [6, 10, 14, 2, 7, 11, 15, 3, 4, 8, 12, 0, 5, 9, 13, 1]), ([12, 0, 4, 8, 13, 1, 5, 9, 14, 2, 6, 10, 15, 3, 7, 11], [1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 0, 4, 8, 12]), ([12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5, 0, 3, 2, 1], [12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5, 0, 3, 2, 1]), ([15, 11, 7, 3, 14, 10, 6, 2, 13, 9, 5, 1, 12, 8, 4, 0], [15, 11, 7, 3, 14, 10, 6, 2, 13, 9, 5, 1, 12, 8, 4, 0]), ([15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10], [5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12, 1, 2, 3, 0])]

theorem okG : grp.all okPerm = true := by decide +kernel

def listed (s : Nat) (ws : List Nat) : Bool :=
  ws.all (fun w => decide (w < 2 ^ 16)) &&
    grp.any (fun pq => ((rowsOf s).getD (key (ws.map (ap pq.1))) []).any (fun l => (ws.map (ap pq.1)).isPerm l))

theorem sym_run {s : Nat} {ys : List Nat} (hl : listed s ys = true) (h : RunD truthMask goal s ys) :
    ∃ i, i < 128 ∧ ∃ zs ∈ (rowsOf s).getD i [], RunD truthMask goal s zs := by
  simp only [listed, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hl
  obtain ⟨hb, pq, hpq, zs, hzs, hz⟩ := hl
  have hok := List.all_eq_true.1 okG pq hpq
  have h2 := run_sym hok h hb
  rw [ok_goal hok] at h2
  exact ⟨_, key_lt _, zs, hzs, Run.perm (List.isPerm_iff.1 hz) h2⟩

def blocked (s : Nat) (ws : List Nat) : Bool :=
  match s with
  | 0 => ws != [goal]
  | s + 1 => !(nextD truthMask (s + 2 - ws.length) ws
      (fun ys => coversP pairs s ys && !(listed s ys)))

private theorem validPairs :
    pairs.all (fun p => truthMask.testBit p.1 && truthMask.testBit p.2 &&
                      !goal.testBit p.1 && goal.testBit p.2) = true := by decide +kernel

def cellCheck (s i : Nat) : Bool := ((rowsOf s).getD i []).all (blocked s)

private theorem lvl_0 : ∀ i, 0 ≤ i → i < 128 → cellCheck 0 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf]
private theorem lvl_1 : ∀ i, 0 ≤ i → i < 128 → cellCheck 1 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf]
private theorem lvl_2 : ∀ i, 0 ≤ i → i < 128 → cellCheck 2 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_0 : ∀ i, 0 ≤ i → i < 1 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_1 : ∀ i, 1 ≤ i → i < 2 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 1 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_2 : ∀ i, 2 ≤ i → i < 3 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 2 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_3 : ∀ i, 3 ≤ i → i < 4 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 3 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_4 : ∀ i, 4 ≤ i → i < 5 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_5 : ∀ i, 5 ≤ i → i < 6 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 5 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_6 : ∀ i, 6 ≤ i → i < 7 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 6 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_7 : ∀ i, 7 ≤ i → i < 8 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 7 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_8 : ∀ i, 8 ≤ i → i < 9 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_9 : ∀ i, 9 ≤ i → i < 10 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 9 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_10 : ∀ i, 10 ≤ i → i < 11 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 10 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_11 : ∀ i, 11 ≤ i → i < 12 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 11 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_12 : ∀ i, 12 ≤ i → i < 13 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_13 : ∀ i, 13 ≤ i → i < 14 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 13 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_14 : ∀ i, 14 ≤ i → i < 15 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 14 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_15 : ∀ i, 15 ≤ i → i < 16 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 15 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_16 : ∀ i, 16 ≤ i → i < 17 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_17 : ∀ i, 17 ≤ i → i < 18 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 17 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_18 : ∀ i, 18 ≤ i → i < 19 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 18 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_19 : ∀ i, 19 ≤ i → i < 20 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 19 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_20 : ∀ i, 20 ≤ i → i < 21 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_21 : ∀ i, 21 ≤ i → i < 22 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 21 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_22 : ∀ i, 22 ≤ i → i < 23 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 22 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_23 : ∀ i, 23 ≤ i → i < 24 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 23 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_24 : ∀ i, 24 ≤ i → i < 25 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_25 : ∀ i, 25 ≤ i → i < 26 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 25 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_26 : ∀ i, 26 ≤ i → i < 27 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 26 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_27 : ∀ i, 27 ≤ i → i < 28 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 27 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_28 : ∀ i, 28 ≤ i → i < 29 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_29 : ∀ i, 29 ≤ i → i < 30 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 29 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_30 : ∀ i, 30 ≤ i → i < 31 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 30 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_31 : ∀ i, 31 ≤ i → i < 32 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 31 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_32 : ∀ i, 32 ≤ i → i < 33 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_33 : ∀ i, 33 ≤ i → i < 34 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 33 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_34 : ∀ i, 34 ≤ i → i < 35 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 34 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_35 : ∀ i, 35 ≤ i → i < 36 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 35 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_36 : ∀ i, 36 ≤ i → i < 37 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_37 : ∀ i, 37 ≤ i → i < 38 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 37 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_38 : ∀ i, 38 ≤ i → i < 39 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 38 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_39 : ∀ i, 39 ≤ i → i < 40 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 39 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_40 : ∀ i, 40 ≤ i → i < 41 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_41 : ∀ i, 41 ≤ i → i < 42 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 41 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_42 : ∀ i, 42 ≤ i → i < 43 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 42 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_43 : ∀ i, 43 ≤ i → i < 44 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 43 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_44 : ∀ i, 44 ≤ i → i < 45 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_45 : ∀ i, 45 ≤ i → i < 46 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 45 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_46 : ∀ i, 46 ≤ i → i < 47 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 46 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_47 : ∀ i, 47 ≤ i → i < 48 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 47 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_48 : ∀ i, 48 ≤ i → i < 49 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_49 : ∀ i, 49 ≤ i → i < 50 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 49 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_50 : ∀ i, 50 ≤ i → i < 51 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 50 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_51 : ∀ i, 51 ≤ i → i < 52 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 51 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_52 : ∀ i, 52 ≤ i → i < 53 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_53 : ∀ i, 53 ≤ i → i < 54 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 53 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_54 : ∀ i, 54 ≤ i → i < 55 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 54 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_55 : ∀ i, 55 ≤ i → i < 56 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 55 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_56 : ∀ i, 56 ≤ i → i < 57 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_57 : ∀ i, 57 ≤ i → i < 58 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 57 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_58 : ∀ i, 58 ≤ i → i < 59 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 58 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_59 : ∀ i, 59 ≤ i → i < 60 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 59 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_60 : ∀ i, 60 ≤ i → i < 61 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_61 : ∀ i, 61 ≤ i → i < 62 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 61 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_62 : ∀ i, 62 ≤ i → i < 63 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 62 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_63 : ∀ i, 63 ≤ i → i < 64 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 63 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_64 : ∀ i, 64 ≤ i → i < 65 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_65 : ∀ i, 65 ≤ i → i < 66 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 65 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_66 : ∀ i, 66 ≤ i → i < 67 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 66 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_67 : ∀ i, 67 ≤ i → i < 68 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 67 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_68 : ∀ i, 68 ≤ i → i < 69 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_69 : ∀ i, 69 ≤ i → i < 70 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 69 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_70 : ∀ i, 70 ≤ i → i < 71 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 70 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_71 : ∀ i, 71 ≤ i → i < 72 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 71 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_72 : ∀ i, 72 ≤ i → i < 73 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_73 : ∀ i, 73 ≤ i → i < 74 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 73 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_74 : ∀ i, 74 ≤ i → i < 75 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 74 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_75 : ∀ i, 75 ≤ i → i < 76 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 75 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_76 : ∀ i, 76 ≤ i → i < 77 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_77 : ∀ i, 77 ≤ i → i < 78 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 77 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_78 : ∀ i, 78 ≤ i → i < 79 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 78 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_79 : ∀ i, 79 ≤ i → i < 80 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 79 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_80 : ∀ i, 80 ≤ i → i < 81 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_81 : ∀ i, 81 ≤ i → i < 82 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 81 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_82 : ∀ i, 82 ≤ i → i < 83 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 82 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_83 : ∀ i, 83 ≤ i → i < 84 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 83 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_84 : ∀ i, 84 ≤ i → i < 85 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_85 : ∀ i, 85 ≤ i → i < 86 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 85 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_86 : ∀ i, 86 ≤ i → i < 87 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 86 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_87 : ∀ i, 87 ≤ i → i < 88 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 87 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_88 : ∀ i, 88 ≤ i → i < 89 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_89 : ∀ i, 89 ≤ i → i < 90 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 89 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_90 : ∀ i, 90 ≤ i → i < 91 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 90 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_91 : ∀ i, 91 ≤ i → i < 92 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 91 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_92 : ∀ i, 92 ≤ i → i < 93 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_93 : ∀ i, 93 ≤ i → i < 94 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 93 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_94 : ∀ i, 94 ≤ i → i < 95 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 94 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_95 : ∀ i, 95 ≤ i → i < 96 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 95 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_96 : ∀ i, 96 ≤ i → i < 97 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_97 : ∀ i, 97 ≤ i → i < 98 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 97 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_98 : ∀ i, 98 ≤ i → i < 99 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 98 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_99 : ∀ i, 99 ≤ i → i < 100 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 99 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_100 : ∀ i, 100 ≤ i → i < 101 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_101 : ∀ i, 101 ≤ i → i < 102 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 101 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_102 : ∀ i, 102 ≤ i → i < 103 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 102 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_103 : ∀ i, 103 ≤ i → i < 104 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 103 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_104 : ∀ i, 104 ≤ i → i < 105 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_105 : ∀ i, 105 ≤ i → i < 106 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 105 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_106 : ∀ i, 106 ≤ i → i < 107 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 106 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_107 : ∀ i, 107 ≤ i → i < 108 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 107 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_108 : ∀ i, 108 ≤ i → i < 109 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_109 : ∀ i, 109 ≤ i → i < 110 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 109 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_110 : ∀ i, 110 ≤ i → i < 111 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 110 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_111 : ∀ i, 111 ≤ i → i < 112 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 111 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_112 : ∀ i, 112 ≤ i → i < 113 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_113 : ∀ i, 113 ≤ i → i < 114 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 113 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_114 : ∀ i, 114 ≤ i → i < 115 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 114 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_115 : ∀ i, 115 ≤ i → i < 116 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 115 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_116 : ∀ i, 116 ≤ i → i < 117 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_117 : ∀ i, 117 ≤ i → i < 118 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 117 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_118 : ∀ i, 118 ≤ i → i < 119 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 118 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_119 : ∀ i, 119 ≤ i → i < 120 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 119 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_120 : ∀ i, 120 ≤ i → i < 121 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_121 : ∀ i, 121 ≤ i → i < 122 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 121 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_122 : ∀ i, 122 ≤ i → i < 123 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 122 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_123 : ∀ i, 123 ≤ i → i < 124 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 123 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_124 : ∀ i, 124 ≤ i → i < 125 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_125 : ∀ i, 125 ≤ i → i < 126 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 125 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_126 : ∀ i, 126 ≤ i → i < 127 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 126 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_3_127 : ∀ i, 127 ≤ i → i < 128 → cellCheck 3 i = true :=
  span_ok (by decide +kernel : span (cellCheck 3) 1 127 = true)
private theorem lvl_3 : ∀ i, 0 ≤ i → i < 128 → cellCheck 3 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_3_0 cell_3_1) (range_split cell_3_2 cell_3_3)) (range_split (range_split cell_3_4 cell_3_5) (range_split cell_3_6 cell_3_7))) (range_split (range_split (range_split cell_3_8 cell_3_9) (range_split cell_3_10 cell_3_11)) (range_split (range_split cell_3_12 cell_3_13) (range_split cell_3_14 cell_3_15)))) (range_split (range_split (range_split (range_split cell_3_16 cell_3_17) (range_split cell_3_18 cell_3_19)) (range_split (range_split cell_3_20 cell_3_21) (range_split cell_3_22 cell_3_23))) (range_split (range_split (range_split cell_3_24 cell_3_25) (range_split cell_3_26 cell_3_27)) (range_split (range_split cell_3_28 cell_3_29) (range_split cell_3_30 cell_3_31))))) (range_split (range_split (range_split (range_split (range_split cell_3_32 cell_3_33) (range_split cell_3_34 cell_3_35)) (range_split (range_split cell_3_36 cell_3_37) (range_split cell_3_38 cell_3_39))) (range_split (range_split (range_split cell_3_40 cell_3_41) (range_split cell_3_42 cell_3_43)) (range_split (range_split cell_3_44 cell_3_45) (range_split cell_3_46 cell_3_47)))) (range_split (range_split (range_split (range_split cell_3_48 cell_3_49) (range_split cell_3_50 cell_3_51)) (range_split (range_split cell_3_52 cell_3_53) (range_split cell_3_54 cell_3_55))) (range_split (range_split (range_split cell_3_56 cell_3_57) (range_split cell_3_58 cell_3_59)) (range_split (range_split cell_3_60 cell_3_61) (range_split cell_3_62 cell_3_63)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_3_64 cell_3_65) (range_split cell_3_66 cell_3_67)) (range_split (range_split cell_3_68 cell_3_69) (range_split cell_3_70 cell_3_71))) (range_split (range_split (range_split cell_3_72 cell_3_73) (range_split cell_3_74 cell_3_75)) (range_split (range_split cell_3_76 cell_3_77) (range_split cell_3_78 cell_3_79)))) (range_split (range_split (range_split (range_split cell_3_80 cell_3_81) (range_split cell_3_82 cell_3_83)) (range_split (range_split cell_3_84 cell_3_85) (range_split cell_3_86 cell_3_87))) (range_split (range_split (range_split cell_3_88 cell_3_89) (range_split cell_3_90 cell_3_91)) (range_split (range_split cell_3_92 cell_3_93) (range_split cell_3_94 cell_3_95))))) (range_split (range_split (range_split (range_split (range_split cell_3_96 cell_3_97) (range_split cell_3_98 cell_3_99)) (range_split (range_split cell_3_100 cell_3_101) (range_split cell_3_102 cell_3_103))) (range_split (range_split (range_split cell_3_104 cell_3_105) (range_split cell_3_106 cell_3_107)) (range_split (range_split cell_3_108 cell_3_109) (range_split cell_3_110 cell_3_111)))) (range_split (range_split (range_split (range_split cell_3_112 cell_3_113) (range_split cell_3_114 cell_3_115)) (range_split (range_split cell_3_116 cell_3_117) (range_split cell_3_118 cell_3_119))) (range_split (range_split (range_split cell_3_120 cell_3_121) (range_split cell_3_122 cell_3_123)) (range_split (range_split cell_3_124 cell_3_125) (range_split cell_3_126 cell_3_127)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_0 : ∀ i, 0 ≤ i → i < 1 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_1 : ∀ i, 1 ≤ i → i < 2 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 1 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_2 : ∀ i, 2 ≤ i → i < 3 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 2 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_3 : ∀ i, 3 ≤ i → i < 4 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 3 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_4 : ∀ i, 4 ≤ i → i < 5 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_5 : ∀ i, 5 ≤ i → i < 6 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 5 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_6 : ∀ i, 6 ≤ i → i < 7 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 6 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_7 : ∀ i, 7 ≤ i → i < 8 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 7 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_8 : ∀ i, 8 ≤ i → i < 9 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_9 : ∀ i, 9 ≤ i → i < 10 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 9 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_10 : ∀ i, 10 ≤ i → i < 11 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 10 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_11 : ∀ i, 11 ≤ i → i < 12 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 11 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_12 : ∀ i, 12 ≤ i → i < 13 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_13 : ∀ i, 13 ≤ i → i < 14 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 13 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_14 : ∀ i, 14 ≤ i → i < 15 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 14 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_15 : ∀ i, 15 ≤ i → i < 16 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 15 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_16 : ∀ i, 16 ≤ i → i < 17 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_17 : ∀ i, 17 ≤ i → i < 18 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 17 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_18 : ∀ i, 18 ≤ i → i < 19 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 18 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_19 : ∀ i, 19 ≤ i → i < 20 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 19 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_20 : ∀ i, 20 ≤ i → i < 21 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_21 : ∀ i, 21 ≤ i → i < 22 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 21 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_22 : ∀ i, 22 ≤ i → i < 23 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 22 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_23 : ∀ i, 23 ≤ i → i < 24 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 23 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_24 : ∀ i, 24 ≤ i → i < 25 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_25 : ∀ i, 25 ≤ i → i < 26 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 25 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_26 : ∀ i, 26 ≤ i → i < 27 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 26 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_27 : ∀ i, 27 ≤ i → i < 28 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 27 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_28 : ∀ i, 28 ≤ i → i < 29 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_29 : ∀ i, 29 ≤ i → i < 30 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 29 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_30 : ∀ i, 30 ≤ i → i < 31 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 30 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_31 : ∀ i, 31 ≤ i → i < 32 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 31 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_32 : ∀ i, 32 ≤ i → i < 33 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_33 : ∀ i, 33 ≤ i → i < 34 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 33 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_34 : ∀ i, 34 ≤ i → i < 35 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 34 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_35 : ∀ i, 35 ≤ i → i < 36 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 35 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_36 : ∀ i, 36 ≤ i → i < 37 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_37 : ∀ i, 37 ≤ i → i < 38 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 37 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_38 : ∀ i, 38 ≤ i → i < 39 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 38 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_39 : ∀ i, 39 ≤ i → i < 40 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 39 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_40 : ∀ i, 40 ≤ i → i < 41 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_41 : ∀ i, 41 ≤ i → i < 42 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 41 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_42 : ∀ i, 42 ≤ i → i < 43 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 42 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_43 : ∀ i, 43 ≤ i → i < 44 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 43 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_44 : ∀ i, 44 ≤ i → i < 45 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_45 : ∀ i, 45 ≤ i → i < 46 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 45 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_46 : ∀ i, 46 ≤ i → i < 47 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 46 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_47 : ∀ i, 47 ≤ i → i < 48 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 47 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_48 : ∀ i, 48 ≤ i → i < 49 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_49 : ∀ i, 49 ≤ i → i < 50 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 49 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_50 : ∀ i, 50 ≤ i → i < 51 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 50 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_51 : ∀ i, 51 ≤ i → i < 52 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 51 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_52 : ∀ i, 52 ≤ i → i < 53 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_53 : ∀ i, 53 ≤ i → i < 54 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 53 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_54 : ∀ i, 54 ≤ i → i < 55 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 54 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_55 : ∀ i, 55 ≤ i → i < 56 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 55 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_56 : ∀ i, 56 ≤ i → i < 57 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_57 : ∀ i, 57 ≤ i → i < 58 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 57 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_58 : ∀ i, 58 ≤ i → i < 59 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 58 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_59 : ∀ i, 59 ≤ i → i < 60 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 59 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_60 : ∀ i, 60 ≤ i → i < 61 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_61 : ∀ i, 61 ≤ i → i < 62 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 61 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_62 : ∀ i, 62 ≤ i → i < 63 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 62 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_63 : ∀ i, 63 ≤ i → i < 64 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 63 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_64 : ∀ i, 64 ≤ i → i < 65 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_65 : ∀ i, 65 ≤ i → i < 66 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 65 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_66 : ∀ i, 66 ≤ i → i < 67 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 66 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_67 : ∀ i, 67 ≤ i → i < 68 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 67 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_68 : ∀ i, 68 ≤ i → i < 69 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_69 : ∀ i, 69 ≤ i → i < 70 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 69 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_70 : ∀ i, 70 ≤ i → i < 71 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 70 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_71 : ∀ i, 71 ≤ i → i < 72 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 71 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_72 : ∀ i, 72 ≤ i → i < 73 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_73 : ∀ i, 73 ≤ i → i < 74 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 73 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_74 : ∀ i, 74 ≤ i → i < 75 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 74 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_75 : ∀ i, 75 ≤ i → i < 76 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 75 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_76 : ∀ i, 76 ≤ i → i < 77 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_77 : ∀ i, 77 ≤ i → i < 78 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 77 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_78 : ∀ i, 78 ≤ i → i < 79 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 78 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_79 : ∀ i, 79 ≤ i → i < 80 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 79 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_80 : ∀ i, 80 ≤ i → i < 81 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_81 : ∀ i, 81 ≤ i → i < 82 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 81 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_82 : ∀ i, 82 ≤ i → i < 83 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 82 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_83 : ∀ i, 83 ≤ i → i < 84 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 83 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_84 : ∀ i, 84 ≤ i → i < 85 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_85 : ∀ i, 85 ≤ i → i < 86 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 85 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_86 : ∀ i, 86 ≤ i → i < 87 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 86 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_87 : ∀ i, 87 ≤ i → i < 88 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 87 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_88 : ∀ i, 88 ≤ i → i < 89 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_89 : ∀ i, 89 ≤ i → i < 90 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 89 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_90 : ∀ i, 90 ≤ i → i < 91 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 90 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_91 : ∀ i, 91 ≤ i → i < 92 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 91 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_92 : ∀ i, 92 ≤ i → i < 93 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_93 : ∀ i, 93 ≤ i → i < 94 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 93 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_94 : ∀ i, 94 ≤ i → i < 95 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 94 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_95 : ∀ i, 95 ≤ i → i < 96 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 95 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_96 : ∀ i, 96 ≤ i → i < 97 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_97 : ∀ i, 97 ≤ i → i < 98 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 97 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_98 : ∀ i, 98 ≤ i → i < 99 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 98 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_99 : ∀ i, 99 ≤ i → i < 100 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 99 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_100 : ∀ i, 100 ≤ i → i < 101 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_101 : ∀ i, 101 ≤ i → i < 102 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 101 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_102 : ∀ i, 102 ≤ i → i < 103 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 102 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_103 : ∀ i, 103 ≤ i → i < 104 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 103 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_104 : ∀ i, 104 ≤ i → i < 105 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_105 : ∀ i, 105 ≤ i → i < 106 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 105 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_106 : ∀ i, 106 ≤ i → i < 107 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 106 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_107 : ∀ i, 107 ≤ i → i < 108 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 107 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_108 : ∀ i, 108 ≤ i → i < 109 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_109 : ∀ i, 109 ≤ i → i < 110 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 109 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_110 : ∀ i, 110 ≤ i → i < 111 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 110 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_111 : ∀ i, 111 ≤ i → i < 112 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 111 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_112 : ∀ i, 112 ≤ i → i < 113 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_113 : ∀ i, 113 ≤ i → i < 114 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 113 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_114 : ∀ i, 114 ≤ i → i < 115 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 114 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_115 : ∀ i, 115 ≤ i → i < 116 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 115 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_116 : ∀ i, 116 ≤ i → i < 117 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_117 : ∀ i, 117 ≤ i → i < 118 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 117 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_118 : ∀ i, 118 ≤ i → i < 119 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 118 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_119 : ∀ i, 119 ≤ i → i < 120 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 119 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_120 : ∀ i, 120 ≤ i → i < 121 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_121 : ∀ i, 121 ≤ i → i < 122 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 121 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_122 : ∀ i, 122 ≤ i → i < 123 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 122 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_123 : ∀ i, 123 ≤ i → i < 124 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 123 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_124 : ∀ i, 124 ≤ i → i < 125 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_125 : ∀ i, 125 ≤ i → i < 126 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 125 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_126 : ∀ i, 126 ≤ i → i < 127 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 126 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_4_127 : ∀ i, 127 ≤ i → i < 128 → cellCheck 4 i = true :=
  span_ok (by decide +kernel : span (cellCheck 4) 1 127 = true)
private theorem lvl_4 : ∀ i, 0 ≤ i → i < 128 → cellCheck 4 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_4_0 cell_4_1) (range_split cell_4_2 cell_4_3)) (range_split (range_split cell_4_4 cell_4_5) (range_split cell_4_6 cell_4_7))) (range_split (range_split (range_split cell_4_8 cell_4_9) (range_split cell_4_10 cell_4_11)) (range_split (range_split cell_4_12 cell_4_13) (range_split cell_4_14 cell_4_15)))) (range_split (range_split (range_split (range_split cell_4_16 cell_4_17) (range_split cell_4_18 cell_4_19)) (range_split (range_split cell_4_20 cell_4_21) (range_split cell_4_22 cell_4_23))) (range_split (range_split (range_split cell_4_24 cell_4_25) (range_split cell_4_26 cell_4_27)) (range_split (range_split cell_4_28 cell_4_29) (range_split cell_4_30 cell_4_31))))) (range_split (range_split (range_split (range_split (range_split cell_4_32 cell_4_33) (range_split cell_4_34 cell_4_35)) (range_split (range_split cell_4_36 cell_4_37) (range_split cell_4_38 cell_4_39))) (range_split (range_split (range_split cell_4_40 cell_4_41) (range_split cell_4_42 cell_4_43)) (range_split (range_split cell_4_44 cell_4_45) (range_split cell_4_46 cell_4_47)))) (range_split (range_split (range_split (range_split cell_4_48 cell_4_49) (range_split cell_4_50 cell_4_51)) (range_split (range_split cell_4_52 cell_4_53) (range_split cell_4_54 cell_4_55))) (range_split (range_split (range_split cell_4_56 cell_4_57) (range_split cell_4_58 cell_4_59)) (range_split (range_split cell_4_60 cell_4_61) (range_split cell_4_62 cell_4_63)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_4_64 cell_4_65) (range_split cell_4_66 cell_4_67)) (range_split (range_split cell_4_68 cell_4_69) (range_split cell_4_70 cell_4_71))) (range_split (range_split (range_split cell_4_72 cell_4_73) (range_split cell_4_74 cell_4_75)) (range_split (range_split cell_4_76 cell_4_77) (range_split cell_4_78 cell_4_79)))) (range_split (range_split (range_split (range_split cell_4_80 cell_4_81) (range_split cell_4_82 cell_4_83)) (range_split (range_split cell_4_84 cell_4_85) (range_split cell_4_86 cell_4_87))) (range_split (range_split (range_split cell_4_88 cell_4_89) (range_split cell_4_90 cell_4_91)) (range_split (range_split cell_4_92 cell_4_93) (range_split cell_4_94 cell_4_95))))) (range_split (range_split (range_split (range_split (range_split cell_4_96 cell_4_97) (range_split cell_4_98 cell_4_99)) (range_split (range_split cell_4_100 cell_4_101) (range_split cell_4_102 cell_4_103))) (range_split (range_split (range_split cell_4_104 cell_4_105) (range_split cell_4_106 cell_4_107)) (range_split (range_split cell_4_108 cell_4_109) (range_split cell_4_110 cell_4_111)))) (range_split (range_split (range_split (range_split cell_4_112 cell_4_113) (range_split cell_4_114 cell_4_115)) (range_split (range_split cell_4_116 cell_4_117) (range_split cell_4_118 cell_4_119))) (range_split (range_split (range_split cell_4_120 cell_4_121) (range_split cell_4_122 cell_4_123)) (range_split (range_split cell_4_124 cell_4_125) (range_split cell_4_126 cell_4_127)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_0 : ∀ i, 0 ≤ i → i < 1 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_1 : ∀ i, 1 ≤ i → i < 2 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 1 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_2 : ∀ i, 2 ≤ i → i < 3 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 2 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_3 : ∀ i, 3 ≤ i → i < 4 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 3 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_4 : ∀ i, 4 ≤ i → i < 5 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_5 : ∀ i, 5 ≤ i → i < 6 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 5 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_6 : ∀ i, 6 ≤ i → i < 7 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 6 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_7 : ∀ i, 7 ≤ i → i < 8 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 7 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_8 : ∀ i, 8 ≤ i → i < 9 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_9 : ∀ i, 9 ≤ i → i < 10 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 9 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_10 : ∀ i, 10 ≤ i → i < 11 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 10 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_11 : ∀ i, 11 ≤ i → i < 12 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 11 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_12 : ∀ i, 12 ≤ i → i < 13 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_13 : ∀ i, 13 ≤ i → i < 14 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 13 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_14 : ∀ i, 14 ≤ i → i < 15 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 14 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_15 : ∀ i, 15 ≤ i → i < 16 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 15 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_16 : ∀ i, 16 ≤ i → i < 17 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_17 : ∀ i, 17 ≤ i → i < 18 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 17 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_18 : ∀ i, 18 ≤ i → i < 19 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 18 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_19 : ∀ i, 19 ≤ i → i < 20 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 19 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_20 : ∀ i, 20 ≤ i → i < 21 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_21 : ∀ i, 21 ≤ i → i < 22 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 21 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_22 : ∀ i, 22 ≤ i → i < 23 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 22 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_23 : ∀ i, 23 ≤ i → i < 24 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 23 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_24 : ∀ i, 24 ≤ i → i < 25 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_25 : ∀ i, 25 ≤ i → i < 26 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 25 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_26 : ∀ i, 26 ≤ i → i < 27 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 26 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_27 : ∀ i, 27 ≤ i → i < 28 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 27 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_28 : ∀ i, 28 ≤ i → i < 29 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_29 : ∀ i, 29 ≤ i → i < 30 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 29 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_30 : ∀ i, 30 ≤ i → i < 31 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 30 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_31 : ∀ i, 31 ≤ i → i < 32 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 31 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_32 : ∀ i, 32 ≤ i → i < 33 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_33 : ∀ i, 33 ≤ i → i < 34 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 33 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_34 : ∀ i, 34 ≤ i → i < 35 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 34 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_35 : ∀ i, 35 ≤ i → i < 36 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 35 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_36 : ∀ i, 36 ≤ i → i < 37 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_37 : ∀ i, 37 ≤ i → i < 38 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 37 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_38 : ∀ i, 38 ≤ i → i < 39 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 38 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_39 : ∀ i, 39 ≤ i → i < 40 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 39 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_40 : ∀ i, 40 ≤ i → i < 41 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_41 : ∀ i, 41 ≤ i → i < 42 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 41 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_42 : ∀ i, 42 ≤ i → i < 43 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 42 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_43 : ∀ i, 43 ≤ i → i < 44 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 43 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_44 : ∀ i, 44 ≤ i → i < 45 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_45 : ∀ i, 45 ≤ i → i < 46 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 45 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_46 : ∀ i, 46 ≤ i → i < 47 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 46 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_47 : ∀ i, 47 ≤ i → i < 48 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 47 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_48 : ∀ i, 48 ≤ i → i < 49 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_49 : ∀ i, 49 ≤ i → i < 50 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 49 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_50 : ∀ i, 50 ≤ i → i < 51 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 50 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_51 : ∀ i, 51 ≤ i → i < 52 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 51 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_52 : ∀ i, 52 ≤ i → i < 53 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_53 : ∀ i, 53 ≤ i → i < 54 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 53 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_54 : ∀ i, 54 ≤ i → i < 55 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 54 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_55 : ∀ i, 55 ≤ i → i < 56 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 55 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_56 : ∀ i, 56 ≤ i → i < 57 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_57 : ∀ i, 57 ≤ i → i < 58 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 57 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_58 : ∀ i, 58 ≤ i → i < 59 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 58 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_59 : ∀ i, 59 ≤ i → i < 60 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 59 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_60 : ∀ i, 60 ≤ i → i < 61 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_61 : ∀ i, 61 ≤ i → i < 62 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 61 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_62 : ∀ i, 62 ≤ i → i < 63 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 62 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_63 : ∀ i, 63 ≤ i → i < 64 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 63 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_64 : ∀ i, 64 ≤ i → i < 65 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_65 : ∀ i, 65 ≤ i → i < 66 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 65 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_66 : ∀ i, 66 ≤ i → i < 67 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 66 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_67 : ∀ i, 67 ≤ i → i < 68 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 67 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_68 : ∀ i, 68 ≤ i → i < 69 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_69 : ∀ i, 69 ≤ i → i < 70 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 69 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_70 : ∀ i, 70 ≤ i → i < 71 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 70 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_71 : ∀ i, 71 ≤ i → i < 72 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 71 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_72 : ∀ i, 72 ≤ i → i < 73 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_73 : ∀ i, 73 ≤ i → i < 74 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 73 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_74 : ∀ i, 74 ≤ i → i < 75 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 74 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_75 : ∀ i, 75 ≤ i → i < 76 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 75 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_76 : ∀ i, 76 ≤ i → i < 77 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_77 : ∀ i, 77 ≤ i → i < 78 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 77 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_78 : ∀ i, 78 ≤ i → i < 79 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 78 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_79 : ∀ i, 79 ≤ i → i < 80 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 79 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_80 : ∀ i, 80 ≤ i → i < 81 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_81 : ∀ i, 81 ≤ i → i < 82 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 81 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_82 : ∀ i, 82 ≤ i → i < 83 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 82 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_83 : ∀ i, 83 ≤ i → i < 84 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 83 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_84 : ∀ i, 84 ≤ i → i < 85 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_85 : ∀ i, 85 ≤ i → i < 86 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 85 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_86 : ∀ i, 86 ≤ i → i < 87 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 86 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_87 : ∀ i, 87 ≤ i → i < 88 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 87 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_88 : ∀ i, 88 ≤ i → i < 89 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_89 : ∀ i, 89 ≤ i → i < 90 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 89 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_90 : ∀ i, 90 ≤ i → i < 91 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 90 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_91 : ∀ i, 91 ≤ i → i < 92 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 91 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_92 : ∀ i, 92 ≤ i → i < 93 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_93 : ∀ i, 93 ≤ i → i < 94 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 93 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_94 : ∀ i, 94 ≤ i → i < 95 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 94 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_95 : ∀ i, 95 ≤ i → i < 96 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 95 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_96 : ∀ i, 96 ≤ i → i < 97 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_97 : ∀ i, 97 ≤ i → i < 98 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 97 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_98 : ∀ i, 98 ≤ i → i < 99 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 98 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_99 : ∀ i, 99 ≤ i → i < 100 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 99 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_100 : ∀ i, 100 ≤ i → i < 101 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_101 : ∀ i, 101 ≤ i → i < 102 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 101 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_102 : ∀ i, 102 ≤ i → i < 103 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 102 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_103 : ∀ i, 103 ≤ i → i < 104 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 103 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_104 : ∀ i, 104 ≤ i → i < 105 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_105 : ∀ i, 105 ≤ i → i < 106 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 105 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_106 : ∀ i, 106 ≤ i → i < 107 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 106 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_107 : ∀ i, 107 ≤ i → i < 108 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 107 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_108 : ∀ i, 108 ≤ i → i < 109 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_109 : ∀ i, 109 ≤ i → i < 110 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 109 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_110 : ∀ i, 110 ≤ i → i < 111 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 110 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_111 : ∀ i, 111 ≤ i → i < 112 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 111 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_112 : ∀ i, 112 ≤ i → i < 113 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_113 : ∀ i, 113 ≤ i → i < 114 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 113 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_114 : ∀ i, 114 ≤ i → i < 115 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 114 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_115 : ∀ i, 115 ≤ i → i < 116 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 115 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_116 : ∀ i, 116 ≤ i → i < 117 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_117 : ∀ i, 117 ≤ i → i < 118 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 117 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_118 : ∀ i, 118 ≤ i → i < 119 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 118 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_119 : ∀ i, 119 ≤ i → i < 120 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 119 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_120 : ∀ i, 120 ≤ i → i < 121 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_121 : ∀ i, 121 ≤ i → i < 122 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 121 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_122 : ∀ i, 122 ≤ i → i < 123 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 122 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_123 : ∀ i, 123 ≤ i → i < 124 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 123 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_124 : ∀ i, 124 ≤ i → i < 125 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_125 : ∀ i, 125 ≤ i → i < 126 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 125 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_126 : ∀ i, 126 ≤ i → i < 127 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 126 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_5_127 : ∀ i, 127 ≤ i → i < 128 → cellCheck 5 i = true :=
  span_ok (by decide +kernel : span (cellCheck 5) 1 127 = true)
private theorem lvl_5 : ∀ i, 0 ≤ i → i < 128 → cellCheck 5 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_5_0 cell_5_1) (range_split cell_5_2 cell_5_3)) (range_split (range_split cell_5_4 cell_5_5) (range_split cell_5_6 cell_5_7))) (range_split (range_split (range_split cell_5_8 cell_5_9) (range_split cell_5_10 cell_5_11)) (range_split (range_split cell_5_12 cell_5_13) (range_split cell_5_14 cell_5_15)))) (range_split (range_split (range_split (range_split cell_5_16 cell_5_17) (range_split cell_5_18 cell_5_19)) (range_split (range_split cell_5_20 cell_5_21) (range_split cell_5_22 cell_5_23))) (range_split (range_split (range_split cell_5_24 cell_5_25) (range_split cell_5_26 cell_5_27)) (range_split (range_split cell_5_28 cell_5_29) (range_split cell_5_30 cell_5_31))))) (range_split (range_split (range_split (range_split (range_split cell_5_32 cell_5_33) (range_split cell_5_34 cell_5_35)) (range_split (range_split cell_5_36 cell_5_37) (range_split cell_5_38 cell_5_39))) (range_split (range_split (range_split cell_5_40 cell_5_41) (range_split cell_5_42 cell_5_43)) (range_split (range_split cell_5_44 cell_5_45) (range_split cell_5_46 cell_5_47)))) (range_split (range_split (range_split (range_split cell_5_48 cell_5_49) (range_split cell_5_50 cell_5_51)) (range_split (range_split cell_5_52 cell_5_53) (range_split cell_5_54 cell_5_55))) (range_split (range_split (range_split cell_5_56 cell_5_57) (range_split cell_5_58 cell_5_59)) (range_split (range_split cell_5_60 cell_5_61) (range_split cell_5_62 cell_5_63)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_5_64 cell_5_65) (range_split cell_5_66 cell_5_67)) (range_split (range_split cell_5_68 cell_5_69) (range_split cell_5_70 cell_5_71))) (range_split (range_split (range_split cell_5_72 cell_5_73) (range_split cell_5_74 cell_5_75)) (range_split (range_split cell_5_76 cell_5_77) (range_split cell_5_78 cell_5_79)))) (range_split (range_split (range_split (range_split cell_5_80 cell_5_81) (range_split cell_5_82 cell_5_83)) (range_split (range_split cell_5_84 cell_5_85) (range_split cell_5_86 cell_5_87))) (range_split (range_split (range_split cell_5_88 cell_5_89) (range_split cell_5_90 cell_5_91)) (range_split (range_split cell_5_92 cell_5_93) (range_split cell_5_94 cell_5_95))))) (range_split (range_split (range_split (range_split (range_split cell_5_96 cell_5_97) (range_split cell_5_98 cell_5_99)) (range_split (range_split cell_5_100 cell_5_101) (range_split cell_5_102 cell_5_103))) (range_split (range_split (range_split cell_5_104 cell_5_105) (range_split cell_5_106 cell_5_107)) (range_split (range_split cell_5_108 cell_5_109) (range_split cell_5_110 cell_5_111)))) (range_split (range_split (range_split (range_split cell_5_112 cell_5_113) (range_split cell_5_114 cell_5_115)) (range_split (range_split cell_5_116 cell_5_117) (range_split cell_5_118 cell_5_119))) (range_split (range_split (range_split cell_5_120 cell_5_121) (range_split cell_5_122 cell_5_123)) (range_split (range_split cell_5_124 cell_5_125) (range_split cell_5_126 cell_5_127)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_0 : ∀ i, 0 ≤ i → i < 1 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_1 : ∀ i, 1 ≤ i → i < 2 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 1 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_2 : ∀ i, 2 ≤ i → i < 3 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 2 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_3 : ∀ i, 3 ≤ i → i < 4 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 3 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_4 : ∀ i, 4 ≤ i → i < 5 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_5 : ∀ i, 5 ≤ i → i < 6 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 5 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_6 : ∀ i, 6 ≤ i → i < 7 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 6 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_7 : ∀ i, 7 ≤ i → i < 8 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 7 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_8 : ∀ i, 8 ≤ i → i < 9 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_9 : ∀ i, 9 ≤ i → i < 10 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 9 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_10 : ∀ i, 10 ≤ i → i < 11 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 10 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_11 : ∀ i, 11 ≤ i → i < 12 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 11 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_12 : ∀ i, 12 ≤ i → i < 13 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_13 : ∀ i, 13 ≤ i → i < 14 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 13 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_14 : ∀ i, 14 ≤ i → i < 15 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 14 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_15 : ∀ i, 15 ≤ i → i < 16 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 15 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_16 : ∀ i, 16 ≤ i → i < 17 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_17 : ∀ i, 17 ≤ i → i < 18 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 17 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_18 : ∀ i, 18 ≤ i → i < 19 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 18 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_19 : ∀ i, 19 ≤ i → i < 20 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 19 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_20 : ∀ i, 20 ≤ i → i < 21 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_21 : ∀ i, 21 ≤ i → i < 22 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 21 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_22 : ∀ i, 22 ≤ i → i < 23 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 22 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_23 : ∀ i, 23 ≤ i → i < 24 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 23 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_24 : ∀ i, 24 ≤ i → i < 25 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_25 : ∀ i, 25 ≤ i → i < 26 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 25 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_26 : ∀ i, 26 ≤ i → i < 27 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 26 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_27 : ∀ i, 27 ≤ i → i < 28 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 27 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_28 : ∀ i, 28 ≤ i → i < 29 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_29 : ∀ i, 29 ≤ i → i < 30 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 29 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_30 : ∀ i, 30 ≤ i → i < 31 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 30 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_31 : ∀ i, 31 ≤ i → i < 32 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 31 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_32 : ∀ i, 32 ≤ i → i < 33 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_33 : ∀ i, 33 ≤ i → i < 34 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 33 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_34 : ∀ i, 34 ≤ i → i < 35 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 34 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_35 : ∀ i, 35 ≤ i → i < 36 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 35 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_36 : ∀ i, 36 ≤ i → i < 37 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_37 : ∀ i, 37 ≤ i → i < 38 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 37 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_38 : ∀ i, 38 ≤ i → i < 39 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 38 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_39 : ∀ i, 39 ≤ i → i < 40 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 39 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_40 : ∀ i, 40 ≤ i → i < 41 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_41 : ∀ i, 41 ≤ i → i < 42 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 41 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_42 : ∀ i, 42 ≤ i → i < 43 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 42 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_43 : ∀ i, 43 ≤ i → i < 44 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 43 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_44 : ∀ i, 44 ≤ i → i < 45 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_45 : ∀ i, 45 ≤ i → i < 46 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 45 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_46 : ∀ i, 46 ≤ i → i < 47 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 46 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_47 : ∀ i, 47 ≤ i → i < 48 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 47 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_48 : ∀ i, 48 ≤ i → i < 49 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_49 : ∀ i, 49 ≤ i → i < 50 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 49 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_50 : ∀ i, 50 ≤ i → i < 51 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 50 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_51 : ∀ i, 51 ≤ i → i < 52 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 51 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_52 : ∀ i, 52 ≤ i → i < 53 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_53 : ∀ i, 53 ≤ i → i < 54 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 53 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_54 : ∀ i, 54 ≤ i → i < 55 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 54 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_55 : ∀ i, 55 ≤ i → i < 56 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 55 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_56 : ∀ i, 56 ≤ i → i < 57 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_57 : ∀ i, 57 ≤ i → i < 58 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 57 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_58 : ∀ i, 58 ≤ i → i < 59 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 58 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_59 : ∀ i, 59 ≤ i → i < 60 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 59 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_60 : ∀ i, 60 ≤ i → i < 61 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_61 : ∀ i, 61 ≤ i → i < 62 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 61 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_62 : ∀ i, 62 ≤ i → i < 63 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 62 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_63 : ∀ i, 63 ≤ i → i < 64 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 63 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_64 : ∀ i, 64 ≤ i → i < 65 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_65 : ∀ i, 65 ≤ i → i < 66 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 65 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_66 : ∀ i, 66 ≤ i → i < 67 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 66 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_67 : ∀ i, 67 ≤ i → i < 68 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 67 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_68 : ∀ i, 68 ≤ i → i < 69 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_69 : ∀ i, 69 ≤ i → i < 70 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 69 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_70 : ∀ i, 70 ≤ i → i < 71 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 70 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_71 : ∀ i, 71 ≤ i → i < 72 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 71 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_72 : ∀ i, 72 ≤ i → i < 73 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_73 : ∀ i, 73 ≤ i → i < 74 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 73 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_74 : ∀ i, 74 ≤ i → i < 75 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 74 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_75 : ∀ i, 75 ≤ i → i < 76 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 75 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_76 : ∀ i, 76 ≤ i → i < 77 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_77 : ∀ i, 77 ≤ i → i < 78 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 77 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_78 : ∀ i, 78 ≤ i → i < 79 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 78 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_79 : ∀ i, 79 ≤ i → i < 80 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 79 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_80 : ∀ i, 80 ≤ i → i < 81 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_81 : ∀ i, 81 ≤ i → i < 82 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 81 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_82 : ∀ i, 82 ≤ i → i < 83 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 82 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_83 : ∀ i, 83 ≤ i → i < 84 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 83 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_84 : ∀ i, 84 ≤ i → i < 85 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_85 : ∀ i, 85 ≤ i → i < 86 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 85 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_86 : ∀ i, 86 ≤ i → i < 87 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 86 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_87 : ∀ i, 87 ≤ i → i < 88 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 87 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_88 : ∀ i, 88 ≤ i → i < 89 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_89 : ∀ i, 89 ≤ i → i < 90 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 89 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_90 : ∀ i, 90 ≤ i → i < 91 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 90 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_91 : ∀ i, 91 ≤ i → i < 92 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 91 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_92 : ∀ i, 92 ≤ i → i < 93 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_93 : ∀ i, 93 ≤ i → i < 94 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 93 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_94 : ∀ i, 94 ≤ i → i < 95 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 94 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_95 : ∀ i, 95 ≤ i → i < 96 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 95 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_96 : ∀ i, 96 ≤ i → i < 97 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_97 : ∀ i, 97 ≤ i → i < 98 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 97 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_98 : ∀ i, 98 ≤ i → i < 99 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 98 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_99 : ∀ i, 99 ≤ i → i < 100 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 99 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_100 : ∀ i, 100 ≤ i → i < 101 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_101 : ∀ i, 101 ≤ i → i < 102 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 101 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_102 : ∀ i, 102 ≤ i → i < 103 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 102 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_103 : ∀ i, 103 ≤ i → i < 104 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 103 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_104 : ∀ i, 104 ≤ i → i < 105 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_105 : ∀ i, 105 ≤ i → i < 106 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 105 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_106 : ∀ i, 106 ≤ i → i < 107 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 106 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_107 : ∀ i, 107 ≤ i → i < 108 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 107 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_108 : ∀ i, 108 ≤ i → i < 109 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_109 : ∀ i, 109 ≤ i → i < 110 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 109 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_110 : ∀ i, 110 ≤ i → i < 111 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 110 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_111 : ∀ i, 111 ≤ i → i < 112 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 111 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_112 : ∀ i, 112 ≤ i → i < 113 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_113 : ∀ i, 113 ≤ i → i < 114 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 113 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_114 : ∀ i, 114 ≤ i → i < 115 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 114 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_115 : ∀ i, 115 ≤ i → i < 116 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 115 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_116 : ∀ i, 116 ≤ i → i < 117 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_117 : ∀ i, 117 ≤ i → i < 118 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 117 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_118 : ∀ i, 118 ≤ i → i < 119 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 118 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_119 : ∀ i, 119 ≤ i → i < 120 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 119 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_120 : ∀ i, 120 ≤ i → i < 121 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_121 : ∀ i, 121 ≤ i → i < 122 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 121 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_122 : ∀ i, 122 ≤ i → i < 123 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 122 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_123 : ∀ i, 123 ≤ i → i < 124 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 123 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_124 : ∀ i, 124 ≤ i → i < 125 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_125 : ∀ i, 125 ≤ i → i < 126 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 125 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_126 : ∀ i, 126 ≤ i → i < 127 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 126 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_6_127 : ∀ i, 127 ≤ i → i < 128 → cellCheck 6 i = true :=
  span_ok (by decide +kernel : span (cellCheck 6) 1 127 = true)
private theorem lvl_6 : ∀ i, 0 ≤ i → i < 128 → cellCheck 6 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_6_0 cell_6_1) (range_split cell_6_2 cell_6_3)) (range_split (range_split cell_6_4 cell_6_5) (range_split cell_6_6 cell_6_7))) (range_split (range_split (range_split cell_6_8 cell_6_9) (range_split cell_6_10 cell_6_11)) (range_split (range_split cell_6_12 cell_6_13) (range_split cell_6_14 cell_6_15)))) (range_split (range_split (range_split (range_split cell_6_16 cell_6_17) (range_split cell_6_18 cell_6_19)) (range_split (range_split cell_6_20 cell_6_21) (range_split cell_6_22 cell_6_23))) (range_split (range_split (range_split cell_6_24 cell_6_25) (range_split cell_6_26 cell_6_27)) (range_split (range_split cell_6_28 cell_6_29) (range_split cell_6_30 cell_6_31))))) (range_split (range_split (range_split (range_split (range_split cell_6_32 cell_6_33) (range_split cell_6_34 cell_6_35)) (range_split (range_split cell_6_36 cell_6_37) (range_split cell_6_38 cell_6_39))) (range_split (range_split (range_split cell_6_40 cell_6_41) (range_split cell_6_42 cell_6_43)) (range_split (range_split cell_6_44 cell_6_45) (range_split cell_6_46 cell_6_47)))) (range_split (range_split (range_split (range_split cell_6_48 cell_6_49) (range_split cell_6_50 cell_6_51)) (range_split (range_split cell_6_52 cell_6_53) (range_split cell_6_54 cell_6_55))) (range_split (range_split (range_split cell_6_56 cell_6_57) (range_split cell_6_58 cell_6_59)) (range_split (range_split cell_6_60 cell_6_61) (range_split cell_6_62 cell_6_63)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_6_64 cell_6_65) (range_split cell_6_66 cell_6_67)) (range_split (range_split cell_6_68 cell_6_69) (range_split cell_6_70 cell_6_71))) (range_split (range_split (range_split cell_6_72 cell_6_73) (range_split cell_6_74 cell_6_75)) (range_split (range_split cell_6_76 cell_6_77) (range_split cell_6_78 cell_6_79)))) (range_split (range_split (range_split (range_split cell_6_80 cell_6_81) (range_split cell_6_82 cell_6_83)) (range_split (range_split cell_6_84 cell_6_85) (range_split cell_6_86 cell_6_87))) (range_split (range_split (range_split cell_6_88 cell_6_89) (range_split cell_6_90 cell_6_91)) (range_split (range_split cell_6_92 cell_6_93) (range_split cell_6_94 cell_6_95))))) (range_split (range_split (range_split (range_split (range_split cell_6_96 cell_6_97) (range_split cell_6_98 cell_6_99)) (range_split (range_split cell_6_100 cell_6_101) (range_split cell_6_102 cell_6_103))) (range_split (range_split (range_split cell_6_104 cell_6_105) (range_split cell_6_106 cell_6_107)) (range_split (range_split cell_6_108 cell_6_109) (range_split cell_6_110 cell_6_111)))) (range_split (range_split (range_split (range_split cell_6_112 cell_6_113) (range_split cell_6_114 cell_6_115)) (range_split (range_split cell_6_116 cell_6_117) (range_split cell_6_118 cell_6_119))) (range_split (range_split (range_split cell_6_120 cell_6_121) (range_split cell_6_122 cell_6_123)) (range_split (range_split cell_6_124 cell_6_125) (range_split cell_6_126 cell_6_127)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_0 : ∀ i, 0 ≤ i → i < 1 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_1 : ∀ i, 1 ≤ i → i < 2 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 1 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_2 : ∀ i, 2 ≤ i → i < 3 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 2 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_3 : ∀ i, 3 ≤ i → i < 4 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 3 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_4 : ∀ i, 4 ≤ i → i < 5 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_5 : ∀ i, 5 ≤ i → i < 6 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 5 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_6 : ∀ i, 6 ≤ i → i < 7 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 6 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_7 : ∀ i, 7 ≤ i → i < 8 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 7 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_8 : ∀ i, 8 ≤ i → i < 9 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_9 : ∀ i, 9 ≤ i → i < 10 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 9 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_10 : ∀ i, 10 ≤ i → i < 11 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 10 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_11 : ∀ i, 11 ≤ i → i < 12 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 11 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_12 : ∀ i, 12 ≤ i → i < 13 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_13 : ∀ i, 13 ≤ i → i < 14 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 13 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_14 : ∀ i, 14 ≤ i → i < 15 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 14 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_15 : ∀ i, 15 ≤ i → i < 16 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 15 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_16 : ∀ i, 16 ≤ i → i < 17 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_17 : ∀ i, 17 ≤ i → i < 18 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 17 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_18 : ∀ i, 18 ≤ i → i < 19 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 18 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_19 : ∀ i, 19 ≤ i → i < 20 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 19 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_20 : ∀ i, 20 ≤ i → i < 21 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_21 : ∀ i, 21 ≤ i → i < 22 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 21 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_22 : ∀ i, 22 ≤ i → i < 23 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 22 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_23 : ∀ i, 23 ≤ i → i < 24 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 23 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_24 : ∀ i, 24 ≤ i → i < 25 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_25 : ∀ i, 25 ≤ i → i < 26 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 25 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_26 : ∀ i, 26 ≤ i → i < 27 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 26 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_27 : ∀ i, 27 ≤ i → i < 28 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 27 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_28 : ∀ i, 28 ≤ i → i < 29 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_29 : ∀ i, 29 ≤ i → i < 30 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 29 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_30 : ∀ i, 30 ≤ i → i < 31 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 30 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_31 : ∀ i, 31 ≤ i → i < 32 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 31 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_32 : ∀ i, 32 ≤ i → i < 33 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_33 : ∀ i, 33 ≤ i → i < 34 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 33 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_34 : ∀ i, 34 ≤ i → i < 35 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 34 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_35 : ∀ i, 35 ≤ i → i < 36 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 35 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_36 : ∀ i, 36 ≤ i → i < 37 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_37 : ∀ i, 37 ≤ i → i < 38 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 37 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_38 : ∀ i, 38 ≤ i → i < 39 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 38 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_39 : ∀ i, 39 ≤ i → i < 40 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 39 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_40 : ∀ i, 40 ≤ i → i < 41 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_41 : ∀ i, 41 ≤ i → i < 42 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 41 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_42 : ∀ i, 42 ≤ i → i < 43 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 42 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_43 : ∀ i, 43 ≤ i → i < 44 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 43 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_44 : ∀ i, 44 ≤ i → i < 45 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_45 : ∀ i, 45 ≤ i → i < 46 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 45 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_46 : ∀ i, 46 ≤ i → i < 47 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 46 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_47 : ∀ i, 47 ≤ i → i < 48 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 47 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_48 : ∀ i, 48 ≤ i → i < 49 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_49 : ∀ i, 49 ≤ i → i < 50 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 49 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_50 : ∀ i, 50 ≤ i → i < 51 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 50 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_51 : ∀ i, 51 ≤ i → i < 52 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 51 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_52 : ∀ i, 52 ≤ i → i < 53 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_53 : ∀ i, 53 ≤ i → i < 54 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 53 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_54 : ∀ i, 54 ≤ i → i < 55 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 54 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_55 : ∀ i, 55 ≤ i → i < 56 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 55 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_56 : ∀ i, 56 ≤ i → i < 57 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_57 : ∀ i, 57 ≤ i → i < 58 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 57 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_58 : ∀ i, 58 ≤ i → i < 59 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 58 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_59 : ∀ i, 59 ≤ i → i < 60 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 59 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_60 : ∀ i, 60 ≤ i → i < 61 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_61 : ∀ i, 61 ≤ i → i < 62 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 61 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_62 : ∀ i, 62 ≤ i → i < 63 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 62 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_63 : ∀ i, 63 ≤ i → i < 64 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 63 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_64 : ∀ i, 64 ≤ i → i < 65 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_65 : ∀ i, 65 ≤ i → i < 66 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 65 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_66 : ∀ i, 66 ≤ i → i < 67 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 66 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_67 : ∀ i, 67 ≤ i → i < 68 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 67 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_68 : ∀ i, 68 ≤ i → i < 69 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_69 : ∀ i, 69 ≤ i → i < 70 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 69 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_70 : ∀ i, 70 ≤ i → i < 71 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 70 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_71 : ∀ i, 71 ≤ i → i < 72 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 71 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_72 : ∀ i, 72 ≤ i → i < 73 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_73 : ∀ i, 73 ≤ i → i < 74 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 73 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_74 : ∀ i, 74 ≤ i → i < 75 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 74 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_75 : ∀ i, 75 ≤ i → i < 76 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 75 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_76 : ∀ i, 76 ≤ i → i < 77 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_77 : ∀ i, 77 ≤ i → i < 78 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 77 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_78 : ∀ i, 78 ≤ i → i < 79 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 78 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_79 : ∀ i, 79 ≤ i → i < 80 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 79 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_80 : ∀ i, 80 ≤ i → i < 81 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_81 : ∀ i, 81 ≤ i → i < 82 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 81 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_82 : ∀ i, 82 ≤ i → i < 83 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 82 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_83 : ∀ i, 83 ≤ i → i < 84 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 83 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_84 : ∀ i, 84 ≤ i → i < 85 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_85 : ∀ i, 85 ≤ i → i < 86 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 85 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_86 : ∀ i, 86 ≤ i → i < 87 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 86 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_87 : ∀ i, 87 ≤ i → i < 88 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 87 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_88 : ∀ i, 88 ≤ i → i < 89 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_89 : ∀ i, 89 ≤ i → i < 90 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 89 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_90 : ∀ i, 90 ≤ i → i < 91 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 90 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_91 : ∀ i, 91 ≤ i → i < 92 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 91 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_92 : ∀ i, 92 ≤ i → i < 93 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_93 : ∀ i, 93 ≤ i → i < 94 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 93 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_94 : ∀ i, 94 ≤ i → i < 95 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 94 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_95 : ∀ i, 95 ≤ i → i < 96 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 95 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_96 : ∀ i, 96 ≤ i → i < 97 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_97 : ∀ i, 97 ≤ i → i < 98 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 97 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_98 : ∀ i, 98 ≤ i → i < 99 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 98 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_99 : ∀ i, 99 ≤ i → i < 100 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 99 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_100 : ∀ i, 100 ≤ i → i < 101 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_101 : ∀ i, 101 ≤ i → i < 102 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 101 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_102 : ∀ i, 102 ≤ i → i < 103 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 102 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_103 : ∀ i, 103 ≤ i → i < 104 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 103 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_104 : ∀ i, 104 ≤ i → i < 105 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_105 : ∀ i, 105 ≤ i → i < 106 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 105 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_106 : ∀ i, 106 ≤ i → i < 107 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 106 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_107 : ∀ i, 107 ≤ i → i < 108 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 107 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_108 : ∀ i, 108 ≤ i → i < 109 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_109 : ∀ i, 109 ≤ i → i < 110 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 109 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_110 : ∀ i, 110 ≤ i → i < 111 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 110 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_111 : ∀ i, 111 ≤ i → i < 112 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 111 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_112 : ∀ i, 112 ≤ i → i < 113 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_113 : ∀ i, 113 ≤ i → i < 114 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 113 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_114 : ∀ i, 114 ≤ i → i < 115 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 114 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_115 : ∀ i, 115 ≤ i → i < 116 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 115 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_116 : ∀ i, 116 ≤ i → i < 117 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_117 : ∀ i, 117 ≤ i → i < 118 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 117 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_118 : ∀ i, 118 ≤ i → i < 119 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 118 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_119 : ∀ i, 119 ≤ i → i < 120 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 119 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_120 : ∀ i, 120 ≤ i → i < 121 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_121 : ∀ i, 121 ≤ i → i < 122 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 121 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_122 : ∀ i, 122 ≤ i → i < 123 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 122 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_123 : ∀ i, 123 ≤ i → i < 124 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 123 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_124 : ∀ i, 124 ≤ i → i < 125 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_125 : ∀ i, 125 ≤ i → i < 126 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 125 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_126 : ∀ i, 126 ≤ i → i < 127 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 126 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_7_127 : ∀ i, 127 ≤ i → i < 128 → cellCheck 7 i = true :=
  span_ok (by decide +kernel : span (cellCheck 7) 1 127 = true)
private theorem lvl_7 : ∀ i, 0 ≤ i → i < 128 → cellCheck 7 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_7_0 cell_7_1) (range_split cell_7_2 cell_7_3)) (range_split (range_split cell_7_4 cell_7_5) (range_split cell_7_6 cell_7_7))) (range_split (range_split (range_split cell_7_8 cell_7_9) (range_split cell_7_10 cell_7_11)) (range_split (range_split cell_7_12 cell_7_13) (range_split cell_7_14 cell_7_15)))) (range_split (range_split (range_split (range_split cell_7_16 cell_7_17) (range_split cell_7_18 cell_7_19)) (range_split (range_split cell_7_20 cell_7_21) (range_split cell_7_22 cell_7_23))) (range_split (range_split (range_split cell_7_24 cell_7_25) (range_split cell_7_26 cell_7_27)) (range_split (range_split cell_7_28 cell_7_29) (range_split cell_7_30 cell_7_31))))) (range_split (range_split (range_split (range_split (range_split cell_7_32 cell_7_33) (range_split cell_7_34 cell_7_35)) (range_split (range_split cell_7_36 cell_7_37) (range_split cell_7_38 cell_7_39))) (range_split (range_split (range_split cell_7_40 cell_7_41) (range_split cell_7_42 cell_7_43)) (range_split (range_split cell_7_44 cell_7_45) (range_split cell_7_46 cell_7_47)))) (range_split (range_split (range_split (range_split cell_7_48 cell_7_49) (range_split cell_7_50 cell_7_51)) (range_split (range_split cell_7_52 cell_7_53) (range_split cell_7_54 cell_7_55))) (range_split (range_split (range_split cell_7_56 cell_7_57) (range_split cell_7_58 cell_7_59)) (range_split (range_split cell_7_60 cell_7_61) (range_split cell_7_62 cell_7_63)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_7_64 cell_7_65) (range_split cell_7_66 cell_7_67)) (range_split (range_split cell_7_68 cell_7_69) (range_split cell_7_70 cell_7_71))) (range_split (range_split (range_split cell_7_72 cell_7_73) (range_split cell_7_74 cell_7_75)) (range_split (range_split cell_7_76 cell_7_77) (range_split cell_7_78 cell_7_79)))) (range_split (range_split (range_split (range_split cell_7_80 cell_7_81) (range_split cell_7_82 cell_7_83)) (range_split (range_split cell_7_84 cell_7_85) (range_split cell_7_86 cell_7_87))) (range_split (range_split (range_split cell_7_88 cell_7_89) (range_split cell_7_90 cell_7_91)) (range_split (range_split cell_7_92 cell_7_93) (range_split cell_7_94 cell_7_95))))) (range_split (range_split (range_split (range_split (range_split cell_7_96 cell_7_97) (range_split cell_7_98 cell_7_99)) (range_split (range_split cell_7_100 cell_7_101) (range_split cell_7_102 cell_7_103))) (range_split (range_split (range_split cell_7_104 cell_7_105) (range_split cell_7_106 cell_7_107)) (range_split (range_split cell_7_108 cell_7_109) (range_split cell_7_110 cell_7_111)))) (range_split (range_split (range_split (range_split cell_7_112 cell_7_113) (range_split cell_7_114 cell_7_115)) (range_split (range_split cell_7_116 cell_7_117) (range_split cell_7_118 cell_7_119))) (range_split (range_split (range_split cell_7_120 cell_7_121) (range_split cell_7_122 cell_7_123)) (range_split (range_split cell_7_124 cell_7_125) (range_split cell_7_126 cell_7_127)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_0 : ∀ i, 0 ≤ i → i < 1 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_1 : ∀ i, 1 ≤ i → i < 2 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 1 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_2 : ∀ i, 2 ≤ i → i < 3 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 2 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_3 : ∀ i, 3 ≤ i → i < 4 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 3 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_4 : ∀ i, 4 ≤ i → i < 5 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 4 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_5 : ∀ i, 5 ≤ i → i < 6 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 5 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_6 : ∀ i, 6 ≤ i → i < 7 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 6 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_7 : ∀ i, 7 ≤ i → i < 8 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 7 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_8 : ∀ i, 8 ≤ i → i < 9 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_9 : ∀ i, 9 ≤ i → i < 10 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 9 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_10 : ∀ i, 10 ≤ i → i < 11 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 10 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_11 : ∀ i, 11 ≤ i → i < 12 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 11 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_12 : ∀ i, 12 ≤ i → i < 13 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_13 : ∀ i, 13 ≤ i → i < 14 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 13 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_14 : ∀ i, 14 ≤ i → i < 15 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 14 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_15 : ∀ i, 15 ≤ i → i < 16 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 15 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_16 : ∀ i, 16 ≤ i → i < 17 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_17 : ∀ i, 17 ≤ i → i < 18 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 17 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_18 : ∀ i, 18 ≤ i → i < 19 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 18 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_19 : ∀ i, 19 ≤ i → i < 20 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 19 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_20 : ∀ i, 20 ≤ i → i < 21 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 20 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_21 : ∀ i, 21 ≤ i → i < 22 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 21 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_22 : ∀ i, 22 ≤ i → i < 23 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 22 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_23 : ∀ i, 23 ≤ i → i < 24 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 23 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_24 : ∀ i, 24 ≤ i → i < 25 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_25 : ∀ i, 25 ≤ i → i < 26 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 25 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_26 : ∀ i, 26 ≤ i → i < 27 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 26 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_27 : ∀ i, 27 ≤ i → i < 28 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 27 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_28 : ∀ i, 28 ≤ i → i < 29 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 28 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_29 : ∀ i, 29 ≤ i → i < 30 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 29 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_30 : ∀ i, 30 ≤ i → i < 31 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 30 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_31 : ∀ i, 31 ≤ i → i < 32 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 31 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_32 : ∀ i, 32 ≤ i → i < 33 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_33 : ∀ i, 33 ≤ i → i < 34 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 33 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_34 : ∀ i, 34 ≤ i → i < 35 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 34 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_35 : ∀ i, 35 ≤ i → i < 36 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 35 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_36 : ∀ i, 36 ≤ i → i < 37 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_37 : ∀ i, 37 ≤ i → i < 38 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 37 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_38 : ∀ i, 38 ≤ i → i < 39 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 38 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_39 : ∀ i, 39 ≤ i → i < 40 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 39 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_40 : ∀ i, 40 ≤ i → i < 41 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_41 : ∀ i, 41 ≤ i → i < 42 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 41 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_42 : ∀ i, 42 ≤ i → i < 43 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 42 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_43 : ∀ i, 43 ≤ i → i < 44 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 43 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_44 : ∀ i, 44 ≤ i → i < 45 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 44 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_45 : ∀ i, 45 ≤ i → i < 46 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 45 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_46 : ∀ i, 46 ≤ i → i < 47 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 46 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_47 : ∀ i, 47 ≤ i → i < 48 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 47 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_48 : ∀ i, 48 ≤ i → i < 49 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_49 : ∀ i, 49 ≤ i → i < 50 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 49 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_50 : ∀ i, 50 ≤ i → i < 51 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 50 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_51 : ∀ i, 51 ≤ i → i < 52 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 51 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_52 : ∀ i, 52 ≤ i → i < 53 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 52 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_53 : ∀ i, 53 ≤ i → i < 54 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 53 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_54 : ∀ i, 54 ≤ i → i < 55 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 54 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_55 : ∀ i, 55 ≤ i → i < 56 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 55 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_56 : ∀ i, 56 ≤ i → i < 57 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_57 : ∀ i, 57 ≤ i → i < 58 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 57 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_58 : ∀ i, 58 ≤ i → i < 59 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 58 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_59 : ∀ i, 59 ≤ i → i < 60 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 59 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_60 : ∀ i, 60 ≤ i → i < 61 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_61 : ∀ i, 61 ≤ i → i < 62 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 61 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_62 : ∀ i, 62 ≤ i → i < 63 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 62 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_63 : ∀ i, 63 ≤ i → i < 64 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 63 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_64 : ∀ i, 64 ≤ i → i < 65 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_65 : ∀ i, 65 ≤ i → i < 66 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 65 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_66 : ∀ i, 66 ≤ i → i < 67 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 66 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_67 : ∀ i, 67 ≤ i → i < 68 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 67 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_68 : ∀ i, 68 ≤ i → i < 69 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 68 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_69 : ∀ i, 69 ≤ i → i < 70 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 69 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_70 : ∀ i, 70 ≤ i → i < 71 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 70 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_71 : ∀ i, 71 ≤ i → i < 72 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 71 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_72 : ∀ i, 72 ≤ i → i < 73 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_73 : ∀ i, 73 ≤ i → i < 74 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 73 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_74 : ∀ i, 74 ≤ i → i < 75 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 74 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_75 : ∀ i, 75 ≤ i → i < 76 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 75 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_76 : ∀ i, 76 ≤ i → i < 77 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 76 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_77 : ∀ i, 77 ≤ i → i < 78 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 77 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_78 : ∀ i, 78 ≤ i → i < 79 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 78 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_79 : ∀ i, 79 ≤ i → i < 80 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 79 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_80 : ∀ i, 80 ≤ i → i < 81 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_81 : ∀ i, 81 ≤ i → i < 82 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 81 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_82 : ∀ i, 82 ≤ i → i < 83 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 82 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_83 : ∀ i, 83 ≤ i → i < 84 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 83 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_84 : ∀ i, 84 ≤ i → i < 85 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_85 : ∀ i, 85 ≤ i → i < 86 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 85 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_86 : ∀ i, 86 ≤ i → i < 87 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 86 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_87 : ∀ i, 87 ≤ i → i < 88 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 87 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_88 : ∀ i, 88 ≤ i → i < 89 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_89 : ∀ i, 89 ≤ i → i < 90 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 89 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_90 : ∀ i, 90 ≤ i → i < 91 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 90 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_91 : ∀ i, 91 ≤ i → i < 92 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 91 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_92 : ∀ i, 92 ≤ i → i < 93 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 92 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_93 : ∀ i, 93 ≤ i → i < 94 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 93 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_94 : ∀ i, 94 ≤ i → i < 95 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 94 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_95 : ∀ i, 95 ≤ i → i < 96 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 95 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_96 : ∀ i, 96 ≤ i → i < 97 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_97 : ∀ i, 97 ≤ i → i < 98 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 97 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_98 : ∀ i, 98 ≤ i → i < 99 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 98 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_99 : ∀ i, 99 ≤ i → i < 100 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 99 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_100 : ∀ i, 100 ≤ i → i < 101 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 100 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_101 : ∀ i, 101 ≤ i → i < 102 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 101 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_102 : ∀ i, 102 ≤ i → i < 103 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 102 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_103 : ∀ i, 103 ≤ i → i < 104 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 103 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_104 : ∀ i, 104 ≤ i → i < 105 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_105 : ∀ i, 105 ≤ i → i < 106 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 105 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_106 : ∀ i, 106 ≤ i → i < 107 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 106 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_107 : ∀ i, 107 ≤ i → i < 108 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 107 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_108 : ∀ i, 108 ≤ i → i < 109 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 108 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_109 : ∀ i, 109 ≤ i → i < 110 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 109 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_110 : ∀ i, 110 ≤ i → i < 111 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 110 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_111 : ∀ i, 111 ≤ i → i < 112 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 111 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_112 : ∀ i, 112 ≤ i → i < 113 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_113 : ∀ i, 113 ≤ i → i < 114 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 113 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_114 : ∀ i, 114 ≤ i → i < 115 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 114 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_115 : ∀ i, 115 ≤ i → i < 116 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 115 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_116 : ∀ i, 116 ≤ i → i < 117 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 116 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_117 : ∀ i, 117 ≤ i → i < 118 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 117 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_118 : ∀ i, 118 ≤ i → i < 119 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 118 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_119 : ∀ i, 119 ≤ i → i < 120 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 119 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_120 : ∀ i, 120 ≤ i → i < 121 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_121 : ∀ i, 121 ≤ i → i < 122 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 121 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_122 : ∀ i, 122 ≤ i → i < 123 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 122 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_123 : ∀ i, 123 ≤ i → i < 124 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 123 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_124 : ∀ i, 124 ≤ i → i < 125 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 124 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_125 : ∀ i, 125 ≤ i → i < 126 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 125 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_126 : ∀ i, 126 ≤ i → i < 127 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 126 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem cell_8_127 : ∀ i, 127 ≤ i → i < 128 → cellCheck 8 i = true :=
  span_ok (by decide +kernel : span (cellCheck 8) 1 127 = true)
private theorem lvl_8 : ∀ i, 0 ≤ i → i < 128 → cellCheck 8 i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split cell_8_0 cell_8_1) (range_split cell_8_2 cell_8_3)) (range_split (range_split cell_8_4 cell_8_5) (range_split cell_8_6 cell_8_7))) (range_split (range_split (range_split cell_8_8 cell_8_9) (range_split cell_8_10 cell_8_11)) (range_split (range_split cell_8_12 cell_8_13) (range_split cell_8_14 cell_8_15)))) (range_split (range_split (range_split (range_split cell_8_16 cell_8_17) (range_split cell_8_18 cell_8_19)) (range_split (range_split cell_8_20 cell_8_21) (range_split cell_8_22 cell_8_23))) (range_split (range_split (range_split cell_8_24 cell_8_25) (range_split cell_8_26 cell_8_27)) (range_split (range_split cell_8_28 cell_8_29) (range_split cell_8_30 cell_8_31))))) (range_split (range_split (range_split (range_split (range_split cell_8_32 cell_8_33) (range_split cell_8_34 cell_8_35)) (range_split (range_split cell_8_36 cell_8_37) (range_split cell_8_38 cell_8_39))) (range_split (range_split (range_split cell_8_40 cell_8_41) (range_split cell_8_42 cell_8_43)) (range_split (range_split cell_8_44 cell_8_45) (range_split cell_8_46 cell_8_47)))) (range_split (range_split (range_split (range_split cell_8_48 cell_8_49) (range_split cell_8_50 cell_8_51)) (range_split (range_split cell_8_52 cell_8_53) (range_split cell_8_54 cell_8_55))) (range_split (range_split (range_split cell_8_56 cell_8_57) (range_split cell_8_58 cell_8_59)) (range_split (range_split cell_8_60 cell_8_61) (range_split cell_8_62 cell_8_63)))))) (range_split (range_split (range_split (range_split (range_split (range_split cell_8_64 cell_8_65) (range_split cell_8_66 cell_8_67)) (range_split (range_split cell_8_68 cell_8_69) (range_split cell_8_70 cell_8_71))) (range_split (range_split (range_split cell_8_72 cell_8_73) (range_split cell_8_74 cell_8_75)) (range_split (range_split cell_8_76 cell_8_77) (range_split cell_8_78 cell_8_79)))) (range_split (range_split (range_split (range_split cell_8_80 cell_8_81) (range_split cell_8_82 cell_8_83)) (range_split (range_split cell_8_84 cell_8_85) (range_split cell_8_86 cell_8_87))) (range_split (range_split (range_split cell_8_88 cell_8_89) (range_split cell_8_90 cell_8_91)) (range_split (range_split cell_8_92 cell_8_93) (range_split cell_8_94 cell_8_95))))) (range_split (range_split (range_split (range_split (range_split cell_8_96 cell_8_97) (range_split cell_8_98 cell_8_99)) (range_split (range_split cell_8_100 cell_8_101) (range_split cell_8_102 cell_8_103))) (range_split (range_split (range_split cell_8_104 cell_8_105) (range_split cell_8_106 cell_8_107)) (range_split (range_split cell_8_108 cell_8_109) (range_split cell_8_110 cell_8_111)))) (range_split (range_split (range_split (range_split cell_8_112 cell_8_113) (range_split cell_8_114 cell_8_115)) (range_split (range_split cell_8_116 cell_8_117) (range_split cell_8_118 cell_8_119))) (range_split (range_split (range_split cell_8_120 cell_8_121) (range_split cell_8_122 cell_8_123)) (range_split (range_split cell_8_124 cell_8_125) (range_split cell_8_126 cell_8_127)))))))

private theorem checkedCells (s : Nat) (hs : s ≤ 8) (i : Nat) (hi : i < 128) : cellCheck s i = true := by
  interval_cases s <;> first | exact lvl_0 i (Nat.zero_le i) hi | exact lvl_1 i (Nat.zero_le i) hi | exact lvl_2 i (Nat.zero_le i) hi | exact lvl_3 i (Nat.zero_le i) hi | exact lvl_4 i (Nat.zero_le i) hi | exact lvl_5 i (Nat.zero_le i) hi | exact lvl_6 i (Nat.zero_le i) hi | exact lvl_7 i (Nat.zero_le i) hi | exact lvl_8 i (Nat.zero_le i) hi

private theorem impossibleState : ∀ s ≤ 8, ∀ i < 128, ∀ ws ∈ (rowsOf s).getD i [], ¬ RunD truthMask goal s ws := by
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
        rw [hcov, Bool.true_and, Bool.not_eq_true']
        by_contra hb
        obtain ⟨i', hi', zs, hzs, hr⟩ := sym_run (by simpa using hb) h
        exact ih s (by omega) (by omega) i' hi' zs hzs hr
      have hn := nextD_complete hrun s rfl ws (List.Perm.refl _) _ good
      simp [blocked, hn] at hc

def rootCheck (s : Nat) (ws : List Nat) : Bool :=
  decide (s + 1 < ws.length) || !(coversP pairs s ws) || listed s ws

def inputSubsets : List (List Nat) := roots.sublists

def rootCheckAt (i : Nat) : Bool :=
  (List.range 9).all (fun s => rootCheck s (inputSubsets.getD i []))

private theorem subsetCount : inputSubsets.length = 256 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_0 : ∀ i, 0 ≤ i → i < 8 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_8 : ∀ i, 8 ≤ i → i < 16 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_16 : ∀ i, 16 ≤ i → i < 24 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_24 : ∀ i, 24 ≤ i → i < 32 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_32 : ∀ i, 32 ≤ i → i < 40 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_40 : ∀ i, 40 ≤ i → i < 48 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_48 : ∀ i, 48 ≤ i → i < 56 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_56 : ∀ i, 56 ≤ i → i < 64 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_64 : ∀ i, 64 ≤ i → i < 72 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_72 : ∀ i, 72 ≤ i → i < 80 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_80 : ∀ i, 80 ≤ i → i < 88 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_88 : ∀ i, 88 ≤ i → i < 96 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_96 : ∀ i, 96 ≤ i → i < 104 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_104 : ∀ i, 104 ≤ i → i < 112 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_112 : ∀ i, 112 ≤ i → i < 120 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_120 : ∀ i, 120 ≤ i → i < 128 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_128 : ∀ i, 128 ≤ i → i < 136 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_136 : ∀ i, 136 ≤ i → i < 144 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_144 : ∀ i, 144 ≤ i → i < 152 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_152 : ∀ i, 152 ≤ i → i < 160 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_160 : ∀ i, 160 ≤ i → i < 168 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_168 : ∀ i, 168 ≤ i → i < 176 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_176 : ∀ i, 176 ≤ i → i < 184 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_184 : ∀ i, 184 ≤ i → i < 192 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_192 : ∀ i, 192 ≤ i → i < 200 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_200 : ∀ i, 200 ≤ i → i < 208 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_208 : ∀ i, 208 ≤ i → i < 216 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_216 : ∀ i, 216 ≤ i → i < 224 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_224 : ∀ i, 224 ≤ i → i < 232 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_232 : ∀ i, 232 ≤ i → i < 240 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_240 : ∀ i, 240 ≤ i → i < 248 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_248 : ∀ i, 248 ≤ i → i < 256 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 248 = true)
private theorem checkedRoots : ∀ i, 0 ≤ i → i < 256 → rootCheckAt i = true :=
  (range_split (range_split (range_split (range_split (range_split rootBlock_0 rootBlock_8) (range_split rootBlock_16 rootBlock_24)) (range_split (range_split rootBlock_32 rootBlock_40) (range_split rootBlock_48 rootBlock_56))) (range_split (range_split (range_split rootBlock_64 rootBlock_72) (range_split rootBlock_80 rootBlock_88)) (range_split (range_split rootBlock_96 rootBlock_104) (range_split rootBlock_112 rootBlock_120)))) (range_split (range_split (range_split (range_split rootBlock_128 rootBlock_136) (range_split rootBlock_144 rootBlock_152)) (range_split (range_split rootBlock_160 rootBlock_168) (range_split rootBlock_176 rootBlock_184))) (range_split (range_split (range_split rootBlock_192 rootBlock_200) (range_split rootBlock_208 rootBlock_216)) (range_split (range_split rootBlock_224 rootBlock_232) (range_split rootBlock_240 rootBlock_248)))))

private theorem impossibleRoot {s : Nat} {ws : List Nat} (hs : s ≤ 8)
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
  obtain ⟨i', hi', zs, hzs, hr⟩ := sym_run hblocked hrun
  exact impossibleState s hs i' hi' zs hzs hr

private theorem rootsAgree : ∀ r : Fin 16,
    roots.map (·.testBit r.val) = PEqualNP.Represents.oneEach
      (Fin.ofNat 4 (r.val / 4)) (Fin.ofNat 4 (r.val % 4)) := by decide +kernel

private theorem domainRows : ∀ r : Fin 16, truthMask.testBit r.val = true := by decide +kernel
private theorem targetIndex : ∀ r : Fin 16, 4 * (r.val / 4) + (r.val % 4) = r.val := by decide

private theorem rulesOut (C : Circuit) (hfan : FanInTwo C) (hs : C.size ≤ 8)
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
  have hz : C.gates.length ≤ 8 := hs
  exact impossibleRoot (by omega) hsub (Run.perm hp' hrun)

end PEqualNP.Outside.L_meta_23965

theorem PEqualNP.Outside.L_meta_23965 : (∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin 4 => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % 4)) C → 9 ≤ C.size) := by
  intro C hfan hrep
  by_contra hlt
  have hs : C.size ≤ 8 := by omega
  have hf : (fun u v : Fin 4 => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % 4)) = (fun u v : Fin 4 => (25500 : ℕ).testBit (4 * u.val + v.val)) := by
    funext u v
    revert u v
    decide
  rw [hf] at hrep
  exact PEqualNP.Outside.L_meta_23965.rulesOut C hfan hs hrep

import PEqualNP.Defs
import PEqualNP.Library.LRAT.PromiseN

namespace PEqualNP.Outside.L_meta_21939

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def truthMask : Nat := 2 ^ 9 - 1

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

theorem truthMask_bit (i : Nat) : truthMask.testBit i = decide (i < 9) := by
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

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 9)
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

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 9)
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

def roots : List Nat := [56, 448, 73, 146, 292]
def target : Nat := 206
def goal : Nat := target &&& truthMask

def pairs : List (Nat × Nat) := [(5, 2), (8, 2), (0, 6), (4, 3), (8, 7), (0, 2), (4, 7), (0, 3), (4, 1), (8, 6), (5, 3), (0, 1), (0, 7), (4, 2), (8, 1), (8, 3), (4, 6), (5, 1)]

def key (ws : List Nat) : Nat := ws.sum % 64

theorem key_lt (ws : List Nat) : key ws < 64 := Nat.mod_lt _ (by decide)

def rowsOf : Nat → List (List (List Nat))
  | 2 => [[], [[9, 312], [56, 265], [73, 376], [120, 329], [201, 504], [248, 457]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[7, 201], [73, 135]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[308, 506], [310, 504], [312, 502], [316, 498], [376, 438]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
  | 3 => [[[45, 56, 219], [56, 63, 201], [56, 73, 191], [56, 319, 457], [63, 73, 184], [63, 73, 312], [73, 319, 504], [73, 383, 504]], [[9, 56, 256], [56, 64, 329], [56, 73, 320], [56, 192, 457], [56, 201, 448], [64, 73, 312], [73, 120, 256], [73, 128, 504], [73, 184, 448], [73, 192, 504], [73, 248, 448], [73, 312, 448], [73, 320, 376], [73, 376], [73, 376, 448], [128, 201, 504], [184, 201, 448], [201, 448, 504], [201, 504], [256, 457, 504], [312, 329, 448], [312, 448, 457]], [], [[73, 130, 504]], [[73, 195, 504]], [], [], [], [], [[45, 56, 292], [292, 365, 376], [292, 493, 504]], [[73, 201, 504]], [], [[7, 73, 316]], [], [[56, 292, 498]], [[73, 191, 455]], [[7, 73, 128], [73, 199, 448], [73, 320, 455], [73, 327, 448], [201, 448, 455]], [], [[54, 292, 504]], [[56, 210, 457], [73, 146, 376], [73, 312, 466], [120, 146, 457], [121, 146, 456], [146, 201, 504]], [], [], [], [], [[45, 292, 455], [56, 73, 151]], [], [], [], [[219, 457, 504]], [], [], [], [], [[288, 457, 504]], [], [[89, 146, 504]], [], [[56, 219, 466], [73, 292, 376], [73, 312, 484], [121, 292, 456], [201, 292, 504], [292, 457, 504]], [], [], [], [[56, 73, 360]], [[316, 438, 504]], [], [], [[56, 63, 310], [56, 191, 438]], [[16, 292, 506], [18, 292, 504], [32, 316, 466], [56, 256, 502], [56, 292, 466], [56, 310, 448], [56, 320, 438], [73, 365, 376], [128, 438, 504], [146, 292, 376], [146, 312, 484], [146, 316, 480], [146, 420, 504], [178, 316, 448], [184, 438, 448], [186, 308, 448], [292, 312, 466], [312, 438, 448]], [], [], [], [], [], [[7, 292, 457], [219, 455, 466]], [[73, 308, 504]], [], [], [], [[56, 73, 376], [56, 201, 504], [73, 312, 504]], [], [], [], [[73, 316, 504], [292, 455, 466]], [[56, 308, 466], [73, 381, 504], [146, 308, 504]], [[73, 316, 506]]]
  | 4 => [[[45, 56, 73, 146], [56, 63, 73, 128], [56, 63, 73, 256], [56, 73, 191], [56, 73, 191, 448], [56, 73, 255, 448], [56, 73, 319, 448], [56, 73, 365, 466], [56, 73, 383, 448], [56, 146, 292, 466], [56, 146, 438, 448], [56, 219, 365, 448], [146, 438, 448, 504]], [[56, 64, 73, 256], [56, 73, 128, 448], [56, 73, 192, 448], [56, 73, 256, 448], [56, 73, 320], [56, 73, 320, 448], [56, 128, 201, 448], [56, 201, 448], [56, 256, 329, 448], [56, 256, 448, 457], [56, 292, 365, 504], [73, 128, 184, 448], [73, 128, 448, 504], [73, 128, 504], [73, 184, 448], [73, 256, 312, 448], [73, 256, 448, 504], [73, 312, 448]], [], [[56, 73, 130, 448]], [[56, 73, 195, 448]], [[56, 73, 260, 448], [56, 73, 292, 480], [56, 105, 292, 448]], [[56, 73, 325, 448], [73, 292, 455, 466]], [], [[56, 63, 292, 365]], [[45, 56, 292], [45, 56, 292, 448], [56, 73, 144, 504], [56, 219, 292, 466], [56, 219, 438, 448], [56, 292, 320, 365], [56, 292, 365, 448], [56, 292, 448, 493], [56, 292, 457, 484], [56, 292, 466, 475], [73, 292, 484, 504], [292, 365, 448, 504]], [[56, 73, 201, 448], [56, 73, 329, 448], [56, 292, 438, 504], [73, 186, 448, 455]], [[56, 73, 146, 504]], [[73, 121, 146, 504], [73, 316, 448, 455]], [[56, 73, 146, 506], [56, 73, 186, 466]], [[32, 56, 292, 466], [56, 146, 292, 480], [56, 178, 292, 448]], [[56, 73, 316, 466], [73, 146, 316, 504], [146, 292, 455, 466], [146, 438, 448, 455]], [[73, 128, 448, 455], [73, 256, 448, 455]], [[56, 63, 292, 438], [56, 73, 144, 448], [73, 144, 448, 504]], [[45, 56, 73, 292], [54, 56, 292, 448], [56, 63, 73, 146], [56, 73, 146, 191], [56, 146, 438, 466], [56, 292, 438, 448], [56, 292, 448, 502], [56, 292, 466, 484], [63, 73, 146, 504], [73, 130, 448, 455], [146, 292, 484, 504], [292, 438, 448, 504]], [[8, 121, 146, 448], [56, 64, 146, 457], [56, 73, 146, 320], [56, 73, 146, 448], [56, 73, 210, 448], [56, 73, 256, 466], [56, 146, 201, 448], [73, 120, 146, 448], [73, 128, 146, 504], [73, 146, 184, 448], [73, 146, 312, 448], [73, 146, 448, 504]], [[56, 73, 219, 504], [73, 260, 448, 455]], [], [], [], [[292, 365, 448, 455]], [[56, 73, 288, 504]], [[7, 56, 73, 146], [73, 146, 455, 504]], [[45, 56, 146, 292], [45, 56, 292, 466], [56, 63, 73, 219], [56, 73, 146, 456], [56, 73, 154, 448], [56, 292, 365, 466], [56, 365, 438, 448]], [[56, 73, 219, 448], [56, 219, 448, 457], [73, 146, 457, 504], [73, 219, 448, 504]], [[56, 73, 292, 504], [56, 146, 219, 504], [56, 292, 457, 504]], [[73, 121, 292, 504]], [[56, 73, 292, 506]], [], [[56, 73, 288, 448], [63, 73, 146, 455], [73, 288, 448, 504], [73, 292, 316, 504], [292, 438, 448, 455]], [[7, 73, 146, 448], [73, 146, 448, 455]], [[16, 73, 146, 504], [56, 73, 146, 464], [56, 89, 146, 448]], [[9, 56, 63, 292], [56, 63, 73, 292], [56, 63, 146, 219], [56, 63, 292, 457], [56, 73, 191, 292], [56, 292, 438, 466], [56, 292, 466, 502], [63, 73, 292, 504]], [[8, 121, 292, 448], [9, 56, 292, 448], [56, 73, 146, 466], [56, 73, 256, 484], [56, 73, 292, 320], [56, 73, 292, 448], [56, 73, 356, 448], [56, 146, 219, 448], [56, 201, 292, 448], [56, 219, 448, 466], [56, 219, 466], [56, 292, 329, 448], [56, 292, 448, 457], [73, 120, 292, 448], [73, 128, 292, 504], [73, 184, 292, 448], [73, 292, 312, 448], [73, 292, 448, 504], [146, 219, 448, 504], [292, 448, 457, 504], [292, 457, 504]], [[56, 73, 365, 504], [56, 146, 292, 504], [56, 292, 466, 504]], [[56, 121, 292, 466], [121, 146, 292, 504]], [[56, 146, 292, 506], [56, 186, 292, 466], [56, 186, 438, 448], [56, 292, 466, 506]], [], [[56, 292, 316, 466], [56, 316, 438, 448], [146, 292, 316, 504]], [[73, 219, 448, 455]], [[7, 56, 73, 292], [73, 292, 455, 504]], [[18, 56, 63, 292], [56, 63, 73, 365], [56, 63, 146, 292], [56, 63, 292, 466], [56, 73, 292, 456], [56, 73, 300, 448], [56, 146, 191, 292], [63, 146, 292, 504]], [[16, 186, 292, 448], [18, 56, 292, 448], [32, 146, 316, 448], [56, 64, 292, 466], [56, 73, 219, 466], [56, 73, 320, 365], [56, 73, 365, 448], [56, 128, 292, 466], [56, 128, 438, 448], [56, 146, 256, 484], [56, 146, 292, 320], [56, 146, 292, 448], [56, 146, 420, 448], [56, 210, 292, 448], [56, 256, 292, 466], [56, 256, 438, 448], [56, 292, 402, 448], [56, 292, 448, 466], [56, 292, 466], [73, 292, 457, 504], [73, 365, 448, 504], [120, 146, 292, 448], [128, 146, 292, 504], [146, 184, 292, 448], [146, 292, 312, 448], [146, 292, 448, 504], [292, 448, 466, 504]], [], [], [], [], [[56, 73, 146, 480], [56, 73, 178, 448], [56, 73, 186, 504], [63, 73, 292, 455]], [[7, 73, 292, 448], [73, 146, 455, 466], [73, 292, 448, 455], [146, 219, 448, 455], [292, 448, 455, 457]], [[7, 56, 146, 292], [16, 73, 292, 504], [56, 73, 186, 506], [56, 73, 292, 464], [56, 73, 308, 448], [56, 73, 316, 504], [56, 292, 455, 466], [146, 292, 455, 504]], [[8, 56, 292, 466], [56, 146, 292, 456]], [[56, 73, 292, 466], [56, 146, 219, 466], [56, 292, 457, 466], [73, 146, 484, 504], [146, 292, 457, 504]], [[56, 146, 438, 504]], [[56, 73, 128, 504], [56, 73, 184, 448], [56, 73, 256, 504], [56, 73, 312, 448]], [[56, 63, 73, 186]], [[56, 73, 186, 448], [73, 186, 448, 504]], [[56, 63, 73, 316], [56, 73, 251, 448], [63, 146, 292, 455], [73, 121, 186, 448]], [[7, 146, 292, 448], [56, 73, 316, 448], [56, 316, 448, 457], [73, 316, 448, 504], [73, 316, 504], [73, 365, 448, 455], [146, 292, 448, 455], [292, 448, 455, 466], [292, 455, 466]], [[16, 56, 292, 466], [16, 146, 292, 504], [56, 73, 381, 448], [56, 146, 292, 464], [56, 146, 308, 448], [73, 121, 316, 448]], [[56, 63, 73, 191], [56, 63, 73, 319], [56, 63, 146, 438], [73, 186, 316, 448]]]
  | 5 => [[[56, 73, 146, 365, 448], [56, 73, 219, 292, 448], [56, 146, 292, 448, 466], [56, 146, 292, 466], [56, 146, 438, 448]], [[56, 73, 128, 448], [56, 73, 256, 448]], [], [], [], [[32, 56, 73, 292, 448]], [[73, 146, 292, 448, 455]], [], [], [[56, 73, 146, 292, 466], [56, 73, 146, 438, 448], [56, 73, 292, 448, 484], [56, 146, 219, 292, 448], [56, 292, 365, 448]], [], [[56, 73, 146, 448, 504], [56, 73, 146, 504]], [[56, 73, 121, 146, 448]], [[56, 73, 146, 186, 448]], [[32, 56, 146, 292, 448]], [[56, 73, 146, 316, 448]], [], [], [[56, 63, 73, 146], [56, 63, 73, 146, 448], [56, 73, 292, 365, 448], [56, 146, 292, 448, 484], [56, 292, 438, 448]], [[56, 64, 73, 146, 448], [56, 73, 128, 146, 448], [56, 73, 146, 256, 448], [56, 73, 146, 448], [73, 146, 448, 504]], [], [], [], [], [], [], [[56, 73, 146, 448, 455]], [[8, 56, 73, 146, 448], [56, 73, 292, 438, 448], [56, 146, 292, 365, 448]], [[56, 73, 146, 448, 457], [56, 73, 219, 448]], [[56, 73, 292, 448, 504], [56, 73, 292, 504]], [[56, 73, 121, 292, 448]], [[56, 73, 186, 292, 448]], [], [[56, 73, 292, 316, 448]], [[73, 146, 448, 455]], [[16, 56, 73, 146, 448]], [[56, 63, 73, 292], [56, 63, 73, 292, 448], [56, 146, 292, 438, 448]], [[56, 64, 73, 292, 448], [56, 73, 128, 292, 448], [56, 73, 146, 448, 466], [56, 73, 146, 466], [56, 73, 256, 292, 448], [56, 73, 292, 448], [56, 146, 219, 448], [56, 292, 448, 457], [73, 292, 448, 504]], [[56, 146, 292, 448, 504], [56, 146, 292, 504]], [[56, 121, 146, 292, 448]], [[56, 146, 186, 292, 448]], [], [[56, 146, 292, 316, 448]], [], [[56, 73, 292, 448, 455]], [[8, 56, 73, 292, 448], [56, 63, 146, 292], [56, 63, 146, 292, 448]], [[56, 64, 146, 292, 448], [56, 73, 146, 219, 448], [56, 73, 292, 448, 457], [56, 73, 365, 448], [56, 128, 146, 292, 448], [56, 146, 256, 292, 448], [56, 146, 292, 448], [56, 292, 448, 466], [56, 292, 466], [146, 292, 448, 504]], [[56, 73, 146, 292, 504]], [], [], [], [[32, 56, 73, 146, 448]], [[73, 292, 448, 455]], [[16, 56, 73, 292, 448], [56, 146, 292, 448, 455]], [[8, 56, 146, 292, 448], [56, 63, 73, 146, 292]], [[56, 73, 146, 292, 448], [56, 73, 146, 448, 484], [56, 73, 292, 448, 466], [56, 73, 292, 466], [56, 146, 292, 448, 457], [73, 146, 292, 448, 504]], [], [], [], [[56, 73, 186, 448]], [], [[56, 73, 316, 448], [146, 292, 448, 455]], [[16, 56, 146, 292, 448]], []]
  | 6 => [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[56, 73, 146, 448]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[56, 73, 292, 448]], [], [], [], [], [], [], [], [], [[56, 146, 292, 448]], [], [], [], [], [], [], [], [], [[56, 73, 146, 292, 448]], [], [], [], [], [], [], [], []]
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

private theorem lvl_0 : ∀ i, 0 ≤ i → i < 64 → cellCheck 0 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf]
private theorem lvl_1 : ∀ i, 0 ≤ i → i < 64 → cellCheck 1 i = true := by
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
private theorem lvl_2 : ∀ i, 0 ≤ i → i < 64 → cellCheck 2 i = true :=
  (range_split (range_split (range_split (range_split cell_2_0 cell_2_4) (range_split cell_2_8 cell_2_12)) (range_split (range_split cell_2_16 cell_2_20) (range_split cell_2_24 cell_2_28))) (range_split (range_split (range_split cell_2_32 cell_2_36) (range_split cell_2_40 cell_2_44)) (range_split (range_split cell_2_48 cell_2_52) (range_split cell_2_56 cell_2_60))))
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
private theorem lvl_3 : ∀ i, 0 ≤ i → i < 64 → cellCheck 3 i = true :=
  (range_split (range_split (range_split (range_split cell_3_0 cell_3_4) (range_split cell_3_8 cell_3_12)) (range_split (range_split cell_3_16 cell_3_20) (range_split cell_3_24 cell_3_28))) (range_split (range_split (range_split cell_3_32 cell_3_36) (range_split cell_3_40 cell_3_44)) (range_split (range_split cell_3_48 cell_3_52) (range_split cell_3_56 cell_3_60))))
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
private theorem lvl_4 : ∀ i, 0 ≤ i → i < 64 → cellCheck 4 i = true :=
  (range_split (range_split (range_split (range_split cell_4_0 cell_4_4) (range_split cell_4_8 cell_4_12)) (range_split (range_split cell_4_16 cell_4_20) (range_split cell_4_24 cell_4_28))) (range_split (range_split (range_split cell_4_32 cell_4_36) (range_split cell_4_40 cell_4_44)) (range_split (range_split cell_4_48 cell_4_52) (range_split cell_4_56 cell_4_60))))
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
private theorem lvl_5 : ∀ i, 0 ≤ i → i < 64 → cellCheck 5 i = true :=
  (range_split (range_split (range_split (range_split cell_5_0 cell_5_4) (range_split cell_5_8 cell_5_12)) (range_split (range_split cell_5_16 cell_5_20) (range_split cell_5_24 cell_5_28))) (range_split (range_split (range_split cell_5_32 cell_5_36) (range_split cell_5_40 cell_5_44)) (range_split (range_split cell_5_48 cell_5_52) (range_split cell_5_56 cell_5_60))))
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
private theorem lvl_6 : ∀ i, 0 ≤ i → i < 64 → cellCheck 6 i = true :=
  (range_split (range_split (range_split (range_split cell_6_0 cell_6_4) (range_split cell_6_8 cell_6_12)) (range_split (range_split cell_6_16 cell_6_20) (range_split cell_6_24 cell_6_28))) (range_split (range_split (range_split cell_6_32 cell_6_36) (range_split cell_6_40 cell_6_44)) (range_split (range_split cell_6_48 cell_6_52) (range_split cell_6_56 cell_6_60))))

private theorem checkedCells (s : Nat) (hs : s ≤ 6) (i : Nat) (hi : i < 64) : cellCheck s i = true := by
  interval_cases s <;> first | exact lvl_0 i (Nat.zero_le i) hi | exact lvl_1 i (Nat.zero_le i) hi | exact lvl_2 i (Nat.zero_le i) hi | exact lvl_3 i (Nat.zero_le i) hi | exact lvl_4 i (Nat.zero_le i) hi | exact lvl_5 i (Nat.zero_le i) hi | exact lvl_6 i (Nat.zero_le i) hi

private theorem impossibleState : ∀ s ≤ 6, ∀ i < 64, ∀ ws ∈ (rowsOf s).getD i [], ¬ RunD truthMask goal s ws := by
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
  (List.range 7).all (fun s => rootCheck s (inputSubsets.getD i []))

private theorem subsetCount : inputSubsets.length = 32 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_0 : ∀ i, 0 ≤ i → i < 32 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 32 0 = true)
private theorem checkedRoots : ∀ i, 0 ≤ i → i < 32 → rootCheckAt i = true :=
  rootBlock_0

private theorem impossibleRoot {s : Nat} {ws : List Nat} (hs : s ≤ 6)
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

def rootsFull : List Nat := [7, 56, 448, 73, 146, 292]
def roots2 : List Nat := [0, 56, 448, 73, 146, 292]
def skip : List Nat := [0]

theorem gvN_agree (w w' : List Nat) (g : Gate) (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) :
    gvN w g = gvN w' g := by
  have hand : ∀ l : List Nat, (∀ i ∈ l, w.getD i 0 = w'.getD i 0) →
      l.foldr (fun i acc => andD truthMask (w.getD i 0) acc) truthMask =
        l.foldr (fun i acc => andD truthMask (w'.getD i 0) acc) truthMask := by
    intro l hl
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, hl i List.mem_cons_self,
        ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))]
  have hor : ∀ l : List Nat, (∀ i ∈ l, w.getD i 0 = w'.getD i 0) →
      l.foldr (fun i acc => orD truthMask (w.getD i 0) acc) 0 =
        l.foldr (fun i acc => orD truthMask (w'.getD i 0) acc) 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, hl i List.mem_cons_self,
        ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))]
  unfold gvN
  cases hop : g.op
  case and => exact hand _ h
  case or => exact hor _ h
  case not =>
    rcases hgi : g.inputs with _ | ⟨i, l⟩
    · rfl
    · have := h i (by rw [hgi]; exact List.mem_cons_self)
      simp only [this]
  all_goals rfl

theorem execN_agree (S : List Nat) : ∀ (gs : List Gate) (w w' : List Nat), w.length = w'.length →
    (∀ i, i ∉ S → w.getD i 0 = w'.getD i 0) → (∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ S) →
    ∀ i, i ∉ S → (execN gs w).getD i 0 = (execN gs w').getD i 0 := by
  intro gs
  induction gs with
  | nil => intro w w' _ h _ i hi; exact h i hi
  | cons g gs ih =>
    intro w w' hl h hg i hi
    have e : gvN w g = gvN w' g :=
      gvN_agree w w' g (fun j hj => h j (hg g List.mem_cons_self j hj))
    have hstep : ∀ j, j ∉ S → (w ++ [gvN w g]).getD j 0 = (w' ++ [gvN w' g]).getD j 0 := by
      intro j hj
      have hj' := h j hj
      rw [e]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl] at hj' ⊢
      by_cases hlt : j < w'.length
      · simpa [hlt] using hj'
      · simp [hlt]
    exact ih (w ++ [gvN w g]) (w' ++ [gvN w' g]) (by simp [hl]) hstep
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) i hi

private theorem rootsAgree : ∀ r : Fin 9,
    rootsFull.map (·.testBit r.val) = PEqualNP.Represents.oneEach
      (Fin.ofNat 3 (r.val / 3)) (Fin.ofNat 3 (r.val % 3)) := by decide +kernel

private theorem domainRows : ∀ r : Fin 9, truthMask.testBit r.val = true := by decide +kernel
private theorem targetIndex : ∀ r : Fin 9, 3 * (r.val / 3) + (r.val % 3) = r.val := by decide

private theorem rulesOut (C : Circuit) (hfan : FanInTwo C) (hs : C.size ≤ 6)
    (hun : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ ({0} : Finset ℕ)) (hou : C.output ∉ ({0} : Finset ℕ))
    (hrep : PEqualNP.Represents.Represents
      (fun u v : Fin 3 => target.testBit (3 * u.val + v.val)) C) : False := by
  have hun' : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ skip :=
    fun g hg i hi h => hun g hg i hi (by simpa [skip] using h)
  have hou' : C.output ∉ skip := fun h => hou (by simpa [skip] using h)
  have hsup0 : ∀ v ∈ roots2, Avail truthMask roots2 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots2 hfan 0 roots2 roots2 rfl hsup0
  have hbase : ∀ i, i ∉ skip → rootsFull.getD i 0 = roots2.getD i 0 := by
    intro i hi
    by_cases h6 : i < 6
    · interval_cases i <;> first | rfl | exact absurd (by decide) hi
    · rw [List.getD_eq_default _ _ (by simp [rootsFull]; omega),
        List.getD_eq_default _ _ (by simp [roots2]; omega)]
  have hag : (execN C.gates rootsFull).getD C.output 0 = (execN C.gates roots2).getD C.output 0 :=
    execN_agree skip C.gates rootsFull roots2 (by decide) hbase hun' C.output hou'
  have hout : (execN C.gates rootsFull).getD C.output 0 &&& truthMask = target &&& truthMask := by
    apply Nat.eq_of_testBit_eq
    intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 9
    · rw [domainRows ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates rootsFull r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [rootsAgree ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates rootsFull).map (·.testBit r)).getD C.output false =
          ((execN C.gates rootsFull).getD C.output 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates rootsFull)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have hr5 : r / 3 < 3 := by omega
      have hcol : r % 3 < 3 := Nat.mod_lt _ (by decide)
      have hv := hrep (Fin.ofNat 3 (r / 3)) (Fin.ofNat 3 (r % 3))
      simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hr5, Nat.mod_eq_of_lt hcol] at hv
      rw [targetIndex ⟨r, hlt⟩] at hv
      exact h2.trans hv
    · have hd : truthMask.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h25 : truthMask < 2 ^ 9 := by decide
        exact lt_of_lt_of_le h25 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  rw [hag] at hout
  have hav_out : Avail truthMask bank ((execN C.gates roots2).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates roots2).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Or.inl (Or.inl (by simp))
  have hn : ¬ IsConst truthMask target := by unfold IsConst target truthMask; decide
  have hd : truthMask &&& truthMask = truthMask := by decide +kernel
  obtain ⟨v, hv, hve⟩ := (avail_of_eq hout hav_out).resolve_left hn
  have hprop : ∀ w ∈ [target &&& truthMask], w ≠ 0 ∧ w ≠ truthMask := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hn (Or.inl e), fun e => hn (Or.inr e)⟩
  have hsubb : ∀ w ∈ [target &&& truthMask], w ∈ bank.map (· &&& truthMask) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hsp, hnd, hnc, hrin, hrun⟩ :=
    reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsubb Run.done
  have hall : ∀ x ∈ roots2.map (· &&& truthMask), x = 0 ∨ x = truthMask ∨ x ∈ roots := by decide +kernel
  have hin : ∀ w ∈ ws, w ∈ roots := by
    intro w hw
    rcases hall w (hrin w hw) with h | h | h
    · exact absurd h (hnc w hw).1
    · exact absurd h (hnc w hw).2
    · exact h
  have hrnd : roots.Nodup := by decide
  let sub := roots.filter (fun x => decide (x ∈ ws))
  have hsub : sub.Sublist roots := List.filter_sublist
  have hp' : ws.Perm sub := by
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hrnd)).2 ?_
    intro x
    simp only [sub, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hin x hx, hx⟩, fun h => h.2⟩
  have hz : C.gates.length ≤ 6 := hs
  exact impossibleRoot (by omega) hsub (Run.perm hp' hrun)

end PEqualNP.Outside.L_meta_21939

theorem PEqualNP.Outside.L_meta_21939 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ ({0} : Finset ℕ)) ∧ C.output ∉ ({0} : Finset ℕ) ∧ PEqualNP.Represents.Represents (fun u v : Fin 3 => (206 : ℕ).testBit (3 * u.val + v.val)) C)) := by
  rintro ⟨C, hfan, hs, hun, hou, hrep⟩
  exact PEqualNP.Outside.L_meta_21939.rulesOut C hfan hs hun hou hrep

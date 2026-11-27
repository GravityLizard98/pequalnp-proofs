import PEqualNP.Defs
import PEqualNP.Library.LRAT.PromiseN

namespace PEqualNP.Outside.L_meta_25469

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def truthMask : Nat := 2 ^ 25 - 1

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

theorem truthMask_bit (i : Nat) : truthMask.testBit i = decide (i < 25) := by
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

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 25)
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

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 25)
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

def roots : List Nat := [31, 992, 31744, 1015808, 32505856, 1082401, 2164802, 4329604, 8659208, 17318416]
def target : Nat := 32435687
def goal : Nat := target &&& truthMask

def pairs : List (Nat × Nat) := [(12, 22), (20, 24), (9, 7), (16, 18), (20, 15), (3, 23), (9, 19), (12, 13), (16, 17), (9, 8), (4, 14), (4, 1), (3, 8), (20, 5), (12, 17), (3, 18), (9, 14), (12, 10), (16, 15), (3, 0), (20, 10), (4, 0), (4, 2), (16, 6), (12, 11), (20, 0), (3, 1), (12, 14), (3, 2), (9, 6), (4, 24), (9, 5), (20, 17), (12, 21), (16, 21), (3, 13), (20, 13), (9, 24), (4, 19), (16, 19), (16, 11), (20, 8), (20, 7), (20, 11), (9, 23), (12, 7), (9, 22), (20, 21), (20, 14), (12, 23), (9, 18), (4, 22), (20, 2), (16, 8), (20, 18), (12, 24), (4, 21), (9, 17), (3, 21), (16, 22), (4, 15), (3, 6), (3, 22), (16, 7), (20, 23), (9, 13), (12, 18), (3, 15), (16, 13), (16, 14), (3, 10), (3, 7), (12, 19), (16, 23), (12, 15), (12, 6), (3, 5), (9, 10), (12, 8), (4, 10), (12, 2), (20, 1), (9, 15), (20, 22), (12, 5), (20, 6), (9, 11), (9, 21), (16, 1), (4, 17), (3, 17), (4, 8), (9, 1), (9, 2), (16, 5), (20, 19), (12, 0), (16, 10), (3, 24), (12, 1), (16, 2), (3, 11), (4, 11), (9, 0), (16, 0), (16, 24)]

def key (ws : List Nat) : Nat := ws.sum % 245

theorem key_lt (ws : List Nat) : key ws < 245 := Nat.mod_lt _ (by decide)

set_option maxRecDepth 100000 in
def fast : Nat → List (List (List (List Nat)))
  | 4 => [[[], [], [], [], [[31744, 2065441, 6494662, 32641412]], [], [], [], [], [], [], [], [[1082431, 2165730, 17809936, 33530120]], [[31744, 2065441, 4329892, 32573506]], [], []], [[], [], [], [[31744, 2065441, 29224827, 32573762], [32000, 2065441, 29224827, 32573506]], [], [], [[31744, 2065441, 5214340, 32573762], [31744, 2065441, 5214596, 32573506], [32000, 2065441, 5214340, 32573506]], [], [], [], [], [], [], [], [], []], [[[31744, 2065441, 4329604, 32603458], [31744, 2065441, 4329860, 32603202], [31744, 2065697, 4329604, 32603202]], [], [], [], [], [], [], [], [], [[31744, 2065441, 4329860, 32708806]], [], [], [], [], [], []], [[], [], [], [], [[31744, 2065441, 4329860, 32709062]], [], [], [], [], [], [], [], [], [[767, 1082401, 2194498, 5214340]], [], []], [[], [], [], [], [[31744, 2065441, 32573762, 32641156]], [], [], [], [], [], [], [[31744, 2065441, 6263973, 32573762], [31744, 2065441, 6264229, 32573506], [32000, 2065441, 6263973, 32573506]], [], [[31744, 2065441, 4329956, 32573506]], [], [[31744, 2065441, 32573762, 32641412]]], [[], [], [], [[1023, 1082401, 2194498, 5214596], [1023, 1082657, 2194498, 5214340]], [], [], [], [], [], [], [], [], [], [], [], [[31744, 2065441, 32708806, 33114719]]], [[], [], [[31744, 2065441, 32573762, 32708806]], [], [], [], [], [], [], [], [], [], [], [[31744, 2065441, 4329604, 32573890], [31744, 2065441, 32573762, 32709062]], [], []], [[], [], [[575, 1082401, 2194498, 5214340]], [], [], [], [], [], [], [[32256, 2065441, 4330468, 32573506]], [], [], [], [], [], []], [[[31744, 980669, 2065441, 4329604]], [], [], [], [], [], [], [], [], [], [], [], [], [], [[31744, 2065441, 21648031, 32708806]], []], [[], [], [[31744, 2065441, 29224475, 32573506]], [], [], [], [[31744, 980925, 2065441, 4329860], [31744, 980925, 2065697, 4329604]], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[[31744, 2065441, 6494406, 32573762], [1082431, 2165730, 17809936, 33317656]], [], [], [], [[1082431, 2165730, 33317656, 33530120]], [], [[1083361, 2194498, 22008468, 33525892]], [], [], [[31744, 2065441, 5412005, 32573762], [31744, 2065441, 5412261, 32573506], [32000, 2065441, 5412005, 32573506]], [], [[31744, 2065441, 6494662, 32573762]], [[31744, 2065441, 4592004, 32573506]], [], [], [[1082431, 2194498, 6263973, 32776456]]], [[], [], [[31744, 2065441, 4329604, 32573762], [31744, 2065441, 4329860, 32573506]], [], [], [], [], [], [], [], [], [], [], [[31744, 2065441, 4329860, 32573762]], [[31744, 2065441, 6494406, 32641412], [31744, 2065441, 6494662, 32641156], [31744, 2065697, 6494406, 32641156], [32000, 2065441, 6494406, 32641156]], []], [[], [], [[31744, 2065441, 29224571, 32573506]], [], []]]
  | 5 => [[[], [[31, 1082401, 2195426, 10824682, 17809936], [992, 1082401, 2194498, 22008468, 33525892]], [[992, 1082431, 2164831, 9412872, 33047056]], [[1023, 1082401, 2164831, 9412872, 33047056]], [[31, 1082401, 17333776, 32573506, 32642020], [992, 32256, 2065441, 4329604, 32573506], [31744, 1082431, 3247203, 5214340, 32776456]], [[31744, 1082431, 2165730, 8659944, 33047056], [31744, 2065441, 4330468, 17809936, 32573506]], [[31744, 1015808, 1082401, 32573506, 32641412], [31744, 1015808, 1082657, 32573506, 32641156], [31744, 1016064, 1082401, 32573506, 32641156]], [[31, 1113121, 8659944, 10824010, 32641156]], [[992, 1082431, 17333776, 19483218, 32776456], [31744, 1015808, 1082401, 2165058, 32709062], [31744, 1015808, 1082401, 2165058, 33525892], [31744, 1015808, 1082657, 2164802, 33525892]], [[992, 1082401, 2164831, 26207000, 33530120]], [[31744, 980925, 2065441, 4329604, 17318431]], [[31, 992, 1113121, 32708806, 33182356], [31744, 2065441, 4329604, 17333791, 32573506]], [[31, 31744, 2065441, 4329604, 32573762], [31, 31744, 2065441, 4329860, 32573506], [31, 32000, 2065441, 4329604, 32573506]], [[31, 992, 1113121, 19483218, 33182356], [31, 1082401, 2165730, 17809936, 33530120], [31, 1082401, 2194498, 32776456, 33525892], [31, 1083361, 8682760, 21648020, 33047056], [288, 31744, 2065441, 4329604, 32573506]], [[31744, 1015808, 1113121, 4329604, 32573762], [31744, 1015808, 1113121, 4329860, 32573506], [31744, 1015808, 1113377, 4329604, 32573506], [31744, 1016064, 1113121, 4329604, 32573506]], []], [[[31744, 2065441, 4329604, 24895231, 32573506]], [[31744, 1015808, 1082401, 32573762, 32641412]], [[31, 31744, 1083361, 33114706, 33317656], [31744, 1015808, 1082401, 2194498, 32641412], [31744, 1015808, 1082401, 2194754, 32641156], [31744, 1015808, 1082657, 2194498, 32641156], [31744, 1016064, 1082401, 2194498, 32641156]], [[256, 31744, 2065441, 29224827, 32573506], [31744, 1016064, 2065441, 4329604, 32573506]], [[31, 1082401, 2165730, 17809936, 33547032], [31, 1082401, 2194498, 22008468, 33525892], [31744, 1015808, 1082401, 10553666, 32641156]], [[31, 1113121, 2194498, 5214340, 32776456]], [[31, 1082401, 2165730, 18859569, 32776456], [256, 31744, 2065441, 5214340, 32573506]], [[543, 31744, 2065441, 4329604, 32573506], [992, 1082431, 3247203, 17809936, 32776456]], [], [[31, 1082401, 2194498, 5214340, 33553695], [31, 1083361, 2194498, 5215204, 17318416]], [[31, 1083361, 2194498, 5214340, 33047056], [31744, 1015808, 1090849, 4329604, 32573506]], [], [], [], [[31744, 1016064, 2065697, 4329604, 32573506]], [[31744, 1015808, 1082401, 2164802, 32641476], [31744, 1015808, 1082721, 2164802, 32641156]]], [[[31, 1082401, 17333776, 29223963, 32776456], [256, 31744, 2065441, 4329604, 32603202]], [[31744, 1015808, 1082401, 32708806, 33114719], [31744, 1083361, 4329631, 6494406, 33047056]], [], [], [[31744, 1015808, 1082401, 32573506, 32709062], [31744, 1015808, 1082401, 32573762, 32708806], [31744, 1015808, 1082657, 32573506, 32708806], [31744, 1016064, 1082401, 32573506, 32708806]], [[31744, 1082401, 2164831, 33047056, 33530120]], [], [[31, 1082401, 2165730, 32641156, 33538576]], [], [], [[31, 31744, 5412005, 6495206, 17809936]], [], [], [], [], [[31744, 1015808, 1082401, 32573762, 32709062]]], [[[31, 31744, 1083361, 33182356, 33317656]], [[31, 31744, 2065441, 12988812, 32844106], [992, 31744, 1082431, 33114706, 33317656]], [], [], [[31744, 1015808, 3247203, 19483231, 32641156]], [], [[31744, 913019, 1015808, 1082401, 2164802]], [], [], [], [[31744, 2065441, 4330468, 18859569, 32573506]], [[992, 1082401, 2164831, 8682760, 26207000], [31744, 2065441, 4329604, 32574434, 32844106]], [], [[31, 736, 1082401, 2194498, 5214340], [31, 1113121, 8659208, 32642020, 32708806], [31, 1113121, 17318416, 24894487, 32641156]], [[31, 913275, 1113121, 8659944, 17318416], [1023, 1082401, 2164831, 17809936, 32776456], [31744, 1015808, 1113121, 2164802, 32641412], [31744, 1015808, 1113121, 2165058, 32641156], [31744, 1015808, 1113377, 2164802, 32641156], [31744, 1015808, 3247203, 18400831, 32641156], [31744, 1016064, 1113121, 2164802, 32641156]], [[288, 1082401, 2194498, 5214340, 32505856]]], [[], [[31744, 2065441, 4329604, 16236000, 32573506]], [[31744, 1016064, 1082401, 32641156, 32708806]], [[992, 1082401, 2194498, 13611404, 33525892], [31744, 1016064, 2065441, 2164802, 32641156]], [], [], [[31, 1113121, 8659944, 18415153, 32641156]], [], [[31744, 2065441, 2065697, 4329604, 32573506]], [[31, 1082401, 2165730, 26207000, 33538576]], [[31744, 1015808, 1082401, 2173250, 32641156], [31744, 1015808, 1090849, 2164802, 32641156]], [[256, 31744, 2065441, 6263973, 32573506]], [[31744, 913275, 1015808, 1082401, 2165058], [31744, 913275, 1015808, 1082657, 2164802]], [[31744, 1082401, 5214340, 17809951, 32573506], [31744, 2065441, 5412005, 17318431, 32573506]], [[31, 1083361, 8682760, 21648020, 32641156], [31744, 1016064, 2065697, 2164802, 32641156]], [[31, 31744, 1083361, 12988812, 33182356], [31, 1113121, 17318416, 32642020, 32911756], [992, 31744, 1082431, 33182356, 33317656]]], [[], [], [[31, 1113121, 8659944, 17318416, 32642020]], [[31, 992, 1082401, 2194498, 5214596], [31, 992, 1082657, 2194498, 5214340], [256, 1023, 1082401, 2194498, 5214340], [287, 992, 1082401, 2194498, 5214340]], [[31, 992, 1113121, 25977624, 32911756]], [[992, 1082401, 2164831, 26207000, 33047056]], [[31, 1082401, 2194498, 13611404, 33525892], [31, 1082401, 17333776, 32777192, 32911756], [31744, 2065441, 4329604, 17318431, 32573506]], [[31, 31744, 9741609, 10824682, 17809936]], [], [], [], [], [], [], [[31, 1082401, 17333776, 32642020, 32776456], [31, 1083361, 3248099, 9412872, 33047056], [543, 992, 1082401, 2194498, 5214340], [992, 31744, 2065441, 32708806, 33114706]], [[31, 1113121, 12989420, 17318416, 32777192], [31744, 1015808, 1082401, 2165186, 32641156]]], [[[31, 31744, 5412837, 9742313, 33047056], [31744, 1082431, 5214340, 21648020, 32776456]], [[31, 31744, 3248099, 5412837, 33047056], [31, 1113121, 8659944, 21648020, 33047056]], [[992, 31744, 1082431, 21648020, 33317656], [31744, 1015808, 3247203, 6494406, 32506112], [31744, 2065441, 6494406, 17318431, 32641156]], [[31, 1082401, 2165730, 32776456, 33538576]], [[31, 31744, 5412837, 12988812, 33047056], [31744, 1015808, 1082401, 19483231, 32708806]], [[31, 992, 1113121, 32911756, 33182356]], [[31, 1083361, 8659208, 33062416, 33114706]], [[31, 1083361, 8682760, 10824010, 33047056], [992, 1082401, 2164831, 9436424, 26207000]], [], [[31, 1082401, 2194498, 13611404, 32776456], [31744, 1082431, 4330468, 32776456, 33047056]], [[31, 1082401, 2165730, 22008468, 33538576]], [[31744, 1015808, 3247203, 5412005, 32506112], [31744, 1015808, 3247203, 5412261, 32505856]], [], [], [[992, 31744, 1082431, 12988812, 33182356]], []], [[], [[31, 31744, 2065441, 32708806, 33114706], [31, 1082401, 2165730, 17825296, 26207000], [31, 1113121, 3247203, 9412872, 32641156]], [[31, 544, 1082401, 2194498, 5214340], [992, 1082401, 2194498, 33047056, 33525892]], [], [[992, 31744, 1082431, 19483218, 33317656]], [], [[31744, 1015808, 3247459, 5412261, 32505856]], [], [[31, 1113121, 3275875, 9412872, 32641156], [31744, 32000, 2065441, 4329604, 32573506]], [], [[31744, 1083361, 5214340, 32573506, 33047056]], [[31, 1113121, 8659944, 17333776, 32641156]], [[31, 1113121, 9412872, 31389629, 32641156], [31744, 2065441, 17318431, 29224827, 32573506]], [[992, 1082401, 2164831, 17333776, 26207000], [31744, 2065441, 4330468, 17333776, 32573506]], [], [[31, 3115074, 4357252, 8659208, 17318896, 32539681], [31744, 1015808, 1082401, 2165218, 32641156], [31744, 2065441, 5214340, 17318431, 32573506]]], [[[31, 1082401, 2194498, 5215204, 13611404], [31744, 1016064, 4329604, 5412005, 32573506]], [], [], [[31, 1082401, 10824682, 17809936, 32776456], [31744, 1082431, 4330468, 12988812, 33047056]], [], [[31, 31744, 1083361, 6494406, 33182356], [31, 1082401, 2194498, 33047056, 33525892], [992, 1082431, 8659208, 33062416, 33114706], [992, 3115074, 4357252, 8659208, 17318431, 32539681]], [[992, 1082431, 8682760, 10824010, 33047056]], [[31, 1083361, 2165730, 9412872, 33047056], [992, 1082401, 2164831, 26207000, 33538576]], [[31, 992, 1113121, 32708806, 32911756], [31, 1082401, 2194498, 32911756, 33530120], [31744, 1082401, 2164831, 26207000, 33530120], [31744, 2065441, 4329604, 17809951, 32573506]], [[31744, 2065441, 4329604, 17318431, 32603202]], [], [[31, 31744, 1083361, 12988812, 33317656], [31, 1082401, 2194498, 32776456, 33534348]], [[31744, 1082431, 4329604, 33317656, 33530120]], [], [], [[992, 31744, 2065441, 21648020, 32708806]]], [[], [[31, 1082401, 2194498, 5214340, 32865610], [31, 1113121, 9764841, 17318416, 32641156], [31, 1114081, 3248099, 8659208, 33047056], [31744, 1082431, 4330468, 17333776, 32776456]], [[31744, 1015808, 1082401, 6494406, 32573762], [31744, 1015808, 1082401, 6494662, 32573506], [31744, 1015808, 1082657, 6494406, 32573506], [31744, 1016064, 1082401, 6494406, 32573506]], [], [[8, 1082401, 2194498, 5214340, 32776456], [31, 1082401, 2165730, 26207000, 32776456], [31744, 1016064, 4329604, 32472030, 32573506]], [[767, 31744, 1082401, 2164802, 5214340]], [[256, 31744, 980925, 2065441, 4329604]], [], [], [], [[992, 31744, 2065441, 32844106, 33114706]], [[992, 1082401, 2164831, 33047056, 33530120], [31744, 1016064, 1082401, 5412005, 32573506]], [[31744, 1082431, 3247203, 9412872, 32641156]], [[31, 31744, 1083361, 10824010, 33317656], [31744, 1015808, 1082401, 6494662, 32573762]], [], []], [[[31, 777975, 1082401, 2194498, 5214340]], [[992, 1082401, 2164831, 32776456, 33538576]], [[31, 31744, 2065441, 21648020, 32708806]], [[992, 31744, 1082431, 21648020, 32911756]], [], [], [], [[1023, 1082401, 2165730, 9412872, 33047056]], [[31, 1082401, 2194498, 8659944, 13611404], [31744, 1082431, 4330468, 8659944, 33047056]], [[31, 1113121, 9412872, 25977624, 32641156]], [[992, 31744, 1082431, 12988812, 33317656], [31744, 2065441, 4329604, 32573506, 33554175]], [[31, 1082401, 2194498, 5214340, 32776456], [1023, 31744, 1082401, 2164802, 5214596], [1023, 31744, 1082401, 2165058, 5214340], [1023, 32000, 1082401, 2164802, 5214340], [31744, 1016320, 1082401, 2165730, 32641156]], [], [[31, 31744, 2065441, 32844106, 33114706], [31, 1082401, 3248099, 17809936, 32776456]], [[992, 31744, 1082431, 32844106, 33317656], [31744, 1015808, 2164802, 32471774, 32641156]], [[992, 1082401, 2164831, 17825296, 26207000], [31744, 1016064, 1082401, 4329860, 32573506], [31744, 1016064, 1082657, 4329604, 32573506]]], [[[31744, 1016064, 1082401, 6494406, 32641156]], [[31744, 1015808, 1082431, 19483218, 32844106]], [[31, 31744, 3248099, 9742313, 33047056], [31, 1083361, 3247203, 9412872, 33047056]], [], [[31744, 1015808, 1082401, 29224571, 32573506], [31744, 2065441, 6263973, 17318431, 32573506]], [[31, 31744, 9742313, 12988812, 33047056], [31, 507375, 1083361, 2164802, 9412872], [31, 1082401, 2165730, 17809936, 32844778]], [], [[31, 1113121, 8659208, 33182356, 33525892]], [], [[992, 1113121, 8659208, 32641183, 32708806]], [[31, 31744, 2065441, 25977624, 32844106]], [], [[992, 31744, 1082431, 10824010, 33317656], [1023, 1082401, 2194498, 5214340, 17318431], [31744, 2065441, 4329604, 18859583, 32573506]], [[31, 1113121, 8659944, 18400817, 32641156]], [], [[31, 1113121, 8659944, 17318416, 32912364], [31744, 2065441, 4330468, 18400817, 32573506]]], [[], [], [[31, 1082401, 2194498, 5214340, 32776479], [31744, 1015808, 2164802, 3247203, 32641412], [31744, 1015808, 2164802, 3247459, 32641156], [31744, 1015808, 2165058, 3247203, 32641156], [31744, 1016064, 2164802, 3247203, 32641156], [31744, 1082401, 2164831, 9412872, 32708806]], [[31, 1083361, 8682760, 29224827, 33047056]], [[31744, 1015808, 2164802, 32472030, 32641412], [31744, 1015808, 2165058, 32472030, 32641156], [31744, 1016064, 2164802, 32472030, 32641156]], [], [[31, 1113121, 8659944, 17318416, 32641156], [31744, 1082401, 2165730, 33182356, 33525892], [31744, 1083361, 4329631, 32776456, 33047056]], [], [[31744, 1015808, 1082431, 32844106, 33317656]], [[31, 1082401, 2194498, 5214340, 32844106]], [[575, 31744, 1082401, 2164802, 5214340], [31744, 1015808, 1082401, 29224827, 32573762], [31744, 1015808, 1082657, 29224827, 32573506], [31744, 1016064, 1082401, 29224827, 32573506]], [[31, 31744, 1083361, 33114706, 33182356], [31, 777975, 1082401, 2165730, 17809936], [31, 1082401, 2194498, 5214340, 32800008], [31, 1082401, 17333776, 32776456, 32912364], [31744, 1015808, 1082401, 3247203, 32641412], [31744, 1015808, 1082401, 3247459, 32641156], [31744, 1015808, 1082657, 3247203, 32641156], [31744, 1016064, 1082401, 3247203, 32641156]], [[31, 992, 1113121, 25977624, 33182356], [992, 31744, 1082431, 32911756, 33317656]], [[480, 31744, 2065441, 4329604, 32573506], [31744, 1015808, 2165058, 3247459, 32641156], [31744, 1016064, 1082401, 5214340, 32573506]], [[31, 1113121, 3247203, 5214340, 32776456]], [[31, 1113121, 8659944, 16236015, 32641156]]], [[], [[31, 1082401, 2165730, 17809936, 33317656], [992, 1082431, 3247203, 9412872, 33047056], [31744, 2065441, 4330468, 16236015, 32573506]], [[31, 992, 1113121, 10824010, 32911756], [992, 1082401, 2164831, 26207000, 32776456]], [], [[31744, 1015808, 1082401, 2164802, 32641412], [31744, 1015808, 1082401, 2165058, 32641156], [31744, 1015808, 1082657, 2164802, 32641156], [31744, 1082431, 8659944, 12988812, 33047056]], [[31, 1082401, 2165730, 33317656, 33530120]], [[31, 1082401, 2165730, 17809936, 32776456], [31744, 1015808, 1082657, 3247459, 32641156], [31744, 1016064, 1082401, 31389629, 32641156]], [[31, 1082401, 2165730, 17809936, 32777192], [992, 31744, 2065441, 12988812, 32708806]], [[31744, 1016064, 1082401, 5214596, 32573506]], [[256, 31744, 2065441, 5412005, 32573506], [1023, 31744, 1082401, 2165058, 32641156]], [], [[992, 31744, 2065441, 32708806, 32844106], [31744, 1083361, 5214340, 19483218, 32573506]], [], [], [], [[31744, 1015808, 1082401, 2165058, 32641412], [31744, 1015808, 1082657, 2165058, 32641156]]], [[[31, 1082401, 2194498, 6263973, 32776456]], [[31, 1082401, 2165730, 32776456, 33547032], [31, 1082401, 8682760, 10824682, 17809936], [31, 1113121, 8659944, 17318416, 32641183], [31744, 777983, 1082401, 2164802, 5214340], [31744, 1082431, 4330468, 32776456, 33317656]], [[256, 31744, 2065441, 4329604, 32573506], [1023, 1082401, 2165730, 17809936, 32776456], [31744, 2065441, 4329604, 32573762], [31744, 2065441, 4329860, 32573506]], [], [], [[31744, 1082431, 4330468, 16236015, 32776456]], [[31, 1113121, 8683496, 17318416, 32641156], [31744, 1082431, 8659944, 10824010, 33047056]], [[31, 913275, 1113121, 2164802, 9412872]], [[31744, 1082401, 5214340, 21648031, 32573506]], [], [[31, 31744, 2065441, 12988812, 32708806], [31, 1082401, 10824682, 17809936, 32574434], [31, 1113121, 17318416, 32642020, 32708806]], [], [[31744, 2065441, 4330468, 12988812, 32573506]], [[31, 1083361, 3247203, 17809936, 32776456], [256, 31744, 2065441, 4329604, 32573762], [256, 31744, 2065441, 4329860, 32573506]], [[31, 31744, 2065441, 32708806, 32844106], [256, 31744, 2065441, 6494406, 32641156], [992, 31744, 2065441, 4329604, 32573762], [992, 31744, 2065441, 4329860, 32573506], [992, 32000, 2065441, 4329604, 32573506]], [[31, 1082401, 6495206, 17333776, 32642020], [31, 1083361, 8682760, 33047056, 33182356], [992, 1082401, 2194498, 32776456, 33525892]]], [[], [], [[31, 1082401, 2165730, 8682760, 26207000], [31744, 1015808, 1082401, 2164802, 32709062], [31744, 1015808, 1082401, 2165058, 32708806], [31744, 1015808, 1082657, 2164802, 32708806]], [[31, 1082401, 2165759, 17809936, 32776456]], [[31, 1082401, 2165730, 17809936, 32844106], [31, 1082431, 2165730, 17809936, 32776456], [31, 1083361, 8682760, 32641156, 33047056], [31744, 1015808, 1082401, 2165090, 32641156]]]]
  | 6 => [[[[31, 992, 1082401, 2194498, 5214340, 8659208], [31, 31744, 1082401, 9413608, 12989420, 17318416], [31, 31744, 1083361, 4329604, 25977624, 32776456], [31, 31744, 1083361, 12988812, 17318416, 32776456], [31, 1082401, 2165730, 8659208, 17809936, 32574434]], [[31, 31744, 2065441, 4329604, 10824010, 32776456], [31744, 1015808, 1082431, 2164802, 5412005, 32776456], [31744, 1015808, 1083361, 2164802, 21648020, 32641156]], [[31, 31744, 1015808, 3247203, 5412005, 32776456], [31, 31744, 1082401, 2165730, 5214340, 17809936], [31744, 1015808, 1082401, 2164802, 24895231, 32641156]], [[31, 992, 31744, 1082401, 25977624, 33182356], [31, 992, 1082401, 2164831, 9412872, 33047056], [31, 31744, 777975, 1082401, 2164802, 5214340]], [[31, 992, 1082401, 2164802, 9412872, 33114706], [31, 31744, 1015808, 18400817, 19483218, 32776456], [31, 31744, 4329604, 8659208, 17809936, 31388701], [992, 31744, 2065441, 6263973, 8659208, 32573506]], [[31, 1023, 1082401, 2164802, 9412872, 33047056], [31, 31744, 1082401, 3247203, 5214340, 32776456], [31, 31744, 1082401, 5214340, 8659944, 10824010], [992, 31744, 1082401, 2164831, 6494406, 17809936]], [[31, 31744, 1082401, 2165730, 5214340, 10824010], [31, 31744, 1082401, 2165730, 8659944, 33047056], [31, 31744, 1082401, 8659944, 16236015, 32641156], [31, 31744, 1082431, 4330468, 17318416, 32776456], [31, 1048575, 1082401, 2165730, 8659208, 17809936], [256, 31744, 1015808, 1082401, 32573506, 32641156], [992, 31744, 1082401, 5214340, 19483218, 32573506], [31744, 1015808, 1082401, 6494406, 17318431, 32573506]], [[31, 992, 31744, 3247203, 5214340, 18400817], [31, 31744, 1082401, 5214340, 21648020, 32573506], [992, 31744, 2065441, 4329604, 10462505, 32573506], [992, 1082401, 2164802, 4329631, 5214340, 17333776]], [[31, 31744, 1082401, 2165730, 6495206, 17809936], [31, 31744, 1082401, 4330468, 17318416, 32800008], [992, 31744, 2065441, 4329604, 17333776, 32573506]], [[31, 992, 31744, 1082401, 10824010, 32911756], [31, 992, 1082401, 17333776, 19483218, 32776456], [31, 992, 1113121, 3247203, 17318416, 32641156], [31, 31744, 1082401, 2165730, 6494406, 9412872], [31, 1082401, 2194498, 5214340, 8659208, 32573506], [543, 31744, 1015808, 1082401, 2164802, 32641156]], [[31, 31744, 1082401, 4330468, 9412872, 25977624], [31, 31744, 1083361, 4329604, 9741609, 33047056], [31, 31744, 1083361, 5412005, 8659208, 33047056], [31, 31744, 4330468, 9412872, 9741609, 17318416], [31, 1047552, 1113121, 2164802, 8659208, 32641156], [31, 1048575, 1113121, 2164802, 4329604, 9412872], [31744, 1015808, 1082401, 2164802, 4329604, 32537856], [31744, 1015808, 1082401, 2164802, 4329860, 32537600], [31744, 1015808, 1082657, 2164802, 4329604, 32537600]], [[31, 992, 1082401, 2164802, 26207000, 33530120], [31, 31744, 1082401, 2164802, 8659944, 13611404], [992, 31744, 4329631, 5412005, 8659208, 33047056], [31744, 1015808, 1082401, 2164802, 32642020, 32911756]], [[31, 256, 31744, 2065441, 4329604, 32573506], [31, 31744, 1082401, 2195426, 4329604, 17809936], [31, 1082401, 2164802, 4330468, 5215204, 17333776], [31, 1082401, 2165730, 2195426, 8659208, 17809936], [992, 1023, 1082401, 2194498, 5214340, 8659208]], [[31, 31744, 507375, 1083361, 4329604, 8659208], [31, 1047552, 1082401, 2164802, 17333776, 32641156], [31744, 1015808, 1082401, 2164802, 32641156, 33182367]], [[31, 31744, 1015808, 2165730, 18400817, 25977624], [31, 31744, 1082401, 2164802, 5214340, 32776456], [256, 31744, 1015808, 1113121, 4329604, 32573506], [992, 31744, 1082431, 4329604, 12988812, 33047056], [31744, 1015808, 1082401, 2165730, 16236015, 32641156]], [[31, 992, 31744, 5412005, 12988812, 33047056]]], [[[31, 992, 31744, 3247203, 5412005, 17809936], [31, 992, 31744, 5214340, 9741609, 10824010], [31, 992, 1113121, 3247203, 8659208, 33047056], [31, 992, 1113121, 3275875, 17318416, 32641156], [31, 31744, 1082401, 4330468, 32573506, 33047056], [31, 31744, 1082401, 5214340, 31389629, 32776456], [31, 1047552, 1082401, 2164802, 8659944, 17809936], [992, 31744, 1082431, 2165730, 8659208, 33047056]], [[31, 32736, 1082401, 2165730, 8659208, 33047056], [31, 1082401, 2165730, 8659208, 17809936, 33047056], [992, 31744, 1082431, 2164831, 8659208, 17809936]], [[31, 992, 1113121, 8659208, 10824010, 32641156], [31, 31744, 1083361, 10824010, 17318416, 32776456], [31, 1082401, 2164802, 5214340, 32776456, 32800008], [256, 31744, 1015808, 1082401, 2194498, 32641156], [31744, 1015808, 1082401, 2164802, 32641156, 32641412]], [[31, 31744, 1083361, 4329604, 8659208, 33047056]], [[31, 992, 1113121, 17318416, 31389629, 32641156], [31, 31744, 1082401, 9412872, 32641156, 32708806], [31, 31744, 1083361, 4329604, 8659944, 33047056], [31, 1082401, 2164802, 5214340, 8682760, 32641156], [992, 31744, 2065441, 4329604, 24895223, 32573506]], [[31, 31744, 1015808, 1082401, 32844106, 32911756], [31, 31744, 1083361, 3247203, 17318416, 32641156]], [[31, 992, 777975, 1082401, 2164802, 17809936]], [[31, 992, 1082401, 2194498, 5214340, 8659231], [31, 992, 1113121, 2194498, 5214340, 17318416], [31, 31744, 2065441, 6263973, 8659208, 32573506], [992, 1082401, 1082431, 2164802, 17809936, 32776456]], [[31, 992, 1082401, 2164802, 9412872, 33538576], [31, 992, 1082401, 3247203, 17809936, 32776456], [31, 31744, 1082401, 4330468, 25977624, 33047056], [31, 31744, 1082401, 8659944, 17318416, 32641183]], [[31, 31744, 1082401, 5214340, 19483218, 32573506]], [[31, 992, 1082401, 8682760, 33047056, 33182356], [31, 31744, 980925, 2065441, 4329604, 17318416], [31, 31744, 1082401, 2165730, 17809936, 25977624], [31, 31744, 2065441, 4329604, 10462505, 32573506]], [[31, 992, 1082401, 2164802, 10462505, 33047056], [31, 31744, 1082431, 8659944, 17318416, 32641156], [31, 31744, 2065441, 4329604, 17333776, 32573506]], [[31, 992, 1082401, 2164802, 17809936, 33317656], [31, 31744, 1083361, 3247203, 8659208, 33047056], [992, 31744, 1082401, 4329631, 25977624, 32776456], [992, 31744, 1082431, 4329604, 17333776, 32776456]], [[31, 31744, 1082401, 8683496, 17318416, 32641156], [31, 1082401, 2164802, 4330468, 17333776, 17809936]], [[31, 31744, 913275, 1082401, 2164802, 9412872]], [[31, 992, 1082401, 8682760, 32641156, 33047056], [31, 1023, 1082401, 2194498, 5214340, 8659208], [31, 31744, 507375, 1083361, 2164802, 8659208], [31, 31744, 1082401, 8659208, 17809936, 31388701], [31, 32736, 1083361, 4329604, 8659208, 33047056], [992, 31744, 1082401, 2164831, 9412872, 17809936], [992, 31744, 1082431, 4329604, 25977624, 32776456], [1023, 31744, 1082401, 2164802, 5214340, 17318431], [31744, 1015808, 1082401, 2164831, 32776456, 33047056]]], [[[31, 992, 1082401, 2194498, 5214340, 8682760], [31, 31744, 1082401, 5214340, 12989420, 17318416], [992, 31744, 1015808, 1082401, 32708806, 33114706], [31744, 1015808, 1082401, 2164802, 21648031, 32641156], [31744, 1015808, 1082431, 2164802, 32776456, 33047056]], [[31, 31744, 1082401, 17318416, 32642020, 32708806]], [[992, 31744, 1082401, 5214340, 32573506, 32776456]], [[31, 31744, 1015808, 1082401, 10824010, 32911756], [31, 31744, 1082401, 2165730, 17809936, 24895223], [31, 1048575, 2164802, 4330468, 8659208, 17333776]], [[31, 31744, 1082401, 4330468, 17318416, 32911756], [31, 32736, 1082401, 2194498, 4329604, 32776456], [256, 31744, 1015808, 1082401, 32573506, 32708806], [992, 31775, 1082401, 2194498, 4329604, 32776456]], [[31, 31744, 1082401, 2164802, 5214340, 32776479], [31, 31744, 1083361, 4329604, 6494406, 33047056], [31, 31744, 4330468, 5412837, 17318416, 32776456], [1023, 32736, 1082401, 2164802, 4329604, 17809936]], [[31, 992, 1082401, 2194498, 17809936, 21648020], [992, 31744, 2065441, 8659208, 18400817, 32573506]], [[31, 31744, 1083361, 8659208, 31389629, 33047056], [31, 31744, 2065441, 4329604, 24895223, 32573506]], [[31, 31744, 1015808, 8659944, 19483218, 21648020], [1023, 31744, 1082401, 2164802, 4329604, 17809951]], [[31, 992, 1082401, 2194498, 17318416, 22008468], [31, 31744, 1015808, 1082401, 6494406, 32844106], [31, 31744, 1082401, 2164802, 9412872, 32911756], [992, 31744, 1082401, 9412872, 17809936, 32573506], [992, 31744, 1082431, 5412005, 8659208, 33047056]], [[31, 992, 31744, 5412005, 9741609, 33047056], [31, 31744, 1082401, 4329604, 6495206, 17809936], [31744, 1015808, 1083361, 19483218, 21648020, 32505856]], [[8, 31744, 2065441, 8659208, 17318416, 32573506], [31, 31744, 5214340, 8659944, 17318416, 19483218], [31, 1047552, 1082401, 2164802, 4329604, 32800008]], [[31, 31744, 1015808, 9742313, 10824682, 17318416], [31, 31744, 1082401, 2164802, 5214340, 32844106], [31, 1082401, 2164802, 8659944, 8682760, 17809936], [992, 31744, 507375, 1082431, 4329604, 8659208]], [[31, 992, 31744, 1082401, 6494406, 32911756], [31, 992, 1082401, 8682760, 21648020, 33047056], [31, 31744, 1015808, 3248099, 10824682, 17318416], [31, 31775, 1082401, 2164802, 5214340, 32776456]], [[31, 31744, 1082401, 2164802, 5214340, 32800008], [31, 31744, 1082401, 9412872, 12988812, 32573506], [31, 31744, 1083361, 4329631, 8659208, 33047056]], [[992, 31744, 2065441, 4329604, 21648020, 32573506]]], [[[31, 31744, 1015808, 3247203, 6495206, 17318416], [31, 31744, 1082401, 2165730, 17809936, 32641156]], [[31, 31744, 1083391, 4329604, 8659208, 33047056], [31, 31744, 2065441, 4329604, 8659208, 32844106], [992, 31744, 1015808, 2164831, 21648020, 25977624]], [[31, 992, 31744, 1082401, 33114706, 33317656], [31, 31744, 1015808, 2165730, 18400817, 21648020], [31, 31775, 1083361, 4329604, 8659208, 33047056], [992, 31744, 1082431, 4329604, 8659208, 33047056]], [[31, 31744, 1015808, 1082401, 32708806, 33114706], [31, 31744, 1082401, 8659944, 10824010, 32641156], [31, 31744, 1083361, 4329604, 8682760, 33047056], [992, 31744, 1015808, 3247203, 19483218, 32641156], [992, 31744, 1082401, 4329631, 6494406, 9412872], [992, 31744, 1082431, 4329604, 8659944, 33047056], [31744, 1015808, 1082401, 2164802, 16236000, 32641156]], [[31, 31744, 5214340, 8659944, 10824682, 17318416], [31, 31744, 5214340, 10824010, 17318416, 32776456], [31, 32736, 1082401, 4329604, 8659944, 33047056], [31, 1082401, 2165730, 8659208, 17809936, 32573506]], [[31, 31744, 1082401, 5214340, 32573506, 32776456], [31, 32736, 1082401, 2165730, 4329604, 33047056], [1023, 31744, 1082401, 2165730, 4329604, 33047056]], [[31, 992, 31744, 5214340, 19483218, 25977624], [31744, 1015808, 2164802, 3247203, 17318431, 32641156]], [[31, 992, 31744, 1082401, 32708806, 33182356], [31, 992, 31744, 5412005, 6494406, 9412872], [31, 992, 1082401, 8682760, 10824010, 17809936], [31, 31744, 1082401, 2164802, 9413608, 13611404], [31, 1047552, 1082401, 2164802, 4330468, 17333776], [31744, 1015808, 1082401, 2165730, 17809936, 32641156]], [[992, 31744, 2065441, 8659208, 16236015, 32573506], [1023, 31775, 1082401, 2164802, 4329604, 17809936], [31744, 1015808, 2164802, 17318431, 32472030, 32641156]], [[31, 992, 31744, 1082401, 19483218, 33182356], [31, 992, 31744, 9412872, 19483218, 21648020], [31, 992, 1082401, 2164802, 5214340, 33538576], [31, 992, 1082401, 2194498, 5215204, 17318416], [31, 992, 1082401, 6494406, 17333776, 32641156], [31, 31744, 1083361, 8659208, 29224827, 33047056], [31, 31744, 2065441, 8659208, 18400817, 32573506], [31, 31744, 2065441, 9741609, 17318416, 32573506], [31, 1082401, 2165730, 8659208, 17333776, 17809936]], [[31, 992, 1082401, 2194498, 5214340, 33047056], [31, 31744, 1082401, 2164802, 5214340, 33530120], [31, 31744, 3115074, 4329604, 8659208, 17318896, 32539681], [31744, 32000, 1015808, 1082401, 4329604, 32573506]], [[31, 31744, 1015808, 2165730, 12988812, 25977624], [31, 31744, 1082401, 2165730, 17318416, 32777192], [992, 31744, 1082431, 3247203, 8659208, 33047056], [31744, 1015808, 1082401, 2165730, 10824010, 32641156]], [[31, 992, 31744, 3247203, 9741609, 33047056], [31, 31744, 1082401, 9412872, 17809936, 32573506], [31, 1082401, 2194498, 5214340, 8659208, 32603202], [992, 31744, 1015808, 3247203, 18400817, 32641156], [992, 31744, 1082401, 5214340, 12988812, 32573506]], [[31, 992, 1082401, 2164802, 8682760, 26207000], [31, 31744, 1082401, 8659944, 17809936, 21648020], [31, 31744, 4329604, 8659944, 17809936, 18400817]], [[31, 992, 1082401, 2164831, 17809936, 32776456], [31, 31744, 1082401, 2165730, 17809936, 21648020], [31, 1082401, 2164802, 4330468, 5214340, 8682760], [256, 31744, 1015808, 1113121, 2164802, 32641156], [992, 31744, 507375, 1082431, 2164802, 8659208], [31744, 1015808, 1082401, 17318431, 29224827, 32573506]], [[31, 31744, 1083361, 5412005, 17318416, 32776456], [31744, 1015808, 1082401, 3247203, 17318431, 32641156]]], [[[31, 31744, 1083361, 3247203, 4329604, 33047056], [31, 1082401, 2165730, 2194498, 8659208, 17809936], [992, 31744, 3115074, 4329604, 8659208, 17318431, 32539681]], [[31, 992, 1113121, 17318416, 25977624, 32641156], [31, 31744, 1082401, 2194498, 5214340, 32776456], [992, 31744, 1082401, 4329631, 6494406, 33047056]], [[31, 992, 1082401, 8682760, 32573506, 32641156], [31, 31744, 1082401, 4330468, 6494406, 32776456], [31, 31744, 2065441, 4329604, 21648020, 32573506]], [[31, 31744, 507375, 1083361, 2164802, 4329604], [31, 31744, 1015808, 8659944, 18400817, 19483218], [31, 31744, 1082401, 2164802, 6263973, 32776456], [31, 31744, 1082401, 4329604, 17809936, 31388701], [31, 31744, 2065441, 8659944, 17318416, 32573506], [31, 1082401, 2165730, 8659208, 17809936, 33538576], [992, 31744, 1082431, 4329604, 21648020, 32776456], [992, 31744, 1082431, 5412031, 8659208, 33047056]], [[31, 992, 31744, 5412005, 21648020, 32776456], [992, 31744, 1082401, 4329631, 17809936, 25977624], [992, 31744, 2065441, 8659208, 18400817, 32641156], [992, 31744, 4329631, 8659208, 17809936, 18400817]], [[31, 992, 1113121, 3247203, 17318416, 32776456], [31, 31744, 1083361, 17318416, 32573506, 32641156], [992, 31744, 1015808, 9741609, 10824010, 32641156]], [[31, 992, 31744, 3247203, 5214340, 10824010], [31, 31744, 1015808, 3247203, 19483218, 32641156], [31, 1082401, 2164802, 8659944, 17809936, 33047056], [992, 31744, 1082431, 8659208, 31389629, 33047056]], [[31, 992, 1082401, 8682760, 17333776, 32641156], [31, 31744, 1083361, 8659208, 33047056, 33114706], [31, 31744, 1113121, 4330468, 17318416, 32776456], [992, 31744, 1082401, 2164831, 6494406, 9412872]], [[31744, 1015808, 1082401, 2164802, 17318431, 32641156]], [[31, 992, 913275, 1113121, 8659208, 17318416]], [[31, 992, 1082401, 8682760, 25977624, 32641156], [31, 992, 1113121, 17318416, 24895223, 32641156], [31, 31744, 1082401, 2164802, 5214340, 32911756], [992, 31744, 1082401, 5214340, 17809936, 32573506], [992, 31744, 2065441, 4329604, 18400817, 32573506]], [[31, 31744, 1015808, 9741609, 10824682, 17318416], [31, 31744, 1083361, 4329604, 31389629, 33047056], [31, 31744, 2065441, 8659208, 16236015, 32573506], [31, 31744, 4330468, 9412872, 17318416, 31389629]], [[31, 31744, 1083361, 8659208, 32573506, 33047056], [31, 32736, 1082401, 2194498, 4329604, 17809936], [256, 31744, 913275, 1015808, 1082401, 2164802], [992, 31744, 1015808, 2164831, 18400817, 25977624], [992, 31775, 1082401, 2194498, 4329604, 17809936]], [[31, 992, 1082401, 2164802, 17809936, 33530120], [992, 31744, 1082431, 4329631, 8659208, 33047056]], [[31, 992, 1082401, 2194498, 8682760, 32641156], [31, 31744, 1082401, 4330468, 19483218, 33047056], [31, 31744, 1082401, 12989420, 17318416, 32641156], [992, 31744, 1082401, 5214340, 10824010, 32573506], [31744, 1015808, 1048319, 1082401, 2164802, 4329604]], [[8, 31744, 2065441, 4329604, 17318416, 32573506], [31, 992, 31744, 3247203, 5214340, 9741609], [31, 31744, 1015808, 3247203, 18400817, 32641156], [31, 31744, 1082401, 5214340, 12988812, 32573506], [31, 31744, 1083361, 4329604, 8659208, 33182356], [992, 31744, 980925, 2065441, 4329604, 8659208]]], [[[31, 992, 31744, 1082401, 33182356, 33317656], [31, 1082401, 2164802, 5214340, 8682760, 32776456]], [[31, 992, 1113121, 3247203, 8659208, 32641156], [31, 992, 1113121, 8659208, 18415153, 32641156], [31, 31744, 1083361, 3247203, 17318416, 32776456]], [[31, 992, 31744, 3247203, 5412005, 9412872], [31, 31744, 1082401, 2165730, 17809936, 26207000], [992, 31744, 1082431, 4329604, 8682760, 33047056]], [[31, 256, 992, 1082401, 2194498, 5214340], [31, 32736, 1082401, 4329604, 8682760, 33047056], [992, 31744, 2065441, 8659208, 12988812, 32573506]], [[31, 992, 31744, 9412872, 18400817, 19483218], [31, 992, 1082401, 2164802, 17809936, 33547032]], [], [[31, 31744, 1015808, 2165730, 9741609, 25977624], [992, 31744, 1015808, 18400817, 25977624, 32573506], [31744, 2065441, 4329604, 17318431, 32573506]], [[31, 31744, 1082401, 8659208, 10824682, 17809936], [31, 31744, 2065441, 8659208, 18400817, 32641156], [31, 31744, 2065441, 9741609, 17318416, 32641156], [992, 31744, 1082431, 3247231, 8659208, 33047056]], [[31, 992, 1113121, 3275875, 8659208, 32641156], [31, 31744, 1015808, 9741609, 10824010, 32641156], [31, 31744, 1082401, 2164802, 9412872, 33534348], [992, 31744, 1082401, 2164831, 17809936, 25977624], [992, 31744, 1082431, 8659208, 29224827, 33047056]], [[31, 31744, 1082401, 2165730, 10824682, 17809936], [992, 31744, 1082401, 2164802, 22008468, 33525892]], [[31, 31744, 1082401, 2165730, 4330468, 17809936]], [], [[31, 992, 1113121, 8659208, 31389629, 32641156], [31, 31744, 1082401, 2165730, 9412872, 25977624], [31, 31744, 1113121, 8659944, 17318416, 32641156], [992, 31744, 1015808, 1082401, 32844106, 33114706], [992, 31744, 2065441, 4329604, 16236015, 32573506]], [[31, 992, 1113121, 8659208, 17318416, 32642020], [31, 31744, 1082401, 5214340, 17809936, 32573506], [31, 31744, 1083361, 3247203, 8659208, 32641156], [31, 31744, 2065441, 4329604, 18400817, 32573506], [31, 31744, 2065441, 5412005, 17318416, 32573506]], [[31, 992, 1082401, 2164802, 9412872, 33317656]], [[31, 992, 31744, 5412005, 18400817, 32776456], [31, 992, 1113121, 2194498, 5214340, 8659208], [31, 31744, 1015808, 2165730, 12988812, 21648020], [31, 1082401, 2164802, 4330468, 9412872, 17333776], [992, 31744, 1082431, 3247203, 4329604, 33047056]]], [[[31, 992, 31744, 3247203, 5412005, 33047056], [31, 31744, 4329604, 9413608, 9742313, 17318416]], [[31, 992, 1082401, 17333776, 32776456, 32911756], [31, 31744, 1082401, 5214340, 10824010, 32573506], [31, 31744, 1082401, 5214340, 21648020, 32776456], [31, 31744, 1082401, 8659944, 32573506, 33047056], [31, 31744, 5214340, 5412005, 17318416, 32776456], [992, 31744, 1082401, 2164831, 17809936, 24895223], [992, 31744, 2065441, 8659208, 17809936, 32573506]], [[31, 992, 1082401, 2194498, 5214340, 17333776], [31, 31744, 980925, 2065441, 4329604, 8659208], [31, 1048575, 1082401, 2164802, 4330468, 17333776], [992, 31744, 2065441, 4329604, 17318431, 32573506], [31744, 1015808, 1082401, 2165058, 6494406, 32505856]], [[31, 992, 31744, 1082401, 21648020, 33317656], [31, 1082401, 2194498, 5214340, 8659208, 32776456], [992, 31744, 1015808, 1082401, 19483218, 32708806]], [[31, 31744, 1082401, 6494406, 9412872, 32573506], [31, 31744, 4329604, 5412837, 8659208, 33047056], [31744, 31775, 1082401, 2165730, 4329604, 17809936], [31744, 1015808, 1048575, 1082401, 2164802, 4329860], [31744, 1015808, 1048575, 1082657, 2164802, 4329604], [31744, 1015808, 1083361, 2164802, 9741609, 32641156]], [[31, 31744, 1083361, 8659208, 33047056, 33182356]], [[31, 31744, 1015808, 6494406, 10824682, 17318416], [31, 31744, 2065441, 4329604, 17318416, 32573506], [31, 31744, 2065441, 8659208, 12988812, 32573506], [992, 31744, 1082431, 8659208, 33047056, 33114706], [31744, 1015808, 1082401, 2164802, 17318431, 32708806]], [[1023, 32736, 1082401, 2164802, 4329604, 9412872]], [[31, 31744, 1082401, 2165730, 8659208, 26207000]], [[31, 992, 1082401, 2164802, 9436424, 26207000], [31, 31744, 1015808, 18400817, 25977624, 32573506], [31, 31744, 1082401, 8659208, 32642020, 32708806], [31, 31744, 1082401, 17318416, 24894487, 32641156]], [[31, 31744, 913275, 1082401, 8659944, 17318416], [31, 31744, 1082401, 4330468, 6494406, 17809936], [31, 31744, 1082401, 4330468, 32776456, 33047056], [31, 31744, 1083361, 8659208, 32641156, 33047056], [31, 1047552, 1113121, 2164802, 4329604, 32776456], [31744, 32000, 1015808, 1082401, 2164802, 32641156]], [[31, 31744, 1083361, 4329604, 33047056, 33114706], [31, 31744, 1083361, 5412837, 8659208, 33047056], [31, 1082401, 2165730, 8659208, 17809936, 17825296], [256, 31744, 1015808, 3247203, 5412005, 32505856], [992, 31744, 1082431, 8659208, 32573506, 33047056], [31744, 1015808, 1082401, 2165058, 5412005, 32505856]], [[31, 992, 1113121, 8659208, 21648020, 33047056], [31, 31744, 1082401, 2164802, 22008468, 33525892], [31, 31744, 1082401, 2165730, 17809936, 32776456], [992, 31744, 1082431, 4329604, 32776456, 33317656]], [[31, 1047552, 2164802, 4329604, 8659944, 17333776], [31744, 1015808, 1082401, 2165058, 6494662, 32505856]], [[31, 992, 1082401, 2164802, 13611404, 33530120], [31, 992, 1082401, 2194498, 5214340, 24895223], [31, 992, 1082401, 8682760, 21648020, 32641156], [31, 31744, 2065441, 9412872, 17318416, 32573506], [31, 1082401, 2164802, 8659944, 17333776, 17809936], [992, 31744, 1082431, 4329604, 8659208, 33182356]], [[31, 992, 31744, 1082401, 12988812, 33182356], [31, 31744, 1015808, 1082401, 32844106, 33114706], [31, 31744, 2065441, 4329604, 16236015, 32573506], [31744, 1015808, 1082401, 17318431, 32573506, 32641156]]], [[[31, 31744, 1082401, 17318416, 32641156, 32912364], [31, 31744, 1083361, 4329604, 32573506, 33047056], [992, 31744, 1082431, 4329604, 16236015, 32776456]], [[31, 31744, 1082401, 2164802, 5214340, 33553695], [31, 1082401, 1113121, 2164802, 9412872, 32641156]], [[31, 31744, 1114081, 4329604, 8659208, 33047056], [31, 31744, 2065441, 6494406, 17318416, 32641156]], [[31, 31744, 1016320, 1082401, 2165730, 4329604], [31, 31744, 1082401, 2165730, 17809936, 22008468], [31, 31744, 5214340, 8659944, 10824010, 17318416], [31, 1082401, 2164802, 4329604, 9436424, 32800008]], [[31, 992, 1082401, 10824010, 17809936, 32573506], [31, 31744, 2065441, 8659208, 17809936, 32573506], [31744, 1015808, 1082401, 2164802, 4329604, 32506112]], [[31, 992, 31744, 1082401, 19483218, 33317656], [31, 992, 31744, 5214340, 18400817, 19483218], [31, 31744, 2065441, 4329604, 17318431, 32573506], [31, 1047552, 2164802, 4330468, 8659208, 17809936]], [[31, 31744, 1015808, 1082401, 19483218, 32708806]], [[31, 992, 1113121, 17318416, 19483218, 32641156], [992, 31744, 2065441, 4329604, 12988812, 32573506], [992, 1047552, 1082401, 2164802, 17809936, 32641156], [31744, 1015808, 1113121, 4329604, 17318431, 32573506]], [[31, 31744, 1083361, 4329604, 25977624, 33047056], [31, 31744, 1083361, 8659208, 21648020, 33047056], [31, 32736, 1082401, 2164802, 5214340, 8682760]], [[31, 31744, 1082401, 2164802, 5214340, 33534348], [992, 31744, 1015808, 2164831, 12988812, 25977624]], [[31, 992, 1082401, 2194498, 9412872, 19483218], [992, 31744, 1082401, 2164802, 17809936, 33525892], [1023, 31775, 1082401, 2164802, 4329604, 9412872], [31744, 1015808, 1082401, 2164802, 17809951, 32641156]], [[31, 31744, 1082401, 17318416, 32642020, 32911756], [31, 32736, 1082401, 2164802, 4329604, 9436424], [992, 31744, 1015808, 3247203, 10824010, 32641156], [992, 1082401, 2164802, 9412872, 33047056, 33554400], [31744, 1015808, 1082401, 2194498, 17318431, 32641156]], [[31, 31744, 1015808, 1082401, 25977624, 32844106], [31, 31744, 1083361, 2194498, 4329604, 33047056], [992, 31744, 1082431, 3247203, 8659208, 32641156]], [], [[31, 992, 31744, 5214340, 10824010, 25977624], [31, 31744, 1082401, 8659944, 17318416, 32642020]], [[31, 992, 913275, 1113121, 2164802, 17318416], [31, 992, 1082401, 2164802, 17333776, 26207000], [31, 31744, 1082401, 2165730, 17318416, 32642020], [31, 31744, 1082401, 8659944, 32641156, 33047056], [31744, 1015808, 1082401, 2164802, 4329860, 32506112], [31744, 1015808, 1082401, 2165058, 4329860, 32505856]]], [[[31, 992, 31744, 1082401, 25977624, 32911756], [31, 992, 1082401, 2194498, 10824010, 17809936], [31, 1082401, 2164802, 4330468, 5214340, 17333776]], [[31, 31744, 1015808, 3247203, 10824682, 17318416], [31, 31744, 1083361, 4329604, 24895223, 33047056], [31, 31744, 1083361, 17318416, 32573506, 32776456]], [[31, 31744, 1015808, 3247203, 19483218, 32776456], [31, 31744, 1082401, 6494406, 9412872, 32641156]], [[31, 31744, 1082401, 2165730, 4329604, 17825296]], [[31, 992, 1082401, 17333776, 32573506, 32641156], [31, 31744, 1082401, 4330468, 12988812, 33047056], [31, 31744, 4330468, 5412005, 8659208, 33047056], [992, 31744, 1015808, 3247203, 9741609, 32641156], [992, 31744, 1082431, 8659208, 33047056, 33182356], [31744, 1015808, 1083361, 10824010, 19483218, 32505856]], [[31, 31744, 1082401, 4329604, 32777192, 32844106], [992, 31744, 2065441, 4329604, 17809936, 32573506]], [[31, 992, 1082401, 8659208, 33062416, 33114706], [31, 992, 1113121, 8659208, 17333776, 32641156], [992, 31744, 1082401, 4329631, 9412872, 25977624]], [[31, 992, 1082401, 8682760, 10824010, 33047056], [31744, 1015808, 1082401, 2165730, 32641156, 33047056]], [[31, 1082401, 2164802, 8659944, 9412872, 33047056]], [[31, 992, 1082401, 2164802, 26207000, 33538576], [31, 992, 1113121, 8659208, 25977624, 32641156], [992, 31744, 1082431, 8659208, 32641156, 33047056]], [[31, 31744, 1082401, 2164802, 26207000, 33530120], [31, 31744, 1083361, 8659208, 19483218, 33047056], [31, 31744, 2065441, 4329604, 12988812, 32573506], [31, 31744, 2065441, 10824010, 17318416, 32776456], [31, 1047552, 1082401, 2164802, 17809936, 32641156]], [[31, 31744, 1015808, 3247203, 18400817, 32776456], [31, 31744, 1082401, 12989420, 17318416, 32777192], [31, 31744, 1083361, 4329604, 8659208, 33317656], [31, 32736, 1082401, 2194498, 5214340, 8659208]], [[31, 992, 1082401, 17333776, 25977624, 32641156], [31, 31744, 1082401, 9412872, 32573506, 33047056], [31, 31744, 2065441, 17318416, 29224827, 32573506], [992, 31744, 1082401, 5214340, 9412872, 32573506]], [[31, 31744, 1082401, 2164802, 17809936, 33525892], [31, 31744, 1082401, 4329604, 33317656, 33530120], [31, 31744, 1082401, 8659944, 21648020, 33047056], [31744, 1015808, 1082401, 17318431, 32573506, 32708806]], [[31, 31744, 1015808, 3247203, 10824010, 32641156], [31, 32736, 1082401, 2194498, 4329604, 9412872], [31, 1082401, 2165730, 8659208, 17809936, 32776456], [992, 31775, 1082401, 2194498, 4329604, 9412872]], [[31, 31744, 2065441, 5214340, 17318416, 32573506], [31, 1082401, 2164802, 5214340, 8659944, 8682760]]], [[[31, 992, 1082401, 2194498, 17333776, 32641156], [31, 31744, 1083361, 2165730, 9412872, 17318416], [992, 31744, 1082401, 2164831, 17809936, 26207000]], [[31, 992, 31744, 1082401, 32911756, 33182356]], [[31, 31744, 1082401, 4330468, 17333776, 32776456], [31, 32736, 1113121, 4329604, 8659208, 33047056], [256, 31744, 1015808, 1082401, 6494406, 32573506], [767, 31744, 1015808, 1082401, 2164802, 4329604], [992, 31744, 2065441, 4329604, 9741609, 32573506], [992, 31744, 2065441, 5412005, 8659208, 32573506], [31744, 1015808, 1082401, 2164802, 4329604, 32573762], [31744, 1015808, 1082401, 2164802, 4329860, 32573506], [31744, 1015808, 1082657, 2164802, 4329604, 32573506]], [], [[31, 31744, 1083361, 4330468, 8659208, 33047056], [992, 31744, 1015808, 2164831, 9741609, 25977624], [992, 31744, 1082401, 4329631, 25977624, 33047056]], [[31, 736, 31744, 1082401, 2164802, 5214340], [31, 992, 3115074, 4357252, 8659208, 17318416, 32539681], [31, 31744, 1015808, 2165730, 9741609, 18400817], [31, 31744, 1082401, 4330468, 25977624, 32776456]], [[31, 992, 1082401, 2164802, 9412872, 33547032], [31, 31744, 1083361, 2165730, 8659208, 17809936], [992, 31744, 2065441, 8659208, 18859569, 32573506]], [[8, 31744, 2065441, 4329604, 8659208, 32573506], [31, 31744, 1015808, 3247203, 9741609, 32641156], [31, 31744, 1082401, 8659944, 10824010, 17809936], [288, 31744, 1082401, 2164802, 5214340, 32505856], [992, 31744, 1082431, 4329604, 25977624, 33047056], [992, 31744, 1082431, 8659208, 21648020, 33047056]], [[31, 31744, 1082401, 2165730, 10824010, 17809936], [31, 31744, 2065441, 4329604, 17809936, 32573506], [31744, 1015808, 1082431, 2164802, 32776456, 33317656]], [[31, 992, 1083361, 2194498, 5214340, 17318416], [31, 31744, 2065441, 4329604, 17318416, 32603202], [31744, 31775, 1082401, 2164802, 5214340, 32776456]], [[31, 31744, 1082401, 4330468, 17318416, 32912364], [992, 31744, 1082401, 2164831, 9412872, 25977624], [992, 31744, 1082401, 5214340, 32573506, 33047056], [1023, 31744, 1082401, 2164802, 4330468, 17809936], [31744, 1015808, 1082401, 2164802, 4329860, 33521664], [31744, 1015808, 1082401, 2165058, 29224827, 32505856]], [[31, 992, 1082401, 2194498, 5214340, 19483218], [992, 31744, 1082401, 2164802, 13611404, 33525892], [992, 31744, 2065441, 4329604, 8659208, 32573506]], [[31, 32736, 1082401, 2194498, 4329604, 33047056], [992, 31775, 1082401, 2194498, 4329604, 33047056], [31744, 1015808, 1082401, 2164802, 32641156, 33554175], [31744, 1015808, 1082431, 2164802, 16236015, 32776456]], [[31, 31744, 1082401, 3247203, 9412872, 32641156], [992, 31744, 1015808, 1082401, 32708806, 32844106], [992, 31744, 1015808, 2164831, 12988812, 21648020], [31744, 1015808, 1082401, 2165058, 5214340, 32505856]], [[31, 31744, 1015808, 2165730, 5412005, 21648020], [992, 31744, 1015808, 9741609, 25977624, 32573506]], [[31, 31744, 1082401, 5214340, 9412872, 32573506], [31, 31744, 1082401, 8659944, 19483218, 33047056], [31, 31744, 1083361, 17318416, 32641156, 32776456]]], [[[31, 31744, 1082401, 5214340, 8659944, 21648020], [31, 31744, 5214340, 5412005, 8659944, 17318416], [992, 31744, 1082431, 4329604, 24895223, 33047056]], [[31, 31744, 1082401, 2165730, 5214340, 21648020], [31, 31744, 1082401, 2165730, 9741609, 17809936], [31, 31744, 1082401, 5215204, 12989420, 17318416], [31, 1082401, 2164802, 9412872, 33047056, 33553439]], [[31, 992, 31744, 9741609, 10824010, 17809936], [31, 1082401, 2194498, 5214340, 8659208, 8659944]], [[31, 31744, 2065441, 10462505, 17318416, 32573506], [31, 1082401, 2165730, 2194498, 5214340, 8659208]], [[31, 992, 31744, 1082401, 21648020, 32911756], [31, 992, 1082401, 2194498, 5214340, 18400817]], [[31, 992, 31744, 1082401, 6494406, 33182356], [31, 31744, 2065441, 4329604, 9741609, 32573506], [31, 31744, 2065441, 5412005, 8659208, 32573506]], [[31, 31744, 1015808, 6494406, 8659944, 19483218], [31, 31744, 1015808, 10824682, 12989420, 17318416], [992, 31744, 1082401, 2164831, 8659208, 26207000]], [[31, 992, 1082401, 2165730, 9412872, 33047056], [31, 31744, 1015808, 6495206, 10824682, 17318416], [31, 31744, 1082401, 8659944, 17333776, 32641156], [992, 31744, 2065441, 6494406, 8659208, 32641156], [31744, 1015808, 1083361, 2164802, 32641156, 33047056], [31744, 1015808, 1113121, 2164802, 17318431, 32641156]], [[31, 31744, 1082401, 9412872, 31389629, 32641156], [1023, 31744, 1015808, 1082401, 2164802, 4329860], [1023, 31744, 1015808, 1082657, 2164802, 4329604], [1023, 31744, 1016064, 1082401, 2164802, 4329604], [31744, 1015808, 1083361, 6494406, 19483218, 32505856]], [[31, 31744, 1082401, 4330468, 8659944, 33047056], [31, 31744, 2065441, 8659208, 18859569, 32573506], [992, 31744, 1082431, 8659208, 19483218, 33047056]], [[31, 992, 1082401, 2164802, 22008468, 33538576], [31, 31744, 1082401, 2165730, 4330468, 33047056], [31, 31744, 1082401, 2165730, 8659208, 17809936], [992, 31744, 1015808, 18400817, 19483218, 32641156], [992, 31744, 1082431, 4329604, 8659208, 33317656]], [[31, 992, 31744, 1082401, 2164802, 5214596], [31, 992, 31744, 1082401, 2165058, 5214340], [31, 992, 31744, 1082401, 12988812, 33317656], [31, 992, 32000, 1082401, 2164802, 5214340], [31, 992, 1082401, 2194498, 5214340, 10845514], [31, 31744, 1082401, 2165730, 8659944, 17809936], [31, 1082401, 2194498, 5214340, 32776456], [256, 1023, 31744, 1082401, 2164802, 5214340], [287, 992, 31744, 1082401, 2164802, 5214340], [992, 31744, 1015808, 1082401, 10824010, 32708806]], [[31, 31744, 1082401, 4330468, 6494406, 9412872]], [[31, 992, 1082401, 2194498, 5214340, 17318416], [31, 992, 1082401, 17333776, 29224827, 32776456], [31, 31744, 1082401, 2165730, 4329604, 22008468], [31, 31744, 1082401, 5214340, 32573506, 33047056], [31, 31744, 1082401, 5214340, 32776456, 32844106], [992, 1047552, 1082401, 2164802, 8682760, 32641156]], [[31, 992, 1082401, 17318416, 32800008, 32844106], [31, 31744, 1082401, 2164802, 13611404, 33525892], [31, 31744, 1083361, 4329604, 19483218, 33047056], [31, 31744, 2065441, 4329604, 8659208, 32573506], [31, 31744, 4330468, 9412872, 17318416, 19483218]], [[31, 992, 31744, 1082401, 32844106, 33317656], [31, 31744, 1082401, 2164802, 4330468, 13611404], [31744, 1015808, 1082401, 2165730, 17333776, 32641156]]], [[[31, 992, 1082401, 2164802, 5214340, 33530120], [31, 992, 1082401, 2194498, 9412872, 12988812], [31, 31744, 1015808, 1082401, 32708806, 32844106], [31, 31744, 2065441, 17318416, 24895223, 32573506], [992, 31744, 1016064, 1082401, 4329604, 32573506], [31744, 1015808, 1082401, 2164802, 4329860, 32641156]], [[31, 992, 1082401, 2164802, 17825296, 26207000], [31, 31744, 1015808, 9741609, 25977624, 32573506], [31, 31744, 1083361, 2165730, 5214340, 17318416]], [[31, 31744, 1015808, 1082401, 19483218, 32844106], [31, 1082401, 1083361, 2164802, 9412872, 33047056], [31, 1082401, 2164802, 4329604, 8683496, 9436424], [992, 31744, 2065441, 4329604, 8659231, 32573506]], [[31, 992, 1082401, 2194498, 8659208, 13611404], [992, 31744, 1082431, 4330468, 8659208, 33047056]], [[31, 992, 31744, 1082401, 32708806, 32911756], [31, 992, 31744, 5214340, 10824010, 19483218], [31, 1047552, 1082401, 2164802, 4330468, 17809936], [31, 1082401, 2164802, 9412872, 9413608, 33047056], [31744, 1015808, 1082401, 2164802, 4329604, 32506176]], [[31, 31744, 4329604, 8659208, 9742313, 33047056], [31744, 913275, 1015808, 1082401, 2164802, 17318431]], [[31, 992, 32256, 1082401, 2164802, 5214340], [31, 992, 1082401, 2194498, 5214340, 16236015], [31, 32736, 1082401, 2165730, 8659208, 17809936], [543, 992, 31744, 1082401, 2164802, 5214340], [31744, 1015808, 1082431, 10824010, 19483218, 32505856]], [[31, 992, 1082401, 2194498, 5214340, 32776456], [31, 31744, 1082401, 9412872, 25977624, 32573506], [31, 31744, 2065441, 4329604, 18400817, 32776456], [31, 31744, 2065441, 5412005, 17318416, 32776456]], [], [[31, 31744, 1015808, 2165730, 5412005, 18400817], [31, 31744, 1083361, 8659208, 21648020, 32641156], [31, 31744, 1083361, 12988812, 17318416, 32641156], [31, 31744, 4330468, 5412005, 17318416, 32776456], [31, 32736, 1082401, 2194498, 8659208, 32641156], [992, 1047552, 1082401, 2164802, 9412872, 32641156]], [[31, 31744, 1082401, 4330468, 6494406, 33047056], [31, 31744, 1083361, 2165730, 4329604, 17809936], [31, 31744, 2065441, 6494406, 8659208, 32641156], [992, 31744, 2065441, 4329604, 18859569, 32573506], [992, 1082401, 2164802, 4329631, 5214340, 8682760]], [[31, 31744, 1082401, 5214340, 10824010, 32776456], [31, 31744, 1082401, 8659944, 32641156, 33182356], [31, 1082401, 2194498, 5214340, 8659208, 33553439], [992, 31744, 1016320, 1082401, 4329604, 32573506], [992, 31744, 2065441, 4329604, 8682760, 32573506], [31744, 1015808, 1082401, 2164802, 4329860, 32641412]], [[31, 992, 1082401, 2194498, 5214340, 17318431], [31, 992, 1113121, 9764137, 17318416, 32641156], [31, 31744, 1082401, 2165730, 6494406, 17809936], [992, 31744, 1082401, 2164802, 9412872, 33525892]], [[31, 992, 31744, 1082401, 10824010, 33317656], [31, 31744, 1015808, 18400817, 19483218, 32641156], [31, 31744, 1082401, 4330468, 17809936, 25977624], [31, 31744, 1083361, 3247203, 4329604, 32776456], [31, 31744, 1083361, 3248099, 8659208, 33047056], [31, 31744, 1083361, 4329604, 8659208, 33062416], [31, 31744, 4330468, 8659208, 17809936, 18400817], [31, 31744, 5214340, 8659944, 17318416, 31389629]], [[31, 31744, 1015808, 1082401, 10824010, 32708806], [992, 31744, 1082401, 4329631, 6494406, 32776456]], [[480, 31744, 1015808, 1082401, 2164802, 32641156]]], [[[31, 31744, 1083361, 8659208, 12988812, 33047056], [31, 1047552, 1082401, 2164802, 8682760, 32641156]], [[31, 31744, 1015808, 3247203, 8659944, 19483218], [31, 31744, 1082401, 5214340, 17318416, 32911756], [992, 31744, 2065441, 8659208, 29224827, 32573506]], [[31, 992, 1082401, 17333776, 19483218, 32641156], [256, 31744, 1015808, 2164802, 3247203, 32641156]], [[31, 31744, 1016064, 1082401, 4329604, 32573506], [31744, 1015808, 1082401, 2165730, 32641156, 33182356], [31744, 1015808, 1082401, 2165730, 32776456, 33047056]], [[31, 31744, 2065441, 6263973, 17318416, 32573506], [256, 31744, 1015808, 2164802, 32472030, 32641156], [992, 31744, 2065441, 5214340, 8659208, 32573506]], [[31, 31744, 1082401, 2165730, 5412005, 17809936], [31, 31744, 1083361, 4329604, 33047056, 33317656], [31, 31744, 2065441, 4329604, 8659231, 32573506], [31744, 1015808, 1082431, 2164802, 17809936, 32776456]], [[31, 1047552, 1082401, 2164802, 17809936, 32776456], [31, 1113121, 8659944, 17318416, 32641156]], [[31, 992, 913275, 1113121, 2164802, 8659208], [31, 31744, 1082401, 2165759, 8659208, 17809936], [31, 1082401, 2164802, 4330468, 17333776, 17825296], [575, 31744, 1015808, 1082401, 2164802, 4329604], [992, 31744, 2065441, 4329604, 9412872, 32573506]], [[31, 992, 1082401, 8682760, 10824010, 32641156], [31, 992, 1113121, 8659208, 18400817, 32641156], [31, 992, 1113121, 9741609, 17318416, 32641156], [31, 31744, 1082431, 2165730, 8659208, 17809936]], [[31, 31744, 1015808, 1082401, 32844106, 33317656], [31, 31744, 1083361, 4330468, 17318416, 32776456], [31, 31775, 1082401, 2165730, 8659208, 17809936], [31744, 1015808, 1082401, 6494406, 19483231, 32505856]], [[31, 544, 31744, 1082401, 2164802, 5214340], [31, 31744, 1015808, 3247203, 8659944, 18400817], [31, 31744, 1083361, 4329604, 32776456, 33047056], [256, 31744, 1015808, 1082401, 29224827, 32573506]], [[31, 31744, 2065441, 17318416, 21648020, 32573506], [256, 31744, 1015808, 1082401, 3247203, 32641156], [31744, 1015808, 1082401, 2165058, 32505856, 32641156]], [[31, 1023, 1082401, 2194498, 5214340, 17318416], [31, 31744, 1082401, 2164802, 17809936, 33530120], [31, 1047552, 1082401, 2164802, 9412872, 32641156], [31, 1047552, 1082401, 8659208, 17333776, 32641156]], [[31, 992, 31744, 1082401, 32911756, 33317656], [31, 31744, 1082401, 9412872, 32573506, 32641156], [31, 31744, 2065441, 4329604, 18859569, 32573506], [31, 31775, 2065441, 4329604, 8659208, 32573506]], [[31, 992, 1082401, 10824010, 17809936, 32776456], [31, 31744, 1082401, 2165730, 4329604, 17809936], [31, 31744, 1082401, 8659944, 21648020, 32641156], [31, 31744, 2065441, 4329604, 8682760, 32573506], [31, 1082401, 1113121, 2164802, 5214340, 32776456], [992, 31744, 2065441, 4329604, 8659208, 32603202]], [[31, 31744, 1082401, 2164802, 9412872, 33525892], [31, 31744, 1082401, 12989420, 17318416, 32642020], [31, 1047552, 1113121, 4329604, 8659208, 32573506]]], [[[31, 31744, 1082401, 6495206, 17318416, 32642020], [31, 1047552, 1082401, 2165730, 8659208, 17809936], [31, 1048575, 1082401, 2194498, 5214340, 8659208]], [[31, 992, 1113121, 8659208, 17318416, 32641156], [31, 31744, 1015808, 3248099, 6495206, 17318416], [992, 1082401, 1082431, 2164802, 9412872, 33047056]], [[31, 992, 31744, 3247203, 9412872, 19483218], [31, 992, 1082401, 3247203, 9412872, 33047056], [31, 992, 1082401, 8682760, 17809936, 21648020], [31, 992, 1113121, 8659944, 17318416, 32641156], [31, 31744, 777975, 1082401, 4330468, 17318416], [31, 31744, 1083361, 8659208, 10824010, 33047056], [288, 31744, 2065441, 2164802, 4329604, 32505856], [992, 31744, 1082401, 2164831, 9412872, 26207000]], [[992, 31744, 1015808, 2164831, 9741609, 18400817]], [[31, 31744, 1082401, 4330468, 18400817, 32776456], [31, 31744, 1083361, 9741609, 17318416, 32641156], [31, 31744, 2065441, 8659208, 29224827, 32573506], [256, 31744, 1015808, 1082401, 2164802, 32641156], [31744, 1015808, 1082401, 2164802, 32641412], [31744, 1015808, 1082401, 2165058, 32641156], [31744, 1015808, 1082657, 2164802, 32641156], [31744, 1015808, 3247203, 5412005, 17318431, 32505856]], [[31, 992, 507375, 1082401, 2164802, 9412872], [31, 31744, 1082401, 8659944, 12988812, 33047056], [31, 31744, 1082401, 9412872, 25977624, 32641156], [31, 31744, 4329604, 8659944, 9741609, 33047056]], [[31, 31744, 1082401, 2165730, 9412872, 17809936], [31, 1082401, 2165730, 17809936, 32776456], [31, 1082401, 2194498, 2195426, 5214340, 8659208], [31744, 1015808, 1082401, 2165730, 21648020, 32641156]], [[31, 31744, 2065441, 5214340, 8659208, 32573506]], [[31, 31744, 1082401, 2164802, 5215204, 13611404], [31, 31744, 1082401, 4330468, 17318416, 33317656], [992, 31744, 1082431, 8659208, 21648020, 32641156], [31744, 1015808, 2164802, 4329631, 5412005, 32776456]], [[31, 992, 31744, 1082401, 2165058, 32641156], [31, 31744, 1082401, 2194498, 9412872, 32641156], [992, 31744, 1082401, 2164831, 9412872, 18400817], [31744, 1015808, 1082401, 2164802, 4329604, 32776448]], [[31, 992, 1113121, 8659208, 16236015, 32641156], [31, 31744, 2065441, 4329604, 9412872, 32573506], [31, 32736, 1082401, 2165730, 4329604, 17809936], [1023, 31744, 1082401, 2165730, 4329604, 17809936]], [[31, 992, 31744, 3247203, 9412872, 18400817], [31, 992, 1082401, 2164802, 9412872, 33047056]], [[31, 992, 1082401, 2164802, 9413608, 33047056], [992, 31744, 1082431, 3247203, 4329604, 32776456], [992, 31744, 1082431, 4329604, 8659208, 33062416]], [[31, 992, 31744, 3247203, 5412005, 32776456], [31, 31744, 1082401, 2165730, 4329604, 17809951], [31, 31744, 1082401, 4330468, 17318416, 32776456], [992, 31744, 1015808, 9741609, 18400817, 32573506]], [[31, 992, 1082401, 17333776, 32641156, 32776456], [31, 31744, 1082401, 4330468, 17318416, 32777192], [31, 31744, 1083361, 8659944, 17318416, 32641156], [31744, 777983, 1015808, 1082401, 2164802, 4329604]], [[256, 31744, 1015808, 1082401, 2164802, 32641412], [256, 31744, 1015808, 1082401, 2165058, 32641156], [256, 31744, 1015808, 1082657, 2164802, 32641156], [992, 31744, 1082401, 2164831, 9741609, 17809936], [992, 31744, 1082431, 8659208, 12988812, 33047056], [31744, 1015808, 1082401, 2164802, 4329604, 32514304]]], [[[31, 992, 31744, 9741609, 12988812, 33047056], [31, 31744, 1083361, 4329604, 9742313, 33047056], [992, 31744, 1015808, 1082401, 2164802, 32641412], [992, 31744, 1015808, 1082401, 2165058, 32641156], [992, 31744, 1015808, 1082657, 2164802, 32641156], [992, 31744, 1016064, 1082401, 2164802, 32641156]], [[31, 992, 31744, 3247203, 9741609, 17809936], [31, 31744, 1083361, 3248099, 4329604, 33047056], [31, 31744, 2065441, 4329604, 8659208, 32603202]], [[31, 992, 1082401, 2165730, 17809936, 32776456], [31, 31744, 1082401, 4330468, 32776456, 33317656], [256, 31744, 2065441, 4329604, 32573506]], [[31, 992, 1082401, 2194498, 5214340, 10824010], [31, 992, 1082401, 8682760, 29224827, 33047056], [31, 31744, 1082401, 8659208, 33182356, 33525892], [31744, 1015808, 1083361, 2164802, 32776456, 33047056]], [[31, 31744, 1083361, 4329604, 12988812, 33047056], [992, 31744, 1082431, 4329604, 33047056, 33317656]], [[31, 31744, 1015808, 10824010, 12989420, 17318416], [992, 31744, 1082401, 8659208, 32641183, 32708806]], [[31, 31744, 1015808, 6495206, 10824010, 17318416], [31, 31744, 1082401, 4330468, 16236015, 32776456], [992, 31744, 1082401, 4329631, 6494406, 17809936], [992, 31744, 1082401, 4329631, 32776456, 33047056]], [[31, 31744, 1082401, 8659944, 10824010, 33047056], [31, 31744, 2065441, 4330468, 17318416, 32573506], [992, 1023, 1082401, 2164802, 9412872, 33047056]], [[31, 31744, 1015808, 2165730, 21648020, 25977624], [992, 31744, 1082401, 2164831, 8659208, 17809936]], [[31, 992, 1113121, 12988812, 17318416, 32776456], [31, 31744, 1082401, 8659944, 18400817, 32641156], [992, 31744, 1082401, 2164831, 8659944, 17809936], [992, 31744, 1082401, 5214340, 21648020, 32573506], [992, 31744, 1082431, 4329604, 32776456, 33047056], [31744, 1015808, 1082409, 2164802, 4329604, 32776456]], [[31, 992, 31744, 5412005, 6494406, 17809936], [31, 31744, 2065441, 4329604, 8659208, 32708806]], [[31, 992, 31744, 1082401, 33114706, 33182356], [31, 31744, 1082401, 8659944, 17318416, 32912364], [31, 32736, 1082401, 2164802, 8659944, 17809936], [992, 31744, 1016320, 1082401, 2164802, 32641156], [992, 31744, 1082401, 2164831, 9412872, 16236015]], [[8, 31744, 1082401, 2164802, 5214340, 32776456], [31, 992, 1082401, 2194498, 5214340, 9741609], [31, 992, 1082401, 6494406, 8682760, 32641156], [31, 992, 1113121, 8659208, 17318416, 32641183], [31, 1082401, 2165730, 8659208, 8682760, 17809936], [31744, 1015808, 1082401, 2164831, 6494406, 32776456]], [[31, 992, 1082401, 2194498, 5214340, 19496530], [31, 31744, 1082401, 2164802, 13611404, 33530120], [31, 31744, 1082401, 9412872, 19483218, 32573506], [31, 31775, 1082401, 2165730, 4329604, 17809936], [31, 1047552, 2164802, 4330468, 8659208, 17333776], [31, 1082401, 1083361, 2164802, 17809936, 32776456]], [[31, 31744, 1015808, 3247203, 6494406, 32776456], [256, 992, 31744, 2065441, 4329604, 32573506]], [[31, 31744, 1083361, 6494406, 17318416, 32641156], [31, 31744, 2065441, 8659208, 25977624, 32573506], [992, 1047552, 1082401, 2164802, 17333776, 32641156]]], [[[31, 992, 31744, 1082401, 32844106, 32911756], [31, 31744, 1015808, 9741609, 18400817, 32573506]], [[31, 992, 1113121, 8682760, 17318416, 32641156], [992, 31744, 1082431, 8659208, 10824010, 33047056]], [[31, 31744, 1082401, 8659944, 17318416, 32641156], [256, 31744, 1015808, 1082401, 2164802, 32708806], [31744, 1015808, 1082401, 2164802, 17333791, 32641156]], [[31, 992, 31744, 3247203, 5214340, 19483218], [31, 31744, 1015808, 1082401, 2164802, 32641412], [31, 31744, 1015808, 1082401, 2165058, 32641156], [31, 31744, 1015808, 1082657, 2164802, 32641156], [31, 31744, 1016064, 1082401, 2164802, 32641156]], [[31, 31744, 1082401, 2165730, 17809936, 29224827], [288, 31744, 1015808, 1082401, 2164802, 32641156]]]]
  | 7 => [[[[31, 992, 1082401, 2194498, 5214340, 8659208], [31, 31744, 777975, 1015808, 1082401, 2164802, 4329604]], [[31, 992, 32736, 1082401, 2164802, 8659208, 17809936], [992, 1023, 31744, 1082401, 2164802, 8659208, 17809936], [31744, 1015808, 1082401, 1082431, 2164802, 4329604, 32776456]], [[31, 31744, 1015808, 1082401, 2164802, 5412005, 32776456], [31, 31744, 1015808, 1082401, 2164802, 8659944, 12988812], [31, 31744, 1015808, 2164802, 4329604, 8659944, 9741609]], [[31, 31744, 1015808, 1082401, 2165730, 6494406, 8659208]], [[31, 992, 31744, 1015808, 2164802, 5412005, 18400817], [31, 992, 31744, 1015808, 3247203, 5412005, 17318416], [31, 31744, 1015808, 1082401, 17318416, 19483218, 32776456], [31, 31744, 1015808, 2164802, 17318416, 18400817, 32776456]], [[31, 31744, 1015808, 1082401, 8659944, 17318416, 32573506], [31, 31744, 1082401, 2164802, 5214340, 8659208, 8659944], [992, 31744, 913275, 1015808, 1082401, 2164802, 8659208]], [[31, 992, 31744, 1082401, 17318416, 32641156, 32911756], [31, 31744, 1047552, 1082401, 4329604, 8659208, 32573506], [31, 31744, 1082401, 2164802, 8659208, 17809936, 33521664], [992, 31744, 1015808, 1082401, 2164802, 24895223, 32641156], [31744, 1015808, 1082401, 2164802, 4329604, 17318431, 32573506]], [[31, 992, 31744, 1082401, 2164802, 5214340, 18400817], [31, 992, 31744, 1082401, 3247203, 5214340, 17318416]], [[31, 992, 31744, 1082401, 8659208, 17318416, 32641156], [31, 31744, 1082401, 2164802, 4329604, 8659944, 9412872]], [[31, 992, 31744, 1082401, 8659944, 17318416, 32641156], [31, 992, 1082401, 1113121, 2164802, 17318416, 32641156]], [[31, 992, 31744, 1082401, 2165730, 17318416, 32641156], [31, 31744, 1015808, 1082401, 2164802, 9413608, 17318416], [31, 31744, 1015808, 1113121, 2164802, 8659208, 32641156], [31, 31744, 1082401, 1083361, 4329604, 8659208, 33047056], [256, 31744, 1015808, 1082401, 2164802, 4329604, 32537600], [31744, 32000, 1015808, 1082401, 2164802, 4329604, 32505856]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 32776456]], [[31, 992, 31744, 1082401, 2164831, 9412872, 17318416]], [[31, 992, 31744, 1015808, 1082401, 10824010, 12988812], [31, 992, 31744, 1015808, 2164802, 9741609, 12988812], [31, 31744, 1015808, 1082401, 2164802, 17333776, 32641156], [31, 31744, 1015808, 1082401, 8659208, 16236015, 32573506]], [[31, 992, 31775, 1082401, 2164802, 9412872, 17318416], [31, 1023, 31744, 1082401, 2164802, 9412872, 17318416], [31, 31744, 1082401, 2164802, 5214340, 32776456], [992, 31744, 1015808, 1082401, 2164802, 32641156, 33182356], [992, 31744, 1015808, 1082401, 2164802, 32776456, 33047056]], [[31, 992, 31744, 1082401, 4329604, 12988812, 33047056], [31, 992, 31744, 4329604, 5412005, 8659208, 33047056]]], [[[31, 992, 31744, 1082401, 2164802, 5214340, 17318416], [31, 992, 31744, 1082401, 2164802, 5412005, 17809936], [31, 992, 31744, 1082401, 3247203, 4329604, 17809936], [31, 992, 31744, 1082401, 5214340, 8659208, 10824010], [31, 992, 1082401, 1113121, 2164802, 8659208, 33047056], [31, 31744, 1015808, 1082401, 2164802, 8659944, 17809936]], [[31, 992, 31744, 1082401, 2165730, 8659208, 33047056], [31, 992, 31744, 1082401, 8659208, 16236015, 32641156]], [[31, 992, 31744, 1082401, 2164831, 8659208, 17809936], [31, 992, 31744, 1082401, 5214340, 17318416, 31389629]], [[31, 992, 31744, 1082401, 2164802, 9412872, 12988812], [31, 31744, 1083361, 4329604, 8659208, 33047056]], [[31, 992, 31775, 1082401, 2164802, 8659208, 17809936], [31, 1023, 31744, 1082401, 2164802, 8659208, 17809936]], [[31, 992, 1047552, 1082401, 2164802, 9412872, 17318416]], [[31, 992, 31744, 1082401, 2164802, 8659208, 13611404], [31, 31744, 1015808, 1082401, 6494406, 17318416, 32573506]], [[31, 31744, 1015808, 1082401, 2165730, 17318416, 24895223], [992, 31744, 1082401, 2164802, 4329604, 17809936, 33521664]], [[31, 992, 31744, 1082401, 4329604, 32573506, 32776456], [31, 31744, 913275, 1015808, 1082401, 2164802, 8659208]], [[31, 992, 31744, 1082401, 2164802, 4329604, 17809936], [31, 992, 31744, 1082401, 2164802, 5214340, 16236015], [31, 992, 1048575, 2164802, 4329604, 8682760, 17318416], [31, 31744, 1015808, 1082401, 2164802, 24895223, 32641156], [992, 31744, 1015808, 1082401, 2164831, 8659208, 17809936]], [[31, 992, 31744, 1082401, 2164802, 5214340, 32776456], [31, 992, 31744, 1082401, 6494406, 17318416, 32641156]], [[31, 992, 31744, 1082401, 4329604, 17809936, 31389629], [31, 992, 1047552, 1082401, 2164802, 8659208, 17809936], [992, 31744, 1015808, 1082401, 6494406, 10824010, 32505856]], [[31, 992, 32736, 1082401, 2164802, 5214340, 17318416], [31, 31744, 1082401, 1083361, 2164802, 8659208, 33047056], [1023, 31744, 1015808, 1082401, 2164802, 4329604, 17318431]], [[31, 992, 31744, 1082401, 4329604, 17333776, 32776456]], [[31, 31744, 1082401, 2164802, 5214340, 8659208, 33553439]], [[31, 992, 31744, 1082401, 2164802, 5214340, 17318431], [31, 992, 31744, 1083361, 4329604, 8659208, 33047056], [31, 31744, 1015808, 2164802, 4330468, 12988812, 17318416]]], [[[31, 992, 31744, 1082401, 4329604, 25977624, 32776456], [31, 992, 31744, 1082401, 12988812, 17318416, 32776456]], [[31, 992, 31744, 1082401, 2164802, 5214340, 22008468], [31, 992, 31744, 1082401, 2164802, 9412872, 17809936], [31, 31744, 1015808, 1082401, 2164802, 32641156, 33182356], [31, 31744, 1015808, 1082401, 2164802, 32776456, 33047056], [31, 31744, 1082401, 2164802, 4329604, 9412872, 33553439], [992, 31744, 1015808, 1082401, 2164802, 21648020, 32641156]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 32776479]], [[31, 992, 31744, 1082401, 8659208, 17318416, 32641183], [31, 31744, 1015808, 1082401, 2164802, 8659208, 32911756]], [[31, 992, 31744, 1082401, 2194498, 4329604, 32776456], [31, 992, 31744, 1082401, 17318416, 32776456, 32844106], [31, 31744, 1015808, 1082401, 2165730, 17318416, 32641156], [992, 31744, 1015808, 3247203, 5412005, 8659208, 32505856]], [[31, 992, 32736, 1082401, 2164802, 4329604, 17809936], [992, 1023, 31744, 1082401, 2164802, 4329604, 17809936]], [[31, 992, 31744, 1082431, 8659208, 17318416, 32641156], [992, 31744, 1015808, 1082401, 19483218, 25977624, 32505856], [992, 31744, 1015808, 8659208, 18400817, 19483218, 32505856]], [], [[31, 992, 31744, 1082401, 2164802, 4329604, 17809951], [31, 992, 31744, 1082401, 8682760, 17318416, 32641156], [31, 31744, 1015808, 2164802, 8659944, 17318416, 21648020]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 32844106]], [[31, 992, 31744, 1082401, 4329604, 9741609, 33047056], [31, 992, 31744, 1082401, 5412005, 8659208, 33047056], [31, 31744, 1015839, 1082401, 2164802, 4329604, 32776456], [31, 31744, 1082401, 2164802, 4329604, 17809936, 33521664]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 32800008], [31, 31744, 1015808, 1113121, 4329604, 8659944, 17318416]], [[31, 31744, 1015808, 1113121, 2165730, 4329604, 17318416]], [[31, 992, 31744, 507375, 1082401, 4329604, 8659208], [992, 31744, 1015808, 2164802, 4329631, 5412005, 8659208]], [[31, 31744, 1015808, 1082401, 6494406, 10824010, 32505856], [31, 31744, 1082401, 4329604, 8659208, 9412872, 32573506]], [[31, 992, 31775, 1082401, 2164802, 5214340, 17318416], [31, 1023, 31744, 1082401, 2164802, 5214340, 17318416], [31, 31744, 1015808, 2164802, 4329604, 17318416, 24894487]]], [[[31, 31744, 1015808, 1082401, 2164802, 6495206, 17318416]], [[31, 992, 31744, 1015808, 2164802, 5412005, 12988812], [31, 992, 1082401, 2164802, 8682760, 9412872, 17318416], [31, 31744, 1015808, 1082401, 2164802, 29224827, 32776456], [31, 31744, 1015808, 2164802, 4329604, 25977624, 32776456], [31, 31744, 1015808, 2164802, 4330468, 8659208, 19483218], [31, 31744, 1015808, 2164802, 12988812, 17318416, 32776456]], [[31, 992, 31744, 1082401, 10824010, 17318416, 32776456], [31, 31744, 1015808, 1082401, 2165730, 17318416, 21648020], [992, 31744, 1082431, 4329604, 8659208, 33047056]], [[31, 992, 31744, 1015808, 2164802, 21648020, 25977624], [31, 992, 31744, 1015808, 8659208, 19483218, 21648020], [31, 992, 31744, 1082401, 4329604, 8659208, 33047056], [31, 992, 1082401, 1113121, 4329604, 17318416, 32776456], [31, 31744, 1048575, 1082401, 2164802, 5214340, 8659208], [992, 31744, 1015808, 1082401, 2164802, 19483218, 32641156], [992, 31744, 1082401, 2164802, 4329604, 4329631, 9412872]], [[31, 992, 31744, 1082401, 2164802, 5214340, 12988812], [31, 992, 31744, 1082401, 4329604, 8659944, 33047056], [31, 992, 1082401, 1113121, 2164802, 4329604, 33047056], [31, 31744, 1015808, 1082401, 2164802, 5214340, 32776456], [31, 31744, 1015808, 1082401, 2164802, 21648020, 32641156], [31, 31744, 1082401, 2164802, 4329604, 9412872, 9413608]], [[31, 992, 31744, 1082401, 2165730, 4329604, 33047056], [31, 992, 31744, 1082401, 3247203, 17318416, 32641156]], [[31, 992, 31744, 5214340, 8659208, 17318416, 19483218], [31, 31744, 1047552, 1082401, 2164802, 8659208, 32641156], [31, 31744, 1048575, 1082401, 2164802, 4329604, 9412872]], [[31, 992, 31744, 1082401, 4329604, 6494406, 9412872], [31, 992, 1082401, 2164802, 8659208, 8682760, 17809936], [31, 31744, 1015808, 1082401, 2164802, 4330468, 17333776], [31, 31744, 1015808, 3247203, 5412005, 8659208, 32505856]], [[31, 992, 31775, 1082401, 2164802, 4329604, 17809936], [31, 1023, 31744, 1082401, 2164802, 4329604, 17809936]], [[31, 992, 31744, 4329604, 9412872, 17318416, 19483218], [31, 31744, 1015808, 1082401, 19483218, 25977624, 32505856], [31, 31744, 1015808, 8659208, 18400817, 19483218, 32505856]], [[31, 992, 31744, 1082401, 2164802, 4329604, 13611404]], [], [[31, 992, 31744, 1082401, 2164802, 9741609, 33047056], [31, 992, 31744, 1082401, 3247203, 8659208, 33047056], [992, 31744, 1015808, 1082401, 2164802, 18400817, 32641156], [31744, 1015808, 1082401, 2164802, 4329604, 32505856, 33554175]], [], [[31, 992, 31744, 1082401, 8659208, 10824010, 32641156], [31, 31744, 1015808, 1082401, 17318416, 32776456, 32844106]], [[31, 992, 31744, 507375, 1082401, 2164802, 8659208], [31, 992, 31744, 1082401, 2164802, 17809936, 29224827], [31, 992, 32736, 1082401, 4329604, 8659208, 33047056], [992, 1023, 31744, 1082401, 4329604, 8659208, 33047056]]], [[[31, 992, 31744, 1082401, 17318416, 31389629, 32641156], [31, 992, 1048575, 1082401, 2164802, 9412872, 17318416], [31, 31744, 1082401, 1083361, 2164802, 4329604, 33047056], [31, 31744, 1082401, 2065441, 2164802, 4329604, 32776456]], [[8, 31744, 1015808, 1082401, 2164802, 17318416, 32641156], [992, 31744, 1015808, 1082401, 2164831, 6494406, 8659208]], [[31, 992, 31744, 1082401, 2164802, 5214340, 17809936], [31, 992, 31744, 1082401, 2164802, 9412872, 13611404], [31, 992, 31744, 1082401, 17318416, 32776456, 32911756], [31, 31744, 1015808, 1082401, 8682760, 17318416, 32641156]], [[31, 992, 31744, 1015808, 1082401, 6494406, 10824010], [31, 992, 31744, 1015808, 3247203, 6494406, 8659208], [31, 992, 31744, 1082401, 2194498, 5214340, 17318416], [31, 31744, 1015808, 1082401, 8659944, 17318416, 19483218], [31, 31744, 1015808, 2164802, 8659944, 17318416, 18400817]], [[31, 992, 31744, 1082401, 4329604, 21648020, 32776456], [31, 992, 31744, 4329604, 5412005, 17318416, 32776456], [31, 31744, 1015808, 2164802, 4330468, 8659944, 17318416], [31, 31744, 1082401, 4329604, 8659208, 33047056, 33521664]], [[31, 992, 31744, 1082401, 4329604, 6494406, 33047056], [31, 992, 1082401, 1113121, 2164802, 17318416, 32776456], [992, 31744, 1015808, 1082401, 8659208, 10824010, 32641156], [992, 31744, 1015808, 2164802, 8659208, 9741609, 32641156]], [[31, 992, 31744, 1082401, 2164802, 5214340, 10824010], [31, 992, 31744, 1082401, 2165730, 17318416, 32776456], [31, 992, 1048575, 1082401, 2164802, 8659208, 17809936], [31, 31744, 1015808, 1082401, 2164802, 19483218, 32641156], [31, 31744, 1015808, 2164802, 3247203, 17318416, 32641156]], [[31, 992, 31744, 1082401, 8659208, 31389629, 33047056]], [[31, 992, 31744, 1082401, 4329604, 17809936, 25977624], [31, 992, 31744, 1082401, 8659208, 17809936, 21648020], [31, 992, 31744, 4329604, 8659208, 17809936, 18400817], [31, 31744, 1015808, 2164802, 17318416, 32472030, 32641156], [31744, 1015808, 1082401, 2164802, 17318431, 32641156]], [], [[31, 31744, 1015808, 1082401, 2164802, 17318416, 24894487], [992, 31744, 1015808, 1082401, 19483218, 21648020, 32505856]], [[31, 992, 1082401, 2164802, 9412872, 17318416, 33047056], [31, 31744, 1015808, 1083361, 2164802, 8659208, 33047056], [992, 31744, 1015808, 1082401, 6494406, 8659208, 32573506]], [[31, 992, 31744, 1015808, 2164802, 5412005, 9741609], [31, 992, 31744, 1015808, 3247203, 5412005, 8659208], [31, 992, 31744, 1082401, 2194498, 4329604, 17809936], [31, 31744, 1015808, 1082401, 2164802, 25977624, 32776456], [31, 31744, 1015808, 1082401, 8659944, 10824682, 17318416], [31, 31744, 1015808, 1082401, 10824010, 17318416, 32776456], [31, 31744, 1015808, 2164802, 4330468, 8659208, 16236015]], [[31, 31744, 1015808, 1082401, 2165730, 10824682, 17318416]], [[31, 992, 31744, 1015808, 1082401, 19483218, 25977624], [31, 992, 31744, 1015808, 2164802, 18400817, 25977624], [31, 992, 31744, 1015808, 8659208, 18400817, 19483218], [31, 992, 31744, 1082401, 4329631, 8659208, 33047056], [31, 992, 31744, 2065441, 8659208, 17318416, 32573506], [31, 31744, 1015808, 1082401, 2165730, 4330468, 17318416], [31, 31744, 1015808, 1082401, 17318416, 29224827, 32573506], [992, 31744, 1015808, 1082401, 2164802, 16236015, 32641156]], [[31, 992, 31744, 1082401, 2164802, 5214340, 9741609], [31, 992, 31744, 1082401, 3247203, 5214340, 8659208], [31, 31744, 1015808, 1082401, 2164802, 18400817, 32641156], [31, 31744, 1015808, 1082401, 3247203, 17318416, 32641156], [31, 31744, 1082401, 4329604, 5214340, 8659208, 32573506], [992, 31744, 1015808, 1082401, 2164802, 32641156, 32776456]]], [[[31, 992, 31744, 3115074, 4329604, 8659208, 17318416, 32539681]], [[31, 992, 31744, 1082431, 4329604, 8659208, 33047056], [31, 992, 1082401, 1113121, 2164802, 8659208, 32641156], [31, 992, 1082401, 2164802, 8659208, 17809936, 33047056]], [[31, 992, 31744, 1082401, 2164802, 5412005, 9412872], [31, 992, 31744, 1082401, 3247203, 4329604, 9412872], [31, 992, 31775, 1082401, 4329604, 8659208, 33047056], [31, 992, 1082401, 2164802, 4329604, 17333776, 17825296], [31, 1023, 31744, 1082401, 4329604, 8659208, 33047056]], [[31, 992, 31744, 1082401, 4329604, 8682760, 33047056]], [[31, 992, 31744, 1082401, 9412872, 17318416, 19483218], [31, 992, 31744, 1083361, 4329604, 17318416, 32776456], [992, 31744, 1015808, 1082401, 2164802, 17318431, 32641156]], [], [[31, 31744, 1015808, 1082401, 2165730, 8659208, 25977624]], [], [[31, 992, 31744, 1082401, 2164802, 5214340, 8659208], [31, 31744, 1015808, 1082401, 2164802, 17318416, 32641156], [31, 31744, 1015808, 1082401, 8659208, 10824010, 32641156], [31, 31744, 1015808, 2164802, 8659208, 9741609, 32641156]], [[31, 992, 31744, 1082401, 8659208, 29224827, 33047056], [992, 31744, 1082401, 2164802, 4329604, 9412872, 33521664]], [[31, 992, 31744, 1082401, 2164802, 17809936, 25977624], [31, 992, 31744, 1082401, 5214340, 8659208, 31389629]], [[31, 992, 31744, 1082401, 2164802, 4329604, 9412872], [31, 992, 1082401, 2164802, 4329604, 8682760, 17809936]], [], [[31, 992, 31744, 777975, 1082401, 4329604, 17318416], [31, 992, 31744, 1082401, 4329604, 9412872, 31389629], [31, 992, 1082401, 2164802, 9412872, 9436424, 17318416], [31, 31744, 1015808, 1082401, 19483218, 21648020, 32505856], [31, 31744, 1082401, 1083361, 2164802, 8659208, 32641156]], [[31, 31744, 1015808, 1082401, 6494406, 8659208, 32573506], [31, 31744, 1015808, 2164802, 4330468, 5412005, 17318416]], [[31, 992, 31744, 1082401, 4329604, 18400817, 32776456], [31, 992, 31744, 1082401, 5412005, 17318416, 32776456], [480, 31744, 1015808, 1082401, 2164802, 4329604, 32505856], [992, 31744, 1082401, 1082431, 2164802, 4329604, 33047056]]], [[[31, 992, 31744, 1082401, 2164802, 5412005, 33047056], [31, 992, 31744, 1082401, 2164802, 17318416, 26207000], [31, 992, 31744, 1082401, 3247203, 4329604, 33047056], [31, 31744, 1015808, 1082401, 2165730, 17318416, 32776456]], [[31, 31744, 1015808, 1082401, 2164802, 16236015, 32641156], [31, 32736, 1016800, 1082401, 2164802, 4329604, 8659208]], [[31, 992, 31744, 1082401, 2164831, 8659208, 33047056], [31, 992, 31744, 1082401, 6494406, 8659208, 32641156], [31, 31744, 1015808, 1082401, 2164802, 32641156, 32776456]], [[31, 992, 31744, 507375, 1082401, 2164802, 4329604], [31, 992, 31744, 1082401, 2164802, 5214340, 13611404], [31, 992, 31744, 1082401, 2164802, 17809936, 24895223], [31, 992, 31744, 1082401, 4329604, 17318416, 33317656], [31, 31744, 1015808, 2164802, 4330468, 8682760, 17318416]], [[31, 992, 32736, 1082401, 2164802, 5214340, 8659208], [256, 31744, 1015808, 1048575, 1082401, 2164802, 4329604], [992, 1023, 31744, 1082401, 2164802, 5214340, 8659208]], [[31, 992, 31744, 1082401, 17318416, 32573506, 32641156]], [[31, 31744, 2065441, 4329604, 17318416, 32573506]], [[31, 992, 31744, 1082401, 8659208, 33047056, 33114706], [31, 992, 31744, 1113121, 8659208, 17318416, 32641156], [31, 992, 32736, 1082401, 2164802, 4329604, 9412872], [31, 31744, 1015808, 1082401, 2164802, 17318431, 32641156], [992, 1023, 31744, 1082401, 2164802, 4329604, 9412872]], [[31, 992, 31744, 1082401, 4329604, 17318416, 32776456]], [[31, 992, 31744, 1082401, 4329604, 17318416, 32777192], [31, 31744, 1082401, 2164802, 5214340, 8659208, 33521664], [992, 31744, 1015808, 1082401, 2164802, 12988812, 32641156]], [[31, 31744, 1015808, 1113121, 2164802, 4329604, 32776456], [31, 31744, 1082401, 2164802, 4329604, 4330468, 17809936], [992, 31744, 1015808, 1082431, 2164802, 8659208, 33047056]], [[31, 992, 31744, 1082401, 4329604, 31389629, 33047056]], [[31, 992, 31744, 1082401, 8659208, 32573506, 33047056], [31, 992, 1047552, 1113121, 2164802, 4329604, 17318416], [31, 31744, 1015808, 2164802, 8659944, 9742313, 17318416], [31, 31744, 1082401, 2164802, 4329604, 9412872, 33521664]], [[31, 992, 31744, 1082401, 4329604, 32776456, 33317656], [31, 992, 31744, 1082401, 17318416, 25977624, 32641156], [31, 31744, 1015808, 2164802, 4329604, 8659944, 17333776]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 33553695], [31, 31744, 1015808, 1083361, 2164802, 4330468, 17318416], [31, 31744, 1048575, 2065441, 2164802, 4329604, 8659208], [992, 31744, 1015808, 1082401, 10824010, 25977624, 32505856]], [[31, 992, 31744, 777975, 1082401, 2164802, 17318416], [31, 992, 31744, 1082401, 2164802, 5214340, 8659231], [31, 992, 31744, 1082401, 4329604, 8659208, 33182356], [31, 31744, 1015808, 1083361, 2164802, 4329604, 33047056], [31, 31744, 1015808, 2164802, 4330468, 9412872, 17318416]]], [[[31, 31744, 1015808, 1082401, 2164802, 4330468, 19483218], [31, 31744, 1015808, 2164802, 3247203, 4330468, 17318416], [31, 31744, 1015808, 2164802, 8659944, 12988812, 17318416]], [[31, 992, 31744, 1082401, 2164802, 9412872, 33047056], [31, 992, 31744, 1082401, 2194498, 17318416, 32641156], [31, 992, 31744, 1082401, 3247203, 17318416, 32776456], [31, 992, 31744, 1082401, 4329604, 16236015, 32776456]], [[31, 992, 31744, 1015808, 1082401, 19483218, 21648020], [31, 992, 31744, 1015808, 2164802, 18400817, 21648020], [31, 992, 31744, 1082401, 2164802, 4329604, 9412895], [31, 992, 31744, 2065441, 4329604, 17318416, 32573506], [31, 31744, 1015808, 1082401, 17318416, 24895223, 32573506], [31, 31744, 1015808, 2164802, 4330468, 17318416, 32472030]], [[31, 992, 1082401, 2164802, 9412872, 17318416, 17333776], [992, 31744, 1015808, 1082401, 8659208, 32573506, 33047056], [31744, 1015808, 1082401, 2164802, 4329604, 17318431, 32537600]], [[31, 992, 32736, 1082401, 4329604, 17318416, 32776456], [256, 31744, 1015808, 1082401, 2164802, 4329604, 32505856], [992, 31744, 1015808, 2164802, 4329631, 8659208, 17333776], [31744, 1015808, 1082401, 2164802, 4329604, 32506112]], [[31, 992, 31744, 913275, 1082401, 8659208, 17318416], [31, 992, 31744, 1082401, 5214340, 17318416, 19483218], [31, 992, 1047552, 1082401, 2164802, 4329604, 8682760], [31, 31744, 1015808, 2164802, 4330468, 8659208, 17809936]], [[31, 992, 31744, 1082401, 17318416, 24895223, 32641156], [31, 31744, 1015808, 1082401, 2164802, 17318416, 32708806]], [[31, 992, 31775, 1082401, 2164802, 5214340, 8659208], [31, 1023, 31744, 1082401, 2164802, 5214340, 8659208], [992, 31744, 1015808, 1082401, 2164802, 17809936, 32641156]], [[31, 992, 31744, 1082401, 2164802, 5214340, 8682760], [31, 992, 1047552, 2164802, 4329604, 8659208, 17333776]], [[31, 992, 1082401, 2164802, 8659208, 17333776, 17809936], [31, 31744, 1015808, 1082401, 2164802, 4330468, 18400817]], [[31, 992, 31775, 1082401, 2164802, 4329604, 9412872], [31, 1023, 31744, 1082401, 2164802, 4329604, 9412872], [31, 31744, 32736, 1082401, 2164802, 9412872, 17318416]], [[31, 992, 31744, 1015808, 2164802, 12988812, 25977624], [31, 992, 31744, 1015808, 10824010, 12988812, 17318416], [31, 992, 31744, 1082401, 2164802, 4329604, 9436424], [992, 31744, 1015808, 1082401, 2164802, 10824010, 32641156], [992, 31744, 1015808, 2164802, 3247203, 8659208, 32641156]], [[31, 992, 31744, 1082401, 17318416, 31389629, 32776456], [31, 31744, 1015808, 1082401, 2164802, 12988812, 32641156]], [[8, 31744, 1015808, 1082401, 2164802, 17318416, 32776456], [31, 992, 31744, 1082401, 3247203, 8659208, 32641156], [992, 31744, 1015808, 2164802, 8659208, 32472030, 32641156]], [[31, 992, 31744, 1082401, 2164802, 17809936, 21648020], [31, 992, 31744, 5214340, 8659208, 10824010, 17318416], [31, 31744, 1016800, 1082401, 2164802, 5214340, 8659208]], [[31, 31744, 1015808, 1082401, 17318416, 32573506, 32641156], [31, 31744, 1082401, 2164802, 5214340, 8659208, 32641156], [256, 31744, 1015808, 1082401, 2164802, 4329604, 32506112]]], [[[31, 31744, 32736, 1082401, 2164802, 8659208, 17809936], [992, 31744, 31775, 1082401, 2164802, 8659208, 17809936], [992, 31744, 1015808, 1082401, 2164802, 4329604, 32506112], [992, 31744, 1015808, 1082401, 2164802, 4329860, 32505856]], [[31, 992, 31744, 1082401, 2164802, 9412872, 29224827], [31, 992, 31744, 1082401, 2164802, 17318416, 22008468], [31, 31744, 1015808, 1082401, 10824010, 25977624, 32505856], [31, 31744, 1015808, 9741609, 10824010, 17318416, 32505856], [31, 31744, 1016800, 1082401, 2164802, 4329604, 9412872]], [[31, 31744, 1015808, 1082401, 2164802, 4330468, 17318416], [31, 31744, 1015808, 1082401, 2164802, 19483218, 32776456], [31, 31744, 1015808, 2164802, 3247203, 17318416, 32776456]], [[31, 992, 31744, 1082401, 4329631, 17318416, 32776456], [31, 992, 1082401, 2164802, 8659208, 17809936, 33538576], [992, 31744, 1015808, 1082401, 8659208, 29224827, 32573506]], [[31, 992, 31744, 1082401, 2164802, 5214340, 9412872], [31, 31744, 1015808, 2164802, 17318416, 32472030, 32776456], [31, 31744, 1082401, 4329604, 4330468, 8659208, 33047056], [992, 31744, 1015808, 1082401, 2164802, 9741609, 32641156], [992, 31744, 1015808, 1082401, 3247203, 8659208, 32641156]], [[31, 992, 31744, 1082401, 8659208, 33047056, 33182356]], [[31, 992, 31744, 1082431, 4329604, 17318416, 32776456], [31, 31744, 1015808, 1082401, 8659208, 32573506, 33047056], [31, 31744, 1082401, 2165730, 4329604, 8659208, 17809936]], [[31, 992, 31775, 1082401, 4329604, 17318416, 32776456], [31, 1023, 31744, 1082401, 4329604, 17318416, 32776456], [31, 31744, 1015808, 1113121, 4329604, 17318416, 32573506]], [[31, 992, 31744, 1082401, 4329604, 17318416, 32800008], [31, 992, 31744, 1082401, 8659208, 31389629, 32641156]], [[8, 31744, 1015808, 1082401, 2164802, 8659208, 32641156], [31, 992, 31744, 1082401, 8659208, 17318416, 32642020], [31, 31744, 777975, 1015808, 1082401, 2164802, 17318416]], [[31, 992, 31744, 1082401, 4329604, 9412872, 25977624], [31, 992, 31744, 1082401, 8659208, 32641156, 33047056], [31, 992, 31744, 1082401, 9412872, 12988812, 17318416], [31, 992, 31744, 4329604, 9412872, 9741609, 17318416], [31, 31744, 1015808, 1082401, 2164802, 17809936, 32641156]], [[31, 992, 31744, 1082401, 2194498, 5214340, 8659208], [31, 992, 31744, 1082401, 4329604, 33047056, 33114706], [31, 31744, 1015808, 1082401, 2164802, 4330468, 16236015], [31, 31744, 1015808, 1082401, 2164802, 18400817, 32776456], [31, 31744, 1015808, 1082401, 2194498, 17318416, 32641156], [31, 31744, 1015808, 1082401, 3247203, 17318416, 32776456], [31, 31744, 1015808, 1082401, 8659944, 10824010, 17318416], [31, 31744, 1015808, 2164802, 8659944, 9741609, 17318416], [992, 31744, 1015808, 1082401, 2164802, 4329604, 32506368], [992, 31744, 1015808, 1082401, 2164802, 32641156, 32911756]], [[31, 31744, 1015808, 1082401, 2165730, 10824010, 17318416]], [[992, 31744, 1015808, 1082401, 2164802, 8659208, 32641156]], [[31, 992, 31744, 1082401, 2194498, 4329604, 9412872], [31, 992, 31744, 1082401, 17318416, 29224827, 32776456], [31, 31744, 1015808, 1082401, 2164802, 10824010, 32641156], [31, 31744, 1015808, 2164802, 3247203, 8659208, 32641156]], [[31, 31744, 1015839, 1082401, 4329604, 8659208, 32573506]]], [[[31, 992, 31744, 1082401, 4329604, 32573506, 33047056], [31, 992, 31744, 1082401, 4329604, 32776456, 32844106], [31, 31744, 1015808, 2164802, 8659208, 32472030, 32641156]], [[31, 992, 31744, 1082401, 2164802, 5215204, 17318416], [31, 31744, 1015808, 1082401, 2164802, 4330468, 17318431], [992, 31744, 1015808, 1082401, 8659208, 32573506, 33114706]], [[31, 736, 31744, 1015808, 1082401, 2164802, 4329604], [31, 992, 31744, 1082401, 2164802, 5214340, 33047056], [31, 992, 31744, 1082401, 2164802, 17809936, 26207000], [31, 992, 31744, 1113121, 4329604, 8659208, 33047056], [256, 31744, 1015808, 1082401, 2164802, 4329604, 32573506], [31744, 1015808, 1082401, 2164802, 4329604, 17333791, 32505856]], [[31, 992, 1082401, 2164802, 8659208, 9412872, 33047056], [31, 31744, 1015808, 1082401, 2164802, 4329604, 32506112], [31, 31744, 1015808, 1082401, 2164802, 4329860, 32505856]], [[31, 992, 1082401, 2164802, 5214340, 17318416, 17333776], [288, 31744, 1015808, 1082401, 2164802, 4329604, 32505856]], [[31, 31744, 1015808, 1082401, 2165730, 8659208, 18400817], [31, 31744, 1015808, 2164802, 4330468, 12989420, 17318416]], [[31, 992, 31744, 1015808, 1082401, 10824010, 25977624], [31, 992, 31744, 1015808, 2164802, 9741609, 25977624], [31, 992, 31744, 1015808, 9741609, 10824010, 17318416], [31, 31744, 1015808, 1082401, 8659208, 29224827, 32573506], [31, 31744, 1047552, 1082401, 2164802, 4329604, 32776456], [31744, 31775, 1015808, 1082401, 2164802, 4329604, 32776456]], [[31, 992, 31744, 1082401, 2164831, 17318416, 32776456], [31, 992, 1048575, 1113121, 2164802, 4329604, 17318416], [31, 31744, 1015808, 1082401, 2164802, 9741609, 32641156], [31, 31744, 1015808, 1082401, 3247203, 8659208, 32641156], [31, 31744, 1082401, 2164802, 8659208, 8659944, 17809936], [31744, 1015808, 1082401, 2164802, 4329604, 24895231, 32505856]], [[31, 992, 31744, 1082401, 4329604, 25977624, 33047056], [31, 992, 31744, 1082401, 8659208, 21648020, 33047056]], [[31, 31744, 1015808, 1082401, 2164802, 32776456, 33317656]], [[31, 992, 31744, 1082401, 2164802, 4330468, 17809936], [31, 992, 1082401, 2164802, 5214340, 8659208, 8682760]], [[31, 31744, 32736, 1082401, 2164802, 5214340, 17318416], [992, 31744, 2065441, 4329604, 8659208, 32573506]], [[31, 992, 31744, 1082401, 2164802, 9412872, 25977624], [31, 992, 31744, 1082401, 2194498, 4329604, 33047056]], [[31, 992, 1082401, 2164802, 4329604, 8682760, 9412872], [31, 992, 1082401, 2164802, 4329604, 17333776, 17809936], [31, 31744, 1015808, 1082401, 2164802, 16236015, 32776456], [31, 31744, 1015808, 1082401, 17318416, 32573506, 32708806]], [[31, 992, 31744, 1082401, 4329604, 10824010, 32776456], [31, 31744, 1015808, 1082401, 2164802, 32641156, 32911756], [543, 31744, 1015808, 1082401, 2164802, 4329604, 32505856]], [[31, 992, 31744, 1015808, 2164802, 12988812, 21648020], [31, 31744, 1015808, 1082401, 2165730, 8659944, 17318416]]], [[[31, 992, 1048575, 1082401, 2164802, 4329604, 8682760], [31, 31744, 1015808, 1082401, 2164802, 8659208, 32641156], [31744, 1015808, 1082401, 2164802, 4329604, 32776456, 33554400]], [[31, 992, 31744, 1082401, 4329604, 24895223, 33047056], [31, 992, 31744, 1082401, 17318416, 32573506, 32776456], [31, 992, 31744, 1082401, 17318416, 32641156, 32708806]], [[31, 992, 31744, 1082401, 8659208, 10824010, 17809936]], [[31, 992, 31744, 1082401, 17318416, 19483218, 32641156], [31, 992, 1048575, 2164802, 4329604, 8659208, 17333776]], [[31, 992, 31744, 1082401, 4329604, 17318416, 32911756], [31, 31744, 32736, 1082401, 2164802, 4329604, 17809936], [31, 31744, 1015808, 1082401, 8659208, 32573506, 33114706], [992, 31744, 31775, 1082401, 2164802, 4329604, 17809936], [992, 31744, 1015808, 1082401, 2164802, 8659231, 32641156], [992, 31744, 1015808, 1082401, 10824010, 19483218, 32505856]], [[31, 31744, 1082401, 2065441, 4329604, 8659208, 32573506]], [[31, 31744, 1015808, 1082401, 2164802, 4330468, 12988812], [31, 31744, 1015808, 2164802, 4329604, 8659944, 19483218], [31, 31744, 1015808, 2164802, 4330468, 5412005, 8659208], [31, 31744, 1015808, 2164802, 6494406, 8659944, 17318416]], [[31, 31744, 1015808, 1082401, 2165730, 8659208, 16236015]], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329860], [31, 992, 31744, 1015808, 1082657, 2164802, 4329604], [31, 992, 31744, 1016064, 1082401, 2164802, 4329604], [31, 992, 31744, 1082401, 2164802, 8659208, 26207000], [31, 31744, 1015808, 1082401, 17318416, 29224827, 32776456], [31, 31744, 1082401, 2164802, 5214340, 8659208, 33525892], [256, 1023, 31744, 1015808, 1082401, 2164802, 4329604], [287, 992, 31744, 1015808, 1082401, 2164802, 4329604]], [[31, 31744, 1082401, 2164802, 4330468, 5214340, 8659208]], [[31, 992, 31744, 1082401, 8659208, 19483218, 33047056], [31, 31744, 1082401, 2165730, 8659208, 17809936]], [[31, 256, 992, 31744, 1082401, 2164802, 5214340], [31, 992, 31744, 913275, 1082401, 2164802, 17318416], [31, 992, 31744, 1082401, 4329604, 8659208, 33317656], [31, 992, 31744, 1082401, 5214340, 8659208, 21648020], [31, 992, 31744, 1082401, 5214340, 12988812, 17318416], [31, 992, 31744, 5214340, 5412005, 8659208, 17318416], [31, 992, 1082401, 2164802, 8659208, 17809936, 17825296], [31, 31744, 1015808, 1082401, 2164802, 5215204, 17318416], [992, 31744, 1015808, 1082401, 2164802, 8659208, 32708806]], [[31, 31744, 1082401, 2164802, 4329604, 4330468, 9412872]], [[31, 992, 31744, 1082401, 8659208, 32573506, 32641156], [31, 992, 1082401, 2194498, 5214340, 17318416], [992, 31744, 1015808, 1082401, 2164802, 8682760, 32641156], [992, 31744, 1015808, 3247203, 8659208, 18400817, 32505856]], [[31, 31744, 2065441, 4329604, 8659208, 32573506], [992, 31744, 1082401, 2164802, 4329604, 17809936, 33554400]], []], [[[31, 992, 31744, 1082401, 2165730, 9412872, 17318416], [31, 31744, 1015808, 1082401, 2165730, 6494406, 17318416], [31, 31744, 1082401, 2164802, 8659208, 17809936, 33553439]], [[31, 992, 31744, 1015808, 6494406, 8659208, 19483218], [31, 992, 31744, 1015808, 6494406, 10824010, 17318416], [31, 992, 1082401, 1113121, 2164802, 4329604, 32776456], [31, 31744, 1015808, 1082401, 2164831, 17318416, 32776456], [31, 31744, 1015808, 1082401, 8659208, 25977624, 32573506], [31, 31744, 1015808, 2164802, 4330468, 17318416, 24895223]], [[31, 992, 31744, 1082401, 8659208, 17333776, 32641156], [31, 31744, 1015808, 1082431, 2164802, 17318416, 32776456]], [[31, 992, 31744, 1016320, 1082401, 2164802, 4329604], [31, 992, 31744, 1082401, 2164802, 17809936, 22008468], [31, 31744, 1015808, 2164802, 4329604, 8659208, 17318896, 32539681], [543, 992, 31744, 1015808, 1082401, 2164802, 4329604]], [[31, 992, 31744, 1082401, 4330468, 8659208, 33047056], [31, 992, 1047552, 1113121, 2164802, 4329604, 8659208], [31, 31744, 1015808, 1082401, 2164802, 4330468, 17809936], [992, 31744, 1015808, 1082401, 8659208, 32573506, 32641156]], [[31, 992, 31744, 1082401, 8659208, 25977624, 32641156]], [[31, 992, 31744, 1082401, 2165730, 8659208, 17809936]], [[31, 992, 1047552, 1082401, 2164802, 4329604, 17333776], [31, 31744, 1015808, 1082401, 2164802, 8659231, 32641156], [31, 31744, 1015808, 1082401, 10824010, 19483218, 32505856], [31, 31744, 1015808, 1113121, 2164802, 17318416, 32641156]], [[31, 31744, 1015808, 1082401, 2164802, 12988812, 32776456], [31, 31744, 1015808, 2164802, 4329604, 8659944, 17318416]], [[31, 992, 31744, 1082401, 2194498, 8659208, 32641156], [31, 31744, 1015808, 1082401, 2165730, 5412005, 17318416], [31, 31744, 1016800, 2065441, 2164802, 4329604, 8659208], [992, 31744, 1015808, 1082401, 2164802, 9412872, 32641156], [992, 31744, 1015808, 1082401, 8659208, 17333776, 32641156], [992, 31744, 1015808, 2164802, 4329604, 8659208, 17318431, 32539681]], [[31, 992, 31744, 1082401, 2164802, 5214340, 17333776], [31, 992, 31744, 2065441, 4329604, 8659208, 32573506]], [[31, 31744, 1015808, 1082401, 17318416, 32573506, 32776456], [31, 31744, 1082401, 2164802, 5214340, 8659208, 32776456]], [[992, 31744, 1015808, 1113121, 4329604, 8659208, 32573506]], [[31, 992, 1082401, 2164802, 4329604, 8682760, 9436424], [31, 31744, 1015808, 1082401, 17318416, 19483218, 32641156], [31, 31744, 1015808, 2164802, 17318416, 18400817, 32641156], [31, 31744, 1082401, 1083361, 2164802, 4329604, 32776456]], [[31, 31744, 32736, 1082401, 4329604, 8659208, 33047056], [31, 31744, 1015808, 1082401, 2164802, 8659208, 32708806], [31, 31744, 1082401, 2164802, 4329604, 9412872, 32776456], [992, 31744, 31775, 1082401, 4329604, 8659208, 33047056]], [[31, 992, 31744, 1082401, 17318416, 32641156, 32776456], [31, 31744, 1015808, 1083361, 2164802, 8659944, 17318416], [31, 31744, 1015808, 2164802, 4330468, 5412837, 17318416], [31, 31744, 1015839, 1082401, 2164802, 8659208, 32641156]]], [[[31, 31744, 1015808, 1082401, 2164802, 8682760, 32641156], [31, 31744, 1015808, 3247203, 8659208, 18400817, 32505856], [31, 31744, 1015808, 3247203, 9741609, 17318416, 32505856], [992, 31744, 1015808, 1082401, 2194498, 8659208, 32641156]], [[31, 31744, 1015808, 1082401, 2164802, 8659944, 19483218], [31, 31744, 1015808, 2164802, 3247203, 8659944, 17318416], [31, 31744, 1015808, 2164802, 4329604, 8659944, 16236015]], [[31, 992, 31744, 1082401, 4329604, 6494406, 32776456]], [[31, 992, 31744, 1082401, 2164802, 4329604, 17825296], [31, 31744, 1015808, 2164802, 8659944, 17318416, 32472030]], [], [[31, 31744, 913275, 1015808, 1082401, 2164802, 17318416]], [[31, 992, 31744, 1082401, 2164802, 5214340, 24895223], [31, 992, 31744, 1082401, 8659208, 32641156, 33182356], [31, 31744, 1015808, 1082401, 2164802, 17809936, 32776456]], [[31, 544, 31744, 1015808, 1082401, 2164802, 4329604], [31, 992, 31744, 1113121, 4329604, 17318416, 32776456], [31, 31744, 1015808, 1082401, 8659208, 32573506, 32641156], [992, 31744, 1015808, 1082401, 2164802, 32641156, 33047056]], [[31, 992, 31744, 5214340, 8659208, 17318416, 31389629], [31, 992, 1082401, 2164802, 9412872, 17318416, 32776456], [992, 31744, 1015808, 1082401, 6494406, 19483218, 32505856], [992, 31744, 1015808, 2164802, 4329631, 8659208, 16236015], [31744, 1015808, 1082401, 2164802, 4329604, 16236000, 32505856]], [[31, 31744, 1015808, 1082401, 2164802, 8659208, 33525892]], [[31, 31744, 1015808, 1082401, 2164802, 8659944, 18400817], [31, 31744, 1015808, 1082401, 2165730, 9412872, 17318416], [31, 31744, 1015808, 1082401, 3247203, 8659944, 17318416]], [[31, 992, 31744, 4329604, 9412872, 17318416, 31389629], [31, 1047552, 1082401, 2164802, 4329604, 8659208, 32537600]], [[31, 992, 31744, 1015808, 1082401, 10824010, 19483218], [31, 992, 31744, 1015808, 3247203, 8659208, 19483218], [31, 992, 31744, 1015808, 3247203, 10824010, 17318416], [31, 31744, 1015808, 1082401, 2164802, 9412872, 32641156], [31, 31744, 1015808, 1082401, 8659208, 17333776, 32641156]], [[31, 992, 31744, 1082401, 17318416, 21648020, 32776456], [31744, 1015808, 1048575, 1082401, 2164802, 4329604, 17318431]], [[31, 992, 31744, 1082401, 4329604, 19483218, 33047056], [31, 31744, 1082401, 2165730, 4329604, 17809936]], [[31, 31744, 1015808, 1113121, 4329604, 8659208, 32573506]]], [[[31, 31744, 1015808, 1082401, 2165730, 8659208, 17809936]], [[31, 992, 31744, 1082401, 2165730, 5214340, 17318416], [31, 992, 31744, 4329604, 8659208, 17809936, 31389629], [31, 992, 1113121, 8659208, 17318416, 32641156]], [[31, 992, 31744, 1082401, 2164802, 9412872, 19483218], [31, 31744, 1082401, 2164802, 5214340, 5215204, 8659208], [992, 31744, 1015808, 1082401, 8659208, 32573506, 32708806]], [[31, 31744, 1015808, 1082401, 2164802, 8659944, 17318416], [31, 31744, 1015808, 1082401, 2194498, 8659208, 32641156], [31, 31744, 1015808, 2164802, 4329631, 8659944, 17318416]], [[31, 992, 31744, 1082401, 2164802, 9412872, 26207000], [31, 31744, 1082401, 2164802, 4329604, 17809936, 33553439], [256, 31744, 1015808, 1082401, 2164802, 32641156], [992, 31744, 1015808, 1082401, 8659208, 19483218, 32573506]], [[31, 992, 31744, 1015808, 2164802, 9741609, 18400817], [31, 992, 31744, 1015808, 3247203, 8659208, 18400817], [31, 992, 31744, 1015808, 3247203, 9741609, 17318416], [31, 31744, 1082401, 2065441, 2164802, 8659208, 32641156], [31, 31744, 1082401, 4329604, 8659208, 8659944, 33047056]], [], [[992, 31744, 1015808, 2164802, 8659208, 21648020, 32641156]], [[31, 31744, 1015808, 2164802, 4329604, 8683496, 17318416]], [[31, 992, 31744, 1082401, 8659208, 21648020, 32641156], [31, 992, 31744, 1082401, 12988812, 17318416, 32641156], [31, 31744, 1015808, 1082401, 17318416, 32573506, 32844106]], [[31, 992, 31744, 1082401, 2165730, 4329604, 17809936], [31, 31744, 1015808, 1082401, 2164802, 32641156, 33047056], [31, 31744, 1015808, 1082401, 2164802, 32776456, 32911756], [992, 31744, 1015808, 1082401, 10824010, 12988812, 32505856]], [[31, 992, 31744, 777975, 1082401, 2164802, 4329604], [31, 992, 31744, 1082401, 2164802, 9412872, 18400817], [31, 992, 31744, 1082401, 3247203, 9412872, 17318416], [31, 992, 1082401, 2164802, 9412872, 33047056], [31, 31744, 1015808, 1082401, 6494406, 19483218, 32505856]], [[31, 31744, 1015808, 1082401, 2164802, 8659944, 16236015], [992, 31744, 1082401, 1082431, 2164802, 4329604, 32776456]], [[31, 992, 31744, 1082401, 2164802, 5412005, 32776456], [31, 992, 31744, 1082401, 3247203, 4329604, 32776456], [31, 992, 31744, 1082401, 4329604, 8659208, 33062416], [31, 31744, 1082401, 4330468, 17318416, 32776456], [31744, 1015808, 1082401, 2164802, 4329604, 17318431, 32505856]], [[31, 992, 31744, 1015808, 2164802, 5412005, 21648020], [31, 31744, 1015808, 2164802, 8659944, 17318416, 29224827]], [[31, 992, 31744, 1082401, 17318416, 19483218, 32776456], [31, 992, 1048575, 1113121, 2164802, 4329604, 8659208], [31, 31744, 1082401, 2164802, 4329604, 5214340, 32776456]]], [[[31, 992, 31744, 1082401, 8659208, 12988812, 33047056], [31, 992, 31744, 4329604, 8659208, 9741609, 33047056], [31, 32736, 1047552, 1082401, 2164802, 4329604, 8659208], [256, 992, 31744, 1015808, 1082401, 2164802, 32641156]], [[31, 992, 31744, 1082401, 2164802, 5214340, 21648020], [31, 992, 31744, 1082401, 2164802, 9741609, 17809936], [31, 992, 31744, 1082401, 3247203, 8659208, 17809936], [31, 31744, 1015808, 1113121, 2164802, 4330468, 17318416], [31, 31744, 1015808, 1113121, 4329604, 17318416, 32776456], [31, 31744, 1015808, 2164802, 5214340, 8659944, 17318416]], [[8, 31744, 1015808, 1082401, 8659208, 17318416, 32573506], [31, 992, 1048575, 1082401, 2164802, 4329604, 17333776]], [[31, 992, 1047552, 2164802, 4329604, 8682760, 17318416], [31, 31744, 32736, 1082401, 2164802, 5214340, 8659208], [992, 31744, 31775, 1082401, 2164802, 5214340, 8659208]], [[31, 992, 31744, 1082401, 2164802, 9412872, 17318416], [31, 31744, 1015808, 3247203, 5412005, 17318416, 32505856], [31744, 1015808, 1082401, 2164802, 4329604, 32506848, 32776456]], [[31, 992, 31744, 1082401, 2164802, 9413608, 17318416], [31, 992, 31744, 1082401, 4329604, 33047056, 33317656], [31, 31744, 1015808, 1082401, 8659208, 32573506, 32708806], [992, 31744, 1015808, 1082401, 2164831, 8659208, 16236015]], [[31, 992, 31744, 1082401, 9412872, 17318416, 31389629], [31, 31744, 32736, 1082401, 2164802, 4329604, 9412872], [31, 31744, 1015808, 2164802, 8659944, 12989420, 17318416], [992, 31744, 31775, 1082401, 2164802, 4329604, 9412872], [992, 31744, 1082401, 2164802, 4329604, 4329631, 17809936]], [[31, 31744, 1015808, 1082401, 8659208, 19483218, 32573506], [31, 31744, 1015808, 1082401, 8659944, 17318416, 29224827], [31, 31744, 1015808, 1082401, 10824010, 17318416, 32573506], [31, 31744, 1015808, 2164802, 4330468, 17318416, 18400817]], [[31, 992, 31744, 1082401, 4329604, 31389629, 32776456], [31, 31744, 1015808, 1082401, 2165730, 17318416, 29224827], [992, 31744, 1082401, 2164831, 8659208, 17809936]], [[8, 31744, 1015808, 1082401, 2164802, 4329604, 32776456], [31, 992, 31744, 1082401, 4330468, 17318416, 32776456], [31, 992, 31744, 1082401, 8659208, 32641156, 32708806], [31, 992, 31744, 1083361, 8659208, 17318416, 32641156]], [[31, 992, 31744, 1082401, 2164802, 8659208, 17809936], [31, 992, 31744, 1082401, 4329604, 6494406, 17809936], [31, 992, 31744, 1082401, 4329604, 32776456, 33047056], [31, 31744, 1015808, 2164802, 8659208, 21648020, 32641156], [31, 31744, 1015808, 2164802, 12988812, 17318416, 32641156], [31, 31744, 1082401, 2164802, 4329604, 9412872, 33530120]], [[31, 992, 31744, 1082401, 2164802, 8659944, 17809936], [31, 31744, 1015808, 1082401, 2165730, 5214340, 17318416]], [[31, 992, 31744, 1082401, 8659208, 17809936, 31389629], [992, 31744, 1015808, 1113121, 2164802, 8659208, 32641156], [31744, 1015808, 1082401, 2164802, 2164831, 4329604, 32776456]], [[31, 992, 31744, 1082401, 2164802, 4329604, 22008468], [31, 992, 31744, 1082401, 2164802, 9412872, 16236015], [31, 31744, 1015808, 1082401, 10824010, 12988812, 32505856], [31, 31744, 1015808, 2164802, 4330468, 8659208, 17333776]], [[31, 31744, 1015808, 1082401, 2164802, 6494406, 32776456], [31, 31744, 1015808, 2164802, 3247203, 4329604, 32776456], [31, 31744, 1082401, 4329604, 8659208, 33047056, 33553439]], [[992, 31744, 1015808, 1082401, 2164802, 17333776, 32641156], [992, 31744, 1015808, 1082401, 8659208, 16236015, 32573506]]], [[[31, 992, 31744, 1015808, 1082401, 6494406, 19483218], [31, 992, 31744, 1015808, 3247203, 6494406, 17318416], [31, 992, 32736, 1082401, 2164802, 9412872, 17318416], [31, 31744, 1015808, 1082401, 2164831, 8659944, 17318416], [31, 31744, 1015808, 1082401, 8659208, 18400817, 32573506], [31, 31744, 1015808, 2164802, 4329604, 32472030, 32776456], [31, 31744, 1015808, 2164802, 4330468, 8659208, 25977624], [992, 31744, 1082401, 2164802, 4329604, 9412872, 33554400]], [[31, 31744, 1015808, 1082401, 2165730, 6495206, 17318416], [31, 31744, 1015808, 1082431, 2164802, 8659944, 17318416], [992, 31744, 1015808, 2164802, 4329631, 8659208, 17809936]], [[31, 992, 31744, 1082401, 8659208, 10824010, 33047056], [31, 31744, 1082401, 8659944, 17318416, 32641156]], [[31, 256, 31744, 1015808, 1082401, 2164802, 32641156], [31, 992, 31744, 913275, 1082401, 2164802, 8659208], [31, 992, 31744, 1082401, 2164802, 5214340, 19483218], [31, 992, 1082401, 1113121, 4329604, 8659208, 33047056], [31, 31744, 32736, 1082401, 4329604, 17318416, 32776456]], [[31, 992, 31744, 1082401, 8659208, 18400817, 32641156], [31, 992, 31744, 1082401, 9741609, 17318416, 32641156], [31, 992, 1082401, 2164802, 9412872, 17318416, 33530120]]]]
  | 8 => [[[], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 16236015, 32505856]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 8659944]], [[31, 31744, 1015808, 1082401, 2164802, 2165730, 4329604, 8659208]], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 18400817], [31, 992, 31744, 1015808, 1082401, 2164802, 5412005, 17318416]], [], [[31, 992, 31744, 1015808, 1082401, 2164831, 8659208, 17318416], [31, 31744, 1015808, 1082401, 2164802, 8659208, 17809936, 32505856]], [[31, 992, 31744, 1015808, 1082431, 2164802, 8659208, 17318416], [31, 31744, 1015808, 1082401, 2164802, 4329604, 17318431, 32505856]], [[31, 992, 31744, 1082401, 8659208, 17318416, 32641156]], [], [], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 32776456]], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 17318416], [31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 12988812], [31, 992, 31744, 1015808, 2164802, 4329604, 8659208, 9741609]], [], []], [[[31, 992, 31744, 1015808, 1082401, 8659208, 17318416, 32573506], [31, 992, 31744, 1082401, 2164802, 5214340, 17318416]], [], [], [[31, 992, 31744, 1082401, 2164802, 4329604, 8659208, 9412872]], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 9412872, 17318416]], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 16236015], [31, 992, 31744, 1048575, 1082401, 2164802, 4329604, 8659208], [31, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 32573506]], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 32776456], [31, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 32505887]], [], [[31, 992, 31744, 1016800, 1082401, 2164802, 4329604, 17318416], [31, 992, 31744, 1082401, 2164802, 4329604, 17809936]], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 17809936], [31, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 33553439]], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 17318431]], [[992, 31744, 1015808, 1048575, 1082401, 2164802, 4329604, 8659208]], [], []], [[], [], [], [], [[992, 31744, 1015808, 1082401, 2164802, 4329604, 9741609, 32505856]], [], [], [], [], [[8, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32505856]], [], [], [[31, 992, 31744, 1015839, 1082401, 2164802, 4329604, 17318416], [31, 1023, 31744, 1015808, 1082401, 2164802, 4329604, 17318416]], [[992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32505856]], [], []], [[[31, 31744, 1015808, 1048575, 1082401, 2164802, 4329604, 8659208]], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 17318416, 29224827], [31, 992, 31744, 1015808, 2164802, 4329604, 17318416, 25977624], [31, 992, 31744, 1015808, 2164802, 8659208, 17318416, 21648020], [31, 992, 31744, 1082401, 4329604, 8659208, 33047056]], [[31, 992, 31744, 1082401, 2164802, 4329604, 5214340, 8659208]], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 5214340, 17318416], [31, 992, 31744, 1015808, 1113121, 4329604, 8659208, 17318416]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 9741609, 32505856], [31, 31744, 1015808, 1082401, 2164802, 5412005, 8659208, 32505856]], [], [[992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32506848]], [], [], [[31, 992, 31744, 1015808, 2164802, 4329604, 17318416, 24895223]], [], [], []], [[[31, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32505856]], [[992, 31744, 1015808, 1082401, 2164802, 2164831, 4329604, 8659208]], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 10824010], [31, 992, 31744, 1015808, 1082401, 2164802, 6494406, 8659208], [31, 992, 31744, 1015808, 2164802, 3247203, 4329604, 8659208]], [[992, 31744, 1015808, 1082401, 2164802, 4329604, 8659231, 32505856]], [[31, 992, 31744, 1015808, 2164802, 4329604, 8659208, 32472030]], [], [], [], [], [], [[992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32573506]], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 9741609], [31, 992, 31744, 1015808, 1082401, 2164802, 5412005, 8659208]], [[992, 31744, 1015808, 1082401, 2164802, 4329604, 8682760, 32505856]], [[31, 992, 31744, 1015808, 1082401, 2164802, 17318416, 25977624], [31, 992, 31744, 1015808, 1082401, 8659208, 17318416, 19483218], [31, 992, 31744, 1015808, 2164802, 8659208, 17318416, 18400817]], [[31, 992, 31744, 1015808, 2164802, 4330468, 8659208, 17318416]]], [[], [], [], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208]], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 17318416, 24895223], [31, 31744, 1015808, 1082401, 2164802, 4329604, 8659231, 32505856]], [[31, 992, 31744, 1082401, 2164802, 5214340, 8659208], [31, 31744, 1015808, 1082401, 2164802, 17318416, 32641156]], [], [], [[31, 992, 31744, 1082401, 2164802, 4329604, 9412872]], [], [], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32573506]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32505887]]], [[[31, 31744, 1015808, 1082401, 2164802, 4329604, 8682760, 32505856]], [[31, 992, 31744, 1016800, 1082401, 2164802, 4329604, 8659208], [992, 1023, 31744, 1015808, 1082401, 2164802, 4329604, 8659208]], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 17318416, 32641156]], [], [[31, 31744, 1015808, 1082401, 2164802, 8659208, 29224827, 32505856]], [], [[31, 992, 31744, 1082401, 4329604, 17318416, 32776456]], [[31, 31744, 1015808, 1082401, 2164802, 5214340, 8659208, 32505856]], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 33047056]], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 8659231], [31, 992, 31744, 1015808, 1113121, 2164802, 4329604, 17318416]], [], [], []], [[[31, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 32776456]], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 17318416, 21648020], [31, 992, 31744, 1015808, 2164802, 4329604, 17318416, 18400817]], [], [[31, 992, 31744, 1015839, 1082401, 2164802, 4329604, 8659208], [31, 1023, 31744, 1015808, 1082401, 2164802, 4329604, 8659208], [256, 31744, 1015808, 1082401, 2164802, 4329604, 32505856]], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 8682760]], [], [], [[31, 992, 31744, 1015808, 2164802, 4329604, 8659208, 17333776]], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 29224827], [31, 992, 31744, 1015808, 2164802, 4329604, 8659208, 25977624], [31, 992, 31744, 1015808, 2164802, 8659208, 12988812, 17318416]], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 5214340, 8659208], [31, 992, 31744, 1082401, 2164802, 4329604, 17318416, 17809936]], []], [[[256, 992, 31744, 1015808, 1082401, 2164802, 4329604, 32505856]], [[31, 31744, 1015808, 1082401, 2164802, 8659208, 25977624, 32505856]], [[31, 31744, 1015808, 1082401, 2164802, 4330468, 17318416]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 32537600]], [], [], [], [], [], [], [], [], [], [[992, 31744, 1015808, 1082401, 2164802, 8659208, 32641156]], [[31, 992, 31744, 1015808, 1082401, 2164802, 4330468, 17318416]], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 33047056], [992, 31744, 1015808, 1082401, 2164802, 4329604, 17333776, 32505856]]], [[], [], [], [[31, 256, 31744, 1015808, 1082401, 2164802, 4329604, 32505856]], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 25977624], [31, 992, 31744, 1015808, 1082401, 8659208, 10824010, 17318416], [31, 992, 31744, 1015808, 2164802, 8659208, 9741609, 17318416]], [], [[31, 992, 31744, 1047552, 1082401, 2164802, 4329604, 17318416], [31, 31744, 32736, 1015808, 1082401, 2164802, 4329604, 17318416]], [], [], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 17318896, 32505856], [992, 31744, 1015808, 1082401, 2164802, 4329604, 24895223, 32505856]], [], [], [], []], [[[31, 992, 31744, 1015808, 1082401, 2164802, 17318416, 32776456], [31, 31744, 1015808, 1082401, 2164802, 8659208, 32641156]], [[992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 17318431, 32505856]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 17333776, 32505856]], [], [], [], [], [], [[31, 256, 992, 31744, 1015808, 1082401, 2164802, 4329604]], [], [[31, 992, 31744, 1015808, 1082401, 2165730, 8659208, 17318416]], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 32641156]], [], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 24895223, 32505856]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 8659944, 17318416]]], [[[31, 31744, 1015808, 1082401, 2164802, 2165730, 4329604, 17318416]], [[31, 992, 31744, 1015808, 2164802, 4329604, 8659208, 19483218], [31, 992, 31744, 1015808, 2164802, 4329604, 10824010, 17318416], [31, 992, 31744, 1015808, 2164802, 6494406, 8659208, 17318416]], [[8, 31744, 1015808, 1082401, 2164802, 8659208, 17318416, 32505856]], [], [[31, 992, 31744, 1015808, 1113121, 2164802, 4329604, 8659208]], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 17333776]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32776456], [31, 31744, 1015808, 2164802, 4329604, 8659944, 17318416], [992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32537600]], [], [], [], [], [], [], []], [[[31, 992, 31744, 1082401, 2164802, 4329604, 9412872, 17318416], [31, 31744, 1015808, 1082401, 2164802, 8659208, 18400817, 32505856]], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 24895223], [31, 992, 31744, 1015808, 2164802, 4329604, 8659208, 17318416], [31, 992, 31744, 1048575, 1082401, 2164802, 4329604, 17318416]], [[31, 992, 31744, 1015808, 2164802, 4329604, 8659944, 17318416]], [], [[31, 992, 31744, 1082401, 2164802, 4329604, 8659208, 17809936]], [], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 33553439]], [[31, 992, 31744, 1015808, 2164802, 4329604, 8659208, 17318416, 32539681]], [[31, 992, 31744, 1015808, 1083361, 2164802, 8659208, 17318416]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32537600]], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 19483218], [31, 992, 31744, 1015808, 1082401, 2164802, 10824010, 17318416], [31, 992, 31744, 1015808, 2164802, 3247203, 8659208, 17318416], [31, 992, 31744, 1015808, 2164802, 4329604, 8659208, 16236015]], [], [[31, 992, 31744, 1015808, 2164802, 8659208, 17318416, 32472030]], []], [[], [[992, 31744, 1015808, 1082401, 2164802, 4329604, 18400817, 32505856]], [[31, 31744, 1015808, 1082401, 2164802, 8659208, 16236015, 32505856]], [[31, 31744, 1015808, 1082401, 2164802, 8659944, 17318416]], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 18400817], [31, 992, 31744, 1015808, 1082401, 2164802, 9741609, 17318416], [31, 992, 31744, 1015808, 1082401, 3247203, 8659208, 17318416]], [[8, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 32505856]], [], [], [], [], [], [], [[31, 31744, 1015808, 1048575, 1082401, 2164802, 4329604, 17318416], [31744, 1015808, 1082401, 2164802, 4329604, 17318431, 32505856]], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 17318416], [31, 992, 31744, 1015808, 2164802, 4329631, 8659208, 17318416]], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659944, 17318416]]], [[[31, 992, 31744, 1047552, 1082401, 2164802, 4329604, 8659208], [31, 31744, 32736, 1015808, 1082401, 2164802, 4329604, 8659208], [992, 31744, 31775, 1015808, 1082401, 2164802, 4329604, 8659208]], [[31, 992, 31744, 1082401, 2164802, 4329604, 5214340, 17318416]], [], [[31, 992, 31744, 1015808, 2164802, 4329604, 8682760, 17318416], [992, 31744, 1015808, 1082401, 2164802, 4329604, 16236015, 32505856]], [[31, 992, 31744, 1082401, 2164802, 9412872, 17318416], [31, 31744, 1015808, 1082401, 2164802, 4329604, 18400817, 32505856]], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 16236015]], [], [[31, 992, 31744, 1015808, 2164802, 8659208, 17318416, 29224827], [992, 31744, 1015808, 1082401, 2164802, 4329604, 17318431, 32505856]], [[31, 992, 31744, 1082401, 2164802, 8659208, 17809936], [992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 33554400]], [], [[31, 992, 31744, 1015808, 2164802, 5214340, 8659208, 17318416]], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 32505856], [31, 31744, 1015808, 1082401, 2164802, 8659208, 12988812, 32505856]], [[31, 992, 31744, 1015808, 1083361, 2164802, 4329604, 17318416]], []], [[[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 19483218], [31, 992, 31744, 1015808, 1082401, 2164802, 6494406, 17318416], [31, 992, 31744, 1015808, 2164802, 3247203, 4329604, 17318416]], [], [[31, 992, 31744, 1015808, 1082401, 8659208, 17318416, 29224827], [31, 992, 31744, 1015808, 2164802, 4329604, 17318416, 32472030]], [], []]]
  | 9 => [[[], [], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 32505856]], [], [], [], [], [], [], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 17318416]], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [[992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32505856]], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[[31, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32505856]], [], [], [], [], [], [], [], [], [], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32505856]], [], [], []], [[], [], [], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208]], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 17318416, 32505856]], [], [], [], [], [], [], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 17318416]], [], [], [], [], []], [[], [], [], [[31, 992, 31744, 1015808, 2164802, 4329604, 8659208, 17318416]], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [[31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 17318416]], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [[31, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 32505856]], [], []], [[], [], [], [], []]]
  | _ => []

def rowsOf (s : Nat) : List (List (List Nat)) := (fast s).flatten

def fastGet (s k : Nat) : List (List Nat) := ((fast s).getD (k / 16) []).getD (k % 16) []

theorem getD_mem2 {α : Type} {L : List (List α)} {i : Nat} {x : α} (h : x ∈ L.getD i []) : L.getD i [] ∈ L := by
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ (by omega)] at h
    cases h

set_option maxRecDepth 100000 in
theorem lenOK : ∀ s, s ≤ 9 → (rowsOf s).length ≤ 245 := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem fast_in {s k : Nat} {l : List Nat} (hs : s ≤ 9) (h : l ∈ fastGet s k) :
    ∃ i, i < 245 ∧ l ∈ (rowsOf s).getD i [] := by
  have h1 : fastGet s k ∈ (fast s).getD (k / 16) [] := getD_mem2 h
  have h2 : (fast s).getD (k / 16) [] ∈ fast s := getD_mem2 h1
  have h3 : fastGet s k ∈ rowsOf s := List.mem_flatten.2 ⟨_, h2, h1⟩
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 h3
  refine ⟨i, Nat.lt_of_lt_of_le hi (lenOK s hs), ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he]
  exact h

set_option maxRecDepth 100000 in
def hintOf : Nat → List (List (List Nat))
  | 4 => [[[], [], [], [], [], [], [1], [], [], [], [], [], [], [], [1], [], [], [1], [], [], [], [], [1], [0], [], [], [], [0], [], [], [], []], [[], [], [], [], [], [], [], [], [0], [], [7], [], [], [], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [2], [], [], [0], [], [10], [], [], [], [], [], [], [], [], [], [], [], [], [], [2], [], [], [], [4], [], [], [1], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [2], [], [4], [], [], [], [], [], [], [], [], [1], [4], [], [], [], [11], [0, 1], [11], [], []], [[], [11], [], [0], [], [], [], [0], [2], [], [], [], [], [], [], [], [], [], [], [6], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [1], [], [], [], [], [], [], [], [0], [], [], [6], [], [0], [], [], [], [], [], [], [4], []], [[], [1], [], [], [], [], [], [], [], [0], [], [], [], [], [9], [0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [0], [], [], [], [], [], [], [], [], [0], [], [10], [], [], [], [], [], [], [7], [], [], [9], [], [], [], [], [], [], [3], [], []], [[0], [], [], [], [1], [], [], [], [], [], [2], [], [], [], [], [], [], [], [], [], [], [0], [], [], [], [7], [], [], [], [0], [], []], [[], [], [], [], [], [], [11], [], [], [], [], [1], [], [], [], [], [9], [], [], [], [], [], [], [], [], [], [], [], [2], [], [], []], [[9], [], [], [], [], [], [], [], [], [], [], [2], [], [], [], [], [], [], [], [9], [4], [], [], [], [], [], [9], [1], [], [], [4], []], [[], [], [], [], [], [], [10], [], [], [2], [], [1], [], [], [], [], [], [9], [], [], [0], [], [], [], [], [], [], [], [], [1], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [9], [], [], [], [2], []], [[6], [], [2], [], [], [], [9], [], [], [4], [6], [], [], [], [], [], [], [11], [], [], [], [], [2], [], [1], [], [], [], [], [], [4], []], [[3], [2], [1], [], [], [], [], [], [4], [], [11], [], [], [1], [], [], [], [], [], [], [], [], [0], [], [9], [0], [0], [], [], [], [], []], [[], [], [], [], [], [], [], [], [10], [0], [], [], [], [], [1], [], [], [], [], [], [], [], [], [0], [], [], [], [0], [], [10], [], []], [[], [], [], [0], [0], [], [], [], [0], [], [], [4, 5], [], [], [], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [1], [], [4], [], [], [], [], [], [], [], [], [], [9], [], [2], [], [0], [], [], [], [], [2], [], [], [], [], []], [[], [], [], [], [], [], [1], [], [], [], [], [], [], [0], [], [], [], [2, 9], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [0], [], [], [], [], [], [], [11], [0], [], [2], [], [], [0], [1], [], [], [], [0], [], [], [], [], [2], []], [[], [], [], [], [], [], [9], [], [], [], [], [], [], [], [], [], [], [7], [], [], [], [], [], [], [], [], [], [1, 11], [], [], [], [6]], [[], [], [], [], [], [2], [11], [], [], [], [], [], [], [], [], [], [], [1], [], [], [], [], [2], [], [], [], [], [], [], [], [], []], [[], [], [], [], [2], [], [], [], [], [], [], [], [], [10], [], [], [], [], [], [], [], [0], [2], [], [], [1], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [], [], [], [], [1], [], [], [], [], [], [], [1], [], [4], []], [[], [], [], [], [], [], [], [], [], [], [2], [], [], [1, 9], [], [], [], [], [], [], [11], [], [], [], [], [], [], [], [], [], [0, 4], []], [[], [], [], [], [], [], [], [], [10], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [4], [9], [], [], [], [], [], []], [[], [], [], [], [11], [], [], [], [], [], [], [], [], [], [10], [], [], [], [], [11], [], [], [], [], [], [], [2], [], [], [], [], []], [[], [9], [], [], [], [], [11], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2], [], [], [], [0], [], [11], [4], []], [[1], [1], [], [], [], [], [], [], [], [], [1], [], [], [11], [], [], [], [], [0, 1], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [2], [], [], [7], [], [], [0], [4], [], [], [0], [2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[0], [], [1], [], [9], [], [], [11], [], [], [], [], [], [4], [5], [], [], [0, 2], [], [0], [], [], [], [], [2, 4], [], [], [], [], [], [], []], [[], [10], [], [], [], [1], [4], [], [], [], [], [], [], [7], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]]
  | 5 => [[[4], [], [2], [], [0, 1], [], [], [3, 4], [], [], [4], [6], [2], [7], [11], [7, 8], [6], [], [2, 6], [1], [0], [8], [1], [0, 1, 8], [2], [0], [2], [], [], [1], [], [0, 7]], [[0], [], [2], [], [0], [1], [0], [4, 8], [8], [2], [], [], [], [2], [], [0], [0], [], [6, 7, 11], [5], [], [], [0], [7], [], [], [], [], [], [0, 6], [], [4, 10]], [[], [6], [0, 4], [], [], [4], [0], [8], [1], [1, 6, 8], [], [5, 7], [], [0], [5], [0], [2, 6], [0, 1], [1, 2], [], [], [2], [0], [], [1], [], [10], [], [], [], [1, 6], []], [[0], [], [], [], [1], [], [4], [], [4], [2], [0], [], [10], [0, 9], [2, 11], [1, 2, 5], [], [], [4], [], [8], [2], [9], [1], [], [], [1, 4, 5], [], [], [3], [], []], [[], [], [0], [0], [], [1], [0], [], [7], [0, 2], [], [6, 10], [9], [], [], [0, 4], [8], [1, 8], [7], [0, 1], [4, 6], [], [2, 10], [0], [11], [0], [0], [], [1], [0, 6, 8], [7], []], [[], [1], [], [0], [], [], [2], [], [11], [], [2, 4], [0], [5], [], [], [], [3], [], [], [], [], [], [], [4], [1, 4], [], [], [], [], [0], [2, 3], [0, 4]], [[], [1, 2], [6], [], [0, 1, 6], [], [], [1, 10], [], [0, 1], [0, 10], [], [2], [], [2, 7, 10], [], [1, 2], [], [0], [], [], [1, 7, 11], [0, 1], [0, 2], [2], [], [], [1], [], [0], [], [0, 1, 2]], [[2], [9], [2, 6], [2], [0], [0], [], [], [2], [1], [4, 7], [], [], [4, 9], [2, 6], [1], [], [0], [0, 5], [], [4], [], [4, 10], [], [9], [2], [], [], [1, 2, 6], [2], [], [0]], [[0, 10], [], [0], [1, 2, 6, 9, 11], [4], [6], [], [], [], [0, 4], [7], [2, 5], [7], [4], [], [6], [1], [], [], [], [0, 3, 4, 10], [], [], [0], [0], [0, 1], [], [], [], [], [10], [1]], [[], [], [1], [], [], [6], [], [8], [9], [0, 9], [0], [1], [0, 2], [], [0], [], [4], [1], [0], [3], [0], [0], [0], [10], [0], [0], [8, 10], [], [], [0, 1, 3, 9], [], [0]], [[0], [], [], [], [0], [6], [], [0], [1], [2], [0, 6], [], [], [2, 7], [], [], [1], [0], [3], [0], [0], [], [], [0, 4], [0], [0], [], [], [0, 2], [], [], [0]], [[], [4], [0, 8], [0], [0], [], [], [0, 4], [2], [0, 8], [0], [3], [7], [4, 11], [], [], [1], [9], [], [1, 6, 11], [], [], [], [0], [], [], [], [], [], [2, 5], [], [1]], [[7], [0], [0], [], [], [2], [10], [], [], [7, 10], [], [5], [3, 4], [9, 10], [2, 4], [0], [], [0], [0, 6], [], [1, 2, 5], [0, 4], [0, 4], [0, 1, 4], [], [2, 5, 6, 9], [5], [5], [7], [2], [2], [0]], [[], [], [], [0], [4], [], [0], [1], [2], [6, 9], [], [], [0], [], [0], [], [0], [], [0, 3], [], [], [0, 2, 11], [1], [4], [], [], [], [], [5, 7], [0], [], [2]], [[], [11], [], [10], [], [], [0, 1], [], [4], [5], [], [], [0], [0], [2], [], [0], [], [0, 2, 5, 11], [0], [0], [4], [2], [], [5, 6], [], [], [0, 7], [0], [4, 6], [0], []], [[2, 4], [2, 8], [], [4], [0], [], [], [], [0], [9], [], [1], [], [1, 2, 4], [], [0, 1], [], [0, 2], [0], [], [], [], [0], [0, 2], [6], [0], [0, 4], [0], [7], [], [0, 3], [6]], [[], [0], [4, 5, 6], [], [2, 7], [0], [], [0], [9], [1, 9], [0, 6, 10], [7], [0, 8], [], [0], [], [2, 6], [4, 6], [1], [], [], [1], [5], [0], [4], [1], [2], [6], [], [], [], []], [[1, 6, 11], [], [2], [], [6], [11], [], [10], [], [1, 6], [4], [8], [], [2, 6], [9], [], [], [0, 9], [], [0, 10], [], [0], [1, 5, 7], [0, 6], [], [0], [5, 7], [], [], [0], [], [9]], [[], [4], [0, 2], [0], [], [0], [0, 5, 7], [], [], [7], [], [0, 2, 4, 7], [2, 6], [4], [], [10], [2, 5, 7], [], [], [0, 11], [], [6, 10], [], [], [], [0, 6], [], [1], [1], [7], [], [1, 6]], [[1], [0], [], [], [2], [8], [], [], [], [0, 2], [], [], [1], [], [], [], [7], [1], [], [], [], [7], [4], [], [0], [2, 4], [0], [0], [], [1], [], []], [[1, 4], [], [0, 2], [7], [], [0, 1], [], [], [4], [], [1, 9, 10], [6], [], [9], [7], [7], [0], [6], [1], [], [1], [0, 5], [], [11], [], [9], [], [], [], [], [0], [1]], [[0, 2], [6], [4], [], [8], [1, 2], [0, 5], [7], [0], [0], [3], [], [0, 8], [0], [], [0, 6], [], [0], [], [0], [3, 4], [0], [], [0], [], [], [0, 2], [9], [0], [1], [4], [0]], [[4], [0, 5], [8], [0], [0], [10], [4, 8], [0], [], [0, 4], [0], [0, 1], [0], [6], [], [], [], [], [], [], [0], [4], [], [2], [], [0, 1], [1], [5], [5], [], [], [0, 10]], [[4], [0], [1], [6, 7], [0], [1], [], [0], [], [], [1, 4, 7], [2], [], [0], [7], [0, 2, 7], [1], [], [1], [0, 1, 8], [], [0], [2, 8], [], [4], [], [], [], [0, 5], [0, 1], [0, 1], []], [[], [2, 5], [0], [], [], [1, 5, 9], [], [4], [0, 8], [], [], [0], [0], [5, 6], [1], [0], [], [0, 1], [], [2], [], [], [0, 4], [0, 2, 7], [2], [], [0], [4], [1], [], [1, 6], []], [[1, 3], [2], [], [0, 2], [0], [], [], [], [1], [0, 4], [4], [0, 1, 2, 11], [8], [], [], [], [0, 1], [], [0], [0], [1, 6], [0], [], [], [2, 9], [0], [4, 7], [], [], [10], [0, 4], [7]], [[4, 7], [], [0, 8], [6, 7], [1, 3], [1], [3, 6], [], [], [0, 2, 11], [11], [], [4], [], [], [2, 10], [10], [0], [0], [5], [], [1], [4], [], [2], [3, 11], [], [], [7], [], [], [1]], [[0, 4], [], [], [2], [], [0, 2], [0, 10], [9], [], [2, 4, 7], [], [5, 7], [], [0], [0], [], [6, 7], [10], [], [], [], [1, 4], [], [0], [], [], [2], [], [], [1, 5], [], []], [[], [4, 7, 8], [10], [10], [], [1], [7], [], [], [], [], [], [], [0], [], [], [0, 2], [], [1], [], [9], [], [0], [1], [0], [], [7], [], [1, 4], [1], [], [5, 6]], [[0, 4], [], [10], [0, 7, 8], [10], [], [], [0, 1], [0, 1], [0, 6], [], [10], [1, 2, 6], [0, 8], [], [6], [1, 3], [5, 11], [0, 4], [0], [7], [0], [10], [6, 9], [2], [], [0], [], [3, 11], [], [0], []], [[], [4, 7], [5], [1], [], [0], [], [1, 6], [], [5], [], [0, 1, 2, 6], [], [2], [], [0], [], [1], [6, 7], [0], [4], [1, 2], [], [1], [0], [1], [], [], [1], [], [6], [0]], [[0], [0, 2], [0, 5, 11], [], [0, 8], [0], [5], [0, 10], [], [3, 4], [7], [7], [], [0], [0, 4], [7], [5, 11], [1], [10], [11], [2], [], [4], [0], [0, 2], [0], [2, 4], [0], [0, 11]]]
  | 6 => [[[], [0], [4], [0], [1, 2], [6], [], [1, 6, 9], [2], [4, 8], [0, 1, 2, 4], [0, 1, 7], [0], [0, 6], [8, 11], [], [2, 8], [], [0], [9], [0, 2, 5], [0], [0, 1], [0, 2], [1, 2, 7], [0, 11], [6, 9], [0], [8], [2, 3, 7], [0, 2], [2]], [[0, 4], [0, 1], [], [2], [], [2, 4, 6, 8], [0, 2, 6, 7, 10], [], [0, 2], [0, 4], [6], [], [2], [0, 2], [], [1], [0, 5, 7], [], [0, 1, 2], [0, 1, 8], [0, 6, 7], [0], [3], [6, 11], [1, 2, 6], [0, 1, 9], [1], [0], [7, 9], [0, 4], [1, 2, 6], [1, 5]], [[0], [0, 4], [1, 7], [10], [0], [0, 2], [0, 3, 4, 6], [0, 7], [0], [2, 5], [0, 1, 4, 7], [0, 1], [2, 4], [0], [], [0, 4, 11], [0, 2, 4, 7], [0, 1, 6], [0, 6], [0], [4, 5], [0, 4, 6], [], [0, 4, 6, 7, 8, 11], [0, 4, 6], [0], [7], [2, 6], [11], [5, 10], [0], [0, 6]], [[1, 2], [0], [0], [2, 6], [0, 11], [8, 9], [4, 6], [1, 6], [1], [0, 2, 4], [2], [], [2], [4, 7], [], [6], [2], [2, 4, 6, 8], [0, 6], [0], [0, 1, 6], [9], [0], [4, 6, 10], [0, 1, 9], [0, 5, 8], [0, 8], [0, 6], [1, 2, 11], [0, 11], [0, 1], [0, 1, 10]], [[1], [4, 5], [0, 6], [1], [4], [1, 6, 9], [0, 2], [0, 1], [2], [0, 4], [], [0], [0, 1, 6, 8, 9], [0, 6], [], [2], [2, 7, 9], [2, 6], [5, 6, 11], [0], [], [0], [1], [4], [], [4], [0, 2], [0], [0], [], [0, 4, 7, 8], []], [[2], [], [6, 8], [0, 2], [6, 8], [0, 4], [7], [1, 6], [0], [1, 8, 11], [0, 4, 6, 10], [0], [0, 1], [4, 6], [0, 3], [0, 1], [0, 1], [0, 8], [], [1, 2, 3, 7], [0, 2, 7, 9], [4, 11], [2], [0], [1], [0, 6], [0, 4], [0, 2], [2], [0, 1, 2, 5, 11], [1], [0, 6]], [[6], [2], [], [0, 2, 11], [4, 11], [0, 2], [1, 2, 7], [0, 1, 2, 4, 6], [0], [11], [1, 2], [0, 1, 2, 5], [0, 1, 5], [], [2], [2, 4, 7], [0, 2], [11], [1, 11], [0], [2], [11], [11], [3, 7], [0], [0, 2], [2, 3, 8], [0, 1], [11], [5, 6], [0, 2, 4], [4]], [[1], [2], [4], [0], [4], [0, 7, 8], [0], [1, 6], [1, 2, 4], [0, 1], [0], [0, 9], [0, 4], [0, 1], [0], [], [], [0], [], [0, 5, 9], [1], [0, 2, 4, 9], [], [0], [3, 8], [0, 10], [], [0, 11], [0, 4, 6], [0], [], [0, 1]], [[0, 1, 2], [1, 2], [0], [6], [0, 4, 11], [1, 6], [0, 4, 11], [2], [2, 6, 11], [], [0], [2, 7, 8], [0, 1, 2, 4], [0], [0, 6], [0, 10], [], [], [], [1], [4, 6, 7], [0], [1, 8], [], [6], [0, 7], [0, 2], [0, 1, 2], [0], [0, 11], [0, 4], []], [[0, 1, 6], [0, 6], [0], [8], [], [0, 6], [0, 2, 9], [0, 1, 2], [0], [1, 2, 8], [0], [7], [1], [1, 4], [], [], [0, 1], [0, 2, 7], [5, 7], [2], [], [0], [3], [0, 5, 9], [], [0], [0, 1], [1, 2, 6, 10], [], [6], [0, 1, 4], [0, 1, 7]], [[0, 2], [0], [0, 2, 4], [1, 2, 5], [], [], [6], [], [0, 1], [], [6, 7], [0], [2, 8, 9], [0, 6, 11], [0, 2], [0, 2], [2], [2], [3], [0, 6], [2, 3, 6, 7, 8], [0, 4], [0, 7, 9], [1, 2], [0, 1, 9, 11], [2], [], [0, 6], [0, 2, 4, 6], [0], [0, 7], [0]], [[0, 1], [0, 4], [2, 6], [6], [6], [], [0, 7], [0, 2, 10], [0, 4], [0, 1, 6], [], [0, 1, 6], [0, 1], [0], [5], [7, 9], [0], [0, 2], [0], [0, 4], [0], [1], [0, 4, 10], [8], [1, 6], [0, 6, 11], [0], [7], [0], [5, 8], [1], [2]], [[], [0, 2], [0], [], [1], [4, 8], [], [], [0], [1, 2, 6], [1], [1], [11], [0, 10], [1, 2, 4, 6, 9], [6, 7], [5, 11], [2], [0], [0], [0], [1, 8], [4], [0, 1, 2, 5], [0, 2], [0, 6], [4], [0], [0, 1, 2, 4], [0, 1], [0, 5, 6, 9], [0, 5, 10]], [[0, 1, 8], [0], [1], [6], [], [0, 1, 3, 7], [], [2, 7], [2, 11], [0, 6], [0, 6], [], [], [2], [0, 6], [0], [1, 2, 10], [0, 6], [0, 1], [], [0, 2, 9], [0, 1], [2, 4], [0, 1, 7], [0, 1], [0, 6, 11], [0, 8], [2], [2, 4, 10], [1, 8], [0], []], [[0, 1], [], [0, 1, 2, 4], [0, 6, 11], [1, 2, 6], [], [0, 2, 8, 11], [0, 5, 8], [1, 6], [7], [0, 11], [4, 7], [2, 7, 11], [0, 1, 2, 3], [], [7], [0, 1], [], [0, 1, 2, 11], [], [0, 6], [4, 6], [0, 2], [0, 2], [0, 4], [0, 1, 9], [2, 3], [0, 1], [0, 3, 6, 11], [], [0, 4], [0, 2, 6]], [[0, 1, 4], [], [0, 6], [6], [0], [], [0, 2], [0, 4, 8], [0, 6, 7], [0, 1, 2], [0], [0, 6], [1], [0, 3, 9], [0, 2, 4], [1, 10], [0, 2], [1, 6], [1, 9], [1], [0], [0, 1, 2], [1], [0, 7], [1, 6], [0, 2], [0, 6], [8], [3, 10], [0, 11], [0, 4], []], [[0, 6], [1], [], [8], [0, 2, 7], [0], [1, 4, 7], [0, 2], [1, 2, 6], [0, 2, 5, 7], [9], [0, 1], [0], [], [0], [1, 2, 6, 10], [0], [2, 8, 9], [0, 4, 8, 9], [4], [0, 3], [0, 4], [6, 7], [], [0, 2, 4, 8], [0, 1], [0, 9], [], [0, 6], [0, 2], [5], [0, 4, 9]], [[0, 6], [0], [0, 1], [4], [6, 11], [0, 2, 4, 11], [0, 2, 4, 8], [0, 4], [0, 10], [3, 10], [1], [11], [0, 2, 5], [], [5], [0], [0, 1], [0], [0, 8, 9], [], [1, 4, 9], [1, 6], [0, 1], [7, 9], [], [0, 1], [1], [4, 6], [0], [4, 7], [0, 6], [8]], [[2, 4], [0, 2, 7, 8], [], [], [0, 1], [0, 1, 3, 7, 11], [0], [0, 9], [0, 2], [0, 2, 6], [0, 1], [1], [], [0, 2, 10], [2, 4, 6], [6, 9], [1, 2, 9], [0, 1], [1, 2, 9], [0, 5], [3], [0, 2, 7], [0, 2, 11], [0, 2], [], [2, 6], [1, 7], [], [], [1, 4], [], [0, 6]], [[], [0, 1, 6], [0, 1, 11], [0, 2, 7, 9], [0, 1, 2, 6], [0], [2, 6], [7], [1, 2], [0], [0, 1, 7], [9], [0, 1], [8], [0, 1, 4, 10], [], [0, 1, 2, 4, 6], [], [0, 2, 4, 10], [], [2], [0, 1, 2, 8], [4], [4, 6], [2, 4], [], [0, 2], [7], [0, 1, 2, 11], [], [1, 4, 6], [0, 4]], [[0, 1, 6], [0], [2, 4, 8], [1, 8], [0, 5], [3], [2], [1, 9], [0, 9], [1], [0], [0, 1, 4], [0], [], [7, 8, 11], [6, 7, 9], [0, 2], [0], [0, 4, 7, 11], [0], [], [0], [0, 5], [], [6], [0], [0, 1], [0, 11], [0, 1, 2, 11], [6], [0, 2, 4, 8], [0, 4]], [[0, 1, 2], [6, 9], [0], [], [2, 5, 9], [2], [0, 7], [1, 3, 4, 6], [0], [2, 6], [0], [0], [0, 4], [2], [4], [0, 2], [0, 1, 11], [4, 6], [1], [0], [2, 6], [0, 2], [0, 9], [], [], [7], [2], [], [0, 8], [1], [2], []], [[0, 1], [1, 2, 6], [0, 5], [0, 7, 9], [], [0], [1], [6], [0], [0, 4, 6], [0, 1, 2, 3, 8], [1, 4, 8, 9], [0, 2, 6], [0, 2, 11], [0], [], [0], [0], [0, 4], [2, 6, 8], [9], [4, 9], [1, 7], [9], [10], [0, 4], [], [0], [0, 1, 2, 5], [2], [0, 11], [7]], [[1, 3, 5, 7, 10], [7], [1, 2, 6, 9], [0, 2, 8, 11], [0], [0, 4], [1, 2], [0, 2, 6, 11], [2, 6], [0, 2], [2, 6], [5], [], [6], [0, 10], [0, 1], [3, 8], [4], [1, 7], [1], [8], [6], [1, 4], [0, 6], [0, 2, 8], [2, 4], [11], [1], [0, 1, 5, 8], [1, 6], [6], [0, 6, 8]], [[1], [0, 9], [2, 4], [4], [0, 1], [0, 6], [1, 2, 4, 5, 6, 7], [0, 7, 9], [0, 2], [0, 1, 2], [0, 2, 9], [4], [0], [2, 11], [7], [0, 7], [0], [0, 6], [0, 10], [0, 2, 6], [2, 8], [0, 1, 6, 9], [1, 2], [0, 1, 2, 3, 6, 7], [6], [1, 7], [0], [0, 6], [], [0, 4], [0, 1], [0]], [[2, 6, 10], [], [], [0, 7], [0, 2, 10], [0, 6, 7], [0, 2, 11], [0, 8], [0, 4, 6], [0, 2], [0, 1], [0, 6, 7], [1, 6], [0, 1], [0, 2], [0], [0, 5], [], [0], [0, 2], [3], [0, 1], [], [1, 11], [], [1], [0, 5, 7], [1, 9], [0, 4], [0], [0], [0]], [[], [0, 2], [0, 1], [0, 1, 6, 8], [0], [], [6], [0, 3], [1, 3], [4], [6], [0], [0], [], [7], [], [], [], [4], [5, 6], [8], [], [0, 7], [0, 2], [2, 3], [11], [0, 6], [0], [], [4], [], [11]], [[], [1, 6, 9], [0, 10], [6], [1], [5, 6], [0, 6], [0, 7], [], [0, 6], [0, 4], [1, 2, 10], [0], [4], [], [2, 6], [0, 11], [1, 2, 4], [], [1, 11], [], [0], [0], [0], [1, 6], [0, 2], [0, 1, 4, 6], [2, 7], [4], [2], [1], []], [[0], [0, 2, 4], [0, 1, 4], [3, 4], [0, 1], [1, 6], [0, 2, 4], [0, 1], [0, 4], [0], [0, 2, 7], [0, 2, 7], [0, 8], [0, 1, 11], [1, 6, 9, 10], [0, 2], [], [1, 7], [], [6], [], [0], [11], [1, 4], [6, 11], [0, 7], [1], [1], [0, 2, 4], [0, 1], [0, 8], []], [[0, 6, 10], [0, 11], [0], [0], [0, 1, 8, 10], [0, 4], [1, 2], [0], [2, 4], [2, 8], [], [2, 4], [0, 2, 9], [2], [0, 4], [6], [0, 1], [0], [2], [0, 2, 4, 10], [0, 1, 4, 6, 9], [0, 5, 6], [0, 1, 5], [2], [1, 6], [0, 6, 10], [0, 1, 5], [0], [2, 7, 11], [2, 8, 9], [1, 2, 4, 9], [0, 2, 7, 8]], [[0, 8], [], [0, 3, 7], [], [1, 5, 6], [0, 1], [2, 8], [2], [0], [], [0], [2], [0], [0, 1, 4], [2], [0, 2, 10], [2], [0, 4, 5, 7], [0, 6], [0, 7], [7], [0, 4, 6, 8], [], [2], [2], [9], [0, 2, 4], [1], [7], [0, 1], [0], [2]], [[4], [0, 4], [0, 1], [0, 6, 7], [0, 4, 5, 11], [1, 2], [0], [0, 2, 6, 10], [0, 2], [4, 7], [8], [], [0], [4, 8], [0, 2, 6], [1, 2], [0, 2], [4], [1, 3], [0, 11], [1, 2], [0, 2, 5, 8, 9], [0, 8], [0, 2], [], [0, 9], [0, 1, 2, 4], [0], []]]
  | 7 => [[[], [0, 5, 11], [], [2, 10], [], [6], [0], [4], [], [], [3], [0], [1], [6], [0], [1, 2], [0, 1], [1], [8, 10], [2, 4, 7], [0], [0, 8], [], [2], [0, 7], [2, 6, 8], [0, 7], [1], [1, 2], [1, 2], [], [0, 1, 6]], [[], [4], [0, 5], [2, 6], [0, 2, 3], [0, 2], [11], [1], [2, 10], [0, 6], [3], [1], [3, 11], [6], [0], [1, 6], [2, 6], [0, 2, 6], [0, 1], [], [4, 9], [0, 1, 6], [0], [2, 10], [4, 7], [0], [1], [0, 2, 4], [0], [4, 6], [3, 9], []], [[], [0, 2], [], [], [3], [0, 2], [1, 3], [0], [1], [0, 2, 7], [0, 2, 6], [0, 1, 10], [4, 6], [], [0, 1, 4], [0, 4, 6], [0, 4], [], [0, 1], [], [4, 6], [], [0, 6, 7], [0, 6, 7], [7], [], [], [1, 2], [2, 8], [0], [1], [3]], [[1], [], [4, 9], [1], [0, 1], [0], [1, 2], [0], [0, 2, 4, 8], [], [], [], [], [0, 1, 2, 4, 6], [], [], [0, 6], [0, 4, 5], [4], [7], [], [2, 6], [0, 5], [1], [], [6], [], [0, 2], [1, 6, 10], [6, 9], [0], [0, 2, 7]], [[0, 2], [0], [], [6, 8, 9], [0], [6], [0], [1, 8], [0], [0, 1], [], [0, 6], [3], [0, 8], [], [0], [6, 9], [0], [1], [6], [1, 2], [0, 7], [2, 6], [6], [0], [0, 1], [], [0], [6], [0, 5], [4], [10]], [[0, 3], [2, 6], [], [2, 4, 6], [3, 6], [0, 1, 4], [9], [], [0], [1], [], [], [4, 6], [], [0, 2, 8], [4, 7], [0], [0, 2], [0], [1], [2], [2, 10], [4], [], [1, 6, 7], [0, 9], [], [2, 4], [1, 3], [2], [0, 9], [0]], [[1, 4, 10], [0, 2], [], [6], [10], [4], [1, 4], [0, 4], [], [1], [0, 4], [0, 4], [1, 4], [], [0, 4], [6], [2], [1], [], [], [4], [0, 1, 6], [0, 4], [], [10], [], [2], [2, 4], [0, 4, 10, 11], [2], [0, 2], [0, 2, 8, 11]], [[1, 4], [10], [1, 7], [4], [0, 2, 4], [0], [0, 4], [0], [0, 4], [0, 2], [], [], [], [], [1], [], [1], [0], [6], [0, 3, 6], [], [0], [], [2], [0, 2, 3, 4, 6], [], [8], [], [], [], [0], []], [[9], [0, 1, 2], [0, 2, 8], [0], [0, 3, 4], [0], [2, 3], [0], [], [0], [1], [0, 4], [0, 1], [0, 7], [0], [1], [1], [], [], [], [1], [0], [0, 1, 10], [], [], [5], [0, 1], [1, 6], [], [0], [1, 8], [0, 7]], [[0, 6], [0], [2, 3, 11], [0, 1, 4, 6], [0], [0], [], [0], [0, 1, 5], [0], [], [5], [0], [4], [2, 4], [0, 7, 9], [1], [6], [0, 2], [4], [0], [6], [], [0], [1], [0], [0], [1, 2, 6], [11], [0], [0], [0, 2, 4, 6]], [[7, 8], [0, 1, 6], [4, 6], [6, 11], [], [6], [4, 6, 11], [0], [], [], [], [0, 6], [0], [0], [2], [1, 6], [], [0], [], [], [1, 2, 9], [0, 2], [0], [1, 2], [1], [0, 2], [2], [6], [], [2, 9], [4], [0]], [[0, 6], [], [0], [], [1, 6], [0, 1, 8], [9], [3, 6], [], [4], [0, 2], [0, 1, 8], [4], [], [], [0], [0, 1], [], [8], [0, 2], [8], [0], [0, 4], [1], [0], [1], [5, 11], [2], [0, 6, 7], [], [2, 3, 8], [0, 1, 2]], [[0, 1, 3], [6], [], [0, 4, 8], [0, 2], [], [8], [], [0, 6, 11], [0, 10], [], [0], [1, 2, 10], [0, 2], [1], [1], [1, 4], [0, 5], [0, 2], [0], [5], [2, 4, 8], [1], [6], [0], [0, 1, 6, 10], [4, 5], [0, 6], [2], [], [3, 6], [0]], [[1, 2], [], [1], [1], [0, 6], [6], [4], [1, 2, 6], [0, 4], [], [0], [0, 1], [0, 7], [2], [0, 5], [0, 2, 6], [], [], [1, 2, 6], [0, 1], [], [1, 6], [0], [0, 1], [1, 4], [], [0, 9], [6], [0], [1], [6], [0, 1, 3]], [[], [0], [1], [0, 2, 8], [0, 4], [1, 2, 6], [4], [0, 2], [0, 2], [], [0], [], [6], [1], [1, 4, 10], [0], [1], [1], [0, 1, 2], [2], [0, 3, 6], [0, 2], [], [0, 2], [0, 3, 10], [0, 1, 6], [1, 2], [0], [0], [5], [1], [0, 3, 7, 8]], [[], [], [], [0], [], [0, 6], [0, 2, 4], [0], [0], [], [0, 2, 7], [], [1, 2, 8, 11], [0, 6], [7], [], [], [2], [0, 1, 5, 9], [0, 4], [0, 1], [], [0, 1, 6], [0], [1], [], [], [0], [0, 6], [1, 10], [6], [0, 1, 6]], [[4], [10], [], [6], [], [0], [1, 9], [4], [1, 6], [0, 2], [], [0, 6], [2, 5], [0], [0], [6], [], [0], [0, 5, 6], [0, 1], [1, 5], [1], [3], [0, 6, 10], [4], [], [0, 6, 7], [2, 6], [0, 6, 7], [4], [0], [0]], [[4], [0], [4], [10], [2, 4, 8], [0, 1], [0, 1, 5], [0, 2], [2], [0], [], [0, 1], [0, 4, 5, 11], [], [5], [], [0], [], [], [2], [6], [], [0, 2, 4, 7], [2, 3], [0, 8, 11], [], [1, 2, 6], [1, 10], [], [], [0, 2, 6], [0, 1]], [[0, 4], [6], [7], [0], [0, 8], [4, 8], [0, 4], [], [], [0], [0, 1], [], [0, 4], [], [0], [0], [0, 2, 7], [0, 2, 6, 8, 9], [1], [0], [], [4], [0, 2], [1, 8], [2], [0], [0, 4], [2, 7], [0, 1], [0, 6], [1], []], [[0, 2], [4], [0], [1, 2], [], [], [0], [], [], [6, 8], [2], [8], [6], [0, 6, 9], [0, 6], [2], [1, 2], [2, 8], [6], [0, 2, 6], [5], [6], [4], [0], [1], [0, 2], [4, 8], [0], [2], [0, 1], [0], [1, 2]], [[0, 8], [1], [], [2], [0], [1, 10], [2], [], [0, 5], [0, 7], [0, 6], [1], [1, 5], [1, 8], [8], [0], [1, 2], [], [2, 4], [], [], [0], [4], [6], [1], [0], [1], [0], [], [0], [0, 11], [0, 8]], [[1, 2, 6, 7], [0, 2], [0, 1, 4], [6], [5, 8], [2], [0], [], [0, 7], [1], [0, 1, 7], [], [1], [0], [2, 4], [2, 6], [6], [], [0, 3], [0, 6], [1], [], [1, 4], [], [4], [], [2, 8], [6, 9], [0], [0, 2, 4, 6], [0, 6], [10]], [[], [1], [1], [0, 6], [6], [6, 11], [0, 1], [1], [0, 2], [0, 2, 4, 8, 10], [0, 1], [6], [2, 7], [2], [2, 4], [0], [2], [0, 1], [0], [0], [], [], [1], [7], [0, 2, 8], [3, 4, 9], [2], [0, 1], [0], [2, 9, 11], [0], []], [[5], [7], [2, 6], [8], [], [0, 8], [0, 1], [], [0, 2], [0], [0, 2, 4, 6, 11], [1, 7], [5], [0, 8], [0, 5], [], [], [1], [1], [10], [10], [0], [11], [0, 1], [], [0], [0, 6, 8], [0, 1], [6], [0, 8, 9], [], [0]], [[1], [0], [1, 4], [0, 9], [1, 6, 7], [0, 1, 3, 10], [0, 6], [], [2], [6, 7, 8], [8], [], [6], [2, 4], [2], [1, 8], [7], [0, 9], [], [0], [1], [0, 1], [0], [], [6, 10], [], [0, 1], [8], [1], [2], [0, 6], []], [[1, 7], [0], [0], [2], [0, 7], [2], [7], [0, 4, 7], [4], [6], [1, 7], [6], [0], [0], [0, 3], [0, 1, 6], [1, 2], [6], [0, 1], [6, 8], [1], [4], [0], [10], [0], [], [2, 3], [6], [2], [0, 2, 10], [4], [0, 1]], [[], [0, 7], [], [1, 6], [2], [6], [], [0], [2, 6], [1, 4, 6], [0, 7], [], [], [1, 7], [7, 8], [0], [], [0, 3], [1], [0], [4], [4], [2, 4], [4, 8], [6], [0, 2, 8], [1], [4, 8], [0, 1, 7], [], [0, 1], []], [[0, 2, 6], [4], [0, 2, 4], [0, 1], [], [0, 4], [2, 5], [], [], [0, 1], [6, 11], [1], [0], [2], [1, 2, 6, 9], [0], [], [4, 6, 7], [0], [6], [], [], [4, 7], [0], [0], [0, 6], [0, 1], [1, 8], [], [1, 3, 10], [0], [6]], [[2, 7], [0, 1, 2], [9], [1, 4, 6], [4, 10], [1, 2, 7], [5], [1, 4], [], [7], [], [0], [0], [0], [], [0, 3, 7, 8, 10], [2], [0, 8], [], [0, 1, 8], [], [0, 2], [0, 8], [6], [], [0, 6, 8], [0, 1], [6], [0, 2], [], [], [1]], [[], [4, 11], [], [0, 6], [0, 2], [0, 4], [2, 4], [0, 5], [2], [3, 4], [0, 2, 3], [10], [], [0], [0, 2], [3], [], [11], [1, 8], [0, 2], [6], [0, 2], [0, 2, 8, 11], [0, 6], [0, 6], [10], [], [], [2], [2], [0, 6], [0]], [[0, 1, 5, 6, 10], [7], [], [3], [10], [0], [6], [], [], [], [0], [0, 1], [0, 6], [1, 2], [], [2], [1, 4], [], [0, 1], [0], [0], [0], [0, 4, 7], [], [0], [0, 4], [0, 1], [], [], [0, 4, 6], [2], [1]], [[], [0], [0, 1, 10], [1, 6], [], [4, 6, 7, 11], [], [4, 9], [0, 6], [0], [], [], [], [1, 2, 6], [], [1, 2], [0], [4], [0, 2, 4, 8], [0], [0], [0, 6], [], [1], [0, 2], [0], [0, 1], [1, 6], [0]]]
  | 8 => [[[0], [], [1], [2], [], [], [0, 1], [1], [], [], [], [1], [], [], [], [0], [0, 10], [], [4], [], [], [], [], [], [0, 7], [], [0], [11], [], [], [], []], [[], [1], [4], [], [3], [], [], [0], [0], [], [8], [], [], [], [], [], [], [11], [], [0], [], [], [], [6], [], [6], [], [], [1], [], [4, 9], []], [[], [], [], [], [], [], [], [], [2], [], [0], [], [], [0], [0, 4], [0], [], [], [6], [], [5, 6], [], [], [], [], [], [], [4, 11], [], [], [], []], [[], [], [], [1], [], [], [], [0], [], [0], [], [], [0], [1], [], [], [], [0], [6], [], [], [6], [0], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [0], [1], [3], [7], [6], [0], [1, 10], [], [1], [6], [], [5], [], [], [0], [0], [], [2], [], [], [], [], [], [0, 5], [], []], [[], [], [0, 8], [4], [], [2], [], [11], [], [], [], [4], [], [], [], [], [], [], [], [0], [], [], [], [0], [], [], [0, 9], [0], [], [], [4], []], [[2], [], [], [], [], [0, 10], [0, 4, 8], [1], [6], [], [], [0], [], [0], [], [], [0], [], [], [], [6], [0], [], [], [8], [], [0, 1], [], [], [10], [], [0]], [[], [], [10], [], [], [0, 4], [], [1], [], [], [], [], [], [], [6], [], [], [], [], [7], [10], [6], [], [], [], [2], [0], [], [], [], [1], []], [[3], [], [], [0], [6], [], [1], [0, 6], [], [5], [0], [], [], [6], [0], [1, 6], [], [], [6], [], [], [], [], [], [], [3, 7], [], [10], [], [], [], [0]], [[0], [], [0], [1], [6], [], [], [11], [], [], [], [], [], [1], [], [0], [], [], [4], [], [], [], [], [], [8], [1], [0, 6], [], [], [], [6], []], [[1], [4, 11], [6], [], [1], [0], [], [], [10], [], [8], [6], [], [], [], [], [1], [], [11], [], [1], [], [0], [], [5], [2], [2, 10], [], [1], [0], [], []], [[], [], [10], [], [9], [], [], [6], [], [], [], [], [], [], [], [0], [], [], [2], [], [], [1], [], [10], [], [], [], [], [], [0], [0], [10]], [[7], [], [0], [], [], [], [], [], [], [], [2], [], [], [11], [2], [], [], [], [], [], [0, 5, 8], [], [0, 1, 4], [0], [], [0], [], [], [], [], [10, 11], []], [[], [], [], [], [], [0], [], [0], [], [], [0], [1], [2], [], [], [4], [], [], [], [], [1], [], [], [3], [1, 6, 8], [], [6, 9], [], [0], [8], [], [0]], [[], [0, 6], [], [0], [0], [], [], [], [0], [1], [5], [], [], [0], [], [], [], [2], [], [10], [], [], [], [], [], [], [], [], [4, 10], [], [6], []], [[], [], [], [], [], [0], [], [], [], [1], [6], [10], [], [0], [], [1], [], [], [], [], [1], [0], [2], [], [2, 6, 9], [], [6], [], [], [], [3], []], [[], [6], [], [], [], [], [2], [], [], [], [4], [], [1, 5], [11], [1], [], [7], [], [0], [6], [0, 2], [6], [5], [1], [], [3], [], [2], [], [], [], [0, 6]], [[8], [], [4], [6], [], [], [], [], [], [], [0], [0, 1], [], [4], [], [3, 8], [], [11], [], [], [], [0, 1], [], [], [], [], [], [1], [], [], [2], []], [[], [], [], [0], [0], [2], [], [], [], [8], [], [10], [], [11], [2], [], [0, 2], [], [], [], [4], [], [0], [], [], [], [], [], [], [], [], []], [[0], [], [0], [3], [], [0], [], [], [2], [], [0], [], [], [], [], [10], [], [], [], [], [], [4], [], [6], [], [0], [], [], [], [7], [10], [0, 4]], [[], [], [], [10], [1], [8], [], [], [2], [], [], [], [], [4], [], [6], [], [], [1], [], [], [1], [], [], [], [], [], [], [], [], [0], []], [[4], [], [6], [2], [], [7], [6], [1], [0, 1, 6], [], [], [], [], [0, 4], [], [1, 6], [], [], [3], [], [], [0], [], [0], [], [], [], [], [], [], [], []], [[1], [], [1], [], [], [0], [], [], [2], [0], [1, 6, 11], [], [], [0], [], [], [], [], [], [], [], [], [], [], [0], [], [], [6], [0], [0], [], []], [[], [], [5, 11], [], [], [], [], [], [], [9], [], [1, 6], [], [], [], [6], [], [0], [], [], [], [10], [1], [], [10], [], [], [1, 11], [], [], [], [0, 6]], [[1], [], [], [0], [0], [4], [], [], [], [7], [], [], [], [], [], [], [3], [], [], [], [0], [1], [], [], [2], [0], [1], [2], [], [10], [4], [0]], [[], [], [0], [], [], [], [], [0], [], [], [1], [10], [], [], [], [], [], [], [], [0], [], [], [], [], [1], [4], [], [], [0], [], [4], [4]], [[2], [], [10], [], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [0], [0, 4], [1], [], [2], [], [0], [], [2], [4, 10], [6], [0], []], [[4], [0, 4], [], [1], [], [2], [10], [], [0], [], [], [], [1], [0, 3], [0], [], [], [], [], [], [], [0, 10], [4, 6], [], [], [], [], [], [0], [], [], []], [[], [], [], [], [], [], [1], [], [3], [], [], [], [1], [], [3, 6], [], [], [0], [0], [0], [], [0], [], [5], [8], [0], [], [2], [8], [], [1], []], [[], [], [], [], [1], [], [], [], [], [3], [], [], [0], [0], [0], [], [10], [0, 1], [], [5], [], [], [], [8], [1], [], [], [2], [], [], [], [0]], [[9], [1], [], [], [], [6], [], [], [], [10], [], [], [6], [], [], [], [], [0], [1], [], [3, 4], [], [], [], [8], [0, 5], [], [7], [], [], [3, 8], []], [[9], [], [], [], [1], [], [0, 5], [], [6], [], [1], [], [7], [3], [0, 3, 4], [], [], [], [9], [], [], [], [6], [], [], [0], [], [], []]]
  | 9 => [[[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [8], [], [], [], [], [], [6], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [0, 8], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [4], []], [[], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [6], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[6], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [10], [4], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2, 10], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [6], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [2], [], [], [], [], [], [10], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0]], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [6], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [1], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], []], [[4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5], [], [6], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [8], [], [], [3], [], [], [], [], [], [], [], [], [], [], [], [], [], []]]
  | _ => []

def ap : List Nat → Nat → Nat
  | [], _ => 0
  | j :: p, w => (w >>> j) % 2 + 2 * ap p w

theorem ap_step (w j : Nat) : (w >>> j) % 2 = (w.testBit j).toNat := by
  unfold Nat.testBit
  rw [Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (w >>> j) with h | h <;> simp [h]

theorem ap_bit : ∀ (p : List Nat) (w i : Nat),
    (ap p w).testBit i = (match p[i]? with | some j => w.testBit j | none => false)
  | [], w, i => by simp [ap]
  | j :: p, w, 0 => by
      simp only [ap, ap_step, Nat.testBit_zero, List.getElem?_cons_zero]
      cases w.testBit j <;> simp <;> omega
  | j :: p, w, i + 1 => by
      have h : ((w >>> j) % 2 + 2 * ap p w) / 2 = ap p w := by omega
      rw [ap, Nat.testBit_succ, h, ap_bit p w i]; simp

def okPerm (pq : List Nat × List Nat) : Bool :=
  pq.1.length == 25 && pq.1.all (fun j => decide (j < 25)) &&
    (List.range 25).all (fun j => pq.1[pq.2.getD j 0]? == some j) &&
    ap pq.1 goal == goal && ap pq.1 truthMask == truthMask

theorem ok_len {pq} (h : okPerm pq = true) : pq.1.length = 25 := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1

theorem ok_lt {pq} (h : okPerm pq = true) : ∀ j ∈ pq.1, j < 25 := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem ok_inv {pq} (h : okPerm pq = true) : ∀ j, j < 25 → pq.1[pq.2.getD j 0]? = some j := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact h.1.1.2

theorem ok_goal {pq} (h : okPerm pq = true) : ap pq.1 goal = goal := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2

theorem ok_mask {pq} (h : okPerm pq = true) : ap pq.1 truthMask = truthMask := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq] at h; exact h.2

theorem perm_cases {pq} (h : okPerm pq = true) (i : Nat) :
    (pq.1[i]? = none ∧ ¬ i < 25) ∨ (∃ j, pq.1[i]? = some j ∧ i < 25 ∧ j < 25) := by
  have hl := ok_len h
  cases hpi : pq.1[i]? with
  | none =>
    left; refine ⟨rfl, ?_⟩
    have := List.getElem?_eq_none_iff.1 hpi; omega
  | some j =>
    right
    obtain ⟨hi, hj⟩ := List.getElem?_eq_some_iff.1 hpi
    exact ⟨j, rfl, by omega, ok_lt h j (hj ▸ List.getElem_mem hi)⟩

theorem high_bit {a : Nat} (ha : a < 2 ^ 25) {j : Nat} (hj : ¬ j < 25) : a.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))

theorem ap_inj {pq} (h : okPerm pq = true) {a b : Nat} (ha : a < 2 ^ 25) (hb : b < 2 ^ 25)
    (he : ap pq.1 a = ap pq.1 b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 25
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

theorem mask_lt : truthMask < 2 ^ 25 := by decide

theorem negD_lt (a : Nat) : negD truthMask a < 2 ^ 25 :=
  Nat.lt_of_le_of_lt Nat.and_le_right mask_lt

theorem bin_lt (c : Bool) (a b : Nat) :
    (if c then andD truthMask a b else orD truthMask a b) < 2 ^ 25 := by
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

theorem ap_new {pq} (h : okPerm pq = true) {w : Nat} {xs : List Nat} (hw : w < 2 ^ 25)
    (hb : ∀ x ∈ xs, x < 2 ^ 25) (h0 : w ≠ 0) (hd : w ≠ truthMask) (hm : w ∉ xs) :
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
    (∀ w ∈ ws, w < 2 ^ 25) → RunD truthMask (ap pq.1 y) s (ws.map (ap pq.1)) := by
  induction h using Run.fold with
  | done => intro _; exact Run.done
  | perm p _ ih =>
    intro hb
    exact Run.perm (p.map _) (ih (fun w hw => hb w (p.mem_iff.1 hw)))
  | @one s a r save h0 hd hnm h ih =>
    intro hb
    obtain ⟨n0, nd, nm⟩ := ap_new hp (negD_lt a) hb h0 hd hnm
    have hb' : ∀ w ∈ negD truthMask a :: kept save a r, w < 2 ^ 25 := by
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
    have hb' : ∀ w ∈ (if c then andD truthMask a b else orD truthMask a b) :: kept ka a (kept kb b r), w < 2 ^ 25 := by
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

def grp : List (Nat × (Nat → Nat) × (List Nat × List Nat)) := [(0, (fun w => (w >>> 0) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 19) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 24) % 2 + 2 * (0)))))))))))))))))))))))))), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24])), (1, (fun w => (w >>> 0) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 19) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 24) % 2 + 2 * (0)))))))))))))))))))))))))), ([0, 2, 1, 3, 4, 5, 7, 6, 8, 9, 15, 17, 16, 18, 19, 10, 12, 11, 13, 14, 20, 22, 21, 23, 24], [0, 2, 1, 3, 4, 5, 7, 6, 8, 9, 15, 17, 16, 18, 19, 10, 12, 11, 13, 14, 20, 22, 21, 23, 24])), (2, (fun w => (w >>> 1) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 24) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 19) % 2 + 2 * (0)))))))))))))))))))))))))), ([1, 0, 2, 3, 4, 6, 5, 7, 8, 9, 11, 10, 12, 13, 14, 21, 20, 22, 23, 24, 16, 15, 17, 18, 19], [1, 0, 2, 3, 4, 6, 5, 7, 8, 9, 11, 10, 12, 13, 14, 21, 20, 22, 23, 24, 16, 15, 17, 18, 19])), (3, (fun w => (w >>> 1) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 24) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 19) % 2 + 2 * (0)))))))))))))))))))))))))), ([1, 2, 0, 3, 4, 6, 7, 5, 8, 9, 21, 22, 20, 23, 24, 11, 12, 10, 13, 14, 16, 17, 15, 18, 19], [2, 0, 1, 3, 4, 7, 5, 6, 8, 9, 17, 15, 16, 18, 19, 22, 20, 21, 23, 24, 12, 10, 11, 13, 14])), (4, (fun w => (w >>> 2) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 19) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 24) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 14) % 2 + 2 * (0)))))))))))))))))))))))))), ([2, 0, 1, 3, 4, 7, 5, 6, 8, 9, 17, 15, 16, 18, 19, 22, 20, 21, 23, 24, 12, 10, 11, 13, 14], [1, 2, 0, 3, 4, 6, 7, 5, 8, 9, 21, 22, 20, 23, 24, 11, 12, 10, 13, 14, 16, 17, 15, 18, 19])), (5, (fun w => (w >>> 2) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 24) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 19) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 14) % 2 + 2 * (0)))))))))))))))))))))))))), ([2, 1, 0, 3, 4, 7, 6, 5, 8, 9, 22, 21, 20, 23, 24, 17, 16, 15, 18, 19, 12, 11, 10, 13, 14], [2, 1, 0, 3, 4, 7, 6, 5, 8, 9, 22, 21, 20, 23, 24, 17, 16, 15, 18, 19, 12, 11, 10, 13, 14])), (6, (fun w => (w >>> 14) % 2 + 2 * ((w >>> 19) % 2 + 2 * ((w >>> 24) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 2) % 2 + 2 * (0)))))))))))))))))))))))))), ([14, 19, 24, 9, 4, 13, 18, 23, 8, 3, 10, 15, 20, 5, 0, 11, 16, 21, 6, 1, 12, 17, 22, 7, 2], [14, 19, 24, 9, 4, 13, 18, 23, 8, 3, 10, 15, 20, 5, 0, 11, 16, 21, 6, 1, 12, 17, 22, 7, 2])), (7, (fun w => (w >>> 14) % 2 + 2 * ((w >>> 24) % 2 + 2 * ((w >>> 19) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 2) % 2 + 2 * (0)))))))))))))))))))))))))), ([14, 24, 19, 9, 4, 13, 23, 18, 8, 3, 11, 21, 16, 6, 1, 10, 20, 15, 5, 0, 12, 22, 17, 7, 2], [19, 14, 24, 9, 4, 18, 13, 23, 8, 3, 15, 10, 20, 5, 0, 17, 12, 22, 7, 2, 16, 11, 21, 6, 1])), (8, (fun w => (w >>> 19) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 24) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 1) % 2 + 2 * (0)))))))))))))))))))))))))), ([19, 14, 24, 9, 4, 18, 13, 23, 8, 3, 15, 10, 20, 5, 0, 17, 12, 22, 7, 2, 16, 11, 21, 6, 1], [14, 24, 19, 9, 4, 13, 23, 18, 8, 3, 11, 21, 16, 6, 1, 10, 20, 15, 5, 0, 12, 22, 17, 7, 2])), (9, (fun w => (w >>> 19) % 2 + 2 * ((w >>> 24) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 1) % 2 + 2 * (0)))))))))))))))))))))))))), ([19, 24, 14, 9, 4, 18, 23, 13, 8, 3, 17, 22, 12, 7, 2, 15, 20, 10, 5, 0, 16, 21, 11, 6, 1], [19, 24, 14, 9, 4, 18, 23, 13, 8, 3, 17, 22, 12, 7, 2, 15, 20, 10, 5, 0, 16, 21, 11, 6, 1])), (10, (fun w => (w >>> 24) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 19) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 0) % 2 + 2 * (0)))))))))))))))))))))))))), ([24, 14, 19, 9, 4, 23, 13, 18, 8, 3, 21, 11, 16, 6, 1, 22, 12, 17, 7, 2, 20, 10, 15, 5, 0], [24, 14, 19, 9, 4, 23, 13, 18, 8, 3, 21, 11, 16, 6, 1, 22, 12, 17, 7, 2, 20, 10, 15, 5, 0])), (11, (fun w => (w >>> 24) % 2 + 2 * ((w >>> 19) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 0) % 2 + 2 * (0)))))))))))))))))))))))))), ([24, 19, 14, 9, 4, 23, 18, 13, 8, 3, 22, 17, 12, 7, 2, 21, 16, 11, 6, 1, 20, 15, 10, 5, 0], [24, 19, 14, 9, 4, 23, 18, 13, 8, 3, 22, 17, 12, 7, 2, 21, 16, 11, 6, 1, 20, 15, 10, 5, 0]))]

set_option maxHeartbeats 0 in
theorem okG : grp.all (fun x => okPerm x.2.2) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem fastOK : ∀ x ∈ grp, x.2.1 = ap x.2.2.1 := by
  intro x hx
  simp only [grp, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def hkey (ws : List Nat) : Nat := (ws.foldl (fun acc w => acc + w * w) 0) % 1021

def look (s : Nat) (zs : List Nat) : Bool :=
  (fastGet s (key zs)).any (fun l => zs.isPerm l)

def tryPerm (s : Nat) (ws : List Nat) (i : Nat) : Bool :=
  match grp[i]? with
  | some x => look s (ws.map x.2.1)
  | none => false

theorem tryPerm_spec {s : Nat} {ws : List Nat} {i : Nat} :
    tryPerm s ws i = true → ∃ x ∈ grp, look s (ws.map x.2.1) = true := by
  unfold tryPerm
  cases h : grp[i]? with
  | none => simp
  | some x =>
    intro hl
    exact ⟨x, List.mem_of_getElem? h, hl⟩

def listed (s : Nat) (ws : List Nat) : Bool :=
  ws.all (fun w => decide (w < 2 ^ 25)) &&
    (((hintOf s).getD (hkey ws / 32) []).getD (hkey ws % 32) []).any (tryPerm s ws)

theorem sym_run {s : Nat} {ys : List Nat} (hs : s ≤ 9) (hl : listed s ys = true) (h : RunD truthMask goal s ys) :
    ∃ i, i < 245 ∧ ∃ zs ∈ (rowsOf s).getD i [], RunD truthMask goal s zs := by
  simp only [listed, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hl
  obtain ⟨hb, i, _, hi⟩ := hl
  obtain ⟨x, hx, hlk⟩ := tryPerm_spec hi
  simp only [look, List.any_eq_true] at hlk
  obtain ⟨zs, hzs, hz⟩ := hlk
  rw [fastOK x hx] at hzs hz
  have hok : okPerm x.2.2 = true := List.all_eq_true.1 okG x hx
  have h2 := run_sym hok h hb
  rw [ok_goal hok] at h2
  obtain ⟨i', hi', hin⟩ := fast_in hs hzs
  exact ⟨i', hi', zs, hin, Run.perm (List.isPerm_iff.1 hz) h2⟩

def blocked (s : Nat) (ws : List Nat) : Bool :=
  match s with
  | 0 => ws != [goal]
  | s + 1 => !(nextD truthMask (s + 2 - ws.length) ws
      (fun ys => coversP pairs s ys && !(listed s ys)))

private theorem validPairs :
    pairs.all (fun p => truthMask.testBit p.1 && truthMask.testBit p.2 &&
                      !goal.testBit p.1 && goal.testBit p.2) = true := by decide +kernel

def cellCheck (s i : Nat) : Bool := ((rowsOf s).getD i []).all (blocked s)

def cc (s o : Nat) : Bool := span (cellCheck s) 5 o

private theorem lvl_0 : ∀ i, 0 ≤ i → i < 245 → cellCheck 0 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf, fast]
private theorem lvl_1 : ∀ i, 0 ≤ i → i < 245 → cellCheck 1 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf, fast]
private theorem lvl_2 : ∀ i, 0 ≤ i → i < 245 → cellCheck 2 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf, fast]
private theorem lvl_3 : ∀ i, 0 ≤ i → i < 245 → cellCheck 3 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf, fast]
set_option maxRecDepth 40000 in
theorem c4_0 : cc 4 0 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_5 : cc 4 5 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_10 : cc 4 10 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_15 : cc 4 15 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_20 : cc 4 20 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_25 : cc 4 25 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_30 : cc 4 30 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_35 : cc 4 35 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_40 : cc 4 40 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_45 : cc 4 45 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_50 : cc 4 50 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_55 : cc 4 55 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_60 : cc 4 60 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_65 : cc 4 65 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_70 : cc 4 70 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_75 : cc 4 75 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_80 : cc 4 80 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_85 : cc 4 85 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_90 : cc 4 90 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_95 : cc 4 95 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_100 : cc 4 100 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_105 : cc 4 105 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_110 : cc 4 110 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_115 : cc 4 115 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_120 : cc 4 120 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_125 : cc 4 125 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_130 : cc 4 130 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_135 : cc 4 135 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_140 : cc 4 140 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_145 : cc 4 145 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_150 : cc 4 150 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_155 : cc 4 155 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_160 : cc 4 160 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_165 : cc 4 165 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_170 : cc 4 170 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_175 : cc 4 175 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_180 : cc 4 180 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_185 : cc 4 185 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_190 : cc 4 190 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_195 : cc 4 195 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_200 : cc 4 200 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_205 : cc 4 205 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_210 : cc 4 210 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_215 : cc 4 215 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_220 : cc 4 220 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_225 : cc 4 225 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_230 : cc 4 230 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_235 : cc 4 235 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c4_240 : cc 4 240 = true := by decide +kernel
private theorem lvl_4 : ∀ i, 0 ≤ i → i < 245 → cellCheck 4 i = true :=
  (range_split (range_split (range_split (range_split (range_split (span_ok c4_0) (range_split (span_ok c4_5) (span_ok c4_10))) (range_split (span_ok c4_15) (range_split (span_ok c4_20) (span_ok c4_25)))) (range_split (range_split (span_ok c4_30) (range_split (span_ok c4_35) (span_ok c4_40))) (range_split (span_ok c4_45) (range_split (span_ok c4_50) (span_ok c4_55))))) (range_split (range_split (range_split (span_ok c4_60) (range_split (span_ok c4_65) (span_ok c4_70))) (range_split (span_ok c4_75) (range_split (span_ok c4_80) (span_ok c4_85)))) (range_split (range_split (span_ok c4_90) (range_split (span_ok c4_95) (span_ok c4_100))) (range_split (span_ok c4_105) (range_split (span_ok c4_110) (span_ok c4_115)))))) (range_split (range_split (range_split (range_split (span_ok c4_120) (range_split (span_ok c4_125) (span_ok c4_130))) (range_split (span_ok c4_135) (range_split (span_ok c4_140) (span_ok c4_145)))) (range_split (range_split (span_ok c4_150) (range_split (span_ok c4_155) (span_ok c4_160))) (range_split (span_ok c4_165) (range_split (span_ok c4_170) (span_ok c4_175))))) (range_split (range_split (range_split (span_ok c4_180) (range_split (span_ok c4_185) (span_ok c4_190))) (range_split (span_ok c4_195) (range_split (span_ok c4_200) (span_ok c4_205)))) (range_split (range_split (span_ok c4_210) (range_split (span_ok c4_215) (span_ok c4_220))) (range_split (range_split (span_ok c4_225) (span_ok c4_230)) (range_split (span_ok c4_235) (span_ok c4_240)))))))
set_option maxRecDepth 40000 in
theorem c5_0 : cc 5 0 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_5 : cc 5 5 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_10 : cc 5 10 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_15 : cc 5 15 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_20 : cc 5 20 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_25 : cc 5 25 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_30 : cc 5 30 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_35 : cc 5 35 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_40 : cc 5 40 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_45 : cc 5 45 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_50 : cc 5 50 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_55 : cc 5 55 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_60 : cc 5 60 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_65 : cc 5 65 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_70 : cc 5 70 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_75 : cc 5 75 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_80 : cc 5 80 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_85 : cc 5 85 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_90 : cc 5 90 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_95 : cc 5 95 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_100 : cc 5 100 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_105 : cc 5 105 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_110 : cc 5 110 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_115 : cc 5 115 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_120 : cc 5 120 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_125 : cc 5 125 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_130 : cc 5 130 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_135 : cc 5 135 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_140 : cc 5 140 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_145 : cc 5 145 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_150 : cc 5 150 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_155 : cc 5 155 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_160 : cc 5 160 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_165 : cc 5 165 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_170 : cc 5 170 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_175 : cc 5 175 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_180 : cc 5 180 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_185 : cc 5 185 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_190 : cc 5 190 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_195 : cc 5 195 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_200 : cc 5 200 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_205 : cc 5 205 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_210 : cc 5 210 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_215 : cc 5 215 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_220 : cc 5 220 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_225 : cc 5 225 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_230 : cc 5 230 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_235 : cc 5 235 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c5_240 : cc 5 240 = true := by decide +kernel
private theorem lvl_5 : ∀ i, 0 ≤ i → i < 245 → cellCheck 5 i = true :=
  (range_split (range_split (range_split (range_split (range_split (span_ok c5_0) (range_split (span_ok c5_5) (span_ok c5_10))) (range_split (span_ok c5_15) (range_split (span_ok c5_20) (span_ok c5_25)))) (range_split (range_split (span_ok c5_30) (range_split (span_ok c5_35) (span_ok c5_40))) (range_split (span_ok c5_45) (range_split (span_ok c5_50) (span_ok c5_55))))) (range_split (range_split (range_split (span_ok c5_60) (range_split (span_ok c5_65) (span_ok c5_70))) (range_split (span_ok c5_75) (range_split (span_ok c5_80) (span_ok c5_85)))) (range_split (range_split (span_ok c5_90) (range_split (span_ok c5_95) (span_ok c5_100))) (range_split (span_ok c5_105) (range_split (span_ok c5_110) (span_ok c5_115)))))) (range_split (range_split (range_split (range_split (span_ok c5_120) (range_split (span_ok c5_125) (span_ok c5_130))) (range_split (span_ok c5_135) (range_split (span_ok c5_140) (span_ok c5_145)))) (range_split (range_split (span_ok c5_150) (range_split (span_ok c5_155) (span_ok c5_160))) (range_split (span_ok c5_165) (range_split (span_ok c5_170) (span_ok c5_175))))) (range_split (range_split (range_split (span_ok c5_180) (range_split (span_ok c5_185) (span_ok c5_190))) (range_split (span_ok c5_195) (range_split (span_ok c5_200) (span_ok c5_205)))) (range_split (range_split (span_ok c5_210) (range_split (span_ok c5_215) (span_ok c5_220))) (range_split (range_split (span_ok c5_225) (span_ok c5_230)) (range_split (span_ok c5_235) (span_ok c5_240)))))))
set_option maxRecDepth 40000 in
theorem c6_0 : cc 6 0 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_5 : cc 6 5 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_10 : cc 6 10 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_15 : cc 6 15 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_20 : cc 6 20 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_25 : cc 6 25 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_30 : cc 6 30 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_35 : cc 6 35 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_40 : cc 6 40 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_45 : cc 6 45 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_50 : cc 6 50 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_55 : cc 6 55 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_60 : cc 6 60 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_65 : cc 6 65 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_70 : cc 6 70 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_75 : cc 6 75 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_80 : cc 6 80 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_85 : cc 6 85 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_90 : cc 6 90 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_95 : cc 6 95 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_100 : cc 6 100 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_105 : cc 6 105 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_110 : cc 6 110 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_115 : cc 6 115 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_120 : cc 6 120 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_125 : cc 6 125 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_130 : cc 6 130 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_135 : cc 6 135 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_140 : cc 6 140 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_145 : cc 6 145 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_150 : cc 6 150 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_155 : cc 6 155 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_160 : cc 6 160 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_165 : cc 6 165 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_170 : cc 6 170 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_175 : cc 6 175 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_180 : cc 6 180 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_185 : cc 6 185 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_190 : cc 6 190 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_195 : cc 6 195 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_200 : cc 6 200 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_205 : cc 6 205 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_210 : cc 6 210 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_215 : cc 6 215 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_220 : cc 6 220 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_225 : cc 6 225 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_230 : cc 6 230 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_235 : cc 6 235 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c6_240 : cc 6 240 = true := by decide +kernel
private theorem lvl_6 : ∀ i, 0 ≤ i → i < 245 → cellCheck 6 i = true :=
  (range_split (range_split (range_split (range_split (range_split (span_ok c6_0) (range_split (span_ok c6_5) (span_ok c6_10))) (range_split (span_ok c6_15) (range_split (span_ok c6_20) (span_ok c6_25)))) (range_split (range_split (span_ok c6_30) (range_split (span_ok c6_35) (span_ok c6_40))) (range_split (span_ok c6_45) (range_split (span_ok c6_50) (span_ok c6_55))))) (range_split (range_split (range_split (span_ok c6_60) (range_split (span_ok c6_65) (span_ok c6_70))) (range_split (span_ok c6_75) (range_split (span_ok c6_80) (span_ok c6_85)))) (range_split (range_split (span_ok c6_90) (range_split (span_ok c6_95) (span_ok c6_100))) (range_split (span_ok c6_105) (range_split (span_ok c6_110) (span_ok c6_115)))))) (range_split (range_split (range_split (range_split (span_ok c6_120) (range_split (span_ok c6_125) (span_ok c6_130))) (range_split (span_ok c6_135) (range_split (span_ok c6_140) (span_ok c6_145)))) (range_split (range_split (span_ok c6_150) (range_split (span_ok c6_155) (span_ok c6_160))) (range_split (span_ok c6_165) (range_split (span_ok c6_170) (span_ok c6_175))))) (range_split (range_split (range_split (span_ok c6_180) (range_split (span_ok c6_185) (span_ok c6_190))) (range_split (span_ok c6_195) (range_split (span_ok c6_200) (span_ok c6_205)))) (range_split (range_split (span_ok c6_210) (range_split (span_ok c6_215) (span_ok c6_220))) (range_split (range_split (span_ok c6_225) (span_ok c6_230)) (range_split (span_ok c6_235) (span_ok c6_240)))))))
set_option maxRecDepth 40000 in
theorem c7_0 : cc 7 0 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_5 : cc 7 5 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_10 : cc 7 10 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_15 : cc 7 15 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_20 : cc 7 20 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_25 : cc 7 25 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_30 : cc 7 30 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_35 : cc 7 35 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_40 : cc 7 40 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_45 : cc 7 45 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_50 : cc 7 50 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_55 : cc 7 55 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_60 : cc 7 60 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_65 : cc 7 65 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_70 : cc 7 70 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_75 : cc 7 75 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_80 : cc 7 80 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_85 : cc 7 85 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_90 : cc 7 90 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_95 : cc 7 95 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_100 : cc 7 100 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_105 : cc 7 105 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_110 : cc 7 110 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_115 : cc 7 115 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_120 : cc 7 120 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_125 : cc 7 125 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_130 : cc 7 130 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_135 : cc 7 135 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_140 : cc 7 140 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_145 : cc 7 145 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_150 : cc 7 150 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_155 : cc 7 155 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_160 : cc 7 160 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_165 : cc 7 165 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_170 : cc 7 170 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_175 : cc 7 175 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_180 : cc 7 180 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_185 : cc 7 185 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_190 : cc 7 190 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_195 : cc 7 195 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_200 : cc 7 200 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_205 : cc 7 205 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_210 : cc 7 210 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_215 : cc 7 215 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_220 : cc 7 220 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_225 : cc 7 225 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_230 : cc 7 230 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_235 : cc 7 235 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c7_240 : cc 7 240 = true := by decide +kernel
private theorem lvl_7 : ∀ i, 0 ≤ i → i < 245 → cellCheck 7 i = true :=
  (range_split (range_split (range_split (range_split (range_split (span_ok c7_0) (range_split (span_ok c7_5) (span_ok c7_10))) (range_split (span_ok c7_15) (range_split (span_ok c7_20) (span_ok c7_25)))) (range_split (range_split (span_ok c7_30) (range_split (span_ok c7_35) (span_ok c7_40))) (range_split (span_ok c7_45) (range_split (span_ok c7_50) (span_ok c7_55))))) (range_split (range_split (range_split (span_ok c7_60) (range_split (span_ok c7_65) (span_ok c7_70))) (range_split (span_ok c7_75) (range_split (span_ok c7_80) (span_ok c7_85)))) (range_split (range_split (span_ok c7_90) (range_split (span_ok c7_95) (span_ok c7_100))) (range_split (span_ok c7_105) (range_split (span_ok c7_110) (span_ok c7_115)))))) (range_split (range_split (range_split (range_split (span_ok c7_120) (range_split (span_ok c7_125) (span_ok c7_130))) (range_split (span_ok c7_135) (range_split (span_ok c7_140) (span_ok c7_145)))) (range_split (range_split (span_ok c7_150) (range_split (span_ok c7_155) (span_ok c7_160))) (range_split (span_ok c7_165) (range_split (span_ok c7_170) (span_ok c7_175))))) (range_split (range_split (range_split (span_ok c7_180) (range_split (span_ok c7_185) (span_ok c7_190))) (range_split (span_ok c7_195) (range_split (span_ok c7_200) (span_ok c7_205)))) (range_split (range_split (span_ok c7_210) (range_split (span_ok c7_215) (span_ok c7_220))) (range_split (range_split (span_ok c7_225) (span_ok c7_230)) (range_split (span_ok c7_235) (span_ok c7_240)))))))
set_option maxRecDepth 40000 in
theorem c8_0 : cc 8 0 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_5 : cc 8 5 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_10 : cc 8 10 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_15 : cc 8 15 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_20 : cc 8 20 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_25 : cc 8 25 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_30 : cc 8 30 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_35 : cc 8 35 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_40 : cc 8 40 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_45 : cc 8 45 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_50 : cc 8 50 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_55 : cc 8 55 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_60 : cc 8 60 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_65 : cc 8 65 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_70 : cc 8 70 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_75 : cc 8 75 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_80 : cc 8 80 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_85 : cc 8 85 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_90 : cc 8 90 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_95 : cc 8 95 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_100 : cc 8 100 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_105 : cc 8 105 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_110 : cc 8 110 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_115 : cc 8 115 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_120 : cc 8 120 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_125 : cc 8 125 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_130 : cc 8 130 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_135 : cc 8 135 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_140 : cc 8 140 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_145 : cc 8 145 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_150 : cc 8 150 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_155 : cc 8 155 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_160 : cc 8 160 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_165 : cc 8 165 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_170 : cc 8 170 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_175 : cc 8 175 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_180 : cc 8 180 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_185 : cc 8 185 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_190 : cc 8 190 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_195 : cc 8 195 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_200 : cc 8 200 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_205 : cc 8 205 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_210 : cc 8 210 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_215 : cc 8 215 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_220 : cc 8 220 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_225 : cc 8 225 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_230 : cc 8 230 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_235 : cc 8 235 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c8_240 : cc 8 240 = true := by decide +kernel
private theorem lvl_8 : ∀ i, 0 ≤ i → i < 245 → cellCheck 8 i = true :=
  (range_split (range_split (range_split (range_split (range_split (span_ok c8_0) (range_split (span_ok c8_5) (span_ok c8_10))) (range_split (span_ok c8_15) (range_split (span_ok c8_20) (span_ok c8_25)))) (range_split (range_split (span_ok c8_30) (range_split (span_ok c8_35) (span_ok c8_40))) (range_split (span_ok c8_45) (range_split (span_ok c8_50) (span_ok c8_55))))) (range_split (range_split (range_split (span_ok c8_60) (range_split (span_ok c8_65) (span_ok c8_70))) (range_split (span_ok c8_75) (range_split (span_ok c8_80) (span_ok c8_85)))) (range_split (range_split (span_ok c8_90) (range_split (span_ok c8_95) (span_ok c8_100))) (range_split (span_ok c8_105) (range_split (span_ok c8_110) (span_ok c8_115)))))) (range_split (range_split (range_split (range_split (span_ok c8_120) (range_split (span_ok c8_125) (span_ok c8_130))) (range_split (span_ok c8_135) (range_split (span_ok c8_140) (span_ok c8_145)))) (range_split (range_split (span_ok c8_150) (range_split (span_ok c8_155) (span_ok c8_160))) (range_split (span_ok c8_165) (range_split (span_ok c8_170) (span_ok c8_175))))) (range_split (range_split (range_split (span_ok c8_180) (range_split (span_ok c8_185) (span_ok c8_190))) (range_split (span_ok c8_195) (range_split (span_ok c8_200) (span_ok c8_205)))) (range_split (range_split (span_ok c8_210) (range_split (span_ok c8_215) (span_ok c8_220))) (range_split (range_split (span_ok c8_225) (span_ok c8_230)) (range_split (span_ok c8_235) (span_ok c8_240)))))))
set_option maxRecDepth 40000 in
theorem c9_0 : cc 9 0 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_5 : cc 9 5 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_10 : cc 9 10 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_15 : cc 9 15 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_20 : cc 9 20 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_25 : cc 9 25 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_30 : cc 9 30 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_35 : cc 9 35 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_40 : cc 9 40 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_45 : cc 9 45 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_50 : cc 9 50 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_55 : cc 9 55 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_60 : cc 9 60 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_65 : cc 9 65 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_70 : cc 9 70 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_75 : cc 9 75 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_80 : cc 9 80 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_85 : cc 9 85 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_90 : cc 9 90 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_95 : cc 9 95 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_100 : cc 9 100 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_105 : cc 9 105 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_110 : cc 9 110 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_115 : cc 9 115 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_120 : cc 9 120 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_125 : cc 9 125 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_130 : cc 9 130 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_135 : cc 9 135 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_140 : cc 9 140 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_145 : cc 9 145 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_150 : cc 9 150 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_155 : cc 9 155 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_160 : cc 9 160 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_165 : cc 9 165 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_170 : cc 9 170 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_175 : cc 9 175 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_180 : cc 9 180 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_185 : cc 9 185 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_190 : cc 9 190 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_195 : cc 9 195 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_200 : cc 9 200 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_205 : cc 9 205 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_210 : cc 9 210 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_215 : cc 9 215 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_220 : cc 9 220 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_225 : cc 9 225 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_230 : cc 9 230 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_235 : cc 9 235 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c9_240 : cc 9 240 = true := by decide +kernel
private theorem lvl_9 : ∀ i, 0 ≤ i → i < 245 → cellCheck 9 i = true :=
  (range_split (range_split (range_split (range_split (range_split (span_ok c9_0) (range_split (span_ok c9_5) (span_ok c9_10))) (range_split (span_ok c9_15) (range_split (span_ok c9_20) (span_ok c9_25)))) (range_split (range_split (span_ok c9_30) (range_split (span_ok c9_35) (span_ok c9_40))) (range_split (span_ok c9_45) (range_split (span_ok c9_50) (span_ok c9_55))))) (range_split (range_split (range_split (span_ok c9_60) (range_split (span_ok c9_65) (span_ok c9_70))) (range_split (span_ok c9_75) (range_split (span_ok c9_80) (span_ok c9_85)))) (range_split (range_split (span_ok c9_90) (range_split (span_ok c9_95) (span_ok c9_100))) (range_split (span_ok c9_105) (range_split (span_ok c9_110) (span_ok c9_115)))))) (range_split (range_split (range_split (range_split (span_ok c9_120) (range_split (span_ok c9_125) (span_ok c9_130))) (range_split (span_ok c9_135) (range_split (span_ok c9_140) (span_ok c9_145)))) (range_split (range_split (span_ok c9_150) (range_split (span_ok c9_155) (span_ok c9_160))) (range_split (span_ok c9_165) (range_split (span_ok c9_170) (span_ok c9_175))))) (range_split (range_split (range_split (span_ok c9_180) (range_split (span_ok c9_185) (span_ok c9_190))) (range_split (span_ok c9_195) (range_split (span_ok c9_200) (span_ok c9_205)))) (range_split (range_split (span_ok c9_210) (range_split (span_ok c9_215) (span_ok c9_220))) (range_split (range_split (span_ok c9_225) (span_ok c9_230)) (range_split (span_ok c9_235) (span_ok c9_240)))))))

private theorem checkedCells (s : Nat) (hs : s ≤ 9) (i : Nat) (hi : i < 245) : cellCheck s i = true := by
  interval_cases s <;> first | exact lvl_0 i (Nat.zero_le i) hi | exact lvl_1 i (Nat.zero_le i) hi | exact lvl_2 i (Nat.zero_le i) hi | exact lvl_3 i (Nat.zero_le i) hi | exact lvl_4 i (Nat.zero_le i) hi | exact lvl_5 i (Nat.zero_le i) hi | exact lvl_6 i (Nat.zero_le i) hi | exact lvl_7 i (Nat.zero_le i) hi | exact lvl_8 i (Nat.zero_le i) hi | exact lvl_9 i (Nat.zero_le i) hi

private theorem impossibleState : ∀ s ≤ 9, ∀ i < 245, ∀ ws ∈ (rowsOf s).getD i [], ¬ RunD truthMask goal s ws := by
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
        obtain ⟨i', hi', zs, hzs, hr⟩ := sym_run (by omega) (by simpa using hb) h
        exact ih s (by omega) (by omega) i' hi' zs hzs hr
      have hn := nextD_complete hrun s rfl ws (List.Perm.refl _) _ good
      simp [blocked, hn] at hc

def rootCheck (s : Nat) (ws : List Nat) : Bool :=
  decide (s + 1 < ws.length) || !(coversP pairs s ws) || listed s ws

def inputSubsets : List (List Nat) := roots.sublists

def rootCheckAt (i : Nat) : Bool :=
  (List.range 10).all (fun s => rootCheck s (inputSubsets.getD i []))

private theorem subsetCount : inputSubsets.length = 1024 := by decide +kernel

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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_256 : ∀ i, 256 ≤ i → i < 264 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_264 : ∀ i, 264 ≤ i → i < 272 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_272 : ∀ i, 272 ≤ i → i < 280 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_280 : ∀ i, 280 ≤ i → i < 288 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_288 : ∀ i, 288 ≤ i → i < 296 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_296 : ∀ i, 296 ≤ i → i < 304 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_304 : ∀ i, 304 ≤ i → i < 312 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_312 : ∀ i, 312 ≤ i → i < 320 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_320 : ∀ i, 320 ≤ i → i < 328 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_328 : ∀ i, 328 ≤ i → i < 336 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_336 : ∀ i, 336 ≤ i → i < 344 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_344 : ∀ i, 344 ≤ i → i < 352 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_352 : ∀ i, 352 ≤ i → i < 360 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_360 : ∀ i, 360 ≤ i → i < 368 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_368 : ∀ i, 368 ≤ i → i < 376 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_376 : ∀ i, 376 ≤ i → i < 384 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_384 : ∀ i, 384 ≤ i → i < 392 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_392 : ∀ i, 392 ≤ i → i < 400 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_400 : ∀ i, 400 ≤ i → i < 408 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_408 : ∀ i, 408 ≤ i → i < 416 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_416 : ∀ i, 416 ≤ i → i < 424 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_424 : ∀ i, 424 ≤ i → i < 432 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_432 : ∀ i, 432 ≤ i → i < 440 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_440 : ∀ i, 440 ≤ i → i < 448 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_448 : ∀ i, 448 ≤ i → i < 456 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_456 : ∀ i, 456 ≤ i → i < 464 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_464 : ∀ i, 464 ≤ i → i < 472 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_472 : ∀ i, 472 ≤ i → i < 480 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_480 : ∀ i, 480 ≤ i → i < 488 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_488 : ∀ i, 488 ≤ i → i < 496 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_496 : ∀ i, 496 ≤ i → i < 504 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_504 : ∀ i, 504 ≤ i → i < 512 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_512 : ∀ i, 512 ≤ i → i < 520 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_520 : ∀ i, 520 ≤ i → i < 528 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_528 : ∀ i, 528 ≤ i → i < 536 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_536 : ∀ i, 536 ≤ i → i < 544 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_544 : ∀ i, 544 ≤ i → i < 552 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_552 : ∀ i, 552 ≤ i → i < 560 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_560 : ∀ i, 560 ≤ i → i < 568 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_568 : ∀ i, 568 ≤ i → i < 576 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_576 : ∀ i, 576 ≤ i → i < 584 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_584 : ∀ i, 584 ≤ i → i < 592 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_592 : ∀ i, 592 ≤ i → i < 600 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_600 : ∀ i, 600 ≤ i → i < 608 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_608 : ∀ i, 608 ≤ i → i < 616 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_616 : ∀ i, 616 ≤ i → i < 624 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 616 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_624 : ∀ i, 624 ≤ i → i < 632 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_632 : ∀ i, 632 ≤ i → i < 640 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 632 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_640 : ∀ i, 640 ≤ i → i < 648 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_648 : ∀ i, 648 ≤ i → i < 656 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 648 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_656 : ∀ i, 656 ≤ i → i < 664 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_664 : ∀ i, 664 ≤ i → i < 672 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 664 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_672 : ∀ i, 672 ≤ i → i < 680 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_680 : ∀ i, 680 ≤ i → i < 688 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 680 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_688 : ∀ i, 688 ≤ i → i < 696 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_696 : ∀ i, 696 ≤ i → i < 704 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 696 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_704 : ∀ i, 704 ≤ i → i < 712 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_712 : ∀ i, 712 ≤ i → i < 720 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 712 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_720 : ∀ i, 720 ≤ i → i < 728 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_728 : ∀ i, 728 ≤ i → i < 736 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 728 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_736 : ∀ i, 736 ≤ i → i < 744 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 736 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_744 : ∀ i, 744 ≤ i → i < 752 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 744 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_752 : ∀ i, 752 ≤ i → i < 760 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 752 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_760 : ∀ i, 760 ≤ i → i < 768 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 760 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_768 : ∀ i, 768 ≤ i → i < 776 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 768 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_776 : ∀ i, 776 ≤ i → i < 784 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 776 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_784 : ∀ i, 784 ≤ i → i < 792 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 784 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_792 : ∀ i, 792 ≤ i → i < 800 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 792 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_800 : ∀ i, 800 ≤ i → i < 808 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 800 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_808 : ∀ i, 808 ≤ i → i < 816 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 808 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_816 : ∀ i, 816 ≤ i → i < 824 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 816 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_824 : ∀ i, 824 ≤ i → i < 832 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 824 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_832 : ∀ i, 832 ≤ i → i < 840 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 832 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_840 : ∀ i, 840 ≤ i → i < 848 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 840 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_848 : ∀ i, 848 ≤ i → i < 856 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 848 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_856 : ∀ i, 856 ≤ i → i < 864 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 856 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_864 : ∀ i, 864 ≤ i → i < 872 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 864 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_872 : ∀ i, 872 ≤ i → i < 880 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 872 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_880 : ∀ i, 880 ≤ i → i < 888 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 880 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_888 : ∀ i, 888 ≤ i → i < 896 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 888 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_896 : ∀ i, 896 ≤ i → i < 904 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 896 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_904 : ∀ i, 904 ≤ i → i < 912 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 904 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_912 : ∀ i, 912 ≤ i → i < 920 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 912 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_920 : ∀ i, 920 ≤ i → i < 928 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 920 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_928 : ∀ i, 928 ≤ i → i < 936 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 928 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_936 : ∀ i, 936 ≤ i → i < 944 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 936 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_944 : ∀ i, 944 ≤ i → i < 952 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 944 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_952 : ∀ i, 952 ≤ i → i < 960 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 952 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_960 : ∀ i, 960 ≤ i → i < 968 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 960 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_968 : ∀ i, 968 ≤ i → i < 976 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 968 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_976 : ∀ i, 976 ≤ i → i < 984 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 976 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_984 : ∀ i, 984 ≤ i → i < 992 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 984 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_992 : ∀ i, 992 ≤ i → i < 1000 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 992 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1000 : ∀ i, 1000 ≤ i → i < 1008 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1000 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1008 : ∀ i, 1008 ≤ i → i < 1016 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1008 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1016 : ∀ i, 1016 ≤ i → i < 1024 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1016 = true)
private theorem checkedRoots : ∀ i, 0 ≤ i → i < 1024 → rootCheckAt i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split rootBlock_0 rootBlock_8) (range_split rootBlock_16 rootBlock_24)) (range_split (range_split rootBlock_32 rootBlock_40) (range_split rootBlock_48 rootBlock_56))) (range_split (range_split (range_split rootBlock_64 rootBlock_72) (range_split rootBlock_80 rootBlock_88)) (range_split (range_split rootBlock_96 rootBlock_104) (range_split rootBlock_112 rootBlock_120)))) (range_split (range_split (range_split (range_split rootBlock_128 rootBlock_136) (range_split rootBlock_144 rootBlock_152)) (range_split (range_split rootBlock_160 rootBlock_168) (range_split rootBlock_176 rootBlock_184))) (range_split (range_split (range_split rootBlock_192 rootBlock_200) (range_split rootBlock_208 rootBlock_216)) (range_split (range_split rootBlock_224 rootBlock_232) (range_split rootBlock_240 rootBlock_248))))) (range_split (range_split (range_split (range_split (range_split rootBlock_256 rootBlock_264) (range_split rootBlock_272 rootBlock_280)) (range_split (range_split rootBlock_288 rootBlock_296) (range_split rootBlock_304 rootBlock_312))) (range_split (range_split (range_split rootBlock_320 rootBlock_328) (range_split rootBlock_336 rootBlock_344)) (range_split (range_split rootBlock_352 rootBlock_360) (range_split rootBlock_368 rootBlock_376)))) (range_split (range_split (range_split (range_split rootBlock_384 rootBlock_392) (range_split rootBlock_400 rootBlock_408)) (range_split (range_split rootBlock_416 rootBlock_424) (range_split rootBlock_432 rootBlock_440))) (range_split (range_split (range_split rootBlock_448 rootBlock_456) (range_split rootBlock_464 rootBlock_472)) (range_split (range_split rootBlock_480 rootBlock_488) (range_split rootBlock_496 rootBlock_504)))))) (range_split (range_split (range_split (range_split (range_split (range_split rootBlock_512 rootBlock_520) (range_split rootBlock_528 rootBlock_536)) (range_split (range_split rootBlock_544 rootBlock_552) (range_split rootBlock_560 rootBlock_568))) (range_split (range_split (range_split rootBlock_576 rootBlock_584) (range_split rootBlock_592 rootBlock_600)) (range_split (range_split rootBlock_608 rootBlock_616) (range_split rootBlock_624 rootBlock_632)))) (range_split (range_split (range_split (range_split rootBlock_640 rootBlock_648) (range_split rootBlock_656 rootBlock_664)) (range_split (range_split rootBlock_672 rootBlock_680) (range_split rootBlock_688 rootBlock_696))) (range_split (range_split (range_split rootBlock_704 rootBlock_712) (range_split rootBlock_720 rootBlock_728)) (range_split (range_split rootBlock_736 rootBlock_744) (range_split rootBlock_752 rootBlock_760))))) (range_split (range_split (range_split (range_split (range_split rootBlock_768 rootBlock_776) (range_split rootBlock_784 rootBlock_792)) (range_split (range_split rootBlock_800 rootBlock_808) (range_split rootBlock_816 rootBlock_824))) (range_split (range_split (range_split rootBlock_832 rootBlock_840) (range_split rootBlock_848 rootBlock_856)) (range_split (range_split rootBlock_864 rootBlock_872) (range_split rootBlock_880 rootBlock_888)))) (range_split (range_split (range_split (range_split rootBlock_896 rootBlock_904) (range_split rootBlock_912 rootBlock_920)) (range_split (range_split rootBlock_928 rootBlock_936) (range_split rootBlock_944 rootBlock_952))) (range_split (range_split (range_split rootBlock_960 rootBlock_968) (range_split rootBlock_976 rootBlock_984)) (range_split (range_split rootBlock_992 rootBlock_1000) (range_split rootBlock_1008 rootBlock_1016)))))))

private theorem impossibleRoot {s : Nat} {ws : List Nat} (hs : s ≤ 9)
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
  obtain ⟨i', hi', zs, hzs, hr⟩ := sym_run hs hblocked hrun
  exact impossibleState s hs i' hi' zs hzs hr

private theorem rootsAgree : ∀ r : Fin 25,
    roots.map (·.testBit r.val) = PEqualNP.Represents.oneEach
      (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5)) := by decide +kernel

private theorem domainRows : ∀ r : Fin 25, truthMask.testBit r.val = true := by decide +kernel
private theorem targetIndex : ∀ r : Fin 25, 5 * (r.val / 5) + (r.val % 5) = r.val := by decide

private theorem rulesOut (C : Circuit) (hfan : FanInTwo C) (hs : C.size ≤ 9)
    (hrep : PEqualNP.Represents.Represents
      (fun u v : Fin 5 => target.testBit (5 * u.val + v.val)) C) : False := by
  have hsup0 : ∀ v ∈ roots, Avail truthMask roots v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots hfan 0 roots roots rfl hsup0
  set out := (execN C.gates roots).getD C.output 0
  have hout : out &&& truthMask = target &&& truthMask := by
    apply Nat.eq_of_testBit_eq
    intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 25
    · rw [domainRows ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [rootsAgree ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots).map (·.testBit r)).getD C.output false = out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have hr5 : r / 5 < 5 := by omega
      have hcol : r % 5 < 5 := Nat.mod_lt _ (by decide)
      have hv := hrep (Fin.ofNat 5 (r / 5)) (Fin.ofNat 5 (r % 5))
      simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hr5, Nat.mod_eq_of_lt hcol] at hv
      rw [targetIndex ⟨r, hlt⟩] at hv
      exact h2.trans hv
    · have hd : truthMask.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h25 : truthMask < 2 ^ 25 := by decide
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
  have hz : C.gates.length ≤ 9 := hs
  exact impossibleRoot (by omega) hsub (Run.perm hp' hrun)

end PEqualNP.Outside.L_meta_25469

theorem PEqualNP.Outside.L_meta_25469 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (32435687 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C, hfan, hs, hrep⟩
  exact PEqualNP.Outside.L_meta_25469.rulesOut C hfan hs hrep

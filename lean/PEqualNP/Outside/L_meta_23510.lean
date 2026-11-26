import PEqualNP.Defs
import PEqualNP.Library.LRAT.PromiseN

namespace PEqualNP.Outside.L_meta_23510

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def truthMask : Nat := 2 ^ 16 - 1

def negD (d w : Nat) : Nat := (w ^^^ truthMask) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then orD d a b else andD d a b

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs
def NN : Prop := False

def RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      NN → negD d a ≠ 0 → negD d a ≠ d → negD d a ∉ (a :: r) →
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
theorem Run.one {s a r} (save : Bool) (hN : NN)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save hN h0 hd hm (h P dn q u b)
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
    (one : ∀ {s a r} (save : Bool) (hN : NN)
      (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
      (h : RunD d y s (negD d a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save hN h0 hd hm h))
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
    (fun k hN h0 hd hm ⟨h', ih⟩ => ⟨Run.one k hN h0 hd hm h', one k hN h0 hd hm h' ih⟩)
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
  | one save _ _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
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
    (NN ∧ ∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
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

theorem pull_one {d Y k ws} (hN : NN) (hd : d &&& truthMask = d) (hnd : ws.Nodup)
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
        exact Run.perm hp2.symm (Run.one true hN hne0 hned hnm h2)
      · have h2 : RunD d Y k (negD d a' :: kept false a' rest) := h1
        have hnm : negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Run.one false hN hne0 hned hnm h2⟩
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
    rcases hr with ⟨hN, b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_one hN hd hnd hprop hrun ha hsub'
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
  | one save _ _ _ _ _ ih =>
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
  | one save _ _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
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

theorem runM_bits_le {d y s ws} (h : RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save hN _ _ _ _ _ => exact False.elim hN
  | @two s a b r conj ka kb _ _ _ h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · cases conj <;> simp only [andD, orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · rcases (mem_kept ka a w _).1 hr with ⟨_, rfl⟩ | hr
      · exact ha
      · rcases (mem_kept kb b w _).1 hr with ⟨_, rfl⟩ | hr
        · exact hb
        · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem bit_sel {w p q : Nat} (hp : w.testBit p = false) (hq : w.testBit q = true) :
    w &&& (2 ^ p ||| 2 ^ q) = 2 ^ q := by
  have hne : p ≠ q := by
    rintro rfl
    rw [hp] at hq
    cases hq
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow]
  by_cases h1 : q = i
  · subst h1; simp [hq]
  · by_cases h2 : p = i
    · subst h2; simp [hp, h1]
    · simp [h1, h2]

def pmOf (pairs : List (Nat × Nat)) : List (Nat × Nat) :=
  pairs.map (fun p => (2 ^ p.1 ||| 2 ^ p.2, 2 ^ p.2))

def coversM (pm : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pm.all (fun m => ws.any (fun w => Nat.beq (w &&& m.1) m.2))

def coversP (pairs : List (Nat × Nat)) (_s : Nat) (ws : List Nat) : Bool :=
  coversM (pmOf pairs) ws

theorem coversP_ok {d T s : Nat} (_hd : d &&& truthMask = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : coversP pairs s ws = true := by
  unfold coversP coversM pmOf
  simp only [List.all_eq_true, List.any_eq_true, List.mem_map]
  rintro m ⟨⟨u, v⟩, hm, rfl⟩
  have hp := List.all_eq_true.1 hpairs (u, v) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra hall
  have hle := runM_bits_le h v u hp.1.1.2 hp.1.1.1 (fun w hw => by
    cases hu : w.testBit u <;> cases hv : w.testBit v
    · decide
    · exact absurd ⟨w, hw, by rw [bit_sel hu hv]; exact Nat.beq_refl _⟩ hall
    · decide
    · decide)
  rw [hp.1.2, hp.2] at hle; contradiction





























def nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    false ||



    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))
























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
  | one save hN _ _ _ _ _ => exact False.elim hN
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
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hno : ∀ g ∈ gs, g.op = GateOp.not → NN) :
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
            Or.inl ⟨hno g List.mem_cons_self h, bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def roots : List Nat := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]
def target : Nat := 25500
def goal : Nat := target &&& truthMask

def pairs : List (Nat × Nat) := [(1, 13), (10, 9), (12, 14), (11, 8), (0, 4), (6, 7), (1, 9), (12, 13), (6, 2), (0, 3), (11, 7), (12, 8), (1, 2), (6, 4), (11, 3), (11, 14), (12, 3), (11, 9), (0, 13), (6, 9), (6, 14), (5, 9), (15, 8), (10, 14), (5, 4), (15, 3), (1, 4), (1, 3), (5, 2), (0, 2), (10, 7), (12, 4), (0, 8), (15, 14), (10, 2), (10, 8), (0, 14), (5, 7), (11, 13), (11, 2), (10, 3), (12, 7), (12, 2), (15, 4), (5, 13), (15, 13), (0, 9), (1, 7), (15, 7), (10, 4), (6, 13), (5, 14), (15, 9), (1, 8), (5, 3)]

def key (ws : List Nat) : Nat := ws.sum % 245

theorem key_lt (ws : List Nat) : key ws < 245 := Nat.mod_lt _ (by decide)

set_option maxRecDepth 100000 in
def fast : Nat → List (List (List (List Nat)))
  | 3 => [[[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [[15, 9104, 17476, 63624]], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [[15, 8976, 17652, 63624]], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 9202, 17476, 64408]], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], []]]
  | 4 => [[[], [[15, 8882, 20292, 36744, 61713]], [[15, 248, 8738, 20292, 61849]], [[15, 8946, 20468, 61713, 65416]], [[12, 144, 8738, 20292, 61713]], [[15, 8882, 20292, 52428, 61713]], [[15, 648, 12274, 17476, 61713], [15, 3968, 8946, 17484, 61713], [15, 3976, 8946, 17476, 61713]], [], [[15, 8944, 20292, 34952, 62225]], [[15, 7953, 9010, 17652, 63624]], [[15, 8946, 20292, 34952, 62225]], [], [], [], [[15, 3976, 8954, 17476, 61713], [15, 8946, 20292, 34952, 62229]], [[15, 152, 8738, 20292, 61713], [15, 12176, 13299, 17476, 63624]]], [[], [[15, 8946, 20292, 62225, 63624]], [[15, 3976, 8946, 20428, 61713]], [], [[15, 4881, 20292, 26358, 63624]], [], [], [], [], [[15, 7953, 9202, 17476, 63624]], [[15, 8946, 20292, 35480, 61713]], [[15, 4369, 20292, 25330, 65416]], [], [], [], []], [[[15, 8946, 20292, 35464, 62225]], [], [[15, 8946, 20292, 53128, 61713]], [], [[15, 240, 28500, 34952, 62259], [15, 7953, 8946, 17732, 63880], [15, 7953, 9202, 17476, 63880], [15, 7953, 9202, 17732, 63624], [271, 7953, 8946, 17732, 63624]], [], [[15, 8882, 20292, 53196, 61713]], [[15, 8946, 20292, 62225, 64136]], [], [], [[4383, 8751, 17652, 20292, 63624]], [[15, 8946, 19780, 36744, 61713]], [], [], [], []], [[], [], [], [[756, 8751, 20292, 61713, 63624]], [], [], [], [], [], [], [], [], [], [], [[12, 8946, 20292, 36744, 61713]], [[15, 8944, 20292, 36744, 61713]]], [[], [[15, 240, 4369, 25092, 36744], [15, 8946, 20292, 36744, 61713]], [[15, 8946, 28500, 44952, 61713]], [], [], [[15, 8946, 20292, 36744, 61717], [15, 8946, 20292, 36748, 61713]], [[15, 8944, 20292, 61713, 65416]], [], [[15, 8946, 20292, 61713, 65416]], [[15, 8946, 20292, 36744, 61721]], [], [], [[271, 8946, 20292, 36744, 61713]], [[15, 3856, 9010, 17652, 63624]], [], []], [[], [[15, 8946, 20292, 36760, 61713], [31, 8946, 20292, 36744, 61713]], [], [[15, 8946, 17860, 36744, 61713]], [], [], [], [[15, 8946, 20292, 36744, 62225]], [], [], [], [], [], [[15, 3856, 9202, 17476, 63624]], [], []], [[], [[15, 8946, 20308, 36760, 61713], [47, 8946, 20292, 36744, 61713]], [], [[15, 9202, 17476, 40857, 63624]], [], [], [], [], [], [[15, 8946, 18372, 36744, 61713]], [[15, 4881, 8994, 17652, 63624]], [], [], [], [[15, 3840, 8874, 17652, 61849], [15, 3976, 8738, 17652, 61849], [15, 3976, 8874, 17652, 61713]], []], [[], [[15, 8946, 12168, 17476, 61713]], [], [[15, 8944, 20292, 43656, 61713]], [[4383, 8751, 17652, 53196, 63624]], [], [], [[15, 904, 8946, 17476, 61713]], [], [], [], [[15, 4369, 20468, 25250, 65416]], [], [], [], [[15, 3976, 8946, 20292, 61713]]], [[], [], [[15, 240, 8738, 20428, 61849], [15, 240, 8874, 20292, 61849]], [[15, 8946, 17908, 36744, 61713], [271, 8946, 17652, 36744, 61713]], [], [[15, 8946, 20292, 43672, 61713]], [], [], [[15, 240, 25378, 53196, 63897]], [], [[15, 4881, 8946, 17732, 63624]], [], [], [], [[15, 3840, 8946, 17612, 61849], [15, 3976, 8946, 17476, 61849], [15, 3976, 8946, 17612, 61713]], [[15, 240, 26436, 34952, 62225]]], [[], [[15, 8946, 17732, 35464, 61713]], [], [], [], [], [], [], [], [], [], [[4, 3840, 4369, 25338, 63624], [12, 3840, 4369, 25330, 63624]], [], [], [], []], [[[15, 4369, 8946, 20292, 62088], [15, 4881, 8946, 18244, 63624]], [[15, 8866, 20468, 36744, 61713]], [[15, 3840, 4369, 25330, 63628], [15, 3844, 4369, 25330, 63624]], [], [], [], [[15, 3840, 4369, 25334, 63628]], [[15, 8946, 20292, 43160, 62259], [15, 8946, 28500, 34952, 62259]], [], [[15, 3844, 25330, 34952, 61713]], [], [], [[15, 8946, 20292, 44936, 61713]], [], [], [[15, 9202, 17476, 63624, 65433]]], [[[15, 8882, 20292, 61713, 63624]], [], [[15, 8946, 18244, 35720, 61713]], [[15, 8946, 17732, 36744, 63897]], [], [], [[15, 3976, 8946, 17652, 61713]], [], [], [[15, 8882, 20292, 34968, 61713]], [[15, 8946, 17732, 63897, 65416], [15, 8946, 20468, 34952, 62225], [15, 9202, 17476, 63897, 65416]], [], [[15, 8946, 20292, 44952, 61713]], [], [], []], [[], [[15, 8946, 20292, 36744, 61841], [143, 8946, 20292, 36744, 61713]], [], [[15, 784, 8946, 17476, 63624]], [[15, 4369, 20468, 26358, 64136], [15, 4881, 20468, 26358, 63624]], [], [[15, 8866, 20468, 53196, 61713]], [], [[15, 8946, 17732, 36744, 61713]], [[15, 7953, 9202, 17652, 63624]], [], [], [[15, 3840, 4881, 25844, 63624]], [], [[15, 784, 9202, 17476, 63624], [15, 3840, 4369, 25266, 64716]], [[15, 8946, 17732, 61713, 65416]]], [[[15, 8946, 17740, 36744, 61713]], [], [], [[271, 8946, 17732, 36744, 61713]], [[15, 7953, 9202, 17908, 63624], [15, 8848, 20292, 36744, 61713]], [], [], [[15, 8946, 20292, 36744, 62353], [655, 8946, 20292, 36744, 61713]], [[15, 8946, 17748, 36744, 61713]], [[15, 8946, 20292, 21265, 63624]], [], [], [], [[4, 3840, 4369, 8946, 24712], [12, 3840, 4369, 8946, 24704]], [[15, 3840, 8946, 29073, 52428], [15, 8946, 18244, 36744, 61713]], []], [[], [], [[15, 3840, 4369, 26356, 64136]], [], [[12, 240, 8738, 20292, 61841]], [[15, 648, 8946, 20292, 61713]], [], [[15, 240, 28484, 34952, 62225], [15, 8432, 20292, 34952, 62225]], [], [], [], [], [], [], [], [[15, 240, 8738, 20300, 61841], [15, 248, 8738, 20292, 61841]]], [[[12, 3840, 8946, 17476, 61841], [12, 3968, 8946, 17476, 61713]], [[15, 8946, 20292, 40840, 61713]], [], [], []]]
  | 5 => [[[[15, 240, 8738, 20292, 51592, 61713], [15, 240, 20292, 25378, 34952, 61713], [15, 3855, 8946, 20292, 36744, 61713]], [[15, 240, 3976, 8946, 17476, 61713], [15, 3840, 4369, 8746, 17652, 63624], [15, 3840, 4373, 8742, 17652, 63624], [15, 3844, 4373, 8738, 17652, 63624]], [[12, 3840, 4369, 8750, 17652, 63624], [12, 3852, 4369, 8738, 17652, 63624], [15, 240, 8738, 17748, 36744, 61712], [15, 3840, 4369, 8747, 17652, 63624], [15, 7953, 12066, 13107, 17652, 63624]], [[12, 3840, 4369, 8751, 17652, 63624], [15, 240, 8738, 17748, 36744, 61713], [15, 4593, 8946, 20292, 36744, 61713]], [[15, 240, 8738, 20292, 21265, 63624], [15, 240, 8738, 20292, 51596, 61713], [15, 240, 20292, 25382, 34952, 61713], [15, 240, 28518, 34952, 62259, 65365], [15, 3840, 4497, 8866, 17652, 63624], [15, 3968, 4369, 8866, 17652, 63624], [15, 5009, 8946, 17476, 36744, 63624]], [[15, 3840, 4369, 8750, 17652, 63624], [15, 3840, 8946, 12689, 25796, 63624], [15, 4369, 8946, 12160, 25796, 63624], [15, 8946, 12160, 12689, 17476, 63624], [15, 8946, 20292, 36744, 61680, 61713]], [[1, 3840, 4383, 8751, 17652, 63624], [15, 240, 8738, 20228, 53132, 61713], [15, 3840, 4369, 8751, 17652, 63624], [15, 3976, 8946, 17476, 61713]], [], [[15, 3840, 4371, 8751, 17652, 63624], [15, 3844, 8738, 17652, 34956, 61713], [15, 3844, 8742, 17652, 34952, 61713], [15, 8946, 17652, 20468, 36744, 61713]], [[4, 3840, 4383, 8751, 17652, 63624], [4, 3840, 8751, 17652, 61713, 63624], [15, 240, 8738, 18244, 36744, 61713], [15, 3840, 4369, 8746, 17660, 63624]], [[15, 3840, 4369, 8751, 17652, 63628], [15, 3840, 4373, 8751, 17652, 63624], [15, 3844, 4369, 8751, 17652, 63624], [15, 8946, 20292, 34952, 62225]], [[15, 3844, 4383, 8738, 17652, 63624], [15, 3844, 8738, 17652, 61713, 63624]], [[4, 15, 4369, 25330, 36744, 61440]], [], [[15, 3840, 4369, 8751, 17660, 63624], [15, 3840, 4377, 8751, 17652, 63624]], [[15, 240, 8738, 20292, 35064, 61841], [15, 3840, 4369, 8946, 24704, 64716], [15, 3840, 4369, 8946, 25796, 63624]]], [[[15, 255, 3976, 8946, 17476, 61713]], [[4, 240, 8746, 20292, 34952, 61713], [12, 240, 8738, 20292, 34952, 61713], [15, 240, 8738, 20292, 53196, 61841], [15, 3840, 4369, 8751, 17652, 63880], [15, 3840, 4369, 8751, 17908, 63624], [15, 3840, 4369, 9007, 17652, 63624], [15, 8946, 20292, 36744, 61713, 61937]], [[12, 3840, 4369, 8738, 17652, 63897], [13, 240, 8738, 20292, 34952, 61713], [15, 3840, 4383, 8994, 17652, 63624]], [], [[15, 240, 8738, 20292, 34952, 61713], [15, 496, 7953, 8946, 17476, 63624], [15, 3840, 4383, 8751, 17652, 63624], [15, 3856, 4593, 8946, 17476, 63624]], [[12, 240, 8738, 20292, 34956, 61713], [15, 896, 4369, 8946, 17476, 63624]], [[12, 3840, 4369, 8946, 17476, 63624], [15, 240, 8738, 20292, 52104, 61713], [15, 242, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8751, 17652, 63640], [15, 3840, 4369, 8767, 17652, 63624], [15, 3856, 4369, 8751, 17652, 63624], [15, 4369, 8946, 20292, 62194, 65416]], [[13, 3840, 4369, 8946, 17476, 63624], [15, 240, 3840, 4881, 25668, 63624], [15, 3840, 4369, 8946, 25804, 63624], [15, 3840, 4383, 8754, 17652, 63624], [15, 3840, 8754, 17652, 61713, 63624], [15, 3856, 4383, 8738, 17652, 63624], [15, 3856, 8738, 17652, 61713, 63624]], [[12, 240, 8738, 20292, 34959, 61713], [12, 240, 8738, 20292, 61713, 63624], [15, 240, 516, 28518, 34952, 61713], [15, 240, 8738, 20292, 34952, 61717], [15, 240, 8738, 20292, 34956, 61713], [15, 240, 8742, 20292, 34952, 61713], [15, 244, 8738, 20292, 34952, 61713], [15, 4080, 8866, 17476, 36744, 61713]], [[4, 3840, 4369, 8946, 17487, 63624], [12, 240, 8738, 20300, 34952, 61713], [15, 3840, 4369, 8946, 17476, 63624], [15, 3840, 4369, 8946, 17652, 59528], [15, 7953, 9202, 17476, 63624], [15, 8946, 13311, 17476, 36744, 61713]], [[1, 240, 8751, 20292, 61713, 63624], [12, 3840, 4369, 8946, 17476, 63628], [15, 246, 8738, 20292, 34952, 61713]], [[12, 240, 3840, 8738, 17476, 61841], [12, 240, 3968, 8738, 17476, 61713], [12, 4369, 8738, 17652, 20292, 63624], [15, 3840, 4383, 8758, 17652, 63624], [15, 3860, 4383, 8738, 17652, 63624], [15, 3968, 8946, 17476, 35064, 61713], [15, 8946, 20292, 39321, 43690, 61713]], [[15, 240, 4369, 25122, 36744, 65348], [15, 240, 4369, 28484, 36744, 61986], [15, 240, 8738, 20292, 34952, 61721], [15, 240, 8738, 20292, 34956, 61717], [15, 240, 8738, 20292, 40840, 61713], [15, 240, 8739, 20292, 61713, 63624], [15, 240, 8742, 20292, 34952, 61717], [15, 240, 8742, 20292, 34956, 61713], [15, 240, 8746, 20292, 34952, 61713], [15, 244, 8738, 20292, 34952, 61717], [15, 244, 8738, 20292, 34956, 61713], [15, 244, 8742, 20292, 34952, 61713], [15, 248, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8751, 17652, 64136], [15, 3840, 4369, 8751, 18164, 63624]], [[4, 240, 8751, 20292, 61713, 63624], [4, 3840, 4369, 8946, 17487, 63628], [4, 3840, 4369, 8950, 17487, 63624], [4, 3840, 4373, 8946, 17487, 63624], [4, 3840, 8946, 17484, 34952, 61713], [12, 240, 8738, 20292, 34952, 61725], [12, 240, 8750, 20292, 34952, 61713], [12, 252, 8738, 20292, 34952, 61713], [12, 3840, 8946, 17476, 34952, 61713], [15, 240, 8738, 20292, 61715, 63624], [15, 242, 8738, 20292, 61713, 63624], [15, 3840, 4369, 8746, 17652, 63897], [15, 3840, 4369, 8946, 17476, 63628], [15, 8946, 12160, 17476, 61713, 63624]], [[12, 3840, 4369, 8946, 17484, 63624], [13, 3840, 8946, 17476, 34952, 61713], [15, 250, 8738, 20292, 34952, 61713], [15, 496, 8738, 20292, 34952, 61712], [15, 4369, 8946, 17652, 36744, 63624]], [[15, 240, 8738, 20292, 35208, 61713], [15, 240, 8738, 20292, 61717, 63624], [15, 240, 8742, 20292, 61713, 63624], [15, 240, 8994, 20292, 34952, 61713], [15, 244, 8738, 20292, 61713, 63624], [15, 496, 7953, 9202, 17476, 63624], [15, 496, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8946, 25812, 63624]]], [[[15, 240, 8738, 20292, 34952, 61725], [15, 240, 8750, 20292, 34952, 61713], [15, 240, 8751, 20292, 34952, 61712], [15, 252, 8738, 20292, 34952, 61713], [15, 3856, 8738, 17652, 34968, 61713], [15, 3856, 8754, 17652, 34952, 61713]], [[12, 3840, 4369, 8946, 17487, 63624], [12, 3840, 8946, 17476, 34956, 61713], [15, 240, 8738, 20228, 36744, 61713], [15, 3840, 4369, 8946, 17484, 63624], [15, 3840, 4369, 8950, 17476, 63628], [15, 3840, 8946, 25684, 43160, 61713], [15, 3844, 4373, 8946, 17476, 63624], [15, 8946, 20292, 20303, 36744, 61713]], [[12, 3840, 4369, 8958, 17476, 63624], [12, 3840, 4381, 8946, 17476, 63624], [12, 3852, 4369, 8946, 17476, 63624], [15, 255, 8738, 20292, 34952, 61712]], [[15, 240, 8738, 20292, 35212, 61713], [15, 240, 8738, 20292, 61717, 63628], [15, 240, 8738, 20292, 61721, 63624], [15, 240, 8746, 20292, 61713, 63624], [15, 240, 8998, 20292, 34952, 61713], [15, 248, 8738, 20292, 34959, 61713], [15, 248, 8738, 20292, 61713, 63624], [15, 500, 8738, 20292, 34952, 61713], [15, 4080, 8946, 17652, 36744, 61713], [15, 8946, 20292, 36744, 45050, 61713]], [[12, 3840, 8946, 17476, 61713, 63624], [15, 240, 8738, 20300, 34952, 61721], [15, 240, 8746, 20292, 34952, 61721], [15, 240, 8746, 20300, 34952, 61713], [15, 248, 8738, 20292, 34952, 61721], [15, 248, 8738, 20300, 34952, 61713], [15, 248, 8746, 20292, 34952, 61713], [15, 3840, 4369, 8946, 17476, 63880], [15, 3840, 4369, 8946, 17732, 63624], [15, 3840, 4497, 8946, 17604, 63624], [15, 3968, 4369, 8946, 17604, 63624], [15, 3968, 8946, 20292, 34952, 61713], [15, 8177, 8946, 17476, 36744, 61713]], [[12, 240, 4369, 25122, 36744, 61440], [15, 3840, 4369, 8946, 26308, 63624]], [[15, 240, 3840, 8738, 17484, 61841], [15, 240, 3848, 8738, 17476, 61841], [15, 240, 3968, 8738, 17484, 61713], [15, 240, 3976, 8738, 17476, 61713], [15, 240, 4369, 25122, 25668, 36744], [15, 240, 8994, 20292, 61713, 63624], [15, 496, 8738, 20292, 61713, 63624], [15, 4369, 8746, 17652, 20292, 63624], [15, 4383, 8946, 20292, 36744, 61713]], [[4, 3840, 8946, 17487, 61713, 63624]], [[15, 240, 8751, 20292, 61713, 63624], [15, 3840, 4369, 8946, 17487, 63628], [15, 3844, 4369, 8946, 17487, 63624]], [[12, 3840, 8946, 17476, 34952, 61725], [12, 3852, 8946, 17476, 34952, 61713], [15, 240, 8738, 20292, 61727, 63624], [15, 3840, 4369, 8874, 17652, 61576], [15, 3840, 4369, 8946, 17476, 63640], [15, 3840, 4369, 8946, 17492, 63624], [15, 3840, 4369, 8954, 17484, 63624], [15, 3840, 4377, 8946, 17484, 63624], [15, 8946, 20292, 36744, 61713, 62451]], [[4, 240, 4369, 25135, 36744, 61440], [15, 240, 8738, 20292, 34952, 62225], [15, 240, 8738, 20292, 35464, 61713], [15, 240, 8994, 20292, 35208, 61713], [15, 496, 8738, 20292, 35208, 61713], [15, 496, 8994, 20292, 34952, 61713], [15, 752, 8738, 20292, 34952, 61713], [4383, 8751, 17652, 20292, 63624]], [[4, 240, 4383, 25122, 36744, 61440], [15, 255, 8738, 20468, 36744, 61713], [15, 3844, 8946, 17476, 61713, 63624], [15, 4369, 8751, 17652, 20292, 63624]], [[15, 754, 8738, 20292, 34952, 61713], [15, 4383, 8946, 17652, 36744, 63624]], [[15, 240, 3840, 4369, 26180, 64136]], [[15, 240, 8738, 20292, 34952, 62229], [15, 240, 8738, 20292, 35468, 61713], [15, 240, 9010, 20292, 34952, 61712], [15, 756, 8738, 20292, 34952, 61713]], [[15, 240, 8738, 20292, 35224, 61713], [15, 240, 9010, 20292, 34952, 61713], [15, 3840, 4369, 8946, 17732, 63880], [15, 3840, 4369, 8946, 17988, 63624], [15, 3840, 4369, 9202, 17732, 63624], [15, 3840, 8946, 17652, 61713, 65416]]], [[[12, 144, 3840, 8738, 17476, 61713], [15, 240, 4369, 25088, 28484, 34952]], [[15, 240, 8738, 20292, 62225, 63624], [15, 752, 8738, 20292, 61713, 63624], [15, 3840, 4369, 8751, 17652, 24712], [15, 4080, 8946, 17476, 35464, 61713]], [[12, 3840, 4369, 8946, 17476, 63897], [15, 240, 3976, 8738, 20428, 61713]], [[15, 240, 4369, 20292, 25122, 59528], [15, 255, 8738, 20292, 34968, 61713], [15, 255, 8738, 20308, 34952, 61713], [15, 255, 8754, 20292, 34952, 61713], [15, 384, 8738, 17652, 36744, 61713], [15, 3840, 8946, 21845, 52428, 63897]], [[12, 240, 8738, 20292, 61713, 63897], [15, 3840, 4369, 8946, 17476, 63896], [15, 3840, 4369, 8946, 17748, 63624]], [[15, 240, 8738, 20292, 35720, 61713], [15, 1008, 8738, 20292, 34952, 61713], [15, 3840, 4369, 26358, 64170, 64716], [15, 3840, 8946, 17652, 20881, 63624], [15, 4369, 8946, 17652, 20352, 63624], [15, 5009, 8946, 17476, 36744, 61713]], [[4, 4383, 8946, 17652, 36744, 61440], [15, 240, 8751, 20292, 61727, 63624], [15, 3840, 4369, 8959, 17492, 63624]], [[15, 3840, 4383, 8946, 17492, 63624], [15, 3855, 8946, 17652, 36744, 61713], [15, 3856, 4383, 8946, 17476, 63624], [15, 3856, 8946, 17476, 61713, 63624]], [[15, 240, 4369, 25122, 53196, 63624]], [[15, 3840, 4369, 8946, 17492, 63640], [15, 3840, 4369, 8946, 17508, 63624], [15, 4383, 8751, 17652, 20292, 63624], [15, 7953, 8946, 17476, 36744, 61713]], [[15, 240, 4369, 28484, 43144, 61986], [15, 3840, 4369, 8946, 18244, 63624], [15, 3840, 4369, 8946, 20292, 61576], [15, 4369, 8432, 20292, 43144, 61986], [15, 4369, 8946, 17652, 36744, 63897], [15, 4593, 8946, 17652, 36744, 61713]], [[15, 152, 3840, 8738, 17476, 61713], [15, 240, 4369, 20292, 25122, 65416], [15, 4369, 8946, 20292, 61986, 65416]], [], [[15, 3840, 4369, 8946, 17484, 63897], [15, 3840, 4369, 8954, 17476, 63897]], [[15, 8946, 20292, 28662, 36744, 61713]], [[15, 240, 8746, 20292, 61713, 63897], [15, 248, 8738, 20292, 61713, 63897], [15, 3840, 4369, 8946, 17476, 64152], [15, 3840, 4369, 8946, 18004, 63624], [15, 3840, 4369, 8946, 25844, 63624], [15, 8946, 20292, 36744, 52428, 61713]]], [[[12, 3840, 8946, 17476, 61713, 63897], [15, 240, 8738, 20292, 35464, 62225], [15, 240, 8738, 20292, 35976, 61713], [15, 752, 8738, 20292, 34952, 62225], [15, 752, 8738, 20292, 35464, 61713], [15, 1264, 8738, 20292, 34952, 61713], [15, 3856, 8946, 17492, 34952, 61713], [15, 8946, 20292, 26214, 36744, 61713]], [[15, 276, 3840, 8738, 17652, 63624], [15, 8946, 20292, 36744, 61713]], [[1, 15, 8946, 20292, 36744, 61713], [15, 240, 8738, 20292, 53128, 61713]], [[1, 4383, 8738, 17652, 36744, 63624]], [[15, 240, 7953, 8738, 17732, 63880], [15, 240, 7953, 8994, 17732, 63624], [15, 240, 8738, 20292, 35980, 61713], [15, 496, 7953, 8738, 17732, 63624], [15, 496, 7953, 8994, 17476, 63624], [15, 1268, 8738, 20292, 34952, 61713]], [[4, 15, 8946, 20292, 36744, 61713], [15, 240, 8738, 17156, 34952, 61713], [15, 3840, 4369, 8946, 17988, 64136]], [[15, 3840, 4369, 8815, 17652, 63624], [15, 3904, 4369, 8751, 17652, 63624]], [[15, 240, 8738, 20292, 62225, 64136], [15, 1264, 8738, 20292, 61713, 63624], [15, 3840, 4383, 8802, 17652, 63624], [15, 3840, 8802, 17652, 61713, 63624], [15, 3904, 4383, 8738, 17652, 63624], [15, 3904, 8738, 17652, 61713, 63624], [15, 7967, 8946, 17476, 36744, 61713]], [[15, 8946, 20292, 61713, 65416]], [[15, 3840, 4369, 8946, 17524, 63624], [15, 3840, 4369, 8946, 17612, 61576]], [], [[15, 240, 8738, 19780, 36744, 61713], [15, 240, 8738, 20292, 36232, 61713], [15, 255, 8946, 20292, 36744, 61713], [15, 1520, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8751, 17652, 59528], [15, 4369, 8746, 17652, 36744, 63624], [15, 8946, 17652, 22005, 36744, 61713]], [[15, 287, 3840, 8738, 17652, 63624]], [[15, 240, 20292, 25378, 36744, 61713], [15, 8946, 17652, 20292, 36744, 61713]], [[15, 8946, 13119, 17476, 36744, 61713]], [[15, 3840, 4369, 8946, 18020, 63624], [15, 4369, 8866, 20292, 35064, 61568]]], [[[15, 4369, 8751, 17652, 36744, 63624]], [[15, 8946, 9202, 17476, 36744, 61713]], [[15, 240, 4369, 20292, 25122, 43144], [15, 240, 4369, 25122, 28484, 34952]], [[15, 384, 8946, 17476, 36744, 61713], [15, 3840, 4369, 8944, 26356, 63624]], [[12, 3840, 4369, 8946, 26358, 63624], [15, 3840, 4497, 8946, 17652, 63624], [15, 3968, 4369, 8946, 17652, 63624]], [[4, 3840, 4369, 8946, 26367, 63624]], [[15, 240, 8738, 20292, 36488, 61713], [15, 240, 12066, 17988, 34952, 62225], [15, 240, 12066, 17988, 35464, 61713], [15, 240, 13107, 20292, 43144, 61713], [15, 240, 13107, 28484, 34952, 61713], [15, 752, 12066, 17476, 35464, 61713], [15, 752, 12066, 17988, 34952, 61713], [15, 1776, 8738, 20292, 34952, 61713]], [[15, 240, 8738, 18244, 39321, 63624], [15, 3840, 4369, 8832, 17652, 63624]], [], [[4, 3840, 4369, 8959, 26358, 63624], [15, 8946, 12274, 20292, 36744, 61713]], [[15, 3840, 4369, 17652, 25250, 63624]], [[15, 3840, 4369, 8946, 26358, 63628], [15, 3840, 4373, 8946, 26358, 63624], [15, 3844, 4369, 8946, 26358, 63624], [15, 3968, 8946, 17652, 34952, 61713]], [], [[15, 4383, 8946, 17652, 36744, 61713]], [[12, 240, 8738, 20292, 36744, 61713], [15, 3840, 4369, 17652, 25254, 63624], [15, 8946, 20292, 34952, 61937, 65297], [15, 8946, 20292, 35064, 36744, 61713]], []], [[[4, 3840, 8959, 26358, 34952, 61713], [12, 4369, 8946, 17476, 36744, 63624], [15, 3840, 4369, 17652, 26214, 64136], [15, 3840, 4881, 17652, 26214, 63624], [15, 8946, 20292, 36744, 53196, 61713]], [[15, 240, 8738, 20292, 36744, 61713]], [[15, 3840, 4369, 17652, 25258, 63624], [15, 3844, 8946, 26358, 34952, 61713]], [[15, 242, 8738, 20292, 36744, 61713], [15, 4369, 8866, 17652, 36744, 61568]], [], [[12, 4369, 8738, 17652, 53196, 63624], [15, 240, 8738, 20292, 36744, 61717], [15, 240, 8738, 20292, 36748, 61713], [15, 240, 8742, 20292, 36744, 61713], [15, 244, 8738, 20292, 36744, 61713]], [], [[15, 3840, 4369, 17652, 25263, 63624], [15, 4080, 8946, 17476, 36744, 61712], [15, 4369, 8751, 17652, 20352, 63624], [15, 8946, 20292, 43690, 61713, 63897]], [[15, 240, 8738, 20292, 61713, 65416], [15, 3840, 4383, 17652, 25250, 63624], [15, 4080, 8946, 17476, 36744, 61713]], [[15, 240, 8738, 20292, 36744, 61721], [15, 240, 8746, 20292, 36744, 61713], [15, 248, 8738, 20292, 36744, 61713], [15, 896, 8946, 17476, 36744, 61713], [15, 3840, 4369, 8882, 17620, 63624], [15, 8946, 20292, 21845, 36744, 61713]], [[12, 3840, 8946, 17476, 36744, 61713], [15, 3840, 4369, 17652, 25266, 63624], [15, 4593, 8946, 17476, 36744, 63897]], [], [[15, 240, 8994, 20292, 36744, 61713], [15, 496, 8738, 20292, 36744, 61713], [15, 7953, 8946, 20292, 61713, 63624]], [], [[15, 240, 4369, 20292, 25250, 63624], [15, 3840, 4369, 8946, 17476, 59544], [15, 3841, 8946, 17476, 36744, 61713]], [[15, 4080, 8946, 17476, 61713, 65416]]], [[], [[15, 240, 8738, 20292, 36760, 61713], [15, 3840, 4369, 8751, 25844, 63624], [15, 3840, 4369, 8946, 17652, 61576], [15, 3844, 8946, 17476, 36744, 61713], [15, 8944, 20292, 34952, 61713, 65297]], [], [[15, 240, 8738, 17860, 36744, 61713], [15, 3840, 4369, 20292, 25330, 63624], [15, 4593, 8946, 17476, 36744, 61456], [15, 7967, 8946, 20292, 34952, 61713]], [[15, 240, 4369, 20292, 26214, 64136], [15, 240, 4881, 20292, 26214, 63624]], [[15, 240, 8751, 20292, 61713, 65416], [15, 3844, 8946, 17476, 36748, 61713], [15, 4369, 8751, 17652, 53196, 63624]], [[13, 4369, 8946, 17476, 36744, 61440], [15, 240, 8738, 20292, 61727, 65416]], [[15, 240, 8738, 20292, 36744, 62225], [15, 752, 8738, 20292, 36744, 61713], [15, 4095, 8946, 17476, 36744, 61713]], [], [[15, 240, 4369, 25122, 53128, 62532], [15, 3840, 4369, 8751, 25852, 63624], [15, 3840, 4369, 8866, 17652, 63624]], [], [], [[15, 240, 8738, 16644, 36744, 61713], [15, 3840, 4369, 25250, 52476, 63624], [15, 3855, 8946, 17476, 36744, 61713]], [[15, 240, 3856, 8994, 17476, 63624], [15, 3840, 4369, 8870, 17652, 63624], [15, 3856, 8946, 17476, 36744, 61713]], [[4, 3840, 4369, 8751, 26358, 63624], [15, 3840, 4369, 8959, 17652, 61576]], [[15, 4593, 8946, 17476, 36744, 61713]]], [[], [[15, 3840, 4369, 8874, 17652, 63624], [15, 8946, 20292, 34952, 61727, 65297]], [[15, 3840, 4369, 16628, 25334, 63624]], [[15, 240, 4369, 25122, 36744, 64716], [15, 3855, 8946, 17476, 61713, 65416]], [[15, 3840, 4369, 8946, 25668, 63624]], [[4, 3840, 8751, 26358, 34952, 61713], [15, 240, 4369, 25122, 53196, 65416]], [[15, 3840, 4369, 8879, 17652, 63624], [15, 3968, 4369, 8751, 17652, 63624], [15, 8946, 13299, 20292, 36744, 61713]], [[15, 240, 4369, 28484, 44936, 61986], [15, 3840, 4383, 8866, 17652, 63624], [15, 3840, 8866, 17652, 61713, 63624], [15, 3968, 4383, 8738, 17652, 63624], [15, 3968, 8738, 17652, 61713, 63624]], [[15, 240, 8738, 16640, 53196, 63897]], [[15, 3840, 4369, 8882, 17652, 63624]], [[15, 240, 8738, 20292, 43400, 61713]], [], [[15, 240, 4369, 26180, 36744, 61952], [15, 240, 8751, 20292, 43144, 61713], [15, 240, 8751, 28484, 34952, 61713], [15, 3840, 4369, 8946, 25676, 63624]], [[15, 240, 3856, 9010, 17476, 63624], [15, 240, 8738, 20292, 43144, 61727], [15, 752, 12066, 17476, 36744, 61713], [15, 3856, 8946, 17476, 36760, 61713], [15, 3872, 8946, 17476, 36744, 61713], [15, 4383, 8946, 17476, 36744, 63897], [15, 4607, 8946, 17476, 36744, 61713]], [], []], [[[15, 8946, 12274, 17652, 36744, 61713]], [[12, 4369, 8946, 17476, 36744, 61713], [15, 3976, 8946, 8959, 17476, 61713], [15, 8946, 16371, 17476, 36744, 61713]], [[15, 4369, 8946, 20292, 36744, 62080]], [], [[15, 240, 8738, 20292, 34952, 61841], [15, 3840, 4369, 8946, 25684, 63624]], [[15, 240, 8738, 20292, 43656, 61713], [15, 8946, 20292, 43690, 52428, 61713]], [[15, 4383, 8946, 17476, 36744, 61456]], [[15, 576, 8946, 20292, 36744, 61713], [15, 3856, 8946, 13299, 17476, 63624], [15, 7953, 8946, 9202, 17476, 63624]], [[15, 240, 3840, 8738, 17748, 63896], [15, 240, 3840, 13073, 26180, 63624], [15, 240, 4369, 25122, 36744, 62532], [15, 3840, 4369, 8944, 26180, 63624]], [[15, 240, 3840, 4369, 25092, 34952], [15, 3840, 4369, 8946, 17604, 63624]], [[15, 240, 20292, 25378, 34952, 65297], [15, 3840, 4369, 8946, 26180, 63624], [15, 3841, 8946, 20292, 34952, 61713]], [[4, 3840, 4369, 8946, 16392, 63624], [15, 240, 8738, 20292, 61841, 63624]], [[15, 240, 4369, 25126, 36744, 62532], [15, 240, 8738, 18244, 34952, 63897], [15, 240, 8738, 20292, 34952, 61849], [15, 240, 8874, 20292, 34952, 61713], [15, 3840, 4369, 25330, 52428, 63624], [15, 4080, 8946, 20468, 36744, 61713]], [[15, 3840, 4369, 8946, 16628, 63624], [15, 3844, 8946, 20292, 34952, 61713], [15, 8946, 17476, 20303, 36744, 61713], [15, 8946, 17487, 20292, 36744, 61713]], [[15, 4369, 8866, 17652, 20292, 63624]], [[12, 240, 4369, 8738, 20292, 61568], [15, 240, 3976, 8738, 20292, 61713]]], [[[15, 8946, 17652, 21845, 36744, 61713]], [[15, 3840, 4369, 8946, 17612, 63624]], [[4, 15, 3840, 4369, 25330, 63624], [4, 3840, 4369, 8946, 16399, 63624], [15, 4383, 8946, 17476, 36744, 61713]], [[15, 240, 8738, 17908, 36744, 61713], [15, 240, 8738, 18244, 63624, 63897], [15, 496, 8738, 17652, 36744, 61713], [15, 3840, 4369, 8751, 17652, 61576], [15, 8946, 20292, 28518, 36744, 61713]], [[15, 240, 4369, 25122, 36744, 65484], [15, 3840, 4369, 8946, 25700, 63624], [15, 3968, 8946, 20420, 34952, 61713]], [[15, 240, 4369, 25135, 36744, 62532]], [[15, 240, 4383, 25122, 36744, 62532]], [[15, 240, 3840, 20757, 25126, 63624], [15, 240, 4369, 20228, 25126, 63624], [15, 3840, 4369, 17652, 25250, 65416], [15, 3968, 8946, 17476, 61713, 63624]], [], [[4, 15, 3840, 25330, 34952, 61713], [4, 15, 8946, 20224, 34952, 61713], [15, 3840, 4369, 8946, 17620, 63624], [15, 3856, 8946, 20292, 34952, 61713]], [[15, 240, 4369, 8994, 17476, 64136], [15, 240, 4369, 8994, 17988, 63624], [15, 240, 4881, 8738, 17732, 63624], [15, 3840, 4369, 17652, 25330, 63624]], [[12, 3840, 4369, 8946, 17476, 61568], [15, 8946, 20292, 34952, 62259, 65297], [15, 8946, 20292, 36744, 36856, 61713]], [[15, 3840, 4369, 8848, 17476, 63624]], [[15, 3904, 8946, 17476, 36744, 61713]], [[4, 15, 4369, 8946, 24576, 36744], [15, 240, 3840, 8738, 17612, 61849], [15, 240, 3840, 8874, 17612, 61713], [15, 240, 3976, 8738, 17476, 61849], [15, 240, 3976, 8738, 17612, 61713], [15, 240, 3976, 8874, 17476, 61713], [15, 240, 4369, 26180, 36744, 61986], [15, 240, 8738, 20228, 51340, 61713], [15, 496, 8738, 17908, 36744, 61713], [15, 4369, 8751, 20292, 26358, 63624]], [[15, 3840, 4369, 8946, 18116, 63624], [15, 4369, 8946, 18116, 36744, 62080], [15, 5009, 8946, 17476, 36744, 62080]]], [[], [[15, 240, 8738, 17732, 34952, 62225], [15, 240, 8738, 17732, 35464, 61713], [15, 240, 8738, 18244, 34952, 61713], [15, 240, 8994, 17988, 34952, 61713]], [[15, 7953, 8946, 20292, 36744, 61713]], [], [], [[15, 240, 4369, 8994, 17476, 64392], [15, 240, 4369, 8994, 18244, 63624]], [[15, 3840, 4369, 8946, 17484, 61568], [15, 8946, 20292, 43690, 53196, 61713]], [[15, 240, 4369, 8751, 18244, 63624], [15, 3840, 4369, 25844, 61986, 63624]], [[15, 240, 4383, 8738, 18244, 63624], [15, 240, 8738, 18244, 61713, 63624], [15, 8946, 13107, 20292, 21845, 63624]], [[12, 3840, 4369, 8946, 26214, 63624], [15, 240, 3840, 4369, 25250, 64716], [15, 240, 12066, 20292, 34952, 62225], [15, 752, 12066, 20292, 34952, 61713], [15, 3840, 4369, 8930, 17652, 63624], [15, 3840, 4369, 8946, 17636, 63624], [15, 3856, 8946, 20308, 34952, 61713], [15, 3872, 8946, 20292, 34952, 61713]], [[15, 240, 4369, 20292, 25088, 34952]], [[4, 240, 3840, 4369, 25130, 63624], [12, 240, 3840, 4369, 25122, 63624], [12, 3840, 4369, 8738, 16624, 63624], [15, 8946, 13107, 20292, 36744, 61713]], [[15, 240, 8994, 18244, 34952, 61713], [15, 8208, 8946, 20292, 36744, 61713]], [[15, 8946, 13299, 17652, 36744, 61713]], [], [[15, 152, 4369, 8738, 20292, 61440], [15, 3840, 8946, 12689, 17652, 63624], [15, 4369, 8946, 12160, 17652, 63624]]], [[[4, 240, 3840, 4369, 25135, 63624], [15, 240, 4881, 8738, 18244, 63624], [15, 3840, 4369, 8946, 26214, 63628], [15, 3840, 4373, 8946, 26214, 63624], [15, 3844, 4369, 8946, 26214, 63624]], [], [[12, 240, 3840, 25122, 34952, 61713], [12, 240, 8738, 20224, 34952, 61713], [15, 240, 3840, 4369, 25122, 63628], [15, 240, 3844, 4369, 25122, 63624], [15, 244, 3840, 4369, 25122, 63624], [15, 3840, 4369, 25330, 63624, 64716]], [[15, 496, 8946, 17476, 36744, 61713], [15, 4369, 8866, 17652, 36744, 63624]], [[15, 240, 4369, 28484, 34952, 61986], [15, 240, 8738, 21845, 53196, 63897]], [], [[12, 3840, 4369, 8946, 17652, 63624], [15, 240, 3840, 4369, 25126, 63628], [15, 8946, 20292, 20468, 36744, 61713]], [[15, 240, 8738, 18244, 34952, 62225], [15, 3840, 4369, 8944, 17652, 63624], [15, 3844, 8946, 26214, 34952, 61713]], [[15, 8946, 17732, 36744, 61713]], [[4, 3840, 4369, 8946, 17663, 63624], [15, 240, 3844, 25122, 34952, 61713], [15, 240, 8738, 16644, 34952, 65297], [15, 240, 8738, 20224, 34956, 61713], [15, 240, 8738, 20228, 34952, 61713], [15, 244, 3840, 25122, 34952, 61713], [15, 244, 8738, 20224, 34952, 61713], [15, 3840, 4369, 8946, 17652, 63624], [15, 3840, 4369, 8946, 25668, 59528], [15, 4369, 8946, 17652, 36744, 62080]], [[15, 3840, 4369, 8947, 17652, 63624], [15, 3840, 4369, 17652, 25250, 64716]], [[15, 240, 4369, 28484, 61986, 63624], [15, 3840, 4371, 8946, 17652, 63624], [15, 4369, 8432, 20292, 61986, 63624], [15, 5009, 8946, 17476, 36744, 62353]], [[15, 240, 8738, 20292, 44936, 61713], [15, 3856, 8946, 13107, 17476, 63624], [15, 8946, 8959, 20292, 36744, 61713]], [[15, 240, 8738, 20228, 34952, 61717], [15, 3840, 4369, 8946, 17652, 63628], [15, 3840, 4369, 8950, 17652, 63624], [15, 3840, 4373, 8946, 17652, 63624], [15, 3844, 4369, 8946, 17652, 63624]], [[15, 496, 9202, 17476, 36744, 61713], [15, 3840, 4369, 8866, 17492, 63624], [15, 3840, 4369, 8882, 17476, 63624]], [[15, 240, 4369, 25378, 34952, 65348], [15, 240, 8738, 20292, 39304, 61713], [15, 3840, 4369, 8751, 16628, 63624]]], [[[4, 136, 3840, 8738, 17652, 61713], [15, 240, 8738, 20228, 61713, 63624], [15, 264, 8946, 17476, 36744, 61713], [15, 8946, 20292, 26358, 36744, 61713]], [[15, 240, 4369, 28484, 34952, 61999], [15, 3840, 4369, 8946, 17660, 63624], [15, 3840, 4369, 8954, 17652, 63624], [15, 3840, 4377, 8946, 17652, 63624], [15, 3840, 8866, 17652, 52428, 61713]], [[15, 240, 4383, 28484, 34952, 61986], [15, 240, 8738, 18244, 35720, 61713], [15, 1008, 8738, 18244, 34952, 61713]], [[15, 240, 8738, 17732, 36744, 63897], [15, 3840, 4369, 20468, 25250, 63624]], [[15, 3840, 4369, 8946, 17652, 63880], [15, 3840, 4369, 8946, 17908, 63624], [15, 3840, 4369, 9202, 17652, 63624], [15, 3844, 8946, 17652, 34952, 61713]], [[15, 8946, 12274, 17476, 36744, 61713]], [[15, 240, 3976, 8738, 17652, 61713], [15, 3840, 4369, 8959, 17652, 63624]], [[15, 271, 8946, 17476, 36744, 61713], [15, 640, 8946, 20292, 36744, 61713], [15, 3840, 4369, 17652, 25130, 63624], [15, 3840, 4369, 25330, 62532, 63624], [15, 3840, 4383, 8946, 17652, 63624], [15, 3840, 8946, 17652, 61713, 63624], [15, 8946, 20292, 24405, 36744, 61713]], [], [[15, 240, 8738, 20244, 34952, 61713], [15, 3840, 4369, 8946, 17652, 63640], [15, 3840, 4369, 8954, 17660, 63624], [15, 3856, 4369, 8946, 17652, 63624]], [[15, 240, 8738, 17732, 63897, 65416], [15, 240, 8738, 20468, 34952, 62225]], [[15, 3840, 4369, 8751, 17620, 63624]], [[15, 3840, 4369, 17652, 25135, 63624], [15, 8946, 12274, 17476, 61713, 65416]], [[12, 240, 8738, 20292, 39321, 61713], [15, 3840, 4383, 17652, 25122, 63624]], [[15, 240, 8738, 20228, 61727, 63624], [15, 240, 20292, 28518, 34952, 62225], [15, 3840, 4369, 8882, 17476, 63640], [15, 3840, 4369, 8946, 24704, 52428]], [[15, 3840, 4369, 8946, 17652, 64136], [15, 3840, 4369, 8946, 18164, 63624], [15, 3840, 4369, 9202, 17908, 63624], [15, 3840, 4881, 8946, 17652, 63624]]], [[[15, 240, 20292, 25378, 34952, 63897], [15, 3856, 8946, 17652, 34952, 61713]], [[15, 240, 8738, 20292, 36744, 61841], [15, 240, 20292, 25378, 51592, 61713], [15, 4080, 8946, 20292, 36744, 61713], [15, 8946, 20292, 36744, 43770, 61713]], [[15, 7953, 12274, 13299, 17476, 63624], [15, 8946, 12287, 17476, 36744, 61713]], [[15, 240, 4369, 20292, 25122, 63624], [15, 4369, 8946, 20292, 61986, 63624]], [[4, 136, 240, 8738, 20292, 61713], [15, 3840, 4383, 8959, 17652, 63624]], [[15, 240, 8738, 20292, 52428, 61841], [15, 255, 3976, 8738, 17652, 61713], [15, 4369, 8751, 17652, 36744, 61568]], [], [[15, 240, 4369, 20292, 25126, 63624]], [[15, 240, 8738, 17732, 36744, 61713], [15, 240, 8746, 20292, 39321, 61713], [15, 248, 8738, 20292, 39321, 61713]], [[12, 3840, 8946, 17476, 39321, 61713], [15, 496, 7953, 8738, 17652, 63624], [15, 3856, 4593, 8738, 17652, 63624], [15, 7953, 8946, 17652, 36744, 61713]], [], [[4, 3840, 4369, 8746, 17652, 63624], [12, 3840, 4369, 8738, 17652, 63624], [15, 240, 4369, 20292, 25130, 63624], [15, 240, 8708, 20292, 34952, 61713]], [[13, 3840, 4369, 8738, 17652, 63624]], [[15, 640, 12274, 17476, 36744, 61713], [15, 3968, 8946, 17476, 36744, 61713]], [[15, 240, 4369, 20292, 25378, 63624], [15, 8432, 20292, 34952, 61713, 62259]], [[12, 3840, 4369, 8738, 17652, 63628], [15, 240, 8738, 17732, 61713, 65416], [15, 8946, 20292, 34952, 62259, 65365]]], [[[4, 3840, 4369, 8751, 17652, 63624], [15, 240, 4369, 20292, 25135, 63624], [15, 240, 8738, 17740, 36744, 61713], [15, 240, 8751, 20292, 20753, 63624], [15, 3840, 4369, 17652, 26358, 64136], [15, 3840, 4881, 17652, 26358, 63624], [15, 3968, 8738, 17652, 35064, 61713], [15, 4369, 8751, 16624, 20292, 63624], [15, 4369, 8946, 20292, 61999, 63624]], [[5, 3840, 4369, 8751, 17652, 63624], [15, 240, 4383, 20292, 25122, 63624]], [[4, 3840, 8746, 17652, 34952, 61713], [6, 3840, 4369, 8751, 17652, 63624], [15, 8946, 13107, 17652, 36744, 61713]], [[13, 3840, 8738, 17652, 34952, 61713], [15, 240, 8994, 17732, 36744, 61713], [15, 496, 8738, 17732, 36744, 61713], [15, 496, 8994, 17476, 36744, 61713], [15, 4369, 8946, 20292, 61680, 65416]], [[4, 3840, 4369, 8751, 17652, 63628], [4, 3840, 4373, 8751, 17652, 63624], [15, 496, 7953, 8738, 17908, 63624]]]]
  | 6 => [[[[4, 15, 4369, 8946, 20292, 36744, 61440], [15, 240, 4383, 8738, 20292, 61713, 63624], [15, 240, 8738, 16640, 20292, 34952, 61713], [15, 240, 8738, 20292, 51592, 61713], [15, 240, 20292, 25378, 34952, 61713], [15, 3840, 4369, 8751, 17652, 36744, 63624], [15, 3840, 4369, 8946, 26214, 62532, 63624]], [[1, 15, 3840, 8738, 17652, 34952, 61713], [4, 15, 3840, 4369, 8738, 17652, 63628], [4, 15, 3840, 4369, 8742, 17652, 63624], [4, 15, 3840, 4373, 8738, 17652, 63624], [4, 15, 3844, 4369, 8738, 17652, 63624], [15, 240, 3840, 4369, 8751, 17652, 63624], [15, 240, 4369, 8738, 20292, 62708, 63624], [15, 240, 4881, 8738, 20292, 34952, 61713], [15, 240, 8738, 16641, 20292, 34952, 61713], [15, 3840, 4369, 8746, 17652, 63624]], [[15, 240, 271, 8738, 17476, 36744, 61713], [15, 240, 3840, 4369, 25122, 62532, 63624], [15, 240, 3840, 4369, 25668, 61986, 63624], [15, 240, 3840, 4383, 8738, 17652, 63624], [15, 240, 3840, 8738, 17652, 61713, 63624], [15, 240, 4369, 8738, 20224, 62532, 63624], [15, 240, 4369, 12032, 17476, 61986, 63624], [15, 240, 8738, 20292, 24405, 36744, 61713], [15, 3840, 4369, 8432, 17476, 61986, 63624], [15, 3840, 4369, 8946, 17652, 52476, 63624]], [[15, 240, 3840, 8738, 17476, 37145, 63624], [15, 240, 3848, 8738, 17652, 34952, 61713], [15, 248, 3840, 8738, 17652, 34952, 61713]], [[4, 15, 3840, 8738, 17652, 34952, 61713], [15, 240, 3840, 4369, 8738, 17652, 63640], [15, 240, 3840, 4369, 8754, 17652, 63624], [15, 240, 3840, 4369, 8930, 17476, 63624], [15, 240, 3856, 4369, 8738, 17652, 63624], [15, 240, 3904, 8738, 20292, 34952, 61713], [15, 240, 8738, 16644, 20292, 34952, 61713], [15, 240, 8738, 20292, 34952, 61713, 65399], [15, 640, 4369, 8946, 17476, 36744, 63624], [15, 3840, 4369, 8751, 17652, 52428, 63624]], [[5, 15, 3840, 8738, 17652, 34952, 61713], [12, 15, 3840, 4369, 8738, 17652, 63624], [15, 130, 4369, 8946, 17476, 36744, 61440], [15, 3840, 4369, 8320, 8946, 25796, 63624], [15, 3840, 4369, 8751, 17652, 26214, 63624]], [[6, 15, 3840, 8738, 17652, 34952, 61713], [15, 240, 7953, 8738, 17732, 34952, 61696], [15, 3840, 4369, 8751, 17652, 63624]], [[1, 15, 3840, 4369, 8751, 17652, 63624], [15, 3840, 4369, 8751, 17652, 61986, 63624], [15, 3840, 4369, 8751, 17652, 63624, 65416]], [[1, 15, 3840, 4383, 8738, 17652, 63624], [1, 15, 3840, 8738, 17652, 61713, 63624], [4, 15, 3840, 8738, 17652, 34952, 61717], [4, 15, 3840, 8738, 17652, 34956, 61713], [4, 15, 3840, 8742, 17652, 34952, 61713], [4, 15, 3844, 8738, 17652, 34952, 61713], [15, 240, 3840, 4369, 25135, 34952, 62532], [15, 240, 4369, 8751, 17476, 36608, 63624], [15, 240, 4369, 8751, 17476, 36744, 63488]], [[15, 240, 3840, 8738, 17476, 37151, 63624], [15, 240, 8738, 20292, 20324, 34952, 61713]], [[4, 15, 3840, 4369, 8751, 17652, 63624], [15, 240, 3840, 4369, 8738, 17652, 64136], [15, 240, 3840, 4369, 8738, 18164, 63624], [15, 240, 3840, 4369, 8946, 25796, 63624], [15, 240, 3840, 4881, 8738, 17652, 63624], [15, 240, 8738, 20292, 39321, 53196, 61713], [15, 255, 3840, 8738, 17652, 34952, 61713]], [[4, 15, 3840, 4383, 8738, 17652, 63624], [4, 15, 3840, 8738, 17652, 61713, 63624], [15, 240, 3856, 8738, 17652, 34952, 61713], [15, 240, 4401, 8738, 20292, 34952, 61713], [15, 248, 3840, 8738, 17660, 34952, 61713]], [[15, 240, 4080, 8738, 20292, 36744, 61713]], [[15, 20, 3840, 4369, 8738, 17652, 63624], [15, 240, 4369, 8994, 17476, 63624, 65280], [15, 3840, 4369, 8946, 17652, 62532, 63624]], [[15, 240, 4369, 8738, 17604, 36744, 63624], [15, 240, 4383, 8738, 20292, 61727, 63624], [15, 240, 8738, 20292, 34952, 36744, 61713], [15, 3840, 4369, 8751, 17652, 26223, 63624]], [[12, 240, 8738, 20292, 34952, 52428, 61713], [15, 240, 3840, 4383, 8751, 17652, 63624], [15, 240, 3840, 8751, 17652, 61713, 63624], [15, 240, 3840, 13107, 21845, 26214, 63624], [15, 240, 8738, 16655, 20292, 34952, 61713], [15, 3840, 4369, 8320, 8946, 17476, 63624], [15, 3840, 4369, 8946, 25796, 63624]]], [[[15, 240, 3840, 8738, 17652, 61727, 63624], [15, 240, 4369, 7953, 8994, 17476, 63624], [15, 255, 3840, 4369, 8751, 17652, 63624], [15, 3840, 4369, 8946, 17652, 63624, 64250]], [[4, 8, 240, 8738, 20292, 34952, 61713], [4, 15, 3840, 4369, 8946, 24576, 34952], [12, 240, 3840, 4369, 8946, 17476, 63624], [12, 240, 8738, 20292, 34952, 61713], [15, 240, 4369, 12066, 17988, 34952, 61952], [15, 240, 8738, 20292, 28662, 34952, 61713], [15, 255, 3840, 4383, 8738, 17652, 63624], [15, 255, 3840, 8738, 17652, 61713, 63624], [15, 3840, 4369, 8322, 8946, 17476, 63624], [15, 3840, 4369, 8946, 12066, 17652, 63624]], [[15, 143, 4369, 8946, 17476, 36744, 61440]], [[4, 240, 255, 8738, 20292, 34952, 61713], [15, 240, 4369, 8946, 20292, 36744, 61713]], [[4, 240, 3840, 4369, 8946, 17487, 63624], [12, 240, 3840, 8738, 17476, 39321, 61713], [12, 3840, 4369, 8946, 17476, 52428, 63624], [15, 20, 3840, 8738, 17652, 34952, 61713], [15, 240, 3840, 4369, 8946, 17476, 63624], [15, 240, 4369, 26214, 36744, 61986, 62532], [15, 240, 8738, 17732, 34952, 61713, 65280], [15, 240, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8751, 17652, 61999, 63624], [15, 3840, 4383, 8751, 17652, 63624]], [[1, 15, 240, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 8947, 17476, 63624], [15, 240, 4369, 8738, 20292, 26223, 63624], [15, 240, 8738, 20292, 34952, 36751, 61713], [15, 240, 8738, 20292, 34952, 61713, 65416], [15, 240, 8738, 20292, 34959, 36744, 61713], [15, 240, 8738, 20292, 36744, 61713, 63624], [15, 241, 3840, 4369, 8946, 17476, 63624]], [[4, 8, 3840, 4369, 8946, 17476, 63624], [12, 3840, 4369, 8946, 17476, 63624], [15, 240, 3840, 4371, 8946, 17476, 63624], [15, 240, 8738, 17152, 20292, 34952, 61713], [15, 242, 3840, 4369, 8946, 17476, 63624], [15, 242, 8738, 20292, 34952, 61713]], [[3, 15, 240, 8738, 20292, 34952, 61713], [4, 3840, 4369, 8946, 26367, 34952, 61440], [15, 240, 276, 8738, 20292, 34952, 61440], [15, 240, 4881, 8738, 20292, 34952, 62225], [15, 240, 5393, 8738, 20292, 34952, 61713], [15, 240, 7953, 8738, 17732, 34952, 61713], [15, 3840, 4369, 8328, 8946, 17476, 63624]], [[4, 15, 240, 8738, 20292, 34952, 61713], [12, 240, 3840, 8946, 17476, 34952, 61713], [15, 31, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4369, 8946, 17476, 63628], [15, 240, 3840, 4369, 8950, 17476, 63624], [15, 240, 3840, 4373, 8946, 17476, 63624], [15, 240, 3840, 8738, 20292, 61713, 65416], [15, 240, 3844, 4369, 8946, 17476, 63624], [15, 240, 3968, 8738, 17476, 36744, 61713], [15, 240, 8738, 20292, 34952, 61717], [15, 240, 8738, 20292, 34956, 61713], [15, 240, 8742, 20292, 34952, 61713], [15, 244, 3840, 4369, 8946, 17476, 63624], [15, 244, 8738, 20292, 34952, 61713]], [[4, 3840, 4369, 8946, 17487, 63624], [5, 15, 240, 8738, 20292, 34952, 61713], [12, 240, 4369, 8738, 20292, 36744, 61440], [15, 240, 4369, 8738, 17652, 20292, 63624], [15, 240, 4369, 8751, 20292, 26214, 63624], [15, 240, 4369, 8946, 17652, 36744, 63624], [15, 240, 8738, 20292, 34959, 52428, 61713], [15, 3840, 4369, 8946, 13299, 17652, 63624], [15, 3840, 4369, 8946, 17476, 63624]], [[1, 15, 3840, 4369, 8946, 17476, 63624], [6, 15, 240, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 17476, 25122, 63624], [15, 240, 3840, 8738, 12561, 25668, 63624], [15, 240, 3840, 8738, 17476, 20753, 63624], [15, 240, 4383, 8738, 20292, 26214, 63624], [15, 240, 8738, 10786, 20292, 34952, 61713], [15, 240, 8738, 20292, 34952, 62259, 65365], [15, 271, 3840, 8738, 17652, 34952, 61713]], [[4, 3840, 4369, 8959, 26358, 34952, 61440], [12, 3840, 8946, 17476, 34952, 52428, 61713], [15, 20, 3840, 4383, 8738, 17652, 63624], [15, 240, 4369, 8751, 20292, 61986, 63624]], [[1, 15, 240, 8738, 20292, 61713, 63624], [1, 240, 4383, 8738, 20292, 36744, 61440], [3, 15, 3840, 4369, 8946, 17476, 63624], [4, 15, 240, 8738, 20292, 34952, 61717], [4, 15, 240, 8738, 20292, 34956, 61713], [4, 15, 240, 8742, 20292, 34952, 61713], [4, 15, 244, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 8946, 17484, 63624], [15, 240, 3840, 4369, 8954, 17476, 63624], [15, 240, 3840, 4377, 8946, 17476, 63624], [15, 240, 3848, 4369, 8946, 17476, 63624], [15, 240, 3968, 8738, 17476, 52428, 61713], [15, 240, 4383, 8738, 20292, 61986, 63624], [15, 240, 8738, 8751, 20292, 36744, 61713], [15, 240, 8738, 20292, 34952, 61721], [15, 240, 8738, 20292, 34952, 62259, 63897], [15, 240, 8746, 20292, 34952, 61713], [15, 244, 3840, 4369, 8950, 17476, 63624], [15, 248, 3840, 4369, 8946, 17476, 63624], [15, 248, 8738, 20292, 34952, 61713]], [[4, 8, 3840, 8946, 17476, 34952, 61713], [4, 15, 3840, 4369, 8946, 17476, 63624], [12, 3840, 8946, 17476, 34952, 61713], [15, 240, 8738, 16179, 20292, 34952, 61713], [15, 3840, 4369, 8751, 17652, 17663, 63624], [15, 3840, 4369, 8946, 17476, 63628]], [[4, 240, 4369, 8751, 20292, 36744, 61440], [5, 15, 3840, 4369, 8946, 17476, 63624], [15, 240, 255, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 17476, 25126, 63624], [15, 240, 3840, 8738, 17476, 20757, 63624], [15, 240, 8738, 20292, 36744, 61713, 65348], [15, 3840, 4369, 8335, 8946, 17476, 63624], [15, 4369, 8946, 17652, 36744, 63624]], [[1, 15, 4369, 8738, 17652, 20292, 63624], [4, 15, 240, 8738, 20292, 61713, 63624], [6, 15, 3840, 4369, 8946, 17476, 63624], [15, 31, 3840, 8738, 17652, 34952, 61713], [15, 240, 3840, 4369, 8712, 17476, 63624], [15, 240, 3840, 4369, 8946, 17476, 63880], [15, 240, 3840, 4369, 8946, 17732, 63624], [15, 240, 3840, 4369, 9202, 17476, 63624], [15, 240, 3840, 8738, 17484, 39321, 61713], [15, 240, 3844, 8946, 17476, 34952, 61713], [15, 240, 3848, 8738, 17476, 39321, 61713], [15, 240, 8738, 20292, 35208, 61713], [15, 240, 8994, 20292, 34952, 61713], [15, 496, 8738, 20292, 34952, 61713]]], [[[12, 15, 240, 8738, 20292, 34952, 61713], [15, 240, 3855, 8738, 20292, 36744, 61713], [15, 240, 4369, 8738, 20292, 50244, 63624], [15, 240, 8751, 20292, 26214, 34952, 61713]], [[1, 15, 3840, 8946, 17476, 34952, 61713], [4, 15, 3840, 4369, 8946, 17476, 63628], [4, 15, 3840, 4369, 8950, 17476, 63624], [4, 15, 3840, 4373, 8946, 17476, 63624], [15, 240, 3840, 4369, 8959, 17476, 63624], [15, 240, 3840, 8738, 25668, 43144, 61713], [15, 3840, 4369, 8946, 17476, 63631, 65416], [15, 3840, 4369, 8946, 17484, 63624]], [[4, 15, 4369, 8738, 17652, 20292, 63624], [15, 240, 287, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 17476, 25130, 63624], [15, 240, 3840, 4383, 8946, 17476, 63624], [15, 240, 3840, 8738, 17476, 20761, 63624], [15, 240, 4369, 8751, 20292, 26223, 63624], [15, 240, 8751, 20292, 34952, 61713, 61986], [15, 3840, 4369, 8946, 17487, 52428, 63624]], [[3, 15, 3840, 8946, 17476, 34952, 61713], [15, 240, 260, 8738, 20292, 34952, 61713], [15, 240, 3848, 8946, 17476, 34952, 61713], [15, 240, 4593, 8738, 20292, 36744, 61713], [15, 255, 3840, 4369, 8946, 17476, 63624], [15, 3840, 4369, 8751, 17652, 35064, 63624]], [[4, 15, 3840, 8946, 17476, 34952, 61713], [12, 3840, 4369, 8738, 17652, 52476, 63624], [15, 240, 3840, 4369, 8946, 17476, 63640], [15, 240, 3840, 4369, 8946, 17492, 63624], [15, 240, 3856, 4369, 8946, 17476, 63624], [15, 240, 4369, 8738, 17663, 20292, 63624], [15, 248, 3840, 4369, 8954, 17476, 63624], [15, 3840, 4369, 8946, 17476, 63880], [15, 3840, 4369, 8946, 17652, 43690, 63624], [15, 3840, 4369, 8946, 17732, 63624]], [[5, 15, 3840, 8946, 17476, 34952, 61713], [12, 15, 3840, 4369, 8946, 17476, 63624], [15, 240, 8738, 17732, 34952, 61713, 65297]], [[1, 15, 8738, 17652, 20292, 34952, 61713], [6, 15, 3840, 8946, 17476, 34952, 61713], [15, 240, 3840, 4369, 8719, 17476, 63624], [15, 240, 3976, 8738, 17476, 61713], [15, 240, 4369, 8751, 17652, 20292, 63624], [15, 240, 8738, 20292, 34952, 61713, 65433]], [[15, 240, 3840, 4369, 17476, 25135, 63624], [15, 240, 4369, 8751, 17476, 20224, 63624], [15, 240, 4383, 8738, 17652, 20292, 63624], [15, 240, 8738, 20292, 21845, 34952, 63897], [15, 240, 8738, 20292, 36744, 40857, 61713]], [[1, 15, 3840, 8946, 17476, 61713, 63624], [4, 15, 3840, 4369, 8946, 17487, 63624], [4, 15, 3840, 8946, 17476, 34952, 61717], [4, 15, 3840, 8946, 17476, 34956, 61713], [4, 15, 3840, 8950, 17476, 34952, 61713], [4, 15, 3844, 8946, 17476, 34952, 61713], [15, 47, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4383, 17476, 25122, 63624], [15, 240, 3840, 8738, 17476, 20767, 63624], [15, 240, 4369, 8751, 20292, 61999, 63624], [15, 240, 8751, 20292, 61713, 63624], [15, 240, 12066, 13107, 20292, 34952, 61713], [15, 3840, 4369, 8946, 17652, 63624, 64764]], [[4, 15, 8738, 17652, 20292, 34952, 61713], [15, 240, 8738, 20292, 61727, 63624], [15, 3840, 4369, 8946, 17476, 63640], [15, 3840, 4369, 8946, 17492, 63624]], [[4, 15, 4369, 8946, 26214, 36744, 61440], [15, 36, 3840, 4369, 8751, 17652, 63624], [15, 240, 3840, 4369, 8946, 17476, 64136], [15, 240, 3840, 4369, 8946, 17988, 63624], [15, 240, 3840, 4881, 8946, 17476, 63624], [15, 240, 8738, 20292, 34952, 62225], [15, 240, 8738, 20292, 35464, 61713], [15, 752, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8751, 17652, 63624, 63736], [15, 3840, 4369, 8751, 17652, 63624, 64716]], [[4, 15, 3840, 8946, 17476, 61713, 63624], [15, 18, 3840, 4369, 8946, 17476, 63624], [15, 240, 3856, 8946, 17476, 34952, 61713], [15, 240, 4433, 8738, 20292, 34952, 61713], [15, 4369, 8751, 17652, 20292, 63624]], [[4, 15, 240, 4369, 25122, 36744, 61440], [4, 15, 4369, 8738, 16624, 36744, 61440], [12, 15, 3840, 8946, 17476, 34952, 61713], [15, 240, 8738, 12274, 20292, 34952, 61713], [15, 3840, 4369, 8946, 20292, 26358, 63624]], [], [[15, 240, 271, 8738, 20292, 34952, 61713], [15, 240, 8738, 20292, 21845, 63624, 63897], [15, 3840, 4369, 8751, 17652, 21845, 63624]], [[15, 47, 3840, 8738, 17652, 34952, 61713], [15, 240, 3840, 4369, 8738, 25796, 63624], [15, 240, 3840, 4383, 8959, 17476, 63624], [15, 240, 3840, 8738, 12689, 17476, 63624], [15, 240, 3840, 8738, 20292, 43144, 61713], [15, 240, 8738, 12032, 20292, 34952, 61713], [15, 240, 8738, 20292, 36744, 61713, 65365], [15, 255, 8738, 17652, 20292, 34952, 61713], [15, 3840, 4369, 8946, 17988, 63624]]], [[[12, 240, 8738, 20292, 34952, 53196, 61713], [15, 240, 255, 3976, 8738, 17476, 61713], [15, 3840, 4369, 8946, 17476, 17663, 63624], [15, 3840, 4369, 8946, 17487, 17652, 63624]], [[15, 240, 8738, 20292, 36744, 61713, 63897], [15, 255, 3840, 8946, 17476, 61713, 63624], [15, 3840, 4369, 8946, 12274, 17476, 63624]], [[15, 18, 3840, 8946, 17476, 34952, 61713]], [[15, 31, 240, 8738, 20292, 34952, 61713], [15, 240, 8738, 20292, 34952, 53196, 61713], [15, 271, 3840, 4369, 8946, 17476, 63624]], [[15, 240, 3840, 4369, 8802, 17652, 63624], [15, 240, 3840, 4369, 8946, 17508, 63624], [15, 240, 3840, 4593, 8738, 17476, 63640], [15, 240, 3856, 4593, 8738, 17476, 63624], [15, 240, 3904, 4369, 8738, 17652, 63624], [15, 3840, 4369, 8751, 17652, 52476, 63624]], [[15, 640, 4369, 8946, 17476, 36744, 61713], [15, 3840, 4369, 17652, 26358, 43690, 63624]], [[12, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 8738, 13107, 18244, 34952, 61713], [15, 240, 8738, 20292, 34952, 53199, 61713], [15, 3840, 4369, 8946, 17476, 35064, 63624], [15, 3840, 4369, 8946, 17476, 63897, 65416], [15, 3840, 4369, 17652, 26214, 63624, 64170]], [[4, 15, 4369, 8946, 17652, 36744, 61440], [13, 240, 3840, 4369, 8738, 17476, 63624]], [[15, 31, 3840, 4369, 8946, 17476, 63624], [15, 240, 8738, 20292, 34952, 35071, 61713], [15, 240, 8738, 20292, 34959, 35064, 61713]], [[4, 240, 3840, 4369, 8738, 17487, 63624], [15, 240, 527, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17652, 59528], [15, 3840, 4369, 8946, 17508, 63624], [15, 7953, 8946, 17476, 36744, 61713]], [[3, 240, 3840, 4369, 8751, 17476, 63624], [12, 240, 3840, 4369, 8738, 17476, 63628], [12, 3840, 4369, 8946, 17476, 63624, 64716], [15, 240, 3840, 4369, 8739, 17476, 63624], [15, 240, 8738, 20292, 34959, 53196, 61713]], [[15, 240, 3840, 4371, 8738, 17476, 63624], [15, 240, 3904, 8738, 17652, 34952, 61713], [15, 240, 3968, 8738, 17476, 35064, 61713], [15, 240, 8738, 20292, 34952, 48059, 61713], [15, 240, 8738, 20292, 39321, 43690, 61713], [15, 240, 13107, 20292, 34952, 43690, 61713], [15, 1039, 3840, 8738, 17652, 34952, 61713]], [[5, 240, 3840, 4369, 8751, 17476, 63624], [15, 240, 8738, 20292, 21845, 34952, 61713]], [[4, 240, 3840, 4369, 8738, 17487, 63628], [4, 240, 3840, 4369, 8742, 17487, 63624], [4, 240, 3840, 4373, 8738, 17487, 63624], [4, 240, 3840, 8738, 17484, 34952, 61713], [6, 240, 3840, 4369, 8751, 17476, 63624], [12, 240, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 63628], [15, 240, 3840, 4369, 8742, 17476, 63624], [15, 240, 3840, 4373, 8738, 17476, 63624], [15, 240, 3840, 8738, 17732, 63624, 63897], [15, 3840, 4369, 8946, 17476, 35071, 63624]], [[12, 240, 3840, 4369, 8738, 17484, 63624], [13, 240, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8743, 17476, 63624], [15, 240, 4369, 8738, 17652, 36744, 63624], [15, 3840, 4369, 8946, 12287, 17476, 63624]], [[15, 31, 3840, 8946, 17476, 34952, 61713], [15, 240, 3840, 4375, 8738, 17476, 63624], [15, 240, 4369, 8738, 17604, 36744, 61713], [15, 240, 4369, 8738, 20292, 21855, 63624], [15, 3840, 4369, 8751, 17652, 62532, 63624]]], [[[4, 3840, 4369, 8751, 26358, 34952, 61440], [15, 240, 7953, 8738, 20468, 34952, 61713], [15, 240, 8738, 20292, 35976, 61713], [15, 255, 8738, 20292, 34952, 35064, 61713], [15, 1264, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8946, 17476, 48059, 63624]], [[12, 240, 3840, 4369, 8738, 17487, 63624], [12, 240, 3840, 8738, 17476, 34956, 61713], [15, 240, 3840, 4369, 8738, 17484, 63624], [15, 240, 3840, 4369, 8742, 17476, 63628], [15, 240, 3840, 4369, 8746, 17476, 63624], [15, 240, 3840, 4373, 8738, 17476, 63628], [15, 240, 3840, 4373, 8742, 17476, 63624], [15, 240, 3840, 4377, 8738, 17476, 63624], [15, 240, 3844, 4369, 8742, 17476, 63624], [15, 240, 3844, 4373, 8738, 17476, 63624], [15, 240, 8738, 20292, 20303, 36744, 61713], [15, 244, 3840, 4369, 8742, 17476, 63624], [15, 8946, 20292, 36744, 61713]], [[12, 240, 3840, 4369, 8750, 17476, 63624], [12, 240, 3840, 4381, 8738, 17476, 63624], [12, 240, 3852, 4369, 8738, 17476, 63624], [12, 252, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8747, 17476, 63624], [15, 240, 4369, 8751, 20292, 21845, 63624], [15, 240, 8738, 20292, 32631, 34952, 61713]], [[12, 240, 3840, 4369, 8751, 17476, 63624], [15, 47, 240, 8738, 20292, 34952, 61713], [15, 240, 3840, 4379, 8738, 17476, 63624], [15, 240, 4080, 8738, 17652, 36744, 61713], [15, 240, 4383, 8738, 20292, 21845, 63624], [15, 240, 6417, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8751, 12066, 17652, 63624]], [[1, 15, 4369, 8738, 17652, 36744, 63624], [12, 240, 3840, 4383, 8738, 17476, 63624], [12, 240, 3840, 8738, 17476, 34959, 61713], [12, 240, 3840, 8738, 17476, 61713, 63624], [15, 240, 3840, 4369, 8738, 17476, 63880], [15, 240, 3840, 4369, 8738, 17732, 63624], [15, 240, 3840, 4369, 8866, 17604, 63624], [15, 240, 3840, 4369, 8994, 17476, 63624], [15, 240, 3840, 4497, 8738, 17604, 63624], [15, 240, 3840, 4497, 8866, 17476, 63624], [15, 240, 3968, 4369, 8738, 17604, 63624], [15, 240, 3968, 4369, 8866, 17476, 63624], [15, 240, 3968, 4497, 8738, 17476, 63624], [15, 240, 3968, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8946, 17476, 63631, 63736], [15, 3840, 4369, 8946, 17476, 63631, 64716]], [[12, 240, 3840, 8738, 17484, 34952, 61713], [15, 240, 3840, 4369, 8750, 17476, 63624], [15, 240, 3840, 4369, 8995, 17476, 63624], [15, 240, 3840, 4381, 8738, 17476, 63624], [15, 3840, 4369, 7953, 8946, 17652, 63624]], [[1, 240, 3840, 4383, 8751, 17476, 63624], [1, 240, 3840, 8751, 17476, 61713, 63624], [4, 240, 3840, 4369, 8751, 17487, 63624], [15, 240, 3840, 4369, 8751, 17476, 63624], [15, 240, 4369, 8738, 20292, 62532, 63624], [15, 240, 4383, 8738, 20292, 36744, 61713], [15, 240, 8738, 20292, 21855, 34952, 61713]], [[4, 15, 4369, 8738, 17652, 36744, 63624], [4, 240, 3840, 4383, 8738, 17487, 63624], [4, 240, 3840, 8738, 17487, 61713, 63624], [12, 3840, 4369, 8738, 17476, 17652, 63624], [15, 240, 3840, 4383, 8738, 17476, 63624], [15, 240, 3840, 8738, 17476, 61713, 63624]], [[4, 240, 4369, 8751, 26214, 36744, 61440], [15, 47, 3840, 4369, 8946, 17476, 63624], [15, 79, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4369, 8738, 17487, 63628], [15, 240, 3840, 4369, 25122, 36744, 62532], [15, 240, 3840, 4369, 25668, 36744, 61986], [15, 240, 3840, 4371, 8751, 17476, 63624], [15, 240, 3840, 4383, 8739, 17476, 63624], [15, 240, 3844, 4369, 8738, 17487, 63624], [15, 240, 3844, 8738, 17476, 34956, 61713], [15, 240, 3844, 8742, 17476, 34952, 61713], [15, 240, 4369, 12032, 17476, 36744, 61986], [15, 242, 3840, 4369, 8751, 17476, 63624], [15, 3840, 4369, 8946, 17487, 63624, 64716]], [[12, 240, 3840, 8738, 17476, 34952, 61725], [12, 240, 3840, 8750, 17476, 34952, 61713], [12, 240, 3852, 8738, 17476, 34952, 61713], [12, 252, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 63640], [15, 240, 3840, 4369, 8738, 17492, 63624], [15, 240, 3840, 4369, 8746, 17484, 63624], [15, 240, 3840, 4369, 8754, 17476, 63624], [15, 240, 3840, 4377, 8738, 17484, 63624], [15, 240, 3840, 4377, 8746, 17476, 63624], [15, 240, 3848, 4369, 8738, 17484, 63624], [15, 240, 3848, 4369, 8746, 17476, 63624], [15, 240, 3848, 4377, 8738, 17476, 63624], [15, 248, 3840, 4369, 8746, 17476, 63624]], [[12, 3840, 4369, 8738, 17652, 63624, 64764], [15, 240, 3840, 4369, 8751, 17476, 63628], [15, 240, 3840, 4369, 8755, 17476, 63624], [15, 240, 3840, 4373, 8751, 17476, 63624], [15, 240, 3844, 4369, 8751, 17476, 63624], [15, 240, 4369, 8946, 17652, 36744, 61713], [15, 240, 4369, 20292, 26214, 63624, 64170], [15, 244, 3840, 4369, 8751, 17476, 63624]], [[15, 240, 3840, 4383, 8738, 17476, 63628], [15, 240, 3840, 4383, 8742, 17476, 63624], [15, 240, 3840, 8738, 17476, 61713, 63628], [15, 240, 3844, 4383, 8738, 17476, 63624], [15, 240, 3844, 8738, 17476, 61713, 63624], [15, 240, 3968, 8738, 17604, 34952, 61713], [15, 240, 4369, 8751, 17652, 36744, 63624], [15, 3840, 4369, 17652, 26214, 61986, 63624]], [[15, 240, 4383, 8738, 17652, 36744, 63624]], [[15, 240, 4383, 8738, 20292, 21855, 63624], [15, 240, 8738, 16640, 20292, 36744, 61713], [15, 240, 13107, 20292, 28518, 34952, 61713]], [[15, 240, 3840, 4369, 8751, 17484, 63624], [15, 240, 3840, 4377, 8751, 17476, 63624], [15, 240, 3848, 4369, 8751, 17476, 63624], [15, 248, 3840, 4369, 8751, 17476, 63624]], [[15, 47, 3840, 8946, 17476, 34952, 61713], [15, 79, 3840, 8738, 17652, 34952, 61713], [15, 240, 1039, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 8738, 17732, 63880], [15, 240, 3840, 4369, 8738, 17988, 63624], [15, 240, 3840, 4369, 8994, 17476, 63880], [15, 240, 3840, 4369, 8994, 17732, 63624], [15, 240, 3840, 4383, 8738, 17484, 63624], [15, 240, 3840, 4383, 8746, 17476, 63624], [15, 240, 3840, 4881, 8738, 17476, 63624], [15, 240, 3840, 8738, 17476, 61717, 63628], [15, 240, 3840, 8738, 17484, 61713, 63624], [15, 240, 3840, 8738, 17652, 61713, 65416], [15, 240, 3848, 4383, 8738, 17476, 63624], [15, 240, 3848, 8738, 17476, 34959, 61713], [15, 240, 3848, 8738, 17476, 61713, 63624]]], [[[12, 240, 4369, 8738, 17652, 36744, 61440], [15, 240, 3848, 8738, 17484, 34952, 61713], [15, 240, 3848, 8746, 17476, 34952, 61713], [15, 248, 3840, 8738, 17484, 34952, 61713], [15, 3840, 4369, 8751, 12079, 17652, 63624], [15, 4369, 8751, 17652, 36744, 63624]], [[4, 240, 4369, 8751, 26223, 36744, 61440], [15, 240, 3840, 4369, 8751, 17476, 63880], [15, 240, 3840, 4369, 8751, 17732, 63624], [15, 240, 3840, 4369, 9007, 17476, 63624], [15, 240, 3840, 4883, 8738, 17476, 63624], [15, 240, 4080, 8738, 17988, 34952, 61713], [15, 240, 4369, 8738, 20292, 62543, 63624], [15, 240, 8738, 12066, 20292, 34952, 61713]], [[12, 240, 3840, 4369, 8738, 17476, 63897], [15, 240, 3840, 4383, 8738, 17476, 63880], [15, 240, 3840, 4383, 8738, 17732, 63624], [15, 240, 3840, 4383, 8994, 17476, 63624], [15, 240, 3840, 8738, 17476, 61713, 63880], [15, 240, 3840, 8738, 17732, 61713, 63624], [15, 3840, 4369, 8746, 17476, 17652, 63624], [15, 3840, 4369, 8946, 17476, 35064, 63897]], [[1, 240, 4383, 8738, 17652, 36744, 61440], [15, 240, 3840, 8738, 21845, 52428, 63897], [15, 240, 4369, 8751, 20292, 62532, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 63896], [15, 240, 3840, 4369, 8738, 17748, 63624], [15, 240, 3840, 4369, 9010, 17476, 63624], [15, 240, 3840, 4383, 8751, 17476, 63624], [15, 240, 4383, 8738, 20292, 62532, 63624], [15, 240, 8738, 18432, 20292, 61713, 63624], [15, 240, 8738, 20292, 28484, 34952, 61713], [15, 240, 8738, 20292, 34952, 62805, 63897], [15, 1039, 3840, 4369, 8946, 17476, 63624]], [[4, 240, 4369, 8751, 17652, 36744, 61440], [15, 240, 3840, 4369, 13107, 17476, 59528], [15, 240, 3840, 4369, 17652, 25250, 63624], [15, 240, 3840, 8738, 17652, 20881, 63624], [15, 240, 4369, 8738, 17652, 20352, 63624], [15, 240, 4369, 20292, 25122, 34952, 65280], [15, 240, 8738, 20292, 24565, 34952, 61713], [15, 3840, 4369, 8946, 17476, 63624, 64250], [15, 3840, 4369, 8946, 26358, 52428, 63624]], [[4, 240, 4383, 8738, 17652, 36744, 61440], [15, 240, 3840, 4369, 8751, 17476, 63640], [15, 240, 3840, 4369, 8751, 17492, 63624], [15, 240, 3840, 4369, 8767, 17476, 63624], [15, 240, 3856, 4369, 8751, 17476, 63624], [15, 240, 8738, 12561, 20292, 34952, 61713], [15, 240, 8738, 20292, 53196, 61713, 63897], [15, 3840, 4369, 8751, 17652, 43690, 63624], [15, 3840, 4369, 8946, 20292, 61680, 63624]], [[15, 240, 3840, 4383, 8738, 17476, 63640], [15, 240, 3840, 4383, 8738, 17492, 63624], [15, 240, 3840, 4383, 8754, 17476, 63624], [15, 240, 3840, 8738, 17476, 61713, 63640], [15, 240, 3840, 8738, 17492, 61713, 63624], [15, 240, 3855, 8738, 17652, 36744, 61713], [15, 240, 3856, 4383, 8738, 17476, 63624], [15, 240, 3856, 8738, 17476, 61713, 63624], [15, 255, 3840, 8738, 17652, 36744, 61713], [15, 3840, 4369, 8751, 17476, 17652, 63624]], [[15, 240, 8738, 12066, 20292, 61713, 63624], [15, 240, 8738, 18688, 20292, 34952, 61713]], [[15, 240, 3840, 4369, 8738, 17492, 63640], [15, 240, 3840, 4369, 8738, 17508, 63624], [15, 240, 3840, 4369, 8754, 17476, 63640], [15, 240, 3840, 4369, 8754, 17492, 63624], [15, 240, 3840, 4369, 8946, 17476, 59528], [15, 240, 3856, 4369, 8754, 17476, 63624], [15, 240, 8738, 13299, 20292, 34952, 61713], [15, 3840, 4369, 8946, 17476, 41714, 63624], [15, 3840, 4369, 8946, 17476, 63736, 63897], [15, 3840, 4369, 8946, 17652, 20468, 63624]], [[15, 240, 3840, 4369, 8738, 18244, 63624], [15, 240, 3840, 4369, 8738, 20292, 61576], [15, 240, 3840, 4369, 17476, 25186, 63624], [15, 240, 4369, 8738, 17652, 36744, 63897], [15, 3840, 4369, 8751, 17652, 63624, 64764], [15, 3840, 4369, 8946, 17476, 63624, 64255], [15, 3840, 4369, 17652, 25250, 63624]], [[4, 15, 3840, 4369, 8946, 26358, 63624], [12, 240, 4369, 8738, 17476, 20292, 63624], [15, 66, 3840, 4369, 8946, 17476, 63624], [15, 3840, 4369, 8751, 17652, 43695, 63624]], [[15, 240, 3840, 4369, 8751, 17476, 64136], [15, 240, 3840, 4369, 8751, 17988, 63624], [15, 240, 3840, 4881, 8751, 17476, 63624]], [[15, 240, 3840, 4369, 8738, 17484, 63897], [15, 240, 3840, 4369, 8746, 17476, 63897], [15, 240, 3840, 4383, 8738, 17476, 64136], [15, 240, 3840, 4383, 8738, 17988, 63624], [15, 240, 3840, 4895, 8738, 17476, 63624], [15, 240, 3840, 8738, 17476, 61713, 64136], [15, 240, 3840, 8738, 17988, 61713, 63624], [15, 3840, 4369, 8946, 17487, 62532, 63624]], [[15, 240, 8738, 12079, 20292, 34952, 61713], [15, 240, 8751, 12066, 20292, 34952, 61713]], [[15, 240, 3840, 4369, 8738, 25844, 63624], [15, 240, 3840, 4369, 17476, 25122, 59528], [15, 240, 3840, 8738, 12561, 17652, 63624], [15, 240, 4369, 8738, 12032, 17652, 63624], [15, 240, 4369, 8739, 17476, 20292, 63624], [15, 240, 4369, 20292, 26214, 61986, 63624], [15, 240, 8738, 20292, 36744, 52428, 61713], [15, 255, 3840, 8738, 17492, 34952, 61713], [15, 3840, 4369, 8946, 8959, 17652, 63624]]], [[[12, 240, 3840, 8738, 17476, 61713, 63897], [15, 240, 3856, 8738, 17476, 34968, 61713], [15, 240, 3856, 8738, 17492, 34952, 61713], [15, 240, 3856, 8754, 17476, 34952, 61713], [15, 240, 7953, 8946, 20292, 34952, 61713]], [[15, 240, 8738, 20292, 36744, 61713]], [[1, 15, 240, 8738, 20292, 36744, 61713], [4, 15, 3840, 8946, 26358, 34952, 61713], [12, 240, 8738, 17476, 20292, 34952, 61713], [15, 66, 3840, 8946, 17476, 34952, 61713], [15, 240, 4369, 8742, 17476, 20292, 63624], [15, 240, 8738, 20292, 36744, 36751, 61713], [15, 240, 8738, 20292, 36744, 61713, 65416], [15, 3840, 4369, 8751, 17487, 17652, 63624]], [[15, 79, 240, 8738, 20292, 34952, 61713], [15, 240, 4080, 8946, 17476, 36744, 61713], [15, 240, 4369, 8738, 17652, 53196, 63624], [15, 240, 8738, 20292, 34952, 53244, 61713], [15, 3840, 4369, 8946, 12079, 17476, 63624], [15, 3840, 4369, 8946, 17652, 26358, 63624]], [[4, 15, 3840, 4369, 25330, 34952, 61440], [4, 15, 4369, 8946, 20224, 34952, 61440], [4, 3840, 4369, 8946, 16399, 34952, 61440], [15, 240, 8738, 20292, 34952, 43690, 61713]], [[4, 15, 240, 8738, 20292, 36744, 61713], [15, 240, 3840, 4369, 8738, 17988, 64136], [15, 240, 3840, 4881, 8738, 17476, 64136], [15, 240, 3840, 4881, 8738, 17988, 63624]], [[15, 240, 3840, 4369, 8751, 17508, 63624], [15, 240, 3840, 4369, 25668, 43144, 61986], [15, 240, 3840, 8738, 17476, 45329, 63624], [15, 240, 3840, 8738, 17476, 47240, 61713], [15, 240, 3840, 8738, 17652, 43144, 61713], [15, 240, 4369, 8738, 17484, 20292, 63624], [15, 240, 4369, 8746, 17476, 20292, 63624], [15, 240, 4369, 12032, 17476, 43144, 61986], [15, 240, 4369, 12032, 25668, 34952, 61986], [15, 3840, 4369, 8432, 17476, 43144, 61986]], [[15, 240, 3840, 4369, 17476, 25122, 65416], [15, 240, 3840, 4383, 8738, 17508, 63624], [15, 240, 3840, 8738, 17476, 20753, 65416], [15, 240, 3840, 8738, 17508, 61713, 63624]], [[15, 79, 3840, 4369, 8946, 17476, 63624], [15, 240, 8738, 20292, 61713, 65416], [15, 4080, 8946, 17476, 36744, 61713]], [[15, 240, 3840, 4369, 8738, 17524, 63624], [15, 240, 3840, 4369, 8738, 17612, 61576], [15, 240, 3840, 4369, 8874, 17476, 61576], [15, 240, 3840, 4369, 8874, 17612, 61440], [15, 240, 3840, 4369, 25126, 51340, 61440], [15, 240, 3840, 4505, 8738, 17476, 61576], [15, 240, 4369, 8738, 17487, 20292, 63624], [15, 240, 4369, 8738, 17604, 20420, 63624], [15, 240, 4369, 8994, 17476, 20292, 63624], [15, 240, 8738, 20292, 20420, 34952, 61713], [15, 240, 8738, 20292, 34952, 43695, 61713], [15, 3840, 4369, 8946, 17476, 43690, 63624]], [[15, 240, 8738, 20292, 34952, 61713, 65501], [15, 3840, 4369, 8946, 13311, 17476, 63624]], [[15, 240, 255, 8738, 20292, 36744, 61713], [15, 240, 3840, 8738, 17484, 61713, 63897], [15, 240, 3848, 8738, 17476, 61713, 63897], [15, 240, 4369, 8751, 17476, 20292, 63624], [15, 240, 4369, 8959, 17476, 36744, 63624], [15, 240, 4497, 8738, 20292, 34952, 61713]], [], [[15, 255, 4369, 8946, 17476, 36744, 63624]], [[1, 15, 3840, 8946, 17476, 36744, 61713], [15, 240, 4369, 8738, 17484, 20300, 63624], [15, 3840, 4369, 8946, 17476, 43695, 63624], [15, 3840, 4369, 8946, 20292, 62194, 63624]], [[15, 79, 3840, 8946, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 18020, 63624], [15, 240, 4369, 8738, 17652, 36744, 61713]]], [[[12, 240, 4369, 8946, 17476, 36744, 61440], [15, 240, 8177, 8738, 20292, 34952, 61713], [15, 240, 8738, 17732, 20292, 34952, 61713]], [[4, 15, 3840, 8946, 17476, 36744, 61713], [15, 240, 4369, 12066, 17476, 61986, 65416], [15, 240, 8751, 20292, 34952, 43690, 61713], [15, 3840, 4369, 8946, 17476, 63897, 64250]], [], [[1, 240, 4383, 8946, 17476, 36744, 61440], [15, 240, 3840, 8738, 17476, 61713, 64648], [15, 240, 8738, 20292, 36744, 61713, 65433]], [[15, 240, 3840, 4369, 8866, 17652, 63624], [15, 240, 3840, 4369, 25122, 34952, 65348], [15, 240, 3840, 4497, 8738, 17652, 63624], [15, 240, 3840, 8738, 20292, 39048, 61713], [15, 240, 3968, 4369, 8738, 17652, 63624], [15, 240, 4369, 12032, 20292, 34952, 61986], [15, 240, 4369, 12066, 20292, 34952, 61952], [15, 240, 7936, 8738, 20292, 34952, 61713], [15, 240, 7953, 8738, 20292, 34952, 61696], [15, 3840, 4369, 8946, 17652, 43770, 63624]], [[15, 3840, 4369, 8177, 8946, 17476, 63624]], [[15, 240, 4369, 8751, 17487, 20292, 63624], [15, 240, 8738, 20292, 28518, 34952, 61713]], [[15, 240, 3840, 8738, 17476, 61576, 61849], [15, 240, 3855, 8946, 17476, 36744, 61713], [15, 240, 4383, 8738, 17487, 20292, 63624], [15, 240, 8738, 20292, 34952, 61727, 62805], [15, 255, 3840, 8946, 17476, 36744, 61713], [15, 3840, 4369, 7953, 8751, 17652, 63624], [15, 3840, 4369, 8946, 20292, 61713, 63624]], [], [[15, 240, 3840, 4369, 8802, 17476, 63624], [15, 3840, 4369, 8866, 17652, 63624]], [], [[15, 240, 2063, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 13107, 25668, 63624], [15, 240, 3840, 8738, 17476, 37265, 63624], [15, 240, 3840, 8738, 20468, 61713, 63624], [15, 240, 3968, 8738, 17652, 34952, 61713], [15, 240, 4369, 12032, 13107, 17476, 63624], [15, 240, 8738, 20292, 34952, 36608, 61713], [15, 3840, 4369, 8946, 26358, 63624, 64716]], [[15, 3855, 8946, 17476, 36744, 61713]], [[5, 15, 4369, 8946, 17476, 36744, 61440], [12, 240, 3840, 4369, 25122, 34952, 61440], [15, 132, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4369, 8806, 17476, 63624], [15, 240, 8738, 20292, 28518, 61713, 63624], [15, 3840, 4369, 8946, 17652, 34959, 63624]], [[6, 15, 4369, 8946, 17476, 36744, 61440], [15, 240, 3840, 4369, 8738, 17476, 59528], [15, 240, 3840, 4369, 8738, 25668, 51336], [15, 240, 3840, 4369, 17476, 25122, 43144], [15, 240, 3840, 4369, 25122, 25668, 34952], [15, 240, 3840, 8738, 12561, 17476, 51336], [15, 240, 3840, 8738, 17476, 20753, 43144], [15, 240, 8738, 20292, 34952, 36856, 61713], [15, 240, 8738, 20292, 34952, 61937, 65297]], [[15, 240, 3840, 4369, 8946, 25668, 63624], [15, 240, 8738, 20292, 28527, 34952, 61713], [15, 3840, 4369, 8432, 8946, 17476, 63624], [15, 3840, 4369, 8946, 21845, 26358, 63624], [15, 4593, 8946, 17476, 36744, 61713]]], [[[4, 15, 3840, 4369, 8738, 26358, 63624], [12, 240, 4369, 8738, 17476, 36744, 63624], [15, 240, 8738, 20292, 36744, 53196, 61713], [15, 3840, 4369, 8946, 17476, 48123, 63624]], [], [[4, 240, 3840, 4369, 25135, 34952, 61440], [4, 240, 4369, 8751, 20224, 34952, 61440], [15, 240, 8738, 20292, 34952, 61713, 65280]], [[1, 240, 4383, 8738, 17476, 36744, 63624], [4, 240, 3840, 4383, 25122, 34952, 61440], [15, 240, 3855, 8738, 20468, 34952, 61713], [15, 240, 8751, 20292, 28518, 34952, 61713], [15, 255, 3840, 8738, 20468, 34952, 61713], [15, 3840, 4369, 8946, 17476, 36856, 63624]], [[15, 132, 3840, 8738, 17652, 34952, 61713], [15, 240, 3840, 4369, 25122, 34952, 61444], [15, 240, 3840, 4369, 25122, 34956, 61440], [15, 240, 4369, 8739, 17476, 36744, 63624], [15, 3840, 4369, 8751, 8946, 17652, 63624], [15, 3840, 4369, 8946, 17652, 63624, 63631], [15, 3840, 4369, 8946, 25668, 63624]], [[15, 240, 3840, 8738, 17476, 28945, 63624], [15, 240, 7953, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8946, 17476, 43690, 63897]], [[15, 240, 3840, 4369, 8815, 17476, 63624], [15, 240, 3904, 4369, 8751, 17476, 63624]], [[4, 15, 3840, 8738, 26358, 34952, 61713], [4, 15, 4369, 8946, 17487, 36744, 61440], [15, 240, 3840, 4383, 8802, 17476, 63624], [15, 240, 3904, 4383, 8738, 17476, 63624], [15, 240, 3904, 8738, 17476, 61713, 63624], [15, 240, 4080, 8738, 17476, 36744, 61712], [15, 240, 4369, 8742, 17476, 36744, 63624]], [[15, 143, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4369, 25126, 34952, 61444], [15, 240, 4080, 8738, 17476, 36744, 61713], [15, 3840, 3855, 4369, 8946, 17652, 63624]], [[15, 240, 3840, 4369, 8818, 17476, 63624], [15, 240, 8738, 20292, 21845, 36744, 61713], [15, 3840, 4369, 12066, 17652, 61986, 63624]], [[12, 240, 3840, 8738, 17476, 36744, 61713], [15, 18, 4369, 8946, 17476, 36744, 61440], [15, 3840, 4369, 7953, 8946, 17476, 63624], [15, 3840, 4369, 8946, 17476, 63736, 65416]], [[4, 136, 3840, 4369, 8738, 17652, 61440], [4, 3840, 4369, 8946, 17663, 34952, 61440], [15, 240, 3840, 4369, 8751, 17476, 59528], [15, 240, 4369, 8738, 17484, 36744, 63624], [15, 240, 4369, 8746, 17476, 36744, 63624], [15, 3840, 4369, 4593, 8946, 17652, 63624], [15, 3840, 4369, 8751, 17652, 20468, 63624]], [[15, 240, 287, 3840, 8738, 17476, 63624], [15, 240, 3840, 4383, 8738, 17476, 59528], [15, 240, 7953, 8738, 20292, 61713, 63624], [15, 3840, 4369, 8751, 13119, 17652, 63624]], [[15, 240, 8738, 20292, 34952, 39321, 61713], [15, 3840, 4369, 8946, 17652, 61680, 63624]], [[4, 3840, 4383, 8946, 17652, 34952, 61440], [15, 240, 3841, 8738, 17476, 36744, 61713], [15, 240, 4369, 8994, 17476, 36744, 63624], [15, 240, 8738, 13107, 20292, 34952, 61713]], [[15, 143, 3840, 8738, 17652, 34952, 61713], [15, 240, 3842, 8738, 17476, 36744, 61713], [15, 240, 4080, 8738, 17476, 61713, 65416], [15, 240, 8751, 20292, 34952, 61713, 65280]]], [[[15, 240, 4369, 8751, 17476, 36744, 63624], [15, 240, 8738, 20292, 34952, 61727, 65280], [15, 3840, 4369, 8946, 26358, 62532, 63624]], [[15, 240, 3840, 4369, 8738, 17652, 61576], [15, 240, 3844, 8738, 17476, 36744, 61713], [15, 240, 8738, 20292, 34952, 61713, 65295], [15, 3840, 4369, 8751, 8959, 17652, 63624], [15, 3840, 4369, 8946, 20292, 26214, 63624]], [], [[15, 240, 3840, 4369, 20292, 25122, 63624], [15, 240, 3840, 8738, 20292, 20753, 63624], [15, 240, 7967, 8738, 20292, 34952, 61713], [15, 240, 8738, 20292, 34952, 39327, 61713], [15, 240, 8738, 20292, 34952, 61713, 65297], [15, 3840, 4369, 8946, 20292, 61986, 63624]], [[15, 240, 3840, 4369, 8946, 17604, 63624], [15, 240, 3840, 4497, 8946, 17476, 63624], [15, 240, 3840, 8738, 17476, 61713, 65416], [15, 240, 3968, 4369, 8946, 17476, 63624], [15, 240, 8738, 20292, 34952, 61841]], [[12, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 26214, 64170, 64716], [15, 240, 3844, 8738, 17476, 36748, 61713], [15, 240, 3848, 8738, 17476, 36744, 61713], [15, 240, 4369, 8994, 17476, 63624, 65416], [15, 240, 8738, 13107, 20292, 61713, 63624], [15, 240, 8738, 17732, 34952, 36744, 61713], [15, 3840, 4369, 8751, 17652, 26358, 63624]], [[13, 240, 4369, 8738, 17476, 36744, 61440]], [[15, 31, 4369, 8946, 17476, 36744, 61440], [15, 240, 4095, 8738, 17476, 36744, 61713]], [[1, 15, 8738, 8946, 20292, 34952, 61713], [1, 240, 4383, 8738, 17476, 36744, 61440], [12, 240, 4369, 8738, 20292, 39321, 61440], [15, 240, 4369, 25122, 36744, 62532], [15, 3840, 4369, 7967, 8946, 17476, 63624], [15, 3840, 4369, 8946, 8947, 17476, 63624]], [[1, 240, 4383, 8738, 17476, 36744, 61441], [1, 240, 4383, 8739, 17476, 36744, 61440], [3, 240, 4369, 8751, 17476, 36744, 61440], [12, 240, 4369, 8738, 17476, 36748, 61440], [15, 240, 4369, 20292, 25122, 34952, 65348], [15, 240, 4369, 20292, 28484, 34952, 61986], [15, 240, 8738, 20292, 20468, 34952, 61713], [15, 240, 8738, 20292, 24388, 34952, 61713], [15, 3840, 4369, 8946, 17604, 63624], [15, 3840, 4369, 8946, 17652, 63624, 63897]], [[1, 15, 3840, 8946, 20292, 34952, 61713], [15, 240, 3840, 4369, 17476, 25250, 63624], [15, 240, 3840, 8738, 17476, 20881, 63624], [15, 240, 3840, 8738, 20292, 51336, 61713], [15, 240, 8738, 12032, 28484, 34952, 61713], [15, 240, 8738, 13119, 20292, 34952, 61713], [15, 240, 8738, 16640, 20292, 34952, 65297], [15, 240, 8738, 20224, 20292, 34952, 61713], [15, 3840, 4369, 17652, 26214, 43690, 63624]], [[4, 15, 8738, 8946, 20292, 34952, 61713], [5, 240, 4369, 8751, 17476, 36744, 61440], [15, 130, 3840, 4369, 8946, 17476, 63624], [15, 240, 3968, 8946, 17476, 34952, 61713], [15, 240, 8738, 20292, 34952, 44970, 61713], [15, 3840, 4369, 8946, 8950, 17476, 63624]], [[5, 240, 4383, 8738, 17476, 36744, 61440], [6, 240, 4369, 8751, 17476, 36744, 61440], [15, 240, 3855, 8738, 17476, 36744, 61713], [15, 240, 4369, 8738, 20292, 26358, 63624], [15, 3840, 4369, 8946, 17652, 22005, 63624]], [[4, 15, 3840, 8946, 20292, 34952, 61713], [4, 3840, 4369, 8751, 17652, 34952, 63624], [6, 240, 4383, 8738, 17476, 36744, 61440], [12, 240, 4369, 8738, 17484, 36744, 61440], [15, 240, 3856, 8738, 17476, 36744, 61713], [15, 240, 4369, 12066, 20292, 61986, 63624]], [[15, 240, 8738, 12066, 20292, 36744, 61713], [15, 255, 4369, 8946, 17476, 36744, 61713], [15, 3840, 4369, 8751, 17652, 26367, 63624], [15, 3840, 4369, 8882, 17476, 63624, 63897], [15, 3840, 4369, 8946, 17652, 20292, 63624]], [[4, 136, 240, 4369, 8738, 20292, 61440], [15, 240, 3840, 8738, 19524, 61713, 63624], [15, 240, 8738, 8959, 20292, 34952, 61713], [15, 240, 8751, 8946, 20292, 34952, 61713], [15, 3840, 4369, 8946, 8954, 17476, 63624], [15, 3840, 4369, 8946, 13119, 17476, 63624]]], [[[12, 240, 4369, 8738, 17487, 36744, 61440], [15, 240, 264, 8738, 17476, 40857, 61440], [15, 240, 3840, 4369, 17476, 26214, 64136], [15, 240, 3840, 4881, 17476, 26214, 63624], [15, 240, 8738, 20292, 20468, 61713, 63624], [15, 240, 8738, 20292, 34952, 53060, 61713]], [[12, 240, 4369, 8738, 17476, 36744, 61452], [12, 240, 4369, 8750, 17476, 36744, 61440], [15, 240, 8738, 20292, 34952, 61713, 65311], [15, 240, 8738, 20292, 34952, 61727, 65297], [15, 240, 8738, 20292, 34952, 62259, 62805], [15, 255, 8738, 8946, 20292, 34952, 61713]], [[12, 240, 4369, 8751, 17476, 36744, 61440], [15, 130, 3840, 8946, 17476, 34952, 61713], [15, 240, 3840, 8738, 17476, 61727, 65416], [15, 240, 8738, 20292, 34952, 51592, 61713], [15, 3840, 4369, 8946, 9202, 17476, 63624], [15, 4383, 8946, 17476, 36744, 61713]], [[15, 143, 240, 8738, 20292, 34952, 61713], [15, 240, 3855, 8738, 17476, 61713, 65416], [15, 240, 3855, 8946, 20292, 34952, 61713], [15, 240, 4369, 28518, 34952, 61986, 65348], [15, 240, 8738, 20292, 25378, 34952, 61713], [15, 255, 3840, 8946, 20292, 34952, 61713]], [[15, 240, 3840, 4369, 8738, 25668, 63624], [15, 240, 3840, 8738, 12561, 17476, 63624], [15, 240, 8738, 20292, 20479, 34952, 61713], [15, 240, 8738, 20292, 34952, 61713, 65314], [15, 240, 12066, 20292, 34952, 61713, 61986], [15, 3840, 4369, 8946, 8959, 17476, 63624]], [[1, 240, 4383, 8751, 17476, 36744, 61440], [4, 240, 4369, 8751, 17487, 36744, 61440], [12, 240, 4369, 8738, 17476, 53196, 63624], [15, 240, 3840, 8738, 20292, 51592, 61713], [15, 3840, 4369, 8946, 17652, 62194, 63624]], [[4, 240, 4383, 8738, 17487, 36744, 61440], [15, 240, 3840, 8738, 12563, 17476, 63624]], [[15, 47, 4369, 8946, 17476, 36744, 61440]], [[15, 143, 3840, 4369, 8946, 17476, 63624], [15, 255, 8738, 20292, 20468, 34952, 61713]], [], [[15, 240, 8738, 20292, 24405, 34952, 61713]], [[15, 240, 3840, 8738, 17652, 37137, 63624], [15, 240, 3840, 8738, 17652, 39048, 61713], [15, 240, 4369, 8738, 17652, 36608, 63624], [15, 240, 4369, 8738, 17652, 36744, 63488], [15, 240, 4369, 12066, 17652, 34952, 61952], [15, 3840, 4336, 8738, 17652, 34952, 61713]], [[15, 240, 3840, 4369, 8738, 25676, 63624], [15, 240, 3840, 8738, 12569, 17476, 63624]], [[4, 3840, 4369, 8746, 17652, 34952, 61440], [15, 240, 3856, 8738, 17476, 36760, 61713], [15, 240, 3872, 8738, 17476, 36744, 61713]], [[13, 3840, 4369, 8738, 17652, 34952, 61440], [15, 240, 4369, 8994, 17476, 36744, 61696], [15, 240, 4369, 20292, 26214, 43690, 63624], [15, 3840, 4369, 4383, 8946, 17652, 63624], [15, 3840, 4369, 8946, 17652, 61713, 63624]], [[15, 143, 3840, 8946, 17476, 34952, 61713], [15, 640, 4369, 8946, 17476, 36744, 62080], [15, 3840, 4369, 8751, 17652, 34959, 63624]]], [[[15, 240, 4369, 8751, 17476, 36744, 61696]], [[12, 240, 4369, 8738, 17476, 36744, 61713], [15, 240, 3840, 4369, 8751, 25668, 63624], [15, 240, 3840, 4369, 8946, 17476, 61576], [15, 240, 4369, 8751, 12032, 17476, 63624], [15, 240, 8738, 18244, 34952, 61713], [15, 240, 8738, 20292, 24405, 61713, 63624], [15, 240, 8738, 20292, 36744, 43690, 61713], [15, 3840, 4369, 8432, 8751, 17476, 63624], [15, 3840, 4369, 8946, 17476, 26367, 63624]], [[4, 3840, 4369, 8751, 17652, 34952, 61440], [15, 240, 3840, 4383, 8738, 25668, 63624], [15, 240, 3840, 8738, 12575, 17476, 63624], [15, 240, 3840, 8738, 25668, 61713, 63624]], [[5, 3840, 4369, 8751, 17652, 34952, 61440], [15, 240, 4080, 8738, 20292, 34952, 61712], [15, 240, 4369, 8738, 17487, 53196, 63624], [15, 240, 4369, 12032, 17476, 44936, 61986]], [[1, 240, 4383, 8738, 17476, 36744, 61713], [5, 3840, 4383, 8738, 17652, 34952, 61440], [6, 3840, 4369, 8751, 17652, 34952, 61440], [15, 240, 4080, 8738, 20292, 34952, 61713], [15, 240, 8738, 20292, 24415, 34952, 61713]], [[6, 3840, 4383, 8738, 17652, 34952, 61440], [15, 240, 4369, 8751, 17476, 53196, 63624], [15, 240, 4369, 8946, 20292, 34952, 61952], [15, 240, 8738, 20292, 34952, 61713, 65331], [15, 3840, 4369, 8946, 17652, 63624, 64170]], [[1, 240, 8738, 8751, 20292, 34952, 61713], [4, 3840, 4369, 8751, 17652, 34952, 61444], [4, 3840, 4373, 8751, 17652, 34952, 61440], [12, 240, 3840, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8751, 17652, 63624, 63631]], [], [[12, 3840, 4369, 8946, 17476, 34952, 63624], [15, 240, 4369, 8742, 17476, 36744, 61713], [15, 240, 8738, 20292, 34952, 34954, 61713]], [[12, 3840, 4369, 8738, 8946, 17476, 63624], [15, 240, 3840, 4369, 8738, 17604, 63624], [15, 240, 3840, 4369, 8751, 25676, 63624], [15, 240, 3840, 4369, 8866, 17476, 63624], [15, 240, 3840, 4497, 8738, 17476, 63624], [15, 240, 4369, 8751, 12040, 17476, 63624], [15, 3840, 4369, 8440, 8751, 17476, 63624], [15, 3840, 4369, 8946, 17476, 43770, 63624]], [[4, 15, 4369, 8946, 26358, 36744, 61440], [15, 240, 3840, 4369, 8738, 26180, 63624], [15, 240, 3840, 8738, 13073, 17476, 63624], [15, 240, 3841, 8738, 20292, 34952, 61713], [15, 3840, 3855, 4369, 8751, 17652, 63624], [15, 3840, 4369, 8946, 20292, 21845, 63624], [15, 3840, 4369, 8946, 26214, 52428, 63624]], [[4, 240, 3840, 4369, 8738, 16392, 63624], [4, 3840, 4369, 8946, 17487, 34952, 63624], [15, 240, 3842, 8738, 20292, 34952, 61713], [15, 240, 4080, 8738, 20292, 61713, 63624], [15, 240, 4369, 8751, 17476, 36744, 61952], [15, 242, 3840, 8738, 20292, 34952, 61713]], [[15, 240, 3840, 4369, 25122, 52428, 63624], [15, 240, 3840, 8738, 20753, 52428, 63624], [15, 240, 4080, 8738, 20468, 36744, 61713], [15, 240, 4369, 8738, 17484, 36744, 61713], [15, 240, 4369, 8746, 17476, 36744, 61713], [15, 240, 8738, 20228, 34952, 61713, 61727]], [[15, 240, 3844, 8738, 20292, 34952, 61713], [15, 240, 8738, 19524, 20292, 34952, 61713], [15, 240, 8738, 20292, 34952, 34959, 61713], [15, 244, 3840, 8738, 20292, 34952, 61713], [15, 3840, 4369, 4593, 8751, 17652, 63624], [15, 3840, 4369, 8946, 17652, 62708, 63624], [15, 3840, 4369, 8946, 20292, 36744, 61713]], [[15, 240, 3840, 4369, 8959, 17476, 61576], [15, 3840, 4369, 8946, 17476, 43775, 63624]], [[15, 240, 4369, 8994, 17476, 36744, 61713], [15, 240, 8738, 8746, 20292, 34952, 61713], [15, 3840, 4369, 8320, 8946, 17652, 63624], [15, 3840, 4369, 8751, 17652, 61680, 63624]]], [[[4, 15, 3840, 4369, 8946, 26214, 63624], [4, 3840, 4383, 8751, 17652, 34952, 61440], [4, 3840, 8751, 17652, 34952, 61440, 61713], [15, 240, 3840, 8738, 20292, 61713, 63624], [15, 240, 8738, 20292, 34952, 61422, 61713], [15, 240, 12066, 20292, 34952, 61713, 62259], [15, 255, 3840, 4369, 8946, 17476, 61576]], [[4, 240, 4369, 8746, 20292, 34952, 61440], [4, 240, 4377, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 8738, 17612, 63624], [15, 240, 3840, 4369, 8874, 17476, 63624], [15, 240, 3840, 4505, 8738, 17476, 63624], [15, 240, 3848, 8738, 20292, 34952, 61713], [15, 248, 3840, 8738, 20292, 34952, 61713]], [[4, 15, 240, 3840, 4369, 25122, 63624], [4, 15, 3840, 4369, 8738, 16624, 63624], [4, 240, 3840, 4369, 8738, 16399, 63624], [13, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 4369, 20292, 28518, 61986, 63624]], [[15, 240, 4095, 8738, 20292, 34952, 61713], [15, 240, 4369, 8751, 17476, 36744, 61960], [15, 240, 8738, 20224, 34952, 52428, 61713], [15, 240, 8738, 20292, 28518, 36744, 61713], [15, 255, 4080, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8946, 17652, 36744, 63624]], [[1, 240, 4383, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 8738, 25700, 63624], [15, 240, 3840, 4369, 8946, 17652, 63624], [15, 240, 3968, 8738, 20420, 34952, 61713], [15, 240, 4369, 28484, 34952, 61986], [15, 240, 8738, 8751, 20292, 34952, 61713], [15, 240, 8738, 20292, 34952, 61937, 63897], [15, 240, 8738, 20292, 34959, 61713, 63624], [15, 3840, 4336, 4369, 8946, 17476, 63624], [15, 3840, 4369, 8746, 8946, 17476, 63624]], [[1, 240, 4383, 8738, 20292, 34952, 61441], [3, 240, 4369, 8751, 20292, 34952, 61440]], [[4, 240, 4369, 8751, 20292, 34952, 61440], [15, 240, 3840, 4369, 8751, 17604, 63624], [15, 240, 3840, 4369, 8879, 17476, 63624], [15, 240, 3840, 4497, 8751, 17476, 63624], [15, 240, 3968, 4369, 8751, 17476, 63624], [15, 3840, 4369, 17652, 26358, 63624, 64170]], [[4, 15, 3840, 8946, 26214, 34952, 61713], [4, 240, 4383, 8738, 20292, 34952, 61440], [5, 240, 4369, 8751, 20292, 34952, 61440], [15, 79, 4369, 8946, 17476, 36744, 61440], [15, 240, 3840, 4383, 8738, 17604, 63624], [15, 240, 3840, 4383, 8866, 17476, 63624], [15, 240, 3840, 4511, 8738, 17476, 63624], [15, 240, 3840, 8738, 17604, 61713, 63624], [15, 240, 3968, 4383, 8738, 17476, 63624], [15, 240, 3968, 8738, 17476, 61713, 63624], [15, 3840, 4369, 8946, 17652, 52428, 63624]], [[5, 240, 4383, 8738, 20292, 34952, 61440], [6, 240, 4369, 8751, 20292, 34952, 61440], [15, 240, 3855, 8738, 20292, 34952, 61713], [15, 3840, 4095, 4369, 8946, 17476, 63624], [15, 3840, 4369, 8946, 17652, 26214, 63624]], [[4, 15, 240, 3840, 25122, 34952, 61713], [4, 15, 240, 8738, 20224, 34952, 61713], [4, 15, 3840, 8738, 16624, 34952, 61713], [6, 240, 4383, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 8738, 17620, 63624], [15, 240, 3840, 4369, 8882, 17476, 63624], [15, 240, 3848, 8738, 20300, 34952, 61713], [15, 240, 3856, 8738, 20292, 34952, 61713], [15, 240, 8738, 20228, 34952, 61713], [15, 3840, 4369, 8751, 8946, 17476, 63624], [15, 3840, 4369, 8946, 17652, 63624]], [[1, 15, 3840, 4369, 8946, 17652, 63624], [4, 240, 4369, 8751, 20292, 34952, 61444], [4, 240, 4369, 8751, 20292, 34956, 61440], [4, 240, 4373, 8751, 20292, 34952, 61440], [4, 244, 4369, 8751, 20292, 34952, 61440], [15, 240, 3840, 4369, 17652, 25122, 63624], [15, 240, 3840, 8738, 17476, 28945, 59528], [15, 240, 3840, 8738, 17652, 20753, 63624], [15, 240, 4369, 8738, 17652, 20224, 63624], [15, 240, 8751, 20292, 34952, 61713, 63624], [15, 3840, 4369, 8946, 17476, 61182, 63624], [15, 3840, 4369, 8946, 17652, 61986, 63624], [15, 3840, 4369, 8946, 17652, 63624, 65416]], [[4, 240, 4383, 8738, 20292, 34952, 61444], [4, 240, 4383, 8742, 20292, 34952, 61440], [12, 240, 3840, 4369, 8738, 17476, 61568], [12, 240, 3968, 4369, 8738, 17476, 61440], [15, 240, 4593, 8738, 20292, 34952, 61713], [15, 240, 8738, 8751, 20292, 61713, 63624], [15, 240, 8738, 20292, 34952, 61727, 63624], [15, 240, 8738, 20292, 34952, 62259, 65297], [15, 240, 8738, 20292, 36744, 36856, 61713], [15, 3840, 4369, 8751, 17652, 63624, 63897], [15, 3840, 4369, 8946, 20292, 62532, 63624]], [[15, 240, 8738, 20292, 34952, 35464, 61713], [15, 3840, 4369, 8746, 8954, 17476, 63624]], [[4, 15, 3840, 4369, 8946, 17652, 63624], [4, 240, 4369, 8751, 20292, 61440, 63624], [12, 240, 4369, 8738, 20292, 34952, 61452], [12, 240, 4369, 8750, 20292, 34952, 61440], [15, 240, 3840, 8751, 20292, 61713, 63624], [15, 240, 3904, 8738, 17476, 36744, 61713], [15, 3840, 3855, 4369, 8946, 17476, 63624]], [[4, 15, 240, 4369, 8738, 24576, 36744], [12, 240, 4369, 8751, 20292, 34952, 61440], [13, 3840, 4369, 8946, 17476, 34952, 61440], [15, 240, 3840, 8738, 20292, 61727, 63624], [15, 240, 8738, 18244, 34952, 61713, 62259], [15, 3840, 4369, 8751, 17652, 22005, 63624], [15, 3840, 4369, 8882, 17476, 63624]], [[15, 240, 3855, 8738, 20292, 61713, 63624], [15, 240, 8738, 20292, 34952, 40857, 61713], [15, 240, 8738, 20292, 36744, 61713, 65280]]], [[[4, 3840, 4369, 8946, 17487, 34952, 61440], [15, 3840, 4369, 4593, 8946, 17476, 63624], [15, 3840, 4369, 8751, 17652, 20292, 63624]], [[1, 15, 3840, 8946, 17652, 34952, 61713], [15, 240, 3840, 4369, 8959, 17652, 63624], [15, 240, 3840, 4369, 25122, 51336, 62532], [15, 240, 3840, 8738, 17652, 51336, 61713], [15, 240, 3840, 8738, 20753, 51336, 62532], [15, 240, 4369, 8738, 20224, 51336, 62532], [15, 240, 8738, 20292, 34952, 61713, 65359]], [[15, 240, 3840, 4383, 8946, 17652, 63624], [15, 240, 3840, 8946, 17652, 61713, 63624], [15, 240, 4593, 8738, 20292, 61713, 63624], [15, 240, 7953, 8738, 20292, 36744, 61713]], [[15, 143, 4369, 8738, 20292, 35064, 61440], [15, 240, 8751, 20292, 34952, 61713, 65348], [15, 255, 3840, 4369, 8946, 17652, 63624]], [[4, 15, 3840, 8946, 17652, 34952, 61713], [4, 240, 4383, 8751, 20292, 34952, 61440], [4, 240, 8751, 20292, 34952, 61440, 61713], [4, 3840, 4369, 8946, 17487, 34952, 61444], [4, 3840, 4369, 8950, 17487, 34952, 61440], [4, 3840, 4373, 8946, 17487, 34952, 61440], [15, 240, 8738, 20292, 34952, 61727, 65348]], [[15, 240, 4369, 8738, 20292, 22005, 63624], [15, 3840, 4369, 8946, 17476, 43770, 63897], [15, 8946, 12274, 17476, 36744, 61713]], [[15, 240, 3840, 4369, 8738, 17484, 61568], [15, 240, 3840, 4497, 8738, 17476, 61448], [15, 240, 8738, 20292, 43690, 53196, 61713], [15, 240, 8738, 20292, 61713, 65280, 65416], [15, 3840, 4369, 8959, 17652, 63624]], [[15, 240, 8738, 20292, 21845, 39321, 63624], [15, 240, 8738, 20292, 34952, 61713, 65365], [15, 3840, 4383, 8946, 17652, 63624], [15, 3840, 8946, 17652, 61713, 63624]], [[15, 240, 4369, 13107, 20292, 26214, 63624], [15, 240, 8738, 13107, 20292, 21845, 63624]], [[12, 240, 3840, 4369, 8738, 26214, 63624], [15, 240, 3840, 4369, 8738, 17636, 63624], [15, 240, 3856, 8738, 20308, 34952, 61713], [15, 240, 3872, 8738, 20292, 34952, 61713], [15, 240, 4607, 8738, 20292, 34952, 61713]], [[15, 240, 8738, 20292, 36744, 39321, 61713], [15, 255, 3840, 8946, 17652, 34952, 61713], [15, 3840, 4369, 8751, 17476, 26358, 63624]], [[15, 240, 3840, 4369, 25122, 34952, 64716], [15, 240, 8738, 13107, 20292, 36744, 61713], [15, 3840, 4369, 17652, 26358, 61986, 63624]], [[15, 132, 4369, 8738, 17652, 36744, 61440], [15, 255, 8738, 20292, 34952, 61680, 61713]], [[12, 240, 4369, 8738, 20292, 34952, 61713], [15, 240, 4383, 8738, 20292, 34952, 61696]], [[4, 240, 3840, 4369, 8751, 26214, 63624], [4, 3840, 8946, 17487, 34952, 61440, 61713], [15, 240, 3840, 7953, 8994, 17476, 63624], [15, 240, 4369, 8738, 17604, 20292, 63624], [15, 240, 4369, 8946, 20292, 61986, 63624], [15, 240, 8738, 20292, 34952, 56797, 61713], [15, 240, 8738, 20292, 39321, 52428, 61713], [15, 3840, 4369, 4607, 8946, 17476, 63624]], [[15, 240, 4369, 12032, 28484, 34952, 61986], [15, 240, 8738, 20292, 20293, 34952, 61713], [15, 240, 8738, 20292, 30583, 34952, 61713], [15, 240, 13107, 20292, 26214, 34952, 61713]]], [[[1, 240, 4383, 8738, 20292, 34952, 61713], [12, 144, 3840, 4369, 8738, 17476, 61440], [12, 240, 3840, 8738, 26214, 34952, 61713], [15, 240, 3840, 4369, 8738, 26214, 63628], [15, 240, 3840, 4373, 8738, 26214, 63624], [15, 240, 3844, 4369, 8738, 26214, 63624], [15, 240, 8738, 16640, 20292, 34952, 63897], [15, 240, 8738, 20292, 20294, 34952, 61713], [15, 240, 8738, 20292, 36744, 61713, 65297], [15, 255, 3840, 4369, 8959, 17652, 63624], [15, 3840, 4369, 4383, 8751, 17652, 63624], [15, 3840, 4369, 8751, 17652, 61713, 63624], [15, 3840, 4369, 8946, 17652, 17663, 63624], [15, 3840, 4369, 8946, 26214, 63624, 64716]], [[15, 240, 3840, 8738, 17652, 51352, 61713], [15, 240, 4383, 8738, 20292, 34952, 61700], [15, 240, 8738, 16640, 20292, 51592, 61713], [15, 240, 8738, 20292, 34952, 61713, 65375], [15, 240, 16640, 20292, 25378, 34952, 61713], [15, 3840, 4369, 8946, 12274, 17652, 63624]], [[15, 240, 3840, 4369, 25122, 63624, 64716], [15, 240, 4371, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8946, 16371, 17476, 63624]], [[4, 240, 4383, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 8751, 17476, 61576], [15, 240, 4369, 20292, 25122, 63624], [15, 240, 8738, 12066, 17988, 34952, 61713], [15, 3840, 4369, 8946, 21845, 52428, 63624], [15, 4369, 8946, 20292, 61986, 63624]], [[15, 240, 280, 8738, 17476, 36744, 61440], [15, 240, 3840, 4383, 8738, 17476, 61576], [15, 240, 3840, 8738, 17476, 61576, 61713], [15, 240, 4369, 8742, 20292, 34952, 61713], [15, 240, 4373, 8738, 20292, 34952, 61713], [15, 3840, 4369, 8946, 21845, 26214, 63624]], [[4, 240, 3840, 8751, 26214, 34952, 61713], [15, 240, 8738, 20292, 34952, 61727, 65365], [15, 240, 20292, 28518, 34952, 61713, 62259]], [[12, 240, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 8738, 17732, 39321, 63624], [15, 240, 8738, 20292, 20300, 34952, 61713], [15, 240, 8738, 20292, 20468, 36744, 61713], [15, 3840, 4369, 8946, 17652, 35064, 63624]], [[4, 240, 3840, 4369, 8751, 26223, 63624], [15, 143, 4369, 8738, 17652, 36744, 61440], [15, 240, 3844, 8738, 26214, 34952, 61713], [15, 240, 4369, 8751, 20292, 34952, 61952], [15, 240, 8738, 20292, 34952, 61727, 61937], [15, 240, 8738, 20292, 34952, 61727, 63897], [15, 244, 3840, 8738, 26214, 34952, 61713], [15, 3840, 4369, 8751, 17652, 63624, 64170]], [[15, 240, 4373, 8738, 20292, 34952, 61717], [15, 240, 4377, 8738, 20292, 34952, 61713], [15, 240, 4383, 8738, 20292, 34952, 61952], [15, 240, 8738, 17732, 36744, 61713], [15, 240, 8738, 20292, 36744, 44970, 61713]], [[4, 240, 3840, 4369, 8738, 17663, 63624], [12, 3840, 4369, 8738, 17652, 52428, 63624], [12, 3840, 4369, 8946, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4369, 8738, 25668, 59528], [15, 240, 8738, 20292, 20303, 34952, 61713]], [[15, 240, 3840, 4369, 8739, 17652, 63624], [15, 240, 3840, 4369, 17476, 25330, 63624]], [[4, 8, 3840, 4369, 8738, 17652, 63624], [4, 240, 3840, 4369, 8751, 17652, 63624], [12, 3840, 4369, 8738, 17652, 63624], [15, 152, 3840, 4369, 8738, 17476, 61440], [15, 240, 287, 8738, 17476, 36744, 61440], [15, 240, 3840, 4371, 8738, 17652, 63624], [15, 240, 4369, 8751, 20292, 34952, 61956], [15, 240, 4497, 8738, 20292, 34952, 61841]], [[15, 240, 3840, 8738, 13107, 17476, 63640], [15, 240, 3840, 8738, 13107, 17492, 63624], [15, 240, 3856, 8738, 13107, 17476, 63624], [15, 3840, 4369, 8751, 17652, 63624, 64175]], [[12, 240, 3840, 8738, 17652, 34952, 61713], [15, 240, 3840, 4369, 8738, 17652, 63628], [15, 240, 3840, 4369, 8742, 17652, 63624], [15, 240, 3840, 4373, 8738, 17652, 63624], [15, 240, 3844, 4369, 8738, 17652, 63624], [15, 240, 8738, 20292, 34952, 39417, 61713], [15, 3840, 4369, 8946, 17652, 63624, 63736], [15, 3840, 4369, 8946, 17652, 63624, 64716]], [[15, 240, 4383, 8738, 20292, 34952, 61713], [15, 240, 8738, 20292, 20308, 34952, 61713], [15, 3840, 4369, 8946, 17487, 20292, 63624]], [[1, 15, 3840, 4369, 8738, 17652, 63624], [15, 3840, 4369, 8751, 17652, 62708, 63624], [15, 3840, 4369, 8946, 10994, 17476, 63624]]], [[[1, 15, 3840, 4369, 8739, 17652, 63624], [4, 3840, 4369, 8751, 17652, 63624], [15, 240, 264, 8738, 17476, 36744, 61713], [15, 240, 3840, 4369, 25122, 34952, 62532], [15, 240, 3840, 8738, 17476, 37137, 63624], [15, 240, 4377, 8738, 20292, 34952, 61721], [15, 240, 4881, 8738, 20292, 34952, 61952], [15, 240, 8738, 20292, 20303, 61713, 63624], [15, 3840, 4369, 8946, 17476, 45050, 63624]], [[3, 15, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4369, 8738, 17660, 63624], [15, 240, 3840, 4369, 8746, 17652, 63624], [15, 240, 3840, 4377, 8738, 17652, 63624], [15, 240, 3848, 4369, 8738, 17652, 63624], [15, 241, 3840, 8738, 17652, 34952, 61713], [15, 3840, 4369, 8946, 17652, 21845, 63624]], [[4, 15, 3840, 4369, 8738, 17652, 63624], [15, 242, 3840, 8738, 17652, 34952, 61713]], [[5, 15, 3840, 4369, 8738, 17652, 63624], [15, 3840, 4369, 4383, 8946, 17476, 63624]], [[6, 15, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4369, 8738, 17652, 63880], [15, 240, 3840, 4369, 8738, 17908, 63624], [15, 240, 3840, 4369, 8994, 17652, 63624], [15, 240, 3840, 4369, 25126, 34952, 62532], [15, 240, 3844, 8738, 17652, 34952, 61713], [15, 240, 4369, 8751, 20292, 61713, 63624], [15, 240, 8738, 20292, 34952, 57309, 61713], [15, 244, 3840, 8738, 17652, 34952, 61713], [15, 3840, 4369, 8946, 17652, 36744, 61713]]]]
  | 7 => [[[[6, 240, 3840, 4383, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952, 61445], [15, 240, 3840, 4369, 8946, 17476, 63624, 64170], [15, 240, 8738, 16640, 20292, 34952, 61713]], [[1, 15, 3840, 8738, 17652, 34952, 61713], [15, 240, 3840, 4369, 8751, 17476, 63624, 63631], [15, 240, 3840, 4369, 8751, 17652, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 63897], [15, 240, 3840, 4383, 8738, 8751, 17476, 63624], [15, 240, 3840, 4383, 8738, 17476, 63624, 63631], [15, 240, 3840, 4383, 8738, 17652, 63624], [15, 240, 3840, 8738, 8751, 17476, 61713, 63624], [15, 240, 3840, 8738, 17476, 61713, 63624, 63631], [15, 240, 3840, 8738, 17652, 61713, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61448], [15, 240, 3840, 4369, 8738, 17476, 34956, 61444], [15, 240, 3840, 4369, 8738, 17652, 36744, 61440], [15, 240, 3840, 4369, 8739, 17476, 61440, 63624], [15, 240, 3840, 4369, 8742, 17476, 34956, 61440]], [[4, 15, 3840, 8738, 17652, 34952, 61713], [12, 240, 3840, 4369, 8738, 17476, 34952, 61452], [12, 240, 3840, 4369, 8750, 17476, 34952, 61440], [12, 240, 3852, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952, 61449]], [[12, 240, 3840, 4369, 8751, 17476, 34952, 61440], [15, 240, 255, 3840, 8738, 17652, 34952, 61713], [15, 240, 3840, 3855, 4369, 8751, 17476, 63624]], [[15, 240, 3840, 3855, 4383, 8738, 17476, 63624], [15, 240, 3840, 3855, 8738, 17476, 61713, 63624], [15, 240, 3840, 4369, 8738, 17476, 34968, 63640], [15, 240, 3840, 4369, 8738, 17476, 34984, 63624], [15, 240, 3840, 4369, 8738, 17508, 34952, 63624], [15, 240, 3840, 4369, 8738, 17604, 34952, 61568], [15, 240, 3840, 4369, 8742, 17476, 61440, 63624], [15, 3840, 4369, 8751, 17652, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61452], [15, 240, 3840, 4369, 8738, 17476, 34952, 61697]], [[4, 240, 3840, 4369, 8751, 17487, 34952, 61440], [15, 240, 3840, 4369, 4593, 8751, 17476, 63624]], [[4, 15, 4369, 8738, 17652, 34952, 36744, 61440], [4, 240, 3840, 4383, 8738, 17487, 34952, 61440], [4, 240, 3840, 8738, 17487, 34952, 61440, 61713], [15, 240, 3840, 4369, 4607, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624, 63897], [15, 240, 3840, 4383, 4593, 8738, 17476, 63624], [15, 240, 3840, 4593, 8738, 17476, 61713, 63624]], [[15, 47, 3840, 4369, 8946, 17476, 34952, 61440], [15, 79, 3840, 4369, 8738, 17652, 34952, 61440], [15, 143, 3840, 4369, 8738, 17476, 35064, 61440], [15, 240, 1039, 4369, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34959, 61448], [15, 240, 3840, 4369, 8738, 17484, 34959, 61440], [15, 240, 3840, 4369, 8738, 17484, 61440, 63624], [15, 240, 3840, 4369, 8738, 17487, 34952, 61444], [15, 240, 3840, 4369, 8738, 17652, 61440, 65416], [15, 240, 3840, 4369, 8746, 17476, 61440, 63624], [15, 240, 3840, 4369, 8751, 17476, 61680, 63624], [15, 255, 3840, 8738, 17652, 34952, 61713]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61456], [15, 240, 3840, 4369, 8738, 17484, 34952, 61448], [15, 240, 3840, 4369, 8738, 17652, 17663, 63624], [15, 240, 3840, 4369, 8738, 26214, 63624, 64716], [15, 240, 3840, 4383, 8738, 17476, 61680, 63624], [15, 240, 3840, 8738, 17476, 61680, 61713, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61457], [15, 240, 3840, 4369, 8751, 17476, 34956, 61440]], [[15, 240, 3840, 4369, 8738, 17476, 63624, 63656]], [[15, 240, 3840, 4369, 8738, 17476, 56797, 63624], [15, 240, 3840, 4369, 8738, 17652, 34952, 63488], [15, 240, 3840, 4369, 8738, 21845, 52428, 63624], [15, 240, 3840, 4369, 8946, 17476, 36744, 63624], [15, 240, 3840, 8738, 17476, 21845, 39321, 63624], [15, 240, 8738, 20292, 34952, 36744, 61713]], [[15, 240, 3840, 4369, 8738, 17476, 63624, 63903], [15, 240, 3840, 4369, 8738, 21845, 26214, 63624], [15, 240, 3840, 4369, 8751, 17476, 61440, 63624], [15, 240, 3840, 4369, 13107, 17476, 26214, 63624], [15, 240, 3840, 8738, 13107, 17476, 21845, 63624], [15, 3840, 4369, 8320, 8946, 17476, 63624]]], [[[15, 240, 3840, 4369, 8751, 17652, 36744, 61440]], [[15, 240, 3840, 4369, 8738, 17476, 35208, 61696], [15, 240, 3840, 4369, 8738, 17652, 35064, 63624], [15, 240, 3840, 4369, 8738, 17732, 35208, 61440]], [[15, 240, 3840, 4369, 8738, 17476, 35464, 64136], [15, 240, 3840, 4369, 8738, 17476, 35976, 63624], [15, 240, 3840, 4369, 8738, 17492, 61440, 63624], [15, 240, 3840, 4369, 8946, 17476, 52428, 63624]], [[15, 240, 3840, 4369, 8946, 17476, 26214, 63624]], [[12, 240, 3840, 4369, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8946, 17476, 63624], [15, 240, 8738, 20292, 34952, 61713]], [[1, 15, 240, 3840, 4369, 8946, 17476, 63624], [1, 15, 240, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 8946, 17476, 61986, 63624], [15, 240, 3840, 4369, 8946, 17476, 63624, 65416]], [[15, 240, 3840, 4369, 8751, 17476, 63624, 63897]], [[1, 240, 3840, 4383, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 34952, 61713], [15, 240, 3840, 4383, 4607, 8738, 17476, 63624], [15, 240, 3840, 4383, 8738, 17476, 63624, 63897], [15, 240, 3840, 8738, 17476, 61713, 61937, 63624], [15, 240, 3840, 8738, 17476, 61713, 63624, 63897]], [[4, 15, 240, 3840, 4369, 8946, 17476, 63624], [4, 15, 240, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 8738, 17652, 63624, 63736], [15, 240, 3840, 4369, 8738, 17652, 63624, 64716], [15, 240, 3840, 4369, 8751, 17476, 34968, 61440]], [[15, 240, 3840, 4369, 8738, 17476, 20303, 63624], [15, 240, 3840, 4369, 8738, 17487, 20292, 63624], [15, 240, 4369, 8738, 17652, 20292, 63624], [15, 3840, 4369, 8946, 17476, 63624]], [[1, 15, 3840, 4369, 8946, 17476, 63624], [15, 240, 3840, 4369, 17476, 25122, 63624], [15, 240, 3840, 8738, 17476, 20753, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61717], [15, 240, 3840, 4369, 8738, 17476, 34956, 61713], [15, 240, 3840, 4369, 8738, 17476, 34968, 61456], [15, 240, 3840, 4369, 8738, 17492, 34952, 61456], [15, 240, 3840, 4369, 8738, 17492, 34968, 61440], [15, 240, 3840, 4369, 8751, 17476, 20292, 63624]], [[1, 15, 240, 3840, 8946, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17652, 21845, 63624], [15, 240, 3840, 4383, 8738, 17476, 20292, 63624]], [[1, 15, 240, 4369, 8738, 20292, 36744, 61440], [4, 15, 3840, 4369, 8946, 17476, 63624], [4, 15, 3840, 4369, 8946, 26358, 34952, 61440], [12, 240, 4369, 8738, 17476, 20292, 34952, 61440], [15, 66, 3840, 4369, 8946, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 39417, 63624], [15, 240, 3840, 4383, 8738, 17476, 63624, 63903]], [[15, 79, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 255, 3840, 4369, 8946, 17476, 63624], [15, 240, 255, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 4383, 8738, 17476, 63624], [15, 240, 3840, 4369, 8751, 17476, 61455, 63624]], [[4, 15, 240, 3840, 8946, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 34952, 61721], [15, 240, 3840, 4369, 8738, 17484, 34952, 61713], [15, 240, 3840, 4369, 8738, 17652, 36744, 61713], [15, 240, 3840, 4383, 8738, 17476, 61455, 63624], [15, 240, 3840, 8738, 17476, 61455, 61713, 63624]]], [[[4, 15, 240, 4369, 8738, 20292, 36744, 61440], [15, 240, 3840, 4369, 8738, 26214, 62532, 63624], [15, 240, 3840, 4369, 8946, 17476, 17652, 63624]], [[1, 15, 3840, 8946, 17476, 34952, 61713], [15, 240, 3840, 4369, 8959, 17476, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 35208, 61713], [15, 240, 3840, 4369, 8738, 17508, 61440, 63624], [15, 240, 3840, 4369, 8738, 17652, 52476, 63624], [15, 240, 3840, 4383, 8946, 17476, 63624]], [[15, 255, 3840, 4369, 8946, 17476, 63624]], [[4, 15, 3840, 8946, 17476, 34952, 61713]], [[15, 240, 255, 3840, 8946, 17476, 34952, 61713]], [[15, 240, 3840, 4369, 8738, 17476, 35016, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34968, 61713], [15, 240, 3840, 4369, 8738, 17492, 34952, 61713]], [], [], [[15, 79, 3840, 4369, 8946, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 63624, 64175]], [[15, 240, 255, 3840, 4369, 8959, 17476, 63624], [15, 240, 3840, 4369, 4383, 8751, 17476, 63624], [15, 240, 3840, 4369, 8751, 17476, 61713, 63624]], [[15, 240, 3840, 4369, 8946, 12274, 17476, 63624], [15, 240, 3840, 4383, 8738, 17476, 61713, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 62225], [15, 240, 3840, 4369, 8738, 17476, 35464, 61713], [15, 240, 3840, 4369, 8738, 17652, 62532, 63624], [15, 240, 3840, 8738, 17476, 61455, 61727, 63624]], [], []], [[], [[4, 15, 240, 3840, 4369, 8738, 24576, 34952], [15, 240, 3840, 4369, 8738, 12066, 17652, 63624], [15, 240, 3840, 4369, 8946, 17476, 35064, 63624], [15, 3840, 4369, 8946, 12274, 17476, 63624]], [[15, 143, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8751, 17476, 63624, 64170]], [[15, 240, 3840, 4369, 8738, 17476, 36744, 63624], [15, 240, 3840, 4383, 8738, 17476, 63624, 64170], [15, 240, 8738, 20292, 34952, 53196, 61713]], [[12, 240, 3840, 4369, 8738, 17476, 52428, 63624]], [], [[4, 8, 240, 3840, 4369, 8738, 17476, 63624], [12, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17652, 34952, 61568], [15, 3840, 4369, 8946, 17476, 35064, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 52428, 63624], [15, 240, 3840, 4369, 8738, 17508, 34952, 61713], [15, 240, 3840, 4369, 8751, 17476, 63624, 64175]], [[15, 240, 3840, 4369, 8946, 17476, 63624, 63736], [15, 240, 3840, 4369, 8946, 17476, 63624, 64716]], [[4, 240, 3840, 4369, 8738, 17487, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624]], [[1, 15, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 36751, 63624], [15, 240, 3840, 4369, 8738, 17476, 52431, 63624], [15, 240, 3840, 4369, 8739, 17476, 63624], [15, 240, 3840, 4383, 8738, 17476, 61727, 63624], [15, 240, 3840, 8738, 17476, 61713, 61727, 63624]], [[1, 15, 240, 3840, 4369, 8739, 17476, 63624], [12, 240, 3840, 8738, 17476, 34952, 52428, 61713], [15, 240, 3840, 4371, 8738, 17476, 63624]], [[3, 15, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8946, 17476, 21845, 63624], [15, 240, 8738, 20292, 21845, 34952, 61713]], [[4, 8, 240, 3840, 8738, 17476, 34952, 61713], [4, 15, 240, 3840, 4369, 8738, 17476, 63624], [12, 240, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 63628], [15, 240, 3840, 4369, 8742, 17476, 63624], [15, 240, 3840, 4373, 8738, 17476, 63624]], [[5, 15, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 4369, 8738, 17652, 36744, 63624]], [[6, 15, 240, 3840, 4369, 8738, 17476, 63624], [15, 132, 3840, 4369, 8738, 17652, 34952, 61440], [15, 240, 3840, 4369, 8946, 17476, 36744, 61713]]], [[[15, 240, 3840, 4369, 8751, 17476, 36744, 63624]], [[1, 15, 240, 3840, 8738, 17476, 34952, 61713], [4, 15, 240, 3840, 4369, 8738, 17476, 63628], [4, 15, 240, 3840, 4369, 8742, 17476, 63624], [4, 15, 240, 3840, 4373, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624, 64443], [15, 240, 3840, 4369, 8738, 17476, 63631, 65416], [15, 240, 3840, 4369, 8738, 17484, 63624], [15, 240, 3840, 4369, 8746, 17476, 63624], [15, 240, 3840, 4377, 8738, 17476, 63624]], [[4, 15, 3840, 4369, 8738, 26358, 34952, 61440], [15, 240, 3840, 4369, 8738, 17487, 52428, 63624]], [[3, 15, 240, 3840, 8738, 17476, 34952, 61713], [15, 240, 255, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 35976, 61713]], [[4, 15, 240, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 63880], [15, 240, 3840, 4369, 8738, 17652, 43690, 63624], [15, 240, 3840, 4369, 8738, 17732, 63624], [15, 240, 3840, 4369, 8751, 17476, 52428, 63624], [15, 240, 3840, 4369, 8994, 17476, 63624]], [[5, 15, 240, 3840, 8738, 17476, 34952, 61713], [12, 15, 240, 3840, 4369, 8738, 17476, 63624], [12, 240, 3840, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8751, 17476, 26214, 63624], [15, 240, 3840, 4383, 8738, 17476, 52428, 63624]], [[6, 15, 240, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8751, 17476, 63624], [15, 240, 4369, 8738, 20292, 62532, 63624]], [[1, 15, 240, 3840, 4369, 8751, 17476, 63624], [15, 240, 3840, 4369, 8751, 17476, 61986, 63624], [15, 240, 3840, 4369, 8751, 17476, 63624, 65416], [15, 240, 3840, 4383, 8738, 17476, 63624], [15, 240, 3840, 8738, 17476, 61713, 63624]], [[1, 15, 240, 3840, 4383, 8738, 17476, 63624], [1, 15, 240, 3840, 8738, 17476, 61713, 63624], [1, 240, 3840, 4383, 8738, 17476, 36744, 61440], [4, 15, 240, 3840, 4369, 8738, 17487, 63624], [4, 15, 240, 3840, 8738, 17476, 34952, 61717], [4, 15, 240, 3840, 8738, 17476, 34956, 61713], [4, 15, 240, 3840, 8742, 17476, 34952, 61713], [4, 15, 240, 3844, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17652, 63624, 64764], [15, 240, 3840, 4383, 8738, 17476, 61986, 63624], [15, 240, 3840, 4383, 8738, 17476, 63624, 65416], [15, 240, 3840, 8738, 17476, 61713, 61986, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 63640], [15, 240, 3840, 4369, 8738, 17492, 63624], [15, 240, 3840, 4369, 8739, 17476, 36744, 61440], [15, 240, 3840, 4369, 8754, 17476, 63624]], [[4, 15, 240, 3840, 4369, 8751, 17476, 63624], [4, 15, 240, 4369, 8738, 26214, 36744, 61440], [15, 143, 3840, 4369, 8738, 17652, 34952, 61440], [15, 240, 255, 3840, 8738, 17476, 34952, 61713]], [[1, 15, 3840, 4369, 8738, 17476, 17652, 63624], [4, 15, 240, 3840, 4383, 8738, 17476, 63624], [4, 15, 240, 3840, 8738, 17476, 61713, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624, 65433]], [[12, 15, 240, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8742, 17476, 36744, 61440]], [[15, 240, 3840, 4369, 8946, 17476, 62532, 63624], [15, 240, 3840, 4369, 12066, 13107, 17476, 63624]], [[15, 240, 287, 3840, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8751, 17476, 26223, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 36744, 63897], [15, 240, 3840, 4369, 8738, 17988, 63624], [15, 240, 3840, 4881, 8738, 17476, 63624]]], [[[15, 240, 255, 3840, 4369, 8751, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 17663, 63624], [15, 240, 3840, 4369, 8738, 17476, 36744, 61448], [15, 240, 3840, 4369, 8738, 17484, 36744, 61440], [15, 240, 3840, 4369, 8738, 17487, 17652, 63624], [15, 240, 3840, 4369, 8746, 17476, 36744, 61440], [15, 240, 3840, 4369, 8946, 17476, 63624, 64250]], [[15, 240, 255, 3840, 4383, 8738, 17476, 63624], [15, 240, 255, 3840, 8738, 17476, 61713, 63624], [15, 240, 3840, 4369, 8738, 12274, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 43144, 63624], [15, 240, 3840, 4369, 8946, 12066, 17476, 63624], [15, 240, 8738, 12066, 20292, 34952, 61713]], [[1, 15, 3840, 8738, 17476, 17652, 34952, 61713], [15, 240, 3840, 4369, 8751, 17476, 17652, 63624]], [[15, 240, 271, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 52428, 63897], [15, 240, 3840, 4369, 8738, 17732, 36744, 61440], [15, 240, 3840, 4383, 8738, 17476, 17652, 63624]], [[1, 15, 240, 4369, 8738, 17652, 36744, 61440], [15, 240, 3840, 4369, 8751, 17476, 61999, 63624], [15, 240, 3840, 4383, 8751, 17476, 63624]], [[15, 240, 3840, 4369, 8751, 17476, 36744, 61440], [15, 3840, 4369, 8946, 17476, 63624, 64250]], [[4, 15, 4369, 8738, 8946, 20292, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 35064, 63624], [15, 240, 3840, 4369, 8738, 17476, 63897, 65416]], [[4, 15, 240, 4369, 8738, 17652, 36744, 61440], [15, 3840, 4369, 8751, 17476, 17652, 63624]], [[4, 15, 3840, 4369, 8946, 20292, 34952, 61440], [15, 31, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 53196, 63624], [15, 240, 3840, 4369, 8738, 17492, 36744, 61440], [15, 240, 3840, 7953, 8738, 13107, 17476, 63624]], [[15, 240, 3840, 4369, 8738, 17508, 63624], [15, 240, 3840, 4369, 8946, 13299, 17476, 63624]], [[12, 240, 3840, 4369, 8738, 17476, 63624, 64716], [15, 240, 271, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 8738, 17476, 21845, 63624, 63897]], [], [[15, 240, 3840, 4369, 8751, 17476, 61440, 65416]], [[15, 130, 3840, 4369, 8946, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 35071, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624, 63736]], [[15, 143, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 527, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17988, 36744, 61440]], [[1, 15, 240, 4369, 8738, 17476, 20292, 63624], [15, 31, 240, 3840, 8738, 17476, 34952, 61713]]], [[[15, 240, 3840, 4369, 8738, 17476, 48059, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624, 64719], [15, 240, 3840, 4369, 13107, 17476, 43690, 63624], [15, 240, 3840, 8738, 13107, 17476, 39321, 63624]], [[15, 240, 8738, 20292, 36744, 61713]], [[15, 240, 3840, 4369, 8738, 17652, 63624, 65280]], [[15, 240, 3840, 4369, 8751, 17476, 35064, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 36744, 61713], [15, 240, 3840, 4369, 8738, 17476, 63624, 63743], [15, 240, 3840, 4369, 8738, 17476, 63631, 63736], [15, 240, 3840, 4369, 8738, 17476, 63631, 64716], [15, 240, 3840, 4369, 8946, 17476, 43690, 63624], [15, 240, 3840, 4383, 8738, 17476, 35064, 63624], [15, 240, 3840, 8738, 17476, 61713, 62259, 63624], [15, 240, 8738, 20292, 34952, 43690, 61713]], [[15, 240, 527, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 7953, 8738, 17652, 63624]], [[1, 15, 240, 8738, 17476, 20292, 34952, 61713], [15, 240, 3840, 4369, 8738, 17604, 34952, 63624]], [[12, 240, 4369, 8738, 17476, 34952, 53196, 61440], [15, 240, 3840, 4369, 8738, 17476, 52476, 63624]], [[15, 47, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 255, 4369, 8738, 17476, 20292, 63624], [15, 240, 3840, 4369, 8738, 17487, 63624, 64716], [15, 240, 3840, 4369, 8738, 17508, 36744, 61440]], [[15, 240, 3840, 4369, 8738, 17476, 63624, 63993], [15, 240, 4369, 8738, 17487, 20292, 63624], [15, 3840, 4369, 8946, 17476, 43690, 63624]], [[15, 143, 3840, 4369, 8946, 17476, 34952, 61440], [15, 240, 3840, 4369, 8751, 17476, 63624, 63736], [15, 240, 3840, 4369, 8751, 17476, 63624, 64716]], [[15, 240, 3840, 4383, 8738, 17476, 63624, 63736], [15, 240, 3840, 4383, 8738, 17476, 63624, 64716], [15, 240, 4369, 8751, 17476, 20292, 63624]], [[15, 240, 3840, 4369, 26214, 34952, 61986, 62532]], [[15, 240, 3840, 4369, 8738, 17652, 39321, 63624]], [[15, 240, 3840, 4369, 8751, 17476, 21845, 63624]], [[15, 47, 240, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 4383, 8738, 17476, 21845, 63624], [15, 240, 3840, 8738, 17476, 21845, 61713, 63624], [15, 240, 4369, 8738, 17652, 36744, 61713]]], [[[15, 240, 3840, 4369, 8946, 17476, 17487, 63624]], [], [[15, 240, 3840, 4369, 8738, 8946, 17652, 63624], [15, 240, 3840, 4369, 8738, 17476, 35064, 63897], [15, 240, 3840, 4383, 8738, 17476, 36744, 61713]], [], [[1, 15, 240, 4369, 8946, 17476, 36744, 61440], [1, 240, 3840, 4383, 8738, 20292, 34952, 61440], [15, 240, 1039, 3840, 4369, 8738, 17476, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 43144, 61455], [15, 240, 3840, 4369, 8738, 17476, 63624, 64250], [15, 240, 3840, 4369, 8738, 25668, 34952, 61455]], [[4, 240, 3840, 4369, 8751, 20292, 34952, 61440], [15, 240, 3840, 4369, 8738, 20292, 61680, 63624], [15, 240, 3840, 4369, 17476, 26214, 63624, 64170], [15, 240, 8738, 20292, 28518, 34952, 61713]], [[4, 15, 240, 4369, 8946, 17476, 36744, 61440], [4, 240, 3840, 4383, 8738, 20292, 34952, 61440]], [[15, 240, 3840, 4369, 8738, 20292, 34952, 61444]], [[15, 240, 3840, 4369, 8738, 17476, 63624, 64989], [15, 240, 3840, 4369, 8738, 17476, 63736, 63897], [15, 240, 3840, 4369, 8738, 17652, 20468, 63624], [15, 240, 3840, 4369, 8802, 17476, 63624], [15, 240, 3840, 4383, 8738, 17476, 21855, 63624]], [], [[15, 240, 1039, 3840, 8738, 17476, 34952, 61713]], [], [[15, 240, 3840, 4369, 8738, 17487, 62532, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 59528]], [[15, 240, 3840, 4369, 8751, 17476, 62532, 63624]]], [[[15, 240, 3840, 4383, 8738, 17476, 62532, 63624]], [], [[4, 15, 3840, 4369, 8946, 26214, 34952, 61440], [15, 240, 3840, 4369, 8738, 17604, 61440, 63624], [15, 240, 3840, 4369, 8946, 17476, 63624, 65280], [15, 240, 8738, 20292, 34952, 61713, 65280]], [[15, 240, 3840, 4369, 8738, 12079, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 34952, 61576], [15, 240, 3840, 4369, 8738, 17652, 26358, 63624], [15, 240, 3840, 4369, 8751, 12066, 17476, 63624]], [[1, 15, 240, 4369, 8738, 17476, 36744, 63624], [4, 15, 240, 3840, 4369, 25122, 34952, 61440], [4, 15, 240, 4369, 8738, 20224, 34952, 61440], [4, 15, 3840, 4369, 8738, 16624, 34952, 61440], [4, 240, 3840, 4369, 8738, 16399, 34952, 61440], [15, 240, 3840, 4369, 8738, 20292, 34968, 61440], [15, 240, 3840, 4383, 8738, 12066, 17476, 63624], [15, 240, 3840, 8738, 12066, 17476, 61713, 63624]], [[15, 240, 3840, 4369, 7953, 8946, 17476, 63624], [15, 240, 7953, 8738, 20292, 34952, 61713]], [], [], [[15, 79, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 4080, 8738, 17476, 36744, 61713]], [[15, 240, 3840, 4369, 8738, 17476, 43690, 63624]], [[15, 240, 3840, 4369, 8738, 20292, 61455, 63624], [15, 3840, 4369, 7953, 8946, 17476, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61584], [15, 240, 3840, 4369, 17476, 26214, 61986, 63624]], [], [[15, 240, 255, 4369, 8738, 17476, 36744, 63624], [15, 240, 3840, 4369, 8946, 17476, 39321, 63624], [15, 240, 8738, 20292, 34952, 39321, 61713]], [[1, 15, 240, 3840, 8738, 17476, 36744, 61713], [15, 240, 3840, 4369, 8738, 17476, 43695, 63624], [15, 240, 3840, 4369, 8946, 13107, 17476, 63624], [15, 240, 8738, 13107, 20292, 34952, 61713]], [[4, 15, 3840, 4369, 8946, 17652, 34952, 61440], [15, 79, 240, 3840, 8738, 17476, 34952, 61713]]], [[[15, 240, 3840, 4369, 8751, 12079, 17476, 63624], [15, 240, 4369, 8751, 17476, 36744, 63624]], [[4, 15, 240, 3840, 8738, 17476, 36744, 61713]], [], [[12, 240, 4369, 8738, 17476, 36744, 52428, 61440], [15, 240, 8738, 20292, 34952, 61713, 65297]], [[15, 240, 3840, 8738, 17476, 61713, 65416]], [[4, 8, 240, 4369, 8738, 17476, 36744, 61440], [12, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8177, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 17487, 63624], [15, 240, 3840, 4593, 7953, 8738, 17476, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 39048, 63624], [15, 240, 3840, 4369, 8738, 17652, 34952, 63624], [15, 240, 3840, 4369, 8751, 17476, 43690, 63624]], [[15, 240, 255, 3840, 8738, 17476, 36744, 61713], [15, 240, 3840, 4369, 8738, 17476, 34952, 61841], [15, 240, 3840, 4369, 8738, 17604, 34952, 61713], [15, 240, 3840, 4369, 8738, 20292, 61713, 63624], [15, 240, 3840, 4383, 8738, 17476, 43690, 63624]], [[1, 240, 4383, 8738, 17476, 36744, 61440]], [[1, 15, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 8738, 20292, 20468, 34952, 61713]], [[1, 15, 240, 4369, 8738, 17476, 36744, 61441], [1, 15, 240, 4369, 8739, 17476, 36744, 61440]], [[3, 15, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8751, 17476, 43695, 63624]], [[15, 240, 3840, 4369, 26214, 43690, 52428, 61440], [15, 240, 3840, 8738, 17476, 61713, 62805, 63624], [15, 240, 3855, 8738, 17476, 36744, 61713]], [[5, 15, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8738, 17652, 34959, 63624], [15, 240, 3840, 4593, 8738, 17476, 39321, 63624]], [[6, 15, 240, 4369, 8738, 17476, 36744, 61440]], [[4, 15, 3840, 4369, 8738, 17652, 34952, 63624], [15, 240, 3840, 4369, 8946, 8959, 17476, 63624]]], [[[4, 15, 240, 4369, 8742, 17476, 36744, 61440], [4, 240, 3840, 4369, 8751, 26214, 34952, 61440], [15, 240, 2063, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 36744, 63488], [15, 240, 3840, 4369, 8738, 19524, 36744, 61440]], [], [[15, 240, 3840, 4369, 8751, 17476, 17487, 63624], [15, 240, 3840, 4369, 8946, 17652, 34952, 61713]], [[15, 240, 3840, 4369, 8738, 17476, 36856, 63624], [15, 240, 3840, 4369, 8751, 17652, 34952, 63624], [15, 240, 3840, 4369, 8946, 17476, 26358, 63624], [15, 240, 3840, 4383, 8738, 17476, 17487, 63624]], [[12, 15, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8738, 8751, 17652, 63624], [15, 240, 3840, 4369, 8738, 17652, 63624, 63631], [15, 240, 3840, 4369, 8738, 25668, 63624], [15, 240, 3840, 8738, 12561, 17476, 63624], [15, 3840, 4369, 8946, 8959, 17476, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 43690, 63897]], [[1, 15, 240, 4369, 8751, 17476, 36744, 61440]], [[1, 15, 240, 4383, 8738, 17476, 36744, 61440], [4, 15, 240, 4369, 8738, 17487, 36744, 61440], [15, 240, 2063, 3840, 8738, 17476, 34952, 61713]], [[15, 240, 3840, 3855, 4369, 8738, 17652, 63624]], [[4, 15, 240, 4369, 8751, 17476, 36744, 61440], [4, 240, 3840, 4369, 8751, 26223, 34952, 61440]], [[4, 15, 240, 4383, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 7953, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 63736, 65416], [15, 240, 8738, 20292, 24405, 34952, 61713]], [[1, 240, 3840, 4383, 8738, 17652, 34952, 61440], [4, 240, 3840, 4369, 8738, 17663, 34952, 61440], [15, 240, 3840, 4369, 4593, 8738, 17652, 63624]], [[15, 240, 3840, 8738, 13107, 17476, 63624, 63897]], [[4, 240, 3840, 4369, 8751, 17652, 34952, 61440], [15, 240, 3840, 4369, 8738, 17652, 61680, 63624]], [[4, 240, 3840, 4383, 8738, 17652, 34952, 61440]], [[15, 240, 3840, 4369, 8738, 17652, 34952, 61444]]], [[], [[15, 240, 3840, 4369, 8738, 20292, 26214, 63624]], [[4, 3840, 4369, 8751, 17652, 34952, 61440], [15, 240, 271, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8738, 17476, 39321, 63624], [15, 240, 3840, 4369, 8738, 17652, 34952, 63897], [15, 240, 3840, 4369, 8738, 17652, 61440, 63624]], [[15, 240, 3840, 4369, 8738, 17652, 34952, 61448], [15, 240, 3840, 4369, 8738, 20292, 61986, 63624]], [[4, 15, 3840, 4369, 8738, 17652, 34952, 61440], [12, 240, 4369, 8738, 17476, 36744, 53196, 61440], [15, 240, 3840, 4369, 8751, 17476, 63624, 65280], [15, 240, 3840, 4369, 8946, 17476, 43770, 63624], [15, 240, 4080, 8738, 20292, 34952, 61713]], [[1, 15, 240, 4369, 8738, 17476, 36744, 61713], [5, 15, 3840, 4369, 8738, 17652, 34952, 61440], [15, 240, 3840, 4383, 8738, 17476, 63624, 65280]], [[6, 15, 3840, 4369, 8738, 17652, 34952, 61440], [15, 240, 3840, 4369, 8738, 17652, 35208, 61440]], [[15, 31, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 7953, 8751, 17476, 63624], [15, 240, 3840, 4369, 8738, 8946, 17476, 63624]], [[1, 15, 3840, 4369, 8738, 17652, 61440, 63624], [4, 15, 3840, 4369, 8738, 17652, 34952, 61444], [4, 15, 3840, 4369, 8738, 17652, 34956, 61440], [4, 15, 3840, 4369, 8742, 17652, 34952, 61440], [4, 15, 3840, 4373, 8738, 17652, 34952, 61440], [4, 15, 3844, 4369, 8738, 17652, 34952, 61440], [15, 240, 3840, 4369, 7967, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 39327, 63624], [15, 240, 3840, 4383, 7953, 8738, 17476, 63624], [15, 240, 3840, 7953, 8738, 17476, 61713, 63624]], [[15, 240, 264, 4383, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8738, 17604, 63624], [15, 240, 3840, 4369, 8738, 17652, 63624, 63897], [15, 240, 3840, 4369, 8866, 17476, 63624], [15, 240, 3840, 4497, 8738, 17476, 63624], [15, 3840, 4369, 8946, 17476, 43770, 63624]], [[1, 15, 240, 3840, 8738, 20292, 34952, 61713]], [[4, 15, 3840, 4369, 8738, 17652, 61440, 63624], [15, 240, 3840, 4369, 8738, 17652, 34968, 61440]], [[15, 240, 3840, 4369, 8738, 17476, 51336, 63624], [15, 240, 3840, 4369, 8738, 17652, 22005, 63624]], [[1, 15, 3840, 4369, 8738, 8946, 17476, 63624], [4, 15, 240, 3840, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 8946, 17476, 34959, 63624], [15, 240, 8738, 20292, 34952, 34959, 61713]], [[15, 240, 3840, 4369, 8738, 17652, 20292, 63624]], [[1, 15, 3840, 4383, 8738, 17652, 34952, 61440], [1, 15, 3840, 8738, 17652, 34952, 61440, 61713], [4, 15, 3840, 4369, 8946, 17476, 34952, 63624], [15, 240, 3840, 4369, 8738, 13119, 17476, 63624], [15, 240, 3840, 4369, 8751, 17476, 39321, 63624], [15, 240, 3840, 4369, 8751, 17652, 61440, 63624]]], [[[15, 240, 3840, 4369, 8738, 17476, 44970, 63624], [15, 240, 3840, 4369, 8751, 13107, 17476, 63624], [15, 240, 3840, 4383, 8738, 17476, 39321, 63624], [15, 240, 3840, 8738, 17476, 39321, 61713, 63624], [15, 240, 3840, 8738, 20292, 61713, 63624]], [[4, 15, 3840, 4369, 8751, 17652, 34952, 61440], [15, 240, 3840, 4369, 8738, 17652, 35464, 61440], [15, 240, 3840, 4369, 8738, 17652, 61455, 63624], [15, 240, 3840, 4369, 8738, 20292, 36744, 61440], [15, 240, 3840, 4383, 8738, 13107, 17476, 63624], [15, 240, 3840, 8738, 13107, 17476, 61713, 63624]], [[4, 15, 3840, 4383, 8738, 17652, 34952, 61440], [4, 15, 3840, 8738, 17652, 34952, 61440, 61713]], [[4, 240, 255, 4369, 8738, 20292, 34952, 61440], [15, 240, 255, 3840, 8738, 20292, 34952, 61713]], [[1, 15, 3840, 8738, 8946, 17476, 34952, 61713], [1, 240, 4383, 8738, 20292, 34952, 61440], [12, 240, 3840, 4369, 8738, 17476, 39321, 61440], [15, 20, 3840, 4369, 8738, 17652, 34952, 61440], [15, 240, 3840, 4369, 8738, 8959, 17476, 63624], [15, 240, 3840, 4369, 8751, 8946, 17476, 63624], [15, 240, 3840, 4369, 8946, 17476, 63624, 63631], [15, 240, 3840, 4369, 8946, 17652, 63624], [15, 240, 8738, 8751, 20292, 34952, 61713]], [[1, 15, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 3840, 4383, 8738, 8946, 17476, 63624], [15, 240, 3840, 8738, 8946, 17476, 61713, 63624]], [[1, 15, 240, 4369, 8738, 20292, 34952, 61441], [4, 240, 4369, 8751, 20292, 34952, 61440], [15, 240, 3840, 4383, 7967, 8738, 17476, 63624], [15, 240, 3840, 4383, 8738, 17476, 39327, 63624]], [[4, 240, 4383, 8738, 20292, 34952, 61440], [15, 47, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8738, 17652, 34952, 61713]], [[4, 15, 240, 4369, 8738, 20292, 34952, 61440], [12, 240, 3840, 4369, 8946, 17476, 34952, 61440], [15, 143, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 3855, 4369, 8946, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 36744, 61568], [15, 240, 3840, 4369, 8738, 17604, 36744, 61440], [15, 240, 3840, 4369, 8738, 20292, 61440, 65416], [15, 240, 3855, 8738, 20292, 34952, 61713]], [[5, 15, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 12066, 17476, 61986, 63624], [15, 3840, 4369, 8751, 8946, 17476, 63624], [15, 3840, 4369, 8946, 17652, 63624]], [[6, 15, 240, 4369, 8738, 20292, 34952, 61440]], [[4, 240, 3840, 4369, 8946, 17487, 34952, 61440], [15, 240, 3840, 4369, 4593, 8946, 17476, 63624], [15, 240, 4593, 8738, 20292, 34952, 61713]], [[1, 15, 240, 4369, 8738, 20292, 61440, 63624], [4, 15, 240, 4369, 8738, 20292, 34952, 61444], [4, 15, 240, 4369, 8738, 20292, 34956, 61440], [4, 15, 240, 4369, 8742, 20292, 34952, 61440], [4, 15, 240, 4373, 8738, 20292, 34952, 61440], [4, 15, 244, 4369, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 8751, 13119, 17476, 63624]], [[15, 240, 3840, 4369, 8946, 17476, 61680, 63624], [15, 240, 3840, 4383, 8738, 13119, 17476, 63624], [15, 3840, 3855, 4369, 8946, 17476, 63624]], [[15, 240, 3840, 4369, 4383, 8738, 17652, 63624], [15, 240, 3840, 4369, 8738, 17652, 61713, 63624], [15, 240, 3840, 4369, 8751, 20292, 36744, 61440]], [[4, 15, 240, 4369, 8738, 20292, 61440, 63624], [15, 31, 3840, 4369, 8738, 17652, 34952, 61440], [15, 143, 240, 3840, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 39321, 61448], [15, 240, 3840, 4369, 8738, 17484, 39321, 61440], [15, 240, 3840, 4369, 8746, 17476, 39321, 61440]]], [[[4, 15, 3840, 4369, 8738, 17652, 34952, 61713], [4, 3840, 4369, 8946, 17487, 34952, 61440], [15, 3840, 4369, 4593, 8946, 17476, 63624]], [[15, 240, 3840, 4369, 8751, 8959, 17476, 63624]], [[15, 20, 3840, 4383, 8738, 17652, 34952, 61440]], [[1, 15, 240, 4383, 8738, 20292, 34952, 61440], [1, 15, 240, 8738, 20292, 34952, 61440, 61713], [15, 240, 260, 4369, 8738, 20292, 34952, 61440], [15, 240, 1039, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8946, 17652, 36744, 61440]], [[4, 15, 3840, 4369, 8946, 17476, 34952, 61440]], [[4, 15, 240, 4369, 8751, 20292, 34952, 61440], [5, 15, 3840, 4369, 8946, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17652, 63624, 64170]], [[4, 15, 240, 4383, 8738, 20292, 34952, 61440], [4, 15, 240, 8738, 20292, 34952, 61440, 61713], [6, 15, 3840, 4369, 8946, 17476, 34952, 61440]], [[15, 240, 3840, 4369, 8738, 17652, 35976, 61440], [15, 240, 8738, 20292, 34952, 61713, 65365]], [[4, 15, 3840, 4369, 8946, 17476, 34952, 61444], [4, 15, 3840, 4369, 8950, 17476, 34952, 61440], [4, 15, 3840, 4373, 8946, 17476, 34952, 61440], [12, 240, 3840, 4369, 8738, 17476, 34952, 63624]], [[4, 15, 4369, 8738, 17652, 20292, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 43770, 63624], [15, 240, 3840, 4369, 8946, 17476, 63624, 63897]], [[15, 240, 3840, 4369, 8738, 17476, 61166, 63624], [15, 240, 3840, 4369, 8738, 20292, 21845, 63624], [15, 240, 3840, 4369, 8738, 26214, 52428, 63624], [15, 240, 3840, 4369, 17476, 26214, 43690, 63624]], [[1, 240, 3840, 4383, 8738, 17476, 34952, 63624], [4, 240, 3840, 4369, 8738, 17487, 34952, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 63625], [15, 240, 3840, 4369, 8738, 17476, 34953, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34954, 63624], [15, 240, 3840, 4369, 8738, 17652, 62708, 63624], [15, 240, 3840, 4369, 8738, 20292, 36744, 61713]], [[15, 240, 271, 4369, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 8946, 17476, 20292, 63624]], [[1, 15, 3840, 8946, 17476, 34952, 61440, 61713], [4, 15, 3840, 4369, 8946, 17487, 34952, 61440], [15, 47, 3840, 4369, 8738, 17652, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34956, 63624]]], [[[4, 15, 240, 3840, 4369, 8738, 26214, 63624], [15, 240, 255, 3840, 4369, 8738, 17476, 61576]], [[1, 15, 240, 4369, 8738, 20292, 34952, 61713], [15, 36, 3840, 4369, 8751, 17652, 34952, 61440], [15, 240, 260, 4383, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 8946, 17476, 61455, 63624]], [[1, 240, 3840, 8738, 8751, 17476, 34952, 61713], [4, 15, 3840, 8946, 17476, 34952, 61440, 61713], [15, 18, 3840, 4369, 8946, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34959, 63624]], [[15, 31, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34956, 63628], [15, 240, 3840, 4369, 8738, 17476, 63624, 63625], [15, 240, 3840, 4369, 8738, 17484, 34952, 63624], [15, 240, 3840, 4369, 8738, 17652, 36744, 63624]], [[4, 15, 240, 4369, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 63624, 63626]], [[15, 240, 3840, 4369, 8946, 17476, 62194, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 35208, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624, 63628], [15, 240, 3840, 4369, 8738, 17732, 34952, 63624]], [[4, 15, 240, 3840, 8738, 26214, 34952, 61713], [15, 79, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8738, 17652, 52428, 63624]], [[15, 240, 3840, 4095, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17652, 26214, 63624]], [[15, 240, 3840, 4369, 8738, 8751, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624, 63631], [15, 240, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4593, 8738, 17476, 63624, 63897], [15, 240, 8738, 20292, 20303, 34952, 61713]], [[1, 15, 240, 3840, 4369, 8738, 17652, 63624], [15, 240, 255, 4369, 8738, 20292, 34952, 61713], [15, 240, 3840, 4369, 8738, 17652, 61986, 63624], [15, 240, 3840, 4369, 8738, 17652, 63624, 65416]], [[15, 240, 3840, 4369, 8738, 17476, 34968, 63624], [15, 240, 3840, 4369, 8738, 17476, 35064, 61568], [15, 240, 3840, 4369, 8738, 17492, 34952, 63624], [15, 240, 3840, 4369, 8738, 20292, 62532, 63624]], [], [[4, 15, 240, 3840, 4369, 8738, 17652, 63624], [12, 240, 3840, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 3855, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624, 63880]], [[13, 240, 3840, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 4383, 8946, 17476, 63624], [15, 240, 3840, 4369, 8946, 17476, 61713, 63624], [15, 240, 4383, 8738, 20292, 34952, 61713]], [[1, 15, 3840, 4369, 8738, 17652, 63624], [15, 31, 3840, 4369, 8946, 17476, 34952, 61440], [15, 240, 3840, 4369, 8751, 17476, 34959, 63624]]], [[[1, 240, 3840, 4383, 8738, 17476, 34952, 61440], [4, 15, 3840, 4369, 8946, 17476, 34952, 61713], [4, 240, 3840, 4369, 8738, 17487, 34952, 61440], [15, 240, 3840, 4369, 4593, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 25122, 34952, 62532], [15, 240, 3840, 4383, 8738, 17476, 34959, 63624], [15, 240, 3840, 8738, 17476, 37137, 63624]], [[1, 15, 240, 3840, 8738, 17652, 34952, 61713], [1, 240, 3840, 4383, 8738, 17476, 34952, 61441], [3, 240, 3840, 4369, 8751, 17476, 34952, 61440], [12, 240, 3840, 4369, 8738, 17476, 34956, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952, 61441], [15, 240, 3840, 4369, 8738, 17476, 35208, 63880], [15, 240, 3840, 4369, 8738, 17476, 35464, 63624], [15, 240, 3840, 4369, 8738, 17988, 34952, 63624]], [[4, 15, 3840, 4369, 8738, 17652, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624, 63640]], [[5, 240, 3840, 4369, 8751, 17476, 34952, 61440], [15, 47, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 255, 3840, 4369, 8738, 17652, 63624], [15, 3840, 4369, 4383, 8946, 17476, 63624]], [[4, 15, 240, 3840, 8738, 17652, 34952, 61713], [4, 240, 3840, 4369, 8738, 17487, 34952, 61444], [4, 240, 3840, 4369, 8742, 17487, 34952, 61440], [4, 240, 3840, 4373, 8738, 17487, 34952, 61440], [5, 240, 3840, 4383, 8738, 17476, 34952, 61440], [6, 240, 3840, 4369, 8751, 17476, 34952, 61440], [12, 240, 3840, 4369, 8738, 17476, 34959, 61440], [12, 240, 3840, 4369, 8738, 17476, 61440, 63624], [15, 240, 3840, 4369, 8738, 17476, 34952, 61444], [15, 240, 3840, 4369, 8738, 17476, 40857, 63624]]]]
  | 8 => [[[[5, 15, 240, 3840, 4369, 8738, 17476, 34952, 61440]], [[6, 15, 240, 3840, 4369, 8738, 17476, 34952, 61440]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 63897]], [[1, 15, 240, 3840, 4369, 8738, 17476, 61440, 63624], [4, 15, 240, 3840, 4369, 8738, 17476, 34952, 61444], [4, 15, 240, 3840, 4369, 8742, 17476, 34952, 61440], [4, 15, 240, 3840, 4373, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952, 61448], [15, 240, 3840, 4369, 8738, 17652, 36744, 61440]], [], [[15, 240, 255, 3840, 4369, 8738, 17476, 34952, 61440]], [], [[12, 15, 240, 3840, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 3855, 4369, 8738, 17476, 36744, 61440]], [], [[15, 240, 3840, 4369, 8738, 17476, 63624, 63897]], [[1, 15, 240, 3840, 4383, 8738, 17476, 34952, 61440], [1, 15, 240, 3840, 8738, 17476, 34952, 61440, 61713], [4, 15, 240, 3840, 4369, 8738, 17487, 34952, 61440], [15, 240, 3840, 4369, 4593, 8738, 17476, 36744, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952, 61713, 61727]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61456]], [[4, 15, 240, 3840, 4369, 8751, 17476, 34952, 61440]], [[4, 15, 240, 3840, 4383, 8738, 17476, 34952, 61440], [4, 15, 240, 3840, 8738, 17476, 34952, 61440, 61713]], [], [[15, 240, 3840, 4369, 8751, 17476, 61440, 63624]]], [[], [], [[15, 240, 255, 3840, 4369, 8751, 17476, 34952, 61440]], [], [[15, 240, 3840, 4369, 8946, 17476, 63624], [15, 240, 8738, 20292, 34952, 61713]], [[15, 240, 271, 3840, 4369, 8738, 17476, 34952, 61440]], [], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61713]], [[1, 15, 240, 3840, 4369, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 34952, 61713, 61986]], [[15, 3840, 4369, 8946, 17476, 63624]], [[15, 31, 240, 3840, 4369, 8738, 17476, 34952, 61440]], [[4, 15, 240, 3840, 4369, 8738, 17476, 34952, 61713]], [], [], [[15, 240, 3840, 4369, 4383, 8738, 17476, 63624]], []], [[], [[15, 240, 255, 3840, 4369, 8738, 17476, 34952, 61713]], [], [], [], [], [], [], [], [], [[15, 47, 240, 3840, 4369, 8738, 17476, 34952, 61440]], [], [], [[15, 240, 3840, 4369, 4383, 8738, 17476, 36744, 61440]], [], []], [[], [], [], [[15, 240, 3840, 4369, 8738, 17476, 36744, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61713, 62259]], [], [[15, 240, 1039, 3840, 4369, 8738, 17476, 34952, 61440]], [[15, 240, 3840, 4369, 8738, 17476, 52428, 63624]], [], [[15, 240, 3840, 4369, 8738, 17476, 63624]], [[1, 15, 240, 3840, 4369, 8738, 17476, 63624]], [], [], [[4, 15, 240, 3840, 4369, 8738, 17476, 63624]], [], []], [[], [[1, 15, 240, 3840, 8738, 17476, 34952, 61713]], [], [[15, 240, 255, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 34952, 61455, 62532]], [[4, 15, 240, 3840, 8738, 17476, 34952, 61713]], [], [[15, 240, 3840, 4369, 8751, 17476, 63624]], [[15, 240, 3840, 4383, 8738, 17476, 63624], [15, 240, 3840, 8738, 17476, 61713, 63624]], [], [[1, 15, 240, 3840, 4369, 8738, 17476, 36744, 61440]], [[15, 79, 240, 3840, 4369, 8738, 17476, 34952, 61440], [15, 240, 255, 3840, 8738, 17476, 34952, 61713]], [], [], [], [], []], [[[15, 240, 3840, 4369, 8738, 17476, 34952, 61713, 62532]], [], [[15, 240, 255, 3840, 4369, 8738, 17476, 36744, 61440]], [], [], [[15, 240, 3840, 4369, 8751, 17476, 36744, 61440]], [[15, 240, 3840, 4369, 8738, 17476, 35064, 63624]], [[15, 240, 3840, 4369, 8177, 8738, 17476, 34952, 61440]], [], [[15, 240, 3840, 4369, 4383, 8738, 20292, 34952, 61440]], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 63624, 63736]], [], []], [[], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 36744, 61713]], [], [], [], [], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61713, 62805], [15, 240, 3840, 4369, 8738, 17476, 34952, 61986, 62532]], [], [], []], [[], [], [], [], [], [[1, 15, 240, 3840, 4369, 8738, 20292, 34952, 61440]], [], [], [[4, 15, 240, 3840, 4369, 8738, 20292, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952, 61455, 65280]], [], [[15, 240, 3840, 4369, 7967, 8738, 17476, 34952, 61440]], [], [], [], [[15, 240, 255, 3840, 4369, 8738, 20292, 34952, 61440]], []], [[], [], [], [], [], [], [[15, 240, 3840, 4369, 8738, 8959, 17476, 34952, 61440]], [], [], [[15, 240, 3840, 4369, 8738, 17476, 43690, 63624]], [[15, 143, 240, 3840, 4369, 8738, 17476, 34952, 61440]], [], [], [[15, 240, 3840, 4369, 4593, 8946, 17476, 34952, 61440]], [], []], [[[15, 240, 3840, 4369, 4383, 8738, 17652, 34952, 61440]], [], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 17487, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61713, 65297], [15, 240, 3840, 4369, 8738, 17652, 34952, 63624]], [], [], [[1, 15, 240, 4369, 8738, 17476, 36744, 61440]], [], [], [], [[15, 240, 3840, 4369, 4593, 8738, 17476, 34952, 63624]], [], []], [[], [], [[4, 15, 240, 3840, 4369, 8738, 26214, 34952, 61440]], [], [], [], [], [], [], [], [[15, 240, 3840, 4095, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 7953, 8738, 17476, 63624]], [], [[1, 15, 240, 3840, 4369, 8738, 17652, 34952, 61440]], [], [], [[4, 15, 240, 3840, 4369, 8738, 17652, 34952, 61440], [15, 240, 3840, 3855, 4369, 8738, 17476, 34952, 61440]]], [[], [], [[15, 240, 3840, 4369, 4593, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 39321, 63624], [15, 240, 3840, 4369, 8738, 17652, 61440, 63624]], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61455, 63624]], [[4, 15, 3840, 4369, 8738, 17652, 34952, 61440]], [[15, 240, 255, 3840, 4369, 8738, 17652, 34952, 61440]], [[15, 240, 3840, 3855, 4369, 8738, 17476, 61440, 63624]], [[15, 240, 3840, 4369, 8738, 8946, 17476, 63624]], [], [[15, 240, 3840, 4369, 4593, 8738, 17476, 61440, 63624]], [], [], [], [], [], [[15, 240, 3840, 4369, 4593, 8751, 17476, 34952, 61440]]], [[[15, 240, 3840, 4369, 4383, 8738, 17476, 34952, 63624], [15, 240, 3840, 4369, 4607, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952, 61713, 63624]], [[15, 240, 3840, 4369, 8738, 20292, 36744, 61440]], [], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61455, 61680]], [], [[1, 15, 240, 4369, 8738, 20292, 34952, 61440]], [], [[15, 240, 3840, 4369, 8738, 17652, 34952, 61713]], [[4, 15, 240, 4369, 8738, 20292, 34952, 61440]], [], [], [[15, 240, 3840, 3855, 4369, 8738, 17476, 34952, 61713]], [], [], [[15, 240, 3840, 4369, 4593, 8738, 17476, 34952, 61713]], [[4, 15, 240, 3840, 4369, 8946, 17476, 34952, 61440]]], [[[15, 240, 3840, 4369, 8738, 17476, 34952, 61680, 61713]], [], [], [], [[4, 15, 3840, 4369, 8946, 17476, 34952, 61440]], [[15, 240, 3840, 4369, 4383, 8738, 17476, 34952, 61440]], [], [], [], [], [], [], [[1, 15, 240, 3840, 4369, 8738, 17476, 34952, 63624], [15, 240, 3840, 4369, 4383, 8738, 17476, 61440, 63624], [15, 240, 3840, 4369, 8738, 17476, 34952, 61713, 61937], [15, 240, 3840, 4369, 8738, 17476, 34952, 61713, 63897]], [], [], [[4, 15, 240, 3840, 4369, 8738, 17476, 34952, 63624]]], [[], [], [[15, 240, 255, 3840, 4369, 8959, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34959, 63624]], [], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61455, 61713]], [[15, 240, 255, 3840, 4369, 8738, 17476, 34952, 63624]], [], [], [], [[15, 240, 3840, 4369, 8738, 8751, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 63624, 63631], [15, 240, 3840, 4369, 8738, 17652, 63624]], [], [[12, 240, 3840, 4369, 8738, 17476, 34952, 52428, 61440]], [], [[4, 8, 240, 3840, 4369, 8738, 17476, 34952, 61440], [12, 240, 3840, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 3855, 4369, 8738, 17476, 63624]], [], []], [[[1, 240, 3840, 4383, 8738, 17476, 34952, 61440], [4, 240, 3840, 4369, 8738, 17487, 34952, 61440], [15, 240, 3840, 4369, 4593, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 34952, 61440]], [[1, 15, 240, 3840, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 4383, 8738, 17476, 34952, 61713], [15, 240, 3840, 4369, 8738, 17476, 34952, 61441]], [[1, 15, 240, 3840, 4369, 8738, 17476, 34952, 61441]], [[3, 15, 240, 3840, 4369, 8738, 17476, 34952, 61440]], [[4, 15, 240, 3840, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952, 61444]]]]
  | 9 => [[[], [], [], [], [], [[15, 240, 255, 3840, 4369, 8738, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61713]], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [[15, 240, 3840, 4369, 8738, 17476, 63624]], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[15, 240, 3840, 3855, 4369, 8738, 17476, 34952, 61440]]], [[], [], [[15, 240, 3840, 4369, 4593, 8738, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [[15, 240, 3840, 4369, 4383, 8738, 17476, 34952, 61440]], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[[15, 240, 3840, 4369, 8738, 17476, 34952, 61440]], [[1, 15, 240, 3840, 4369, 8738, 17476, 34952, 61440]], [], [], [[4, 15, 240, 3840, 4369, 8738, 17476, 34952, 61440]]]]
  | 10 => [[[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[[15, 240, 3840, 4369, 8738, 17476, 34952, 61440]], [], [], [], []]]
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
theorem lenOK : ∀ s, s ≤ 10 → (rowsOf s).length ≤ 245 := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem fast_in {s k : Nat} {l : List Nat} (hs : s ≤ 10) (h : l ∈ fastGet s k) :
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
  | 3 => [[[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [3], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [1]], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5]], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]]
  | 4 => [[[], [], [], [10], [6], [], [10], [], [], [], [], [7], [], [0], [1, 5], [], [], [], [], [0], [0, 1], [2], [6], [], [], [], [], [], [], [2], [], []], [[], [5], [], [2, 4], [], [1], [], [5], [], [], [2, 5], [], [], [], [], [], [2], [], [], [], [11], [0], [9], [], [], [], [], [], [], [1], [], [5]], [[], [], [10], [5], [9], [], [2], [10], [], [], [], [], [], [], [], [], [], [], [], [0, 9], [], [], [], [], [1], [10], [9, 10], [8, 10], [0], [5], [2], [2]], [[4], [9], [], [2, 10], [12], [], [], [], [0], [5, 9], [0], [], [0], [10], [], [], [], [6, 12], [1, 5], [], [9], [], [4], [], [], [14], [], [], [], [10], [], []], [[], [], [], [], [], [9], [], [], [], [0], [], [], [0], [], [], [], [], [0], [], [], [2, 12], [9], [], [], [], [], [], [0], [0], [5, 9], [0, 1], []], [[1, 2], [], [], [], [], [10], [2], [], [9], [], [], [0], [], [], [], [], [1], [], [10], [], [], [9], [0], [], [9], [9], [], [], [2], [4], [], []], [[], [4], [], [5], [14], [2, 12], [5], [5], [5], [], [], [], [14], [], [], [], [], [], [], [], [3], [], [], [2, 9], [0], [], [11], [], [5], [5], [], []], [[0, 10], [1], [], [8], [], [], [], [], [], [7], [0], [2], [0], [], [], [], [], [], [], [], [9], [], [3], [6], [1], [9], [], [], [9], [2], [9], [9]], [[5], [], [], [], [], [], [10], [], [], [], [], [], [], [], [], [14], [], [], [], [], [], [], [], [], [0], [], [], [], [], [6], [], []], [[], [], [], [5], [1], [], [2, 8], [], [2], [9], [], [5], [0], [], [], [6], [], [], [], [], [11], [], [0], [], [], [], [], [], [], [2], [14], []], [[], [0], [], [], [7], [2], [5], [0], [], [], [], [5], [5], [], [], [], [], [], [], [], [], [5], [], [], [0, 6], [10, 14], [3, 5], [], [], [], [1, 2, 5, 13], []], [[0, 3], [0], [], [], [6, 14], [], [], [], [], [], [5, 6], [], [], [0, 5], [], [0], [], [], [], [], [], [], [], [7], [], [], [], [], [], [], [4], []], [[], [0], [], [], [], [9], [], [], [], [1, 2], [], [], [2], [], [], [7, 9, 10, 12], [5], [0], [], [], [], [], [14], [], [10], [10], [], [], [12], [], [], []], [[2], [], [], [], [], [], [], [], [], [], [10], [], [0, 7], [], [], [], [0], [], [], [6, 10], [], [15], [], [], [], [], [11], [], [9], [], [2], []], [[0, 6], [5], [2, 5], [], [], [], [5], [], [0, 1], [], [], [], [], [], [], [2], [1], [2], [], [], [], [], [], [], [], [11], [], [5], [], [], [], [14]], [[2], [12], [9], [1], [], [], [9, 14], [], [], [], [], [], [11], [0, 9], [], [], [2], [], [], [], [0, 4, 5], [], [], [], [], [], [], [], [], [], [], [1]], [[], [12], [], [], [], [], [], [3, 7, 12], [2], [], [1], [], [], [0], [5], [5], [], [], [2], [], [], [], [2, 10], [], [], [], [], [], [], [0, 5], [], []], [[], [], [], [], [], [], [], [1], [0], [], [], [], [5], [], [], [5], [], [9], [12], [], [], [], [2, 5, 14], [], [], [], [9], [], [], [], [2, 6], []], [[], [0], [], [6], [0, 1], [], [], [], [], [], [5], [0], [8], [], [], [], [0], [0], [], [], [], [], [], [], [1], [], [], [], [0, 9], [], [], []], [[5], [], [], [5], [], [], [], [], [], [], [10], [], [], [0, 3], [], [2], [], [6], [], [], [2], [], [], [9, 13], [], [], [], [], [], [3], [], []], [[], [2], [], [], [], [9], [], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], [], [2], [0], [], [1], [], [], []], [[4], [9], [], [], [9], [], [], [], [], [], [8], [], [], [10], [0], [4], [7], [], [], [], [9, 14], [3, 5], [9], [], [5, 10], [0], [], [2, 7], [4], [14], [], [1]], [[], [], [12], [], [0], [2], [], [], [], [], [], [2], [0, 7], [0, 3], [0], [11], [], [0], [11], [], [], [8], [11], [], [3, 9], [], [], [2, 3], [5], [], [1, 14], [7]], [[], [0], [9], [6], [0], [], [], [], [], [], [], [], [], [], [], [], [0], [13], [], [], [5], [], [], [14], [], [], [], [], [], [10, 15], [2, 6], []], [[1], [], [], [], [], [], [], [6], [7], [], [], [], [8], [], [], [], [], [2], [], [0], [], [10], [], [0], [5], [9], [1], [], [], [], [9], [7]], [[9], [], [10], [], [6], [], [0], [], [7, 11], [7], [], [], [6], [0, 6], [], [], [9], [5], [0], [], [], [], [], [], [], [], [9], [3], [], [], [2], [2]], [[12], [], [15], [], [], [], [0], [1], [], [], [4], [], [], [11], [], [6], [], [], [], [10], [], [], [], [], [], [0], [0], [2], [5], [], [2, 6, 10], []], [[], [], [], [], [0, 4], [], [], [0], [], [], [0], [], [0], [11], [], [0, 2, 4], [0, 1], [], [], [6], [], [5], [], [], [], [6], [2], [10], [], [], [], []], [[2], [], [], [], [], [0], [], [], [], [], [], [], [9], [], [], [9], [], [], [0], [], [], [0], [], [5], [10], [], [1], [], [], [3], [0], [5]], [[], [], [5], [], [2], [], [], [12], [0], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], [15], [], [], [9], [], [], [14], []], [[10], [], [], [], [0], [7], [], [5], [12], [3], [1], [6], [], [], [], [1], [1, 7], [], [], [5], [], [], [], [], [0], [], [], [], [], [], [], []], [[], [], [6, 7, 9], [], [14], [], [], [], [], [10], [2], [], [5], [0], [], [], [], [], [0, 6], [10], [9], [0, 4], [4], [], [], [], [], [], []]]
  | 5 => [[[0], [], [2], [0, 6, 11], [2, 11], [0, 11], [0, 2, 7], [1], [0, 1, 7, 10, 15], [6, 10], [0, 2], [0, 7, 12], [9], [], [], [2, 4, 5, 10], [5, 10, 15], [3, 7], [0, 5], [2, 6], [0, 5, 8, 11, 12], [2, 9], [0, 2], [2, 14, 15], [1], [0], [0], [1, 4, 6, 8, 9, 15], [15], [6, 10], [0, 3, 15], [0, 5]], [[15], [0], [9], [5], [0], [9, 11], [0, 5, 12], [0, 6, 15], [9], [10, 11], [2, 3, 4, 5, 10], [0, 5, 8], [0, 6, 11], [2, 8], [4, 6], [], [5, 9], [0, 6], [0, 11], [0], [], [5, 8], [0, 2, 4, 9, 10, 11], [0], [0, 3, 9, 15], [0, 1, 10], [0, 2, 8, 10], [2, 5, 6, 8], [0, 10], [6], [], [15]], [[2, 5, 8], [0, 1], [4, 8], [], [10], [3, 6], [0, 10], [0, 6, 12], [0, 5, 10], [5, 9], [0, 5, 10], [0], [2, 15], [], [5, 8, 9], [0, 4, 6], [3, 12], [3], [0], [6], [5], [4, 6, 8], [], [0, 2, 10], [6, 12], [5], [5, 9, 11], [2, 5, 10, 11], [0, 4], [10], [0, 13], [2]], [[0, 3], [4], [0, 4, 15], [12], [2, 11], [1, 10], [9], [6], [8], [0, 1], [4, 5], [0, 2], [], [5], [2, 8], [7], [2, 8, 11], [8, 9, 11, 12], [0, 10], [0, 1], [0, 3], [2, 10, 14], [0, 2, 3, 12], [5], [0, 3, 12], [6, 9], [0, 2, 9], [3, 9], [3], [5], [0, 5, 9], [5, 10]], [[6, 9], [2, 15], [0, 1], [0, 4], [2, 9, 10], [], [4, 5], [1, 7, 9], [11], [2, 3], [0, 3, 10], [10], [2, 4, 5, 9], [4, 6, 7, 10], [0, 10], [0, 5, 9], [1, 2, 4, 10], [0], [0, 2, 5, 6, 11], [0, 2, 4, 8], [2, 5, 10], [9, 10], [0, 10], [], [5, 7], [0, 8], [0], [1, 3, 9], [0, 5, 14], [1], [0], [6]], [[0, 5], [0], [], [0, 10], [], [2, 6, 15], [2], [0, 1], [1, 6], [3], [3, 8], [0, 1, 2], [0, 2], [], [0, 7, 15], [0, 6], [0, 5, 11], [1], [5, 10], [6, 10, 13], [2, 6], [], [0], [2, 6, 10], [5, 10], [2], [9, 10, 15], [0], [11], [2], [1], [4, 9]], [[12], [6], [0, 10], [0, 5, 14, 15], [14], [0, 5], [0, 3, 12], [2, 7], [2, 5], [5, 12, 14], [], [3], [5], [2, 15], [0, 2], [0], [0, 2, 6], [0, 10], [1, 2, 12], [2, 4, 6], [3, 8, 12], [0], [1, 2, 9, 10], [0, 4, 9], [4, 5, 10], [4, 8], [0], [5], [2, 6, 8], [5, 13], [], [0]], [[2, 3, 8], [0, 1], [5], [2, 3], [0, 5, 6], [], [0, 1], [0, 5, 6, 11, 14], [], [3], [2, 10], [], [2, 4], [0, 5, 10], [0], [6], [2, 6], [0], [1, 12], [3, 9, 10], [3, 6, 8, 10], [], [1, 8], [0, 4, 5, 10, 15], [2], [], [4, 10], [0, 5, 10], [0, 2], [0, 1, 6, 11, 15], [12], [1, 2]], [[0], [], [2], [0, 12], [1, 10, 12], [2, 5, 8], [15], [0], [14], [2, 11, 14], [], [6, 10], [0, 5, 8], [0, 1, 9, 14], [5, 6], [0], [2], [4, 13], [6, 10, 14], [0, 6, 10], [], [5], [6, 15], [3, 7], [2, 4, 7, 8], [], [8], [0, 2], [11], [0, 5, 6, 8], [14], [6, 10]], [[], [1], [3], [5, 10], [0, 2, 10], [0, 1, 9, 15], [0, 4, 5], [5, 7], [], [5], [10], [0, 8], [0, 2], [12], [], [0], [6], [0, 4, 5], [0, 5, 10], [1, 3], [5, 8, 9], [0], [0, 2, 9], [4, 9], [6], [7, 10], [0, 2, 6, 12], [2, 3], [0, 3, 10], [0, 8, 10], [0, 6], [0, 1, 2]], [[2], [0, 1, 5, 9], [0, 1], [0, 6, 10], [10], [9], [3, 5], [1, 6], [5], [0, 1, 9, 10], [8, 10, 14], [2, 4, 5], [9], [0, 3, 6, 9], [11], [0, 2], [], [0, 4, 9], [0, 5, 10], [2, 5, 6, 14], [3, 6, 10], [1], [0, 2, 5], [0, 7], [0, 1, 2], [0], [0, 2], [4, 14], [6, 9, 11], [0], [0, 1], [3, 7]], [[0, 6], [4, 13], [], [0, 8], [2, 10, 11], [0, 2], [5, 14], [2, 3, 6, 7], [0, 5, 6], [1, 2], [5, 6, 12], [4, 10], [13], [1, 2, 13], [0, 1], [1], [0, 2, 5], [4], [0, 4, 6, 15], [2, 10], [12], [9, 12], [2, 4], [0, 3], [0, 7, 10], [0, 6], [0, 10], [2, 9], [2, 7], [1], [0, 5], [4, 8]], [[3, 6, 15], [10, 15], [4, 6, 10, 14], [0], [0, 7, 14], [0], [4], [0, 9, 10], [4, 6], [3], [5, 9], [6, 10], [2, 10, 13], [3, 6], [0, 5], [0], [0, 8], [0, 2, 4, 6, 9, 10], [9], [1, 2, 3, 12], [8, 9, 11], [0, 1], [], [2, 13, 14], [3, 6, 10], [2, 10], [0, 2, 5, 11, 12], [0, 3, 5], [0, 6], [1], [0], [0, 13]], [[4], [0], [], [0, 1], [8], [], [0, 2], [0], [0], [0, 3, 5, 11], [6, 8, 9, 15], [10, 14], [0, 9], [6, 7, 8], [1, 5, 8], [2, 6], [4, 11], [6, 7, 10], [2, 3], [0, 1, 2, 3, 6], [1], [0, 8], [0, 8], [7, 12], [6], [0, 10], [2, 12], [1, 12], [0], [0, 6], [0, 8, 9, 10], [5, 6]], [[1, 9], [6], [2, 7, 10], [5, 13], [0, 10], [0], [2, 10], [1, 5, 10], [9], [], [3, 10, 15], [1], [0, 2, 5, 8], [2], [3, 6, 10, 15], [1, 2], [0, 4, 5], [0, 1, 5, 8, 14], [0, 5, 10], [11, 13, 15], [5, 11, 12], [5, 10], [9], [0], [2, 6, 10], [2, 6, 9, 10], [3, 4, 8], [2], [5, 13], [0, 2, 10], [0, 2, 5, 10, 12], [0, 14]], [[0, 6], [6, 10, 11], [5, 8, 9], [8], [9, 13], [2, 10], [3, 4, 5, 8], [0, 5, 9], [], [2, 9, 11], [8], [], [6], [1, 10], [0], [1, 5], [4, 9], [0], [0, 6], [], [0], [], [2, 8, 10], [1, 5, 12, 14], [], [12], [4, 10], [3, 6, 10], [0, 1], [0, 10], [1, 3, 5, 11], [0]], [[0, 5], [0, 1, 4, 5], [5, 6, 13], [0, 2, 4, 5, 10], [0, 2, 5], [0, 5, 10], [1], [2], [5, 11], [14], [0, 4, 14], [15], [12], [0, 1, 2, 4, 5, 14], [5, 9, 10], [1], [11], [0, 1, 3, 15], [], [0, 2, 5], [1, 11], [0, 5, 6, 8, 15], [4], [0, 2], [5], [2, 5, 10, 13], [2, 14], [0, 10], [0, 11], [], [2, 12], [5, 14]], [[0], [1, 6], [], [0, 1, 3, 10], [0, 3], [0, 3], [10], [1, 2, 9, 13], [0], [4], [8, 9], [0, 2, 5], [0, 12], [3], [8, 9], [15], [9, 12], [0], [0], [0, 2, 12], [0, 15], [1, 9], [0, 3], [1, 3], [3, 14], [0, 1, 2], [3, 9, 11], [0, 5, 6, 10], [2, 10], [2, 6, 12], [0, 5, 8], [0, 5]], [[14], [6, 9, 10, 11], [0], [4, 5], [4, 11], [0, 1, 6, 8, 15], [0, 4], [8], [2, 12, 15], [0, 9, 10], [0, 4, 6], [0, 5, 10], [2, 4, 6], [4], [6], [10], [0, 2], [0, 2, 5, 8, 15], [9], [4, 6, 14], [7, 14], [4], [0, 2, 3, 6], [0, 2, 13], [5, 6, 14], [0, 5, 12], [3, 8], [3, 9, 15], [], [], [0, 2, 11, 14], [0, 9]], [[], [0, 1, 3, 4, 9], [], [], [0], [0, 5], [4, 6], [2], [14], [0, 2, 11], [3, 4, 9], [6, 10], [7, 9], [1, 2, 10, 12], [7], [0, 4, 6, 14], [1, 6], [6, 10], [], [2, 10], [1, 4, 9, 11], [1, 9], [], [7], [4], [3], [2, 13], [], [7, 10], [0], [10], [6]], [[0, 14], [0, 1, 2, 5, 10], [12], [0, 9], [0, 2, 14], [3, 10, 12], [6], [9, 10], [], [1, 2, 8, 9, 10, 12], [2, 14], [0, 2, 5, 11], [0, 5, 9], [2], [1, 3, 15], [2, 3, 10, 11], [2], [0, 4], [], [2, 9, 10], [0, 2, 6, 8, 11], [0, 3], [0, 1, 5, 13], [0, 3, 7, 8, 12], [], [0, 7, 10], [0, 6, 10], [8], [0, 1, 5, 6], [9], [], [6]], [[5, 6, 7, 8], [4, 8], [0, 10], [4, 5], [0, 1, 2, 4], [2, 9, 10], [0], [0], [], [0, 2, 3, 6], [0], [10, 14], [2, 8], [10], [0], [0, 1], [5, 15], [4], [8, 12], [9], [0], [1, 6, 12], [4], [1, 5, 9], [0, 1, 5], [12], [2], [0, 3, 6, 12], [0, 2, 15], [14], [5, 6, 7], [0, 6]], [[2, 5], [6, 10, 15], [0, 5, 11], [0, 9], [0, 1, 5, 8, 10], [0], [7, 10], [0, 2], [1, 5, 12], [6], [3, 5, 10], [0], [0, 5, 6, 10], [9, 10], [2, 9, 11], [7], [0, 11], [], [0, 2, 4], [0], [4, 5, 6], [5, 8, 10, 11, 12], [2, 4, 11, 13], [0, 5, 7], [4, 6, 9, 11], [2, 5, 9], [0, 6], [7, 8], [2], [], [2, 5], [1]], [[2, 6, 10, 11], [1, 2, 5, 6], [0, 8, 9, 11], [], [], [4, 7], [2, 3, 5, 8], [], [0, 2], [0, 2], [6], [], [0, 2, 4, 6, 10, 12], [2, 4], [2, 12], [0, 6], [1, 5, 12], [10], [13], [2, 5, 9], [1, 6], [1, 7, 10], [1, 8, 10], [], [1, 4, 5, 10], [0, 5, 6, 11], [0, 2, 10], [1, 3, 10], [0, 2, 10], [15], [5, 9], [12]], [[0, 3, 6], [8], [2], [], [5, 9, 10], [1, 8, 10], [5], [2, 3, 5, 11], [0, 5, 10], [2, 3, 9], [5], [2, 5], [], [0], [], [1, 5], [], [2, 11], [0], [0, 1, 4, 5], [1, 4, 6, 7, 8], [0, 5], [10, 11, 14], [0, 2, 9, 11], [4, 9, 15], [12, 14], [2, 5], [0, 5, 12], [2, 11, 13], [0], [0, 10, 11], [2, 6, 8, 9]], [[1, 2, 6], [5, 10], [], [3, 6, 10], [0, 6], [0], [7], [], [0, 12], [9], [0, 9], [], [], [0, 2, 11], [2], [0, 5, 14], [0, 7, 9, 10, 12], [2], [0, 2, 3], [6, 9], [6, 8], [0, 9], [], [4, 10, 14], [0, 7], [4, 6], [12], [0], [0, 12], [6, 10], [0, 3, 12], [2]], [[0, 4, 5, 7, 10], [12], [15], [0, 14], [0, 10], [0, 10, 12], [0, 14], [9, 10, 11], [9], [9, 11], [2], [5, 9, 12, 13], [0, 6, 9, 10, 15], [0, 10, 11], [0, 9], [], [0, 2, 9], [0, 10], [9, 14], [5, 12], [2], [1], [], [0], [3], [1, 5, 7], [2], [4], [0, 9], [0, 2, 7, 11], [0, 5], [3, 5, 7, 11]], [[], [1, 7, 13], [1, 2, 6, 9], [0, 2, 10], [10], [2, 6, 10, 12], [11], [0, 12, 14], [10, 14], [5], [5, 6, 12], [0, 4, 10], [0, 4, 12], [5], [2], [6], [0, 10], [1], [2], [0, 5, 7, 10], [0], [0, 1, 2, 7], [4, 8, 11], [0, 3], [1, 2, 3, 14], [0, 4, 9], [0, 10, 11], [0, 10, 12], [1, 5, 8], [0, 8], [4], []], [[2, 6, 7, 9], [0, 1, 8], [0, 9, 12], [0, 2, 4, 7, 10], [12], [2, 9], [0, 7], [6, 9], [14], [9], [5, 9], [0, 10], [0, 5, 6], [6], [0, 6, 11], [0, 4, 5, 10], [6, 10], [0, 1, 5, 10], [9], [0, 5], [2, 10, 11], [3, 4], [13], [11], [0, 5], [5, 10], [0], [0, 1, 3, 11], [0, 14], [10], [0], [0, 8]], [[], [1, 6, 12], [7], [2], [2, 8, 9], [2, 6, 9], [0, 4, 6], [0, 5], [0], [1, 10, 15], [0, 5, 7], [4, 7], [2, 9], [0, 9], [1, 5, 10, 12], [0, 5, 6, 8, 9], [0, 8], [0, 3, 5], [], [0, 2], [2], [10], [0, 2, 9, 10], [0, 2, 5, 9], [0, 8, 10, 12], [1, 10, 11], [5, 9, 11], [0, 2, 10], [0, 5, 15], [3, 6, 9], [1], [1, 6]], [[10, 14], [1, 3, 12], [0, 1], [10, 11, 12], [3], [0, 1, 12], [0, 2, 9], [], [0, 3, 8, 15], [0, 5, 10], [0, 10], [0, 10], [11], [0, 8, 9], [], [0, 2, 4, 12, 15], [0], [0, 2, 5, 14], [0, 4, 9, 15], [], [], [], [0, 10], [0, 2, 9], [0], [9], [0, 9], [], [0, 1, 2, 4, 15], [0, 5], [], [1]], [[], [], [0, 1, 2, 5, 12], [2, 5, 7], [14], [0, 3, 4], [0, 1], [3, 5, 6, 10], [12], [10], [], [6], [0, 1, 14], [0, 1, 7], [10], [4, 6, 8, 11], [6], [5], [2, 4], [4, 10], [5, 11], [0, 5, 10], [], [10, 14], [1], [0, 1, 5, 9, 12], [0, 6], [10, 11], [7]]]
  | 6 => [[[0, 2, 5], [2, 10, 11, 13], [0, 1, 2, 3, 9], [0, 1, 5, 9], [6, 8, 11], [2, 3, 4, 11], [0, 2, 11], [1, 2, 6, 11], [1, 2, 5, 10, 12], [5, 6, 8], [6, 15], [0, 8, 9], [0], [1, 5], [0, 2, 4, 8], [1, 4, 6, 7, 14], [0, 10], [0, 3], [6], [2, 6], [1], [0, 1, 4, 7, 10, 12], [12], [0], [0, 1, 3, 5, 6], [0, 4, 6], [2, 8, 13], [6, 10, 11, 15], [0, 6, 13], [1, 4, 6, 10, 11], [0, 15], [0, 2, 8]], [[0, 2], [0, 1, 4, 10], [3, 5], [0, 4, 5, 6, 8], [0, 8, 12, 15], [0, 4, 5, 8, 12], [8, 13], [3, 5, 14], [0, 4, 10], [0, 1, 10], [3, 6, 10], [6, 8], [0, 3, 6, 8], [0, 2, 5, 7, 8, 10, 12], [0, 4, 15], [0, 1, 8, 10], [], [1, 10, 12, 13], [3, 5, 8], [8, 9], [8, 9, 11], [0, 3, 6, 8, 9, 15], [0, 4, 10], [0, 5, 8], [0], [0, 2, 8, 10, 15], [4, 8], [0, 1, 3, 5, 6, 12, 15], [4, 11], [0, 1, 6, 8, 10], [0, 3, 5, 8, 9], [10]], [[14, 15], [5], [0, 6, 10], [2, 3, 8, 13], [1, 3, 8], [0, 6], [0, 1, 5, 12], [0, 7], [0, 4, 5], [0, 1, 12, 13], [0, 1, 2, 5], [6], [4, 5], [0, 12], [5, 6, 12, 15], [0, 2, 12], [2, 8], [6], [1, 2, 8], [5, 6], [5, 11, 12], [4, 5], [0], [0, 1, 10], [1, 2, 15], [0, 4, 8], [0, 3, 11], [0, 10, 11], [0, 4, 5], [0, 1, 10, 15], [2, 13], [4, 6, 9]], [[0, 10], [0, 3, 12], [2], [0, 5], [2, 8, 12], [0, 6, 9], [0, 1, 5, 6], [0, 4, 6, 13], [0, 2, 6, 9, 13], [0, 1, 3, 5], [2, 3], [0, 4, 5, 11], [0, 4, 7], [1, 4, 5], [8, 11], [0, 3, 5, 12], [1, 4, 6, 9, 12], [3, 6, 10], [1, 2, 3, 8, 11], [0, 1, 2, 4], [0, 1, 2, 4, 5, 10, 12], [0, 1, 4, 5], [0, 12], [0, 4, 5, 9], [0, 2, 6, 7, 9], [0, 1, 7], [3, 8, 10, 12], [0, 5, 8, 13], [9], [0, 1, 5, 6], [1, 5, 11, 12], [0, 8]], [[0, 6], [0, 3, 15], [0, 2, 6], [0, 1], [3, 10], [0, 4, 8], [8, 10], [1, 8, 9, 10], [0, 5], [0, 5], [0, 5, 14, 15], [0, 1, 2], [0, 5, 8], [2, 7, 9, 10, 14], [0, 6, 10], [0, 3], [4, 8, 10], [1, 2, 4, 13], [0, 2], [2, 5, 10, 13], [0, 1, 2, 5, 7, 8], [0, 8, 10], [3, 10], [0, 6, 15], [0, 3, 8, 13, 15], [4, 5], [0, 3], [0, 5, 6, 13], [0, 8, 10, 11], [0, 3, 7, 10], [4, 8], [0, 1, 10, 13, 15]], [[0, 1, 4, 14, 15], [0, 4, 10], [0, 9, 10], [2, 3, 6], [0, 4, 6, 8, 10], [0, 8, 10], [0, 4, 10], [0, 5, 11], [0, 6], [0, 3, 6], [0], [0, 4, 9, 11], [0, 10], [0, 4, 7], [0, 2, 3, 6, 10, 12], [0, 6, 8, 10, 15], [1, 5, 10], [0], [], [2, 4], [1, 6, 9], [11, 12], [0, 5, 10], [0], [3, 4, 8, 11, 15], [0, 10], [2], [2, 6], [], [1, 2], [0, 3, 4, 8, 11], [1, 8, 9, 12]], [[0, 11, 15], [0, 10, 13], [10], [0, 2, 5, 10, 12], [0, 3, 6, 10], [13], [0, 2, 3, 4, 10, 12], [0, 6, 11], [5], [6], [4], [], [0, 2, 3], [0, 1, 11], [0, 2, 6, 10], [0, 2, 5], [0, 4, 6, 10], [0, 6, 15], [12], [0, 6], [12], [0, 4, 5, 8, 9], [0, 10], [4], [0, 2, 4, 6, 10], [1, 6], [0], [], [0, 6], [3, 6], [9], [1, 3, 8, 13, 15]], [[0, 15], [1, 8, 12], [5, 6, 15], [0, 3], [], [0, 11], [0, 15], [0, 9], [0], [0, 7, 10, 15], [10, 13], [8, 10], [2, 4, 5], [6, 10], [0, 2, 5], [], [0, 12], [0, 1, 4, 8], [10, 11], [0, 1, 5], [0, 6, 14], [0, 1, 7, 11, 15], [2, 8, 10], [0, 2], [2, 5], [1, 8, 10, 13, 15], [0, 1, 10], [5], [0, 8], [0, 13], [0, 2, 8], [0, 1, 4, 9, 12]], [[3, 6], [0, 5, 8, 9, 10, 11], [0, 5, 9], [0, 6], [0, 2, 5, 10, 11], [0, 1, 3, 14], [0, 3, 5, 6, 7], [0, 1], [0, 6, 12], [0, 3], [0, 5, 6, 10], [6, 7, 10, 13], [0, 4], [0, 3, 14], [], [0, 2, 10], [], [0, 2], [0, 4, 14], [0, 3, 5, 6, 9, 10], [0], [], [0, 6, 8, 9], [4, 5], [2, 4, 6, 10, 15], [10], [1, 2], [0, 5, 6, 14], [3, 10, 15], [0, 4, 5, 10], [0, 1, 6], [4, 11, 12]], [[0, 15], [0, 2, 9, 11], [0, 2, 3], [0, 8], [0, 9], [0, 3, 10, 15], [0, 1, 10], [2, 13], [8, 10], [0, 3, 5, 11], [8, 9], [8], [0, 6], [0, 3], [0, 2, 6, 8, 10], [0, 5], [0, 2, 6, 12], [0, 6, 7, 10], [0, 1, 4, 5, 8], [0], [2, 4, 5, 8, 9, 13], [0, 2, 4, 8], [0, 6, 11], [4, 9, 10], [0, 2, 5], [0, 10], [4, 5], [0, 10, 15], [2, 3, 4, 10], [0, 1, 2, 8, 10], [], [2, 4]], [[5, 11], [0, 12, 13], [1, 5, 11], [2], [3, 9], [4, 10], [4, 6, 13], [0, 1, 11], [0, 6], [0, 4], [0], [0, 8, 11, 15], [5, 10], [2, 3, 12], [0], [3, 10, 12, 15], [0, 2, 3, 4, 6], [5, 6, 7, 9, 10], [0, 8, 10, 12], [2], [0, 2], [0, 10, 13], [0, 2, 5, 8, 10, 13], [0, 10], [1, 2], [0, 4, 9], [2, 5, 9], [13], [1, 2, 6, 10, 12], [0, 5, 6], [0, 3, 6], [0, 5, 7, 9]], [[2, 4, 6, 7, 15], [2, 4, 13], [0, 8, 12], [0, 2, 4, 6, 15], [3, 6, 10], [0], [0, 7, 8, 14], [0, 1, 8, 10], [2, 4, 5, 8], [1, 4, 7, 8], [0, 1, 3, 8, 9, 10], [2, 6, 11], [0, 1, 5, 8, 9], [0, 1, 3, 10, 13], [0, 1, 2, 5, 6, 7], [0, 1, 9, 10, 11, 12], [5], [0, 1, 5, 7, 8], [2], [3, 9], [4, 12], [0, 8, 10], [0, 5, 8, 9], [2], [0, 5, 6, 10], [0, 1, 8, 10], [0, 2, 4, 10], [0, 3, 8, 15], [0, 2, 5, 8, 10], [4], [], [1, 4, 5, 7]], [[0, 1, 9, 14, 15], [0, 4, 6, 10], [0, 1, 4, 10], [6, 9, 15], [3, 5, 10], [0, 5], [0, 1, 2, 5, 6, 8, 10, 13], [0, 1, 2, 6], [0, 4, 8], [0, 6, 15], [3, 15], [5, 12], [5, 11, 12], [0, 4, 5, 8, 10], [8, 9], [4, 7, 10], [0, 6, 10], [0, 5, 12], [0, 6, 8, 14], [0, 10], [0, 6, 9], [6, 10], [1, 3, 11, 15], [10, 11], [5, 10], [6, 11], [0, 4, 5], [0, 7, 11], [0, 4, 9, 14], [2, 6, 10, 12], [5, 9], [12]], [[2, 4, 8, 12], [1, 2, 3, 9], [4], [0, 2], [12], [0, 10], [12, 15], [0, 8, 9, 14], [0, 4, 5], [0], [0, 5, 10], [0, 2, 4], [0, 1, 9], [6, 10, 11, 15], [0, 1, 5], [0, 2, 6, 12], [0, 12], [], [4, 13], [0, 2], [1, 2], [4, 5, 8, 10], [0, 1, 5, 6, 9, 10, 12], [5, 6, 8, 11], [1, 8], [1, 2, 4, 10, 12], [12], [0, 5, 8], [5, 8], [8, 10, 13], [0, 8, 10], [0, 5, 6]], [[6, 8], [0, 1, 2, 6], [0, 2, 5], [8, 10], [5, 9], [0, 3, 4, 15], [0, 1, 3, 7, 8], [1, 8, 9], [0, 2, 15], [5, 7, 8], [3], [1, 4, 7], [0], [0], [0, 1, 2, 4, 10], [1, 2], [0, 3, 4, 6, 7, 9], [0, 7, 13], [0, 2, 5, 10], [0, 4, 8, 9, 11], [0, 6], [0, 4, 5, 10, 12, 13], [0, 2, 9], [0, 1, 2, 5, 8], [], [0, 10], [4, 11], [0, 2, 6, 8, 14], [0, 8], [0, 2, 10], [0, 2, 5], [0, 5, 10]], [[0, 1, 8], [0, 2, 6, 10, 15], [2, 11, 14], [3, 5], [0, 2], [2, 6, 10], [0, 2, 5, 8], [4, 10, 12], [], [0, 8, 10, 13], [0, 8, 9], [0, 4, 8, 14], [0, 2, 9, 10], [0, 6, 9, 10, 11, 12], [0], [0, 5], [0], [0, 4, 10, 14], [0, 1, 6], [5, 8, 13], [0, 2, 12], [0, 4], [2, 5, 6, 14], [0, 1, 5, 7, 11], [], [0, 1, 2, 5, 11], [8], [3, 10], [0, 10, 12], [0, 8, 10], [3, 4, 12, 14], [0, 4, 13]], [[0, 1, 3], [11], [4, 6, 10, 11], [2], [0, 4, 5, 11, 12], [0, 7], [0, 6, 13], [0, 5, 6, 10], [0, 2, 12], [13], [10], [4], [0, 1, 4, 6], [0, 8], [5], [1], [0, 6], [0, 5], [0, 3, 4, 9, 11], [4, 9], [5, 10, 11], [4, 5, 8, 11], [0, 4, 10, 12], [2, 5, 7, 12], [0, 1, 5, 8], [4, 7], [0, 4, 6], [5, 9, 10, 12], [5, 10], [1, 8, 15], [0, 1, 10], [0, 1, 8]], [[0, 1, 2], [2, 11], [0, 10], [2, 5, 8], [0, 3, 6, 8], [2, 7], [1, 2, 3, 6, 10, 11, 15], [0, 1, 10, 12], [1, 2, 6], [0, 5, 8, 10, 15], [0, 1, 6, 12], [4], [0, 13], [0, 3, 8, 10], [0, 5, 10], [9, 11, 15], [2, 3, 9, 10], [2, 5, 8, 9], [4], [4, 6, 12], [2], [1, 5, 6, 8], [0, 1, 2, 8], [0, 3, 6, 10, 15], [0, 1, 3, 8], [0, 8, 11], [0, 9, 11], [0, 4, 5, 8, 10, 11], [4, 5, 9, 10], [0, 12], [1, 2, 8], [0, 4, 5]], [[0, 4, 6], [5, 9, 10], [0, 9], [6, 9, 11], [0, 10, 12, 15], [0, 5, 10, 11], [0, 4, 10, 12], [0, 4, 5, 11, 14, 15], [4, 8, 12, 15], [1, 8, 12, 15], [0, 1, 6], [0, 6, 8], [], [0, 3, 8, 10], [4, 5, 6, 12], [5], [0, 2], [0, 2, 5, 8, 10, 12], [1, 3, 8, 11], [0, 10, 11, 15], [1, 3, 4, 7, 11], [0, 8, 9], [0, 2, 3, 6, 11], [], [0, 2, 3], [5, 6, 10], [4, 7], [9, 10], [0, 2], [0, 2, 4, 9, 12], [4], [0]], [[0, 8], [1, 4, 5, 15], [3, 10, 13], [0, 3, 6, 7, 8], [0, 3, 8, 9], [0, 5, 6], [1, 8], [0], [1, 6], [3, 5, 12, 14], [0, 1, 3, 5], [0, 1], [2, 4], [0, 8, 10], [0, 1], [0, 1, 6], [0, 2, 9], [0, 3, 15], [1, 8, 13], [1, 8, 15], [0, 10], [4, 5, 6, 8, 11, 15], [0, 9, 10], [0, 6, 8], [0, 4], [0, 5, 8, 11], [0, 8], [0, 1, 4], [0, 1, 10], [0, 1, 6, 8, 9], [0, 1, 6, 10, 12, 15], [0, 10, 13]], [[0, 9, 14], [7, 8, 9], [10, 12], [0], [2, 8, 12], [2, 4, 9], [6, 10], [3, 6, 7], [0, 2, 6, 9, 11], [0, 6, 8, 9, 11, 15], [0, 10], [0, 4, 5, 8, 11], [0, 4], [2, 11], [0, 6], [0, 6, 11], [12], [0, 1, 11, 12], [0, 1, 2, 4, 8, 11], [2, 3, 10], [0, 5, 6], [0], [4, 5, 9, 14], [11, 14], [0, 2, 12], [6, 9], [5, 12], [0], [5], [0, 10], [5, 10], [0, 1, 2, 4, 5, 14]], [[0, 6, 8], [0, 1, 2], [2, 4, 9, 12], [0, 5, 6, 12], [4, 9, 13], [0, 3, 7, 11], [0, 4, 5, 8], [1, 6, 7, 10, 15], [15], [0, 2, 4, 7], [0, 2, 8], [0, 12], [7], [0, 1, 2, 3, 5], [2, 4, 14], [0, 1, 3, 4, 10], [1, 5, 9], [0, 1, 4, 6, 8, 9, 12, 15], [14], [3, 4, 6, 12], [0, 5, 7, 9], [0, 1, 2, 6, 9, 10], [0, 2, 4, 5, 9], [0, 2, 8, 12], [3, 8, 9, 10], [5, 6], [0, 1, 4, 9, 10], [0, 3, 5], [5, 10], [0], [0, 7, 13], [3]], [[0, 8, 11], [5, 6, 9, 11], [6, 10, 11, 15], [0, 4, 6, 15], [2, 10, 11], [], [0], [0, 6, 12], [5], [0, 2, 7], [], [2, 4, 6], [0, 2, 5, 6, 7, 10], [4, 5, 6, 9, 10], [0, 4, 9, 14, 15], [0, 5, 9], [0, 1, 8], [5, 6, 10], [0, 4, 5, 6, 8, 12], [0, 1], [4, 9, 11], [0, 4, 10, 11], [2, 4], [0, 5], [0, 3, 5, 6, 10], [0, 4, 10], [0, 6], [0, 4, 9], [0, 10], [4, 5, 6, 12], [0, 4, 6, 9, 10, 12], [0, 1, 10, 14]], [[8, 10], [0, 5, 8, 10], [0, 4, 10, 11], [0, 1, 3, 9], [0, 6], [0, 4, 11], [6, 14], [0, 5], [5, 7, 10, 15], [0], [0, 1, 15], [0, 1, 10], [2, 5, 6], [0, 1], [0, 10, 12, 15], [2, 4, 8], [1], [0], [0, 6, 8, 12], [8, 15], [6, 10], [0, 2, 4, 10], [0, 5, 7, 10], [0, 6, 7], [2, 4, 5, 8], [1, 4], [11, 12], [0, 10], [0, 1, 2], [9, 10], [2, 4, 5, 9], [0, 2, 8, 12]], [[5], [0], [0, 4, 5, 6], [0, 3, 5, 6, 8, 14], [0, 6, 10], [0, 1, 5, 9], [0], [0, 2, 5, 6, 8], [12], [0, 11, 13], [2, 10], [0], [10, 12], [0, 9], [0, 6, 10], [2, 4, 9], [4], [0, 12, 14], [2], [0, 6, 8, 10], [0, 5, 6, 8, 11], [0, 6], [2, 4, 6, 8], [0, 1, 6, 11, 12], [0, 2, 4, 6, 9, 11], [0, 9, 12], [0, 4, 5, 8], [0, 1, 5, 9], [6, 9], [8, 10], [0, 3], [0, 6, 8, 9, 13]], [[5, 8, 10], [0, 15], [0, 6], [0, 3, 4, 5, 10, 13], [0], [], [2, 3, 4, 10], [1, 6, 7, 9], [0, 10], [7, 9, 15], [4, 5, 9, 10, 14], [1], [1, 8, 9], [0, 15], [4], [2, 3, 4, 12], [0, 4], [12], [0, 1, 3], [0, 3, 4], [0, 2], [0, 1, 2], [0], [0, 4, 5, 10], [7, 10], [4, 8, 10, 13], [0, 7, 8], [], [1, 8, 10, 14, 15], [15], [5, 10], [1, 3, 9, 14]], [[4, 5, 7, 12], [0, 9], [], [0, 2, 4, 5, 8], [2, 3, 8, 12], [0, 2, 5, 11, 12], [0, 1, 10, 14], [], [0, 1], [0, 1, 2, 5, 8], [5, 8, 13, 14], [3, 5, 6, 8, 10, 11, 12], [0, 14], [0, 5], [0, 4, 9, 10], [0, 1, 2, 9], [0], [0, 8, 9], [5, 6, 12], [2, 4, 10], [5, 11], [3, 4], [8, 10], [5, 6], [0, 8], [5], [13], [0, 2, 6, 12, 14], [0, 4, 5, 9], [0, 3, 5, 11], [0, 4, 9, 12], [5]], [[0], [0, 11], [0, 4, 9, 12], [0, 1, 10], [0, 2, 13], [0, 3, 10, 13], [0], [0, 8], [0, 2], [2, 5, 11], [7, 8], [0, 15], [0, 1, 3, 4, 10], [0], [0, 12], [0, 2], [4, 5, 6, 8], [2, 8, 14], [5, 6, 10], [0, 8, 10], [2, 3, 10], [0, 8, 9], [2, 5], [0, 5, 6, 10, 12], [0, 2, 3, 5, 8, 10], [0, 5, 6, 8, 9, 15], [2, 4, 8], [0, 14], [1, 5], [4, 10], [1, 8, 13], [0, 2, 10]], [[0], [], [2, 14], [0, 2, 3, 4, 5, 6, 10, 11], [0], [0, 5, 6, 7, 10], [2, 3, 4, 9, 10, 13], [0, 4], [0], [1, 2, 12, 15], [1, 5], [2, 7], [], [0, 6, 9], [0, 11, 12], [3, 5, 15], [1, 2, 5, 12], [0, 1, 5], [1, 3, 8, 9], [0, 8, 14], [0, 10], [7], [2], [4], [0, 3], [4, 8, 10], [7], [0, 4, 12, 13], [], [0, 2], [0, 3, 4, 10], [0, 5]], [[11], [15], [12], [0, 2, 12], [2, 4, 9], [6, 9, 10], [0], [0, 12, 15], [], [0, 4, 10], [4, 5, 8, 12], [1, 4, 9, 12], [0, 6, 8, 10], [0, 4, 10], [0, 4, 8, 10, 11], [2, 13], [0, 1, 4, 12], [2, 5, 8], [0, 2, 3, 8], [0, 2, 3, 9], [10], [0, 4, 6, 8, 10], [1, 8, 9, 11], [0, 2, 4, 5, 6, 9, 12], [0, 1, 2], [5, 6, 10], [4, 8, 12], [0, 4, 9, 10], [1, 5, 15], [0, 5], [0, 1, 5, 7, 8], [0, 12]], [[0, 5, 12], [0, 2, 8, 12], [0, 1, 8, 14], [6, 7, 10], [4, 5, 6, 10, 12], [], [4, 12, 15], [3, 10], [0, 2, 8, 11], [0, 1, 8], [2, 3, 12], [4, 5], [0, 5, 10, 13], [0, 9], [0, 2, 10, 14], [0, 2, 10, 12], [10], [2, 8], [12], [8, 9, 10], [0, 2, 5, 8, 10], [0, 3, 5, 14], [0, 4, 6], [3, 5, 6, 8, 9, 10], [0, 1, 5], [8], [0, 12], [0, 2, 14], [1, 3, 8], [2, 3, 15], [0, 6, 8, 12], [0, 2, 6, 9, 10]], [[8, 12], [8], [1, 5, 6], [0, 4, 6, 7, 9, 10], [1, 6], [0, 1, 4, 12], [0, 4, 12], [4, 15], [0, 2, 5], [0, 5, 8, 10], [0, 15], [2, 7, 8, 10], [2, 10], [4, 6], [0, 10, 12], [], [0], [0, 4, 5, 15], [4, 5], [2, 5, 8], [0, 6], [0, 6, 7, 12], [0, 1, 3, 4], [0, 13], [9], [0, 2, 6, 8, 9], [15], [2], [0, 6, 9, 10]]]
  | 7 => [[[2], [1, 13], [4, 12], [1, 5], [0, 1, 8], [1, 10], [8, 11], [0, 1, 14], [6], [1, 3, 4, 10], [0, 1, 6, 12, 15], [8], [2], [1], [7], [14], [0], [6, 8], [], [0], [], [1, 4], [0, 11, 13], [10], [5], [6, 8], [], [1, 6, 7, 14], [0, 9], [], [0, 1, 4], [2, 8]], [[0], [0, 11], [0, 2], [5, 6, 8], [6, 7, 12], [5, 8], [], [0, 6], [], [1], [8], [8], [0], [12], [4], [0], [2, 8], [0, 9], [0], [0, 3], [0, 11], [8], [14], [], [0, 3, 6, 9], [0, 2, 10], [3], [0, 9], [0, 4], [2, 8], [0], []], [[11], [0, 1, 10], [], [], [3], [0, 7, 8], [2, 5], [4, 11], [0, 4], [6, 10, 11], [0], [7], [0, 5, 12], [0], [1], [7], [14], [6], [0, 1], [0, 3, 15], [0, 1, 4, 5], [0], [0], [0, 1, 4], [0, 3, 8, 13], [1, 2], [], [12], [4], [0, 8], [8], [0, 4]], [[0, 6, 10, 14], [0, 8], [15], [0, 8], [2], [], [0, 15], [2, 7, 8, 13], [0, 15], [], [11], [3, 4, 8, 11], [0, 1, 4], [1, 6], [0], [0, 8, 13], [14], [6, 14], [8, 12], [1], [2], [1], [0, 6, 10], [0], [6], [8, 11], [0, 2, 3], [2, 13], [1, 8], [0, 8], [8], []], [[8, 11], [3, 10, 13], [0, 3], [0, 1, 3], [12], [0], [11, 14], [1], [], [0, 8], [], [0], [0, 2, 5, 8], [4, 14], [0], [0], [0, 2, 10], [], [0, 2, 4, 13], [2, 3, 13], [7], [0, 6], [], [0], [0, 8, 15], [0, 8, 12], [5], [3, 6, 9], [0, 4, 8, 10], [0, 3, 7], [0], [0, 2, 10]], [[0, 4, 8], [0, 1, 10], [3, 5, 12, 14], [0, 1, 3, 6, 7, 8], [0], [3, 8], [0, 10, 15], [0, 10], [0, 4, 7], [2], [0, 4, 9, 13, 14], [8], [0], [7, 8, 11], [5], [], [], [0], [], [0, 8, 10], [0], [0, 11], [12], [0, 1], [0, 8], [1], [], [0, 10], [2], [2], [0, 1, 2, 3, 11], [0, 5, 8]], [[0, 4, 8], [0, 10, 13], [], [8, 10], [1, 7], [0, 2], [], [0, 5, 6, 8], [0], [], [], [], [], [0, 1, 3], [6], [2, 7, 8], [10], [6], [3], [1, 6, 8], [], [5], [1], [2], [2, 4, 10], [0, 12], [5, 6, 7], [], [0], [], [0, 1, 8], []], [[0, 2, 10], [2], [7, 8], [], [], [], [0, 3, 11], [3], [0, 2, 8, 9], [], [4], [0, 3], [0, 4, 12], [], [2, 4], [8], [3, 14], [], [4], [0, 2, 8], [0, 15], [0], [0, 10, 11], [], [0, 1], [0, 8], [1, 10], [5, 10], [2, 8], [2], [0, 11, 14], [0, 8]], [[0, 4], [0, 8, 9], [0, 5, 8], [0, 8, 10], [0, 10], [8, 11], [0, 8, 11, 12], [0, 1, 10, 13], [0, 1], [8], [2], [0, 7], [1, 5, 8], [], [0], [0], [], [0], [8], [3, 6, 12], [0, 1, 12, 15], [], [3, 8, 11], [0], [0], [], [14], [0, 8], [], [0], [3], [0, 12]], [[8], [7], [1, 4, 15], [8], [0, 13], [0], [7, 10], [10, 12], [5, 6, 7, 10], [0, 1, 10, 12], [], [0], [], [], [0], [0], [], [6], [8], [], [7, 15], [0, 8], [0], [10], [2, 12], [], [5], [12], [0, 3, 8], [10], [8], [0]], [[2, 3], [1, 4], [0], [], [0, 3], [0, 5], [0], [2], [0, 2, 11, 15], [0, 7, 8], [0, 8], [], [1], [0, 10, 11], [9], [1], [10], [0], [3], [4, 8, 11], [0], [], [0, 1, 12], [9, 10], [1, 8], [3], [0, 3], [0, 1], [5, 7, 10, 12, 13, 15], [0, 5], [0], [5]], [[0, 4, 6], [1, 2], [0], [0, 6, 9], [1, 13], [8], [8], [8, 9], [5, 9], [7], [0, 1, 6, 13], [8], [1, 9], [0, 1, 8, 10], [12], [0], [8, 10], [], [0, 7, 14], [0, 3], [0, 2, 12], [7, 9], [0, 3, 12], [], [0, 11], [1, 8], [4, 8], [3, 4, 8], [0, 9], [0], [0, 7, 9], [8]], [[0], [10], [1], [6], [2, 7, 8], [], [10], [0, 1, 8], [0], [15], [2, 5], [8, 15], [6], [0, 5, 8], [0], [7, 10, 12], [], [8], [8, 14], [2, 14], [1, 4, 8], [2, 7], [0, 3, 8], [6], [], [14], [6], [0, 11], [0, 10, 11], [0, 2, 7, 10], [7], [12]], [[0], [0, 1], [0, 1], [], [], [8], [8], [0, 6, 14], [2, 8], [8], [9], [7, 9], [0, 1, 4, 9], [0, 3, 8, 10, 15], [0, 1, 5], [0, 8, 12], [0, 9, 12, 15], [], [7], [7], [], [5, 8, 10], [1, 4, 10], [3, 11], [], [0], [0, 12], [6], [5], [], [0, 10], [0, 8, 9, 10, 11]], [[11], [1, 6, 12], [2], [8], [0, 4], [], [0, 8, 9], [0], [3, 10], [0, 11], [], [6], [3, 12], [6], [0, 4], [0, 5, 8], [0], [0], [], [0, 1, 8], [0], [], [5, 11, 15], [], [8], [8], [4], [0], [], [0], [7, 13], [0]], [[0, 1], [], [0, 14], [0, 4], [], [1, 4, 6], [0, 3, 7, 13], [0], [0, 4], [4, 5], [3, 8, 11], [0, 14], [1], [0, 9, 12], [4], [], [0, 8, 13], [4, 8], [8], [8], [], [10], [5, 8, 15], [1, 8], [0], [1, 4], [], [4, 7, 12], [], [], [0, 2], [0, 1]], [[3, 4, 10], [0], [10, 11], [2, 11, 12], [0, 5, 8, 12], [0], [], [0, 1, 4], [0, 2, 10], [0], [2], [8], [0, 1], [0, 4, 9, 12], [6, 8], [], [0, 1, 9], [0], [14], [0, 4, 6], [0, 6, 10], [1, 8], [4], [1, 2, 8, 11], [2, 4, 8], [0, 4, 8, 10], [], [0], [6, 10], [0, 1, 7, 14], [3], [1, 9, 12]], [[0, 6], [], [11], [], [0, 6], [10], [15], [0, 1, 2, 8], [10], [1, 2], [7, 8], [], [11], [], [3], [0, 15], [14], [11], [4], [2, 8], [5], [6], [0, 1, 8], [10], [0], [11], [0], [4, 7, 8], [0], [8], [2, 4, 6], [0, 4, 11]], [[0], [1], [], [], [2, 11], [0, 7], [1, 8, 12, 15], [7], [1, 3, 4], [0, 1, 9, 10, 13], [1, 8], [0, 8], [2], [0, 5, 8, 13], [3, 9, 12], [0, 7], [], [0, 10], [], [0, 7, 8], [0, 2, 4], [0, 6, 10, 11], [6, 15], [14], [2, 15], [0, 3, 5, 6], [0, 10], [], [8], [0, 12], [0, 8], [1]], [[2, 3], [0], [0, 2], [3, 7], [], [5], [1, 10], [0], [15], [0, 3, 8], [3, 8], [14], [], [0, 3, 8, 10], [0, 2, 10, 11], [8], [0, 13], [0], [0, 1, 5, 11], [0, 1], [10, 11, 14], [0, 5, 8, 14], [14], [0, 6], [8, 10], [1, 10], [0, 5, 8, 9, 10], [0, 8], [1, 8, 14], [0, 6, 7], [], []], [[4], [8], [], [0], [8, 15], [2], [0], [3], [11], [], [2], [0, 9, 11], [], [], [0, 3], [0, 5, 7, 12, 14], [0, 12], [11], [], [8], [0, 3, 12], [0, 8], [0, 2, 15], [0, 2, 4, 12, 14], [0], [10], [8, 12], [], [11], [0], [], [0, 2]], [[2], [], [0], [3], [], [3, 11, 12], [], [0, 4], [1, 8], [1, 4, 10], [0, 3, 5], [8], [], [], [2], [5, 10, 12], [4], [], [0, 2, 13, 15], [9], [], [0], [0], [0, 8, 12], [2, 8], [0], [], [0], [], [], [7], []], [[6, 9, 11], [0, 1], [0, 6, 8], [0, 3, 8, 11], [0, 4, 8, 9, 11], [0, 7], [0], [1, 13], [2], [8], [], [0, 8], [0, 10, 14], [0, 6], [8], [0, 4], [0, 1, 5, 14], [5], [0, 1, 14], [], [0, 7], [0, 8], [8, 11], [4, 8], [0], [0, 12], [], [], [9], [0, 5], [0], []], [[8], [0, 3, 8, 12], [3], [0], [], [0], [], [4], [11], [2], [0, 9], [1, 13], [], [0, 8, 11], [0], [], [1, 7], [0, 10], [], [8], [0], [10], [9], [8], [], [14], [0, 4], [], [0], [11], [8], [0, 2, 7]], [[1, 6, 14], [], [3, 15], [0, 1, 3], [6], [0, 8], [0, 11], [3], [0, 2, 5], [0, 2, 11, 13], [0, 9, 13], [4], [], [0], [0, 8], [0, 7], [0], [2, 4, 6, 12], [0, 10], [0], [0, 5, 10, 14], [0, 10, 11], [6, 8], [0], [0, 9, 10], [], [0, 4, 6, 11], [8], [0], [11], [0], [7]], [[], [0, 2, 12, 15], [1, 4], [0, 3], [8], [8], [3], [], [0, 3, 6], [10], [], [0, 8], [14], [], [], [8], [0], [0, 14], [0], [4, 8], [0, 11, 14], [0, 5], [], [0, 1], [], [2], [0, 1, 2, 3, 10], [0, 12], [0], [11], [6], [0, 4]], [[1], [0], [8], [8], [0, 1, 10], [1, 2, 12], [0], [0, 1, 3], [], [1, 2, 4, 5, 7], [0, 2, 6], [3, 8, 14], [0, 4, 15], [0, 9], [0], [8], [0, 1, 7, 11], [7], [0, 6, 8], [0, 4, 8], [0, 6, 8], [0], [0, 4, 5, 10], [], [0, 8], [0, 2, 3, 6], [11], [6, 8], [4, 9], [3, 5], [0, 6, 7, 8], []], [[10], [], [0, 6, 8], [0, 8], [0, 2, 4], [0], [], [], [8], [1, 11], [8, 10, 12, 13], [], [8], [2, 8], [], [1, 2, 14], [4], [8, 9], [0, 10], [], [], [3], [0, 5, 9, 10], [], [0, 11, 14], [0, 4, 5, 10], [], [], [4, 12], [2, 10], [1, 8], [0]], [[0], [], [6], [4, 11, 12], [4], [0], [0, 2, 3, 9], [], [4], [1, 13], [], [0, 3, 4], [8], [4, 8], [0, 8, 10, 15], [0, 2, 10, 11], [], [1, 8], [0, 1], [0, 13], [], [0, 12], [2, 8], [0, 10], [], [3], [], [0, 6, 8], [6, 7], [1, 14], [], [5, 7, 11, 12]], [[8], [0, 8], [15], [0], [3], [], [0], [0, 10, 15], [10], [4, 8], [1, 8], [0, 1], [], [0, 3, 4, 8], [0], [2, 4], [1, 4, 6], [], [10], [], [], [], [2, 6], [0, 4, 5], [], [2, 8], [0, 11], [], [0, 8], [0, 6], [0, 5], [0, 8]], [[0, 8], [0], [14], [0, 12], [0], [1, 10], [14], [], [4, 7, 13], [1, 7, 15], [6], [14], [0, 8], [], [], [0, 4], [], [0, 5], [5, 11, 12], [8], [0, 8], [0], [0, 10, 12], [1, 3, 10], [6], [], [1, 11], [], [0, 8], [12], [0, 8], [0, 6]], [[], [], [], [0, 1, 7, 8, 10], [0, 1, 3, 8], [0], [], [6, 8, 11], [], [], [12], [0, 13], [10], [0, 4, 8], [6, 8], [0, 2, 11, 12], [0, 8], [4, 9], [], [2], [0], [0, 4, 10], [3, 4], [], [8], [0], [11], [0], [0, 8]]]
  | 8 => [[[], [], [], [1], [1], [], [11], [], [], [], [], [], [], [8], [7], [], [], [], [], [0], [], [], [], [], [], [8], [0], [], [], [], [4], []], [[], [], [], [], [], [2, 6, 10], [], [0], [], [], [5], [], [], [1, 2], [4], [], [], [], [], [3], [], [6], [], [2], [], [0], [0], [7], [4, 5], [3, 6], [], []], [[], [10], [8], [0], [], [7, 8], [], [], [], [0, 10], [], [], [], [11], [], [], [], [], [], [4], [14], [0, 3], [12], [], [], [], [], [2], [4], [10], [], []], [[], [], [], [8], [], [1], [], [], [], [8, 14], [], [], [6], [], [], [], [], [], [], [6], [2], [2], [], [], [], [2, 11], [], [], [], [], [], []], [[11], [], [], [], [12], [], [], [], [], [6], [], [4], [], [], [], [0], [0], [], [4, 13], [1, 3], [], [], [3], [0], [8], [], [0], [6], [0, 2], [9], [0], [0, 10]], [[], [], [8], [], [14], [], [], [0], [], [], [4, 5], [0, 8], [], [0], [0], [10], [], [], [], [10], [], [], [], [], [], [0], [0], [1], [], [], [13], [5, 8]], [[], [0], [], [], [], [1], [], [], [], [10], [], [], [], [], [], [2], [7], [], [11], [], [], [9], [], [], [], [], [], [], [0], [9], [8], []], [[0], [2], [1], [], [], [6], [], [], [0], [], [4], [], [4], [], [4], [0], [14], [0, 8], [3], [], [], [], [], [], [0], [1], [], [], [], [], [], [6]], [[0], [], [], [10], [], [], [], [1], [], [], [], [7], [1], [], [], [], [], [], [], [], [], [], [], [3], [], [], [14], [8], [], [0], [], [12]], [[], [7], [8], [], [], [], [], [4], [], [7], [], [], [], [], [], [], [], [0], [], [], [], [], [], [], [], [0, 12], [], [2], [], [], [], [7]], [[2], [], [], [], [], [6], [], [], [], [], [], [12], [], [], [], [1], [], [8, 11], [], [], [], [], [], [], [], [], [], [], [2, 5], [0], [], []], [[], [], [], [], [], [], [], [], [14], [3], [6, 7], [], [], [], [], [], [10], [], [], [0], [], [4, 9], [], [], [], [], [], [0], [], [9], [], [8]], [[], [], [], [], [], [], [], [4], [], [], [13], [], [], [12], [], [12], [], [], [], [], [1], [7], [7], [], [], [], [], [], [], [2, 10], [], [12]], [[], [], [], [], [], [8], [], [0], [], [], [], [0, 7], [1, 4], [], [0], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [0], [], [11]], [[11], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [4, 8], [0], [], [], [], [], []], [[], [], [], [], [], [1], [], [], [], [5, 8], [1], [], [1], [1], [], [], [], [], [], [0], [], [10], [1, 3], [], [], [8], [], [6], [0], [], [0], [3]], [[3], [0], [11], [], [0, 13], [9], [], [], [], [], [5, 6], [], [], [12], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], [2], [0], [], []], [[], [], [], [], [6], [1], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], [8], [0, 3], [], [], [], [], [], [8], [], [3, 6], [], [3]], [[], [1], [], [], [], [], [], [], [], [5], [], [], [], [], [], [], [], [], [], [2], [], [], [], [], [], [5], [0], [], [1], [], [], []], [[], [], [10], [], [], [5], [], [], [], [1, 8], [], [], [], [3], [], [], [], [], [0], [], [], [], [], [0], [10], [0, 4], [9], [0, 1], [], [7], [], [0]], [[], [], [7, 10], [], [5, 15], [1], [], [], [0], [4, 9], [8], [], [], [], [], [], [], [], [], [], [8], [], [], [], [], [], [], [], [], [], [], []], [[], [0], [1], [], [], [], [], [], [0], [4], [0, 3], [], [], [], [1], [10], [], [], [], [], [], [], [], [], [8], [0], [], [], [5], [], [6], []], [[9], [1], [], [0], [], [], [13], [], [2, 8], [], [2], [], [], [0], [13], [0, 1, 4], [], [], [], [], [], [], [], [14], [8], [12], [], [], [], [0], [], []], [[], [], [], [], [], [], [], [], [0], [], [4], [], [], [8], [], [], [], [], [], [], [], [], [], [0], [], [], [], [11], [], [], [], [2]], [[1, 6], [], [], [1], [], [0], [3], [], [], [], [], [], [], [], [], [0], [], [], [], [], [], [], [], [], [10], [], [], [], [], [9], [7], [1]], [[], [], [], [], [], [], [12], [4], [3], [], [], [], [], [], [3], [3], [0], [], [0], [0], [], [4], [2], [], [], [0, 10], [3], [0, 8], [0], [], [6, 9], []], [[], [], [0, 5], [8], [], [], [0], [], [], [7], [0], [0, 10], [], [0, 14], [], [], [5], [], [], [], [6], [], [10], [], [], [6], [], [5], [], [3], [9], [2]], [[1], [], [5, 8], [8], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [2, 10, 15], [], [], [], [6], [], [], [], [], [], [12], [0], [1, 8], []], [[], [], [], [0], [], [], [0, 7], [], [4], [1], [], [15], [8], [4], [], [0, 10], [], [], [4], [], [], [], [6], [], [], [14], [], [0, 6], [6, 8], [], [], [2]], [[], [], [], [], [], [], [8], [], [11], [], [1, 4], [0, 1], [8], [4], [6], [], [], [], [], [], [], [], [], [], [], [3, 13], [], [], [], [], [], []], [[8], [], [10, 12], [], [], [], [], [], [], [7], [13], [14], [], [], [3], [], [], [], [0], [1], [8], [15], [], [], [], [], [], [], [], [], [], []], [[], [2], [], [0], [], [], [], [11], [0], [1], [10], [], [9], [0], [], [], [14], [], [1], [], [], [], [11, 15], [0], [], [], [9], [], [8]]]
  | 9 => [[[], [], [], [1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [2, 6], [], [], [], [], [], [], [], [2], [], [], [], [], [], [], [], [6], [], [], [], [0], [], [7], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [11], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [13], [], [], [], [], [], [], [], [], [6], [], [], [], []], [[], [], [], [], [], [], [], [0], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [14], [], [3], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [7], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [14], [3], [], [], [], [], [], [], [], [], [], [0], [], [4], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [7], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [8], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [5], [], [], [1], [], [], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], []], [[3], [], [], [], [], [9], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [6], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 3], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [5], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5], [], [], [1], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [10], [], [9], [], [], [], [], []], [[], [], [7], [], [15], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [1], [], [], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5], [], [], []], [[], [], [], [], [], [], [], [], [], [], [2], [], [], [], [], [1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2]], [[], [], [], [], [], [], [3], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [7], []], [[], [], [], [], [], [], [12], [4], [], [], [], [], [], [], [], [], [], [], [0], [0], [], [4], [2], [], [], [], [3], [8], [], [], [6, 9], []], [[], [], [0, 5], [], [], [], [], [], [], [], [], [], [], [14], [], [], [], [], [], [], [], [], [10], [], [], [], [], [], [], [], [], []], [[], [], [5, 8], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2], [], [], [], [], [], [], [], [], [], [12], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [10, 12], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [11], [], [], [], [], [], [], [], [], [], [], [1], [], [], [], [], [], [], [], [], [], []]]
  | 10 => [[[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]]
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
  | @one s a r save hN h0 hd hnm h ih =>
    intro _
    exact False.elim hN
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

def grp : List (Nat × (Nat → Nat) × (List Nat × List Nat)) := [(0, (fun w => (w >>> 0) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 15) % 2 + 2 * (0))))))))))))))))), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])), (1, (fun w => (w >>> 0) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 5) % 2 + 2 * (0))))))))))))))))), ([0, 12, 8, 4, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5], [0, 12, 8, 4, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5])), (2, (fun w => (w >>> 1) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 6) % 2 + 2 * (0))))))))))))))))), ([1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6], [1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6])), (3, (fun w => (w >>> 1) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 12) % 2 + 2 * (0))))))))))))))))), ([1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 0, 4, 8, 12], [12, 0, 4, 8, 13, 1, 5, 9, 14, 2, 6, 10, 15, 3, 7, 11])), (4, (fun w => (w >>> 5) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 10) % 2 + 2 * (0))))))))))))))))), ([5, 1, 13, 9, 4, 0, 12, 8, 7, 3, 15, 11, 6, 2, 14, 10], [5, 1, 13, 9, 4, 0, 12, 8, 7, 3, 15, 11, 6, 2, 14, 10])), (5, (fun w => (w >>> 5) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 0) % 2 + 2 * (0))))))))))))))))), ([5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12, 1, 2, 3, 0], [15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10])), (6, (fun w => (w >>> 6) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 11) % 2 + 2 * (0))))))))))))))))), ([6, 5, 4, 7, 2, 1, 0, 3, 14, 13, 12, 15, 10, 9, 8, 11], [6, 5, 4, 7, 2, 1, 0, 3, 14, 13, 12, 15, 10, 9, 8, 11])), (7, (fun w => (w >>> 6) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 1) % 2 + 2 * (0))))))))))))))))), ([6, 10, 14, 2, 7, 11, 15, 3, 4, 8, 12, 0, 5, 9, 13, 1], [11, 15, 3, 7, 8, 12, 0, 4, 9, 13, 1, 5, 10, 14, 2, 6])), (8, (fun w => (w >>> 10) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 15) % 2 + 2 * (0))))))))))))))))), ([10, 6, 2, 14, 9, 5, 1, 13, 8, 4, 0, 12, 11, 7, 3, 15], [10, 6, 2, 14, 9, 5, 1, 13, 8, 4, 0, 12, 11, 7, 3, 15])), (9, (fun w => (w >>> 10) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 5) % 2 + 2 * (0))))))))))))))))), ([10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], [10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5])), (10, (fun w => (w >>> 11) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 12) % 2 + 2 * (0))))))))))))))))), ([11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12], [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12])), (11, (fun w => (w >>> 11) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 6) % 2 + 2 * (0))))))))))))))))), ([11, 15, 3, 7, 8, 12, 0, 4, 9, 13, 1, 5, 10, 14, 2, 6], [6, 10, 14, 2, 7, 11, 15, 3, 4, 8, 12, 0, 5, 9, 13, 1])), (12, (fun w => (w >>> 12) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 11) % 2 + 2 * (0))))))))))))))))), ([12, 0, 4, 8, 13, 1, 5, 9, 14, 2, 6, 10, 15, 3, 7, 11], [1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 0, 4, 8, 12])), (13, (fun w => (w >>> 12) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 1) % 2 + 2 * (0))))))))))))))))), ([12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5, 0, 3, 2, 1], [12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5, 0, 3, 2, 1])), (14, (fun w => (w >>> 15) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 0) % 2 + 2 * (0))))))))))))))))), ([15, 11, 7, 3, 14, 10, 6, 2, 13, 9, 5, 1, 12, 8, 4, 0], [15, 11, 7, 3, 14, 10, 6, 2, 13, 9, 5, 1, 12, 8, 4, 0])), (15, (fun w => (w >>> 15) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 0) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 10) % 2 + 2 * (0))))))))))))))))), ([15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10], [5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12, 1, 2, 3, 0]))]

theorem okG : grp.all (fun x => okPerm x.2.2) = true := by decide +kernel

theorem fastOK : ∀ x ∈ grp, x.2.1 = ap x.2.2.1 := by
  intro x hx
  simp only [grp, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

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
  ws.all (fun w => decide (w < 2 ^ 16)) &&
    (((hintOf s).getD (hkey ws / 32) []).getD (hkey ws % 32) []).any (tryPerm s ws)

theorem sym_run {s : Nat} {ys : List Nat} (hs : s ≤ 10) (hl : listed s ys = true) (h : RunD truthMask goal s ys) :
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
set_option maxRecDepth 40000 in
theorem c3_0 : cc 3 0 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_5 : cc 3 5 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_10 : cc 3 10 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_15 : cc 3 15 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_20 : cc 3 20 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_25 : cc 3 25 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_30 : cc 3 30 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_35 : cc 3 35 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_40 : cc 3 40 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_45 : cc 3 45 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_50 : cc 3 50 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_55 : cc 3 55 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_60 : cc 3 60 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_65 : cc 3 65 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_70 : cc 3 70 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_75 : cc 3 75 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_80 : cc 3 80 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_85 : cc 3 85 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_90 : cc 3 90 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_95 : cc 3 95 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_100 : cc 3 100 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_105 : cc 3 105 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_110 : cc 3 110 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_115 : cc 3 115 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_120 : cc 3 120 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_125 : cc 3 125 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_130 : cc 3 130 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_135 : cc 3 135 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_140 : cc 3 140 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_145 : cc 3 145 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_150 : cc 3 150 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_155 : cc 3 155 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_160 : cc 3 160 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_165 : cc 3 165 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_170 : cc 3 170 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_175 : cc 3 175 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_180 : cc 3 180 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_185 : cc 3 185 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_190 : cc 3 190 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_195 : cc 3 195 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_200 : cc 3 200 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_205 : cc 3 205 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_210 : cc 3 210 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_215 : cc 3 215 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_220 : cc 3 220 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_225 : cc 3 225 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_230 : cc 3 230 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_235 : cc 3 235 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c3_240 : cc 3 240 = true := by decide +kernel
private theorem lvl_3 : ∀ i, 0 ≤ i → i < 245 → cellCheck 3 i = true :=
  (range_split (range_split (range_split (range_split (range_split (span_ok c3_0) (range_split (span_ok c3_5) (span_ok c3_10))) (range_split (span_ok c3_15) (range_split (span_ok c3_20) (span_ok c3_25)))) (range_split (range_split (span_ok c3_30) (range_split (span_ok c3_35) (span_ok c3_40))) (range_split (span_ok c3_45) (range_split (span_ok c3_50) (span_ok c3_55))))) (range_split (range_split (range_split (span_ok c3_60) (range_split (span_ok c3_65) (span_ok c3_70))) (range_split (span_ok c3_75) (range_split (span_ok c3_80) (span_ok c3_85)))) (range_split (range_split (span_ok c3_90) (range_split (span_ok c3_95) (span_ok c3_100))) (range_split (span_ok c3_105) (range_split (span_ok c3_110) (span_ok c3_115)))))) (range_split (range_split (range_split (range_split (span_ok c3_120) (range_split (span_ok c3_125) (span_ok c3_130))) (range_split (span_ok c3_135) (range_split (span_ok c3_140) (span_ok c3_145)))) (range_split (range_split (span_ok c3_150) (range_split (span_ok c3_155) (span_ok c3_160))) (range_split (span_ok c3_165) (range_split (span_ok c3_170) (span_ok c3_175))))) (range_split (range_split (range_split (span_ok c3_180) (range_split (span_ok c3_185) (span_ok c3_190))) (range_split (span_ok c3_195) (range_split (span_ok c3_200) (span_ok c3_205)))) (range_split (range_split (span_ok c3_210) (range_split (span_ok c3_215) (span_ok c3_220))) (range_split (range_split (span_ok c3_225) (span_ok c3_230)) (range_split (span_ok c3_235) (span_ok c3_240)))))))
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
set_option maxRecDepth 40000 in
theorem c10_0 : cc 10 0 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_5 : cc 10 5 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_10 : cc 10 10 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_15 : cc 10 15 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_20 : cc 10 20 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_25 : cc 10 25 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_30 : cc 10 30 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_35 : cc 10 35 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_40 : cc 10 40 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_45 : cc 10 45 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_50 : cc 10 50 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_55 : cc 10 55 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_60 : cc 10 60 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_65 : cc 10 65 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_70 : cc 10 70 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_75 : cc 10 75 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_80 : cc 10 80 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_85 : cc 10 85 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_90 : cc 10 90 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_95 : cc 10 95 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_100 : cc 10 100 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_105 : cc 10 105 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_110 : cc 10 110 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_115 : cc 10 115 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_120 : cc 10 120 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_125 : cc 10 125 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_130 : cc 10 130 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_135 : cc 10 135 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_140 : cc 10 140 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_145 : cc 10 145 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_150 : cc 10 150 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_155 : cc 10 155 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_160 : cc 10 160 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_165 : cc 10 165 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_170 : cc 10 170 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_175 : cc 10 175 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_180 : cc 10 180 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_185 : cc 10 185 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_190 : cc 10 190 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_195 : cc 10 195 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_200 : cc 10 200 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_205 : cc 10 205 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_210 : cc 10 210 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_215 : cc 10 215 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_220 : cc 10 220 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_225 : cc 10 225 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_230 : cc 10 230 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_235 : cc 10 235 = true := by decide +kernel
set_option maxRecDepth 40000 in
theorem c10_240 : cc 10 240 = true := by decide +kernel
private theorem lvl_10 : ∀ i, 0 ≤ i → i < 245 → cellCheck 10 i = true :=
  (range_split (range_split (range_split (range_split (range_split (span_ok c10_0) (range_split (span_ok c10_5) (span_ok c10_10))) (range_split (span_ok c10_15) (range_split (span_ok c10_20) (span_ok c10_25)))) (range_split (range_split (span_ok c10_30) (range_split (span_ok c10_35) (span_ok c10_40))) (range_split (span_ok c10_45) (range_split (span_ok c10_50) (span_ok c10_55))))) (range_split (range_split (range_split (span_ok c10_60) (range_split (span_ok c10_65) (span_ok c10_70))) (range_split (span_ok c10_75) (range_split (span_ok c10_80) (span_ok c10_85)))) (range_split (range_split (span_ok c10_90) (range_split (span_ok c10_95) (span_ok c10_100))) (range_split (span_ok c10_105) (range_split (span_ok c10_110) (span_ok c10_115)))))) (range_split (range_split (range_split (range_split (span_ok c10_120) (range_split (span_ok c10_125) (span_ok c10_130))) (range_split (span_ok c10_135) (range_split (span_ok c10_140) (span_ok c10_145)))) (range_split (range_split (span_ok c10_150) (range_split (span_ok c10_155) (span_ok c10_160))) (range_split (span_ok c10_165) (range_split (span_ok c10_170) (span_ok c10_175))))) (range_split (range_split (range_split (span_ok c10_180) (range_split (span_ok c10_185) (span_ok c10_190))) (range_split (span_ok c10_195) (range_split (span_ok c10_200) (span_ok c10_205)))) (range_split (range_split (span_ok c10_210) (range_split (span_ok c10_215) (span_ok c10_220))) (range_split (range_split (span_ok c10_225) (span_ok c10_230)) (range_split (span_ok c10_235) (span_ok c10_240)))))))

private theorem checkedCells (s : Nat) (hs : s ≤ 10) (i : Nat) (hi : i < 245) : cellCheck s i = true := by
  interval_cases s <;> first | exact lvl_0 i (Nat.zero_le i) hi | exact lvl_1 i (Nat.zero_le i) hi | exact lvl_2 i (Nat.zero_le i) hi | exact lvl_3 i (Nat.zero_le i) hi | exact lvl_4 i (Nat.zero_le i) hi | exact lvl_5 i (Nat.zero_le i) hi | exact lvl_6 i (Nat.zero_le i) hi | exact lvl_7 i (Nat.zero_le i) hi | exact lvl_8 i (Nat.zero_le i) hi | exact lvl_9 i (Nat.zero_le i) hi | exact lvl_10 i (Nat.zero_le i) hi

private theorem impossibleState : ∀ s ≤ 10, ∀ i < 245, ∀ ws ∈ (rowsOf s).getD i [], ¬ RunD truthMask goal s ws := by
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
  (List.range 11).all (fun s => rootCheck s (inputSubsets.getD i []))

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

private theorem impossibleRoot {s : Nat} {ws : List Nat} (hs : s ≤ 10)
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

private theorem rootsAgree : ∀ r : Fin 16,
    roots.map (·.testBit r.val) = PEqualNP.Represents.oneEach
      (Fin.ofNat 4 (r.val / 4)) (Fin.ofNat 4 (r.val % 4)) := by decide +kernel

private theorem domainRows : ∀ r : Fin 16, truthMask.testBit r.val = true := by decide +kernel
private theorem targetIndex : ∀ r : Fin 16, 4 * (r.val / 4) + (r.val % 4) = r.val := by decide

private theorem rulesOut (C : Circuit) (hfan : FanInTwo C) (hno : ∀ g ∈ C.gates, g.op = GateOp.not → NN) (hs : C.size ≤ 10)
    (hrep : PEqualNP.Represents.Represents
      (fun u v : Fin 4 => target.testBit (4 * u.val + v.val)) C) : False := by
  have hsup0 : ∀ v ∈ roots, Avail truthMask roots v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots hfan hno 0 roots roots rfl hsup0
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
  have hz : C.gates.length ≤ 10 := hs
  exact impossibleRoot (by omega) hsub (Run.perm hp' hrun)

end PEqualNP.Outside.L_meta_23510

theorem PEqualNP.Outside.L_meta_23510 : (¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % 4)) 10) := by
  rintro ⟨C, hmono, hs, hrep⟩
  have hf : (fun u v : Fin 4 => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % 4)) = (fun u v : Fin 4 => (25500 : ℕ).testBit (4 * u.val + v.val)) := by
    funext u v
    revert u v
    decide
  rw [hf] at hrep
  have hfan : PEqualNP.MetaComplexity.FanInTwo C := fun g hg => ⟨by
    have h2 := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2 ⊢
    rcases h2 with h | h <;> simp [h], (hmono g hg).2⟩
  have hno : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → PEqualNP.Outside.L_meta_23510.NN := by
    intro g hg h
    have h2 := (hmono g hg).1
    rw [h] at h2
    simp at h2
  exact PEqualNP.Outside.L_meta_23510.rulesOut C hfan hno hs hrep

import PEqualNP.Defs
import PEqualNP.Library.LRAT.PromiseN

namespace PEqualNP.Outside.L_meta_25027

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def truthMask : Nat := 2 ^ 36 - 1

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

theorem truthMask_bit (i : Nat) : truthMask.testBit i = decide (i < 36) := by
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

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 36)
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

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 36)
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

def roots : List Nat := [63, 4032, 258048, 16515072, 1056964608, 67645734912, 1090785345, 2181570690, 4363141380, 8726282760, 17452565520, 34905131040]
def target : Nat := 3275554815
def goal : Nat := target &&& truthMask

def pairs : List (Nat × Nat) := [(16, 4), (16, 10), (16, 12), (16, 13), (16, 14), (16, 15), (26, 14), (26, 20)]

def key (ws : List Nat) : Nat := ws.sum % 245

theorem key_lt (ws : List Nat) : key ws < 245 := Nat.mod_lt _ (by decide)

set_option maxRecDepth 100000 in
def fast : Nat → List (List (List (List Nat)))
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
theorem lenOK : ∀ s, s ≤ 6 → (rowsOf s).length ≤ 245 := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem fast_in {s k : Nat} {l : List Nat} (hs : s ≤ 6) (h : l ∈ fastGet s k) :
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
  pq.1.length == 36 && pq.1.all (fun j => decide (j < 36)) &&
    (List.range 36).all (fun j => pq.1[pq.2.getD j 0]? == some j) &&
    ap pq.1 goal == goal && ap pq.1 truthMask == truthMask

theorem ok_len {pq} (h : okPerm pq = true) : pq.1.length = 36 := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1

theorem ok_lt {pq} (h : okPerm pq = true) : ∀ j ∈ pq.1, j < 36 := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem ok_inv {pq} (h : okPerm pq = true) : ∀ j, j < 36 → pq.1[pq.2.getD j 0]? = some j := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact h.1.1.2

theorem ok_goal {pq} (h : okPerm pq = true) : ap pq.1 goal = goal := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2

theorem ok_mask {pq} (h : okPerm pq = true) : ap pq.1 truthMask = truthMask := by
  simp only [okPerm, Bool.and_eq_true, beq_iff_eq] at h; exact h.2

theorem perm_cases {pq} (h : okPerm pq = true) (i : Nat) :
    (pq.1[i]? = none ∧ ¬ i < 36) ∨ (∃ j, pq.1[i]? = some j ∧ i < 36 ∧ j < 36) := by
  have hl := ok_len h
  cases hpi : pq.1[i]? with
  | none =>
    left; refine ⟨rfl, ?_⟩
    have := List.getElem?_eq_none_iff.1 hpi; omega
  | some j =>
    right
    obtain ⟨hi, hj⟩ := List.getElem?_eq_some_iff.1 hpi
    exact ⟨j, rfl, by omega, ok_lt h j (hj ▸ List.getElem_mem hi)⟩

theorem high_bit {a : Nat} (ha : a < 2 ^ 36) {j : Nat} (hj : ¬ j < 36) : a.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))

theorem ap_inj {pq} (h : okPerm pq = true) {a b : Nat} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36)
    (he : ap pq.1 a = ap pq.1 b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 36
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

theorem mask_lt : truthMask < 2 ^ 36 := by decide

theorem negD_lt (a : Nat) : negD truthMask a < 2 ^ 36 :=
  Nat.lt_of_le_of_lt Nat.and_le_right mask_lt

theorem bin_lt (c : Bool) (a b : Nat) :
    (if c then andD truthMask a b else orD truthMask a b) < 2 ^ 36 := by
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

theorem ap_new {pq} (h : okPerm pq = true) {w : Nat} {xs : List Nat} (hw : w < 2 ^ 36)
    (hb : ∀ x ∈ xs, x < 2 ^ 36) (h0 : w ≠ 0) (hd : w ≠ truthMask) (hm : w ∉ xs) :
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
    (∀ w ∈ ws, w < 2 ^ 36) → RunD truthMask (ap pq.1 y) s (ws.map (ap pq.1)) := by
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
    have hb' : ∀ w ∈ (if c then andD truthMask a b else orD truthMask a b) :: kept ka a (kept kb b r), w < 2 ^ 36 := by
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

def grp : List (Nat × (Nat → Nat) × (List Nat × List Nat)) := [(0, (fun w => (w >>> 0) % 2 + 2 * ((w >>> 1) % 2 + 2 * ((w >>> 2) % 2 + 2 * ((w >>> 3) % 2 + 2 * ((w >>> 4) % 2 + 2 * ((w >>> 5) % 2 + 2 * ((w >>> 6) % 2 + 2 * ((w >>> 7) % 2 + 2 * ((w >>> 8) % 2 + 2 * ((w >>> 9) % 2 + 2 * ((w >>> 10) % 2 + 2 * ((w >>> 11) % 2 + 2 * ((w >>> 12) % 2 + 2 * ((w >>> 13) % 2 + 2 * ((w >>> 14) % 2 + 2 * ((w >>> 15) % 2 + 2 * ((w >>> 16) % 2 + 2 * ((w >>> 17) % 2 + 2 * ((w >>> 18) % 2 + 2 * ((w >>> 19) % 2 + 2 * ((w >>> 20) % 2 + 2 * ((w >>> 21) % 2 + 2 * ((w >>> 22) % 2 + 2 * ((w >>> 23) % 2 + 2 * ((w >>> 24) % 2 + 2 * ((w >>> 25) % 2 + 2 * ((w >>> 26) % 2 + 2 * ((w >>> 27) % 2 + 2 * ((w >>> 28) % 2 + 2 * ((w >>> 29) % 2 + 2 * ((w >>> 30) % 2 + 2 * ((w >>> 31) % 2 + 2 * ((w >>> 32) % 2 + 2 * ((w >>> 33) % 2 + 2 * ((w >>> 34) % 2 + 2 * ((w >>> 35) % 2 + 2 * (0))))))))))))))))))))))))))))))))))))), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]))]

theorem okG : grp.all (fun x => okPerm x.2.2) = true := by decide +kernel

theorem fastOK : ∀ x ∈ grp, x.2.1 = ap x.2.2.1 := by
  intro x hx
  simp only [grp, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl <;> rfl

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
  ws.all (fun w => decide (w < 2 ^ 36)) &&
    (((hintOf s).getD (hkey ws / 32) []).getD (hkey ws % 32) []).any (tryPerm s ws)

theorem sym_run {s : Nat} {ys : List Nat} (hs : s ≤ 6) (hl : listed s ys = true) (h : RunD truthMask goal s ys) :
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
private theorem lvl_4 : ∀ i, 0 ≤ i → i < 245 → cellCheck 4 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf, fast]
private theorem lvl_5 : ∀ i, 0 ≤ i → i < 245 → cellCheck 5 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf, fast]
private theorem lvl_6 : ∀ i, 0 ≤ i → i < 245 → cellCheck 6 i = true := by
  intro i _ _
  simp [cellCheck, rowsOf, fast]

private theorem checkedCells (s : Nat) (hs : s ≤ 6) (i : Nat) (hi : i < 245) : cellCheck s i = true := by
  interval_cases s <;> first | exact lvl_0 i (Nat.zero_le i) hi | exact lvl_1 i (Nat.zero_le i) hi | exact lvl_2 i (Nat.zero_le i) hi | exact lvl_3 i (Nat.zero_le i) hi | exact lvl_4 i (Nat.zero_le i) hi | exact lvl_5 i (Nat.zero_le i) hi | exact lvl_6 i (Nat.zero_le i) hi

private theorem impossibleState : ∀ s ≤ 6, ∀ i < 245, ∀ ws ∈ (rowsOf s).getD i [], ¬ RunD truthMask goal s ws := by
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
  (List.range 7).all (fun s => rootCheck s (inputSubsets.getD i []))

private theorem subsetCount : inputSubsets.length = 4096 := by decide +kernel

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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1024 : ∀ i, 1024 ≤ i → i < 1032 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1024 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1032 : ∀ i, 1032 ≤ i → i < 1040 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1032 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1040 : ∀ i, 1040 ≤ i → i < 1048 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1040 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1048 : ∀ i, 1048 ≤ i → i < 1056 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1048 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1056 : ∀ i, 1056 ≤ i → i < 1064 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1056 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1064 : ∀ i, 1064 ≤ i → i < 1072 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1064 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1072 : ∀ i, 1072 ≤ i → i < 1080 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1072 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1080 : ∀ i, 1080 ≤ i → i < 1088 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1080 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1088 : ∀ i, 1088 ≤ i → i < 1096 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1088 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1096 : ∀ i, 1096 ≤ i → i < 1104 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1096 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1104 : ∀ i, 1104 ≤ i → i < 1112 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1112 : ∀ i, 1112 ≤ i → i < 1120 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1120 : ∀ i, 1120 ≤ i → i < 1128 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1128 : ∀ i, 1128 ≤ i → i < 1136 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1136 : ∀ i, 1136 ≤ i → i < 1144 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1144 : ∀ i, 1144 ≤ i → i < 1152 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1152 : ∀ i, 1152 ≤ i → i < 1160 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1160 : ∀ i, 1160 ≤ i → i < 1168 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1168 : ∀ i, 1168 ≤ i → i < 1176 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1176 : ∀ i, 1176 ≤ i → i < 1184 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1184 : ∀ i, 1184 ≤ i → i < 1192 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1192 : ∀ i, 1192 ≤ i → i < 1200 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1200 : ∀ i, 1200 ≤ i → i < 1208 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1208 : ∀ i, 1208 ≤ i → i < 1216 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1216 : ∀ i, 1216 ≤ i → i < 1224 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1224 : ∀ i, 1224 ≤ i → i < 1232 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1232 : ∀ i, 1232 ≤ i → i < 1240 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1240 : ∀ i, 1240 ≤ i → i < 1248 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1248 : ∀ i, 1248 ≤ i → i < 1256 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1256 : ∀ i, 1256 ≤ i → i < 1264 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1264 : ∀ i, 1264 ≤ i → i < 1272 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1272 : ∀ i, 1272 ≤ i → i < 1280 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1280 : ∀ i, 1280 ≤ i → i < 1288 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1288 : ∀ i, 1288 ≤ i → i < 1296 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1296 : ∀ i, 1296 ≤ i → i < 1304 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1304 : ∀ i, 1304 ≤ i → i < 1312 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1312 : ∀ i, 1312 ≤ i → i < 1320 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1320 : ∀ i, 1320 ≤ i → i < 1328 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1328 : ∀ i, 1328 ≤ i → i < 1336 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1336 : ∀ i, 1336 ≤ i → i < 1344 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1344 : ∀ i, 1344 ≤ i → i < 1352 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1352 : ∀ i, 1352 ≤ i → i < 1360 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1360 : ∀ i, 1360 ≤ i → i < 1368 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1368 : ∀ i, 1368 ≤ i → i < 1376 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1376 : ∀ i, 1376 ≤ i → i < 1384 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1384 : ∀ i, 1384 ≤ i → i < 1392 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1392 : ∀ i, 1392 ≤ i → i < 1400 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1400 : ∀ i, 1400 ≤ i → i < 1408 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1408 : ∀ i, 1408 ≤ i → i < 1416 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1416 : ∀ i, 1416 ≤ i → i < 1424 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1424 : ∀ i, 1424 ≤ i → i < 1432 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1432 : ∀ i, 1432 ≤ i → i < 1440 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1440 : ∀ i, 1440 ≤ i → i < 1448 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1448 : ∀ i, 1448 ≤ i → i < 1456 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1456 : ∀ i, 1456 ≤ i → i < 1464 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1464 : ∀ i, 1464 ≤ i → i < 1472 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1472 : ∀ i, 1472 ≤ i → i < 1480 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1480 : ∀ i, 1480 ≤ i → i < 1488 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1488 : ∀ i, 1488 ≤ i → i < 1496 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1496 : ∀ i, 1496 ≤ i → i < 1504 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1504 : ∀ i, 1504 ≤ i → i < 1512 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1512 : ∀ i, 1512 ≤ i → i < 1520 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1520 : ∀ i, 1520 ≤ i → i < 1528 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1528 : ∀ i, 1528 ≤ i → i < 1536 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1536 : ∀ i, 1536 ≤ i → i < 1544 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1544 : ∀ i, 1544 ≤ i → i < 1552 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1552 : ∀ i, 1552 ≤ i → i < 1560 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1560 : ∀ i, 1560 ≤ i → i < 1568 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1568 : ∀ i, 1568 ≤ i → i < 1576 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1576 : ∀ i, 1576 ≤ i → i < 1584 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1584 : ∀ i, 1584 ≤ i → i < 1592 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1592 : ∀ i, 1592 ≤ i → i < 1600 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1600 : ∀ i, 1600 ≤ i → i < 1608 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1608 : ∀ i, 1608 ≤ i → i < 1616 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1616 : ∀ i, 1616 ≤ i → i < 1624 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1616 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1624 : ∀ i, 1624 ≤ i → i < 1632 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1632 : ∀ i, 1632 ≤ i → i < 1640 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1632 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1640 : ∀ i, 1640 ≤ i → i < 1648 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1648 : ∀ i, 1648 ≤ i → i < 1656 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1648 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1656 : ∀ i, 1656 ≤ i → i < 1664 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1664 : ∀ i, 1664 ≤ i → i < 1672 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1664 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1672 : ∀ i, 1672 ≤ i → i < 1680 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1680 : ∀ i, 1680 ≤ i → i < 1688 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1680 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1688 : ∀ i, 1688 ≤ i → i < 1696 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1696 : ∀ i, 1696 ≤ i → i < 1704 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1696 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1704 : ∀ i, 1704 ≤ i → i < 1712 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1712 : ∀ i, 1712 ≤ i → i < 1720 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1712 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1720 : ∀ i, 1720 ≤ i → i < 1728 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1728 : ∀ i, 1728 ≤ i → i < 1736 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1728 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1736 : ∀ i, 1736 ≤ i → i < 1744 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1736 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1744 : ∀ i, 1744 ≤ i → i < 1752 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1744 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1752 : ∀ i, 1752 ≤ i → i < 1760 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1752 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1760 : ∀ i, 1760 ≤ i → i < 1768 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1760 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1768 : ∀ i, 1768 ≤ i → i < 1776 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1768 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1776 : ∀ i, 1776 ≤ i → i < 1784 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1776 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1784 : ∀ i, 1784 ≤ i → i < 1792 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1784 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1792 : ∀ i, 1792 ≤ i → i < 1800 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1792 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1800 : ∀ i, 1800 ≤ i → i < 1808 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1800 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1808 : ∀ i, 1808 ≤ i → i < 1816 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1808 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1816 : ∀ i, 1816 ≤ i → i < 1824 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1816 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1824 : ∀ i, 1824 ≤ i → i < 1832 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1824 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1832 : ∀ i, 1832 ≤ i → i < 1840 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1832 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1840 : ∀ i, 1840 ≤ i → i < 1848 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1840 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1848 : ∀ i, 1848 ≤ i → i < 1856 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1848 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1856 : ∀ i, 1856 ≤ i → i < 1864 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1856 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1864 : ∀ i, 1864 ≤ i → i < 1872 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1864 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1872 : ∀ i, 1872 ≤ i → i < 1880 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1872 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1880 : ∀ i, 1880 ≤ i → i < 1888 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1880 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1888 : ∀ i, 1888 ≤ i → i < 1896 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1888 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1896 : ∀ i, 1896 ≤ i → i < 1904 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1896 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1904 : ∀ i, 1904 ≤ i → i < 1912 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1904 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1912 : ∀ i, 1912 ≤ i → i < 1920 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1912 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1920 : ∀ i, 1920 ≤ i → i < 1928 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1920 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1928 : ∀ i, 1928 ≤ i → i < 1936 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1928 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1936 : ∀ i, 1936 ≤ i → i < 1944 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1936 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1944 : ∀ i, 1944 ≤ i → i < 1952 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1944 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1952 : ∀ i, 1952 ≤ i → i < 1960 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1952 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1960 : ∀ i, 1960 ≤ i → i < 1968 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1960 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1968 : ∀ i, 1968 ≤ i → i < 1976 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1968 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1976 : ∀ i, 1976 ≤ i → i < 1984 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1976 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1984 : ∀ i, 1984 ≤ i → i < 1992 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1984 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_1992 : ∀ i, 1992 ≤ i → i < 2000 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 1992 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2000 : ∀ i, 2000 ≤ i → i < 2008 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2000 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2008 : ∀ i, 2008 ≤ i → i < 2016 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2008 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2016 : ∀ i, 2016 ≤ i → i < 2024 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2016 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2024 : ∀ i, 2024 ≤ i → i < 2032 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2024 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2032 : ∀ i, 2032 ≤ i → i < 2040 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2032 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2040 : ∀ i, 2040 ≤ i → i < 2048 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2040 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2048 : ∀ i, 2048 ≤ i → i < 2056 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2048 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2056 : ∀ i, 2056 ≤ i → i < 2064 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2056 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2064 : ∀ i, 2064 ≤ i → i < 2072 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2064 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2072 : ∀ i, 2072 ≤ i → i < 2080 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2072 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2080 : ∀ i, 2080 ≤ i → i < 2088 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2080 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2088 : ∀ i, 2088 ≤ i → i < 2096 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2088 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2096 : ∀ i, 2096 ≤ i → i < 2104 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2096 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2104 : ∀ i, 2104 ≤ i → i < 2112 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2112 : ∀ i, 2112 ≤ i → i < 2120 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2120 : ∀ i, 2120 ≤ i → i < 2128 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2128 : ∀ i, 2128 ≤ i → i < 2136 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2136 : ∀ i, 2136 ≤ i → i < 2144 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2144 : ∀ i, 2144 ≤ i → i < 2152 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2152 : ∀ i, 2152 ≤ i → i < 2160 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2160 : ∀ i, 2160 ≤ i → i < 2168 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2168 : ∀ i, 2168 ≤ i → i < 2176 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2176 : ∀ i, 2176 ≤ i → i < 2184 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2184 : ∀ i, 2184 ≤ i → i < 2192 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2192 : ∀ i, 2192 ≤ i → i < 2200 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2200 : ∀ i, 2200 ≤ i → i < 2208 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2208 : ∀ i, 2208 ≤ i → i < 2216 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2216 : ∀ i, 2216 ≤ i → i < 2224 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2224 : ∀ i, 2224 ≤ i → i < 2232 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2232 : ∀ i, 2232 ≤ i → i < 2240 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2240 : ∀ i, 2240 ≤ i → i < 2248 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2248 : ∀ i, 2248 ≤ i → i < 2256 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2256 : ∀ i, 2256 ≤ i → i < 2264 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2264 : ∀ i, 2264 ≤ i → i < 2272 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2272 : ∀ i, 2272 ≤ i → i < 2280 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2280 : ∀ i, 2280 ≤ i → i < 2288 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2288 : ∀ i, 2288 ≤ i → i < 2296 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2296 : ∀ i, 2296 ≤ i → i < 2304 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2304 : ∀ i, 2304 ≤ i → i < 2312 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2312 : ∀ i, 2312 ≤ i → i < 2320 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2320 : ∀ i, 2320 ≤ i → i < 2328 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2328 : ∀ i, 2328 ≤ i → i < 2336 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2336 : ∀ i, 2336 ≤ i → i < 2344 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2344 : ∀ i, 2344 ≤ i → i < 2352 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2352 : ∀ i, 2352 ≤ i → i < 2360 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2360 : ∀ i, 2360 ≤ i → i < 2368 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2368 : ∀ i, 2368 ≤ i → i < 2376 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2376 : ∀ i, 2376 ≤ i → i < 2384 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2384 : ∀ i, 2384 ≤ i → i < 2392 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2392 : ∀ i, 2392 ≤ i → i < 2400 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2400 : ∀ i, 2400 ≤ i → i < 2408 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2408 : ∀ i, 2408 ≤ i → i < 2416 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2416 : ∀ i, 2416 ≤ i → i < 2424 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2424 : ∀ i, 2424 ≤ i → i < 2432 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2432 : ∀ i, 2432 ≤ i → i < 2440 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2440 : ∀ i, 2440 ≤ i → i < 2448 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2448 : ∀ i, 2448 ≤ i → i < 2456 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2456 : ∀ i, 2456 ≤ i → i < 2464 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2464 : ∀ i, 2464 ≤ i → i < 2472 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2472 : ∀ i, 2472 ≤ i → i < 2480 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2480 : ∀ i, 2480 ≤ i → i < 2488 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2488 : ∀ i, 2488 ≤ i → i < 2496 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2496 : ∀ i, 2496 ≤ i → i < 2504 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2504 : ∀ i, 2504 ≤ i → i < 2512 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2512 : ∀ i, 2512 ≤ i → i < 2520 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2520 : ∀ i, 2520 ≤ i → i < 2528 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2528 : ∀ i, 2528 ≤ i → i < 2536 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2536 : ∀ i, 2536 ≤ i → i < 2544 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2544 : ∀ i, 2544 ≤ i → i < 2552 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2552 : ∀ i, 2552 ≤ i → i < 2560 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2560 : ∀ i, 2560 ≤ i → i < 2568 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2568 : ∀ i, 2568 ≤ i → i < 2576 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2576 : ∀ i, 2576 ≤ i → i < 2584 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2584 : ∀ i, 2584 ≤ i → i < 2592 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2592 : ∀ i, 2592 ≤ i → i < 2600 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2600 : ∀ i, 2600 ≤ i → i < 2608 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2608 : ∀ i, 2608 ≤ i → i < 2616 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2616 : ∀ i, 2616 ≤ i → i < 2624 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2616 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2624 : ∀ i, 2624 ≤ i → i < 2632 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2632 : ∀ i, 2632 ≤ i → i < 2640 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2632 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2640 : ∀ i, 2640 ≤ i → i < 2648 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2648 : ∀ i, 2648 ≤ i → i < 2656 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2648 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2656 : ∀ i, 2656 ≤ i → i < 2664 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2664 : ∀ i, 2664 ≤ i → i < 2672 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2664 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2672 : ∀ i, 2672 ≤ i → i < 2680 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2680 : ∀ i, 2680 ≤ i → i < 2688 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2680 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2688 : ∀ i, 2688 ≤ i → i < 2696 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2696 : ∀ i, 2696 ≤ i → i < 2704 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2696 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2704 : ∀ i, 2704 ≤ i → i < 2712 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2712 : ∀ i, 2712 ≤ i → i < 2720 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2712 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2720 : ∀ i, 2720 ≤ i → i < 2728 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2728 : ∀ i, 2728 ≤ i → i < 2736 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2728 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2736 : ∀ i, 2736 ≤ i → i < 2744 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2736 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2744 : ∀ i, 2744 ≤ i → i < 2752 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2744 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2752 : ∀ i, 2752 ≤ i → i < 2760 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2752 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2760 : ∀ i, 2760 ≤ i → i < 2768 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2760 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2768 : ∀ i, 2768 ≤ i → i < 2776 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2768 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2776 : ∀ i, 2776 ≤ i → i < 2784 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2776 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2784 : ∀ i, 2784 ≤ i → i < 2792 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2784 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2792 : ∀ i, 2792 ≤ i → i < 2800 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2792 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2800 : ∀ i, 2800 ≤ i → i < 2808 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2800 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2808 : ∀ i, 2808 ≤ i → i < 2816 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2808 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2816 : ∀ i, 2816 ≤ i → i < 2824 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2816 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2824 : ∀ i, 2824 ≤ i → i < 2832 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2824 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2832 : ∀ i, 2832 ≤ i → i < 2840 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2832 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2840 : ∀ i, 2840 ≤ i → i < 2848 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2840 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2848 : ∀ i, 2848 ≤ i → i < 2856 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2848 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2856 : ∀ i, 2856 ≤ i → i < 2864 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2856 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2864 : ∀ i, 2864 ≤ i → i < 2872 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2864 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2872 : ∀ i, 2872 ≤ i → i < 2880 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2872 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2880 : ∀ i, 2880 ≤ i → i < 2888 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2880 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2888 : ∀ i, 2888 ≤ i → i < 2896 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2888 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2896 : ∀ i, 2896 ≤ i → i < 2904 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2896 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2904 : ∀ i, 2904 ≤ i → i < 2912 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2904 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2912 : ∀ i, 2912 ≤ i → i < 2920 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2912 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2920 : ∀ i, 2920 ≤ i → i < 2928 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2920 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2928 : ∀ i, 2928 ≤ i → i < 2936 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2928 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2936 : ∀ i, 2936 ≤ i → i < 2944 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2936 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2944 : ∀ i, 2944 ≤ i → i < 2952 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2944 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2952 : ∀ i, 2952 ≤ i → i < 2960 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2952 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2960 : ∀ i, 2960 ≤ i → i < 2968 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2960 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2968 : ∀ i, 2968 ≤ i → i < 2976 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2968 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2976 : ∀ i, 2976 ≤ i → i < 2984 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2976 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2984 : ∀ i, 2984 ≤ i → i < 2992 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2984 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_2992 : ∀ i, 2992 ≤ i → i < 3000 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 2992 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3000 : ∀ i, 3000 ≤ i → i < 3008 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3000 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3008 : ∀ i, 3008 ≤ i → i < 3016 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3008 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3016 : ∀ i, 3016 ≤ i → i < 3024 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3016 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3024 : ∀ i, 3024 ≤ i → i < 3032 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3024 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3032 : ∀ i, 3032 ≤ i → i < 3040 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3032 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3040 : ∀ i, 3040 ≤ i → i < 3048 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3040 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3048 : ∀ i, 3048 ≤ i → i < 3056 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3048 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3056 : ∀ i, 3056 ≤ i → i < 3064 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3056 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3064 : ∀ i, 3064 ≤ i → i < 3072 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3064 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3072 : ∀ i, 3072 ≤ i → i < 3080 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3072 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3080 : ∀ i, 3080 ≤ i → i < 3088 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3080 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3088 : ∀ i, 3088 ≤ i → i < 3096 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3088 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3096 : ∀ i, 3096 ≤ i → i < 3104 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3096 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3104 : ∀ i, 3104 ≤ i → i < 3112 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3112 : ∀ i, 3112 ≤ i → i < 3120 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3120 : ∀ i, 3120 ≤ i → i < 3128 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3128 : ∀ i, 3128 ≤ i → i < 3136 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3136 : ∀ i, 3136 ≤ i → i < 3144 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3144 : ∀ i, 3144 ≤ i → i < 3152 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3152 : ∀ i, 3152 ≤ i → i < 3160 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3160 : ∀ i, 3160 ≤ i → i < 3168 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3168 : ∀ i, 3168 ≤ i → i < 3176 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3176 : ∀ i, 3176 ≤ i → i < 3184 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3184 : ∀ i, 3184 ≤ i → i < 3192 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3192 : ∀ i, 3192 ≤ i → i < 3200 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3200 : ∀ i, 3200 ≤ i → i < 3208 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3208 : ∀ i, 3208 ≤ i → i < 3216 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3216 : ∀ i, 3216 ≤ i → i < 3224 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3224 : ∀ i, 3224 ≤ i → i < 3232 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3232 : ∀ i, 3232 ≤ i → i < 3240 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3240 : ∀ i, 3240 ≤ i → i < 3248 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3248 : ∀ i, 3248 ≤ i → i < 3256 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3256 : ∀ i, 3256 ≤ i → i < 3264 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3264 : ∀ i, 3264 ≤ i → i < 3272 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3272 : ∀ i, 3272 ≤ i → i < 3280 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3280 : ∀ i, 3280 ≤ i → i < 3288 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3288 : ∀ i, 3288 ≤ i → i < 3296 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3296 : ∀ i, 3296 ≤ i → i < 3304 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3304 : ∀ i, 3304 ≤ i → i < 3312 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3312 : ∀ i, 3312 ≤ i → i < 3320 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3320 : ∀ i, 3320 ≤ i → i < 3328 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3328 : ∀ i, 3328 ≤ i → i < 3336 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3336 : ∀ i, 3336 ≤ i → i < 3344 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3344 : ∀ i, 3344 ≤ i → i < 3352 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3352 : ∀ i, 3352 ≤ i → i < 3360 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3360 : ∀ i, 3360 ≤ i → i < 3368 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3368 : ∀ i, 3368 ≤ i → i < 3376 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3376 : ∀ i, 3376 ≤ i → i < 3384 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3384 : ∀ i, 3384 ≤ i → i < 3392 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3392 : ∀ i, 3392 ≤ i → i < 3400 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3400 : ∀ i, 3400 ≤ i → i < 3408 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3408 : ∀ i, 3408 ≤ i → i < 3416 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3416 : ∀ i, 3416 ≤ i → i < 3424 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3424 : ∀ i, 3424 ≤ i → i < 3432 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3432 : ∀ i, 3432 ≤ i → i < 3440 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3440 : ∀ i, 3440 ≤ i → i < 3448 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3448 : ∀ i, 3448 ≤ i → i < 3456 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3456 : ∀ i, 3456 ≤ i → i < 3464 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3464 : ∀ i, 3464 ≤ i → i < 3472 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3472 : ∀ i, 3472 ≤ i → i < 3480 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3480 : ∀ i, 3480 ≤ i → i < 3488 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3488 : ∀ i, 3488 ≤ i → i < 3496 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3496 : ∀ i, 3496 ≤ i → i < 3504 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3504 : ∀ i, 3504 ≤ i → i < 3512 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3512 : ∀ i, 3512 ≤ i → i < 3520 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3520 : ∀ i, 3520 ≤ i → i < 3528 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3528 : ∀ i, 3528 ≤ i → i < 3536 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3536 : ∀ i, 3536 ≤ i → i < 3544 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3544 : ∀ i, 3544 ≤ i → i < 3552 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3552 : ∀ i, 3552 ≤ i → i < 3560 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3560 : ∀ i, 3560 ≤ i → i < 3568 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3568 : ∀ i, 3568 ≤ i → i < 3576 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3576 : ∀ i, 3576 ≤ i → i < 3584 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3584 : ∀ i, 3584 ≤ i → i < 3592 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3592 : ∀ i, 3592 ≤ i → i < 3600 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3600 : ∀ i, 3600 ≤ i → i < 3608 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3608 : ∀ i, 3608 ≤ i → i < 3616 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3616 : ∀ i, 3616 ≤ i → i < 3624 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3616 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3624 : ∀ i, 3624 ≤ i → i < 3632 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3632 : ∀ i, 3632 ≤ i → i < 3640 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3632 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3640 : ∀ i, 3640 ≤ i → i < 3648 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3648 : ∀ i, 3648 ≤ i → i < 3656 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3648 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3656 : ∀ i, 3656 ≤ i → i < 3664 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3664 : ∀ i, 3664 ≤ i → i < 3672 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3664 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3672 : ∀ i, 3672 ≤ i → i < 3680 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3680 : ∀ i, 3680 ≤ i → i < 3688 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3680 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3688 : ∀ i, 3688 ≤ i → i < 3696 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3696 : ∀ i, 3696 ≤ i → i < 3704 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3696 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3704 : ∀ i, 3704 ≤ i → i < 3712 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3712 : ∀ i, 3712 ≤ i → i < 3720 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3712 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3720 : ∀ i, 3720 ≤ i → i < 3728 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3728 : ∀ i, 3728 ≤ i → i < 3736 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3728 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3736 : ∀ i, 3736 ≤ i → i < 3744 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3736 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3744 : ∀ i, 3744 ≤ i → i < 3752 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3744 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3752 : ∀ i, 3752 ≤ i → i < 3760 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3752 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3760 : ∀ i, 3760 ≤ i → i < 3768 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3760 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3768 : ∀ i, 3768 ≤ i → i < 3776 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3768 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3776 : ∀ i, 3776 ≤ i → i < 3784 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3776 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3784 : ∀ i, 3784 ≤ i → i < 3792 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3784 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3792 : ∀ i, 3792 ≤ i → i < 3800 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3792 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3800 : ∀ i, 3800 ≤ i → i < 3808 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3800 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3808 : ∀ i, 3808 ≤ i → i < 3816 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3808 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3816 : ∀ i, 3816 ≤ i → i < 3824 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3816 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3824 : ∀ i, 3824 ≤ i → i < 3832 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3824 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3832 : ∀ i, 3832 ≤ i → i < 3840 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3832 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3840 : ∀ i, 3840 ≤ i → i < 3848 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3840 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3848 : ∀ i, 3848 ≤ i → i < 3856 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3848 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3856 : ∀ i, 3856 ≤ i → i < 3864 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3856 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3864 : ∀ i, 3864 ≤ i → i < 3872 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3864 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3872 : ∀ i, 3872 ≤ i → i < 3880 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3872 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3880 : ∀ i, 3880 ≤ i → i < 3888 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3880 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3888 : ∀ i, 3888 ≤ i → i < 3896 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3888 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3896 : ∀ i, 3896 ≤ i → i < 3904 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3896 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3904 : ∀ i, 3904 ≤ i → i < 3912 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3904 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3912 : ∀ i, 3912 ≤ i → i < 3920 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3912 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3920 : ∀ i, 3920 ≤ i → i < 3928 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3920 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3928 : ∀ i, 3928 ≤ i → i < 3936 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3928 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3936 : ∀ i, 3936 ≤ i → i < 3944 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3936 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3944 : ∀ i, 3944 ≤ i → i < 3952 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3944 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3952 : ∀ i, 3952 ≤ i → i < 3960 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3952 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3960 : ∀ i, 3960 ≤ i → i < 3968 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3960 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3968 : ∀ i, 3968 ≤ i → i < 3976 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3968 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3976 : ∀ i, 3976 ≤ i → i < 3984 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3976 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3984 : ∀ i, 3984 ≤ i → i < 3992 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3984 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_3992 : ∀ i, 3992 ≤ i → i < 4000 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 3992 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4000 : ∀ i, 4000 ≤ i → i < 4008 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4000 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4008 : ∀ i, 4008 ≤ i → i < 4016 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4008 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4016 : ∀ i, 4016 ≤ i → i < 4024 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4016 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4024 : ∀ i, 4024 ≤ i → i < 4032 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4024 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4032 : ∀ i, 4032 ≤ i → i < 4040 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4032 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4040 : ∀ i, 4040 ≤ i → i < 4048 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4040 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4048 : ∀ i, 4048 ≤ i → i < 4056 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4048 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4056 : ∀ i, 4056 ≤ i → i < 4064 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4056 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4064 : ∀ i, 4064 ≤ i → i < 4072 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4064 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4072 : ∀ i, 4072 ≤ i → i < 4080 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4072 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4080 : ∀ i, 4080 ≤ i → i < 4088 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4080 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rootBlock_4088 : ∀ i, 4088 ≤ i → i < 4096 → rootCheckAt i = true :=
  span_ok (by decide +kernel : span rootCheckAt 8 4088 = true)
private theorem checkedRoots : ∀ i, 0 ≤ i → i < 4096 → rootCheckAt i = true :=
  (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split rootBlock_0 rootBlock_8) (range_split rootBlock_16 rootBlock_24)) (range_split (range_split rootBlock_32 rootBlock_40) (range_split rootBlock_48 rootBlock_56))) (range_split (range_split (range_split rootBlock_64 rootBlock_72) (range_split rootBlock_80 rootBlock_88)) (range_split (range_split rootBlock_96 rootBlock_104) (range_split rootBlock_112 rootBlock_120)))) (range_split (range_split (range_split (range_split rootBlock_128 rootBlock_136) (range_split rootBlock_144 rootBlock_152)) (range_split (range_split rootBlock_160 rootBlock_168) (range_split rootBlock_176 rootBlock_184))) (range_split (range_split (range_split rootBlock_192 rootBlock_200) (range_split rootBlock_208 rootBlock_216)) (range_split (range_split rootBlock_224 rootBlock_232) (range_split rootBlock_240 rootBlock_248))))) (range_split (range_split (range_split (range_split (range_split rootBlock_256 rootBlock_264) (range_split rootBlock_272 rootBlock_280)) (range_split (range_split rootBlock_288 rootBlock_296) (range_split rootBlock_304 rootBlock_312))) (range_split (range_split (range_split rootBlock_320 rootBlock_328) (range_split rootBlock_336 rootBlock_344)) (range_split (range_split rootBlock_352 rootBlock_360) (range_split rootBlock_368 rootBlock_376)))) (range_split (range_split (range_split (range_split rootBlock_384 rootBlock_392) (range_split rootBlock_400 rootBlock_408)) (range_split (range_split rootBlock_416 rootBlock_424) (range_split rootBlock_432 rootBlock_440))) (range_split (range_split (range_split rootBlock_448 rootBlock_456) (range_split rootBlock_464 rootBlock_472)) (range_split (range_split rootBlock_480 rootBlock_488) (range_split rootBlock_496 rootBlock_504)))))) (range_split (range_split (range_split (range_split (range_split (range_split rootBlock_512 rootBlock_520) (range_split rootBlock_528 rootBlock_536)) (range_split (range_split rootBlock_544 rootBlock_552) (range_split rootBlock_560 rootBlock_568))) (range_split (range_split (range_split rootBlock_576 rootBlock_584) (range_split rootBlock_592 rootBlock_600)) (range_split (range_split rootBlock_608 rootBlock_616) (range_split rootBlock_624 rootBlock_632)))) (range_split (range_split (range_split (range_split rootBlock_640 rootBlock_648) (range_split rootBlock_656 rootBlock_664)) (range_split (range_split rootBlock_672 rootBlock_680) (range_split rootBlock_688 rootBlock_696))) (range_split (range_split (range_split rootBlock_704 rootBlock_712) (range_split rootBlock_720 rootBlock_728)) (range_split (range_split rootBlock_736 rootBlock_744) (range_split rootBlock_752 rootBlock_760))))) (range_split (range_split (range_split (range_split (range_split rootBlock_768 rootBlock_776) (range_split rootBlock_784 rootBlock_792)) (range_split (range_split rootBlock_800 rootBlock_808) (range_split rootBlock_816 rootBlock_824))) (range_split (range_split (range_split rootBlock_832 rootBlock_840) (range_split rootBlock_848 rootBlock_856)) (range_split (range_split rootBlock_864 rootBlock_872) (range_split rootBlock_880 rootBlock_888)))) (range_split (range_split (range_split (range_split rootBlock_896 rootBlock_904) (range_split rootBlock_912 rootBlock_920)) (range_split (range_split rootBlock_928 rootBlock_936) (range_split rootBlock_944 rootBlock_952))) (range_split (range_split (range_split rootBlock_960 rootBlock_968) (range_split rootBlock_976 rootBlock_984)) (range_split (range_split rootBlock_992 rootBlock_1000) (range_split rootBlock_1008 rootBlock_1016))))))) (range_split (range_split (range_split (range_split (range_split (range_split (range_split rootBlock_1024 rootBlock_1032) (range_split rootBlock_1040 rootBlock_1048)) (range_split (range_split rootBlock_1056 rootBlock_1064) (range_split rootBlock_1072 rootBlock_1080))) (range_split (range_split (range_split rootBlock_1088 rootBlock_1096) (range_split rootBlock_1104 rootBlock_1112)) (range_split (range_split rootBlock_1120 rootBlock_1128) (range_split rootBlock_1136 rootBlock_1144)))) (range_split (range_split (range_split (range_split rootBlock_1152 rootBlock_1160) (range_split rootBlock_1168 rootBlock_1176)) (range_split (range_split rootBlock_1184 rootBlock_1192) (range_split rootBlock_1200 rootBlock_1208))) (range_split (range_split (range_split rootBlock_1216 rootBlock_1224) (range_split rootBlock_1232 rootBlock_1240)) (range_split (range_split rootBlock_1248 rootBlock_1256) (range_split rootBlock_1264 rootBlock_1272))))) (range_split (range_split (range_split (range_split (range_split rootBlock_1280 rootBlock_1288) (range_split rootBlock_1296 rootBlock_1304)) (range_split (range_split rootBlock_1312 rootBlock_1320) (range_split rootBlock_1328 rootBlock_1336))) (range_split (range_split (range_split rootBlock_1344 rootBlock_1352) (range_split rootBlock_1360 rootBlock_1368)) (range_split (range_split rootBlock_1376 rootBlock_1384) (range_split rootBlock_1392 rootBlock_1400)))) (range_split (range_split (range_split (range_split rootBlock_1408 rootBlock_1416) (range_split rootBlock_1424 rootBlock_1432)) (range_split (range_split rootBlock_1440 rootBlock_1448) (range_split rootBlock_1456 rootBlock_1464))) (range_split (range_split (range_split rootBlock_1472 rootBlock_1480) (range_split rootBlock_1488 rootBlock_1496)) (range_split (range_split rootBlock_1504 rootBlock_1512) (range_split rootBlock_1520 rootBlock_1528)))))) (range_split (range_split (range_split (range_split (range_split (range_split rootBlock_1536 rootBlock_1544) (range_split rootBlock_1552 rootBlock_1560)) (range_split (range_split rootBlock_1568 rootBlock_1576) (range_split rootBlock_1584 rootBlock_1592))) (range_split (range_split (range_split rootBlock_1600 rootBlock_1608) (range_split rootBlock_1616 rootBlock_1624)) (range_split (range_split rootBlock_1632 rootBlock_1640) (range_split rootBlock_1648 rootBlock_1656)))) (range_split (range_split (range_split (range_split rootBlock_1664 rootBlock_1672) (range_split rootBlock_1680 rootBlock_1688)) (range_split (range_split rootBlock_1696 rootBlock_1704) (range_split rootBlock_1712 rootBlock_1720))) (range_split (range_split (range_split rootBlock_1728 rootBlock_1736) (range_split rootBlock_1744 rootBlock_1752)) (range_split (range_split rootBlock_1760 rootBlock_1768) (range_split rootBlock_1776 rootBlock_1784))))) (range_split (range_split (range_split (range_split (range_split rootBlock_1792 rootBlock_1800) (range_split rootBlock_1808 rootBlock_1816)) (range_split (range_split rootBlock_1824 rootBlock_1832) (range_split rootBlock_1840 rootBlock_1848))) (range_split (range_split (range_split rootBlock_1856 rootBlock_1864) (range_split rootBlock_1872 rootBlock_1880)) (range_split (range_split rootBlock_1888 rootBlock_1896) (range_split rootBlock_1904 rootBlock_1912)))) (range_split (range_split (range_split (range_split rootBlock_1920 rootBlock_1928) (range_split rootBlock_1936 rootBlock_1944)) (range_split (range_split rootBlock_1952 rootBlock_1960) (range_split rootBlock_1968 rootBlock_1976))) (range_split (range_split (range_split rootBlock_1984 rootBlock_1992) (range_split rootBlock_2000 rootBlock_2008)) (range_split (range_split rootBlock_2016 rootBlock_2024) (range_split rootBlock_2032 rootBlock_2040)))))))) (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split rootBlock_2048 rootBlock_2056) (range_split rootBlock_2064 rootBlock_2072)) (range_split (range_split rootBlock_2080 rootBlock_2088) (range_split rootBlock_2096 rootBlock_2104))) (range_split (range_split (range_split rootBlock_2112 rootBlock_2120) (range_split rootBlock_2128 rootBlock_2136)) (range_split (range_split rootBlock_2144 rootBlock_2152) (range_split rootBlock_2160 rootBlock_2168)))) (range_split (range_split (range_split (range_split rootBlock_2176 rootBlock_2184) (range_split rootBlock_2192 rootBlock_2200)) (range_split (range_split rootBlock_2208 rootBlock_2216) (range_split rootBlock_2224 rootBlock_2232))) (range_split (range_split (range_split rootBlock_2240 rootBlock_2248) (range_split rootBlock_2256 rootBlock_2264)) (range_split (range_split rootBlock_2272 rootBlock_2280) (range_split rootBlock_2288 rootBlock_2296))))) (range_split (range_split (range_split (range_split (range_split rootBlock_2304 rootBlock_2312) (range_split rootBlock_2320 rootBlock_2328)) (range_split (range_split rootBlock_2336 rootBlock_2344) (range_split rootBlock_2352 rootBlock_2360))) (range_split (range_split (range_split rootBlock_2368 rootBlock_2376) (range_split rootBlock_2384 rootBlock_2392)) (range_split (range_split rootBlock_2400 rootBlock_2408) (range_split rootBlock_2416 rootBlock_2424)))) (range_split (range_split (range_split (range_split rootBlock_2432 rootBlock_2440) (range_split rootBlock_2448 rootBlock_2456)) (range_split (range_split rootBlock_2464 rootBlock_2472) (range_split rootBlock_2480 rootBlock_2488))) (range_split (range_split (range_split rootBlock_2496 rootBlock_2504) (range_split rootBlock_2512 rootBlock_2520)) (range_split (range_split rootBlock_2528 rootBlock_2536) (range_split rootBlock_2544 rootBlock_2552)))))) (range_split (range_split (range_split (range_split (range_split (range_split rootBlock_2560 rootBlock_2568) (range_split rootBlock_2576 rootBlock_2584)) (range_split (range_split rootBlock_2592 rootBlock_2600) (range_split rootBlock_2608 rootBlock_2616))) (range_split (range_split (range_split rootBlock_2624 rootBlock_2632) (range_split rootBlock_2640 rootBlock_2648)) (range_split (range_split rootBlock_2656 rootBlock_2664) (range_split rootBlock_2672 rootBlock_2680)))) (range_split (range_split (range_split (range_split rootBlock_2688 rootBlock_2696) (range_split rootBlock_2704 rootBlock_2712)) (range_split (range_split rootBlock_2720 rootBlock_2728) (range_split rootBlock_2736 rootBlock_2744))) (range_split (range_split (range_split rootBlock_2752 rootBlock_2760) (range_split rootBlock_2768 rootBlock_2776)) (range_split (range_split rootBlock_2784 rootBlock_2792) (range_split rootBlock_2800 rootBlock_2808))))) (range_split (range_split (range_split (range_split (range_split rootBlock_2816 rootBlock_2824) (range_split rootBlock_2832 rootBlock_2840)) (range_split (range_split rootBlock_2848 rootBlock_2856) (range_split rootBlock_2864 rootBlock_2872))) (range_split (range_split (range_split rootBlock_2880 rootBlock_2888) (range_split rootBlock_2896 rootBlock_2904)) (range_split (range_split rootBlock_2912 rootBlock_2920) (range_split rootBlock_2928 rootBlock_2936)))) (range_split (range_split (range_split (range_split rootBlock_2944 rootBlock_2952) (range_split rootBlock_2960 rootBlock_2968)) (range_split (range_split rootBlock_2976 rootBlock_2984) (range_split rootBlock_2992 rootBlock_3000))) (range_split (range_split (range_split rootBlock_3008 rootBlock_3016) (range_split rootBlock_3024 rootBlock_3032)) (range_split (range_split rootBlock_3040 rootBlock_3048) (range_split rootBlock_3056 rootBlock_3064))))))) (range_split (range_split (range_split (range_split (range_split (range_split (range_split rootBlock_3072 rootBlock_3080) (range_split rootBlock_3088 rootBlock_3096)) (range_split (range_split rootBlock_3104 rootBlock_3112) (range_split rootBlock_3120 rootBlock_3128))) (range_split (range_split (range_split rootBlock_3136 rootBlock_3144) (range_split rootBlock_3152 rootBlock_3160)) (range_split (range_split rootBlock_3168 rootBlock_3176) (range_split rootBlock_3184 rootBlock_3192)))) (range_split (range_split (range_split (range_split rootBlock_3200 rootBlock_3208) (range_split rootBlock_3216 rootBlock_3224)) (range_split (range_split rootBlock_3232 rootBlock_3240) (range_split rootBlock_3248 rootBlock_3256))) (range_split (range_split (range_split rootBlock_3264 rootBlock_3272) (range_split rootBlock_3280 rootBlock_3288)) (range_split (range_split rootBlock_3296 rootBlock_3304) (range_split rootBlock_3312 rootBlock_3320))))) (range_split (range_split (range_split (range_split (range_split rootBlock_3328 rootBlock_3336) (range_split rootBlock_3344 rootBlock_3352)) (range_split (range_split rootBlock_3360 rootBlock_3368) (range_split rootBlock_3376 rootBlock_3384))) (range_split (range_split (range_split rootBlock_3392 rootBlock_3400) (range_split rootBlock_3408 rootBlock_3416)) (range_split (range_split rootBlock_3424 rootBlock_3432) (range_split rootBlock_3440 rootBlock_3448)))) (range_split (range_split (range_split (range_split rootBlock_3456 rootBlock_3464) (range_split rootBlock_3472 rootBlock_3480)) (range_split (range_split rootBlock_3488 rootBlock_3496) (range_split rootBlock_3504 rootBlock_3512))) (range_split (range_split (range_split rootBlock_3520 rootBlock_3528) (range_split rootBlock_3536 rootBlock_3544)) (range_split (range_split rootBlock_3552 rootBlock_3560) (range_split rootBlock_3568 rootBlock_3576)))))) (range_split (range_split (range_split (range_split (range_split (range_split rootBlock_3584 rootBlock_3592) (range_split rootBlock_3600 rootBlock_3608)) (range_split (range_split rootBlock_3616 rootBlock_3624) (range_split rootBlock_3632 rootBlock_3640))) (range_split (range_split (range_split rootBlock_3648 rootBlock_3656) (range_split rootBlock_3664 rootBlock_3672)) (range_split (range_split rootBlock_3680 rootBlock_3688) (range_split rootBlock_3696 rootBlock_3704)))) (range_split (range_split (range_split (range_split rootBlock_3712 rootBlock_3720) (range_split rootBlock_3728 rootBlock_3736)) (range_split (range_split rootBlock_3744 rootBlock_3752) (range_split rootBlock_3760 rootBlock_3768))) (range_split (range_split (range_split rootBlock_3776 rootBlock_3784) (range_split rootBlock_3792 rootBlock_3800)) (range_split (range_split rootBlock_3808 rootBlock_3816) (range_split rootBlock_3824 rootBlock_3832))))) (range_split (range_split (range_split (range_split (range_split rootBlock_3840 rootBlock_3848) (range_split rootBlock_3856 rootBlock_3864)) (range_split (range_split rootBlock_3872 rootBlock_3880) (range_split rootBlock_3888 rootBlock_3896))) (range_split (range_split (range_split rootBlock_3904 rootBlock_3912) (range_split rootBlock_3920 rootBlock_3928)) (range_split (range_split rootBlock_3936 rootBlock_3944) (range_split rootBlock_3952 rootBlock_3960)))) (range_split (range_split (range_split (range_split rootBlock_3968 rootBlock_3976) (range_split rootBlock_3984 rootBlock_3992)) (range_split (range_split rootBlock_4000 rootBlock_4008) (range_split rootBlock_4016 rootBlock_4024))) (range_split (range_split (range_split rootBlock_4032 rootBlock_4040) (range_split rootBlock_4048 rootBlock_4056)) (range_split (range_split rootBlock_4064 rootBlock_4072) (range_split rootBlock_4080 rootBlock_4088)))))))))

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
  obtain ⟨i', hi', zs, hzs, hr⟩ := sym_run hs hblocked hrun
  exact impossibleState s hs i' hi' zs hzs hr

private theorem rootsAgree : ∀ r : Fin 36,
    roots.map (·.testBit r.val) = PEqualNP.Represents.oneEach
      (Fin.ofNat 6 (r.val / 6)) (Fin.ofNat 6 (r.val % 6)) := by decide +kernel

private theorem domainRows : ∀ r : Fin 36, truthMask.testBit r.val = true := by decide +kernel
private theorem targetIndex : ∀ r : Fin 36, 6 * (r.val / 6) + (r.val % 6) = r.val := by decide

private theorem rulesOut (C : Circuit) (hfan : FanInTwo C) (hno : ∀ g ∈ C.gates, g.op = GateOp.not → NN) (hs : C.size ≤ 6)
    (hrep : PEqualNP.Represents.Represents
      (fun u v : Fin 6 => target.testBit (6 * u.val + v.val)) C) : False := by
  have hsup0 : ∀ v ∈ roots, Avail truthMask roots v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots hfan hno 0 roots roots rfl hsup0
  set out := (execN C.gates roots).getD C.output 0
  have hout : out &&& truthMask = target &&& truthMask := by
    apply Nat.eq_of_testBit_eq
    intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 36
    · rw [domainRows ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [rootsAgree ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots).map (·.testBit r)).getD C.output false = out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have hr5 : r / 6 < 6 := by omega
      have hcol : r % 6 < 6 := Nat.mod_lt _ (by decide)
      have hv := hrep (Fin.ofNat 6 (r / 6)) (Fin.ofNat 6 (r % 6))
      simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hr5, Nat.mod_eq_of_lt hcol] at hv
      rw [targetIndex ⟨r, hlt⟩] at hv
      exact h2.trans hv
    · have hd : truthMask.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h25 : truthMask < 2 ^ 36 := by decide
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
  have hz : C.gates.length ≤ 6 := hs
  exact impossibleRoot (by omega) hsub (Run.perm hp' hrun)

end PEqualNP.Outside.L_meta_25027

theorem PEqualNP.Outside.L_meta_25027 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => decide ((v : ℕ) < ![6, 6, 4, 4, 2, 2] u)) 7 ∧ ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => decide ((v : ℕ) < ![6, 6, 4, 4, 2, 2] u)) s → 7 ≤ s) := by
  refine ⟨?_, ?_⟩
  · refine ⟨(⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [6, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.Monotone2]
    · decide +kernel
  · intro s hsA
    by_contra hlt
    obtain ⟨C, hmono, hs0, hrep⟩ := hsA
    have hs : C.size ≤ 6 := by omega
    have hf : (fun u v : Fin 6 => decide ((v : ℕ) < ![6, 6, 4, 4, 2, 2] u)) = (fun u v : Fin 6 => (3275554815 : ℕ).testBit (6 * u.val + v.val)) := by
      funext u v
      revert u v
      decide
    rw [hf] at hrep
    have hfan : PEqualNP.MetaComplexity.FanInTwo C := fun g hg => ⟨by
      have h2 := (hmono g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2 ⊢
      rcases h2 with h | h <;> simp [h], (hmono g hg).2⟩
    have hno : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → PEqualNP.Outside.L_meta_25027.NN := by
      intro g hg h
      have h2 := (hmono g hg).1
      rw [h] at h2
      simp at h2
    exact PEqualNP.Outside.L_meta_25027.rulesOut C hfan hno hs hrep

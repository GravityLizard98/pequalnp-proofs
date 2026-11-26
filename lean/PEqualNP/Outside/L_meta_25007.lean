import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25007

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def S_dg : Gate := ⟨GateOp.or, []⟩

def S_stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def S_M2 (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem S_ifp {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem S_ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem S_len (gs : List Gate) (x : List Bool) : (gs.foldl S_stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, S_stp, ih]; omega

theorem S_getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem S_getD_last {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k = l.length) :
    (l ++ [b]).getD k d = b := by
  subst hk; simp [List.getD_eq_getElem?_getD]

theorem S_getD_left {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k < l.length) :
    (l ++ [b]).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem S_snoc_fold (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl S_stp x =
      gs.foldl S_stp x ++ [g.op.eval (g.inputs.map fun i => (gs.foldl S_stp x).getD i false)] := by
  simp [List.foldl_append, S_stp]

theorem S_pre (gs hs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length + gs.length) :
    ((gs ++ hs).foldl S_stp x).getD w false = (gs.foldl S_stp x).getD w false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, S_snoc_fold, S_getD_snoc, S_len, S_ifp (by simp; omega), ih]

theorem S_inp (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (gs.foldl S_stp x).getD w false = x.getD w false := by
  have := S_pre [] gs x w (by simpa using hw)
  simpa using this

theorem S_top (gs : List Gate) (g : Gate) (x : List Bool) :
    ((gs ++ [g]).foldl S_stp x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl S_stp x).getD i false) := by
  rw [S_snoc_fold, S_getD_snoc, S_len, S_ifn (by omega), S_ifp rfl]

theorem S_beyond (gs : List Gate) (x : List Bool) (w : ℕ) (hw : x.length + gs.length ≤ w) :
    (gs.foldl S_stp x).getD w false = false := by
  apply List.getD_eq_default
  rw [S_len]; exact hw

theorem S_wire_at (gs : List Gate) (x : List Bool) : ∀ i, i < gs.length →
    (gs.foldl S_stp x).getD (x.length + i) false =
      (gs.getD i S_dg).op.eval ((gs.getD i S_dg).inputs.map fun w =>
        if w < x.length + i then (gs.foldl S_stp x).getD w false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; simp at hi
  | append_singleton gs g ih =>
    intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases h : i < gs.length
    · rw [S_pre gs [g] x _ (by omega), ih i h, S_getD_left gs g S_dg i h]
      congr 1
      apply List.map_congr_left
      intro w _
      split_ifs with hw
      · rw [S_pre gs [g] x _ (by omega)]
      · rfl
    · have hi' : i = gs.length := by omega
      subst hi'
      rw [S_top, S_getD_last gs g S_dg _ rfl]
      congr 1
      apply List.map_congr_left
      intro w _
      split_ifs with hw
      · rw [S_pre gs [g] x _ hw]
      · rw [S_beyond gs x w (by omega)]

theorem S_oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega


def S_finv {a b : ℕ} (f : Fin a → Fin b) (i : Fin b) : Option (Fin a) :=
  (List.finRange a).find? (fun u => decide (f u = i))

theorem S_finv_some {a b : ℕ} (f : Fin a → Fin b) (i : Fin b) (u : Fin a) (h : S_finv f i = some u) :
    f u = i := by
  have := List.find?_some h
  exact of_decide_eq_true this

theorem S_finv_none {a b : ℕ} (f : Fin a → Fin b) (i : Fin b) (h : S_finv f i = none) (u : Fin a) :
    f u ≠ i := by
  unfold S_finv at h
  rw [List.find?_eq_none] at h
  have := h u (List.mem_finRange u)
  intro e
  exact this (decide_eq_true e)

def S_phi (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (S_finv f ⟨w, h⟩).elim B (fun u => u.val)
  else if h2 : w - n < m then (S_finv g ⟨w - n, h2⟩).elim B (fun v => n' + v.val)
  else n' + m' + (w - (n + m))

def S_mg (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (q : Gate) : Gate :=
  ⟨q.op, q.inputs.map (S_phi n m n' m' B f g)⟩

theorem S_phi_row (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (w : ℕ) (h : w < n) :
    S_phi n m n' m' B f g w = (S_finv f ⟨w, h⟩).elim B (fun u => u.val) := by
  unfold S_phi
  rw [dif_pos h]

theorem S_phi_col (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (w : ℕ) (h : ¬ w < n)
    (h2 : w - n < m) :
    S_phi n m n' m' B f g w = (S_finv g ⟨w - n, h2⟩).elim B (fun v => n' + v.val) := by
  unfold S_phi
  rw [dif_neg h, dif_pos h2]

theorem S_phi_big (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (w : ℕ) (h : n + m ≤ w) :
    S_phi n m n' m' B f g w = n' + m' + (w - (n + m)) := by
  unfold S_phi
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem S_phi_small (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (w : ℕ) (h : w < n + m) :
    S_phi n m n' m' B f g w < n' + m' ∨ S_phi n m n' m' B f g w = B := by
  by_cases h1 : w < n
  · rw [S_phi_row n m n' m' B f g w h1]
    cases hf : S_finv f ⟨w, h1⟩ with
    | none => exact Or.inr rfl
    | some u =>
      left
      show u.val < n' + m'
      have := u.isLt
      omega
  · have h2 : w - n < m := by omega
    rw [S_phi_col n m n' m' B f g w h1 h2]
    cases hf : S_finv g ⟨w - n, h2⟩ with
    | none => exact Or.inr rfl
    | some v =>
      left
      show n' + v.val < n' + m'
      have := v.isLt
      omega

theorem S_map_getD (n m n' m' B : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (gs : List Gate) (i : ℕ)
    (hi : i < gs.length) :
    (gs.map (S_mg n m n' m' B f g)).getD i S_dg = S_mg n m n' m' B f g (gs.getD i S_dg) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  rfl

theorem S_sim (n m n' m' : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (hf : Function.Injective f)
    (hg : Function.Injective g) (gs : List Gate) (u : Fin n') (v : Fin m') :
    ∀ w, ((gs.map (S_mg n m n' m' (n' + m' + gs.length) f g)).foldl S_stp (oneEach u v)).getD
        (S_phi n m n' m' (n' + m' + gs.length) f g w) false =
      (gs.foldl S_stp (oneEach (f u) (g v))).getD w false := by
  have hx : (oneEach u v).length = n' + m' := by simp [oneEach]
  have hx' : (oneEach (f u) (g v)).length = n + m := by simp [oneEach]
  have hB : ∀ (y : List Bool), y.length = n' + m' →
      ((gs.map (S_mg n m n' m' (n' + m' + gs.length) f g)).foldl S_stp y).getD (n' + m' + gs.length) false = false := by
    intro y hy
    exact S_beyond _ _ _ (by rw [List.length_map]; omega)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < n + m
    · rw [S_inp gs _ w (by omega)]
      by_cases h : w < n
      · rw [S_phi_row n m n' m' _ f g w h]
        cases hfi : S_finv f ⟨w, h⟩ with
        | none =>
          show _ = _
          simp only [Option.elim]
          rw [hB _ hx]
          symm
          rw [← Bool.not_eq_true, S_oe]
          rintro (q | q)
          · exact S_finv_none f _ hfi u (Fin.ext q.symm)
          · omega
        | some u2 =>
          simp only [Option.elim]
          have hu2 := u2.isLt
          have hfu := S_finv_some f _ u2 hfi
          have hfu' : (f u2).val = w := congrArg Fin.val hfu
          rw [S_inp _ _ _ (by omega), Bool.eq_iff_iff, S_oe, S_oe]
          constructor
          · rintro (q | q)
            · have : u2 = u := Fin.ext q
              rw [this] at hfu'
              exact Or.inl hfu'.symm
            · omega
          · rintro (q | q)
            · have : f u2 = f u := Fin.ext (by omega)
              exact Or.inl (congrArg Fin.val (hf this))
            · omega
      · have h2 : w - n < m := by omega
        rw [S_phi_col n m n' m' _ f g w h h2]
        cases hfi : S_finv g ⟨w - n, h2⟩ with
        | none =>
          simp only [Option.elim]
          rw [hB _ hx]
          symm
          rw [← Bool.not_eq_true, S_oe]
          rintro (q | q)
          · have := (f u).isLt
            omega
          · exact S_finv_none g _ hfi v (Fin.ext (by show (g v).val = w - n; omega))
        | some v2 =>
          simp only [Option.elim]
          have hv2 := v2.isLt
          have hfv := S_finv_some g _ v2 hfi
          have hfv' : (g v2).val = w - n := congrArg Fin.val hfv
          rw [S_inp _ _ _ (by omega), Bool.eq_iff_iff, S_oe, S_oe]
          have := (f u).isLt
          have := u.isLt
          constructor
          · rintro (q | q)
            · omega
            · have : v2 = v := Fin.ext (by omega)
              rw [this] at hfv'
              exact Or.inr (by omega)
          · rintro (q | q)
            · omega
            · have : g v2 = g v := Fin.ext (by omega)
              have := congrArg Fin.val (hg this)
              exact Or.inr (by omega)
    · rw [S_phi_big n m n' m' _ f g w (by omega)]
      by_cases h2 : n + m + gs.length ≤ w
      · rw [S_beyond _ _ _ (by rw [List.length_map]; omega), S_beyond _ _ _ (by omega)]
      · obtain ⟨i, rfl⟩ : ∃ i, w = n + m + i := ⟨w - (n + m), by omega⟩
        have hi : i < gs.length := by omega
        have ei : n + m + i - (n + m) = i := by omega
        rw [ei]
        have e1 := S_wire_at (gs.map (S_mg n m n' m' (n' + m' + gs.length) f g)) (oneEach u v) i
          (by rw [List.length_map]; exact hi)
        have e2 := S_wire_at gs (oneEach (f u) (g v)) i hi
        rw [hx] at e1
        rw [hx'] at e2
        rw [e1, e2, S_map_getD n m n' m' _ f g gs i hi]
        show (gs.getD i S_dg).op.eval (List.map _
          ((gs.getD i S_dg).inputs.map (S_phi n m n' m' (n' + m' + gs.length) f g))) = _
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro w' _
        show (if S_phi n m n' m' (n' + m' + gs.length) f g w' < n' + m' + i then
          ((gs.map (S_mg n m n' m' (n' + m' + gs.length) f g)).foldl S_stp (oneEach u v)).getD
            (S_phi n m n' m' (n' + m' + gs.length) f g w') false else false) = _
        by_cases hc : w' < n + m + i
        · rw [S_ifp hc, ← ih w' (by omega)]
          by_cases hp : S_phi n m n' m' (n' + m' + gs.length) f g w' < n' + m' + i
          · rw [S_ifp hp]
          · rw [S_ifn hp]
            by_cases hw' : w' < n + m
            · rcases S_phi_small n m n' m' (n' + m' + gs.length) f g w' hw' with q | q
              · omega
              · rw [q, hB _ hx]
            · rw [S_phi_big n m n' m' _ f g w' (by omega)] at hp
              omega
        · rw [S_ifn hc, S_phi_big n m n' m' _ f g w' (by omega), S_ifn (by omega)]

theorem S_main : ∀ (n m n' m' : ℕ) (A : Fin n → Fin m → Bool) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit), Function.Injective f → Function.Injective g → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ C.size ∧ PEqualNP.Represents.Represents (fun (u : Fin n') (v : Fin m') => A (f u) (g v)) C' := by
  intro n m n' m' A f g C hf hg hF hrep
  obtain ⟨gs, o⟩ := C
  refine ⟨⟨gs.map (S_mg n m n' m' (n' + m' + gs.length) f g),
    S_phi n m n' m' (n' + m' + gs.length) f g o⟩, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ gs.map (S_mg n m n' m' (n' + m' + gs.length) f g) at hq
    rw [List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    have := hF q0 hq0
    refine ⟨this.1, ?_⟩
    show (q0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact this.2
  · show (gs.map (S_mg n m n' m' (n' + m' + gs.length) f g)).length ≤ gs.length
    rw [List.length_map]
  · intro u v
    show ((gs.map (S_mg n m n' m' (n' + m' + gs.length) f g)).foldl S_stp (oneEach u v)).getD
      (S_phi n m n' m' (n' + m' + gs.length) f g o) false = A (f u) (g v)
    rw [S_sim n m n' m' f g hf hg gs u v o]
    exact hrep (f u) (g v)


def P_truthMask : Nat := 2 ^ 9 - 1

def P_negD (d w : Nat) : Nat := (w ^^^ P_truthMask) &&& d
def P_andD (d a b : Nat) : Nat := (a &&& b) &&& d
def P_orD (d a b : Nat) : Nat := (a ||| b) &&& d
def P_binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then P_orD d a b else P_andD d a b

def P_kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def P_RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      P_negD d a ≠ 0 → P_negD d a ≠ d → P_negD d a ∉ (a :: r) →
      P s (P_negD d a :: P_kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then P_andD d a b else P_orD d a b) ≠ 0 →
      (if c then P_andD d a b else P_orD d a b) ≠ d →
      (if c then P_andD d a b else P_orD d a b) ∉ (a :: b :: r) →
      P s ((if c then P_andD d a b else P_orD d a b) :: P_kept ka a (P_kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {d y : Nat}

theorem P_Run.done : P_RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem P_Run.perm {s xs zs} (p : List.Perm xs zs) (h : P_RunD d y s xs) :
    P_RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem P_Run.one {s a r} (save : Bool)
    (h0 : P_negD d a ≠ 0) (hd : P_negD d a ≠ d) (hm : P_negD d a ∉ (a :: r))
    (h : P_RunD d y s (P_negD d a :: P_kept save a r)) :
    P_RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem P_Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then P_andD d a b else P_orD d a b) ≠ 0)
    (hd : (if c then P_andD d a b else P_orD d a b) ≠ d)
    (hm : (if c then P_andD d a b else P_orD d a b) ∉ (a :: b :: r))
    (h : P_RunD d y s ((if c then P_andD d a b else P_orD d a b) :: P_kept ka a (P_kept kb b r))) :
    P_RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem P_Run.fold {P : ∀ t ws, P_RunD d y t ws → Prop}
    (done : P 0 [y] P_Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : P_RunD d y s xs),
      P s xs h → P s zs (P_Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : P_negD d a ≠ 0) (hd : P_negD d a ≠ d) (hm : P_negD d a ∉ (a :: r))
      (h : P_RunD d y s (P_negD d a :: P_kept save a r)),
      P _ _ h → P _ _ (P_Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then P_andD d a b else P_orD d a b) ≠ 0)
      (hd : (if c then P_andD d a b else P_orD d a b) ≠ d)
      (hm : (if c then P_andD d a b else P_orD d a b) ∉ (a :: b :: r))
      (h : P_RunD d y s ((if c then P_andD d a b else P_orD d a b) :: P_kept ka a (P_kept kb b r))),
      P _ _ h → P _ _ (P_Run.two c ka kb h0 hd hm h))
    {t ws} (h : P_RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : P_RunD d y s xs, P s xs h')
    ⟨P_Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨P_Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨P_Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨P_Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem P_mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ P_kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [P_kept]

theorem P_nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (P_kept b x xs).Nodup := by
  cases b
  · simpa [P_kept] using h
  · simpa [P_kept] using And.intro hx h

theorem P_keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (P_kept b a xs).Perm (P_kept b a ys) := by cases b <;> simpa [P_kept] using p

theorem P_run_len {d y s xs} (h : P_RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using P_Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [P_kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [P_kept] <;> omega

theorem P_zero_done {d y t ws} (h : P_RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using P_Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def P_IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def P_Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  P_IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def P_NatReach (d : Nat) (P_roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = P_roots
  | p + 1, bank =>
    (∃ b a, bank = P_negD d a :: b ∧ P_NatReach d P_roots p b ∧ P_Avail d b a) ∨
    (∃ b a c op, bank = P_binD d op a c :: b ∧ P_NatReach d P_roots p b ∧ P_Avail d b a ∧ P_Avail d b c)

theorem P_truthMask_bit (i : Nat) : P_truthMask.testBit i = decide (i < 9) := by
  rw [P_truthMask, Nat.testBit_two_pow_sub_one]

theorem P_negD_const {d : Nat} (hd : d &&& P_truthMask = d) {a : Nat} (hc : P_IsConst d a) :
    P_IsConst d (P_negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [P_negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [P_negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem P_binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : P_IsConst d a) :
    (P_binD d op a b &&& d = 0) ∨ (P_binD d op a b &&& d = d) ∨ (P_binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [P_binD, P_andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [P_binD, P_orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [P_binD, P_andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [P_binD, P_orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem P_binD_comm (d : Nat) (op : Bool) (a b : Nat) : P_binD d op a b = P_binD d op b a := by
  cases op <;> simp [P_binD, P_andD, P_orD, Nat.and_comm, Nat.or_comm]

theorem P_avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : P_Avail d bank w) :
    P_Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem P_avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : P_Avail d bank v) : P_Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem P_negD_mask (d a : Nat) : P_negD d (a &&& d) = P_negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [P_negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem P_andD_mask (d a b : Nat) : P_andD d (a &&& d) (b &&& d) = P_andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [P_andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem P_orD_mask (d a b : Nat) : P_orD d (a &&& d) (b &&& d) = P_orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [P_orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem P_pull_one {d Y k ws} (hd : d &&& P_truthMask = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : P_RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : P_Avail d b a) (hsub : ∀ w ∈ ws, w ∈ P_negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ P_RunD d Y k' ws' := by
  set z := P_negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ P_IsConst d a := by
        intro hc
        rcases P_negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, P_negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, P_negD, Nat.and_assoc, Nat.and_self] using h1)
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
      have ez : P_negD d a' = z := P_negD_mask d a
      have h1 : P_RunD d Y k (P_negD d a' :: rest) := by
        rw [ez]; exact P_Run.perm hp1 h
      have hne0 : P_negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : P_negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : P_RunD d Y k (P_negD d a' :: P_kept true a' (rest.erase a')) :=
          P_Run.perm (hp2.cons _) h1
        have hnm : P_negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact P_Run.perm hp2.symm (P_Run.one true hne0 hned hnm h2)
      · have h2 : P_RunD d Y k (P_negD d a' :: P_kept false a' rest) := h1
        have hnm : P_negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, P_Run.one false hne0 hned hnm h2⟩
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

theorem P_pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : P_RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : P_Avail d b a) (hc : P_Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ P_binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ P_RunD d Y k' ws' := by
  set z := P_binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, P_binD, P_andD, P_orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ P_IsConst d a := by
        intro hca
        rcases P_binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ P_IsConst d c := by
        intro hcc
        have hz' : z = P_binD d op c a := P_binD_comm d op a c
        rcases P_binD_const_left op hcc with h0 | h1 | he
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
          · simp only [z, P_binD, Bool.false_eq_true, ite_false]; rw [← P_andD_mask, ← heq]; simp [P_andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, P_binD, ite_true]; rw [← P_orD_mask, ← heq]; simp [P_orD, a', Nat.and_assoc, Nat.and_self]
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
      have ez : (if !op then P_andD d a' c' else P_orD d a' c') = z := by
        cases op
        · simp [z, P_binD, a', c', P_andD_mask]
        · simp [z, P_binD, a', c', P_orD_mask]
      have h1 : P_RunD d Y k ((if !op then P_andD d a' c' else P_orD d a' c') :: rest) := by
        rw [ez]; exact P_Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ P_kept kb c' tail := by
        rw [P_mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (P_kept ka a' (P_kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (P_nodup_kept ka a' _ (P_nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [P_mem_kept, P_mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := P_Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then P_andD d a' c' else P_orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then P_andD d a' c' else P_orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then P_andD d a' c' else P_orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : P_RunD d Y (k + 1) (a' :: c' :: tail) := P_Run.two (!op) ka kb hne0 hned hnm h2
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

theorem P_reach_to_run_aux {d : Nat} {P_roots : List Nat} {p bank} (hd : d &&& P_truthMask = d)
    (hr : P_NatReach d P_roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → P_RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ P_roots.map (· &&& d)) ∧ P_RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ P_negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, P_negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := P_pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ P_binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : P_binD d op a c &&& d = P_binD d op a c := by cases op <;> simp [P_binD, P_andD, P_orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := P_pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem P_reach_to_run {d : Nat} {P_roots : List Nat} {T : Nat} {p bank} (hd : d &&& P_truthMask = d)
    (hnc : ¬ P_IsConst d T) (hr : P_NatReach d P_roots p bank) (ha : P_Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ P_roots.map (· &&& d)) ∧ P_RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := P_reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub P_Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

theorem P_runD_bits {d y s ws} (hd : d &&& P_truthMask = d) (h : P_RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : P_truthMask.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : P_truthMask.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using P_Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [P_kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [P_negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [P_negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [P_kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [P_andD, P_orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem P_runD_bits_le {d y s ws} (h : P_RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using P_Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := P_run_len h; cases save <;> simp [P_kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := P_run_len h
    cases ka <;> cases kb <;> simp [P_kept] at hh hl <;> try omega
    apply ih (by simp [P_kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [P_kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [P_andD, P_orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem P_getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

def P_coversP (P_pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    P_pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    P_pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem P_coversP_ok {d T s : Nat} (hd : d &&& P_truthMask = d)
    (P_pairs : List (Nat × Nat))
    (hpairs : P_pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : P_RunD d (T &&& d) s ws) : P_coversP P_pairs s ws = true := by
  unfold P_coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := P_runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := P_runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def P_nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := P_negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then P_andD dm a b else P_orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem P_nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : P_negD dm a ≠ 0) (hd : P_negD dm a ≠ dm) (hnm : P_negD dm a ∉ (a :: rest))
    (h : P_RunD dm y s (P_negD dm a :: P_kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, P_RunD dm y s ys → f ys = true) :
    P_nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := P_run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [P_kept] at hh <;> omega
  have hnc : ws.contains (P_negD dm a) = false := by
    cases h : ws.contains (P_negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (P_negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (P_negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (P_Run.perm ((P_keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [P_kept] at ht; simp [ht]
  | true => simp [P_kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem P_nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then P_andD dm a b else P_orD dm a b) ≠ 0)
    (hd : (if conj then P_andD dm a b else P_orD dm a b) ≠ dm)
    (hnm : (if conj then P_andD dm a b else P_orD dm a b) ∉ (a :: b :: rest))
    (h : P_RunD dm y s ((if conj then P_andD dm a b else P_orD dm a b) :: P_kept ka a (P_kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, P_RunD dm y s ys → f ys = true) :
    P_nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := P_run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then P_andD dm a b else P_orD dm a b) = false := by
    cases h : ws.contains (if conj then P_andD dm a b else P_orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then P_andD dm a b else P_orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then P_andD dm a b else P_orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (P_Run.perm ((P_keep_perm (P_keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [P_kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem P_nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then P_andD dm a b else P_orD dm a b) ≠ 0)
    (hd : (if conj then P_andD dm a b else P_orD dm a b) ≠ dm)
    (hnm : (if conj then P_andD dm a b else P_orD dm a b) ∉ (a :: b :: rest))
    (h : P_RunD dm y s ((if conj then P_andD dm a b else P_orD dm a b) :: P_kept ka a (P_kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, P_RunD dm y s ys → f ys = true) :
    P_nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact P_nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then P_andD dm a b else P_orD dm a b) = (if conj then P_andD dm b a else P_orD dm b a) := by
      cases conj <;> simp [P_andD, P_orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then P_andD dm b a else P_orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply P_nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply P_Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [P_kept]; exact List.Perm.swap _ _ _

theorem P_nextD_complete {dm y t ws} (h : P_RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, P_RunD dm y s ys → f ys = true) →
      P_nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using P_Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact P_nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact P_nextD_two p h0 hd hnm h f hf

def P_span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && P_span f n (i + 1)

theorem P_span_ok {f n o} (h : P_span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [P_span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem P_range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def P_gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => P_andD P_truthMask (w.getD i 0) acc) P_truthMask
  | .or  => g.inputs.foldr (fun i acc => P_orD P_truthMask (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => P_truthMask | i :: _ => P_negD P_truthMask (w.getD i 0)
  | _ => 0

def P_execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [P_gvN l g]) w

theorem P_gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 9)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (P_gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : P_truthMask.testBit r = true := by simp [P_truthMask_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [P_gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, P_andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [P_gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, P_orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [P_gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, P_negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem P_execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 9)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (P_execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [P_execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [P_gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem P_execN_reach (gs : List Gate) (P_roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), P_NatReach P_truthMask P_roots p bank →
      (∀ v ∈ w, P_Avail P_truthMask bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ P_NatReach P_truthMask P_roots p' bank' ∧
        ∀ v ∈ P_execN gs w, P_Avail P_truthMask bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, P_Avail P_truthMask bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (P_getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))

    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ P_NatReach P_truthMask P_roots p1 bank1 ∧
        (∀ v ∈ w ++ [P_gvN w g], P_Avail P_truthMask bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, P_andD P_truthMask a P_truthMask &&& P_truthMask = a &&& P_truthMask := fun a => by
        simp [P_andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, P_orD P_truthMask a 0 &&& P_truthMask = a &&& P_truthMask := fun a => by
        simp [P_orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, P_Avail P_truthMask (z :: bank) v) := fun z v hv => P_avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [P_gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [P_gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact P_avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, P_binD P_truthMask false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [P_gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [P_binD, P_andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [P_gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [P_gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact P_avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, P_binD P_truthMask true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [P_gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [P_binD, P_orD]; cases P_truthMask.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [P_gvN, h, hgi]))⟩
        · refine ⟨p + 1, P_negD P_truthMask (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [P_gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def P_roots : List Nat := [7, 56, 448, 73, 146, 292]
def P_target : Nat := 433
def P_goal : Nat := P_target &&& P_truthMask

def P_pairs : List (Nat × Nat) := [(1, 4), (3, 4), (2, 0), (6, 0), (1, 8), (3, 7)]

def P_key (ws : List Nat) : Nat := ws.sum % 2

theorem P_key_lt (ws : List Nat) : P_key ws < 2 := Nat.mod_lt _ (by decide)

def P_rowsOf : Nat → List (List (List Nat))
  | 2 => [[[7, 73]], [[7, 438], [73, 504]]]
  | 3 => [[[7, 56, 73], [7, 73], [7, 73, 146], [7, 73, 292], [7, 73, 448]], [[7, 146, 292], [56, 73, 448]]]
  | _ => []

def P_listed (s : Nat) (ws : List Nat) : Bool := ((P_rowsOf s).getD (P_key ws) []).any (fun listedWs => ws.isPerm listedWs)

def P_blocked (s : Nat) (ws : List Nat) : Bool :=
  match s with
  | 0 => ws != [P_goal]
  | s + 1 => !(P_nextD P_truthMask (s + 2 - ws.length) ws
      (fun ys => P_coversP P_pairs s ys && !(P_listed s ys)))

private theorem P_validPairs :
    P_pairs.all (fun p => P_truthMask.testBit p.1 && P_truthMask.testBit p.2 &&
                      !P_goal.testBit p.1 && P_goal.testBit p.2) = true := by decide +kernel

def P_cellCheck (s i : Nat) : Bool := ((P_rowsOf s).getD i []).all (P_blocked s)

private theorem P_lvl_0 : ∀ i, 0 ≤ i → i < 2 → P_cellCheck 0 i = true := by
  intro i _ _
  simp [P_cellCheck, P_rowsOf]
private theorem P_lvl_1 : ∀ i, 0 ≤ i → i < 2 → P_cellCheck 1 i = true := by
  intro i _ _
  simp [P_cellCheck, P_rowsOf]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem P_cell_2_0 : ∀ i, 0 ≤ i → i < 2 → P_cellCheck 2 i = true :=
  P_span_ok (by decide +kernel : P_span (P_cellCheck 2) 2 0 = true)
private theorem P_lvl_2 : ∀ i, 0 ≤ i → i < 2 → P_cellCheck 2 i = true :=
  P_cell_2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem P_cell_3_0 : ∀ i, 0 ≤ i → i < 2 → P_cellCheck 3 i = true :=
  P_span_ok (by decide +kernel : P_span (P_cellCheck 3) 2 0 = true)
private theorem P_lvl_3 : ∀ i, 0 ≤ i → i < 2 → P_cellCheck 3 i = true :=
  P_cell_3_0

private theorem P_checkedCells (s : Nat) (hs : s ≤ 3) (i : Nat) (hi : i < 2) : P_cellCheck s i = true := by
  interval_cases s <;> first | exact P_lvl_0 i (Nat.zero_le i) hi | exact P_lvl_1 i (Nat.zero_le i) hi | exact P_lvl_2 i (Nat.zero_le i) hi | exact P_lvl_3 i (Nat.zero_le i) hi

private theorem P_impossibleState : ∀ s ≤ 3, ∀ i < 2, ∀ ws ∈ (P_rowsOf s).getD i [], ¬ P_RunD P_truthMask P_goal s ws := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi ws hw hrun
    have hc := List.all_eq_true.1 (show ((P_rowsOf s).getD i []).all (P_blocked s) = true from P_checkedCells s hs i hi) ws hw
    cases s with
    | zero => simp [P_blocked, P_zero_done hrun rfl] at hc
    | succ s =>
      have good (ys : List Nat) (h : P_RunD P_truthMask P_goal s ys) :
          (P_coversP P_pairs s ys && !(P_listed s ys)) = true := by
        have hcov := P_coversP_ok (by decide +kernel : P_truthMask &&& P_truthMask = P_truthMask) P_pairs P_validPairs h
        rw [hcov, Bool.true_and, Bool.not_eq_true', P_listed, List.any_eq_false]
        intro zs hzs
        by_contra! hb
        exact ih s (by omega) (by omega) (P_key ys) (P_key_lt ys) zs hzs (P_Run.perm (List.isPerm_iff.1 hb) h)
      have hn := P_nextD_complete hrun s rfl ws (List.Perm.refl _) _ good
      simp [P_blocked, hn] at hc

def P_rootCheck (s : Nat) (ws : List Nat) : Bool :=
  decide (s + 1 < ws.length) || !(P_coversP P_pairs s ws) || P_listed s ws

def P_inputSubsets : List (List Nat) := P_roots.sublists

def P_rootCheckAt (i : Nat) : Bool :=
  (List.range 4).all (fun s => P_rootCheck s (P_inputSubsets.getD i []))

private theorem P_subsetCount : P_inputSubsets.length = 64 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem P_rootBlock_0 : ∀ i, 0 ≤ i → i < 32 → P_rootCheckAt i = true :=
  P_span_ok (by decide +kernel : P_span P_rootCheckAt 32 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem P_rootBlock_32 : ∀ i, 32 ≤ i → i < 64 → P_rootCheckAt i = true :=
  P_span_ok (by decide +kernel : P_span P_rootCheckAt 32 32 = true)
private theorem P_checkedRoots : ∀ i, 0 ≤ i → i < 64 → P_rootCheckAt i = true :=
  (P_range_split P_rootBlock_0 P_rootBlock_32)

private theorem P_impossibleRoot {s : Nat} {ws : List Nat} (hs : s ≤ 3)
    (hsub : ws.Sublist P_roots) (hrun : P_RunD P_truthMask P_goal s ws) : False := by
  obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.1 (show ws ∈ P_inputSubsets from List.mem_sublists.2 hsub)
  have hc : P_rootCheck s ws = true := by
    have hv := P_checkedRoots i (Nat.zero_le i) (P_subsetCount ▸ hi)
    have hv' := List.all_eq_true.1 hv s (List.mem_range.2 (by omega))
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, h] using hv'
  have hcov := P_coversP_ok (by decide +kernel : P_truthMask &&& P_truthMask = P_truthMask) P_pairs P_validPairs hrun
  have hlen := P_run_len hrun
  have hblocked : P_listed s ws = true := by
    simpa [P_rootCheck, hcov, Nat.not_lt.mpr hlen] using hc
  obtain ⟨zs, hzs, hz⟩ := List.any_eq_true.1 hblocked
  exact P_impossibleState s hs (P_key ws) (P_key_lt ws) zs hzs (P_Run.perm (List.isPerm_iff.1 hz) hrun)

private theorem P_rootsAgree : ∀ r : Fin 9,
    P_roots.map (·.testBit r.val) = PEqualNP.Represents.oneEach
      (Fin.ofNat 3 (r.val / 3)) (Fin.ofNat 3 (r.val % 3)) := by decide +kernel

private theorem P_domainRows : ∀ r : Fin 9, P_truthMask.testBit r.val = true := by decide +kernel
private theorem P_targetIndex : ∀ r : Fin 9, 3 * (r.val / 3) + (r.val % 3) = r.val := by decide

private theorem P_rulesOut (C : Circuit) (hfan : FanInTwo C) (hs : C.size ≤ 3)
    (hrep : PEqualNP.Represents.Represents
      (fun u v : Fin 3 => P_target.testBit (3 * u.val + v.val)) C) : False := by
  have hsup0 : ∀ v ∈ P_roots, P_Avail P_truthMask P_roots v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := P_execN_reach C.gates P_roots hfan 0 P_roots P_roots rfl hsup0
  set out := (P_execN C.gates P_roots).getD C.output 0
  have hout : out &&& P_truthMask = P_target &&& P_truthMask := by
    apply Nat.eq_of_testBit_eq
    intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 9
    · rw [P_domainRows ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := P_execN_bit C.gates P_roots r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [P_rootsAgree ⟨r, hlt⟩] at h2
      have hgd : ((P_execN C.gates P_roots).map (·.testBit r)).getD C.output false = out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (P_execN C.gates P_roots)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have hr5 : r / 3 < 3 := by omega
      have hcol : r % 3 < 3 := Nat.mod_lt _ (by decide)
      have hv := hrep (Fin.ofNat 3 (r / 3)) (Fin.ofNat 3 (r % 3))
      simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hr5, Nat.mod_eq_of_lt hcol] at hv
      rw [P_targetIndex ⟨r, hlt⟩] at hv
      exact h2.trans hv
    · have hd : P_truthMask.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h25 : P_truthMask < 2 ^ 9 := by decide
        exact lt_of_lt_of_le h25 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : P_Avail P_truthMask bank out := by
    by_cases hi : C.output < (P_execN C.gates P_roots).length
    · exact hsup _ (P_getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]
      exact Or.inl (Or.inl (by simp))
  have hn : ¬ P_IsConst P_truthMask P_target := by unfold P_IsConst P_target P_truthMask; decide
  obtain ⟨s, ws, hsp, hnd, hrin, hrun⟩ :=
    P_reach_to_run (by decide +kernel : P_truthMask &&& P_truthMask = P_truthMask) hn hr (P_avail_of_eq hout hav_out)
  have hmask : P_roots.map (· &&& P_truthMask) = P_roots := by decide
  rw [hmask] at hrin
  have hrnd : P_roots.Nodup := by decide
  let sub := P_roots.filter (fun x => decide (x ∈ ws))
  have hsub : sub.Sublist P_roots := List.filter_sublist
  have hp' : ws.Perm sub := by
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hrnd)).2 ?_
    intro x
    simp only [sub, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hrin x hx, hx⟩, fun h => h.2⟩
  have hz : C.gates.length ≤ 3 := hs
  exact P_impossibleRoot (by omega) hsub (P_Run.perm hp' hrun)


def Q_truthMask : Nat := 2 ^ 9 - 1

def Q_negD (d w : Nat) : Nat := (w ^^^ Q_truthMask) &&& d
def Q_andD (d a b : Nat) : Nat := (a &&& b) &&& d
def Q_orD (d a b : Nat) : Nat := (a ||| b) &&& d
def Q_binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then Q_orD d a b else Q_andD d a b

def Q_kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Q_RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      Q_negD d a ≠ 0 → Q_negD d a ≠ d → Q_negD d a ∉ (a :: r) →
      P s (Q_negD d a :: Q_kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then Q_andD d a b else Q_orD d a b) ≠ 0 →
      (if c then Q_andD d a b else Q_orD d a b) ≠ d →
      (if c then Q_andD d a b else Q_orD d a b) ∉ (a :: b :: r) →
      P s ((if c then Q_andD d a b else Q_orD d a b) :: Q_kept ka a (Q_kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {d y : Nat}

theorem Q_Run.done : Q_RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem Q_Run.perm {s xs zs} (p : List.Perm xs zs) (h : Q_RunD d y s xs) :
    Q_RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem Q_Run.one {s a r} (save : Bool)
    (h0 : Q_negD d a ≠ 0) (hd : Q_negD d a ≠ d) (hm : Q_negD d a ∉ (a :: r))
    (h : Q_RunD d y s (Q_negD d a :: Q_kept save a r)) :
    Q_RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem Q_Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then Q_andD d a b else Q_orD d a b) ≠ 0)
    (hd : (if c then Q_andD d a b else Q_orD d a b) ≠ d)
    (hm : (if c then Q_andD d a b else Q_orD d a b) ∉ (a :: b :: r))
    (h : Q_RunD d y s ((if c then Q_andD d a b else Q_orD d a b) :: Q_kept ka a (Q_kept kb b r))) :
    Q_RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem Q_Run.fold {P : ∀ t ws, Q_RunD d y t ws → Prop}
    (done : P 0 [y] Q_Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Q_RunD d y s xs),
      P s xs h → P s zs (Q_Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : Q_negD d a ≠ 0) (hd : Q_negD d a ≠ d) (hm : Q_negD d a ∉ (a :: r))
      (h : Q_RunD d y s (Q_negD d a :: Q_kept save a r)),
      P _ _ h → P _ _ (Q_Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then Q_andD d a b else Q_orD d a b) ≠ 0)
      (hd : (if c then Q_andD d a b else Q_orD d a b) ≠ d)
      (hm : (if c then Q_andD d a b else Q_orD d a b) ∉ (a :: b :: r))
      (h : Q_RunD d y s ((if c then Q_andD d a b else Q_orD d a b) :: Q_kept ka a (Q_kept kb b r))),
      P _ _ h → P _ _ (Q_Run.two c ka kb h0 hd hm h))
    {t ws} (h : Q_RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Q_RunD d y s xs, P s xs h')
    ⟨Q_Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Q_Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨Q_Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨Q_Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem Q_mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ Q_kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [Q_kept]

theorem Q_nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (Q_kept b x xs).Nodup := by
  cases b
  · simpa [Q_kept] using h
  · simpa [Q_kept] using And.intro hx h

theorem Q_keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (Q_kept b a xs).Perm (Q_kept b a ys) := by cases b <;> simpa [Q_kept] using p

theorem Q_run_len {d y s xs} (h : Q_RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Q_Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [Q_kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [Q_kept] <;> omega

theorem Q_zero_done {d y t ws} (h : Q_RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Q_Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def Q_IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def Q_Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  Q_IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def Q_NatReach (d : Nat) (Q_roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = Q_roots
  | p + 1, bank =>
    (∃ b a, bank = Q_negD d a :: b ∧ Q_NatReach d Q_roots p b ∧ Q_Avail d b a) ∨
    (∃ b a c op, bank = Q_binD d op a c :: b ∧ Q_NatReach d Q_roots p b ∧ Q_Avail d b a ∧ Q_Avail d b c)

theorem Q_truthMask_bit (i : Nat) : Q_truthMask.testBit i = decide (i < 9) := by
  rw [Q_truthMask, Nat.testBit_two_pow_sub_one]

theorem Q_negD_const {d : Nat} (hd : d &&& Q_truthMask = d) {a : Nat} (hc : Q_IsConst d a) :
    Q_IsConst d (Q_negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [Q_negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [Q_negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem Q_binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : Q_IsConst d a) :
    (Q_binD d op a b &&& d = 0) ∨ (Q_binD d op a b &&& d = d) ∨ (Q_binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [Q_binD, Q_andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [Q_binD, Q_orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [Q_binD, Q_andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [Q_binD, Q_orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem Q_binD_comm (d : Nat) (op : Bool) (a b : Nat) : Q_binD d op a b = Q_binD d op b a := by
  cases op <;> simp [Q_binD, Q_andD, Q_orD, Nat.and_comm, Nat.or_comm]

theorem Q_avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Q_Avail d bank w) :
    Q_Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem Q_avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Q_Avail d bank v) : Q_Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem Q_negD_mask (d a : Nat) : Q_negD d (a &&& d) = Q_negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Q_negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem Q_andD_mask (d a b : Nat) : Q_andD d (a &&& d) (b &&& d) = Q_andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Q_andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem Q_orD_mask (d a b : Nat) : Q_orD d (a &&& d) (b &&& d) = Q_orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Q_orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem Q_pull_one {d Y k ws} (hd : d &&& Q_truthMask = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : Q_RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : Q_Avail d b a) (hsub : ∀ w ∈ ws, w ∈ Q_negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ Q_RunD d Y k' ws' := by
  set z := Q_negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ Q_IsConst d a := by
        intro hc
        rcases Q_negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, Q_negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, Q_negD, Nat.and_assoc, Nat.and_self] using h1)
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
      have ez : Q_negD d a' = z := Q_negD_mask d a
      have h1 : Q_RunD d Y k (Q_negD d a' :: rest) := by
        rw [ez]; exact Q_Run.perm hp1 h
      have hne0 : Q_negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : Q_negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : Q_RunD d Y k (Q_negD d a' :: Q_kept true a' (rest.erase a')) :=
          Q_Run.perm (hp2.cons _) h1
        have hnm : Q_negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact Q_Run.perm hp2.symm (Q_Run.one true hne0 hned hnm h2)
      · have h2 : Q_RunD d Y k (Q_negD d a' :: Q_kept false a' rest) := h1
        have hnm : Q_negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Q_Run.one false hne0 hned hnm h2⟩
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

theorem Q_pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : Q_RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : Q_Avail d b a) (hc : Q_Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ Q_binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ Q_RunD d Y k' ws' := by
  set z := Q_binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, Q_binD, Q_andD, Q_orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ Q_IsConst d a := by
        intro hca
        rcases Q_binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ Q_IsConst d c := by
        intro hcc
        have hz' : z = Q_binD d op c a := Q_binD_comm d op a c
        rcases Q_binD_const_left op hcc with h0 | h1 | he
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
          · simp only [z, Q_binD, Bool.false_eq_true, ite_false]; rw [← Q_andD_mask, ← heq]; simp [Q_andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, Q_binD, ite_true]; rw [← Q_orD_mask, ← heq]; simp [Q_orD, a', Nat.and_assoc, Nat.and_self]
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
      have ez : (if !op then Q_andD d a' c' else Q_orD d a' c') = z := by
        cases op
        · simp [z, Q_binD, a', c', Q_andD_mask]
        · simp [z, Q_binD, a', c', Q_orD_mask]
      have h1 : Q_RunD d Y k ((if !op then Q_andD d a' c' else Q_orD d a' c') :: rest) := by
        rw [ez]; exact Q_Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ Q_kept kb c' tail := by
        rw [Q_mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (Q_kept ka a' (Q_kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (Q_nodup_kept ka a' _ (Q_nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [Q_mem_kept, Q_mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := Q_Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then Q_andD d a' c' else Q_orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then Q_andD d a' c' else Q_orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then Q_andD d a' c' else Q_orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : Q_RunD d Y (k + 1) (a' :: c' :: tail) := Q_Run.two (!op) ka kb hne0 hned hnm h2
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

theorem Q_reach_to_run_aux {d : Nat} {Q_roots : List Nat} {p bank} (hd : d &&& Q_truthMask = d)
    (hr : Q_NatReach d Q_roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → Q_RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ Q_roots.map (· &&& d)) ∧ Q_RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ Q_negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, Q_negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := Q_pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ Q_binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : Q_binD d op a c &&& d = Q_binD d op a c := by cases op <;> simp [Q_binD, Q_andD, Q_orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := Q_pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem Q_reach_to_run {d : Nat} {Q_roots : List Nat} {T : Nat} {p bank} (hd : d &&& Q_truthMask = d)
    (hnc : ¬ Q_IsConst d T) (hr : Q_NatReach d Q_roots p bank) (ha : Q_Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ Q_roots.map (· &&& d)) ∧ Q_RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := Q_reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub Q_Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

theorem Q_runD_bits {d y s ws} (hd : d &&& Q_truthMask = d) (h : Q_RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : Q_truthMask.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : Q_truthMask.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Q_Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [Q_kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [Q_negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [Q_negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [Q_kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [Q_andD, Q_orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem Q_runD_bits_le {d y s ws} (h : Q_RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Q_Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := Q_run_len h; cases save <;> simp [Q_kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := Q_run_len h
    cases ka <;> cases kb <;> simp [Q_kept] at hh hl <;> try omega
    apply ih (by simp [Q_kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [Q_kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [Q_andD, Q_orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem Q_getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

def Q_coversP (Q_pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    Q_pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    Q_pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem Q_coversP_ok {d T s : Nat} (hd : d &&& Q_truthMask = d)
    (Q_pairs : List (Nat × Nat))
    (hpairs : Q_pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : Q_RunD d (T &&& d) s ws) : Q_coversP Q_pairs s ws = true := by
  unfold Q_coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := Q_runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := Q_runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def Q_nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := Q_negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then Q_andD dm a b else Q_orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem Q_nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : Q_negD dm a ≠ 0) (hd : Q_negD dm a ≠ dm) (hnm : Q_negD dm a ∉ (a :: rest))
    (h : Q_RunD dm y s (Q_negD dm a :: Q_kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, Q_RunD dm y s ys → f ys = true) :
    Q_nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := Q_run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [Q_kept] at hh <;> omega
  have hnc : ws.contains (Q_negD dm a) = false := by
    cases h : ws.contains (Q_negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (Q_negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (Q_negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Q_Run.perm ((Q_keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [Q_kept] at ht; simp [ht]
  | true => simp [Q_kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem Q_nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then Q_andD dm a b else Q_orD dm a b) ≠ 0)
    (hd : (if conj then Q_andD dm a b else Q_orD dm a b) ≠ dm)
    (hnm : (if conj then Q_andD dm a b else Q_orD dm a b) ∉ (a :: b :: rest))
    (h : Q_RunD dm y s ((if conj then Q_andD dm a b else Q_orD dm a b) :: Q_kept ka a (Q_kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, Q_RunD dm y s ys → f ys = true) :
    Q_nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := Q_run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then Q_andD dm a b else Q_orD dm a b) = false := by
    cases h : ws.contains (if conj then Q_andD dm a b else Q_orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then Q_andD dm a b else Q_orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then Q_andD dm a b else Q_orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Q_Run.perm ((Q_keep_perm (Q_keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [Q_kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem Q_nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then Q_andD dm a b else Q_orD dm a b) ≠ 0)
    (hd : (if conj then Q_andD dm a b else Q_orD dm a b) ≠ dm)
    (hnm : (if conj then Q_andD dm a b else Q_orD dm a b) ∉ (a :: b :: rest))
    (h : Q_RunD dm y s ((if conj then Q_andD dm a b else Q_orD dm a b) :: Q_kept ka a (Q_kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, Q_RunD dm y s ys → f ys = true) :
    Q_nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact Q_nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then Q_andD dm a b else Q_orD dm a b) = (if conj then Q_andD dm b a else Q_orD dm b a) := by
      cases conj <;> simp [Q_andD, Q_orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then Q_andD dm b a else Q_orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply Q_nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Q_Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [Q_kept]; exact List.Perm.swap _ _ _

theorem Q_nextD_complete {dm y t ws} (h : Q_RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, Q_RunD dm y s ys → f ys = true) →
      Q_nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using Q_Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact Q_nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact Q_nextD_two p h0 hd hnm h f hf

def Q_span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && Q_span f n (i + 1)

theorem Q_span_ok {f n o} (h : Q_span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [Q_span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem Q_range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def Q_gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => Q_andD Q_truthMask (w.getD i 0) acc) Q_truthMask
  | .or  => g.inputs.foldr (fun i acc => Q_orD Q_truthMask (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => Q_truthMask | i :: _ => Q_negD Q_truthMask (w.getD i 0)
  | _ => 0

def Q_execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [Q_gvN l g]) w

theorem Q_gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 9)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (Q_gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : Q_truthMask.testBit r = true := by simp [Q_truthMask_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [Q_gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, Q_andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [Q_gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, Q_orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [Q_gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, Q_negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem Q_execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 9)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (Q_execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [Q_execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [Q_gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem Q_execN_reach (gs : List Gate) (Q_roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), Q_NatReach Q_truthMask Q_roots p bank →
      (∀ v ∈ w, Q_Avail Q_truthMask bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ Q_NatReach Q_truthMask Q_roots p' bank' ∧
        ∀ v ∈ Q_execN gs w, Q_Avail Q_truthMask bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Q_Avail Q_truthMask bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (Q_getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))

    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ Q_NatReach Q_truthMask Q_roots p1 bank1 ∧
        (∀ v ∈ w ++ [Q_gvN w g], Q_Avail Q_truthMask bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, Q_andD Q_truthMask a Q_truthMask &&& Q_truthMask = a &&& Q_truthMask := fun a => by
        simp [Q_andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, Q_orD Q_truthMask a 0 &&& Q_truthMask = a &&& Q_truthMask := fun a => by
        simp [Q_orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Q_Avail Q_truthMask (z :: bank) v) := fun z v hv => Q_avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [Q_gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [Q_gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact Q_avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, Q_binD Q_truthMask false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [Q_gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [Q_binD, Q_andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [Q_gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [Q_gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact Q_avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, Q_binD Q_truthMask true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [Q_gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [Q_binD, Q_orD]; cases Q_truthMask.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [Q_gvN, h, hgi]))⟩
        · refine ⟨p + 1, Q_negD Q_truthMask (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [Q_gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def Q_roots : List Nat := [7, 56, 448, 73, 146, 292]
def Q_target : Nat := 291
def Q_goal : Nat := Q_target &&& Q_truthMask

def Q_pairs : List (Nat × Nat) := [(2, 0), (2, 5), (7, 1), (7, 8), (2, 1), (3, 0), (3, 5)]

def Q_key (ws : List Nat) : Nat := ws.sum % 2

theorem Q_key_lt (ws : List Nat) : Q_key ws < 2 := Nat.mod_lt _ (by decide)

def Q_rowsOf : Nat → List (List (List Nat))
  | 2 => [[[7, 219], [292, 504]], [[7, 292]]]
  | 3 => [[[7, 73, 146], [7, 73, 292], [56, 292, 448]], [[7, 56, 292], [7, 146, 292], [7, 292], [7, 292, 448]]]
  | _ => []

def Q_listed (s : Nat) (ws : List Nat) : Bool := ((Q_rowsOf s).getD (Q_key ws) []).any (fun listedWs => ws.isPerm listedWs)

def Q_blocked (s : Nat) (ws : List Nat) : Bool :=
  match s with
  | 0 => ws != [Q_goal]
  | s + 1 => !(Q_nextD Q_truthMask (s + 2 - ws.length) ws
      (fun ys => Q_coversP Q_pairs s ys && !(Q_listed s ys)))

private theorem Q_validPairs :
    Q_pairs.all (fun p => Q_truthMask.testBit p.1 && Q_truthMask.testBit p.2 &&
                      !Q_goal.testBit p.1 && Q_goal.testBit p.2) = true := by decide +kernel

def Q_cellCheck (s i : Nat) : Bool := ((Q_rowsOf s).getD i []).all (Q_blocked s)

private theorem Q_lvl_0 : ∀ i, 0 ≤ i → i < 2 → Q_cellCheck 0 i = true := by
  intro i _ _
  simp [Q_cellCheck, Q_rowsOf]
private theorem Q_lvl_1 : ∀ i, 0 ≤ i → i < 2 → Q_cellCheck 1 i = true := by
  intro i _ _
  simp [Q_cellCheck, Q_rowsOf]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem Q_cell_2_0 : ∀ i, 0 ≤ i → i < 2 → Q_cellCheck 2 i = true :=
  Q_span_ok (by decide +kernel : Q_span (Q_cellCheck 2) 2 0 = true)
private theorem Q_lvl_2 : ∀ i, 0 ≤ i → i < 2 → Q_cellCheck 2 i = true :=
  Q_cell_2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem Q_cell_3_0 : ∀ i, 0 ≤ i → i < 2 → Q_cellCheck 3 i = true :=
  Q_span_ok (by decide +kernel : Q_span (Q_cellCheck 3) 2 0 = true)
private theorem Q_lvl_3 : ∀ i, 0 ≤ i → i < 2 → Q_cellCheck 3 i = true :=
  Q_cell_3_0

private theorem Q_checkedCells (s : Nat) (hs : s ≤ 3) (i : Nat) (hi : i < 2) : Q_cellCheck s i = true := by
  interval_cases s <;> first | exact Q_lvl_0 i (Nat.zero_le i) hi | exact Q_lvl_1 i (Nat.zero_le i) hi | exact Q_lvl_2 i (Nat.zero_le i) hi | exact Q_lvl_3 i (Nat.zero_le i) hi

private theorem Q_impossibleState : ∀ s ≤ 3, ∀ i < 2, ∀ ws ∈ (Q_rowsOf s).getD i [], ¬ Q_RunD Q_truthMask Q_goal s ws := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi ws hw hrun
    have hc := List.all_eq_true.1 (show ((Q_rowsOf s).getD i []).all (Q_blocked s) = true from Q_checkedCells s hs i hi) ws hw
    cases s with
    | zero => simp [Q_blocked, Q_zero_done hrun rfl] at hc
    | succ s =>
      have good (ys : List Nat) (h : Q_RunD Q_truthMask Q_goal s ys) :
          (Q_coversP Q_pairs s ys && !(Q_listed s ys)) = true := by
        have hcov := Q_coversP_ok (by decide +kernel : Q_truthMask &&& Q_truthMask = Q_truthMask) Q_pairs Q_validPairs h
        rw [hcov, Bool.true_and, Bool.not_eq_true', Q_listed, List.any_eq_false]
        intro zs hzs
        by_contra! hb
        exact ih s (by omega) (by omega) (Q_key ys) (Q_key_lt ys) zs hzs (Q_Run.perm (List.isPerm_iff.1 hb) h)
      have hn := Q_nextD_complete hrun s rfl ws (List.Perm.refl _) _ good
      simp [Q_blocked, hn] at hc

def Q_rootCheck (s : Nat) (ws : List Nat) : Bool :=
  decide (s + 1 < ws.length) || !(Q_coversP Q_pairs s ws) || Q_listed s ws

def Q_inputSubsets : List (List Nat) := Q_roots.sublists

def Q_rootCheckAt (i : Nat) : Bool :=
  (List.range 4).all (fun s => Q_rootCheck s (Q_inputSubsets.getD i []))

private theorem Q_subsetCount : Q_inputSubsets.length = 64 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem Q_rootBlock_0 : ∀ i, 0 ≤ i → i < 32 → Q_rootCheckAt i = true :=
  Q_span_ok (by decide +kernel : Q_span Q_rootCheckAt 32 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem Q_rootBlock_32 : ∀ i, 32 ≤ i → i < 64 → Q_rootCheckAt i = true :=
  Q_span_ok (by decide +kernel : Q_span Q_rootCheckAt 32 32 = true)
private theorem Q_checkedRoots : ∀ i, 0 ≤ i → i < 64 → Q_rootCheckAt i = true :=
  (Q_range_split Q_rootBlock_0 Q_rootBlock_32)

private theorem Q_impossibleRoot {s : Nat} {ws : List Nat} (hs : s ≤ 3)
    (hsub : ws.Sublist Q_roots) (hrun : Q_RunD Q_truthMask Q_goal s ws) : False := by
  obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.1 (show ws ∈ Q_inputSubsets from List.mem_sublists.2 hsub)
  have hc : Q_rootCheck s ws = true := by
    have hv := Q_checkedRoots i (Nat.zero_le i) (Q_subsetCount ▸ hi)
    have hv' := List.all_eq_true.1 hv s (List.mem_range.2 (by omega))
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, h] using hv'
  have hcov := Q_coversP_ok (by decide +kernel : Q_truthMask &&& Q_truthMask = Q_truthMask) Q_pairs Q_validPairs hrun
  have hlen := Q_run_len hrun
  have hblocked : Q_listed s ws = true := by
    simpa [Q_rootCheck, hcov, Nat.not_lt.mpr hlen] using hc
  obtain ⟨zs, hzs, hz⟩ := List.any_eq_true.1 hblocked
  exact Q_impossibleState s hs (Q_key ws) (Q_key_lt ws) zs hzs (Q_Run.perm (List.isPerm_iff.1 hz) hrun)

private theorem Q_rootsAgree : ∀ r : Fin 9,
    Q_roots.map (·.testBit r.val) = PEqualNP.Represents.oneEach
      (Fin.ofNat 3 (r.val / 3)) (Fin.ofNat 3 (r.val % 3)) := by decide +kernel

private theorem Q_domainRows : ∀ r : Fin 9, Q_truthMask.testBit r.val = true := by decide +kernel
private theorem Q_targetIndex : ∀ r : Fin 9, 3 * (r.val / 3) + (r.val % 3) = r.val := by decide

private theorem Q_rulesOut (C : Circuit) (hfan : FanInTwo C) (hs : C.size ≤ 3)
    (hrep : PEqualNP.Represents.Represents
      (fun u v : Fin 3 => Q_target.testBit (3 * u.val + v.val)) C) : False := by
  have hsup0 : ∀ v ∈ Q_roots, Q_Avail Q_truthMask Q_roots v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := Q_execN_reach C.gates Q_roots hfan 0 Q_roots Q_roots rfl hsup0
  set out := (Q_execN C.gates Q_roots).getD C.output 0
  have hout : out &&& Q_truthMask = Q_target &&& Q_truthMask := by
    apply Nat.eq_of_testBit_eq
    intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 9
    · rw [Q_domainRows ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := Q_execN_bit C.gates Q_roots r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [Q_rootsAgree ⟨r, hlt⟩] at h2
      have hgd : ((Q_execN C.gates Q_roots).map (·.testBit r)).getD C.output false = out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (Q_execN C.gates Q_roots)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have hr5 : r / 3 < 3 := by omega
      have hcol : r % 3 < 3 := Nat.mod_lt _ (by decide)
      have hv := hrep (Fin.ofNat 3 (r / 3)) (Fin.ofNat 3 (r % 3))
      simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hr5, Nat.mod_eq_of_lt hcol] at hv
      rw [Q_targetIndex ⟨r, hlt⟩] at hv
      exact h2.trans hv
    · have hd : Q_truthMask.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h25 : Q_truthMask < 2 ^ 9 := by decide
        exact lt_of_lt_of_le h25 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Q_Avail Q_truthMask bank out := by
    by_cases hi : C.output < (Q_execN C.gates Q_roots).length
    · exact hsup _ (Q_getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]
      exact Or.inl (Or.inl (by simp))
  have hn : ¬ Q_IsConst Q_truthMask Q_target := by unfold Q_IsConst Q_target Q_truthMask; decide
  obtain ⟨s, ws, hsp, hnd, hrin, hrun⟩ :=
    Q_reach_to_run (by decide +kernel : Q_truthMask &&& Q_truthMask = Q_truthMask) hn hr (Q_avail_of_eq hout hav_out)
  have hmask : Q_roots.map (· &&& Q_truthMask) = Q_roots := by decide
  rw [hmask] at hrin
  have hrnd : Q_roots.Nodup := by decide
  let sub := Q_roots.filter (fun x => decide (x ∈ ws))
  have hsub : sub.Sublist Q_roots := List.filter_sublist
  have hp' : ws.Perm sub := by
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hrnd)).2 ?_
    intro x
    simp only [sub, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hrin x hx, hx⟩, fun h => h.2⟩
  have hz : C.gates.length ≤ 3 := hs
  exact Q_impossibleRoot (by omega) hsub (Q_Run.perm hp' hrun)

def pick {α : Type} (a b c : α) : Fin 3 → α := fun i => if i.val = 0 then a else if i.val = 1 then b else c

theorem pick_inj {α : Type} (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (pick a b c) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [pick]

theorem pick_dec (n : ℕ) (S : Finset (Fin n)) (a b c : Fin n) (i : Fin 3) :
    decide (pick a b c i ∈ S) = pick (decide (a ∈ S)) (decide (b ∈ S)) (decide (c ∈ S)) i := by
  unfold pick
  split_ifs <;> rfl

theorem xnor_eq (p q : Prop) [Decidable p] [Decidable q] :
    decide ((p ∧ q) ∨ (¬ p ∧ ¬ q)) = (decide p == decide q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem third (n : ℕ) (hn : 3 ≤ n) (a b : Fin n) : ∃ r : Fin n, r ≠ a ∧ r ≠ b := by
  by_cases h0 : (⟨0, by omega⟩ : Fin n) ≠ a ∧ (⟨0, by omega⟩ : Fin n) ≠ b
  · exact ⟨_, h0⟩
  · by_cases h1 : (⟨1, by omega⟩ : Fin n) ≠ a ∧ (⟨1, by omega⟩ : Fin n) ≠ b
    · exact ⟨_, h1⟩
    · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
      · intro h
        simp only [Fin.ext_iff, ne_eq, not_and_or, not_not] at h0 h1 h
        omega
      · intro h
        simp only [Fin.ext_iff, ne_eq, not_and_or, not_not] at h0 h1 h
        omega

theorem tab1 : ∀ i j : Fin 3, (pick true false false i == pick true false false j) =
    P_target.testBit (3 * i.val + j.val) := by decide

theorem tab1c : ∀ i j : Fin 3, (pick false true true i == pick false true true j) =
    P_target.testBit (3 * i.val + j.val) := by decide

theorem tab2 : ∀ i j : Fin 3, (pick true false false i == pick true true false j) =
    Q_target.testBit (3 * i.val + j.val) := by decide

theorem tab2c : ∀ i j : Fin 3, (pick false true true i == pick false false true j) =
    Q_target.testBit (3 * i.val + j.val) := by decide

theorem fin1 (n : ℕ) (S T : Finset (Fin n)) (C : Circuit) (hF : FanInTwo C) (hs : C.size ≤ 3)
    (hrep : Represents (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) C)
    (a b c d e f : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hde : d ≠ e) (hdf : d ≠ f)
    (hef : e ≠ f)
    (htab : ∀ i j : Fin 3, (pick (decide (a ∈ S)) (decide (b ∈ S)) (decide (c ∈ S)) i ==
      pick (decide (d ∈ T)) (decide (e ∈ T)) (decide (f ∈ T)) j) = P_target.testBit (3 * i.val + j.val)) :
    False := by
  obtain ⟨C', hF', hsz', hrep'⟩ := S_main n n 3 3 _ (pick a b c) (pick d e f) C
    (pick_inj a b c hab hac hbc) (pick_inj d e f hde hdf hef) hF hrep
  have hfun : (fun (u : Fin 3) (v : Fin 3) => decide ((pick a b c u ∈ S ∧ pick d e f v ∈ T) ∨
      (pick a b c u ∉ S ∧ pick d e f v ∉ T))) =
      (fun u v : Fin 3 => P_target.testBit (3 * u.val + v.val)) := by
    funext i j
    rw [xnor_eq, pick_dec, pick_dec]
    exact htab i j
  have hrep2 : Represents (fun u v : Fin 3 => P_target.testBit (3 * u.val + v.val)) C' := by
    rw [← hfun]
    exact hrep'
  exact P_rulesOut C' hF' (by omega) hrep2

theorem fin2 (n : ℕ) (S T : Finset (Fin n)) (C : Circuit) (hF : FanInTwo C) (hs : C.size ≤ 3)
    (hrep : Represents (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) C)
    (a b c d e f : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hde : d ≠ e) (hdf : d ≠ f)
    (hef : e ≠ f)
    (htab : ∀ i j : Fin 3, (pick (decide (a ∈ S)) (decide (b ∈ S)) (decide (c ∈ S)) i ==
      pick (decide (d ∈ T)) (decide (e ∈ T)) (decide (f ∈ T)) j) = Q_target.testBit (3 * i.val + j.val)) :
    False := by
  obtain ⟨C', hF', hsz', hrep'⟩ := S_main n n 3 3 _ (pick a b c) (pick d e f) C
    (pick_inj a b c hab hac hbc) (pick_inj d e f hde hdf hef) hF hrep
  have hfun : (fun (u : Fin 3) (v : Fin 3) => decide ((pick a b c u ∈ S ∧ pick d e f v ∈ T) ∨
      (pick a b c u ∉ S ∧ pick d e f v ∉ T))) =
      (fun u v : Fin 3 => Q_target.testBit (3 * u.val + v.val)) := by
    funext i j
    rw [xnor_eq, pick_dec, pick_dec]
    exact htab i j
  have hrep2 : Represents (fun u v : Fin 3 => Q_target.testBit (3 * u.val + v.val)) C' := by
    rw [← hfun]
    exact hrep'
  exact Q_rulesOut C' hF' (by omega) hrep2

theorem main : ∀ (n : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) C := by
  intro n S T hn hS hSc hT hTc hex
  obtain ⟨C, hF, hs, hrep⟩ := hex
  obtain ⟨s, hs1⟩ := hS
  obtain ⟨s', hs2⟩ := hSc
  obtain ⟨t, ht1⟩ := hT
  obtain ⟨t', ht2⟩ := hTc
  rw [Finset.mem_compl] at hs2 ht2
  have hss : s ≠ s' := fun h => hs2 (h ▸ hs1)
  have htt : t ≠ t' := fun h => ht2 (h ▸ ht1)
  obtain ⟨r, hr1, hr2⟩ := third n hn s s'
  obtain ⟨c, hc1, hc2⟩ := third n hn t t'
  have e1 : decide (s ∈ S) = true := decide_eq_true hs1
  have e2 : decide (s' ∈ S) = false := decide_eq_false hs2
  have e3 : decide (t ∈ T) = true := decide_eq_true ht1
  have e4 : decide (t' ∈ T) = false := decide_eq_false ht2
  by_cases hr : r ∈ S
  · have e5 : decide (r ∈ S) = true := decide_eq_true hr
    by_cases hc : c ∈ T
    · have e6 : decide (c ∈ T) = true := decide_eq_true hc
      exact fin1 n S T C hF hs hrep s' s r t' t c (Ne.symm hss) (Ne.symm hr2) (Ne.symm hr1)
        (Ne.symm htt) (Ne.symm hc2) (Ne.symm hc1) (by rw [e1, e2, e3, e4, e5, e6]; exact tab1c)
    · have e6 : decide (c ∈ T) = false := decide_eq_false hc
      exact fin2 n S T C hF hs hrep s' s r t' c t (Ne.symm hss) (Ne.symm hr2) (Ne.symm hr1)
        (Ne.symm hc2) (Ne.symm htt) hc1 (by rw [e1, e2, e3, e4, e5, e6]; exact tab2c)
  · have e5 : decide (r ∈ S) = false := decide_eq_false hr
    by_cases hc : c ∈ T
    · have e6 : decide (c ∈ T) = true := decide_eq_true hc
      exact fin2 n S T C hF hs hrep s s' r t c t' hss (Ne.symm hr1) (Ne.symm hr2)
        (Ne.symm hc1) htt hc2 (by rw [e1, e2, e3, e4, e5, e6]; exact tab2)
    · have e6 : decide (c ∈ T) = false := decide_eq_false hc
      exact fin1 n S T C hF hs hrep s s' r t t' c hss (Ne.symm hr1) (Ne.symm hr2)
        htt (Ne.symm hc1) (Ne.symm hc2) (by rw [e1, e2, e3, e4, e5, e6]; exact tab1)

end PEqualNP.Outside.L_meta_25007

theorem PEqualNP.Outside.L_meta_25007 : ∀ (n : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) C :=
  PEqualNP.Outside.L_meta_25007.main

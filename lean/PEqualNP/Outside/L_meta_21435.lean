import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21435

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def dg : Gate := ⟨GateOp.or, []⟩

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def M2 (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_last {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k = l.length) :
    (l ++ [b]).getD k d = b := by
  subst hk; simp [List.getD_eq_getElem?_getD]

theorem getD_left {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k < l.length) :
    (l ++ [b]).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem snoc_fold (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl stp x =
      gs.foldl stp x ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stp x).getD i false)] := by
  simp [List.foldl_append, stp]

theorem pre (gs hs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length + gs.length) :
    ((gs ++ hs).foldl stp x).getD w false = (gs.foldl stp x).getD w false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, snoc_fold, getD_snoc, len, ifp (by simp; omega), ih]

theorem inp (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (gs.foldl stp x).getD w false = x.getD w false := by
  have := pre [] gs x w (by simpa using hw)
  simpa using this

theorem top (gs : List Gate) (g : Gate) (x : List Bool) :
    ((gs ++ [g]).foldl stp x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl stp x).getD i false) := by
  rw [snoc_fold, getD_snoc, len, ifn (by omega), ifp rfl]

theorem beyond (gs : List Gate) (x : List Bool) (w : ℕ) (hw : x.length + gs.length ≤ w) :
    (gs.foldl stp x).getD w false = false := by
  apply List.getD_eq_default
  rw [len]; exact hw

theorem wire_at (gs : List Gate) (x : List Bool) : ∀ i, i < gs.length →
    (gs.foldl stp x).getD (x.length + i) false =
      (gs.getD i dg).op.eval ((gs.getD i dg).inputs.map fun w =>
        if w < x.length + i then (gs.foldl stp x).getD w false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; simp at hi
  | append_singleton gs g ih =>
    intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases h : i < gs.length
    · rw [pre gs [g] x _ (by omega), ih i h, getD_left gs g dg i h]
      congr 1
      apply List.map_congr_left
      intro w _
      split_ifs with hw
      · rw [pre gs [g] x _ (by omega)]
      · rfl
    · have hi' : i = gs.length := by omega
      subst hi'
      rw [top, getD_last gs g dg _ rfl]
      congr 1
      apply List.map_congr_left
      intro w _
      split_ifs with hw
      · rw [pre gs [g] x _ hw]
      · rw [beyond gs x w (by omega)]

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega


def interp (W : List Bool) (a : Sum Bool ℕ) : Bool := Sum.elim id (fun w => W.getD w false) a

def comb : GateOp → List (Sum Bool ℕ) → Sum (Sum Bool ℕ) Gate
  | GateOp.not, [] => Sum.inl (Sum.inl true)
  | GateOp.not, (Sum.inl c :: _) => Sum.inl (Sum.inl (!c))
  | GateOp.not, (Sum.inr w :: _) => Sum.inr ⟨GateOp.not, [w]⟩
  | GateOp.and, [] => Sum.inl (Sum.inl true)
  | GateOp.and, [a] => Sum.inl a
  | GateOp.and, [Sum.inl c, b] => if c then Sum.inl b else Sum.inl (Sum.inl false)
  | GateOp.and, [Sum.inr w, Sum.inl c] => if c then Sum.inl (Sum.inr w) else Sum.inl (Sum.inl false)
  | GateOp.and, [Sum.inr w, Sum.inr w'] => Sum.inr ⟨GateOp.and, [w, w']⟩
  | GateOp.or, [] => Sum.inl (Sum.inl false)
  | GateOp.or, [a] => Sum.inl a
  | GateOp.or, [Sum.inl c, b] => if c then Sum.inl (Sum.inl true) else Sum.inl b
  | GateOp.or, [Sum.inr w, Sum.inl c] => if c then Sum.inl (Sum.inl true) else Sum.inl (Sum.inr w)
  | GateOp.or, [Sum.inr w, Sum.inr w'] => Sum.inr ⟨GateOp.or, [w, w']⟩
  | _, _ => Sum.inl (Sum.inl false)

def Ar (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)

theorem comb_sem (op : GateOp) (r : List (Sum Bool ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hr : r.length ≤ 2) (W : List Bool) :
    (∀ a, comb op r = Sum.inl a → interp W a = op.eval (r.map (interp W)) ∧
      (∀ w, a = Sum.inr w → Sum.inr w ∈ r)) ∧
    (∀ g', comb op r = Sum.inr g' →
      g'.op.eval (g'.inputs.map (fun w => W.getD w false)) = op.eval (r.map (interp W)) ∧
      Ar g' ∧ ∀ w ∈ g'.inputs, Sum.inr w ∈ r) := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [comb, interp, GateOp.eval]
  · rcases hop with rfl | rfl | rfl <;> rcases a with ca | wa <;>
      simp [comb, interp, GateOp.eval, Ar]
  · rcases hop with rfl | rfl | rfl <;> rcases a with ca | wa <;> rcases b with cb | wb <;>
      (try cases ca) <;> (try cases cb) <;> simp [comb, interp, GateOp.eval, Ar]
  · simp at hr

def rin (res : List (Sum Bool ℕ)) (g : Gate) : List (Sum Bool ℕ) :=
  g.inputs.map (fun i => res.getD i (Sum.inl false))

def stepR (N : ℕ) (st : List Gate × List (Sum Bool ℕ)) (g : Gate) : List Gate × List (Sum Bool ℕ) :=
  Sum.elim (fun a => (st.1, st.2 ++ [a]))
    (fun g' => (st.1 ++ [g'], st.2 ++ [Sum.inr (N + st.1.length)])) (comb g.op (rin st.2 g))

def runR (N : ℕ) (gs : List Gate) : List Gate × List (Sum Bool ℕ) :=
  gs.foldl (stepR N) ([], (List.range N).map Sum.inr)

def PL (N : ℕ) (hs : List Gate) : Prop :=
  (∀ g ∈ hs, Ar g) ∧ ∀ j < hs.length, ∀ i ∈ (hs.getD j dg).inputs, i < N + j

def Inv (N : ℕ) (gs : List Gate) (st : List Gate × List (Sum Bool ℕ)) : Prop :=
  st.2.length = N + gs.length ∧ st.1.length ≤ gs.length ∧
  (∀ k w, st.2.getD k (Sum.inl false) = Sum.inr w → w < N + st.1.length) ∧
  PL N st.1 ∧
  ∀ x : List Bool, x.length = N → ∀ k,
    (gs.foldl stp x).getD k false = interp (st.1.foldl stp x) (st.2.getD k (Sum.inl false))

theorem rget (N k : ℕ) : ((List.range N).map (Sum.inr : ℕ → Sum Bool ℕ)).getD k (Sum.inl false) =
    if k < N then Sum.inr k else Sum.inl false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem interp_ext (W : List Bool) (b : Bool) (a : Sum Bool ℕ) (h : ∀ w, a = Sum.inr w → w < W.length) :
    interp (W ++ [b]) a = interp W a := by
  rcases a with c | w
  · rfl
  · exact getD_left W b false w (h w rfl)

theorem inv_run (N : ℕ) (gs : List Gate)
    (hF : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    Inv N gs (runR N gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [runR], Nat.le_refl _, ?_, ⟨fun g hg => by simp [runR] at hg, fun j hj => by simp [runR] at hj⟩, ?_⟩
    · intro k w h
      simp only [runR, List.foldl_nil] at h
      rw [rget] at h
      split_ifs at h with hk
      · have := Sum.inr.inj h
        simp only [runR, List.foldl_nil, List.length_nil]
        omega
    · intro x hx k
      simp only [runR, List.foldl_nil]
      rw [rget]
      split_ifs with hk
      · rfl
      · exact List.getD_eq_default _ _ (by omega)
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hF g' (List.mem_append_left _ hg'))
    obtain ⟨hop, hlen⟩ := hF g (by simp)
    have erun : runR N (gs ++ [g]) = stepR N (runR N gs) g := by
      unfold runR
      rw [List.foldl_append]
      rfl
    rw [erun]
    generalize runR N gs = st at ih'
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih'
    have hr : (rin st.2 g).length ≤ 2 := by
      unfold rin
      rw [List.length_map]
      exact hlen
    have semr : ∀ x : List Bool, x.length = N →
        g.op.eval (g.inputs.map (fun i => (gs.foldl stp x).getD i false)) =
          g.op.eval ((rin st.2 g).map (interp (st.1.foldl stp x))) := by
      intro x hx
      congr 1
      unfold rin
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact i5 x hx i
    have rmem : ∀ w, Sum.inr w ∈ rin st.2 g → w < N + st.1.length := by
      intro w hw
      unfold rin at hw
      rw [List.mem_map] at hw
      obtain ⟨i, _, hi⟩ := hw
      exact i3 i w hi
    have oldlt : ∀ (x : List Bool), x.length = N → ∀ k, k < N + gs.length →
        ((gs ++ [g]).foldl stp x).getD k false = (gs.foldl stp x).getD k false := by
      intro x hx k hk
      exact pre gs [g] x k (by omega)
    have oldtop : ∀ (x : List Bool), x.length = N →
        ((gs ++ [g]).foldl stp x).getD (N + gs.length) false =
          g.op.eval ((rin st.2 g).map (interp (st.1.foldl stp x))) := by
      intro x hx
      have := top gs g x
      rw [hx] at this
      rw [this, semr x hx]
    have oldgt : ∀ (x : List Bool), x.length = N → ∀ k, N + gs.length < k →
        ((gs ++ [g]).foldl stp x).getD k false = false := by
      intro x hx k hk
      exact beyond _ x k (by rw [List.length_append, List.length_singleton]; omega)
    cases hc : comb g.op (rin st.2 g) with
    | inl a =>
      have e : stepR N st g = (st.1, st.2 ++ [a]) := by
        unfold stepR
        rw [hc]
        rfl
      rw [e]
      refine ⟨by simp [i1]; omega, by simp; omega, ?_, i4, ?_⟩
      · intro k w h
        show w < N + st.1.length
        change (st.2 ++ [a]).getD k (Sum.inl false) = Sum.inr w at h
        by_cases hk : k < st.2.length
        · rw [getD_left _ _ _ _ hk] at h
          exact i3 k w h
        · by_cases hk2 : k = st.2.length
          · rw [getD_last _ _ _ _ hk2] at h
            exact rmem w (((comb_sem g.op _ hop hr []).1 a hc).2 w h)
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)] at h
            exact absurd h (by simp)
      · intro x hx k
        show _ = interp (st.1.foldl stp x) ((st.2 ++ [a]).getD k (Sum.inl false))
        by_cases hk : k < st.2.length
        · rw [getD_left _ _ _ _ hk, oldlt x hx k (by omega)]
          exact i5 x hx k
        · by_cases hk2 : k = st.2.length
          · rw [getD_last _ _ _ _ hk2, hk2, i1, oldtop x hx]
            exact (((comb_sem g.op _ hop hr _).1 a hc).1).symm
          · rw [List.getD_eq_default (st.2 ++ [a]) _
              (by rw [List.length_append, List.length_singleton]; omega), oldgt x hx k (by omega)]
            rfl
    | inr g' =>
      have e : stepR N st g = (st.1 ++ [g'], st.2 ++ [Sum.inr (N + st.1.length)]) := by
        unfold stepR
        rw [hc]
        rfl
      rw [e]
      have s23 := ((comb_sem g.op _ hop hr []).2 g' hc).2
      refine ⟨by simp [i1]; omega, by simp; omega, ?_, ⟨?_, ?_⟩, ?_⟩
      · intro k w h
        show w < N + (st.1 ++ [g']).length
        rw [List.length_append, List.length_singleton]
        change (st.2 ++ [Sum.inr (N + st.1.length)]).getD k (Sum.inl false) = Sum.inr w at h
        by_cases hk : k < st.2.length
        · rw [getD_left _ _ _ _ hk] at h
          have := i3 k w h
          omega
        · by_cases hk2 : k = st.2.length
          · rw [getD_last _ _ _ _ hk2] at h
            have := Sum.inr.inj h
            omega
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)] at h
            exact absurd h (by simp)
      · intro q hq
        change q ∈ st.1 ++ [g'] at hq
        rw [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact i4.1 q hq
        · exact s23.1
      · intro j hj i hi
        change j < (st.1 ++ [g']).length at hj
        rw [List.length_append, List.length_singleton] at hj
        change i ∈ ((st.1 ++ [g']).getD j dg).inputs at hi
        by_cases hj1 : j < st.1.length
        · rw [getD_left _ _ _ _ hj1] at hi
          exact i4.2 j hj1 i hi
        · have hj2 : j = st.1.length := by omega
          rw [getD_last _ _ _ _ hj2] at hi
          have := rmem i (s23.2 i hi)
          omega
      · intro x hx k
        show _ = interp ((st.1 ++ [g']).foldl stp x)
          ((st.2 ++ [Sum.inr (N + st.1.length)]).getD k (Sum.inl false))
        have hW : (st.1.foldl stp x).length = N + st.1.length := by rw [len, hx]
        rw [snoc_fold st.1 g' x]
        by_cases hk : k < st.2.length
        · rw [getD_left _ _ _ _ hk, oldlt x hx k (by omega),
            interp_ext _ _ _ (fun w hw => by rw [hW]; exact i3 k w hw)]
          exact i5 x hx k
        · by_cases hk2 : k = st.2.length
          · rw [getD_last _ _ _ _ hk2, hk2, i1, oldtop x hx]
            show _ = ((st.1.foldl stp x) ++ _).getD (N + st.1.length) false
            rw [getD_last _ _ _ _ hW.symm]
            exact (((comb_sem g.op _ hop hr _).2 g' hc).1).symm
          · rw [List.getD_eq_default (st.2 ++ [Sum.inr (N + st.1.length)]) _
              (by rw [List.length_append, List.length_singleton]; omega), oldgt x hx k (by omega)]
            rfl

theorem norm (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (hF : FanInTwo C)
    (hrep : Represents A C) :
    (∃ D : Circuit, PL (n + m) D.gates ∧ Represents A D ∧ D.gates.length ≤ C.gates.length) ∨
      (∃ c, ∀ u v, A u v = c) := by
  obtain ⟨gs, o⟩ := C
  have hF' : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hF g hg
    simpa [Set.mem_insert_iff] using this
  obtain ⟨i1, i2, i3, i4, i5⟩ := inv_run (n + m) gs hF'
  have hx : ∀ (u : Fin n) (v : Fin m), (oneEach u v).length = n + m := by
    intro u v
    simp [oneEach]
  have hev : ∀ (u : Fin n) (v : Fin m), (gs.foldl stp (oneEach u v)).getD o false = A u v :=
    fun u v => hrep u v
  cases ha : (runR (n + m) gs).2.getD o (Sum.inl false) with
  | inl c =>
    right
    refine ⟨c, fun u v => ?_⟩
    have := i5 (oneEach u v) (hx u v) o
    rw [ha, hev u v] at this
    exact this
  | inr w =>
    left
    refine ⟨⟨(runR (n + m) gs).1, w⟩, i4, fun u v => ?_, i2⟩
    have := i5 (oneEach u v) (hx u v) o
    rw [ha, hev u v] at this
    exact this.symm

def phi (N j s w : ℕ) : ℕ := if w < N + j then w else if w = N + j then N + s else w - 1

def mg (N j s : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi N j s)⟩

def hs (N j : ℕ) (gs : List Gate) : List Gate := (gs.eraseIdx j).map (mg N j gs.length)

theorem phi_lt (N j s w : ℕ) (h : w < N + j) : phi N j s w = w := by
  unfold phi; rw [ifp h]

theorem phi_gt (N j s w : ℕ) (h : N + j < w) : phi N j s w = w - 1 := by
  unfold phi; rw [ifn (by omega), ifn (by omega)]

theorem hs_len (N j : ℕ) (gs : List Gate) (hj : j < gs.length) : (hs N j gs).length + 1 = gs.length := by
  unfold hs
  rw [List.length_map, List.length_eraseIdx, ifp hj]
  omega

theorem hs_lt (N j : ℕ) (gs : List Gate) (i : ℕ) (hi : i < j) (hj : j < gs.length) :
    (hs N j gs).getD i dg = mg N j gs.length (gs.getD i dg) := by
  unfold hs
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eraseIdx, ifp hi, List.getElem?_eq_getElem (by omega)]
  rfl

theorem hs_ge (N j : ℕ) (gs : List Gate) (i : ℕ) (hi : j ≤ i) (hj : i + 1 < gs.length) :
    (hs N j gs).getD i dg = mg N j gs.length (gs.getD (i + 1) dg) := by
  unfold hs
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eraseIdx, ifn (by omega), List.getElem?_eq_getElem hj]
  rfl

theorem sim2 (N j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (hun : ∀ i < gs.length, N + j ∉ (gs.getD i dg).inputs) (x : List Bool) (hx : x.length = N) :
    ∀ w, w ≠ N + j → ((hs N j gs).foldl stp x).getD (phi N j gs.length w) false =
      (gs.foldl stp x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwj
    have hl1 := hs_len N j gs hj
    by_cases h1 : w < N
    · rw [phi_lt _ _ _ _ (by omega), inp _ _ _ (by omega), inp _ _ _ (by omega)]
    · by_cases h2 : N + gs.length ≤ w
      · rw [phi_gt _ _ _ _ (by omega), beyond _ _ _ (by omega), beyond _ _ _ (by omega)]
      · obtain ⟨i, rfl⟩ : ∃ i, w = N + i := ⟨w - N, by omega⟩
        by_cases h4 : i < j
        · rw [phi_lt _ _ _ _ (by omega)]
          have e1 := wire_at (hs N j gs) x i (by omega)
          have e2 := wire_at gs x i (by omega)
          rw [hx] at e1 e2
          rw [e1, e2, hs_lt N j gs i h4 hj]
          show (gs.getD i dg).op.eval (List.map _ ((gs.getD i dg).inputs.map (phi N j gs.length))) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro w' _
          show (if phi N j gs.length w' < N + i then
            ((hs N j gs).foldl stp x).getD (phi N j gs.length w') false else false) = _
          by_cases hc : w' < N + i
          · rw [ifp hc, ← ih w' (by omega) (by omega), phi_lt _ _ _ _ (by omega), ifp hc]
          · rw [ifn hc]
            by_cases hc1 : w' < N + j
            · rw [phi_lt _ _ _ _ hc1, ifn hc]
            · unfold phi
              rw [ifn hc1]
              split_ifs <;> first | rfl | omega
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
          rw [phi_gt _ _ _ _ (by omega)]
          have ek : N + (k + 1) - 1 = N + k := by omega
          rw [ek]
          have e1 := wire_at (hs N j gs) x k (by omega)
          have e2 := wire_at gs x (k + 1) (by omega)
          rw [hx] at e1 e2
          rw [e1, e2, hs_ge N j gs k (by omega) (by omega)]
          show (gs.getD (k + 1) dg).op.eval
            (List.map _ ((gs.getD (k + 1) dg).inputs.map (phi N j gs.length))) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro w' hw'
          show (if phi N j gs.length w' < N + k then
            ((hs N j gs).foldl stp x).getD (phi N j gs.length w') false else false) = _
          have hne : w' ≠ N + j := fun e => hun (k + 1) (by omega) (e ▸ hw')
          by_cases hc : w' < N + (k + 1)
          · rw [ifp hc, ← ih w' (by omega) hne]
            by_cases hc1 : w' < N + j
            · rw [phi_lt _ _ _ _ hc1, ifp (by omega)]
            · rw [phi_gt _ _ _ _ (by omega), ifp (by omega)]
          · rw [ifn hc, phi_gt _ _ _ _ (by omega), ifn (by omega)]

theorem hs_PL (N j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (hun : ∀ i < gs.length, N + j ∉ (gs.getD i dg).inputs) (hP : PL N gs) : PL N (hs N j gs) := by
  have hl1 := hs_len N j gs hj
  constructor
  · intro g hg
    unfold hs at hg
    rw [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hP.1 g0 (List.mem_of_mem_eraseIdx hg0)
    unfold Ar at this ⊢
    unfold mg
    simp only [List.length_map]
    exact this
  · intro i hi c hc
    by_cases h : i < j
    · rw [hs_lt N j gs i h hj] at hc
      unfold mg at hc
      simp only [List.mem_map] at hc
      obtain ⟨w', hw', rfl⟩ := hc
      have := hP.2 i (by omega) w' hw'
      rw [phi_lt _ _ _ _ (by omega)]
      exact this
    · rw [hs_ge N j gs i (by omega) (by omega)] at hc
      unfold mg at hc
      simp only [List.mem_map] at hc
      obtain ⟨w', hw', rfl⟩ := hc
      have := hP.2 (i + 1) (by omega) w' hw'
      have hne : w' ≠ N + j := fun e => hun (i + 1) (by omega) (e ▸ hw')
      by_cases hc1 : w' < N + j
      · rw [phi_lt _ _ _ _ hc1]; omega
      · rw [phi_gt _ _ _ _ (by omega)]; omega

theorem exmin (P : ℕ → Prop) : ∀ k, P k → ∃ m, P m ∧ ∀ k', P k' → m ≤ k' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h : ∀ k', P k' → k ≤ k'
    · exact ⟨k, hk, h⟩
    · obtain ⟨k', hk'⟩ := not_forall.1 h
      obtain ⟨hk1, hk2⟩ := Classical.not_imp.1 hk'
      exact ih k' (by omega) hk1

theorem crown_out (n : ℕ) (gs : List Gate) (o : ℕ)
    (hrep : Represents (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)) ⟨gs, o⟩) :
    n + n ≤ o := by
  have hout : ∀ u : Fin n, o ≠ u.val ∧ o ≠ n + u.val := by
    intro u
    have h := hrep u u
    have hx : (oneEach u u).length = n + n := by simp [oneEach]
    have hf : (gs.foldl stp (oneEach u u)).getD o false = false := by
      rw [show (gs.foldl stp (oneEach u u)).getD o false = (Circuit.mk gs o).eval (oneEach u u) from rfl, h]
      simp
    constructor
    · intro e
      rw [inp gs _ o (by omega)] at hf
      have := (oe u u o).2 (Or.inl e)
      rw [this] at hf
      exact Bool.noConfusion hf
    · intro e
      rw [inp gs _ o (by omega)] at hf
      have := (oe u u o).2 (Or.inr e)
      rw [this] at hf
      exact Bool.noConfusion hf
  by_contra hlt
  by_cases h : o < n
  · exact (hout ⟨o, h⟩).1 rfl
  · exact (hout ⟨o - n, by omega⟩).2 (by show o = n + (o - n); omega)

theorem crown_tt (n : ℕ) (hn : 3 ≤ n) :
    (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)) ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by
  show decide ((2 : ℕ) ≠ 0 ∧ (2 : ℕ) ≠ (0 + 1) % n) = true
  rw [decide_eq_true_iff, Nat.mod_eq_of_lt (by omega)]
  omega

theorem crown_ff (n : ℕ) (hn : 3 ≤ n) :
    (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)) ⟨0, by omega⟩ ⟨0, by omega⟩ = false := by
  show decide ((0 : ℕ) ≠ 0 ∧ (0 : ℕ) ≠ (0 + 1) % n) = false
  rw [decide_eq_false_iff_not]
  exact fun h => h.1 rfl

theorem main : ∀ (n : ℕ), 3 ≤ n → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
  PEqualNP.Represents.Represents (fun u1 v1 : Fin n => decide (v1.val ≠ u1.val ∧ v1.val ≠ (u1.val + 1) % n)) C →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
    PEqualNP.Represents.Represents (fun u2 v2 : Fin n => decide (v2.val ≠ u2.val ∧ v2.val ≠ (u2.val + 1) % n)) D ∧
    D.size ≤ C.size ∧
    (∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo E →
      PEqualNP.Represents.Represents (fun u3 v3 : Fin n => decide (v3.val ≠ u3.val ∧ v3.val ≠ (u3.val + 1) % n)) E →
      D.size ≤ E.size) ∧
    (∀ g ∈ D.gates,
      ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          g.inputs.length = 2) ∨
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) D ∧
    0 < D.size ∧ D.output + 1 = n + n + D.size ∧
    (∀ j < D.size,
      (PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) (n + n + j) = 0 ↔ j + 1 = D.size)) := by
  intro n hn C hF hrep
  have hnorm : ∀ E : Circuit, FanInTwo E →
      Represents (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)) E →
      ∃ D : Circuit, PL (n + n) D.gates ∧
        Represents (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)) D ∧
        D.gates.length ≤ E.gates.length := by
    intro E hE hr
    rcases norm n n _ E hE hr with h | ⟨c, hc⟩
    · exact h
    · exfalso
      have h1 := hc ⟨0, by omega⟩ ⟨2, by omega⟩
      have h2 := hc ⟨0, by omega⟩ ⟨0, by omega⟩
      have e1 : true = c := (crown_tt n hn).symm.trans h1
      have e2 : false = c := (crown_ff n hn).symm.trans h2
      rw [← e1] at e2
      exact Bool.noConfusion e2
  obtain ⟨D1, p1, r1, l1⟩ := hnorm C hF hrep
  obtain ⟨m0, ⟨D, hPL, hrepD, hsz⟩, hmin⟩ := exmin (fun k => ∃ D : Circuit, PL (n + n) D.gates ∧
      Represents (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)) D ∧
      D.gates.length = k) D1.gates.length ⟨D1, p1, r1, rfl⟩
  have hmin' : ∀ D' : Circuit, PL (n + n) D'.gates →
      Represents (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)) D' →
      D.gates.length ≤ D'.gates.length := by
    intro D' h1 h2
    rw [hsz]
    exact hmin _ ⟨D', h1, h2, rfl⟩
  obtain ⟨gs, o⟩ := D
  have hx : ∀ u v : Fin n, (oneEach u v).length = n + n := by
    intro u v
    simp [oneEach]
  have hev : ∀ u v : Fin n, (gs.foldl stp (oneEach u v)).getD o false =
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) := fun u v => hrepD u v
  have c1 : n + n ≤ o := crown_out n gs o hrepD
  have c2 : o < n + n + gs.length := by
    by_contra h
    have := hev ⟨0, by omega⟩ ⟨2, by omega⟩
    rw [beyond gs _ o (by rw [hx]; omega)] at this
    have h2 : true = false := (crown_tt n hn).symm.trans this.symm
    exact Bool.noConfusion h2
  have c3 : o + 1 = n + n + gs.length := by
    by_contra h
    have hne : gs ≠ [] := by
      intro e
      rw [e] at c2
      simp at c2
      omega
    obtain ⟨gs', g, rfl⟩ : ∃ gs' g, gs = gs' ++ [g] :=
      ⟨gs.dropLast, gs.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    rw [List.length_append, List.length_singleton] at c2 h
    have := hmin' ⟨gs', o⟩
      ⟨fun q hq => hPL.1 q (List.mem_append_left _ hq), fun j hj i hi => by
        have hj' : j < gs'.length := hj
        have := hPL.2 j (by show j < (gs' ++ [g]).length; rw [List.length_append, List.length_singleton]; omega) i
          (by
            show i ∈ ((gs' ++ [g]).getD j dg).inputs
            rw [getD_left gs' g dg j hj']
            exact hi)
        exact this⟩
      (fun u v => by
        show (gs'.foldl stp (oneEach u v)).getD o false = decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)
        rw [← hev u v]
        exact (pre gs' [g] (oneEach u v) o (by rw [hx]; omega)).symm)
    have : (gs' ++ [g]).length ≤ gs'.length := this
    rw [List.length_append, List.length_singleton] at this
    omega
  have c4 : ∀ j, j + 1 < gs.length → ∃ i, i < gs.length ∧ n + n + j ∈ (gs.getD i dg).inputs := by
    intro j hj
    by_contra hno
    have hun : ∀ i < gs.length, n + n + j ∉ (gs.getD i dg).inputs :=
      fun i hi hm => hno ⟨i, hi, hm⟩
    have hl := hs_len (n + n) j gs (by omega)
    have := hmin' ⟨hs (n + n) j gs, phi (n + n) j gs.length o⟩
      (hs_PL (n + n) j gs (by omega) hun hPL)
      (fun u v => by
        show ((hs (n + n) j gs).foldl stp (oneEach u v)).getD (phi (n + n) j gs.length o) false =
          decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)
        rw [← hev u v]
        exact sim2 (n + n) j gs (by omega) hun (oneEach u v) (hx u v) o (by omega))
    have : gs.length ≤ (hs (n + n) j gs).length := this
    omega
  refine ⟨⟨gs, o⟩, ?_, hrepD, ?_, ?_, fun g hg => hPL.1 g hg, hPL.2, ?_, c3, ?_⟩
  · intro g hg
    rcases hPL.1 g hg with ⟨h | h, hl⟩ | ⟨h, hl⟩
    · exact ⟨by rw [h]; simp, by omega⟩
    · exact ⟨by rw [h]; simp, by omega⟩
    · exact ⟨by rw [h]; simp, by omega⟩
  · exact le_trans (hmin' D1 p1 r1) l1
  · intro E hE hr
    obtain ⟨D2, p2, r2, l2⟩ := hnorm E hE hr
    exact le_trans (hmin' D2 p2 r2) l2
  · show 0 < gs.length
    omega
  · intro j hj
    have hj' : j < gs.length := hj
    show (∑ i ∈ Finset.range gs.length, (gs.getD i dg).inputs.count (n + n + j)) = 0 ↔
      j + 1 = gs.length
    constructor
    · intro h0
      by_contra hne
      obtain ⟨i, hi, hm⟩ := c4 j (by omega)
      have hle := Finset.single_le_sum (f := fun i => ((gs.getD i dg).inputs.count (n + n + j)))
        (fun i _ => Nat.zero_le _) (Finset.mem_range.2 hi)
      have p1 : 0 < (gs.getD i dg).inputs.count (n + n + j) := List.count_pos_iff.2 hm
      omega
    · intro hlast
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      apply List.count_eq_zero.2
      intro hm
      have := hPL.2 i hi _ hm
      omega

end PEqualNP.Outside.L_meta_21435

theorem PEqualNP.Outside.L_meta_21435 : ∀ (n : ℕ), 3 ≤ n → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
  PEqualNP.Represents.Represents (fun u1 v1 : Fin n => decide (v1.val ≠ u1.val ∧ v1.val ≠ (u1.val + 1) % n)) C →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
    PEqualNP.Represents.Represents (fun u2 v2 : Fin n => decide (v2.val ≠ u2.val ∧ v2.val ≠ (u2.val + 1) % n)) D ∧
    D.size ≤ C.size ∧
    (∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo E →
      PEqualNP.Represents.Represents (fun u3 v3 : Fin n => decide (v3.val ≠ u3.val ∧ v3.val ≠ (u3.val + 1) % n)) E →
      D.size ≤ E.size) ∧
    (∀ g ∈ D.gates,
      ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          g.inputs.length = 2) ∨
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) D ∧
    0 < D.size ∧ D.output + 1 = n + n + D.size ∧
    (∀ j < D.size,
      (PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) (n + n + j) = 0 ↔ j + 1 = D.size)) :=
  PEqualNP.Outside.L_meta_21435.main


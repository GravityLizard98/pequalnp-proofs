import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24694

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

def n_dg : Gate := ⟨GateOp.or, []⟩

def n_stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def n_M2 (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem n_ifp {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem n_ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem n_len (gs : List Gate) (x : List Bool) : (gs.foldl n_stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, n_stp, ih]; omega

theorem n_getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem n_getD_last {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k = l.length) :
    (l ++ [b]).getD k d = b := by
  subst hk; simp [List.getD_eq_getElem?_getD]

theorem n_getD_left {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k < l.length) :
    (l ++ [b]).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem n_snoc_fold (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl n_stp x =
      gs.foldl n_stp x ++ [g.op.eval (g.inputs.map fun i => (gs.foldl n_stp x).getD i false)] := by
  simp [List.foldl_append, n_stp]

theorem n_pre (gs n_hs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length + gs.length) :
    ((gs ++ n_hs).foldl n_stp x).getD w false = (gs.foldl n_stp x).getD w false := by
  induction n_hs using List.reverseRecOn with
  | nil => simp
  | append_singleton n_hs g ih =>
    rw [← List.append_assoc, n_snoc_fold, n_getD_snoc, n_len, n_ifp (by simp; omega), ih]

theorem n_inp (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (gs.foldl n_stp x).getD w false = x.getD w false := by
  have := n_pre [] gs x w (by simpa using hw)
  simpa using this

theorem n_top (gs : List Gate) (g : Gate) (x : List Bool) :
    ((gs ++ [g]).foldl n_stp x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl n_stp x).getD i false) := by
  rw [n_snoc_fold, n_getD_snoc, n_len, n_ifn (by omega), n_ifp rfl]

theorem n_beyond (gs : List Gate) (x : List Bool) (w : ℕ) (hw : x.length + gs.length ≤ w) :
    (gs.foldl n_stp x).getD w false = false := by
  apply List.getD_eq_default
  rw [n_len]; exact hw

theorem n_wire_at (gs : List Gate) (x : List Bool) : ∀ i, i < gs.length →
    (gs.foldl n_stp x).getD (x.length + i) false =
      (gs.getD i n_dg).op.eval ((gs.getD i n_dg).inputs.map fun w =>
        if w < x.length + i then (gs.foldl n_stp x).getD w false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; simp at hi
  | append_singleton gs g ih =>
    intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases h : i < gs.length
    · rw [n_pre gs [g] x _ (by omega), ih i h, n_getD_left gs g n_dg i h]
      congr 1
      apply List.map_congr_left
      intro w _
      split_ifs with hw
      · rw [n_pre gs [g] x _ (by omega)]
      · rfl
    · have hi' : i = gs.length := by omega
      subst hi'
      rw [n_top, n_getD_last gs g n_dg _ rfl]
      congr 1
      apply List.map_congr_left
      intro w _
      split_ifs with hw
      · rw [n_pre gs [g] x _ hw]
      · rw [n_beyond gs x w (by omega)]

theorem n_oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega


def n_interp (W : List Bool) (a : Sum Bool ℕ) : Bool := Sum.elim id (fun w => W.getD w false) a

def n_comb : GateOp → List (Sum Bool ℕ) → Sum (Sum Bool ℕ) Gate
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

def n_Ar (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)

theorem n_comb_sem (op : GateOp) (r : List (Sum Bool ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hr : r.length ≤ 2) (W : List Bool) :
    (∀ a, n_comb op r = Sum.inl a → n_interp W a = op.eval (r.map (n_interp W)) ∧
      (∀ w, a = Sum.inr w → Sum.inr w ∈ r)) ∧
    (∀ g', n_comb op r = Sum.inr g' →
      g'.op.eval (g'.inputs.map (fun w => W.getD w false)) = op.eval (r.map (n_interp W)) ∧
      n_Ar g' ∧ ∀ w ∈ g'.inputs, Sum.inr w ∈ r) := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [n_comb, n_interp, GateOp.eval]
  · rcases hop with rfl | rfl | rfl <;> rcases a with ca | wa <;>
      simp [n_comb, n_interp, GateOp.eval, n_Ar]
  · rcases hop with rfl | rfl | rfl <;> rcases a with ca | wa <;> rcases b with cb | wb <;>
      (try cases ca) <;> (try cases cb) <;> simp [n_comb, n_interp, GateOp.eval, n_Ar]
  · simp at hr

def n_rin (res : List (Sum Bool ℕ)) (g : Gate) : List (Sum Bool ℕ) :=
  g.inputs.map (fun i => res.getD i (Sum.inl false))

def n_stepR (N : ℕ) (st : List Gate × List (Sum Bool ℕ)) (g : Gate) : List Gate × List (Sum Bool ℕ) :=
  Sum.elim (fun a => (st.1, st.2 ++ [a]))
    (fun g' => (st.1 ++ [g'], st.2 ++ [Sum.inr (N + st.1.length)])) (n_comb g.op (n_rin st.2 g))

def n_runR (N : ℕ) (gs : List Gate) : List Gate × List (Sum Bool ℕ) :=
  gs.foldl (n_stepR N) ([], (List.range N).map Sum.inr)

def n_PL (N : ℕ) (n_hs : List Gate) : Prop :=
  (∀ g ∈ n_hs, n_Ar g) ∧ ∀ j < n_hs.length, ∀ i ∈ (n_hs.getD j n_dg).inputs, i < N + j

def n_Inv (N : ℕ) (gs : List Gate) (st : List Gate × List (Sum Bool ℕ)) : Prop :=
  st.2.length = N + gs.length ∧ st.1.length ≤ gs.length ∧
  (∀ k w, st.2.getD k (Sum.inl false) = Sum.inr w → w < N + st.1.length) ∧
  n_PL N st.1 ∧
  ∀ x : List Bool, x.length = N → ∀ k,
    (gs.foldl n_stp x).getD k false = n_interp (st.1.foldl n_stp x) (st.2.getD k (Sum.inl false))

theorem n_rget (N k : ℕ) : ((List.range N).map (Sum.inr : ℕ → Sum Bool ℕ)).getD k (Sum.inl false) =
    if k < N then Sum.inr k else Sum.inl false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem n_interp_ext (W : List Bool) (b : Bool) (a : Sum Bool ℕ) (h : ∀ w, a = Sum.inr w → w < W.length) :
    n_interp (W ++ [b]) a = n_interp W a := by
  rcases a with c | w
  · rfl
  · exact n_getD_left W b false w (h w rfl)

theorem n_inv_run (N : ℕ) (gs : List Gate)
    (hF : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    n_Inv N gs (n_runR N gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [n_runR], Nat.le_refl _, ?_, ⟨fun g hg => by simp [n_runR] at hg, fun j hj => by simp [n_runR] at hj⟩, ?_⟩
    · intro k w h
      simp only [n_runR, List.foldl_nil] at h
      rw [n_rget] at h
      split_ifs at h with hk
      · have := Sum.inr.inj h
        simp only [n_runR, List.foldl_nil, List.length_nil]
        omega
    · intro x hx k
      simp only [n_runR, List.foldl_nil]
      rw [n_rget]
      split_ifs with hk
      · rfl
      · exact List.getD_eq_default _ _ (by omega)
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hF g' (List.mem_append_left _ hg'))
    obtain ⟨hop, hlen⟩ := hF g (by simp)
    have erun : n_runR N (gs ++ [g]) = n_stepR N (n_runR N gs) g := by
      unfold n_runR
      rw [List.foldl_append]
      rfl
    rw [erun]
    generalize n_runR N gs = st at ih'
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih'
    have hr : (n_rin st.2 g).length ≤ 2 := by
      unfold n_rin
      rw [List.length_map]
      exact hlen
    have semr : ∀ x : List Bool, x.length = N →
        g.op.eval (g.inputs.map (fun i => (gs.foldl n_stp x).getD i false)) =
          g.op.eval ((n_rin st.2 g).map (n_interp (st.1.foldl n_stp x))) := by
      intro x hx
      congr 1
      unfold n_rin
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact i5 x hx i
    have rmem : ∀ w, Sum.inr w ∈ n_rin st.2 g → w < N + st.1.length := by
      intro w hw
      unfold n_rin at hw
      rw [List.mem_map] at hw
      obtain ⟨i, _, hi⟩ := hw
      exact i3 i w hi
    have oldlt : ∀ (x : List Bool), x.length = N → ∀ k, k < N + gs.length →
        ((gs ++ [g]).foldl n_stp x).getD k false = (gs.foldl n_stp x).getD k false := by
      intro x hx k hk
      exact n_pre gs [g] x k (by omega)
    have oldtop : ∀ (x : List Bool), x.length = N →
        ((gs ++ [g]).foldl n_stp x).getD (N + gs.length) false =
          g.op.eval ((n_rin st.2 g).map (n_interp (st.1.foldl n_stp x))) := by
      intro x hx
      have := n_top gs g x
      rw [hx] at this
      rw [this, semr x hx]
    have oldgt : ∀ (x : List Bool), x.length = N → ∀ k, N + gs.length < k →
        ((gs ++ [g]).foldl n_stp x).getD k false = false := by
      intro x hx k hk
      exact n_beyond _ x k (by rw [List.length_append, List.length_singleton]; omega)
    cases hc : n_comb g.op (n_rin st.2 g) with
    | inl a =>
      have e : n_stepR N st g = (st.1, st.2 ++ [a]) := by
        unfold n_stepR
        rw [hc]
        rfl
      rw [e]
      refine ⟨by simp [i1]; omega, by simp; omega, ?_, i4, ?_⟩
      · intro k w h
        show w < N + st.1.length
        change (st.2 ++ [a]).getD k (Sum.inl false) = Sum.inr w at h
        by_cases hk : k < st.2.length
        · rw [n_getD_left _ _ _ _ hk] at h
          exact i3 k w h
        · by_cases hk2 : k = st.2.length
          · rw [n_getD_last _ _ _ _ hk2] at h
            exact rmem w (((n_comb_sem g.op _ hop hr []).1 a hc).2 w h)
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)] at h
            exact absurd h (by simp)
      · intro x hx k
        show _ = n_interp (st.1.foldl n_stp x) ((st.2 ++ [a]).getD k (Sum.inl false))
        by_cases hk : k < st.2.length
        · rw [n_getD_left _ _ _ _ hk, oldlt x hx k (by omega)]
          exact i5 x hx k
        · by_cases hk2 : k = st.2.length
          · rw [n_getD_last _ _ _ _ hk2, hk2, i1, oldtop x hx]
            exact (((n_comb_sem g.op _ hop hr _).1 a hc).1).symm
          · rw [List.getD_eq_default (st.2 ++ [a]) _
              (by rw [List.length_append, List.length_singleton]; omega), oldgt x hx k (by omega)]
            rfl
    | inr g' =>
      have e : n_stepR N st g = (st.1 ++ [g'], st.2 ++ [Sum.inr (N + st.1.length)]) := by
        unfold n_stepR
        rw [hc]
        rfl
      rw [e]
      have s23 := ((n_comb_sem g.op _ hop hr []).2 g' hc).2
      refine ⟨by simp [i1]; omega, by simp; omega, ?_, ⟨?_, ?_⟩, ?_⟩
      · intro k w h
        show w < N + (st.1 ++ [g']).length
        rw [List.length_append, List.length_singleton]
        change (st.2 ++ [Sum.inr (N + st.1.length)]).getD k (Sum.inl false) = Sum.inr w at h
        by_cases hk : k < st.2.length
        · rw [n_getD_left _ _ _ _ hk] at h
          have := i3 k w h
          omega
        · by_cases hk2 : k = st.2.length
          · rw [n_getD_last _ _ _ _ hk2] at h
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
        change i ∈ ((st.1 ++ [g']).getD j n_dg).inputs at hi
        by_cases hj1 : j < st.1.length
        · rw [n_getD_left _ _ _ _ hj1] at hi
          exact i4.2 j hj1 i hi
        · have hj2 : j = st.1.length := by omega
          rw [n_getD_last _ _ _ _ hj2] at hi
          have := rmem i (s23.2 i hi)
          omega
      · intro x hx k
        show _ = n_interp ((st.1 ++ [g']).foldl n_stp x)
          ((st.2 ++ [Sum.inr (N + st.1.length)]).getD k (Sum.inl false))
        have hW : (st.1.foldl n_stp x).length = N + st.1.length := by rw [n_len, hx]
        rw [n_snoc_fold st.1 g' x]
        by_cases hk : k < st.2.length
        · rw [n_getD_left _ _ _ _ hk, oldlt x hx k (by omega),
            n_interp_ext _ _ _ (fun w hw => by rw [hW]; exact i3 k w hw)]
          exact i5 x hx k
        · by_cases hk2 : k = st.2.length
          · rw [n_getD_last _ _ _ _ hk2, hk2, i1, oldtop x hx]
            show _ = ((st.1.foldl n_stp x) ++ _).getD (N + st.1.length) false
            rw [n_getD_last _ _ _ _ hW.symm]
            exact (((n_comb_sem g.op _ hop hr _).2 g' hc).1).symm
          · rw [List.getD_eq_default (st.2 ++ [Sum.inr (N + st.1.length)]) _
              (by rw [List.length_append, List.length_singleton]; omega), oldgt x hx k (by omega)]
            rfl

def n_RRg (g : Gate) (w : ℕ) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ w ∈ g.inputs) ∨ (g.op = GateOp.not ∧ g.inputs.head? = some w)

def n_RR (gs : List Gate) (w : ℕ) : Prop := ∃ g ∈ gs, n_RRg g w

def n_Lst (n_hs : List Gate) (w : ℕ) : Prop := ∃ g ∈ n_hs, w ∈ g.inputs

theorem n_comb_reads (op : GateOp) (r : List (Sum Bool ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hr : r.length ≤ 2) :
    (∀ w, n_comb op r = Sum.inl (Sum.inr w) →
      (op = GateOp.and ∨ op = GateOp.or) ∧ ∀ w', Sum.inr w' ∈ r → w' = w) ∧
    (∀ g', n_comb op r = Sum.inr g' →
      ((op = GateOp.and ∨ op = GateOp.or) ∧ ∃ w w', r = [Sum.inr w, Sum.inr w'] ∧ g'.inputs = [w, w']) ∨
      (op = GateOp.not ∧ ∃ w t, r = Sum.inr w :: t ∧ g'.inputs = [w])) := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [n_comb]
  · rcases hop with rfl | rfl | rfl <;> rcases a with ca | wa <;>
      simp [n_comb]
  · rcases hop with rfl | rfl | rfl <;> rcases a with ca | wa <;> rcases b with cb | wb <;>
      (try cases ca) <;> (try cases cb) <;> simp [n_comb]
  · simp at hr

theorem n_rr_mono {gs : List Gate} (g : Gate) {w : ℕ} (h : n_RR gs w) : n_RR (gs ++ [g]) w := by
  obtain ⟨q, hq, hw⟩ := h
  exact ⟨q, List.mem_append_left _ hq, hw⟩

theorem n_lst_mono {n_hs : List Gate} (g : Gate) {w : ℕ} (h : n_Lst n_hs w) : n_Lst (n_hs ++ [g]) w := by
  obtain ⟨q, hq, hw⟩ := h
  exact ⟨q, List.mem_append_left _ hq, hw⟩

def n_RInv (N : ℕ) (gs : List Gate) (st : List Gate × List (Sum Bool ℕ)) : Prop :=
  (∀ k < N, st.2.getD k (Sum.inl false) = Sum.inr k) ∧
  (∀ k w, st.2.getD k (Sum.inl false) = Sum.inr w → w < N → k = w ∨ n_RR gs w) ∧
  (∀ w < N, n_Lst st.1 w → n_RR gs w) ∧
  (st.1.length = gs.length → ∀ w < N, n_RR gs w → n_Lst st.1 w)

theorem n_rinv_run (N : ℕ) (gs : List Gate)
    (hF : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    n_RInv N gs (n_runR N gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      simp only [n_runR, List.foldl_nil]
      rw [n_rget, n_ifp hk]
    · intro k w h hw
      simp only [n_runR, List.foldl_nil] at h
      rw [n_rget] at h
      split_ifs at h with hk
      · exact Or.inl (Sum.inr.inj h)
    · intro w _ h
      obtain ⟨q, hq, _⟩ := h
      simp [n_runR] at hq
    · intro _ w _ h
      obtain ⟨q, hq, _⟩ := h
      simp at hq
  | append_singleton gs g ih =>
    have hFp : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
        g'.inputs.length ≤ 2 := fun g' hg' => hF g' (List.mem_append_left _ hg')
    have ih' := ih hFp
    obtain ⟨i1, i2, -, -, -⟩ := n_inv_run N gs hFp
    obtain ⟨hop, hlen⟩ := hF g (by simp)
    have erun : n_runR N (gs ++ [g]) = n_stepR N (n_runR N gs) g := by
      unfold n_runR
      rw [List.foldl_append]
      rfl
    rw [erun]
    generalize n_runR N gs = st at ih' i1 i2
    obtain ⟨r0, r2, r1, r3⟩ := ih'
    have hr : (n_rin st.2 g).length ≤ 2 := by
      unfold n_rin
      rw [List.length_map]
      exact hlen
    have F1 : (g.op = GateOp.and ∨ g.op = GateOp.or) → ∀ w, Sum.inr w ∈ n_rin st.2 g → w < N →
        n_RR (gs ++ [g]) w := by
      intro ho w hw hwN
      unfold n_rin at hw
      rw [List.mem_map] at hw
      obtain ⟨i, hi, hiw⟩ := hw
      rcases r2 i w hiw hwN with e | h
      · rw [e] at hi
        exact ⟨g, by simp, Or.inl ⟨ho, hi⟩⟩
      · exact n_rr_mono g h
    have F2 : g.op = GateOp.not → ∀ w t, n_rin st.2 g = Sum.inr w :: t → w < N → n_RR (gs ++ [g]) w := by
      intro ho w t hw hwN
      unfold n_rin at hw
      rcases hgi : g.inputs with _ | ⟨i, rest⟩
      · rw [hgi] at hw
        simp at hw
      · rw [hgi] at hw
        simp only [List.map_cons, List.cons.injEq] at hw
        rcases r2 i w hw.1 hwN with e | h
        · exact ⟨g, by simp, Or.inr ⟨ho, by rw [hgi, e]; rfl⟩⟩
        · exact n_rr_mono g h
    have F3 : ∀ w < N, w ∈ g.inputs → Sum.inr w ∈ n_rin st.2 g := by
      intro w hw hi
      unfold n_rin
      rw [List.mem_map]
      exact ⟨w, hi, r0 w hw⟩
    cases hc : n_comb g.op (n_rin st.2 g) with
    | inl a =>
      have e : n_stepR N st g = (st.1, st.2 ++ [a]) := by
        unfold n_stepR
        rw [hc]
        rfl
      rw [e]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k hk
        show (st.2 ++ [a]).getD k (Sum.inl false) = Sum.inr k
        rw [n_getD_left _ _ _ _ (by omega)]
        exact r0 k hk
      · intro k w h hw
        change (st.2 ++ [a]).getD k (Sum.inl false) = Sum.inr w at h
        by_cases hk : k < st.2.length
        · rw [n_getD_left _ _ _ _ hk] at h
          rcases r2 k w h hw with e1 | h1
          · exact Or.inl e1
          · exact Or.inr (n_rr_mono g h1)
        · by_cases hk2 : k = st.2.length
          · rw [n_getD_last _ _ _ _ hk2] at h
            rw [h] at hc
            have hcr := (n_comb_reads g.op _ hop hr).1 w hc
            exact Or.inr (F1 hcr.1 w (((n_comb_sem g.op _ hop hr []).1 _ hc).2 w rfl) hw)
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)] at h
            exact absurd h (by simp)
      · intro w hw h
        exact n_rr_mono g (r1 w hw h)
      · intro hl
        exfalso
        change st.1.length = (gs ++ [g]).length at hl
        rw [List.length_append, List.length_singleton] at hl
        omega
    | inr g' =>
      have e : n_stepR N st g = (st.1 ++ [g'], st.2 ++ [Sum.inr (N + st.1.length)]) := by
        unfold n_stepR
        rw [hc]
        rfl
      rw [e]
      have hB := (n_comb_reads g.op _ hop hr).2 g' hc
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k hk
        show (st.2 ++ [Sum.inr (N + st.1.length)]).getD k (Sum.inl false) = Sum.inr k
        rw [n_getD_left _ _ _ _ (by omega)]
        exact r0 k hk
      · intro k w h hw
        change (st.2 ++ [Sum.inr (N + st.1.length)]).getD k (Sum.inl false) = Sum.inr w at h
        by_cases hk : k < st.2.length
        · rw [n_getD_left _ _ _ _ hk] at h
          rcases r2 k w h hw with e1 | h1
          · exact Or.inl e1
          · exact Or.inr (n_rr_mono g h1)
        · by_cases hk2 : k = st.2.length
          · rw [n_getD_last _ _ _ _ hk2] at h
            have := Sum.inr.inj h
            omega
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)] at h
            exact absurd h (by simp)
      · intro w hw h
        obtain ⟨q, hq, hwq⟩ := h
        change q ∈ st.1 ++ [g'] at hq
        rw [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact n_rr_mono g (r1 w hw ⟨q, hq, hwq⟩)
        · rcases hB with ⟨ho, w1, w2, hr12, hg'⟩ | ⟨ho, w1, t, hr1, hg'⟩
          · rw [hg'] at hwq
            refine F1 ho w ?_ hw
            rw [hr12]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hwq
            rcases hwq with rfl | rfl <;> simp
          · rw [hg'] at hwq
            have hww : w = w1 := by simpa using hwq
            rw [hww]
            rw [hww] at hw
            exact F2 ho w1 t hr1 hw
      · intro hl w hw h
        change (st.1 ++ [g']).length = (gs ++ [g]).length at hl
        rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton] at hl
        have hl' : st.1.length = gs.length := by omega
        obtain ⟨q, hq, hwq⟩ := h
        rw [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact n_lst_mono g' (r3 hl' w hw ⟨q, hq, hwq⟩)
        · refine ⟨g', by simp, ?_⟩
          rcases hwq with ⟨ho, hin⟩ | ⟨ho, hhd⟩
          · have hmem := F3 w hw hin
            rcases hB with ⟨_, w1, w2, hr12, hg'⟩ | ⟨ho', _⟩
            · rw [hr12] at hmem
              rw [hg']
              simpa using hmem
            · rw [ho'] at ho
              rcases ho with ho | ho <;> cases ho
          · rcases hB with ⟨ho', _⟩ | ⟨_, w1, t, hr1, hg'⟩
            · rw [ho] at ho'
              rcases ho' with ho' | ho' <;> cases ho'
            · rcases hgi : q.inputs with _ | ⟨i, rest⟩
              · rw [hgi] at hhd
                simp at hhd
              · rw [hgi] at hhd
                have hi : i = w := by simpa using hhd
                unfold n_rin at hr1
                rw [hgi] at hr1
                simp only [List.map_cons, List.cons.injEq] at hr1
                rw [hi, r0 w hw] at hr1
                have hww : w = w1 := Sum.inr.inj hr1.1
                rw [hg', hww]
                simp

theorem n_norm' (n m : ℕ) (A : Fin n → Fin m → Bool) (gs : List Gate) (o : ℕ) (hF : FanInTwo ⟨gs, o⟩)
    (hrep : Represents A ⟨gs, o⟩) (hnc : ∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2) :
    ∃ o' : ℕ, (n_runR (n + m) gs).2.getD o (Sum.inl false) = Sum.inr o' ∧
      n_PL (n + m) (n_runR (n + m) gs).1 ∧ Represents A ⟨(n_runR (n + m) gs).1, o'⟩ ∧
      (n_runR (n + m) gs).1.length ≤ gs.length ∧ o' < n + m + (n_runR (n + m) gs).1.length ∧
      (∀ w < n + m, (n_Lst (n_runR (n + m) gs).1 w ∨ o' = w) → (n_RR gs w ∨ o = w)) ∧
      ((n_runR (n + m) gs).1.length = gs.length → ∀ w < n + m, (n_RR gs w ∨ o = w) →
        (n_Lst (n_runR (n + m) gs).1 w ∨ o' = w)) := by
  have hF' : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hF g hg
    simpa [Set.mem_insert_iff] using this
  obtain ⟨i1, i2, i3, i4, i5⟩ := n_inv_run (n + m) gs hF'
  obtain ⟨r0, r2, r1, r3⟩ := n_rinv_run (n + m) gs hF'
  have hx : ∀ (u : Fin n) (v : Fin m), (oneEach u v).length = n + m := by
    intro u v
    simp [oneEach]
  have hev : ∀ (u : Fin n) (v : Fin m), (gs.foldl n_stp (oneEach u v)).getD o false = A u v :=
    fun u v => hrep u v
  cases ha : (n_runR (n + m) gs).2.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨u, u2, v, v2, hne⟩ := hnc
    have h1 : A u v = c := by
      have := i5 (oneEach u v) (hx u v) o
      rw [ha, hev u v] at this
      exact this
    have h2 : A u2 v2 = c := by
      have := i5 (oneEach u2 v2) (hx u2 v2) o
      rw [ha, hev u2 v2] at this
      exact this
    exact hne (h1.trans h2.symm)
  | inr w =>
    refine ⟨w, rfl, i4, fun u v => ?_, i2, i3 o w ha, ?_, ?_⟩
    · have := i5 (oneEach u v) (hx u v) o
      rw [ha, hev u v] at this
      exact this.symm
    · intro w' hw' h
      rcases h with h | h
      · exact Or.inl (r1 w' hw' h)
      · rw [← h] at hw' ⊢
        rcases r2 o w ha hw' with e | h
        · exact Or.inr e
        · exact Or.inl h
    · intro hl w' hw' h
      rcases h with h | h
      · exact Or.inl (r3 hl w' hw' h)
      · right
        rw [← h] at hw' ⊢
        have := r0 o hw'
        rw [ha] at this
        exact Sum.inr.inj this

def n_phi (N j s w : ℕ) : ℕ := if w < N + j then w else if w = N + j then N + s else w - 1

def n_mg (N j s : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (n_phi N j s)⟩

def n_hs (N j : ℕ) (gs : List Gate) : List Gate := (gs.eraseIdx j).map (n_mg N j gs.length)

theorem n_phi_lt (N j s w : ℕ) (h : w < N + j) : n_phi N j s w = w := by
  unfold n_phi; rw [n_ifp h]

theorem n_phi_gt (N j s w : ℕ) (h : N + j < w) : n_phi N j s w = w - 1 := by
  unfold n_phi; rw [n_ifn (by omega), n_ifn (by omega)]

theorem n_hs_len (N j : ℕ) (gs : List Gate) (hj : j < gs.length) : (n_hs N j gs).length + 1 = gs.length := by
  unfold n_hs
  rw [List.length_map, List.length_eraseIdx, n_ifp hj]
  omega

theorem n_hs_lt (N j : ℕ) (gs : List Gate) (i : ℕ) (hi : i < j) (hj : j < gs.length) :
    (n_hs N j gs).getD i n_dg = n_mg N j gs.length (gs.getD i n_dg) := by
  unfold n_hs
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eraseIdx, n_ifp hi, List.getElem?_eq_getElem (by omega)]
  rfl

theorem n_hs_ge (N j : ℕ) (gs : List Gate) (i : ℕ) (hi : j ≤ i) (hj : i + 1 < gs.length) :
    (n_hs N j gs).getD i n_dg = n_mg N j gs.length (gs.getD (i + 1) n_dg) := by
  unfold n_hs
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eraseIdx, n_ifn (by omega), List.getElem?_eq_getElem hj]
  rfl

theorem n_sim2 (N j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (hun : ∀ i < gs.length, N + j ∉ (gs.getD i n_dg).inputs) (x : List Bool) (hx : x.length = N) :
    ∀ w, w ≠ N + j → ((n_hs N j gs).foldl n_stp x).getD (n_phi N j gs.length w) false =
      (gs.foldl n_stp x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwj
    have hl1 := n_hs_len N j gs hj
    by_cases h1 : w < N
    · rw [n_phi_lt _ _ _ _ (by omega), n_inp _ _ _ (by omega), n_inp _ _ _ (by omega)]
    · by_cases h2 : N + gs.length ≤ w
      · rw [n_phi_gt _ _ _ _ (by omega), n_beyond _ _ _ (by omega), n_beyond _ _ _ (by omega)]
      · obtain ⟨i, rfl⟩ : ∃ i, w = N + i := ⟨w - N, by omega⟩
        by_cases h4 : i < j
        · rw [n_phi_lt _ _ _ _ (by omega)]
          have e1 := n_wire_at (n_hs N j gs) x i (by omega)
          have e2 := n_wire_at gs x i (by omega)
          rw [hx] at e1 e2
          rw [e1, e2, n_hs_lt N j gs i h4 hj]
          show (gs.getD i n_dg).op.eval (List.map _ ((gs.getD i n_dg).inputs.map (n_phi N j gs.length))) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro w' _
          show (if n_phi N j gs.length w' < N + i then
            ((n_hs N j gs).foldl n_stp x).getD (n_phi N j gs.length w') false else false) = _
          by_cases hc : w' < N + i
          · rw [n_ifp hc, ← ih w' (by omega) (by omega), n_phi_lt _ _ _ _ (by omega), n_ifp hc]
          · rw [n_ifn hc]
            by_cases hc1 : w' < N + j
            · rw [n_phi_lt _ _ _ _ hc1, n_ifn hc]
            · unfold n_phi
              rw [n_ifn hc1]
              split_ifs <;> first | rfl | omega
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
          rw [n_phi_gt _ _ _ _ (by omega)]
          have ek : N + (k + 1) - 1 = N + k := by omega
          rw [ek]
          have e1 := n_wire_at (n_hs N j gs) x k (by omega)
          have e2 := n_wire_at gs x (k + 1) (by omega)
          rw [hx] at e1 e2
          rw [e1, e2, n_hs_ge N j gs k (by omega) (by omega)]
          show (gs.getD (k + 1) n_dg).op.eval
            (List.map _ ((gs.getD (k + 1) n_dg).inputs.map (n_phi N j gs.length))) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro w' hw'
          show (if n_phi N j gs.length w' < N + k then
            ((n_hs N j gs).foldl n_stp x).getD (n_phi N j gs.length w') false else false) = _
          have hne : w' ≠ N + j := fun e => hun (k + 1) (by omega) (e ▸ hw')
          by_cases hc : w' < N + (k + 1)
          · rw [n_ifp hc, ← ih w' (by omega) hne]
            by_cases hc1 : w' < N + j
            · rw [n_phi_lt _ _ _ _ hc1, n_ifp (by omega)]
            · rw [n_phi_gt _ _ _ _ (by omega), n_ifp (by omega)]
          · rw [n_ifn hc, n_phi_gt _ _ _ _ (by omega), n_ifn (by omega)]

theorem n_hs_PL (N j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (hun : ∀ i < gs.length, N + j ∉ (gs.getD i n_dg).inputs) (hP : n_PL N gs) : n_PL N (n_hs N j gs) := by
  have hl1 := n_hs_len N j gs hj
  constructor
  · intro g hg
    unfold n_hs at hg
    rw [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hP.1 g0 (List.mem_of_mem_eraseIdx hg0)
    unfold n_Ar at this ⊢
    unfold n_mg
    simp only [List.length_map]
    exact this
  · intro i hi c hc
    by_cases h : i < j
    · rw [n_hs_lt N j gs i h hj] at hc
      unfold n_mg at hc
      simp only [List.mem_map] at hc
      obtain ⟨w', hw', rfl⟩ := hc
      have := hP.2 i (by omega) w' hw'
      rw [n_phi_lt _ _ _ _ (by omega)]
      exact this
    · rw [n_hs_ge N j gs i (by omega) (by omega)] at hc
      unfold n_mg at hc
      simp only [List.mem_map] at hc
      obtain ⟨w', hw', rfl⟩ := hc
      have := hP.2 (i + 1) (by omega) w' hw'
      have hne : w' ≠ N + j := fun e => hun (i + 1) (by omega) (e ▸ hw')
      by_cases hc1 : w' < N + j
      · rw [n_phi_lt _ _ _ _ hc1]; omega
      · rw [n_phi_gt _ _ _ _ (by omega)]; omega

theorem n_exmin (P : ℕ → Prop) : ∀ k, P k → ∃ m, P m ∧ ∀ k', P k' → m ≤ k' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h : ∀ k', P k' → k ≤ k'
    · exact ⟨k, hk, h⟩
    · obtain ⟨k', hk'⟩ := not_forall.1 h
      obtain ⟨hk1, hk2⟩ := Classical.not_imp.1 hk'
      exact ih k' (by omega) hk1

theorem n_lst_hs (N j : ℕ) (gs : List Gate) (w : ℕ) (hw : w < N) (h : n_Lst (n_hs N j gs) w) : n_Lst gs w := by
  obtain ⟨q, hq, hwq⟩ := h
  unfold n_hs at hq
  rw [List.mem_map] at hq
  obtain ⟨q0, hq0, rfl⟩ := hq
  refine ⟨q0, List.mem_of_mem_eraseIdx hq0, ?_⟩
  change w ∈ q0.inputs.map (n_phi N j gs.length) at hwq
  rw [List.mem_map] at hwq
  obtain ⟨x, hx, hxe⟩ := hwq
  have hxw : x = w := by
    unfold n_phi at hxe
    split_ifs at hxe <;> omega
  rw [← hxw]
  exact hx

theorem n_reduced_props (N : ℕ) (gs : List Gate) (o : ℕ) (hPL : n_PL N gs) (hpos : 0 < gs.length)
    (c3 : o + 1 = N + gs.length)
    (c4 : ∀ j, j + 1 < gs.length → ∃ i, i < gs.length ∧ N + j ∈ (gs.getD i n_dg).inputs) :
    FanInTwo ⟨gs, o⟩ ∧
    (∀ g ∈ (Circuit.mk gs o).gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, o⟩ ∧ 0 < (Circuit.mk gs o).size ∧
    (Circuit.mk gs o).output + 1 = N + (Circuit.mk gs o).size ∧
    (∀ j < (Circuit.mk gs o).size,
      (PEqualNP.MetaComplexity.NestedCover.readsIn ⟨gs, o⟩ (Finset.range (Circuit.mk gs o).size) (N + j) = 0 ↔
        j + 1 = (Circuit.mk gs o).size)) := by
  refine ⟨?_, fun g hg => hPL.1 g hg, hPL.2, hpos, c3, ?_⟩
  · intro g hg
    rcases hPL.1 g hg with ⟨h | h, hl⟩ | ⟨h, hl⟩
    · exact ⟨by rw [h]; simp, by omega⟩
    · exact ⟨by rw [h]; simp, by omega⟩
    · exact ⟨by rw [h]; simp, by omega⟩
  · intro j hj
    have hj' : j < gs.length := hj
    show (∑ i ∈ Finset.range gs.length, (gs.getD i n_dg).inputs.count (N + j)) = 0 ↔
      j + 1 = gs.length
    constructor
    · intro h0
      by_contra hne
      obtain ⟨i, hi, hm⟩ := c4 j (by omega)
      have hle := Finset.single_le_sum (f := fun i => ((gs.getD i n_dg).inputs.count (N + j)))
        (fun i _ => Nat.zero_le _) (Finset.mem_range.2 hi)
      have p1 : 0 < (gs.getD i n_dg).inputs.count (N + j) := List.count_pos_iff.2 hm
      omega
    · intro hlast
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      apply List.count_eq_zero.2
      intro hm
      have := hPL.2 i hi _ hm
      omega

theorem n_main (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (hF : FanInTwo C)
    (hrep : Represents A C)
    (hnc : ∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2) :
    ∃ D : Circuit, FanInTwo D ∧ Represents A D ∧ D.size ≤ C.size ∧
      (((∀ g ∈ D.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
        (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) D ∧ 0 < D.size ∧
      D.output + 1 = (n + m) + D.size ∧
      (∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) ((n + m) + j) = 0 ↔
        j + 1 = D.size))) ∨ (D.size = 0 ∧ D.output < (n + m))) ∧
      (∀ w < (n + m), (n_Lst D.gates w ∨ D.output = w) → (n_RR C.gates w ∨ C.output = w)) ∧
      (D.size + 1 ≤ C.size ∨ ∀ w < (n + m), (n_RR C.gates w ∨ C.output = w) →
        (n_Lst D.gates w ∨ D.output = w)) := by
  obtain ⟨gsC, oc⟩ := C
  obtain ⟨o', ha, hPL0, hrep0, hle0, hlt0, rd10, rd20⟩ := n_norm' n m A gsC oc hF hrep hnc
  obtain ⟨m0, ⟨D, hPL, hrepD, hsz, hk, rd1, rd2⟩, hmin⟩ := n_exmin (fun k => ∃ D : Circuit,
      n_PL (n + m) D.gates ∧ Represents A D ∧ D.gates.length = k ∧ k ≤ gsC.length ∧
      (∀ w < (n + m), (n_Lst D.gates w ∨ D.output = w) → (n_RR gsC w ∨ oc = w)) ∧
      (k = gsC.length → ∀ w < (n + m), (n_RR gsC w ∨ oc = w) → (n_Lst D.gates w ∨ D.output = w)))
    (n_runR (n + m) gsC).1.length ⟨⟨(n_runR (n + m) gsC).1, o'⟩, hPL0, hrep0, rfl, hle0, rd10, rd20⟩
  obtain ⟨gs, o⟩ := D
  have hsz' : gs.length = m0 := hsz
  have hmin' : ∀ D' : Circuit, n_PL (n + m) D'.gates → Represents A D' →
      D'.gates.length < gs.length →
      (∀ w < (n + m), (n_Lst D'.gates w ∨ D'.output = w) → (n_RR gsC w ∨ oc = w)) → False := by
    intro D' q1 q2 q3 q4
    have := hmin D'.gates.length ⟨D', q1, q2, rfl, by omega, q4, fun hh => by omega⟩
    omega
  have hx : ∀ (u : Fin n) (v : Fin m), (oneEach u v).length = n + m := by
    intro u v
    simp [oneEach]
  have hev : ∀ (u : Fin n) (v : Fin m), (gs.foldl n_stp (oneEach u v)).getD o false = A u v :=
    fun u v => hrepD u v
  have c2 : o < n + m + gs.length := by
    by_contra h
    obtain ⟨u, u2, v, v2, hne⟩ := hnc
    have e1 := hev u v
    have e2 := hev u2 v2
    rw [n_beyond gs _ o (by rw [hx]; omega)] at e1 e2
    exact hne (e1.symm.trans e2)
  have last : (Circuit.mk gs o).size + 1 ≤ (Circuit.mk gsC oc).size ∨ ∀ w < (n + m),
      (n_RR gsC w ∨ oc = w) → (n_Lst gs w ∨ o = w) := by
    by_cases heq : gs.length = gsC.length
    · exact Or.inr (rd2 (by omega))
    · left
      show gs.length + 1 ≤ gsC.length
      omega
  have hle : (Circuit.mk gs o).size ≤ (Circuit.mk gsC oc).size := by
    show gs.length ≤ gsC.length
    omega
  by_cases hgs : gs.length = 0
  · have hgs' : gs = [] := List.eq_nil_of_length_eq_zero hgs
    have ho : o < n + m := by
      rw [hgs] at c2
      exact c2
    refine ⟨⟨gs, o⟩, ?_, hrepD, hle, Or.inr ⟨hgs, ho⟩, rd1, last⟩
    intro g hg
    rw [hgs'] at hg
    simp at hg
  · have c3 : o + 1 = n + m + gs.length := by
      by_contra h
      have hne : gs ≠ [] := by
        intro e
        rw [e] at hgs
        exact hgs rfl
      obtain ⟨gs', g, rfl⟩ : ∃ gs' g, gs = gs' ++ [g] :=
        ⟨gs.dropLast, gs.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      rw [List.length_append, List.length_singleton] at c2 h
      refine hmin' ⟨gs', o⟩
        ⟨fun q hq => hPL.1 q (List.mem_append_left _ hq), fun j hj i hi => by
          have hj' : j < gs'.length := hj
          have := hPL.2 j (by show j < (gs' ++ [g]).length; rw [List.length_append, List.length_singleton]; omega) i
            (by
              show i ∈ ((gs' ++ [g]).getD j n_dg).inputs
              rw [n_getD_left gs' g n_dg j hj']
              exact hi)
          exact this⟩
        (fun u v => by
          show (gs'.foldl n_stp (oneEach u v)).getD o false = A u v
          rw [← hev u v]
          exact (n_pre gs' [g] (oneEach u v) o (by rw [hx]; omega)).symm)
        (by
          show gs'.length < (gs' ++ [g]).length
          rw [List.length_append, List.length_singleton]
          omega)
        ?_
      intro w hw' hh
      rcases hh with hh | hh
      · exact rd1 w hw' (Or.inl (n_lst_mono g hh))
      · exact rd1 w hw' (Or.inr hh)
    have c4 : ∀ j, j + 1 < gs.length → ∃ i, i < gs.length ∧ n + m + j ∈ (gs.getD i n_dg).inputs := by
      intro j hj
      by_contra hno
      have hun : ∀ i < gs.length, n + m + j ∉ (gs.getD i n_dg).inputs :=
        fun i hi hm => hno ⟨i, hi, hm⟩
      have hl := n_hs_len (n + m) j gs (by omega)
      refine hmin' ⟨n_hs (n + m) j gs, n_phi (n + m) j gs.length o⟩
        (n_hs_PL (n + m) j gs (by omega) hun hPL)
        (fun u v => by
          show ((n_hs (n + m) j gs).foldl n_stp (oneEach u v)).getD (n_phi (n + m) j gs.length o) false = A u v
          rw [← hev u v]
          exact n_sim2 (n + m) j gs (by omega) hun (oneEach u v) (hx u v) o (by omega))
        (by
          show (n_hs (n + m) j gs).length < gs.length
          omega)
        ?_
      intro w hw' hh
      rcases hh with hh | hh
      · exact rd1 w hw' (Or.inl (n_lst_hs (n + m) j gs w hw' hh))
      · exfalso
        change n_phi (n + m) j gs.length o = w at hh
        rw [n_phi_gt (n + m) j gs.length o (by omega)] at hh
        omega
    obtain ⟨a, b, c, d, e, f⟩ := n_reduced_props (n + m) gs o hPL (by omega) c3 c4
    exact ⟨⟨gs, o⟩, a, hrepD, hle, Or.inl ⟨b, c, d, e, f⟩, rd1, last⟩

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem sa_val {m : ℕ} (k : Fin (m + 1)) (v : Fin m) :
    (k.succAbove v).val = if v.val < k.val then v.val else v.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (by simp [Fin.lt_def] at h2 ⊢; omega)
  · exact absurd h2 (by simp [Fin.lt_def] at h1 ⊢; omega)
  · rfl

def rho (p r : ℕ) (i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def rg (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho p r)⟩

theorem sim (Q : Prop) (p r B : ℕ) (X X' : List Bool) (hl : X.length = X'.length + 1)
    (hp : p ≤ X'.length) (hr : r < X'.length ∨ B ≤ r)
    (hbase : ∀ i, (i = p → Q) → X'.getD (rho p r i) false = X.getD i false) :
    ∀ Bs : List Gate, X'.length + Bs.length ≤ B → (∀ g ∈ Bs, ∀ i ∈ g.inputs, i = p → Q) →
      ∀ i, (i = p → Q) →
      ((Bs.map (rg p r)).foldl stp X').getD (rho p r i) false =
        (Bs.foldl stp X).getD i false := by
  intro Bs
  induction Bs using List.reverseRecOn with
  | nil =>
    intro _ _ i hi
    exact hbase i hi
  | append_singleton Bs g ih =>
    intro hB hQ i hiQ
    rw [List.length_append, List.length_singleton] at hB
    have ih' := ih (by omega) (fun g' hg' => hQ g' (List.mem_append_left _ hg'))
    have hv : (rg p r g).op.eval ((rg p r g).inputs.map fun i =>
        ((Bs.map (rg p r)).foldl stp X').getD i false) =
        g.op.eval (g.inputs.map fun i => (Bs.foldl stp X).getD i false) := by
      show g.op.eval ((g.inputs.map (rho p r)).map fun i =>
        ((Bs.map (rg p r)).foldl stp X').getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact ih' j (hQ g (by simp) j hj)
    rw [List.map_append, List.map_singleton, snoc_fold, snoc_fold, hv, getD_snoc, getD_snoc,
      len, len, List.length_map]
    simp only [hl]
    have hi := ih' i hiQ
    rcases Nat.lt_trichotomy i p with h | h | h
    · have hr' : rho p r i = i := by unfold rho; rw [ifp h]
      rw [hr'] at hi ⊢
      rw [ifp (by omega), ifp (by omega)]
      exact hi
    · have hr' : rho p r i = r := by unfold rho; rw [ifn (by omega), ifp h]
      rw [hr'] at hi ⊢
      rcases hr with h1 | h1
      · rw [ifp (by omega), ifp (by omega)]
        exact hi
      · rw [ifn (by omega), ifn (by omega), ifp (by omega), ← hi]
        symm
        exact List.getD_eq_default _ _ (by rw [len, List.length_map]; omega)
    · have hr' : rho p r i = i - 1 := by unfold rho; rw [ifn (by omega), ifn (by omega)]
      rw [hr'] at hi ⊢
      by_cases h2 : i < X'.length + 1 + Bs.length
      · rw [ifp (by omega), ifp h2]
        exact hi
      · by_cases h3 : i = X'.length + 1 + Bs.length
        · rw [ifn (by omega), ifp (by omega), ifn h2, ifp h3]
        · rw [ifn (by omega), ifn (by omega), ifn h2, ifn h3]

theorem bool_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp at h ⊢

theorem pre (gs : List Gate) (X : List Bool) (i : ℕ) (hi : i < X.length) :
    (gs.foldl stp X).getD i false = X.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [snoc_fold, getD_left _ _ _ _ (by rw [len]; omega)]
    exact ih

theorem stable (G1 G2 : List Gate) (g : Gate) (X : List Bool) (p : ℕ)
    (hp : p = X.length + G1.length) :
    ((G1 ++ g :: G2).foldl stp X).getD p false =
      g.op.eval (g.inputs.map fun i => (G1.foldl stp X).getD i false) := by
  rw [List.foldl_append, List.foldl_cons, pre _ _ _ (by simp [stp, len]; omega)]
  exact getD_last _ _ _ _ (by rw [len]; exact hp)

theorem shape (g : Gate)
    (h : ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    (∃ a b, g = ⟨GateOp.and, [a, b]⟩) ∨ (∃ a b, g = ⟨GateOp.or, [a, b]⟩) ∨
      (∃ a, g = ⟨GateOp.not, [a]⟩) := by
  obtain ⟨op, ins⟩ := g
  rcases h with ⟨h1 | h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    subst h1
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at h2
    exact Or.inl ⟨a, b, rfl⟩
  · simp only at h1 h2
    subst h1
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at h2
    exact Or.inr (Or.inl ⟨a, b, rfl⟩)
  · simp only at h1 h2
    subst h1
    rcases ins with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp at h2
    exact Or.inr (Or.inr ⟨a, rfl⟩)


theorem ev_and (W : List Bool) (a b : ℕ) :
    (⟨GateOp.and, [a, b]⟩ : Gate).op.eval
      ((⟨GateOp.and, [a, b]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (W.getD a false && W.getD b false) := by
  simp [GateOp.eval]

theorem ev_or (W : List Bool) (a b : ℕ) :
    (⟨GateOp.or, [a, b]⟩ : Gate).op.eval
      ((⟨GateOp.or, [a, b]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (W.getD a false || W.getD b false) := by
  simp [GateOp.eval]

theorem ev_not1 (W : List Bool) (a : ℕ) :
    (⟨GateOp.not, [a]⟩ : Gate).op.eval
      ((⟨GateOp.not, [a]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (!W.getD a false) := by
  simp [GateOp.eval]

theorem ev_not2 (W : List Bool) (a b : ℕ) :
    (⟨GateOp.not, [a, b]⟩ : Gate).op.eval
      ((⟨GateOp.not, [a, b]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (!W.getD a false) := by
  simp [GateOp.eval]

theorem hx {n m : ℕ} (k : Fin (n + 1)) (u : Fin n) (v : Fin m) :
    (oneEach (k.succAbove u) v).length = n + 1 + m := by
  simp [oneEach]
  omega

theorem ck (n m : ℕ) (k : Fin (n + 1)) (u : Fin n) (v : Fin m) (gs : List Gate) :
    (gs.foldl stp (oneEach (k.succAbove u) v)).getD k.val false = false := by
  rw [pre _ _ _ (by rw [hx]; have := k.isLt; omega)]
  cases hb : (oneEach (k.succAbove u) v).getD k.val false with
  | false => rfl
  | true =>
    rw [oe] at hb
    rcases hb with hb | hb
    · exact absurd (Fin.ext hb.symm) (Fin.succAbove_ne k u)
    · have := k.isLt
      omega

theorem cc (n m : ℕ) (k : Fin (n + 1)) (u : Fin n) (v : Fin m) (gs : List Gate) (c c' : ℕ)
    (h1 : n + 1 ≤ c) (h2 : c < n + 1 + m) (h3 : n + 1 ≤ c') (h4 : c' < n + 1 + m) (hne : c ≠ c') :
    ((gs.foldl stp (oneEach (k.succAbove u) v)).getD c false &&
      (gs.foldl stp (oneEach (k.succAbove u) v)).getD c' false) = false := by
  rw [pre _ _ _ (by rw [hx]; exact h2), pre _ _ _ (by rw [hx]; exact h4)]
  cases hb : (oneEach (k.succAbove u) v).getD c false with
  | false => rfl
  | true =>
    cases hb' : (oneEach (k.succAbove u) v).getD c' false with
    | false => rfl
    | true =>
      rw [oe] at hb hb'
      have := (k.succAbove u).isLt
      omega

def Rd (C : Circuit) (i : ℕ) : Prop := (∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i

def Shp (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)

def GR (g : Gate) (i : ℕ) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ i ∈ g.inputs) ∨
    (g.op = GateOp.not ∧ g.inputs.head? = some i)

def RR (C : Circuit) (i : ℕ) : Prop := (∃ g ∈ C.gates, GR g i) ∨ C.output = i

theorem mem_of_GR (g : Gate) (i : ℕ) (h : GR g i) : i ∈ g.inputs := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact h
  · cases hi : g.inputs with
    | nil => simp [hi] at h
    | cons a t =>
      simp [hi] at h
      simp [h]

theorem GR_of_mem (g : Gate) (hs : Shp g) (i : ℕ) (hi : i ∈ g.inputs) : GR g i := by
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, hi⟩
  · refine Or.inr ⟨h1, ?_⟩
    cases hin : g.inputs with
    | nil => simp [hin] at h2
    | cons a t =>
      cases t with
      | nil =>
        simp [hin] at hi
        simp [hi]
      | cons b t2 => simp [hin] at h2

theorem GR_rg (p r : ℕ) (g : Gate) (i j : ℕ) (h : GR g i) (e : rho p r i = j) :
    GR (rg p r g) j := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, List.mem_map.mpr ⟨i, h2, e⟩⟩
  · refine Or.inr ⟨h1, ?_⟩
    show (g.inputs.map (rho p r)).head? = some j
    rw [List.head?_map, h2]
    simp [e]

theorem Shp_rg (p r : ℕ) (g : Gate) (h : Shp g) : Shp (rg p r g) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, ?_⟩
    show (g.inputs.map (rho p r)).length = 2
    rw [List.length_map]
    exact h2
  · refine Or.inr ⟨h1, ?_⟩
    show (g.inputs.map (rho p r)).length = 1
    rw [List.length_map]
    exact h2

def Rel (n m : ℕ) (k : Fin (n + 1)) (d : ℕ) (F : Prop) (C C' : Circuit) : Prop :=
  C'.size + d = C.size ∧ (FanInTwo C → FanInTwo C') ∧
  ((∀ g ∈ C.gates, Shp g) → ∀ g ∈ C'.gates, Shp g) ∧
  (∀ (u : Fin n) (v : Fin m),
    C'.eval (oneEach (k.succAbove u) v) = C.eval (oneEach (k.succAbove u) v)) ∧
  (∀ i < n + 1 + m, Rd C' i → Rd C i) ∧
  (F → ∀ i < n + 1 + m, n + 1 ≤ i → RR C i → RR C' i)

def Goal2 (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (C : Circuit) : Prop :=
  ∃ C2 : Circuit, FanInTwo C2 ∧ (∀ g ∈ C2.gates, Shp g) ∧
    Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) C2 ∧ C2.size + 1 ≤ C.size ∧
    (∀ u : Fin n, Rd C2 u.val → Rd C (k.succAbove u).val) ∧
    (∀ v : Fin m, Rd C2 (n + v.val) → Rd C (n + 1 + v.val)) ∧
    (C2.size + 2 ≤ C.size ∨ ∀ v : Fin m, RR C (n + 1 + v.val) → RR C2 (n + v.val))

theorem rel_trans (n m : ℕ) (k : Fin (n + 1)) (d1 d2 : ℕ) (F : Prop) (C C' C'' : Circuit)
    (h1 : Rel n m k d1 F C C') (h2 : Rel n m k d2 F C' C'') : Rel n m k (d1 + d2) F C C'' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
  exact ⟨by omega, fun h => b2 (a2 h), fun h => b3 (a3 h), fun u v => (b4 u v).trans (a4 u v),
    fun i hi h => a5 i hi (b5 i hi h), fun hf i hi hc h => b6 hf i hi hc (a6 hf i hi hc h)⟩

theorem mod_rel (n m : ℕ) (k : Fin (n + 1)) (F : Prop) (C : Circuit) (G1 G2 : List Gate)
    (h h' : Gate) (hC : C.gates = G1 ++ h :: G2)
    (hf' : h'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h'.inputs.length ≤ 2)
    (hs' : Shp h')
    (hv : ∀ (u : Fin n) (v : Fin m),
      h'.op.eval (h'.inputs.map fun i => (G1.foldl stp (oneEach (k.succAbove u) v)).getD i false) =
      h.op.eval (h.inputs.map fun i => (G1.foldl stp (oneEach (k.succAbove u) v)).getD i false))
    (hin : ∀ i ∈ h'.inputs, i < n + 1 + m → Rd C i)
    (hkeep : F → ∀ i, GR h i → i < n + 1 + m → n + 1 ≤ i → GR h' i) :
    Rel n m k 0 F C ⟨G1 ++ h' :: G2, C.output⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (G1 ++ h' :: G2).length + 0 = C.gates.length
    rw [hC]
    simp
  · intro hF g hg
    have hg' : g ∈ G1 ++ h' :: G2 := hg
    rw [List.mem_append, List.mem_cons] at hg'
    rcases hg' with h1 | h1 | h1
    · exact hF g (by rw [hC]; simp [h1])
    · rw [h1]
      exact hf'
    · exact hF g (by rw [hC]; simp [h1])
  · intro hS g hg
    have hg' : g ∈ G1 ++ h' :: G2 := hg
    rw [List.mem_append, List.mem_cons] at hg'
    rcases hg' with h1 | h1 | h1
    · exact hS g (by rw [hC]; simp [h1])
    · rw [h1]
      exact hs'
    · exact hS g (by rw [hC]; simp [h1])
  · intro u v
    show ((G1 ++ h' :: G2).foldl stp (oneEach (k.succAbove u) v)).getD C.output false =
      (C.gates.foldl stp (oneEach (k.succAbove u) v)).getD C.output false
    have e : stp (G1.foldl stp (oneEach (k.succAbove u) v)) h' =
        stp (G1.foldl stp (oneEach (k.succAbove u) v)) h := by
      show G1.foldl stp (oneEach (k.succAbove u) v) ++ [h'.op.eval (h'.inputs.map fun i =>
        (G1.foldl stp (oneEach (k.succAbove u) v)).getD i false)] =
        G1.foldl stp (oneEach (k.succAbove u) v) ++ [h.op.eval (h.inputs.map fun i =>
        (G1.foldl stp (oneEach (k.succAbove u) v)).getD i false)]
      rw [hv u v]
    rw [hC, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, e]
  · intro i hi hrd
    rcases hrd with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ G1 ++ h' :: G2 := hg
      rw [List.mem_append, List.mem_cons] at hg'
      rcases hg' with h1 | h1 | h1
      · exact Or.inl ⟨g, by rw [hC]; simp [h1], hmem⟩
      · rw [h1] at hmem
        exact hin i hmem hi
      · exact Or.inl ⟨g, by rw [hC]; simp [h1], hmem⟩
    · exact Or.inr ho
  · intro hf i hi hc hrd
    rcases hrd with ⟨g, hg, hmem⟩ | ho
    · rw [hC, List.mem_append, List.mem_cons] at hg
      rcases hg with h1 | h1 | h1
      · exact Or.inl ⟨g, (by simp [h1] : g ∈ G1 ++ h' :: G2), hmem⟩
      · rw [h1] at hmem
        exact Or.inl ⟨h', (by simp : h' ∈ G1 ++ h' :: G2), hkeep hf i hmem hi hc⟩
      · exact Or.inl ⟨g, (by simp [h1] : g ∈ G1 ++ h' :: G2), hmem⟩
    · exact Or.inr ho

theorem del_rel (n m : ℕ) (k : Fin (n + 1)) (F : Prop) (C : Circuit) (G1 G2 : List Gate)
    (h : Gate) (r : ℕ)
    (hC : C.gates = G1 ++ h :: G2)
    (hr : r < n + 1 + m + G1.length ∨ n + 1 + m + C.gates.length ≤ r)
    (hrin : r < n + 1 + m → r ∈ h.inputs)
    (hv : ∀ (u : Fin n) (v : Fin m),
      h.op.eval (h.inputs.map fun i => (G1.foldl stp (oneEach (k.succAbove u) v)).getD i false) =
        (G1.foldl stp (oneEach (k.succAbove u) v)).getD r false)
    (hkeep : F → ∀ i, GR h i → i < n + 1 + m → n + 1 ≤ i →
      ((∃ g ∈ G1, GR g i) ∨ (∃ g ∈ G2, GR g i) ∨
        (i = r ∧ ((∃ g ∈ G2, GR g (n + 1 + m + G1.length)) ∨
          C.output = n + 1 + m + G1.length)))) :
    Rel n m k 1 F C
      ⟨G1 ++ G2.map (rg (n + 1 + m + G1.length) r), rho (n + 1 + m + G1.length) r C.output⟩ := by
  have hlen : C.gates.length = G1.length + G2.length + 1 := by rw [hC]; simp; omega
  have e2 : rho (n + 1 + m + G1.length) r (n + 1 + m + G1.length) = r := by
    unfold rho
    rw [ifn (lt_irrefl _), ifp rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (G1 ++ G2.map _).length + 1 = C.gates.length
    rw [hlen]
    simp
  · intro hF g hg
    have hg' : g ∈ G1 ++ G2.map (rg (n + 1 + m + G1.length) r) := hg
    rw [List.mem_append, List.mem_map] at hg'
    rcases hg' with h1 | ⟨g0, hg0, rfl⟩
    · exact hF g (by rw [hC]; simp [h1])
    · have hf := hF g0 (by rw [hC]; simp [hg0])
      refine ⟨hf.1, ?_⟩
      show (g0.inputs.map _).length ≤ 2
      rw [List.length_map]
      exact hf.2
  · intro hS g hg
    have hg' : g ∈ G1 ++ G2.map (rg (n + 1 + m + G1.length) r) := hg
    rw [List.mem_append, List.mem_map] at hg'
    rcases hg' with h1 | ⟨g0, hg0, rfl⟩
    · exact hS g (by rw [hC]; simp [h1])
    · exact Shp_rg _ _ _ (hS g0 (by rw [hC]; simp [hg0]))
  · intro u v
    show ((G1 ++ G2.map (rg (n + 1 + m + G1.length) r)).foldl stp
      (oneEach (k.succAbove u) v)).getD (rho (n + 1 + m + G1.length) r C.output) false =
      (C.gates.foldl stp (oneEach (k.succAbove u) v)).getD C.output false
    rw [hC, List.foldl_append, List.foldl_append, List.foldl_cons]
    have hl1 : (G1.foldl stp (oneEach (k.succAbove u) v)).length = n + 1 + m + G1.length := by
      rw [len, hx]
    refine sim True (n + 1 + m + G1.length) r (n + 1 + m + C.gates.length)
      (stp (G1.foldl stp (oneEach (k.succAbove u) v)) h) (G1.foldl stp (oneEach (k.succAbove u) v))
      ?_ ?_ ?_ ?_ G2 ?_ (fun _ _ _ _ _ => trivial) C.output (fun _ => trivial)
    · simp [stp]
    · rw [hl1]
    · rw [hl1]
      exact hr
    · intro i _
      show (G1.foldl stp (oneEach (k.succAbove u) v)).getD (rho (n + 1 + m + G1.length) r i) false =
        (G1.foldl stp (oneEach (k.succAbove u) v) ++ [_]).getD i false
      rw [getD_snoc, hl1]
      unfold rho
      by_cases h1 : i < n + 1 + m + G1.length
      · rw [ifp h1, ifp h1]
      · by_cases h2 : i = n + 1 + m + G1.length
        · rw [ifn h1, ifp h2, ifn h1, ifp h2]
          exact (hv u v).symm
        · rw [ifn h1, ifn h2, ifn h1, ifn h2]
          exact List.getD_eq_default _ _ (by rw [hl1]; omega)
    · rw [hl1, hlen]
      omega
  · intro i hi hrd
    have key : ∀ j, rho (n + 1 + m + G1.length) r j = i →
        j = i ∨ (j = n + 1 + m + G1.length ∧ r = i) := by
      intro j
      unfold rho
      split_ifs <;> omega
    rcases hrd with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ G1 ++ G2.map (rg (n + 1 + m + G1.length) r) := hg
      rw [List.mem_append, List.mem_map] at hg'
      rcases hg' with h1 | ⟨g0, hg0, rfl⟩
      · exact Or.inl ⟨g, by rw [hC]; simp [h1], hmem⟩
      · have hmem' : i ∈ g0.inputs.map (rho (n + 1 + m + G1.length) r) := hmem
        rw [List.mem_map] at hmem'
        obtain ⟨j, hj, hji⟩ := hmem'
        rcases key j hji with h3 | ⟨_, h3⟩
        · subst h3
          exact Or.inl ⟨g0, by rw [hC]; simp [hg0], hj⟩
        · subst h3
          exact Or.inl ⟨h, by rw [hC]; simp, hrin hi⟩
    · rcases key _ ho with h3 | ⟨_, h3⟩
      · exact Or.inr h3
      · subst h3
        exact Or.inl ⟨h, by rw [hC]; simp, hrin hi⟩
  · intro hf i hi hc hrd
    have e1 : rho (n + 1 + m + G1.length) r i = i := by
      unfold rho
      rw [ifp (by omega)]
    rcases hrd with ⟨g, hg, hmem⟩ | ho
    · rw [hC, List.mem_append, List.mem_cons] at hg
      rcases hg with h1 | h1 | h1
      · exact Or.inl ⟨g, List.mem_append_left _ h1, hmem⟩
      · rw [h1] at hmem
        rcases hkeep hf i hmem hi hc with ⟨g0, hg0, hm0⟩ | ⟨g0, hg0, hm0⟩ |
          ⟨heq, ⟨g0, hg0, hm0⟩ | ho⟩
        · exact Or.inl ⟨g0, List.mem_append_left _ hg0, hm0⟩
        · exact Or.inl ⟨rg (n + 1 + m + G1.length) r g0,
            List.mem_append_right _ (List.mem_map_of_mem hg0), GR_rg _ _ _ _ _ hm0 e1⟩
        · exact Or.inl ⟨rg (n + 1 + m + G1.length) r g0,
            List.mem_append_right _ (List.mem_map_of_mem hg0),
            GR_rg _ _ _ _ _ hm0 (e2.trans heq.symm)⟩
        · refine Or.inr ?_
          show rho (n + 1 + m + G1.length) r C.output = i
          rw [ho]
          exact e2.trans heq.symm
      · exact Or.inl ⟨rg (n + 1 + m + G1.length) r g,
          List.mem_append_right _ (List.mem_map_of_mem h1), GR_rg _ _ _ _ _ hmem e1⟩
    · refine Or.inr ?_
      show rho (n + 1 + m + G1.length) r C.output = i
      rw [ho]
      exact e1

theorem row_fin (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (d : ℕ) (F : Prop)
    (C C1 : Circuit) (hrel : Rel n m k d F C C1) (hd : 1 ≤ d) (hF2 : 2 ≤ d ∨ F)
    (hF : FanInTwo C) (hS : ∀ g ∈ C.gates, Shp g) (hrep : Represents A C) : Goal2 n m A k C := by
  obtain ⟨hs, hF1, hS1, hev, hbk, hfw⟩ := hrel
  have hk : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
  have hs' : C1.gates.length + d = C.gates.length := hs
  refine ⟨⟨C1.gates.map (rg k.val (n + 1 + m + C1.gates.length)),
    rho k.val (n + 1 + m + C1.gates.length) C1.output⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ C1.gates.map (rg k.val (n + 1 + m + C1.gates.length)) := hg
    rw [List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    have hf := hF1 hF g0 hg0
    refine ⟨hf.1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact hf.2
  · intro g hg
    have hg' : g ∈ C1.gates.map (rg k.val (n + 1 + m + C1.gates.length)) := hg
    rw [List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    exact Shp_rg _ _ _ (hS1 hS g0 hg0)
  · intro u v
    have hr : (C1.gates.foldl stp (oneEach (k.succAbove u) v)).getD C1.output false =
      A (k.succAbove u) v := (hev u v).trans (hrep (k.succAbove u) v)
    show ((C1.gates.map (rg k.val (n + 1 + m + C1.gates.length))).foldl stp (oneEach u v)).getD
      (rho k.val (n + 1 + m + C1.gates.length) C1.output) false = A (k.succAbove u) v
    rw [← hr]
    have hlx : (oneEach u v).length = n + m := by simp [oneEach]
    have hlx2 : (oneEach (k.succAbove u) v).length = n + 1 + m := hx k u v
    refine sim True k.val (n + 1 + m + C1.gates.length) (n + 1 + m + C1.gates.length)
      (oneEach (k.succAbove u) v) (oneEach u v)
      (by omega) (by omega) (Or.inr le_rfl) ?_ C1.gates (by omega)
      (fun _ _ _ _ _ => trivial) C1.output (fun _ => trivial)
    intro i _
    apply bool_iff
    rw [oe, oe, sa_val]
    have hu := u.isLt
    have hv := v.isLt
    unfold rho
    split_ifs <;> omega
  · show (C1.gates.map _).length + 1 ≤ C.gates.length
    rw [List.length_map]
    omega
  · intro u hu
    have hul := u.isLt
    have key : ∀ i, rho k.val (n + 1 + m + C1.gates.length) i = u.val →
        i = (k.succAbove u).val := by
      intro i
      rw [sa_val]
      unfold rho
      split_ifs <;> omega
    refine hbk _ (by have := (k.succAbove u).isLt; omega) ?_
    rcases hu with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ C1.gates.map (rg k.val (n + 1 + m + C1.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      have hmem' : u.val ∈ g0.inputs.map (rho k.val (n + 1 + m + C1.gates.length)) := hmem
      rw [List.mem_map] at hmem'
      obtain ⟨i, hi, hiu⟩ := hmem'
      have := key i hiu
      subst this
      exact Or.inl ⟨g0, hg0, hi⟩
    · exact Or.inr (key _ ho)
  · intro v hv
    have hvl := v.isLt
    have key : ∀ i, rho k.val (n + 1 + m + C1.gates.length) i = n + v.val →
        i = n + 1 + v.val := by
      intro i
      unfold rho
      split_ifs <;> omega
    refine hbk _ (by omega) ?_
    rcases hv with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ C1.gates.map (rg k.val (n + 1 + m + C1.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      have hmem' : n + v.val ∈ g0.inputs.map (rho k.val (n + 1 + m + C1.gates.length)) := hmem
      rw [List.mem_map] at hmem'
      obtain ⟨i, hi, hiu⟩ := hmem'
      have := key i hiu
      subst this
      exact Or.inl ⟨g0, hg0, hi⟩
    · exact Or.inr (key _ ho)
  · rcases hF2 with h2 | hf
    · left
      show (C1.gates.map _).length + 2 ≤ C.gates.length
      rw [List.length_map]
      omega
    · right
      intro v hv
      have hvl := v.isLt
      have e : rho k.val (n + 1 + m + C1.gates.length) (n + 1 + v.val) = n + v.val := by
        unfold rho
        rw [ifn (by omega), ifn (by omega)]
        omega
      rcases hfw hf (n + 1 + v.val) (by omega) (by omega) hv with ⟨g, hg, hmem⟩ | ho
      · exact Or.inl ⟨rg k.val (n + 1 + m + C1.gates.length) g, List.mem_map_of_mem hg,
          GR_rg _ _ _ _ _ hmem e⟩
      · refine Or.inr ?_
        show rho k.val (n + 1 + m + C1.gates.length) C1.output = n + v.val
        rw [ho]
        exact e

theorem gat (C : Circuit) (G1 G2 : List Gate) (h : Gate) (hC : C.gates = G1 ++ h :: G2) :
    gateAt C G1.length = h := by
  unfold gateAt
  rw [hC]
  simp [List.getD_eq_getElem?_getD]

theorem rb (N : ℕ) (C : Circuit) (G1 G2 : List Gate) (h : Gate) (hC : C.gates = G1 ++ h :: G2)
    (hRB : ReadsBack N C) : ∀ i ∈ h.inputs, i < N + G1.length := by
  intro i hi
  exact hRB G1.length (by rw [hC]; simp) i (by rw [gat C G1 G2 h hC]; exact hi)

theorem rd_or (N : ℕ) (C : Circuit) (G1 G2 : List Gate) (h : Gate) (hC : C.gates = G1 ++ h :: G2)
    (hRB : ReadsBack N C) (hout : C.output + 1 = N + C.size)
    (hread : ∀ j < C.size, (readsIn C (Finset.range C.size) (N + j) = 0 ↔ j + 1 = C.size)) :
    (∃ g' ∈ G2, N + G1.length ∈ g'.inputs) ∨ C.output = N + G1.length := by
  have hlen : C.size = G1.length + G2.length + 1 := by
    show C.gates.length = _
    rw [hC]
    simp
    omega
  by_cases h0 : G2.length = 0
  · right
    omega
  · left
    have hne : readsIn C (Finset.range C.size) (N + G1.length) ≠ 0 := by
      intro h1
      have := (hread G1.length (by omega)).mp h1
      omega
    unfold readsIn at hne
    rw [Ne, Finset.sum_eq_zero_iff] at hne
    push Not at hne
    obtain ⟨j', hj', hcnt⟩ := hne
    rw [Finset.mem_range] at hj'
    have hmem : N + G1.length ∈ (gateAt C j').inputs := by
      by_contra hno
      exact hcnt (List.count_eq_zero_of_not_mem hno)
    have hlt := hRB j' hj' _ hmem
    refine ⟨gateAt C j', ?_, hmem⟩
    unfold gateAt
    rw [hC, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    have e : j' - G1.length = (j' - G1.length - 1) + 1 := by omega
    rw [e, List.getElem?_cons_succ, List.getElem?_eq_getElem (by omega)]
    simp

theorem trueR (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (C : Circuit)
    (hF : FanInTwo C) (hrep : Represents A C) (hkind : ∀ g ∈ C.gates, Shp g)
    (hRB : ReadsBack (n + 1 + m) C) (hout : C.output + 1 = (n + 1 + m) + C.size)
    (hread : ∀ j < C.size, (readsIn C (Finset.range C.size) ((n + 1 + m) + j) = 0 ↔
      j + 1 = C.size))
    (hnc : ∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) v ≠ A (k.succAbove u2) v2)
    (L1 L2 : List Gate) (h2 : Gate) (hC2 : C.gates = L1 ++ h2 :: L2)
    (h2val : ∀ (u : Fin n) (v : Fin m), h2.op.eval (h2.inputs.map fun i =>
      (L1.foldl stp (oneEach (k.succAbove u) v)).getD i false) = true)
    (second : ∀ (L2a L2b : List Gate) (g3 : Gate) (rgf : Gate → Gate) (o : ℕ),
      L2 = L2a ++ g3 :: L2b →
      ∃ C'', Rel n m k 1 False ⟨(L1 ++ h2 :: L2a) ++ L2b.map rgf, o⟩ C'') :
    Goal2 n m A k C := by
  have ho : C.output ≠ n + 1 + m + L1.length := by
    intro ho
    obtain ⟨u, u2, v, v2, hne⟩ := hnc
    have ht : ∀ (u : Fin n) (v : Fin m), A (k.succAbove u) v = true := by
      intro u v
      have h0 : (C.gates.foldl stp (oneEach (k.succAbove u) v)).getD C.output false =
        A (k.succAbove u) v := hrep (k.succAbove u) v
      rw [← h0, ho, hC2, stable L1 L2 _ _ _ (by rw [hx]), h2val]
    exact hne ((ht u v).trans (ht u2 v2).symm)
  have hlen : C.gates.length = L1.length + L2.length + 1 := by rw [hC2]; simp; omega
  rcases rd_or (n + 1 + m) C L1 L2 h2 hC2 hRB hout hread with ⟨g3, hg3, hq⟩ | h
  swap
  · exact absurd h ho
  obtain ⟨L2a, L2b, hL2⟩ := List.append_of_mem hg3
  have hC3 : C.gates = (L1 ++ h2 :: L2a) ++ g3 :: L2b := by
    rw [hC2, hL2]
    simp
  have hlen2 : L2.length = L2a.length + L2b.length + 1 := by rw [hL2]; simp; omega
  have hl3 : (L1 ++ h2 :: L2a).length = L1.length + L2a.length + 1 := by
    simp
    omega
  have hg3C : g3 ∈ C.gates := by rw [hC3]; simp
  have hlt3 := rb (n + 1 + m) C _ L2b g3 hC3 hRB
  have hT4 : ∀ (u : Fin n) (v : Fin m),
      ((L1 ++ h2 :: L2a).foldl stp (oneEach (k.succAbove u) v)).getD
        (n + 1 + m + L1.length) false = true := by
    intro u v
    rw [stable L1 L2a _ _ _ (by rw [hx]), h2val]
  have hrd3 : (∃ g ∈ L2b, GR g (n + 1 + m + (L1 ++ h2 :: L2a).length)) ∨
      C.output = n + 1 + m + (L1 ++ h2 :: L2a).length := by
    rcases rd_or (n + 1 + m) C _ L2b g3 hC3 hRB hout hread with ⟨g4, hg4, h4⟩ | h
    · exact Or.inl ⟨g4, hg4, GR_of_mem g4 (hkind g4 (by rw [hC3]; simp [hg4])) _ h4⟩
    · exact Or.inr h
  rcases shape g3 (hkind g3 hg3C) with ⟨a3, b3, rfl⟩ | ⟨a3, b3, rfl⟩ | ⟨a3, rfl⟩
  · simp at hq
    have hzz : ∃ z, (a3 = n + 1 + m + L1.length ∧ b3 = z) ∨
        (b3 = n + 1 + m + L1.length ∧ a3 = z) := by
      rcases hq with h | h
      · exact ⟨b3, Or.inl ⟨h.symm, rfl⟩⟩
      · exact ⟨a3, Or.inr ⟨h.symm, rfl⟩⟩
    obtain ⟨z, hzz⟩ := hzz
    have hzmem : z ∈ (⟨GateOp.and, [a3, b3]⟩ : Gate).inputs := by
      rcases hzz with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    refine row_fin n m A k 1 True C _ (del_rel n m k True C _ L2b _ z hC3
      (Or.inl (hlt3 z hzmem)) (fun _ => hzmem) ?_ ?_) le_rfl (Or.inr trivial) hF hkind hrep
    · intro u v
      rw [ev_and]
      rcases hzz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hT4]
        rfl
      · rw [h1, h2, hT4]
        simp
    · intro _ i hi hiN hci
      have hi' := mem_of_GR _ _ hi
      simp at hi'
      have hiz : i = z := by
        rcases hzz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi' with h | h <;> omega
      exact Or.inr (Or.inr ⟨hiz, hrd3⟩)
  · simp at hq
    obtain ⟨C'', hC''⟩ := second L2a L2b ⟨GateOp.or, [a3, b3]⟩
      (rg (n + 1 + m + (L1 ++ h2 :: L2a).length) (n + 1 + m + L1.length))
      (rho (n + 1 + m + (L1 ++ h2 :: L2a).length) (n + 1 + m + L1.length) C.output) hL2
    refine row_fin n m A k (1 + 1) False C C'' (rel_trans n m k 1 1 False C _ C''
      (del_rel n m k False C _ L2b _ (n + 1 + m + L1.length) hC3
      (Or.inl (by rw [hl3]; omega)) (by intro h; omega) ?_ (fun hf => hf.elim)) hC'')
      (by omega) (Or.inl le_rfl) hF hkind hrep
    intro u v
    rw [ev_or]
    rcases hq with h1 | h1
    · rw [← h1, hT4]
      rfl
    · rw [← h1, hT4]
      simp
  · simp at hq
    refine row_fin n m A k 1 True C _ (del_rel n m k True C _ L2b _ (n + 1 + m + C.gates.length)
      hC3 (Or.inr le_rfl) (by intro h; omega) ?_ ?_) le_rfl (Or.inr trivial) hF hkind hrep
    · intro u v
      rw [ev_not1, ← hq, hT4, List.getD_eq_default _ _ (by rw [len, hx, hl3]; omega)]
      rfl
    · intro _ i hi hiN hci
      have hi' := mem_of_GR _ _ hi
      simp at hi'
      omega

theorem core (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (C : Circuit)
    (hF : FanInTwo C) (hrep : Represents A C) (hkind : ∀ g ∈ C.gates, Shp g)
    (hRB : ReadsBack (n + 1 + m) C) (hout : C.output + 1 = (n + 1 + m) + C.size)
    (hread : ∀ j < C.size, (readsIn C (Finset.range C.size) ((n + 1 + m) + j) = 0 ↔
      j + 1 = C.size))
    (hlist : ∃ g ∈ C.gates, k.val ∈ g.inputs)
    (hnc : ∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) :
    Goal2 n m A k C := by
  have hkl : k.val < n + 1 := k.isLt
  obtain ⟨g, hg, hc⟩ := hlist
  obtain ⟨G1, G2, hC⟩ := List.append_of_mem hg
  have hlen : C.gates.length = G1.length + G2.length + 1 := by rw [hC]; simp; omega
  have hW1 : ∀ (u : Fin n) (v : Fin m),
      (G1.foldl stp (oneEach (k.succAbove u) v)).length = n + 1 + m + G1.length := by
    intro u v
    rw [len, hx]
  have hrd := rd_or (n + 1 + m) C G1 G2 g hC hRB hout hread
  have hrdG : (∃ g' ∈ G2, GR g' (n + 1 + m + G1.length)) ∨ C.output = n + 1 + m + G1.length := by
    rcases hrd with ⟨g4, hg4, h4⟩ | h
    · exact Or.inl ⟨g4, hg4, GR_of_mem g4 (hkind g4 (by rw [hC]; simp [hg4])) _ h4⟩
    · exact Or.inr h
  have hlt := rb (n + 1 + m) C G1 G2 g hC hRB
  have fin : ∀ C1, Rel n m k 1 True C C1 → Goal2 n m A k C :=
    fun C1 h => row_fin n m A k 1 True C C1 h le_rfl (Or.inr trivial) hF hkind hrep
  have fin01 : ∀ C' C1, Rel n m k 0 True C C' → Rel n m k 1 True C' C1 → Goal2 n m A k C :=
    fun C' C1 h h' => row_fin n m A k (0 + 1) True C C1 (rel_trans n m k 0 1 True C C' C1 h h')
      le_rfl (Or.inr trivial) hF hkind hrep
  have hconst : ∀ b : Bool, (∀ (u : Fin n) (v : Fin m),
      g.op.eval (g.inputs.map fun i => (G1.foldl stp (oneEach (k.succAbove u) v)).getD i false) = b) →
      C.output ≠ n + 1 + m + G1.length := by
    intro b hb ho
    obtain ⟨u, u2, v, v2, hne⟩ := hnc
    have ht : ∀ (u : Fin n) (v : Fin m), A (k.succAbove u) v = b := by
      intro u v
      have h0 : (C.gates.foldl stp (oneEach (k.succAbove u) v)).getD C.output false =
        A (k.succAbove u) v := hrep (k.succAbove u) v
      rw [← h0, ho, hC, stable G1 G2 _ _ _ (by rw [hx]), hb]
    exact hne ((ht u v).trans (ht u2 v2).symm)
  have getreader : C.output ≠ n + 1 + m + G1.length →
      ∃ (g' : Gate) (G2a G2b : List Gate), G2 = G2a ++ g' :: G2b ∧
        n + 1 + m + G1.length ∈ g'.inputs := by
    intro ho
    rcases hrd with ⟨g', hg', hp'⟩ | h
    · obtain ⟨G2a, G2b, hG2⟩ := List.append_of_mem hg'
      exact ⟨g', G2a, G2b, hG2, hp'⟩
    · exact absurd h ho
  rcases shape g (hkind g hg) with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, rfl⟩
  · simp at hc
    have hxx : ∃ x, (a = k.val ∧ b = x) ∨ (b = k.val ∧ a = x) := by
      rcases hc with h | h
      · exact ⟨b, Or.inl ⟨h.symm, rfl⟩⟩
      · exact ⟨a, Or.inr ⟨h.symm, rfl⟩⟩
    obtain ⟨x, hxx⟩ := hxx
    have hval : ∀ (u : Fin n) (v : Fin m), (⟨GateOp.and, [a, b]⟩ : Gate).op.eval
        ((⟨GateOp.and, [a, b]⟩ : Gate).inputs.map fun i =>
          (G1.foldl stp (oneEach (k.succAbove u) v)).getD i false) = false := by
      intro u v
      rw [ev_and]
      rcases hxx with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1, ck]
        rfl
      · rw [h1, ck]
        simp
    have hxmem : x ∈ (⟨GateOp.and, [a, b]⟩ : Gate).inputs := by
      rcases hxx with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    have hcols : ∀ i, GR (⟨GateOp.and, [a, b]⟩ : Gate) i → n + 1 ≤ i → i = x := by
      intro i hi hci
      have hi' := mem_of_GR _ _ hi
      simp at hi'
      rcases hxx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi' with h | h <;> omega
    by_cases hxc : n + 1 ≤ x ∧ x < n + 1 + m
    swap
    · apply fin
      refine del_rel n m k True C G1 G2 _ (n + 1 + m + C.gates.length) hC (Or.inr le_rfl)
        (by intro h; omega) ?_ ?_
      · intro u v
        rw [hval u v]
        symm
        exact List.getD_eq_default _ _ (by rw [hW1]; omega)
      · intro _ i hi hiN hci
        have := hcols i hi hci
        subst this
        exact absurd ⟨hci, hiN⟩ hxc
    · obtain ⟨g', G2a, G2b, hG2, hp'⟩ := getreader (hconst false hval)
      have hC2 : C.gates = (G1 ++ ⟨GateOp.and, [a, b]⟩ :: G2a) ++ g' :: G2b := by
        rw [hC, hG2]
        simp
      have hlen2 : G2.length = G2a.length + G2b.length + 1 := by rw [hG2]; simp; omega
      have hg'C : g' ∈ C.gates := by rw [hC2]; simp
      have hl2 : ∀ g0 : Gate, (G1 ++ g0 :: G2a).length = G1.length + G2a.length + 1 := by
        intro g0
        simp
        omega
      have hlt' := rb (n + 1 + m) C _ G2b g' hC2 hRB
      have hrd' : (∃ g0 ∈ G2b, GR g0 (n + 1 + m + (G1 ++ (⟨GateOp.and, [a, b]⟩ : Gate) ::
          G2a).length)) ∨ C.output = n + 1 + m + (G1 ++ (⟨GateOp.and, [a, b]⟩ : Gate) ::
          G2a).length := by
        rcases rd_or (n + 1 + m) C _ G2b g' hC2 hRB hout hread with ⟨g4, hg4, h4⟩ | h
        · exact Or.inl ⟨g4, hg4, GR_of_mem g4 (hkind g4 (by rw [hC2]; simp [hg4])) _ h4⟩
        · exact Or.inr h
      rw [hl2] at hlt' hrd'
      have hT2 : ∀ (u : Fin n) (v : Fin m),
          ((G1 ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: G2a).foldl stp
            (oneEach (k.succAbove u) v)).getD (n + 1 + m + G1.length) false = false := by
        intro u v
        rw [stable G1 G2a _ _ _ (by rw [hx]), hval u v]
      have hmB : Rel n m k 0 True C
          ⟨G1 ++ ⟨GateOp.and, [n + 1 + m + C.gates.length, x]⟩ :: G2, C.output⟩ := by
        refine mod_rel n m k True C G1 G2 _ _ hC ⟨by simp, by simp⟩ (Or.inl ⟨Or.inl rfl, rfl⟩)
          ?_ ?_ ?_
        · intro u v
          rw [hval u v, ev_and, List.getD_eq_default _ _ (by rw [hW1]; omega)]
          rfl
        · intro i hi hiN
          simp at hi
          rcases hi with h | h
          · omega
          · rw [h]
            exact Or.inl ⟨_, hg, hxmem⟩
        · intro _ i hi hiN hci
          have := hcols i hi hci
          exact Or.inl ⟨Or.inl rfl, by simp [this]⟩
      have hTB : ∀ (u : Fin n) (v : Fin m),
          ((G1 ++ (⟨GateOp.and, [n + 1 + m + C.gates.length, x]⟩ : Gate) :: G2a).foldl stp
            (oneEach (k.succAbove u) v)).getD (n + 1 + m + G1.length) false = false := by
        intro u v
        rw [stable G1 G2a _ _ _ (by rw [hx]), ev_and,
          List.getD_eq_default _ _ (by rw [hW1]; omega)]
        rfl
      rcases shape g' (hkind g' hg'C) with ⟨a', b', rfl⟩ | ⟨a', b', rfl⟩ | ⟨a', rfl⟩
      · simp at hp'
        have hyy : ∃ y, (a' = n + 1 + m + G1.length ∧ b' = y) ∨
            (b' = n + 1 + m + G1.length ∧ a' = y) := by
          rcases hp' with h | h
          · exact ⟨b', Or.inl ⟨h.symm, rfl⟩⟩
          · exact ⟨a', Or.inr ⟨h.symm, rfl⟩⟩
        obtain ⟨y, hyy⟩ := hyy
        have hymem : y ∈ (⟨GateOp.and, [a', b']⟩ : Gate).inputs := by
          rcases hyy with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
        have hcols' : ∀ i, GR (⟨GateOp.and, [a', b']⟩ : Gate) i → i < n + 1 + m → i = y := by
          intro i hi hci
          have hi' := mem_of_GR _ _ hi
          simp at hi'
          rcases hyy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi' with h | h <;> omega
        by_cases hyc : (n + 1 ≤ y ∧ y < n + 1 + m) ∧ y ≠ x
        · have hm : Rel n m k 0 True C ⟨G1 ++ ⟨GateOp.and, [x, y]⟩ :: G2, C.output⟩ := by
            refine mod_rel n m k True C G1 G2 _ _ hC ⟨by simp, by simp⟩
              (Or.inl ⟨Or.inl rfl, rfl⟩) ?_ ?_ ?_
            · intro u v
              rw [hval u v, ev_and]
              exact cc n m k u v G1 x y hxc.1 hxc.2 hyc.1.1 hyc.1.2 (Ne.symm hyc.2)
            · intro i hi hiN
              simp at hi
              rcases hi with h | h
              · rw [h]
                exact Or.inl ⟨_, hg, hxmem⟩
              · rw [h]
                exact Or.inl ⟨_, hg'C, hymem⟩
            · intro _ i hi hiN hci
              have := hcols i hi hci
              exact Or.inl ⟨Or.inl rfl, by simp [this]⟩
          have hT3 : ∀ (u : Fin n) (v : Fin m),
              ((G1 ++ (⟨GateOp.and, [x, y]⟩ : Gate) :: G2a).foldl stp
                (oneEach (k.succAbove u) v)).getD (n + 1 + m + G1.length) false = false := by
            intro u v
            rw [stable G1 G2a _ _ _ (by rw [hx]), ev_and]
            exact cc n m k u v G1 x y hxc.1 hxc.2 hyc.1.1 hyc.1.2 (Ne.symm hyc.2)
          refine fin01 _ _ hm
            (del_rel n m k True ⟨G1 ++ ⟨GateOp.and, [x, y]⟩ :: G2, C.output⟩
            (G1 ++ ⟨GateOp.and, [x, y]⟩ :: G2a) G2b ⟨GateOp.and, [a', b']⟩
            (n + 1 + m + G1.length)
            (by show G1 ++ _ :: G2 = _; rw [hG2]; simp) (Or.inl (by rw [hl2]; omega))
            (by intro h; omega) ?_ ?_)
          · intro u v
            rw [ev_and]
            rcases hyy with ⟨h1, _⟩ | ⟨h1, _⟩
            · rw [h1, hT3]
              rfl
            · rw [h1, hT3]
              simp
          · intro _ i hi hiN hci
            have := hcols' i hi hiN
            exact Or.inl ⟨⟨GateOp.and, [x, y]⟩, by simp, Or.inl ⟨Or.inl rfl, by simp [this]⟩⟩
        · refine fin01 _ _ hmB
            (del_rel n m k True
            ⟨G1 ++ ⟨GateOp.and, [n + 1 + m + C.gates.length, x]⟩ :: G2, C.output⟩
            (G1 ++ ⟨GateOp.and, [n + 1 + m + C.gates.length, x]⟩ :: G2a) G2b
            ⟨GateOp.and, [a', b']⟩ (n + 1 + m + G1.length)
            (by show G1 ++ _ :: G2 = _; rw [hG2]; simp) (Or.inl (by rw [hl2]; omega))
            (by intro h; omega) ?_ ?_)
          · intro u v
            rw [ev_and]
            rcases hyy with ⟨h1, _⟩ | ⟨h1, _⟩
            · rw [h1, hTB]
              rfl
            · rw [h1, hTB]
              simp
          · intro _ i hi hiN hci
            have hy := hcols' i hi hiN
            have hix : i = x := by
              by_contra hne
              exact hyc ⟨⟨by omega, by omega⟩, by omega⟩
            exact Or.inl ⟨⟨GateOp.and, [n + 1 + m + C.gates.length, x]⟩, by simp,
              Or.inl ⟨Or.inl rfl, by simp [hix]⟩⟩
      · simp at hp'
        have hyy : ∃ y, (a' = n + 1 + m + G1.length ∧ b' = y) ∨
            (b' = n + 1 + m + G1.length ∧ a' = y) := by
          rcases hp' with h | h
          · exact ⟨b', Or.inl ⟨h.symm, rfl⟩⟩
          · exact ⟨a', Or.inr ⟨h.symm, rfl⟩⟩
        obtain ⟨y, hyy⟩ := hyy
        have hymem : y ∈ (⟨GateOp.or, [a', b']⟩ : Gate).inputs := by
          rcases hyy with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
        have hcols' : ∀ i, GR (⟨GateOp.or, [a', b']⟩ : Gate) i → i < n + 1 + m → i = y := by
          intro i hi hci
          have hi' := mem_of_GR _ _ hi
          simp at hi'
          rcases hyy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi' with h | h <;> omega
        refine fin01 _ _ hmB
          (del_rel n m k True
          ⟨G1 ++ ⟨GateOp.and, [n + 1 + m + C.gates.length, x]⟩ :: G2, C.output⟩
          (G1 ++ ⟨GateOp.and, [n + 1 + m + C.gates.length, x]⟩ :: G2a) G2b
          ⟨GateOp.or, [a', b']⟩ y
          (by show G1 ++ _ :: G2 = _; rw [hG2]; simp)
          (Or.inl (by rw [hl2]; exact hlt' y hymem))
          (fun _ => hymem) ?_ ?_)
        · intro u v
          rw [ev_or]
          rcases hyy with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2, hTB]
            rfl
          · rw [h1, h2, hTB]
            simp
        · intro _ i hi hiN hci
          have hy := hcols' i hi hiN
          refine Or.inr (Or.inr ⟨hy, ?_⟩)
          rw [hl2]
          exact hrd'
      · simp at hp'
        refine trueR n m A k C hF hrep hkind hRB hout hread hnc _ G2b _ hC2 ?_ ?_
        · intro u v
          rw [ev_not1, ← hp', hT2]
          rfl
        · intro L2a L2b g3 rgf o hL
          refine ⟨_, del_rel n m k False
            ⟨((G1 ++ ⟨GateOp.and, [a, b]⟩ :: G2a) ++ ⟨GateOp.not, [a']⟩ :: L2a) ++ L2b.map rgf, o⟩
            G1 (G2a ++ ⟨GateOp.not, [a']⟩ :: L2a ++ L2b.map rgf) ⟨GateOp.and, [a, b]⟩
            (n + 1 + m + C.gates.length) (by simp) (Or.inr ?_) (by intro h; omega) ?_
            (fun hf => hf.elim)⟩
          · have e : C.gates.length = G1.length + G2a.length + L2a.length + L2b.length + 3 := by
              rw [hC2, hL]
              simp
              omega
            rw [e]
            simp
            omega
          · intro u v
            rw [hval u v]
            symm
            exact List.getD_eq_default _ _ (by rw [hW1]; omega)
  · simp at hc
    have hxx : ∃ x, (a = k.val ∧ b = x) ∨ (b = k.val ∧ a = x) := by
      rcases hc with h | h
      · exact ⟨b, Or.inl ⟨h.symm, rfl⟩⟩
      · exact ⟨a, Or.inr ⟨h.symm, rfl⟩⟩
    obtain ⟨x, hxx⟩ := hxx
    have hval : ∀ (u : Fin n) (v : Fin m), (⟨GateOp.or, [a, b]⟩ : Gate).op.eval
        ((⟨GateOp.or, [a, b]⟩ : Gate).inputs.map fun i =>
          (G1.foldl stp (oneEach (k.succAbove u) v)).getD i false) =
        (G1.foldl stp (oneEach (k.succAbove u) v)).getD x false := by
      intro u v
      rw [ev_or]
      rcases hxx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, ck]
        rfl
      · rw [h1, h2, ck]
        simp
    have hxmem : x ∈ (⟨GateOp.or, [a, b]⟩ : Gate).inputs := by
      rcases hxx with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    have hcols : ∀ i, GR (⟨GateOp.or, [a, b]⟩ : Gate) i → n + 1 ≤ i → i = x := by
      intro i hi hci
      have hi' := mem_of_GR _ _ hi
      simp at hi'
      rcases hxx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi' with h | h <;> omega
    apply fin
    refine del_rel n m k True C G1 G2 _ x hC (Or.inl (hlt x hxmem)) (fun _ => hxmem) hval ?_
    intro _ i hi hiN hci
    exact Or.inr (Or.inr ⟨hcols i hi hci, hrdG⟩)
  · simp at hc
    have hval : ∀ (u : Fin n) (v : Fin m), (⟨GateOp.not, [a]⟩ : Gate).op.eval
        ((⟨GateOp.not, [a]⟩ : Gate).inputs.map fun i =>
          (G1.foldl stp (oneEach (k.succAbove u) v)).getD i false) = true := by
      intro u v
      rw [ev_not1, ← hc, ck]
      rfl
    obtain ⟨g', G2a, G2b, hG2, hp'⟩ := getreader (hconst true hval)
    have hC2 : C.gates = (G1 ++ ⟨GateOp.not, [a]⟩ :: G2a) ++ g' :: G2b := by
      rw [hC, hG2]
      simp
    have hlen2 : G2.length = G2a.length + G2b.length + 1 := by rw [hG2]; simp; omega
    have hg'C : g' ∈ C.gates := by rw [hC2]; simp
    have hl2 : ∀ g0 : Gate, (G1 ++ g0 :: G2a).length = G1.length + G2a.length + 1 := by
      intro g0
      simp
      omega
    have hlt' := rb (n + 1 + m) C _ G2b g' hC2 hRB
    have hrd' : (∃ g0 ∈ G2b, GR g0 (n + 1 + m + (G1 ++ (⟨GateOp.not, [a]⟩ : Gate) ::
        G2a).length)) ∨ C.output = n + 1 + m + (G1 ++ (⟨GateOp.not, [a]⟩ : Gate) ::
        G2a).length := by
      rcases rd_or (n + 1 + m) C _ G2b g' hC2 hRB hout hread with ⟨g4, hg4, h4⟩ | h
      · exact Or.inl ⟨g4, hg4, GR_of_mem g4 (hkind g4 (by rw [hC2]; simp [hg4])) _ h4⟩
      · exact Or.inr h
    rw [hl2] at hlt'
    have hT : ∀ (u : Fin n) (v : Fin m),
        ((G1 ++ (⟨GateOp.not, [a]⟩ : Gate) :: G2a).foldl stp
          (oneEach (k.succAbove u) v)).getD (n + 1 + m + G1.length) false = true := by
      intro u v
      rw [stable G1 G2a _ _ _ (by rw [hx]), hval u v]
    rcases shape g' (hkind g' hg'C) with ⟨a', b', rfl⟩ | ⟨a', b', rfl⟩ | ⟨a', rfl⟩
    · simp at hp'
      have hyy : ∃ y, (a' = n + 1 + m + G1.length ∧ b' = y) ∨
          (b' = n + 1 + m + G1.length ∧ a' = y) := by
        rcases hp' with h | h
        · exact ⟨b', Or.inl ⟨h.symm, rfl⟩⟩
        · exact ⟨a', Or.inr ⟨h.symm, rfl⟩⟩
      obtain ⟨y, hyy⟩ := hyy
      have hymem : y ∈ (⟨GateOp.and, [a', b']⟩ : Gate).inputs := by
        rcases hyy with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
      have hcols' : ∀ i, GR (⟨GateOp.and, [a', b']⟩ : Gate) i → i < n + 1 + m → i = y := by
        intro i hi hci
        have hi' := mem_of_GR _ _ hi
        simp at hi'
        rcases hyy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi' with h | h <;> omega
      apply fin
      refine del_rel n m k True C _ G2b _ y hC2 (Or.inl (by rw [hl2]; exact hlt' y hymem))
        (fun _ => hymem) ?_ ?_
      · intro u v
        rw [ev_and]
        rcases hyy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2, hT]
          rfl
        · rw [h1, h2, hT]
          simp
      · intro _ i hi hiN hci
        exact Or.inr (Or.inr ⟨hcols' i hi hiN, hrd'⟩)
    · simp at hp'
      have hyy : ∃ y, (a' = n + 1 + m + G1.length ∧ b' = y) ∨
          (b' = n + 1 + m + G1.length ∧ a' = y) := by
        rcases hp' with h | h
        · exact ⟨b', Or.inl ⟨h.symm, rfl⟩⟩
        · exact ⟨a', Or.inr ⟨h.symm, rfl⟩⟩
      obtain ⟨y, hyy⟩ := hyy
      have hcols' : ∀ i, GR (⟨GateOp.or, [a', b']⟩ : Gate) i → i < n + 1 + m → i = y := by
        intro i hi hci
        have hi' := mem_of_GR _ _ hi
        simp at hi'
        rcases hyy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi' with h | h <;> omega
      have h2val : ∀ (u : Fin n) (v : Fin m), (⟨GateOp.or, [a', b']⟩ : Gate).op.eval
          ((⟨GateOp.or, [a', b']⟩ : Gate).inputs.map fun i =>
            ((G1 ++ (⟨GateOp.not, [a]⟩ : Gate) :: G2a).foldl stp
              (oneEach (k.succAbove u) v)).getD i false) = true := by
        intro u v
        rw [ev_or]
        rcases hyy with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [h1, hT]
          rfl
        · rw [h1, hT]
          simp
      by_cases hyc : n + 1 ≤ y ∧ y < n + 1 + m
      swap
      · apply fin
        refine del_rel n m k True C _ G2b _ (n + 1 + m + G1.length) hC2
          (Or.inl (by rw [hl2]; omega)) (by intro h; omega) ?_ ?_
        · intro u v
          rw [h2val, hT]
        · intro _ i hi hiN hci
          have := hcols' i hi hiN
          subst this
          exact absurd ⟨hci, hiN⟩ hyc
      · refine trueR n m A k C hF hrep hkind hRB hout hread hnc _ G2b _ hC2 h2val ?_
        intro L2a L2b g3 rgf o hL
        refine ⟨_, del_rel n m k False
          ⟨((G1 ++ ⟨GateOp.not, [a]⟩ :: G2a) ++ ⟨GateOp.or, [a', b']⟩ :: L2a) ++ L2b.map rgf, o⟩
          (G1 ++ ⟨GateOp.not, [a]⟩ :: G2a) (L2a ++ L2b.map rgf) ⟨GateOp.or, [a', b']⟩
          (n + 1 + m + G1.length) (by simp) (Or.inl (by rw [hl2]; omega)) (by intro h; omega) ?_
          (fun hf => hf.elim)⟩
        intro u v
        rw [h2val, hT]
    · simp at hp'
      apply fin
      refine del_rel n m k True C _ G2b _ (n + 1 + m + C.gates.length) hC2 (Or.inr le_rfl)
        (by intro h; omega) ?_ ?_
      · intro u v
        rw [ev_not1, ← hp', hT, List.getD_eq_default _ _ (by rw [len, hx, hl2]; omega)]
        rfl
      · intro _ i hi hiN hci
        have hi' := mem_of_GR _ _ hi
        simp at hi'
        omega

theorem main : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + 1 + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + 1 + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + 1 + m))) → ((∃ g ∈ C.gates, k.val ∈ g.inputs) ∨ C.output = k.val) → (∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (k.succAbove u).val ∈ g.inputs) ∨ C.output = (k.succAbove u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val))) ∧ (C2.size + 2 ≤ C.size ∨ ∀ v : Fin m, ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val)) → ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val))) := by
  intro n m A k C hF hrep hred hk hnc
  have hkl : k.val < n + 1 := k.isLt
  rcases hred with ⟨hkind, hRB, hpos, hout, hread⟩ | ⟨hz, ho⟩
  · have hlist : ∃ g ∈ C.gates, k.val ∈ g.inputs := by
      rcases hk with h | h
      · exact h
      · exfalso
        omega
    obtain ⟨C2, hF2, hS2, hrep2, hsz2, hu2, hv2, hlast⟩ :=
      core n m A k C hF hrep hkind hRB hout hread hlist hnc
    obtain ⟨D, hFD, hrepD, hszD, hredD, hb, hf⟩ :=
      n_main n m (fun u v => A (k.succAbove u) v) C2 hF2 hrep2 hnc
    have RRofRd : ∀ i, Rd C i → RR C i := by
      intro i h
      rcases h with ⟨g, hg, hi⟩ | h
      · exact Or.inl ⟨g, hg, GR_of_mem g (hkind g hg) i hi⟩
      · exact Or.inr h
    have RdofRR : ∀ (i : ℕ), RR C2 i → Rd C2 i := by
      intro i h
      rcases h with ⟨g, hg, hi⟩ | h
      · exact Or.inl ⟨g, hg, mem_of_GR g i hi⟩
      · exact Or.inr h
    refine ⟨D, hFD, hrepD, hredD, by omega, ?_, ?_, ?_⟩
    · intro u hu
      exact hu2 u (RdofRR _ (hb u.val (by have := u.isLt; omega) hu))
    · intro v hv
      exact hv2 v (RdofRR _ (hb (n + v.val) (by have := v.isLt; omega) hv))
    · rcases hlast with h2 | hfw
      · left
        omega
      · rcases hf with h3 | hf2
        · left
          omega
        · right
          intro v hv
          have hvl := v.isLt
          exact hf2 (n + v.val) (by omega) (hfw v (RRofRd _ hv))
  · exfalso
    have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero hz
    have hko : C.output = k.val := by
      rcases hk with ⟨g, hg, _⟩ | h
      · rw [hnil] at hg
        simp at hg
      · exact h
    obtain ⟨u, u2, v, v2, hne⟩ := hnc
    have ht : ∀ (u : Fin n) (v : Fin m), A (k.succAbove u) v = false := by
      intro u v
      have h0 : (C.gates.foldl stp (oneEach (k.succAbove u) v)).getD C.output false =
        A (k.succAbove u) v := hrep (k.succAbove u) v
      rw [← h0, hko, ck]
    exact hne ((ht u v).trans (ht u2 v2).symm)

end PEqualNP.Outside.L_meta_24694

theorem PEqualNP.Outside.L_meta_24694 : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + 1 + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + 1 + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + 1 + m))) → ((∃ g ∈ C.gates, k.val ∈ g.inputs) ∨ C.output = k.val) → (∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (k.succAbove u).val ∈ g.inputs) ∨ C.output = (k.succAbove u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val))) ∧ (C2.size + 2 ≤ C.size ∨ ∀ v : Fin m, ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val)) → ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val))) :=
  PEqualNP.Outside.L_meta_24694.main

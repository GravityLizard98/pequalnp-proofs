import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19197

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

def rd (W : List Bool) : Option ℕ → Bool
  | some j => W.getD j false
  | none => false

theorem rd_getD (W : List Bool) (o : Option ℕ) : W.getD (o.getD W.length) false = rd W o := by
  cases o with
  | none => exact List.getD_eq_default _ _ le_rfl
  | some j => rfl

theorem rd_pre (G H : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ j, o = some j → j < x.length + G.length) :
    rd ((G ++ H).foldl stp x) o = rd (G.foldl stp x) o := by
  cases o with
  | none => rfl
  | some j => exact pre G H x j (h j rfl)

theorem emit (G : List Gate) (x : List Bool) (op : GateOp) (rs : List (Option ℕ)) :
    ((G ++ [(⟨op, rs.map fun o => o.getD (x.length + G.length)⟩ : Gate)]).foldl stp x).getD
        (x.length + G.length) false = op.eval (rs.map fun o => rd (G.foldl stp x) o) := by
  rw [top]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro o _
  have := rd_getD (G.foldl stp x) o
  rw [len] at this
  exact this

theorem and_ev (l : List ℕ) (f : ℕ → Bool) : GateOp.and.eval (l.map f) = l.all f := by
  simp [GateOp.eval]

theorem or_ev (l : List ℕ) (f : ℕ → Bool) : GateOp.or.eval (l.map f) = l.any f := by
  simp [GateOp.eval]

theorem dm_or (l : List ℕ) (v : ℕ → Bool) (f d : ℕ → Bool)
    (h1 : ∀ w ∈ l, v w = true → d w = !f w) (h2 : ∀ w ∈ l, v w = false → f w = false) :
    (l.filter v).all d = !(l.any f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih := ih (fun w hw => h1 w (List.mem_cons_of_mem _ hw))
      (fun w hw => h2 w (List.mem_cons_of_mem _ hw))
    by_cases hv : v a = true
    · rw [List.filter_cons_of_pos hv, List.all_cons, List.any_cons, ih, h1 a (by simp) hv]
      cases f a <;> simp
    · have hv' : v a = false := by simpa using hv
      rw [List.filter_cons_of_neg hv, List.any_cons, ih, h2 a (by simp) hv']
      simp

theorem dm_and (l : List ℕ) (f d : ℕ → Bool) (h1 : ∀ w ∈ l, d w = !f w) :
    l.any d = !(l.all f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.all_cons, ih (fun w hw => h1 w (List.mem_cons_of_mem _ hw)),
      h1 a (by simp)]
    cases f a <;> simp

theorem or2 (W : List Bool) (a b : ℕ) :
    (⟨GateOp.or, [a, b]⟩ : Gate).op.eval ((⟨GateOp.or, [a, b]⟩ : Gate).inputs.map fun i => W.getD i false)
      = (W.getD a false || W.getD b false) := by
  simp [GateOp.eval]

theorem chainE (N : ℕ) (f : ℕ → ℕ) : ∀ (k : ℕ) (G : List Gate), (∀ i, i ≤ k → f i < N) →
    ∃ (L : List Gate) (π : ℕ → ℕ), L.length = k ∧ (∀ g ∈ L, M2 g) ∧
      (∀ j, j ≤ k → π j < N + G.length + k) ∧
      ∀ x : List Bool, x.length = N → ∀ j, j ≤ k →
        (((G ++ L).foldl stp x).getD (π j) false = true ↔
          ∃ i, i ≤ j ∧ x.getD (f i) false = true) := by
  intro k
  induction k with
  | zero =>
    intro G hf
    refine ⟨[], fun _ => f 0, rfl, by simp, ?_, ?_⟩
    · intro j _
      show f 0 < N + G.length + 0
      have := hf 0 le_rfl
      omega
    · intro x hx j hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [List.append_nil, inp G x (f 0) (by rw [hx]; exact hf 0 le_rfl)]
      constructor
      · intro h; exact ⟨0, le_rfl, h⟩
      · rintro ⟨i, hi, h⟩
        have : i = 0 := by omega
        subst this; exact h
  | succ k ih =>
    intro G hf
    obtain ⟨L, π, hL, hm, hb, hv⟩ := ih G (fun i hi => hf i (by omega))
    refine ⟨L ++ [⟨GateOp.or, [π k, f (k + 1)]⟩],
      fun j => if j ≤ k then π j else N + G.length + k, by simp [hL], ?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hm g hg
      · simp at hg; subst hg; simp [M2]
    · intro j hj
      dsimp only
      split_ifs with h
      · have := hb j h; omega
      · omega
    · intro x hx j hj
      dsimp only
      rw [← List.append_assoc]
      by_cases h : j ≤ k
      · rw [ifp h, pre (G ++ L) _ x _ (by rw [hx, List.length_append, hL]; have := hb j h; omega)]
        exact hv x hx j h
      · have hj' : j = k + 1 := by omega
        subst hj'
        rw [ifn h]
        have e : N + G.length + k = x.length + (G ++ L).length := by
          rw [hx, List.length_append, hL]; omega
        rw [e, top, or2, Bool.or_eq_true, hv x hx k le_rfl,
          inp (G ++ L) x (f (k + 1)) (by rw [hx]; exact hf _ le_rfl)]
        constructor
        · rintro (⟨i, hi, h⟩ | h)
          · exact ⟨i, by omega, h⟩
          · exact ⟨k + 1, le_rfl, h⟩
        · rintro ⟨i, hi, h⟩
          by_cases hik : i ≤ k
          · exact Or.inl ⟨i, hik, h⟩
          · have : i = k + 1 := by omega
            subst this; exact Or.inr h

theorem combE (N : ℕ) (p q : ℕ → ℕ) : ∀ (k : ℕ) (G : List Gate),
    (∀ e, e < k → p e < N + G.length ∧ q e < N + G.length) →
    ∃ (L : List Gate) (τ : ℕ → ℕ), L.length = k ∧ (∀ g ∈ L, M2 g) ∧
      (∀ e, e < k → τ e < N + G.length + k) ∧
      ∀ x : List Bool, x.length = N → ∀ e, e < k →
        ((G ++ L).foldl stp x).getD (τ e) false =
          ((G.foldl stp x).getD (p e) false || (G.foldl stp x).getD (q e) false) := by
  intro k
  induction k with
  | zero =>
    intro G _
    exact ⟨[], fun _ => 0, rfl, by simp, by intro e he; omega, by intro x _ e he; omega⟩
  | succ k ih =>
    intro G hf
    obtain ⟨L, τ, hL, hm, hb, hv⟩ := ih G (fun e he => hf e (by omega))
    refine ⟨L ++ [⟨GateOp.or, [p k, q k]⟩],
      fun e => if e < k then τ e else N + G.length + k, by simp [hL], ?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hm g hg
      · simp at hg; subst hg; simp [M2]
    · intro e he
      dsimp only
      split_ifs with h
      · have := hb e h; omega
      · omega
    · intro x hx e he
      dsimp only
      rw [← List.append_assoc]
      by_cases h : e < k
      · rw [ifp h, pre (G ++ L) _ x _ (by rw [hx, List.length_append, hL]; have := hb e h; omega)]
        exact hv x hx e h
      · have he' : e = k := by omega
        subst he'
        rw [ifn h]
        have e1 : N + G.length + e = x.length + (G ++ L).length := by
          rw [hx, List.length_append, hL]; omega
        rw [e1, top, or2, pre G L x _ (by rw [hx]; exact (hf e (by omega)).1),
          pre G L x _ (by rw [hx]; exact (hf e (by omega)).2)]

theorem block (N a c : ℕ) (hc : 2 ≤ c) (hac : a + c ≤ N) (G : List Gate) :
    ∃ (L : List Gate) (ν : ℕ → ℕ), L.length = 3 * c - 6 ∧ (∀ g ∈ L, M2 g) ∧
      (∀ i, i < c → ν i < N + G.length + L.length) ∧
      ∀ x : List Bool, x.length = N → ∀ u, u < c →
        (∀ i, i < c → (x.getD (a + i) false = true ↔ i = u)) →
        ∀ i, i < c → (((G ++ L).foldl stp x).getD (ν i) false = true ↔ i ≠ u) := by
  obtain ⟨L1, π, hL1, hm1, hb1, hv1⟩ := chainE N (fun i => a + i) (c - 2) G (fun i hi => by omega)
  obtain ⟨L2, σ, hL2, hm2, hb2, hv2⟩ :=
    chainE N (fun i => a + (c - 1 - i)) (c - 2) (G ++ L1) (fun i hi => by omega)
  rw [List.length_append, hL1] at hb2
  have hpq : ∀ e, e < c - 2 → π e < N + (G ++ L1 ++ L2).length ∧
      σ (c - 3 - e) < N + (G ++ L1 ++ L2).length := by
    intro e he
    rw [List.length_append, List.length_append, hL1, hL2]
    have := hb1 e (by omega)
    have := hb2 (c - 3 - e) (by omega)
    constructor <;> omega
  obtain ⟨L3, τ, hL3, hm3, hb3, hv3⟩ :=
    combE N (fun e => π e) (fun e => σ (c - 3 - e)) (c - 2) (G ++ L1 ++ L2) hpq
  rw [List.length_append, List.length_append, hL1, hL2] at hb3
  refine ⟨L1 ++ L2 ++ L3,
    fun i => if i = 0 then σ (c - 2) else if i = c - 1 then π (c - 2) else τ (i - 1), ?_, ?_, ?_, ?_⟩
  · rw [List.length_append, List.length_append, hL1, hL2, hL3]; omega
  · intro g hg
    rw [List.mem_append, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact hm1 g hg
    · exact hm2 g hg
    · exact hm3 g hg
  · intro i hi
    rw [List.length_append, List.length_append, hL1, hL2, hL3]
    dsimp only
    split_ifs with h1 h2
    · have := hb2 (c - 2) le_rfl; omega
    · have := hb1 (c - 2) le_rfl; omega
    · have := hb3 (i - 1) (by omega); omega
  · intro x hx u hu hp i hi
    have hP : ∀ j, j ≤ c - 2 →
        ((∃ i', i' ≤ j ∧ x.getD (a + i') false = true) ↔ u ≤ j) := by
      intro j hj
      constructor
      · rintro ⟨i', h1, h2⟩
        have := (hp i' (by omega)).1 h2
        omega
      · intro h
        exact ⟨u, h, (hp u hu).2 rfl⟩
    have hS : ∀ j, j ≤ c - 2 →
        ((∃ i', i' ≤ j ∧ x.getD (a + (c - 1 - i')) false = true) ↔ c - 1 - j ≤ u) := by
      intro j hj
      constructor
      · rintro ⟨i', h1, h2⟩
        have := (hp (c - 1 - i') (by omega)).1 h2
        omega
      · intro h
        exact ⟨c - 1 - u, by omega, (hp (c - 1 - (c - 1 - u)) (by omega)).2 (by omega)⟩
    have w1 : ∀ j, j ≤ c - 2 →
        (((G ++ (L1 ++ L2 ++ L3)).foldl stp x).getD (π j) false = true ↔ u ≤ j) := by
      intro j hj
      have e : G ++ (L1 ++ L2 ++ L3) = (G ++ L1) ++ (L2 ++ L3) := by simp
      rw [e, pre (G ++ L1) _ x _ (by rw [hx, List.length_append, hL1]; have := hb1 j hj; omega)]
      exact (hv1 x hx j hj).trans (hP j hj)
    have w2 : ∀ j, j ≤ c - 2 →
        (((G ++ (L1 ++ L2 ++ L3)).foldl stp x).getD (σ j) false = true ↔ c - 1 - j ≤ u) := by
      intro j hj
      have e : G ++ (L1 ++ L2 ++ L3) = ((G ++ L1) ++ L2) ++ L3 := by simp
      rw [e, pre ((G ++ L1) ++ L2) _ x _ (by
        rw [hx, List.length_append, List.length_append, hL1, hL2]; have := hb2 j hj; omega)]
      exact (hv2 x hx j hj).trans (hS j hj)
    dsimp only
    by_cases h1 : i = 0
    · rw [ifp h1, w2 (c - 2) le_rfl]; omega
    · rw [ifn h1]
      by_cases h2 : i = c - 1
      · rw [ifp h2, w1 (c - 2) le_rfl]; omega
      · rw [ifn h2]
        have e : G ++ (L1 ++ L2 ++ L3) = (G ++ L1 ++ L2) ++ L3 := by simp
        have q1 := w1 (i - 1) (by omega)
        have q2 := w2 (c - 3 - (i - 1)) (by omega)
        rw [e] at q1 q2 ⊢
        rw [pre (G ++ L1 ++ L2) L3 x _ (by
          rw [hx]; exact (hpq (i - 1) (by omega)).1)] at q1
        rw [pre (G ++ L1 ++ L2) L3 x _ (by
          rw [hx]; exact (hpq (i - 1) (by omega)).2)] at q2
        rw [hv3 x hx (i - 1) (by omega), Bool.or_eq_true, q1, q2]
        omega

theorem blockO (N a c : ℕ) (hac : a + c ≤ N) (G : List Gate) :
    ∃ (L : List Gate) (ν : ℕ → Option ℕ), L.length ≤ 3 * c - 6 ∧ (∀ g ∈ L, M2 g) ∧
      (∀ i j, ν i = some j → j < N + G.length + L.length) ∧
      ∀ x : List Bool, x.length = N → ∀ u, u < c →
        (∀ i, i < c → (x.getD (a + i) false = true ↔ i = u)) →
        ∀ i, i < c → rd ((G ++ L).foldl stp x) (ν i) = !x.getD (a + i) false := by
  by_cases hc : 2 ≤ c
  · obtain ⟨L, ν, hL, hm, hb, hv⟩ := block N a c hc hac G
    refine ⟨L, fun i => if i < c then some (ν i) else none, by omega, hm, ?_, ?_⟩
    · intro i j hij
      dsimp only at hij
      by_cases h : i < c
      · rw [ifp h] at hij
        have e : ν i = j := by simpa using hij
        rw [← e]; exact hb i h
      · rw [ifn h] at hij; simp at hij
    · intro x hx u hu hp i hi
      dsimp only
      rw [ifp hi]
      show ((G ++ L).foldl stp x).getD (ν i) false = !x.getD (a + i) false
      have q := hv x hx u hu hp i hi
      by_cases hiu : i = u
      · rw [(hp i hi).2 hiu]
        have : ((G ++ L).foldl stp x).getD (ν i) false ≠ true := fun h => (q.1 h) hiu
        simpa using this
      · have h1 : x.getD (a + i) false ≠ true := fun h => hiu ((hp i hi).1 h)
        have h2 : x.getD (a + i) false = false := by simpa using h1
        rw [h2, q.2 hiu]; rfl
  · refine ⟨[], fun _ => none, by simp, by simp, by simp, ?_⟩
    intro x hx u hu hp i hi
    have h0 : i = u := by omega
    rw [(hp i hi).2 h0]; rfl

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem pcnet (n m : ℕ) : ∃ (PC : List Gate) (ν : ℕ → Option ℕ),
    PC.length ≤ (3 * n - 6) + (3 * m - 6) ∧ (∀ g ∈ PC, M2 g) ∧
    (∀ w j, ν w = some j → j < n + m + PC.length) ∧
    ∀ (u : Fin n) (v : Fin m), ∀ w, w < n + m →
      rd (PC.foldl stp (oneEach u v)) (ν w) = !(oneEach u v).getD w false := by
  obtain ⟨L1, ν1, hl1, hm1, hb1, hv1⟩ := blockO (n + m) 0 n (by omega) []
  obtain ⟨L2, ν2, hl2, hm2, hb2, hv2⟩ := blockO (n + m) n m (by omega) L1
  simp only [List.length_nil, Nat.add_zero, List.nil_append] at hb1 hv1
  refine ⟨L1 ++ L2, fun w => if w < n then ν1 w else ν2 (w - n), ?_, ?_, ?_, ?_⟩
  · rw [List.length_append]; omega
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hm1 g hg
    · exact hm2 g hg
  · intro w j hwj
    dsimp only at hwj
    rw [List.length_append]
    by_cases h : w < n
    · rw [ifp h] at hwj
      have := hb1 w j hwj; omega
    · rw [ifn h] at hwj
      have := hb2 (w - n) j hwj; omega
  · intro u v w hw
    have hx : (oneEach u v).length = n + m := by simp [oneEach]
    dsimp only
    by_cases h : w < n
    · rw [ifp h, rd_pre L1 L2 _ _ (by intro j hj; rw [hx]; exact hb1 w j hj)]
      have := hv1 (oneEach u v) hx u.val u.isLt (by
        intro i hi
        rw [oe]
        constructor
        · rintro (h | h) <;> omega
        · intro h; left; omega) w h
      rw [this, Nat.zero_add]
    · rw [ifn h]
      have := hv2 (oneEach u v) hx v.val v.isLt (by
        intro i hi
        rw [oe]
        have := u.isLt
        constructor
        · rintro (h | h) <;> omega
        · intro h; right; omega) (w - n) (by omega)
      rw [this]
      have e : n + (w - n) = w := by omega
      rw [e]

def cl (N : ℕ) (gs : List Gate) : List (List ℕ) :=
  gs.foldl (PEqualNP.EdgeOwnership.coneStep N) []

theorem cl_snoc (N : ℕ) (gs : List Gate) (g : Gate) : cl N (gs ++ [g]) = cl N gs ++
    [(g.inputs.filter (fun w => decide (N ≤ w ∧ w < N + (cl N gs).length))).flatMap
      (fun w => (w - N) :: (cl N gs).getD (w - N) [])] := by
  unfold cl
  rw [List.foldl_append]
  rfl

theorem cl_len (N : ℕ) (gs : List Gate) : (cl N gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => rw [cl_snoc, List.length_append, ih]; simp

theorem mem_cl (N : ℕ) (gs : List Gate) : ∀ i a, i < gs.length →
    (a ∈ (cl N gs).getD i [] ↔ ∃ w, w ∈ (gs.getD i dg).inputs ∧ N ≤ w ∧ w < N + i ∧
      (a = w - N ∨ a ∈ (cl N gs).getD (w - N) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i a hi; simp at hi
  | append_singleton gs g ih =>
    intro i a hi
    rw [List.length_append, List.length_singleton] at hi
    have hpre : ∀ j, j < gs.length → (cl N (gs ++ [g])).getD j [] = (cl N gs).getD j [] := by
      intro j hj
      rw [cl_snoc, getD_left _ _ _ _ (by rw [cl_len]; exact hj)]
    by_cases h : i < gs.length
    · rw [hpre i h, ih i a h, getD_left gs g dg i h]
      constructor
      · rintro ⟨w, hw, h1, h2, h3⟩
        exact ⟨w, hw, h1, h2, by rw [hpre (w - N) (by omega)]; exact h3⟩
      · rintro ⟨w, hw, h1, h2, h3⟩
        exact ⟨w, hw, h1, h2, by rw [hpre (w - N) (by omega)] at h3; exact h3⟩
    · have hi' : i = gs.length := by omega
      subst hi'
      rw [getD_last gs g dg _ rfl, cl_snoc, getD_last _ _ _ _ (cl_len N gs).symm, List.mem_flatMap]
      constructor
      · rintro ⟨w, hwf, h3⟩
        rw [List.mem_filter] at hwf
        obtain ⟨hw, hd⟩ := hwf
        have hd' := of_decide_eq_true hd
        rw [cl_len] at hd'
        rw [List.mem_cons] at h3
        refine ⟨w, hw, hd'.1, hd'.2, ?_⟩
        rw [← cl_snoc, hpre (w - N) (by omega)]
        exact h3
      · rintro ⟨w, hw, h1, h2, h3⟩
        rw [← cl_snoc, hpre (w - N) (by omega)] at h3
        refine ⟨w, List.mem_filter.2 ⟨hw, decide_eq_true ⟨h1, by rw [cl_len]; exact h2⟩⟩, ?_⟩
        rw [List.mem_cons]
        exact h3

theorem cl_out (N : ℕ) (gs : List Gate) (i a : ℕ) (ha : a ∈ (cl N gs).getD i []) :
    i < gs.length := by
  by_contra h
  rw [List.getD_eq_default _ _ (by rw [cl_len]; omega)] at ha
  simp at ha

theorem cone_trans (N : ℕ) (gs : List Gate) : ∀ c a b, a ∈ (cl N gs).getD b [] →
    b ∈ (cl N gs).getD c [] → a ∈ (cl N gs).getD c [] := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro a b hab hbc
    have hc := cl_out N gs c b hbc
    obtain ⟨w, hw, h1, h2, h3⟩ := (mem_cl N gs c b hc).1 hbc
    refine (mem_cl N gs c a hc).2 ⟨w, hw, h1, h2, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hab
    · exact ih (w - N) (by omega) a b hab h3

theorem closure (N : ℕ) (gs : List Gate) (h i w : ℕ) (hi : i < gs.length)
    (hw : w ∈ (gs.getD i dg).inputs) (h1 : N ≤ w) (h2 : w < N + i)
    (hR : i = h ∨ i ∈ (cl N gs).getD h []) : w - N = h ∨ (w - N) ∈ (cl N gs).getD h [] := by
  have hd : (w - N) ∈ (cl N gs).getD i [] := (mem_cl N gs i _ hi).2 ⟨w, hw, h1, h2, Or.inl rfl⟩
  rcases hR with hR | hR
  · subst hR; exact Or.inr hd
  · exact Or.inr (cone_trans N gs h _ i hd hR)

def Inv (N : ℕ) (gs : List Gate) (X : List Bool → Prop) (R : ℕ → Prop) (ν : ℕ → Option ℕ)
    (t s : ℕ) (G : List Gate) (ρ δ : ℕ → Option ℕ) : Prop :=
  (∀ g ∈ G, M2 g) ∧
  (∀ w j, ρ w = some j → j < N + G.length) ∧
  (∀ w j, δ w = some j → j < N + G.length) ∧
  (∀ w j, ν w = some j → j < N + G.length) ∧
  ∀ x, X x →
    (∀ w, w < N + t → rd (G.foldl stp x) (ρ w) = (gs.foldl stp x).getD w false) ∧
    (∀ i, i < s → (R i ∨ (gs.getD i dg).op = GateOp.not) →
      rd (G.foldl stp x) (δ i) = !(gs.foldl stp x).getD (N + i) false) ∧
    (∀ w, w < N → rd (G.foldl stp x) (ν w) = !x.getD w false)

theorem inv_app (N : ℕ) (gs : List Gate) (X : List Bool → Prop) (R : ℕ → Prop)
    (ν : ℕ → Option ℕ) (t s : ℕ) (G : List Gate) (ρ δ : ℕ → Option ℕ)
    (hX : ∀ x, X x → x.length = N) (g' : Gate) (hg : M2 g')
    (hI : Inv N gs X R ν t s G ρ δ) : Inv N gs X R ν t s (G ++ [g']) ρ δ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg'
    rw [List.mem_append] at hg'
    rcases hg' with hg' | hg'
    · exact h1 g hg'
    · simp at hg'; subst hg'; exact hg
  · intro w j hw
    have := h2 w j hw
    rw [List.length_append, List.length_singleton]; omega
  · intro w j hw
    have := h3 w j hw
    rw [List.length_append, List.length_singleton]; omega
  · intro w j hw
    have := h4 w j hw
    rw [List.length_append, List.length_singleton]; omega
  · intro x hx
    obtain ⟨a1, a2, a3⟩ := h5 x hx
    have hl := hX x hx
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rw [rd_pre G [g'] x _ (fun j hj => by rw [hl]; exact h2 w j hj)]
      exact a1 w hw
    · intro i hi hR
      rw [rd_pre G [g'] x _ (fun j hj => by rw [hl]; exact h3 i j hj)]
      exact a2 i hi hR
    · intro w hw
      rw [rd_pre G [g'] x _ (fun j hj => by rw [hl]; exact h4 w j hj)]
      exact a3 w hw

theorem inv_setr (N : ℕ) (gs : List Gate) (X : List Bool → Prop) (R : ℕ → Prop)
    (ν : ℕ → Option ℕ) (t s : ℕ) (G : List Gate) (ρ δ : ℕ → Option ℕ) (o : Option ℕ)
    (hI : Inv N gs X R ν t s G ρ δ)
    (hb : ∀ j, o = some j → j < N + G.length)
    (hv : ∀ x, X x → rd (G.foldl stp x) o = (gs.foldl stp x).getD (N + t) false) :
    Inv N gs X R ν (t + 1) s G (fun w => if w = N + t then o else ρ w) δ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  refine ⟨h1, ?_, h3, h4, ?_⟩
  · intro w j hw
    dsimp only at hw
    by_cases e : w = N + t
    · rw [ifp e] at hw; exact hb j hw
    · rw [ifn e] at hw; exact h2 w j hw
  · intro x hx
    obtain ⟨a1, a2, a3⟩ := h5 x hx
    refine ⟨?_, a2, a3⟩
    intro w hw
    dsimp only
    by_cases e : w = N + t
    · rw [ifp e, e]; exact hv x hx
    · rw [ifn e]; exact a1 w (by omega)

theorem inv_setd (N : ℕ) (gs : List Gate) (X : List Bool → Prop) (R : ℕ → Prop)
    (ν : ℕ → Option ℕ) (t s : ℕ) (G : List Gate) (ρ δ : ℕ → Option ℕ) (o : Option ℕ)
    (hI : Inv N gs X R ν t s G ρ δ)
    (hb : ∀ j, o = some j → j < N + G.length)
    (hv : ∀ x, X x → (R s ∨ (gs.getD s dg).op = GateOp.not) →
      rd (G.foldl stp x) o = !(gs.foldl stp x).getD (N + s) false) :
    Inv N gs X R ν t (s + 1) G ρ (fun i => if i = s then o else δ i) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  refine ⟨h1, h2, ?_, h4, ?_⟩
  · intro w j hw
    dsimp only at hw
    by_cases e : w = s
    · rw [ifp e] at hw; exact hb j hw
    · rw [ifn e] at hw; exact h3 w j hw
  · intro x hx
    obtain ⟨a1, a2, a3⟩ := h5 x hx
    refine ⟨a1, ?_, a3⟩
    intro i hi hR
    dsimp only
    by_cases e : i = s
    · rw [ifp e]
      rw [e] at hR ⊢
      exact hv x hx hR
    · rw [ifn e]; exact a2 i (by omega) hR

theorem gate_r (N : ℕ) (gs : List Gate) (X : List Bool → Prop) (R : ℕ → Prop)
    (ν : ℕ → Option ℕ) (t s : ℕ) (G : List Gate) (ρ δ : ℕ → Option ℕ)
    (hX : ∀ x, X x → x.length = N) (op1 : GateOp) (rs1 : List (Option ℕ))
    (hop1 : op1 = GateOp.and ∨ op1 = GateOp.or) (hl1 : rs1.length ≤ 2)
    (hI : Inv N gs X R ν t s G ρ δ)
    (hv : ∀ x, X x → op1.eval (rs1.map fun o => rd (G.foldl stp x) o) =
      (gs.foldl stp x).getD (N + t) false) :
    Inv N gs X R ν (t + 1) s (G ++ [(⟨op1, rs1.map fun o => o.getD (N + G.length)⟩ : Gate)])
      (fun w => if w = N + t then some (N + G.length) else ρ w) δ := by
  have I0 := inv_app N gs X R ν t s G ρ δ hX
    (⟨op1, rs1.map fun o => o.getD (N + G.length)⟩ : Gate)
    ⟨hop1, by rw [List.length_map]; exact hl1⟩ hI
  refine inv_setr N gs X R ν t s _ ρ δ (some (N + G.length)) I0 ?_ ?_
  · intro j hj
    have : N + G.length = j := by simpa using hj
    rw [List.length_append, List.length_singleton]; omega
  · intro x hx
    have e := emit G x op1 rs1
    rw [hX x hx] at e
    show ((G ++ [(⟨op1, rs1.map fun o => o.getD (N + G.length)⟩ : Gate)]).foldl stp x).getD
      (N + G.length) false = _
    rw [e]
    exact hv x hx

theorem gate_d (N : ℕ) (gs : List Gate) (X : List Bool → Prop) (R : ℕ → Prop)
    (ν : ℕ → Option ℕ) (t s : ℕ) (G : List Gate) (ρ δ : ℕ → Option ℕ)
    (hX : ∀ x, X x → x.length = N) (op1 : GateOp) (rs1 : List (Option ℕ))
    (hop1 : op1 = GateOp.and ∨ op1 = GateOp.or) (hl1 : rs1.length ≤ 2)
    (hI : Inv N gs X R ν t s G ρ δ)
    (hv : ∀ x, X x → op1.eval (rs1.map fun o => rd (G.foldl stp x) o) =
      !(gs.foldl stp x).getD (N + s) false) :
    Inv N gs X R ν t (s + 1) (G ++ [(⟨op1, rs1.map fun o => o.getD (N + G.length)⟩ : Gate)])
      ρ (fun i => if i = s then some (N + G.length) else δ i) := by
  have I0 := inv_app N gs X R ν t s G ρ δ hX
    (⟨op1, rs1.map fun o => o.getD (N + G.length)⟩ : Gate)
    ⟨hop1, by rw [List.length_map]; exact hl1⟩ hI
  refine inv_setd N gs X R ν t s _ ρ δ (some (N + G.length)) I0 ?_ ?_
  · intro j hj
    have : N + G.length = j := by simpa using hj
    rw [List.length_append, List.length_singleton]; omega
  · intro x hx _
    have e := emit G x op1 rs1
    rw [hX x hx] at e
    show ((G ++ [(⟨op1, rs1.map fun o => o.getD (N + G.length)⟩ : Gate)]).foldl stp x).getD
      (N + G.length) false = _
    rw [e]
    exact hv x hx

theorem cardstep (P : ℕ → Prop) [DecidablePred P] (t : ℕ) :
    ((Finset.range (t + 1)).filter P).card =
      ((Finset.range t).filter P).card + if P t then 1 else 0 := by
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_eq_ite, ifn (by simp)]
  · rfl

theorem card_pos (P : ℕ → Prop) [DecidablePred P] (t : ℕ) (h : P t) :
    ((Finset.range (t + 1)).filter P).card = ((Finset.range t).filter P).card + 1 := by
  rw [cardstep, ifp h]

theorem card_neg (P : ℕ → Prop) [DecidablePred P] (t : ℕ) (h : ¬ P t) :
    ((Finset.range (t + 1)).filter P).card = ((Finset.range t).filter P).card := by
  rw [cardstep, ifn h, Nat.add_zero]

theorem core (N : ℕ) (gs : List Gate) (X : List Bool → Prop) (hX : ∀ x, X x → x.length = N)
    (p q : ℕ) (K R : ℕ → Prop) [DecidablePred K] (ν : ℕ → Option ℕ) (PC : List Gate)
    (hF : ∀ i, i < gs.length → ((gs.getD i dg).op = GateOp.and ∨ (gs.getD i dg).op = GateOp.or ∨
      (gs.getD i dg).op = GateOp.not) ∧ (gs.getD i dg).inputs.length ≤ 2)
    (hnot : ∀ t, t < gs.length → (gs.getD t dg).op = GateOp.not → (t = p ∨ t = q) ∧
      ∃ hh, hh < t ∧ (gs.getD t dg).inputs.head? = some (N + hh) ∧
        (R hh ∨ (gs.getD hh dg).op = GateOp.not))
    (hpq : ∀ t, t < gs.length → (t = p ∨ t = q) → (gs.getD t dg).op = GateOp.not)
    (hK : ∀ t, t < gs.length → ¬ (t = p ∨ t = q) → (K t ↔ R t))
    (hKn : ∀ t, K t → ¬ (t = p ∨ t = q))
    (hcl : ∀ t, t < gs.length → R t → ∀ w, w ∈ (gs.getD t dg).inputs → N ≤ w → w < N + t →
      R (w - N))
    (hPCm : ∀ g ∈ PC, M2 g)
    (hPCb : ∀ w j, ν w = some j → j < N + PC.length)
    (hPCv : ∀ x, X x → ∀ w, w < N → rd (PC.foldl stp x) (ν w) = !x.getD w false) :
    ∀ t, t ≤ gs.length → ∃ (G : List Gate) (ρ δ : ℕ → Option ℕ), Inv N gs X R ν t t G ρ δ ∧
      G.length + ((Finset.range t).filter (fun i => i = p ∨ i = q)).card =
        PC.length + t + ((Finset.range t).filter K).card := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨PC, fun w => if w < N then some w else none, fun _ => none,
      ⟨hPCm, ?_, ?_, hPCb, ?_⟩, by simp⟩
    · intro w j hw
      dsimp only at hw
      by_cases e : w < N
      · rw [ifp e] at hw
        have : w = j := by simpa using hw
        omega
      · rw [ifn e] at hw; simp at hw
    · intro w j hw; simp at hw
    · intro x hx
      have hl := hX x hx
      refine ⟨?_, ?_, hPCv x hx⟩
      · intro w hw
        dsimp only
        rw [ifp (by omega : w < N)]
        show (PC.foldl stp x).getD w false = _
        rw [inp PC x w (by omega), inp gs x w (by omega)]
      · intro i hi; omega
  | succ t ih =>
    intro ht
    obtain ⟨G, ρ, δ, hI, hc⟩ := ih (by omega)
    have htl : t < gs.length := by omega
    obtain ⟨hop, hlen⟩ := hF t htl
    obtain ⟨h1, h2, h3, h4, h5⟩ := id hI
    by_cases hn : (gs.getD t dg).op = GateOp.not
    · obtain ⟨hpqt, hh, hlt, hhead, hRh⟩ := hnot t htl hn
      have hv : ∀ x, X x → (gs.foldl stp x).getD (N + t) false =
          !(gs.foldl stp x).getD (N + hh) false := by
        intro x hx
        have hl := hX x hx
        have := wire_at gs x t htl
        rw [hl] at this
        rw [this, hn]
        cases hin : (gs.getD t dg).inputs with
        | nil => rw [hin] at hhead; simp at hhead
        | cons a l =>
          rw [hin] at hhead
          have ha : a = N + hh := by simpa using hhead
          subst ha
          simp [GateOp.eval, hlt]
      have I1 := inv_setr N gs X R ν t t G ρ δ (δ hh) hI (fun j hj => h3 hh j hj) (by
        intro x hx
        rw [hv x hx]
        exact (h5 x hx).2.1 hh hlt hRh)
      have I2 := inv_setd N gs X R ν (t + 1) t G _ δ (ρ (N + hh)) I1 (fun j hj => h2 _ j hj) (by
        intro x hx _
        rw [hv x hx, (h5 x hx).1 (N + hh) (by omega)]
        simp)
      refine ⟨G, _, _, I2, ?_⟩
      have c1 := card_pos (fun i => i = p ∨ i = q) t hpqt
      have c2 := card_neg K t (fun hk => hKn t hk hpqt)
      rw [c1, c2]
      omega
    · have hao : (gs.getD t dg).op = GateOp.and ∨ (gs.getD t dg).op = GateOp.or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hn
      have hnpq : ¬ (t = p ∨ t = q) := fun e => hn (hpq t htl e)
      have c1 := card_neg (fun i => i = p ∨ i = q) t hnpq
      have I1 := gate_r N gs X R ν t t G ρ δ hX (gs.getD t dg).op
        ((gs.getD t dg).inputs.map fun w => if w < N + t then ρ w else none) hao
        (by rw [List.length_map]; exact hlen) hI (by
          intro x hx
          have w := wire_at gs x t htl
          rw [hX x hx] at w
          rw [w, List.map_map]
          congr 1
          apply List.map_congr_left
          intro a _
          show rd (G.foldl stp x) (if a < N + t then ρ a else none) = _
          split_ifs with hlt
          · exact (h5 x hx).1 a hlt
          · rfl)
      obtain ⟨G1, hG1⟩ : ∃ G1 : List Gate, G1 = G ++ [(⟨(gs.getD t dg).op,
          ((gs.getD t dg).inputs.map fun w => if w < N + t then ρ w else none).map
            fun o => o.getD (N + G.length)⟩ : Gate)] := ⟨_, rfl⟩
      rw [← hG1] at I1
      have hG1l : G1.length = G.length + 1 := by
        rw [hG1, List.length_append, List.length_singleton]
      by_cases hRt : R t
      · obtain ⟨k1, k2, k3, k4, k5⟩ := id I1
        have hD : ∀ x, X x → ∀ a, a ∈ (gs.getD t dg).inputs → a < N + t →
            rd (G1.foldl stp x) (if a < N then ν a else δ (a - N)) =
              !(gs.foldl stp x).getD a false := by
          intro x hx a ha hlt
          by_cases haN : a < N
          · rw [ifp haN, (k5 x hx).2.2 a haN, inp gs x a (by rw [hX x hx]; exact haN)]
          · rw [ifn haN, (k5 x hx).2.1 (a - N) (by omega)
              (Or.inl (hcl t htl hRt a ha (by omega) hlt))]
            have e : N + (a - N) = a := by omega
            rw [e]
        have hex : ∃ (op2 : GateOp) (rs2 : List (Option ℕ)),
            (op2 = GateOp.and ∨ op2 = GateOp.or) ∧ rs2.length ≤ 2 ∧
            ∀ x, X x → op2.eval (rs2.map fun o => rd (G1.foldl stp x) o) =
              !(gs.foldl stp x).getD (N + t) false := by
          rcases hao with ha | ho
          · by_cases hall : ∀ a, a ∈ (gs.getD t dg).inputs → a < N + t
            · refine ⟨GateOp.or,
                (gs.getD t dg).inputs.map (fun a => if a < N then ν a else δ (a - N)),
                Or.inr rfl, by rw [List.length_map]; exact hlen, ?_⟩
              intro x hx
              have w := wire_at gs x t htl
              rw [hX x hx] at w
              rw [w, ha, and_ev, List.map_map, or_ev]
              apply dm_and
              intro a hain
              show rd (G1.foldl stp x) (if a < N then ν a else δ (a - N)) = _
              rw [hD x hx a hain (hall a hain), ifp (hall a hain)]
            · refine ⟨GateOp.and, [], Or.inl rfl, by simp, ?_⟩
              intro x hx
              have w := wire_at gs x t htl
              rw [hX x hx] at w
              rw [w, ha, and_ev]
              have hf : ((gs.getD t dg).inputs.all fun w =>
                  if w < N + t then (gs.foldl stp x).getD w false else false) = false := by
                rw [Bool.eq_false_iff]
                intro hall2
                rw [List.all_eq_true] at hall2
                apply hall
                intro a hain
                by_contra hlt
                have := hall2 a hain
                rw [ifn hlt] at this
                exact absurd this (by simp)
              rw [hf]
              rfl
          · refine ⟨GateOp.and,
              ((gs.getD t dg).inputs.filter (fun a => decide (a < N + t))).map
                (fun a => if a < N then ν a else δ (a - N)), Or.inl rfl, ?_, ?_⟩
            · rw [List.length_map]
              exact le_trans (List.length_filter_le _ _) hlen
            · intro x hx
              have w := wire_at gs x t htl
              rw [hX x hx] at w
              rw [w, ho, or_ev, List.map_map, and_ev]
              apply dm_or
              · intro a hain hva
                have hlt : a < N + t := of_decide_eq_true hva
                show rd (G1.foldl stp x) (if a < N then ν a else δ (a - N)) = _
                rw [hD x hx a hain hlt, ifp hlt]
              · intro a hain hva
                have hlt : ¬ a < N + t := of_decide_eq_false hva
                rw [ifn hlt]
        obtain ⟨op2, rs2, hop2, hl2, hv2⟩ := hex
        have I2 := gate_d N gs X R ν (t + 1) t G1 _ δ hX op2 rs2 hop2 hl2 I1 hv2
        refine ⟨_, _, _, I2, ?_⟩
        have c2 := card_pos K t ((hK t htl hnpq).2 hRt)
        rw [c1, c2, List.length_append, List.length_singleton, hG1l]
        omega
      · have I2 := inv_setd N gs X R ν (t + 1) t G1 _ δ none I1 (by intro j hj; simp at hj) (by
          intro x hx hc'
          rcases hc' with hc' | hc'
          · exact absurd hc' hRt
          · exact absurd hc' hn)
        refine ⟨_, _, _, I2, ?_⟩
        have c2 := card_neg K t (fun hk => hRt ((hK t htl hnpq).1 hk))
        rw [c1, c2, hG1l]
        omega

def XP (n m : ℕ) (x : List Bool) : Prop := ∃ (u : Fin n) (v : Fin m), x = oneEach u v

def RP (N : ℕ) (C : Circuit) (h h' i : ℕ) : Prop :=
  (i = h ∨ PEqualNP.EdgeOwnership.InCone N C i h) ∨ (i = h' ∨ PEqualNP.EdgeOwnership.InCone N C i h')

theorem fin (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (p q h h' : ℕ)
    (hF : FanInTwo C) (hs : C.size ≤ s) (hR : Represents A C)
    (hp : p < C.gates.length) (hq : q < C.gates.length) (hpq : p ≠ q)
    (hpn : (NestedCover.gateAt C p).op = GateOp.not)
    (hqn : (NestedCover.gateAt C q).op = GateOp.not)
    (hph : (NestedCover.gateAt C p).inputs.head? = some (n + m + h))
    (hqh : (NestedCover.gateAt C q).inputs.head? = some (n + m + h'))
    (hhp : h < p) (hhq : h' < q)
    (hall : ∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.not → j = p ∨ j = q) :
    RepSizeAtMost A (s - 2 + ((Finset.range C.gates.length).filter (fun i => i ≠ p ∧ i ≠ q ∧
      ((i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∨
        (i = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h')))).card +
      ((3 * n - 6) + (3 * m - 6))) := by
  obtain ⟨PC, ν, hPCl, hPCm, hPCb, hPCv⟩ := pcnet n m
  have hlen2 : ((Finset.range C.gates.length).filter (fun i => i = p ∨ i = q)).card = 2 := by
    have e : (Finset.range C.gates.length).filter (fun i => i = p ∨ i = q) = {p, q} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun hh => hh.2
      · rintro (rfl | rfl)
        · exact ⟨hp, Or.inl rfl⟩
        · exact ⟨hq, Or.inr rfl⟩
    rw [e, Finset.card_pair hpq]
  have hgm : ∀ i, i < C.gates.length → C.gates.getD i dg ∈ C.gates := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have a1 : ∀ i, i < C.gates.length → ((C.gates.getD i dg).op = GateOp.and ∨
      (C.gates.getD i dg).op = GateOp.or ∨ (C.gates.getD i dg).op = GateOp.not) ∧
      (C.gates.getD i dg).inputs.length ≤ 2 := by
    intro i hi
    obtain ⟨ho, hl⟩ := hF _ (hgm i hi)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    exact ⟨ho, hl⟩
  have a2 : ∀ t, t < C.gates.length → (C.gates.getD t dg).op = GateOp.not → (t = p ∨ t = q) ∧
      ∃ hh, hh < t ∧ (C.gates.getD t dg).inputs.head? = some (n + m + hh) ∧
        (RP (n + m) C h h' hh ∨ (C.gates.getD hh dg).op = GateOp.not) := by
    intro t ht hn
    have hpq' := hall t ht hn
    refine ⟨hpq', ?_⟩
    rcases hpq' with e | e
    · rw [e]; exact ⟨h, hhp, hph, Or.inl (Or.inl (Or.inl rfl))⟩
    · rw [e]; exact ⟨h', hhq, hqh, Or.inl (Or.inr (Or.inl rfl))⟩
  have a3 : ∀ t, t < C.gates.length → (t = p ∨ t = q) → (C.gates.getD t dg).op = GateOp.not := by
    intro t _ e
    rcases e with e | e
    · rw [e]; exact hpn
    · rw [e]; exact hqn
  have a4 : ∀ t, t < C.gates.length → ¬ (t = p ∨ t = q) →
      ((t ≠ p ∧ t ≠ q ∧ ((t = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C t h) ∨
        (t = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C t h'))) ↔ RP (n + m) C h h' t) := by
    intro t _ hne
    constructor
    · exact fun hk => hk.2.2
    · exact fun hr => ⟨fun e => hne (Or.inl e), fun e => hne (Or.inr e), hr⟩
  have a5 : ∀ t, (t ≠ p ∧ t ≠ q ∧ ((t = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C t h) ∨
      (t = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C t h'))) → ¬ (t = p ∨ t = q) := by
    intro t hk e
    rcases e with e | e
    · exact hk.1 e
    · exact hk.2.1 e
  have a6 : ∀ t, t < C.gates.length → RP (n + m) C h h' t → ∀ w, w ∈ (C.gates.getD t dg).inputs →
      n + m ≤ w → w < n + m + t → RP (n + m) C h h' (w - (n + m)) := by
    intro t ht hr w hw h1 h2
    rcases hr with hr | hr
    · exact Or.inl (closure (n + m) C.gates h t w ht hw h1 h2 hr)
    · exact Or.inr (closure (n + m) C.gates h' t w ht hw h1 h2 hr)
  have a7 : ∀ x, XP n m x → ∀ w, w < n + m → rd (PC.foldl stp x) (ν w) = !x.getD w false := by
    rintro x ⟨u, v, rfl⟩ w hw
    exact hPCv u v w hw
  have a0 : ∀ x, XP n m x → x.length = n + m := by
    rintro x ⟨u, v, rfl⟩
    simp [oneEach]
  obtain ⟨G, ρ, δ, hI, hc⟩ := core (n + m) C.gates (XP n m) a0 p q
    (fun i => i ≠ p ∧ i ≠ q ∧ ((i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∨
      (i = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h')))
    (RP (n + m) C h h') ν PC a1 a2 a3 a4 a5 a6 hPCm hPCb a7 C.gates.length le_rfl
  rw [hlen2] at hc
  obtain ⟨g1, g2, g3, g4, g5⟩ := hI
  refine ⟨⟨G, (if C.output < n + m + C.gates.length then ρ C.output else none).getD
    (n + m + G.length)⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨ho, hl⟩ := g1 g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ho
  · show G.length ≤ _
    have : C.gates.length ≤ s := hs
    omega
  · intro u v
    have hx : (oneEach u v).length = n + m := by simp [oneEach]
    obtain ⟨b1, b2, b3⟩ := g5 (oneEach u v) ⟨u, v, rfl⟩
    have hWl := len G (oneEach u v)
    rw [hx] at hWl
    show (G.foldl stp (oneEach u v)).getD ((if C.output < n + m + C.gates.length then ρ C.output
      else none).getD (n + m + G.length)) false = A u v
    rw [← hWl, rd_getD, ← hR u v]
    show _ = (C.gates.foldl stp (oneEach u v)).getD C.output false
    split_ifs with hv
    · exact b1 C.output hv
    · rw [beyond C.gates _ _ (by rw [hx]; omega)]; rfl

end PEqualNP.Outside.L_meta_19197

theorem PEqualNP.Outside.L_meta_19197 : (∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (p q h h' : ℕ), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → p < C.gates.length → q < C.gates.length → p ≠ q → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C q).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).inputs.head? = some (n + m + h) → (PEqualNP.MetaComplexity.NestedCover.gateAt C q).inputs.head? = some (n + m + h') → h < p → h' < q → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.not → j = p ∨ j = q) → PEqualNP.Represents.RepSizeAtMost A (s - 2 + ((Finset.range C.gates.length).filter (fun i => i ≠ p ∧ i ≠ q ∧ ((i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∨ (i = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h')))).card + ((3 * n - 6) + (3 * m - 6)))) := by
  intro n m s A C p q h h' hF hs hR hp hq hpq hpn hqn hph hqh hhp hhq hall
  exact PEqualNP.Outside.L_meta_19197.fin n m s A C p q h h' hF hs hR hp hq hpq hpn hqn hph hqh hhp hhq hall

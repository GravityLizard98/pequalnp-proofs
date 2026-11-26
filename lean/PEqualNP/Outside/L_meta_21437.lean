import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21437

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

def leafF (i : ℕ) : ℕ → List Gate × ℕ := fun _ => ([], i)

def nodeF (op : GateOp) (f g : ℕ → List Gate × ℕ) : ℕ → List Gate × ℕ := fun base =>
  ((f base).1 ++ (g (base + (f base).1.length)).1 ++
      [⟨op, [(f base).2, (g (base + (f base).1.length)).2]⟩],
    base + (f base).1.length + (g (base + (f base).1.length)).1.length)

def cnt (G : List Gate) (w : ℕ) : ℕ := (G.map (fun g => g.inputs.count w)).sum

def Spec (m : ℕ) (f : ℕ → List Gate × ℕ) (L : List ℕ) (ev : List Bool → Bool) (sz : ℕ) : Prop :=
  L.length = sz + 1 ∧ (∀ i ∈ L, i < m) ∧
  (∀ W W' : List Bool, (∀ i < m, W.getD i false = W'.getD i false) → ev W = ev W') ∧
  ∀ base, m ≤ base →
    (f base).1.length = sz ∧
    (∀ g ∈ (f base).1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    (∀ k < sz, ∀ i ∈ ((f base).1.getD k dg).inputs, i < base + k) ∧
    (f base).2 < base + sz ∧ (1 ≤ sz → (f base).2 + 1 = base + sz) ∧
    (∀ w, cnt (f base).1 w + (if (f base).2 = w then 1 else 0) =
      if (w ∈ L ∨ (base ≤ w ∧ w < base + sz)) then 1 else 0) ∧
    (∀ W : List Bool, W.length = base → ((f base).1.foldl stp W).getD (f base).2 false = ev W)

theorem gA {α : Type} (l1 l2 : List α) (k : ℕ) (d : α) (h : k < l1.length) :
    (l1 ++ l2).getD k d = l1.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gB {α : Type} (l1 l2 : List α) (k : ℕ) (d : α) (h : l1.length ≤ k) :
    (l1 ++ l2).getD k d = l2.getD (k - l1.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem spec_leaf (m i : ℕ) (hi : i < m) : Spec m (leafF i) [i] (fun W => W.getD i false) 0 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro k hk
    rw [List.mem_singleton] at hk
    omega
  · intro W W' h
    exact h i hi
  · intro base hb
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp [leafF] at hg
    · intro k hk
      omega
    · show i < base + 0
      omega
    · intro h
      omega
    · intro w
      show cnt [] w + (if i = w then 1 else 0) = _
      by_cases h : i = w
      · subst h
        simp [cnt]
      · have h' : ¬ w = i := fun e => h e.symm
        simp [cnt, h, h']
    · intro W _
      rfl

theorem spec_node (m : ℕ) (op : GateOp) (f g : ℕ → List Gate × ℕ) (L1 L2 : List ℕ)
    (e1 e2 : List Bool → Bool) (s1 s2 : ℕ) (hop : op = GateOp.and ∨ op = GateOp.or)
    (h1 : Spec m f L1 e1 s1) (h2 : Spec m g L2 e2 s2) (hd : ∀ i, i ∈ L1 → i ∈ L2 → False) :
    Spec m (nodeF op f g) (L1 ++ L2) (fun W => op.eval [e1 W, e2 W]) (s1 + s2 + 1) := by
  obtain ⟨l1, m1, d1, S1⟩ := h1
  obtain ⟨l2, m2, d2, S2⟩ := h2
  refine ⟨by rw [List.length_append]; omega, ?_, ?_, ?_⟩
  · intro i hi
    rw [List.mem_append] at hi
    rcases hi with h | h
    · exact m1 i h
    · exact m2 i h
  · intro W W' h
    show op.eval [e1 W, e2 W] = op.eval [e1 W', e2 W']
    rw [d1 W W' h, d2 W W' h]
  · intro base hb
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := S1 base hb
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := S2 (base + s1) (by omega)
    have eN : nodeF op f g base = ((f base).1 ++ (g (base + s1)).1 ++
        [(Gate.mk op [(f base).2, (g (base + s1)).2])], base + s1 + s2) := by
      unfold nodeF
      rw [a1, b1]
    rw [eN]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show ((f base).1 ++ (g (base + s1)).1 ++ [_]).length = _
      rw [List.length_append, List.length_append, a1, b1]
      rfl
    · intro q hq
      change q ∈ (f base).1 ++ (g (base + s1)).1 ++ [_] at hq
      rw [List.mem_append, List.mem_append, List.mem_singleton] at hq
      rcases hq with (hq | hq) | hq
      · exact a2 q hq
      · exact b2 q hq
      · rw [hq]
        exact ⟨hop, rfl⟩
    · intro k hk i hi
      change i ∈ (((f base).1 ++ (g (base + s1)).1 ++ [_]).getD k dg).inputs at hi
      by_cases hk1 : k < s1
      · rw [List.append_assoc, gA _ _ k dg (by omega)] at hi
        exact a3 k hk1 i hi
      · by_cases hk2 : k < s1 + s2
        · rw [gA _ _ k dg (by rw [List.length_append]; omega), gB _ _ k dg (by omega), a1] at hi
          have := b3 (k - s1) (by omega) i hi
          omega
        · have hk3 : k = ((f base).1 ++ (g (base + s1)).1).length := by
            rw [List.length_append]; omega
          rw [getD_last _ _ _ _ hk3] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
    · show base + s1 + s2 < base + (s1 + s2 + 1)
      omega
    · intro _
      show base + s1 + s2 + 1 = base + (s1 + s2 + 1)
      omega
    · intro w
      show cnt ((f base).1 ++ (g (base + s1)).1 ++ [(Gate.mk op [(f base).2, (g (base + s1)).2])]) w +
        (if base + s1 + s2 = w then 1 else 0) = _
      have ec : cnt ((f base).1 ++ (g (base + s1)).1 ++ [(Gate.mk op [(f base).2, (g (base + s1)).2])]) w =
          cnt (f base).1 w + cnt (g (base + s1)).1 w +
            ((if (f base).2 = w then 1 else 0) + (if (g (base + s1)).2 = w then 1 else 0)) := by
        unfold cnt
        rw [List.map_append, List.map_append, List.sum_append, List.sum_append]
        simp [List.count_cons]
        omega
      rw [ec]
      have e6 := a6 w
      have f6 := b6 w
      have q1 : w ∈ L1 → w < m := m1 w
      have q2 : w ∈ L2 → w < m := m2 w
      by_cases c1 : w ∈ L1 <;> by_cases c2 : w ∈ L2
      · exact (hd w c1 c2).elim
      · have := q1 c1
        simp only [c1, c2, List.mem_append, true_or, false_or, ite_true] at e6 f6 ⊢
        split_ifs at e6 f6 ⊢ <;> omega
      · have := q2 c2
        simp only [c1, c2, List.mem_append, true_or, false_or, or_true, ite_true] at e6 f6 ⊢
        split_ifs at e6 f6 ⊢ <;> omega
      · simp only [c1, c2, List.mem_append, false_or, or_self] at e6 f6 ⊢
        split_ifs at e6 f6 ⊢ <;> omega
    · intro W hW
      show (((f base).1 ++ (g (base + s1)).1 ++ [(Gate.mk op [(f base).2, (g (base + s1)).2])]).foldl stp W).getD
        (base + s1 + s2) false = op.eval [e1 W, e2 W]
      have hW1 : ((f base).1.foldl stp W).length = base + s1 := by rw [len, hW, a1]
      have hW2 : ((g (base + s1)).1.foldl stp ((f base).1.foldl stp W)).length = base + s1 + s2 := by
        rw [len, hW1, b1]
      rw [snoc_fold, List.foldl_append, getD_last _ _ _ _ hW2.symm]
      show op.eval [((g (base + s1)).1.foldl stp ((f base).1.foldl stp W)).getD (f base).2 false,
        ((g (base + s1)).1.foldl stp ((f base).1.foldl stp W)).getD (g (base + s1)).2 false] =
        op.eval [e1 W, e2 W]
      have v2 := b7 _ hW1
      have v1 := a7 W hW
      rw [v2, inp _ _ _ (by rw [hW1]; exact a4), v1]
      rw [d2 ((f base).1.foldl stp W) W (fun i hi => inp _ W i (by omega))]

def rd (gs : List Gate) (G : Finset ℕ) (w : ℕ) : ℕ := ∑ j ∈ G, (gs.getD j dg).inputs.count w

def rf (m : ℕ) (gs : List Gate) (Rg : Finset ℕ) (a c : ℕ) : Prop :=
  m ≤ c ∧ c - m ∈ Rg ∧ a ∈ (gs.getD (c - m) dg).inputs

def fd (m : ℕ) (gs : List Gate) (a c : ℕ) : Prop :=
  ∃ j, j < gs.length ∧ c = m + j ∧ a ∈ (gs.getD j dg).inputs

def Hyp (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) : Prop :=
  (∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < m + j) ∧
  tj ∈ Rg ∧ (∀ j ∈ Rg, j < gs.length) ∧ (∀ i ∈ S, i < m) ∧
  (∀ j ∈ Rg, (((gs.getD j dg).op = GateOp.and ∨ (gs.getD j dg).op = GateOp.or) ∧
      (gs.getD j dg).inputs.length = 2) ∧
    ∀ w ∈ (gs.getD j dg).inputs, w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg) ∨ w = bw) ∧
  bw ∉ S ∧ ¬ (m ≤ bw ∧ bw - m ∈ Rg) ∧
  rd gs Rg bw ≤ 1 ∧
  (∀ i ∈ S, rd gs (Finset.range gs.length) i = 1 ∧ rd gs Rg i = 1) ∧
  (∀ j ∈ Rg, rd gs Rg (m + j) = if j = tj then 0 else 1) ∧
  (∀ j ∈ Rg, j ≠ tj → rd gs (Finset.range gs.length) (m + j) = 1) ∧
  (∀ j ∈ Rg, Relation.TransGen (rf m gs Rg) bw (m + j) → (gs.getD j dg).op = GateOp.or)

theorem uniqR (gs : List Gate) (G : Finset ℕ) (w j1 j2 : ℕ) (h : rd gs G w ≤ 1) (h1 : j1 ∈ G)
    (h2 : j2 ∈ G) (m1 : w ∈ (gs.getD j1 dg).inputs) (m2 : w ∈ (gs.getD j2 dg).inputs) : j1 = j2 := by
  by_contra hne
  have hsub : ({j1, j2} : Finset ℕ) ⊆ G := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset (f := fun j => ((gs.getD j dg).inputs.count w)) hsub
  rw [Finset.sum_pair hne] at hle
  have p1 : 0 < (gs.getD j1 dg).inputs.count w := List.count_pos_iff.2 m1
  have p2 : 0 < (gs.getD j2 dg).inputs.count w := List.count_pos_iff.2 m2
  have h' : ∑ j ∈ G, (gs.getD j dg).inputs.count w ≤ 1 := h
  omega

theorem exreader (gs : List Gate) (G : Finset ℕ) (w : ℕ) (h : 1 ≤ rd gs G w) :
    ∃ j ∈ G, w ∈ (gs.getD j dg).inputs := by
  by_contra hno
  have : rd gs G w = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact List.count_eq_zero.2 (fun hm => hno ⟨j, hj, hm⟩)
  omega

theorem rd_le (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw)
    (w c : ℕ) (h : rf m gs Rg w c) : rd gs Rg w ≤ 1 := by
  obtain ⟨_, _, _, _, h5, _, _, h8, h9, h10, _, _⟩ := H
  obtain ⟨_, hc, hw⟩ := h
  rcases (h5 _ hc).2 w hw with hs | ⟨hm, hr⟩ | hb
  · rw [(h9 w hs).2]
  · have := h10 _ hr
    have e : m + (w - m) = w := by omega
    rw [e] at this
    rw [this]
    split_ifs <;> omega
  · rw [hb]
    exact h8

theorem rfU (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw) :
    Relator.RightUnique (rf m gs Rg) := by
  intro a c c' h h'
  have hle := rd_le m gs S Rg tj bw H a c h
  have := uniqR gs Rg a (c - m) (c' - m) hle h.2.1 h'.2.1 h.2.2 h'.2.2
  have := h.1
  have := h'.1
  omega

theorem rf_lt (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw)
    (a c : ℕ) (h : rf m gs Rg a c) : a < c := by
  have := H.1 (c - m) (H.2.2.1 _ h.2.1) a h.2.2
  have := h.1
  omega

theorem rt_le (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw)
    (a c : ℕ) (h : Relation.ReflTransGen (rf m gs Rg) a c) : a ≤ c := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hf ih =>
    have := rf_lt m gs S Rg tj bw H _ _ hf
    omega

theorem tg_lt (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw)
    (a c : ℕ) (h : Relation.TransGen (rf m gs Rg) a c) : a < c := by
  induction h with
  | single hf => exact rf_lt m gs S Rg tj bw H _ _ hf
  | tail _ hf ih =>
    have := rf_lt m gs S Rg tj bw H _ _ hf
    omega

theorem two_in (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw)
    (j : ℕ) (hj : j ∈ Rg) :
    ∃ a b, (gs.getD j dg).inputs = [a, b] ∧ a < m + j ∧ b < m + j ∧ a ≠ b := by
  have hl := (H.2.2.2.2.1 j hj).1.2
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hl
  have hjl := H.2.2.1 j hj
  refine ⟨a, b, hab, H.1 j hjl a (by rw [hab]; simp), H.1 j hjl b (by rw [hab]; simp), ?_⟩
  intro e
  subst e
  have hrf : rf m gs Rg a (m + j) := ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hj,
    by rw [Nat.add_sub_cancel_left, hab]; simp⟩
  have hle := rd_le m gs S Rg tj bw H a (m + j) hrf
  have h1 := Finset.single_le_sum (f := fun j => ((gs.getD j dg).inputs.count a))
    (fun i _ => Nat.zero_le _) hj
  simp only [hab] at h1
  have : [a, a].count a = 2 := by simp
  have hle' : ∑ j ∈ Rg, (gs.getD j dg).inputs.count a ≤ 1 := hle
  omega

theorem disjR (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw)
    (j a b : ℕ) (hj : j ∈ Rg) (hab : (gs.getD j dg).inputs = [a, b]) (ha : a < m + j) (hb : b < m + j)
    (hne : a ≠ b) (k : ℕ) (h1 : Relation.ReflTransGen (rf m gs Rg) k a)
    (h2 : Relation.ReflTransGen (rf m gs Rg) k b) : False := by
  have hU := rfU m gs S Rg tj bw H
  have key : ∀ c d, c ∈ (gs.getD j dg).inputs → d < m + j → c ≠ d →
      Relation.ReflTransGen (rf m gs Rg) c d → False := by
    intro c d hc hd hcd hbl
    rcases Relation.ReflTransGen.cases_head hbl with e | ⟨q, hq, hqd⟩
    · exact hcd e
    · have hrf : rf m gs Rg c (m + j) := ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hj,
        by rw [Nat.add_sub_cancel_left]; exact hc⟩
      have := hU hq hrf
      subst this
      have := rt_le m gs S Rg tj bw H _ _ hqd
      omega
  rcases Relation.ReflTransGen.total_of_right_unique hU h1 h2 with h | h
  · exact key a b (by rw [hab]; simp) hb hne h
  · exact key b a (by rw [hab]; simp) ha (Ne.symm hne) h

theorem valgate (m : ℕ) (gs : List Gate) (j a b : ℕ) (hj : j < gs.length)
    (hab : (gs.getD j dg).inputs = [a, b]) (ha : a < m + j) (hb : b < m + j)
    (x : List Bool) (hx : x.length = m) :
    (gs.foldl stp x).getD (m + j) false =
      (gs.getD j dg).op.eval [(gs.foldl stp x).getD a false, (gs.foldl stp x).getD b false] := by
  have e := wire_at gs x j hj
  rw [hx] at e
  rw [e, hab, List.map_cons, List.map_cons, List.map_nil, ifp ha, ifp hb]

def QS (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (bw w : ℕ) : Prop :=
  ∃ (f : ℕ → List Gate × ℕ) (L : List ℕ) (ev : List Bool → Bool) (sz : ℕ) (c : Bool),
    Spec m f L ev sz ∧ L.Nodup ∧
    (∀ i, i ∈ L ↔ (i ∈ S ∧ Relation.ReflTransGen (rf m gs Rg) i w)) ∧
    (c = true → Relation.TransGen (rf m gs Rg) bw w) ∧
    ∀ x : List Bool, x.length = m →
      (gs.foldl stp x).getD w false = ((c && (gs.foldl stp x).getD bw false) || ev x)

theorem bool1 (ca cb bv p q : Bool) :
    (((ca && bv) || p) || ((cb && bv) || q)) = (((ca || cb) && bv) || (p || q)) := by
  cases ca <;> cases cb <;> cases bv <;> cases p <;> cases q <;> rfl

theorem bool2 (cb bv q : Bool) : (bv || ((cb && bv) || q)) = ((true && bv) || q) := by
  cases cb <;> cases bv <;> cases q <;> rfl

theorem bool3 (ca bv p : Bool) : (((ca && bv) || p) || bv) = ((true && bv) || p) := by
  cases ca <;> cases bv <;> cases p <;> rfl

theorem evor (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by
  simp [GateOp.eval]

theorem evand (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by
  simp [GateOp.eval]

theorem extract (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw) :
    ∀ w, (w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg)) → QS m gs S Rg bw w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    have hSm := H.2.2.2.1
    have hbS := H.2.2.2.2.2.1
    have hbR := H.2.2.2.2.2.2.1
    have nobw : ∀ i, i ∈ S → Relation.ReflTransGen (rf m gs Rg) i bw → False := by
      intro i hi hr
      rcases Relation.ReflTransGen.cases_tail hr with e | ⟨c, _, hc⟩
      · exact hbS (e ▸ hi)
      · exact hbR ⟨hc.1, hc.2.1⟩
    by_cases hwS : w ∈ S
    · have hwm := hSm w hwS
      refine ⟨leafF w, [w], fun W => W.getD w false, 0, false, spec_leaf m w hwm,
        List.nodup_singleton w, ?_, fun h => Bool.noConfusion h, ?_⟩
      · intro i
        rw [List.mem_singleton]
        constructor
        · intro e
          subst e
          exact ⟨hwS, Relation.ReflTransGen.refl⟩
        · rintro ⟨_, hr⟩
          rcases Relation.ReflTransGen.cases_tail hr with e | ⟨c, _, hc⟩
          · exact e.symm
          · have := hc.1
            omega
      · intro x hx
        rw [inp gs x w (by omega)]
        rfl
    · have hw' : m ≤ w ∧ w - m ∈ Rg := hw.resolve_left hwS
      obtain ⟨j, rfl⟩ : ∃ j, w = m + j := ⟨w - m, by omega⟩
      have hj : j ∈ Rg := by
        have := hw'.2
        rw [Nat.add_sub_cancel_left] at this
        exact this
      have hjl := H.2.2.1 j hj
      obtain ⟨a, b, hab, ha, hb, hne⟩ := two_in m gs S Rg tj bw H j hj
      have hop := (H.2.2.2.2.1 j hj).1.1
      have hin := (H.2.2.2.2.1 j hj).2
      have h12 := H.2.2.2.2.2.2.2.2.2.2.2 j hj
      have rfa : rf m gs Rg a (m + j) := ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hj,
        by rw [Nat.add_sub_cancel_left, hab]; simp⟩
      have rfb : rf m gs Rg b (m + j) := ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hj,
        by rw [Nat.add_sub_cancel_left, hab]; simp⟩
      have hval := fun (x : List Bool) (hx : x.length = m) => valgate m gs j a b hjl hab ha hb x hx
      have tail_cases : ∀ i, i ∈ S → Relation.ReflTransGen (rf m gs Rg) i (m + j) →
          Relation.ReflTransGen (rf m gs Rg) i a ∨ Relation.ReflTransGen (rf m gs Rg) i b := by
        intro i hi hr
        rcases Relation.ReflTransGen.cases_tail hr with e | ⟨c, hc1, hc2⟩
        · have := hSm i hi
          omega
        · have hc3 := hc2.2.2
          rw [Nat.add_sub_cancel_left, hab] at hc3
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc3
          rcases hc3 with e | e
          · exact Or.inl (e ▸ hc1)
          · exact Or.inr (e ▸ hc1)
      have ina := hin a (by rw [hab]; simp)
      have inb := hin b (by rw [hab]; simp)
      by_cases hab1 : a = bw
      · have hbb : b ≠ bw := fun e => hne (hab1.trans e.symm)
        have qb : b ∈ S ∨ (m ≤ b ∧ b - m ∈ Rg) := by
          rcases inb with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (hbb h).elim
        obtain ⟨f2, L2, e2, s2, c2, sp2, nd2, mem2, tg2, v2⟩ := ih b hb qb
        have hor := h12 (Relation.TransGen.single (hab1 ▸ rfa))
        refine ⟨f2, L2, e2, s2, true, sp2, nd2, ?_, fun _ => Relation.TransGen.single (hab1 ▸ rfa), ?_⟩
        · intro i
          rw [mem2]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, Relation.ReflTransGen.tail h2 rfb⟩
          · rintro ⟨h1, h2⟩
            rcases tail_cases i h1 h2 with h | h
            · exact (nobw i h1 (hab1 ▸ h)).elim
            · exact ⟨h1, h⟩
        · intro x hx
          rw [hval x hx, hor, evor, v2 x hx, hab1]
          exact bool2 _ _ _
      · by_cases hab2 : b = bw
        · have qa : a ∈ S ∨ (m ≤ a ∧ a - m ∈ Rg) := by
            rcases ina with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact (hab1 h).elim
          obtain ⟨f1, L1, e1, s1, c1, sp1, nd1, mem1, tg1, v1⟩ := ih a ha qa
          have hor := h12 (Relation.TransGen.single (hab2 ▸ rfb))
          refine ⟨f1, L1, e1, s1, true, sp1, nd1, ?_, fun _ => Relation.TransGen.single (hab2 ▸ rfb), ?_⟩
          · intro i
            rw [mem1]
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨h1, Relation.ReflTransGen.tail h2 rfa⟩
            · rintro ⟨h1, h2⟩
              rcases tail_cases i h1 h2 with h | h
              · exact ⟨h1, h⟩
              · exact (nobw i h1 (hab2 ▸ h)).elim
          · intro x hx
            rw [hval x hx, hor, evor, v1 x hx, hab2]
            exact bool3 _ _ _
        · have qa : a ∈ S ∨ (m ≤ a ∧ a - m ∈ Rg) := by
            rcases ina with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact (hab1 h).elim
          have qb : b ∈ S ∨ (m ≤ b ∧ b - m ∈ Rg) := by
            rcases inb with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact (hab2 h).elim
          obtain ⟨f1, L1, e1, s1, c1, sp1, nd1, mem1, tg1, v1⟩ := ih a ha qa
          obtain ⟨f2, L2, e2, s2, c2, sp2, nd2, mem2, tg2, v2⟩ := ih b hb qb
          have hdis : ∀ i, i ∈ L1 → i ∈ L2 → False := by
            intro i h1 h2
            exact disjR m gs S Rg tj bw H j a b hj hab ha hb hne i ((mem1 i).1 h1).2 ((mem2 i).1 h2).2
          have tgc : (c1 || c2) = true → Relation.TransGen (rf m gs Rg) bw (m + j) := by
            intro h
            rw [Bool.or_eq_true] at h
            rcases h with h | h
            · exact Relation.TransGen.tail (tg1 h) rfa
            · exact Relation.TransGen.tail (tg2 h) rfb
          refine ⟨nodeF (gs.getD j dg).op f1 f2, L1 ++ L2,
            fun W => (gs.getD j dg).op.eval [e1 W, e2 W], s1 + s2 + 1, c1 || c2,
            spec_node m _ f1 f2 L1 L2 e1 e2 s1 s2 hop sp1 sp2 hdis, ?_, ?_, tgc, ?_⟩
          · rw [List.nodup_append]
            exact ⟨nd1, nd2, fun x h1 y h2 e => hdis x h1 (e ▸ h2)⟩
          · intro i
            rw [List.mem_append, mem1, mem2]
            constructor
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact ⟨h1, Relation.ReflTransGen.tail h2 rfa⟩
              · exact ⟨h1, Relation.ReflTransGen.tail h2 rfb⟩
            · rintro ⟨h1, h2⟩
              rcases tail_cases i h1 h2 with h | h
              · exact Or.inl ⟨h1, h⟩
              · exact Or.inr ⟨h1, h⟩
          · intro x hx
            show _ = ((c1 || c2) && (gs.foldl stp x).getD bw false ||
              (gs.getD j dg).op.eval [e1 x, e2 x])
            rw [hval x hx, v1 x hx, v2 x hx]
            rcases hop with ho | ho
            · have hc : (c1 || c2) = false := by
                by_contra hh
                rw [Bool.not_eq_false] at hh
                have := h12 (tgc hh)
                rw [ho] at this
                exact GateOp.noConfusion this
              rw [Bool.or_eq_false_iff] at hc
              rw [ho, hc.1, hc.2, evand, evand]
              rfl
            · rw [ho, evor, evor]
              exact bool1 _ _ _ _ _

theorem chain (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw) :
    ∀ d w, m + gs.length - w = d → (w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg)) →
      Relation.ReflTransGen (rf m gs Rg) w (m + tj) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro w hd hw
    by_cases hwt : w = m + tj
    · rw [hwt]
    · have r1 : rd gs Rg w = 1 := by
        rcases hw with h | ⟨h1, h2⟩
        · exact (H.2.2.2.2.2.2.2.2.1 w h).2
        · have := H.2.2.2.2.2.2.2.2.2.1 _ h2
          have e : m + (w - m) = w := by omega
          rw [e, ifn (by omega)] at this
          exact this
      obtain ⟨r, hrR, hrm⟩ := exreader gs Rg w (by omega)
      have hrf : rf m gs Rg w (m + r) := ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hrR,
        by rw [Nat.add_sub_cancel_left]; exact hrm⟩
      have hlt := rf_lt m gs S Rg tj bw H _ _ hrf
      have hrl := H.2.2.1 r hrR
      exact Relation.ReflTransGen.head hrf (ih (m + gs.length - (m + r)) (by omega) (m + r) rfl
        (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hrR⟩))

theorem depC (m : ℕ) (gs : List Gate) (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < m + j)
    (x y : List Bool) (hx : x.length = m) (hy : y.length = m) :
    ∀ w, (∀ k < m, Relation.ReflTransGen (fd m gs) k w → x.getD k false = y.getD k false) →
      (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h1 : w < m
    · rw [inp gs x w (by omega), inp gs y w (by omega)]
      exact h w h1 Relation.ReflTransGen.refl
    · by_cases h2 : m + gs.length ≤ w
      · rw [beyond gs x w (by omega), beyond gs y w (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, w = m + j := ⟨w - m, by omega⟩
        have hj : j < gs.length := by omega
        have e1 := wire_at gs x j hj
        have e2 := wire_at gs y j hj
        rw [hx] at e1
        rw [hy] at e2
        rw [e1, e2]
        congr 1
        apply List.map_congr_left
        intro c hc
        have hlt := hrb j hj c hc
        rw [ifp hlt, ifp hlt]
        exact ih c hlt (fun k hk hr => h k hk (Relation.ReflTransGen.tail hr ⟨j, hj, rfl, hc⟩))

theorem path (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw)
    (i : ℕ) (hi : i ∈ S) : ∀ w, Relation.ReflTransGen (fd m gs) i w →
      (w = i ∨ (m ≤ w ∧ w - m ∈ Rg) ∨ m + tj < w) := by
  intro w hr
  induction hr with
  | refl => exact Or.inl rfl
  | tail _ hf ih =>
    obtain ⟨j', hj', rfl, hb'⟩ := hf
    have hlt := H.1 j' hj' _ hb'
    have h3 := H.2.2.1
    rcases ih with e | ⟨hm, hr⟩ | hgt
    · rw [e] at hb'
      obtain ⟨r, hrR, hrm⟩ := exreader gs Rg i (by rw [(H.2.2.2.2.2.2.2.2.1 i hi).2])
      have := uniqR gs (Finset.range gs.length) i j' r (by rw [(H.2.2.2.2.2.2.2.2.1 i hi).1])
        (Finset.mem_range.2 hj') (Finset.mem_range.2 (h3 r hrR)) hb' hrm
      exact Or.inr (Or.inl ⟨by omega, by rw [Nat.add_sub_cancel_left, this]; exact hrR⟩)
    · rename_i b _
      by_cases ht : b - m = tj
      · exact Or.inr (Or.inr (by omega))
      · have e : m + (b - m) = b := by omega
        have r1 : rd gs Rg b = 1 := by
          have := H.2.2.2.2.2.2.2.2.2.1 _ hr
          rw [e, ifn ht] at this
          exact this
        have r2 : rd gs (Finset.range gs.length) b = 1 := by
          have := H.2.2.2.2.2.2.2.2.2.2.1 _ hr ht
          rw [e] at this
          exact this
        obtain ⟨r, hrR, hrm⟩ := exreader gs Rg b (by omega)
        have := uniqR gs (Finset.range gs.length) b j' r (by omega)
          (Finset.mem_range.2 hj') (Finset.mem_range.2 (h3 r hrR)) hb' hrm
        exact Or.inr (Or.inl ⟨by omega, by rw [Nat.add_sub_cancel_left, this]; exact hrR⟩)
    · exact Or.inr (Or.inr (by omega))

theorem blind (m : ℕ) (gs : List Gate) (S Rg : Finset ℕ) (tj bw : ℕ) (H : Hyp m gs S Rg tj bw)
    (htg : Relation.TransGen (rf m gs Rg) bw (m + tj)) (x y : List Bool) (hx : x.length = m)
    (hy : y.length = m) (hag : ∀ i < m, i ∉ S → x.getD i false = y.getD i false) :
    (gs.foldl stp x).getD bw false = (gs.foldl stp y).getD bw false := by
  apply depC m gs H.1 x y hx hy
  intro k hk hr
  apply hag k hk
  intro hkS
  rcases path m gs S Rg tj bw H k hkS bw hr with e | h | h
  · exact H.2.2.2.2.2.1 (e ▸ hkS)
  · exact H.2.2.2.2.2.2.1 h
  · have := tg_lt m gs S Rg tj bw H _ _ htg
    omega

theorem sum_getD (l : List Gate) (w : ℕ) :
    ∑ j ∈ Finset.range l.length, (l.getD j dg).inputs.count w = cnt l w := by
  induction l using List.reverseRecOn with
  | nil => simp [cnt]
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ, getD_last l a dg _ rfl]
    have e : ∑ j ∈ Finset.range l.length, ((l ++ [a]).getD j dg).inputs.count w =
        ∑ j ∈ Finset.range l.length, (l.getD j dg).inputs.count w := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [getD_left l a dg j (Finset.mem_range.1 hj)]
    rw [e, ih]
    simp [cnt]

theorem ofFn_get (m : ℕ) (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem main : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (S Rg : Finset ℕ) (tj bw : ℕ),
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C → tj ∈ Rg → (∀ j ∈ Rg, j < C.size) →
  (∀ i ∈ S, i < m) → 2 ≤ S.card →
  (∀ j ∈ Rg,
    (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) ∧
    ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg) ∨ w = bw) →
  bw ∉ S → ¬ (m ≤ bw ∧ bw - m ∈ Rg) →
  PEqualNP.MetaComplexity.NestedCover.readsIn C Rg bw ≤ 1 →
  (∀ i ∈ S, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) i = 1 ∧
    PEqualNP.MetaComplexity.NestedCover.readsIn C Rg i = 1) →
  (∀ j ∈ Rg, PEqualNP.MetaComplexity.NestedCover.readsIn C Rg (m + j) = if j = tj then 0 else 1) →
  (∀ j ∈ Rg, j ≠ tj → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 1) →
  (∀ j ∈ Rg,
    Relation.TransGen (fun a c => m ≤ c ∧ c - m ∈ Rg ∧
      a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (c - m)).inputs) bw (m + j) →
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  ∃ (F : PEqualNP.CircuitLowerBounds.Circuit) (b : (Fin m → Bool) → Bool),
    (∀ g ∈ F.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack m F ∧ 0 < F.size ∧ F.output + 1 = m + F.size ∧
    (∀ i < m, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i = if i ∈ S then 1 else 0) ∧
    (∀ j < F.size, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (m + j) =
      if j + 1 = F.size then 0 else 1) ∧
    (∀ x y : Fin m → Bool, (∀ i : Fin m, (i : ℕ) ∉ S → x i = y i) → b x = b y) ∧
    ∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD (m + tj) false = (b x || F.eval (List.ofFn x)) := by
  intro m C S Rg tj bw hrb htj hRg hS hcard h6 hbS hbR h8 h9 h10 h11 h12
  obtain ⟨gs, o⟩ := C
  have H : Hyp m gs S Rg tj bw := ⟨hrb, htj, hRg, hS, h6, hbS, hbR, h8, h9, h10, h11, h12⟩
  obtain ⟨f, L, ev, sz, c, sp, nd, mem, tg, val⟩ := extract m gs S Rg tj bw H (m + tj)
    (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact htj⟩)
  have hLS : ∀ i, i ∈ L ↔ i ∈ S := fun i => (mem i).trans
    ⟨fun h => h.1, fun h => ⟨h, chain m gs S Rg tj bw H _ i rfl (Or.inl h)⟩⟩
  have hsz : 1 ≤ sz := by
    have h1 : S ⊆ L.toFinset := by
      intro i hi
      rw [List.mem_toFinset]
      exact (hLS i).2 hi
    have h2 := Finset.card_le_card h1
    have h3 := List.toFinset_card_le L
    have h4 := sp.1
    omega
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := sp.2.2.2 m (Nat.le_refl m)
  have ho := a5 hsz
  have hlen : ∀ x : Fin m → Bool, (List.ofFn x).length = m := by
    intro x
    simp
  refine ⟨⟨(f m).1, (f m).2⟩, fun x => c && (gs.foldl stp (List.ofFn x)).getD bw false, a2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    have hj' : j < (f m).1.length := hj
    exact a3 j (by omega) i hi
  · show 0 < (f m).1.length
    omega
  · show (f m).2 + 1 = m + (f m).1.length
    omega
  · intro i hi
    show ∑ j ∈ Finset.range (f m).1.length, ((f m).1.getD j dg).inputs.count i = if i ∈ S then 1 else 0
    rw [sum_getD]
    have h := a6 i
    rw [ifn (by omega)] at h
    by_cases hiS : i ∈ S
    · rw [ifp (Or.inl ((hLS i).2 hiS))] at h
      rw [ifp hiS]
      omega
    · rw [ifn (not_or.2 ⟨fun q => hiS ((hLS i).1 q), by omega⟩)] at h
      rw [ifn hiS]
      omega
  · intro j hj
    have hj' : j < (f m).1.length := hj
    show ∑ k ∈ Finset.range (f m).1.length, ((f m).1.getD k dg).inputs.count (m + j) =
      if j + 1 = (f m).1.length then 0 else 1
    rw [sum_getD]
    have h := a6 (m + j)
    rw [ifp (Or.inr ⟨by omega, by omega⟩)] at h
    split_ifs at h ⊢ <;> omega
  · intro x y hxy
    show (c && (gs.foldl stp (List.ofFn x)).getD bw false) =
      (c && (gs.foldl stp (List.ofFn y)).getD bw false)
    cases hc : c with
    | false => rfl
    | true =>
      rw [blind m gs S Rg tj bw H (tg hc) (List.ofFn x) (List.ofFn y) (hlen x) (hlen y)
        (fun i hi hiS => by
          rw [ofFn_get m x i hi, ofFn_get m y i hi]
          exact hxy ⟨i, hi⟩ hiS)]
  · intro x
    show (gs.foldl stp (List.ofFn x)).getD (m + tj) false =
      ((c && (gs.foldl stp (List.ofFn x)).getD bw false) ||
        ((f m).1.foldl stp (List.ofFn x)).getD (f m).2 false)
    rw [a7 _ (hlen x)]
    exact val _ (hlen x)

end PEqualNP.Outside.L_meta_21437

theorem PEqualNP.Outside.L_meta_21437 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (S Rg : Finset ℕ) (tj bw : ℕ),
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C → tj ∈ Rg → (∀ j ∈ Rg, j < C.size) →
  (∀ i ∈ S, i < m) → 2 ≤ S.card →
  (∀ j ∈ Rg,
    (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) ∧
    ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg) ∨ w = bw) →
  bw ∉ S → ¬ (m ≤ bw ∧ bw - m ∈ Rg) →
  PEqualNP.MetaComplexity.NestedCover.readsIn C Rg bw ≤ 1 →
  (∀ i ∈ S, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) i = 1 ∧
    PEqualNP.MetaComplexity.NestedCover.readsIn C Rg i = 1) →
  (∀ j ∈ Rg, PEqualNP.MetaComplexity.NestedCover.readsIn C Rg (m + j) = if j = tj then 0 else 1) →
  (∀ j ∈ Rg, j ≠ tj → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 1) →
  (∀ j ∈ Rg,
    Relation.TransGen (fun a c => m ≤ c ∧ c - m ∈ Rg ∧
      a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (c - m)).inputs) bw (m + j) →
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  ∃ (F : PEqualNP.CircuitLowerBounds.Circuit) (b : (Fin m → Bool) → Bool),
    (∀ g ∈ F.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack m F ∧ 0 < F.size ∧ F.output + 1 = m + F.size ∧
    (∀ i < m, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i = if i ∈ S then 1 else 0) ∧
    (∀ j < F.size, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (m + j) =
      if j + 1 = F.size then 0 else 1) ∧
    (∀ x y : Fin m → Bool, (∀ i : Fin m, (i : ℕ) ∉ S → x i = y i) → b x = b y) ∧
    ∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD (m + tj) false = (b x || F.eval (List.ofFn x)) :=
  PEqualNP.Outside.L_meta_21437.main


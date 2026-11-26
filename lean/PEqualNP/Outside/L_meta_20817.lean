import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20817

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

theorem getD_def (gs : List Gate) (g : ℕ) (h : g < gs.length) (d1 d2 : Gate) : gs.getD g d1 = gs.getD g d2 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_mem (gs : List Gate) (g : ℕ) (h : g < gs.length) (d : Gate) : gs.getD g d ∈ gs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem agree (N : ℕ) (gs : List Gate) (o : ℕ) (x x' : List Bool) (hx : x.length = N) (hx' : x'.length = N)
    (D : ℕ → Prop) (hag : ∀ w < N, ¬ D w → x.getD w false = x'.getD w false)
    (hD : ∀ g < gs.length, (g = o ∨ g ∈ (cl N gs).getD o []) → ∀ w ∈ (gs.getD g dg).inputs, ¬ D w) :
    ∀ i, i < gs.length → (i = o ∨ i ∈ (cl N gs).getD o []) →
      (gs.foldl stp x).getD (N + i) false = (gs.foldl stp x').getD (N + i) false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hR
    have e1 := wire_at gs x i hi
    have e2 := wire_at gs x' i hi
    rw [hx] at e1
    rw [hx'] at e2
    rw [e1, e2]
    congr 1
    apply List.map_congr_left
    intro w hw
    split_ifs with h
    · by_cases hwN : w < N
      · rw [inp gs x w (by omega), inp gs x' w (by omega)]
        exact hag w hwN (hD i hi hR w hw)
      · have hc := closure N gs o i w hi hw (by omega) h hR
        have := ih (w - N) (by omega) (by omega) hc
        have e : N + (w - N) = w := by omega
        rw [e] at this
        exact this
    · rfl

theorem magree (N : ℕ) (gs : List Gate) (o : ℕ) (x x' : List Bool) (hx : x.length = N) (hx' : x'.length = N)
    (hM : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (D : ℕ → Prop) (hag : ∀ w < N, ¬ D w → x.getD w false = true → x'.getD w false = true)
    (hD : ∀ g < gs.length, (g = o ∨ g ∈ (cl N gs).getD o []) → ∀ w ∈ (gs.getD g dg).inputs, ¬ D w) :
    ∀ i, i < gs.length → (i = o ∨ i ∈ (cl N gs).getD o []) →
      (gs.foldl stp x).getD (N + i) false = true → (gs.foldl stp x').getD (N + i) false = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hR
    have e1 := wire_at gs x i hi
    have e2 := wire_at gs x' i hi
    rw [hx] at e1
    rw [hx'] at e2
    rw [e1, e2]
    have key : ∀ w ∈ (gs.getD i dg).inputs,
        (if w < N + i then (gs.foldl stp x).getD w false else false) = true →
        (if w < N + i then (gs.foldl stp x').getD w false else false) = true := by
      intro w hw
      split_ifs with h
      · by_cases hwN : w < N
        · rw [inp gs x w (by omega), inp gs x' w (by omega)]
          exact hag w hwN (hD i hi hR w hw)
        · have hc := closure N gs o i w hi hw (by omega) h hR
          have := ih (w - N) (by omega) (by omega) hc
          have e : N + (w - N) = w := by omega
          rw [e] at this
          exact this
      · exact fun h => h
    rcases hM _ (getD_mem gs i hi dg) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      rintro h b ⟨w, hw, rfl⟩
      exact key w hw (h _ ⟨w, hw, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨w, hw, rfl⟩, h⟩
      exact ⟨_, ⟨w, hw, rfl⟩, key w hw h⟩

theorem indep (N : ℕ) (gs : List Gate) (o : ℕ) (x x' : List Bool) (hx : x.length = N) (hx' : x'.length = N)
    (D : ℕ → Prop) (hag : ∀ w < N, ¬ D w → x.getD w false = x'.getD w false)
    (hD : ∀ g < gs.length, ∀ w ∈ (gs.getD g dg).inputs, ¬ D w) (ho : ¬ D o) :
    (gs.foldl stp x).getD o false = (gs.foldl stp x').getD o false := by
  by_cases h1 : o < N
  · rw [inp gs _ o (by omega), inp gs _ o (by omega)]
    exact hag o h1 ho
  · by_cases h2 : N + gs.length ≤ o
    · rw [beyond gs _ o (by omega), beyond gs _ o (by omega)]
    · have := agree N gs (o - N) x x' hx hx' D hag (fun g hg _ => hD g hg) (o - N) (by omega) (Or.inl rfl)
      have e : N + (o - N) = o := by omega
      rw [e] at this
      exact this

theorem unread (C : Circuit) (w : ℕ)
    (h : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w = 0) :
    ∀ g < C.gates.length, w ∉ (C.gates.getD g dg).inputs := by
  intro g hg
  unfold PEqualNP.MetaComplexity.NestedCover.readsIn at h
  rw [Finset.sum_eq_zero_iff] at h
  have := h g (Finset.mem_range.2 hg)
  exact List.count_eq_zero.1 this

theorem arith (n a b : ℕ) (hn : 3 ≤ n) (ha : a < n) (hb : b < n) (h1 : a = (b + 1) % n)
    (h2 : b = (a + 1) % n) : False := by
  by_cases h : b + 1 < n
  · rw [Nat.mod_eq_of_lt h] at h1
    by_cases h' : a + 1 < n
    · rw [Nat.mod_eq_of_lt h'] at h2; omega
    · have e : a + 1 = n := by omega
      rw [e, Nat.mod_self] at h2; omega
  · have e : b + 1 = n := by omega
    rw [e, Nat.mod_self] at h1
    by_cases h' : a + 1 < n
    · rw [Nat.mod_eq_of_lt h'] at h2; omega
    · omega

theorem cnt (n : ℕ) (R : ℕ → ℕ) (inst : DecidablePred fun w => 1 ≤ R w)
    (hr : ∀ a b, a < n → b < n → R a = 0 → R b = 0 → a = b)
    (hc : ∀ a b, a < n → b < n → R (n + a) = 0 → R (n + b) = 0 → a = b) :
    n + n ≤ (@Finset.filter ℕ (fun w => 1 ≤ R w) inst (Finset.range (n + n))).card + 2 := by
  have h := @Finset.card_filter_add_card_filter_not ℕ (Finset.range (n + n)) (fun w => 1 ≤ R w) inst _
  rw [Finset.card_range] at h
  have hT : (Finset.filter (fun w => ¬ 1 ≤ R w) (Finset.range (n + n))).card ≤ 2 := by
    have hsub : Finset.filter (fun w => ¬ 1 ≤ R w) (Finset.range (n + n)) ⊆
        Finset.filter (fun w => R w = 0) (Finset.range n) ∪
        Finset.filter (fun w => n ≤ w ∧ R w = 0) (Finset.range (n + n)) := by
      intro w hw
      rw [Finset.mem_filter, Finset.mem_range] at hw
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range]
      by_cases hwn : w < n
      · exact Or.inl ⟨hwn, by omega⟩
      · exact Or.inr ⟨hw.1, by omega, by omega⟩
    have h1 : (Finset.filter (fun w => R w = 0) (Finset.range n)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter, Finset.mem_range] at ha hb
      exact hr a b ha.1 hb.1 ha.2 hb.2
    have h2 : (Finset.filter (fun w => n ≤ w ∧ R w = 0) (Finset.range (n + n))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter, Finset.mem_range] at ha hb
      have ea : n + (a - n) = a := by omega
      have eb : n + (b - n) = b := by omega
      have := hc (a - n) (b - n) (by omega) (by omega) (by rw [ea]; exact ha.2.2) (by rw [eb]; exact hb.2.2)
      omega
    have := Finset.card_le_card hsub
    have := Finset.card_union_le (Finset.filter (fun w => R w = 0) (Finset.range n))
      (Finset.filter (fun w => n ≤ w ∧ R w = 0) (Finset.range (n + n)))
    omega
  omega

theorem main : ∀ (n : ℕ), 3 ≤ n → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.Represents.Represents (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)) C →
  (∀ u1 u2 : Fin n,
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) u1.val = 0 →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) u2.val = 0 → u1 = u2) ∧
  (∀ v1 v2 : Fin n,
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + v1.val) = 0 →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + v2.val) = 0 → v1 = v2) ∧
  n + n ≤ (@Finset.filter ℕ
      (fun w => 1 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w)
      (fun d1 => Classical.propDecidable _) (Finset.range (n + n))).card + 2 := by
  intro n hn C hrep
  have hout : ∀ u : Fin n, C.output ≠ u.val ∧ C.output ≠ n + u.val := by
    intro u
    have h := hrep u u
    obtain ⟨gs, o⟩ := C
    have hx : (oneEach u u).length = n + n := by simp [oneEach]
    have hf : (gs.foldl stp (oneEach u u)).getD o false = false := by
      rw [show (gs.foldl stp (oneEach u u)).getD o false = (Circuit.mk gs o).eval (oneEach u u) from rfl, h]
      simp
    constructor
    · intro e
      simp only at e
      rw [inp gs _ o (by omega)] at hf
      have := (oe u u o).2 (Or.inl e)
      rw [this] at hf
      exact Bool.noConfusion hf
    · intro e
      simp only at e
      rw [inp gs _ o (by omega)] at hf
      have := (oe u u o).2 (Or.inr e)
      rw [this] at hf
      exact Bool.noConfusion hf
  have hrow : ∀ u1 u2 : Fin n,
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) u1.val = 0 →
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) u2.val = 0 → u1 = u2 := by
    intro u1 u2 h1 h2
    by_contra hne
    have hne' : u1.val ≠ u2.val := fun e => hne (Fin.ext e)
    have r1 := unread C _ h1
    have r2 := unread C _ h2
    have key : ∀ v : Fin n, C.eval (oneEach u1 v) = C.eval (oneEach u2 v) := by
      intro v
      obtain ⟨gs, o⟩ := C
      have hx : (oneEach u1 v).length = n + n := by simp [oneEach]
      have hx' : (oneEach u2 v).length = n + n := by simp [oneEach]
      exact indep (n + n) gs o _ _ hx hx' (fun w => w = u1.val ∨ w = u2.val)
        (by
          intro w _ hw
          rw [Bool.eq_iff_iff, oe, oe]
          constructor
          · rintro (h | h)
            · exact absurd (Or.inl h) hw
            · exact Or.inr h
          · rintro (h | h)
            · exact absurd (Or.inr h) hw
            · exact Or.inr h)
        (by
          intro g hg w hw hDw
          rcases hDw with h | h
          · exact r1 g hg (h ▸ hw)
          · exact r2 g hg (h ▸ hw))
        (by
          intro hDw
          rcases hDw with h | h
          · exact (hout u1).1 h
          · exact (hout u2).1 h)
    have k1 := key u1
    rw [hrep u1 u1, hrep u2 u1] at k1
    have k2 := key u2
    rw [hrep u1 u2, hrep u2 u2] at k2
    simp only [ne_eq, not_true_eq_false, false_and, decide_false] at k1 k2
    have a1 : u1.val = (u2.val + 1) % n := by
      by_contra hh
      have := k1.symm
      simp [hne', hh] at this
    have a2 : u2.val = (u1.val + 1) % n := by
      by_contra hh
      simp [Ne.symm hne', hh] at k2
    exact arith n u1.val u2.val hn u1.isLt u2.isLt a1 a2
  have hcol : ∀ v1 v2 : Fin n,
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + v1.val) = 0 →
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + v2.val) = 0 → v1 = v2 := by
    intro v1 v2 h1 h2
    by_contra hne
    have hne' : v1.val ≠ v2.val := fun e => hne (Fin.ext e)
    have r1 := unread C _ h1
    have r2 := unread C _ h2
    have key : ∀ u : Fin n, C.eval (oneEach u v1) = C.eval (oneEach u v2) := by
      intro u
      obtain ⟨gs, o⟩ := C
      have hx : (oneEach u v1).length = n + n := by simp [oneEach]
      have hx' : (oneEach u v2).length = n + n := by simp [oneEach]
      exact indep (n + n) gs o _ _ hx hx' (fun w => w = n + v1.val ∨ w = n + v2.val)
        (by
          intro w _ hw
          rw [Bool.eq_iff_iff, oe, oe]
          constructor
          · rintro (h | h)
            · exact Or.inl h
            · exact absurd (Or.inl h) hw
          · rintro (h | h)
            · exact Or.inl h
            · exact absurd (Or.inr h) hw)
        (by
          intro g hg w hw hDw
          rcases hDw with h | h
          · exact r1 g hg (h ▸ hw)
          · exact r2 g hg (h ▸ hw))
        (by
          intro hDw
          rcases hDw with h | h
          · exact (hout v1).2 h
          · exact (hout v2).2 h)
    have k1 := key v1
    rw [hrep v1 v1, hrep v1 v2] at k1
    have k2 := key v2
    rw [hrep v2 v1, hrep v2 v2] at k2
    simp only [ne_eq, not_true_eq_false, false_and, decide_false] at k1 k2
    have a2 : v2.val = (v1.val + 1) % n := by
      by_contra hh
      have := k1.symm
      simp [Ne.symm hne', hh] at this
    have a1 : v1.val = (v2.val + 1) % n := by
      by_contra hh
      simp [hne', hh] at k2
    exact arith n v1.val v2.val hn v1.isLt v2.isLt a1 a2
  refine ⟨hrow, hcol, ?_⟩
  exact cnt n (fun w => PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) _
    (fun a b ha hb h1 h2 => congrArg Fin.val (hrow ⟨a, ha⟩ ⟨b, hb⟩ h1 h2))
    (fun a b ha hb h1 h2 => congrArg Fin.val (hcol ⟨a, ha⟩ ⟨b, hb⟩ h1 h2))

end PEqualNP.Outside.L_meta_20817

theorem PEqualNP.Outside.L_meta_20817 : ∀ (n : ℕ), 3 ≤ n → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.Represents.Represents (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)) C →
  (∀ u1 u2 : Fin n,
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) u1.val = 0 →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) u2.val = 0 → u1 = u2) ∧
  (∀ v1 v2 : Fin n,
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + v1.val) = 0 →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + v2.val) = 0 → v1 = v2) ∧
  n + n ≤ (@Finset.filter ℕ
      (fun w => 1 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w)
      (fun d1 => Classical.propDecidable _) (Finset.range (n + n))).card + 2 :=
  PEqualNP.Outside.L_meta_20817.main

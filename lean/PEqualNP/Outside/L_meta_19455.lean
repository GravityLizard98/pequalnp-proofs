import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19455

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

theorem main : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin m), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C → (C.output ≠ (n + v.val) ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → (n + v.val) ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∀ (u : Fin n) (v' : Fin m), A u v = true → A u v' = true := by
  intro n m A C v hmono hrep hs u v'
  rw [← hrep u v, ← hrep u v']
  obtain ⟨gs, o⟩ := C
  obtain ⟨ho, hg⟩ := hs
  simp only at ho hg
  show (gs.foldl stp (oneEach u v)).getD o false = true → (gs.foldl stp (oneEach u v')).getD o false = true
  have hx : (oneEach u v).length = n + m := by simp [oneEach]
  have hx' : (oneEach u v').length = n + m := by simp [oneEach]
  have hag : ∀ w < n + m, ¬ (w = n + v.val) →
      (oneEach u v).getD w false = true → (oneEach u v').getD w false = true := by
    intro w _ hw
    rw [oe, oe]
    rintro (h | h)
    · exact Or.inl h
    · exact absurd h hw
  by_cases h1 : o < n + m
  · rw [inp gs _ o (by omega), inp gs _ o (by omega)]
    exact hag o h1 (by omega)
  · by_cases h2 : n + m + gs.length ≤ o
    · rw [beyond gs _ o (by omega), beyond gs _ o (by omega)]
      exact fun h => h
    · have := magree (n + m) gs (o - (n + m)) (oneEach u v) (oneEach u v') hx hx'
        (fun g hgm => by
          have := (hmono g hgm).1
          simpa using this)
        (fun w => w = n + v.val) hag
        (by
          intro g hgl hR w hw hDw
          have hcond : o = n + m + g ∨ (n + m ≤ o ∧ PEqualNP.EdgeOwnership.InCone (n + m) ⟨gs, o⟩ g (o - (n + m))) := by
            rcases hR with h | h
            · exact Or.inl (by omega)
            · exact Or.inr ⟨by omega, h⟩
          rw [getD_def gs g hgl dg ⟨GateOp.and, []⟩] at hw
          exact hg g hgl hcond (hDw ▸ hw))
        (o - (n + m)) (by omega) (Or.inl rfl)
      have e : n + m + (o - (n + m)) = o := by omega
      rw [e] at this
      exact this

end PEqualNP.Outside.L_meta_19455

theorem PEqualNP.Outside.L_meta_19455 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin m), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C → (C.output ≠ (n + v.val) ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → (n + v.val) ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∀ (u : Fin n) (v' : Fin m), A u v = true → A u v' = true :=
  PEqualNP.Outside.L_meta_19455.main

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25001

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


def kill (w : ℕ) (g : Gate) : Gate := if w ∈ g.inputs then ⟨GateOp.or, []⟩ else g

theorem kill_getD (w : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (gs.map (kill w)).getD j dg = kill w (gs.getD j dg) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj]
  rfl

theorem getD_irrel (gs : List Gate) (j : ℕ) (hj : j < gs.length) (d1 d2 : Gate) :
    gs.getD j d1 = gs.getD j d2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

theorem keep (N w : ℕ) (gs : List Gate) (o : ℕ) (x : List Bool) (hx : x.length = N)
    (hc : ∀ g < gs.length, (o = N + g ∨ (N ≤ o ∧ g ∈ (cl N gs).getD (o - N) [])) →
      w ∉ (gs.getD g dg).inputs) :
    ∀ j, j < gs.length → (o = N + j ∨ (N ≤ o ∧ j ∈ (cl N gs).getD (o - N) [])) →
      ((gs.map (kill w)).foldl stp x).getD (N + j) false = (gs.foldl stp x).getD (N + j) false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hR
    have hl : (gs.map (kill w)).length = gs.length := List.length_map _
    have h1 := wire_at (gs.map (kill w)) x j (by omega)
    have h2 := wire_at gs x j hj
    rw [hx] at h1 h2
    rw [h1, h2, kill_getD w gs j hj]
    have hk : kill w (gs.getD j dg) = gs.getD j dg := by
      unfold kill
      rw [ifn (hc j hj hR)]
    rw [hk]
    congr 1
    apply List.map_congr_left
    intro k hkin
    by_cases hlt : k < N + j
    · rw [ifp hlt, ifp hlt]
      by_cases hkN : k < N
      · rw [inp _ x k (by omega), inp _ x k (by omega)]
      · have hNo : N ≤ o := by
          rcases hR with h | h
          · omega
          · exact h.1
        have hR' : j = o - N ∨ j ∈ (cl N gs).getD (o - N) [] := by
          rcases hR with h | h
          · left
            omega
          · exact Or.inr h.2
        have hcl := closure N gs (o - N) j k hj hkin (by omega) hlt hR'
        have e : k = N + (k - N) := by omega
        rw [e]
        apply ih (k - N) (by omega) (by omega)
        rcases hcl with h | h
        · left
          omega
        · exact Or.inr ⟨hNo, h⟩
    · rw [ifn hlt, ifn hlt]

theorem main : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ), w < n + m → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ w ∧ ∀ g < C.gates.length, (C.output = (n + m) + g ∨ ((n + m) ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → w ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents A C2 ∧ C2.size ≤ C.size ∧ (∀ g ∈ C2.gates, w ∉ g.inputs) ∧ C2.output ≠ w ∧ (∀ i < (n + m), ((∃ g ∈ C2.gates, i ∈ g.inputs) ∨ C2.output = i) → ((∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i)) := by
  intro n m A C w hw hF hrep hcone
  obtain ⟨gs, o⟩ := C
  obtain ⟨how, hc0⟩ := hcone
  have how' : o ≠ w := how
  have hc : ∀ g < gs.length, (o = (n + m) + g ∨ ((n + m) ≤ o ∧ g ∈ (cl (n + m) gs).getD (o - (n + m)) [])) →
      w ∉ (gs.getD g dg).inputs := by
    intro g hg hR
    rw [getD_irrel gs g hg dg ⟨GateOp.and, []⟩]
    exact hc0 g hg hR
  have hl : (gs.map (kill w)).length = gs.length := List.length_map _
  refine ⟨⟨gs.map (kill w), o⟩, ?_, ?_, ?_, ?_, how, ?_⟩
  · intro g hg
    change g ∈ gs.map (kill w) at hg
    rw [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    unfold kill
    split_ifs with hin
    · exact ⟨by simp, by simp⟩
    · exact hF g0 hg0
  · intro u v
    have hx : (oneEach u v).length = n + m := by simp [oneEach]
    have hev : (gs.foldl stp (oneEach u v)).getD o false = A u v := hrep u v
    show ((gs.map (kill w)).foldl stp (oneEach u v)).getD o false = A u v
    rw [← hev]
    by_cases h1 : o < n + m
    · rw [inp _ _ o (by omega), inp _ _ o (by omega)]
    · by_cases h2 : o < n + m + gs.length
      · have e : o = (n + m) + (o - (n + m)) := by omega
        rw [e]
        exact keep (n + m) w gs _ (oneEach u v) hx (by rw [← e]; exact hc) (o - (n + m)) (by omega)
          (Or.inl rfl)
      · rw [beyond _ _ o (by rw [hx, hl]; omega), beyond _ _ o (by rw [hx]; omega)]
  · show (gs.map (kill w)).length ≤ gs.length
    omega
  · intro g hg
    change g ∈ gs.map (kill w) at hg
    rw [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    unfold kill
    split_ifs with hin
    · simp
    · exact hin
  · intro i hi h
    rcases h with ⟨g, hg, hig⟩ | h
    · change g ∈ gs.map (kill w) at hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      unfold kill at hig
      split_ifs at hig with hin
      · simp at hig
      · exact Or.inl ⟨g0, hg0, hig⟩
    · exact Or.inr h

end PEqualNP.Outside.L_meta_25001

theorem PEqualNP.Outside.L_meta_25001 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ), w < n + m → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ w ∧ ∀ g < C.gates.length, (C.output = (n + m) + g ∨ ((n + m) ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → w ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents A C2 ∧ C2.size ≤ C.size ∧ (∀ g ∈ C2.gates, w ∉ g.inputs) ∧ C2.output ≠ w ∧ (∀ i < (n + m), ((∃ g ∈ C2.gates, i ∈ g.inputs) ∨ C2.output = i) → ((∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i)) :=
  PEqualNP.Outside.L_meta_25001.main

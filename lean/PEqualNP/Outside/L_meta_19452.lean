import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19452
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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

theorem dep (N : ℕ) (P : ℕ → Prop) (gs : List Gate)
    (hP : ∀ j (h : j < gs.length), P (N + j) → ∀ i ∈ (gs[j]).inputs, i < N + j → P i)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, P i → x.getD i false = y.getD i false) :
    ∀ w, P w → (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil => simpa using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun j h hj i hi hlt => hP j (by simp; omega) hj i (by
      rw [List.getElem_append_left h]; exact hi) hlt)
    intro w hw
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [getD_snoc, getD_snoc, len, len, hx, hy]
    split_ifs with h1 h3
    · exact ih w hw
    · congr 1
      refine List.map_congr_left fun i hi => ?_
      by_cases hlt : i < N + gs.length
      · exact ih i (hP gs.length (by simp) (h3 ▸ hw) i (by simpa using hi) hlt)
      · rw [List.getD_eq_default _ _ (by rw [len, hx]; omega),
          List.getD_eq_default _ _ (by rw [len, hy]; omega)]
    · rfl

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (gs.foldl stp x).getD i false = true → (gs.foldl stp y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa using hxy
  | append_singleton gs g ih =>
    have ih := ih fun g' h => hg g' (by simp [h])
    intro i
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [getD_snoc, getD_snoc, len, len, hl]
    split_ifs
    · exact ih i
    · rcases hg g (by simp) with h | h
      · simp only [h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
        exact fun hh a ha => ih a (hh a ha)
      · simp only [h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact fun ⟨a, ha, hh⟩ => ⟨a, ha, ih a hh⟩
    · simp

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem ev (C : Circuit) (x : List Bool) : C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_last {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k = l.length) :
    (l ++ [b]).getD k d = b := by
  subst hk; simp [List.getD_eq_getElem?_getD]

theorem getD_left {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k < l.length) :
    (l ++ [b]).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

def dg : Gate := ⟨GateOp.and, []⟩

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

def RP (N : ℕ) (C : Circuit) (g : ℕ) : Prop :=
  C.output = N + g ∨ (N ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone N C g (C.output - N))

def PP (N : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  w = C.output ∨ (N ≤ w ∧ w < N + C.gates.length ∧ RP N C (w - N)) ∨
    (w < N ∧ ∃ g < C.gates.length, RP N C g ∧ w ∈ (C.gates.getD g dg).inputs)

theorem PP_closed (N : ℕ) (C : Circuit) : ∀ j (h : j < C.gates.length), PP N C (N + j) →
    ∀ i ∈ (C.gates[j]).inputs, i < N + j → PP N C i := by
  intro j h hj i hi hlt
  have hi' : i ∈ (C.gates.getD j dg).inputs := by
    rw [List.getD_eq_getElem _ _ h]; exact hi
  have hr : RP N C j := by
    rcases hj with hj | hj | hj
    · exact Or.inl hj.symm
    · have e : N + j - N = j := by omega
      rw [e] at hj; exact hj.2.2
    · omega
  by_cases hN : i < N
  · exact Or.inr (Or.inr ⟨hN, j, h, hr, hi'⟩)
  · refine Or.inr (Or.inl ⟨by omega, by omega, ?_⟩)
    have hd : (i - N) ∈ (cl N C.gates).getD j [] :=
      (mem_cl N C.gates j _ h).2 ⟨i, hi', by omega, hlt, Or.inl rfl⟩
    rcases hr with hr | hr
    · refine Or.inr ⟨by omega, ?_⟩
      have e : C.output - N = j := by omega
      rw [e]; exact hd
    · exact Or.inr ⟨hr.1, cone_trans N C.gates _ _ j hd hr.2⟩

theorem PP_not (N : ℕ) (C : Circuit) (w : ℕ) (hw : w < N)
    (h : C.output ≠ w ∧ ∀ g < C.gates.length, (C.output = N + g ∨ (N ≤ C.output ∧
      PEqualNP.EdgeOwnership.InCone N C g (C.output - N))) → w ∉ (C.gates.getD g dg).inputs) :
    ¬ PP N C w := by
  rintro (h1 | h1 | h1)
  · exact h.1 h1.symm
  · omega
  · obtain ⟨_, g, hg, hr, hin⟩ := h1
    exact h.2 g hg hr hin

theorem agree (N : ℕ) (C : Circuit) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, PP N C i → x.getD i false = y.getD i false) : C.eval x = C.eval y := by
  rw [ev, ev]
  exact dep N (PP N C) C.gates (PP_closed N C) x y hx hy hxy _ (Or.inl rfl)

theorem setD (x : List Bool) (k : ℕ) : ∀ i, (x.set k false).getD i false =
    if i = k then false else x.getD i false := by
  intro i
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases h : k = i
  · subst h; simp only [ite_true]; split_ifs <;> rfl
  · simp [h, Ne.symm h]

theorem two_rows {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hR : Represents A C)
    (u u' : Fin n) (hu : ¬ PP (n + m) C u.val) (hu' : ¬ PP (n + m) C u'.val) (v : Fin m) :
    A u v = A u' v := by
  rw [← hR u v, ← hR u' v]
  apply agree (n + m) C _ _ (by simp [oneEach]) (by simp [oneEach])
  intro i hi
  rw [Bool.eq_iff_iff, oe, oe]
  constructor
  · rintro (h | h)
    · exact absurd (h ▸ hi) hu
    · exact Or.inr h
  · rintro (h | h)
    · exact absurd (h ▸ hi) hu'
    · exact Or.inr h

theorem two_cols {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hR : Represents A C)
    (v v' : Fin m) (hv : ¬ PP (n + m) C (n + v.val)) (hv' : ¬ PP (n + m) C (n + v'.val))
    (u : Fin n) : A u v = A u v' := by
  rw [← hR u v, ← hR u v']
  apply agree (n + m) C _ _ (by simp [oneEach]) (by simp [oneEach])
  intro i hi
  rw [Bool.eq_iff_iff, oe, oe]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact absurd (h ▸ hi) hv
  · rintro (h | h)
    · exact Or.inl h
    · exact absurd (h ▸ hi) hv'

theorem drop_mono {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hM : Monotone2 C)
    (hR : Represents A C) (u u' : Fin n) (v v' : Fin m) (k : ℕ) (hk : ¬ PP (n + m) C k)
    (hsub : ∀ i, i ≠ k → (i = u.val ∨ i = n + v.val) → (i = u'.val ∨ i = n + v'.val))
    (h1 : A u v = true) : A u' v' = true := by
  rw [← hR u' v']
  rw [← hR u v] at h1
  have hx : (oneEach u v).length = n + m := by simp [oneEach]
  have eq := agree (n + m) C (oneEach u v) ((oneEach u v).set k false) hx
    (by simp [hx]) (fun i hi => by
      rw [setD]; split_ifs with h
      · exact absurd (h ▸ hi) hk
      · rfl)
  rw [eq] at h1
  rw [ev] at h1 ⊢
  refine mono C.gates (fun g hg => by simpa using (hM g hg).1) ((oneEach u v).set k false)
    (oneEach u' v') (by simp [oneEach]) (fun i hi => ?_) C.output h1
  rw [setD] at hi
  split_ifs at hi with h
  rw [oe] at hi ⊢
  exact hsub i h hi

end PEqualNP.Outside.L_meta_19452

theorem PEqualNP.Outside.L_meta_19452 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (u u' : Fin n), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ u.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → (C.output ≠ u'.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u'.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∀ v : Fin m, A u v = A u' v := by
  intro n m A C u u' _ hR hu hu' v
  exact PEqualNP.Outside.L_meta_19452.two_rows A C hR u u'
    (PEqualNP.Outside.L_meta_19452.PP_not (n + m) C u.val (by omega) hu)
    (PEqualNP.Outside.L_meta_19452.PP_not (n + m) C u'.val (by omega) hu') v

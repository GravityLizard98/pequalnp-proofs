import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24492

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

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

theorem colstep (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : Circuit)
    (hrep : ∀ (u : Fin n) (v : Fin m), C.eval (oneEach u (k.succAbove v)) = A u (k.succAbove v)) :
    ∃ C' : Circuit, C'.size = C.size ∧ (FanInTwo C → FanInTwo C') ∧
      Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C' ∧
      (∀ u : Fin n, ((∃ g ∈ C'.gates, u.val ∈ g.inputs) ∨ C'.output = u.val) →
        ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧
      (∀ v : Fin m, ((∃ g ∈ C'.gates, n + v.val ∈ g.inputs) ∨ C'.output = n + v.val) →
        ((∃ g ∈ C.gates, n + (k.succAbove v).val ∈ g.inputs) ∨
          C.output = n + (k.succAbove v).val)) := by
  have hk : k.val ≤ m := Nat.lt_succ_iff.mp k.isLt
  refine ⟨⟨C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)),
    rho (n + k.val) (n + m + 1 + C.gates.length) C.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show (C.gates.map _).length = C.gates.length
    rw [List.length_map]
  · intro hF g hg
    have hg' : g ∈ C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
    rw [List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    have hf := hF g0 hg0
    refine ⟨hf.1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact hf.2
  · intro u v
    have hr : (C.gates.foldl stp (oneEach u (k.succAbove v))).getD C.output false =
      A u (k.succAbove v) := hrep u v
    show ((C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length))).foldl stp (oneEach u v)).getD
      (rho (n + k.val) (n + m + 1 + C.gates.length) C.output) false = A u (k.succAbove v)
    rw [← hr]
    have hlx : (oneEach u v).length = n + m := by simp [oneEach]
    have hlx2 : (oneEach u (k.succAbove v)).length = n + m + 1 := by simp [oneEach]; omega
    refine sim True (n + k.val) (n + m + 1 + C.gates.length) (n + m + 1 + C.gates.length)
      (oneEach u (k.succAbove v)) (oneEach u v)
      (by rw [hlx, hlx2]) (by rw [hlx]; omega) (Or.inr le_rfl) ?_ C.gates (by rw [hlx]; omega)
      (fun _ _ _ _ _ => trivial) C.output (fun _ => trivial)
    intro i _
    apply bool_iff
    rw [oe, oe, sa_val]
    have hu := u.isLt
    have hv := v.isLt
    unfold rho
    split_ifs <;> omega
  · intro u hu
    have hul := u.isLt
    have key : ∀ i, rho (n + k.val) (n + m + 1 + C.gates.length) i = u.val → i = u.val := by
      intro i
      unfold rho
      split_ifs <;> omega
    rcases hu with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      have hmem' : u.val ∈ g0.inputs.map (rho (n + k.val) (n + m + 1 + C.gates.length)) := hmem
      rw [List.mem_map] at hmem'
      obtain ⟨i, hi, hiu⟩ := hmem'
      have := key i hiu
      subst this
      exact Or.inl ⟨g0, hg0, hi⟩
    · exact Or.inr (key _ ho)
  · intro v hv
    have hvl := v.isLt
    have key : ∀ i, rho (n + k.val) (n + m + 1 + C.gates.length) i = n + v.val →
        i = n + (k.succAbove v).val := by
      intro i
      rw [sa_val]
      unfold rho
      split_ifs <;> omega
    rcases hv with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      have hmem' : n + v.val ∈ g0.inputs.map (rho (n + k.val) (n + m + 1 + C.gates.length)) := hmem
      rw [List.mem_map] at hmem'
      obtain ⟨i, hi, hiu⟩ := hmem'
      have := key i hiu
      subst this
      exact Or.inl ⟨g0, hg0, hi⟩
    · exact Or.inr (key _ ho)

theorem delstep (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : Circuit)
    (G1 G2 : List Gate) (h : Gate) (r : ℕ) (Q : Prop)
    (hC : C.gates = G1 ++ h :: G2) (hF : FanInTwo C)
    (hrep : ∀ (u : Fin n) (v : Fin m), C.eval (oneEach u (k.succAbove v)) = A u (k.succAbove v))
    (hr : r < n + m + 1 + G1.length ∨ n + m + 1 + C.gates.length ≤ r)
    (hrin : r < n + m + 1 → r ∈ h.inputs)
    (hQ2 : ∀ g ∈ G2, ∀ i ∈ g.inputs, i = n + m + 1 + G1.length → Q)
    (hQo : C.output = n + m + 1 + G1.length → Q)
    (hv : Q → ∀ (u : Fin n) (v : Fin m),
      h.op.eval (h.inputs.map fun i => (G1.foldl stp (oneEach u (k.succAbove v))).getD i false) =
        (G1.foldl stp (oneEach u (k.succAbove v))).getD r false) :
    ∃ C1 : Circuit, C1.size + 1 = C.size ∧ FanInTwo C1 ∧
      (∀ (u : Fin n) (v : Fin m), C1.eval (oneEach u (k.succAbove v)) = A u (k.succAbove v)) ∧
      (∀ i < n + m + 1, ((∃ g ∈ C1.gates, i ∈ g.inputs) ∨ C1.output = i) →
        ((∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i)) := by
  have hlen : C.gates.length = G1.length + G2.length + 1 := by rw [hC]; simp; omega
  refine ⟨⟨G1 ++ G2.map (rg (n + m + 1 + G1.length) r), rho (n + m + 1 + G1.length) r C.output⟩,
    ?_, ?_, ?_, ?_⟩
  · show (G1 ++ G2.map _).length + 1 = C.gates.length
    rw [hlen]
    simp
  · intro g hg
    have hg' : g ∈ G1 ++ G2.map (rg (n + m + 1 + G1.length) r) := hg
    rw [List.mem_append, List.mem_map] at hg'
    rcases hg' with h1 | ⟨g0, hg0, rfl⟩
    · exact hF g (by rw [hC]; simp [h1])
    · have hf := hF g0 (by rw [hC]; simp [hg0])
      refine ⟨hf.1, ?_⟩
      show (g0.inputs.map _).length ≤ 2
      rw [List.length_map]
      exact hf.2
  · intro u v
    have hx : (oneEach u (k.succAbove v)).length = n + m + 1 := by simp [oneEach]; omega
    have h0 : (C.gates.foldl stp (oneEach u (k.succAbove v))).getD C.output false =
      A u (k.succAbove v) := hrep u v
    show ((G1 ++ G2.map (rg (n + m + 1 + G1.length) r)).foldl stp
      (oneEach u (k.succAbove v))).getD (rho (n + m + 1 + G1.length) r C.output) false = _
    rw [← h0, hC, List.foldl_append, List.foldl_append, List.foldl_cons]
    have hl1 : (G1.foldl stp (oneEach u (k.succAbove v))).length = n + m + 1 + G1.length := by
      rw [len, hx]
    refine sim Q (n + m + 1 + G1.length) r (n + m + 1 + C.gates.length)
      (stp (G1.foldl stp (oneEach u (k.succAbove v))) h) (G1.foldl stp (oneEach u (k.succAbove v)))
      ?_ ?_ ?_ ?_ G2 ?_ hQ2 C.output hQo
    · simp [stp]
    · rw [hl1]
    · rw [hl1]
      exact hr
    · intro i hi
      show (G1.foldl stp (oneEach u (k.succAbove v))).getD (rho (n + m + 1 + G1.length) r i) false =
        (G1.foldl stp (oneEach u (k.succAbove v)) ++ [_]).getD i false
      rw [getD_snoc, hl1]
      unfold rho
      by_cases h1 : i < n + m + 1 + G1.length
      · rw [ifp h1, ifp h1]
      · by_cases h2 : i = n + m + 1 + G1.length
        · rw [ifn h1, ifp h2, ifn h1, ifp h2]
          exact (hv (hi h2) u v).symm
        · rw [ifn h1, ifn h2, ifn h1, ifn h2]
          exact List.getD_eq_default _ _ (by rw [hl1]; omega)
    · rw [hl1, hlen]
      omega
  · intro i hi hrd
    have key : ∀ j, rho (n + m + 1 + G1.length) r j = i →
        j = i ∨ (j = n + m + 1 + G1.length ∧ r = i) := by
      intro j
      unfold rho
      split_ifs <;> omega
    rcases hrd with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ G1 ++ G2.map (rg (n + m + 1 + G1.length) r) := hg
      rw [List.mem_append, List.mem_map] at hg'
      rcases hg' with h1 | ⟨g0, hg0, rfl⟩
      · exact Or.inl ⟨g, by rw [hC]; simp [h1], hmem⟩
      · have hmem' : i ∈ g0.inputs.map (rho (n + m + 1 + G1.length) r) := hmem
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

theorem fin (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : Circuit)
    (G1 G2 : List Gate) (h : Gate) (r : ℕ) (Q : Prop)
    (hC : C.gates = G1 ++ h :: G2) (hF : FanInTwo C) (hrep : Represents A C)
    (hr : r < n + m + 1 + G1.length ∨ n + m + 1 + C.gates.length ≤ r)
    (hrin : r < n + m + 1 → r ∈ h.inputs)
    (hQ2 : ∀ g ∈ G2, ∀ i ∈ g.inputs, i = n + m + 1 + G1.length → Q)
    (hQo : C.output = n + m + 1 + G1.length → Q)
    (hv : Q → ∀ (u : Fin n) (v : Fin m),
      h.op.eval (h.inputs.map fun i => (G1.foldl stp (oneEach u (k.succAbove v))).getD i false) =
        (G1.foldl stp (oneEach u (k.succAbove v))).getD r false) :
    ∃ C2 : Circuit, FanInTwo C2 ∧
      Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ C2.size + 1 ≤ C.size ∧
      (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) →
        ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧
      (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) →
        ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨
          C.output = (n + (k.succAbove v).val))) := by
  obtain ⟨C1, hs1, hF1, hrep1, hrd1⟩ := delstep n m A k C G1 G2 h r Q hC hF
    (fun u v => hrep u (k.succAbove v)) hr hrin hQ2 hQo hv
  obtain ⟨C2, hs2, hF2, hrep2, hu2, hv2⟩ := colstep n m A k C1 hrep1
  refine ⟨C2, hF2 hF1, hrep2, by omega, ?_, ?_⟩
  · intro u hu
    exact hrd1 u.val (by have := u.isLt; omega) (hu2 u hu)
  · intro v hv'
    exact hrd1 _ (by have := (k.succAbove v).isLt; omega) (hv2 v hv')

theorem and_ev (W : List Bool) (a b : ℕ) :
    (⟨GateOp.and, [a, b]⟩ : Gate).op.eval
      ((⟨GateOp.and, [a, b]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (W.getD a false && W.getD b false) := by
  simp [GateOp.eval]

theorem or_ev (W : List Bool) (a b : ℕ) :
    (⟨GateOp.or, [a, b]⟩ : Gate).op.eval
      ((⟨GateOp.or, [a, b]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (W.getD a false || W.getD b false) := by
  simp [GateOp.eval]

theorem not_ev (W : List Bool) (a : ℕ) :
    (⟨GateOp.not, [a]⟩ : Gate).op.eval
      ((⟨GateOp.not, [a]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (!W.getD a false) := by
  simp [GateOp.eval]

theorem ckc (n m : ℕ) (k : Fin (m + 1)) (u : Fin n) (v : Fin m) (gs : List Gate) :
    (gs.foldl stp (oneEach u (k.succAbove v))).getD (n + k.val) false = false := by
  have hx : (oneEach u (k.succAbove v)).length = n + m + 1 := by simp [oneEach]; omega
  rw [pre _ _ _ (by rw [hx]; have := k.isLt; omega)]
  cases hb : (oneEach u (k.succAbove v)).getD (n + k.val) false with
  | false => rfl
  | true =>
    rw [oe] at hb
    rcases hb with hb | hb
    · have := u.isLt
      omega
    · exact absurd (Fin.ext (by omega)) (Fin.succAbove_ne k v)

def rr (p B a : ℕ) : ℕ := if a < p then a else B

theorem rr_val (W : List Bool) (p B a : ℕ) (hW : W.length = p) (hB : p ≤ B) :
    W.getD (rr p B a) false = W.getD a false := by
  unfold rr
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem rr_hr (p B a : ℕ) : rr p B a < p ∨ B ≤ rr p B a := by
  unfold rr
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr le_rfl

theorem rr_in (p B N a : ℕ) (hN : N ≤ B) (h : rr p B a < N) : rr p B a = a := by
  unfold rr at h ⊢
  split_ifs at h ⊢ <;> omega

theorem colmain : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.Represents.Represents A C → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C hF hkind hrep hlist hnc
  obtain ⟨g, hg, hc⟩ := hlist
  obtain ⟨G1, G2, hC⟩ := List.append_of_mem hg
  have hlen : C.gates.length = G1.length + G2.length + 1 := by rw [hC]; simp; omega
  have hx : ∀ (u : Fin n) (v : Fin m), (oneEach u (k.succAbove v)).length = n + m + 1 := by
    intro u v
    simp [oneEach]
    omega
  have hW1 : ∀ (u : Fin n) (v : Fin m),
      (G1.foldl stp (oneEach u (k.succAbove v))).length = n + m + 1 + G1.length := by
    intro u v
    rw [len, hx]
  rcases shape g (hkind g hg) with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, rfl⟩
  · refine fin n m A k C G1 G2 _ (n + m + 1 + C.gates.length) True hC hF hrep (Or.inr le_rfl)
      (by intro h; omega) (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
    intro _ u v
    rw [List.getD_eq_default _ _ (by rw [hW1]; omega), and_ev]
    simp at hc
    rcases hc with h1 | h1
    · subst h1
      rw [ckc]
      rfl
    · subst h1
      rw [ckc]
      simp
  · simp at hc
    rcases hc with h1 | h1
    · subst h1
      refine fin n m A k C G1 G2 _ (rr (n + m + 1 + G1.length) (n + m + 1 + C.gates.length) b) True
        hC hF hrep (rr_hr _ _ _) ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
      · intro h
        rw [rr_in _ _ (n + m + 1) _ (by omega) h]
        simp
      · intro _ u v
        rw [rr_val _ _ _ _ (hW1 u v) (by omega), or_ev, ckc]
        simp
    · subst h1
      refine fin n m A k C G1 G2 _ (rr (n + m + 1 + G1.length) (n + m + 1 + C.gates.length) a) True
        hC hF hrep (rr_hr _ _ _) ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
      · intro h
        rw [rr_in _ _ (n + m + 1) _ (by omega) h]
        simp
      · intro _ u v
        rw [rr_val _ _ _ _ (hW1 u v) (by omega), or_ev, ckc]
        simp
  · simp at hc
    subst hc
    by_cases ho : C.output = n + m + 1 + G1.length
    · exfalso
      obtain ⟨u, u2, v, v2, hne⟩ := hnc
      have ht : ∀ (u : Fin n) (v : Fin m), A u (k.succAbove v) = true := by
        intro u v
        have h0 : (C.gates.foldl stp (oneEach u (k.succAbove v))).getD C.output false =
          A u (k.succAbove v) := hrep u (k.succAbove v)
        rw [← h0, ho, hC, stable G1 G2 _ _ _ (by rw [hx]), not_ev, ckc]
        rfl
      exact hne ((ht u v).trans (ht u2 v2).symm)
    · by_cases hread : ∃ g' ∈ G2, (n + m + 1 + G1.length) ∈ g'.inputs
      · obtain ⟨g', hg', hp'⟩ := hread
        obtain ⟨G2a, G2b, hG2⟩ := List.append_of_mem hg'
        have hC' : C.gates = (G1 ++ ⟨GateOp.not, [n + k.val]⟩ :: G2a) ++ g' :: G2b := by
          rw [hC, hG2]
          simp
        have hl' : (G1 ++ (⟨GateOp.not, [n + k.val]⟩ : Gate) :: G2a).length =
            G1.length + G2a.length + 1 := by
          simp
          omega
        have hlen2 : G2.length = G2a.length + G2b.length + 1 := by rw [hG2]; simp; omega
        have hW2 : ∀ (u : Fin n) (v : Fin m),
            ((G1 ++ (⟨GateOp.not, [n + k.val]⟩ : Gate) :: G2a).foldl stp
              (oneEach u (k.succAbove v))).length = n + m + 1 + (G1.length + G2a.length + 1) := by
          intro u v
          rw [len, hx, hl']
        have hT : ∀ (u : Fin n) (v : Fin m),
            ((G1 ++ (⟨GateOp.not, [n + k.val]⟩ : Gate) :: G2a).foldl stp
              (oneEach u (k.succAbove v))).getD (n + m + 1 + G1.length) false = true := by
          intro u v
          rw [stable G1 G2a _ _ _ (by rw [hx]), not_ev, ckc]
          rfl
        have hg'C : g' ∈ C.gates := by rw [hC']; simp
        rcases shape g' (hkind g' hg'C) with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, rfl⟩
        · simp at hp'
          rcases hp' with h1 | h1
          · subst h1
            refine fin n m A k C _ G2b _
              (rr (n + m + 1 + (G1.length + G2a.length + 1)) (n + m + 1 + C.gates.length) b) True
              hC' hF hrep ?_ ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
            · rw [hl']
              exact rr_hr _ _ _
            · intro h
              rw [rr_in _ _ (n + m + 1) _ (by omega) h]
              simp
            · intro _ u v
              rw [rr_val _ _ _ _ (hW2 u v) (by omega), and_ev, hT]
              simp
          · subst h1
            refine fin n m A k C _ G2b _
              (rr (n + m + 1 + (G1.length + G2a.length + 1)) (n + m + 1 + C.gates.length) a) True
              hC' hF hrep ?_ ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
            · rw [hl']
              exact rr_hr _ _ _
            · intro h
              rw [rr_in _ _ (n + m + 1) _ (by omega) h]
              simp
            · intro _ u v
              rw [rr_val _ _ _ _ (hW2 u v) (by omega), and_ev, hT]
              simp
        · refine fin n m A k C _ G2b _ (n + m + 1 + G1.length) True hC' hF hrep
            (Or.inl (by rw [hl']; omega)) (by intro h; omega) (fun _ _ _ _ _ => trivial)
            (fun _ => trivial) ?_
          intro _ u v
          simp at hp'
          rcases hp' with h1 | h1
          · subst h1
            rw [or_ev, hT]
            simp
          · subst h1
            rw [or_ev, hT]
            simp
        · simp at hp'
          subst hp'
          refine fin n m A k C _ G2b _ (n + m + 1 + C.gates.length) True hC' hF hrep
            (Or.inr le_rfl) (by intro h; omega) (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
          intro _ u v
          rw [not_ev, hT, List.getD_eq_default _ _ (by rw [hW2]; omega)]
          rfl
      · refine fin n m A k C G1 G2 _ (n + m + 1 + C.gates.length) False hC hF hrep (Or.inr le_rfl)
          (by intro h; omega) ?_ ho ?_
        · intro g' hg' i hi hip
          exact hread ⟨g', hg', hip ▸ hi⟩
        · intro hf
          exact hf.elim

theorem main : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin (m + 1) → Bool) (k : Fin (n + 1)) (l : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + (m + 1)) C → 0 < C.size → C.output + 1 = (n + 1 + (m + 1)) + C.size → (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + 1 + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ k.val ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some k.val)) ∨ C.output = k.val) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (n + 1 + l.val) ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some (n + 1 + l.val))) ∨ C.output = (n + 1 + l.val)) → (∃ (u u2 : Fin n) (v v2 : Fin (m + 1)), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) → (∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) (l.succAbove v) ≠ A (k.succAbove u2) (l.succAbove v2)) → ¬ (∀ (u : Fin n) (v : Fin (m + 1)), A (k.succAbove u) v = decide (v = l)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) (l.succAbove v)) C2 ∧ C2.size + 2 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ u.val ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some u.val)) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (k.succAbove u).val ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some (k.succAbove u).val)) ∨ C.output = (k.succAbove u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (n + v.val) ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some (n + v.val))) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (n + 1 + (l.succAbove v).val) ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some (n + 1 + (l.succAbove v).val))) ∨ C.output = (n + 1 + (l.succAbove v).val))) := by
  intro n m A k l C hF hrep hkind hRB hpos hout hread hk hl hnc1 hnc2 hnot
  have hkl : k.val < n + 1 := k.isLt
  have hlist : ∃ g ∈ C.gates, k.val ∈ g.inputs := by
    rcases hk with ⟨g, hg, hgr⟩ | h
    · exact ⟨g, hg, mem_of_GR g _ hgr⟩
    · exfalso
      omega
  obtain ⟨C2, hF2, hS2, hrep2, hsz2, hu2, hv2, hlast⟩ :=
    core n (m + 1) A k C hF hrep hkind hRB hout hread hlist hnc1
  have RRofRd : ∀ i, Rd C i → RR C i := by
    intro i h
    rcases h with ⟨g, hg, hi⟩ | h
    · exact Or.inl ⟨g, hg, GR_of_mem g (hkind g hg) i hi⟩
    · exact Or.inr h
  have RdofRR : ∀ (D : Circuit) (i : ℕ), RR D i → Rd D i := by
    intro D i h
    rcases h with ⟨g, hg, hi⟩ | h
    · exact Or.inl ⟨g, hg, mem_of_GR g i hi⟩
    · exact Or.inr h
  rcases hlast with h2 | hcol
  · obtain ⟨C3, hs3, hF3, hrep3, hu3, hv3⟩ := colstep n m (fun u v => A (k.succAbove u) v) l C2
      (fun u v => hrep2 u (l.succAbove v))
    refine ⟨C3, hF3 hF2, hrep3, by omega, ?_, ?_⟩
    · intro u hu
      exact RRofRd _ (hu2 u (hu3 u (RdofRR C3 _ hu)))
    · intro v hv
      exact RRofRd _ (hv2 (l.succAbove v) (hv3 v (RdofRR C3 _ hv)))
  · have hl2 : RR C2 (n + l.val) := hcol l hl
    rcases hl2 with ⟨g, hg, hgr⟩ | ho
    · obtain ⟨C3, hF3, hrep3, hs3, hu3, hv3⟩ := colmain n m (fun u v => A (k.succAbove u) v) l C2
        hF2 hS2 hrep2 ⟨g, hg, mem_of_GR g _ hgr⟩ hnc2
      refine ⟨C3, hF3, hrep3, by omega, ?_, ?_⟩
      · intro u hu
        exact RRofRd _ (hu2 u (hu3 u (RdofRR C3 _ hu)))
      · intro v hv
        exact RRofRd _ (hv2 (l.succAbove v) (hv3 v (RdofRR C3 _ hv)))
    · exfalso
      apply hnot
      intro u v
      have h0 : (C2.gates.foldl stp (oneEach u v)).getD C2.output false = A (k.succAbove u) v :=
        hrep2 u v
      have hlx : (oneEach u v).length = n + (m + 1) := by simp [oneEach]
      rw [← h0, ho, pre _ _ _ (by rw [hlx]; have := l.isLt; omega)]
      apply bool_iff
      rw [oe, decide_eq_true_iff]
      constructor
      · intro h
        have := u.isLt
        exact Fin.ext (by omega)
      · intro h
        right
        rw [h]

end PEqualNP.Outside.L_meta_24492

theorem PEqualNP.Outside.L_meta_24492 : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin (m + 1) → Bool) (k : Fin (n + 1)) (l : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + (m + 1)) C → 0 < C.size → C.output + 1 = (n + 1 + (m + 1)) + C.size → (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + 1 + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ k.val ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some k.val)) ∨ C.output = k.val) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (n + 1 + l.val) ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some (n + 1 + l.val))) ∨ C.output = (n + 1 + l.val)) → (∃ (u u2 : Fin n) (v v2 : Fin (m + 1)), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) → (∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) (l.succAbove v) ≠ A (k.succAbove u2) (l.succAbove v2)) → ¬ (∀ (u : Fin n) (v : Fin (m + 1)), A (k.succAbove u) v = decide (v = l)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) (l.succAbove v)) C2 ∧ C2.size + 2 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ u.val ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some u.val)) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (k.succAbove u).val ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some (k.succAbove u).val)) ∨ C.output = (k.succAbove u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (n + v.val) ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some (n + v.val))) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (n + 1 + (l.succAbove v).val) ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some (n + 1 + (l.succAbove v).val))) ∨ C.output = (n + 1 + (l.succAbove v).val))) :=
  PEqualNP.Outside.L_meta_24492.main

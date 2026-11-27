import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25487

open PEqualNP.CircuitLowerBounds

-- helpers stp through oe_get are copied from the merged L_meta_25481 by willakone

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem stp_len (W : List Bool) (g : Gate) : (stp W g).length = W.length + 1 := by
  simp [stp]

theorem stp_getD (W : List Bool) (g : Gate) (j : ℕ) : (stp W g).getD j false =
    if j < W.length then W.getD j false else if j = W.length then
      g.op.eval (g.inputs.map fun i => W.getD i false) else false := getD_snoc _ _ _

theorem flen : ∀ (gs : List Gate) (W : List Bool), (gs.foldl stp W).length = W.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro W; simp
  | cons g t ih => intro W; rw [List.foldl_cons, ih, stp_len]; simp; omega

theorem pre : ∀ (gs : List Gate) (W : List Bool) (j : ℕ), j < W.length →
    (gs.foldl stp W).getD j false = W.getD j false := by
  intro gs
  induction gs with
  | nil => intro W j _; rfl
  | cons g t ih =>
    intro W j hj
    rw [List.foldl_cons, ih _ _ (by rw [stp_len]; omega), stp_getD, if_pos hj]

theorem vgate : ∀ (gs : List Gate) (W : List Bool) (r : ℕ) (h : r < gs.length),
    (gs.foldl stp W).getD (W.length + r) false = gs[r].op.eval (gs[r].inputs.map fun a =>
      if a < W.length + r then (gs.foldl stp W).getD a false else false) := by
  intro gs
  induction gs with
  | nil => intro W r h; simp at h
  | cons g t ih =>
    intro W r h
    cases r with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [pre t (stp W g) W.length (by rw [stp_len]; omega), stp_getD, if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro a _
      split_ifs with ha
      · rw [pre t _ a (by rw [stp_len]; omega), stp_getD, if_pos ha]
      · exact getD_ge W a (by omega)
    | succ r =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have := ih (stp W g) r (by simp at h; omega)
      rw [stp_len] at this
      rw [show W.length + (r + 1) = W.length + 1 + r by omega]
      exact this

theorem allP (P : Bool → Bool → Prop) (ht : P true true)
    (hand : ∀ a b c d : Bool, P a b → P c d → P (a && c) (b && d)) :
    ∀ (l : List ℕ) (f1 f2 : ℕ → Bool), (∀ a ∈ l, P (f1 a) (f2 a)) →
      P ((l.map f1).all id) ((l.map f2).all id) := by
  intro l
  induction l with
  | nil => intro f1 f2 _; simpa using ht
  | cons x l ih =>
    intro f1 f2 h
    simp only [List.map_cons, List.all_cons, id]
    exact hand _ _ _ _ (h x (by simp)) (by simpa using ih f1 f2 (fun a ha => h a (by simp [ha])))

theorem anyP (P : Bool → Bool → Prop) (hf : P false false)
    (hor : ∀ a b c d : Bool, P a b → P c d → P (a || c) (b || d)) :
    ∀ (l : List ℕ) (f1 f2 : ℕ → Bool), (∀ a ∈ l, P (f1 a) (f2 a)) →
      P ((l.map f1).any id) ((l.map f2).any id) := by
  intro l
  induction l with
  | nil => intro f1 f2 _; simpa using hf
  | cons x l ih =>
    intro f1 f2 h
    simp only [List.map_cons, List.any_cons, id]
    exact hor _ _ _ _ (h x (by simp)) (by simpa using ih f1 f2 (fun a ha => h a (by simp [ha])))


theorem oe_len {n m : ℕ} (u : Fin n) (v : Fin m) : (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]


theorem p1and : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a && c) = true → (b && d) = true := by decide

theorem p1or : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a || c) = true → (b || d) = true := by decide


theorem oe_get {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_ofFn, h, dite_true, Option.getD_some, Fin.ext_iff]
    apply decide_eq_decide.2
    constructor <;> intro hh <;> omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp only [h2, dite_true, Option.getD_some, Fin.ext_iff]
      apply decide_eq_decide.2
      constructor <;> intro hh <;> omega
    · simp only [h2, dite_false, Option.getD_none]
      symm
      apply decide_eq_false
      omega


theorem col_get {n m : ℕ} (c : Fin m) (i : ℕ) :
    (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).getD i false =
      decide (i = n + c.val) := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_replicate, h, if_true, Option.getD_some]
    symm; apply decide_eq_false; omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp only [h2, dite_true, Option.getD_some, Fin.ext_iff]
      apply decide_eq_decide.2
      constructor <;> intro hh <;> omega
    · simp only [h2, dite_false, Option.getD_none]
      symm
      apply decide_eq_false
      omega

theorem col_len {n m : ℕ} (c : Fin m) :
    (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).length = n + m := by
  simp

theorem agree (gs : List Gate) (N : ℕ) (X Y : List Bool) (hX : X.length = N) (hY : Y.length = N)
    (T : ℕ → Prop) (z : ℕ)
    (hz : (gs.foldl stp X).getD z false = (gs.foldl stp Y).getD z false)
    (hin : ∀ j < N, ¬ T j → X.getD j false = Y.getD j false)
    (hg : ∀ r (hr : r < gs.length), N + r ≠ z → ¬ T (N + r) → ∀ a ∈ (gs[r]).inputs, a ≠ z → ¬ T a) :
    ∀ j, ¬ T j → (gs.foldl stp X).getD j false = (gs.foldl stp Y).getD j false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hT
    by_cases hjz : j = z
    · subst hjz; exact hz
    rcases lt_or_ge j N with h1 | h1
    · rw [pre _ _ _ (by omega), pre _ _ _ (by omega)]; exact hin j h1 hT
    rcases lt_or_ge (j - N) gs.length with h2 | h2
    · obtain ⟨r, rfl⟩ : ∃ r, j = N + r := ⟨j - N, by omega⟩
      have h2' : r < gs.length := by omega
      have e1 := vgate gs X r h2'
      have e2 := vgate gs Y r h2'
      rw [hX] at e1
      rw [hY] at e2
      rw [e1, e2]
      congr 1
      apply List.map_congr_left
      intro a ha
      split_ifs with hlt
      · by_cases haz : a = z
        · subst haz; exact hz
        · exact ih a hlt (hg r h2' hjz hT a ha haz)
      · rfl
    · rw [getD_ge _ _ (by rw [flen, hX]; omega), getD_ge _ _ (by rw [flen, hY]; omega)]

theorem mono (gs : List Gate) (hC : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (N : ℕ) (X Y : List Bool) (hX : X.length = N) (hY : Y.length = N)
    (hin : ∀ j < N, X.getD j false = true → Y.getD j false = true) :
    ∀ j, (gs.foldl stp X).getD j false = true → (gs.foldl stp Y).getD j false = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hT
    rcases lt_or_ge j N with h1 | h1
    · rw [pre _ _ _ (by omega)] at hT ⊢
      exact hin j h1 hT
    rcases lt_or_ge (j - N) gs.length with h2 | h2
    · obtain ⟨r, rfl⟩ : ∃ r, j = N + r := ⟨j - N, by omega⟩
      have h2' : r < gs.length := by omega
      have e1 := vgate gs X r h2'
      have e2 := vgate gs Y r h2'
      rw [hX] at e1
      rw [hY] at e2
      rw [e1] at hT
      rw [e2]
      have key : ∀ a ∈ (gs[r]).inputs, (fun p q : Bool => p = true → q = true)
          (if a < N + r then (gs.foldl stp X).getD a false else false)
          (if a < N + r then (gs.foldl stp Y).getD a false else false) := by
        intro a _
        split_ifs with hlt
        · exact ih a hlt
        · exact fun h => h
      have hop := (hC _ (List.getElem_mem h2')).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with e | e
      · rw [e] at hT ⊢
        simp only [GateOp.eval] at hT ⊢
        exact allP (fun p q : Bool => p = true → q = true) (fun h => h) p1and _ _ _ key hT
      · rw [e] at hT ⊢
        simp only [GateOp.eval] at hT ⊢
        exact anyP (fun p q : Bool => p = true → q = true) (fun h => h) p1or _ _ _ key hT
    · rw [getD_ge _ _ (by rw [flen, hX]; omega)] at hT
      exact absurd hT (by simp)

theorem andfalse (g : Gate) (f : ℕ → Bool) (q : ℕ) (h1 : g.op = GateOp.and) (h2 : q ∈ g.inputs)
    (h3 : f q = false) : g.op.eval (g.inputs.map f) = false := by
  rw [h1]
  simp only [GateOp.eval]
  rw [List.all_eq_false]
  exact ⟨f q, List.mem_map_of_mem h2, by simp [h3]⟩

end PEqualNP.Outside.L_meta_25487

open PEqualNP.Outside.L_meta_25487 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25487 :
    ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n)
    (j : Fin C.gates.length) (q : ℕ),
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let g := n + m + j.val
  let edge := fun source target : ℕ => ∃ idx : Fin C.gates.length,
    target = n + m + idx.val ∧ source ∈ (gate idx.val).inputs
  let cuts := fun (z start : ℕ) =>
    ¬ (start ≠ z ∧ C.output ≠ z ∧ Relation.ReflTransGen
      (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧ edge prev next) start C.output)
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C → u ≠ v →
  (gate j.val).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  q ∈ (gate j.val).inputs →
  cuts g u.val → cuts q v.val → ¬ Relation.ReflTransGen edge u.val q →
  ∀ c : Fin m, (∃ w : Fin n, G w c = false) →
    let col := List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))
    let value := (C.wires col).getD q false
    (G u c = true → value = true) ∧ (G v c = true → value = false) := by
  intro n m G C u v j q gate g edge cuts hM _ hrep huv hand hq hcg hcq hnp c hcol col value
  have hu1 := u.2
  have hv1 := v.2
  have hc1 := c.2
  have hj1 := j.2
  have hga : ∀ r (hr : r < C.gates.length), gate r = C.gates[r] := by
    intro r hr
    show PEqualNP.MetaComplexity.NestedCover.gateAt C r = C.gates[r]
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hr]
  have hev : ∀ x, C.eval x = (C.gates.foldl stp x).getD C.output false := fun x => rfl
  have hval : value = (C.gates.foldl stp col).getD q false := rfl
  have hcl : col.length = n + m := col_len c
  have hcg2 : ∀ x, x < n + m → (C.gates.foldl stp col).getD x false = decide (x = n + c.val) := by
    intro x hx
    rw [pre _ _ _ (by rw [hcl]; exact hx)]
    exact col_get c x
  obtain ⟨w0, hw0⟩ := hcol
  have hZ : (C.gates.foldl stp (PEqualNP.Represents.oneEach w0 c)).getD C.output false = false := by
    rw [← hev, hrep w0 c, hw0]
  have hmono : ∀ (x : Fin n), ∀ i, (C.gates.foldl stp col).getD i false = true →
      (C.gates.foldl stp (PEqualNP.Represents.oneEach x c)).getD i false = true := by
    intro x
    apply mono C.gates hM (n + m) col _ hcl (oe_len x c)
    intro i _ h
    rw [col_get] at h
    rw [oe_get]
    simp only [decide_eq_true_eq] at h ⊢
    exact Or.inr h
  have hcolout : (C.gates.foldl stp col).getD C.output false = false := by
    cases h : (C.gates.foldl stp col).getD C.output false with
    | false => rfl
    | true => rw [hmono w0 _ h] at hZ; exact absurd hZ (by simp)
  have hand' : (C.gates[j.val]).op = GateOp.and := by rw [← hga j.val j.2]; exact hand
  have hq' : q ∈ (C.gates[j.val]).inputs := by rw [← hga j.val j.2]; exact hq
  have hgate : ∀ (x : List Bool), x.length = n + m →
      (C.gates.foldl stp x).getD q false = false → (C.gates.foldl stp x).getD g false = false := by
    intro x hx hqx
    have e := vgate C.gates x j.val j.2
    rw [hx] at e
    show (C.gates.foldl stp x).getD (n + m + j.val) false = false
    rw [e]
    apply andfalse _ _ q hand' hq'
    split_ifs
    · exact hqx
    · rfl
  have hedge : ∀ r (hr : r < C.gates.length) a, a ∈ (C.gates[r]).inputs → edge a (n + m + r) :=
    fun r hr a ha => ⟨⟨r, hr⟩, rfl, by rw [hga r hr]; exact ha⟩
  constructor
  · intro hGu
    have hqa := agree C.gates (n + m) (PEqualNP.Represents.oneEach u c) col (oe_len u c) hcl
      (fun j => Relation.ReflTransGen edge u.val j) (n + m + C.gates.length)
      (by rw [getD_ge _ _ (by rw [flen, oe_len]), getD_ge _ _ (by rw [flen, hcl])])
      (by
        intro i hi hT
        have : i ≠ u.val := by intro e; exact hT (by rw [e])
        rw [oe_get, col_get]
        apply decide_eq_decide.2
        constructor
        · rintro (e | e)
          · exact absurd e this
          · exact e
        · exact Or.inr)
      (by
        intro r hr _ hT a ha _ hTa
        exact hT (Relation.ReflTransGen.tail hTa (hedge r hr a ha)))
      q hnp
    rw [hval]
    by_contra hv
    have hv' : (C.gates.foldl stp col).getD q false = false := by simpa using hv
    have hgX := hgate _ (oe_len u c) (hqa.trans hv')
    have hgY := hgate _ hcl hv'
    have hX : (C.gates.foldl stp (PEqualNP.Represents.oneEach u c)).getD C.output false = true := by
      rw [← hev, hrep u c, hGu]
    by_cases hog : C.output = g
    · rw [hog, hgX] at hX; exact absurd hX (by simp)
    have hug : u.val ≠ g := by show u.val ≠ n + m + j.val; omega
    have hnr : ¬ Relation.ReflTransGen (fun prev next : ℕ => prev ≠ g ∧ next ≠ g ∧ edge prev next)
        u.val C.output := fun h => hcg ⟨hug, hog, h⟩
    have hoa := agree C.gates (n + m) (PEqualNP.Represents.oneEach u c) col (oe_len u c) hcl
      (fun j => Relation.ReflTransGen (fun prev next : ℕ => prev ≠ g ∧ next ≠ g ∧ edge prev next) u.val j) g
      (hgX.trans hgY.symm)
      (by
        intro i hi hT
        have : i ≠ u.val := by intro e; exact hT (by rw [e])
        rw [oe_get, col_get]
        apply decide_eq_decide.2
        constructor
        · rintro (e | e)
          · exact absurd e this
          · exact e
        · exact Or.inr)
      (by
        intro r hr hrz hT a ha haz hTa
        exact hT (Relation.ReflTransGen.tail hTa ⟨haz, hrz, hedge r hr a ha⟩))
      C.output hnr
    rw [hoa, hcolout] at hX
    exact absurd hX (by simp)
  · intro hGv
    rw [hval]
    by_contra hv
    have hv' : (C.gates.foldl stp col).getD q false = true := by simpa using hv
    by_cases hqv : q = v.val
    · rw [hqv, hcg2 _ (by omega)] at hv'
      simp only [decide_eq_true_eq] at hv'
      omega
    by_cases hoq : C.output = q
    · rw [← hoq, hcolout] at hv'; exact absurd hv' (by simp)
    have hnr : ¬ Relation.ReflTransGen (fun prev next : ℕ => prev ≠ q ∧ next ≠ q ∧ edge prev next)
        v.val C.output := fun h => hcq ⟨fun e => hqv e.symm, hoq, h⟩
    have hXq := hmono v q hv'
    have hoa := agree C.gates (n + m) (PEqualNP.Represents.oneEach v c) col (oe_len v c) hcl
      (fun j => Relation.ReflTransGen (fun prev next : ℕ => prev ≠ q ∧ next ≠ q ∧ edge prev next) v.val j) q
      (hXq.trans hv'.symm)
      (by
        intro i hi hT
        have : i ≠ v.val := by intro e; exact hT (by rw [e])
        rw [oe_get, col_get]
        apply decide_eq_decide.2
        constructor
        · rintro (e | e)
          · exact absurd e this
          · exact e
        · exact Or.inr)
      (by
        intro r hr hrz hT a ha haz hTa
        exact hT (Relation.ReflTransGen.tail hTa ⟨haz, hrz, hedge r hr a ha⟩))
      C.output hnr
    have hX : (C.gates.foldl stp (PEqualNP.Represents.oneEach v c)).getD C.output false = true := by
      rw [← hev, hrep v c, hGv]
    rw [hoa, hcolout] at hX
    exact absurd hX (by simp)

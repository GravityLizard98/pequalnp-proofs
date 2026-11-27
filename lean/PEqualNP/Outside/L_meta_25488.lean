import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25488

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem mono (N : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ w : ℕ, val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < N
    · rw [val_input hx hw] at hv
      rw [val_input hy hw]
      exact hxy _ hv
    · by_cases hlen : N + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate hx hk] at hv
        rw [val_gate hy hk]
        have hop := hAO _ (gateAt_mem hk)
        rcases hop with hop | hop
        · rw [hop] at hv ⊢
          rw [eval_and_iff] at hv ⊢
          intro i hi
          have := hv i hi
          by_cases hi2 : i < N + k
          · rw [if_pos hi2] at this ⊢
            exact ih i hi2 this
          · rw [if_neg hi2] at this; cases this
        · rw [hop] at hv ⊢
          rw [eval_or_iff] at hv ⊢
          obtain ⟨i, hi, h⟩ := hv
          refine ⟨i, hi, ?_⟩
          by_cases hi2 : i < N + k
          · rw [if_pos hi2] at h ⊢
            exact ih i hi2 h
          · rw [if_neg hi2] at h; cases h

theorem getD_append_ofFn {n m : ℕ} (f : Fin n → Bool) (g : Fin m → Bool) (i : ℕ) :
    (List.ofFn f ++ List.ofFn g).getD i false =
      if h : i < n then f ⟨i, h⟩ else if h2 : i - n < m then g ⟨i - n, h2⟩ else false := by
  by_cases h : i < n
  · rw [dif_pos h, getD_app_lt _ _ _ (by simpa using h), ofFn_getD _ _ h]
  · rw [dif_neg h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    by_cases h2 : i - n < m
    · rw [dif_pos h2]; simp [h2]
    · rw [dif_neg h2]; simp [List.getElem?_eq_none (by simp; omega : (List.ofFn g).length ≤ i - n)]

theorem getD_rep_ofFn {n m : ℕ} (g : Fin m → Bool) (i : ℕ) :
    (List.replicate n false ++ List.ofFn g).getD i false =
      if i < n then false else if h2 : i - n < m then g ⟨i - n, h2⟩ else false := by
  by_cases h : i < n
  · rw [if_pos h, getD_app_lt _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [if_neg h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate]
    by_cases h2 : i - n < m
    · rw [dif_pos h2]; simp [h2]
    · rw [dif_neg h2]; simp [List.getElem?_eq_none (by simp; omega : (List.ofFn g).length ≤ i - n)]

theorem getD_ofFn_rep {n m : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f ++ List.replicate m false).getD i false =
      if h : i < n then f ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [dif_pos h, getD_app_lt _ _ _ (by simpa using h), ofFn_getD _ _ h]
  · rw [dif_neg h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    by_cases h2 : i - n < m
    · simp [h2]
    · simp [List.getElem?_eq_none (by simp; omega : (List.replicate m false).length ≤ i - n)]


theorem only_reader (C : Circuit) (w k0 : ℕ)
    (h1 : readsIn C (Finset.range C.gates.length) w = 1) (hk0 : k0 < C.gates.length)
    (hmem : w ∈ (gateAt C k0).inputs) :
    (gateAt C k0).inputs.count w = 1 ∧
      ∀ k < C.gates.length, k ≠ k0 → w ∉ (gateAt C k).inputs := by
  unfold readsIn at h1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hk0)] at h1
  have hpos : 0 < (gateAt C k0).inputs.count w := List.count_pos_iff.mpr hmem
  have hrest : ∑ x ∈ (Finset.range C.gates.length).erase k0, (gateAt C x).inputs.count w = 0 := by
    omega
  refine ⟨by omega, ?_⟩
  intro k hk hne hw
  have := (Finset.sum_eq_zero_iff.mp hrest) k (Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr hk⟩)
  have : 0 < (gateAt C k).inputs.count w := List.count_pos_iff.mpr hw
  omega

theorem val_bin {N : ℕ} {C : Circuit} (hRB : ReadsBack N C) {x : List Bool} (hx : x.length = N)
    {k : ℕ} (hk : k < C.gates.length) {a b : ℕ}
    (hin : (gateAt C k).inputs = [a, b] ∨ (gateAt C k).inputs = [b, a]) :
    val C x (N + k) = (gateAt C k).op.eval [val C x a, val C x b] ∨
      val C x (N + k) = (gateAt C k).op.eval [val C x b, val C x a] := by
  have hrb := hRB k hk
  rcases hin with e | e
  · left
    rw [e] at hrb
    rw [val_gate hx hk, e]
    simp [hrb a (by simp), hrb b (by simp)]
  · right
    rw [e] at hrb
    rw [val_gate hx hk, e]
    simp [hrb a (by simp), hrb b (by simp)]

theorem val_or_bin {N : ℕ} {C : Circuit} (hRB : ReadsBack N C) {x : List Bool} (hx : x.length = N)
    {k : ℕ} (hk : k < C.gates.length) {a b : ℕ} (hop : (gateAt C k).op = GateOp.or)
    (hin : (gateAt C k).inputs = [a, b] ∨ (gateAt C k).inputs = [b, a]) :
    val C x (N + k) = (val C x a || val C x b) := by
  rcases val_bin hRB hx hk hin with e | e <;> rw [e, hop, eval_or2]
  rw [Bool.or_comm]

theorem val_and_bin {N : ℕ} {C : Circuit} (hRB : ReadsBack N C) {x : List Bool} (hx : x.length = N)
    {k : ℕ} (hk : k < C.gates.length) {a b : ℕ} (hop : (gateAt C k).op = GateOp.and)
    (hin : (gateAt C k).inputs = [a, b] ∨ (gateAt C k).inputs = [b, a]) :
    val C x (N + k) = (val C x a && val C x b) := by
  rcases val_bin hRB hx hk hin with e | e <;> rw [e, hop, eval_and2]
  rw [Bool.and_comm]

theorem agree {N : ℕ} {C : Circuit} (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (D : ℕ → Prop)
    (hin : ∀ w < N, ¬ D w → x.getD w false = y.getD w false)
    (hg : ∀ k < C.gates.length, ¬ D (N + k) →
      (∀ i < N + k, ¬ D i → val C x i = val C y i) → val C x (N + k) = val C y (N + k)) :
    ∀ w, ¬ D w → val C x w = val C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < N
    · rw [val_input hx h1, val_input hy h1]; exact hin w h1 hw
    · by_cases h2 : N + C.gates.length ≤ w
      · rw [val_ge hx h2, val_ge hy h2]
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        exact hg k (by omega) hw (fun i hi hD => ih i hi hD)

theorem gate_same {N : ℕ} {C : Circuit} (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    {k : ℕ} (hk : k < C.gates.length) (D : ℕ → Prop) (hnd : ∀ i ∈ (gateAt C k).inputs, ¬ D i)
    (ih : ∀ i < N + k, ¬ D i → val C x i = val C y i) : val C x (N + k) = val C y (N + k) := by
  rw [val_gate hx hk, val_gate hy hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases h : i < N + k
  · rw [if_pos h, if_pos h]; exact ih i h (hnd i hi)
  · rw [if_neg h, if_neg h]

end PEqualNP.Outside.L_meta_25488

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_25488 in
theorem PEqualNP.Outside.L_meta_25488 :
    ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n) (c : Fin m)
    (i j : Fin C.gates.length) (p q : ℕ),
  let g := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let wire := fun idx : Fin C.gates.length => n + m + idx.val
  let isOr := fun (z : Fin C.gates.length) (a b : ℕ) =>
    (g z.val).op = .or ∧ ((g z.val).inputs = [a, b] ∨ (g z.val).inputs = [b, a])
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  u ≠ v → i ≠ j → isOr i u.val p → isOr j v.val q →
  PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) u.val = 1 →
  C.output ∉ [u.val, wire i] → G u c = true → G v c = false →
  (C.wires (PEqualNP.Represents.oneEach v c)).getD (wire i) false = false ∧
    ∀ t : Fin C.gates.length, isOr t (wire i) (wire j) →
      ∃ h : Fin C.gates.length, h ≠ t ∧ wire i ∈ (g h.val).inputs := by
  intro n m G C u v c i j p q g wire isOr hM hRB hR huv hij hI hJ hru hout hGu hGv
  have hAO : PEqualNP.EdgeOwnership.AndOrOnly C := by
    intro g hg
    have h1 := (hM g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  let xv := PEqualNP.Represents.oneEach v c
  let xu := PEqualNP.Represents.oneEach u c
  let xuv := List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++
    List.ofFn (fun b : Fin m => decide (b = c))
  have lv : xv.length = n + m := by simp [xv, PEqualNP.Represents.oneEach]
  have lu : xu.length = n + m := by simp [xu, PEqualNP.Represents.oneEach]
  have luv : xuv.length = n + m := by simp [xuv]
  have hle : ∀ w, xu.getD w false = true → xuv.getD w false = true := by
    intro w h
    simp only [xu, xuv, PEqualNP.Represents.oneEach] at h ⊢
    rw [getD_append_ofFn] at h ⊢
    by_cases h1 : w < n
    · rw [dif_pos h1] at h ⊢
      simp only [decide_eq_true_eq] at h
      simp [h]
    · rw [dif_neg h1] at h ⊢; exact h
  have hdiff : ∀ w, w < n + m → w ≠ u.val → xuv.getD w false = xv.getD w false := by
    intro w _ hw
    simp only [xv, xuv, PEqualNP.Represents.oneEach]
    rw [getD_append_ofFn, getD_append_ofFn]
    by_cases h1 : w < n
    · rw [dif_pos h1, dif_pos h1]
      have : ¬ ((⟨w, h1⟩ : Fin n) = u) := fun e => hw (congrArg Fin.val e)
      simp [this]
    · rw [dif_neg h1, dif_neg h1]
  have huvout : val C xuv C.output = true := by
    apply mono (n + m) C hAO xu xuv lu luv hle
    have h2 := hR u c
    rw [hGu] at h2
    exact h2
  have hvout : val C xv C.output = false := by
    have h2 := hR v c
    rw [hGv] at h2
    exact h2
  have hiL := i.isLt
  have hjL := j.isLt
  obtain ⟨hIop, hIin⟩ := hI
  obtain ⟨hJop, hJin⟩ := hJ
  have memI : u.val ∈ (gateAt C i.val).inputs := by
    rcases hIin with e | e <;> rw [e] <;> simp
  obtain ⟨_, ou⟩ := only_reader C u.val i.val hru hiL memI
  have hout' : C.output ≠ u.val ∧ C.output ≠ wire i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
    exact hout
  have hu_n : u.val < n := u.isLt
  have hv_n : v.val < n := v.isLt
  have xuv_u : val C xuv u.val = true := by
    rw [val_input luv (by omega)]
    simp only [xuv]
    rw [getD_append_ofFn, dif_pos hu_n]
    simp
  have xv_v : val C xv v.val = true := by
    rw [val_input lv (by omega)]
    simp only [xv, PEqualNP.Represents.oneEach]
    rw [getD_append_ofFn, dif_pos hv_n]
    simp
  have hIuv : val C xuv (wire i) = true := by
    show val C xuv (n + m + i.val) = true
    rw [val_or_bin hRB luv hiL hIop hIin, xuv_u]
    simp
  have partA : val C xv (wire i) = false := by
    by_contra hIt
    have hIt' : val C xv (wire i) = true := by simpa using hIt
    let D : ℕ → Prop := fun w => w = u.val
    have key := agree xuv xv luv lv D
      (fun w hw hD => hdiff w hw hD)
      (by
        intro k hk hD ih
        by_cases hki : k = i.val
        · subst hki
          exact hIuv.trans hIt'.symm
        · apply gate_same _ _ luv lv hk D _ ih
          intro w hw hD
          subst hD
          exact ou k hk hki hw)
      C.output hout'.1
    rw [huvout, hvout] at key
    cases key
  refine ⟨partA, ?_⟩
  intro t ⟨hTop, hTin⟩
  by_contra hno
  push_neg at hno
  have htL := t.isLt
  have memT : wire i ∈ (gateAt C t.val).inputs := by
    rcases hTin with e | e <;> rw [e] <;> simp
  have memTJ : wire j ∈ (gateAt C t.val).inputs := by
    rcases hTin with e | e <;> rw [e] <;> simp
  have hJlt : wire j < n + m + t.val := hRB t.val htL _ memTJ
  have hIlt : wire i < n + m + t.val := hRB t.val htL _ memT
  have hJv : val C xv (wire j) = true := by
    show val C xv (n + m + j.val) = true
    rw [val_or_bin hRB lv hjL hJop hJin, xv_v]
    simp
  let D : ℕ → Prop := fun w => w = u.val ∨ w = wire i
  have hJD : ¬ D (wire j) := by
    rintro (e | e)
    · simp [wire] at e; omega
    · simp [wire] at e; exact hij (Fin.ext e.symm)
  have key := agree xuv xv luv lv D
    (fun w hw hD => hdiff w hw (fun e => hD (Or.inl e)))
    (by
      intro k hk hD ih
      by_cases hkt : k = t.val
      · subst hkt
        rw [val_or_bin hRB luv htL hTop hTin, val_or_bin hRB lv htL hTop hTin,
          ih _ hJlt hJD, hJv]
        simp
      · apply gate_same _ _ luv lv hk D _ ih
        intro w hw hD'
        rcases hD' with e | e
        · subst e
          have hki : k ≠ i.val := by
            intro e; apply hD; right; simp [wire, e]
          exact ou k hk hki hw
        · subst e
          have hkt' : (⟨k, hk⟩ : Fin C.gates.length) ≠ t := fun e => hkt (congrArg Fin.val e)
          exact hno ⟨k, hk⟩ hkt' hw)
    C.output (by rintro (e | e); exact hout'.1 e; exact hout'.2 e)
  rw [huvout, hvout] at key
  cases key

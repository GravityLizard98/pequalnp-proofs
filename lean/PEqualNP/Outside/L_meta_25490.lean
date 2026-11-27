import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25490

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

end PEqualNP.Outside.L_meta_25490

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_25490 in
theorem PEqualNP.Outside.L_meta_25490 :
    ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (r : Fin n → Fin C.gates.length) (s : Fin n → ℕ) (v : Fin n),
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let wire := fun idx : Fin C.gates.length => n + m + idx.val
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length)
  let col := fun label : Fin m =>
    List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = label))
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  (∀ u : Fin n, C.output ≠ u.val) →
  (∀ c, ∃ u, G u c = false) →
  (∀ u w, u ≠ w → ∃ c, G u c = true ∧ G w c = false) →
  (∀ u : Fin n, reads u.val = 1 ∧ (gate (r u).val).op = .or ∧
    ((gate (r u).val).inputs = [u.val, s u] ∨
      (gate (r u).val).inputs = [s u, u.val])) →
  2 ≤ (Finset.univ.filter (fun c => G v c = false)).card →
  (∀ c, G v c = false → (C.wires (col c)).getD (s v) false = true) →
  ∃ j : Fin C.gates.length, s v = wire j ∧
    ∀ w, j ≠ r w ∧ wire (r w) ∉ (gate j.val).inputs := by
  intro n m G C r s v gate wire reads col hM hRB hR hout hzero hinc hrow hcard hsv
  have hAO : PEqualNP.EdgeOwnership.AndOrOnly C := by
    intro g hg
    have h1 := (hM g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  have lo : ∀ (a : Fin n) (b : Fin m), (PEqualNP.Represents.oneEach a b).length = n + m := by
    intro a b; simp [PEqualNP.Represents.oneEach]
  have lc : ∀ b : Fin m, (col b).length = n + m := by intro b; simp [col]
  let X := fun (a a' : Fin n) (b : Fin m) =>
    List.ofFn (fun r : Fin n => decide (r = a) || decide (r = a')) ++
      List.ofFn (fun b' : Fin m => decide (b' = b))
  have lX : ∀ a a' b, (X a a' b).length = n + m := by intro a a' b; simp [X]
  have ecol : ∀ (b : Fin m) w, (col b).getD w false = if w < n then false else
      if h2 : w - n < m then decide ((⟨w - n, h2⟩ : Fin m) = b) else false := by
    intro b w; exact getD_rep_ofFn _ w
  have hleC : ∀ (a : Fin n) (b : Fin m) w, (col b).getD w false = true →
      (PEqualNP.Represents.oneEach a b).getD w false = true := by
    intro a b w h
    rw [ecol] at h
    unfold PEqualNP.Represents.oneEach
    rw [getD_append_ofFn]
    by_cases h1 : w < n
    · rw [if_pos h1] at h; cases h
    · rw [if_neg h1] at h; rw [dif_neg h1]; exact h
  have hdiffC : ∀ (a : Fin n) (b : Fin m) w, w < n + m → w ≠ a.val →
      (PEqualNP.Represents.oneEach a b).getD w false = (col b).getD w false := by
    intro a b w _ hw
    rw [ecol]
    unfold PEqualNP.Represents.oneEach
    rw [getD_append_ofFn]
    by_cases h1 : w < n
    · rw [dif_pos h1, if_pos h1]
      simp only [decide_eq_false_iff_not]
      intro e; exact hw (congrArg Fin.val e)
    · rw [dif_neg h1, if_neg h1]
  have hleX : ∀ (a a' : Fin n) (b : Fin m) w,
      (PEqualNP.Represents.oneEach a' b).getD w false = true → (X a a' b).getD w false = true := by
    intro a a' b w h
    unfold PEqualNP.Represents.oneEach at h
    simp only [X]
    rw [getD_append_ofFn] at h ⊢
    by_cases h1 : w < n
    · rw [dif_pos h1] at h ⊢
      simp only [decide_eq_true_eq] at h
      simp [h]
    · rw [dif_neg h1] at h ⊢; exact h
  have hdiffX : ∀ (a a' : Fin n) (b : Fin m) w, w < n + m → w ≠ a'.val →
      (X a a' b).getD w false = (PEqualNP.Represents.oneEach a b).getD w false := by
    intro a a' b w _ hw
    unfold PEqualNP.Represents.oneEach
    simp only [X]
    rw [getD_append_ofFn, getD_append_ofFn]
    by_cases h1 : w < n
    · rw [dif_pos h1, dif_pos h1]
      have : ¬ ((⟨w, h1⟩ : Fin n) = a') := fun e => hw (congrArg Fin.val e)
      simp [this]
    · rw [dif_neg h1, dif_neg h1]
  have colout : ∀ b : Fin m, val C (col b) C.output = false := by
    intro b
    obtain ⟨z, hz⟩ := hzero b
    by_contra hc
    have h1 := mono (n + m) C hAO (col b) _ (lc b) (lo z b) (hleC z b) C.output (by simpa using hc)
    have h2 := hR z b
    rw [hz] at h2
    have : val C (PEqualNP.Represents.oneEach z b) C.output = false := h2
    rw [this] at h1; cases h1
  have rowL : ∀ a : Fin n, (r a).val < C.gates.length := fun a => (r a).isLt
  have memR : ∀ a : Fin n, a.val ∈ (gateAt C (r a).val).inputs := by
    intro a
    rcases (hrow a).2.2 with e | e <;> rw [show gate = gateAt C from rfl] at e <;> rw [e] <;> simp
  have memS : ∀ a : Fin n, s a ∈ (gateAt C (r a).val).inputs := by
    intro a
    rcases (hrow a).2.2 with e | e <;> rw [show gate = gateAt C from rfl] at e <;> rw [e] <;> simp
  have onlyR : ∀ a : Fin n, ∀ k < C.gates.length, k ≠ (r a).val → a.val ∉ (gateAt C k).inputs :=
    fun a => (only_reader C a.val (r a).val (hrow a).1 (rowL a) (memR a)).2
  have valR : ∀ (a : Fin n) (x : List Bool), x.length = n + m →
      val C x (wire (r a)) = (val C x a.val || val C x (s a)) := by
    intro a x hx
    exact val_or_bin hRB hx (rowL a) (hrow a).2.1 (hrow a).2.2
  have FLIP : ∀ (w : Fin n) (c : Fin m), val C (col c) (wire (r w)) = true → G w c = false := by
    intro w c hO
    by_contra hG
    have hG' : G w c = true := by simpa using hG
    let D : ℕ → Prop := fun z => z = w.val
    have key := agree (PEqualNP.Represents.oneEach w c) (col c) (lo w c) (lc c) D
      (fun z hz hD => hdiffC w c z hz hD)
      (by
        intro k hk hD ih
        by_cases hkr : k = (r w).val
        · subst hkr
          have e1 : val C (PEqualNP.Represents.oneEach w c) (wire (r w)) = true := by
            rw [valR w _ (lo w c), val_input (lo w c) (by have := w.isLt; omega)]
            unfold PEqualNP.Represents.oneEach
            rw [getD_append_ofFn, dif_pos w.isLt]
            simp
          exact e1.trans hO.symm
        · apply gate_same _ _ (lo w c) (lc c) hk D _ ih
          intro z hz hD
          subst hD
          exact onlyR w k hk hkr hz)
      C.output (hout w)
    have h2 := hR w c
    rw [hG'] at h2
    have : val C (PEqualNP.Represents.oneEach w c) C.output = true := h2
    rw [key, colout] at this
    cases this
  have XL : ∀ (a w : Fin n) (c : Fin m), a ≠ w → G a c = true →
      val C (PEqualNP.Represents.oneEach w c) (wire (r a)) = true → G w c = true := by
    intro a w c haw hG hO
    let D : ℕ → Prop := fun z => z = a.val
    have key := agree (X w a c) (PEqualNP.Represents.oneEach w c) (lX w a c) (lo w c) D
      (fun z hz hD => hdiffX w a c z hz hD)
      (by
        intro k hk hD ih
        by_cases hkr : k = (r a).val
        · subst hkr
          have e1 : val C (X w a c) (wire (r a)) = true := by
            rw [valR a _ (lX w a c), val_input (lX w a c) (by have := a.isLt; omega)]
            simp only [X]
            rw [getD_append_ofFn, dif_pos a.isLt]
            simp
          exact e1.trans hO.symm
        · apply gate_same _ _ (lX w a c) (lo w c) hk D _ ih
          intro z hz hD
          subst hD
          exact onlyR a k hk hkr hz)
      C.output (hout a)
    have hXo : val C (X w a c) C.output = true := by
      apply mono (n + m) C hAO _ _ (lo a c) (lX w a c) (hleX w a c)
      have h2 := hR a c
      rw [hG] at h2
      exact h2
    have h2 := hR w c
    rw [key] at hXo
    rw [← h2]; exact hXo
  obtain ⟨c0, hc0⟩ : ∃ c, G v c = false := by
    have : 0 < (Finset.univ.filter (fun c => G v c = false)).card := by omega
    obtain ⟨c, hc⟩ := Finset.card_pos.mp this
    exact ⟨c, (Finset.mem_filter.mp hc).2⟩
  have hs0 := hsv c0 hc0
  have hsl : s v < n + m + (r v).val := hRB _ (rowL v) _ (memS v)
  have hsN : n + m ≤ s v := by
    by_contra hlt
    push_neg at hlt
    by_cases h1 : s v < n
    · rw [show (C.wires (col c0)).getD (s v) false = val C (col c0) (s v) from rfl,
        val_input (lc c0) hlt, ecol, if_pos h1] at hs0
      cases hs0
    · obtain ⟨c1, hc1, hne⟩ : ∃ c, G v c = false ∧ c.val ≠ s v - n := by
        by_contra hno
        push_neg at hno
        have : (Finset.univ.filter (fun c => G v c = false)) ⊆ {⟨s v - n, by omega⟩} := by
          intro c hc
          rw [Finset.mem_singleton]
          exact Fin.ext (hno c (Finset.mem_filter.mp hc).2)
        have := Finset.card_le_card this
        simp at this
        omega
      have hs1 := hsv c1 hc1
      rw [show (C.wires (col c1)).getD (s v) false = val C (col c1) (s v) from rfl,
        val_input (lc c1) hlt, ecol, if_neg h1, dif_pos (by omega)] at hs1
      simp only [decide_eq_true_eq] at hs1
      exact hne (by rw [← hs1])
  obtain ⟨jj, hjj⟩ : ∃ jj, s v = n + m + jj := ⟨s v - (n + m), by omega⟩
  have hjL : jj < C.gates.length := by
    by_contra hge
    push_neg at hge
    rw [show (C.wires (col c0)).getD (s v) false = val C (col c0) (s v) from rfl,
      val_ge (lc c0) (by omega)] at hs0
    cases hs0
  refine ⟨⟨jj, hjL⟩, hjj, ?_⟩
  intro w
  constructor
  · intro e
    have e' : (r w).val = jj := (congrArg Fin.val e).symm
    by_cases hwv : w = v
    · subst hwv
      omega
    · obtain ⟨c, hGw, hGv⟩ := hinc w v hwv
      have h1 := hsv c hGv
      have : val C (col c) (wire (r w)) = true := by
        show val C (col c) (n + m + (r w).val) = true
        rw [e', ← hjj]; exact h1
      rw [FLIP w c this] at hGw
      cases hGw
  · intro hmem
    have hmem' : wire (r w) ∈ (gateAt C jj).inputs := hmem
    have hlt : wire (r w) < n + m + jj := hRB jj hjL _ hmem'
    by_cases hwv : w = v
    · subst hwv
      simp only [wire] at hlt
      omega
    · rcases hAO _ (gateAt_mem hjL) with hop | hop
      · obtain ⟨c, hGw, hGv⟩ := hinc w v hwv
        have h1 := hsv c hGv
        have h1' : val C (col c) (n + m + jj) = true := by rw [← hjj]; exact h1
        rw [val_gate (lc c) hjL, hop, eval_and_iff] at h1'
        have := h1' _ hmem'
        rw [if_pos hlt] at this
        rw [FLIP w c this] at hGw
        cases hGw
      · obtain ⟨c, hGv, hGw⟩ := hinc v w (Ne.symm hwv)
        have hOw : val C (PEqualNP.Represents.oneEach w c) (wire (r w)) = true := by
          rw [valR w _ (lo w c), val_input (lo w c) (by have := w.isLt; omega)]
          unfold PEqualNP.Represents.oneEach
          rw [getD_append_ofFn, dif_pos w.isLt]
          simp
        have hj1 : val C (PEqualNP.Represents.oneEach w c) (n + m + jj) = true := by
          rw [val_gate (lo w c) hjL, hop, eval_or_iff]
          exact ⟨_, hmem', by rw [if_pos hlt]; exact hOw⟩
        have hOv : val C (PEqualNP.Represents.oneEach w c) (wire (r v)) = true := by
          rw [valR v _ (lo w c), hjj, hj1]
          simp
        rw [XL v w c (Ne.symm hwv) hGv hOv] at hGw
        cases hGw

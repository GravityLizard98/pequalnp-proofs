import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19415
open PEqualNP.CircuitLowerBounds

def run (G : List Gate) (x : List Bool) : List Bool :=
  G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def V (G : List Gate) (x : List Bool) (i : ℕ) : Bool := (run G x).getD i false

def M (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem run_snoc (G : List Gate) (g : Gate) (x : List Bool) :
    run (G ++ [g]) x = run G x ++ [g.op.eval (g.inputs.map fun i => (run G x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_append (G H : List Gate) (x : List Bool) : run (G ++ H) x = run H (run G x) := by
  simp [run, List.foldl_append]

theorem run_len (G : List Gate) (x : List Bool) : (run G x).length = x.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton G g ih => rw [run_snoc]; simp [ih]; omega

theorem gl (l : List Bool) (v : Bool) (i : ℕ) (h : i < l.length) : (l ++ [v]).getD i false = l.getD i false :=
  List.getD_append _ _ _ _ h

theorem ge (l : List Bool) (v : Bool) (k : ℕ) (h : k = l.length) : (l ++ [v]).getD k false = v := by
  subst h; simp

theorem run_pre (E : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run E w).getD i false = w.getD i false := by
  induction E using List.reverseRecOn with
  | nil => intro w i _; rfl
  | append_singleton E g ih =>
    intro w i hi
    rw [run_snoc, gl _ _ _ (by rw [run_len]; omega)]
    exact ih w i hi

theorem V_old (G E : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length + G.length) :
    V (G ++ E) x i = V G x i := by
  unfold V
  rw [run_append]
  exact run_pre E _ i (by rw [run_len]; exact h)

theorem V_in (G : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) : V G x i = x.getD i false :=
  run_pre G x i h

theorem V_new (G : List Gate) (g : Gate) (x : List Bool) :
    V (G ++ [g]) x (x.length + G.length) = g.op.eval (g.inputs.map (V G x)) := by
  unfold V
  rw [run_snoc, ge _ _ _ (by rw [run_len])]

theorem any_ext {α : Type} (f g : α → Bool) : ∀ l : List α, (∀ a ∈ l, f a = g a) → l.any f = l.any g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.any_cons, List.any_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

def orInto (N : ℕ) : List Gate → ℕ → List ℕ → List Gate × ℕ
  | G, acc, [] => (G, acc)
  | G, acc, w :: ws => orInto N (G ++ [(⟨GateOp.or, [acc, w]⟩ : Gate)]) (N + G.length) ws

theorem orInto_len (N : ℕ) : ∀ (ws : List ℕ) (G : List Gate) (acc : ℕ),
    (orInto N G acc ws).1.length = G.length + ws.length := by
  intro ws
  induction ws with
  | nil => intro G acc; rfl
  | cons w ws ih =>
    intro G acc
    rw [orInto, ih]
    simp
    omega

theorem orInto_pre (N : ℕ) : ∀ (ws : List ℕ) (G : List Gate) (acc : ℕ),
    ∃ E, (orInto N G acc ws).1 = G ++ E := by
  intro ws
  induction ws with
  | nil => intro G acc; exact ⟨[], by simp [orInto]⟩
  | cons w ws ih =>
    intro G acc
    obtain ⟨E, hE⟩ := ih (G ++ [(⟨GateOp.or, [acc, w]⟩ : Gate)]) (N + G.length)
    exact ⟨[(⟨GateOp.or, [acc, w]⟩ : Gate)] ++ E, by rw [orInto, hE, List.append_assoc]⟩

theorem orInto_mono (N : ℕ) : ∀ (ws : List ℕ) (G : List Gate) (acc : ℕ),
    (∀ g ∈ G, M g) → ∀ g ∈ (orInto N G acc ws).1, M g := by
  intro ws
  induction ws with
  | nil => intro G acc h; exact h
  | cons w ws ih =>
    intro G acc h
    rw [orInto]
    apply ih
    intro g hg
    rcases List.mem_append.1 hg with h1 | h1
    · exact h g h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      subst h1
      simp [M]

theorem orInto_lt (N : ℕ) : ∀ (ws : List ℕ) (G : List Gate) (acc : ℕ), acc < N + G.length →
    (orInto N G acc ws).2 < N + (orInto N G acc ws).1.length := by
  intro ws
  induction ws with
  | nil => intro G acc h; exact h
  | cons w ws ih =>
    intro G acc h
    rw [orInto]
    apply ih
    simp

theorem orInto_val (N : ℕ) (x : List Bool) (hx : x.length = N) : ∀ (ws : List ℕ) (G : List Gate) (acc : ℕ),
    acc < N + G.length → (∀ w ∈ ws, w < N + G.length) →
    V (orInto N G acc ws).1 x (orInto N G acc ws).2 = (V G x acc || ws.any (V G x)) := by
  intro ws
  induction ws with
  | nil => intro G acc _ _; simp [orInto]
  | cons w ws ih =>
    intro G acc h hw
    rw [orInto, ih _ _ (by simp) (fun w' hw' => by have := hw w' (by simp [hw']); simp; omega)]
    have e1 : V (G ++ [(⟨GateOp.or, [acc, w]⟩ : Gate)]) x (N + G.length) = (V G x acc || V G x w) := by
      rw [← hx, V_new]
      simp [GateOp.eval]
    have e2 : ws.any (V (G ++ [(⟨GateOp.or, [acc, w]⟩ : Gate)]) x) = ws.any (V G x) :=
      any_ext _ _ ws (fun w' hw' => V_old G _ x w' (by rw [hx]; exact hw w' (by simp [hw'])))
    rw [e1, e2, List.any_cons, Bool.or_assoc]

def res (base off k : ℕ) : ℕ := if k = 0 then base else off + (k - 1)

def orch (base off : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => orch base off k ++ [(⟨GateOp.or, [res base off k, base + (k + 1)]⟩ : Gate)]

theorem orch_len (base off : ℕ) : ∀ k, (orch base off k).length = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [orch, ih]

theorem orch_mono (base off : ℕ) : ∀ k, ∀ g ∈ orch base off k, M g := by
  intro k
  induction k with
  | zero => intro g hg; simp [orch] at hg
  | succ k ih =>
    intro g hg
    simp only [orch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl
    · exact ih g h
    · simp [M]

theorem orch_key (base off : ℕ) (x : List Bool) (hx : x.length = off) : ∀ k, base + k < off →
    ∀ j, j ≤ k → V (orch base off k) x (res base off j)
      = (List.range (j + 1)).any (fun i => x.getD (base + i) false) := by
  intro k
  induction k with
  | zero =>
    intro hk j hj
    have : j = 0 := by omega
    subst this
    simp [orch, res, V, run]
  | succ k ih =>
    intro hk j hj
    rw [orch]
    by_cases hjk : j ≤ k
    · rw [V_old _ _ _ _ (by rw [hx, orch_len]; unfold res; split <;> omega)]
      exact ih (by omega) j hjk
    · have hj' : j = k + 1 := by omega
      subst hj'
      have e : res base off (k + 1) = x.length + (orch base off k).length := by
        rw [orch_len, hx]; simp [res]
      rw [e, V_new]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id]
      rw [ih (by omega) k (le_refl k), V_in _ _ _ (by omega), List.range_succ (n := k + 1), List.any_append,
        List.any_cons, List.any_nil, Bool.or_false]

def stp (N : ℕ) (s : List Gate × ℕ) (c : List ℕ × ℕ) : List Gate × ℕ :=
  match c.1 with
  | [] => s
  | w :: ws =>
    ((orInto N s.1 w ws).1 ++ [(⟨GateOp.and, [(orInto N s.1 w ws).2, c.2]⟩ : Gate)]
      ++ [(⟨GateOp.or, [s.2, N + (orInto N s.1 w ws).1.length]⟩ : Gate)],
      N + (orInto N s.1 w ws).1.length + 1)

theorem stp_spec (N : ℕ) (G : List Gate) (acc : ℕ) (c : List ℕ × ℕ) (hacc : acc < N + G.length)
    (hne : c.1 ≠ []) (hw : ∀ w ∈ c.1, w < N + G.length) (hq : c.2 < N + G.length) :
    (stp N (G, acc) c).2 < N + (stp N (G, acc) c).1.length ∧
    (∃ E, (stp N (G, acc) c).1 = G ++ E) ∧
    (stp N (G, acc) c).1.length = G.length + (c.1.length + 1) ∧
    ((∀ g ∈ G, M g) → ∀ g ∈ (stp N (G, acc) c).1, M g) ∧
    ∀ x : List Bool, x.length = N →
      V (stp N (G, acc) c).1 x (stp N (G, acc) c).2 = (V G x acc || (c.1.any (V G x) && V G x c.2)) := by
  obtain ⟨l, q⟩ := c
  cases l with
  | nil => exact absurd rfl hne
  | cons w ws =>
    have hw0 : w < N + G.length := hw w (by simp)
    have hws : ∀ w' ∈ ws, w' < N + G.length := fun w' hw' => hw w' (by simp [hw'])
    have hlen := orInto_len N ws G w
    have hlt := orInto_lt N ws G w hw0
    obtain ⟨E, hE⟩ := orInto_pre N ws G w
    have hmono := orInto_mono N ws G w
    have hval := fun x hx => orInto_val N x hx ws G w hw0 hws
    simp only [stp]
    generalize orInto N G w ws = p at *
    obtain ⟨P, r⟩ := p
    simp only at hlen hlt hE hmono hval hq ⊢
    refine ⟨by simp; omega, ⟨E ++ [(⟨GateOp.and, [r, q]⟩ : Gate)] ++ [(⟨GateOp.or, [acc, N + P.length]⟩ : Gate)], by
      rw [hE]; simp⟩, by simp [hlen]; omega, ?_, ?_⟩
    · intro h g hg
      rcases List.mem_append.1 hg with h1 | h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact hmono h g h2
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
          subst h2
          simp [M]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
        subst h1
        simp [M]
    · intro x hx
      have e0 : N + P.length + 1 = x.length + (P ++ [(⟨GateOp.and, [r, q]⟩ : Gate)]).length := by
        simp; omega
      rw [e0, V_new]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id]
      have e1 : V (P ++ [(⟨GateOp.and, [r, q]⟩ : Gate)]) x acc = V G x acc := by
        rw [hE, List.append_assoc]
        exact V_old _ _ _ _ (by omega)
      have e2 : V (P ++ [(⟨GateOp.and, [r, q]⟩ : Gate)]) x (N + P.length) = (V P x r && V P x q) := by
        rw [← hx, V_new]
        simp [GateOp.eval]
      have e3 : V P x q = V G x q := by
        rw [hE]
        exact V_old _ _ _ _ (by omega)
      rw [e1, e2, e3, hval x hx]

theorem fold_spec (N : ℕ) : ∀ (cs : List (List ℕ × ℕ)) (G : List Gate) (acc : ℕ), acc < N + G.length →
    (∀ c ∈ cs, c.1 ≠ [] ∧ (∀ w ∈ c.1, w < N + G.length) ∧ c.2 < N + G.length) →
    (cs.foldl (stp N) (G, acc)).2 < N + (cs.foldl (stp N) (G, acc)).1.length ∧
    (∃ E, (cs.foldl (stp N) (G, acc)).1 = G ++ E) ∧
    (cs.foldl (stp N) (G, acc)).1.length = G.length + (cs.map (fun c => c.1.length + 1)).sum ∧
    ((∀ g ∈ G, M g) → ∀ g ∈ (cs.foldl (stp N) (G, acc)).1, M g) ∧
    ∀ x : List Bool, x.length = N →
      V (cs.foldl (stp N) (G, acc)).1 x (cs.foldl (stp N) (G, acc)).2
        = (V G x acc || cs.any (fun c => c.1.any (V G x) && V G x c.2)) := by
  intro cs
  induction cs with
  | nil => intro G acc h _; exact ⟨h, ⟨[], by simp⟩, by simp, fun h => h, fun x _ => by simp⟩
  | cons c cs ih =>
    intro G acc hacc hc
    obtain ⟨hne, hw, hq⟩ := hc c (by simp)
    obtain ⟨s1, s2, s3, s4, s5⟩ := stp_spec N G acc c hacc hne hw hq
    rw [List.foldl_cons]
    generalize stp N (G, acc) c = s at *
    obtain ⟨G1, acc1⟩ := s
    simp only at s1 s2 s3 s4 s5
    obtain ⟨E1, hE1⟩ := s2
    have hc' : ∀ c' ∈ cs, c'.1 ≠ [] ∧ (∀ w ∈ c'.1, w < N + G1.length) ∧ c'.2 < N + G1.length := by
      intro c' hc'
      obtain ⟨a, b, d⟩ := hc c' (by simp [hc'])
      exact ⟨a, fun w hw' => by have := b w hw'; omega, by omega⟩
    obtain ⟨t1, t2, t3, t4, t5⟩ := ih G1 acc1 s1 hc'
    obtain ⟨E2, hE2⟩ := t2
    refine ⟨t1, ⟨E1 ++ E2, by rw [hE2, hE1, List.append_assoc]⟩, by
      rw [t3, s3, List.map_cons, List.sum_cons]; omega, fun h => t4 (s4 h), ?_⟩
    intro x hx
    rw [t5 x hx, s5 x hx, List.any_cons, Bool.or_assoc]
    congr 2
    apply any_ext
    intro c' hc''
    obtain ⟨a, b, d⟩ := hc c' (by simp [hc''])
    have e1 : V G1 x c'.2 = V G x c'.2 := by
      rw [hE1]; exact V_old _ _ _ _ (by omega)
    have e2 : c'.1.any (V G1 x) = c'.1.any (V G x) :=
      any_ext _ _ _ (fun w hw' => by rw [hE1]; exact V_old _ _ _ _ (by have := b w hw'; omega))
    rw [e1, e2]

theorem ofg {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) : (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [h]

theorem one_len {n : ℕ} (u v : Fin n) : (PEqualNP.Represents.oneEach u v).length = 2 * n := by
  simp [PEqualNP.Represents.oneEach]; omega

theorem one_l {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  rw [ofg _ i hi]; simp [Fin.ext_iff]

theorem one_r {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (PEqualNP.Represents.oneEach u v).getD (n + i) false = decide (i = v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  have e : n + i - (List.ofFn fun i : Fin n => decide (i = u)).length = i := by simp
  rw [e, ofg _ i hi]; simp [Fin.ext_iff]

theorem rows_any {n : ℕ} (u v : Fin n) (G : List Gate) (L : List (Fin n)) :
    (L.map Fin.val).any (V G (PEqualNP.Represents.oneEach u v)) = decide (u ∈ L) := by
  rw [Bool.eq_iff_iff, List.any_eq_true]
  simp only [List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨w, ⟨u', hu', rfl⟩, h⟩
    rw [V_in _ _ _ (by rw [one_len]; omega), one_l u v _ u'.isLt] at h
    have := of_decide_eq_true h
    have : u' = u := Fin.ext this
    rw [← this]; exact hu'
  · intro h
    refine ⟨u.val, ⟨u, h, rfl⟩, ?_⟩
    rw [V_in _ _ _ (by rw [one_len]; omega), one_l u v _ u.isLt]
    simp

theorem cnt (n : ℕ) (R : ℕ → List (Fin n)) (q : ℕ → ℕ) : ∀ vals : List ℕ,
    (List.map (fun c : List ℕ × ℕ => c.1.length + 1) (List.map (fun a => ((R a).map Fin.val, q a)) vals)).sum
      = (vals.map (fun a => (R a).length)).sum + vals.length := by
  intro vals
  induction vals with
  | nil => rfl
  | cons a vals ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, List.length_cons, List.length_map]
    omega

theorem build (n : ℕ) (t : Fin n → ℕ) (a1 : ℕ) (R : ℕ → List (Fin n)) (vals : List ℕ)
    (hR : ∀ a u, u ∈ R a ↔ t u = a) (h1 : 1 ≤ a1) (h2 : a1 + 2 ≤ n) (hmin : ∀ u, a1 ≤ t u)
    (hn : R n ≠ []) (hv : ∀ a ∈ vals, a1 < a ∧ a < n ∧ R a ≠ [])
    (hall : ∀ u, t u = a1 ∨ t u = n ∨ t u ∈ vals) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      C.size + 3 = n + (R n).length + (vals.map (fun a => (R a).length)).sum + vals.length ∧
      PEqualNP.Represents.Represents (fun u v : Fin n => decide ((v : ℕ) < t u)) C := by
  cases hRn : R n with
  | nil => exact absurd hRn hn
  | cons u0 us =>
    have hQl := orch_len (n + a1) (2 * n) (n - a1 - 2)
    have hQm := orch_mono (n + a1) (2 * n) (n - a1 - 2)
    generalize hQ : orch (n + a1) (2 * n) (n - a1 - 2) = Q at hQl hQm
    have hw0 : ∀ w ∈ us.map Fin.val ++ (List.range a1).map (fun i => n + i), w < 2 * n + Q.length := by
      intro w hw
      rcases List.mem_append.1 hw with h | h
      · obtain ⟨u', _, rfl⟩ := List.mem_map.1 h
        have := u'.isLt; omega
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
        have := List.mem_range.1 hi; omega
    have hu0 : u0.val < 2 * n + Q.length := by have := u0.isLt; omega
    have p_len := orInto_len (2 * n) (us.map Fin.val ++ (List.range a1).map (fun i => n + i)) Q u0.val
    have p_lt := orInto_lt (2 * n) (us.map Fin.val ++ (List.range a1).map (fun i => n + i)) Q u0.val hu0
    have p_pre := orInto_pre (2 * n) (us.map Fin.val ++ (List.range a1).map (fun i => n + i)) Q u0.val
    have p_mono := orInto_mono (2 * n) (us.map Fin.val ++ (List.range a1).map (fun i => n + i)) Q u0.val hQm
    have p_val := fun x hx => orInto_val (2 * n) x hx
      (us.map Fin.val ++ (List.range a1).map (fun i => n + i)) Q u0.val hu0 hw0
    generalize orInto (2 * n) Q u0.val (us.map Fin.val ++ (List.range a1).map (fun i => n + i)) = p at *
    obtain ⟨G0, acc0⟩ := p
    simp only at p_len p_lt p_pre p_mono p_val
    obtain ⟨E0, hE0⟩ := p_pre
    have hres : ∀ a ∈ vals, res (n + a1) (2 * n) (a - 1 - a1) < 2 * n + Q.length := by
      intro a ha
      obtain ⟨b1, b2, _⟩ := hv a ha
      unfold res; split <;> omega
    have hcs : ∀ c ∈ vals.map (fun a => ((R a).map Fin.val, res (n + a1) (2 * n) (a - 1 - a1))),
        c.1 ≠ [] ∧ (∀ w ∈ c.1, w < 2 * n + G0.length) ∧ c.2 < 2 * n + G0.length := by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
      obtain ⟨b1, b2, b3⟩ := hv a ha
      refine ⟨by simpa using b3, ?_, ?_⟩
      · intro w hw
        obtain ⟨u', _, rfl⟩ := List.mem_map.1 hw
        have := u'.isLt; omega
      · have := hres a ha; omega
    obtain ⟨f1, f2, f3, f4, f5⟩ := fold_spec (2 * n)
      (vals.map (fun a => ((R a).map Fin.val, res (n + a1) (2 * n) (a - 1 - a1)))) G0 acc0 p_lt hcs
    generalize (vals.map (fun a => ((R a).map Fin.val, res (n + a1) (2 * n) (a - 1 - a1)))).foldl
      (stp (2 * n)) (G0, acc0) = s at *
    obtain ⟨G1, acc1⟩ := s
    simp only at f1 f2 f3 f4 f5
    refine ⟨⟨G1, acc1⟩, fun g hg => f4 p_mono g hg, ?_, ?_⟩
    · show G1.length + 3 = _
      have e : (List.map (fun c : List ℕ × ℕ => c.1.length + 1)
          (List.map (fun a => ((R a).map Fin.val, res (n + a1) (2 * n) (a - 1 - a1))) vals)).sum
          = (vals.map (fun a => (R a).length)).sum + vals.length := by
        exact cnt n R (fun a => res (n + a1) (2 * n) (a - 1 - a1)) vals
      rw [f3, e, p_len]
      simp
      omega
    · intro u v
      have hx := one_len u v
      show V G1 (PEqualNP.Represents.oneEach u v) acc1 = _
      rw [f5 _ hx, p_val _ hx, List.any_append]
      have hu := u.isLt
      have hvv := v.isLt
      have c1 : V Q (PEqualNP.Represents.oneEach u v) u0.val = decide (u = u0) := by
        rw [V_in _ _ _ (by rw [hx]; have := u0.isLt; omega), one_l u v _ u0.isLt]
        simp [Fin.ext_iff, eq_comm]
      have c2 : (us.map Fin.val).any (V Q (PEqualNP.Represents.oneEach u v)) = decide (u ∈ us) := rows_any u v Q us
      have c3 : ((List.range a1).map (fun i => n + i)).any (V Q (PEqualNP.Represents.oneEach u v))
          = decide (v.val < a1) := by
        rw [Bool.eq_iff_iff, List.any_eq_true]
        simp only [List.mem_map, List.mem_range, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨i, hi, rfl⟩, h⟩
          rw [V_in _ _ _ (by rw [hx]; omega), one_r u v _ (by omega)] at h
          have := of_decide_eq_true h
          omega
        · intro h
          refine ⟨n + v.val, ⟨v.val, h, rfl⟩, ?_⟩
          rw [V_in _ _ _ (by rw [hx]; omega), one_r u v _ hvv]
          simp
      have c4 : (vals.map (fun a => ((R a).map Fin.val, res (n + a1) (2 * n) (a - 1 - a1)))).any
          (fun c => c.1.any (V G0 (PEqualNP.Represents.oneEach u v)) && V G0 (PEqualNP.Represents.oneEach u v) c.2)
          = vals.any (fun a => decide (t u = a) && decide (a1 ≤ v.val ∧ v.val < a)) := by
        rw [List.any_map]
        apply any_ext
        intro a ha
        obtain ⟨b1, b2, b3⟩ := hv a ha
        simp only [Function.comp_apply]
        rw [rows_any u v G0 (R a), hE0, V_old _ _ _ _ (by rw [hx]; exact hres a ha), ← hQ,
          orch_key (n + a1) (2 * n) _ hx (n - a1 - 2) (by omega) (a - 1 - a1) (by omega)]
        congr 1
        · simp [hR]
        · rw [Bool.eq_iff_iff, List.any_eq_true]
          simp only [List.mem_range, decide_eq_true_eq]
          constructor
          · rintro ⟨i, hi, h⟩
            rw [Nat.add_assoc, one_r u v _ (by omega)] at h
            have := of_decide_eq_true h
            omega
          · intro h
            refine ⟨v.val - a1, by omega, ?_⟩
            rw [Nat.add_assoc, one_r u v _ (by omega)]
            simp
            omega
      rw [c1, c2, c3, c4, Bool.eq_iff_iff]
      have hRu : u ∈ R n ↔ t u = n := hR n u
      rw [hRn] at hRu
      simp only [List.mem_cons] at hRu
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
      constructor
      · rintro ((h | h | h) | ⟨a, ha, h3, h4⟩)
        · have := hRu.1 (Or.inl h); omega
        · have := hRu.1 (Or.inr h); omega
        · have := hmin u; omega
        · omega
      · intro h
        rcases hall u with h3 | h3 | h3
        · exact Or.inl (Or.inr (Or.inr (by omega)))
        · rcases hRu.2 h3 with h4 | h4
          · exact Or.inl (Or.inl h4)
          · exact Or.inl (Or.inr (Or.inl h4))
        · by_cases h5 : v.val < a1
          · exact Or.inl (Or.inr (Or.inr h5))
          · exact Or.inr ⟨t u, h3, rfl, by omega, h⟩

theorem main : ∀ n k : ℕ, 3 ≤ k → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) (2 * n + k - 6) := by
  intro n k hk t ht htop hcard
  obtain ⟨utop, hutop⟩ := htop
  obtain ⟨u0, _, hu0⟩ := Finset.exists_min_image Finset.univ t ⟨utop, Finset.mem_univ _⟩
  have hmin : ∀ u, t u0 ≤ t u := fun u => hu0 u (Finset.mem_univ _)
  have hS : ∀ a, a ∈ ((Finset.univ.image t).erase (t u0)).erase n ↔ (a ≠ n ∧ a ≠ t u0 ∧ ∃ u, t u = a) := by
    intro a
    simp [Finset.mem_erase, Finset.mem_image]
  have hc1 : k - 2 ≤ (((Finset.univ.image t).erase (t u0)).erase n).card := by
    have a1 := Finset.pred_card_le_card_erase (s := Finset.univ.image t) (a := t u0)
    have a2 := Finset.pred_card_le_card_erase (s := (Finset.univ.image t).erase (t u0)) (a := n)
    omega
  have hne : (((Finset.univ.image t).erase (t u0)).erase n).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨am, ham⟩ := hne
  obtain ⟨am1, am2, um, hum⟩ := (hS am).1 ham
  have hlo : t u0 + 2 ≤ n := by
    have := hmin um; have := (ht um).2; omega
  have hmemn : n ∈ (Finset.univ.image t).erase (t u0) := by
    rw [Finset.mem_erase, Finset.mem_image]
    exact ⟨by omega, utop, Finset.mem_univ _, hutop⟩
  have hmem0 : t u0 ∈ Finset.univ.image t := Finset.mem_image.2 ⟨u0, Finset.mem_univ _, rfl⟩
  have hc2 : (((Finset.univ.image t).erase (t u0)).erase n).card = k - 2 := by
    rw [Finset.card_erase_of_mem hmemn, Finset.card_erase_of_mem hmem0, hcard]; rfl
  obtain ⟨C, hC1, hC2, hC3⟩ := build n t (t u0) (fun a => (Finset.univ.filter (fun u => t u = a)).toList)
    (((Finset.univ.image t).erase (t u0)).erase n).toList
    (fun a u => by simp) (ht u0).1 hlo hmin
    (by
      intro h
      have : utop ∈ (Finset.univ.filter (fun u => t u = n)).toList := by simp [hutop]
      rw [h] at this
      simp at this)
    (by
      intro a ha
      rw [Finset.mem_toList] at ha
      obtain ⟨b1, b2, ub, hub⟩ := (hS a).1 ha
      have := hmin ub; have := (ht ub).2
      refine ⟨by omega, by omega, ?_⟩
      intro h
      have : ub ∈ (Finset.univ.filter (fun u => t u = a)).toList := by simp [hub]
      rw [h] at this
      simp at this)
    (by
      intro u
      by_cases h1 : t u = t u0
      · exact Or.inl h1
      · by_cases h2 : t u = n
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (by rw [Finset.mem_toList, hS]; exact ⟨h2, h1, u, rfl⟩)))
  refine ⟨C, hC1, ?_, hC3⟩
  simp only [Finset.length_toList] at hC2
  rw [Finset.sum_map_toList, hc2] at hC2
  have hnS : n ∉ ((Finset.univ.image t).erase (t u0)).erase n := Finset.notMem_erase _ _
  have key : (Finset.univ.filter (fun u => t u = n)).card
      + ∑ a ∈ ((Finset.univ.image t).erase (t u0)).erase n, (Finset.univ.filter (fun u => t u = a)).card
      ≤ n - 1 := by
    rw [← Finset.sum_insert (f := fun a => (Finset.univ.filter (fun u => t u = a)).card) hnS]
    have e : ∑ a ∈ insert n (((Finset.univ.image t).erase (t u0)).erase n),
        (Finset.univ.filter (fun u => t u = a)).card
        = (Finset.univ.filter (fun u => t u ∈ insert n (((Finset.univ.image t).erase (t u0)).erase n))).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := t)
        (s := Finset.univ.filter (fun u => t u ∈ insert n (((Finset.univ.image t).erase (t u0)).erase n)))
        (t := insert n (((Finset.univ.image t).erase (t u0)).erase n))
        (fun u hu => (Finset.mem_filter.1 hu).2)]
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨by rw [h]; exact ha, h⟩
      · intro h; exact h.2
    rw [e]
    have sub : Finset.univ.filter (fun u => t u ∈ insert n (((Finset.univ.image t).erase (t u0)).erase n))
        ⊆ Finset.univ.erase u0 := by
      intro u hu
      rw [Finset.mem_filter, Finset.mem_insert, hS] at hu
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      subst h
      rcases hu.2 with h | h
      · omega
      · exact h.2.1 rfl
    have := Finset.card_le_card sub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    exact this
  show C.size ≤ 2 * n + k - 6
  omega

end PEqualNP.Outside.L_meta_19415

theorem PEqualNP.Outside.L_meta_19415 : ∀ n k : ℕ, 3 ≤ k → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) (2 * n + k - 6) :=
  PEqualNP.Outside.L_meta_19415.main

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22921
open PEqualNP.CircuitLowerBounds

def run (G : List Gate) (x : List Bool) : List Bool :=
  G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def val (x : List Bool) (N : ℕ) (vs : List Bool) (i : ℕ) : Bool :=
  if i < N then x.getD i false else vs.getD (i - N) false

theorem val_eq (x : List Bool) (N : ℕ) (hx : x.length = N) (vs : List Bool) (i : ℕ) :
    (x ++ vs).getD i false = val x N vs i := by
  unfold val
  by_cases h : i < N
  · rw [ite_eq_left h, List.getD_append _ _ _ _ (by omega)]
  · rw [ite_eq_right h, List.getD_append_right _ _ _ _ (by omega), hx]

def go (x : List Bool) (N : ℕ) : List Gate → List Bool → List Bool
  | [], vs => vs
  | g :: G, vs => go x N G (vs ++ [g.op.eval (g.inputs.map (val x N vs))])

theorem run_go (x : List Bool) (N : ℕ) (hx : x.length = N) :
    ∀ (G : List Gate) (vs : List Bool), run G (x ++ vs) = x ++ go x N G vs := by
  intro G
  induction G with
  | nil => intro vs; rfl
  | cons g G ih =>
    intro vs
    have e : run (g :: G) (x ++ vs) = run G (x ++ (vs ++ [g.op.eval (g.inputs.map (val x N vs))])) := by
      show run G ((x ++ vs) ++ [g.op.eval (g.inputs.map fun i => (x ++ vs).getD i false)]) = _
      have hf : (fun i => (x ++ vs).getD i false) = val x N vs := funext (val_eq x N hx vs)
      rw [hf, List.append_assoc]
    rw [e, ih]
    rfl

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

def res (base off k : ℕ) : ℕ := if k = 0 then base else off + (k - 1)

def orch (base off : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => orch base off k ++ [(⟨GateOp.or, [res base off k, base + (k + 1)]⟩ : Gate)]

theorem orch_len (base off : ℕ) : ∀ k, (orch base off k).length = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [orch, ih]

theorem orch_mono (base off : ℕ) : ∀ k, ∀ g ∈ orch base off k,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro g hg; simp [orch] at hg
  | succ k ih =>
    intro g hg
    simp only [orch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl
    · exact ih g h
    · simp

theorem orch_key (base off : ℕ) (w : List Bool) (hw : w.length = off) : ∀ k, base + k < off →
    (∀ i < off, (run (orch base off k) w).getD i false = w.getD i false) ∧
    (run (orch base off k) w).getD (res base off k) false
      = (List.range (k + 1)).any (fun j => w.getD (base + j) false) := by
  intro k
  induction k with
  | zero => intro _; simp [orch, run, res]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hl := run_len (orch base off k) w
    rw [orch_len, hw] at hl
    have hr : res base off k < off + k := by unfold res; split <;> omega
    rw [orch, run_snoc]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [gl _ _ _ (by omega)]; exact h1 i hi
    · have e : res base off (k + 1) = off + k := by simp [res]
      rw [e, ge _ _ _ (by omega)]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id]
      rw [h2, h1 (base + (k + 1)) (by omega), List.range_succ (n := k + 1), List.any_append, List.any_cons, List.any_nil,
        Bool.or_false]

def fg (N r0 r1 r2 r3 c0 c1 c2 c3 ip iq : ℕ) : List Gate :=
  [⟨GateOp.or, [r0, ip]⟩, ⟨GateOp.and, [N, c0]⟩, ⟨GateOp.or, [r0, r2]⟩, ⟨GateOp.and, [N + 2, c3]⟩,
    ⟨GateOp.or, [c1, c2]⟩, ⟨GateOp.and, [r1, N + 4]⟩, ⟨GateOp.or, [c0, c1]⟩, ⟨GateOp.or, [N + 6, iq]⟩,
    ⟨GateOp.and, [r3, N + 7]⟩, ⟨GateOp.or, [N + 1, N + 3]⟩, ⟨GateOp.or, [N + 9, N + 5]⟩,
    ⟨GateOp.or, [N + 10, N + 8]⟩]

theorem core (x : List Bool) (N r0 r1 r2 r3 c0 c1 c2 c3 ip iq : ℕ) (hx : x.length = N) (h0 : r0 < N)
    (h1 : r1 < N) (h2 : r2 < N) (h3 : r3 < N) (k0 : c0 < N) (k1 : c1 < N) (k2 : c2 < N) (k3 : c3 < N)
    (hip : ip < N) (hiq : iq < N) :
    (run (fg N r0 r1 r2 r3 c0 c1 c2 c3 ip iq) x).getD (N + 11) false
      = (((((x.getD r0 false || x.getD ip false) && x.getD c0 false) ||
            ((x.getD r0 false || x.getD r2 false) && x.getD c3 false)) ||
          (x.getD r1 false && (x.getD c1 false || x.getD c2 false))) ||
        (x.getD r3 false && ((x.getD c0 false || x.getD c1 false) || x.getD iq false))) := by
  have e : run (fg N r0 r1 r2 r3 c0 c1 c2 c3 ip iq) x = run (fg N r0 r1 r2 r3 c0 c1 c2 c3 ip iq) (x ++ []) := by
    rw [List.append_nil]
  rw [e, run_go x N hx, val_eq x N hx]
  simp [fg, go, val, GateOp.eval, h0, h1, h2, h3, k0, k1, k2, k3, hip, hiq]

theorem main : ∀ n : ℕ, 5 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 0 ∨ v.val = 3)) ∨ (u.val = 1 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ (v.val ≤ 1 ∨ 4 ≤ v.val)) ∨ (4 ≤ u.val ∧ v.val = 0))) (2 * n + 2) := by
  intro n hn
  refine ⟨⟨(orch (n + 4) (2 * n) (n - 5) ++ orch 4 (2 * n + (n - 5)) (n - 5)) ++
      fg (2 * n + (n - 5) + (n - 5)) 0 1 2 3 n (n + 1) (n + 2) (n + 3) (res 4 (2 * n + (n - 5)) (n - 5))
        (res (n + 4) (2 * n) (n - 5)), 2 * n + (n - 5) + (n - 5) + 11⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · rcases List.mem_append.1 h with h | h
      · exact orch_mono _ _ _ g h
      · exact orch_mono _ _ _ g h
    · simp only [fg, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [Circuit.size, orch_len, fg]; omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    have hx := one_len u v
    obtain ⟨a1, a2⟩ := orch_key (n + 4) (2 * n) _ hx (n - 5) (by omega)
    have hl1 := run_len (orch (n + 4) (2 * n) (n - 5)) (PEqualNP.Represents.oneEach u v)
    rw [orch_len, hx] at hl1
    obtain ⟨b1, b2⟩ := orch_key 4 (2 * n + (n - 5)) _ hl1 (n - 5) (by omega)
    have hl2 := run_len (orch 4 (2 * n + (n - 5)) (n - 5)) (run (orch (n + 4) (2 * n) (n - 5)) (PEqualNP.Represents.oneEach u v))
    rw [orch_len, hl1] at hl2
    have r1 : res (n + 4) (2 * n) (n - 5) < 2 * n + (n - 5) := by unfold res; split <;> omega
    have r2 : res 4 (2 * n + (n - 5)) (n - 5) < 2 * n + (n - 5) + (n - 5) := by unfold res; split <;> omega
    show (run ((orch (n + 4) (2 * n) (n - 5) ++ orch 4 (2 * n + (n - 5)) (n - 5)) ++
      fg (2 * n + (n - 5) + (n - 5)) 0 1 2 3 n (n + 1) (n + 2) (n + 3) (res 4 (2 * n + (n - 5)) (n - 5))
        (res (n + 4) (2 * n) (n - 5))) (PEqualNP.Represents.oneEach u v)).getD (2 * n + (n - 5) + (n - 5) + 11) false = _
    rw [run_append, run_append]
    generalize hY1 : run (orch (n + 4) (2 * n) (n - 5)) (PEqualNP.Represents.oneEach u v) = Y1 at *
    generalize hY2 : run (orch 4 (2 * n + (n - 5)) (n - 5)) Y1 = Y2 at *
    rw [core Y2 _ _ _ _ _ _ _ _ _ _ _ hl2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) r2 (by omega)]
    have e0 : Y2.getD 0 false = decide (0 = u.val) := by
      rw [b1 0 (by omega), a1 0 (by omega), one_l u v 0 (by omega)]
    have e1 : Y2.getD 1 false = decide (1 = u.val) := by
      rw [b1 _ (by omega), a1 _ (by omega), one_l u v 1 (by omega)]
    have e2 : Y2.getD 2 false = decide (2 = u.val) := by
      rw [b1 _ (by omega), a1 _ (by omega), one_l u v 2 (by omega)]
    have e3 : Y2.getD 3 false = decide (3 = u.val) := by
      rw [b1 _ (by omega), a1 _ (by omega), one_l u v 3 (by omega)]
    have f0 : Y2.getD n false = decide (0 = v.val) := by
      rw [b1 n (by omega), a1 n (by omega)]
      exact one_r u v 0 (by omega)
    have f1 : Y2.getD (n + 1) false = decide (1 = v.val) := by
      rw [b1 _ (by omega), a1 _ (by omega), one_r u v 1 (by omega)]
    have f2 : Y2.getD (n + 2) false = decide (2 = v.val) := by
      rw [b1 _ (by omega), a1 _ (by omega), one_r u v 2 (by omega)]
    have f3 : Y2.getD (n + 3) false = decide (3 = v.val) := by
      rw [b1 _ (by omega), a1 _ (by omega), one_r u v 3 (by omega)]
    have cq : Y2.getD (res (n + 4) (2 * n) (n - 5)) false = decide (4 ≤ v.val) := by
      rw [b1 _ r1, a2, Bool.eq_iff_iff, List.any_eq_true]
      simp only [List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj, h⟩
        rw [Nat.add_assoc, one_r u v (4 + j) (by omega)] at h
        have := of_decide_eq_true h
        omega
      · intro h
        refine ⟨v.val - 4, by omega, ?_⟩
        rw [Nat.add_assoc, one_r u v (4 + (v.val - 4)) (by omega)]
        simp
        omega
    have cp : Y2.getD (res 4 (2 * n + (n - 5)) (n - 5)) false = decide (4 ≤ u.val) := by
      rw [b2, Bool.eq_iff_iff, List.any_eq_true]
      simp only [List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj, h⟩
        rw [a1 _ (by omega), one_l u v (4 + j) (by omega)] at h
        have := of_decide_eq_true h
        omega
      · intro h
        refine ⟨u.val - 4, by omega, ?_⟩
        rw [a1 _ (by omega), one_l u v (4 + (u.val - 4)) (by omega)]
        simp
        omega
    rw [e0, e1, e2, e3, f0, f1, f2, f3, cp, cq, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

end PEqualNP.Outside.L_meta_22921

theorem PEqualNP.Outside.L_meta_22921 : ∀ n : ℕ, 5 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 0 ∨ v.val = 3)) ∨ (u.val = 1 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ (v.val ≤ 1 ∨ 4 ≤ v.val)) ∨ (4 ≤ u.val ∧ v.val = 0))) (2 * n + 2) :=
  PEqualNP.Outside.L_meta_22921.main

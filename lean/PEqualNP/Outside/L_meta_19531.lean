import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19531
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

def fg (N ia ib ip iq : ℕ) : List Gate :=
  [⟨GateOp.and, [ip, iq]⟩, ⟨GateOp.or, [N, ia]⟩, ⟨GateOp.or, [N + 1, ib]⟩]

theorem core (x : List Bool) (N ia ib ip iq : ℕ) (hx : x.length = N) (hia : ia < N) (hib : ib < N)
    (hip : ip < N) (hiq : iq < N) :
    (run (fg N ia ib ip iq) x).getD (N + 2) false
      = (((x.getD ip false && x.getD iq false) || x.getD ia false) || x.getD ib false) := by
  have e : run (fg N ia ib ip iq) x = run (fg N ia ib ip iq) (x ++ []) := by
    rw [List.append_nil]
  rw [e, run_go x N hx, val_eq x N hx]
  simp [fg, go, val, GateOp.eval, hia, hib, hip, hiq]

theorem main : ∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u : ℕ) = 0 ∨ (v : ℕ) = 0 ∨ ((u : ℕ) ≠ n - 1 ∧ (v : ℕ) ≠ n - 1))) (2 * n - 3) := by
  intro n hn
  refine ⟨⟨(orch (n + 1) (2 * n) (n - 3) ++ orch 1 (2 * n + (n - 3)) (n - 3)) ++
      fg (2 * n + (n - 3) + (n - 3)) 0 n (res (n + 1) (2 * n) (n - 3))
        (res 1 (2 * n + (n - 3)) (n - 3)), 2 * n + (n - 3) + (n - 3) + 2⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · rcases List.mem_append.1 h with h | h
      · exact orch_mono _ _ _ g h
      · exact orch_mono _ _ _ g h
    · simp only [fg, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp
  · simp [Circuit.size, orch_len, fg]; omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    have hx := one_len u v
    obtain ⟨a1, a2⟩ := orch_key (n + 1) (2 * n) _ hx (n - 3) (by omega)
    have hl1 := run_len (orch (n + 1) (2 * n) (n - 3)) (PEqualNP.Represents.oneEach u v)
    rw [orch_len, hx] at hl1
    obtain ⟨b1, b2⟩ := orch_key 1 (2 * n + (n - 3)) _ hl1 (n - 3) (by omega)
    have hl2 := run_len (orch 1 (2 * n + (n - 3)) (n - 3)) (run (orch (n + 1) (2 * n) (n - 3)) (PEqualNP.Represents.oneEach u v))
    rw [orch_len, hl1] at hl2
    have r1 : res (n + 1) (2 * n) (n - 3) < 2 * n + (n - 3) := by unfold res; split <;> omega
    have r2 : res 1 (2 * n + (n - 3)) (n - 3) < 2 * n + (n - 3) + (n - 3) := by unfold res; split <;> omega
    show (run ((orch (n + 1) (2 * n) (n - 3) ++ orch 1 (2 * n + (n - 3)) (n - 3)) ++
      fg (2 * n + (n - 3) + (n - 3)) 0 n (res (n + 1) (2 * n) (n - 3))
        (res 1 (2 * n + (n - 3)) (n - 3))) (PEqualNP.Represents.oneEach u v)).getD (2 * n + (n - 3) + (n - 3) + 2) false = _
    rw [run_append, run_append]
    generalize hY1 : run (orch (n + 1) (2 * n) (n - 3)) (PEqualNP.Represents.oneEach u v) = Y1 at *
    generalize hY2 : run (orch 1 (2 * n + (n - 3)) (n - 3)) Y1 = Y2 at *
    rw [core Y2 _ _ _ _ _ hl2 (by omega) (by omega) (by omega) r2]
    have c0 : Y2.getD 0 false = decide (0 = u.val) := by
      rw [b1 0 (by omega), a1 0 (by omega), one_l u v 0 (by omega)]
    have c1 : Y2.getD n false = decide (0 = v.val) := by
      rw [b1 n (by omega), a1 n (by omega)]
      exact one_r u v 0 (by omega)
    have cp : Y2.getD (res (n + 1) (2 * n) (n - 3)) false = decide (1 ≤ v.val ∧ v.val ≤ n - 2) := by
      rw [b1 _ r1, a2, Bool.eq_iff_iff, List.any_eq_true]
      simp only [List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj, h⟩
        rw [Nat.add_assoc, one_r u v (1 + j) (by omega)] at h
        have := of_decide_eq_true h
        omega
      · intro h
        refine ⟨v.val - 1, by omega, ?_⟩
        rw [Nat.add_assoc, one_r u v (1 + (v.val - 1)) (by omega)]
        simp
        omega
    have cq : Y2.getD (res 1 (2 * n + (n - 3)) (n - 3)) false = decide (1 ≤ u.val ∧ u.val ≤ n - 2) := by
      rw [b2, Bool.eq_iff_iff, List.any_eq_true]
      simp only [List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj, h⟩
        rw [a1 _ (by omega), one_l u v (1 + j) (by omega)] at h
        have := of_decide_eq_true h
        omega
      · intro h
        refine ⟨u.val - 1, by omega, ?_⟩
        rw [a1 _ (by omega), one_l u v (1 + (u.val - 1)) (by omega)]
        simp
        omega
    rw [c0, c1, cp, cq, Bool.eq_iff_iff]
    simp
    omega

end PEqualNP.Outside.L_meta_19531

theorem PEqualNP.Outside.L_meta_19531 : ∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u : ℕ) = 0 ∨ (v : ℕ) = 0 ∨ ((u : ℕ) ≠ n - 1 ∧ (v : ℕ) ≠ n - 1))) (2 * n - 3) :=
  PEqualNP.Outside.L_meta_19531.main

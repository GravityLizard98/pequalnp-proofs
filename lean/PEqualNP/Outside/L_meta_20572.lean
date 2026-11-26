import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20572
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

def circ (N i0 i1 : ℕ) : Circuit :=
  ⟨[⟨GateOp.and, [i0, i1]⟩, ⟨GateOp.or, [i0, i1]⟩, ⟨GateOp.not, [N + 1]⟩, ⟨GateOp.or, [N + 0, N + 2]⟩], N + 3⟩

theorem core (x : List Bool) (N i0 i1 : ℕ) (hx : x.length = N) (h0 : i0 < N) (h1 : i1 < N) :
    (circ N i0 i1).eval x = ((x.getD i0 false && x.getD i1 false) || (!(x.getD i0 false || x.getD i1 false))) := by
  have e : (circ N i0 i1).eval x = (run (circ N i0 i1).gates (x ++ [])).getD (N + 3) false := by
    rw [List.append_nil]; rfl
  rw [e, run_go x N hx, val_eq x N hx]
  simp [circ, go, val, GateOp.eval, h0, h1]

theorem main : ∀ n : ℕ, 2 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val = 0) ∨ (u.val ≠ 0 ∧ v.val ≠ 0))) C := by
  intro n hn
  refine ⟨circ (2 * n) (0) (n + 0), ?_, by simp [circ, Circuit.size], ?_⟩
  · intro g hg
    simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro u v
    rw [core _ (2 * n) (0) (n + 0) (one_len u v) (by omega) (by omega)]
    rw [one_l u v 0 (by omega), one_r u v 0 (by omega)]
    have := u.isLt
    have := v.isLt
    rw [Bool.eq_iff_iff]
    simp
    omega

end PEqualNP.Outside.L_meta_20572

theorem PEqualNP.Outside.L_meta_20572 : ∀ n : ℕ, 2 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val = 0) ∨ (u.val ≠ 0 ∧ v.val ≠ 0))) C :=
  PEqualNP.Outside.L_meta_20572.main

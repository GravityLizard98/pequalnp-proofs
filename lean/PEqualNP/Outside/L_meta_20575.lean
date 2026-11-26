import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20575
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

def fg (N ia ib ic id ie jf : ℕ) : List Gate :=
  [⟨GateOp.or, [ib, ic]⟩, ⟨GateOp.or, [id, ie]⟩, ⟨GateOp.or, [ia, N]⟩, ⟨GateOp.and, [N, N + 1]⟩,
    ⟨GateOp.or, [jf, N + 3]⟩, ⟨GateOp.and, [N + 2, N + 4]⟩, ⟨GateOp.or, [N + 2, N + 4]⟩,
    ⟨GateOp.not, [N + 6]⟩, ⟨GateOp.or, [N + 5, N + 7]⟩]

theorem core (x : List Bool) (N ia ib ic id ie jf : ℕ) (hx : x.length = N) (hia : ia < N) (hib : ib < N)
    (hic : ic < N) (hid : id < N) (hie : ie < N) (hjf : jf < N) :
    (run (fg N ia ib ic id ie jf) x).getD (N + 8) false
      = (((x.getD ia false || (x.getD ib false || x.getD ic false)) &&
            (x.getD jf false || ((x.getD ib false || x.getD ic false) && (x.getD id false || x.getD ie false))))
          || !((x.getD ia false || (x.getD ib false || x.getD ic false)) ||
            (x.getD jf false || ((x.getD ib false || x.getD ic false) && (x.getD id false || x.getD ie false))))) := by
  have e : run (fg N ia ib ic id ie jf) x = run (fg N ia ib ic id ie jf) (x ++ []) := by
    rw [List.append_nil]
  rw [e, run_go x N hx, val_eq x N hx]
  simp [fg, go, val, GateOp.eval, hia, hib, hic, hid, hie, hjf]

theorem main : ∀ n : ℕ, 4 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u.val = 0 ∧ v.val = 2) ∨ (1 ≤ u.val ∧ u.val + 3 ≤ n ∧ v.val ≠ 2) ∨ (n ≤ u.val + 2 ∧ v.val ≤ 2))) C := by
  intro n hn
  refine ⟨⟨fg (2 * n) 0 (n - 2) (n - 1) n (n + 1) (n + 2), 2 * n + 8⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [fg, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [Circuit.size, fg]
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    have hx := one_len u v
    show (run (fg (2 * n) 0 (n - 2) (n - 1) n (n + 1) (n + 2)) (PEqualNP.Represents.oneEach u v)).getD (2 * n + 8) false = _
    rw [core _ _ _ _ _ _ _ _ hx (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    have c0 := one_l u v 0 (by omega)
    have c1 := one_l u v (n - 2) (by omega)
    have c2 := one_l u v (n - 1) (by omega)
    have c3 := one_r u v 0 (by omega)
    have c4 := one_r u v 1 (by omega)
    have c5 := one_r u v 2 (by omega)
    rw [Nat.add_zero] at c3
    rw [c0, c1, c2, c3, c4, c5, Bool.eq_iff_iff]
    simp
    omega

end PEqualNP.Outside.L_meta_20575

theorem PEqualNP.Outside.L_meta_20575 : ∀ n : ℕ, 4 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u.val = 0 ∧ v.val = 2) ∨ (1 ≤ u.val ∧ u.val + 3 ≤ n ∧ v.val ≠ 2) ∨ (n ≤ u.val + 2 ∧ v.val ≤ 2))) C :=
  PEqualNP.Outside.L_meta_20575.main

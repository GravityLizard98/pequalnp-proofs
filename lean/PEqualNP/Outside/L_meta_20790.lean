import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20790
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

def andl (N : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => andl N k ++ [(⟨GateOp.and, [k, N + k]⟩ : Gate)]

theorem andl_len (N : ℕ) : ∀ k, (andl N k).length = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [andl, ih]

theorem andl_fan (N : ℕ) : ∀ k, ∀ g ∈ andl N k,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro g hg; simp [andl] at hg
  | succ k ih =>
    intro g hg
    simp only [andl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl
    · exact ih g h
    · simp

theorem andl_key (N : ℕ) (x : List Bool) (hx : x.length = 2 * N) : ∀ k, k ≤ N →
    (∀ i < 2 * N, (run (andl N k) x).getD i false = x.getD i false) ∧
    (∀ j < k, (run (andl N k) x).getD (2 * N + j) false = (x.getD j false && x.getD (N + j) false)) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun i _ => rfl, fun j hj => absurd hj (by omega)⟩
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hl := run_len (andl N k) x
    rw [andl_len, hx] at hl
    rw [andl, run_snoc]
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · rw [gl _ _ _ (by omega)]; exact h1 i hi
    · by_cases hjk : j < k
      · rw [gl _ _ _ (by omega)]; exact h2 j hjk
      · have e : j = k := by omega
        subst e
        rw [ge _ _ _ (by omega)]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id]
        rw [h1 j (by omega), h1 (N + j) (by omega)]

theorem main : ∀ (N : ℕ), 1 ≤ N → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.Represents.Represents (fun u v : Fin N => decide (u ≠ v)) C ∧ C.size ≤ 2 * N := by
  intro N hN
  refine ⟨⟨(andl N N ++ orch (2 * N) (3 * N) (N - 1)) ++ [(⟨GateOp.not, [res (2 * N) (3 * N) (N - 1)]⟩ : Gate)],
    3 * N + (N - 1)⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · rcases List.mem_append.1 h with h | h
      · exact andl_fan _ _ g h
      · obtain ⟨h1, h2⟩ := orch_mono _ _ _ g h
        refine ⟨?_, h2⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
        tauto
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      simp
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    have hx := one_len u v
    obtain ⟨a1, a2⟩ := andl_key N _ hx N (le_refl _)
    have hl1 := run_len (andl N N) (PEqualNP.Represents.oneEach u v)
    rw [andl_len, hx] at hl1
    have hl1' : (run (andl N N) (PEqualNP.Represents.oneEach u v)).length = 3 * N := by omega
    obtain ⟨b1, b2⟩ := orch_key (2 * N) (3 * N) _ hl1' (N - 1) (by omega)
    have hl2 := run_len (orch (2 * N) (3 * N) (N - 1)) (run (andl N N) (PEqualNP.Represents.oneEach u v))
    rw [orch_len, hl1'] at hl2
    have r1 : res (2 * N) (3 * N) (N - 1) < 3 * N + (N - 1) := by unfold res; split <;> omega
    show (run ((andl N N ++ orch (2 * N) (3 * N) (N - 1)) ++
      [(⟨GateOp.not, [res (2 * N) (3 * N) (N - 1)]⟩ : Gate)]) (PEqualNP.Represents.oneEach u v)).getD (3 * N + (N - 1)) false = _
    rw [run_snoc, run_append, ge _ _ _ (by rw [hl2])]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [b2]
    have key : ((List.range (N - 1 + 1)).any fun j =>
        (run (andl N N) (PEqualNP.Represents.oneEach u v)).getD (2 * N + j) false) = decide (u = v) := by
      rw [Bool.eq_iff_iff, List.any_eq_true]
      simp only [List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj, h⟩
        rw [a2 j (by omega), one_l u v j (by omega), one_r u v j (by omega)] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact Fin.ext (by omega)
      · intro h
        refine ⟨u.val, by omega, ?_⟩
        rw [a2 _ (by omega), one_l u v u.val (by omega), one_r u v u.val (by omega)]
        simp [h]
    rw [key]
    simp
  · simp [Circuit.size, orch_len, andl_len]; omega

end PEqualNP.Outside.L_meta_20790

theorem PEqualNP.Outside.L_meta_20790 : ∀ (N : ℕ), 1 ≤ N → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.Represents.Represents (fun u v : Fin N => decide (u ≠ v)) C ∧ C.size ≤ 2 * N :=
  PEqualNP.Outside.L_meta_20790.main

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17870

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := List.getD_append _ _ _ _ h

theorem step_eq (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold step
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem run_len (gs : List Gate) : ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih, step_len]
    simp
    omega

def build : ℕ → ℕ → List (ℕ × ℕ) → List Gate
  | _, _, [] => []
  | acc, pos, q :: rest =>
    ⟨GateOp.and, [q.1, q.2]⟩ :: ⟨GateOp.or, [acc, pos]⟩ :: build (pos + 1) (pos + 2) rest

def fin : ℕ → ℕ → List (ℕ × ℕ) → ℕ
  | acc, _, [] => acc
  | _, pos, _ :: rest => fin (pos + 1) (pos + 2) rest

theorem build_len (rest : List (ℕ × ℕ)) : ∀ acc pos, (build acc pos rest).length = 2 * rest.length := by
  induction rest with
  | nil => intro acc pos; rfl
  | cons q rest ih =>
    intro acc pos
    simp only [build, List.length_cons, ih]
    omega

theorem build_mono (rest : List (ℕ × ℕ)) : ∀ acc pos, ∀ g ∈ build acc pos rest,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction rest with
  | nil => intro acc pos g hg; simp [build] at hg
  | cons q rest ih =>
    intro acc pos g hg
    simp only [build, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact ih _ _ g hg

theorem any_congr' (r : List (ℕ × ℕ)) (f g : ℕ × ℕ → Bool) (h : ∀ q ∈ r, f q = g q) :
    r.any f = r.any g := by
  induction r with
  | nil => rfl
  | cons q r ih =>
    simp only [List.any_cons]
    rw [h q List.mem_cons_self, ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]

theorem key (rest : List (ℕ × ℕ)) : ∀ (w : List Bool) (acc pos : ℕ), w.length = pos → acc < pos →
    (∀ q ∈ rest, q.1 < pos ∧ q.2 < pos) →
    ((build acc pos rest).foldl step w).length = pos + 2 * rest.length ∧
    (∀ k, k < pos → ((build acc pos rest).foldl step w).getD k false = w.getD k false) ∧
    fin acc pos rest < pos + 2 * rest.length ∧
    ((build acc pos rest).foldl step w).getD (fin acc pos rest) false
      = (w.getD acc false || rest.any fun q => w.getD q.1 false && w.getD q.2 false) := by
  induction rest with
  | nil =>
    intro w acc pos hw hacc _
    simp [build, fin, hw, hacc]
  | cons q rest ih =>
    intro w acc pos hw hacc hq
    have hq0 := hq q List.mem_cons_self
    simp only [build, List.foldl_cons, fin]
    have hl1 : (step w ⟨GateOp.and, [q.1, q.2]⟩).length = pos + 1 := by rw [step_len, hw]
    have hl2 : (step (step w ⟨GateOp.and, [q.1, q.2]⟩) ⟨GateOp.or, [acc, pos]⟩).length = pos + 2 := by
      rw [step_len, hl1]
    have hv1 : (step w ⟨GateOp.and, [q.1, q.2]⟩).getD pos false
        = (w.getD q.1 false && w.getD q.2 false) := by
      have e := step_eq w ⟨GateOp.and, [q.1, q.2]⟩
      rw [hw] at e
      rw [e]
      simp [GateOp.eval]
    have hk1 : ∀ k, k < pos → (step w ⟨GateOp.and, [q.1, q.2]⟩).getD k false = w.getD k false :=
      fun k hk => step_lt _ _ _ (by omega)
    have hk2 : ∀ k, k < pos →
        (step (step w ⟨GateOp.and, [q.1, q.2]⟩) ⟨GateOp.or, [acc, pos]⟩).getD k false
          = w.getD k false := by
      intro k hk
      rw [step_lt _ _ _ (by omega)]
      exact hk1 k hk
    have hv2 : (step (step w ⟨GateOp.and, [q.1, q.2]⟩) ⟨GateOp.or, [acc, pos]⟩).getD (pos + 1) false
        = (w.getD acc false || (w.getD q.1 false && w.getD q.2 false)) := by
      have e := step_eq (step w ⟨GateOp.and, [q.1, q.2]⟩) ⟨GateOp.or, [acc, pos]⟩
      rw [hl1] at e
      rw [e]
      simp only [List.map_cons, List.map_nil]
      rw [hk1 acc hacc, hv1]
      simp [GateOp.eval]
    obtain ⟨h1, h2, h3, h4⟩ := ih (step (step w ⟨GateOp.and, [q.1, q.2]⟩) ⟨GateOp.or, [acc, pos]⟩)
      (pos + 1) (pos + 2) hl2 (by omega)
      (fun q' hq' => by
        have := hq q' (List.mem_cons_of_mem _ hq')
        omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1]
      simp only [List.length_cons]
      omega
    · intro k hk
      rw [h2 k (by omega)]
      exact hk2 k hk
    · simp only [List.length_cons]
      omega
    · rw [h4, hv2, List.any_cons, Bool.or_assoc]
      congr 2
      apply any_congr'
      intro q' hq'
      have := hq q' (List.mem_cons_of_mem _ hq')
      rw [hk2 _ this.1, hk2 _ this.2]

theorem main (C : Circuit) (L : List (ℕ × ℕ)) (hC : Monotone2 C) (hg : C.gates ≠ []) (hL : L ≠ [])
    (hb : ∀ p ∈ L, p.1 < 24 + C.size ∧ p.2 < 24 + C.size) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.gates.head? = C.gates.head? ∧ C.size ≤ C'.size ∧
      C'.size + 1 ≤ C.size + 2 * L.length ∧ C'.output < 24 + C'.size ∧
      ∀ x : Fin 24 → Bool,
        (∀ k, k < 24 + C.size → PEqualNP.BlindGate.wireValue C' 24 x k
          = PEqualNP.BlindGate.wireValue C 24 x k) ∧
        C'.eval (List.ofFn x) = L.any fun p => PEqualNP.BlindGate.wireValue C 24 x p.1 &&
          PEqualNP.BlindGate.wireValue C 24 x p.2 := by
  obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil hL
  have hp := hb p List.mem_cons_self
  have hsz : C.size = C.gates.length := rfl
  rw [hsz] at hp
  refine ⟨⟨C.gates ++ ⟨GateOp.and, [p.1, p.2]⟩ ::
      build (24 + C.gates.length) (24 + C.gates.length + 1) rest,
    fin (24 + C.gates.length) (24 + C.gates.length + 1) rest⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg'
    simp only [List.mem_append, List.mem_cons] at hg'
    rcases hg' with h | rfl | h
    · exact hC g h
    · simp
    · exact build_mono rest _ _ g h
  · cases hgs : C.gates with
    | nil => exact absurd hgs hg
    | cons g gs => simp
  · simp only [Circuit.size, List.length_append, List.length_cons, build_len]
    omega
  · simp only [Circuit.size, List.length_append, List.length_cons, build_len]
    omega
  · have h3 := (key rest (step (C.gates.foldl step (List.ofFn fun _ : Fin 24 => false))
        ⟨GateOp.and, [p.1, p.2]⟩) (24 + C.gates.length) (24 + C.gates.length + 1)
      (by rw [step_len, run_len]; simp) (by omega)
      (fun q hq => by
        have := hb q (List.mem_cons_of_mem _ hq)
        rw [hsz] at this
        omega)).2.2.1
    simp only [Circuit.size, List.length_append, List.length_cons, build_len]
    omega
  · intro x
    have hl0 : (C.gates.foldl step (List.ofFn x)).length = 24 + C.gates.length := by
      rw [run_len]; simp
    obtain ⟨_, h2, _, h4⟩ := key rest (step (C.gates.foldl step (List.ofFn x))
        ⟨GateOp.and, [p.1, p.2]⟩) (24 + C.gates.length) (24 + C.gates.length + 1)
      (by rw [step_len, hl0]) (by omega)
      (fun q hq => by
        have := hb q (List.mem_cons_of_mem _ hq)
        rw [hsz] at this
        omega)
    have hw : ∀ k, k < 24 + C.gates.length →
        (step (C.gates.foldl step (List.ofFn x)) ⟨GateOp.and, [p.1, p.2]⟩).getD k false
          = (C.gates.foldl step (List.ofFn x)).getD k false :=
      fun k hk => step_lt _ _ _ (by rw [hl0]; exact hk)
    have hwires : (⟨C.gates ++ ⟨GateOp.and, [p.1, p.2]⟩ ::
          build (24 + C.gates.length) (24 + C.gates.length + 1) rest,
        fin (24 + C.gates.length) (24 + C.gates.length + 1) rest⟩ : Circuit).wires (List.ofFn x)
        = (build (24 + C.gates.length) (24 + C.gates.length + 1) rest).foldl step
          (step (C.gates.foldl step (List.ofFn x)) ⟨GateOp.and, [p.1, p.2]⟩) := by
      show List.foldl step _ _ = _
      rw [List.foldl_append, List.foldl_cons]
    have hwC : C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
    refine ⟨?_, ?_⟩
    · intro k hk
      rw [hsz] at hk
      unfold PEqualNP.BlindGate.wireValue
      rw [hwires, hwC, h2 k (by omega)]
      exact hw k hk
    · unfold PEqualNP.BlindGate.wireValue Circuit.eval
      rw [hwires, hwC]
      simp only []
      rw [h4, List.any_cons]
      have e := step_eq (C.gates.foldl step (List.ofFn x)) ⟨GateOp.and, [p.1, p.2]⟩
      rw [hl0] at e
      rw [e]
      simp only [List.map_cons, List.map_nil]
      congr 1
      · simp [GateOp.eval]
      · apply any_congr'
        intro q hq
        have := hb q (List.mem_cons_of_mem _ hq)
        rw [hsz] at this
        rw [hw _ this.1, hw _ this.2]

end PEqualNP.Outside.L_meta_17870

theorem PEqualNP.Outside.L_meta_17870 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → x1.gates ≠ [] → x2 ≠ [] → (∀ x6 ∈ x2, x6.1 < (24 : ℕ) + x1.size ∧ x6.2 < (24 : ℕ) + x1.size) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.gates.head? = x1.gates.head? ∧ x1.size ≤ x7.size ∧ x7.size + (1 : ℕ) ≤ x1.size + (2 : ℕ) * x2.length ∧ x7.output < (24 : ℕ) + x7.size ∧ ∀ (x8 : Fin (24 : ℕ) → Bool), (∀ x9 < (24 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x7 (24 : ℕ) x8 x9 = PEqualNP.BlindGate.wireValue x1 (24 : ℕ) x8 x9) ∧ x7.eval (List.ofFn x8) = x2.any fun (x9 : ℕ × ℕ) => PEqualNP.BlindGate.wireValue x1 (24 : ℕ) x8 x9.1 && PEqualNP.BlindGate.wireValue x1 (24 : ℕ) x8 x9.2 := by
  intro C L hC hg hL hb
  exact PEqualNP.Outside.L_meta_17870.main C L hC hg hL hb

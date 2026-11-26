import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17912

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

theorem run_lt (gs : List Gate) : ∀ (w : List Bool) (k : ℕ), k < w.length →
    (gs.foldl step w).getD k false = w.getD k false := by
  induction gs with
  | nil => intro w k _; rfl
  | cons g gs ih =>
    intro w k hk
    simp only [List.foldl_cons]
    rw [ih _ k (by rw [step_len]; omega), step_lt _ _ _ hk]

def sgates (pos : ℕ) (s : ℕ × ℕ × ℕ × ℕ × ℕ) : List Gate :=
  [⟨GateOp.or, [s.2.1, s.2.2.1]⟩, ⟨GateOp.or, [pos, s.2.2.2.1]⟩, ⟨GateOp.or, [pos + 1, s.2.2.2.2]⟩,
    ⟨GateOp.and, [s.1, pos + 2]⟩]

def sval (w : List Bool) (s : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  w.getD s.1 false && (w.getD s.2.1 false || w.getD s.2.2.1 false || w.getD s.2.2.2.1 false ||
    w.getD s.2.2.2.2 false)

def slt (pos : ℕ) (s : ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  s.1 < pos ∧ s.2.1 < pos ∧ s.2.2.1 < pos ∧ s.2.2.2.1 < pos ∧ s.2.2.2.2 < pos

theorem sgates_run (w : List Bool) (pos : ℕ) (s : ℕ × ℕ × ℕ × ℕ × ℕ) (hw : w.length = pos)
    (hs : slt pos s) :
    ((sgates pos s).foldl step w).length = pos + 4 ∧
    (∀ k, k < pos → ((sgates pos s).foldl step w).getD k false = w.getD k false) ∧
    ((sgates pos s).foldl step w).getD (pos + 3) false = sval w s := by
  obtain ⟨p, l1, l2, l3, l4⟩ := s
  obtain ⟨h0, h1, h2, h3, h4⟩ := hs
  simp only at h0 h1 h2 h3 h4
  simp only [sgates, List.foldl_cons, List.foldl_nil]
  have e1 := step_eq w ⟨GateOp.or, [l1, l2]⟩
  have n1 : (step w ⟨GateOp.or, [l1, l2]⟩).length = pos + 1 := by rw [step_len, hw]
  have e2 := step_eq (step w ⟨GateOp.or, [l1, l2]⟩) ⟨GateOp.or, [pos, l3]⟩
  have n2 : (step (step w ⟨GateOp.or, [l1, l2]⟩) ⟨GateOp.or, [pos, l3]⟩).length = pos + 2 := by
    rw [step_len, n1]
  have e3 := step_eq (step (step w ⟨GateOp.or, [l1, l2]⟩) ⟨GateOp.or, [pos, l3]⟩)
    ⟨GateOp.or, [pos + 1, l4]⟩
  have n3 : (step (step (step w ⟨GateOp.or, [l1, l2]⟩) ⟨GateOp.or, [pos, l3]⟩)
      ⟨GateOp.or, [pos + 1, l4]⟩).length = pos + 3 := by rw [step_len, n2]
  have e4 := step_eq (step (step (step w ⟨GateOp.or, [l1, l2]⟩) ⟨GateOp.or, [pos, l3]⟩)
    ⟨GateOp.or, [pos + 1, l4]⟩) ⟨GateOp.and, [p, pos + 2]⟩
  rw [hw] at e1
  rw [n1] at e2
  rw [n2] at e3
  rw [n3] at e4
  have k1 : ∀ k, k < pos → (step w ⟨GateOp.or, [l1, l2]⟩).getD k false = w.getD k false :=
    fun k hk => step_lt _ _ _ (by omega)
  have k2 : ∀ k, k < pos →
      (step (step w ⟨GateOp.or, [l1, l2]⟩) ⟨GateOp.or, [pos, l3]⟩).getD k false = w.getD k false :=
    fun k hk => by rw [step_lt _ _ _ (by omega)]; exact k1 k hk
  have k3 : ∀ k, k < pos →
      (step (step (step w ⟨GateOp.or, [l1, l2]⟩) ⟨GateOp.or, [pos, l3]⟩)
        ⟨GateOp.or, [pos + 1, l4]⟩).getD k false = w.getD k false :=
    fun k hk => by rw [step_lt _ _ _ (by omega)]; exact k2 k hk
  refine ⟨by rw [step_len, n3], ?_, ?_⟩
  · intro k hk
    rw [step_lt _ _ _ (by omega)]
    exact k3 k hk
  · rw [e4]
    simp only [List.map_cons, List.map_nil]
    rw [k3 p h0, e3]
    simp only [List.map_cons, List.map_nil]
    rw [k2 l4 h4, e2]
    simp only [List.map_cons, List.map_nil]
    rw [k1 l3 h3, e1]
    simp only [List.map_cons, List.map_nil]
    simp [GateOp.eval, sval]

def build : ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ) → List Gate
  | _, _, [] => []
  | acc, pos, s :: rest =>
    sgates pos s ++ ⟨GateOp.or, [acc, pos + 3]⟩ :: build (pos + 4) (pos + 5) rest

def fin : ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ
  | acc, _, [] => acc
  | _, pos, _ :: rest => fin (pos + 4) (pos + 5) rest

theorem build_len (rest : List (ℕ × ℕ × ℕ × ℕ × ℕ)) :
    ∀ acc pos, (build acc pos rest).length = 5 * rest.length := by
  induction rest with
  | nil => intro acc pos; rfl
  | cons q rest ih =>
    intro acc pos
    simp only [build, sgates, List.length_cons, List.length_append, ih, List.length_nil]
    omega

theorem sgates_mono (pos : ℕ) (s : ℕ × ℕ × ℕ × ℕ × ℕ) : ∀ g ∈ sgates pos s,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [sgates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem build_mono (rest : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : ∀ acc pos, ∀ g ∈ build acc pos rest,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction rest with
  | nil => intro acc pos g hg; simp [build] at hg
  | cons q rest ih =>
    intro acc pos g hg
    simp only [build, List.mem_append, List.mem_cons] at hg
    rcases hg with hg | rfl | hg
    · exact sgates_mono pos q g hg
    · simp
    · exact ih _ _ g hg

theorem any_congr' (r : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (f g : ℕ × ℕ × ℕ × ℕ × ℕ → Bool)
    (h : ∀ q ∈ r, f q = g q) : r.any f = r.any g := by
  induction r with
  | nil => rfl
  | cons q r ih =>
    simp only [List.any_cons]
    rw [h q List.mem_cons_self, ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]

theorem sval_congr (w w' : List Bool) (pos : ℕ) (s : ℕ × ℕ × ℕ × ℕ × ℕ) (hs : slt pos s)
    (h : ∀ k, k < pos → w'.getD k false = w.getD k false) : sval w' s = sval w s := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hs
  unfold sval
  rw [h _ h0, h _ h1, h _ h2, h _ h3, h _ h4]

theorem key (rest : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : ∀ (w : List Bool) (acc pos : ℕ), w.length = pos →
    acc < pos → (∀ q ∈ rest, slt 26 q) → 26 ≤ pos →
    ((build acc pos rest).foldl step w).length = pos + 5 * rest.length ∧
    (∀ k, k < pos → ((build acc pos rest).foldl step w).getD k false = w.getD k false) ∧
    fin acc pos rest < pos + 5 * rest.length ∧ acc ≤ fin acc pos rest ∧
    ((build acc pos rest).foldl step w).getD (fin acc pos rest) false
      = (w.getD acc false || rest.any fun q => sval w q) := by
  induction rest with
  | nil =>
    intro w acc pos hw hacc _ _
    simp [build, fin, hw, hacc]
  | cons q rest ih =>
    intro w acc pos hw hacc hq hpos
    have hq0 : slt pos q := by
      obtain ⟨h0, h1, h2, h3, h4⟩ := hq q List.mem_cons_self
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    simp only [build, List.foldl_append, List.foldl_cons, fin]
    obtain ⟨s1, s2, s3⟩ := sgates_run w pos q hw hq0
    have e := step_eq ((sgates pos q).foldl step w) ⟨GateOp.or, [acc, pos + 3]⟩
    rw [s1] at e
    have hl : (step ((sgates pos q).foldl step w) ⟨GateOp.or, [acc, pos + 3]⟩).length = pos + 5 := by
      rw [step_len, s1]
    have hk : ∀ k, k < pos →
        (step ((sgates pos q).foldl step w) ⟨GateOp.or, [acc, pos + 3]⟩).getD k false
          = w.getD k false := by
      intro k hk
      rw [step_lt _ _ _ (by omega)]
      exact s2 k hk
    obtain ⟨h1, h2, h3, h3', h4⟩ := ih (step ((sgates pos q).foldl step w) ⟨GateOp.or, [acc, pos + 3]⟩)
      (pos + 4) (pos + 5) hl (by omega) (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq')) (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h1]
      simp only [List.length_cons]
      omega
    · intro k hk'
      rw [h2 k (by omega)]
      exact hk k hk'
    · simp only [List.length_cons]
      omega
    · omega
    · rw [h4, e]
      simp only [List.map_cons, List.map_nil]
      rw [s2 acc hacc, s3, List.any_cons]
      have : (rest.any fun q' => sval (step ((sgates pos q).foldl step w)
          ⟨GateOp.or, [acc, pos + 3]⟩) q') = rest.any fun q' => sval w q' := by
        apply any_congr'
        intro q' hq'
        obtain ⟨h0, h1, h2, h3, h4⟩ := hq q' (List.mem_cons_of_mem _ hq')
        exact sval_congr _ _ pos q' ⟨by omega, by omega, by omega, by omega, by omega⟩ hk
      rw [this]
      simp [GateOp.eval, Bool.or_assoc]

def xin (A B : Finset (Fin 13)) : List Bool :=
  List.ofFn fun (i : Fin 26) =>
    if (i : ℕ) < 13 then decide (Fin.ofNat 13 (i : ℕ) ∈ A) else decide (Fin.ofNat 13 (i : ℕ) ∈ B)

theorem xpt (A B : Finset (Fin 13)) (p : Fin 13) :
    (xin A B).getD (p : ℕ) false = decide (p ∈ A) := by
  unfold xin
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have hp := p.isLt
  simp [hp]

theorem xln (A B : Finset (Fin 13)) (l : Fin 13) :
    (xin A B).getD (13 + (l : ℕ)) false = decide (l ∈ B) := by
  unfold xin
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have hl := l.isLt
  have e : Fin.ofNat 13 (13 + (l : ℕ)) = l := by
    apply Fin.ext
    simp [Fin.ofNat]
  rw [if_neg (show ¬ (13 + (l : ℕ) < 13) by omega)]
  show decide (Fin.ofNat 13 (13 + (l : ℕ)) ∈ B) = _
  rw [e]

def STN : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [(4, 18, 22, 23, 25), (5, 17, 21, 22, 24), (7, 15, 19, 20, 22), (8, 14, 18, 19, 21), (9, 13, 17, 18, 20), (10, 16, 17, 19, 25), (11, 15, 16, 18, 24), (12, 14, 15, 17, 23)]

def SF : List (Fin 13 × List (Fin 13)) := [((4 : Fin 13), [(5 : Fin 13), 9, 10, 12]), ((5 : Fin 13), [(4 : Fin 13), 8, 9, 11]), ((7 : Fin 13), [(2 : Fin 13), 6, 7, 9]), ((8 : Fin 13), [(1 : Fin 13), 5, 6, 8]), ((9 : Fin 13), [(0 : Fin 13), 4, 5, 7]), ((10 : Fin 13), [(3 : Fin 13), 4, 6, 12]), ((11 : Fin 13), [(2 : Fin 13), 3, 5, 11]), ((12 : Fin 13), [(1 : Fin 13), 2, 4, 10])]

theorem rel : ∀ p l : Fin 13, (∃ s ∈ SF, s.1 = p ∧ l ∈ s.2) ↔
    ((p : ℕ) ∉ [0, 1, 2, 3, 6] ∧ ((p : ℕ) + (l : ℕ)) % 13 ∈ [0, 1, 3, 9]) := by
  decide

theorem sem (S : List (Fin 13 × List (Fin 13))) (A B : Finset (Fin 13)) :
    (S.any fun s => decide (s.1 ∈ A) && s.2.any fun l => decide (l ∈ B))
      = decide (∃ p ∈ A, ∃ l ∈ B, ∃ s ∈ S, s.1 = p ∧ l ∈ s.2) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, hp, l, hl, hlB⟩
    exact ⟨s.1, hp, l, hlB, s, hs, rfl, hl⟩
  · rintro ⟨p, hp, l, hl, s, hs, rfl, hsl⟩
    exact ⟨s, hs, hp, l, hsl, hl⟩

theorem STN_lt : ∀ q ∈ STN, slt 26 q := by
  unfold slt
  decide

theorem main (C : Circuit) (hC : Monotone2 C) (hs : C.size ≤ 23) (ho : C.output < 26 + C.size) :
    ∃ (C' : Circuit) (o : ℕ), Monotone2 C' ∧ C'.size ≤ 62 ∧ C.output < o ∧
      ∀ A B : Finset (Fin 13),
        (C'.wires (xin A B)).getD C.output false = C.eval (xin A B) ∧
        (C'.wires (xin A B)).getD o false = decide (∃ p ∈ A, (p : ℕ) ∉ [0, 1, 2, 3, 6] ∧
          ∃ l ∈ B, ((p : ℕ) + (l : ℕ)) % 13 ∈ [0, 1, 3, 9]) := by
  have hsz : C.size = C.gates.length := rfl
  rw [hsz] at hs ho
  refine ⟨⟨C.gates ++ (sgates (26 + C.gates.length) (4, 18, 22, 23, 25) ++
      build (26 + C.gates.length + 3) (26 + C.gates.length + 4) STN.tail), 0⟩,
    fin (26 + C.gates.length + 3) (26 + C.gates.length + 4) STN.tail, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with h | h | h
    · exact hC g h
    · exact sgates_mono _ _ g h
    · exact build_mono _ _ _ g h
  · simp only [Circuit.size, List.length_append, build_len, sgates, List.length_cons,
      List.length_nil, STN, List.tail_cons]
    omega
  · have hx : (List.ofFn fun _ : Fin 26 => false).length = 26 := by simp
    have h0 : (C.gates.foldl step (List.ofFn fun _ : Fin 26 => false)).length
        = 26 + C.gates.length := by rw [run_len, hx]
    obtain ⟨s1, _, _⟩ := sgates_run _ (26 + C.gates.length) (4, 18, 22, 23, 25) h0 (by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> omega)
    have h3 := (key STN.tail _ (26 + C.gates.length + 3) (26 + C.gates.length + 4) s1 (by omega)
      (fun q hq => STN_lt q (List.mem_of_mem_tail hq)) (by omega)).2.2.2.1
    omega
  · intro A B
    have hx : (xin A B).length = 26 := by simp [xin]
    have h0 : (C.gates.foldl step (xin A B)).length = 26 + C.gates.length := by rw [run_len, hx]
    have hin : ∀ k, k < 26 → (C.gates.foldl step (xin A B)).getD k false = (xin A B).getD k false :=
      fun k hk => run_lt _ _ k (by rw [hx]; exact hk)
    have hF : slt (26 + C.gates.length) (4, 18, 22, 23, 25) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> omega
    obtain ⟨s1, s2, s3⟩ := sgates_run _ (26 + C.gates.length) (4, 18, 22, 23, 25) h0 hF
    obtain ⟨_, h2, _, _, h4⟩ := key STN.tail _ (26 + C.gates.length + 3) (26 + C.gates.length + 4)
      s1 (by omega) (fun q hq => STN_lt q (List.mem_of_mem_tail hq)) (by omega)
    have hwires : (⟨C.gates ++ (sgates (26 + C.gates.length) (4, 18, 22, 23, 25) ++
        build (26 + C.gates.length + 3) (26 + C.gates.length + 4) STN.tail), 0⟩ : Circuit).wires
          (xin A B)
        = (build (26 + C.gates.length + 3) (26 + C.gates.length + 4) STN.tail).foldl step
          ((sgates (26 + C.gates.length) (4, 18, 22, 23, 25)).foldl step (C.gates.foldl step (xin A B))) := by
      show List.foldl step _ _ = _
      rw [List.foldl_append, List.foldl_append]
    rw [hwires]
    refine ⟨?_, ?_⟩
    · rw [h2 _ (by omega), s2 _ ho]
      rfl
    · rw [h4, s3]
      have hc : ∀ q, slt 26 q →
          sval ((sgates (26 + C.gates.length) (4, 18, 22, 23, 25)).foldl step (C.gates.foldl step (xin A B))) q
            = sval (xin A B) q := by
        intro q hq
        obtain ⟨q0, q1, q2, q3, q4⟩ := hq
        rw [sval_congr _ _ (26 + C.gates.length) q ⟨by omega, by omega, by omega, by omega, by omega⟩ s2]
        exact sval_congr _ _ 26 q ⟨q0, q1, q2, q3, q4⟩ hin
      rw [any_congr' STN.tail _ (fun q => sval (xin A B) q)
        (fun q hq => hc q (STN_lt q (List.mem_of_mem_tail hq)))]
      rw [sval_congr _ _ 26 (4, 18, 22, 23, 25) (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp) hin]
      have hall : (sval (xin A B) (4, 18, 22, 23, 25) || STN.tail.any fun q => sval (xin A B) q)
          = SF.any fun s => decide (s.1 ∈ A) && s.2.any fun l => decide (l ∈ B) := by
        have a4 : (xin A B).getD 4 false = decide ((4 : Fin 13) ∈ A) := xpt A B 4
        have a5 : (xin A B).getD 5 false = decide ((5 : Fin 13) ∈ A) := xpt A B 5
        have a7 : (xin A B).getD 7 false = decide ((7 : Fin 13) ∈ A) := xpt A B 7
        have a8 : (xin A B).getD 8 false = decide ((8 : Fin 13) ∈ A) := xpt A B 8
        have a9 : (xin A B).getD 9 false = decide ((9 : Fin 13) ∈ A) := xpt A B 9
        have a10 : (xin A B).getD 10 false = decide ((10 : Fin 13) ∈ A) := xpt A B 10
        have a11 : (xin A B).getD 11 false = decide ((11 : Fin 13) ∈ A) := xpt A B 11
        have a12 : (xin A B).getD 12 false = decide ((12 : Fin 13) ∈ A) := xpt A B 12
        have b0 : (xin A B).getD 13 false = decide ((0 : Fin 13) ∈ B) := xln A B 0
        have b1 : (xin A B).getD 14 false = decide ((1 : Fin 13) ∈ B) := xln A B 1
        have b2 : (xin A B).getD 15 false = decide ((2 : Fin 13) ∈ B) := xln A B 2
        have b3 : (xin A B).getD 16 false = decide ((3 : Fin 13) ∈ B) := xln A B 3
        have b4 : (xin A B).getD 17 false = decide ((4 : Fin 13) ∈ B) := xln A B 4
        have b5 : (xin A B).getD 18 false = decide ((5 : Fin 13) ∈ B) := xln A B 5
        have b6 : (xin A B).getD 19 false = decide ((6 : Fin 13) ∈ B) := xln A B 6
        have b7 : (xin A B).getD 20 false = decide ((7 : Fin 13) ∈ B) := xln A B 7
        have b8 : (xin A B).getD 21 false = decide ((8 : Fin 13) ∈ B) := xln A B 8
        have b9 : (xin A B).getD 22 false = decide ((9 : Fin 13) ∈ B) := xln A B 9
        have b10 : (xin A B).getD 23 false = decide ((10 : Fin 13) ∈ B) := xln A B 10
        have b11 : (xin A B).getD 24 false = decide ((11 : Fin 13) ∈ B) := xln A B 11
        have b12 : (xin A B).getD 25 false = decide ((12 : Fin 13) ∈ B) := xln A B 12
        simp only [STN, SF, List.tail_cons, List.any_cons, List.any_nil, sval, Bool.or_false,
          a4, a5, a7, a8, a9, a10, a11, a12, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, Bool.or_assoc]
      rw [hall, sem]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨p, hp, l, hl, h⟩
        exact ⟨p, hp, ((rel p l).mp h).1, l, hl, ((rel p l).mp h).2⟩
      · rintro ⟨p, hp, h1, l, hl, h2⟩
        exact ⟨p, hp, l, hl, (rel p l).mpr ⟨h1, h2⟩⟩

end PEqualNP.Outside.L_meta_17912

theorem PEqualNP.Outside.L_meta_17912 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x4 : Fin (26 : ℕ)) => if ↑x4 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x2) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x3); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (23 : ℕ) → x3.output < (26 : ℕ) + x3.size → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ (62 : ℕ) ∧ x3.output < x8 ∧ ∀ (x9 x10 : Finset (Fin (13 : ℕ))), (x7.wires (x2 x9 x10)).getD x3.output Bool.false = x3.eval (x2 x9 x10) ∧ (x7.wires (x2 x9 x10)).getD x8 Bool.false = Decidable.decide (∃ x11 ∈ x9, ↑x11 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)] ∧ ∃ x12 ∈ x10, x1 x11 x12) := by
  intro x1 x2 C hC hs ho
  exact PEqualNP.Outside.L_meta_17912.main C hC hs ho

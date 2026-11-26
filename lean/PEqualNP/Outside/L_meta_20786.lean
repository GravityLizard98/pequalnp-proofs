import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20786
open PEqualNP.CircuitLowerBounds

def run (G : List Gate) (x : List Bool) : List Bool :=
  G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_append (G H : List Gate) (x : List Bool) : run (G ++ H) x = run H (run G x) := by
  simp [run, List.foldl_append]

theorem run_snoc (G : List Gate) (g : Gate) (x : List Bool) :
    run (G ++ [g]) x = run G x ++ [g.op.eval (g.inputs.map fun i => (run G x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_len (G : List Gate) (x : List Bool) : (run G x).length = x.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton G g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem gl (l : List Bool) (v : Bool) (i : ℕ) (h : i < l.length) : (l ++ [v]).getD i false = l.getD i false :=
  List.getD_append _ _ _ _ h

theorem ge (l : List Bool) (v : Bool) (k : ℕ) (h : k = l.length) : (l ++ [v]).getD k false = v := by
  subst h; simp

def P (n k : ℕ) : ℕ := if k = 0 then 0 else n + 4 * k - 1

def xch (n : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => xch n k ++ [(⟨GateOp.or, [P n k, k + 1]⟩ : Gate), ⟨GateOp.and, [P n k, k + 1]⟩,
      ⟨GateOp.not, [n + 4 * k + 1]⟩, ⟨GateOp.and, [n + 4 * k, n + 4 * k + 2]⟩]

theorem xch_len (n : ℕ) : ∀ k, (xch n k).length = 4 * k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [xch, ih]; omega

theorem xch_fan (n : ℕ) : ∀ k, ∀ g ∈ xch n k,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro g hg; simp [xch] at hg
  | succ k ih =>
    intro g hg
    simp only [xch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl | rfl | rfl
    · exact ih g h
    · simp
    · simp
    · simp
    · simp

theorem xkey (n : ℕ) (x : List Bool) (hx : x.length = n) : ∀ k, k < n →
    (∀ i < n, (run (xch n k) x).getD i false = x.getD i false) ∧
    (run (xch n k) x).getD (P n k) false = decide (((x.take (k + 1)).count true) % 2 = 1) := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨fun i _ => rfl, ?_⟩
    show x.getD 0 false = _
    match x, hx with
    | a :: l, _ => cases a <;> simp
    | [], hx => simp at hx; omega
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hl := run_len (xch n k) x
    rw [xch_len, hx] at hl
    have hP : P n k < n + 4 * k := by unfold P; split <;> omega
    rw [xch, run_append]
    generalize run (xch n k) x = W at h1 h2 hl
    have e : run [(⟨GateOp.or, [P n k, k + 1]⟩ : Gate), ⟨GateOp.and, [P n k, k + 1]⟩,
        ⟨GateOp.not, [n + 4 * k + 1]⟩, ⟨GateOp.and, [n + 4 * k, n + 4 * k + 2]⟩] W =
        (((W ++ [W.getD (P n k) false || W.getD (k + 1) false]) ++
          [W.getD (P n k) false && W.getD (k + 1) false]) ++
          [!(W.getD (P n k) false && W.getD (k + 1) false)]) ++
          [(W.getD (P n k) false || W.getD (k + 1) false) &&
            !(W.getD (P n k) false && W.getD (k + 1) false)] := by
      have hk1 : k + 1 < n + 4 * k := by omega
      simp only [run, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval,
        List.any_cons, List.any_nil, List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id,
        List.headD_cons, getD_snoc, List.length_append, List.length_singleton, hl]
      simp only [hP, hk1, if_true]
      split_ifs <;> first | rfl | omega
    rw [e]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [gl _ _ _ (by simp; omega), gl _ _ _ (by simp; omega), gl _ _ _ (by simp; omega),
        gl _ _ _ (by omega)]
      exact h1 i hi
    · have eP : P n (k + 1) = n + 4 * k + 3 := by simp [P]; omega
      rw [eP, ge _ _ _ (by simp; omega), h2, h1 (k + 1) (by omega)]
      have ht : x.take (k + 1 + 1) = x.take (k + 1) ++ [x.getD (k + 1) false] := by
        rw [List.take_add_one, List.getD_eq_getElem?_getD]
        have : x[k + 1]? = some x[k + 1] := List.getElem?_eq_getElem (by omega)
        simp [this]
      rw [ht, List.count_append]
      generalize (x.take (k + 1)).count true = c
      cases x.getD (k + 1) false
      · simp
      · by_cases hc : c % 2 = 1
        · simp [hc]; omega
        · simp [hc]; omega

theorem main : ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((List.ofFn x).count true % 2 = 1)) (4 * (n - 1)) := by
  intro n hn
  refine ⟨⟨xch n (n - 1), P n (n - 1)⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact xch_fan n (n - 1) g hg
  · simp [Circuit.size, xch_len]
  · intro x
    have hx : (List.ofFn x).length = n := by simp
    obtain ⟨_, h2⟩ := xkey n (List.ofFn x) hx (n - 1) (by omega)
    show (run (xch n (n - 1)) (List.ofFn x)).getD (P n (n - 1)) false = _
    rw [h2, List.take_of_length_le (by rw [hx]; omega)]

set_option maxRecDepth 100000 in
theorem tab : ∀ x : Fin 5 → Bool, decide ((List.ofFn x).count true % 2 = 1) =
    (2523490710 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x) := by
  decide +kernel

end PEqualNP.Outside.L_meta_20786

theorem PEqualNP.Outside.L_meta_20786 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (2523490710 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 16 := by
  obtain ⟨C, hf, hs, hev⟩ := PEqualNP.Outside.L_meta_20786.main 5 (by omega)
  exact ⟨C, hf, hs, fun x => (hev x).trans (PEqualNP.Outside.L_meta_20786.tab x)⟩

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17846

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

def mu (n : ℕ) (V : ℕ → ℕ) (i : ℕ) : ℕ := if i < n then V i else i

def gate (n : ℕ) (V A B : ℕ → ℕ) (op : ℕ → GateOp) (j : ℕ) : Gate :=
  ⟨op j, [mu n V (A j), mu n V (B j)]⟩

theorem inv (n m : ℕ) (F : ℕ → (Fin n → Bool) → Bool) (V A B : ℕ → ℕ) (op : ℕ → GateOp)
    (hV : ∀ i, i < n → V i < n ∧ ∀ x : Fin n → Bool, F i x = (List.ofFn x).getD (V i) false)
    (hA : ∀ j, j < m → A j < n + j) (hB : ∀ j, j < m → B j < n + j)
    (hop : ∀ j, j < m → ∀ x : Fin n → Bool, F (n + j) x = (op j).eval [F (A j) x, F (B j) x])
    (x : Fin n → Bool) : ∀ t, t ≤ m →
      (((List.range t).map (gate n V A B op)).foldl step (List.ofFn x)).length = n + t ∧
      ∀ i, i < n + t →
        (((List.range t).map (gate n V A B op)).foldl step (List.ofFn x)).getD (mu n V i) false
          = F i x := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    intro i hi
    have hi' : i < n := by omega
    simp only [List.range_zero, List.map_nil, List.foldl_nil, mu, if_pos hi']
    exact ((hV i hi').2 x).symm
  | succ t ih =>
    intro ht
    obtain ⟨hlen, hval⟩ := ih (by omega)
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    have hmu : ∀ i, i < n + t → mu n V i < n + t := by
      intro i hi
      unfold mu
      split_ifs with h
      · have := (hV i h).1
        omega
      · exact hi
    refine ⟨by simp [step, hlen]; omega, ?_⟩
    intro i hi
    rcases Nat.lt_or_ge i (n + t) with h | h
    · rw [step_lt _ _ _ (by rw [hlen]; exact hmu i h)]
      exact hval i h
    · have hit : i = n + t := by omega
      subst hit
      have hmi : mu n V (n + t) = n + t := by
        unfold mu
        rw [if_neg (by omega)]
      have e := step_eq (((List.range t).map (gate n V A B op)).foldl step (List.ofFn x))
        (gate n V A B op t)
      rw [hlen] at e
      rw [hmi, e]
      simp only [gate, List.map_cons, List.map_nil]
      rw [hval _ (hA t (by omega)), hval _ (hB t (by omega))]
      exact (hop t (by omega) x).symm

theorem main (n m k : ℕ) (F : ℕ → (Fin n → Bool) → Bool) (hk : k < n + m)
    (h1 : ∀ i, i < n → ∃ v : Fin n, ∀ x : Fin n → Bool, F i x = x v)
    (h2 : ∀ j, j < m → ∃ a, a < n + j ∧ ∃ b, b < n + j ∧
      ((∀ x : Fin n → Bool, F (n + j) x = (F a x && F b x)) ∨
        ∀ x : Fin n → Bool, F (n + j) x = (F a x || F b x))) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ m ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F k x := by
  classical
  have h1' : ∀ i, ∃ v : ℕ, i < n →
      v < n ∧ ∀ x : Fin n → Bool, F i x = (List.ofFn x).getD v false := by
    intro i
    by_cases hi : i < n
    · obtain ⟨v, hv⟩ := h1 i hi
      refine ⟨v, fun _ => ⟨v.isLt, fun x => ?_⟩⟩
      rw [hv x, List.getD_eq_getElem _ _ (by simp)]
      simp
    · exact ⟨0, fun h => absurd h hi⟩
  choose V hV using h1'
  have h2' : ∀ j, ∃ a b : ℕ, j < m → a < n + j ∧ b < n + j ∧
      ((∀ x : Fin n → Bool, F (n + j) x = (F a x && F b x)) ∨
        ∀ x : Fin n → Bool, F (n + j) x = (F a x || F b x)) := by
    intro j
    by_cases hj : j < m
    · obtain ⟨a, ha, b, hb, h⟩ := h2 j hj
      exact ⟨a, b, fun _ => ⟨ha, hb, h⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose A B hAB using h2'
  let op : ℕ → GateOp := fun j =>
    if ∀ x : Fin n → Bool, F (n + j) x = (F (A j) x && F (B j) x) then GateOp.and else GateOp.or
  have hop : ∀ j, j < m → ∀ x : Fin n → Bool,
      F (n + j) x = (op j).eval [F (A j) x, F (B j) x] := by
    intro j hj x
    by_cases hc : ∀ x : Fin n → Bool, F (n + j) x = (F (A j) x && F (B j) x)
    · have : op j = GateOp.and := if_pos hc
      rw [this, hc x]
      simp [GateOp.eval]
    · have : op j = GateOp.or := if_neg hc
      rw [this]
      rcases (hAB j hj).2.2 with h | h
      · exact absurd h hc
      · rw [h x]
        simp [GateOp.eval]
  refine ⟨⟨(List.range m).map (gate n V A B op), mu n V k⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
    refine ⟨?_, by simp [gate]⟩
    by_cases hc : ∀ x : Fin n → Bool, F (n + j) x = (F (A j) x && F (B j) x)
    · have : op j = GateOp.and := if_pos hc
      simp [gate, this]
    · have : op j = GateOp.or := if_neg hc
      simp [gate, this]
  · simp [Circuit.size]
  · intro x
    exact (inv n m F V A B op hV (fun j hj => (hAB j hj).1) (fun j hj => (hAB j hj).2.1) hop x m
      le_rfl).2 k hk

end PEqualNP.Outside.L_meta_17846

theorem PEqualNP.Outside.L_meta_17846 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → (Fin x1 → Bool) → Bool), x3 < x1 + x2 → (∀ x6 < x1, ∃ (x8 : Fin x1), ∀ (x9 : Fin x1 → Bool), x4 x6 x9 = x9 x8) → (∀ x7 < x2, ∃ x9 < x1 + x7, ∃ x10 < x1 + x7, (∀ (x11 : Fin x1 → Bool), x4 (x1 + x7) x11 = (x4 x9 x11 && x4 x10 x11)) ∨ ∀ (x11 : Fin x1 → Bool), x4 (x1 + x7) x11 = (x4 x9 x11 || x4 x10 x11)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x2 ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4 x3 x9 := by
  intro n m k F hk h1 h2
  exact PEqualNP.Outside.L_meta_17846.main n m k F hk h1
    (fun j hj => by
      obtain ⟨a, ha, b, hb, h⟩ := h2 j hj
      exact ⟨a, ha, b, hb, h⟩)

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17979

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_getD (w : List Bool) (g : Gate) (i : ℕ) : (step w g).getD i false =
    if i < w.length then w.getD i false
    else if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold step
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · rw [List.getD_append_right _ _ _ _ (by omega), h2]
    simp
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem any_or (l : List ℕ) (f g : ℕ → Bool) :
    (l.any fun i => f i || g i) = (l.any f || l.any g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, ih]
    cases f a <;> cases g a <;> cases l.any f <;> cases l.any g <;> rfl

theorem add_run (gs : List Gate) : ∀ (w w1 w2 : List Bool),
    (∀ g ∈ gs, g.op = GateOp.or) → w.length = w1.length → w.length = w2.length →
    (∀ i, w.getD i false = (w1.getD i false || w2.getD i false)) →
    ∀ i, (gs.foldl step w).getD i false
      = ((gs.foldl step w1).getD i false || (gs.foldl step w2).getD i false) := by
  induction gs with
  | nil => intro w w1 w2 _ _ _ h i; simpa using h i
  | cons g gs ih =>
    intro w w1 w2 hall h1 h2 h
    simp only [List.foldl_cons]
    apply ih (step w g) (step w1 g) (step w2 g) (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg'))
      (by simp [step, h1]) (by simp [step, h2])
    intro i
    rw [step_getD, step_getD, step_getD, ← h1, ← h2]
    split_ifs with c1 c2
    · exact h i
    · rw [hall g List.mem_cons_self]
      simp only [GateOp.eval, List.any_map]
      have : (fun i => w.getD i false) = fun i => (w1.getD i false || w2.getD i false) := funext h
      have e := any_or g.inputs (fun i => w1.getD i false) (fun i => w2.getD i false)
      simp only [Function.comp_def, id] at e ⊢
      rw [this]
      exact e
    · rfl

theorem main (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hf : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ (p : Fin 13) (l : Fin 13),
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ p ≠ 0 ∧ x (Fin.castAdd 13 p) = true ∧
        x (Fin.natAdd 13 l) = true)
    (hno : ¬∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and) : False := by
  have hor : ∀ g ∈ C.gates, g.op = GateOp.or := by
    intro g hg
    rcases hC.1 g hg with h | h
    · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
      exact absurd ⟨j, h⟩ hno
    · exact h
  have hadd := add_run C.gates (List.ofFn fun _ : Fin 26 => true)
    (List.ofFn fun j : Fin 26 => decide ((j : ℕ) < 13))
    (List.ofFn fun j : Fin 26 => decide (13 ≤ (j : ℕ))) hor (by simp) (by simp)
    (by
      intro i
      rcases Nat.lt_or_ge i 26 with h | h
      · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
          List.getD_eq_getElem _ _ (by simpa using h)]
        simp only [List.getElem_ofFn]
        by_cases h13 : i < 13
        · simp [h13]
        · simp [h13]
          omega
      · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ (by simpa using h),
          List.getD_eq_default _ _ (by simpa using h)]
        rfl) C.output
  have h1 : C.eval (List.ofFn fun _ : Fin 26 => true) = true :=
    (hf _).mpr ⟨1, 1, Or.inl rfl, by decide, rfl, rfl⟩
  have h2 : C.eval (List.ofFn fun j : Fin 26 => decide ((j : ℕ) < 13)) = false := by
    by_contra hne
    have ht : C.eval (List.ofFn fun j : Fin 26 => decide ((j : ℕ) < 13)) = true := by simpa using hne
    obtain ⟨p, l, _, _, _, hl⟩ := (hf _).mp ht
    simp at hl
  have h3 : C.eval (List.ofFn fun j : Fin 26 => decide (13 ≤ (j : ℕ))) = false := by
    by_contra hne
    have ht : C.eval (List.ofFn fun j : Fin 26 => decide (13 ≤ (j : ℕ))) = true := by simpa using hne
    obtain ⟨p, l, _, _, hp, _⟩ := (hf _).mp ht
    have := p.isLt
    simp at hp
    omega
  have e1 : C.eval (List.ofFn fun _ : Fin 26 => true)
      = (C.gates.foldl step (List.ofFn fun _ : Fin 26 => true)).getD C.output false := rfl
  have e2 : C.eval (List.ofFn fun j : Fin 26 => decide ((j : ℕ) < 13))
      = (C.gates.foldl step (List.ofFn fun j : Fin 26 => decide ((j : ℕ) < 13))).getD C.output false :=
    rfl
  have e3 : C.eval (List.ofFn fun j : Fin 26 => decide (13 ≤ (j : ℕ)))
      = (C.gates.foldl step (List.ofFn fun j : Fin 26 => decide (13 ≤ (j : ℕ)))).getD C.output false :=
    rfl
  rw [← e1, ← e2, ← e3, h1, h2, h3] at hadd
  exact Bool.noConfusion hadd

end PEqualNP.Outside.L_meta_17979

theorem PEqualNP.Outside.L_meta_17979 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x4 ≠ (0 : Fin (13 : ℕ)) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (¬∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (59 : ℕ) ≤ x1.size := by
  intro C hC hf hno
  exact (PEqualNP.Outside.L_meta_17979.main C hC hf hno).elim

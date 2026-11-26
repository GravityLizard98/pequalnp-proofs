import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17955

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem wires_cons (g : Gate) (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨g :: gs, o⟩ x
      = Circuit.wires ⟨gs, o⟩ (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

theorem wires_prefix (gs : List Gate) (o : ℕ) :
    ∀ x : List Bool, ∃ t : List Bool, Circuit.wires ⟨gs, o⟩ x = x ++ t := by
  induction gs with
  | nil => intro x; exact ⟨[], by simp [Circuit.wires]⟩
  | cons g gs ih =>
    intro x
    obtain ⟨t, ht⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    exact ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: t, by rw [wires_cons, ht]; simp⟩

theorem first_wire (g : Gate) (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨g :: gs, o⟩ x).getD x.length false
      = g.op.eval (g.inputs.map fun i => x.getD i false) := by
  obtain ⟨t, ht⟩ := wires_prefix gs o (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
  rw [wires_cons, ht, List.append_assoc]
  simp [List.getD_eq_getElem?_getD]

theorem early_wire (gs : List Gate) (o : ℕ) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (Circuit.wires ⟨gs, o⟩ x).getD i false = x.getD i false := by
  obtain ⟨t, ht⟩ := wires_prefix gs o x
  rw [ht, List.getD_append _ _ _ _ h]

def inp (y : Fin 9 → Bool) (a : ℕ) : Bool := (List.ofFn y).getD a false

theorem inp_lt (y : Fin 9 → Bool) (a : ℕ) (h : a < 9) : inp y a = y ⟨a, h⟩ := by
  unfold inp
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]

theorem inp_ge (y : Fin 9 → Bool) (a : ℕ) (h : 9 ≤ a) : inp y a = false := by
  unfold inp
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [show ¬ a < 9 by omega]

theorem gate_form (op : GateOp) (ins : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : ins.length ≤ 2)
    (hnc : ∃ x y : Fin 9 → Bool,
      op.eval (ins.map fun k => inp x k)
        ≠ op.eval (ins.map fun k => inp y k))
    (hne : ∀ i : ℕ, i < 9 → ∃ x : Fin 9 → Bool,
      inp x i ≠ op.eval (ins.map fun k => inp x k)) :
    ∃ i : Fin 9,
      (∀ y : Fin 9 → Bool, op.eval (ins.map fun k => inp y k) = !(y i)) ∨
      (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool,
        op.eval (ins.map fun k => inp y k) = (y i && y j)) ∨
      (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool,
        op.eval (ins.map fun k => inp y k) = (y i || y j)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ =>
      exfalso; obtain ⟨x, y, h⟩ := hnc; exact h (by simp [GateOp.eval])
    | [a], _ =>
      exfalso
      by_cases ha : a < 9
      · obtain ⟨x, h⟩ := hne a ha; exact h (by simp [GateOp.eval])
      · obtain ⟨x, y, h⟩ := hnc
        exact h (by simp [GateOp.eval, inp_ge x a (by omega), inp_ge y a (by omega)])
    | [a, b], _ =>
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · rcases Nat.lt_trichotomy a b with hab | hab | hab
          · exact ⟨⟨a, ha⟩, Or.inr (Or.inl ⟨⟨b, hb⟩, hab, fun y => by
              simp [GateOp.eval, inp_lt y a ha, inp_lt y b hb]⟩)⟩
          · exfalso; subst hab
            obtain ⟨x, h⟩ := hne a ha; exact h (by simp [GateOp.eval])
          · exact ⟨⟨b, hb⟩, Or.inr (Or.inl ⟨⟨a, ha⟩, hab, fun y => by
              simp [GateOp.eval, inp_lt y a ha, inp_lt y b hb, Bool.and_comm]⟩)⟩
        · exfalso; obtain ⟨x, y, h⟩ := hnc
          exact h (by simp [GateOp.eval, inp_ge x b (by omega), inp_ge y b (by omega)])
      · exfalso; obtain ⟨x, y, h⟩ := hnc
        exact h (by simp [GateOp.eval, inp_ge x a (by omega), inp_ge y a (by omega)])
    | _ :: _ :: _ :: _, h => exact absurd h (by simp)
  · match ins, hlen with
    | [], _ =>
      exfalso; obtain ⟨x, y, h⟩ := hnc; exact h (by simp [GateOp.eval])
    | [a], _ =>
      exfalso
      by_cases ha : a < 9
      · obtain ⟨x, h⟩ := hne a ha; exact h (by simp [GateOp.eval])
      · obtain ⟨x, y, h⟩ := hnc
        exact h (by simp [GateOp.eval, inp_ge x a (by omega), inp_ge y a (by omega)])
    | [a, b], _ =>
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · rcases Nat.lt_trichotomy a b with hab | hab | hab
          · exact ⟨⟨a, ha⟩, Or.inr (Or.inr ⟨⟨b, hb⟩, hab, fun y => by
              simp [GateOp.eval, inp_lt y a ha, inp_lt y b hb]⟩)⟩
          · exfalso; subst hab
            obtain ⟨x, h⟩ := hne a ha; exact h (by simp [GateOp.eval])
          · exact ⟨⟨b, hb⟩, Or.inr (Or.inr ⟨⟨a, ha⟩, hab, fun y => by
              simp [GateOp.eval, inp_lt y a ha, inp_lt y b hb, Bool.or_comm]⟩)⟩
        · exfalso
          obtain ⟨x, h⟩ := hne a ha
          exact h (by simp [GateOp.eval, inp_ge x b (by omega)])
      · by_cases hb : b < 9
        · exfalso
          obtain ⟨x, h⟩ := hne b hb
          exact h (by simp [GateOp.eval, inp_ge x a (by omega)])
        · exfalso; obtain ⟨x, y, h⟩ := hnc
          exact h (by simp [GateOp.eval, inp_ge x a (by omega), inp_ge y a (by omega), inp_ge x b (by omega), inp_ge y b (by omega)])
    | _ :: _ :: _ :: _, h => exact absurd h (by simp)
  · match ins, hlen with
    | [], _ =>
      exfalso; obtain ⟨x, y, h⟩ := hnc; exact h (by simp [GateOp.eval])
    | a :: rest, _ =>
      by_cases ha : a < 9
      · exact ⟨⟨a, ha⟩, Or.inl fun y => by simp [GateOp.eval, inp_lt y a ha]⟩
      · exfalso; obtain ⟨x, y, h⟩ := hnc
        exact h (by simp [GateOp.eval, inp_ge x a (by omega), inp_ge y a (by omega)])

theorem core (f : (Fin 9 → Bool) → Bool)
    (hnc : ∃ x y : Fin 9 → Bool, f x ≠ f y)
    (hproj : ∀ o : ℕ, ∃ x : Fin 9 → Bool, (List.ofFn x).getD o false ≠ f x)
    (H0 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)))
    (HC : ∀ i : Fin 9, ∀ C : Circuit, FanInTwo C →
      ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y i)) ∨
        (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool,
          (C.wires (List.ofFn y)).getD 9 false = (y i && y j)) ∨
        (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool,
          (C.wires (List.ofFn y)).getD 9 false = (y i || y j))) →
      circuitFun 9 C = f → 16 ≤ C.size) :
    ∀ t : ℕ, HasCircuitSize 9 f t → 16 ≤ t := by
  classical
  rintro t ⟨C0, hfan0, hsz0, hev0⟩
  have hex : ∃ s : ℕ, ∃ C : Circuit, FanInTwo C ∧ circuitFun 9 C = f ∧ C.size = s :=
    ⟨C0.size, C0, hfan0, funext hev0, rfl⟩
  obtain ⟨C, hfan, hfun, hsz⟩ := Nat.find_spec hex
  have hmin : IsMinimalCircuit 9 C := by
    refine ⟨hfan, fun D hD hDf => ?_⟩
    have := Nat.find_min' hex ⟨D, hD, hDf.trans hfun, rfl⟩
    omega
  have hle : C.size ≤ C0.size := by
    have := Nat.find_min' hex ⟨C0, hfan0, funext hev0, rfl⟩
    omega
  obtain ⟨hA, hB, -, -⟩ := H0 9 C hmin (by rw [hfun]; exact hnc)
  suffices hgoal : 16 ≤ C.size by omega
  obtain ⟨gates, o⟩ := C
  cases gates with
  | nil =>
    exfalso
    obtain ⟨x, hx⟩ := hproj o
    apply hx
    exact congrFun hfun x
  | cons g gs =>
    have hw : ∀ y : Fin 9 → Bool,
        (Circuit.wires ⟨g :: gs, o⟩ (List.ofFn y)).getD 9 false
          = g.op.eval (g.inputs.map fun k => (List.ofFn y).getD k false) := by
      intro y
      have := first_wire g gs o (List.ofFn y)
      rw [List.length_ofFn] at this
      exact this
    have hg := hfan g List.mem_cons_self
    have hnc' : ∃ x y : Fin 9 → Bool,
        g.op.eval (g.inputs.map fun k => inp x k)
          ≠ g.op.eval (g.inputs.map fun k => inp y k) := by
      obtain ⟨x, y, h⟩ := hA 0 (by simp)
      refine ⟨x, y, ?_⟩
      show ¬ (g.op.eval (g.inputs.map fun k => inp x k) = g.op.eval (g.inputs.map fun k => inp y k))
      intro h'
      apply h
      have e1 := hw x
      have e2 := hw y
      exact e1.trans (h'.trans e2.symm)
    have hne' : ∀ i : ℕ, i < 9 → ∃ x : Fin 9 → Bool,
        inp x i ≠ g.op.eval (g.inputs.map fun k => inp x k) := by
      intro i hi
      obtain ⟨x, h⟩ := hB i 0 (by omega) (by simp)
      refine ⟨x, ?_⟩
      intro h'
      apply h
      have e1 := hw x
      have e2 := early_wire (g :: gs) o (List.ofFn x) i (by rw [List.length_ofFn]; exact hi)
      exact e2.trans (h'.trans e1.symm)
    obtain ⟨i, hi⟩ := gate_form g.op g.inputs hg.1 hg.2 hnc' hne'
    refine HC i ⟨g :: gs, o⟩ hfan ?_ hfun
    rcases hi with h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩
    · exact Or.inl fun y => (hw y).trans (h y)
    · exact Or.inr (Or.inl ⟨j, hj, fun y => (hw y).trans (h y)⟩)
    · exact Or.inr (Or.inr ⟨j, hj, fun y => (hw y).trans (h y)⟩)

def target (x : Fin 9 → Bool) : Bool := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)

theorem target_nc : ∃ x y : Fin 9 → Bool, target x ≠ target y :=
  ⟨fun _ => true, fun _ => false, by decide⟩

theorem target_proj : ∀ o : ℕ, ∃ x : Fin 9 → Bool, (List.ofFn x).getD o false ≠ target x := by
  intro o
  by_cases h : o < 9
  · refine ⟨fun i => decide (i.val = o), ?_⟩
    interval_cases o <;> decide
  · refine ⟨fun _ => true, ?_⟩
    have h2 := inp_ge (fun _ : Fin 9 => true) o (by omega)
    unfold inp at h2
    rw [h2]
    decide

end PEqualNP.Outside.L_meta_17955

open PEqualNP.Outside.L_meta_17955 in
theorem PEqualNP.Outside.L_meta_17955 :
(∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y j)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 1)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y j)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y j)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 6)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y j)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 8)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 && y j)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) t → 16 ≤ t := by
  intro H0 h0 h1 h2 h3 h4 h5 h6 h7 h8
  refine core target target_nc target_proj H0 ?_
  intro i
  fin_cases i
  all_goals first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7 | exact h8

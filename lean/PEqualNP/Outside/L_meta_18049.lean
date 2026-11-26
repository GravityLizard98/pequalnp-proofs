import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18049

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def lstep (w : List (Bool × Bool)) (g : Gate) : List (Bool × Bool) :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  w ++ [match g.op with
    | GateOp.or  => (ins.any (·.1), ins.any (·.2))
    | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
    | _ => (false, false)]

theorem lstep_len (w : List (Bool × Bool)) (g : Gate) : (lstep w g).length = w.length + 1 := by
  simp [lstep]

theorem lstep_lt (w : List (Bool × Bool)) (g : Gate) (i : ℕ) (h : i < w.length) :
    (lstep w g).getD i (false, false) = w.getD i (false, false) := List.getD_append _ _ _ _ h

theorem lstep_eq (w : List (Bool × Bool)) (g : Gate) (a b : ℕ) (hab : g.inputs = [a, b]) :
    (lstep w g).getD w.length (false, false)
      = (match g.op with
        | GateOp.or => ((w.getD a (false, false)).1 || (w.getD b (false, false)).1,
            (w.getD a (false, false)).2 || (w.getD b (false, false)).2)
        | GateOp.and => ((w.getD a (false, false)).1 && (w.getD b (false, false)).1,
            ((w.getD a (false, false)).1 && (w.getD b (false, false)).2) ||
            ((w.getD a (false, false)).2 && (w.getD b (false, false)).1))
        | _ => (false, false)) := by
  unfold lstep
  simp only []
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, hab]
  cases g.op <;> simp

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := List.getD_append _ _ _ _ h

theorem step_eq (w : List Bool) (g : Gate) (a b : ℕ) (hab : g.inputs = [a, b]) :
    (step w g).getD w.length false = g.op.eval [w.getD a false, w.getD b false] := by
  unfold step
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, hab]
  simp

theorem run_lt (gs : List Gate) : ∀ (w : List Bool) (k : ℕ), k < w.length →
    (gs.foldl step w).getD k false = w.getD k false := by
  induction gs with
  | nil => intro w k _; rfl
  | cons g gs ih =>
    intro w k hk
    simp only [List.foldl_cons]
    rw [ih _ k (by rw [step_len]; omega), step_lt _ _ _ hk]

def X0 (p : ℕ) : List Bool := List.ofFn fun (i : Fin 26) => decide ((i : ℕ) = p)

def L0 (p l : ℕ) : List (Bool × Bool) :=
  (((List.range 26).map fun i => i == p || i == l).zipIdx).map
    fun (b, i) => if (decide (i = l)) = true then (false, b) else (b, false)

def R (C : Circuit) (p : ℕ) (a b : ℕ) : Prop :=
  ∃ (j : ℕ) (k : ℕ) (g : Gate), b = 26 + j ∧ C.gates[j]? = some g ∧
    (g.inputs = [a, k] ∨ g.inputs = [k, a]) ∧
    (g.op = GateOp.or ∨ (C.wires (X0 p)).getD k false = true)

theorem l0_get (p l k : ℕ) (hk : k < 26) : (L0 p l).getD k (false, false)
    = if k = l then (false, (k == p || k == l)) else ((k == p || k == l), false) := by
  unfold L0
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem x0_get (p k : ℕ) (hk : k < 26) : (X0 p).getD k false = decide (k = p) := by
  unfold X0
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]

theorem inv (C : Circuit) (p l : ℕ) (hC : PEqualNP.TopForm.IsAO2 26 C) (hl : l < 26) :
    ∀ pre : List Gate, (∃ post, C.gates = pre ++ post) →
      (pre.foldl lstep (L0 p l)).length = 26 + pre.length ∧
      (pre.foldl step (X0 p)).length = 26 + pre.length ∧
      ∀ k, k < 26 + pre.length →
        (((pre.foldl lstep (L0 p l)).getD k (false, false)).1 = true →
          (pre.foldl step (X0 p)).getD k false = true) ∧
        (((pre.foldl lstep (L0 p l)).getD k (false, false)).2 = true →
          Relation.ReflTransGen (R C p) l k) := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨by simp [L0], by simp [X0], ?_⟩
    intro k hk
    have hk' : k < 26 := by simpa using hk
    simp only [List.foldl_nil]
    rw [l0_get p l k hk', x0_get p k hk']
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl]
      exact ⟨fun h => by simp at h, fun _ => Relation.ReflTransGen.refl⟩
    · rw [if_neg hkl]
      refine ⟨fun h => ?_, fun h => by simp at h⟩
      simpa [hkl] using h
  | append_singleton pre g ih =>
    rintro ⟨post, hpost⟩
    have hpost' : C.gates = pre ++ (g :: post) := by simpa using hpost
    obtain ⟨h1, h2, h3⟩ := ih ⟨g :: post, hpost'⟩
    obtain ⟨hao, hrb, hlen⟩ := hC
    have hmem : g ∈ C.gates := by rw [hpost']; simp
    have hget : C.gates[pre.length]? = some g := by rw [hpost']; simp
    have hjlt : pre.length < C.gates.length := by rw [hpost']; simp
    have hgat : gateAt C pre.length = g := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, hget]
      rfl
    have hin2 := hlen g hmem
    obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
      rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
      · rw [hgi] at hin2; simp at hin2
      · rw [hgi] at hin2; simp at hin2
      · exact ⟨a, b, rfl⟩
      · rw [hgi] at hin2; simp at hin2
    have ha : a < 26 + pre.length := by
      have := hrb pre.length hjlt a (by rw [hgat, hab]; simp)
      exact this
    have hb : b < 26 + pre.length := by
      have := hrb pre.length hjlt b (by rw [hgat, hab]; simp)
      exact this
    have hfull : ∀ k, k < 26 + pre.length →
        (C.wires (X0 p)).getD k false = (pre.foldl step (X0 p)).getD k false := by
      intro k hk
      show (C.gates.foldl step (X0 p)).getD k false = _
      rw [hpost', List.foldl_append]
      exact run_lt _ _ k (by rw [h2]; exact hk)
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton]
    refine ⟨by rw [lstep_len, h1]; omega, by rw [step_len, h2]; omega, ?_⟩
    intro k hk
    rcases Nat.lt_or_ge k (26 + pre.length) with hlt | hge
    · rw [lstep_lt _ _ _ (by rw [h1]; exact hlt), step_lt _ _ _ (by rw [h2]; exact hlt)]
      exact h3 k hlt
    · have hk' : k = 26 + pre.length := by omega
      subst hk'
      have e1 := lstep_eq (pre.foldl lstep (L0 p l)) g a b hab
      rw [h1] at e1
      have e2 := step_eq (pre.foldl step (X0 p)) g a b hab
      rw [h2] at e2
      rw [e1, e2]
      obtain ⟨ha1, ha2⟩ := h3 a ha
      obtain ⟨hb1, hb2⟩ := h3 b hb
      rcases hao g hmem with hop | hop
      · rw [hop]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true,
          Bool.or_eq_true]
        refine ⟨fun h => ⟨ha1 h.1, hb1 h.2⟩, ?_⟩
        rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
        · exact Relation.ReflTransGen.tail (hb2 hB)
            ⟨pre.length, a, g, rfl, hget, Or.inr hab, Or.inr (by rw [hfull a ha]; exact ha1 hA)⟩
        · exact Relation.ReflTransGen.tail (ha2 hA)
            ⟨pre.length, b, g, rfl, hget, Or.inl hab, Or.inr (by rw [hfull b hb]; exact hb1 hB)⟩
      · rw [hop]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true]
        refine ⟨fun h => h.elim (fun h => Or.inl (ha1 h)) (fun h => Or.inr (hb1 h)), ?_⟩
        rintro (hA | hB)
        · exact Relation.ReflTransGen.tail (ha2 hA)
            ⟨pre.length, b, g, rfl, hget, Or.inl hab, Or.inl hop⟩
        · exact Relation.ReflTransGen.tail (hb2 hB)
            ⟨pre.length, a, g, rfl, hget, Or.inr hab, Or.inl hop⟩

theorem main (C : Circuit) (p l : ℕ) (hC : PEqualNP.TopForm.IsAO2 26 C) (hp : p < 26) (hl : l < 26)
    (h : PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = l)) p l = true) :
    Relation.ReflTransGen (R C p) l C.output := by
  obtain ⟨h1, _, h3⟩ := inv C p l hC hl C.gates ⟨[], by simp⟩
  have hL : PEqualNP.ReadK.linearParts C (fun i => decide (i = l))
      ((List.range 26).map fun i => i == p || i == l) = C.gates.foldl lstep (L0 p l) := rfl
  unfold PEqualNP.ReadK.lineSingle at h
  rw [hL] at h
  by_cases ho : C.output < 26 + C.gates.length
  · exact (h3 C.output ho).2 h
  · rw [List.getD_eq_default _ _ (by rw [h1]; omega)] at h
    simp at h

end PEqualNP.Outside.L_meta_18049

theorem PEqualNP.Outside.L_meta_18049 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → x2 < (26 : ℕ) → x3 < (26 : ℕ) → PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = x3)) x2 x3 = Bool.true → Relation.ReflTransGen (fun (x8 x9 : ℕ) => ∃ (x10 : ℕ) (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x9 = (26 : ℕ) + x10 ∧ x1.gates[x10]? = Option.some x12 ∧ (x12.inputs = [x8, x11] ∨ x12.inputs = [x11, x8]) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ (x1.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = x2))).getD x11 Bool.false = Bool.true)) x3 x1.output := by
  intro C p l hC hp hl h
  exact PEqualNP.Outside.L_meta_18049.main C p l hC hp hl h

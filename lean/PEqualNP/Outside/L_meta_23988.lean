import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23988

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_last {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k = l.length) :
    (l ++ [b]).getD k d = b := by
  subst hk; simp [List.getD_eq_getElem?_getD]

theorem getD_left {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k < l.length) :
    (l ++ [b]).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem snoc_fold (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl stp x =
      gs.foldl stp x ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stp x).getD i false)] := by
  simp [List.foldl_append, stp]

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem sa_val {m : ℕ} (k : Fin (m + 1)) (v : Fin m) :
    (k.succAbove v).val = if v.val < k.val then v.val else v.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (by simp [Fin.lt_def] at h2 ⊢; omega)
  · exact absurd h2 (by simp [Fin.lt_def] at h1 ⊢; omega)
  · rfl

def rho (p r : ℕ) (i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def rg (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho p r)⟩

theorem sim (Q : Prop) (p r B : ℕ) (X X' : List Bool) (hl : X.length = X'.length + 1)
    (hp : p ≤ X'.length) (hr : r < X'.length ∨ B ≤ r)
    (hbase : ∀ i, (i = p → Q) → X'.getD (rho p r i) false = X.getD i false) :
    ∀ Bs : List Gate, X'.length + Bs.length ≤ B → (∀ g ∈ Bs, ∀ i ∈ g.inputs, i = p → Q) →
      ∀ i, (i = p → Q) →
      ((Bs.map (rg p r)).foldl stp X').getD (rho p r i) false =
        (Bs.foldl stp X).getD i false := by
  intro Bs
  induction Bs using List.reverseRecOn with
  | nil =>
    intro _ _ i hi
    exact hbase i hi
  | append_singleton Bs g ih =>
    intro hB hQ i hiQ
    rw [List.length_append, List.length_singleton] at hB
    have ih' := ih (by omega) (fun g' hg' => hQ g' (List.mem_append_left _ hg'))
    have hv : (rg p r g).op.eval ((rg p r g).inputs.map fun i =>
        ((Bs.map (rg p r)).foldl stp X').getD i false) =
        g.op.eval (g.inputs.map fun i => (Bs.foldl stp X).getD i false) := by
      show g.op.eval ((g.inputs.map (rho p r)).map fun i =>
        ((Bs.map (rg p r)).foldl stp X').getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact ih' j (hQ g (by simp) j hj)
    rw [List.map_append, List.map_singleton, snoc_fold, snoc_fold, hv, getD_snoc, getD_snoc,
      len, len, List.length_map]
    simp only [hl]
    have hi := ih' i hiQ
    rcases Nat.lt_trichotomy i p with h | h | h
    · have hr' : rho p r i = i := by unfold rho; rw [ifp h]
      rw [hr'] at hi ⊢
      rw [ifp (by omega), ifp (by omega)]
      exact hi
    · have hr' : rho p r i = r := by unfold rho; rw [ifn (by omega), ifp h]
      rw [hr'] at hi ⊢
      rcases hr with h1 | h1
      · rw [ifp (by omega), ifp (by omega)]
        exact hi
      · rw [ifn (by omega), ifn (by omega), ifp (by omega), ← hi]
        symm
        exact List.getD_eq_default _ _ (by rw [len, List.length_map]; omega)
    · have hr' : rho p r i = i - 1 := by unfold rho; rw [ifn (by omega), ifn (by omega)]
      rw [hr'] at hi ⊢
      by_cases h2 : i < X'.length + 1 + Bs.length
      · rw [ifp (by omega), ifp h2]
        exact hi
      · by_cases h3 : i = X'.length + 1 + Bs.length
        · rw [ifn (by omega), ifp (by omega), ifn h2, ifp h3]
        · rw [ifn (by omega), ifn (by omega), ifn h2, ifn h3]

theorem bool_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp at h ⊢

theorem pre (gs : List Gate) (X : List Bool) (i : ℕ) (hi : i < X.length) :
    (gs.foldl stp X).getD i false = X.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [snoc_fold, getD_left _ _ _ _ (by rw [len]; omega)]
    exact ih

theorem stable (G1 G2 : List Gate) (g : Gate) (X : List Bool) (p : ℕ)
    (hp : p = X.length + G1.length) :
    ((G1 ++ g :: G2).foldl stp X).getD p false =
      g.op.eval (g.inputs.map fun i => (G1.foldl stp X).getD i false) := by
  rw [List.foldl_append, List.foldl_cons, pre _ _ _ (by simp [stp, len]; omega)]
  exact getD_last _ _ _ _ (by rw [len]; exact hp)

theorem colstep (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : Circuit)
    (hrep : ∀ (u : Fin n) (v : Fin m), C.eval (oneEach u (k.succAbove v)) = A u (k.succAbove v)) :
    ∃ C' : Circuit, C'.size = C.size ∧ (FanInTwo C → FanInTwo C') ∧
      Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C' ∧
      (∀ u : Fin n, ((∃ g ∈ C'.gates, u.val ∈ g.inputs) ∨ C'.output = u.val) →
        ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧
      (∀ v : Fin m, ((∃ g ∈ C'.gates, n + v.val ∈ g.inputs) ∨ C'.output = n + v.val) →
        ((∃ g ∈ C.gates, n + (k.succAbove v).val ∈ g.inputs) ∨
          C.output = n + (k.succAbove v).val)) := by
  have hk : k.val ≤ m := Nat.lt_succ_iff.mp k.isLt
  refine ⟨⟨C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)),
    rho (n + k.val) (n + m + 1 + C.gates.length) C.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show (C.gates.map _).length = C.gates.length
    rw [List.length_map]
  · intro hF g hg
    have hg' : g ∈ C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
    rw [List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    have hf := hF g0 hg0
    refine ⟨hf.1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact hf.2
  · intro u v
    have hr : (C.gates.foldl stp (oneEach u (k.succAbove v))).getD C.output false =
      A u (k.succAbove v) := hrep u v
    show ((C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length))).foldl stp (oneEach u v)).getD
      (rho (n + k.val) (n + m + 1 + C.gates.length) C.output) false = A u (k.succAbove v)
    rw [← hr]
    have hlx : (oneEach u v).length = n + m := by simp [oneEach]
    have hlx2 : (oneEach u (k.succAbove v)).length = n + m + 1 := by simp [oneEach]; omega
    refine sim True (n + k.val) (n + m + 1 + C.gates.length) (n + m + 1 + C.gates.length)
      (oneEach u (k.succAbove v)) (oneEach u v)
      (by rw [hlx, hlx2]) (by rw [hlx]; omega) (Or.inr le_rfl) ?_ C.gates (by rw [hlx]; omega)
      (fun _ _ _ _ _ => trivial) C.output (fun _ => trivial)
    intro i _
    apply bool_iff
    rw [oe, oe, sa_val]
    have hu := u.isLt
    have hv := v.isLt
    unfold rho
    split_ifs <;> omega
  · intro u hu
    have hul := u.isLt
    have key : ∀ i, rho (n + k.val) (n + m + 1 + C.gates.length) i = u.val → i = u.val := by
      intro i
      unfold rho
      split_ifs <;> omega
    rcases hu with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      have hmem' : u.val ∈ g0.inputs.map (rho (n + k.val) (n + m + 1 + C.gates.length)) := hmem
      rw [List.mem_map] at hmem'
      obtain ⟨i, hi, hiu⟩ := hmem'
      have := key i hiu
      subst this
      exact Or.inl ⟨g0, hg0, hi⟩
    · exact Or.inr (key _ ho)
  · intro v hv
    have hvl := v.isLt
    have key : ∀ i, rho (n + k.val) (n + m + 1 + C.gates.length) i = n + v.val →
        i = n + (k.succAbove v).val := by
      intro i
      rw [sa_val]
      unfold rho
      split_ifs <;> omega
    rcases hv with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      have hmem' : n + v.val ∈ g0.inputs.map (rho (n + k.val) (n + m + 1 + C.gates.length)) := hmem
      rw [List.mem_map] at hmem'
      obtain ⟨i, hi, hiu⟩ := hmem'
      have := key i hiu
      subst this
      exact Or.inl ⟨g0, hg0, hi⟩
    · exact Or.inr (key _ ho)

theorem delstep (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : Circuit)
    (G1 G2 : List Gate) (h : Gate) (r : ℕ) (Q : Prop)
    (hC : C.gates = G1 ++ h :: G2) (hF : FanInTwo C)
    (hrep : ∀ (u : Fin n) (v : Fin m), C.eval (oneEach u (k.succAbove v)) = A u (k.succAbove v))
    (hr : r < n + m + 1 + G1.length ∨ n + m + 1 + C.gates.length ≤ r)
    (hrin : r < n + m + 1 → r ∈ h.inputs)
    (hQ2 : ∀ g ∈ G2, ∀ i ∈ g.inputs, i = n + m + 1 + G1.length → Q)
    (hQo : C.output = n + m + 1 + G1.length → Q)
    (hv : Q → ∀ (u : Fin n) (v : Fin m),
      h.op.eval (h.inputs.map fun i => (G1.foldl stp (oneEach u (k.succAbove v))).getD i false) =
        (G1.foldl stp (oneEach u (k.succAbove v))).getD r false) :
    ∃ C1 : Circuit, C1.size + 1 = C.size ∧ FanInTwo C1 ∧
      (∀ (u : Fin n) (v : Fin m), C1.eval (oneEach u (k.succAbove v)) = A u (k.succAbove v)) ∧
      (∀ i < n + m + 1, ((∃ g ∈ C1.gates, i ∈ g.inputs) ∨ C1.output = i) →
        ((∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i)) := by
  have hlen : C.gates.length = G1.length + G2.length + 1 := by rw [hC]; simp; omega
  refine ⟨⟨G1 ++ G2.map (rg (n + m + 1 + G1.length) r), rho (n + m + 1 + G1.length) r C.output⟩,
    ?_, ?_, ?_, ?_⟩
  · show (G1 ++ G2.map _).length + 1 = C.gates.length
    rw [hlen]
    simp
  · intro g hg
    have hg' : g ∈ G1 ++ G2.map (rg (n + m + 1 + G1.length) r) := hg
    rw [List.mem_append, List.mem_map] at hg'
    rcases hg' with h1 | ⟨g0, hg0, rfl⟩
    · exact hF g (by rw [hC]; simp [h1])
    · have hf := hF g0 (by rw [hC]; simp [hg0])
      refine ⟨hf.1, ?_⟩
      show (g0.inputs.map _).length ≤ 2
      rw [List.length_map]
      exact hf.2
  · intro u v
    have hx : (oneEach u (k.succAbove v)).length = n + m + 1 := by simp [oneEach]; omega
    have h0 : (C.gates.foldl stp (oneEach u (k.succAbove v))).getD C.output false =
      A u (k.succAbove v) := hrep u v
    show ((G1 ++ G2.map (rg (n + m + 1 + G1.length) r)).foldl stp
      (oneEach u (k.succAbove v))).getD (rho (n + m + 1 + G1.length) r C.output) false = _
    rw [← h0, hC, List.foldl_append, List.foldl_append, List.foldl_cons]
    have hl1 : (G1.foldl stp (oneEach u (k.succAbove v))).length = n + m + 1 + G1.length := by
      rw [len, hx]
    refine sim Q (n + m + 1 + G1.length) r (n + m + 1 + C.gates.length)
      (stp (G1.foldl stp (oneEach u (k.succAbove v))) h) (G1.foldl stp (oneEach u (k.succAbove v)))
      ?_ ?_ ?_ ?_ G2 ?_ hQ2 C.output hQo
    · simp [stp]
    · rw [hl1]
    · rw [hl1]
      exact hr
    · intro i hi
      show (G1.foldl stp (oneEach u (k.succAbove v))).getD (rho (n + m + 1 + G1.length) r i) false =
        (G1.foldl stp (oneEach u (k.succAbove v)) ++ [_]).getD i false
      rw [getD_snoc, hl1]
      unfold rho
      by_cases h1 : i < n + m + 1 + G1.length
      · rw [ifp h1, ifp h1]
      · by_cases h2 : i = n + m + 1 + G1.length
        · rw [ifn h1, ifp h2, ifn h1, ifp h2]
          exact (hv (hi h2) u v).symm
        · rw [ifn h1, ifn h2, ifn h1, ifn h2]
          exact List.getD_eq_default _ _ (by rw [hl1]; omega)
    · rw [hl1, hlen]
      omega
  · intro i hi hrd
    have key : ∀ j, rho (n + m + 1 + G1.length) r j = i →
        j = i ∨ (j = n + m + 1 + G1.length ∧ r = i) := by
      intro j
      unfold rho
      split_ifs <;> omega
    rcases hrd with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ G1 ++ G2.map (rg (n + m + 1 + G1.length) r) := hg
      rw [List.mem_append, List.mem_map] at hg'
      rcases hg' with h1 | ⟨g0, hg0, rfl⟩
      · exact Or.inl ⟨g, by rw [hC]; simp [h1], hmem⟩
      · have hmem' : i ∈ g0.inputs.map (rho (n + m + 1 + G1.length) r) := hmem
        rw [List.mem_map] at hmem'
        obtain ⟨j, hj, hji⟩ := hmem'
        rcases key j hji with h3 | ⟨_, h3⟩
        · subst h3
          exact Or.inl ⟨g0, by rw [hC]; simp [hg0], hj⟩
        · subst h3
          exact Or.inl ⟨h, by rw [hC]; simp, hrin hi⟩
    · rcases key _ ho with h3 | ⟨_, h3⟩
      · exact Or.inr h3
      · subst h3
        exact Or.inl ⟨h, by rw [hC]; simp, hrin hi⟩

theorem fin (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : Circuit)
    (G1 G2 : List Gate) (h : Gate) (r : ℕ) (Q : Prop)
    (hC : C.gates = G1 ++ h :: G2) (hF : FanInTwo C) (hrep : Represents A C)
    (hr : r < n + m + 1 + G1.length ∨ n + m + 1 + C.gates.length ≤ r)
    (hrin : r < n + m + 1 → r ∈ h.inputs)
    (hQ2 : ∀ g ∈ G2, ∀ i ∈ g.inputs, i = n + m + 1 + G1.length → Q)
    (hQo : C.output = n + m + 1 + G1.length → Q)
    (hv : Q → ∀ (u : Fin n) (v : Fin m),
      h.op.eval (h.inputs.map fun i => (G1.foldl stp (oneEach u (k.succAbove v))).getD i false) =
        (G1.foldl stp (oneEach u (k.succAbove v))).getD r false) :
    ∃ C2 : Circuit, FanInTwo C2 ∧
      Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ C2.size + 1 ≤ C.size ∧
      (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) →
        ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧
      (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) →
        ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨
          C.output = (n + (k.succAbove v).val))) := by
  obtain ⟨C1, hs1, hF1, hrep1, hrd1⟩ := delstep n m A k C G1 G2 h r Q hC hF
    (fun u v => hrep u (k.succAbove v)) hr hrin hQ2 hQo hv
  obtain ⟨C2, hs2, hF2, hrep2, hu2, hv2⟩ := colstep n m A k C1 hrep1
  refine ⟨C2, hF2 hF1, hrep2, by omega, ?_, ?_⟩
  · intro u hu
    exact hrd1 u.val (by have := u.isLt; omega) (hu2 u hu)
  · intro v hv'
    exact hrd1 _ (by have := (k.succAbove v).isLt; omega) (hv2 v hv')

theorem shape (g : Gate)
    (h : ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    (∃ a b, g = ⟨GateOp.and, [a, b]⟩) ∨ (∃ a b, g = ⟨GateOp.or, [a, b]⟩) ∨
      (∃ a, g = ⟨GateOp.not, [a]⟩) := by
  obtain ⟨op, ins⟩ := g
  rcases h with ⟨h1 | h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    subst h1
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at h2
    exact Or.inl ⟨a, b, rfl⟩
  · simp only at h1 h2
    subst h1
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at h2
    exact Or.inr (Or.inl ⟨a, b, rfl⟩)
  · simp only at h1 h2
    subst h1
    rcases ins with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp at h2
    exact Or.inr (Or.inr ⟨a, rfl⟩)

theorem and_ev (W : List Bool) (a b : ℕ) :
    (⟨GateOp.and, [a, b]⟩ : Gate).op.eval
      ((⟨GateOp.and, [a, b]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (W.getD a false && W.getD b false) := by
  simp [GateOp.eval]

theorem or_ev (W : List Bool) (a b : ℕ) :
    (⟨GateOp.or, [a, b]⟩ : Gate).op.eval
      ((⟨GateOp.or, [a, b]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (W.getD a false || W.getD b false) := by
  simp [GateOp.eval]

theorem not_ev (W : List Bool) (a : ℕ) :
    (⟨GateOp.not, [a]⟩ : Gate).op.eval
      ((⟨GateOp.not, [a]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (!W.getD a false) := by
  simp [GateOp.eval]

theorem ck (n m : ℕ) (k : Fin (m + 1)) (u : Fin n) (v : Fin m) (gs : List Gate) :
    (gs.foldl stp (oneEach u (k.succAbove v))).getD (n + k.val) false = false := by
  have hx : (oneEach u (k.succAbove v)).length = n + m + 1 := by simp [oneEach]; omega
  rw [pre _ _ _ (by rw [hx]; have := k.isLt; omega)]
  cases hb : (oneEach u (k.succAbove v)).getD (n + k.val) false with
  | false => rfl
  | true =>
    rw [oe] at hb
    rcases hb with hb | hb
    · have := u.isLt
      omega
    · exact absurd (Fin.ext (by omega)) (Fin.succAbove_ne k v)

def rr (p B a : ℕ) : ℕ := if a < p then a else B

theorem rr_val (W : List Bool) (p B a : ℕ) (hW : W.length = p) (hB : p ≤ B) :
    W.getD (rr p B a) false = W.getD a false := by
  unfold rr
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem rr_hr (p B a : ℕ) : rr p B a < p ∨ B ≤ rr p B a := by
  unfold rr
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr le_rfl

theorem rr_in (p B N a : ℕ) (hN : N ≤ B) (h : rr p B a < N) : rr p B a = a := by
  unfold rr at h ⊢
  split_ifs at h ⊢ <;> omega

theorem main : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.Represents.Represents A C → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C hF hkind hrep hlist hnc
  obtain ⟨g, hg, hc⟩ := hlist
  obtain ⟨G1, G2, hC⟩ := List.append_of_mem hg
  have hlen : C.gates.length = G1.length + G2.length + 1 := by rw [hC]; simp; omega
  have hx : ∀ (u : Fin n) (v : Fin m), (oneEach u (k.succAbove v)).length = n + m + 1 := by
    intro u v
    simp [oneEach]
    omega
  have hW1 : ∀ (u : Fin n) (v : Fin m),
      (G1.foldl stp (oneEach u (k.succAbove v))).length = n + m + 1 + G1.length := by
    intro u v
    rw [len, hx]
  rcases shape g (hkind g hg) with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, rfl⟩
  · refine fin n m A k C G1 G2 _ (n + m + 1 + C.gates.length) True hC hF hrep (Or.inr le_rfl)
      (by intro h; omega) (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
    intro _ u v
    rw [List.getD_eq_default _ _ (by rw [hW1]; omega), and_ev]
    simp at hc
    rcases hc with h1 | h1
    · subst h1
      rw [ck]
      rfl
    · subst h1
      rw [ck]
      simp
  · simp at hc
    rcases hc with h1 | h1
    · subst h1
      refine fin n m A k C G1 G2 _ (rr (n + m + 1 + G1.length) (n + m + 1 + C.gates.length) b) True
        hC hF hrep (rr_hr _ _ _) ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
      · intro h
        rw [rr_in _ _ (n + m + 1) _ (by omega) h]
        simp
      · intro _ u v
        rw [rr_val _ _ _ _ (hW1 u v) (by omega), or_ev, ck]
        simp
    · subst h1
      refine fin n m A k C G1 G2 _ (rr (n + m + 1 + G1.length) (n + m + 1 + C.gates.length) a) True
        hC hF hrep (rr_hr _ _ _) ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
      · intro h
        rw [rr_in _ _ (n + m + 1) _ (by omega) h]
        simp
      · intro _ u v
        rw [rr_val _ _ _ _ (hW1 u v) (by omega), or_ev, ck]
        simp
  · simp at hc
    subst hc
    by_cases ho : C.output = n + m + 1 + G1.length
    · exfalso
      obtain ⟨u, u2, v, v2, hne⟩ := hnc
      have ht : ∀ (u : Fin n) (v : Fin m), A u (k.succAbove v) = true := by
        intro u v
        have h0 : (C.gates.foldl stp (oneEach u (k.succAbove v))).getD C.output false =
          A u (k.succAbove v) := hrep u (k.succAbove v)
        rw [← h0, ho, hC, stable G1 G2 _ _ _ (by rw [hx]), not_ev, ck]
        rfl
      exact hne ((ht u v).trans (ht u2 v2).symm)
    · by_cases hread : ∃ g' ∈ G2, (n + m + 1 + G1.length) ∈ g'.inputs
      · obtain ⟨g', hg', hp'⟩ := hread
        obtain ⟨G2a, G2b, hG2⟩ := List.append_of_mem hg'
        have hC' : C.gates = (G1 ++ ⟨GateOp.not, [n + k.val]⟩ :: G2a) ++ g' :: G2b := by
          rw [hC, hG2]
          simp
        have hl' : (G1 ++ (⟨GateOp.not, [n + k.val]⟩ : Gate) :: G2a).length =
            G1.length + G2a.length + 1 := by
          simp
          omega
        have hlen2 : G2.length = G2a.length + G2b.length + 1 := by rw [hG2]; simp; omega
        have hW2 : ∀ (u : Fin n) (v : Fin m),
            ((G1 ++ (⟨GateOp.not, [n + k.val]⟩ : Gate) :: G2a).foldl stp
              (oneEach u (k.succAbove v))).length = n + m + 1 + (G1.length + G2a.length + 1) := by
          intro u v
          rw [len, hx, hl']
        have hT : ∀ (u : Fin n) (v : Fin m),
            ((G1 ++ (⟨GateOp.not, [n + k.val]⟩ : Gate) :: G2a).foldl stp
              (oneEach u (k.succAbove v))).getD (n + m + 1 + G1.length) false = true := by
          intro u v
          rw [stable G1 G2a _ _ _ (by rw [hx]), not_ev, ck]
          rfl
        have hg'C : g' ∈ C.gates := by rw [hC']; simp
        rcases shape g' (hkind g' hg'C) with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, rfl⟩
        · simp at hp'
          rcases hp' with h1 | h1
          · subst h1
            refine fin n m A k C _ G2b _
              (rr (n + m + 1 + (G1.length + G2a.length + 1)) (n + m + 1 + C.gates.length) b) True
              hC' hF hrep ?_ ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
            · rw [hl']
              exact rr_hr _ _ _
            · intro h
              rw [rr_in _ _ (n + m + 1) _ (by omega) h]
              simp
            · intro _ u v
              rw [rr_val _ _ _ _ (hW2 u v) (by omega), and_ev, hT]
              simp
          · subst h1
            refine fin n m A k C _ G2b _
              (rr (n + m + 1 + (G1.length + G2a.length + 1)) (n + m + 1 + C.gates.length) a) True
              hC' hF hrep ?_ ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
            · rw [hl']
              exact rr_hr _ _ _
            · intro h
              rw [rr_in _ _ (n + m + 1) _ (by omega) h]
              simp
            · intro _ u v
              rw [rr_val _ _ _ _ (hW2 u v) (by omega), and_ev, hT]
              simp
        · refine fin n m A k C _ G2b _ (n + m + 1 + G1.length) True hC' hF hrep
            (Or.inl (by rw [hl']; omega)) (by intro h; omega) (fun _ _ _ _ _ => trivial)
            (fun _ => trivial) ?_
          intro _ u v
          simp at hp'
          rcases hp' with h1 | h1
          · subst h1
            rw [or_ev, hT]
            simp
          · subst h1
            rw [or_ev, hT]
            simp
        · simp at hp'
          subst hp'
          refine fin n m A k C _ G2b _ (n + m + 1 + C.gates.length) True hC' hF hrep
            (Or.inr le_rfl) (by intro h; omega) (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
          intro _ u v
          rw [not_ev, hT, List.getD_eq_default _ _ (by rw [hW2]; omega)]
          rfl
      · refine fin n m A k C G1 G2 _ (n + m + 1 + C.gates.length) False hC hF hrep (Or.inr le_rfl)
          (by intro h; omega) ?_ ho ?_
        · intro g' hg' i hi hip
          exact hread ⟨g', hg', hip ▸ hi⟩
        · intro hf
          exact hf.elim

end PEqualNP.Outside.L_meta_23988

theorem PEqualNP.Outside.L_meta_23988 : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.Represents.Represents A C → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) :=
  PEqualNP.Outside.L_meta_23988.main

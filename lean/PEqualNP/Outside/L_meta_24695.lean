import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24695

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def E_stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem E_ifp {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem E_ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem E_len (gs : List Gate) (x : List Bool) : (gs.foldl E_stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, E_stp, ih]; omega

theorem E_getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem E_getD_last {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k = l.length) :
    (l ++ [b]).getD k d = b := by
  subst hk; simp [List.getD_eq_getElem?_getD]

theorem E_getD_left {α : Type} (l : List α) (b d : α) (k : ℕ) (hk : k < l.length) :
    (l ++ [b]).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem E_snoc_fold (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl E_stp x =
      gs.foldl E_stp x ++ [g.op.eval (g.inputs.map fun i => (gs.foldl E_stp x).getD i false)] := by
  simp [List.foldl_append, E_stp]

theorem E_oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem E_sa_val {m : ℕ} (k : Fin (m + 1)) (v : Fin m) :
    (k.succAbove v).val = if v.val < k.val then v.val else v.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (by simp [Fin.lt_def] at h2 ⊢; omega)
  · exact absurd h2 (by simp [Fin.lt_def] at h1 ⊢; omega)
  · rfl

def E_rho (p r : ℕ) (i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def E_rg (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (E_rho p r)⟩

theorem E_sim (Q : Prop) (p r B : ℕ) (X X' : List Bool) (hl : X.length = X'.length + 1)
    (hp : p ≤ X'.length) (hr : r < X'.length ∨ B ≤ r)
    (hbase : ∀ i, (i = p → Q) → X'.getD (E_rho p r i) false = X.getD i false) :
    ∀ Bs : List Gate, X'.length + Bs.length ≤ B → (∀ g ∈ Bs, ∀ i ∈ g.inputs, i = p → Q) →
      ∀ i, (i = p → Q) →
      ((Bs.map (E_rg p r)).foldl E_stp X').getD (E_rho p r i) false =
        (Bs.foldl E_stp X).getD i false := by
  intro Bs
  induction Bs using List.reverseRecOn with
  | nil =>
    intro _ _ i hi
    exact hbase i hi
  | append_singleton Bs g ih =>
    intro hB hQ i hiQ
    rw [List.length_append, List.length_singleton] at hB
    have ih' := ih (by omega) (fun g' hg' => hQ g' (List.mem_append_left _ hg'))
    have hv : (E_rg p r g).op.eval ((E_rg p r g).inputs.map fun i =>
        ((Bs.map (E_rg p r)).foldl E_stp X').getD i false) =
        g.op.eval (g.inputs.map fun i => (Bs.foldl E_stp X).getD i false) := by
      show g.op.eval ((g.inputs.map (E_rho p r)).map fun i =>
        ((Bs.map (E_rg p r)).foldl E_stp X').getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact ih' j (hQ g (by simp) j hj)
    rw [List.map_append, List.map_singleton, E_snoc_fold, E_snoc_fold, hv, E_getD_snoc, E_getD_snoc,
      E_len, E_len, List.length_map]
    simp only [hl]
    have hi := ih' i hiQ
    rcases Nat.lt_trichotomy i p with h | h | h
    · have hr' : E_rho p r i = i := by unfold E_rho; rw [E_ifp h]
      rw [hr'] at hi ⊢
      rw [E_ifp (by omega), E_ifp (by omega)]
      exact hi
    · have hr' : E_rho p r i = r := by unfold E_rho; rw [E_ifn (by omega), E_ifp h]
      rw [hr'] at hi ⊢
      rcases hr with h1 | h1
      · rw [E_ifp (by omega), E_ifp (by omega)]
        exact hi
      · rw [E_ifn (by omega), E_ifn (by omega), E_ifp (by omega), ← hi]
        symm
        exact List.getD_eq_default _ _ (by rw [E_len, List.length_map]; omega)
    · have hr' : E_rho p r i = i - 1 := by unfold E_rho; rw [E_ifn (by omega), E_ifn (by omega)]
      rw [hr'] at hi ⊢
      by_cases h2 : i < X'.length + 1 + Bs.length
      · rw [E_ifp (by omega), E_ifp h2]
        exact hi
      · by_cases h3 : i = X'.length + 1 + Bs.length
        · rw [E_ifn (by omega), E_ifp (by omega), E_ifn h2, E_ifp h3]
        · rw [E_ifn (by omega), E_ifn (by omega), E_ifn h2, E_ifn h3]

theorem E_bool_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp at h ⊢

theorem E_pre (gs : List Gate) (X : List Bool) (i : ℕ) (hi : i < X.length) :
    (gs.foldl E_stp X).getD i false = X.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [E_snoc_fold, E_getD_left _ _ _ _ (by rw [E_len]; omega)]
    exact ih

theorem E_stable (G1 G2 : List Gate) (g : Gate) (X : List Bool) (p : ℕ)
    (hp : p = X.length + G1.length) :
    ((G1 ++ g :: G2).foldl E_stp X).getD p false =
      g.op.eval (g.inputs.map fun i => (G1.foldl E_stp X).getD i false) := by
  rw [List.foldl_append, List.foldl_cons, E_pre _ _ _ (by simp [E_stp, E_len]; omega)]
  exact E_getD_last _ _ _ _ (by rw [E_len]; exact hp)

theorem E_colstep (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : Circuit)
    (hrep : ∀ (u : Fin n) (v : Fin m), C.eval (oneEach u (k.succAbove v)) = A u (k.succAbove v)) :
    ∃ C' : Circuit, C'.size = C.size ∧ (FanInTwo C → FanInTwo C') ∧
      Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C' ∧
      (∀ u : Fin n, ((∃ g ∈ C'.gates, u.val ∈ g.inputs) ∨ C'.output = u.val) →
        ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧
      (∀ v : Fin m, ((∃ g ∈ C'.gates, n + v.val ∈ g.inputs) ∨ C'.output = n + v.val) →
        ((∃ g ∈ C.gates, n + (k.succAbove v).val ∈ g.inputs) ∨
          C.output = n + (k.succAbove v).val)) := by
  have hk : k.val ≤ m := Nat.lt_succ_iff.mp k.isLt
  refine ⟨⟨C.gates.map (E_rg (n + k.val) (n + m + 1 + C.gates.length)),
    E_rho (n + k.val) (n + m + 1 + C.gates.length) C.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show (C.gates.map _).length = C.gates.length
    rw [List.length_map]
  · intro hF g hg
    have hg' : g ∈ C.gates.map (E_rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
    rw [List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    have hf := hF g0 hg0
    refine ⟨hf.1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact hf.2
  · intro u v
    have hr : (C.gates.foldl E_stp (oneEach u (k.succAbove v))).getD C.output false =
      A u (k.succAbove v) := hrep u v
    show ((C.gates.map (E_rg (n + k.val) (n + m + 1 + C.gates.length))).foldl E_stp (oneEach u v)).getD
      (E_rho (n + k.val) (n + m + 1 + C.gates.length) C.output) false = A u (k.succAbove v)
    rw [← hr]
    have hlx : (oneEach u v).length = n + m := by simp [oneEach]
    have hlx2 : (oneEach u (k.succAbove v)).length = n + m + 1 := by simp [oneEach]; omega
    refine E_sim True (n + k.val) (n + m + 1 + C.gates.length) (n + m + 1 + C.gates.length)
      (oneEach u (k.succAbove v)) (oneEach u v)
      (by rw [hlx, hlx2]) (by rw [hlx]; omega) (Or.inr le_rfl) ?_ C.gates (by rw [hlx]; omega)
      (fun _ _ _ _ _ => trivial) C.output (fun _ => trivial)
    intro i _
    apply E_bool_iff
    rw [E_oe, E_oe, E_sa_val]
    have hu := u.isLt
    have hv := v.isLt
    unfold E_rho
    split_ifs <;> omega
  · intro u hu
    have hul := u.isLt
    have key : ∀ i, E_rho (n + k.val) (n + m + 1 + C.gates.length) i = u.val → i = u.val := by
      intro i
      unfold E_rho
      split_ifs <;> omega
    rcases hu with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ C.gates.map (E_rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      have hmem' : u.val ∈ g0.inputs.map (E_rho (n + k.val) (n + m + 1 + C.gates.length)) := hmem
      rw [List.mem_map] at hmem'
      obtain ⟨i, hi, hiu⟩ := hmem'
      have := key i hiu
      subst this
      exact Or.inl ⟨g0, hg0, hi⟩
    · exact Or.inr (key _ ho)
  · intro v hv
    have hvl := v.isLt
    have key : ∀ i, E_rho (n + k.val) (n + m + 1 + C.gates.length) i = n + v.val →
        i = n + (k.succAbove v).val := by
      intro i
      rw [E_sa_val]
      unfold E_rho
      split_ifs <;> omega
    rcases hv with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ C.gates.map (E_rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      have hmem' : n + v.val ∈ g0.inputs.map (E_rho (n + k.val) (n + m + 1 + C.gates.length)) := hmem
      rw [List.mem_map] at hmem'
      obtain ⟨i, hi, hiu⟩ := hmem'
      have := key i hiu
      subst this
      exact Or.inl ⟨g0, hg0, hi⟩
    · exact Or.inr (key _ ho)

theorem E_delstep (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : Circuit)
    (G1 G2 : List Gate) (h : Gate) (r : ℕ) (Q : Prop)
    (hC : C.gates = G1 ++ h :: G2) (hF : FanInTwo C)
    (hrep : ∀ (u : Fin n) (v : Fin m), C.eval (oneEach u (k.succAbove v)) = A u (k.succAbove v))
    (hr : r < n + m + 1 + G1.length ∨ n + m + 1 + C.gates.length ≤ r)
    (hrin : r < n + m + 1 → r ∈ h.inputs)
    (hQ2 : ∀ g ∈ G2, ∀ i ∈ g.inputs, i = n + m + 1 + G1.length → Q)
    (hQo : C.output = n + m + 1 + G1.length → Q)
    (hv : Q → ∀ (u : Fin n) (v : Fin m),
      h.op.eval (h.inputs.map fun i => (G1.foldl E_stp (oneEach u (k.succAbove v))).getD i false) =
        (G1.foldl E_stp (oneEach u (k.succAbove v))).getD r false) :
    ∃ C1 : Circuit, C1.size + 1 = C.size ∧ FanInTwo C1 ∧
      (∀ (u : Fin n) (v : Fin m), C1.eval (oneEach u (k.succAbove v)) = A u (k.succAbove v)) ∧
      (∀ i < n + m + 1, ((∃ g ∈ C1.gates, i ∈ g.inputs) ∨ C1.output = i) →
        ((∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i)) := by
  have hlen : C.gates.length = G1.length + G2.length + 1 := by rw [hC]; simp; omega
  refine ⟨⟨G1 ++ G2.map (E_rg (n + m + 1 + G1.length) r), E_rho (n + m + 1 + G1.length) r C.output⟩,
    ?_, ?_, ?_, ?_⟩
  · show (G1 ++ G2.map _).length + 1 = C.gates.length
    rw [hlen]
    simp
  · intro g hg
    have hg' : g ∈ G1 ++ G2.map (E_rg (n + m + 1 + G1.length) r) := hg
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
    have h0 : (C.gates.foldl E_stp (oneEach u (k.succAbove v))).getD C.output false =
      A u (k.succAbove v) := hrep u v
    show ((G1 ++ G2.map (E_rg (n + m + 1 + G1.length) r)).foldl E_stp
      (oneEach u (k.succAbove v))).getD (E_rho (n + m + 1 + G1.length) r C.output) false = _
    rw [← h0, hC, List.foldl_append, List.foldl_append, List.foldl_cons]
    have hl1 : (G1.foldl E_stp (oneEach u (k.succAbove v))).length = n + m + 1 + G1.length := by
      rw [E_len, hx]
    refine E_sim Q (n + m + 1 + G1.length) r (n + m + 1 + C.gates.length)
      (E_stp (G1.foldl E_stp (oneEach u (k.succAbove v))) h) (G1.foldl E_stp (oneEach u (k.succAbove v)))
      ?_ ?_ ?_ ?_ G2 ?_ hQ2 C.output hQo
    · simp [E_stp]
    · rw [hl1]
    · rw [hl1]
      exact hr
    · intro i hi
      show (G1.foldl E_stp (oneEach u (k.succAbove v))).getD (E_rho (n + m + 1 + G1.length) r i) false =
        (G1.foldl E_stp (oneEach u (k.succAbove v)) ++ [_]).getD i false
      rw [E_getD_snoc, hl1]
      unfold E_rho
      by_cases h1 : i < n + m + 1 + G1.length
      · rw [E_ifp h1, E_ifp h1]
      · by_cases h2 : i = n + m + 1 + G1.length
        · rw [E_ifn h1, E_ifp h2, E_ifn h1, E_ifp h2]
          exact (hv (hi h2) u v).symm
        · rw [E_ifn h1, E_ifn h2, E_ifn h1, E_ifn h2]
          exact List.getD_eq_default _ _ (by rw [hl1]; omega)
    · rw [hl1, hlen]
      omega
  · intro i hi hrd
    have key : ∀ j, E_rho (n + m + 1 + G1.length) r j = i →
        j = i ∨ (j = n + m + 1 + G1.length ∧ r = i) := by
      intro j
      unfold E_rho
      split_ifs <;> omega
    rcases hrd with ⟨g, hg, hmem⟩ | ho
    · have hg' : g ∈ G1 ++ G2.map (E_rg (n + m + 1 + G1.length) r) := hg
      rw [List.mem_append, List.mem_map] at hg'
      rcases hg' with h1 | ⟨g0, hg0, rfl⟩
      · exact Or.inl ⟨g, by rw [hC]; simp [h1], hmem⟩
      · have hmem' : i ∈ g0.inputs.map (E_rho (n + m + 1 + G1.length) r) := hmem
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

theorem E_fin (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : Circuit)
    (G1 G2 : List Gate) (h : Gate) (r : ℕ) (Q : Prop)
    (hC : C.gates = G1 ++ h :: G2) (hF : FanInTwo C) (hrep : Represents A C)
    (hr : r < n + m + 1 + G1.length ∨ n + m + 1 + C.gates.length ≤ r)
    (hrin : r < n + m + 1 → r ∈ h.inputs)
    (hQ2 : ∀ g ∈ G2, ∀ i ∈ g.inputs, i = n + m + 1 + G1.length → Q)
    (hQo : C.output = n + m + 1 + G1.length → Q)
    (hv : Q → ∀ (u : Fin n) (v : Fin m),
      h.op.eval (h.inputs.map fun i => (G1.foldl E_stp (oneEach u (k.succAbove v))).getD i false) =
        (G1.foldl E_stp (oneEach u (k.succAbove v))).getD r false) :
    ∃ C2 : Circuit, FanInTwo C2 ∧
      Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ C2.size + 1 ≤ C.size ∧
      (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) →
        ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧
      (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) →
        ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨
          C.output = (n + (k.succAbove v).val))) := by
  obtain ⟨C1, hs1, hF1, hrep1, hrd1⟩ := E_delstep n m A k C G1 G2 h r Q hC hF
    (fun u v => hrep u (k.succAbove v)) hr hrin hQ2 hQo hv
  obtain ⟨C2, hs2, hF2, hrep2, hu2, hv2⟩ := E_colstep n m A k C1 hrep1
  refine ⟨C2, hF2 hF1, hrep2, by omega, ?_, ?_⟩
  · intro u hu
    exact hrd1 u.val (by have := u.isLt; omega) (hu2 u hu)
  · intro v hv'
    exact hrd1 _ (by have := (k.succAbove v).isLt; omega) (hv2 v hv')

theorem E_shape (g : Gate)
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

theorem E_and_ev (W : List Bool) (a b : ℕ) :
    (⟨GateOp.and, [a, b]⟩ : Gate).op.eval
      ((⟨GateOp.and, [a, b]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (W.getD a false && W.getD b false) := by
  simp [GateOp.eval]

theorem E_or_ev (W : List Bool) (a b : ℕ) :
    (⟨GateOp.or, [a, b]⟩ : Gate).op.eval
      ((⟨GateOp.or, [a, b]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (W.getD a false || W.getD b false) := by
  simp [GateOp.eval]

theorem E_not_ev (W : List Bool) (a : ℕ) :
    (⟨GateOp.not, [a]⟩ : Gate).op.eval
      ((⟨GateOp.not, [a]⟩ : Gate).inputs.map fun i => W.getD i false) =
      (!W.getD a false) := by
  simp [GateOp.eval]

theorem E_ck (n m : ℕ) (k : Fin (m + 1)) (u : Fin n) (v : Fin m) (gs : List Gate) :
    (gs.foldl E_stp (oneEach u (k.succAbove v))).getD (n + k.val) false = false := by
  have hx : (oneEach u (k.succAbove v)).length = n + m + 1 := by simp [oneEach]; omega
  rw [E_pre _ _ _ (by rw [hx]; have := k.isLt; omega)]
  cases hb : (oneEach u (k.succAbove v)).getD (n + k.val) false with
  | false => rfl
  | true =>
    rw [E_oe] at hb
    rcases hb with hb | hb
    · have := u.isLt
      omega
    · exact absurd (Fin.ext (by omega)) (Fin.succAbove_ne k v)

def E_rr (p B a : ℕ) : ℕ := if a < p then a else B

theorem E_rr_val (W : List Bool) (p B a : ℕ) (hW : W.length = p) (hB : p ≤ B) :
    W.getD (E_rr p B a) false = W.getD a false := by
  unfold E_rr
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem E_rr_hr (p B a : ℕ) : E_rr p B a < p ∨ B ≤ E_rr p B a := by
  unfold E_rr
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr le_rfl

theorem E_rr_in (p B N a : ℕ) (hN : N ≤ B) (h : E_rr p B a < N) : E_rr p B a = a := by
  unfold E_rr at h ⊢
  split_ifs at h ⊢ <;> omega

theorem E_main : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.Represents.Represents A C → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C hF hkind hrep hlist hnc
  obtain ⟨g, hg, hc⟩ := hlist
  obtain ⟨G1, G2, hC⟩ := List.append_of_mem hg
  have hlen : C.gates.length = G1.length + G2.length + 1 := by rw [hC]; simp; omega
  have hx : ∀ (u : Fin n) (v : Fin m), (oneEach u (k.succAbove v)).length = n + m + 1 := by
    intro u v
    simp [oneEach]
    omega
  have hW1 : ∀ (u : Fin n) (v : Fin m),
      (G1.foldl E_stp (oneEach u (k.succAbove v))).length = n + m + 1 + G1.length := by
    intro u v
    rw [E_len, hx]
  rcases E_shape g (hkind g hg) with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, rfl⟩
  · refine E_fin n m A k C G1 G2 _ (n + m + 1 + C.gates.length) True hC hF hrep (Or.inr le_rfl)
      (by intro h; omega) (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
    intro _ u v
    rw [List.getD_eq_default _ _ (by rw [hW1]; omega), E_and_ev]
    simp at hc
    rcases hc with h1 | h1
    · subst h1
      rw [E_ck]
      rfl
    · subst h1
      rw [E_ck]
      simp
  · simp at hc
    rcases hc with h1 | h1
    · subst h1
      refine E_fin n m A k C G1 G2 _ (E_rr (n + m + 1 + G1.length) (n + m + 1 + C.gates.length) b) True
        hC hF hrep (E_rr_hr _ _ _) ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
      · intro h
        rw [E_rr_in _ _ (n + m + 1) _ (by omega) h]
        simp
      · intro _ u v
        rw [E_rr_val _ _ _ _ (hW1 u v) (by omega), E_or_ev, E_ck]
        simp
    · subst h1
      refine E_fin n m A k C G1 G2 _ (E_rr (n + m + 1 + G1.length) (n + m + 1 + C.gates.length) a) True
        hC hF hrep (E_rr_hr _ _ _) ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
      · intro h
        rw [E_rr_in _ _ (n + m + 1) _ (by omega) h]
        simp
      · intro _ u v
        rw [E_rr_val _ _ _ _ (hW1 u v) (by omega), E_or_ev, E_ck]
        simp
  · simp at hc
    subst hc
    by_cases ho : C.output = n + m + 1 + G1.length
    · exfalso
      obtain ⟨u, u2, v, v2, hne⟩ := hnc
      have ht : ∀ (u : Fin n) (v : Fin m), A u (k.succAbove v) = true := by
        intro u v
        have h0 : (C.gates.foldl E_stp (oneEach u (k.succAbove v))).getD C.output false =
          A u (k.succAbove v) := hrep u (k.succAbove v)
        rw [← h0, ho, hC, E_stable G1 G2 _ _ _ (by rw [hx]), E_not_ev, E_ck]
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
            ((G1 ++ (⟨GateOp.not, [n + k.val]⟩ : Gate) :: G2a).foldl E_stp
              (oneEach u (k.succAbove v))).length = n + m + 1 + (G1.length + G2a.length + 1) := by
          intro u v
          rw [E_len, hx, hl']
        have hT : ∀ (u : Fin n) (v : Fin m),
            ((G1 ++ (⟨GateOp.not, [n + k.val]⟩ : Gate) :: G2a).foldl E_stp
              (oneEach u (k.succAbove v))).getD (n + m + 1 + G1.length) false = true := by
          intro u v
          rw [E_stable G1 G2a _ _ _ (by rw [hx]), E_not_ev, E_ck]
          rfl
        have hg'C : g' ∈ C.gates := by rw [hC']; simp
        rcases E_shape g' (hkind g' hg'C) with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, rfl⟩
        · simp at hp'
          rcases hp' with h1 | h1
          · subst h1
            refine E_fin n m A k C _ G2b _
              (E_rr (n + m + 1 + (G1.length + G2a.length + 1)) (n + m + 1 + C.gates.length) b) True
              hC' hF hrep ?_ ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
            · rw [hl']
              exact E_rr_hr _ _ _
            · intro h
              rw [E_rr_in _ _ (n + m + 1) _ (by omega) h]
              simp
            · intro _ u v
              rw [E_rr_val _ _ _ _ (hW2 u v) (by omega), E_and_ev, hT]
              simp
          · subst h1
            refine E_fin n m A k C _ G2b _
              (E_rr (n + m + 1 + (G1.length + G2a.length + 1)) (n + m + 1 + C.gates.length) a) True
              hC' hF hrep ?_ ?_ (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
            · rw [hl']
              exact E_rr_hr _ _ _
            · intro h
              rw [E_rr_in _ _ (n + m + 1) _ (by omega) h]
              simp
            · intro _ u v
              rw [E_rr_val _ _ _ _ (hW2 u v) (by omega), E_and_ev, hT]
              simp
        · refine E_fin n m A k C _ G2b _ (n + m + 1 + G1.length) True hC' hF hrep
            (Or.inl (by rw [hl']; omega)) (by intro h; omega) (fun _ _ _ _ _ => trivial)
            (fun _ => trivial) ?_
          intro _ u v
          simp at hp'
          rcases hp' with h1 | h1
          · subst h1
            rw [E_or_ev, hT]
            simp
          · subst h1
            rw [E_or_ev, hT]
            simp
        · simp at hp'
          subst hp'
          refine E_fin n m A k C _ G2b _ (n + m + 1 + C.gates.length) True hC' hF hrep
            (Or.inr le_rfl) (by intro h; omega) (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
          intro _ u v
          rw [E_not_ev, hT, List.getD_eq_default _ _ (by rw [hW2]; omega)]
          rfl
      · refine E_fin n m A k C G1 G2 _ (n + m + 1 + C.gates.length) False hC hF hrep (Or.inr le_rfl)
          (by intro h; omega) ?_ ho ?_
        · intro g' hg' i hi hip
          exact hread ⟨g', hg', hip ▸ hi⟩
        · intro hf
          exact hf.elim



def dg : Gate := ⟨GateOp.or, []⟩

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def M2 (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

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

theorem pre (gs hs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length + gs.length) :
    ((gs ++ hs).foldl stp x).getD w false = (gs.foldl stp x).getD w false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, snoc_fold, getD_snoc, len, ifp (by simp; omega), ih]

theorem inp (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (gs.foldl stp x).getD w false = x.getD w false := by
  have := pre [] gs x w (by simpa using hw)
  simpa using this

theorem top (gs : List Gate) (g : Gate) (x : List Bool) :
    ((gs ++ [g]).foldl stp x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl stp x).getD i false) := by
  rw [snoc_fold, getD_snoc, len, ifn (by omega), ifp rfl]

theorem beyond (gs : List Gate) (x : List Bool) (w : ℕ) (hw : x.length + gs.length ≤ w) :
    (gs.foldl stp x).getD w false = false := by
  apply List.getD_eq_default
  rw [len]; exact hw

theorem wire_at (gs : List Gate) (x : List Bool) : ∀ i, i < gs.length →
    (gs.foldl stp x).getD (x.length + i) false =
      (gs.getD i dg).op.eval ((gs.getD i dg).inputs.map fun w =>
        if w < x.length + i then (gs.foldl stp x).getD w false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; simp at hi
  | append_singleton gs g ih =>
    intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases h : i < gs.length
    · rw [pre gs [g] x _ (by omega), ih i h, getD_left gs g dg i h]
      congr 1
      apply List.map_congr_left
      intro w _
      split_ifs with hw
      · rw [pre gs [g] x _ (by omega)]
      · rfl
    · have hi' : i = gs.length := by omega
      subst hi'
      rw [top, getD_last gs g dg _ rfl]
      congr 1
      apply List.map_congr_left
      intro w _
      split_ifs with hw
      · rw [pre gs [g] x _ hw]
      · rw [beyond gs x w (by omega)]

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega


def interp (W : List Bool) (a : Sum Bool ℕ) : Bool := Sum.elim id (fun w => W.getD w false) a

def comb : GateOp → List (Sum Bool ℕ) → Sum (Sum Bool ℕ) Gate
  | GateOp.not, [] => Sum.inl (Sum.inl true)
  | GateOp.not, (Sum.inl c :: _) => Sum.inl (Sum.inl (!c))
  | GateOp.not, (Sum.inr w :: _) => Sum.inr ⟨GateOp.not, [w]⟩
  | GateOp.and, [] => Sum.inl (Sum.inl true)
  | GateOp.and, [a] => Sum.inl a
  | GateOp.and, [Sum.inl c, b] => if c then Sum.inl b else Sum.inl (Sum.inl false)
  | GateOp.and, [Sum.inr w, Sum.inl c] => if c then Sum.inl (Sum.inr w) else Sum.inl (Sum.inl false)
  | GateOp.and, [Sum.inr w, Sum.inr w'] => Sum.inr ⟨GateOp.and, [w, w']⟩
  | GateOp.or, [] => Sum.inl (Sum.inl false)
  | GateOp.or, [a] => Sum.inl a
  | GateOp.or, [Sum.inl c, b] => if c then Sum.inl (Sum.inl true) else Sum.inl b
  | GateOp.or, [Sum.inr w, Sum.inl c] => if c then Sum.inl (Sum.inl true) else Sum.inl (Sum.inr w)
  | GateOp.or, [Sum.inr w, Sum.inr w'] => Sum.inr ⟨GateOp.or, [w, w']⟩
  | _, _ => Sum.inl (Sum.inl false)

def Ar (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)

theorem comb_sem (op : GateOp) (r : List (Sum Bool ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hr : r.length ≤ 2) (W : List Bool) :
    (∀ a, comb op r = Sum.inl a → interp W a = op.eval (r.map (interp W)) ∧
      (∀ w, a = Sum.inr w → Sum.inr w ∈ r)) ∧
    (∀ g', comb op r = Sum.inr g' →
      g'.op.eval (g'.inputs.map (fun w => W.getD w false)) = op.eval (r.map (interp W)) ∧
      Ar g' ∧ ∀ w ∈ g'.inputs, Sum.inr w ∈ r) := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [comb, interp, GateOp.eval]
  · rcases hop with rfl | rfl | rfl <;> rcases a with ca | wa <;>
      simp [comb, interp, GateOp.eval, Ar]
  · rcases hop with rfl | rfl | rfl <;> rcases a with ca | wa <;> rcases b with cb | wb <;>
      (try cases ca) <;> (try cases cb) <;> simp [comb, interp, GateOp.eval, Ar]
  · simp at hr

def rin (res : List (Sum Bool ℕ)) (g : Gate) : List (Sum Bool ℕ) :=
  g.inputs.map (fun i => res.getD i (Sum.inl false))

def stepR (N : ℕ) (st : List Gate × List (Sum Bool ℕ)) (g : Gate) : List Gate × List (Sum Bool ℕ) :=
  Sum.elim (fun a => (st.1, st.2 ++ [a]))
    (fun g' => (st.1 ++ [g'], st.2 ++ [Sum.inr (N + st.1.length)])) (comb g.op (rin st.2 g))

def runR (N : ℕ) (gs : List Gate) : List Gate × List (Sum Bool ℕ) :=
  gs.foldl (stepR N) ([], (List.range N).map Sum.inr)

def PL (N : ℕ) (hs : List Gate) : Prop :=
  (∀ g ∈ hs, Ar g) ∧ ∀ j < hs.length, ∀ i ∈ (hs.getD j dg).inputs, i < N + j

def Inv (N : ℕ) (gs : List Gate) (st : List Gate × List (Sum Bool ℕ)) : Prop :=
  st.2.length = N + gs.length ∧ st.1.length ≤ gs.length ∧
  (∀ k w, st.2.getD k (Sum.inl false) = Sum.inr w → w < N + st.1.length) ∧
  PL N st.1 ∧
  ∀ x : List Bool, x.length = N → ∀ k,
    (gs.foldl stp x).getD k false = interp (st.1.foldl stp x) (st.2.getD k (Sum.inl false))

theorem rget (N k : ℕ) : ((List.range N).map (Sum.inr : ℕ → Sum Bool ℕ)).getD k (Sum.inl false) =
    if k < N then Sum.inr k else Sum.inl false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem interp_ext (W : List Bool) (b : Bool) (a : Sum Bool ℕ) (h : ∀ w, a = Sum.inr w → w < W.length) :
    interp (W ++ [b]) a = interp W a := by
  rcases a with c | w
  · rfl
  · exact getD_left W b false w (h w rfl)

theorem inv_run (N : ℕ) (gs : List Gate)
    (hF : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    Inv N gs (runR N gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [runR], Nat.le_refl _, ?_, ⟨fun g hg => by simp [runR] at hg, fun j hj => by simp [runR] at hj⟩, ?_⟩
    · intro k w h
      simp only [runR, List.foldl_nil] at h
      rw [rget] at h
      split_ifs at h with hk
      · have := Sum.inr.inj h
        simp only [runR, List.foldl_nil, List.length_nil]
        omega
    · intro x hx k
      simp only [runR, List.foldl_nil]
      rw [rget]
      split_ifs with hk
      · rfl
      · exact List.getD_eq_default _ _ (by omega)
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hF g' (List.mem_append_left _ hg'))
    obtain ⟨hop, hlen⟩ := hF g (by simp)
    have erun : runR N (gs ++ [g]) = stepR N (runR N gs) g := by
      unfold runR
      rw [List.foldl_append]
      rfl
    rw [erun]
    generalize runR N gs = st at ih'
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih'
    have hr : (rin st.2 g).length ≤ 2 := by
      unfold rin
      rw [List.length_map]
      exact hlen
    have semr : ∀ x : List Bool, x.length = N →
        g.op.eval (g.inputs.map (fun i => (gs.foldl stp x).getD i false)) =
          g.op.eval ((rin st.2 g).map (interp (st.1.foldl stp x))) := by
      intro x hx
      congr 1
      unfold rin
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact i5 x hx i
    have rmem : ∀ w, Sum.inr w ∈ rin st.2 g → w < N + st.1.length := by
      intro w hw
      unfold rin at hw
      rw [List.mem_map] at hw
      obtain ⟨i, _, hi⟩ := hw
      exact i3 i w hi
    have oldlt : ∀ (x : List Bool), x.length = N → ∀ k, k < N + gs.length →
        ((gs ++ [g]).foldl stp x).getD k false = (gs.foldl stp x).getD k false := by
      intro x hx k hk
      exact pre gs [g] x k (by omega)
    have oldtop : ∀ (x : List Bool), x.length = N →
        ((gs ++ [g]).foldl stp x).getD (N + gs.length) false =
          g.op.eval ((rin st.2 g).map (interp (st.1.foldl stp x))) := by
      intro x hx
      have := top gs g x
      rw [hx] at this
      rw [this, semr x hx]
    have oldgt : ∀ (x : List Bool), x.length = N → ∀ k, N + gs.length < k →
        ((gs ++ [g]).foldl stp x).getD k false = false := by
      intro x hx k hk
      exact beyond _ x k (by rw [List.length_append, List.length_singleton]; omega)
    cases hc : comb g.op (rin st.2 g) with
    | inl a =>
      have e : stepR N st g = (st.1, st.2 ++ [a]) := by
        unfold stepR
        rw [hc]
        rfl
      rw [e]
      refine ⟨by simp [i1]; omega, by simp; omega, ?_, i4, ?_⟩
      · intro k w h
        show w < N + st.1.length
        change (st.2 ++ [a]).getD k (Sum.inl false) = Sum.inr w at h
        by_cases hk : k < st.2.length
        · rw [getD_left _ _ _ _ hk] at h
          exact i3 k w h
        · by_cases hk2 : k = st.2.length
          · rw [getD_last _ _ _ _ hk2] at h
            exact rmem w (((comb_sem g.op _ hop hr []).1 a hc).2 w h)
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)] at h
            exact absurd h (by simp)
      · intro x hx k
        show _ = interp (st.1.foldl stp x) ((st.2 ++ [a]).getD k (Sum.inl false))
        by_cases hk : k < st.2.length
        · rw [getD_left _ _ _ _ hk, oldlt x hx k (by omega)]
          exact i5 x hx k
        · by_cases hk2 : k = st.2.length
          · rw [getD_last _ _ _ _ hk2, hk2, i1, oldtop x hx]
            exact (((comb_sem g.op _ hop hr _).1 a hc).1).symm
          · rw [List.getD_eq_default (st.2 ++ [a]) _
              (by rw [List.length_append, List.length_singleton]; omega), oldgt x hx k (by omega)]
            rfl
    | inr g' =>
      have e : stepR N st g = (st.1 ++ [g'], st.2 ++ [Sum.inr (N + st.1.length)]) := by
        unfold stepR
        rw [hc]
        rfl
      rw [e]
      have s23 := ((comb_sem g.op _ hop hr []).2 g' hc).2
      refine ⟨by simp [i1]; omega, by simp; omega, ?_, ⟨?_, ?_⟩, ?_⟩
      · intro k w h
        show w < N + (st.1 ++ [g']).length
        rw [List.length_append, List.length_singleton]
        change (st.2 ++ [Sum.inr (N + st.1.length)]).getD k (Sum.inl false) = Sum.inr w at h
        by_cases hk : k < st.2.length
        · rw [getD_left _ _ _ _ hk] at h
          have := i3 k w h
          omega
        · by_cases hk2 : k = st.2.length
          · rw [getD_last _ _ _ _ hk2] at h
            have := Sum.inr.inj h
            omega
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)] at h
            exact absurd h (by simp)
      · intro q hq
        change q ∈ st.1 ++ [g'] at hq
        rw [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact i4.1 q hq
        · exact s23.1
      · intro j hj i hi
        change j < (st.1 ++ [g']).length at hj
        rw [List.length_append, List.length_singleton] at hj
        change i ∈ ((st.1 ++ [g']).getD j dg).inputs at hi
        by_cases hj1 : j < st.1.length
        · rw [getD_left _ _ _ _ hj1] at hi
          exact i4.2 j hj1 i hi
        · have hj2 : j = st.1.length := by omega
          rw [getD_last _ _ _ _ hj2] at hi
          have := rmem i (s23.2 i hi)
          omega
      · intro x hx k
        show _ = interp ((st.1 ++ [g']).foldl stp x)
          ((st.2 ++ [Sum.inr (N + st.1.length)]).getD k (Sum.inl false))
        have hW : (st.1.foldl stp x).length = N + st.1.length := by rw [len, hx]
        rw [snoc_fold st.1 g' x]
        by_cases hk : k < st.2.length
        · rw [getD_left _ _ _ _ hk, oldlt x hx k (by omega),
            interp_ext _ _ _ (fun w hw => by rw [hW]; exact i3 k w hw)]
          exact i5 x hx k
        · by_cases hk2 : k = st.2.length
          · rw [getD_last _ _ _ _ hk2, hk2, i1, oldtop x hx]
            show _ = ((st.1.foldl stp x) ++ _).getD (N + st.1.length) false
            rw [getD_last _ _ _ _ hW.symm]
            exact (((comb_sem g.op _ hop hr _).2 g' hc).1).symm
          · rw [List.getD_eq_default (st.2 ++ [Sum.inr (N + st.1.length)]) _
              (by rw [List.length_append, List.length_singleton]; omega), oldgt x hx k (by omega)]
            rfl

def RRg (g : Gate) (w : ℕ) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ w ∈ g.inputs) ∨ (g.op = GateOp.not ∧ g.inputs.head? = some w)

def RR (gs : List Gate) (w : ℕ) : Prop := ∃ g ∈ gs, RRg g w

def Lst (hs : List Gate) (w : ℕ) : Prop := ∃ g ∈ hs, w ∈ g.inputs

theorem comb_reads (op : GateOp) (r : List (Sum Bool ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hr : r.length ≤ 2) :
    (∀ w, comb op r = Sum.inl (Sum.inr w) →
      (op = GateOp.and ∨ op = GateOp.or) ∧ ∀ w', Sum.inr w' ∈ r → w' = w) ∧
    (∀ g', comb op r = Sum.inr g' →
      ((op = GateOp.and ∨ op = GateOp.or) ∧ ∃ w w', r = [Sum.inr w, Sum.inr w'] ∧ g'.inputs = [w, w']) ∨
      (op = GateOp.not ∧ ∃ w t, r = Sum.inr w :: t ∧ g'.inputs = [w])) := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [comb]
  · rcases hop with rfl | rfl | rfl <;> rcases a with ca | wa <;>
      simp [comb]
  · rcases hop with rfl | rfl | rfl <;> rcases a with ca | wa <;> rcases b with cb | wb <;>
      (try cases ca) <;> (try cases cb) <;> simp [comb]
  · simp at hr

theorem rr_mono {gs : List Gate} (g : Gate) {w : ℕ} (h : RR gs w) : RR (gs ++ [g]) w := by
  obtain ⟨q, hq, hw⟩ := h
  exact ⟨q, List.mem_append_left _ hq, hw⟩

theorem lst_mono {hs : List Gate} (g : Gate) {w : ℕ} (h : Lst hs w) : Lst (hs ++ [g]) w := by
  obtain ⟨q, hq, hw⟩ := h
  exact ⟨q, List.mem_append_left _ hq, hw⟩

def RInv (N : ℕ) (gs : List Gate) (st : List Gate × List (Sum Bool ℕ)) : Prop :=
  (∀ k < N, st.2.getD k (Sum.inl false) = Sum.inr k) ∧
  (∀ k w, st.2.getD k (Sum.inl false) = Sum.inr w → w < N → k = w ∨ RR gs w) ∧
  (∀ w < N, Lst st.1 w → RR gs w) ∧
  (st.1.length = gs.length → ∀ w < N, RR gs w → Lst st.1 w)

theorem rinv_run (N : ℕ) (gs : List Gate)
    (hF : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    RInv N gs (runR N gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      simp only [runR, List.foldl_nil]
      rw [rget, ifp hk]
    · intro k w h hw
      simp only [runR, List.foldl_nil] at h
      rw [rget] at h
      split_ifs at h with hk
      · exact Or.inl (Sum.inr.inj h)
    · intro w _ h
      obtain ⟨q, hq, _⟩ := h
      simp [runR] at hq
    · intro _ w _ h
      obtain ⟨q, hq, _⟩ := h
      simp at hq
  | append_singleton gs g ih =>
    have hFp : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
        g'.inputs.length ≤ 2 := fun g' hg' => hF g' (List.mem_append_left _ hg')
    have ih' := ih hFp
    obtain ⟨i1, i2, -, -, -⟩ := inv_run N gs hFp
    obtain ⟨hop, hlen⟩ := hF g (by simp)
    have erun : runR N (gs ++ [g]) = stepR N (runR N gs) g := by
      unfold runR
      rw [List.foldl_append]
      rfl
    rw [erun]
    generalize runR N gs = st at ih' i1 i2
    obtain ⟨r0, r2, r1, r3⟩ := ih'
    have hr : (rin st.2 g).length ≤ 2 := by
      unfold rin
      rw [List.length_map]
      exact hlen
    have F1 : (g.op = GateOp.and ∨ g.op = GateOp.or) → ∀ w, Sum.inr w ∈ rin st.2 g → w < N →
        RR (gs ++ [g]) w := by
      intro ho w hw hwN
      unfold rin at hw
      rw [List.mem_map] at hw
      obtain ⟨i, hi, hiw⟩ := hw
      rcases r2 i w hiw hwN with e | h
      · rw [e] at hi
        exact ⟨g, by simp, Or.inl ⟨ho, hi⟩⟩
      · exact rr_mono g h
    have F2 : g.op = GateOp.not → ∀ w t, rin st.2 g = Sum.inr w :: t → w < N → RR (gs ++ [g]) w := by
      intro ho w t hw hwN
      unfold rin at hw
      rcases hgi : g.inputs with _ | ⟨i, rest⟩
      · rw [hgi] at hw
        simp at hw
      · rw [hgi] at hw
        simp only [List.map_cons, List.cons.injEq] at hw
        rcases r2 i w hw.1 hwN with e | h
        · exact ⟨g, by simp, Or.inr ⟨ho, by rw [hgi, e]; rfl⟩⟩
        · exact rr_mono g h
    have F3 : ∀ w < N, w ∈ g.inputs → Sum.inr w ∈ rin st.2 g := by
      intro w hw hi
      unfold rin
      rw [List.mem_map]
      exact ⟨w, hi, r0 w hw⟩
    cases hc : comb g.op (rin st.2 g) with
    | inl a =>
      have e : stepR N st g = (st.1, st.2 ++ [a]) := by
        unfold stepR
        rw [hc]
        rfl
      rw [e]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k hk
        show (st.2 ++ [a]).getD k (Sum.inl false) = Sum.inr k
        rw [getD_left _ _ _ _ (by omega)]
        exact r0 k hk
      · intro k w h hw
        change (st.2 ++ [a]).getD k (Sum.inl false) = Sum.inr w at h
        by_cases hk : k < st.2.length
        · rw [getD_left _ _ _ _ hk] at h
          rcases r2 k w h hw with e1 | h1
          · exact Or.inl e1
          · exact Or.inr (rr_mono g h1)
        · by_cases hk2 : k = st.2.length
          · rw [getD_last _ _ _ _ hk2] at h
            rw [h] at hc
            have hcr := (comb_reads g.op _ hop hr).1 w hc
            exact Or.inr (F1 hcr.1 w (((comb_sem g.op _ hop hr []).1 _ hc).2 w rfl) hw)
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)] at h
            exact absurd h (by simp)
      · intro w hw h
        exact rr_mono g (r1 w hw h)
      · intro hl
        exfalso
        change st.1.length = (gs ++ [g]).length at hl
        rw [List.length_append, List.length_singleton] at hl
        omega
    | inr g' =>
      have e : stepR N st g = (st.1 ++ [g'], st.2 ++ [Sum.inr (N + st.1.length)]) := by
        unfold stepR
        rw [hc]
        rfl
      rw [e]
      have hB := (comb_reads g.op _ hop hr).2 g' hc
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k hk
        show (st.2 ++ [Sum.inr (N + st.1.length)]).getD k (Sum.inl false) = Sum.inr k
        rw [getD_left _ _ _ _ (by omega)]
        exact r0 k hk
      · intro k w h hw
        change (st.2 ++ [Sum.inr (N + st.1.length)]).getD k (Sum.inl false) = Sum.inr w at h
        by_cases hk : k < st.2.length
        · rw [getD_left _ _ _ _ hk] at h
          rcases r2 k w h hw with e1 | h1
          · exact Or.inl e1
          · exact Or.inr (rr_mono g h1)
        · by_cases hk2 : k = st.2.length
          · rw [getD_last _ _ _ _ hk2] at h
            have := Sum.inr.inj h
            omega
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)] at h
            exact absurd h (by simp)
      · intro w hw h
        obtain ⟨q, hq, hwq⟩ := h
        change q ∈ st.1 ++ [g'] at hq
        rw [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact rr_mono g (r1 w hw ⟨q, hq, hwq⟩)
        · rcases hB with ⟨ho, w1, w2, hr12, hg'⟩ | ⟨ho, w1, t, hr1, hg'⟩
          · rw [hg'] at hwq
            refine F1 ho w ?_ hw
            rw [hr12]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hwq
            rcases hwq with rfl | rfl <;> simp
          · rw [hg'] at hwq
            have hww : w = w1 := by simpa using hwq
            rw [hww]
            rw [hww] at hw
            exact F2 ho w1 t hr1 hw
      · intro hl w hw h
        change (st.1 ++ [g']).length = (gs ++ [g]).length at hl
        rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton] at hl
        have hl' : st.1.length = gs.length := by omega
        obtain ⟨q, hq, hwq⟩ := h
        rw [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact lst_mono g' (r3 hl' w hw ⟨q, hq, hwq⟩)
        · refine ⟨g', by simp, ?_⟩
          rcases hwq with ⟨ho, hin⟩ | ⟨ho, hhd⟩
          · have hmem := F3 w hw hin
            rcases hB with ⟨_, w1, w2, hr12, hg'⟩ | ⟨ho', _⟩
            · rw [hr12] at hmem
              rw [hg']
              simpa using hmem
            · rw [ho'] at ho
              rcases ho with ho | ho <;> cases ho
          · rcases hB with ⟨ho', _⟩ | ⟨_, w1, t, hr1, hg'⟩
            · rw [ho] at ho'
              rcases ho' with ho' | ho' <;> cases ho'
            · rcases hgi : q.inputs with _ | ⟨i, rest⟩
              · rw [hgi] at hhd
                simp at hhd
              · rw [hgi] at hhd
                have hi : i = w := by simpa using hhd
                unfold rin at hr1
                rw [hgi] at hr1
                simp only [List.map_cons, List.cons.injEq] at hr1
                rw [hi, r0 w hw] at hr1
                have hww : w = w1 := Sum.inr.inj hr1.1
                rw [hg', hww]
                simp

theorem norm' (n m : ℕ) (A : Fin n → Fin m → Bool) (gs : List Gate) (o : ℕ) (hF : FanInTwo ⟨gs, o⟩)
    (hrep : Represents A ⟨gs, o⟩) (hnc : ∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2) :
    ∃ o' : ℕ, (runR (n + m) gs).2.getD o (Sum.inl false) = Sum.inr o' ∧
      PL (n + m) (runR (n + m) gs).1 ∧ Represents A ⟨(runR (n + m) gs).1, o'⟩ ∧
      (runR (n + m) gs).1.length ≤ gs.length ∧ o' < n + m + (runR (n + m) gs).1.length ∧
      (∀ w < n + m, (Lst (runR (n + m) gs).1 w ∨ o' = w) → (RR gs w ∨ o = w)) ∧
      ((runR (n + m) gs).1.length = gs.length → ∀ w < n + m, (RR gs w ∨ o = w) →
        (Lst (runR (n + m) gs).1 w ∨ o' = w)) := by
  have hF' : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hF g hg
    simpa [Set.mem_insert_iff] using this
  obtain ⟨i1, i2, i3, i4, i5⟩ := inv_run (n + m) gs hF'
  obtain ⟨r0, r2, r1, r3⟩ := rinv_run (n + m) gs hF'
  have hx : ∀ (u : Fin n) (v : Fin m), (oneEach u v).length = n + m := by
    intro u v
    simp [oneEach]
  have hev : ∀ (u : Fin n) (v : Fin m), (gs.foldl stp (oneEach u v)).getD o false = A u v :=
    fun u v => hrep u v
  cases ha : (runR (n + m) gs).2.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨u, u2, v, v2, hne⟩ := hnc
    have h1 : A u v = c := by
      have := i5 (oneEach u v) (hx u v) o
      rw [ha, hev u v] at this
      exact this
    have h2 : A u2 v2 = c := by
      have := i5 (oneEach u2 v2) (hx u2 v2) o
      rw [ha, hev u2 v2] at this
      exact this
    exact hne (h1.trans h2.symm)
  | inr w =>
    refine ⟨w, rfl, i4, fun u v => ?_, i2, i3 o w ha, ?_, ?_⟩
    · have := i5 (oneEach u v) (hx u v) o
      rw [ha, hev u v] at this
      exact this.symm
    · intro w' hw' h
      rcases h with h | h
      · exact Or.inl (r1 w' hw' h)
      · rw [← h] at hw' ⊢
        rcases r2 o w ha hw' with e | h
        · exact Or.inr e
        · exact Or.inl h
    · intro hl w' hw' h
      rcases h with h | h
      · exact Or.inl (r3 hl w' hw' h)
      · right
        rw [← h] at hw' ⊢
        have := r0 o hw'
        rw [ha] at this
        exact Sum.inr.inj this

def phi (N j s w : ℕ) : ℕ := if w < N + j then w else if w = N + j then N + s else w - 1

def mg (N j s : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi N j s)⟩

def hs (N j : ℕ) (gs : List Gate) : List Gate := (gs.eraseIdx j).map (mg N j gs.length)

theorem phi_lt (N j s w : ℕ) (h : w < N + j) : phi N j s w = w := by
  unfold phi; rw [ifp h]

theorem phi_gt (N j s w : ℕ) (h : N + j < w) : phi N j s w = w - 1 := by
  unfold phi; rw [ifn (by omega), ifn (by omega)]

theorem hs_len (N j : ℕ) (gs : List Gate) (hj : j < gs.length) : (hs N j gs).length + 1 = gs.length := by
  unfold hs
  rw [List.length_map, List.length_eraseIdx, ifp hj]
  omega

theorem hs_lt (N j : ℕ) (gs : List Gate) (i : ℕ) (hi : i < j) (hj : j < gs.length) :
    (hs N j gs).getD i dg = mg N j gs.length (gs.getD i dg) := by
  unfold hs
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eraseIdx, ifp hi, List.getElem?_eq_getElem (by omega)]
  rfl

theorem hs_ge (N j : ℕ) (gs : List Gate) (i : ℕ) (hi : j ≤ i) (hj : i + 1 < gs.length) :
    (hs N j gs).getD i dg = mg N j gs.length (gs.getD (i + 1) dg) := by
  unfold hs
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eraseIdx, ifn (by omega), List.getElem?_eq_getElem hj]
  rfl

theorem sim2 (N j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (hun : ∀ i < gs.length, N + j ∉ (gs.getD i dg).inputs) (x : List Bool) (hx : x.length = N) :
    ∀ w, w ≠ N + j → ((hs N j gs).foldl stp x).getD (phi N j gs.length w) false =
      (gs.foldl stp x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwj
    have hl1 := hs_len N j gs hj
    by_cases h1 : w < N
    · rw [phi_lt _ _ _ _ (by omega), inp _ _ _ (by omega), inp _ _ _ (by omega)]
    · by_cases h2 : N + gs.length ≤ w
      · rw [phi_gt _ _ _ _ (by omega), beyond _ _ _ (by omega), beyond _ _ _ (by omega)]
      · obtain ⟨i, rfl⟩ : ∃ i, w = N + i := ⟨w - N, by omega⟩
        by_cases h4 : i < j
        · rw [phi_lt _ _ _ _ (by omega)]
          have e1 := wire_at (hs N j gs) x i (by omega)
          have e2 := wire_at gs x i (by omega)
          rw [hx] at e1 e2
          rw [e1, e2, hs_lt N j gs i h4 hj]
          show (gs.getD i dg).op.eval (List.map _ ((gs.getD i dg).inputs.map (phi N j gs.length))) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro w' _
          show (if phi N j gs.length w' < N + i then
            ((hs N j gs).foldl stp x).getD (phi N j gs.length w') false else false) = _
          by_cases hc : w' < N + i
          · rw [ifp hc, ← ih w' (by omega) (by omega), phi_lt _ _ _ _ (by omega), ifp hc]
          · rw [ifn hc]
            by_cases hc1 : w' < N + j
            · rw [phi_lt _ _ _ _ hc1, ifn hc]
            · unfold phi
              rw [ifn hc1]
              split_ifs <;> first | rfl | omega
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
          rw [phi_gt _ _ _ _ (by omega)]
          have ek : N + (k + 1) - 1 = N + k := by omega
          rw [ek]
          have e1 := wire_at (hs N j gs) x k (by omega)
          have e2 := wire_at gs x (k + 1) (by omega)
          rw [hx] at e1 e2
          rw [e1, e2, hs_ge N j gs k (by omega) (by omega)]
          show (gs.getD (k + 1) dg).op.eval
            (List.map _ ((gs.getD (k + 1) dg).inputs.map (phi N j gs.length))) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro w' hw'
          show (if phi N j gs.length w' < N + k then
            ((hs N j gs).foldl stp x).getD (phi N j gs.length w') false else false) = _
          have hne : w' ≠ N + j := fun e => hun (k + 1) (by omega) (e ▸ hw')
          by_cases hc : w' < N + (k + 1)
          · rw [ifp hc, ← ih w' (by omega) hne]
            by_cases hc1 : w' < N + j
            · rw [phi_lt _ _ _ _ hc1, ifp (by omega)]
            · rw [phi_gt _ _ _ _ (by omega), ifp (by omega)]
          · rw [ifn hc, phi_gt _ _ _ _ (by omega), ifn (by omega)]

theorem hs_PL (N j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (hun : ∀ i < gs.length, N + j ∉ (gs.getD i dg).inputs) (hP : PL N gs) : PL N (hs N j gs) := by
  have hl1 := hs_len N j gs hj
  constructor
  · intro g hg
    unfold hs at hg
    rw [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hP.1 g0 (List.mem_of_mem_eraseIdx hg0)
    unfold Ar at this ⊢
    unfold mg
    simp only [List.length_map]
    exact this
  · intro i hi c hc
    by_cases h : i < j
    · rw [hs_lt N j gs i h hj] at hc
      unfold mg at hc
      simp only [List.mem_map] at hc
      obtain ⟨w', hw', rfl⟩ := hc
      have := hP.2 i (by omega) w' hw'
      rw [phi_lt _ _ _ _ (by omega)]
      exact this
    · rw [hs_ge N j gs i (by omega) (by omega)] at hc
      unfold mg at hc
      simp only [List.mem_map] at hc
      obtain ⟨w', hw', rfl⟩ := hc
      have := hP.2 (i + 1) (by omega) w' hw'
      have hne : w' ≠ N + j := fun e => hun (i + 1) (by omega) (e ▸ hw')
      by_cases hc1 : w' < N + j
      · rw [phi_lt _ _ _ _ hc1]; omega
      · rw [phi_gt _ _ _ _ (by omega)]; omega

theorem exmin (P : ℕ → Prop) : ∀ k, P k → ∃ m, P m ∧ ∀ k', P k' → m ≤ k' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h : ∀ k', P k' → k ≤ k'
    · exact ⟨k, hk, h⟩
    · obtain ⟨k', hk'⟩ := not_forall.1 h
      obtain ⟨hk1, hk2⟩ := Classical.not_imp.1 hk'
      exact ih k' (by omega) hk1

theorem lst_hs (N j : ℕ) (gs : List Gate) (w : ℕ) (hw : w < N) (h : Lst (hs N j gs) w) : Lst gs w := by
  obtain ⟨q, hq, hwq⟩ := h
  unfold hs at hq
  rw [List.mem_map] at hq
  obtain ⟨q0, hq0, rfl⟩ := hq
  refine ⟨q0, List.mem_of_mem_eraseIdx hq0, ?_⟩
  change w ∈ q0.inputs.map (phi N j gs.length) at hwq
  rw [List.mem_map] at hwq
  obtain ⟨x, hx, hxe⟩ := hwq
  have hxw : x = w := by
    unfold phi at hxe
    split_ifs at hxe <;> omega
  rw [← hxw]
  exact hx

theorem reduced_props (N : ℕ) (gs : List Gate) (o : ℕ) (hPL : PL N gs) (hpos : 0 < gs.length)
    (c3 : o + 1 = N + gs.length)
    (c4 : ∀ j, j + 1 < gs.length → ∃ i, i < gs.length ∧ N + j ∈ (gs.getD i dg).inputs) :
    FanInTwo ⟨gs, o⟩ ∧
    (∀ g ∈ (Circuit.mk gs o).gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, o⟩ ∧ 0 < (Circuit.mk gs o).size ∧
    (Circuit.mk gs o).output + 1 = N + (Circuit.mk gs o).size ∧
    (∀ j < (Circuit.mk gs o).size,
      (PEqualNP.MetaComplexity.NestedCover.readsIn ⟨gs, o⟩ (Finset.range (Circuit.mk gs o).size) (N + j) = 0 ↔
        j + 1 = (Circuit.mk gs o).size)) := by
  refine ⟨?_, fun g hg => hPL.1 g hg, hPL.2, hpos, c3, ?_⟩
  · intro g hg
    rcases hPL.1 g hg with ⟨h | h, hl⟩ | ⟨h, hl⟩
    · exact ⟨by rw [h]; simp, by omega⟩
    · exact ⟨by rw [h]; simp, by omega⟩
    · exact ⟨by rw [h]; simp, by omega⟩
  · intro j hj
    have hj' : j < gs.length := hj
    show (∑ i ∈ Finset.range gs.length, (gs.getD i dg).inputs.count (N + j)) = 0 ↔
      j + 1 = gs.length
    constructor
    · intro h0
      by_contra hne
      obtain ⟨i, hi, hm⟩ := c4 j (by omega)
      have hle := Finset.single_le_sum (f := fun i => ((gs.getD i dg).inputs.count (N + j)))
        (fun i _ => Nat.zero_le _) (Finset.mem_range.2 hi)
      have p1 : 0 < (gs.getD i dg).inputs.count (N + j) := List.count_pos_iff.2 hm
      omega
    · intro hlast
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      apply List.count_eq_zero.2
      intro hm
      have := hPL.2 i hi _ hm
      omega

theorem norm_main (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (hF : FanInTwo C)
    (hrep : Represents A C)
    (hnc : ∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2) :
    ∃ D : Circuit, FanInTwo D ∧ Represents A D ∧ D.size ≤ C.size ∧
      (((∀ g ∈ D.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
        (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) D ∧ 0 < D.size ∧
      D.output + 1 = (n + m) + D.size ∧
      (∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) ((n + m) + j) = 0 ↔
        j + 1 = D.size))) ∨ (D.size = 0 ∧ D.output < (n + m))) ∧
      (∀ w < (n + m), (Lst D.gates w ∨ D.output = w) → (RR C.gates w ∨ C.output = w)) ∧
      (D.size + 1 ≤ C.size ∨ ∀ w < (n + m), (RR C.gates w ∨ C.output = w) →
        (Lst D.gates w ∨ D.output = w)) := by
  obtain ⟨gsC, oc⟩ := C
  obtain ⟨o', ha, hPL0, hrep0, hle0, hlt0, rd10, rd20⟩ := norm' n m A gsC oc hF hrep hnc
  obtain ⟨m0, ⟨D, hPL, hrepD, hsz, hk, rd1, rd2⟩, hmin⟩ := exmin (fun k => ∃ D : Circuit,
      PL (n + m) D.gates ∧ Represents A D ∧ D.gates.length = k ∧ k ≤ gsC.length ∧
      (∀ w < (n + m), (Lst D.gates w ∨ D.output = w) → (RR gsC w ∨ oc = w)) ∧
      (k = gsC.length → ∀ w < (n + m), (RR gsC w ∨ oc = w) → (Lst D.gates w ∨ D.output = w)))
    (runR (n + m) gsC).1.length ⟨⟨(runR (n + m) gsC).1, o'⟩, hPL0, hrep0, rfl, hle0, rd10, rd20⟩
  obtain ⟨gs, o⟩ := D
  have hsz' : gs.length = m0 := hsz
  have hmin' : ∀ D' : Circuit, PL (n + m) D'.gates → Represents A D' →
      D'.gates.length < gs.length →
      (∀ w < (n + m), (Lst D'.gates w ∨ D'.output = w) → (RR gsC w ∨ oc = w)) → False := by
    intro D' q1 q2 q3 q4
    have := hmin D'.gates.length ⟨D', q1, q2, rfl, by omega, q4, fun hh => by omega⟩
    omega
  have hx : ∀ (u : Fin n) (v : Fin m), (oneEach u v).length = n + m := by
    intro u v
    simp [oneEach]
  have hev : ∀ (u : Fin n) (v : Fin m), (gs.foldl stp (oneEach u v)).getD o false = A u v :=
    fun u v => hrepD u v
  have c2 : o < n + m + gs.length := by
    by_contra h
    obtain ⟨u, u2, v, v2, hne⟩ := hnc
    have e1 := hev u v
    have e2 := hev u2 v2
    rw [beyond gs _ o (by rw [hx]; omega)] at e1 e2
    exact hne (e1.symm.trans e2)
  have last : (Circuit.mk gs o).size + 1 ≤ (Circuit.mk gsC oc).size ∨ ∀ w < (n + m),
      (RR gsC w ∨ oc = w) → (Lst gs w ∨ o = w) := by
    by_cases heq : gs.length = gsC.length
    · exact Or.inr (rd2 (by omega))
    · left
      show gs.length + 1 ≤ gsC.length
      omega
  have hle : (Circuit.mk gs o).size ≤ (Circuit.mk gsC oc).size := by
    show gs.length ≤ gsC.length
    omega
  by_cases hgs : gs.length = 0
  · have hgs' : gs = [] := List.eq_nil_of_length_eq_zero hgs
    have ho : o < n + m := by
      rw [hgs] at c2
      exact c2
    refine ⟨⟨gs, o⟩, ?_, hrepD, hle, Or.inr ⟨hgs, ho⟩, rd1, last⟩
    intro g hg
    rw [hgs'] at hg
    simp at hg
  · have c3 : o + 1 = n + m + gs.length := by
      by_contra h
      have hne : gs ≠ [] := by
        intro e
        rw [e] at hgs
        exact hgs rfl
      obtain ⟨gs', g, rfl⟩ : ∃ gs' g, gs = gs' ++ [g] :=
        ⟨gs.dropLast, gs.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      rw [List.length_append, List.length_singleton] at c2 h
      refine hmin' ⟨gs', o⟩
        ⟨fun q hq => hPL.1 q (List.mem_append_left _ hq), fun j hj i hi => by
          have hj' : j < gs'.length := hj
          have := hPL.2 j (by show j < (gs' ++ [g]).length; rw [List.length_append, List.length_singleton]; omega) i
            (by
              show i ∈ ((gs' ++ [g]).getD j dg).inputs
              rw [getD_left gs' g dg j hj']
              exact hi)
          exact this⟩
        (fun u v => by
          show (gs'.foldl stp (oneEach u v)).getD o false = A u v
          rw [← hev u v]
          exact (pre gs' [g] (oneEach u v) o (by rw [hx]; omega)).symm)
        (by
          show gs'.length < (gs' ++ [g]).length
          rw [List.length_append, List.length_singleton]
          omega)
        ?_
      intro w hw' hh
      rcases hh with hh | hh
      · exact rd1 w hw' (Or.inl (lst_mono g hh))
      · exact rd1 w hw' (Or.inr hh)
    have c4 : ∀ j, j + 1 < gs.length → ∃ i, i < gs.length ∧ n + m + j ∈ (gs.getD i dg).inputs := by
      intro j hj
      by_contra hno
      have hun : ∀ i < gs.length, n + m + j ∉ (gs.getD i dg).inputs :=
        fun i hi hm => hno ⟨i, hi, hm⟩
      have hl := hs_len (n + m) j gs (by omega)
      refine hmin' ⟨hs (n + m) j gs, phi (n + m) j gs.length o⟩
        (hs_PL (n + m) j gs (by omega) hun hPL)
        (fun u v => by
          show ((hs (n + m) j gs).foldl stp (oneEach u v)).getD (phi (n + m) j gs.length o) false = A u v
          rw [← hev u v]
          exact sim2 (n + m) j gs (by omega) hun (oneEach u v) (hx u v) o (by omega))
        (by
          show (hs (n + m) j gs).length < gs.length
          omega)
        ?_
      intro w hw' hh
      rcases hh with hh | hh
      · exact rd1 w hw' (Or.inl (lst_hs (n + m) j gs w hw' hh))
      · exfalso
        change phi (n + m) j gs.length o = w at hh
        rw [phi_gt (n + m) j gs.length o (by omega)] at hh
        omega
    obtain ⟨a, b, c, d, e, f⟩ := reduced_props (n + m) gs o hPL (by omega) c3 c4
    exact ⟨⟨gs, o⟩, a, hrepD, hle, Or.inl ⟨b, c, d, e, f⟩, rd1, last⟩


theorem rr_lst {gs : List Gate} {w : ℕ} (h : RR gs w) : ∃ g ∈ gs, w ∈ g.inputs := by
  obtain ⟨g, hg, hr⟩ := h
  refine ⟨g, hg, ?_⟩
  rcases hr with ⟨_, hin⟩ | ⟨_, hhd⟩
  · exact hin
  · rcases hgi : g.inputs with _ | ⟨i, rest⟩
    · rw [hgi] at hhd
      simp at hhd
    · rw [hgi] at hhd
      have hi : i = w := by simpa using hhd
      rw [hi]
      simp

theorem main : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + (m + 1)))) → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C hF hrep hred hlist hnc
  have hAr : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1) := by
    rcases hred with ⟨h, _⟩ | ⟨h0, _⟩
    · exact h
    · exfalso
      obtain ⟨g, hg, _⟩ := hlist
      have h0' : C.gates.length = 0 := h0
      have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero h0'
      rw [hnil] at hg
      simp at hg
  obtain ⟨C2, hF2, hrep2, hsz2, hrow, hcol⟩ := E_main n m A k C hF hAr hrep hlist hnc
  obtain ⟨D, hFD, hrepD, hszD, hredD, rd1, _⟩ :=
    norm_main n m (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 hF2 hrep2 hnc
  refine ⟨D, hFD, hrepD, hredD, by omega, ?_, ?_⟩
  · intro u h
    have hu := u.isLt
    rcases rd1 u.val (by omega) h with h2 | h2
    · exact hrow u (Or.inl (rr_lst h2))
    · exact hrow u (Or.inr h2)
  · intro v h
    have hv := v.isLt
    rcases rd1 (n + v.val) (by omega) h with h2 | h2
    · exact hcol v (Or.inl (rr_lst h2))
    · exact hcol v (Or.inr h2)

end PEqualNP.Outside.L_meta_24695

theorem PEqualNP.Outside.L_meta_24695 : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + (m + 1)))) → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) :=
  PEqualNP.Outside.L_meta_24695.main

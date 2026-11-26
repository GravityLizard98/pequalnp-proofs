import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25000

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

theorem gdel (N : ℕ) (I : List Bool → Prop) (hI : ∀ X, I X → X.length = N) (C : Circuit)
    (G1 G2 : List Gate) (h : Gate) (r : ℕ) (Q : Prop)
    (hC : C.gates = G1 ++ h :: G2) (hF : FanInTwo C)
    (hr : r < N + G1.length ∨ N + C.gates.length ≤ r)
    (hQ2 : ∀ g ∈ G2, ∀ i ∈ g.inputs, i = N + G1.length → Q)
    (hQo : C.output = N + G1.length → Q)
    (hv : Q → ∀ X, I X →
      h.op.eval (h.inputs.map fun i => (G1.foldl stp X).getD i false) =
        (G1.foldl stp X).getD r false) :
    ∃ C1 : Circuit, C1.size + 1 = C.size ∧ FanInTwo C1 ∧ (∀ X, I X → C1.eval X = C.eval X) := by
  have hlen : C.gates.length = G1.length + G2.length + 1 := by rw [hC]; simp; omega
  refine ⟨⟨G1 ++ G2.map (rg (N + G1.length) r), rho (N + G1.length) r C.output⟩, ?_, ?_, ?_⟩
  · show (G1 ++ G2.map _).length + 1 = C.gates.length
    rw [hlen]
    simp
  · intro g hg
    have hg' : g ∈ G1 ++ G2.map (rg (N + G1.length) r) := hg
    rw [List.mem_append, List.mem_map] at hg'
    rcases hg' with h1 | ⟨g0, hg0, rfl⟩
    · exact hF g (by rw [hC]; simp [h1])
    · have hf := hF g0 (by rw [hC]; simp [hg0])
      refine ⟨hf.1, ?_⟩
      show (g0.inputs.map _).length ≤ 2
      rw [List.length_map]
      exact hf.2
  · intro X hX
    have hx : X.length = N := hI X hX
    show ((G1 ++ G2.map (rg (N + G1.length) r)).foldl stp X).getD
      (rho (N + G1.length) r C.output) false = (C.gates.foldl stp X).getD C.output false
    rw [hC, List.foldl_append, List.foldl_append, List.foldl_cons]
    have hl1 : (G1.foldl stp X).length = N + G1.length := by
      rw [len, hx]
    refine sim Q (N + G1.length) r (N + C.gates.length)
      (stp (G1.foldl stp X) h) (G1.foldl stp X)
      ?_ ?_ ?_ ?_ G2 ?_ hQ2 C.output hQo
    · simp [stp]
    · rw [hl1]
    · rw [hl1]
      exact hr
    · intro i hi
      show (G1.foldl stp X).getD (rho (N + G1.length) r i) false =
        (G1.foldl stp X ++ [_]).getD i false
      rw [getD_snoc, hl1]
      unfold rho
      by_cases h1 : i < N + G1.length
      · rw [ifp h1, ifp h1]
      · by_cases h2 : i = N + G1.length
        · rw [ifn h1, ifp h2, ifn h1, ifp h2]
          exact (hv (hi h2) X hX).symm
        · rw [ifn h1, ifn h2, ifn h1, ifn h2]
          exact List.getD_eq_default _ _ (by rw [hl1]; omega)
    · rw [hl1, hlen]
      omega

def tau (a B i : ℕ) : ℕ := if i = a then B else i

def tg (a B : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (tau a B)⟩

theorem simt (a B c : ℕ) (X X' : List Bool) (hl : X.length = X'.length) (ha : a < X'.length)
    (hbase : ∀ i, i ≠ c → X'.getD (tau a B i) false = X.getD i false) :
    ∀ Bs : List Gate, X'.length + Bs.length ≤ B → (∀ g ∈ Bs, ∀ j ∈ g.inputs, j ≠ c) →
      ∀ i, i ≠ c →
      ((Bs.map (tg a B)).foldl stp X').getD (tau a B i) false =
        (Bs.foldl stp X).getD i false := by
  intro Bs
  induction Bs using List.reverseRecOn with
  | nil =>
    intro _ _ i hi
    exact hbase i hi
  | append_singleton Bs g ih =>
    intro hB hQ i hi
    rw [List.length_append, List.length_singleton] at hB
    have ih' := ih (by omega) (fun g' hg' => hQ g' (List.mem_append_left _ hg'))
    have hv : (tg a B g).op.eval ((tg a B g).inputs.map fun i =>
        ((Bs.map (tg a B)).foldl stp X').getD i false) =
        g.op.eval (g.inputs.map fun i => (Bs.foldl stp X).getD i false) := by
      show g.op.eval ((g.inputs.map (tau a B)).map fun i =>
        ((Bs.map (tg a B)).foldl stp X').getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact ih' j (hQ g (by simp) j hj)
    rw [List.map_append, List.map_singleton, snoc_fold, snoc_fold, hv, getD_snoc, getD_snoc,
      len, len, List.length_map]
    simp only [hl]
    have hi' := ih' i hi
    by_cases h1 : i = a
    · have ht : tau a B i = B := by unfold tau; rw [ifp h1]
      rw [ht] at hi' ⊢
      rw [ifn (by omega), ifn (by omega), ifp (by omega), ← hi']
      symm
      exact List.getD_eq_default _ _ (by rw [len, List.length_map]; omega)
    · have ht : tau a B i = i := by unfold tau; rw [ifn h1]
      rw [ht] at hi' ⊢
      by_cases h2 : i < X'.length + Bs.length
      · rw [ifp h2, ifp h2]
        exact hi'
      · rw [ifn h2, ifn h2]

def nz (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem nz_eval (f : ℕ → Bool) (g : Gate) :
    (nz g).op.eval ((nz g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> try rfl
  show GateOp.not.eval ((ins.take 1).map f) = GateOp.not.eval (ins.map f)
  cases ins <;> simp [GateOp.eval]

theorem nz_fold (gs : List Gate) : ∀ X : List Bool, (gs.map nz).foldl stp X = gs.foldl stp X := by
  induction gs with
  | nil => intro X; rfl
  | cons g gs ih =>
    intro X
    have e : stp X (nz g) = stp X g := by
      show X ++ [(nz g).op.eval ((nz g).inputs.map fun i => X.getD i false)] =
        X ++ [g.op.eval (g.inputs.map fun i => X.getD i false)]
      rw [nz_eval]
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e]
    exact ih _

theorem nz_ok (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ((nz g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (nz g).inputs.length ≤ 2) ∧
      ((nz g).op = GateOp.not → (nz g).inputs.length ≤ 1) := by
  obtain ⟨op, ins⟩ := g
  cases op
  · exact ⟨h, fun h' => by simp [nz] at h'⟩
  · exact ⟨h, fun h' => by simp [nz] at h'⟩
  · refine ⟨⟨by simp [nz], ?_⟩, fun _ => ?_⟩
    · show (ins.take 1).length ≤ 2
      rw [List.length_take]
      omega
    · show (ins.take 1).length ≤ 1
      rw [List.length_take]
      omega
  · simp at h
  · simp at h

theorem and_f (W : List Bool) (l : List ℕ) (c : ℕ) (hc : c ∈ l) (h : W.getD c false = false) :
    GateOp.and.eval (l.map fun i => W.getD i false) = false := by
  simp only [GateOp.eval, List.all_map, List.all_eq_false]
  exact ⟨c, hc, by simpa using h⟩

theorem or_t (W : List Bool) (l : List ℕ) (c : ℕ) (hc : c ∈ l) (h : W.getD c false = true) :
    GateOp.or.eval (l.map fun i => W.getD i false) = true := by
  simp only [GateOp.eval, List.any_map, List.any_eq_true]
  exact ⟨c, hc, by simpa using h⟩

theorem or1 (W : List Bool) (a : ℕ) :
    GateOp.or.eval ([a].map fun i => W.getD i false) = W.getD a false := by
  simp [GateOp.eval]

theorem or2 (W : List Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map fun i => W.getD i false) =
      (W.getD a false || W.getD b false) := by
  simp [GateOp.eval]

theorem and1 (W : List Bool) (a : ℕ) :
    GateOp.and.eval ([a].map fun i => W.getD i false) = W.getD a false := by
  simp [GateOp.eval]

theorem and2 (W : List Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map fun i => W.getD i false) =
      (W.getD a false && W.getD b false) := by
  simp [GateOp.eval]

theorem not1 (W : List Bool) (a : ℕ) :
    GateOp.not.eval ([a].map fun i => W.getD i false) = (!W.getD a false) := by
  simp [GateOp.eval]

theorem sh2 (l : List ℕ) (c : ℕ) (hl : l.length ≤ 2) (hc : c ∈ l) :
    l = [c] ∨ ∃ x, (l = [c, x] ∨ l = [x, c]) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
  · simp at hc
  · simp at hc
    left
    rw [hc]
  · simp at hc
    right
    rcases hc with h | h
    · exact ⟨b, Or.inl (by rw [h])⟩
    · exact ⟨a, Or.inr (by rw [h])⟩
  · have : (a :: b :: d :: t).length = t.length + 3 := rfl
    omega

theorem sh1 (l : List ℕ) (c : ℕ) (hl : l.length ≤ 1) (hc : c ∈ l) : l = [c] := by
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at hc
  · simp at hc
    rw [hc]
  · have : (a :: b :: t).length = t.length + 2 := rfl
    omega

def Inp (n m : ℕ) (u2 : Fin n) (X : List Bool) : Prop :=
  ∃ (w : Fin n) (v : Fin m), w ≠ u2 ∧ X = oneEach w v

theorem caseA (n m : ℕ) (A : Fin n → Fin m → Bool) (u u2 : Fin n) (C : Circuit)
    (hF : FanInTwo C) (hN : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (hrep : ∀ (w : Fin n) (v : Fin m), w ≠ u2 → C.eval (oneEach w v) = A w v)
    (hlist : ∃ g ∈ C.gates, u2.val ∈ g.inputs) :
    ∃ C2 : Circuit, FanInTwo C2 ∧
      (∀ (w : Fin n) (v : Fin m), w ≠ u2 → C2.eval (oneEach w v) = A w v) ∧
      (C2.size + 1 ≤ C.size ∨ (C2.size ≤ C.size ∧ C2.output ≠ u.val ∧
        ∀ g ∈ C2.gates, u.val ∉ g.inputs)) := by
  obtain ⟨g, hg, hc⟩ := hlist
  obtain ⟨G1, G2, hC⟩ := List.append_of_mem hg
  have hlen : C.gates.length = G1.length + G2.length + 1 := by rw [hC]; simp; omega
  have hI : ∀ X, Inp n m u2 X → X.length = n + m := by
    rintro X ⟨w, v, _, rfl⟩
    simp [oneEach]
  have hc0 : ∀ X, Inp n m u2 X → ∀ gs : List Gate,
      (gs.foldl stp X).getD u2.val false = false := by
    rintro X ⟨w, v, hw, rfl⟩ gs
    have hl : (oneEach w v).length = n + m := by simp [oneEach]
    rw [pre _ _ _ (by rw [hl]; have := u2.isLt; omega)]
    cases hb : (oneEach w v).getD u2.val false with
    | false => rfl
    | true =>
      rw [oe] at hb
      rcases hb with hb | hb
      · exact absurd (Fin.ext hb).symm hw
      · have := u2.isLt
        omega
  have hWl : ∀ X, Inp n m u2 X → ∀ L : List Gate,
      (L.foldl stp X).length = n + m + L.length := by
    intro X hX L
    rw [len, hI X hX]
  have fin1 : ∀ (L1 L2 : List Gate) (h : Gate) (r : ℕ) (Q : Prop), C.gates = L1 ++ h :: L2 →
      (r < n + m + L1.length ∨ n + m + C.gates.length ≤ r) →
      (∀ g ∈ L2, ∀ i ∈ g.inputs, i = n + m + L1.length → Q) →
      (C.output = n + m + L1.length → Q) →
      (Q → ∀ X, Inp n m u2 X →
        h.op.eval (h.inputs.map fun i => (L1.foldl stp X).getD i false) =
          (L1.foldl stp X).getD r false) →
      ∃ C2 : Circuit, FanInTwo C2 ∧
        (∀ (w : Fin n) (v : Fin m), w ≠ u2 → C2.eval (oneEach w v) = A w v) ∧
        (C2.size + 1 ≤ C.size ∨ (C2.size ≤ C.size ∧ C2.output ≠ u.val ∧
          ∀ g ∈ C2.gates, u.val ∉ g.inputs)) := by
    intro L1 L2 h r Q hC' hr hQ2 hQo hv
    obtain ⟨C1, hs1, hF1, hev⟩ := gdel (n + m) (Inp n m u2) hI C L1 L2 h r Q hC' hF hr hQ2 hQo hv
    exact ⟨C1, hF1, fun w v hw => (hev _ ⟨w, v, hw, rfl⟩).trans (hrep w v hw), Or.inl (by omega)⟩
  obtain ⟨hop, hl2⟩ := hF g hg
  have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hop
  rcases hop' with ha | ho | hn
  · refine fin1 G1 G2 g (n + m + C.gates.length) True hC (Or.inr le_rfl)
      (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
    intro _ X hX
    rw [List.getD_eq_default _ _ (by rw [hWl X hX]; omega), ha]
    exact and_f _ _ _ hc (hc0 X hX G1)
  · rcases sh2 g.inputs u2.val hl2 hc with h1 | ⟨x, h1 | h1⟩
    · refine fin1 G1 G2 g (n + m + C.gates.length) True hC (Or.inr le_rfl)
        (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
      intro _ X hX
      rw [List.getD_eq_default _ _ (by rw [hWl X hX]; omega), ho, h1, or1, hc0 X hX G1]
    · refine fin1 G1 G2 g (rr (n + m + G1.length) (n + m + C.gates.length) x) True hC
        (rr_hr _ _ _) (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
      intro _ X hX
      rw [rr_val _ _ _ _ (hWl X hX G1) (by omega), ho, h1, or2, hc0 X hX G1]
      rfl
    · refine fin1 G1 G2 g (rr (n + m + G1.length) (n + m + C.gates.length) x) True hC
        (rr_hr _ _ _) (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
      intro _ X hX
      rw [rr_val _ _ _ _ (hWl X hX G1) (by omega), ho, h1, or2, hc0 X hX G1]
      simp
  · have hin : g.inputs = [u2.val] := sh1 _ _ (hN g hg hn) hc
    have hval : ∀ X, Inp n m u2 X →
        g.op.eval (g.inputs.map fun i => (G1.foldl stp X).getD i false) = true := by
      intro X hX
      rw [hn, hin, not1, hc0 X hX G1]
      rfl
    by_cases hread : ∃ g' ∈ G2, (n + m + G1.length) ∈ g'.inputs
    · obtain ⟨g', hg', hp'⟩ := hread
      obtain ⟨G2a, G2b, hG2⟩ := List.append_of_mem hg'
      have hC2 : C.gates = (G1 ++ g :: G2a) ++ g' :: G2b := by
        rw [hC, hG2]
        simp
      have hl' : (G1 ++ g :: G2a).length = G1.length + G2a.length + 1 := by
        simp
        omega
      have hlen2 : G2.length = G2a.length + G2b.length + 1 := by rw [hG2]; simp; omega
      have hT : ∀ X, Inp n m u2 X →
          ((G1 ++ g :: G2a).foldl stp X).getD (n + m + G1.length) false = true := by
        intro X hX
        rw [stable G1 G2a _ _ _ (by rw [hI X hX]), hval X hX]
      have hg'C : g' ∈ C.gates := by rw [hC2]; simp
      obtain ⟨hop2, hl22⟩ := hF g' hg'C
      have hop2' : g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not := by
        simpa using hop2
      rcases hop2' with ha | ho | hn2
      · rcases sh2 g'.inputs _ hl22 hp' with h1 | ⟨y, h1 | h1⟩
        · refine fin1 _ G2b g' (n + m + G1.length) True hC2 (Or.inl (by rw [hl']; omega))
            (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
          intro _ X hX
          rw [ha, h1, and1]
        · refine fin1 _ G2b g'
            (rr (n + m + (G1 ++ g :: G2a).length) (n + m + C.gates.length) y) True hC2
            (rr_hr _ _ _) (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
          intro _ X hX
          rw [rr_val _ _ _ _ (hWl X hX _) (by rw [hl']; omega), ha, h1, and2, hT X hX]
          rfl
        · refine fin1 _ G2b g'
            (rr (n + m + (G1 ++ g :: G2a).length) (n + m + C.gates.length) y) True hC2
            (rr_hr _ _ _) (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
          intro _ X hX
          rw [rr_val _ _ _ _ (hWl X hX _) (by rw [hl']; omega), ha, h1, and2, hT X hX]
          simp
      · refine fin1 _ G2b g' (n + m + G1.length) True hC2 (Or.inl (by rw [hl']; omega))
          (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
        intro _ X hX
        rw [ho, hT X hX]
        exact or_t _ _ _ hp' (hT X hX)
      · have hin' : g'.inputs = [n + m + G1.length] := sh1 _ _ (hN g' hg'C hn2) hp'
        refine fin1 _ G2b g' (n + m + C.gates.length) True hC2 (Or.inr le_rfl)
          (fun _ _ _ _ _ => trivial) (fun _ => trivial) ?_
        intro _ X hX
        rw [List.getD_eq_default _ _ (by rw [hWl X hX, hl']; omega), hn2, hin', not1, hT X hX]
        rfl
    · by_cases ho : C.output = n + m + G1.length
      · refine ⟨⟨[⟨GateOp.not, []⟩], n + m⟩, ?_, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
        · intro g0 hg0
          have hg0' : g0 ∈ [(⟨GateOp.not, []⟩ : Gate)] := hg0
          rw [List.mem_singleton] at hg0'
          rw [hg0']
          exact ⟨by simp, by simp⟩
        · intro w v hw
          have h0 : (C.gates.foldl stp (oneEach w v)).getD C.output false = A w v := hrep w v hw
          have hX : Inp n m u2 (oneEach w v) := ⟨w, v, hw, rfl⟩
          rw [← h0, ho, hC, stable G1 G2 _ _ _ (by rw [hI _ hX]), hval _ hX]
          show (oneEach w v ++ [true]).getD (n + m) false = true
          exact getD_last _ _ _ _ (hI _ hX).symm
        · show 1 ≤ C.gates.length
          omega
        · show n + m ≠ u.val
          have := u.isLt
          omega
        · intro g0 hg0
          have hg0' : g0 ∈ [(⟨GateOp.not, []⟩ : Gate)] := hg0
          rw [List.mem_singleton] at hg0'
          rw [hg0']
          simp
      · exact fin1 G1 G2 g (n + m + C.gates.length) False hC (Or.inr le_rfl)
          (fun g' hg' i hi hip => hread ⟨g', hg', hip ▸ hi⟩) ho (fun hf => hf.elim)

theorem caseB (n m : ℕ) (A : Fin n → Fin m → Bool) (u u2 : Fin n)
    (heq : ∀ v : Fin m, A u v = A u2 v) (C : Circuit) (hF : FanInTwo C)
    (hrep : ∀ (w : Fin n) (v : Fin m), C.eval (oneEach w v) = A w v)
    (hnl : ∀ g ∈ C.gates, u2.val ∉ g.inputs) (hno : C.output ≠ u2.val) :
    ∃ C2 : Circuit, FanInTwo C2 ∧
      (∀ (w : Fin n) (v : Fin m), w ≠ u2 → C2.eval (oneEach w v) = A w v) ∧
      (C2.size + 1 ≤ C.size ∨ (C2.size ≤ C.size ∧ C2.output ≠ u.val ∧
        ∀ g ∈ C2.gates, u.val ∉ g.inputs)) := by
  have hul := u.isLt
  refine ⟨⟨C.gates.map (tg u.val (n + m + C.gates.length)),
    tau u.val (n + m + C.gates.length) C.output⟩, ?_, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
  · intro g hg
    have hg' : g ∈ C.gates.map (tg u.val (n + m + C.gates.length)) := hg
    rw [List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    have hf := hF g0 hg0
    refine ⟨hf.1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]
    exact hf.2
  · intro w v hw
    have hlx : ∀ z : Fin n, (oneEach z v).length = n + m := by
      intro z
      simp [oneEach]
    have key : ∀ w' : Fin n, ((w' = u2 ∧ w = u) ∨ (w' = w ∧ w ≠ u)) →
        ((C.gates.map (tg u.val (n + m + C.gates.length))).foldl stp (oneEach w v)).getD
          (tau u.val (n + m + C.gates.length) C.output) false =
        (C.gates.foldl stp (oneEach w' v)).getD C.output false := by
      intro w' hw'
      refine simt u.val (n + m + C.gates.length) u2.val (oneEach w' v) (oneEach w v)
        (by rw [hlx, hlx]) (by rw [hlx]; omega) ?_ C.gates (by rw [hlx])
        (fun g hg j hj h => hnl g hg (h ▸ hj)) C.output hno
      intro i hi
      apply bool_iff
      rw [oe, oe]
      unfold tau
      have h0 := w.isLt
      have h00 := v.isLt
      have h000 := u2.isLt
      have h0000 := w'.isLt
      have h1 : w.val ≠ u2.val := fun h => hw (Fin.ext h)
      rcases hw' with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · rw [h2, h3]
        rw [h3] at h1
        split_ifs <;> omega
      · rw [h2]
        have h4 : w.val ≠ u.val := fun h => h3 (Fin.ext h)
        split_ifs <;> omega
    have hk2 : ∀ w' : Fin n, ((w' = u2 ∧ w = u) ∨ (w' = w ∧ w ≠ u)) →
        (⟨C.gates.map (tg u.val (n + m + C.gates.length)),
          tau u.val (n + m + C.gates.length) C.output⟩ : Circuit).eval (oneEach w v) =
        A w' v := by
      intro w' hw'
      exact (key w' hw').trans (hrep w' v)
    by_cases hwu : w = u
    · rw [hk2 u2 (Or.inl ⟨rfl, hwu⟩), hwu, heq]
    · rw [hk2 w (Or.inr ⟨rfl, hwu⟩)]
  · show (C.gates.map _).length ≤ C.gates.length
    rw [List.length_map]
  · show tau u.val (n + m + C.gates.length) C.output ≠ u.val
    unfold tau
    split_ifs <;> omega
  · intro g hg hmem
    have hg' : g ∈ C.gates.map (tg u.val (n + m + C.gates.length)) := hg
    rw [List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    have hmem' : u.val ∈ g0.inputs.map (tau u.val (n + m + C.gates.length)) := hmem
    rw [List.mem_map] at hmem'
    obtain ⟨j, _, hj⟩ := hmem'
    unfold tau at hj
    split_ifs at hj <;> omega

theorem main : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (u u2 : Fin n), (∀ v : Fin m, A u v = A u2 v) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ (∀ (w : Fin n) (v : Fin m), w ≠ u2 → C2.eval (PEqualNP.Represents.oneEach w v) = A w v) ∧ (C2.size + 1 ≤ s ∨ (C2.size ≤ s ∧ (C2.output ≠ u.val ∧ ∀ g < C2.gates.length, (C2.output = n + m + g ∨ (n + m ≤ C2.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C2 g (C2.output - (n + m)))) → u.val ∉ (C2.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs))) := by
  intro n m s A u u2 heq hex
  obtain ⟨C, hF, hs, hrep⟩ := hex
  have hul := u.isLt
  suffices h : ∃ C2 : Circuit, FanInTwo C2 ∧
      (∀ (w : Fin n) (v : Fin m), w ≠ u2 → C2.eval (oneEach w v) = A w v) ∧
      (C2.size + 1 ≤ C.size ∨ (C2.size ≤ C.size ∧ C2.output ≠ u.val ∧
        ∀ g ∈ C2.gates, u.val ∉ g.inputs)) by
    obtain ⟨C2, hF2, hr2, hd⟩ := h
    refine ⟨C2, hF2, hr2, ?_⟩
    rcases hd with h | ⟨h1, h2, h3⟩
    · left
      omega
    · right
      refine ⟨by omega, h2, ?_⟩
      intro g hg _
      refine h3 _ ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg]
      simp
  by_cases hO : C.output = u2.val
  · refine ⟨⟨[], n + m⟩, ?_, ?_, Or.inr ⟨Nat.zero_le _, ?_, ?_⟩⟩
    · intro g hg
      exact absurd hg (List.not_mem_nil)
    · intro w v hw
      have h0 : (C.gates.foldl stp (oneEach w v)).getD C.output false = A w v := hrep w v
      have hl : (oneEach w v).length = n + m := by simp [oneEach]
      show (oneEach w v).getD (n + m) false = A w v
      rw [← h0, hO, pre _ _ _ (by rw [hl]; have := u2.isLt; omega),
        List.getD_eq_default _ _ (by rw [hl])]
      symm
      cases hb : (oneEach w v).getD u2.val false with
      | false => rfl
      | true =>
        rw [oe] at hb
        rcases hb with hb | hb
        · exact absurd (Fin.ext hb).symm hw
        · have := u2.isLt
          omega
    · show n + m ≠ u.val
      omega
    · intro g hg
      exact absurd hg (List.not_mem_nil)
  · have e : (⟨C.gates.map nz, C.output⟩ : Circuit).size = C.size := by
      show (C.gates.map nz).length = C.gates.length
      rw [List.length_map]
    have hF0 : FanInTwo ⟨C.gates.map nz, C.output⟩ := by
      intro g hg
      have hg' : g ∈ C.gates.map nz := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      exact (nz_ok g0 (hF g0 hg0)).1
    have hN0 : ∀ g ∈ (⟨C.gates.map nz, C.output⟩ : Circuit).gates,
        g.op = GateOp.not → g.inputs.length ≤ 1 := by
      intro g hg
      have hg' : g ∈ C.gates.map nz := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      exact (nz_ok g0 (hF g0 hg0)).2
    have hrep0 : ∀ (w : Fin n) (v : Fin m),
        (⟨C.gates.map nz, C.output⟩ : Circuit).eval (oneEach w v) = A w v := by
      intro w v
      have h0 : (C.gates.foldl stp (oneEach w v)).getD C.output false = A w v := hrep w v
      show ((C.gates.map nz).foldl stp (oneEach w v)).getD C.output false = A w v
      rw [nz_fold]
      exact h0
    rw [← e]
    by_cases hlist : ∃ g ∈ (⟨C.gates.map nz, C.output⟩ : Circuit).gates, u2.val ∈ g.inputs
    · exact caseA n m A u u2 _ hF0 hN0 (fun w v _ => hrep0 w v) hlist
    · exact caseB n m A u u2 heq _ hF0 hrep0 (fun g hg hm => hlist ⟨g, hg, hm⟩) hO

end PEqualNP.Outside.L_meta_25000

theorem PEqualNP.Outside.L_meta_25000 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (u u2 : Fin n), (∀ v : Fin m, A u v = A u2 v) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ (∀ (w : Fin n) (v : Fin m), w ≠ u2 → C2.eval (PEqualNP.Represents.oneEach w v) = A w v) ∧ (C2.size + 1 ≤ s ∨ (C2.size ≤ s ∧ (C2.output ≠ u.val ∧ ∀ g < C2.gates.length, (C2.output = n + m + g ∨ (n + m ≤ C2.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C2 g (C2.output - (n + m)))) → u.val ∉ (C2.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs))) :=
  PEqualNP.Outside.L_meta_25000.main

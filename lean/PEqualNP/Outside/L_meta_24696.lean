import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24696

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

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

def colC (n m : ℕ) (k : Fin (m + 1)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)),
    rho (n + k.val) (n + m + 1 + C.gates.length) C.output⟩

theorem colstep (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : Circuit)
    (hrep : ∀ (u : Fin n) (v : Fin m), C.eval (oneEach u (k.succAbove v)) = A u (k.succAbove v)) :
    (colC n m k C).size = C.size ∧ (FanInTwo C → FanInTwo (colC n m k C)) ∧
      Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) (colC n m k C) ∧
      (∀ u : Fin n, ((∃ g ∈ (colC n m k C).gates, u.val ∈ g.inputs) ∨
        (colC n m k C).output = u.val) →
        ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧
      (∀ v : Fin m, ((∃ g ∈ (colC n m k C).gates, n + v.val ∈ g.inputs) ∨
        (colC n m k C).output = n + v.val) →
        ((∃ g ∈ C.gates, n + (k.succAbove v).val ∈ g.inputs) ∨
          C.output = n + (k.succAbove v).val)) := by
  have hk : k.val ≤ m := Nat.lt_succ_iff.mp k.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

theorem gateAt_map (C : Circuit) (p B o j : ℕ) :
    gateAt ⟨C.gates.map (rg p B), o⟩ j = rg p B (gateAt C j) := by
  unfold gateAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.gates[j]? <;> rfl

theorem gmem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  simp

theorem cnt (p B t : ℕ) (hp : p ≤ t) (hB : t < B) : ∀ l : List ℕ, (∀ i ∈ l, i ≠ p) →
    (l.map (rho p B)).count t = l.count (t + 1) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    have ha := h a (List.mem_cons_self)
    have hiff : rho p B a = t ↔ a = t + 1 := by
      unfold rho
      split_ifs <;> omega
    have e : (rho p B a == t) = (a == t + 1) := by
      by_cases h1 : a = t + 1
      · have h2 : rho p B a = t := hiff.mpr h1
        rw [h2, h1]
        simp
      · have h2 : rho p B a ≠ t := fun h => h1 (hiff.mp h)
        simp [h1, h2]
    rw [List.map_cons, List.count_cons, List.count_cons,
      ih (fun i hi => h i (List.mem_cons_of_mem _ hi)), e]

theorem Shp_rg (p r : ℕ) (g : Gate)
    (h : ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    (((rg p r g).op = GateOp.and ∨ (rg p r g).op = GateOp.or) ∧ (rg p r g).inputs.length = 2) ∨
      ((rg p r g).op = GateOp.not ∧ (rg p r g).inputs.length = 1) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, ?_⟩
    show (g.inputs.map (rho p r)).length = 2
    rw [List.length_map]
    exact h2
  · refine Or.inr ⟨h1, ?_⟩
    show (g.inputs.map (rho p r)).length = 1
    rw [List.length_map]
    exact h2

theorem main : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + (m + 1)))) → (∀ g ∈ C.gates, n + k.val ∉ g.inputs) → C.output ≠ n + k.val → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size = C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C hF hrep hred hnl hno
  have hk : k.val ≤ m := Nat.lt_succ_iff.mp k.isLt
  have hsz : C.size = C.gates.length := rfl
  obtain ⟨h1, h2, h3, h4, h5⟩ := colstep n m A k C (fun u v => hrep u (k.succAbove v))
  refine ⟨colC n m k C, h2 hF, h3, ?_, h1, h4, h5⟩
  rcases hred with ⟨hS, hRB, hpos, hout, hread⟩ | ⟨hz, ho⟩
  · left
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      have hg' : g ∈ C.gates.map (rg (n + k.val) (n + m + 1 + C.gates.length)) := hg
      rw [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      exact Shp_rg _ _ _ (hS g0 hg0)
    · intro j hj i hi
      have e : (colC n m k C).gates.length = C.gates.length := h1
      have hj' : j < C.gates.length := by omega
      rw [show gateAt (colC n m k C) j = rg (n + k.val) (n + m + 1 + C.gates.length) (gateAt C j)
        from gateAt_map C _ _ _ j] at hi
      have hi' : i ∈ (gateAt C j).inputs.map (rho (n + k.val) (n + m + 1 + C.gates.length)) := hi
      rw [List.mem_map] at hi'
      obtain ⟨i0, hi0, rfl⟩ := hi'
      have hlt := hRB j hj' i0 hi0
      have hne : i0 ≠ n + k.val := fun h => hnl _ (gmem C j hj') (h ▸ hi0)
      unfold rho
      split_ifs <;> omega
    · rw [h1]
      exact hpos
    · show rho (n + k.val) (n + m + 1 + C.gates.length) C.output + 1 = n + m + (colC n m k C).size
      rw [h1]
      unfold rho
      split_ifs <;> omega
    · intro j hj
      rw [h1] at hj ⊢
      have e : readsIn (colC n m k C) (Finset.range C.size) (n + m + j) =
          readsIn C (Finset.range C.size) (n + (m + 1) + j) := by
        unfold readsIn
        apply Finset.sum_congr rfl
        intro j' hj'
        rw [Finset.mem_range] at hj'
        rw [show gateAt (colC n m k C) j' =
          rg (n + k.val) (n + m + 1 + C.gates.length) (gateAt C j') from gateAt_map C _ _ _ j']
        show ((gateAt C j').inputs.map (rho (n + k.val) (n + m + 1 + C.gates.length))).count
          (n + m + j) = _
        rw [show n + (m + 1) + j = n + m + j + 1 by omega]
        exact cnt (n + k.val) (n + m + 1 + C.gates.length) (n + m + j) (by omega) (by omega) _
          (fun i hi h => hnl _ (gmem C j' hj') (h ▸ hi))
      rw [e]
      exact hread j hj
  · right
    refine ⟨by rw [h1]; exact hz, ?_⟩
    show rho (n + k.val) (n + m + 1 + C.gates.length) C.output < n + m
    unfold rho
    split_ifs <;> omega

end PEqualNP.Outside.L_meta_24696

theorem PEqualNP.Outside.L_meta_24696 : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + (m + 1)))) → (∀ g ∈ C.gates, n + k.val ∉ g.inputs) → C.output ≠ n + k.val → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size = C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) :=
  PEqualNP.Outside.L_meta_24696.main

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20881

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

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

def feeds (N : ℕ) (gs : List Gate) (c w : ℕ) : Prop :=
  ∃ j, j < gs.length ∧ w = N + j ∧ c ∈ (gs.getD j dg).inputs

def Below (N : ℕ) (gs : List Gate) (k w : ℕ) : Prop := Relation.ReflTransGen (feeds N gs) k w

def V (gs : List Gate) (w : ℕ) (x : List Bool) : Bool := (gs.foldl stp x).getD w false

def E (N a b : ℕ) : List Bool := List.ofFn (fun r : Fin N => decide (r.val = a ∨ r.val = b))

def Good (N : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j) ∧
  (∀ c j1 j2, j1 < gs.length → j2 < gs.length → c ∈ (gs.getD j1 dg).inputs →
    c ∈ (gs.getD j2 dg).inputs → j1 = j2) ∧
  (∀ j < gs.length, ∀ a, (gs.getD j dg).inputs ≠ [a, a])

theorem getD_mem' (gs : List Gate) (g : ℕ) (h : g < gs.length) (d : Gate) : gs.getD g d ∈ gs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem E_len (N a b : ℕ) : (E N a b).length = N := by simp [E]

theorem E_get (N a b k : ℕ) (hk : k < N) : (E N a b).getD k false = decide (k = a ∨ k = b) := by
  simp [E, List.getD_eq_getElem?_getD, hk]

theorem gate_two (N : ℕ) (gs : List Gate) (hG : Good N gs) (j : ℕ) (hj : j < gs.length) :
    ∃ a b, (gs.getD j dg).inputs = [a, b] ∧ a < N + j ∧ b < N + j ∧ a ≠ b ∧
      ((gs.getD j dg).op = GateOp.and ∨ (gs.getD j dg).op = GateOp.or) := by
  obtain ⟨h1, h2, _, h4⟩ := hG
  obtain ⟨hop, hl⟩ := h1 _ (getD_mem' gs j hj dg)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hl
  refine ⟨a, b, hab, h2 j hj a (by rw [hab]; simp), h2 j hj b (by rw [hab]; simp), ?_, hop⟩
  intro e
  subst e
  exact h4 j hj a hab

theorem gate_val (N : ℕ) (gs : List Gate) (j a b : ℕ) (hj : j < gs.length)
    (hab : (gs.getD j dg).inputs = [a, b]) (ha : a < N + j) (hb : b < N + j)
    (x : List Bool) (hx : x.length = N) :
    V gs (N + j) x = (gs.getD j dg).op.eval [V gs a x, V gs b x] := by
  have e := wire_at gs x j hj
  rw [hx] at e
  unfold V
  rw [e, hab, List.map_cons, List.map_cons, List.map_nil, ifp ha, ifp hb]

theorem val_and (N : ℕ) (gs : List Gate) (j a b : ℕ) (hj : j < gs.length)
    (hab : (gs.getD j dg).inputs = [a, b]) (ha : a < N + j) (hb : b < N + j)
    (hop : (gs.getD j dg).op = GateOp.and) (x : List Bool) (hx : x.length = N) :
    V gs (N + j) x = (V gs a x && V gs b x) := by
  rw [gate_val N gs j a b hj hab ha hb x hx, hop]
  simp [GateOp.eval]

theorem val_or (N : ℕ) (gs : List Gate) (j a b : ℕ) (hj : j < gs.length)
    (hab : (gs.getD j dg).inputs = [a, b]) (ha : a < N + j) (hb : b < N + j)
    (hop : (gs.getD j dg).op = GateOp.or) (x : List Bool) (hx : x.length = N) :
    V gs (N + j) x = (V gs a x || V gs b x) := by
  rw [gate_val N gs j a b hj hab ha hb x hx, hop]
  simp [GateOp.eval]

theorem below_le (N : ℕ) (gs : List Gate) (hG : Good N gs) (k w : ℕ) (h : Below N gs k w) : k ≤ w := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hf ih =>
    obtain ⟨j, hj, rfl, hc⟩ := hf
    have := hG.2.1 j hj _ hc
    omega

theorem dep (N : ℕ) (gs : List Gate) (hG : Good N gs) (x x' : List Bool) (hx : x.length = N)
    (hx' : x'.length = N) : ∀ w, (∀ k < N, Below N gs k w → x.getD k false = x'.getD k false) →
      V gs w x = V gs w x' := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h1 : w < N
    · unfold V
      rw [inp gs x w (by omega), inp gs x' w (by omega)]
      exact h w h1 Relation.ReflTransGen.refl
    · by_cases h2 : N + gs.length ≤ w
      · unfold V
        rw [beyond gs x w (by omega), beyond gs x' w (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < gs.length := by omega
        obtain ⟨a, b, hab, ha, hb, _, _⟩ := gate_two N gs hG j hj
        rw [gate_val N gs j a b hj hab ha hb x hx, gate_val N gs j a b hj hab ha hb x' hx']
        have fa : feeds N gs a (N + j) := ⟨j, hj, rfl, by rw [hab]; simp⟩
        have fb : feeds N gs b (N + j) := ⟨j, hj, rfl, by rw [hab]; simp⟩
        rw [ih a ha (fun k hk hb' => h k hk (Relation.ReflTransGen.tail hb' fa)),
          ih b hb (fun k hk hb' => h k hk (Relation.ReflTransGen.tail hb' fb))]

theorem zero0 (N : ℕ) (gs : List Gate) (hG : Good N gs) (x : List Bool) (hx : x.length = N)
    (h0 : ∀ k < N, x.getD k false = false) : ∀ w, V gs w x = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < N
    · unfold V
      rw [inp gs x w (by omega)]
      exact h0 w h1
    · by_cases h2 : N + gs.length ≤ w
      · unfold V
        rw [beyond gs x w (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < gs.length := by omega
        obtain ⟨a, b, hab, ha, hb, _, hop⟩ := gate_two N gs hG j hj
        rw [gate_val N gs j a b hj hab ha hb x hx, ih a ha, ih b hb]
        rcases hop with h | h <;> rw [h] <;> rfl

theorem zerob (N : ℕ) (gs : List Gate) (hG : Good N gs) (x : List Bool) (hx : x.length = N) (w : ℕ)
    (h0 : ∀ k < N, Below N gs k w → x.getD k false = false) : V gs w x = false := by
  have hr : (List.replicate N false).length = N := by simp
  have hg : ∀ k < N, (List.replicate N false).getD k false = false := by
    intro k hk
    simp [List.getD_eq_getElem?_getD]
  rw [dep N gs hG x (List.replicate N false) hx hr w (fun k hk hb => by rw [h0 k hk hb, hg k hk])]
  exact zero0 N gs hG _ hr hg w

theorem mono (N : ℕ) (gs : List Gate) (hG : Good N gs) (x x' : List Bool) (hx : x.length = N)
    (hx' : x'.length = N) (hm : ∀ k < N, x.getD k false = true → x'.getD k false = true) :
    ∀ w, V gs w x = true → V gs w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < N
    · unfold V
      rw [inp gs x w (by omega), inp gs x' w (by omega)]
      exact hm w h1
    · by_cases h2 : N + gs.length ≤ w
      · unfold V
        rw [beyond gs x w (by omega), beyond gs x' w (by omega)]
        exact fun h => h
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < gs.length := by omega
        obtain ⟨a, b, hab, ha, hb, _, hop⟩ := gate_two N gs hG j hj
        have ia := ih a ha
        have ib := ih b hb
        rcases hop with h | h
        · rw [val_and N gs j a b hj hab ha hb h x hx, val_and N gs j a b hj hab ha hb h x' hx',
            Bool.and_eq_true, Bool.and_eq_true]
          exact fun hh => ⟨ia hh.1, ib hh.2⟩
        · rw [val_or N gs j a b hj hab ha hb h x hx, val_or N gs j a b hj hab ha hb h x' hx',
            Bool.or_eq_true, Bool.or_eq_true]
          exact fun hh => hh.elim (fun q => Or.inl (ia q)) (fun q => Or.inr (ib q))

theorem red1 (N : ℕ) (gs : List Gate) (hG : Good N gs) (c p q : ℕ) (h : ¬ Below N gs q c) :
    V gs c (E N p q) = V gs c (E N p p) := by
  apply dep N gs hG _ _ (E_len N p q) (E_len N p p)
  intro k hk hb
  rw [E_get N p q k hk, E_get N p p k hk]
  have : k ≠ q := fun e => h (e ▸ hb)
  simp [this]

theorem red2 (N : ℕ) (gs : List Gate) (hG : Good N gs) (c p q : ℕ) (h : ¬ Below N gs p c) :
    V gs c (E N p q) = V gs c (E N q q) := by
  apply dep N gs hG _ _ (E_len N p q) (E_len N q q)
  intro k hk hb
  rw [E_get N p q k hk, E_get N q q k hk]
  have : k ≠ p := fun e => h (e ▸ hb)
  simp [this]

theorem red0 (N : ℕ) (gs : List Gate) (hG : Good N gs) (c p : ℕ) (h : ¬ Below N gs p c) :
    V gs c (E N p p) = false := by
  apply zerob N gs hG _ (E_len N p p)
  intro k hk hb
  rw [E_get N p p k hk]
  have : k ≠ p := fun e => h (e ▸ hb)
  simp [this]

theorem both (N : ℕ) (gs : List Gate) (hG : Good N gs) (c p q : ℕ) (h : V gs c (E N p q) = true)
    (hp : V gs c (E N p p) = false) (hq : V gs c (E N q q) = false) :
    Below N gs p c ∧ Below N gs q c := by
  constructor
  · by_contra hn
    rw [red2 N gs hG c p q hn, hq] at h
    exact Bool.noConfusion h
  · by_contra hn
    rw [red1 N gs hG c p q hn, hp] at h
    exact Bool.noConfusion h

theorem disj (N : ℕ) (gs : List Gate) (hG : Good N gs) (j a b : ℕ) (hj : j < gs.length)
    (hab : (gs.getD j dg).inputs = [a, b]) (hne : a ≠ b) (k : ℕ)
    (h1 : Below N gs k a) (h2 : Below N gs k b) : False := by
  have hU : Relator.RightUnique (feeds N gs) := by
    intro c w w' hw hw'
    obtain ⟨j1, hj1, rfl, hc1⟩ := hw
    obtain ⟨j2, hj2, rfl, hc2⟩ := hw'
    rw [hG.2.2.1 c j1 j2 hj1 hj2 hc1 hc2]
  have ha : a < N + j := hG.2.1 j hj a (by rw [hab]; simp)
  have hb : b < N + j := hG.2.1 j hj b (by rw [hab]; simp)
  have key : ∀ c d, c ∈ (gs.getD j dg).inputs → d < N + j → c ≠ d → Below N gs c d → False := by
    intro c d hc hd hcd hbl
    rcases Relation.ReflTransGen.cases_head hbl with e | ⟨m, hm, hmd⟩
    · exact hcd e
    · obtain ⟨j', hj', rfl, hc'⟩ := hm
      have := hG.2.2.1 c j' j hj' hj hc' hc
      subst this
      have := below_le N gs hG _ _ hmd
      omega
  rcases Relation.ReflTransGen.total_of_right_unique hU h1 h2 with h | h
  · exact key a b (by rw [hab]; simp) hb hne h
  · exact key b a (by rw [hab]; simp) ha (Ne.symm hne) h

theorem P4w (N : ℕ) (gs : List Gate) (hG : Good N gs) : ∀ w i i' j j',
    V gs w (E N i i) = false → V gs w (E N i' i') = false → V gs w (E N j j) = false →
    V gs w (E N j' j') = false → V gs w (E N i j) = true → V gs w (E N i' j) = true →
    V gs w (E N i' j') = true → V gs w (E N i j') = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro i i' j j' si si' sj sj' h1 h2 h3
    by_cases hw1 : w < N
    · exfalso
      unfold V at si sj h1
      rw [inp gs _ w (by rw [E_len]; exact hw1), E_get N _ _ w hw1] at si sj h1
      simp at si sj h1
      omega
    · by_cases hw2 : N + gs.length ≤ w
      · exfalso
        unfold V at h1
        rw [beyond gs _ w (by rw [E_len]; exact hw2)] at h1
        exact Bool.noConfusion h1
      · obtain ⟨g, rfl⟩ : ∃ g, w = N + g := ⟨w - N, by omega⟩
        have hg : g < gs.length := by omega
        obtain ⟨a, b, hab, ha, hb, hne, hop⟩ := gate_two N gs hG g hg
        have dab : ∀ k, Below N gs k a → Below N gs k b → False :=
          fun k => disj N gs hG g a b hg hab hne k
        have dba : ∀ k, Below N gs k b → Below N gs k a → False := fun k p q => dab k q p
        rcases hop with hop | hop
        · have hv : ∀ p q, V gs (N + g) (E N p q) = (V gs a (E N p q) && V gs b (E N p q)) :=
            fun p q => val_and N gs g a b hg hab ha hb hop _ (E_len N p q)
          rw [hv] at si si' sj sj' h1 h2 h3 ⊢
          rw [Bool.and_eq_true] at h1 h2 h3 ⊢
          have andc : ∀ c d, (∀ k, Below N gs k c → Below N gs k d → False) →
              (V gs c (E N i' i') && V gs d (E N i' i')) = false →
              V gs c (E N i j) = true → V gs d (E N i j) = true →
              V gs c (E N i' j) = true → V gs c (E N i' j') = true → V gs d (E N i' j') = true →
              Below N gs i c → V gs c (E N i j') = true ∧ V gs d (E N i j') = true := by
            intro c d hd ti' c1 d1 c2 c3 d3 hic
            have nid : ¬ Below N gs i d := fun h => hd i hic h
            have d1' := d1
            rw [red2 N gs hG d i j nid] at d1'
            have hjd : Below N gs j d := by
              by_contra hn
              rw [red0 N gs hG d j hn] at d1'
              exact Bool.noConfusion d1'
            have njc : ¬ Below N gs j c := fun h => hd j h hjd
            have c1' := c1
            rw [red1 N gs hG c i j njc] at c1'
            have c2' := c2
            rw [red1 N gs hG c i' j njc] at c2'
            have nj'c : ¬ Below N gs j' c := by
              intro hj'c
              have nj'd : ¬ Below N gs j' d := fun h => hd j' hj'c h
              have d3' := d3
              rw [red1 N gs hG d i' j' nj'd] at d3'
              rw [c2', d3'] at ti'
              exact Bool.noConfusion ti'
            have ni'd : ¬ Below N gs i' d := by
              intro hi'd
              have ni'c : ¬ Below N gs i' c := fun h => hd i' h hi'd
              rw [red0 N gs hG c i' ni'c] at c2'
              exact Bool.noConfusion c2'
            constructor
            · rw [red1 N gs hG c i j' nj'c]; exact c1'
            · rw [red2 N gs hG d i j' nid, ← red2 N gs hG d i' j' ni'd]; exact d3
          by_cases hia : Below N gs i a
          · exact andc a b dab si' h1.1 h1.2 h2.1 h3.1 h3.2 hia
          · by_cases hib : Below N gs i b
            · rw [Bool.and_comm] at si'
              have := andc b a dba si' h1.2 h1.1 h2.2 h3.2 h3.1 hib
              exact ⟨this.2, this.1⟩
            · exfalso
              rw [red2 N gs hG a i j hia] at h1
              rw [red2 N gs hG b i j hib] at h1
              rw [h1.1, h1.2] at sj
              exact Bool.noConfusion sj
        · have hv : ∀ p q, V gs (N + g) (E N p q) = (V gs a (E N p q) || V gs b (E N p q)) :=
            fun p q => val_or N gs g a b hg hab ha hb hop _ (E_len N p q)
          rw [hv] at si si' sj sj' h1 h2 h3 ⊢
          rw [Bool.or_eq_false_iff] at si si' sj sj'
          rw [Bool.or_eq_true] at h1 h2 h3 ⊢
          have orc : ∀ c d, c < N + g → (∀ k, Below N gs k c → Below N gs k d → False) →
              V gs c (E N i i) = false → V gs c (E N i' i') = false → V gs c (E N j j) = false →
              V gs c (E N j' j') = false →
              V gs d (E N i' i') = false → V gs d (E N j j) = false → V gs d (E N j' j') = false →
              (V gs c (E N i' j) = true ∨ V gs d (E N i' j) = true) →
              (V gs c (E N i' j') = true ∨ V gs d (E N i' j') = true) →
              V gs c (E N i j) = true → V gs c (E N i j') = true := by
            intro c d hc hd ci ci' cj cj' di' dj dj' q2 q3 c1
            have b1 := both N gs hG c i j c1 ci cj
            have c2 : V gs c (E N i' j) = true := by
              rcases q2 with q | q
              · exact q
              · exact (hd j b1.2 (both N gs hG d i' j q di' dj).2).elim
            have b2 := both N gs hG c i' j c2 ci' cj
            have c3 : V gs c (E N i' j') = true := by
              rcases q3 with q | q
              · exact q
              · exact (hd i' b2.1 (both N gs hG d i' j' q di' dj').1).elim
            exact ih c hc i i' j j' ci ci' cj cj' c1 c2 c3
          rcases h1 with c1 | c1
          · exact Or.inl (orc a b ha dab si.1 si'.1 sj.1 sj'.1 si'.2 sj.2 sj'.2 h2 h3 c1)
          · exact Or.inr (orc b a hb dba si.2 si'.2 sj.2 sj'.2 si'.1 sj.1 sj'.1 h2.symm h3.symm c1)

theorem endgame (n : ℕ) (s : Fin n → Fin n) (Z H : Fin n → Fin n → Bool) (fr fc : Fin n → Bool)
    (Sr Sc : Finset (Fin n))
    (hs_inj : Function.Injective s) (hs1 : ∀ u, s u ≠ u) (hs2 : ∀ u, s (s u) ≠ u)
    (hZ : ∀ u v, Z u v = false ↔ (v = u ∨ v = s u))
    (Trow : ∀ v, v ∉ Sc → ∀ u ∈ Sr, ∀ u' ∈ Sr, fr u = fr u' → Z u v = Z u' v)
    (Tcol : ∀ u, u ∉ Sr → ∀ v ∈ Sc, ∀ v' ∈ Sc, fc v = fc v' → Z u v = Z u v')
    (Tin : ∀ u ∈ Sr, ∀ u' ∈ Sr, ∀ v ∈ Sc, ∀ v' ∈ Sc, H u v = H u' v' → Z u v = Z u' v')
    (mr : ∀ u v, fr u = true → H u v = true) (mc : ∀ u v, fc v = true → H u v = true)
    (P4 : ∀ u u' v v', fr u = false → fr u' = false → fc v = false → fc v' = false →
      H u v = true → H u' v = true → H u' v' = true → H u v' = true) :
    Sr.card ≤ 10 := by
  by_contra hcard
  have rowsmall : ∀ u (T : Finset (Fin n)), (∀ v ∈ T, Z u v = false) → T.card ≤ 2 := by
    intro u T hT
    have hsub : T ⊆ {u, s u} := by
      intro v hv
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact (hZ u v).1 (hT v hv)
    exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
  have colsmall : ∀ v (T : Finset (Fin n)), (∀ u ∈ T, Z u v = false) → T.card ≤ 2 := by
    intro v T hT
    by_contra h
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := (Finset.two_lt_card (s := T)).1 (by omega)
    have key : ∀ x y, x ∈ T → y ∈ T → x ≠ y → v ≠ x → v ≠ y → False := by
      intro x y hx hy hxy h1 h2
      rcases (hZ x v).1 (hT x hx) with e | e
      · exact h1 e
      · rcases (hZ y v).1 (hT y hy) with e' | e'
        · exact h2 e'
        · exact hxy (hs_inj (e.symm.trans e'))
    by_cases va : v = a
    · exact key b c hb hc hbc (fun e => hab (va.symm.trans e)) (fun e => hac (va.symm.trans e))
    · by_cases vb : v = b
      · exact key a c ha hc hac va (fun e => hbc (vb.symm.trans e))
      · exact key a b ha hb hab va vb
  obtain ⟨c, K, hKS, hK6, hKc⟩ : ∃ (c : Bool) (K : Finset (Fin n)), K ⊆ Sr ∧ 6 ≤ K.card ∧
      ∀ u ∈ K, fr u = c := by
    have h := Finset.card_filter_add_card_filter_not (s := Sr) (fun u => fr u = true)
    by_cases h6 : 6 ≤ (Sr.filter (fun u => fr u = true)).card
    · exact ⟨true, _, Finset.filter_subset _ _, h6, fun u hu => (Finset.mem_filter.1 hu).2⟩
    · exact ⟨false, Sr.filter (fun u => ¬ fr u = true), Finset.filter_subset _ _, by omega,
        fun u hu => by simpa using (Finset.mem_filter.1 hu).2⟩
  have K3 : ∀ T : Finset (Fin n), K ⊆ T → T.card ≤ 2 → False := by
    intro T h1 h2
    have := Finset.card_le_card h1
    omega
  have good : ∀ u ∈ K, ∀ v, Z u v = false → v ∈ Sc := by
    intro u hu v hz
    by_contra hv
    exact K3 K (Finset.Subset.refl K) (colsmall v K (fun u' hu' => by
      rw [← Trow v hv u (hKS hu) u' (hKS hu') (by rw [hKc u hu, hKc u' hu'])]
      exact hz))
  have hZd : ∀ u, Z u u = false := fun u => (hZ u u).2 (Or.inl rfl)
  have zs : ∀ u, Z u (s u) = false := fun u => (hZ u (s u)).2 (Or.inr rfl)
  have zt : ∀ u v, v ≠ u → v ≠ s u → Z u v = true := by
    intro u v h1 h2
    rw [← Bool.not_eq_false]
    intro h
    rcases (hZ u v).1 h with e | e
    · exact h1 e
    · exact h2 e
  have KSc : K ⊆ Sc := fun u hu => good u hu u (hZd u)
  have pick : ∀ (T : Finset (Fin n)), T.card < 6 → ∃ e ∈ K, e ∉ T :=
    fun T hT => Finset.exists_mem_notMem_of_card_lt_card (lt_of_lt_of_le hT hK6)
  obtain ⟨u0, hu0, -⟩ := pick ∅ (by simp)
  obtain ⟨v1, hv1, hv1n⟩ := pick {u0, s u0} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hv1n
  have zv1 : Z u0 v1 = true := zt u0 v1 hv1n.1 hv1n.2
  have hne : H u0 u0 ≠ H u0 v1 := by
    intro e
    have := Tin u0 (hKS hu0) u0 (hKS hu0) u0 (KSc hu0) v1 (KSc hv1) e
    rw [hZd, zv1] at this
    exact Bool.noConfusion this
  cases hH : H u0 u0 with
  | false =>
    have hv1H : H u0 v1 = true := by
      rw [hH] at hne
      rw [← Bool.not_eq_false]
      exact fun e => hne e.symm
    have ZH : ∀ u ∈ Sr, ∀ v ∈ Sc, Z u v = H u v := by
      intro u hu v hv
      cases hh : H u v with
      | false =>
        rw [Tin u hu u0 (hKS hu0) v hv u0 (KSc hu0) (by rw [hh, hH])]
        exact hZd u0
      | true =>
        rw [Tin u hu u0 (hKS hu0) v hv v1 (KSc hv1) (by rw [hh, hv1H])]
        exact zv1
    have fK : ∀ u ∈ K, fr u = false ∧ fc u = false := by
      intro u hu
      have hd : H u u = false := by
        rw [← ZH u (hKS hu) u (KSc hu)]
        exact hZd u
      constructor
      · by_contra h
        rw [Bool.not_eq_false] at h
        rw [mr u u h] at hd
        exact Bool.noConfusion hd
      · by_contra h
        rw [Bool.not_eq_false] at h
        rw [mc u u h] at hd
        exact Bool.noConfusion hd
    obtain ⟨i', hi', -⟩ := pick ∅ (by simp)
    obtain ⟨i, hi, hin⟩ := pick {i', s i'} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
    obtain ⟨j, hj, hjn⟩ := pick {i, s i, i', s i'} (lt_of_le_of_lt Finset.card_le_four (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hin hjn
    have a1 : H i' i = true := by
      rw [← ZH i' (hKS hi') i (KSc hi)]
      exact zt i' i hin.1 hin.2
    have a2 : H i j = true := by
      rw [← ZH i (hKS hi) j (KSc hj)]
      exact zt i j hjn.1 hjn.2.1
    have a3 : H i' j = true := by
      rw [← ZH i' (hKS hi') j (KSc hj)]
      exact zt i' j hjn.2.2.1 hjn.2.2.2
    have := P4 i i' j i (fK i hi).1 (fK i' hi').1 (fK j hj).2 (fK i hi).2 a2 a3 a1
    rw [← ZH i (hKS hi) i (KSc hi), hZd] at this
    exact Bool.noConfusion this
  | true =>
    have hv1H : H u0 v1 = false := by
      rw [hH] at hne
      rw [← Bool.not_eq_true]
      exact fun e => hne e.symm
    have ZH : ∀ u ∈ Sr, ∀ v ∈ Sc, Z u v = !H u v := by
      intro u hu v hv
      cases hh : H u v with
      | false =>
        rw [Tin u hu u0 (hKS hu0) v hv v1 (KSc hv1) (by rw [hh, hv1H])]
        exact zv1
      | true =>
        rw [Tin u hu u0 (hKS hu0) v hv u0 (KSc hu0) (by rw [hh, hH])]
        exact hZd u0
    have frz : ∀ u ∈ Sr, fr u = false := by
      intro u hu
      by_contra h
      rw [Bool.not_eq_false] at h
      exact K3 K (Finset.Subset.refl K) (rowsmall u K (fun v hv => by
        rw [ZH u hu v (KSc hv), mr u v h]; rfl))
    have fcz : ∀ v ∈ Sc, fc v = false := by
      intro v hv
      by_contra h
      rw [Bool.not_eq_false] at h
      exact K3 K (Finset.Subset.refl K) (colsmall v K (fun u hu => by
        rw [ZH u (hKS hu) v hv, mc u v h]; rfl))
    have goodr : ∀ u ∈ Sr, ∀ v, Z u v = false → v ∈ Sc := by
      intro u hu v hz
      by_contra hv
      exact K3 K (Finset.Subset.refl K) (colsmall v K (fun u' hu' => by
        rw [← Trow v hv u hu u' (hKS hu') (by rw [frz u hu, frz u' (hKS hu')])]
        exact hz))
    have goodc : ∀ v ∈ Sc, ∀ u, Z u v = false → u ∈ Sr := by
      intro v hv u hz
      by_contra hu
      exact K3 K (Finset.Subset.refl K) (rowsmall u K (fun v' hv' => by
        rw [← Tcol u hu v hv v' (KSc hv') (by rw [fcz v hv, fcz v' (KSc hv')])]
        exact hz))
    have r0 := hKS hu0
    have c1 := goodr u0 r0 (s u0) (zs u0)
    have r1 := goodc (s u0) c1 (s u0) (hZd _)
    have c2 := goodr (s u0) r1 (s (s u0)) (zs _)
    have Ht : ∀ u ∈ Sr, ∀ v ∈ Sc, Z u v = false → H u v = true := by
      intro u hu v hv hz
      have := ZH u hu v hv
      rw [hz] at this
      cases hh : H u v with
      | false => rw [hh] at this; exact Bool.noConfusion this
      | true => rfl
    have := P4 u0 (s u0) (s u0) (s (s u0)) (frz _ r0) (frz _ r1) (fcz _ c1) (fcz _ c2)
      (Ht _ r0 _ c1 (zs u0)) (Ht _ r1 _ c1 (hZd _)) (Ht _ r1 _ c2 (zs _))
    have hz : Z u0 (s (s u0)) = false := by
      rw [ZH u0 r0 _ c2, this]; rfl
    rcases (hZ _ _).1 hz with e | e
    · exact hs2 u0 e
    · exact hs1 (s u0) e

theorem smod (n a : ℕ) (ha : a < n) : (a + 1) % n = if a + 1 = n then 0 else a + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem pmod (n a : ℕ) (ha : a < n) : (a + n - 1) % n = if a = 0 then n - 1 else a - 1 := by
  split_ifs with h
  · subst h
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · have e : a + n - 1 = (a - 1) + n := by omega
    rw [e, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

def sF (n : ℕ) (hn : 0 < n) (u : Fin n) : Fin n := ⟨(u.val + 1) % n, Nat.mod_lt _ hn⟩

def pF (n : ℕ) (hn : 0 < n) (v : Fin n) : Fin n := ⟨(v.val + n - 1) % n, Nat.mod_lt _ hn⟩

theorem sF_inj (n : ℕ) (hn : 3 ≤ n) (h0 : 0 < n) : Function.Injective (sF n h0) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [sF] at h'
  rw [smod n a.val a.isLt, smod n b.val b.isLt] at h'
  apply Fin.ext
  split_ifs at h' <;> omega

theorem sF_ne (n : ℕ) (hn : 3 ≤ n) (h0 : 0 < n) (a : Fin n) : sF n h0 a ≠ a := by
  intro h
  have h' := congrArg Fin.val h
  simp only [sF] at h'
  rw [smod n a.val a.isLt] at h'
  have := a.isLt
  split_ifs at h' <;> omega

theorem sF_ne2 (n : ℕ) (hn : 3 ≤ n) (h0 : 0 < n) (a : Fin n) : sF n h0 (sF n h0 a) ≠ a := by
  intro h
  have h' := congrArg Fin.val h
  simp only [sF] at h'
  rw [smod n _ (Nat.mod_lt _ h0), smod n a.val a.isLt] at h'
  have := a.isLt
  split_ifs at h' <;> omega

theorem pF_inj (n : ℕ) (hn : 3 ≤ n) (h0 : 0 < n) : Function.Injective (pF n h0) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [pF] at h'
  rw [pmod n a.val a.isLt, pmod n b.val b.isLt] at h'
  have := a.isLt
  have := b.isLt
  apply Fin.ext
  split_ifs at h' <;> omega

theorem pF_ne (n : ℕ) (hn : 3 ≤ n) (h0 : 0 < n) (a : Fin n) : pF n h0 a ≠ a := by
  intro h
  have h' := congrArg Fin.val h
  simp only [pF] at h'
  rw [pmod n a.val a.isLt] at h'
  have := a.isLt
  split_ifs at h' <;> omega

theorem pF_ne2 (n : ℕ) (hn : 3 ≤ n) (h0 : 0 < n) (a : Fin n) : pF n h0 (pF n h0 a) ≠ a := by
  intro h
  have h' := congrArg Fin.val h
  simp only [pF] at h'
  rw [pmod n _ (Nat.mod_lt _ h0), pmod n a.val a.isLt] at h'
  have := a.isLt
  split_ifs at h' <;> omega

theorem sp (n : ℕ) (h0 : 0 < n) (u v : Fin n) : v = sF n h0 u ↔ u = pF n h0 v := by
  rw [Fin.ext_iff, Fin.ext_iff]
  simp only [sF, pF]
  rw [smod n u.val u.isLt, pmod n v.val v.isLt]
  have := u.isLt
  have := v.isLt
  split_ifs <;> omega

theorem mkGood (N : ℕ) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < N + j)
    (hr1 : ∀ c, c < N + gs.length →
      PEqualNP.MetaComplexity.NestedCover.readsIn ⟨gs, o⟩ (Finset.range gs.length) c ≤ 1) :
    Good N gs := by
  refine ⟨hg, hrb, ?_, ?_⟩
  · intro c j1 j2 hj1 hj2 hc1 hc2
    by_contra hne
    have hc := hr1 c (by have := hrb j1 hj1 c hc1; omega)
    have hsub : ({j1, j2} : Finset ℕ) ⊆ Finset.range gs.length := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_range]
      rcases hx with rfl | rfl <;> assumption
    have hle := Finset.sum_le_sum_of_subset (f := fun j => ((gs.getD j dg).inputs.count c)) hsub
    rw [Finset.sum_pair hne] at hle
    have p1 : 0 < (gs.getD j1 dg).inputs.count c := List.count_pos_iff.2 hc1
    have p2 : 0 < (gs.getD j2 dg).inputs.count c := List.count_pos_iff.2 hc2
    have hc' : ∑ j ∈ Finset.range gs.length, (gs.getD j dg).inputs.count c ≤ 1 := hc
    omega
  · intro j hj a hab
    have ha : a < N + j := hrb j hj a (by rw [hab]; simp)
    have hc : ∑ j ∈ Finset.range gs.length, (gs.getD j dg).inputs.count a ≤ 1 := hr1 a (by omega)
    have hle := Finset.single_le_sum (f := fun j => ((gs.getD j dg).inputs.count a))
      (fun i _ => Nat.zero_le _) (Finset.mem_range.2 hj)
    simp only [hab] at hle
    have : [a, a].count a = 2 := by simp
    omega

theorem leaf_read (N : ℕ) (gs : List Gate) (o k w : ℕ) (h : Below N gs k w) (hne : k ≠ w) :
    1 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn ⟨gs, o⟩ (Finset.range gs.length) k := by
  rcases Relation.ReflTransGen.cases_head h with e | ⟨m, hm, _⟩
  · exact (hne e).elim
  · obtain ⟨j, hj, _, hk⟩ := hm
    have hle := Finset.single_le_sum (f := fun j => ((gs.getD j dg).inputs.count k))
      (fun i _ => Nat.zero_le _) (Finset.mem_range.2 hj)
    have p1 : 0 < (gs.getD j dg).inputs.count k := List.count_pos_iff.2 hk
    show 1 ≤ ∑ j ∈ Finset.range gs.length, (gs.getD j dg).inputs.count k
    omega

def cr (n : ℕ) (u : Fin n) : Fin (n + n) := ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right n n)⟩

def cc (n : ℕ) (v : Fin n) : Fin (n + n) := ⟨n + v.val, Nat.add_lt_add_left v.isLt n⟩

theorem main : ∀ (n : ℕ), 4 ≤ n → ∀ (S : Finset (Fin (n + n))) (F : PEqualNP.CircuitLowerBounds.Circuit)
  (b : (Fin (n + n) → Bool) → Bool) (G : Bool → (Fin (n + n) → Bool) → Bool),
  (∀ g ∈ F.gates,
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) F →
  0 < F.size →
  F.output + 1 = n + n + F.size →
  (∀ i : Fin (n + n), PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (i : ℕ) =
    if i ∈ S then 1 else 0) →
  (∀ j < F.size, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (n + n + j) =
    if j + 1 = F.size then 0 else 1) →
  (∀ x y : Fin (n + n) → Bool, (∀ i, i ∉ S → x i = y i) → b x = b y) →
  (∀ (c : Bool) (x y : Fin (n + n) → Bool), (∀ i, i ∉ S → x i = y i) → G c x = G c y) →
  (∀ (u v : Fin n) (x : Fin (n + n) → Bool),
    x = (fun r : Fin (n + n) => decide ((r : ℕ) = u.val ∨ (r : ℕ) = n + v.val)) →
    decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) = G (b x || F.eval (List.ofFn x)) x) →
  S.card ≤ 20 := by
  intro n hn S F b G hg hrb hpos hout hin hgt hb hG hA
  obtain ⟨gs, o⟩ := F
  have h0 : 0 < n := by omega
  have hn3 : 3 ≤ n := by omega
  have hpos' : 0 < gs.length := hpos
  have ho : o + 1 = n + n + gs.length := hout
  have hin' : ∀ i : Fin (n + n),
      PEqualNP.MetaComplexity.NestedCover.readsIn ⟨gs, o⟩ (Finset.range gs.length) i.val =
        if i ∈ S then 1 else 0 := hin
  have hgt' : ∀ j < gs.length,
      PEqualNP.MetaComplexity.NestedCover.readsIn ⟨gs, o⟩ (Finset.range gs.length) (n + n + j) =
        if j + 1 = gs.length then 0 else 1 := hgt
  have GD : Good (n + n) gs := by
    apply mkGood (n + n) gs o hg hrb
    intro c hc
    by_cases h : c < n + n
    · have := hin' ⟨c, h⟩
      simp only at this
      rw [this]
      split_ifs <;> omega
    · have e : c = n + n + (c - (n + n)) := by omega
      rw [e, hgt' (c - (n + n)) (by omega)]
      split_ifs <;> omega
  have notb : ∀ (i : Fin (n + n)), i ∉ S → ¬ Below (n + n) gs i.val o := by
    intro i hi hbl
    have := leaf_read (n + n) gs o i.val o hbl (by have := i.isLt; omega)
    rw [hin' i, ifn hi] at this
    omega
  have hA' : ∀ u v : Fin n, decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) =
      G (b (fun r : Fin (n + n) => decide ((r : ℕ) = u.val ∨ (r : ℕ) = n + v.val)) ||
        V gs o (E (n + n) u.val (n + v.val)))
        (fun r : Fin (n + n) => decide ((r : ℕ) = u.val ∨ (r : ℕ) = n + v.val)) :=
    fun u v => hA u v _ rfl
  have Tgen : ∀ u v u' v' : Fin n,
      (∀ i : Fin (n + n), i ∉ S → decide ((i : ℕ) = u.val ∨ (i : ℕ) = n + v.val) =
        decide ((i : ℕ) = u'.val ∨ (i : ℕ) = n + v'.val)) →
      V gs o (E (n + n) u.val (n + v.val)) = V gs o (E (n + n) u'.val (n + v'.val)) →
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) =
        decide (v'.val ≠ u'.val ∧ v'.val ≠ (u'.val + 1) % n) := by
    intro u v u' v' hag e
    have hag' : ∀ i : Fin (n + n), i ∉ S →
        (fun r : Fin (n + n) => decide ((r : ℕ) = u.val ∨ (r : ℕ) = n + v.val)) i =
        (fun r : Fin (n + n) => decide ((r : ℕ) = u'.val ∨ (r : ℕ) = n + v'.val)) i := hag
    rw [hA' u v, hA' u' v', hb _ _ hag', e, hG _ _ _ hag']
  have nr : ∀ (i : Fin (n + n)) (u : Fin n), i ∉ S → cr n u ∈ S → i.val ≠ u.val := by
    intro i u hi hu e
    exact hi ((Fin.ext e : i = cr n u) ▸ hu)
  have nc : ∀ (i : Fin (n + n)) (v : Fin n), i ∉ S → cc n v ∈ S → i.val ≠ n + v.val := by
    intro i v hi hv e
    exact hi ((Fin.ext e : i = cc n v) ▸ hv)
  have hSr : ∀ u : Fin n, u ∈ Finset.univ.filter (fun u : Fin n => cr n u ∈ S) ↔ cr n u ∈ S := by
    intro u
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hSc : ∀ v : Fin n, v ∈ Finset.univ.filter (fun v : Fin n => cc n v ∈ S) ↔ cc n v ∈ S := by
    intro v
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hZ : ∀ u v : Fin n, decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) = false ↔
      (v = u ∨ v = sF n h0 u) := by
    intro u v
    rw [decide_eq_false_iff_not, Fin.ext_iff, Fin.ext_iff]
    show ¬ (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) ↔ (v.val = u.val ∨ v.val = (u.val + 1) % n)
    tauto
  have Trow : ∀ v : Fin n, v ∉ Finset.univ.filter (fun v : Fin n => cc n v ∈ S) →
      ∀ u ∈ Finset.univ.filter (fun u : Fin n => cr n u ∈ S),
      ∀ u' ∈ Finset.univ.filter (fun u : Fin n => cr n u ∈ S),
      V gs o (E (n + n) u.val u.val) = V gs o (E (n + n) u'.val u'.val) →
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) =
        decide (v.val ≠ u'.val ∧ v.val ≠ (u'.val + 1) % n) := by
    intro v hv u hu u' hu' hf
    rw [hSc] at hv
    rw [hSr] at hu hu'
    apply Tgen u v u' v
    · intro i hi
      have h1 := nr i u hi hu
      have h2 := nr i u' hi hu'
      simp [h1, h2]
    · have nb := notb (cc n v) hv
      rw [red1 (n + n) gs GD o u.val (n + v.val) nb, red1 (n + n) gs GD o u'.val (n + v.val) nb]
      exact hf
  have Tcol : ∀ u : Fin n, u ∉ Finset.univ.filter (fun u : Fin n => cr n u ∈ S) →
      ∀ v ∈ Finset.univ.filter (fun v : Fin n => cc n v ∈ S),
      ∀ v' ∈ Finset.univ.filter (fun v : Fin n => cc n v ∈ S),
      V gs o (E (n + n) (n + v.val) (n + v.val)) = V gs o (E (n + n) (n + v'.val) (n + v'.val)) →
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) =
        decide (v'.val ≠ u.val ∧ v'.val ≠ (u.val + 1) % n) := by
    intro u hu v hv v' hv' hf
    rw [hSr] at hu
    rw [hSc] at hv hv'
    apply Tgen u v u v'
    · intro i hi
      have h1 := nc i v hi hv
      have h2 := nc i v' hi hv'
      simp [h1, h2]
    · have nb := notb (cr n u) hu
      rw [red2 (n + n) gs GD o u.val (n + v.val) nb, red2 (n + n) gs GD o u.val (n + v'.val) nb]
      exact hf
  have Tin : ∀ u ∈ Finset.univ.filter (fun u : Fin n => cr n u ∈ S),
      ∀ u' ∈ Finset.univ.filter (fun u : Fin n => cr n u ∈ S),
      ∀ v ∈ Finset.univ.filter (fun v : Fin n => cc n v ∈ S),
      ∀ v' ∈ Finset.univ.filter (fun v : Fin n => cc n v ∈ S),
      V gs o (E (n + n) u.val (n + v.val)) = V gs o (E (n + n) u'.val (n + v'.val)) →
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) =
        decide (v'.val ≠ u'.val ∧ v'.val ≠ (u'.val + 1) % n) := by
    intro u hu u' hu' v hv v' hv' hf
    rw [hSr] at hu hu'
    rw [hSc] at hv hv'
    apply Tgen u v u' v' _ hf
    intro i hi
    have h1 := nr i u hi hu
    have h2 := nr i u' hi hu'
    have h3 := nc i v hi hv
    have h4 := nc i v' hi hv'
    simp [h1, h2, h3, h4]
  have mr : ∀ u v : Fin n, V gs o (E (n + n) u.val u.val) = true →
      V gs o (E (n + n) u.val (n + v.val)) = true := by
    intro u v
    apply mono (n + n) gs GD _ _ (E_len _ _ _) (E_len _ _ _)
    intro k hk
    rw [E_get _ _ _ k hk, E_get _ _ _ k hk, decide_eq_true_iff, decide_eq_true_iff]
    exact fun h => Or.inl (h.elim id id)
  have mc : ∀ u v : Fin n, V gs o (E (n + n) (n + v.val) (n + v.val)) = true →
      V gs o (E (n + n) u.val (n + v.val)) = true := by
    intro u v
    apply mono (n + n) gs GD _ _ (E_len _ _ _) (E_len _ _ _)
    intro k hk
    rw [E_get _ _ _ k hk, E_get _ _ _ k hk, decide_eq_true_iff, decide_eq_true_iff]
    exact fun h => Or.inr (h.elim id id)
  have R := endgame n (sF n h0)
    (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n))
    (fun u v : Fin n => V gs o (E (n + n) u.val (n + v.val)))
    (fun u : Fin n => V gs o (E (n + n) u.val u.val))
    (fun v : Fin n => V gs o (E (n + n) (n + v.val) (n + v.val)))
    (Finset.univ.filter (fun u : Fin n => cr n u ∈ S))
    (Finset.univ.filter (fun v : Fin n => cc n v ∈ S))
    (sF_inj n hn3 h0) (sF_ne n hn3 h0) (sF_ne2 n hn3 h0) hZ Trow Tcol Tin mr mc
    (fun u u' v v' => P4w (n + n) gs GD o u.val u'.val (n + v.val) (n + v'.val))
  have Cc := endgame n (pF n h0)
    (fun v u : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n))
    (fun v u : Fin n => V gs o (E (n + n) u.val (n + v.val)))
    (fun v : Fin n => V gs o (E (n + n) (n + v.val) (n + v.val)))
    (fun u : Fin n => V gs o (E (n + n) u.val u.val))
    (Finset.univ.filter (fun v : Fin n => cc n v ∈ S))
    (Finset.univ.filter (fun u : Fin n => cr n u ∈ S))
    (pF_inj n hn3 h0) (pF_ne n hn3 h0) (pF_ne2 n hn3 h0)
    (fun v u => by
      rw [hZ u v, sp n h0 u v]
      exact ⟨fun h => h.elim (fun e => Or.inl e.symm) Or.inr,
        fun h => h.elim (fun e => Or.inl e.symm) Or.inr⟩)
    (fun u hu v hv v' hv' hf => Tcol u hu v hv v' hv' hf)
    (fun v hv u hu u' hu' hf => Trow v hv u hu u' hu' hf)
    (fun v hv v' hv' u hu u' hu' hf => Tin u hu u' hu' v hv v' hv' hf)
    (fun v u h => mc u v h) (fun v u h => mr u v h)
    (fun v v' u u' a1 a2 a3 a4 b1 b2 b3 =>
      P4w (n + n) gs GD o u'.val u.val (n + v'.val) (n + v.val) a4 a3 a2 a1 b3 b2 b1)
  have hsub : S ⊆ (Finset.univ.filter (fun u : Fin n => cr n u ∈ S)).image (cr n) ∪
      (Finset.univ.filter (fun v : Fin n => cc n v ∈ S)).image (cc n) := by
    intro i hi
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    by_cases h : i.val < n
    · left
      have e : cr n ⟨i.val, h⟩ = i := Fin.ext rfl
      exact ⟨⟨i.val, h⟩, (hSr _).2 (by rw [e]; exact hi), e⟩
    · right
      have hlt : i.val - n < n := by have := i.isLt; omega
      have e : cc n ⟨i.val - n, hlt⟩ = i := by
        apply Fin.ext
        show n + (i.val - n) = i.val
        omega
      exact ⟨⟨i.val - n, hlt⟩, (hSc _).2 (by rw [e]; exact hi), e⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((Finset.univ.filter (fun u : Fin n => cr n u ∈ S)).image (cr n))
    ((Finset.univ.filter (fun v : Fin n => cc n v ∈ S)).image (cc n))
  have h3 := Finset.card_image_le (s := Finset.univ.filter (fun u : Fin n => cr n u ∈ S)) (f := cr n)
  have h4 := Finset.card_image_le (s := Finset.univ.filter (fun v : Fin n => cc n v ∈ S)) (f := cc n)
  omega

end PEqualNP.Outside.L_meta_20881

theorem PEqualNP.Outside.L_meta_20881 : ∀ (n : ℕ), 4 ≤ n → ∀ (S : Finset (Fin (n + n))) (F : PEqualNP.CircuitLowerBounds.Circuit)
  (b : (Fin (n + n) → Bool) → Bool) (G : Bool → (Fin (n + n) → Bool) → Bool),
  (∀ g ∈ F.gates,
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) F →
  0 < F.size →
  F.output + 1 = n + n + F.size →
  (∀ i : Fin (n + n), PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (i : ℕ) =
    if i ∈ S then 1 else 0) →
  (∀ j < F.size, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (n + n + j) =
    if j + 1 = F.size then 0 else 1) →
  (∀ x y : Fin (n + n) → Bool, (∀ i, i ∉ S → x i = y i) → b x = b y) →
  (∀ (c : Bool) (x y : Fin (n + n) → Bool), (∀ i, i ∉ S → x i = y i) → G c x = G c y) →
  (∀ (u v : Fin n) (x : Fin (n + n) → Bool),
    x = (fun r : Fin (n + n) => decide ((r : ℕ) = u.val ∨ (r : ℕ) = n + v.val)) →
    decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) = G (b x || F.eval (List.ofFn x)) x) →
  S.card ≤ 20 :=
  PEqualNP.Outside.L_meta_20881.main


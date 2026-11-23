import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_991

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

def Wv (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

theorem Wv_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    Wv C n x i = x i := by
  unfold Wv
  rw [wires_eq, foldl_step_getD _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem Wv_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (t : ℕ) (ht : t < C.gates.length) :
    Wv C n x (n + t) = (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
      if i < n + t then Wv C n x i else false) := by
  have := gate_value C.gates (List.ofFn x) t ht
  rw [List.length_ofFn] at this
  exact this

theorem Wv_big (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) : Wv C n x i = false := by
  unfold Wv
  rw [wires_eq]
  apply getD_of_length_le
  rw [foldl_step_length, List.length_ofFn]
  exact hi


def ind (n : ℕ) (A : Finset (Fin n)) : Fin n → Bool := fun q => decide (q ∈ A)

def below (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, Wv C n x j = true → ∃ p ∈ S, x p = true

def Ls (C : Circuit) (n : ℕ) (y : Finset (Fin n)) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => Wv C n (ind n (insert p y)) j = true)

theorem mem_Ls (C : Circuit) (n : ℕ) (y : Finset (Fin n)) (j : ℕ) (p : Fin n) :
    p ∈ Ls C n y j ↔ Wv C n (ind n (insert p y)) j = true := by
  simp [Ls]

theorem gate_lift (C : Circuit) (n : ℕ) (x y : Fin n → Bool) (t : ℕ) (ht : t < C.gates.length)
    (hop : (C.gates[t]).op = GateOp.and ∨ (C.gates[t]).op = GateOp.or)
    (h : ∀ a ∈ (C.gates[t]).inputs, (if a < n + t then Wv C n x a else false) = true →
      (if a < n + t then Wv C n y a else false) = true) :
    Wv C n x (n + t) = true → Wv C n y (n + t) = true := by
  rw [Wv_gate C n x t ht, Wv_gate C n y t ht]
  rcases hop with h' | h'
  · rw [h']
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    rintro hh v ⟨a, ha, rfl⟩
    exact h a ha (hh _ ⟨a, ha, rfl⟩)
  · rw [h']
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨v, ⟨a, ha, rfl⟩, hv⟩
    exact ⟨_, ⟨a, ha, rfl⟩, h a ha hv⟩

theorem Wv_mono (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ j, Wv C n x j = true → Wv C n y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  by_cases hin : j < n
  · have h1 := Wv_input C n x ⟨j, hin⟩
    have h2 := Wv_input C n y ⟨j, hin⟩
    simp only at h1 h2
    rw [h1, h2]
    exact hxy _
  · by_cases hbig : n + C.gates.length ≤ j
    · rw [Wv_big C n x j hbig]
      intro h
      exact absurd h (by simp)
    · obtain ⟨t, rfl⟩ : ∃ t, j = n + t := ⟨j - n, by omega⟩
      have ht : t < C.gates.length := by omega
      apply gate_lift C n x y t ht (hg (C.gates[t]) (List.getElem_mem ht)).1
      intro a _
      split_ifs with hlt
      · exact ih a hlt
      · exact id

theorem priv_range (C : Circuit) (n : ℕ) (S y : Finset (Fin n)) (hy : Disjoint y S) (j : ℕ)
    (hb : below C n S j) (h2 : 2 ≤ (Ls C n y j).card) :
    n ≤ j ∧ j < n + C.gates.length := by
  constructor
  · by_contra hlt
    push_neg at hlt
    have hjy : (⟨j, hlt⟩ : Fin n) ∉ y := by
      intro hmem
      have h1 := Wv_input C n (ind n y) ⟨j, hlt⟩
      simp only at h1
      obtain ⟨p, hpS, hpy⟩ := hb (ind n y) (by rw [h1]; simp [ind, hmem])
      simp only [ind, decide_eq_true_eq] at hpy
      exact Finset.disjoint_left.mp hy hpy hpS
    have hsub : Ls C n y j ⊆ {⟨j, hlt⟩} := by
      intro p hp
      rw [mem_Ls] at hp
      have h1 := Wv_input C n (ind n (insert p y)) ⟨j, hlt⟩
      simp only at h1
      rw [h1] at hp
      simp only [ind, decide_eq_true_eq, Finset.mem_insert] at hp
      rw [Finset.mem_singleton]
      rcases hp with hp | hp
      · exact hp.symm
      · exact absurd hp hjy
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  · by_contra hge
    push_neg at hge
    have hemp : Ls C n y j = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      rw [mem_Ls, Wv_big C n _ j hge] at hp
      exact Bool.false_ne_true hp
    rw [hemp] at h2
    simp at h2

theorem inv (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S y : Finset (Fin n)) (hy : Disjoint y S) :
    ∀ N : ℕ, ∀ J : Finset ℕ, (∀ j ∈ J, j < N) →
      ∃ (D : Finset ℕ) (A B : Finset (Fin n)),
        (∀ t ∈ D, n + t < N ∧ t < C.gates.length ∧ below C n S (n + t) ∧
          2 ≤ (Ls C n y (n + t)).card) ∧
        (∀ q ∈ A, q ∉ S) ∧
        B.card ≤ D.card + J.card ∧
        ∀ j ∈ J, ∀ p ∈ S, p ∉ B → Wv C n (ind n (insert p y)) j = true →
          Wv C n (ind n (A ∪ y)) j = true := by
  intro N
  induction N with
  | zero =>
    intro J hJ
    have hJe : J = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      have := hJ j hj
      omega
    subst hJe
    exact ⟨∅, ∅, ∅, by simp, by simp, by simp, by simp⟩
  | succ N ih =>
    intro J hJ
    by_cases hN : N ∈ J
    · have hJ0 : ∀ j ∈ J.erase N, j < N := by
        intro j hj
        rw [Finset.mem_erase] at hj
        have := hJ j hj.2
        omega
      have hcard : (J.erase N).card + 1 = J.card := Finset.card_erase_add_one hN
      by_cases hsub : below C n S N
      · by_cases hpriv : 2 ≤ (Ls C n y N).card
        · obtain ⟨hnN, hNlt⟩ := priv_range C n S y hy N hsub hpriv
          obtain ⟨t, rfl⟩ : ∃ t, N = n + t := ⟨N - n, by omega⟩
          have ht : t < C.gates.length := by omega
          obtain ⟨hop, hlen⟩ := hg (C.gates[t]) (List.getElem_mem ht)
          have hJ' : ∀ j ∈ J.erase (n + t) ∪ ((C.gates[t]).inputs.toFinset.filter (fun i => i < n + t)),
              j < n + t := by
            intro j hj
            rw [Finset.mem_union] at hj
            rcases hj with hj | hj
            · exact hJ0 j hj
            · exact (Finset.mem_filter.mp hj).2
          obtain ⟨D, A, B, hD, hA, hc, hp⟩ := ih _ hJ'
          have htD : t ∉ D := by
            intro h
            have := (hD t h).1
            omega
          have hJc : (J.erase (n + t) ∪ ((C.gates[t]).inputs.toFinset.filter (fun i => i < n + t))).card ≤
              (J.erase (n + t)).card + 2 := by
            have h1 := Finset.card_union_le (J.erase (n + t))
              ((C.gates[t]).inputs.toFinset.filter (fun i => i < n + t))
            have h2 := Finset.card_filter_le (C.gates[t]).inputs.toFinset (fun i => i < n + t)
            have h3 := List.toFinset_card_le (C.gates[t]).inputs
            omega
          refine ⟨insert t D, A, B, ?_, hA, ?_, ?_⟩
          · intro t' ht'
            rw [Finset.mem_insert] at ht'
            rcases ht' with rfl | ht'
            · exact ⟨by omega, ht, hsub, hpriv⟩
            · exact ⟨by have := (hD t' ht').1; omega, (hD t' ht').2⟩
          · rw [Finset.card_insert_of_notMem htD]
            omega
          · intro j hj p hpS hpB
            by_cases hjN : j = n + t
            · subst hjN
              apply gate_lift C n _ _ t ht hop
              intro a ha
              split_ifs with hlt
              · intro hw
                refine hp a ?_ p hpS hpB hw
                rw [Finset.mem_union]
                right
                rw [Finset.mem_filter]
                exact ⟨List.mem_toFinset.mpr ha, hlt⟩
              · exact id
            · refine hp j ?_ p hpS hpB
              rw [Finset.mem_union]
              left
              rw [Finset.mem_erase]
              exact ⟨hjN, hj⟩
        · obtain ⟨D, A, B, hD, hA, hc, hp⟩ := ih _ hJ0
          have hL1 : (Ls C n y N).card ≤ 1 := by omega
          refine ⟨D, A, B ∪ Ls C n y N, ?_, hA, ?_, ?_⟩
          · intro t' ht'
            exact ⟨by have := (hD t' ht').1; omega, (hD t' ht').2⟩
          · have := Finset.card_union_le B (Ls C n y N)
            omega
          · intro j hj p hpS hpB
            rw [Finset.mem_union, not_or] at hpB
            by_cases hjN : j = N
            · subst hjN
              intro hw
              exact absurd ((mem_Ls C n y j p).2 hw) hpB.2
            · refine hp j ?_ p hpS hpB.1
              rw [Finset.mem_erase]
              exact ⟨hjN, hj⟩
      · unfold below at hsub
        push_neg at hsub
        obtain ⟨x, hxN, hxS⟩ := hsub
        obtain ⟨D, A, B, hD, hA, hc, hp⟩ := ih _ hJ0
        have hmono : ∀ j, Wv C n (ind n (A ∪ y)) j = true →
            Wv C n (ind n ((A ∪ Finset.univ.filter (fun q => x q = true)) ∪ y)) j = true := by
          apply Wv_mono C n hg
          intro r hr
          simp only [ind, decide_eq_true_eq, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          tauto
        refine ⟨D, A ∪ Finset.univ.filter (fun q => x q = true), B, ?_, ?_, ?_, ?_⟩
        · intro t' ht'
          exact ⟨by have := (hD t' ht').1; omega, (hD t' ht').2⟩
        · intro r hr
          rw [Finset.mem_union] at hr
          rcases hr with hr | hr
          · exact hA r hr
          · intro hrS
            exact hxS r hrS (Finset.mem_filter.mp hr).2
        · omega
        · intro j hj p hpS hpB
          by_cases hjN : j = N
          · subst hjN
            intro _
            apply Wv_mono C n hg x _ ?_ j hxN
            intro r hr
            simp only [ind, decide_eq_true_eq, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            tauto
          · intro hw
            apply hmono
            refine hp j ?_ p hpS hpB hw
            rw [Finset.mem_erase]
            exact ⟨hjN, hj⟩
    · obtain ⟨D, A, B, hD, hA, hc, hp⟩ := ih J (by
        intro j hj
        have := hJ j hj
        have hne : j ≠ N := fun h => hN (h ▸ hj)
        omega)
      refine ⟨D, A, B, ?_, hA, hc, hp⟩
      intro t' ht'
      exact ⟨by have := (hD t' ht').1; omega, (hD t' ht').2⟩

theorem per (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S y : Finset (Fin n)) (hy : Disjoint y S) (o : ℕ)
    (h4 : below C n S o)
    (h5 : ∀ p ∈ S, Wv C n (ind n (insert p y)) o = true) :
    ∃ D : Finset ℕ, (∀ t ∈ D, t < C.gates.length ∧ below C n S (n + t) ∧
          2 ≤ (Ls C n y (n + t)).card) ∧ S.card ≤ D.card + 1 := by
  obtain ⟨D, A, B, hD, hA, hc, hp⟩ := inv C n hg S y hy (o + 1) {o} (by simp)
  refine ⟨D, fun t ht => (hD t ht).2, ?_⟩
  rw [Finset.card_singleton] at hc
  have hfalse : ¬ Wv C n (ind n (A ∪ y)) o = true := by
    intro htrue
    obtain ⟨p, hpS, hpx⟩ := h4 _ htrue
    simp only [ind, decide_eq_true_eq, Finset.mem_union] at hpx
    rcases hpx with hpx | hpx
    · exact hA p hpx hpS
    · exact Finset.disjoint_left.mp hy hpx hpS
  have hSB : S ⊆ B := by
    intro p hpS
    by_contra hpB
    exact hfalse (hp o (Finset.mem_singleton_self _) p hpS hpB (h5 p hpS))
  have h3 := Finset.card_le_card hSB
  omega

theorem share (C : Circuit) (n : ℕ) (S1 S2 y1 : Finset (Fin n)) (j : ℕ)
    (hint : (S1 ∩ S2).card ≤ 1)
    (hb1 : below C n S1 j) (hb2 : below C n S2 j) (h2 : 2 ≤ (Ls C n y1 j).card)
    (hy1 : Disjoint y1 S1) : ¬ Disjoint y1 S2 := by
  intro hd
  have hsub : Ls C n y1 j ⊆ S1 ∩ S2 := by
    intro p hp
    rw [mem_Ls] at hp
    rw [Finset.mem_inter]
    constructor
    · obtain ⟨r, hrS, hr⟩ := hb1 _ hp
      simp only [ind, decide_eq_true_eq, Finset.mem_insert] at hr
      rcases hr with hr | hr
      · exact hr ▸ hrS
      · exact absurd hrS (Finset.disjoint_left.mp hy1 hr)
    · obtain ⟨r, hrS, hr⟩ := hb2 _ hp
      simp only [ind, decide_eq_true_eq, Finset.mem_insert] at hr
      rcases hr with hr | hr
      · exact hr ▸ hrS
      · exact absurd hrS (Finset.disjoint_left.mp hd hr)
  have := Finset.card_le_card hsub
  omega

theorem main : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  intro n m D S y C o hint hdis hg h4 h5 hD
  classical
  have hper : ∀ i : Fin m, (S i).card ≤ ((Finset.range C.gates.length).filter (fun t =>
      PEqualNP.Outside.L_meta_991.below C n (S i) (n + t) ∧
        2 ≤ (PEqualNP.Outside.L_meta_991.Ls C n (y i) (n + t)).card)).card + 1 := by
    intro i
    obtain ⟨E, hE, hcard⟩ := PEqualNP.Outside.L_meta_991.per C n hg (S i) (y i) (hdis i) (o i)
      (fun x hx => h4 i x hx)
      (fun p hp => by
        have hfun : PEqualNP.Outside.L_meta_991.ind n (insert p (y i)) =
            (fun v : Fin n => decide (v ∈ y i ∨ v = p)) := by
          funext v
          simp [PEqualNP.Outside.L_meta_991.ind, or_comm]
        rw [hfun]
        exact h5 i p hp)
    have hsub : E ⊆ (Finset.range C.gates.length).filter (fun t =>
      PEqualNP.Outside.L_meta_991.below C n (S i) (n + t) ∧
        2 ≤ (PEqualNP.Outside.L_meta_991.Ls C n (y i) (n + t)).card) := by
      intro t ht
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨(hE t ht).1, (hE t ht).2⟩
    have := Finset.card_le_card hsub
    omega
  have hcol : ∀ t : ℕ, (Finset.univ.filter (fun i : Fin m =>
      PEqualNP.Outside.L_meta_991.below C n (S i) (n + t) ∧
        2 ≤ (PEqualNP.Outside.L_meta_991.Ls C n (y i) (n + t)).card)).card ≤ D := by
    intro t
    apply hD
    intro i hi j hj hij
    rw [Finset.mem_filter] at hi hj
    exact PEqualNP.Outside.L_meta_991.share C n (S i) (S j) (y i) (n + t) (hint i j hij)
      hi.2.1 hj.2.1 hi.2.2 (hdis i)
  calc ∑ i : Fin m, (S i).card
      ≤ ∑ i : Fin m, (((Finset.range C.gates.length).filter (fun t =>
          PEqualNP.Outside.L_meta_991.below C n (S i) (n + t) ∧
          2 ≤ (PEqualNP.Outside.L_meta_991.Ls C n (y i) (n + t)).card)).card + 1) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = (∑ t ∈ Finset.range C.gates.length, (Finset.univ.filter (fun i : Fin m =>
          PEqualNP.Outside.L_meta_991.below C n (S i) (n + t) ∧
          2 ≤ (PEqualNP.Outside.L_meta_991.Ls C n (y i) (n + t)).card)).card) + m := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.card_filter, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        rw [Finset.sum_comm]
    _ ≤ D * C.gates.length + m := by
        have := Finset.sum_le_card_nsmul (Finset.range C.gates.length) _ D (fun t _ => hcol t)
        rw [Finset.card_range, smul_eq_mul, Nat.mul_comm] at this
        omega

end PEqualNP.Outside.L_meta_991

theorem PEqualNP.Outside.L_meta_991 : ¬ (∃ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧ (∀ i : Fin m, Disjoint (y i) (S i)) ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) ∧ (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) ∧ (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) ∧ D * C.gates.length + m < ∑ i : Fin m, (S i).card) := by
  rintro ⟨n, m, D, S, y, C, o, h1, h2, h3, h4, h5, h6, h7⟩
  have := PEqualNP.Outside.L_meta_991.main n m D S y C o h1 h2 h3 h4 h5 h6
  omega

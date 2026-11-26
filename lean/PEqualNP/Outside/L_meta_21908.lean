import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21908
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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

theorem cone (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (R : Finset ℕ) :
    ∃ R' : Finset ℕ, R'.card ≤ R.card + gs.length ∧ ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ R', x.getD i false = y.getD i false) →
      ∀ w ∈ R, (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => exact ⟨R, by simp, fun x y _ _ h => by simpa using h⟩
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have h2 : g.inputs.length ≤ 2 := hg g (by simp)
    let t := N + gs.length
    let R0 := if t ∈ R then R.erase t ∪ g.inputs.toFinset else R
    obtain ⟨R', hc, hR'⟩ := ih hg' R0
    refine ⟨R', ?_, ?_⟩
    · have : R0.card ≤ R.card + 1 := by
        simp only [R0]; split_ifs with ht
        · have := Finset.card_union_le (R.erase t) g.inputs.toFinset
          have := Finset.card_erase_of_mem ht
          have := List.toFinset_card_le g.inputs
          have : 0 < R.card := Finset.card_pos.2 ⟨t, ht⟩
          omega
        · omega
      simp; omega
    · intro x y hx hy hxy w hw
      have e := hR' x y hx hy hxy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
      rw [getD_snoc, getD_snoc, len, len, hx, hy]
      split_ifs with h1 h3
      · exact e w (by simp only [R0]; split_ifs <;> simp_all; omega)
      · have ht : t ∈ R := by simp only [t]; rw [← h3]; exact hw
        congr 1
        refine List.map_congr_left fun i hi => e i ?_
        simp [R0, ht, hi]
      · rfl

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega


theorem e_setD (x : List Bool) (k : ℕ) : ∀ i, (x.set k false).getD i false =
    if i = k then false else x.getD i false := by
  intro i
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases h : k = i
  · subst h; simp only [ite_true]; split_ifs <;> rfl
  · simp [h, Ne.symm h]

theorem mono (gs : List Gate) (hM : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (x y : List Bool)
    (hl : x.length = y.length) (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (gs.foldl stp x).getD i false = true → (gs.foldl stp y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h' => hM g' (by simp [h']))
    intro i
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [getD_snoc, getD_snoc, len, len, hl]
    split_ifs with h1 h3
    · exact ih' i
    · rcases hM g (by simp) with hop | hop
      · rw [hop]
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
        rintro hh b ⟨w, hw, rfl⟩
        exact ih' w (hh _ ⟨w, hw, rfl⟩)
      · rw [hop]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
        rintro ⟨b, ⟨w, hw, rfl⟩, hh⟩
        exact ⟨_, ⟨w, hw, rfl⟩, ih' w hh⟩
    · exact fun hh => hh

theorem cone_main : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool), PEqualNP.Represents.RepSizeAtMost A s → (Finset.univ.filter (fun u : Fin n => ∃ u' : Fin n, ∃ v : Fin m, A u v = true ∧ A u' v = false)).card + (Finset.univ.filter (fun v : Fin m => ∃ v' : Fin m, ∃ u : Fin n, A u v = true ∧ A u v' = false)).card ≤ s + 1 := by
  intro n m s A hrep
  obtain ⟨C, hM, hs, hR⟩ := hrep
  obtain ⟨R', hc, hR'⟩ := cone (n + m) C.gates (fun g hg => (hM g hg).2) {C.output}
  rw [Finset.card_singleton] at hc
  have hMM : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hM g hg).1
    simpa using this
  have hlen : ∀ (u : Fin n) (v : Fin m), (oneEach u v).length = n + m := by
    intro u v; simp [oneEach]
  have hev : ∀ (u : Fin n) (v : Fin m),
      (C.gates.foldl stp (oneEach u v)).getD C.output false = A u v := fun u v => hR u v
  have hrow : ∀ u u' : Fin n, ∀ v : Fin m, A u v = true → A u' v = false → u.val ∈ R' := by
    intro u u' v h1 h2
    by_contra hu
    have e1 := hR' (oneEach u v) ((oneEach u v).set u.val false) (hlen u v) (by simp [hlen u v]) (by
      intro i hi
      rw [e_setD]
      have : i ≠ u.val := fun h => hu (h ▸ hi)
      simp [this]) C.output (Finset.mem_singleton_self _)
    rw [hev u v, h1] at e1
    have e2 := mono C.gates hMM ((oneEach u v).set u.val false) (oneEach u' v) (by simp [hlen]) (by
      intro i
      rw [e_setD]
      split_ifs with hi
      · intro h; exact absurd h (by simp)
      · rw [oe, oe]
        rintro (h | h)
        · exact absurd h hi
        · exact Or.inr h) C.output e1.symm
    rw [hev u' v, h2] at e2
    exact absurd e2 (by simp)
  have hcol : ∀ v v' : Fin m, ∀ u : Fin n, A u v = true → A u v' = false → n + v.val ∈ R' := by
    intro v v' u h1 h2
    by_contra hv
    have e1 := hR' (oneEach u v) ((oneEach u v).set (n + v.val) false) (hlen u v) (by simp [hlen u v]) (by
      intro i hi
      rw [e_setD]
      have : i ≠ n + v.val := fun h => hv (h ▸ hi)
      simp [this]) C.output (Finset.mem_singleton_self _)
    rw [hev u v, h1] at e1
    have e2 := mono C.gates hMM ((oneEach u v).set (n + v.val) false) (oneEach u v') (by simp [hlen]) (by
      intro i
      rw [e_setD]
      split_ifs with hi
      · intro h; exact absurd h (by simp)
      · rw [oe, oe]
        rintro (h | h)
        · exact Or.inl h
        · exact absurd h hi) C.output e1.symm
    rw [hev u v', h2] at e2
    exact absurd e2 (by simp)
  have h2 : (Finset.univ.filter (fun u : Fin n => ∃ u' : Fin n, ∃ v : Fin m, A u v = true ∧ A u' v = false)).card ≤
      (R'.filter (fun w => w < n)).card := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    apply Finset.card_le_card
    intro w hw
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨u, ⟨u', v, ha, hb⟩, rfl⟩ := hw
    exact ⟨hrow u u' v ha hb, u.isLt⟩
  have h5 : (Finset.univ.filter (fun v : Fin m => ∃ v' : Fin m, ∃ u : Fin n, A u v = true ∧ A u v' = false)).card ≤
      (R'.filter (fun w => ¬ w < n)).card := by
    rw [← Finset.card_image_of_injective _
      (fun (a b : Fin m) (h : n + a.val = n + b.val) => Fin.ext (Nat.add_left_cancel h))]
    apply Finset.card_le_card
    intro w hw
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨v, ⟨v', u, ha, hb⟩, rfl⟩ := hw
    exact ⟨hcol v v' u ha hb, by omega⟩
  have h3 := Finset.card_filter_add_card_filter_not (s := R') (fun w => w < n)
  simp only [Circuit.size] at hs
  omega

theorem lb (n s : ℕ) (A : Fin n → Fin n → Bool) (a b : ℕ)
    (hrep : PEqualNP.Represents.RepSizeAtMost A s)
    (ha : (Finset.univ.filter (fun u : Fin n => ¬ ∃ u' : Fin n, ∃ v : Fin n, A u v = true ∧ A u' v = false)).card ≤ a)
    (hb : (Finset.univ.filter (fun v : Fin n => ¬ ∃ v' : Fin n, ∃ u : Fin n, A u v = true ∧ A u v' = false)).card ≤ b) :
    2 * n ≤ s + 1 + a + b := by
  have h := cone_main n n s A hrep
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun u : Fin n => ∃ u' : Fin n, ∃ v : Fin n, A u v = true ∧ A u' v = false)
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun v : Fin n => ∃ v' : Fin n, ∃ u : Fin n, A u v = true ∧ A u v' = false)
  rw [Finset.card_univ, Fintype.card_fin] at h1 h2
  omega

theorem main : ∀ n k a b : ℕ, k = 3 → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a → (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤ (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b → ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) s → 2 * n + k - 4 - a - b ≤ s := by
  intro n k a b hk t ht _ _ hA hB s hrep
  have h := lb n s (fun u v => decide ((v : ℕ) < t u)) a b hrep ?_ ?_
  · omega
  · rw [← hA]
    apply Finset.card_le_card
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨hu.1, ?_⟩
    intro u'
    by_contra hlt
    apply hu.2
    have hlt' : t u' < t u := by omega
    have hle := (ht u).2
    exact ⟨u', ⟨t u', by omega⟩, by simp [hlt'], by simp⟩
  · rw [← hB]
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨hv.1, ?_⟩
    intro v'
    apply Finset.card_le_card
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨hu.1, ?_⟩
    by_contra hn
    exact hv.2 ⟨v', u, by simp [hu.2], by simp [hn]⟩

end PEqualNP.Outside.L_meta_21908

theorem PEqualNP.Outside.L_meta_21908 : ∀ n k a b : ℕ, k = 3 → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a → (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤ (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b → ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) s → 2 * n + k - 4 - a - b ≤ s :=
  PEqualNP.Outside.L_meta_21908.main

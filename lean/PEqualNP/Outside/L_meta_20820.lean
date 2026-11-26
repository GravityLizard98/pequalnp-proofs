import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20820

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem memf {p : ℕ → Prop} (d : DecidablePred p) (s : Finset ℕ) (a : ℕ) :
    a ∈ @Finset.filter ℕ p d s ↔ a ∈ s ∧ p a := Finset.mem_filter

theorem countP_or (f g h : ℕ → Bool) (hh : ∀ x, h x = (f x || g x))
    (hd : ∀ x, ¬ (f x = true ∧ g x = true)) (l : List ℕ) :
    l.countP h = l.countP f + l.countP g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih, hh a]
    have := hd a
    cases hf : f a <;> cases hg : g a <;> simp [hf, hg] at this ⊢ <;> omega

theorem countP_sum (m : ℕ) (G : Finset ℕ) (p : ℕ → Bool)
    (hp : ∀ v, p v = true ↔ ∃ g ∈ G, v = m + g) (l : List ℕ) :
    l.countP p = ∑ g ∈ G, l.count (m + g) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, ih]
    simp only [List.count_cons]
    rw [Finset.sum_add_distrib]
    congr 1
    by_cases h : p a = true
    · obtain ⟨g, hg, rfl⟩ := (hp a).mp h
      rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      rw [Finset.sum_eq_single_of_mem g hg]
      · simp
      · intro b _ hb
        have : ¬ (m + g = m + b) := by omega
        simp [Ne.symm hb]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have : ¬ (a = m + b) := fun e => h ((hp a).mpr ⟨b, hb, e⟩)
      simp [this]

theorem core (m n : ℕ) (inp : ℕ → List ℕ) (sp sk : ℕ → Prop)
    (hrange : ∀ w, sk w → m ≤ w ∧ w < m + n)
    (hdisj : ∀ w, ¬ (sp w ∧ sk w))
    (hR : ∀ h < n, sk (m + h) → ∑ g ∈ Finset.range n, (inp g).count (m + h) ≤ 1)
    (hF2 : ∀ g < n, sk (m + g) → ∃ w ∈ inp g, sp w ∨ sk w) :
    (@Finset.filter ℕ (fun g => (sk (m + g) ∧ (inp g).countP (fun i => @decide (sp i ∨ sk i) (Classical.propDecidable _)) = 1) ∧
        ¬ ∃ g', g' < n ∧ (sk (m + g') ∧ (inp g').countP (fun i => @decide (sp i ∨ sk i) (Classical.propDecidable _)) = 1) ∧ m + g ∈ inp g')
        (fun _ => Classical.propDecidable _) (Finset.range n)).card ≤
    2 * ∑ g ∈ @Finset.filter ℕ (fun g => sk (m + g)) (fun _ => Classical.propDecidable _) (Finset.range n),
      (inp g).countP (fun i => @decide (sp i) (Classical.propDecidable _)) := by
  classical
  let GS : Finset ℕ := @Finset.filter ℕ (fun g => sk (m + g)) (fun _ => Classical.propDecidable _) (Finset.range n)
  let K : ℕ → ℕ := fun g => (inp g).countP (fun i => @decide (sk i) (Classical.propDecidable _))
  let S : ℕ → ℕ := fun g => (inp g).countP (fun i => @decide (sp i) (Classical.propDecidable _))
  let ch : ℕ → Prop := fun g => sk (m + g) ∧ (inp g).countP (fun i => @decide (sp i ∨ sk i) (Classical.propDecidable _)) = 1
  let rb : ℕ → Prop := fun g => ∃ g', g' < n ∧ ch g' ∧ m + g ∈ inp g'
  have hGS : ∀ g, g ∈ GS ↔ g < n ∧ sk (m + g) := by
    intro g
    show g ∈ Finset.filter _ _ ↔ _
    rw [memf, Finset.mem_range]
  have hKS : ∀ g, (inp g).countP (fun i => @decide (sp i ∨ sk i) (Classical.propDecidable _)) = S g + K g := by
    intro g
    exact countP_or _ _ _ (fun x => by simp)
      (fun x hx => hdisj x ⟨of_decide_eq_true hx.1, of_decide_eq_true hx.2⟩) (inp g)
  have hKsum : ∀ g, K g = ∑ h ∈ GS, (inp g).count (m + h) := by
    intro g
    refine countP_sum m GS _ (fun v => ?_) (inp g)
    rw [decide_eq_true_iff]
    constructor
    · intro hv
      obtain ⟨h1, h2⟩ := hrange v hv
      refine ⟨v - m, (hGS _).mpr ⟨by omega, ?_⟩, by omega⟩
      rwa [Nat.add_sub_cancel' h1]
    · rintro ⟨h, hh, rfl⟩
      exact ((hGS h).mp hh).2
  have hR' : ∀ h ∈ GS, ∑ g ∈ GS, (inp g).count (m + h) ≤ 1 := by
    intro h hh
    obtain ⟨h1, h2⟩ := (hGS h).mp hh
    exact le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (hR h h1 h2)
  have F1 : ∑ g ∈ GS, K g ≤ GS.card := by
    calc ∑ g ∈ GS, K g = ∑ g ∈ GS, ∑ h ∈ GS, (inp g).count (m + h) :=
          Finset.sum_congr rfl (fun g _ => hKsum g)
      _ = ∑ h ∈ GS, ∑ g ∈ GS, (inp g).count (m + h) := Finset.sum_comm
      _ ≤ ∑ h ∈ GS, 1 := Finset.sum_le_sum hR'
      _ = GS.card := by simp
  have F4 : ∑ g ∈ GS.filter ch, K g ≤ (GS.filter rb).card := by
    calc ∑ g ∈ GS.filter ch, K g = ∑ g ∈ GS.filter ch, ∑ h ∈ GS, (inp g).count (m + h) :=
          Finset.sum_congr rfl (fun g _ => hKsum g)
      _ = ∑ h ∈ GS, ∑ g ∈ GS.filter ch, (inp g).count (m + h) := Finset.sum_comm
      _ ≤ ∑ h ∈ GS, (if rb h then 1 else 0) := by
        apply Finset.sum_le_sum
        intro h hh
        split_ifs with hrb
        · exact le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (hR' h hh)
        · apply le_of_eq
          apply Finset.sum_eq_zero
          intro g hg
          rw [memf] at hg
          rw [List.count_eq_zero]
          intro hmem
          exact hrb ⟨g, ((hGS g).mp hg.1).1, hg.2, hmem⟩
      _ = (GS.filter rb).card := by rw [Finset.card_filter]
  have Fnode : ∀ g ∈ GS, 2 ≤ 2 * S g + (if ch g then K g else 0) + K g := by
    intro g hg
    obtain ⟨h1, h2⟩ := (hGS g).mp hg
    obtain ⟨w, hw, hp⟩ := hF2 g h1 h2
    have hpos : 0 < (inp g).countP (fun i => @decide (sp i ∨ sk i) (Classical.propDecidable _)) :=
      List.countP_pos_iff.mpr ⟨w, hw, @decide_eq_true _ (Classical.propDecidable _) hp⟩
    have hks := hKS g
    split_ifs with hc
    · have hc' : (inp g).countP (fun i => @decide (sp i ∨ sk i) (Classical.propDecidable _)) = 1 := hc.2
      omega
    · have hc' : (inp g).countP (fun i => @decide (sp i ∨ sk i) (Classical.propDecidable _)) ≠ 1 :=
        fun e => hc ⟨h2, e⟩
      omega
  have Fsum : 2 * GS.card ≤ 2 * ∑ g ∈ GS, S g + ∑ g ∈ GS.filter ch, K g + ∑ g ∈ GS, K g := by
    have e1 : ∑ g ∈ GS.filter ch, K g = ∑ g ∈ GS, (if ch g then K g else 0) := Finset.sum_filter _ _
    have e2 := Finset.sum_le_sum Fnode
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      smul_eq_mul] at e2
    omega
  have e := Finset.card_filter_add_card_filter_not (s := GS) rb
  refine le_trans (Finset.card_le_card (t := GS.filter (fun g => ¬ rb g)) ?_) ?_
  · intro g hg
    rw [memf, Finset.mem_range] at hg
    rw [memf]
    exact ⟨(hGS g).mpr ⟨hg.1, hg.2.1.1⟩, hg.2.2⟩
  · show _ ≤ 2 * ∑ g ∈ GS, S g
    omega

theorem one_read (C : Circuit) (n : ℕ) (w g1 : ℕ) (h1 : g1 < n)
    (m1 : w ∈ (gateAt C g1).inputs) : 1 ≤ readsIn C (Finset.range n) w := by
  unfold readsIn
  have := Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count w)
    (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr h1)
  have a1 := List.count_pos_iff.mpr m1
  omega

theorem two_reads (C : Circuit) (n : ℕ) (w g1 g2 : ℕ) (h1 : g1 < n) (h2 : g2 < n) (hne : g1 ≠ g2)
    (m1 : w ∈ (gateAt C g1).inputs) (m2 : w ∈ (gateAt C g2).inputs) :
    2 ≤ readsIn C (Finset.range n) w := by
  unfold readsIn
  have hs : ({g1, g2} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr ‹_›
  have := Finset.sum_le_sum_of_subset (f := fun j => (gateAt C j).inputs.count w) hs
  rw [Finset.sum_pair hne] at this
  have a1 := List.count_pos_iff.mpr m1
  have a2 := List.count_pos_iff.mpr m2
  omega

theorem main : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size → C.output + 1 = m + C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
let R : ℕ → ℕ := fun w => PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w
let special : ℕ → Prop := fun w => (w < m ∧ 2 ≤ R w) ∨
  (m ≤ w ∧ w < m + C.size ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).op = PEqualNP.CircuitLowerBounds.GateOp.not ∨ 2 ≤ R w))
let ordinary : ℕ → Prop := fun w => (w < m ∧ R w = 1) ∨
  (m ≤ w ∧ w < m + C.size ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ R w ≤ 1)
let feeds : ℕ → ℕ → Prop := fun w g => g < C.size ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs
let edge : ℕ → ℕ → Prop := fun w w' => ordinary w ∧ ordinary w' ∧ m ≤ w' ∧ feeds w (w' - m)
let root : ℕ → Prop := fun w => ordinary w ∧ (w = C.output ∨ ∃ g, feeds w g ∧ special (m + g))
let skel : ℕ → Prop := fun w => ordinary w ∧ m ≤ w ∧
  ∃ g w0, ordinary (m + g) ∧ feeds w0 g ∧ special w0 ∧ Relation.ReflTransGen edge (m + g) w
let chainGate : ℕ → Prop := fun w => skel w ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).inputs.countP
    (fun i => @decide (special i ∨ skel i) (Classical.propDecidable _)) = 1
let chainTop : ℕ → Prop := fun w => chainGate w ∧ (root w ∨ ∃ g, feeds w g ∧ ¬ chainGate (m + g))
let ext : ℕ := ∑ g ∈ @Finset.filter ℕ (fun g1 => ordinary (m + g1)) (fun d1 => Classical.propDecidable _)
    (Finset.range C.size),
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.countP
    (fun i => @decide (special i) (Classical.propDecidable _))
let Fin_ : ℕ := ∑ w ∈ Finset.range m, R w
let X : ℕ := ∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
    (Finset.range C.size), (R (m + j) - 1)
let t : ℕ := (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
    PEqualNP.CircuitLowerBounds.GateOp.not) (fun d3 => Classical.propDecidable _) (Finset.range C.size)).card
let r : ℕ := (@Finset.filter ℕ (fun w => 1 ≤ R w) (fun d4 => Classical.propDecidable _) (Finset.range m)).card
(@Finset.filter ℕ chainTop (fun d5 => Classical.propDecidable _) (Finset.range (m + C.size))).card ≤ 2 * ext := by
  intro m C _ _ _ hout hlast R special ordinary feeds edge root skel chainGate chainTop ext Fin_ X t r
  have hskm : ∀ w, skel w → m ≤ w ∧ w < m + C.size ∧
      (gateAt C (w - m)).op ≠ GateOp.not ∧ readsIn C (Finset.range C.size) w ≤ 1 := by
    intro w hw
    have hw' : ((w < m ∧ R w = 1) ∨ (m ≤ w ∧ w < m + C.size ∧
      (gateAt C (w - m)).op ≠ GateOp.not ∧ R w ≤ 1)) ∧ m ≤ w ∧ _ := hw
    obtain ⟨h, h0, _⟩ := hw'
    rcases h with h | h
    · exact absurd h.1 (by omega)
    · exact h
  have hrtg : ∀ a c, Relation.ReflTransGen edge a c → m ≤ a → m ≤ c := by
    intro a c h ha
    induction h with
    | refl => exact ha
    | tail _ hbc _ =>
      have hbc' : ordinary _ ∧ ordinary _ ∧ m ≤ _ ∧ _ := hbc
      exact hbc'.2.2.1
  have hF2 : ∀ g < C.size, skel (m + g) → ∃ w ∈ (gateAt C g).inputs, special w ∨ skel w := by
    intro g hg hs
    have hs' : ordinary (m + g) ∧ m ≤ m + g ∧ ∃ g0 w0, ordinary (m + g0) ∧ feeds w0 g0 ∧
      special w0 ∧ Relation.ReflTransGen edge (m + g0) (m + g) := hs
    obtain ⟨_, _, g0, w0, ho, hf, hsp, hr⟩ := hs'
    rcases Relation.ReflTransGen.cases_tail hr with he | ⟨c, hc, hedge⟩
    · have hgg : g = g0 := by omega
      subst hgg
      have hf' : g < C.size ∧ w0 ∈ (gateAt C g).inputs := hf
      exact ⟨w0, hf'.2, Or.inl hsp⟩
    · have he' : ordinary c ∧ ordinary (m + g) ∧ m ≤ m + g ∧
        (m + g - m < C.size ∧ c ∈ (gateAt C (m + g - m)).inputs) := hedge
      rw [Nat.add_sub_cancel_left] at he'
      refine ⟨c, he'.2.2.2.2, Or.inr ?_⟩
      show ordinary c ∧ m ≤ c ∧ ∃ g0 w0, ordinary (m + g0) ∧ feeds w0 g0 ∧ special w0 ∧
        Relation.ReflTransGen edge (m + g0) c
      exact ⟨he'.1, hrtg _ _ hc (Nat.le_add_right _ _), g0, w0, ho, hf, hsp, hc⟩
  have hspo : ∀ w, special w → m ≤ w → (gateAt C (w - m)).op ≠ GateOp.not →
      readsIn C (Finset.range C.size) w ≤ 1 → False := by
    intro w hs k1 k3 k4
    have hs' : (w < m ∧ 2 ≤ readsIn C (Finset.range C.size) w) ∨ (m ≤ w ∧ w < m + C.size ∧
      ((gateAt C (w - m)).op = GateOp.not ∨ 2 ≤ readsIn C (Finset.range C.size) w)) := hs
    rcases hs' with h | ⟨_, _, h | h⟩
    · omega
    · exact k3 h
    · omega
  have hdisj : ∀ w, ¬ (special w ∧ skel w) := by
    rintro w ⟨hs, hk⟩
    obtain ⟨k1, k2, k3, k4⟩ := hskm w hk
    exact hspo w hs k1 k3 k4
  have hc := core m C.size (fun g => (gateAt C g).inputs) special skel
    (fun w hw => ⟨(hskm w hw).1, (hskm w hw).2.1⟩) hdisj
    (fun h _ hs => (hskm (m + h) hs).2.2.2) hF2
  refine le_trans (Finset.card_le_card_of_injOn (fun w => w - m) ?_ ?_) (le_trans hc ?_)
  · intro w hw
    rw [Finset.mem_coe, memf] at hw
    obtain ⟨_, hct⟩ := hw
    have hct' : chainGate w ∧ (root w ∨ ∃ g, feeds w g ∧ ¬ chainGate (m + g)) := hct
    obtain ⟨hcg, htop⟩ := hct'
    have hcg' : skel w ∧ (gateAt C (w - m)).inputs.countP
      (fun i => @decide (special i ∨ skel i) (Classical.propDecidable _)) = 1 := hcg
    obtain ⟨k1, k2, k3, k4⟩ := hskm w hcg'.1
    obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le k1
    rw [Nat.add_sub_cancel_left] at hcg'
    show m + g - m ∈ _
    rw [Nat.add_sub_cancel_left, Finset.mem_coe, memf, Finset.mem_range]
    refine ⟨by omega, hcg', ?_⟩
    rintro ⟨g', hg', hch', hmem⟩
    obtain ⟨j1, j2, j3, j4⟩ := hskm (m + g') hch'.1
    rw [Nat.add_sub_cancel_left] at j3
    have key : ∀ g2, g2 < C.size → m + g ∈ (gateAt C g2).inputs → g2 = g' := by
      intro g2 h2 hm2
      by_contra hne
      have := two_reads C C.size (m + g) g2 g' h2 hg' hne hm2 hmem
      omega
    rcases htop with hr | ⟨g2, hf2, hn2⟩
    · have hr' : ordinary (m + g) ∧ (m + g = C.output ∨ ∃ g3, feeds (m + g) g3 ∧ special (m + g3)) := hr
      rcases hr'.2 with ho | ⟨g3, hf3, hs3⟩
      · have h0 := (hlast g (by omega)).mpr (by omega)
        have h1 := one_read C C.size (m + g) g' hg' hmem
        omega
      · have hf3' : g3 < C.size ∧ (m + g) ∈ (gateAt C g3).inputs := hf3
        have hgg := key g3 hf3'.1 hf3'.2
        subst hgg
        exact hspo (m + g3) hs3 j1 (by rw [Nat.add_sub_cancel_left]; exact j3) j4
    · have hf2' : g2 < C.size ∧ m + g ∈ (gateAt C g2).inputs := hf2
      have hgg := key g2 hf2'.1 hf2'.2
      subst hgg
      apply hn2
      show skel (m + g2) ∧ (gateAt C (m + g2 - m)).inputs.countP
        (fun i => @decide (special i ∨ skel i) (Classical.propDecidable _)) = 1
      rw [Nat.add_sub_cancel_left]
      exact hch'
  · intro a ha b hb hab
    have ha' : chainGate a ∧ _ := ((memf _ _ _).mp (Finset.mem_coe.mp ha)).2
    have hb' : chainGate b ∧ _ := ((memf _ _ _).mp (Finset.mem_coe.mp hb)).2
    have ha2 : skel a ∧ _ := ha'.1
    have hb2 : skel b ∧ _ := hb'.1
    have ha3 := (hskm a ha2.1).1
    have hb3 := (hskm b hb2.1).1
    have hab' : a - m = b - m := hab
    omega
  · show _ ≤ 2 * ∑ g ∈ @Finset.filter ℕ (fun g1 => ordinary (m + g1)) (fun _ => Classical.propDecidable _)
        (Finset.range C.size),
      (gateAt C g).inputs.countP (fun i => @decide (special i) (Classical.propDecidable _))
    apply Nat.mul_le_mul_left
    apply Finset.sum_le_sum_of_subset
    intro g hg
    rw [memf] at hg ⊢
    have h' : ordinary (m + g) ∧ _ := hg.2
    exact ⟨hg.1, h'.1⟩

end PEqualNP.Outside.L_meta_20820

theorem PEqualNP.Outside.L_meta_20820 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size → C.output + 1 = m + C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
let R : ℕ → ℕ := fun w => PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w
let special : ℕ → Prop := fun w => (w < m ∧ 2 ≤ R w) ∨
  (m ≤ w ∧ w < m + C.size ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).op = PEqualNP.CircuitLowerBounds.GateOp.not ∨ 2 ≤ R w))
let ordinary : ℕ → Prop := fun w => (w < m ∧ R w = 1) ∨
  (m ≤ w ∧ w < m + C.size ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ R w ≤ 1)
let feeds : ℕ → ℕ → Prop := fun w g => g < C.size ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs
let edge : ℕ → ℕ → Prop := fun w w' => ordinary w ∧ ordinary w' ∧ m ≤ w' ∧ feeds w (w' - m)
let root : ℕ → Prop := fun w => ordinary w ∧ (w = C.output ∨ ∃ g, feeds w g ∧ special (m + g))
let skel : ℕ → Prop := fun w => ordinary w ∧ m ≤ w ∧
  ∃ g w0, ordinary (m + g) ∧ feeds w0 g ∧ special w0 ∧ Relation.ReflTransGen edge (m + g) w
let chainGate : ℕ → Prop := fun w => skel w ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).inputs.countP
    (fun i => @decide (special i ∨ skel i) (Classical.propDecidable _)) = 1
let chainTop : ℕ → Prop := fun w => chainGate w ∧ (root w ∨ ∃ g, feeds w g ∧ ¬ chainGate (m + g))
let ext : ℕ := ∑ g ∈ @Finset.filter ℕ (fun g1 => ordinary (m + g1)) (fun d1 => Classical.propDecidable _)
    (Finset.range C.size),
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.countP
    (fun i => @decide (special i) (Classical.propDecidable _))
let Fin_ : ℕ := ∑ w ∈ Finset.range m, R w
let X : ℕ := ∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
    (Finset.range C.size), (R (m + j) - 1)
let t : ℕ := (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
    PEqualNP.CircuitLowerBounds.GateOp.not) (fun d3 => Classical.propDecidable _) (Finset.range C.size)).card
let r : ℕ := (@Finset.filter ℕ (fun w => 1 ≤ R w) (fun d4 => Classical.propDecidable _) (Finset.range m)).card
(@Finset.filter ℕ chainTop (fun d5 => Classical.propDecidable _) (Finset.range (m + C.size))).card ≤ 2 * ext :=
  PEqualNP.Outside.L_meta_20820.main

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25449

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rho (N N' : ℕ) (f : Fin N → Fin N') (w : ℕ) : ℕ :=
  if h : w < N then (f ⟨w, h⟩).val else w - N + N'

def mg (N N' : ℕ) (f : Fin N → Fin N') (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rho N N' f)⟩

theorem stp_def (w : List Bool) (g : Gate) :
    stp w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

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

theorem rho_lt (N N' : ℕ) (f : Fin N → Fin N') (w k : ℕ) :
    rho N N' f w < N' + k ↔ w < N + k := by
  unfold rho
  split_ifs with h
  · have := (f ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · constructor <;> intro <;> omega

theorem rho_eq (N N' : ℕ) (f : Fin N → Fin N') (w k : ℕ) :
    rho N N' f w = N' + k ↔ w = N + k := by
  unfold rho
  split_ifs with h
  · have := (f ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · constructor <;> intro <;> omega

theorem rho_inj (N N' : ℕ) (f : Fin N → Fin N') (hf : Function.Injective f) :
    Function.Injective (rho N N' f) := by
  intro a b hab
  unfold rho at hab
  split_ifs at hab with ha hb hb
  · have := hf (Fin.ext hab)
    simpa using this
  · have := (f ⟨a, ha⟩).isLt
    omega
  · have := (f ⟨b, hb⟩).isLt
    omega
  · omega

theorem inv (N N' : ℕ) (f : Fin N → Fin N') (x : Fin N' → Bool) (gs : List Gate) :
    ∀ w, ((gs.map (mg N N' f)).foldl stp (List.ofFn x)).getD (rho N N' f w) false =
      (gs.foldl stp (List.ofFn (fun i => x (f i)))).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil, List.foldl_nil]
    unfold rho
    split_ifs with h
    · simp [List.getD_eq_getElem?_getD, h]
    · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega),
        List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.foldl_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [stp_def, stp_def, getD_snoc, getD_snoc]
    have e : (List.map (fun i => ((gs.map (mg N N' f)).foldl stp (List.ofFn x)).getD i false)
        (mg N N' f g).inputs) =
        List.map (fun i => (gs.foldl stp (List.ofFn (fun i => x (f i)))).getD i false) g.inputs := by
      simp only [mg, List.map_map]
      apply List.map_congr_left
      intro i _
      exact ih i
    have hop : (mg N N' f g).op = g.op := rfl
    rw [e, hop, len, len, List.length_map, List.length_ofFn, List.length_ofFn]
    by_cases h1 : w < N + gs.length
    · rw [if_pos ((rho_lt N N' f w gs.length).2 h1), if_pos h1, ih]
    · rw [if_neg (fun h => h1 ((rho_lt N N' f w gs.length).1 h)), if_neg h1]
      by_cases h2 : w = N + gs.length
      · rw [if_pos ((rho_eq N N' f w gs.length).2 h2), if_pos h2]
      · rw [if_neg (fun h => h2 ((rho_eq N N' f w gs.length).1 h)), if_neg h2]

theorem gateAt_map (N N' : ℕ) (f : Fin N → Fin N') (gs : List Gate) (o : ℕ) (j : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs.map (mg N N' f), o⟩ j =
      mg N N' f (PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, 0⟩ j) := by
  show (gs.map (mg N N' f)).getD j ⟨GateOp.or, []⟩ = mg N N' f (gs.getD j ⟨GateOp.or, []⟩)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases gs[j]? <;> rfl

theorem gateAt_out (gs : List Gate) (o : ℕ) (j : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, o⟩ j =
      PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, 0⟩ j := rfl

theorem main : ∀ (N N' : ℕ) (f : Fin N → Fin N') (C C' : PEqualNP.CircuitLowerBounds.Circuit) (ρ : ℕ → ℕ), Function.Injective f → ρ = (fun w => if h : w < N then (f ⟨w, h⟩).val else w - N + N') → C' = ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ C.output⟩ → (∀ x : Fin N' → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (f i)))) ∧ C'.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C ↔ PEqualNP.MetaComplexity.FanInTwo C') ∧ (PEqualNP.MetaComplexity.Monotone2 C ↔ PEqualNP.MetaComplexity.Monotone2 C') ∧ (PEqualNP.MetaComplexity.NestedCover.ReadsBack N C → PEqualNP.MetaComplexity.NestedCover.ReadsBack N' C') ∧ (∀ (G : Finset ℕ) (i : Fin N), PEqualNP.MetaComplexity.NestedCover.readsIn C' G (f i).val = PEqualNP.MetaComplexity.NestedCover.readsIn C G i.val) ∧ (∀ (G : Finset ℕ) (i : Fin N'), (∀ i0 : Fin N, f i0 ≠ i) → PEqualNP.MetaComplexity.NestedCover.readsIn C' G i.val = 0) ∧ (∀ (G : Finset ℕ) (j : ℕ), PEqualNP.MetaComplexity.NestedCover.readsIn C' G (N' + j) = PEqualNP.MetaComplexity.NestedCover.readsIn C G (N + j)) := by
  intro N N' f C C' ρ hf hρ hC
  have hρ' : ρ = rho N N' f := hρ
  subst hρ'
  obtain ⟨gs, o⟩ := C
  have hC' : C' = ⟨gs.map (mg N N' f), rho N N' f o⟩ := hC
  subst hC'
  have hga : ∀ j, PEqualNP.MetaComplexity.NestedCover.gateAt
      (⟨gs.map (mg N N' f), rho N N' f o⟩ : PEqualNP.CircuitLowerBounds.Circuit) j =
      mg N N' f (PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, o⟩ j) := by
    intro j
    rw [gateAt_map, gateAt_out gs o]
  have hri := rho_inj N N' f hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact inv N N' f x gs o
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp only [PEqualNP.MetaComplexity.FanInTwo, List.forall_mem_map, mg, List.length_map]
  · simp only [PEqualNP.MetaComplexity.Monotone2, List.forall_mem_map, mg, List.length_map]
  · intro hR j hj i hi
    rw [hga] at hi
    simp only [mg, List.mem_map] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    simp only [List.length_map] at hj
    have := hR j hj a ha
    exact (rho_lt N N' f a j).2 this
  · intro G i
    unfold PEqualNP.MetaComplexity.NestedCover.readsIn
    apply Finset.sum_congr rfl
    intro j _
    rw [hga]
    have : (f i).val = rho N N' f i.val := by
      unfold rho; rw [dif_pos i.isLt]
    rw [this]
    exact List.count_map_of_injective _ _ hri _
  · intro G i hi
    unfold PEqualNP.MetaComplexity.NestedCover.readsIn
    apply Finset.sum_eq_zero
    intro j _
    rw [hga]
    apply List.count_eq_zero.mpr
    simp only [mg, List.mem_map, not_exists, not_and]
    intro a _ hai
    unfold rho at hai
    split_ifs at hai with h
    · exact hi ⟨a, h⟩ (Fin.ext hai)
    · have := i.isLt
      omega
  · intro G j
    unfold PEqualNP.MetaComplexity.NestedCover.readsIn
    apply Finset.sum_congr rfl
    intro k _
    rw [hga]
    have : N' + j = rho N N' f (N + j) := by
      unfold rho; rw [dif_neg (by omega)]; omega
    rw [this]
    exact List.count_map_of_injective _ _ hri _

end PEqualNP.Outside.L_meta_25449

theorem PEqualNP.Outside.L_meta_25449 : ∀ (N N' : ℕ) (f : Fin N → Fin N') (C C' : PEqualNP.CircuitLowerBounds.Circuit) (ρ : ℕ → ℕ), Function.Injective f → ρ = (fun w => if h : w < N then (f ⟨w, h⟩).val else w - N + N') → C' = ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ C.output⟩ → (∀ x : Fin N' → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (f i)))) ∧ C'.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C ↔ PEqualNP.MetaComplexity.FanInTwo C') ∧ (PEqualNP.MetaComplexity.Monotone2 C ↔ PEqualNP.MetaComplexity.Monotone2 C') ∧ (PEqualNP.MetaComplexity.NestedCover.ReadsBack N C → PEqualNP.MetaComplexity.NestedCover.ReadsBack N' C') ∧ (∀ (G : Finset ℕ) (i : Fin N), PEqualNP.MetaComplexity.NestedCover.readsIn C' G (f i).val = PEqualNP.MetaComplexity.NestedCover.readsIn C G i.val) ∧ (∀ (G : Finset ℕ) (i : Fin N'), (∀ i0 : Fin N, f i0 ≠ i) → PEqualNP.MetaComplexity.NestedCover.readsIn C' G i.val = 0) ∧ (∀ (G : Finset ℕ) (j : ℕ), PEqualNP.MetaComplexity.NestedCover.readsIn C' G (N' + j) = PEqualNP.MetaComplexity.NestedCover.readsIn C G (N + j)) :=
  PEqualNP.Outside.L_meta_25449.main

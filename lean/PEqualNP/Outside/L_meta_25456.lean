import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25456

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ev (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def run : List Gate → List Bool → List Bool
  | [], w => w
  | g :: G, w => run G (w ++ [ev w g])

theorem run_eq (G : List Gate) (w : List Bool) :
    G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = run G w := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih => exact ih _

theorem run_append (G H : List Gate) (w : List Bool) : run (G ++ H) w = run H (run G w) := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih => exact ih _

theorem run_len (G : List Gate) (w : List Bool) : (run G w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp [run]
  | cons g G ih => simp only [run]; rw [ih]; simp; omega

theorem run_pre (G : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (run G w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    simp only [run]
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ h]

theorem gnew (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by simp

theorem gold (w : List Bool) (b : Bool) (i : ℕ) (h : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := List.getD_append _ _ _ _ h

theorem any_congr' {α : Type} (L : List α) (f g : α → Bool) (h : ∀ l ∈ L, f l = g l) :
    L.any f = L.any g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun l hl => h l (by simp [hl]))]

def RBl : ℕ → List Gate → Prop
  | _, [] => True
  | t, g :: G => (∀ i ∈ g.inputs, i < t) ∧ RBl (t + 1) G

theorem RBl_append (t : ℕ) (G H : List Gate) (h1 : RBl t G) (h2 : RBl (t + G.length) H) :
    RBl t (G ++ H) := by
  induction G generalizing t with
  | nil => simpa using h2
  | cons g G ih =>
    refine ⟨h1.1, ih (t + 1) h1.2 ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm 1] using h2

theorem RBl_get (t : ℕ) (G : List Gate) (h : RBl t G) :
    ∀ j < G.length, ∀ i ∈ (G.getD j ⟨GateOp.or, []⟩).inputs, i < t + j := by
  induction G generalizing t with
  | nil => intro j hj; simp at hj
  | cons g G ih =>
    intro j hj i hi
    cases j with
    | zero => simpa using h.1 i (by simpa using hi)
    | succ j =>
      have := ih (t + 1) h.2 j (by simp at hj; omega) i (by simpa using hi)
      omega

def MB (G : List Gate) : Prop :=
  ∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem MB_append (G H : List Gate) (h1 : MB G) (h2 : MB H) : MB (G ++ H) := by
  intro g hg
  rcases List.mem_append.1 hg with h | h
  · exact h1 g h
  · exact h2 g h

theorem MB_cons (g : Gate) (G : List Gate) (h1 : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h2 : MB G) : MB (g :: G) := by
  intro g' hg
  rcases List.mem_cons.1 hg with h | h
  · subst h; exact h1
  · exact h2 g' h

def orL (t a : ℕ) : List ℕ → List Gate
  | [] => []
  | l :: L => ⟨GateOp.or, [a, l]⟩ :: orL (t + 1) t L

def resL (t a : ℕ) : List ℕ → ℕ
  | [] => a
  | _ :: L => resL (t + 1) t L

theorem orL_len (t a : ℕ) (L : List ℕ) : (orL t a L).length = L.length := by
  induction L generalizing t a with
  | nil => rfl
  | cons l L ih => simp [orL, ih]

theorem orL_mb (t a : ℕ) (L : List ℕ) : MB (orL t a L) := by
  induction L generalizing t a with
  | nil => intro g hg; simp [orL] at hg
  | cons l L ih => exact MB_cons _ _ (by simp) (ih _ _)

theorem orL_rb (t a : ℕ) (L : List ℕ) (ha : a < t) (hL : ∀ l ∈ L, l < t) : RBl t (orL t a L) := by
  induction L generalizing t a with
  | nil => trivial
  | cons l L ih =>
    refine ⟨?_, ih (t + 1) t (by omega) (fun l' hl' => by have := hL l' (by simp [hl']); omega)⟩
    intro i hi
    simp at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hL _ (by simp)

theorem orL_key (L : List ℕ) : ∀ (t a : ℕ) (w : List Bool), w.length = t → a < t → (∀ l ∈ L, l < t) →
    resL t a L < t + L.length ∧
    (run (orL t a L) w).getD (resL t a L) false = (w.getD a false || L.any (fun l => w.getD l false)) := by
  induction L with
  | nil => intro t a w _ ha _; simp [resL, orL, run]; omega
  | cons l L ih =>
    intro t a w hw ha hL
    have hl : l < t := hL l (by simp)
    have hw1 : (w ++ [ev w ⟨GateOp.or, [a, l]⟩]).length = t + 1 := by simp [hw]
    obtain ⟨h1, h2⟩ := ih (t + 1) t _ hw1 (by omega) (fun l' hl' => by have := hL l' (by simp [hl']); omega)
    refine ⟨by simp [resL]; omega, ?_⟩
    simp only [resL, orL, run]
    rw [h2]
    have e1 : (w ++ [ev w ⟨GateOp.or, [a, l]⟩]).getD t false = (w.getD a false || w.getD l false) := by
      rw [← hw, gnew]; simp [ev, GateOp.eval]
    rw [e1, any_congr' L _ (fun l => w.getD l false)
      (fun l' hl' => gold _ _ _ (by have := hL l' (by simp [hl']); omega))]
    simp [Bool.or_assoc]

def blk (t : ℕ) : List (List ℕ) → List Gate
  | [] => []
  | I :: Is => orL t (I.headD 0) I.tail ++ blk (t + I.tail.length) Is

def zw (t : ℕ) : List (List ℕ) → List ℕ
  | [] => []
  | I :: Is => resL t (I.headD 0) I.tail :: zw (t + I.tail.length) Is

theorem blk_len (t : ℕ) (Is : List (List ℕ)) : (blk t Is).length = (Is.map (fun I => I.tail.length)).sum := by
  induction Is generalizing t with
  | nil => rfl
  | cons I Is ih => simp [blk, ih, orL_len]

theorem zw_len (t : ℕ) (Is : List (List ℕ)) : (zw t Is).length = Is.length := by
  induction Is generalizing t with
  | nil => rfl
  | cons I Is ih => simp [zw, ih]

theorem blk_mb (t : ℕ) (Is : List (List ℕ)) : MB (blk t Is) := by
  induction Is generalizing t with
  | nil => intro g hg; simp [blk] at hg
  | cons I Is ih => exact MB_append _ _ (orL_mb _ _ _) (ih _)

theorem blk_key (N : ℕ) (Is : List (List ℕ)) : ∀ (t : ℕ) (w : List Bool), w.length = t → N ≤ t →
    (∀ I ∈ Is, I ≠ [] ∧ ∀ l ∈ I, l < N) →
    RBl t (blk t Is) ∧ (∀ z ∈ zw t Is, z < t + (blk t Is).length) ∧
    (zw t Is).map (fun z => (run (blk t Is) w).getD z false) = Is.map (fun I => I.any (fun l => w.getD l false)) := by
  induction Is with
  | nil => intro t w _ _ _; simp [blk, zw, RBl]
  | cons I Is ih =>
    intro t w hw hN hI
    obtain ⟨hne, hlt⟩ := hI I (by simp)
    have hh : I.headD 0 < t := by
      cases I with
      | nil => exact absurd rfl hne
      | cons a I => simp; have := hlt a (by simp); omega
    have htl : ∀ l ∈ I.tail, l < t := by
      intro l hl
      have := hlt l (List.mem_of_mem_tail hl)
      omega
    have hw1 := run_len (orL t (I.headD 0) I.tail) w
    rw [orL_len, hw] at hw1
    obtain ⟨k1, k2⟩ := orL_key I.tail t (I.headD 0) w hw hh htl
    obtain ⟨i1, i2, i3⟩ := ih (t + I.tail.length) (run (orL t (I.headD 0) I.tail) w) hw1 (by omega)
      (fun I' hI' => hI I' (by simp [hI']))
    refine ⟨?_, ?_, ?_⟩
    · simp only [blk]
      exact RBl_append _ _ _ (orL_rb _ _ _ hh htl) (by rw [orL_len]; exact i1)
    · intro z hz
      simp only [zw, List.mem_cons] at hz
      simp only [blk, List.length_append, orL_len]
      rcases hz with rfl | hz
      · omega
      · have := i2 z hz; omega
    · simp only [zw, blk, List.map_cons, run_append]
      rw [i3, run_pre _ _ _ (by omega), k2]
      congr 1
      · cases I with
        | nil => exact absurd rfl hne
        | cons a I => simp
      · apply List.map_congr_left
        intro I' hI'
        apply any_congr'
        intro l hl
        have := (hI I' (by simp [hI'])).2 l hl
        exact run_pre _ _ _ (by omega)

def thc (t p q : ℕ) : List ℕ → List Gate
  | [] => []
  | [z] => [⟨GateOp.and, [p, z]⟩, ⟨GateOp.or, [q, t]⟩]
  | z :: z' :: zs => [⟨GateOp.and, [p, z]⟩, ⟨GateOp.or, [q, t]⟩, ⟨GateOp.or, [p, z]⟩] ++
      thc (t + 3) (t + 2) (t + 1) (z' :: zs)

def thr (t p q : ℕ) : List ℕ → ℕ
  | [] => q
  | [_] => t + 1
  | _ :: z' :: zs => thr (t + 3) (t + 2) (t + 1) (z' :: zs)

def S : Bool → Bool → List Bool → Bool
  | _, Q, [] => Q
  | P, Q, z :: zs => S (P || z) (Q || (P && z)) zs

theorem gapp (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i < w.length then w.getD i false else if i = w.length then b else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem thc_key (L : List ℕ) : ∀ (t p q : ℕ) (w : List Bool), L ≠ [] → w.length = t → p < t → q < t →
    (∀ z ∈ L, z < t) →
    (thc t p q L).length + 1 = 3 * L.length ∧ MB (thc t p q L) ∧ RBl t (thc t p q L) ∧
    thr t p q L < t + (thc t p q L).length ∧
    (run (thc t p q L) w).getD (thr t p q L) false = S (w.getD p false) (w.getD q false) (L.map (fun z => w.getD z false)) := by
  induction L with
  | nil => intro _ _ _ _ h; exact absurd rfl h
  | cons z tl ih =>
    intro t p q w _ hw hp hq hz
    have hz0 : z < t := hz z (by simp)
    cases tl with
    | nil =>
      refine ⟨by simp [thc], ?_, ?_, by simp [thc, thr], ?_⟩
      · intro g hg; simp [thc] at hg; rcases hg with rfl | rfl <;> simp
      · refine ⟨?_, ?_, trivial⟩
        · intro i hi; simp at hi; omega
        · intro i hi; simp at hi; omega
      · have q1 : q < t + 1 := by omega
        simp [thc, thr, run, gapp, ev, GateOp.eval, hw, S, hq, hp, hz0, q1]
    | cons z' zs =>
      set w3 := run [⟨GateOp.and, [p, z]⟩, ⟨GateOp.or, [q, t]⟩, ⟨GateOp.or, [p, z]⟩] w with hw3
      have hl3 : w3.length = t + 3 := by rw [hw3, run_len, hw]; rfl
      have hz' : ∀ y ∈ z' :: zs, y < t + 3 := fun y hy => by have := hz y (by simp [hy]); omega
      obtain ⟨a1, a2, a3, a4, a5⟩ := ih (t + 3) (t + 2) (t + 1) w3 (by simp) hl3 (by omega) (by omega) hz'
      have v0 : ∀ i < t, w3.getD i false = w.getD i false := by
        intro i hi
        rw [hw3, run_pre _ _ _ (by omega)]
      have p1 : p < t + 1 := by omega
      have p2 : p < t + 1 + 1 := by omega
      have z1 : z < t + 1 := by omega
      have z2 : z < t + 1 + 1 := by omega
      have q1 : q < t + 1 := by omega
      have vt1 : w3.getD (t + 1) false = (w.getD q false || (w.getD p false && w.getD z false)) := by
        simp [hw3, run, gapp, ev, GateOp.eval, hw, hp, hq, hz0, p1, z1, q1]
      have vt2 : w3.getD (t + 2) false = (w.getD p false || w.getD z false) := by
        simp [hw3, run, gapp, ev, GateOp.eval, hw, hp, hz0, p1, z1, p2, z2]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [thc, List.length_append] at a1 ⊢; simp at a1 ⊢; omega
      · simp only [thc]
        refine MB_append _ _ ?_ a2
        intro g hg; simp at hg; rcases hg with rfl | rfl | rfl <;> simp
      · simp only [thc]
        refine RBl_append _ _ _ ⟨?_, ?_, ?_, trivial⟩ (by simpa using a3)
        · intro i hi; simp at hi; omega
        · intro i hi; simp at hi; omega
        · intro i hi; simp at hi; omega
      · simp only [thc, thr, List.length_append] at a4 ⊢; simp at a4 ⊢; omega
      · simp only [thc, thr, run_append]
        rw [← hw3, a5, vt2, vt1]
        have e : (z' :: zs).map (fun y => w3.getD y false) = (z' :: zs).map (fun y => w.getD y false) :=
          List.map_congr_left (fun y hy => v0 y (hz y (by simp [hy])))
        rw [e]
        rfl

def th2 : List Bool → Bool
  | [] => false
  | z :: zs => (z && zs.any id) || th2 zs

theorem S_eq (L : List Bool) : ∀ P Q : Bool, S P Q L = (Q || (P && L.any id) || th2 L) := by
  induction L with
  | nil => intro P Q; simp [S, th2]
  | cons z L ih =>
    intro P Q
    simp only [S, ih, th2, List.any_cons]
    cases P <;> cases Q <;> cases z <;> simp

def st2 (t : ℕ) : List ℕ → List Gate
  | z0 :: z1 :: rest => ⟨GateOp.and, [z0, z1]⟩ ::
      (if rest = [] then [] else ⟨GateOp.or, [z0, z1]⟩ :: thc (t + 2) (t + 1) t rest)
  | _ => []

def st2r (t : ℕ) : List ℕ → ℕ
  | _ :: _ :: rest => if rest = [] then t else thr (t + 2) (t + 1) t rest
  | _ => 0

theorem st2_key (L : List ℕ) (t : ℕ) (w : List Bool) (h2 : 2 ≤ L.length) (hw : w.length = t)
    (hz : ∀ z ∈ L, z < t) :
    (st2 t L).length + 5 = 3 * L.length ∧ MB (st2 t L) ∧ RBl t (st2 t L) ∧
    st2r t L < t + (st2 t L).length ∧
    (run (st2 t L) w).getD (st2r t L) false = th2 (L.map (fun z => w.getD z false)) := by
  match L, h2 with
  | z0 :: z1 :: rest, _ =>
    have h0 : z0 < t := hz z0 (by simp)
    have h1 : z1 < t := hz z1 (by simp)
    have h0' : z0 < t + 1 := by omega
    have h1' : z1 < t + 1 := by omega
    by_cases hr : rest = []
    · subst hr
      refine ⟨by simp [st2], ?_, ?_, by simp [st2, st2r], ?_⟩
      · intro g hg; simp [st2] at hg; subst hg; simp
      · refine ⟨?_, trivial⟩
        intro i hi; simp at hi; omega
      · simp [st2, st2r, run, gapp, ev, GateOp.eval, hw, h0, h1, th2]
    · set w2 := run [⟨GateOp.and, [z0, z1]⟩, ⟨GateOp.or, [z0, z1]⟩] w with hw2
      have hl2 : w2.length = t + 2 := by rw [hw2, run_len, hw]; rfl
      have hz' : ∀ y ∈ rest, y < t + 2 := fun y hy => by have := hz y (by simp [hy]); omega
      obtain ⟨a1, a2, a3, a4, a5⟩ := thc_key rest (t + 2) (t + 1) t w2 hr hl2 (by omega) (by omega) hz'
      have v0 : ∀ i < t, w2.getD i false = w.getD i false := by
        intro i hi
        rw [hw2, run_pre _ _ _ (by omega)]
      have vt : w2.getD t false = (w.getD z0 false && w.getD z1 false) := by
        simp [hw2, run, gapp, ev, GateOp.eval, hw, h0, h1, h0', h1']
      have vt1 : w2.getD (t + 1) false = (w.getD z0 false || w.getD z1 false) := by
        simp [hw2, run, gapp, ev, GateOp.eval, hw, h0, h1, h0', h1']
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [st2, if_neg hr, List.length_cons] at a1 ⊢; omega
      · simp only [st2, if_neg hr]
        refine MB_cons _ _ (by simp) (MB_cons _ _ (by simp) a2)
      · simp only [st2, if_neg hr]
        refine ⟨?_, ?_, a3⟩
        · intro i hi; simp at hi; omega
        · intro i hi; simp at hi; omega
      · simp only [st2, st2r, if_neg hr, List.length_cons]; omega
      · have er : run (st2 t (z0 :: z1 :: rest)) w = run (thc (t + 2) (t + 1) t rest) w2 := by
          simp only [st2, if_neg hr, hw2, run]
        simp only [st2r, if_neg hr]
        rw [er, a5, vt1, vt, S_eq]
        have e : rest.map (fun z => w2.getD z false) = rest.map (fun z => w.getD z false) := by
          apply List.map_congr_left
          intro y hy
          exact v0 y (hz y (by simp [hy]))
        rw [e]
        simp only [List.map_cons, th2, List.any_cons]
        cases w.getD z0 false <;> cases w.getD z1 false <;> simp

theorem ofg {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) : (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [h]

theorem one_l {r c : ℕ} (u : Fin r) (v : Fin c) (i : ℕ) (hi : i < r) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  rw [ofg _ i hi]; simp [Fin.ext_iff]

theorem one_r {r c : ℕ} (u : Fin r) (v : Fin c) (i : ℕ) (hi : i < c) :
    (PEqualNP.Represents.oneEach u v).getD (r + i) false = decide (i = v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  have e : r + i - (List.ofFn fun i : Fin r => decide (i = u)).length = i := by simp
  rw [e, ofg _ i hi]; simp [Fin.ext_iff]

theorem one_len {r c : ℕ} (u : Fin r) (v : Fin c) : (PEqualNP.Represents.oneEach u v).length = r + c := by
  simp [PEqualNP.Represents.oneEach]

def cls (r c m : ℕ) (κr : Fin r → Fin m) (κc : Fin c → Fin m) (K : Fin m) : List ℕ :=
  ((List.finRange r).filter (fun u => κr u = K)).map (fun u => u.val) ++
    ((List.finRange c).filter (fun v => κc v = K)).map (fun v => r + v.val)

theorem th2_map {m : ℕ} (a b : Fin m) (L : List (Fin m)) (hL : L.Nodup) :
    th2 (L.map (fun K => decide (a = K) || decide (b = K))) = decide (a ∈ L ∧ b ∈ L ∧ a ≠ b) ∧
    (L.map (fun K => decide (a = K) || decide (b = K))).any id = decide (a ∈ L ∨ b ∈ L) := by
  induction L with
  | nil => simp [th2]
  | cons K L ih =>
    rw [List.nodup_cons] at hL
    obtain ⟨i1, i2⟩ := ih hL.2
    simp only [List.map_cons, th2, List.any_cons, i1, i2, List.mem_cons]
    by_cases ha : a = K <;> by_cases hb : b = K
    · subst ha; subst hb; simp [hL.1]
    · subst ha; simp [hb, hL.1] <;> tauto
    · subst hb; simp [ha, hL.1] <;> tauto
    · simp [ha, hb]

theorem sumfib {r m : ℕ} (κr : Fin r → Fin m) (l : List (Fin r)) :
    ((List.finRange m).map (fun K => (l.filter (fun u => κr u = K)).length)).sum = l.length := by
  induction l with
  | nil => simp
  | cons u l ih =>
    have e : (List.finRange m).map (fun K => ((u :: l).filter (fun u => κr u = K)).length) =
        (List.finRange m).map (fun K => (if κr u = K then 1 else 0) + (l.filter (fun u => κr u = K)).length) := by
      apply List.map_congr_left
      intro K _
      rw [List.filter_cons]
      split_ifs with h1 h2 h2 <;> simp_all <;> omega
    rw [← Fin.sum_univ_def] at ih
    rw [e, ← Fin.sum_univ_def, Finset.sum_add_distrib, ih, Finset.sum_ite_eq]
    simp; omega

theorem sub1 {α : Type} (f : α → ℕ) (L : List α) (h : ∀ x ∈ L, 1 ≤ f x) :
    (L.map (fun x => f x - 1)).sum + L.length = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (by simp)
    rw [← ih (fun x hx => h x (by simp [hx]))]
    omega

theorem main (r c m : ℕ) (κr : Fin r → Fin m) (κc : Fin c → Fin m) (hm : 2 ≤ m)
    (hK : ∀ K : Fin m, (∃ u, κr u = K) ∧ (∃ v, κc v = K)) :
    ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack (r + c) C ∧ C.size ≤ (r + c - m) + (3 * m - 5) ∧
      PEqualNP.Represents.Represents (fun (u : Fin r) (v : Fin c) => decide (κr u ≠ κc v)) C := by
  set Is := (List.finRange m).map (cls r c m κr κc) with hIs
  set t1 := r + c + (blk (r + c) Is).length with ht1
  set G := blk (r + c) Is ++ st2 t1 (zw (r + c) Is) with hG
  have hI : ∀ I ∈ Is, I ≠ [] ∧ ∀ l ∈ I, l < r + c := by
    intro I hI
    rw [hIs, List.mem_map] at hI
    obtain ⟨K, _, rfl⟩ := hI
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨u, hu⟩, _⟩ := hK K
      intro h
      have : u.val ∈ cls r c m κr κc K := by
        simp only [cls, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
        exact Or.inl ⟨u, by simp [hu], rfl⟩
      rw [h] at this; simp at this
    · intro l hl
      simp only [cls, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hl
      rcases hl with ⟨u, _, rfl⟩ | ⟨v, _, rfl⟩
      · have := u.isLt; omega
      · have := v.isLt; omega
  have hzl : (zw (r + c) Is).length = m := by rw [zw_len, hIs]; simp
  have hsum : (Is.map (fun I => I.length)).sum = r + c := by
    rw [hIs, List.map_map]
    have e : (List.finRange m).map ((fun I : List ℕ => I.length) ∘ cls r c m κr κc) =
        (List.finRange m).map (fun K => ((List.finRange r).filter (fun u => κr u = K)).length +
          ((List.finRange c).filter (fun v => κc v = K)).length) := by
      apply List.map_congr_left; intro K _; simp [cls]
    rw [e, ← Fin.sum_univ_def, Finset.sum_add_distrib, Fin.sum_univ_def, Fin.sum_univ_def, sumfib, sumfib]
    simp
  have hblk : (blk (r + c) Is).length + m = r + c := by
    rw [blk_len, ← hsum]
    have := sub1 (fun I : List ℕ => I.length) Is (fun I hI' => by
      have := (hI I hI').1
      cases I with
      | nil => exact absurd rfl this
      | cons a I => simp)
    have hlen : Is.length = m := by rw [hIs]; simp
    rw [hlen] at this
    rw [← this]
    simp [List.length_tail]
  refine ⟨⟨G, st2r t1 (zw (r + c) Is)⟩, ?_, ?_, ?_, ?_⟩
  · exact MB_append _ _ (blk_mb _ _) (fun g hg => by
      have := (st2_key (zw (r + c) Is) t1 (List.replicate t1 false) (by omega) (by simp)
        (fun z hz => by
          obtain ⟨_, b2, _⟩ := blk_key (r + c) Is (r + c) (List.replicate (r + c) false) (by simp) le_rfl hI
          exact b2 z hz)).2.1
      exact this g hg)
  · intro j hj i hi
    obtain ⟨b1, b2, _⟩ := blk_key (r + c) Is (r + c) (List.replicate (r + c) false) (by simp) le_rfl hI
    obtain ⟨_, _, s3, _, _⟩ := st2_key (zw (r + c) Is) t1 (List.replicate t1 false) (by omega) (by simp) b2
    exact RBl_get (r + c) G (RBl_append _ _ _ b1 s3) j hj i hi
  · obtain ⟨_, b2, _⟩ := blk_key (r + c) Is (r + c) (List.replicate (r + c) false) (by simp) le_rfl hI
    obtain ⟨s1, _⟩ := st2_key (zw (r + c) Is) t1 (List.replicate t1 false) (by omega) (by simp) b2
    show (blk (r + c) Is ++ st2 t1 (zw (r + c) Is)).length ≤ _
    rw [List.length_append]
    rw [hzl] at s1
    omega
  · intro u v
    have hx := one_len u v
    obtain ⟨_, b2, b3⟩ := blk_key (r + c) Is (r + c) (PEqualNP.Represents.oneEach u v) hx le_rfl hI
    have hl1 := run_len (blk (r + c) Is) (PEqualNP.Represents.oneEach u v)
    rw [hx] at hl1
    obtain ⟨_, _, _, _, s5⟩ := st2_key (zw (r + c) Is) t1 _ (by omega) hl1 b2
    unfold Circuit.eval Circuit.wires
    rw [run_eq]
    show (run (blk (r + c) Is ++ st2 t1 (zw (r + c) Is)) _).getD _ false = _
    rw [run_append, s5, b3, hIs, List.map_map]
    have e : (List.finRange m).map ((fun I => I.any (fun l => (PEqualNP.Represents.oneEach u v).getD l false)) ∘
        cls r c m κr κc) = (List.finRange m).map (fun K => decide (κr u = K) || decide (κc v = K)) := by
      apply List.map_congr_left
      intro K _
      simp only [Function.comp, cls, List.any_append, List.any_map]
      congr 1
      · rw [Bool.eq_iff_iff, List.any_eq_true]
        simp only [List.mem_filter, List.mem_finRange, true_and, Function.comp]
        constructor
        · rintro ⟨u', hu', h⟩
          rw [one_l u v u'.val u'.isLt] at h
          have := of_decide_eq_true h
          have e : u' = u := Fin.ext this
          subst e; simpa using hu'
        · intro h
          refine ⟨u, by simpa using h, ?_⟩
          rw [one_l u v u.val u.isLt]; simp
      · rw [Bool.eq_iff_iff, List.any_eq_true]
        simp only [List.mem_filter, List.mem_finRange, true_and, Function.comp]
        constructor
        · rintro ⟨v', hv', h⟩
          rw [one_r u v v'.val v'.isLt] at h
          have := of_decide_eq_true h
          have e : v' = v := Fin.ext this
          subst e; simpa using hv'
        · intro h
          refine ⟨v, by simpa using h, ?_⟩
          rw [one_r u v v.val v.isLt]; simp
    rw [e, (th2_map (κr u) (κc v) (List.finRange m) (List.nodup_finRange m)).1]
    simp

theorem main2 (n m : ℕ) (f g : Fin n → Fin m) (hm : 2 ≤ m) (hf : ∀ k : Fin m, ∃ u, f u = k)
    (hg : ∀ k : Fin m, ∃ v, g v = k) :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (f u ≠ g v)) (2 * n + 2 * m - 5) := by
  obtain ⟨C, h1, _, h3, h4⟩ := main n n m f g hm (fun K => ⟨hf K, hg K⟩)
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_surjective f (fun k => hf k)
  exact ⟨C, h1, by omega, h4⟩

end PEqualNP.Outside.L_meta_25456

theorem PEqualNP.Outside.L_meta_25456 : ∀ (n m : ℕ) (f g : Fin n → Fin m), 2 ≤ m → (∀ k : Fin m, ∃ u, f u = k) → (∀ k : Fin m, ∃ v, g v = k) → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (f u ≠ g v)) (2 * n + 2 * m - 5) := by
  intro n m f g hm hf hg
  exact PEqualNP.Outside.L_meta_25456.main2 n m f g hm hf hg

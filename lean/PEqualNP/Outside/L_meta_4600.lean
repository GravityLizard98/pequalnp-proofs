import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4600

def s1 (l : List (BitVec 59)) (p : Bool × Fin 40 × Fin 40) : List (BitVec 59) :=
  l ++ [if p.1 = true then l.getD ↑p.2.1 (0 : BitVec 59) ||| l.getD ↑p.2.2 (0 : BitVec 59)
    else l.getD ↑p.2.1 (0 : BitVec 59) &&& l.getD ↑p.2.2 (0 : BitVec 59)]

def s2 (l : List ℕ) (p : Bool × ℕ × ℕ) : List ℕ :=
  l ++ [if p.1 = true then l.getD p.2.1 0 ||| l.getD p.2.2 0
    else l.getD p.2.1 0 &&& l.getD p.2.2 0]

theorem gd (l : List (BitVec 59)) (i : ℕ) :
    (l.map BitVec.toNat).getD i 0 = (l.getD i (0 : BitVec 59)).toNat := by
  have h := List.getD_map (f := BitVec.toNat) (l := l) (d := (0 : BitVec 59)) (n := i)
  simpa using h

theorem one (l : List (BitVec 59)) (p : Bool × Fin 40 × Fin 40) :
    s2 (l.map BitVec.toNat) (p.1, ↑p.2.1, ↑p.2.2) = (s1 l p).map BitVec.toNat := by
  unfold s1 s2
  rw [List.map_append]
  congr 1
  simp only [List.map_cons, List.map_nil, gd]
  split_ifs
  · rw [BitVec.toNat_or]
  · rw [BitVec.toNat_and]

theorem main (q : List (Bool × Fin 40 × Fin 40)) : ∀ l : List (BitVec 59),
    List.foldl s2 (l.map BitVec.toNat)
      (q.map fun p : Bool × Fin 40 × Fin 40 => (p.1, (p.2.1 : ℕ), (p.2.2 : ℕ)))
      = (List.foldl s1 l q).map BitVec.toNat := by
  induction q with
  | nil => intro l; rfl
  | cons p q ih =>
    intro l
    simp only [List.map_cons, List.foldl_cons]
    rw [one, ih]

end PEqualNP.Outside.L_meta_4600

theorem PEqualNP.Outside.L_meta_4600 : have x1 : List (BitVec (59 : ℕ)) → Bool × Fin (40 : ℕ) × Fin (40 : ℕ) → List (BitVec (59 : ℕ)) := fun (x1 : List (BitVec (59 : ℕ))) (x2 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x1 ++ [if x2.1 = Bool.true then x1.getD ↑x2.2.1 (0 : BitVec (59 : ℕ)) ||| x1.getD ↑x2.2.2 (0 : BitVec (59 : ℕ)) else x1.getD ↑x2.2.1 (0 : BitVec (59 : ℕ)) &&& x1.getD ↑x2.2.2 (0 : BitVec (59 : ℕ))]; have x2 : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]; ∀ (x3 : List (BitVec (59 : ℕ))) (x4 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))), List.foldl x2 (List.map BitVec.toNat x3) (List.map (fun (x5 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => (x5.1, ↑x5.2.1, ↑x5.2.2)) x4) = List.map BitVec.toNat (List.foldl x1 x3 x4) := by
  intro x1 x2 x3 x4
  exact L_meta_4600.main x4 x3

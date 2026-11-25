import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_17723

abbrev Word := BitVec 32768

def inputAt (r : Fin 32768) (i : Fin 15) : Bool := r.val.testBit i.val


def joinHalves {n : Nat} (hi lo : BitVec (2^n)) : BitVec (2^(n+1)) :=
  (hi ++ lo).cast (by rw [Nat.pow_succ, Nat.mul_two])

theorem joinBit {n : Nat} (hi lo : BitVec (2^n)) (r : Nat) :
    (joinHalves hi lo).getLsbD r =
      if r < 2^n then lo.getLsbD r else hi.getLsbD (r - 2^n) := by
  simp only [joinHalves, BitVec.getLsbD_cast, BitVec.getLsbD_append]

def binaryColumn : (n i : Nat) → BitVec (2^n)
  | 0, _ => 0
  | n+1, i =>
      if i < n then
        let old := binaryColumn n i
        joinHalves old old
      else
        joinHalves (BitVec.allOnes (2^n)) 0

theorem binaryColumnBit {n i r : Nat} (hi : i < n) (hr : r < 2^n) :
    (binaryColumn n i).getLsbD r = r.testBit i := by
  induction n generalizing i r with
  | zero => omega
  | succ n ih =>
    have half : r - 2^n < 2^n := by rw [Nat.pow_succ, Nat.mul_two] at hr; omega
    by_cases lower : i < n
    · rw [binaryColumn, if_pos lower, joinBit]
      by_cases head : r < 2^n
      · exact (if_pos head).trans (ih lower head)
      · rw [if_neg head, ih lower half]
        have split : 2^n+(r-2^n)=r := by omega
        exact ((congrArg (fun t : Nat => t.testBit i) split).symm.trans
          (Nat.testBit_two_pow_add_gt lower (r-2^n))).symm
    · have eq : i=n := by omega
      subst i
      rw [binaryColumn, if_neg (by omega), joinBit]
      by_cases head : r < 2^n
      · rw [if_pos head, Nat.testBit_lt_two_pow head]
        simp [BitVec.getLsbD]
      · rw [if_neg head, BitVec.getLsbD_allOnes,
          Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (Nat.le_of_not_gt head) hr]
        exact decide_eq_true half

def source (i : Fin 15) : Word := binaryColumn 15 i.val

theorem sourceBit (r : Fin 32768) (i : Fin 15) :
    (source i).getLsbD r.val = inputAt r i :=
  binaryColumnBit i.isLt r.isLt


def inputRow (x : Fin 15 → Bool) : Fin 32768 :=
  let bits := BitVec.ofBoolListLE (List.ofFn x)
  ⟨bits.toNat, by simpa using bits.isLt⟩

theorem rowCorrect (x : Fin 15 → Bool) : inputAt (inputRow x) = x := by
  funext i
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, dif_pos, Option.getD_some]

def observe (r : Fin 32768) (w : Word) : Bool := w.getLsbD r.val

def allBits (xs : List Word) : Word := xs.foldr (· &&& ·) (BitVec.allOnes 32768)
def anyBits (xs : List Word) : Word := xs.foldr (· ||| ·) 0

theorem allBitsCorrect (r : Fin 32768) (xs : List Word) :
    observe r (allBits xs) = (xs.map (observe r)).all id := by
  induction xs with
  | nil =>
    change (BitVec.allOnes 32768).getLsbD r.val = true
    rw [BitVec.getLsbD_allOnes]
    exact decide_eq_true r.isLt
  | cons x xs ih =>
    change observe r (x &&& allBits xs) = (observe r x && (xs.map (observe r)).all id)
    exact (BitVec.getLsbD_and).trans (congrArg (fun b => observe r x && b) ih)

theorem anyBitsCorrect (r : Fin 32768) (xs : List Word) :
    observe r (anyBits xs) = (xs.map (observe r)).any id := by
  induction xs with
  | nil => simp [anyBits, observe]
  | cons x xs ih =>
    change observe r (x ||| anyBits xs) = (observe r x || (xs.map (observe r)).any id)
    exact (BitVec.getLsbD_or).trans (congrArg (fun b => observe r x || b) ih)

theorem observedRead (r : Fin 32768) (xs : List Word) (i : ℕ) :
    observe r (xs.getD i 0) = (xs.map (observe r)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : xs[i]? <;> simp [observe, h]

def packedGate (op : GateOp) (xs : List Word) : Word :=
  match op with
  | .and => allBits xs
  | .or => anyBits xs
  | .not => ~~~(xs.headD 0)
  | _ => 0

theorem gateMatches (r : Fin 32768) (g : Gate) (ws : List Word)
    (ops : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    observe r (packedGate g.op (g.inputs.map (fun i => ws.getD i 0))) =
      g.op.eval (g.inputs.map (fun i => (ws.map (observe r)).getD i false)) := by
  have reads : (g.inputs.map (fun i => ws.getD i 0)).map (observe r) =
      g.inputs.map (fun i => (ws.map (observe r)).getD i false) := by
    rw [List.map_map]
    congr 1
    funext i
    exact observedRead r ws i
  rcases ops with h | h | h
  · rw [h]
    change observe r (allBits _) = _
    rw [allBitsCorrect, reads]
    rfl
  · rw [h]
    change observe r (anyBits _) = _
    rw [anyBitsCorrect, reads]
    rfl
  · rw [h]
    change observe r (~~~((g.inputs.map fun i => ws.getD i 0).headD 0)) = !_
    rw [← reads]
    simp only [List.headD_eq_getD, ← observedRead]
    simp [observe, BitVec.getLsbD_not, r.isLt]

def packedRun : List Gate → List Word → List Word
  | [], ws => ws
  | g :: gs, ws => packedRun gs (ws ++ [packedGate g.op (g.inputs.map (fun i => ws.getD i 0))])

theorem runMatches (r : Fin 32768) (gs : List Gate) (ws : List Word)
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (packedRun gs ws).map (observe r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) (ws.map (observe r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [packedRun, List.foldl_cons]
    rw [ih _ (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))]
    simp only [List.map_append, List.map_singleton]
    rw [gateMatches r g ws (ops g (by simp))]



def witness : Circuit :=
  ⟨[⟨.and, [9, 14]⟩, ⟨.and, [10, 13]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 17]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [20, 17]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [31, 36]⟩, ⟨.and, [37, 22]⟩, ⟨.or, [32, 35]⟩, ⟨.and, [39, 23]⟩, ⟨.or, [33, 34]⟩, ⟨.and, [41, 24]⟩, ⟨.or, [38, 40]⟩, ⟨.or, [43, 42]⟩, ⟨.and, [25, 30]⟩, ⟨.and, [45, 44]⟩, ⟨.or, [25, 30]⟩, ⟨.and, [47, 22]⟩, ⟨.or, [26, 29]⟩, ⟨.and, [49, 23]⟩, ⟨.or, [27, 28]⟩, ⟨.and, [51, 24]⟩, ⟨.or, [48, 50]⟩, ⟨.or, [53, 52]⟩, ⟨.and, [31, 36]⟩, ⟨.and, [55, 54]⟩, ⟨.or, [46, 56]⟩, ⟨.and, [19, 57]⟩, ⟨.and, [10, 26]⟩, ⟨.and, [59, 32]⟩, ⟨.and, [11, 27]⟩, ⟨.and, [61, 33]⟩, ⟨.and, [12, 28]⟩, ⟨.and, [63, 34]⟩, ⟨.and, [13, 29]⟩, ⟨.and, [65, 35]⟩, ⟨.or, [58, 60]⟩, ⟨.or, [67, 62]⟩, ⟨.or, [68, 64]⟩, ⟨.or, [69, 66]⟩, ⟨.and, [0, 70]⟩, ⟨.and, [0, 14]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [72, 73]⟩, ⟨.or, [75, 74]⟩, ⟨.and, [72, 73]⟩, ⟨.and, [77, 74]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [5, 11]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [2, 13]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [88, 93]⟩, ⟨.and, [94, 79]⟩, ⟨.or, [89, 92]⟩, ⟨.and, [96, 80]⟩, ⟨.or, [90, 91]⟩, ⟨.and, [98, 81]⟩, ⟨.or, [95, 97]⟩, ⟨.or, [100, 99]⟩, ⟨.and, [82, 87]⟩, ⟨.and, [102, 101]⟩, ⟨.or, [82, 87]⟩, ⟨.and, [104, 79]⟩, ⟨.or, [83, 86]⟩, ⟨.and, [106, 80]⟩, ⟨.or, [84, 85]⟩, ⟨.and, [108, 81]⟩, ⟨.or, [105, 107]⟩, ⟨.or, [110, 109]⟩, ⟨.and, [88, 93]⟩, ⟨.and, [112, 111]⟩, ⟨.or, [103, 113]⟩, ⟨.and, [76, 114]⟩, ⟨.and, [3, 83]⟩, ⟨.and, [116, 89]⟩, ⟨.and, [4, 84]⟩, ⟨.and, [118, 90]⟩, ⟨.and, [7, 85]⟩, ⟨.and, [120, 91]⟩, ⟨.and, [8, 86]⟩, ⟨.and, [122, 92]⟩, ⟨.or, [115, 117]⟩, ⟨.or, [124, 119]⟩, ⟨.or, [125, 121]⟩, ⟨.or, [126, 123]⟩, ⟨.and, [9, 127]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [129, 130]⟩, ⟨.or, [132, 131]⟩, ⟨.and, [129, 130]⟩, ⟨.and, [134, 131]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [3, 10]⟩, ⟨.and, [3, 12]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [7, 12]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [4, 8]⟩, ⟨.and, [4, 11]⟩, ⟨.and, [4, 13]⟩, ⟨.and, [8, 11]⟩, ⟨.and, [8, 13]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [145, 150]⟩, ⟨.and, [151, 136]⟩, ⟨.or, [146, 149]⟩, ⟨.and, [153, 137]⟩, ⟨.or, [147, 148]⟩, ⟨.and, [155, 138]⟩, ⟨.or, [152, 154]⟩, ⟨.or, [157, 156]⟩, ⟨.and, [139, 144]⟩, ⟨.and, [159, 158]⟩, ⟨.or, [139, 144]⟩, ⟨.and, [161, 136]⟩, ⟨.or, [140, 143]⟩, ⟨.and, [163, 137]⟩, ⟨.or, [141, 142]⟩, ⟨.and, [165, 138]⟩, ⟨.or, [162, 164]⟩, ⟨.or, [167, 166]⟩, ⟨.and, [145, 150]⟩, ⟨.and, [169, 168]⟩, ⟨.or, [160, 170]⟩, ⟨.and, [133, 171]⟩, ⟨.and, [1, 140]⟩, ⟨.and, [173, 146]⟩, ⟨.and, [2, 141]⟩, ⟨.and, [175, 147]⟩, ⟨.and, [5, 142]⟩, ⟨.and, [177, 148]⟩, ⟨.and, [6, 143]⟩, ⟨.and, [179, 149]⟩, ⟨.or, [172, 174]⟩, ⟨.or, [181, 176]⟩, ⟨.or, [182, 178]⟩, ⟨.or, [183, 180]⟩, ⟨.and, [14, 184]⟩, ⟨.or, [21, 71]⟩, ⟨.or, [186, 78]⟩, ⟨.or, [187, 128]⟩, ⟨.or, [188, 135]⟩, ⟨.or, [189, 185]⟩, ⟨.not, [190]⟩], 191⟩



def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

theorem witnessOps : ∀ g ∈ witness.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  intro g hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (witnessFit g hg).1


def packedWitness : Word := (packedRun witness.gates (List.ofFn source)).getD witness.output 0

theorem packedCorrect (r : Fin 32768) :
    observe r packedWitness = witness.eval (List.ofFn (inputAt r)) := by
  have inputs : (List.ofFn source).map (observe r) = List.ofFn (inputAt r) := by
    rw [List.map_ofFn]
    exact congrArg (fun f : Fin 15 → Bool => List.ofFn f) (funext (fun i => sourceBit r i))
  unfold packedWitness Circuit.eval Circuit.wires
  rw [observedRead, runMatches r witness.gates _ witnessOps, inputs]

def expected : Word := ~~~((source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 7 &&& source 9 &&& source 13 &&& source 14) ||| (source 0 &&& source 2 &&& source 4 &&& source 6 &&& source 8 &&& source 13) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 9 &&& source 11 &&& source 12 &&& source 13) ||| (source 0 &&& source 3 &&& source 4 &&& source 5 &&& source 7 &&& source 9 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 6 &&& source 7 &&& source 9 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 13) ||| (source 0 &&& source 3 &&& source 4 &&& source 6 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 5 &&& source 6 &&& source 9 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 4 &&& source 5 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 13) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 13) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 4 &&& source 6 &&& source 8 &&& source 10 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 2 &&& source 3 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 1 &&& source 2 &&& source 3 &&& source 5 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 13) ||| (source 0 &&& source 1 &&& source 3 &&& source 6 &&& source 7 &&& source 10 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 4 &&& source 5 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12) ||| (source 0 &&& source 1 &&& source 2 &&& source 5 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 2 &&& source 4 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 5 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 2 &&& source 4 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 13) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 14) ||| (source 0 &&& source 2 &&& source 3 &&& source 5 &&& source 6 &&& source 9 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 6 &&& source 7 &&& source 9 &&& source 11 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 5 &&& source 7 &&& source 10) ||| (source 0 &&& source 3 &&& source 4 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 6 &&& source 7 &&& source 10 &&& source 11 &&& source 13) ||| (source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 5 &&& source 6 &&& source 9) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 3 &&& source 5 &&& source 7 &&& source 8 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 8 &&& source 9 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 13) ||| (source 0 &&& source 1 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 12 &&& source 13) ||| (source 0 &&& source 2 &&& source 4 &&& source 6 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 4 &&& source 5 &&& source 7 &&& source 8 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 3 &&& source 4 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 2 &&& source 4 &&& source 5 &&& source 8 &&& source 10 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12) ||| (source 0 &&& source 3 &&& source 4 &&& source 7 &&& source 8 &&& source 14) ||| (source 1 &&& source 2 &&& source 3 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 8 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 12) ||| (source 0 &&& source 2 &&& source 3 &&& source 6 &&& source 7 &&& source 12) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 8 &&& source 10 &&& source 12 &&& source 13) ||| (source 1 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 8 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 3 &&& source 4 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 14) ||| (source 0 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 13) ||| (source 0 &&& source 2 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 11 &&& source 12) ||| (source 0 &&& source 2 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 4 &&& source 5 &&& source 6 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 7 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 2 &&& source 3 &&& source 5 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 14) ||| (source 0 &&& source 1 &&& source 4 &&& source 5 &&& source 8 &&& source 11) ||| (source 1 &&& source 2 &&& source 3 &&& source 9 &&& source 10 &&& source 12) ||| (source 0 &&& source 1 &&& source 4 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 6 &&& source 8 &&& source 10 &&& source 11 &&& source 12) ||| (source 0 &&& source 2 &&& source 3 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 11 &&& source 13) ||| (source 0 &&& source 1 &&& source 2 &&& source 5 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 5 &&& source 7 &&& source 8 &&& source 10 &&& source 11 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 13 &&& source 14) ||| (source 2 &&& source 3 &&& source 4 &&& source 12 &&& source 13 &&& source 14) ||| (source 6 &&& source 7 &&& source 8 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 4 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 2 &&& source 3 &&& source 5 &&& source 7 &&& source 10 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 5 &&& source 6 &&& source 8 &&& source 9 &&& source 11 &&& source 13) ||| (source 0 &&& source 2 &&& source 3 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 10 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 3 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 3 &&& source 4 &&& source 10 &&& source 11 &&& source 14) ||| (source 0 &&& source 2 &&& source 3 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 2 &&& source 4 &&& source 9 &&& source 11 &&& source 13) ||| (source 5 &&& source 6 &&& source 7 &&& source 9 &&& source 10 &&& source 12) ||| (source 0 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 12) ||| (source 1 &&& source 2 &&& source 3 &&& source 5 &&& source 6 &&& source 8 &&& source 9 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 12 &&& source 14) ||| (source 0 &&& source 3 &&& source 4 &&& source 5 &&& source 8 &&& source 9 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 2 &&& source 4 &&& source 5 &&& source 6 &&& source 9 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 9 &&& source 12 &&& source 13 &&& source 14))
def target (x : Fin 15 → Bool) : Bool := !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14))

set_option maxRecDepth 16000 in
theorem expectedCorrect (r : Fin 32768) :
    observe r expected = target (inputAt r) := by
  simp only [expected, target, observe, BitVec.getLsbD_not, r.isLt, decide_true,
    Bool.true_and, BitVec.getLsbD_and, BitVec.getLsbD_or, sourceBit]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 60000000 in
theorem wordsMatch : packedWitness = expected := by
  decide +kernel

end PEqualNP.Outside.L_meta_17723

open PEqualNP.Outside.L_meta_17723 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_17723 : PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14))) 290 := by
  change PEqualNP.MetaComplexity.HasCircuitSize 15 target 290
  refine ⟨witness, witnessFit, by decide, ?_⟩
  intro x
  have h := packedCorrect (inputRow x)
  rw [wordsMatch, expectedCorrect, rowCorrect] at h
  exact h.symm

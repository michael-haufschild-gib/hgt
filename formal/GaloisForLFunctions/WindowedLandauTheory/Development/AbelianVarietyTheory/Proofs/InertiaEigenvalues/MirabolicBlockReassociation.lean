import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalRadicalReindex

/-! Splitting the first row of the right rectangle and adjoining the removed
mirabolic column gives the coordinates for the next tail subgroup. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ}

/-- Reassociate the rectangle coordinates for blocks of sizes a, 1 and b. -/
def mirabolicRectangleEquiv :
    ((Fin a → ZMod g) × Matrix (Fin (a + 1)) (Fin b) (ZMod g)) ≃
      (Matrix (Fin a) (Fin (1 + b)) (ZMod g) × Matrix (Fin 1) (Fin b) (ZMod g)) where
  toFun x :=
    (fun i j => Fin.addCases (fun _ => x.1 i) (x.2 (Fin.castAdd 1 i)) j,
      fun i j => x.2 (Fin.natAdd a i) j)
  invFun x :=
    (fun i => x.1 i (Fin.castAdd b 0),
      fun i j => Fin.addCases (fun k => x.1 k (Fin.natAdd 1 j)) (fun k => x.2 k j) i)
  left_inv x := by
    apply Prod.ext
    · funext i
      simp
    · ext i j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp
  right_inv x := by
    apply Prod.ext
    · ext i j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · have h : k = 0 := Subsingleton.elim _ _
        subst k
        simp
      · simp
    · ext i j
      simp

variable [Fact g.Prime]

/-- Reassociating the ranks of three blocks preserves the upper block unit. -/
theorem upperBlockUnit_mirabolic_assoc (A : Gn g a) (v : Fin a → ZMod g)
    (X : Matrix (Fin (a + 1)) (Fin b) (ZMod g)) (D : Gn g b) :
    reindexUnit (finCongr (Nat.add_assoc a 1 b)) (upperBlockUnit (mirabolicBlock A v) X D) =
      upperBlockUnit A (mirabolicRectangleEquiv (v, X)).1
        (upperBlockUnit (1 : Gn g 1) (mirabolicRectangleEquiv (v, X)).2 D) := by
  let e := finCongr (Nat.add_assoc a 1 b).symm
  have hA (i : Fin a) : e (Fin.castAdd (1 + b) i) = Fin.castAdd b (Fin.castAdd 1 i) := Fin.ext rfl
  have hM (i : Fin 1) : e (Fin.natAdd a (Fin.castAdd b i)) = Fin.castAdd b (Fin.natAdd a i) :=
    Fin.ext rfl
  have hD (i : Fin b) : e (Fin.natAdd a (Fin.natAdd 1 i)) = Fin.natAdd (a + 1) i :=
    Fin.ext (Nat.add_assoc a 1 i.val).symm
  apply Units.ext
  apply Matrix.ext
  intro i j
  rw [reindexUnit_apply]
  change (upperBlockMatrix (upperBlockMatrix A.val (fun i (_ : Fin 1) => v i) (1 : Mt g 1))
      X D.val) (e i) (e j) =
    (upperBlockMatrix A.val (mirabolicRectangleEquiv (v, X)).1
      (upperBlockMatrix (1 : Mt g 1) (mirabolicRectangleEquiv (v, X)).2 D.val)) i j
  refine Fin.addCases (fun i => ?_) (fun i => Fin.addCases (fun i => ?_) (fun i => ?_) i) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => Fin.addCases (fun j => ?_) (fun j => ?_) j) j <;>
    simp [hA, hM, hD, upperBlockMatrix, mirabolicRectangleEquiv]

end GlobalTheory.GLq

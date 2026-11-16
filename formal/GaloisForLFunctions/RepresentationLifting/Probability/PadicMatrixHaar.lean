import GaloisForLFunctions.RepresentationLifting.Probability.FiniteQuotientHaar
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.PadicNilpotence
import GaloisForLFunctions.RHTower.FieldOnePadicCyclicHaarQuadrature
import GaloisForLFunctions.HTGeometry.CompactAbelianHaar

/-!
# Haar probability on integral p-adic matrices

The compact additive matrix group carries normalized Haar measure.
Every finite residue event has its uniform counting probability;
this connects finite matrix laws to genuine p-adic random matrices.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

open MeasureTheory OperatorKernels

variable (p : ℕ) [Fact p.Prime]

instance padicMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℤ_[p]) := borel _

instance padicMatrixBorelSpace (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℤ_[p]) := ⟨rfl⟩

instance padicMatrixCompactSpace (n : ℕ) :
    CompactSpace (Matrix (Fin n) (Fin n) ℤ_[p]) :=
  inferInstanceAs (CompactSpace (Fin n → Fin n → ℤ_[p]))

/-- Additive Haar probability on all integral p-adic matrices of size `n`. -/
abbrev padicMatrixHaar (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℤ_[p]) :=
  CompactAbelian.haarProb _

/-- Entrywise residue reduction is continuous. -/
theorem padicMatrixProjection_continuous (k n : ℕ) :
    Continuous (padicMatrixProjection p k (Fin n)) :=
  continuous_id.matrix_map (RHTower.fieldOnePadicInt_toZModPow_continuous p k)

/-- Every finite matrix has a p-adic lift, by lifting its entries. -/
theorem padicMatrixProjection_surjective (k n : ℕ) :
    Function.Surjective (padicMatrixProjection p k (Fin n)) := by
  intro A
  refine ⟨fun i j => RHTower.fieldOnePadicIntResidueRep p k (A i j), ?_⟩
  ext i j
  exact RHTower.fieldOnePadicIntResidueRep_spec p k (A i j)

/-- Finite residue conditions have exactly their finite uniform probability. -/
theorem padicMatrixHaar_residue_probability (k n : ℕ)
    (P : Matrix (Fin n) (Fin n) (ZMod (p ^ k)) → Prop) :
    (padicMatrixHaar p n).real {A | P (padicMatrixProjection p k (Fin n) A)} =
      (Nat.card {A : Matrix (Fin n) (Fin n) (ZMod (p ^ k)) // P A} : ℝ) /
        Nat.card (Matrix (Fin n) (Fin n) (ZMod (p ^ k))) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out : p.Prime).ne_zero⟩
  exact haar_finite_quotient_probability (padicMatrixHaar p n)
    (padicMatrixProjection p k (Fin n)).toAddMonoidHom
    (padicMatrixProjection_surjective p k n) (padicMatrixProjection_continuous p k n) P

#print axioms padicMatrixHaar_residue_probability

end GaloisForLFunctions.RepresentationLifting

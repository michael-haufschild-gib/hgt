import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryKernel

/-!
# Source-faithful interface to the classical Nevanlinna parametrization

Classical moment-problem references commonly use the Stieltjes-transform convention

`integral (z - x)⁻¹ dν(x) = (A(z) τ - C(z)) / (B(z) τ - D(z))`

with `A D - B C = 1`.  The carrier modules in this project use the Herglotz convention
`integral (x - z)⁻¹ dν(x)`, so the determinant-one matrix seen by the carrier is exactly

`(a,b,c,d) = (-A,C,B,-D)`.

This file makes that convention change a theorem.  Its external structure contains only the
classical output actually used downstream: the determinant identity, continuity of the lower
row, a weakly continuous family of N-extremal probability measures, exact denominator support,
and equality of every Hamburger moment.  All projective labels, measurability, barycenters, and
closed-simplex consequences are then supplied by the proved Lean kernel.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint
open scoped OnePoint Topology

noncomputable section

/-- The classical `A,C;B,D` Nevanlinna matrix convention used with the Stieltjes transform
`integral (z-x)⁻¹ dν(x)`. -/
structure ClassicalNevanlinnaMatrixData (X : Type*) where
  A : X → ℝ
  B : X → ℝ
  C : X → ℝ
  D : X → ℝ
  det_one : ∀ x, A x * D x - B x * C x = 1

namespace ClassicalNevanlinnaMatrixData

variable {X : Type*} (W : ClassicalNevanlinnaMatrixData X)

/-- The source denominator-zero set for a finite constant Pick parameter. -/
def finiteDenominatorFiber (tau : ℝ) : Set X :=
  {x | W.B x * tau - W.D x = 0}

/-- The source denominator-zero set for the constant parameter at infinity. -/
def infinityDenominatorFiber : Set X :=
  {x | W.B x = 0}

/-- The projective parameter selected by the source denominator row `[B:-D]`. -/
def projectiveLabel (x : X) : OnePoint ℝ :=
  if W.B x = 0 then ∞ else ((W.D x / W.B x : ℝ) : OnePoint ℝ)

/-- The finite-parameter Stieltjes fraction in the classical `(z-x)⁻¹` convention. -/
def stieltjesFraction (x : X) (tau : ℝ) : ℝ :=
  (W.A x * tau - W.C x) / (W.B x * tau - W.D x)

/-- Convert the source matrix to the determinant-one matrix for the carrier convention
`integral (x-z)⁻¹ dν(x)`. -/
def toCarrierMatrix : NevanlinnaMatrixData X where
  a := -W.A
  b := W.C
  c := W.B
  d := -W.D
  det_one := by
    intro x
    simpa only [Pi.neg_apply, neg_mul_neg, mul_comm] using W.det_one x

/-- The carrier fraction is the negative of the source Stieltjes fraction, exactly as dictated by
`(x-z)⁻¹ = -(z-x)⁻¹`. -/
theorem carrierFraction_eq_neg_stieltjesFraction (x : X) (tau : ℝ) :
    ((W.toCarrierMatrix.a x * tau + W.toCarrierMatrix.b x) /
        (W.toCarrierMatrix.c x * tau + W.toCarrierMatrix.d x)) =
      -W.stieltjesFraction x tau := by
  simp only [toCarrierMatrix, stieltjesFraction, Pi.neg_apply]
  ring

/-- The source finite denominator fiber is literally the carrier finite denominator fiber after
the convention conversion. -/
theorem toCarrierMatrix_finiteDenominatorFiber (tau : ℝ) :
    W.toCarrierMatrix.finiteDenominatorFiber tau = W.finiteDenominatorFiber tau := by
  ext x
  simp [NevanlinnaMatrixData.finiteDenominatorFiber, finiteDenominatorFiber,
    toCarrierMatrix, sub_eq_add_neg]

/-- The source infinity fiber is unchanged by the convention conversion. -/
theorem toCarrierMatrix_infinityDenominatorFiber :
    W.toCarrierMatrix.infinityDenominatorFiber = W.infinityDenominatorFiber := by
  rfl

/-- The source support label `D/B` is exactly the carrier label `-d/c`. -/
theorem toCarrierMatrix_projectiveLabel (x : X) :
    W.toCarrierMatrix.projectiveLabel x = W.projectiveLabel x := by
  simp [NevanlinnaMatrixData.projectiveLabel, projectiveLabel, toCarrierMatrix]

end ClassicalNevanlinnaMatrixData

/-- Minimal source-identical output of the classical N-extremal Nevanlinna theorem for the moment
sequence `s`.  In particular, no project-specific barycenter, label-recovery, simplex, density, or
atomlessness conclusion is included as an external hypothesis. -/
structure ClassicalNevanlinnaExtremalFamily (s : ℕ → ℝ) where
  matrix : ClassicalNevanlinnaMatrixData ℝ
  continuous_B : Continuous matrix.B
  continuous_D : Continuous matrix.D
  leaf : OnePoint ℝ → ProbabilityMeasure ℝ
  continuous_leaf : Continuous leaf
  finite_carried : ∀ tau : ℝ,
    (leaf tau : Measure ℝ) (matrix.finiteDenominatorFiber tau)ᶜ = 0
  infinity_carried :
    (leaf ∞ : Measure ℝ) matrix.infinityDenominatorFiberᶜ = 0
  leaf_moments : ∀ t, HasHamburgerMoments s (leaf t : Measure ℝ)

namespace ClassicalNevanlinnaExtremalFamily

variable {s : ℕ → ℝ} (F : ClassicalNevanlinnaExtremalFamily s)

/-- The complete verified adapter from the classical Berg--Valent/Akhiezer convention to the
projective Nevanlinna boundary kernel.  Weak continuity supplies Giry measurability internally. -/
def toBoundaryFamily : NevanlinnaBoundaryFamily s where
  matrix := F.matrix.toCarrierMatrix
  continuous_c := F.continuous_B
  continuous_d := F.continuous_D.neg
  leaf := F.leaf
  continuous_leaf := F.continuous_leaf
  finite_carried := by
    intro tau
    simpa only [F.matrix.toCarrierMatrix_finiteDenominatorFiber tau] using
      F.finite_carried tau
  infinity_carried := by
    simpa only [F.matrix.toCarrierMatrix_infinityDenominatorFiber] using
      F.infinity_carried
  leaf_moments := F.leaf_moments

@[simp]
theorem toBoundaryFamily_leaf (t : OnePoint ℝ) :
    F.toBoundaryFamily.leaf t = F.leaf t := rfl

@[simp]
theorem toBoundaryFamily_projectiveLabel (x : ℝ) :
    F.toBoundaryFamily.matrix.projectiveLabel x = F.matrix.projectiveLabel x :=
  F.matrix.toCarrierMatrix_projectiveLabel x

/-- Exact source-label recovery for every classical N-extremal leaf.  This is the first genuinely
new geometric consequence after the classical interface: the denominator parameter is recovered
as a measurable projective coordinate on the carrier line. -/
theorem map_projectiveLabel_leaf (t : OnePoint ℝ) :
    Measure.map F.matrix.projectiveLabel (F.leaf t : Measure ℝ) = Measure.dirac t := by
  rw [← funext F.toBoundaryFamily_projectiveLabel]
  exact F.toBoundaryFamily.map_projectiveLabel_leaf t

/-- The source-convention N-extremal family therefore generates the closed boundary simplex with
no additional analytic or measure-theoretic assumption. -/
theorem barycenter_isClosedEmbedding :
    Topology.IsClosedEmbedding F.toBoundaryFamily.barycenter :=
  F.toBoundaryFamily.barycenter_isClosedEmbedding

end ClassicalNevanlinnaExtremalFamily

end


end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.SelbergClass.MultipleStandardTwistGammaGeometry
import GaloisForLFunctions.SelbergClass.MultipleStandardTwistTensor

/-!
# Gamma geometry from multiple-standard-twist data

The affine linear part in Kaczorowski--Perelli's gamma-cleared divisor is the
degree-weighted coordinate functional `Σ d_ν s_ν`.  Its nonzeroness follows
from the actual positive-degree fields of `MultipleStandardTwistData`, so the
reciprocal-Gamma denominator needs no externally supplied nonzero proof.

The source's affine constant is kept explicit here.  Constructing the entire
gamma-cleared numerator remains the unformalized continuation theorem.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass

open GaloisForLFunctions.HTGeometry

/-- Degree-weighted coordinate linear functional occurring in the source's
Gamma divisor. -/
noncomputable def multipleStandardTwistDegreeLinear {N : ℕ}
    (D : MultipleStandardTwistData N) : (Fin N → ℂ) →L[ℂ] ℂ :=
  ∑ i, (((D.factors i).gammaData.degree : ℝ) : ℂ) • ContinuousLinearMap.proj i

theorem multipleStandardTwistDegreeLinear_apply {N : ℕ}
    (D : MultipleStandardTwistData N) (s : Fin N → ℂ) :
    multipleStandardTwistDegreeLinear D s =
      ∑ i, (((D.factors i).gammaData.degree : ℝ) : ℂ) * s i := by
  simp [multipleStandardTwistDegreeLinear]

/-- The source degree functional is nonzero because the input family has a
positive degree in every coordinate. -/
theorem multipleStandardTwistDegreeLinear_ne_zero {N : ℕ}
    (D : MultipleStandardTwistData N) : multipleStandardTwistDegreeLinear D ≠ 0 := by
  let i0 : Fin N := ⟨0, lt_of_lt_of_le (by norm_num) D.two_le_card⟩
  let e : Fin N → ℂ := fun j => if j = i0 then 1 else 0
  have heval : multipleStandardTwistDegreeLinear D e =
      (((D.factors i0).gammaData.degree : ℝ) : ℂ) := by
    rw [multipleStandardTwistDegreeLinear_apply]
    simp [e]
  intro hzero
  have hz : multipleStandardTwistDegreeLinear D e = 0 := by
    rw [hzero]
    rfl
  rw [heval] at hz
  exact (Complex.ofReal_ne_zero.mpr (ne_of_gt (D.degree_pos i0))) hz

/-- The reciprocal-Gamma denominator for the source degree functional is
intrinsically nonzero, for every affine constant. -/
theorem reciprocalGammaAffineEntire_ne_zero_of_multipleStandardTwistData
    {N : ℕ} (D : MultipleStandardTwistData N) (b : ℂ) :
    reciprocalGammaAffineEntire N (multipleStandardTwistDegreeLinear D) b ≠ 0 :=
  reciprocalGammaAffineEntire_ne_zero_of_linear_ne_zero
    (multipleStandardTwistDegreeLinear D) b (multipleStandardTwistDegreeLinear_ne_zero D)

/-- Concrete gamma-cleared quotient presentation attached to source data and
an explicitly constructed entire numerator.  This definition does not assert
that such a numerator comes from the multiple twist. -/
noncomputable def multipleStandardTwistGammaClearedPresentation {N : ℕ}
    (D : MultipleStandardTwistData N) (G : entireSubring (Fin N → ℂ)) (b : ℂ) :
    MeromorphicTensorPresentation N :=
  gammaClearedPresentation G (multipleStandardTwistDegreeLinear D) b
    (reciprocalGammaAffineEntire_ne_zero_of_multipleStandardTwistData D b)

/-- Candidate Gamma divisor of the source-data presentation is the expected
degree-weighted affine hyperplane union. -/
theorem multipleStandardTwistGammaClearedPresentation_candidatePolarSet
    {N : ℕ} (D : MultipleStandardTwistData N) (G : entireSubring (Fin N → ℂ)) (b : ℂ) :
    (multipleStandardTwistGammaClearedPresentation D G b).candidatePolarSet =
      gammaCandidatePolarSet (multipleStandardTwistDegreeLinear D) b := by
  exact gammaClearedPresentation_candidatePolarSet G
    (multipleStandardTwistDegreeLinear D) b
    (reciprocalGammaAffineEntire_ne_zero_of_multipleStandardTwistData D b)

end GaloisForLFunctions.SelbergClass

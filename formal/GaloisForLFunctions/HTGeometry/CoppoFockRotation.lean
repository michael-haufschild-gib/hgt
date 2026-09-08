import GaloisForLFunctions.HTGeometry.WickFockModel
import Mathlib.Tactic

/-!
# Collective rotation of the exact polynomial Fock Kerr interaction

The local normal-ordered Kerr operators of arXiv:2606.25061, Eq. (1), can be
rotated on the corpus's polynomial Fock domain without a Gaussian approximation.
The resulting cross-number coefficient is determined by an operator identity.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
abbrev CoppoFock := MvPolynomial Bool ℂ
abbrev CoppoFockEnd := Module.End ℂ CoppoFock

/-- The numerator of the orthogonally rotated sum of local Kerr interactions. -/
def coppoRotatedKerrNumerator : CoppoFockEnd :=
  (fockCre ℂ Bool false + fockCre ℂ Bool true) ^ 2 *
      (fockAnn ℂ Bool false + fockAnn ℂ Bool true) ^ 2 +
    (fockCre ℂ Bool false - fockCre ℂ Bool true) ^ 2 *
      (fockAnn ℂ Bool false - fockAnn ℂ Bool true) ^ 2

/-- Pair conversion and local quartics, grouped in normal order. -/
def coppoFockPairQuartic : CoppoFockEnd :=
  (fockCre ℂ Bool false ^ 2 + fockCre ℂ Bool true ^ 2) *
    (fockAnn ℂ Bool false ^ 2 + fockAnn ℂ Bool true ^ 2)

/-- The product of the two occupation operators, in normal order. -/
def coppoFockCrossNumber : CoppoFockEnd :=
  fockCre ℂ Bool false * fockCre ℂ Bool true *
    fockAnn ℂ Bool false * fockAnn ℂ Bool true

/-- Exact coefficient of the cross-number term under the collective rotation. -/
theorem coppoRotatedKerrNumerator_eq :
    coppoRotatedKerrNumerator = 2 • coppoFockPairQuartic + 8 • coppoFockCrossNumber := by
  apply LinearMap.ext
  intro p
  simp [coppoRotatedKerrNumerator, coppoFockPairQuartic, coppoFockCrossNumber,
    pow_two, Module.End.mul_apply, GaloisForLFunctions.pderiv_comm true false]
  ring

/-- Four times the interaction printed in Eq. (30), with the common Kerr strength removed. -/
def coppoPrintedCollectiveKerrNumerator : CoppoFockEnd :=
  2 • coppoFockPairQuartic + 4 • coppoFockCrossNumber

/-- The displayed Eq. (30) differs from the rotated local interaction by one cross-number term. -/
theorem coppoPrintedCollectiveKerr_defect :
    coppoRotatedKerrNumerator - coppoPrintedCollectiveKerrNumerator =
      4 • coppoFockCrossNumber := by
  rw [coppoRotatedKerrNumerator_eq, coppoPrintedCollectiveKerrNumerator]
  module

/-- The cross-number defect acts identically on the state with one excitation per mode. -/
theorem coppoFockCrossNumber_one_pair :
    coppoFockCrossNumber (X false * X true) = (X false * X true : CoppoFock) := by
  simp [coppoFockCrossNumber, Module.End.mul_apply]

/-- The coefficient discrepancy survives on the one-pair state. -/
theorem coppoPrintedCollectiveKerr_defect_one_pair :
    (coppoRotatedKerrNumerator - coppoPrintedCollectiveKerrNumerator)
      (X false * X true) = (4 : ℂ) • (X false * X true : CoppoFock) := by
  rw [coppoPrintedCollectiveKerr_defect]
  simp [coppoFockCrossNumber_one_pair, MvPolynomial.smul_eq_C_mul, map_ofNat]

/-- The two local number operators equal the normal-ordered cross-number operator. -/
theorem coppoFockCrossNumber_eq_number_product :
    coppoFockCrossNumber =
      (fockCre ℂ Bool false * fockAnn ℂ Bool false) *
        (fockCre ℂ Bool true * fockAnn ℂ Bool true) := by
  apply LinearMap.ext
  intro p
  simp [coppoFockCrossNumber, Module.End.mul_apply]

/-- The printed and rotated interactions are distinct operators on the actual Fock domain. -/
theorem coppoPrintedCollectiveKerr_ne_rotated :
    coppoRotatedKerrNumerator ≠ coppoPrintedCollectiveKerrNumerator := by
  intro h
  have hz : (4 : ℂ) • (X false * X true : CoppoFock) = 0 := by
    rw [← coppoPrintedCollectiveKerr_defect_one_pair, h, sub_self]
    rfl
  exact (smul_ne_zero (by norm_num : (4 : ℂ) ≠ 0)
    (mul_ne_zero (MvPolynomial.X_ne_zero false) (MvPolynomial.X_ne_zero true))) hz

end GaloisForLFunctions.HTGeometry

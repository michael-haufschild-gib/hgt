import GaloisForLFunctions.RHTower.RealSphericalComplementarySeries

/-!
# One-step complementary-series generator energies

For the explicit positive complementary-series form, this file computes the exact real energy of
one raising or lowering step from a spherical `K`-type.  These closed identities are the local
input for an analytic-vector estimate: repeated derived actions shift `K`-type support by one at
a time, while the recurrence controls each shifted coefficient.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Exact complementary-form energy of one raising step from `K`-type `m`. -/
theorem sphericalPrincipalE_single_complementary_energy (s : ℝ) (hs : |s| < 1) (m : ℤ) :
    (sphericalComplementaryHermitianForm s
      (sphericalPrincipalE (s : ℂ) (Finsupp.single m 1))
      (sphericalPrincipalE (s : ℂ) (Finsupp.single m 1))).re =
        ((((2 : ℤ) * m + 1 : ℤ) : ℝ)^2 - s^2) / 4 * complementaryKTypeWeight s m := by
  rw [sphericalPrincipalE_single]
  unfold sphericalComplementaryHermitianForm
  rw [diagonalKTypeHermitianForm_single]
  simp only [if_pos, mul_one]
  have hrec := complementaryKTypeWeight_succ_recurrence s hs m
  norm_num [Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.mul_im,
    Complex.div_im, Complex.sub_im] at ⊢
  push_cast at hrec
  linear_combination ((2 * (m : ℝ) + 1 - s) / 4) * hrec

/-- Exact complementary-form energy of one lowering step from `K`-type `m`. -/
theorem sphericalPrincipalF_single_complementary_energy (s : ℝ) (hs : |s| < 1) (m : ℤ) :
    (sphericalComplementaryHermitianForm s
      (sphericalPrincipalF (s : ℂ) (Finsupp.single m 1))
      (sphericalPrincipalF (s : ℂ) (Finsupp.single m 1))).re =
        ((((2 : ℤ) * m - 1 : ℤ) : ℝ)^2 - s^2) / 4 * complementaryKTypeWeight s m := by
  rw [sphericalPrincipalF_single]
  unfold sphericalComplementaryHermitianForm
  rw [diagonalKTypeHermitianForm_single]
  simp only [if_pos, mul_one]
  have hrec := complementaryKTypeWeight_succ_recurrence s hs (m - 1)
  have hrec' : (2 * (m : ℝ) - 1 - s) * complementaryKTypeWeight s m =
      (2 * (m : ℝ) - 1 + s) * complementaryKTypeWeight s (m - 1) := by
    norm_num at hrec
    convert hrec using 1 <;> ring_nf
  norm_num [Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.mul_im,
    Complex.div_im, Complex.sub_im] at ⊢
  linear_combination -((2 * (m : ℝ) - 1 + s) / 4) * hrec'

end

end GaloisForLFunctions.RHTower

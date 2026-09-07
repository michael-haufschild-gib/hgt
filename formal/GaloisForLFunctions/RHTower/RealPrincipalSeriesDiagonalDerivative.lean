import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactHarishChandra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Positive-diagonal derivative in the real compact principal series

This file constructs the positive diagonal one-parameter subgroup and differentiates its actual
compact-picture action at the identity of `K`.  The calculation fixes the normalization: Borel
exponent `s - 1` gives the sum of the raising and lowering coefficients in the spherical
Harish-Chandra model.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Positive diagonal one-parameter subgroup, regarded as an element of the upper Borel. -/
def realPositiveDiagonalBorel (t : ℝ) : realUpperBorel :=
  ⟨⟨!![Real.exp t, 0; 0, Real.exp (-t)], by
      simp [Matrix.det_fin_two, Real.exp_neg]⟩, by simp⟩

@[simp]
theorem realPositiveDiagonalBorel_zero : realPositiveDiagonalBorel 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realPositiveDiagonalBorel]

theorem realPositiveDiagonalBorel_add (t u : ℝ) :
    realPositiveDiagonalBorel (t + u) =
      realPositiveDiagonalBorel t * realPositiveDiagonalBorel u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realPositiveDiagonalBorel, Matrix.mul_apply, Fin.sum_univ_two,
      Real.exp_add]
  all_goals ring

@[simp]
theorem realPositiveDiagonalBorel_character (σ t : ℝ) :
    realUpperBorelRpowCharacter σ (realPositiveDiagonalBorel t) =
      (Real.exp (t * σ) : ℂ) := by
  change ((|Real.exp t| ^ σ : ℝ) : ℂ) = _
  rw [abs_of_pos (Real.exp_pos t), ← Real.exp_mul]

@[simp]
theorem compactRealPrincipalSeries_positiveDiagonal_one_apply
    (σ t : ℝ) (φ : realCompactPictureSpace σ) :
    ((compactRealPrincipalSeries σ (realPositiveDiagonalBorel t : SL2R)) φ).1 1 =
      (Real.exp (t * σ) : ℂ) * φ.1 1 := by
  rw [compactRealPrincipalSeries_factor_apply σ
    (realPositiveDiagonalBorel t : SL2R) 1 φ (realPositiveDiagonalBorel t) 1]
  · rw [realPositiveDiagonalBorel_character]
  · simp

/-- At the identity of `K`, the positive-diagonal derivative is multiplication by the inducing
exponent. -/
theorem hasDerivAt_compactRealPrincipalSeries_positiveDiagonal_one
    (σ : ℝ) (φ : realCompactPictureSpace σ) :
    HasDerivAt
      (fun t : ℝ =>
        ((compactRealPrincipalSeries σ (realPositiveDiagonalBorel t : SL2R)) φ).1 1)
      ((σ : ℂ) * φ.1 1) 0 := by
  have hr : HasDerivAt (fun t : ℝ => Real.exp (t * σ)) σ 0 := by
    convert! (Real.hasDerivAt_exp (0 * σ)).comp 0
      ((hasDerivAt_id 0).mul_const σ) using 1
    all_goals norm_num
  have hc : HasDerivAt (fun t : ℝ => (Real.exp (t * σ) : ℂ)) (σ : ℂ) 0 :=
    hr.ofReal_comp
  simpa only [compactRealPrincipalSeries_positiveDiagonal_one_apply] using
    hc.mul_const (φ.1 1)

/-- Borel exponent `s - 1` matches the total `E + F` coefficient of every spherical K-type at
the identity.  This is the normalization check for the compact Harish-Chandra embedding. -/
theorem positiveDiagonal_matches_spherical_E_add_F_at_one
    (s : ℝ) (m : ℤ) (z : ℂ) :
    HasDerivAt
      (fun t : ℝ =>
        ((compactRealPrincipalSeries (s - 1)
          (realPositiveDiagonalBorel t : SL2R))
          (realCompactKFiniteEmbedding (s - 1) (Finsupp.single m z))).1 1)
      ((realCompactKFiniteEmbedding (s - 1)
        ((sphericalPrincipalE (s : ℂ) + sphericalPrincipalF (s : ℂ))
          (Finsupp.single m z))).1 1) 0 := by
  have h := hasDerivAt_compactRealPrincipalSeries_positiveDiagonal_one (s - 1)
    (realCompactKFiniteEmbedding (s - 1) (Finsupp.single m z))
  convert h using 1
  simp only [LinearMap.add_apply, sphericalPrincipalE_single,
    sphericalPrincipalF_single, map_add, realCompactKFiniteEmbedding_single]
  simp only [AddMemClass.coe_add, Pi.add_apply, SetLike.val_smul,
    Pi.smul_apply, smul_eq_mul, realCompactKType_apply, map_one, mul_one]
  push_cast
  ring

/-- In the normalized compact Harish-Chandra subspace, the positive-diagonal derivative agrees
with transported `E + F` at the identity of `K` on every basis K-type. -/
theorem compactPositiveDiagonal_hasDerivAt_eq_E_add_F_single_at_one
    (s : ℝ) (m : ℤ) (z : ℂ) :
    HasDerivAt
      (fun t : ℝ =>
        ((compactRealPrincipalSeries (s - 1)
          (realPositiveDiagonalBorel t : SL2R))
          (sphericalModelCompactKFiniteEquiv s (Finsupp.single m z))).1 1)
      (((compactSphericalPrincipalE s + compactSphericalPrincipalF s)
        (sphericalModelCompactKFiniteEquiv s (Finsupp.single m z))).1.1 1) 0 := by
  rw [sphericalModelCompactKFiniteEquiv_apply_coe]
  convert positiveDiagonal_matches_spherical_E_add_F_at_one s m z using 1
  simp only [LinearMap.add_apply, compactSphericalPrincipalE_equiv_apply,
    compactSphericalPrincipalF_equiv_apply, ← map_add,
    sphericalModelCompactKFiniteEquiv_apply_coe]

end
end GaloisForLFunctions.RHTower

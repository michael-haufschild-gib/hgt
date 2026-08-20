/-
# Chen--Gupta--Li infinite Mellin detector identity

This module proves source equation (12.1)'s initial Mellin identity on its
safe line `Re(z)=2`: the full exponentially smoothed detector product is the
inverse Mellin transform of `Γ(z) M_X(s+z,χ)L(s+z,χ)`. The contour shift and
residue calculation are intentionally separate.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiTailCoefficientBounds

open Complex LSeries DirichletCharacter Filter MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Full detector-product coefficients shifted by a certified point on or to
the right of the critical line. -/
def cglShiftedDetectorProductCoefficient (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (n : ℕ) : ℂ :=
  LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) n *
    (n : ℂ) ^ (-s.1)

theorem cglShiftedDetectorProductCoefficient_zero (X q : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) :
    cglShiftedDetectorProductCoefficient X q χ s 0 = 0 := by
  simp [cglShiftedDetectorProductCoefficient, LSeries.convolution_map_zero]

/-- A single positive constant bounds the shifted full detector coefficients,
uniformly in every cutoff, modulus, character, and certified point. -/
theorem exists_cglShiftedDetectorProductCoefficient_uniformBound :
    ∃ C : ℝ, 0 < C ∧ ∀ X q : ℕ, ∀ χ : DirichletCharacter ℂ (q + 1),
      ∀ s : CGLRightHalfPlanePoint, ∀ n : ℕ,
        ‖cglShiftedDetectorProductCoefficient X q χ s n‖ ≤ C := by
  obtain ⟨C, hC, hdiv⟩ := card_divisors_le_const_mul_rpow (ε := (1 / 4 : ℝ)) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro X q χ s n
  by_cases hn : n = 0
  · subst n
    simpa [cglShiftedDetectorProductCoefficient, LSeries.convolution_map_zero] using hC.le
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  unfold cglShiftedDetectorProductCoefficient
  rw [cglTruncatedMobiusTwist_convolution_character_eq_mobiusCoefficient_all,
    norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re]
  calc
    ‖(zeroDetectionMobiusCoefficient X n : ℂ)‖ * ‖χ n‖ * (n : ℝ) ^ (-s.1.re) ≤
        (n.divisors.card : ℝ) * (n : ℝ) ^ (-s.1.re) := by
      calc
        ‖(zeroDetectionMobiusCoefficient X n : ℂ)‖ * ‖χ n‖ * (n : ℝ) ^ (-s.1.re) ≤
            ((n.divisors.card : ℝ) * 1) * (n : ℝ) ^ (-s.1.re) := by
          gcongr
          exact norm_zeroDetectionMobiusCoefficient_le_card_divisors X n
          exact χ.norm_le_one n
        _ = (n.divisors.card : ℝ) * (n : ℝ) ^ (-s.1.re) := by ring
    _ ≤ (C * (n : ℝ) ^ (1 / 4 : ℝ)) * (n : ℝ) ^ (-s.1.re) :=
      mul_le_mul_of_nonneg_right (hdiv n hnpos) (Real.rpow_nonneg hnR.le _)
    _ = C * ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-s.1.re)) := by ring
    _ = C * (n : ℝ) ^ ((1 / 4 : ℝ) + (-s.1.re)) := by
      rw [← Real.rpow_add hnR]
    _ ≤ C * 1 := by
      gcongr
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (Nat.succ_le_iff.mpr hnpos)
      · linarith [s.2]
    _ = C := by ring

/-- Twisting coefficients by `n^{-s}` shifts their L-series argument exactly. -/
theorem LSeries_cglShiftedDetectorProductCoefficient_eq_shiftedConvolution
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (z : ℂ) :
    LSeries (cglShiftedDetectorProductCoefficient X q χ s) z =
      LSeries (LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ)
        (fun m : ℕ => χ m)) (s.1 + z) := by
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_zero]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  unfold cglShiftedDetectorProductCoefficient
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc
    (LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) n *
        (n : ℂ) ^ (-s.1)) / (n : ℂ) ^ z =
        LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) n *
          ((n : ℂ) ^ (-s.1) * (n : ℂ) ^ (-z)) := by
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
      ring
    _ = LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) n *
          (n : ℂ) ^ ((-s.1) + (-z)) := by
      rw [Complex.cpow_add _ _ hnC]
    _ = LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) n *
          (n : ℂ) ^ (-(s.1 + z)) := by
      congr 2
      ring
    _ = LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) n /
          (n : ℂ) ^ (s.1 + z) := by
      rw [Complex.cpow_neg]
      ring

/-- On inversion line `Re(z)=2`, the shifted detector L-series is exactly the
finite Möbius polynomial times the analytically continued Dirichlet L-function. -/
theorem cglShiftedDetectorProductCoefficient_initialLine_LSeries
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (t : ℝ) :
    LSeries (cglShiftedDetectorProductCoefficient X q χ s)
      ((2 : ℂ) + (t : ℂ) * Complex.I) =
      zeroDetectionMobiusPolynomial X (q + 1) χ (s.1 + ((2 : ℂ) + (t : ℂ) * Complex.I)) *
        DirichletCharacter.LFunction χ (s.1 + ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  let w : CGLAbsoluteConvergencePoint :=
    ⟨s.1 + ((2 : ℂ) + (t : ℂ) * Complex.I), by
      rw [Complex.add_re]
      norm_num
      linarith [s.2]⟩
  rw [LSeries_cglShiftedDetectorProductCoefficient_eq_shiftedConvolution]
  simpa [w] using
    (zeroDetectionMobiusPolynomial_mul_lfunction_eq_convolutionLSeries X q χ w).symm

/-- **Initial infinite Mellin detector identity.** At the positive smoothing
scale `(Y+1)⁻¹`, the full exponentially smoothed detector product is exactly
the inverse Mellin transform on `Re(z)=2` of
`Γ(z)M_X(s+z,χ)L(s+z,χ)`. -/
theorem cglDetectorProduct_mellin_initialLine_identity (X q Y : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) :
    mellinInv 2 (fun z => Complex.Gamma z *
      (zeroDetectionMobiusPolynomial X (q + 1) χ (s.1 + z) *
        DirichletCharacter.LFunction χ (s.1 + z))) ((Y + 1 : ℕ) : ℝ)⁻¹ =
      coeffLaplaceProfile (cglShiftedDetectorProductCoefficient X q χ s) ((Y + 1 : ℕ) : ℝ)⁻¹ := by
  obtain ⟨C, hC, hbound⟩ := exists_cglShiftedDetectorProductCoefficient_uniformBound
  have hx : 0 < ((Y + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hbase := RHTower.Sieve.mellinInv_two_gamma_mul_LSeries_eq_coeffLaplaceProfile_of_bound
    hC (hbound X q χ s) (cglShiftedDetectorProductCoefficient_zero X q χ s) hx
  calc
    mellinInv 2 (fun z => Complex.Gamma z *
        (zeroDetectionMobiusPolynomial X (q + 1) χ (s.1 + z) *
          DirichletCharacter.LFunction χ (s.1 + z))) ((Y + 1 : ℕ) : ℝ)⁻¹ =
        mellinInv 2 (fun z => Complex.Gamma z *
          LSeries (cglShiftedDetectorProductCoefficient X q χ s) z) ((Y + 1 : ℕ) : ℝ)⁻¹ := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp
        rw [cglShiftedDetectorProductCoefficient_initialLine_LSeries]
    _ = coeffLaplaceProfile (cglShiftedDetectorProductCoefficient X q χ s)
        ((Y + 1 : ℕ) : ℝ)⁻¹ := hbase

end RHTower

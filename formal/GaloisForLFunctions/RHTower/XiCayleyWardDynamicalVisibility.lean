import GaloisForLFunctions.HTGeometry.CayleyDefectDynamicalVisibility
import GaloisForLFunctions.RHTower.WCoordinate
import GaloisForLFunctions.RHTower.XiWardEndpointSourceIndex

/-!
# Cayley dynamics of the source-weighted Xi Ward defect

Functional-equation reflection is inversion in the Li coordinate `w(ρ) = 1 - ρ⁻¹`.  The
degree-one reflected Cayley defect `2 - w - w⁻¹` is exactly the endpoint cross charge which marks
the source-weighted `8π` Ward index.

On strict-right Xi zeros the Cayley radius is strictly below one.  Its inverse powers therefore
turn every positive endpoint mark into a noncancelling exponential signal.  The resulting complete
moment tower is absolutely convergent at every order, starts at the weighted Ward mass, and is
bounded exactly when RH holds.
-/

open Complex Real
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Reflected degree-`n` Cayley defect. -/
def cayleyReflectedPairDefect (z : ℂ) (n : ℕ) : ℂ :=
  2 - wCoordinate z ^ n - (wCoordinate z)⁻¹ ^ n

/-- The degree-one reflected Cayley defect is the reciprocal FE-pair kernel. -/
theorem cayleyReflectedPairDefect_one
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    cayleyReflectedPairDefect z 1 = (z * (1 - z))⁻¹ := by
  rw [cayleyReflectedPairDefect, pow_one, pow_one]
  unfold wCoordinate
  field_simp
  ring

/-- The Li Cayley node of one strict-right upper Xi divisor copy. -/
def xiWardLiCayleyNode (q : XiRightUpperZeroCopy) : ℂ :=
  wCoordinate (q.1.1.1 : ℂ)

private theorem xiRightUpper_rho_ne_zero (q : XiRightUpperZeroCopy) :
    (q.1.1.1 : ℂ) ≠ 0 := by
  intro h
  have him := xi_divisor_support_im_ne_zero q.1.1.1
  apply him
  simpa [h]

private theorem xiRightUpper_rho_ne_one (q : XiRightUpperZeroCopy) :
    (q.1.1.1 : ℂ) ≠ 1 := by
  intro h
  have him := xi_divisor_support_im_ne_zero q.1.1.1
  apply him
  simpa [h]

/-- The endpoint source mark is exactly the real degree-one Li pair defect. -/
theorem xiEndpointWardPairWeight_eq_re_cayleyReflectedPairDefect_one
    (q : XiRightUpperZeroCopy) :
    xiEndpointWardPairWeight q =
      (cayleyReflectedPairDefect (q.1.1.1 : ℂ) 1).re := by
  rw [cayleyReflectedPairDefect_one
    (xiRightUpper_rho_ne_zero q) (xiRightUpper_rho_ne_one q)]
  rw [xiEndpointWardPairWeight, xiEndpointCrossCharge,
    xiRawReciprocalCoordinate, xiRawReciprocalCoordinate]
  have hline : ((xiZeroCopyLineConjEquiv q.1.1).1 : ℂ) =
      1 - (starRingEnd ℂ) (q.1.1.1 : ℂ) := rfl
  rw [hline, map_inv₀, map_sub, map_one]
  congr 1
  field_simp

/-- The strict-right Cayley node has radius below one. -/
theorem norm_xiWardLiCayleyNode_lt_one (q : XiRightUpperZeroCopy) :
    ‖xiWardLiCayleyNode q‖ < 1 := by
  have hρ0 := xiRightUpper_rho_ne_zero q
  have hden : 0 < Complex.normSq (q.1.1.1 : ℂ) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1.1.1)]
  have hright : 1 / 2 < (q.1.1.1 : ℂ).re := by
    have h := xiRightCenteredZero_re_pos q.1
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at h
    simp only [Complex.sub_re] at h
    norm_num at h
    linarith
  have hfrac :
      (1 - 2 * (q.1.1.1 : ℂ).re) /
          Complex.normSq (q.1.1.1 : ℂ) < 0 :=
    div_neg_of_neg_of_pos (by linarith) hden
  have hsq := wCoordinate_normSq_sub_one (q.1.1.1 : ℂ) hρ0
  have hnormSq : Complex.normSq (xiWardLiCayleyNode q) < 1 := by
    dsimp only [xiWardLiCayleyNode]
    linarith
  rw [← Complex.sq_norm] at hnormSq
  nlinarith [norm_nonneg (xiWardLiCayleyNode q)]

/-- The certified Xi height gap keeps every strict-right Cayley node uniformly outside radius
`1/2`. -/
theorem one_half_lt_norm_xiWardLiCayleyNode (q : XiRightUpperZeroCopy) :
    1 / 2 < ‖xiWardLiCayleyNode q‖ := by
  have hheight :=
    xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq
      q.1.1 (xiRightUpperZeroCopy_offLine q)
  have hρnorm : 2 < ‖(q.1.1.1 : ℂ)‖ := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [norm_nonneg (q.1.1.1 : ℂ)]
  have hinv : ‖((q.1.1.1 : ℂ)⁻¹)‖ < 1 / 2 := by
    rw [norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr (xiRightUpper_rho_ne_zero q))
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by norm_num at hρnorm ⊢; exact hρnorm)
  have hreverse := norm_sub_norm_le (1 : ℂ) ((q.1.1.1 : ℂ)⁻¹)
  change ‖(1 : ℂ)‖ - ‖((q.1.1.1 : ℂ)⁻¹)‖ ≤
      ‖xiWardLiCayleyNode q‖ at hreverse
  norm_num at hreverse
  linarith

theorem xiWardLiCayleyNode_ne_zero (q : XiRightUpperZeroCopy) :
    xiWardLiCayleyNode q ≠ 0 :=
  norm_pos_iff.mp ((by linarith [one_half_lt_norm_xiWardLiCayleyNode q]) :
    0 < ‖xiWardLiCayleyNode q‖)

/-- Every source-weighted inverse-radial moment is absolutely summable. -/
theorem summable_xiEndpointWardPairWeight_mul_inv_norm_cayley_pow
    (n : ℕ) :
    Summable (fun q : XiRightUpperZeroCopy =>
      xiEndpointWardPairWeight q * ‖xiWardLiCayleyNode q‖⁻¹ ^ n) := by
  apply Summable.of_norm_bounded
      (summable_xiEndpointWardPairWeight.mul_left ((2 : ℝ) ^ n))
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (xiEndpointWardPairWeight_pos q).le
      (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _))]
  have hinv : ‖xiWardLiCayleyNode q‖⁻¹ ≤ (2 : ℝ) := by
    exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith [one_half_lt_norm_xiWardLiCayleyNode q] :
        0 < ‖xiWardLiCayleyNode q‖)).mpr
      (one_half_lt_norm_xiWardLiCayleyNode q).le
  have hpow := pow_le_pow_left₀
    (inv_nonneg.mpr (norm_nonneg (xiWardLiCayleyNode q))) hinv n
  calc
    xiEndpointWardPairWeight q * ‖xiWardLiCayleyNode q‖⁻¹ ^ n ≤
        xiEndpointWardPairWeight q * 2 ^ n :=
      mul_le_mul_of_nonneg_left hpow (xiEndpointWardPairWeight_pos q).le
    _ = 2 ^ n * xiEndpointWardPairWeight q := by ring

/-- Source-weighted radial Cayley visibility at observation order `n`. -/
def xiCayleyWardRadialVisibility (n : ℕ) : ℝ :=
  HTGeometry.inverseRadialMoment
    xiEndpointWardPairWeight xiWardLiCayleyNode n

/-- Time zero of the radial visibility tower is exactly the source-weighted Ward mass. -/
theorem xiEndpointWeightedWardIndex_eq_eightPi_mul_cayleyVisibility_zero :
    xiEndpointWeightedWardIndex =
      (8 * π) * xiCayleyWardRadialVisibility 0 := by
  rw [xiEndpointWeightedWardIndex, xiCayleyWardRadialVisibility,
    HTGeometry.inverseRadialMoment_zero]

/-- If RH is false, the actual Xi radial visibility tower has a positive exponential lower bound
at every order. -/
theorem exists_exponential_lowerBound_xiCayleyWardRadialVisibility
    (hnot : ¬RiemannHypothesis) :
    ∃ m c : ℝ, 0 < m ∧ 1 < c ∧
      ∀ n : ℕ, m * c ^ n ≤ xiCayleyWardRadialVisibility n := by
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_of_not_riemannHypothesis hnot
  exact HTGeometry.exists_exponential_lowerBound_inverseRadialMoment
    xiEndpointWardPairWeight xiWardLiCayleyNode
    xiEndpointWardPairWeight_pos xiWardLiCayleyNode_ne_zero
    norm_xiWardLiCayleyNode_lt_one
    summable_xiEndpointWardPairWeight_mul_inv_norm_cayley_pow q

end

end RHTower

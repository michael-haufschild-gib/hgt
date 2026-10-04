import GaloisForLFunctions.RHTower.SoninGammaClockEndpoint
import GaloisForLFunctions.RHTower.SoninPrimePolarFullResponse
import GaloisForLFunctions.RHTower.SoninPrimePowerRegularization

/-!
# The literal finite Gamma remainder operator

The forced homogeneous principal term remains separate. The remainder is
constructed by its strong integral on physical L2. Its exact ground action,
Fourier/reflection symmetry, self-adjointness and all-degree positive energy
defect are derived from that integral, with no commutation assumptions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower
local notation "Op" => (SoninL2 →L[ℂ] SoninL2)

/-- The complete symmetric logarithmic dilation difference. -/
def gammaClockDifferenceOperator (u : ℝ) : Op :=
  dilationCLM (Real.exp u) (Real.exp_pos u) +
    dilationCLM (Real.exp (-u)) (Real.exp_pos (-u)) - (2:ℂ) • (1:Op)

private theorem difference_apply (u : ℝ) (f : SoninL2) :
    gammaClockDifferenceOperator u f =
      rayDilate (Real.exp u) f + rayDilate (Real.exp (-u)) f - (2:ℂ) • f := by
  simp only [gammaClockDifferenceOperator, sub_apply,
    add_apply, smul_apply,
    one_apply_eq_self, rayDilate_of_pos (Real.exp_pos _), dilationCLM_apply]

private theorem difference_continuous (f : SoninL2) :
    Continuous (fun u => gammaClockDifferenceOperator u f) := by
  simp only [difference_apply]
  exact ((continuous_dilationOrbit f).add
    ((continuous_dilationOrbit f).comp continuous_neg)).sub continuous_const

private theorem difference_norm (u : ℝ) (f : SoninL2) :
    ‖gammaClockDifferenceOperator u f‖ ≤ 4*‖f‖ := by
  rw [difference_apply]
  calc
    _ ≤ ‖rayDilate (Real.exp u) f + rayDilate (Real.exp (-u)) f‖ + ‖(2:ℂ) • f‖ := norm_sub_le _ _
    _ ≤ (‖rayDilate (Real.exp u) f‖ + ‖rayDilate (Real.exp (-u)) f‖) + ‖(2:ℂ) • f‖ :=
      by linarith [norm_add_le (rayDilate (Real.exp u) f) (rayDilate (Real.exp (-u)) f)]
    _ = _ := by rw [norm_rayDilate (Real.exp_pos _), norm_rayDilate (Real.exp_pos _), norm_smul]; norm_num; ring

private theorem remainder_continuous {ε R : ℝ} (hε : 0 < ε) :
    ContinuousOn gammaClockRemainderDensity (Icc ε R) := by
  intro u hu
  have hu0 : 0 < u := hε.trans_le hu.1
  have hden : Real.exp u - Real.exp (-u) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
  unfold gammaClockRemainderDensity ccmPublishedArchimedeanDensity
  apply ContinuousAt.continuousWithinAt
  have h : ContinuousAt (fun t : ℝ => Real.exp (t/2)/(Real.exp t-Real.exp (-t))) u :=
    (by fun_prop : ContinuousAt (fun t : ℝ => Real.exp (t/2)) u).div (by fun_prop) hden
  have hd : 2*u^2 ≠ 0 := by positivity
  exact (h.div continuousAt_id hu0.ne').sub (by fun_prop)

private theorem remainder_integrable (ε R : ℝ) (hε : 0 < ε) (f : SoninL2) :
    Integrable (fun u => (gammaClockRemainderDensity u:ℂ) • gammaClockDifferenceOperator u f)
      (volume.restrict (Icc ε R)) :=
  ((Complex.continuous_ofReal.comp_continuousOn (remainder_continuous hε)).smul
    (difference_continuous f).continuousOn).integrableOn_Icc

/-- Actual finite Gamma remainder, defined by its full strong integral. -/
def gammaClockRemainderOperator (ε R : ℝ) (hε : 0 < ε) : Op :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ u in Icc ε R,
        (gammaClockRemainderDensity u:ℂ) • gammaClockDifferenceOperator u f
      map_add' := by
        intro f g
        rw [← integral_add (remainder_integrable ε R hε f) (remainder_integrable ε R hε g)]
        apply integral_congr_ae
        filter_upwards [] with u
        rw [map_add, smul_add]
      map_smul' := by
        intro c f
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [] with u
        simp only [map_smul, smul_smul, RingHom.id_apply]
        rw [mul_comm] }
    (4 * ∫ u in Icc ε R, ‖(gammaClockRemainderDensity u:ℂ)‖) (fun f => by
      have hd : Integrable (fun u => ‖(gammaClockRemainderDensity u:ℂ)‖)
          (volume.restrict (Icc ε R)) :=
        ((Complex.continuous_ofReal.comp_continuousOn (remainder_continuous hε)).norm).integrableOn_Icc
      calc
        _ ≤ ∫ u in Icc ε R, ‖(gammaClockRemainderDensity u:ℂ) • gammaClockDifferenceOperator u f‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ u in Icc ε R, ‖(gammaClockRemainderDensity u:ℂ)‖ * (4*‖f‖) := by
          apply integral_mono_ae (remainder_integrable ε R hε f).norm (hd.mul_const _)
          filter_upwards [] with u
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (difference_norm u f) (norm_nonneg _)
        _ = _ := by rw [integral_mul_const]; ring)

/-- Literal finite remainder action; no operator-norm integral is postulated. -/
theorem gammaClockRemainderOperator_apply (ε R : ℝ) (hε : 0 < ε) (f : SoninL2) :
    gammaClockRemainderOperator ε R hε f =
      ∫ u in Icc ε R, (gammaClockRemainderDensity u:ℂ) • gammaClockDifferenceOperator u f := rfl

private theorem difference_ground (a u : ℝ) :
    gammaClockDifferenceOperator u (soninCutoffMonomial a 0) = gammaGroundDifference a u := by
  rw [difference_apply]
  unfold gammaGroundDifference soninGroundEntry
  simp only [zero_div, neg_zero, Real.exp_zero, Complex.ofReal_one, one_smul]
  have h : rayDilate 1 (soninCutoffMonomial a 0) = soninCutoffMonomial a 0 := by
    rw [rayDilate_of_pos zero_lt_one]
    change dilationCLM 1 zero_lt_one _ = _
    rw [dilationCLM_one, one_apply_eq_self]
  rw [h]

/-- The bounded finite operator retains exactly the principal/remainder split. -/
theorem gammaClockRemainderOperator_ground (a ε R : ℝ) (hε : 0 < ε) :
    gammaClockRemainderOperator ε R hε (soninCutoffMonomial a 0) =
      gammaGroundTruncated a ε R-gammaHomogeneousGroundTruncated a ε R := by
  rw [gammaGroundTruncated_sub_homogeneous a ε R hε, gammaClockRemainderOperator_apply]
  simp only [difference_ground]

private theorem remainder_commutes (L : Op)
    (hL : ∀ t f, L (rayDilate (Real.exp t) f) = rayDilate (Real.exp t) (L f))
    (ε R : ℝ) (hε : 0 < ε) (f : SoninL2) :
    L (gammaClockRemainderOperator ε R hε f) = gammaClockRemainderOperator ε R hε (L f) := by
  rw [gammaClockRemainderOperator_apply, gammaClockRemainderOperator_apply,
    ← L.integral_comp_comm (remainder_integrable ε R hε f)]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [map_smul, difference_apply, difference_apply, map_sub, map_add, map_smul, hL, hL]

/-- Exact monomial transfer commutation for the literal Gamma remainder. -/
theorem gammaClockRemainderOperator_transfer (ε R : ℝ) (hε : 0 < ε) (n : ℕ) (f : SoninL2) :
    soninMonomialTransfer n (gammaClockRemainderOperator ε R hε f) =
      gammaClockRemainderOperator ε R hε (soninMonomialTransfer n f) :=
  remainder_commutes _ (soninMonomialTransfer_dilation n) ε R hε f

/-- Exact parity commutation for the literal Gamma remainder. -/
theorem gammaClockRemainderOperator_parity (ε R : ℝ) (hε : 0 < ε) (n : ℕ) (f : SoninL2) :
    soninParityMultiplier n (gammaClockRemainderOperator ε R hε f) =
      gammaClockRemainderOperator ε R hε (soninParityMultiplier n f) := by
  apply remainder_commutes
  intro t g
  simp only [rayDilate_of_pos (Real.exp_pos _)]
  exact soninParityMultiplier_dilation n _ (Real.exp_pos _) g

private theorem fourier_log_dilation (t : ℝ) (f : SoninL2) :
    fourierUnitary (rayDilate (Real.exp t) f) =
      rayDilate (Real.exp (-t)) (fourierUnitary f) := by
  rw [rayDilate_of_pos (Real.exp_pos _), rayDilate_of_pos (Real.exp_pos _), fourierUnitary_dilation]
  simp only [Real.exp_neg]

/-- Symmetry of the actual Gamma integrand gives exact Fourier commutation. -/
theorem fourier_gammaClockRemainderOperator (ε R : ℝ) (hε : 0 < ε) (f : SoninL2) :
    fourierUnitary (gammaClockRemainderOperator ε R hε f) =
      gammaClockRemainderOperator ε R hε (fourierUnitary f) := by
  let L : Op := fourierUnitary.toLinearIsometry.toContinuousLinearMap
  change L (gammaClockRemainderOperator ε R hε f) = _
  rw [gammaClockRemainderOperator_apply, gammaClockRemainderOperator_apply,
    ← L.integral_comp_comm (remainder_integrable ε R hε f)]
  apply integral_congr_ae
  filter_upwards [] with u
  change fourierUnitary ((gammaClockRemainderDensity u:ℂ) • gammaClockDifferenceOperator u f) = _
  rw [map_smul, difference_apply, difference_apply, map_sub, map_add, map_smul,
    fourier_log_dilation, fourier_log_dilation, neg_neg, add_comm]

/-- Reflection preserves the complete finite Gamma remainder. -/
theorem reflection_gammaClockRemainderOperator (ε R : ℝ) (hε : 0 < ε) (f : SoninL2) :
    l2Reflection (gammaClockRemainderOperator ε R hε f) =
      gammaClockRemainderOperator ε R hε (l2Reflection f) := by
  apply remainder_commutes
  intro t g
  rw [rayDilate_of_pos (Real.exp_pos _), rayDilate_of_pos (Real.exp_pos _)]
  exact l2Reflection_dilation _ _ g

private theorem inner_log_dilation (t : ℝ) (f g : SoninL2) :
    inner ℂ (rayDilate (Real.exp t) f) g = inner ℂ f (rayDilate (Real.exp (-t)) g) := by
  rw [rayDilate_of_pos (Real.exp_pos _), rayDilate_of_pos (Real.exp_pos _)]
  change inner ℂ (dilationCLM (Real.exp t) (Real.exp_pos t) f) g = _
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_dilationCLM]
  simp only [Real.exp_neg, dilationCLM_apply]

private theorem inner_difference (u : ℝ) (f g : SoninL2) :
    inner ℂ (gammaClockDifferenceOperator u f) g = inner ℂ f (gammaClockDifferenceOperator u g) := by
  rw [difference_apply, difference_apply, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_log_dilation, inner_log_dilation, neg_neg]
  have h2 : (starRingEnd ℂ) (2:ℂ) = (2:ℂ) := Complex.conj_ofReal 2
  rw [h2]
  ring

private theorem inner_integral_left {μ : Measure ℝ} {f : ℝ → SoninL2}
    (hf : Integrable f μ) (y : SoninL2) :
    inner ℂ (∫ u, f u ∂μ) y = ∫ u, inner ℂ (f u) y ∂μ := by
  rw [← inner_conj_symm, ← integral_inner hf, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with u
  exact inner_conj_symm _ _

/-- Self-adjointness is proved on the complete strong integral, including its counterterm. -/
theorem adjoint_gammaClockRemainderOperator (ε R : ℝ) (hε : 0 < ε) :
    ContinuousLinearMap.adjoint (gammaClockRemainderOperator ε R hε) =
      gammaClockRemainderOperator ε R hε := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, gammaClockRemainderOperator_apply,
    gammaClockRemainderOperator_apply, inner_integral_left (remainder_integrable ε R hε g),
    ← integral_inner (remainder_integrable ε R hε f)]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, inner_difference]

/-- Exact positive all-degree energy defect for every two-cutoff remainder difference. -/
theorem gammaClockRemainder_tail_monomial_energy (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (ε δ R S : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    let K := gammaClockRemainderOperator ε R hε-gammaClockRemainderOperator δ S hδ
    ‖K (soninCutoffMonomial a n)‖^2 +
      a^(2*n)*(n:ℝ)*((n:ℝ)+1)*
        ‖soninDilationResolvent ((n:ℝ)+1/2) (by positivity) (K (soninCutoffMonomial a 0))‖^2 =
      a^(2*n)*‖K (soninCutoffMonomial a 0)‖^2 := by
  dsimp only
  let K := gammaClockRemainderOperator ε R hε-gammaClockRemainderOperator δ S hδ
  have hT (f : SoninL2) : K (soninMonomialTransfer n f) = soninMonomialTransfer n (K f) := by
    simp only [K, sub_apply, map_sub, gammaClockRemainderOperator_transfer]
  have hP (f : SoninL2) : K (soninParityMultiplier n f) = soninParityMultiplier n (K f) := by
    simp only [K, sub_apply, map_sub, gammaClockRemainderOperator_parity]
  change ‖K (soninCutoffMonomial a n)‖^2 + _ = _
  rw [soninMonomialTransfer_cutoff a ha n, ContinuousLinearMap.map_smul_of_tower,
    hP, hT, norm_smul, norm_soninParityMultiplier, Real.norm_eq_abs, mul_pow, sq_abs]
  have h := soninMonomialTransfer_energy n (K (soninCutoffMonomial a 0))
  have hp : a^(2*n) = (a^n)^2 := by rw [mul_comm 2 n, pow_mul]
  rw [hp]
  linear_combination (a^n)^2*h

end RHTower

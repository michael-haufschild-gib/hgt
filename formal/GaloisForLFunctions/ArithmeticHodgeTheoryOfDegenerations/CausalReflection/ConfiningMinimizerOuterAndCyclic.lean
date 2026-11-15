import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineGroundStateRigidity
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateIsCyclic

/-!
# Boundary Laplace nonvanishing, outerness, and causal cyclicity at every confinement ratio

Every positive confinement ratio `R > 0` admits a normalized minimizer of
`criticalHalfLineFullEnergy R`. Pointwise Fourier skewness of the real undamped
resolvent implies ordinary `L²` orthogonality by Plancherel, annihilating the
eigenvalue right-hand side of the weak Euler–Lagrange equation at any imaginary-axis
Laplace zero. Combining closed-right-half-plane Laplace zero-freeness with positive
terminal mass near `0` shows that at every `R > 0`, the Cayley–Laplace multiplier
is outer and the reflected minimizer is cyclic for causal translations on `L²(0, ∞)`.
-/

noncomputable section
open MeasureTheory Filter Set Topology Metric Zeta23 FourierTransform
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ
open _root_.HTGeometry

private theorem norm_add_eq_norm_sub_of_orthogonal (z w : ℂ)
    (h : z.re * w.re + z.im * w.im = 0) : ‖z + w‖ = ‖z - w‖ := by
  have he : ‖z + w‖ ^ 2 = ‖z - w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    nlinarith only [h]
  nlinarith only [he, norm_nonneg (z + w), norm_nonneg (z - w)]

/-- Pointwise Fourier skewness implies ordinary `L²` orthogonality on the energy domain. -/
theorem integral_mul_eq_zero_of_fourier_pair_zero {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hpair : ∀ r, gammaFourierPair F G r = 0) :
    (∫ u, F u * G u) = 0 := by
  have hn (r : ℝ) :
      ‖paperFT (cx (fun u => F u + (1 : ℝ) * G u)) r‖ =
        ‖paperFT (cx (fun u => F u + (-1 : ℝ) * G u)) r‖ := by
    rw [paperFT_cx_add_const_mul hF.integrable hG.integrable,
      paperFT_cx_add_const_mul hF.integrable hG.integrable]
    simp only [Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul,
      ← sub_eq_add_neg]
    exact norm_add_eq_norm_sub_of_orthogonal _ _ (hpair r)
  have hfourier (ξ : ℝ) :
      ‖𝓕 (cx (fun u => F u + (1 : ℝ) * G u)) ξ‖ =
        ‖𝓕 (cx (fun u => F u + (-1 : ℝ) * G u)) ξ‖ := by
    have he := hn (-(2 * Real.pi * ξ))
    simp only [paperFT_ofReal_eq_fourier] at he
    have hs : -(-(2 * Real.pi * ξ)) / (2 * Real.pi) = ξ := by
      field_simp [Real.pi_ne_zero]
    simpa only [hs] using he
  have hsum := hF.add_const_mul hG 1
  have hdiff := hF.add_const_mul hG (-1)
  have he := integral_conj_mul_translate_eq_of_fourier_norm
    (hsum.integrable.ofReal (𝕜 := ℂ)) hsum.memLp_complex
    (hdiff.integrable.ofReal (𝕜 := ℂ)) hdiff.memLp_complex
    (Eventually.of_forall hfourier) 0
  change (∫ u : ℝ, (starRingEnd ℂ) ((F u + (1 : ℝ) * G u : ℝ) : ℂ) *
      ((F (u + 0) + (1 : ℝ) * G (u + 0) : ℝ) : ℂ)) =
    ∫ u : ℝ, (starRingEnd ℂ) ((F u + (-1 : ℝ) * G u : ℝ) : ℂ) *
      ((F (u + 0) + (-1 : ℝ) * G (u + 0) : ℝ) : ℂ) at he
  simp only [add_zero, Complex.conj_ofReal, ← Complex.ofReal_mul] at he
  rw [integral_complex_ofReal, integral_complex_ofReal] at he
  have hreal : (∫ u, (F u + (1 : ℝ) * G u) ^ 2) = ∫ u, (F u + (-1 : ℝ) * G u) ^ 2 := by
    simpa only [pow_two] using Complex.ofReal_inj.mp he
  rw [criticalHalfLine_square_mass_add_const_mul hF hG 1,
    criticalHalfLine_square_mass_add_const_mul hF hG (-1)] at hreal
  linarith only [hreal]

/-- The eighth-exponential cross integral against the real undamped resolvent equals a
positive multiple of the weighted complex resolvent square norm. -/
theorem integral_weighted_realUndampedCausalConvolution_mixed (b : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    (∫ u in Iio 0, F u * realUndampedCausalConvolution b F u * Real.exp (-(8 * u))) =
      (4 / Real.pi) * ∫ u, ‖causalLaplaceWeighted (4 / Real.pi)
        (modulatedCausalConvolution 0 b (cx F)) u‖ ^ 2 := by
  have hm := (integral_weighted_modulatedCausalConvolution_mixed_energy
    (a := 0) (x := 4 / Real.pi) (by positivity) b hF.memLp_weightedComplex).2
  have hweight (u : ℝ) : Complex.exp (-(Real.pi * (4 / Real.pi) * u : ℝ)) =
      (Real.exp (-(4 * u)) : ℂ) := by
    rw [show Real.pi * (4 / Real.pi) = 4 by field_simp [Real.pi_ne_zero],
      ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  have hpoint (u : ℝ) :
      ((starRingEnd ℂ) (causalLaplaceWeighted (4 / Real.pi) (cx F) u) *
        causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution 0 b (cx F)) u).re =
        F u * realUndampedCausalConvolution b F u * Real.exp (-(8 * u)) := by
    unfold causalLaplaceWeighted
    simp only [hweight]
    change ((starRingEnd ℂ) ((Real.exp (-(4 * u)) : ℂ) * (F u : ℂ)) *
      ((Real.exp (-(4 * u)) : ℂ) * modulatedCausalConvolution 0 b (cx F) u)).re = _
    rw [map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    have he : Real.exp (-(8 * u)) = Real.exp (-(4 * u)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    unfold realUndampedCausalConvolution
    ring
  have hs : (Iio (0 : ℝ)).indicator
      (fun u => F u * realUndampedCausalConvolution b F u * Real.exp (-(8 * u))) =
      fun u => F u * realUndampedCausalConvolution b F u * Real.exp (-(8 * u)) := by
    funext u
    by_cases hu : u ∈ Iio (0 : ℝ)
    · exact indicator_of_mem hu _
    · rw [indicator_of_notMem hu, hF.support u (le_of_not_gt hu), zero_mul, zero_mul]
  rw [← integral_indicator measurableSet_Iio, hs]
  simpa only [hpoint, zero_add] using hm

/-- Every normalized confining minimizer has nonzero imaginary-axis Laplace transform. -/
theorem IsHalfLineEnergyMinimizer.boundaryLaplace_ne_zero
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) (b : ℝ) :
    negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 b) ≠ 0 := by
  intro hz
  have hd := hF.1
  have hH := hd.realUndampedCausalConvolution b hz
  have horth : (∫ u, F u * realUndampedCausalConvolution b F u) = 0 :=
    integral_mul_eq_zero_of_fourier_pair_zero hd hH
      (gammaFourierPair_realUndampedCausalConvolution b hd hz)
  have he := hF.weakEquation hR hH
  rw [horth, mul_zero] at he
  obtain ⟨hg, hp⟩ := arithmetic_mixed_realUndampedCausalConvolution_eq_zero b hd hz
  have hpolar := pole_mixed_realUndampedCausalConvolution_eq_zero b hd hz
  unfold criticalHalfLineMixedEnergy at he
  rw [hg, hp, hpolar, integral_weighted_realUndampedCausalConvolution_mixed b hd] at he
  simp only [zero_div, sub_zero, zero_add] at he
  have hcoef : criticalAliasCoefficient R * (4 / Real.pi) ≠ 0 :=
    ne_of_gt (mul_pos (criticalAliasCoefficient_positive hR) (by positivity))
  have hmass : (∫ u, ‖causalLaplaceWeighted (4 / Real.pi)
      (modulatedCausalConvolution 0 b (cx F)) u‖ ^ 2) = 0 := by
    rw [← mul_assoc] at he
    exact (mul_eq_zero.mp he).resolve_left hcoef
  have hK := memLp_weighted_modulatedCausalConvolution
    (a := 0) (x := 4 / Real.pi) (by positivity) b hd.memLp_weightedComplex
  have hKi := (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).mp hK
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun u => sq_nonneg
      ‖causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution 0 b (cx F)) u‖) hKi).mp hmass
  have hKzero : modulatedCausalConvolution 0 b (cx F) =ᵐ[volume] 0 := by
    filter_upwards [hae] with u hu
    change ‖causalLaplaceWeighted (4 / Real.pi)
      (modulatedCausalConvolution 0 b (cx F)) u‖ ^ 2 = 0 at hu
    have hn : ‖causalLaplaceWeighted (4 / Real.pi)
        (modulatedCausalConvolution 0 b (cx F)) u‖ = 0 := by nlinarith only [hu]
    have hv := norm_eq_zero.mp hn
    change Complex.exp (-(Real.pi * (4 / Real.pi) * u : ℝ)) *
      modulatedCausalConvolution 0 b (cx F) u = 0 at hv
    exact (mul_eq_zero.mp hv).resolve_left (Complex.exp_ne_zero _)
  have hm : Measurable (cx F) := Complex.continuous_ofReal.measurable.comp hd.meas
  have hf : Integrable (cx F) := hd.integrable.ofReal (𝕜 := ℂ)
  have hs : ∀ u, 0 ≤ u → cx F u = 0 := by
    intro u hu
    change (F u : ℂ) = 0
    rw [hd.support u hu, Complex.ofReal_zero]
  have hFzero : cx F =ᵐ[volume] 0 := by
    apply _root_.HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hf
    intro ξ
    have hk : 𝓕 (modulatedCausalConvolution 0 b (cx F)) ξ = 0 := by
      rw [Real.fourier_congr_ae hKzero, Real.fourier_real_eq_integral_exp_smul]
      simp
    have hh := fourier_undampedCausalConvolution_mul b hm hf hd.memLp_weightedComplex hs hz ξ
    rw [hk, mul_zero] at hh
    exact hh.symm
  have hnorm : (∫ u, F u ^ 2) = 0 := by
    calc
      _ = ∫ _u : ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hFzero] with u hu
        change (F u : ℂ) = 0 at hu
        have hfu : F u = 0 := Complex.ofReal_eq_zero.mp hu
        rw [hfu, zero_pow two_ne_zero]
      _ = 0 := by simp
  linarith only [hnorm, hF.2.1]

/-- Every normalized confining minimizer has a zero-free Laplace transform on the
entire closed right half-plane `Re z ≥ 0`. -/
theorem IsHalfLineEnergyMinimizer.closedRightHalfPlaneLaplace_ne_zero
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F)
    {z : ℂ} (hz : 0 ≤ z.re) : negativeHalfLineLaplace (cx F) z ≠ 0 := by
  rcases lt_or_eq_of_le hz with hpos | heq
  · exact hF.complexLaplace_ne_zero hR hpos
  · have he : modulatedLaplaceRate 0 (z.im / (2 * Real.pi)) = z := by
      have hi : 2 * Real.pi * (z.im / (2 * Real.pi)) = z.im := by
        field_simp [Real.pi_ne_zero]
      unfold modulatedLaplaceRate
      rw [hi]
      apply Complex.ext
      · simpa only [mul_zero, Complex.ofReal_zero, zero_add, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, sub_zero] using heq
      · simp only [mul_zero, Complex.ofReal_zero, zero_add, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_one, add_zero]
    rw [← he]
    exact hF.boundaryLaplace_ne_zero hR _

/-- Every terminal interval `(-d, 0)` carries strictly positive square mass of a
normalized confining minimizer at any positive ratio `R > 0`. -/
theorem IsHalfLineEnergyMinimizer.endpoint_mass_pos
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F)
    {d : ℝ} (hd : 0 < d) : 0 < ∫ u in Ioo (-d) 0, F u ^ 2 := by
  have hD := hF.1
  by_contra hbad
  have hzero : (∫ u in Ioo (-d) 0, F u ^ 2) = 0 :=
    le_antisymm (le_of_not_gt hbad) (integral_nonneg fun _ => sq_nonneg _)
  have hsq := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun u => sq_nonneg (F u)) hD.sq.integrableOn).mp hzero
  have hgap : ∀ᵐ u ∂volume, u ∈ Ioo (-d) 0 → F u ^ 2 = 0 :=
    (ae_restrict_iff' measurableSet_Ioo).mp hsq
  let G : ℝ → ℝ := (Iio (-d / 2)).indicator F
  have he : F =ᵐ[volume] G := by
    filter_upwards [hgap] with u hu
    by_cases hlt : u < -d / 2
    · exact (indicator_of_mem (show u ∈ Iio (-d / 2) from hlt) F).symm
    · rw [show G u = 0 from
        indicator_of_notMem (show u ∉ Iio (-d / 2) from hlt) F]
      by_cases hp : 0 ≤ u
      · exact hD.support u hp
      · have hz := hu ⟨by linarith only [hlt, hd], lt_of_not_ge hp⟩
        nlinarith only [hz]
  have hsG (u : ℝ) (hu : 0 ≤ u) : G u = 0 :=
    indicator_of_notMem (show u ∉ Iio (-d / 2) by
      change ¬u < -d / 2
      linarith only [hu, hd]) F
  have hG := hD.congr_ae (hD.meas.indicator measurableSet_Iio) he hsG
  have hnG : (∫ u, G u ^ 2) = 1 := by
    rw [← hF.2.1]
    exact integral_congr_ae (he.symm.mono fun u hu => congrArg (fun x : ℝ => x ^ 2) hu)
  have hmass : 0 < ∫ u, G u ^ 2 * Real.exp (-(8 * u)) :=
    lt_of_lt_of_le zero_lt_one (one_le_exponential_square_of_domain hG hnG)
  have henergy : criticalHalfLineFullEnergy R G = criticalHalfLineGroundEnergy R := by
    rw [← criticalHalfLineFullEnergy_congr_ae hD hG he]
    exact hF.2.2
  have hsShift (u : ℝ) (hu : 0 ≤ u) : G (u + (-d / 2)) = 0 :=
    indicator_of_notMem (show u + (-d / 2) ∉ Iio (-d / 2) by
      change ¬u + (-d / 2) < -d / 2
      linarith only [hu]) F
  have hnShift : (∫ u, G (u + (-d / 2)) ^ 2) = 1 :=
    (integral_add_right_eq_self (μ := volume) (fun u => G u ^ 2) (-d / 2)).trans hnG
  have hfloor := criticalHalfLineGroundEnergy_le hR (hG.comp_add_right (-d / 2) hsShift) hnShift
  rw [criticalHalfLineFullEnergy_comp_add_right hG _ _ hsShift, henergy] at hfloor
  have heps : Real.exp (8 * (-d / 2)) - 1 < 0 := by
    have hh : Real.exp (8 * (-d / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hd])
    linarith only [hh]
  have hneg := mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (criticalAliasCoefficient_positive hR) heps) hmass
  linarith only [hfloor, hneg]

/-- The Cayley-transformed Laplace multiplier of a normalized confining minimizer. -/
def halfLineMinimizerLaplaceMultiplier {R : ℝ} {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) : DiskMultiplier :=
  negativeHalfLineLaplaceDiskMultiplier (cx F)
    (hF.1.integrable.ofReal (𝕜 := ℂ))
    hF.1.memLp_complex
    (fun u hu => by
      change (F u : ℂ) = 0
      rw [hF.1.support u hu, Complex.ofReal_zero])

/-- At every positive confinement ratio `R > 0`, the Cayley–Laplace multiplier of
any normalized minimizer is an outer Hardy disk multiplier. -/
theorem IsHalfLineEnergyMinimizer.laplaceMultiplier_outer
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    IsOuterDiskMultiplier (halfLineMinimizerLaplaceMultiplier hF) := by
  apply isOuter_negativeHalfLineLaplaceDiskMultiplier
  · intro z hz
    exact hF.closedRightHalfPlaneLaplace_ne_zero hR hz
  · intro a ha
    have hpos := hF.endpoint_mass_pos hR ha
    simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hpos

/-- A normalized confining minimizer reflected into positive-half-line `L²(0, ∞)`. -/
def reflectedHalfLineMinimizerDatum {R : ℝ} {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) : BurnolHalfLineL2 :=
  (memLp_reflected_negativeProfile hF.1.memLp_complex).toLp (fun u => cx F (-u))

/-- The disk multiplier evaluates to the Laplace transform of the reflected `L²` datum. -/
theorem halfLineMinimizerLaplaceMultiplier_fn_eq_reflectedDatum {R : ℝ} {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) (z : ℂ) :
    (halfLineMinimizerLaplaceMultiplier hF).fn z =
      laplaceRay (reflectedHalfLineMinimizerDatum hF) (diskToRight z) := by
  have hs : ∀ u, 0 ≤ u → cx F u = 0 := by
    intro u hu
    change (F u : ℂ) = 0
    rw [hF.1.support u hu, Complex.ofReal_zero]
  change negativeHalfLineLaplace (cx F) (diskToRight z) = _
  rw [negativeHalfLineLaplace_eq_laplaceRay_reflect (cx F) hs]
  unfold laplaceRay
  have hae : (reflectedHalfLineMinimizerDatum hF : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      (fun u => cx F (-u)) :=
    MemLp.coeFn_toLp (memLp_reflected_negativeProfile hF.1.memLp_complex)
  apply integral_congr_ae
  filter_upwards [hae] with u hu
  rw [hu]

/-- At every positive confinement ratio `R > 0`, causal translations of the reflected
minimizer span a dense subspace of `L²(0, ∞)`. -/
theorem IsHalfLineEnergyMinimizer.causalCyclicSubspace_eq_top
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    causalCyclicSubspace (reflectedHalfLineMinimizerDatum hF) = ⊤ :=
  causalCyclicSubspace_eq_top_of_outerLaplace (reflectedHalfLineMinimizerDatum hF)
    (halfLineMinimizerLaplaceMultiplier hF)
    (fun z _ => halfLineMinimizerLaplaceMultiplier_fn_eq_reflectedDatum hF z)
    (hF.laplaceMultiplier_outer hR)

#print axioms IsHalfLineEnergyMinimizer.closedRightHalfPlaneLaplace_ne_zero
#print axioms IsHalfLineEnergyMinimizer.endpoint_mass_pos
#print axioms IsHalfLineEnergyMinimizer.laplaceMultiplier_outer
#print axioms IsHalfLineEnergyMinimizer.causalCyclicSubspace_eq_top

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

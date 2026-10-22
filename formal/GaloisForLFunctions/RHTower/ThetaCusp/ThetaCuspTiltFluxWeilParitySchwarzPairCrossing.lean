import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxWeilParitySchwarzPairNullCone
import GaloisForLFunctions.RHTower.XiPositivePairedDiagonalSectorCollapse

/-!
# Schwarz-paired parity-null states have an exact transverse source crossing

At a hypothetical off-line centered Xi zero `alpha`, the Schwarz-paired boundary fiber is a
nonzero vector on the Weil parity null cone. This module identifies its source-side orientation.
Along the canonical reciprocal horizontal mesh leaving `alpha` from the side opposite
`alpha.re`, the positive-paired continued Cauchy diagonal has the exact first-order limit

`epsilon_n * K(z_n,z_n) -> -2 * |alpha.re| * ord_alpha(Xi) / normSq alpha`.

The coefficient is strictly negative and records full analytic multiplicity. This upgrades the
existing nearby-negativity theorem to a canonical Krein spectral-flow law and proves that source
orientation is a transverse first jet, not boundary-value positivity.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Horizontal direction pointing toward the side opposite the real coordinate. -/
def xiReciprocalSquareTransverseDirection (alpha : ℂ) : ℝ :=
  if 0 < alpha.re then -1 else 1

/-- Canonical reciprocal mesh used to leave a Schwarz-paired divisor boundary state. -/
def xiReciprocalSquareTransverseStep (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)⁻¹)

/-- Canonical horizontal approach to a non-imaginary-axis centered Xi zero. -/
def xiReciprocalSquareTransverseApproach (alpha : ℂ) (n : ℕ) : ℂ :=
  alpha + ((xiReciprocalSquareTransverseDirection alpha *
    xiReciprocalSquareTransverseStep n : ℝ) : ℂ)

theorem tendsto_xiReciprocalSquareTransverseApproach (alpha : ℂ) :
    Tendsto (xiReciprocalSquareTransverseApproach alpha) atTop (nhds alpha) := by
  have hepsilonZero : Tendsto xiReciprocalSquareTransverseStep atTop (nhds 0) := by
    rw [show xiReciprocalSquareTransverseStep =
      fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹) by rfl]
    exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  have htZero : Tendsto
      (fun n => xiReciprocalSquareTransverseDirection alpha *
        xiReciprocalSquareTransverseStep n) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hepsilonZero : Tendsto
        (fun n => xiReciprocalSquareTransverseDirection alpha *
          xiReciprocalSquareTransverseStep n) atTop
        (nhds (xiReciprocalSquareTransverseDirection alpha * 0)))
  have htCast : Tendsto
      (fun n => ((xiReciprocalSquareTransverseDirection alpha *
        xiReciprocalSquareTransverseStep n : ℝ) : ℂ)) atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp htZero
  show Tendsto
    (fun n => alpha + ((xiReciprocalSquareTransverseDirection alpha *
      xiReciprocalSquareTransverseStep n : ℝ) : ℂ)) atTop (nhds alpha)
  have hconst : Tendsto (fun _ : ℕ => alpha) atTop (nhds alpha) :=
    tendsto_const_nhds
  simpa only [add_zero] using hconst.add htCast

/-- The canonical horizontal approach eventually consists of full continued-source points. -/
theorem eventually_xiReciprocalSquareTransverseApproach_continuedDomain
    {alpha : ℂ}
    (haim : 0 < alpha.im) (haimhalf : alpha.im < 1 / 2)
    (haXi : XiC alpha = 0) :
    ∀ᶠ n in atTop,
      CCMContinuedCauchyDomain (xiReciprocalSquareTransverseApproach alpha n) := by
  let sigma : ℂ := 1 / 2 + alpha * I
  have hsigmaZero : xi sigma = 0 := by
    simpa [XiC, sigma] using haXi
  let epsilon : ℕ → ℝ := xiReciprocalSquareTransverseStep
  have hepsilonPos (n : ℕ) : 0 < epsilon n := by
    dsimp only [epsilon, xiReciprocalSquareTransverseStep]
    positivity
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    dsimp only [epsilon, xiReciprocalSquareTransverseStep]
    exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  let kappa : ℝ := xiReciprocalSquareTransverseDirection alpha
  have hkappa_ne : kappa ≠ 0 := by
    dsimp only [kappa, xiReciprocalSquareTransverseDirection]
    split_ifs <;> norm_num
  let t : ℕ → ℝ := fun n => kappa * epsilon n
  have ht_ne (n : ℕ) : t n ≠ 0 :=
    mul_ne_zero hkappa_ne (ne_of_gt (hepsilonPos n))
  have htZero : Tendsto t atTop (nhds 0) := by
    simpa only [t, mul_zero] using
      (tendsto_const_nhds.mul hepsilonZero :
        Tendsto (fun n => kappa * epsilon n) atTop (nhds (kappa * 0)))
  let z : ℕ → ℂ := xiReciprocalSquareTransverseApproach alpha
  have hzFormula (n : ℕ) : z n = alpha + (t n : ℂ) := by
    rfl
  have hzTend : Tendsto z atTop (nhds alpha) :=
    tendsto_xiReciprocalSquareTransverseApproach alpha
  let s : ℕ → ℂ := fun n => sigma + (t n : ℂ) * I
  have hsTend : Tendsto s atTop (nhds sigma) := by
    have htCast : Tendsto (fun n => (t n : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp htZero
    simpa [s] using tendsto_const_nhds.add (htCast.mul tendsto_const_nhds)
  obtain ⟨R, hR, _h, _hhan, hh0, hfactor⟩ := xi_peel_ball sigma
  have hevBall : ∀ᶠ n in atTop, s n ∈ ball sigma R :=
    hsTend (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hevXi : ∀ᶠ n in atTop, XiC (z n) ≠ 0 := by
    filter_upwards [hevBall] with n hnBall
    have hsne : s n ≠ sigma := by
      intro heq
      apply ht_ne n
      have htI : (t n : ℂ) * I = 0 := by
        dsimp only [s] at heq
        linear_combination heq
      exact ofReal_injective (mul_eq_zero.mp htI |>.resolve_right I_ne_zero)
    have hxis : xi (s n) ≠ 0 := by
      rw [hfactor (s n) hnBall]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hsne)) (hh0 (s n) hnBall)
    have hcoord : 1 / 2 + z n * I = s n := by
      rw [hzFormula]
      simp [s, sigma]
      ring
    rw [XiC, hcoord]
    exact hxis
  filter_upwards [hevXi] with n hnXi
  apply ccmContinuedCauchyDomain_of_regular_mem_centeredStrip
  · simp only [xiReciprocalSquareTransverseApproach, Complex.add_im,
      Complex.ofReal_im, add_zero]
    linarith
  · simpa only [xiReciprocalSquareTransverseApproach, Complex.add_im,
      Complex.ofReal_im, add_zero] using haimhalf
  · exact hnXi

/-- Exact multiplicity-sensitive first crossing of the reciprocal-square sector observable. -/
theorem tendsto_xiReciprocalSquareTransverse_sector
    {alpha : ℂ}
    (hare : alpha.re ≠ 0) (haXi : XiC alpha = 0) :
    Tendsto
      (fun n => xiReciprocalSquareTransverseStep n *
        ((xiReciprocalSquareTransverseApproach alpha n).re *
          (-logDeriv XiC (xiReciprocalSquareTransverseApproach alpha n) /
            xiReciprocalSquareTransverseApproach alpha n).im))
      atTop
      (nhds (-|alpha.re| *
        (((analyticOrderAt xi (1 / 2 + alpha * I)).toNat : ℕ) : ℝ) * alpha.im /
        normSq alpha)) := by
  let sigma : ℂ := 1 / 2 + alpha * I
  have hsigmaZero : xi sigma = 0 := by
    simpa [XiC, sigma] using haXi
  have halpha0 : alpha ≠ 0 := by
    intro h
    apply hare
    rw [h]
    norm_num
  let epsilon : ℕ → ℝ := xiReciprocalSquareTransverseStep
  have hepsilonPos (n : ℕ) : 0 < epsilon n := by
    dsimp only [epsilon, xiReciprocalSquareTransverseStep]
    positivity
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    dsimp only [epsilon, xiReciprocalSquareTransverseStep]
    exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  let kappa : ℝ := xiReciprocalSquareTransverseDirection alpha
  have hkappa_ne : kappa ≠ 0 := by
    dsimp only [kappa, xiReciprocalSquareTransverseDirection]
    split_ifs <;> norm_num
  have hkappa_sq : kappa * kappa = 1 := by
    dsimp only [kappa, xiReciprocalSquareTransverseDirection]
    split_ifs <;> norm_num
  have hkappa_re : kappa * alpha.re = -|alpha.re| := by
    by_cases hapos : 0 < alpha.re
    · simp [kappa, xiReciprocalSquareTransverseDirection, hapos,
        abs_of_pos hapos]
    · have haneg : alpha.re < 0 := lt_of_le_of_ne (not_lt.mp hapos) hare
      simp [kappa, xiReciprocalSquareTransverseDirection, hapos,
        abs_of_neg haneg]
  let t : ℕ → ℝ := fun n => kappa * epsilon n
  have ht_ne (n : ℕ) : t n ≠ 0 :=
    mul_ne_zero hkappa_ne (ne_of_gt (hepsilonPos n))
  have htZero : Tendsto t atTop (nhds 0) := by
    simpa only [t, mul_zero] using
      (tendsto_const_nhds.mul hepsilonZero :
        Tendsto (fun n => kappa * epsilon n) atTop (nhds (kappa * 0)))
  let z : ℕ → ℂ := xiReciprocalSquareTransverseApproach alpha
  have hzFormula (n : ℕ) : z n = alpha + (t n : ℂ) := by
    rfl
  have hzTend : Tendsto z atTop (nhds alpha) :=
    tendsto_xiReciprocalSquareTransverseApproach alpha
  let s : ℕ → ℂ := fun n => sigma + (t n : ℂ) * I
  have hsTend : Tendsto s atTop (nhds sigma) := by
    have htCast : Tendsto (fun n => (t n : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp htZero
    simpa [s] using tendsto_const_nhds.add (htCast.mul tendsto_const_nhds)
  have hsWithin : Tendsto s atTop (nhdsWithin sigma ({sigma}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hsTend, Eventually.of_forall (fun n => ?_)⟩
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have htI : (t n : ℂ) * I = 0 := by
      dsimp only [s] at h
      linear_combination h
    exact ht_ne n (ofReal_injective (mul_eq_zero.mp htI |>.resolve_right I_ne_zero))
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  have hnormalized := (xi_normalizedLogDeriv_tendsto_order sigma).comp hsWithin
  have hnormalizedXiC : Tendsto
      (fun n => (t n : ℂ) * logDeriv XiC (z n))
      atTop (nhds (m : ℂ)) := by
    have hfun : (fun n => (t n : ℂ) * logDeriv XiC (z n)) =
        fun n => (s n - sigma) * logDeriv xi (s n) := by
      funext n
      rw [logDeriv_XiC_eq_mul_I_logDeriv_xi]
      have hcoord : 1 / 2 + z n * I = s n := by
        rw [hzFormula]
        simp [s, sigma]
        ring
      rw [hcoord]
      dsimp only [s]
      ring
    rw [hfun]
    simpa only [m, Function.comp_apply] using! hnormalized
  have hquot : Tendsto
      (fun n => (t n : ℂ) * (-logDeriv XiC (z n) / z n))
      atTop (nhds (-((m : ℂ) / alpha))) := by
    have h := hnormalizedXiC.neg.div hzTend halpha0
    have hfun : (fun n => (t n : ℂ) * (-logDeriv XiC (z n) / z n)) =
        fun n => (-(t n : ℂ) * logDeriv XiC (z n)) / z n := by
      funext n
      simp only [div_eq_mul_inv]
      ring
    rw [hfun]
    change Tendsto ((fun n => (-(t n : ℂ) * logDeriv XiC (z n))) / z)
      atTop (nhds (-((m : ℂ) / alpha)))
    convert h using 1
    · funext n
      ring
    · ring
  have hquotIm : Tendsto
      (fun n => t n * (-logDeriv XiC (z n) / z n).im)
      atTop (nhds (-((m : ℂ) / alpha)).im) := by
    have h := Complex.continuous_im.continuousAt.tendsto.comp hquot
    convert h using 1
    funext n
    simp only [Function.comp_apply, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  have hzRe : Tendsto (fun n => (z n).re) atTop (nhds alpha.re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hzTend
  have hsectorScaled : Tendsto
      (fun n => t n * ((z n).re * (-logDeriv XiC (z n) / z n).im))
      atTop (nhds (alpha.re * (-((m : ℂ) / alpha)).im)) := by
    have h := hzRe.mul hquotIm
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hquotLimit : (-((m : ℂ) / alpha)).im =
      (m : ℝ) * alpha.im / normSq alpha := by
    rw [neg_im, Complex.div_im]
    norm_num
  have hscaled := (tendsto_const_nhds.mul hsectorScaled :
    Tendsto
      (fun n => kappa *
        (t n * ((z n).re * (-logDeriv XiC (z n) / z n).im)))
      atTop
      (nhds (kappa * (alpha.re * (-((m : ℂ) / alpha)).im))))
  have hcanon : Tendsto
      (fun n => epsilon n *
        ((z n).re * (-logDeriv XiC (z n) / z n).im))
      atTop
      (nhds (-|alpha.re| * (m : ℝ) * alpha.im / normSq alpha)) := by
    convert hscaled using 1
    · funext n
      dsimp only [t]
      calc
        epsilon n * ((z n).re * (-logDeriv XiC (z n) / z n).im) =
            (kappa * kappa) *
              (epsilon n * ((z n).re * (-logDeriv XiC (z n) / z n).im)) := by
          rw [hkappa_sq, one_mul]
        _ = kappa *
            (kappa * epsilon n *
              ((z n).re * (-logDeriv XiC (z n) / z n).im)) := by ring
    · rw [hquotLimit, ← mul_assoc, hkappa_re]
      congr 1
      ring
  simpa only [epsilon, z, m, sigma] using hcanon

/-- Exact negative first Krein crossing of the positive-paired continued source diagonal. -/
theorem tendsto_ccmPositivePairedReducedKernel_transverse_crossing
    {alpha : ℂ}
    (haim : 0 < alpha.im) (haimhalf : alpha.im < 1 / 2)
    (hare : alpha.re ≠ 0) (haXi : XiC alpha = 0) :
    Tendsto
      (fun n => xiReciprocalSquareTransverseStep n *
        ccmPositivePairedReducedKernel
          (xiReciprocalSquareTransverseApproach alpha n)
          (xiReciprocalSquareTransverseApproach alpha n))
      atTop
      (nhds (-2 * |alpha.re| *
        (((analyticOrderAt xi (1 / 2 + alpha * I)).toNat : ℕ) : ℝ) /
        normSq alpha)) := by
  let z : ℕ → ℂ := xiReciprocalSquareTransverseApproach alpha
  let epsilon : ℕ → ℝ := xiReciprocalSquareTransverseStep
  let m : ℕ := (analyticOrderAt xi (1 / 2 + alpha * I)).toNat
  have hsector := tendsto_xiReciprocalSquareTransverse_sector hare haXi
  have hdom := eventually_xiReciprocalSquareTransverseApproach_continuedDomain
    haim haimhalf haXi
  have hfun : ∀ᶠ n in atTop,
      epsilon n * ccmPositivePairedReducedKernel (z n) (z n) =
        (2 / alpha.im) *
          (epsilon n * ((z n).re * (-logDeriv XiC (z n) / z n).im)) := by
    filter_upwards [hdom] with n hndom
    have hzim : (z n).im = alpha.im := by
      simp [z, xiReciprocalSquareTransverseApproach]
    rw [ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector
      (by rw [hzim]; exact haim.ne'),
      continuedPrimeArchReciprocalSquareTrace,
      continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC_of_domain hndom,
      hzim]
    field_simp [haim.ne']
    ring
  have hscaled := (tendsto_const_nhds.mul hsector : Tendsto
      (fun n => (2 / alpha.im) *
        (xiReciprocalSquareTransverseStep n *
          ((xiReciprocalSquareTransverseApproach alpha n).re *
            (-logDeriv XiC (xiReciprocalSquareTransverseApproach alpha n) /
              xiReciprocalSquareTransverseApproach alpha n).im)))
      atTop
      (nhds ((2 / alpha.im) *
        (-|alpha.re| * (m : ℝ) * alpha.im / normSq alpha))))
  have hlimit : (2 / alpha.im) *
      (-|alpha.re| * (m : ℝ) * alpha.im / normSq alpha) =
        -2 * |alpha.re| * (m : ℝ) / normSq alpha := by
    field_simp [haim.ne']
  rw [hlimit] at hscaled
  apply hscaled.congr'
  filter_upwards [hfun] with n hn
  simpa only [z, epsilon] using hn.symm

/-- The multiplicity-exact transverse crossing coefficient is genuinely negative. -/
theorem ccmPositivePairedReducedKernel_transverse_crossingLimit_neg
    {alpha : ℂ} (hare : alpha.re ≠ 0) (haXi : XiC alpha = 0) :
    -2 * |alpha.re| *
        (((analyticOrderAt xi (1 / 2 + alpha * I)).toNat : ℕ) : ℝ) /
      normSq alpha < 0 := by
  let sigma : ℂ := 1 / 2 + alpha * I
  have hsigmaZero : xi sigma = 0 := by
    simpa [XiC, sigma] using haXi
  have hmpos : 0 < (analyticOrderAt xi sigma).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hsigmaZero)
  have hrepos : 0 < |alpha.re| := abs_pos.mpr hare
  have halpha0 : alpha ≠ 0 := by
    intro h
    apply hare
    rw [h]
    norm_num
  have hnormSq : 0 < normSq alpha := normSq_pos.mpr halpha0
  dsimp only [sigma] at hmpos
  have hmposReal :
      0 < (((analyticOrderAt xi (1 / 2 + alpha * I)).toNat : ℕ) : ℝ) := by
    exact_mod_cast hmpos
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hrepos) hmposReal)
    hnormSq

/-- The canonical horizontal source mesh eventually crosses into the negative paired cone. -/
theorem eventually_ccmPositivePairedReducedKernel_transverse_neg
    {alpha : ℂ}
    (haim : 0 < alpha.im) (haimhalf : alpha.im < 1 / 2)
    (hare : alpha.re ≠ 0) (haXi : XiC alpha = 0) :
    ∀ᶠ n in atTop,
      ccmPositivePairedReducedKernel
        (xiReciprocalSquareTransverseApproach alpha n)
        (xiReciprocalSquareTransverseApproach alpha n) < 0 := by
  have hlimit := tendsto_ccmPositivePairedReducedKernel_transverse_crossing
    haim haimhalf hare haXi
  have hlimitNeg :=
    ccmPositivePairedReducedKernel_transverse_crossingLimit_neg hare haXi
  have hscaledNeg := hlimit.eventually (eventually_lt_nhds hlimitNeg)
  filter_upwards [hscaledNeg] with n hn
  have hepsilon : 0 < xiReciprocalSquareTransverseStep n := by
    simp only [xiReciprocalSquareTransverseStep]
    positivity
  nlinarith

end
end RHTower

import GaloisForLFunctions.RHTower.PrimeArchAntiHerglotzGate
import GaloisForLFunctions.RHTower.ModulusSlopeBudget

/-!
# Reciprocal-square sector gate for the continued prime--Gamma source

The functional-equation pairing of the centered Xi relative resolvent gives

`-T(z) / z = sum_q lambda_q / (1 - z^2 lambda_q)`,

where `lambda_q` is the centered reciprocal-square coordinate.  If all Xi zeros lie on the
critical line, the `lambda_q` are positive real numbers, so this is a Stieltjes-type transform:
on the centered upper half-plane its imaginary part has the sign of `re z`.

The converse is local and orientation-sensitive.  A nonreal centered zero in the upper strip is
an actual pole of this transform.  Approaching that pole horizontally from the side opposite to
its nonzero real coordinate forces a strictly negative sector value.  Thus the sector sign of one
explicit continued prime--Gamma value function excludes every off-line zero.

This is a source-value criterion, not a divisor enumeration or a limiting zero measure.  The file
proves the local pole law and the resulting top-down chain to RH; it does not prove the source
sector inequality.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- The reciprocal-square transform written only in terms of the analytically continued
prime--archimedean relative trace.  The upper-strip criteria below never evaluate it at `z = 0`. -/
def continuedPrimeArchReciprocalSquareTrace (z : ℂ) : ℂ :=
  -continuedPrimeArchSourceRelativeTrace z / z

/-- Target-coordinate version of the reciprocal-square sector sign. -/
def XiReciprocalSquareUpperSectorNonnegative : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → XiC z ≠ 0 →
    0 ≤ z.re * (-logDeriv XiC z / z).im

/-- Source-only reciprocal-square sector sign on the continued prime--Gamma domain. -/
def ContinuedPrimeArchReciprocalSquareUpperSectorNonnegative : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      0 ≤ z.re * (continuedPrimeArchReciprocalSquareTrace z).im

/-- On its natural pole-free strip domain, the source reciprocal-square transform is exactly the
paired Xi reciprocal-square resolvent. -/
theorem continuedPrimeArchReciprocalSquareTrace_eq_tsum
    {z : ℂ}
    (hzpos : 0 < z.im) (hzhalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    continuedPrimeArchReciprocalSquareTrace z =
      ∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm z q := by
  have hspos : 0 < (1 / 2 + z * I).re := by
    simp [mul_re]
    linarith
  have hs1 : 1 / 2 + z * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [mul_re] at hre
    linarith
  have hXi : XiC z ≠ 0 := by
    change xi (1 / 2 + z * I) ≠ 0
    exact (xi_eq_zero_iff hspos hs1).not.mpr hzeta
  rw [continuedPrimeArchReciprocalSquareTrace,
    continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hspos hs1 hzeta,
    xiRelativeResolventTrace_eq_reciprocalSquareResolvent hXi]
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hzpos
  field_simp [hz0]

/-- Under RH, every reciprocal-square resolvent summand has the Stieltjes sector sign. -/
theorem xiReciprocalSquareResolventTerm_sector_nonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) (z : ℂ) (hzIm : 0 ≤ z.im) (q : XiZeroCopy) :
    0 ≤ z.re * (xiReciprocalSquareResolventTerm z q).im := by
  obtain ⟨x, hx, hcoord⟩ := xiCentralReciprocalSquare_pos_real_of_rh hRH q.1
  have hcopy : xiZeroCopyReciprocalSquare q = (x : ℂ) := by
    rw [xiZeroCopyReciprocalSquare_eq]
    exact hcoord
  rw [xiReciprocalSquareResolventTerm, hcopy, Complex.div_im]
  have hden : 0 ≤ normSq (1 - z ^ 2 * (x : ℂ)) := normSq_nonneg _
  have him : (1 - z ^ 2 * (x : ℂ)).im = -2 * z.re * z.im * x := by
    simp only [sub_im, one_im, mul_im, ofReal_re, ofReal_im, mul_zero, pow_two]
    ring
  rw [him]
  simp only [ofReal_im, ofReal_re, zero_mul]
  rw [show z.re * (0 / normSq (1 - z ^ 2 * (x : ℂ)) -
      x * (-2 * z.re * z.im * x) / normSq (1 - z ^ 2 * (x : ℂ))) =
      (2 * x ^ 2 * z.re ^ 2 * z.im) /
        normSq (1 - z ^ 2 * (x : ℂ)) by ring]
  exact div_nonneg (by positivity) hden

/-- RH supplies the source reciprocal-square sector sign term by term. -/
theorem continuedPrimeArchReciprocalSquareUpperSectorNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ContinuedPrimeArchReciprocalSquareUpperSectorNonnegative := by
  intro z hzpos hzhalf hzeta
  rw [continuedPrimeArchReciprocalSquareTrace_eq_tsum hzpos hzhalf hzeta]
  have hspos : 0 < (1 / 2 + z * I).re := by
    simp [mul_re]
    linarith
  have hs1 : 1 / 2 + z * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [mul_re] at hre
    linarith
  have hXi : XiC z ≠ 0 := by
    change xi (1 / 2 + z * I) ≠ 0
    exact (xi_eq_zero_iff hspos hs1).not.mpr hzeta
  have hsum := summable_xiReciprocalSquareResolventTerm hXi
  rw [Complex.im_tsum hsum, ← tsum_mul_left]
  exact tsum_nonneg fun q =>
    xiReciprocalSquareResolventTerm_sector_nonnegative_of_riemannHypothesis
      hRH z hzpos.le q

/-- The source sector condition supplies the target-coordinate sector condition. -/
theorem xiReciprocalSquareUpperSectorNonnegative_of_continuedPrimeArch
    (hsource : ContinuedPrimeArchReciprocalSquareUpperSectorNonnegative) :
    XiReciprocalSquareUpperSectorNonnegative := by
  intro z hzpos hzhalf hXi
  have hspos : 0 < (1 / 2 + z * I).re := by
    simp [mul_re]
    linarith
  have hshalf : (1 / 2 + z * I).re < 1 := by
    simp [mul_re]
    linarith
  have hs1 : 1 / 2 + z * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [mul_re] at hre
    linarith
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 := by
    exact (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hXi)
  have h := hsource z hzpos hzhalf hzeta
  rw [continuedPrimeArchReciprocalSquareTrace,
    continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hspos hs1 hzeta,
    ← logDeriv_XiC_eq_relativeResolventTrace hXi] at h
  exact h

/-- **Positive local pole law.**  Every nonreal zero of `XiC` in the centered upper strip emits a
nearby regular point at which the reciprocal-square sector value is strictly negative. -/
theorem exists_xiReciprocalSquareUpperSector_neg_of_zero
    {alpha : ℂ}
    (haim : 0 < alpha.im) (haimhalf : alpha.im < 1 / 2)
    (hare : alpha.re ≠ 0) (haXi : XiC alpha = 0) :
    ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧ XiC z ≠ 0 ∧
      z.re * (-logDeriv XiC z / z).im < 0 := by
  let sigma : ℂ := 1 / 2 + alpha * I
  have hsigmaZero : xi sigma = 0 := by
    simpa [XiC, sigma] using haXi
  have hsigmaPos : 0 < sigma.re := by
    simp [sigma, mul_re]
    linarith
  have hsigmaLt : sigma.re < 1 := by
    simp [sigma, mul_re]
    linarith
  have halpha0 : alpha ≠ 0 := by
    intro h
    subst alpha
    norm_num at haim
  let epsilon : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ)⁻¹)
  have hepsilonPos (n : ℕ) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    dsimp only [epsilon]
    exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  let kappa : ℝ := if 0 < alpha.re then -1 else 1
  have hkappa_ne : kappa ≠ 0 := by
    dsimp only [kappa]
    split_ifs <;> norm_num
  have hkappa_sign :
      (0 < alpha.re ∧ kappa < 0) ∨ (alpha.re < 0 ∧ 0 < kappa) := by
    by_cases hapos : 0 < alpha.re
    · left
      simp [kappa, hapos]
    · right
      have haneg : alpha.re < 0 := lt_of_le_of_ne (not_lt.mp hapos) hare
      simp [kappa, hapos, haneg]
  let t : ℕ → ℝ := fun n => kappa * epsilon n
  have ht_ne (n : ℕ) : t n ≠ 0 :=
    mul_ne_zero hkappa_ne (ne_of_gt (hepsilonPos n))
  have htZero : Tendsto t atTop (nhds 0) := by
    simpa only [t, mul_zero] using
      (tendsto_const_nhds.mul hepsilonZero :
        Tendsto (fun n => kappa * epsilon n) atTop (nhds (kappa * 0)))
  let z : ℕ → ℂ := fun n => alpha + (t n : ℂ)
  have hzTend : Tendsto z atTop (nhds alpha) := by
    have htCast : Tendsto (fun n => (t n : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp htZero
    simpa [z] using tendsto_const_nhds.add htCast
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
  have hmpos : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hsigmaZero)
  have hnormalized := (xi_normalizedLogDeriv_tendsto_order sigma).comp hsWithin
  have hnormalizedXiC : Tendsto
      (fun n => (t n : ℂ) * logDeriv XiC (z n))
      atTop (nhds (m : ℂ)) := by
    have hfun : (fun n => (t n : ℂ) * logDeriv XiC (z n)) =
        fun n => (s n - sigma) * logDeriv xi (s n) := by
      funext n
      rw [logDeriv_XiC_eq_mul_I_logDeriv_xi]
      have hcoord : 1 / 2 + z n * I = s n := by
        simp [z, s, sigma]
        ring
      rw [hcoord]
      dsimp only [s]
      ring
    rw [hfun]
    simpa only [m, Function.comp_apply] using hnormalized
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
  have hnormSq : 0 < normSq alpha := normSq_pos.mpr halpha0
  have hquotLimit : (-((m : ℂ) / alpha)).im =
      (m : ℝ) * alpha.im / normSq alpha := by
    rw [neg_im, Complex.div_im]
    norm_num
  have hlimitFactor : 0 < (-((m : ℂ) / alpha)).im := by
    rw [hquotLimit]
    positivity
  obtain ⟨R, hR, h, _hhan, hh0, hfactor⟩ := xi_peel_ball sigma
  have hevBall : ∀ᶠ n in atTop, s n ∈ ball sigma R :=
    hsTend (isOpen_ball.mem_nhds (mem_ball_self hR))
  rcases hkappa_sign with hpos | hneg
  · have hlimitPos : 0 < alpha.re * (-((m : ℂ) / alpha)).im :=
      mul_pos hpos.1 hlimitFactor
    have hevPos : ∀ᶠ n in atTop,
        0 < t n * ((z n).re * (-logDeriv XiC (z n) / z n).im) :=
      hsectorScaled.eventually (eventually_gt_nhds hlimitPos)
    obtain ⟨n, hnBall, hnPos⟩ := (hevBall.and hevPos).exists
    have htneg : t n < 0 := mul_neg_of_neg_of_pos hpos.2 (hepsilonPos n)
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
      simp [z, s, sigma]
      ring
    refine ⟨z n, ?_, ?_, ?_, ?_⟩
    · simp [z]
      exact haim
    · simpa only [z, Complex.add_im, Complex.ofReal_im, add_zero] using haimhalf
    · rw [XiC, hcoord]
      exact hxis
    · nlinarith
  · have hlimitNeg : alpha.re * (-((m : ℂ) / alpha)).im < 0 :=
      mul_neg_of_neg_of_pos hneg.1 hlimitFactor
    have hevNeg : ∀ᶠ n in atTop,
        t n * ((z n).re * (-logDeriv XiC (z n) / z n).im) < 0 :=
      hsectorScaled.eventually (eventually_lt_nhds hlimitNeg)
    obtain ⟨n, hnBall, hnNeg⟩ := (hevBall.and hevNeg).exists
    have htpos : 0 < t n := mul_pos hneg.2 (hepsilonPos n)
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
      simp [z, s, sigma]
      ring
    refine ⟨z n, ?_, ?_, ?_, ?_⟩
    · simp [z]
      exact haim
    · simpa only [z, Complex.add_im, Complex.ofReal_im, add_zero] using haimhalf
    · rw [XiC, hcoord]
      exact hxis
    · nlinarith

/-- The target reciprocal-square sector sign excludes all off-line Xi zeros. -/
theorem riemannHypothesis_of_xiReciprocalSquareUpperSectorNonnegative
    (hsector : XiReciprocalSquareUpperSectorNonnegative) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hrhoGt : 1 / 2 < rho.re := mem_rightHalf.mp hrho
  have hrhoPos : 0 < rho.re := lt_trans (by norm_num) hrhoGt
  have hrhoLt : rho.re < 1 := xi_zero_re_lt_one hrhoPos hzero
  let sigma : ℂ := 1 - rho
  have hsigmaZero : xi sigma = 0 := by
    dsimp only [sigma]
    rw [xi_one_sub, hzero]
  have hsigmaPos : 0 < sigma.re := by
    dsimp only [sigma]
    simp only [sub_re, one_re]
    linarith
  have hsigmaHalf : sigma.re < 1 / 2 := by
    dsimp only [sigma]
    simp only [sub_re, one_re]
    linarith
  have hsigmaLt : sigma.re < 1 := lt_trans hsigmaHalf (by norm_num)
  have hsigmaIm : sigma.im ≠ 0 := by
    intro him
    have heq : sigma = (sigma.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hzreal : xi (sigma.re : ℂ) = 0 := by
      rw [← heq]
      exact hsigmaZero
    exact (xi_ne_zero_real_anchor hsigmaPos hsigmaLt) hzreal
  let alpha : ℂ := (sigma - 1 / 2) * (-I)
  have halphaIm : alpha.im = 1 / 2 - sigma.re := by
    simp [alpha, mul_im]
  have halphaRe : alpha.re = sigma.im := by
    simp [alpha, mul_re]
  have halphaImPos : 0 < alpha.im := by rw [halphaIm]; linarith
  have halphaImHalf : alpha.im < 1 / 2 := by rw [halphaIm]; linarith
  have halphaReNe : alpha.re ≠ 0 := by rwa [halphaRe]
  have hcoord : 1 / 2 + alpha * I = sigma := by
    dsimp only [alpha]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have halphaXi : XiC alpha = 0 := by
    rw [XiC, hcoord]
    exact hsigmaZero
  obtain ⟨z, hzpos, hzhalf, hzXi, hzneg⟩ :=
    exists_xiReciprocalSquareUpperSector_neg_of_zero
      halphaImPos halphaImHalf halphaReNe halphaXi
  exact (not_lt_of_ge (hsector z hzpos hzhalf hzXi)) hzneg

/-- **Source-to-RH reciprocal-square sector chain.**  The static quadrant sign of the explicit
continued prime--Gamma reciprocal-square transform forces the Riemann hypothesis. -/
theorem riemannHypothesis_of_continuedPrimeArchReciprocalSquareUpperSectorNonnegative
    (hsource : ContinuedPrimeArchReciprocalSquareUpperSectorNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiReciprocalSquareUpperSectorNonnegative
    (xiReciprocalSquareUpperSectorNonnegative_of_continuedPrimeArch hsource)

/-- Exact target-coordinate reciprocal-square sector criterion. -/
theorem xiReciprocalSquareUpperSectorNonnegative_iff_riemannHypothesis :
    XiReciprocalSquareUpperSectorNonnegative ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiReciprocalSquareUpperSectorNonnegative
  · intro hRH
    exact xiReciprocalSquareUpperSectorNonnegative_of_continuedPrimeArch
      (continuedPrimeArchReciprocalSquareUpperSectorNonnegative_of_riemannHypothesis hRH)

/-- **Exact source criterion.**  RH is equivalent to the sector sign of the single explicit
continued prime--Gamma reciprocal-square transform on the centered upper strip. -/
theorem continuedPrimeArchReciprocalSquareUpperSectorNonnegative_iff_riemannHypothesis :
    ContinuedPrimeArchReciprocalSquareUpperSectorNonnegative ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_continuedPrimeArchReciprocalSquareUpperSectorNonnegative,
    continuedPrimeArchReciprocalSquareUpperSectorNonnegative_of_riemannHypothesis⟩

end

end RHTower

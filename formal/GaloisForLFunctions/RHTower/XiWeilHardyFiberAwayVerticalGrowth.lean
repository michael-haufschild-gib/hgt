import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv
import GaloisForLFunctions.HTGeometry.PrimeResiduePickInertia
import GaloisForLFunctions.RHTower.WeightedLittlewoodRectangle
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.XiWeilHardyFiberPositiveHighFrequency

/-!
# Hardy-fiber deletion as vertical growth of an entire canonical product

Removing one complete Xi fiber from the genus-one relative resolvent is exactly the logarithmic
derivative of `xiCanonicalProductAway`.  The genus-one normalization is essential: its elementary
factor supplies the constant subtraction at the functional-equation centre.

For a Hardy critical fiber, RH is therefore equivalent to nonnegative vertical logarithmic-modulus
velocity of this one entire deflated product only in the positive high-frequency strip
`4 < Re z`, `0 < Im z < 1/2`.  Central and negative frequencies require no hypothesis.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A point off the Xi divisor is also off the divisor of every fiber-deleted canonical product. -/
theorem xiCanonicalProductAway_ne_zero_of_XiC_ne_zero
    (ρ : XiDivisorSupport) {z : ℂ} (hz : XiC z ≠ 0) :
    xiCanonicalProductAway ρ z ≠ 0 := by
  have hcan : xiCanonicalProduct z ≠ 0 := by
    intro hzero
    apply hz
    have hfactor := congrFun xiHadamardQuotient_mul_canonicalProduct z
    rw [Pi.mul_apply] at hfactor
    rw [← hfactor, hzero, mul_zero]
  intro haway
  apply hcan
  rw [xiCanonicalProduct_factorization_at_support ρ z, haway, mul_zero]

/-- Exact genus-one deletion identity: the logarithmic derivative of the entire product with the
`ρ` fiber removed is the full relative resolvent trace minus that complete finite fiber. -/
theorem logDeriv_xiCanonicalProductAway_eq_xiTrace_sub_fiber
    (ρ : XiDivisorSupport) {z : ℂ} (hz : XiC z ≠ 0) :
    logDeriv (xiCanonicalProductAway ρ) z =
      xiRelativeResolventTrace z -
        ∑ q ∈ xiZeroCopyFiber ρ, xiRelativeResolventTerm z q := by
  have hzaway : ∀ q : XiZeroCopyAway ρ, z ≠ xiSpectralPoint q.1 := by
    intro q hq
    apply hz
    rw [hq]
    exact XiC_xiSpectralPoint_eq_zero q.1
  have hlog := logDeriv_canonicalProductE1Indexed
    (a := fun q : XiZeroCopyAway ρ => xiSpectralPoint q.1)
    (fun q => xiSpectralPoint_ne_zero q.1)
    (xiCanonicalProductAway_inv_sq_summable ρ) hzaway
  have hterm : ∀ q : XiZeroCopyAway ρ,
      ((z - xiSpectralPoint q.1)⁻¹ + (xiSpectralPoint q.1)⁻¹) =
        xiRelativeResolventTerm z q.1 := by
    intro q
    rw [xiRelativeResolventTerm]
    rw [show z - xiSpectralPoint q.1 =
      -(xiSpectralPoint q.1 - z) by ring, inv_neg]
    ring
  have hsum : Summable (xiRelativeResolventTerm z) :=
    summable_xiRelativeResolventTerm hz
  have hsplit := hsum.sum_add_tsum_subtype_compl (xiZeroCopyFiber ρ)
  let e : XiZeroCopyAway ρ ≃
      {q : XiZeroCopy // q ∉ xiZeroCopyFiber ρ} :=
    { toFun := fun q =>
        ⟨q.1, by simpa only [mem_xiZeroCopyFiber] using q.2⟩
      invFun := fun q =>
        ⟨q.1, by simpa only [mem_xiZeroCopyFiber] using q.2⟩
      left_inv := fun q => by cases q; rfl
      right_inv := fun q => by cases q; rfl }
  have haway_tsum :=
    e.tsum_eq (fun q : {q : XiZeroCopy // q ∉ xiZeroCopyFiber ρ} =>
      xiRelativeResolventTerm z q.1)
  change (∑' q : XiZeroCopyAway ρ, xiRelativeResolventTerm z q.1) =
    ∑' q : {q : XiZeroCopy // q ∉ xiZeroCopyFiber ρ},
      xiRelativeResolventTerm z q.1 at haway_tsum
  change logDeriv
    (canonicalProductE1Indexed
      (fun q : XiZeroCopyAway ρ => xiSpectralPoint q.1)) z = _
  rw [hlog]
  simp_rw [hterm]
  rw [haway_tsum, xiRelativeResolventTrace, ← hsplit]
  ring

/-- On the continued prime--Gamma comparison domain, the fixed-fiber-deflated source trace is
literally the logarithmic derivative of the entire fiber-deleted canonical product. -/
theorem ccmFixedFiberDeflatedRelativeTrace_eq_logDeriv_xiCanonicalProductAway
    (ρ : XiDivisorSupport) {z : ℂ}
    (hspos : 0 < (1 / 2 + z * Complex.I).re)
    (hs1 : 1 / 2 + z * Complex.I ≠ 1)
    (hzeta : riemannZeta (1 / 2 + z * Complex.I) ≠ 0) :
    ccmFixedFiberDeflatedRelativeTrace ρ z =
      logDeriv (xiCanonicalProductAway ρ) z := by
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 hzeta
  rw [ccmFixedFiberDeflatedRelativeTrace_eq_xiTrace_sub_fiber ρ hspos hs1 hzeta,
    ← logDeriv_xiCanonicalProductAway_eq_xiTrace_sub_fiber ρ hXi]

/-- On a critical fiber, fixed-fiber deflation is exactly subtraction of a multiplicity-weighted
rank-one Nevanlinna--Pick kernel.  This identifies genus-one divisor deletion with the
Schur-complement chart used by Pick and de Branges methods. -/
theorem ccmFixedCriticalFiberDeflatedCauchyKernel_eq_sub_pickKernel
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    ccmFixedFiberDeflatedCauchyKernel ρ z w =
      ccmContinuedCauchyKernel z w -
        ((xiZeroCopyFiber ρ).card : ℂ) *
          GaloisForLFunctions.HTGeometry.pickKernel
            (GaloisForLFunctions.HTGeometry.cauchyAtom
              (xiSpectralPointSupport ρ).re) z w := by
  have hαim : (xiSpectralPointSupport ρ).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff ρ).2 hρ
  have hαreal : (((xiSpectralPointSupport ρ).re : ℝ) : ℂ) =
      xiSpectralPointSupport ρ := by
    apply Complex.ext <;> simp [hαim]
  have hzα : z ≠ xiSpectralPointSupport ρ := by
    intro heq
    apply hz
    rw [heq, hαim]
  have hwα : (starRingEnd ℂ) w ≠ xiSpectralPointSupport ρ := by
    intro heq
    apply hw
    have him := congrArg Complex.im heq
    simp only [Complex.conj_im, hαim] at him
    exact neg_eq_zero.mp him
  rw [ccmFixedFiberDeflatedCauchyKernel_eq_sub_rankOne ρ hzα hwα hzw,
    GaloisForLFunctions.HTGeometry.pickKernel_cauchyAtom
      (xiSpectralPointSupport ρ).re hz hw hzw]
  simp only [GaloisForLFunctions.HTGeometry.cauchyAtom, hαreal,
    map_inv₀, map_sub]
  rw [show (starRingEnd ℂ) (xiSpectralPointSupport ρ) =
      xiSpectralPointSupport ρ by
    apply Complex.ext <;> simp [hαim]]
  ring

/-- The deflated logarithmic derivative controls the vertical derivative of its entire product's
log modulus, with no branch of the complex logarithm. -/
theorem hasDerivAt_log_norm_xiCanonicalProductAway_vertical
    (ρ : XiDivisorSupport) {x y : ℝ}
    (hXi : XiC ((x : ℂ) + y * Complex.I) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => Real.log ‖xiCanonicalProductAway ρ
        ((x : ℂ) + u * Complex.I)‖)
      (-(logDeriv (xiCanonicalProductAway ρ)
        ((x : ℂ) + y * Complex.I)).im) y := by
  apply hasDerivAt_log_norm_vertical
  · exact (xiCanonicalProductAway_analytic ρ
      ((x : ℂ) + y * Complex.I) (Set.mem_univ _)).differentiableAt.hasDerivAt
  · exact xiCanonicalProductAway_ne_zero_of_XiC_ne_zero ρ hXi

/-- Positive-tail infinitesimal vertical log-modulus growth of one fiber-deleted entire product. -/
def FixedFiberAwayPositiveHighVerticalLogGrowth (ρ : XiDivisorSupport) : Prop :=
  ∀ z : ℂ, 4 < z.re → 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
      0 ≤ -(logDeriv (xiCanonicalProductAway ρ) z).im

/-- For a critical fiber, the entire-product vertical-growth condition is exactly the explicit
prime--Gamma Poisson margin. -/
theorem fixedCriticalFiberAwayPositiveHighVerticalLogGrowth_iff_primeGammaMargin
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) :
    FixedFiberAwayPositiveHighVerticalLogGrowth ρ ↔
      FixedFiberPrimeGammaPositiveHighPoissonMargin ρ := by
  have hαim : (xiSpectralPointSupport ρ).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff ρ).2 hρ
  constructor
  · intro hgrowth z hzre hzim hzimhalf hzeta
    have hspos : 0 < (1 / 2 + z * I).re := centeredAbscissa_re_pos hzimhalf
    have hs1 : 1 / 2 + z * I ≠ 1 := centeredAbscissa_ne_one hzim
    have hg := hgrowth z hzre hzim hzimhalf hzeta
    rw [← ccmFixedFiberDeflatedRelativeTrace_eq_logDeriv_xiCanonicalProductAway
      ρ hspos hs1 hzeta,
      ccmFixedFiberDeflatedRelativeTrace_im_eq_add_poisson ρ z hαim] at hg
    linarith
  · intro hmargin z hzre hzim hzimhalf hzeta
    have hspos : 0 < (1 / 2 + z * I).re := centeredAbscissa_re_pos hzimhalf
    have hs1 : 1 / 2 + z * I ≠ 1 := centeredAbscissa_ne_one hzim
    have hm := hmargin z hzre hzim hzimhalf hzeta
    rw [← ccmFixedFiberDeflatedRelativeTrace_eq_logDeriv_xiCanonicalProductAway
      ρ hspos hs1 hzeta,
      ccmFixedFiberDeflatedRelativeTrace_im_eq_add_poisson ρ z hαim]
    linarith

/-- RH is equivalent to positive-tail vertical log-modulus growth of one entire canonical product
after deleting any fixed critical Xi fiber. -/
theorem riemannHypothesis_iff_fixedCriticalFiberAwayPositiveHighVerticalLogGrowth
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) :
    RiemannHypothesis ↔ FixedFiberAwayPositiveHighVerticalLogGrowth ρ := by
  rw [riemannHypothesis_iff_fixedCriticalFiber_positiveHighPoissonMargin ρ hρ,
    ← fixedCriticalFiberAwayPositiveHighVerticalLogGrowth_iff_primeGammaMargin ρ hρ]

/-- Hardy supplies an unconditional critical fiber for the one-deflated-entire-function vertical
growth criterion. -/
theorem exists_hardyCriticalFiber_awayPositiveHighVerticalLogGrowth_criterion :
    ∃ ρ : XiDivisorSupport,
      (ρ : ℂ).re = 1 / 2 ∧
        (RiemannHypothesis ↔ FixedFiberAwayPositiveHighVerticalLogGrowth ρ) := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  exact ⟨ρ, hρ,
    riemannHypothesis_iff_fixedCriticalFiberAwayPositiveHighVerticalLogGrowth ρ hρ⟩

end

end RHTower

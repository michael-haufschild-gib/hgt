import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyFunctionalEquationPairPolarization
import GaloisForLFunctions.RHTower.BurnolHedenmalmCompletionDomain

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

/-!
# Completed Xi source line-conjugate Dirac resolvent

Actual completed first-divided Xi vector transforms by pointwise conjugation under critical-line
reflection. Its invariant and anti-invariant real sectors form an exact driven Dirac system for
maximal real-coordinate multiplication. Both sectors have literal Lorentzian source-response
kernels. Off critical line, odd sector is nonzero and its radial source work is strictly positive
almost everywhere.

Results are unconditional: no root-location, simplicity, positivity, landing map, or spectral
hypothesis is assumed. They classify why formal self-adjointness does not force centered spectral
coordinate real: common nonzero Xi source actively drives paired response.
-/

noncomputable section

namespace RHTower

private theorem completedXiLinePairEven_algebra (G x a b : ℂ)
    (hm : x - (a + Complex.I * b) ≠ 0)
    (hp : x - (a - Complex.I * b) ≠ 0) :
    (1 / 2 : ℂ) *
        (G / (x - (a + Complex.I * b)) +
          G / (x - (a - Complex.I * b))) =
      G * (x - a) / ((x - a) ^ 2 + b ^ 2) := by
  have hprod :
      (x - (a + Complex.I * b)) * (x - (a - Complex.I * b)) =
        (x - a) ^ 2 + b ^ 2 := by
    calc
      _ = (x - a) ^ 2 - (Complex.I * b) ^ 2 := by ring
      _ = _ := by rw [mul_pow, Complex.I_sq]; ring
  rw [← hprod]
  field_simp [hm, hp]
  ring

private theorem completedXiLinePairOdd_algebra (G x a b : ℂ)
    (hm : x - (a + Complex.I * b) ≠ 0)
    (hp : x - (a - Complex.I * b) ≠ 0) :
    (-Complex.I / 2 : ℂ) *
        (G / (x - (a + Complex.I * b)) -
          G / (x - (a - Complex.I * b))) =
      G * b / ((x - a) ^ 2 + b ^ 2) := by
  have hprod :
      (x - (a + Complex.I * b)) * (x - (a - Complex.I * b)) =
        (x - a) ^ 2 + b ^ 2 := by
    calc
      _ = (x - a) ^ 2 - (Complex.I * b) ^ 2 := by ring
      _ = _ := by rw [mul_pow, Complex.I_sq]; ring
  rw [← hprod]
  field_simp [hm, hp]
  ring_nf
  simp only [Complex.I_sq, neg_mul, one_mul]
  ring

theorem xiSpectralPointSupport_lineConj (rho : XiDivisorSupport) :
    xiSpectralPointSupport (xiZeroLineConjEquiv rho) =
      (starRingEnd ℂ) (xiSpectralPointSupport rho) := by
  rw [xiSpectralPointSupport, xiSpectralPointSupport,
    xiZeroLineConjEquiv_apply]
  simp only [map_mul, map_sub, map_neg, conj_I, map_div₀, map_one,
    map_ofNat]
  ring

theorem completedXiFirstDividedFunction_lineConj (rho : XiDivisorSupport) {x : ℝ}
    (hxXi : XiC (x : ℂ) ≠ 0) :
    completedXiFirstDividedFunction (xiZeroLineConjEquiv rho) x =
      (starRingEnd ℂ) (completedXiFirstDividedFunction rho x) := by
  have hxrho : (x : ℂ) ≠ xiSpectralPointSupport rho := by
    intro hx
    apply hxXi
    rw [hx]
    exact XiC_xiSpectralPointSupport_eq_zero rho
  have hxpartner : (x : ℂ) ≠
      xiSpectralPointSupport (xiZeroLineConjEquiv rho) := by
    intro hx
    apply hxXi
    rw [hx]
    exact XiC_xiSpectralPointSupport_eq_zero (xiZeroLineConjEquiv rho)
  rw [completedXiFirstDividedFunction, completedXiFirstDividedFunction,
    xiThetaDividedChain_one_apply_of_ne _ _ hxpartner
      (XiC_xiSpectralPointSupport_eq_zero (xiZeroLineConjEquiv rho)),
    xiThetaDividedChain_one_apply_of_ne _ _ hxrho
      (XiC_xiSpectralPointSupport_eq_zero rho),
    xiSpectralPointSupport_lineConj]
  simp only [map_div₀, map_sub, Complex.conj_ofReal]
  rw [XiC_ofReal]
  simp

theorem completedXiFirstDividedL2_lineConj (rho : XiDivisorSupport) :
    completedXiFirstDividedL2 (xiZeroLineConjEquiv rho) =
      star (completedXiFirstDividedL2 rho) := by
  apply Lp.ext
  filter_upwards [completedXiFirstDividedL2_ae (xiZeroLineConjEquiv rho),
    completedXiFirstDividedL2_ae rho,
    Lp.coeFn_star (completedXiFirstDividedL2 rho),
    XiC_ofReal_ne_zero_ae] with x hpartner hrho hstar hXi
  rw [hpartner, hstar]
  simpa only [Pi.star_apply, hrho, starRingEnd_apply] using completedXiFirstDividedFunction_lineConj rho hXi

theorem xiThetaFourierSourceL2_star :
    star xiThetaFourierSourceL2 = xiThetaFourierSourceL2 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star xiThetaFourierSourceL2,
    xiThetaFourierSourceL2_ae] with x hstar hsource
  rw [hstar]
  simp only [Pi.star_apply, hsource, XiC_ofReal]
  exact Complex.conj_ofReal (Xi x)

theorem star_BurnolCompletedSpectralL2_add (f g : BurnolCompletedSpectralL2) :
    star (f + g) = star f + star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g,
    Lp.coeFn_add (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g] with
      x hstar hadd haddStar hf hg
  rw [hstar]
  calc
    star ((f + g : BurnolCompletedSpectralL2) x) = star (f x + g x) := by
      rw [hadd, Pi.add_apply]
    _ = star (f x) + star (g x) := star_add _ _
    _ = (star f : BurnolCompletedSpectralL2) x +
        (star g : BurnolCompletedSpectralL2) x := by
      rw [hf, hg, Pi.star_apply, Pi.star_apply]
    _ = (star f + star g : BurnolCompletedSpectralL2) x := by
      rw [haddStar, Pi.add_apply]

theorem star_BurnolCompletedSpectralL2_smul (c : ℂ) (f : BurnolCompletedSpectralL2) :
    star (c • f) = star c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_smul (star c) (star f), Lp.coeFn_star f] with
      x hstar hsmul hsmulStar hf
  rw [hstar]
  calc
    star ((c • f : BurnolCompletedSpectralL2) x) = star (c * f x) := by
      rw [hsmul, Pi.smul_apply, smul_eq_mul]
    _ = star c * star (f x) := map_mul (starRingEnd ℂ) c (f x)
    _ = star c * (star f : BurnolCompletedSpectralL2) x := by
      rw [hf, Pi.star_apply]
    _ = (star c • star f : BurnolCompletedSpectralL2) x := by
      rw [hsmulStar, Pi.smul_apply, smul_eq_mul]

def completedXiFirstDividedDomainVector (rho : XiDivisorSupport) : maximalRealCoordinate.domain :=
  ⟨completedXiFirstDividedL2 rho,
    completedXiFirstDividedL2_mem_maximalRealCoordinateDomain rho⟩

def completedXiLinePairEvenDomain (rho : XiDivisorSupport) : maximalRealCoordinate.domain :=
  (1 / 2 : ℂ) •
    (completedXiFirstDividedDomainVector rho + completedXiFirstDividedDomainVector (xiZeroLineConjEquiv rho))

def completedXiLinePairOddDomain (rho : XiDivisorSupport) : maximalRealCoordinate.domain :=
  (-Complex.I / 2 : ℂ) •
    (completedXiFirstDividedDomainVector rho - completedXiFirstDividedDomainVector (xiZeroLineConjEquiv rho))

def completedXiLinePairEven (rho : XiDivisorSupport) : BurnolCompletedSpectralL2 :=
  completedXiLinePairEvenDomain rho

def completedXiLinePairOdd (rho : XiDivisorSupport) : BurnolCompletedSpectralL2 :=
  completedXiLinePairOddDomain rho

theorem completedXiLinePairEven_eq (rho : XiDivisorSupport) :
    completedXiLinePairEven rho = (1 / 2 : ℂ) •
      (completedXiFirstDividedL2 rho +
        completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)) := rfl

theorem completedXiLinePairOdd_eq (rho : XiDivisorSupport) :
    completedXiLinePairOdd rho = (-Complex.I / 2 : ℂ) •
      (completedXiFirstDividedL2 rho -
        completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)) := rfl

theorem completedXiLinePairEven_star (rho : XiDivisorSupport) :
    star (completedXiLinePairEven rho) = completedXiLinePairEven rho := by
  have hstarRho := completedXiFirstDividedL2_lineConj rho
  have hstarPartner :
      star (completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)) =
        completedXiFirstDividedL2 rho := by
    rw [← completedXiFirstDividedL2_lineConj (xiZeroLineConjEquiv rho),
      xiZeroLineConjEquiv_involutive rho]
  rw [completedXiLinePairEven_eq, star_BurnolCompletedSpectralL2_smul, star_BurnolCompletedSpectralL2_add]
  rw [← hstarRho, hstarPartner]
  have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    change (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2
    simp only [map_div₀, map_one, map_ofNat]
  rw [hhalf]
  module

theorem completedXiLinePairOdd_star (rho : XiDivisorSupport) :
    star (completedXiLinePairOdd rho) = completedXiLinePairOdd rho := by
  have hstarRho := completedXiFirstDividedL2_lineConj rho
  have hstarPartner :
      star (completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)) =
        completedXiFirstDividedL2 rho := by
    rw [← completedXiFirstDividedL2_lineConj (xiZeroLineConjEquiv rho),
      xiZeroLineConjEquiv_involutive rho]
  rw [completedXiLinePairOdd_eq]
  rw [show completedXiFirstDividedL2 rho -
      completedXiFirstDividedL2 (xiZeroLineConjEquiv rho) =
        completedXiFirstDividedL2 rho +
          -completedXiFirstDividedL2 (xiZeroLineConjEquiv rho) by abel]
  rw [star_BurnolCompletedSpectralL2_smul, star_BurnolCompletedSpectralL2_add]
  have hstarNeg :
      star (-completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)) =
        -star (completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)) := by
    rw [show -completedXiFirstDividedL2 (xiZeroLineConjEquiv rho) =
      (-1 : ℂ) • completedXiFirstDividedL2 (xiZeroLineConjEquiv rho) by simp,
      star_BurnolCompletedSpectralL2_smul]
    simp
  rw [hstarNeg, ← hstarRho, hstarPartner]
  have hscalar : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by
    change (starRingEnd ℂ) (-Complex.I / 2 : ℂ) = Complex.I / 2
    simp only [map_div₀, map_neg, conj_I, map_ofNat, neg_neg]
  rw [hscalar]
  module

theorem completedXiLinePairOdd_eq_zero_iff (rho : XiDivisorSupport) :
    completedXiLinePairOdd rho = 0 ↔ (xiSpectralPointSupport rho).im = 0 := by
  constructor
  · intro hodd
    rw [completedXiLinePairOdd_eq] at hodd
    have hscalar : (-Complex.I / 2 : ℂ) ≠ 0 := by
      apply div_ne_zero <;> norm_num
    have hdiff : completedXiFirstDividedL2 rho -
        completedXiFirstDividedL2 (xiZeroLineConjEquiv rho) = 0 :=
      (smul_eq_zero.mp hodd).resolve_left hscalar
    have hf : completedXiFirstDividedL2 rho =
        completedXiFirstDividedL2 (xiZeroLineConjEquiv rho) :=
      sub_eq_zero.mp hdiff
    have hdom : completedXiFirstDividedDomainVector rho = completedXiFirstDividedDomainVector (xiZeroLineConjEquiv rho) :=
      Subtype.ext hf
    have heq :
        xiSpectralPointSupport rho • completedXiFirstDividedL2 rho +
            xiThetaFourierSourceL2 =
          xiSpectralPointSupport (xiZeroLineConjEquiv rho) •
              completedXiFirstDividedL2 (xiZeroLineConjEquiv rho) +
            xiThetaFourierSourceL2 := by
      calc
        _ = maximalRealCoordinate (completedXiFirstDividedDomainVector rho) :=
          (maximalRealCoordinate_completedXiFirstDividedL2 rho).symm
        _ = maximalRealCoordinate (completedXiFirstDividedDomainVector (xiZeroLineConjEquiv rho)) := by rw [hdom]
        _ = _ := maximalRealCoordinate_completedXiFirstDividedL2
          (xiZeroLineConjEquiv rho)
    have hsmul :
        (xiSpectralPointSupport rho -
            (starRingEnd ℂ) (xiSpectralPointSupport rho)) •
          completedXiFirstDividedL2 rho = 0 := by
      rw [sub_smul]
      rw [← xiSpectralPointSupport_lineConj rho]
      rw [← hf] at heq
      exact sub_eq_zero.mpr (add_right_cancel heq)
    have hscalarZero : xiSpectralPointSupport rho -
        (starRingEnd ℂ) (xiSpectralPointSupport rho) = 0 :=
      (smul_eq_zero.mp hsmul).resolve_right
        (completedXiFirstDividedL2_ne_zero rho)
    have hzconj := sub_eq_zero.mp hscalarZero
    have him := congrArg Complex.im hzconj
    simp only [Complex.conj_im] at him
    linarith
  · intro him
    have hzconj : (starRingEnd ℂ) (xiSpectralPointSupport rho) =
        xiSpectralPointSupport rho := by
      apply Complex.ext
      · exact Complex.conj_re _
      · simp only [Complex.conj_im, him, neg_zero]
    have hsupport : xiSpectralPointSupport (xiZeroLineConjEquiv rho) =
        xiSpectralPointSupport rho := (xiSpectralPointSupport_lineConj rho).trans hzconj
    have hrho : xiZeroLineConjEquiv rho = rho :=
      xiSpectralPointSupport_injective hsupport
    rw [completedXiLinePairOdd_eq, hrho, sub_self, smul_zero]

theorem completedXiLinePairOdd_ne_zero_iff (rho : XiDivisorSupport) :
    completedXiLinePairOdd rho ≠ 0 ↔ (xiSpectralPointSupport rho).im ≠ 0 := by
  exact not_congr (completedXiLinePairOdd_eq_zero_iff rho)

theorem completedXiLinePair_reconstruction (rho : XiDivisorSupport) :
    completedXiLinePairEven rho + Complex.I • completedXiLinePairOdd rho =
      completedXiFirstDividedL2 rho := by
  rw [completedXiLinePairEven_eq, completedXiLinePairOdd_eq, smul_smul]
  have hI : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
    apply Complex.ext <;> norm_num
  rw [hI]
  module

theorem completedXiLinePair_partner_reconstruction (rho : XiDivisorSupport) :
    completedXiLinePairEven rho - Complex.I • completedXiLinePairOdd rho =
      completedXiFirstDividedL2 (xiZeroLineConjEquiv rho) := by
  rw [completedXiLinePairEven_eq, completedXiLinePairOdd_eq, smul_smul]
  have hI : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
    apply Complex.ext <;> norm_num
  rw [hI]
  module

theorem all_completedXiLinePairOdd_eq_zero_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport, completedXiLinePairOdd rho = 0) ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_xiZeroLineConj_fixed]
  constructor
  · intro h rho
    have him := (completedXiLinePairOdd_eq_zero_iff rho).mp (h rho)
    have hzconj : (starRingEnd ℂ) (xiSpectralPointSupport rho) =
        xiSpectralPointSupport rho := by
      apply Complex.ext
      · exact Complex.conj_re _
      · simp only [Complex.conj_im, him, neg_zero]
    apply xiSpectralPointSupport_injective
    exact (xiSpectralPointSupport_lineConj rho).trans hzconj
  · intro h rho
    rw [completedXiLinePairOdd_eq, h rho, sub_self, smul_zero]

def completedXiLinePairDenominator (rho : XiDivisorSupport) (x : ℝ) : ℝ :=
  (x - (xiSpectralPointSupport rho).re) ^ 2 +
    (xiSpectralPointSupport rho).im ^ 2

theorem completedXiLinePairDenominator_pos_of_XiC_ne_zero (rho : XiDivisorSupport) {x : ℝ}
    (hXi : XiC (x : ℂ) ≠ 0) : 0 < completedXiLinePairDenominator rho x := by
  have hnonneg : 0 ≤ completedXiLinePairDenominator rho x := by
    rw [completedXiLinePairDenominator]
    positivity
  refine lt_of_le_of_ne hnonneg (Ne.symm ?_)
  intro hzero
  have hx : x - (xiSpectralPointSupport rho).re = 0 := by
    rw [completedXiLinePairDenominator] at hzero
    nlinarith [sq_nonneg (x - (xiSpectralPointSupport rho).re),
      sq_nonneg (xiSpectralPointSupport rho).im]
  have him : (xiSpectralPointSupport rho).im = 0 := by
    rw [completedXiLinePairDenominator] at hzero
    nlinarith [sq_nonneg (x - (xiSpectralPointSupport rho).re),
      sq_nonneg (xiSpectralPointSupport rho).im]
  have heq : (x : ℂ) = xiSpectralPointSupport rho := by
    apply Complex.ext
    · simpa using sub_eq_zero.mp hx
    · simpa using him.symm
  apply hXi
  rw [heq]
  exact XiC_xiSpectralPointSupport_eq_zero rho

theorem completedXiFirstDividedL2_quotient_ae (rho : XiDivisorSupport) :
    (completedXiFirstDividedL2 rho : ℝ → ℂ) =ᵐ[volume]
      fun x => XiC (x : ℂ) / ((x : ℂ) - xiSpectralPointSupport rho) := by
  filter_upwards [completedXiFirstDividedL2_ae rho,
    XiC_ofReal_ne_zero_ae] with x hx hXi
  rw [hx, completedXiFirstDividedFunction]
  have hne : (x : ℂ) ≠ xiSpectralPointSupport rho := by
    intro heq
    apply hXi
    rw [heq]
    exact XiC_xiSpectralPointSupport_eq_zero rho
  exact xiThetaDividedChain_one_apply_of_ne _ _ hne
    (XiC_xiSpectralPointSupport_eq_zero rho)

theorem completedXiLinePairEven_lorentzian_ae (rho : XiDivisorSupport) :
    (completedXiLinePairEven rho : ℝ → ℂ) =ᵐ[volume] fun x =>
      XiC (x : ℂ) * ((x - (xiSpectralPointSupport rho).re : ℝ) : ℂ) /
        (completedXiLinePairDenominator rho x : ℂ) := by
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ)
      (completedXiFirstDividedL2 rho +
        completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)),
    Lp.coeFn_add (completedXiFirstDividedL2 rho)
      (completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)),
    completedXiFirstDividedL2_quotient_ae rho,
    completedXiFirstDividedL2_quotient_ae (xiZeroLineConjEquiv rho),
    XiC_ofReal_ne_zero_ae] with x hsmul hadd hq hp hXi
  rw [completedXiLinePairEven_eq, hsmul, Pi.smul_apply, smul_eq_mul, hadd, Pi.add_apply,
    hq, hp, xiSpectralPointSupport_lineConj]
  have hne : (x : ℂ) ≠ xiSpectralPointSupport rho := by
    intro heq
    apply hXi
    rw [heq]
    exact XiC_xiSpectralPointSupport_eq_zero rho
  have hnePartner : (x : ℂ) ≠
      xiSpectralPointSupport (xiZeroLineConjEquiv rho) := by
    intro heq
    apply hXi
    rw [heq]
    exact XiC_xiSpectralPointSupport_eq_zero (xiZeroLineConjEquiv rho)
  have hz : xiSpectralPointSupport rho =
      ((xiSpectralPointSupport rho).re : ℂ) +
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ) := by
    apply Complex.ext <;> norm_num
  have hzc : (starRingEnd ℂ) (xiSpectralPointSupport rho) =
      ((xiSpectralPointSupport rho).re : ℂ) -
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ) := by
    apply Complex.ext <;> norm_num
  have hminus : (x : ℂ) -
      (((xiSpectralPointSupport rho).re : ℂ) +
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ)) ≠ 0 := by
    rw [← hz]
    exact sub_ne_zero.mpr hne
  have hplus : (x : ℂ) -
      (((xiSpectralPointSupport rho).re : ℂ) -
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ)) ≠ 0 := by
    have := sub_ne_zero.mpr hnePartner
    rw [xiSpectralPointSupport_lineConj, hzc] at this
    exact this
  have hdenEq : (completedXiLinePairDenominator rho x : ℂ) =
      (((x : ℂ) - ((xiSpectralPointSupport rho).re : ℂ)) ^ 2 +
        ((xiSpectralPointSupport rho).im : ℂ) ^ 2) := by
    rw [completedXiLinePairDenominator]
    push_cast
    rfl
  rw [hz]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  rw [hdenEq]
  rw [show (((x - (xiSpectralPointSupport rho).re : ℝ) : ℂ)) =
      (x : ℂ) - ((xiSpectralPointSupport rho).re : ℂ) by push_cast; rfl]
  simpa only [sub_eq_add_neg, neg_mul] using
    completedXiLinePairEven_algebra (XiC (x : ℂ)) (x : ℂ)
      ((xiSpectralPointSupport rho).re : ℂ)
      ((xiSpectralPointSupport rho).im : ℂ) hminus hplus

theorem completedXiLinePairOdd_lorentzian_ae (rho : XiDivisorSupport) :
    (completedXiLinePairOdd rho : ℝ → ℂ) =ᵐ[volume] fun x =>
      XiC (x : ℂ) * ((xiSpectralPointSupport rho).im : ℂ) /
        (completedXiLinePairDenominator rho x : ℂ) := by
  filter_upwards [Lp.coeFn_smul (-Complex.I / 2 : ℂ)
      (completedXiFirstDividedL2 rho -
        completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)),
    Lp.coeFn_sub (completedXiFirstDividedL2 rho)
      (completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)),
    completedXiFirstDividedL2_quotient_ae rho,
    completedXiFirstDividedL2_quotient_ae (xiZeroLineConjEquiv rho),
    XiC_ofReal_ne_zero_ae] with x hsmul hsub hq hp hXi
  rw [completedXiLinePairOdd_eq, hsmul, Pi.smul_apply, smul_eq_mul, hsub, Pi.sub_apply,
    hq, hp, xiSpectralPointSupport_lineConj]
  have hne : (x : ℂ) ≠ xiSpectralPointSupport rho := by
    intro heq
    apply hXi
    rw [heq]
    exact XiC_xiSpectralPointSupport_eq_zero rho
  have hnePartner : (x : ℂ) ≠
      xiSpectralPointSupport (xiZeroLineConjEquiv rho) := by
    intro heq
    apply hXi
    rw [heq]
    exact XiC_xiSpectralPointSupport_eq_zero (xiZeroLineConjEquiv rho)
  have hz : xiSpectralPointSupport rho =
      ((xiSpectralPointSupport rho).re : ℂ) +
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ) := by
    apply Complex.ext <;> norm_num
  have hzc : (starRingEnd ℂ) (xiSpectralPointSupport rho) =
      ((xiSpectralPointSupport rho).re : ℂ) -
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ) := by
    apply Complex.ext <;> norm_num
  have hminus : (x : ℂ) -
      (((xiSpectralPointSupport rho).re : ℂ) +
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ)) ≠ 0 := by
    rw [← hz]
    exact sub_ne_zero.mpr hne
  have hplus : (x : ℂ) -
      (((xiSpectralPointSupport rho).re : ℂ) -
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ)) ≠ 0 := by
    have := sub_ne_zero.mpr hnePartner
    rw [xiSpectralPointSupport_lineConj, hzc] at this
    exact this
  have hdenEq : (completedXiLinePairDenominator rho x : ℂ) =
      (((x : ℂ) - ((xiSpectralPointSupport rho).re : ℂ)) ^ 2 +
        ((xiSpectralPointSupport rho).im : ℂ) ^ 2) := by
    rw [completedXiLinePairDenominator]
    push_cast
    rfl
  rw [hz]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_add, one_mul]
  rw [hdenEq]
  simpa only [sub_eq_add_neg, neg_mul] using
    completedXiLinePairOdd_algebra (XiC (x : ℂ)) (x : ℂ)
      ((xiSpectralPointSupport rho).re : ℂ)
      ((xiSpectralPointSupport rho).im : ℂ) hminus hplus

def burnolCompletedRadialSourceWorkDensity (rho : XiDivisorSupport) (x : ℝ) : ℝ :=
  (xiSpectralPointSupport rho).im *
    ((starRingEnd ℂ) ((completedXiLinePairOdd rho : ℝ → ℂ) x) * XiC (x : ℂ)).re

theorem burnolCompletedRadialSourceWorkDensity_pos_ae (rho : XiDivisorSupport)
    (hb : (xiSpectralPointSupport rho).im ≠ 0) :
    ∀ᵐ x : ℝ ∂volume, 0 < burnolCompletedRadialSourceWorkDensity rho x := by
  filter_upwards [completedXiLinePairOdd_lorentzian_ae rho,
    XiC_ofReal_ne_zero_ae] with x hodd hXi
  rw [burnolCompletedRadialSourceWorkDensity, hodd, XiC_ofReal]
  have hXiReal : Xi x ≠ 0 := by
    intro hzero
    apply hXi
    rw [XiC_ofReal, hzero]
    norm_num
  have hdenPos := completedXiLinePairDenominator_pos_of_XiC_ne_zero rho hXi
  have hrealQuot :
      (Xi x : ℂ) * ((xiSpectralPointSupport rho).im : ℂ) /
          (completedXiLinePairDenominator rho x : ℂ) =
        ((Xi x * (xiSpectralPointSupport rho).im /
          completedXiLinePairDenominator rho x : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hrealQuot, Complex.conj_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [show (xiSpectralPointSupport rho).im *
      (Xi x * (xiSpectralPointSupport rho).im /
        completedXiLinePairDenominator rho x * Xi x) =
      ((xiSpectralPointSupport rho).im ^ 2 * Xi x ^ 2) /
        completedXiLinePairDenominator rho x by ring]
  exact div_pos (mul_pos (sq_pos_of_ne_zero hb) (sq_pos_of_ne_zero hXiReal)) hdenPos

theorem completedXiLinePairEven_recurrence (rho : XiDivisorSupport) :
    maximalRealCoordinate (completedXiLinePairEvenDomain rho) =
      ((xiSpectralPointSupport rho).re : ℂ) • completedXiLinePairEven rho -
        ((xiSpectralPointSupport rho).im : ℂ) • completedXiLinePairOdd rho +
        xiThetaFourierSourceL2 := by
  have hrho := maximalRealCoordinate_completedXiFirstDividedL2 rho
  have hpartner := maximalRealCoordinate_completedXiFirstDividedL2
    (xiZeroLineConjEquiv rho)
  have hsupport := xiSpectralPointSupport_lineConj rho
  have hz : xiSpectralPointSupport rho =
      ((xiSpectralPointSupport rho).re : ℂ) +
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ) := by
    apply Complex.ext <;> norm_num
  have hzc : (starRingEnd ℂ) (xiSpectralPointSupport rho) =
      ((xiSpectralPointSupport rho).re : ℂ) -
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ) := by
    apply Complex.ext <;> norm_num
  change maximalRealCoordinate.toFun (completedXiLinePairEvenDomain rho) = _
  rw [completedXiLinePairEvenDomain, maximalRealCoordinate.toFun.map_smul,
    maximalRealCoordinate.toFun.map_add]
  change (1 / 2 : ℂ) •
      (maximalRealCoordinate (completedXiFirstDividedDomainVector rho) +
        maximalRealCoordinate (completedXiFirstDividedDomainVector (xiZeroLineConjEquiv rho))) = _
  simp only [completedXiFirstDividedDomainVector]
  rw [hrho, hpartner, hsupport, hzc, hz]
  rw [completedXiLinePairEven_eq, completedXiLinePairOdd_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add, one_mul]
  module

theorem completedXiLinePairOdd_recurrence (rho : XiDivisorSupport) :
    maximalRealCoordinate (completedXiLinePairOddDomain rho) =
      ((xiSpectralPointSupport rho).im : ℂ) • completedXiLinePairEven rho +
        ((xiSpectralPointSupport rho).re : ℂ) • completedXiLinePairOdd rho := by
  have hrho := maximalRealCoordinate_completedXiFirstDividedL2 rho
  have hpartner := maximalRealCoordinate_completedXiFirstDividedL2
    (xiZeroLineConjEquiv rho)
  have hsupport := xiSpectralPointSupport_lineConj rho
  have hz : xiSpectralPointSupport rho =
      ((xiSpectralPointSupport rho).re : ℂ) +
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ) := by
    apply Complex.ext <;> norm_num
  have hzc : (starRingEnd ℂ) (xiSpectralPointSupport rho) =
      ((xiSpectralPointSupport rho).re : ℂ) -
        Complex.I * ((xiSpectralPointSupport rho).im : ℂ) := by
    apply Complex.ext <;> norm_num
  have hcoefPlus :
      (-Complex.I / 2) *
          (((xiSpectralPointSupport rho).re : ℂ) +
            Complex.I * ((xiSpectralPointSupport rho).im : ℂ)) =
        ((xiSpectralPointSupport rho).im : ℂ) / 2 +
          ((xiSpectralPointSupport rho).re : ℂ) * (-Complex.I / 2) := by
    apply Complex.ext <;> norm_num <;> ring
  have hcoefMinus :
      (-Complex.I / 2) *
          (((xiSpectralPointSupport rho).re : ℂ) -
            Complex.I * ((xiSpectralPointSupport rho).im : ℂ)) =
        -((xiSpectralPointSupport rho).im : ℂ) / 2 +
          ((xiSpectralPointSupport rho).re : ℂ) * (-Complex.I / 2) := by
    apply Complex.ext <;> norm_num <;> ring
  change maximalRealCoordinate.toFun (completedXiLinePairOddDomain rho) = _
  rw [completedXiLinePairOddDomain, maximalRealCoordinate.toFun.map_smul,
    maximalRealCoordinate.toFun.map_sub]
  change (-Complex.I / 2 : ℂ) •
      (maximalRealCoordinate (completedXiFirstDividedDomainVector rho) -
        maximalRealCoordinate (completedXiFirstDividedDomainVector (xiZeroLineConjEquiv rho))) = _
  simp only [completedXiFirstDividedDomainVector]
  rw [hrho, hpartner, hsupport, hzc, hz]
  rw [completedXiLinePairEven_eq, completedXiLinePairOdd_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add, one_mul]
  simp only [smul_add, smul_sub, smul_smul]
  rw [hcoefPlus, hcoefMinus]
  module

/-! ## Exact source-work balance -/

/-- Radial work done by completed Xi source on anti-invariant response. -/
def burnolCompletedRadialSourceWork (rho : XiDivisorSupport) : ℝ :=
  (xiSpectralPointSupport rho).im *
    (inner ℂ (completedXiLinePairOdd rho) xiThetaFourierSourceL2).re

/-- **Source-work identity.** Formal self-adjointness and driven Dirac system force radial source
work to equal spectral width squared times total pair-response energy. -/
theorem burnolCompletedRadialSourceWork_eq (rho : XiDivisorSupport) :
    burnolCompletedRadialSourceWork rho =
      (xiSpectralPointSupport rho).im ^ 2 *
        (‖completedXiLinePairEven rho‖ ^ 2 + ‖completedXiLinePairOdd rho‖ ^ 2) := by
  have hadjoint := maximalRealCoordinate_formalSelfAdjoint
    (completedXiLinePairOddDomain rho) (completedXiLinePairEvenDomain rho)
  rw [completedXiLinePairOdd_recurrence, completedXiLinePairEven_recurrence] at hadjoint
  change inner ℂ
      (((xiSpectralPointSupport rho).im : ℂ) • completedXiLinePairEven rho +
        ((xiSpectralPointSupport rho).re : ℂ) • completedXiLinePairOdd rho)
      (completedXiLinePairEven rho) =
    inner ℂ (completedXiLinePairOdd rho)
      (((xiSpectralPointSupport rho).re : ℂ) • completedXiLinePairEven rho -
        ((xiSpectralPointSupport rho).im : ℂ) • completedXiLinePairOdd rho +
          xiThetaFourierSourceL2) at hadjoint
  have hinner :
      inner ℂ (completedXiLinePairOdd rho) xiThetaFourierSourceL2 =
        ((xiSpectralPointSupport rho).im : ℂ) *
          (inner ℂ (completedXiLinePairEven rho) (completedXiLinePairEven rho) +
            inner ℂ (completedXiLinePairOdd rho) (completedXiLinePairOdd rho)) := by
    simp only [inner_add_left, inner_add_right, inner_sub_right,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal] at hadjoint
    calc
      inner ℂ (completedXiLinePairOdd rho) xiThetaFourierSourceL2 =
          (((xiSpectralPointSupport rho).re : ℂ) *
              inner ℂ (completedXiLinePairOdd rho) (completedXiLinePairEven rho) -
            ((xiSpectralPointSupport rho).im : ℂ) *
              inner ℂ (completedXiLinePairOdd rho) (completedXiLinePairOdd rho) +
            inner ℂ (completedXiLinePairOdd rho) xiThetaFourierSourceL2) -
          ((xiSpectralPointSupport rho).re : ℂ) *
              inner ℂ (completedXiLinePairOdd rho) (completedXiLinePairEven rho) +
          ((xiSpectralPointSupport rho).im : ℂ) *
              inner ℂ (completedXiLinePairOdd rho) (completedXiLinePairOdd rho) := by ring
      _ = (((xiSpectralPointSupport rho).im : ℂ) *
              inner ℂ (completedXiLinePairEven rho) (completedXiLinePairEven rho) +
            ((xiSpectralPointSupport rho).re : ℂ) *
              inner ℂ (completedXiLinePairOdd rho) (completedXiLinePairEven rho)) -
          ((xiSpectralPointSupport rho).re : ℂ) *
              inner ℂ (completedXiLinePairOdd rho) (completedXiLinePairEven rho) +
          ((xiSpectralPointSupport rho).im : ℂ) *
              inner ℂ (completedXiLinePairOdd rho) (completedXiLinePairOdd rho) := by
            rw [hadjoint]
      _ = _ := by ring
  have hinnerRe := congrArg Complex.re hinner
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re] at hinnerRe
  have hevenRe :
      (inner ℂ (completedXiLinePairEven rho) (completedXiLinePairEven rho)).re =
        ‖completedXiLinePairEven rho‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (completedXiLinePairEven rho)).symm
  have hoddRe :
      (inner ℂ (completedXiLinePairOdd rho) (completedXiLinePairOdd rho)).re =
        ‖completedXiLinePairOdd rho‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (completedXiLinePairOdd rho)).symm
  rw [hevenRe, hoddRe] at hinnerRe
  rw [burnolCompletedRadialSourceWork, hinnerRe]
  ring

/-- Off critical line, common completed Xi source does strictly positive radial work. -/
theorem burnolCompletedRadialSourceWork_pos_iff (rho : XiDivisorSupport) :
    0 < burnolCompletedRadialSourceWork rho ↔
      (xiSpectralPointSupport rho).im ≠ 0 := by
  rw [burnolCompletedRadialSourceWork_eq]
  have hresponse : 0 < ‖completedXiLinePairEven rho‖ ^ 2 +
      ‖completedXiLinePairOdd rho‖ ^ 2 := by
    by_contra h
    have hzero : ‖completedXiLinePairEven rho‖ ^ 2 +
        ‖completedXiLinePairOdd rho‖ ^ 2 = 0 := by
      have hnonneg : 0 ≤ ‖completedXiLinePairEven rho‖ ^ 2 +
          ‖completedXiLinePairOdd rho‖ ^ 2 := by positivity
      linarith
    have heven : completedXiLinePairEven rho = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖completedXiLinePairEven rho‖,
        sq_nonneg ‖completedXiLinePairOdd rho‖]
    have hodd : completedXiLinePairOdd rho = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖completedXiLinePairEven rho‖,
        sq_nonneg ‖completedXiLinePairOdd rho‖]
    have hreconstruct := completedXiLinePair_reconstruction rho
    rw [heven, hodd, smul_zero, add_zero] at hreconstruct
    exact completedXiFirstDividedL2_ne_zero rho hreconstruct.symm
  constructor
  · intro h
    by_contra him
    rw [him, zero_pow (by norm_num), zero_mul] at h
    exact lt_irrefl 0 h
  · intro him
    exact mul_pos (sq_pos_of_ne_zero him) hresponse

/-- Global absence of completed radial source work is exactly RH. -/
theorem all_burnolCompletedRadialSourceWork_eq_zero_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport, burnolCompletedRadialSourceWork rho = 0) ↔
      RiemannHypothesis := by
  rw [← all_completedXiLinePairOdd_eq_zero_iff_riemannHypothesis]
  constructor
  · intro h rho
    rw [completedXiLinePairOdd_eq_zero_iff]
    by_contra him
    exact (ne_of_gt ((burnolCompletedRadialSourceWork_pos_iff rho).mpr him)) (h rho)
  · intro h rho
    have him := (completedXiLinePairOdd_eq_zero_iff rho).mp (h rho)
    rw [burnolCompletedRadialSourceWork, him, zero_mul]

end RHTower

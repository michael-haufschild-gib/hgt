import GaloisForLFunctions.RHTower.HedenmalmThetaEigenODE
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureCurvatureFlow
import GaloisForLFunctions.RHTower.SourceZeroHorizontalCarrier

/-!
# Source-zero Hedenmalm orientation rigidity

The actual causal Hedenmalm flow is injective in its strip spectral parameter.  Indeed, equality
of two flows lets us subtract their exact theta-source ODEs.  Distinct parameters would force the
common flow to vanish identically, contradicting strict positivity of the theta source.

Critical-line reflection on an `XiZeroCopy` is conjugation of its centered spectral parameter.
Consequently equality of the two reflected causal flows is an exact source-level law for
critical-line placement.  It annihilates the complete-resolution component, the cofinal tail log,
and every prime-labelled Bockstein component before bounded scalarization, without forgetting the
divisor-multiplicity copy.

All implications are unconditional.  The global source law is proved equivalent to RH; it is not
asserted here.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Strip rigidity of the actual source-pointed flow.**  Two causal Hedenmalm flows driven by
the same nonvanishing theta source have the same strip spectral parameter whenever they agree
pointwise. -/
theorem hedenmalmCausalVolterra_injective_on_strip
    {alpha beta : ℂ} (halpha : |alpha.im| < 1) (hbeta : |beta.im| < 1)
    (hflow : ∀ x : ℝ,
      hedenmalmCausalVolterra alpha x = hedenmalmCausalVolterra beta x) :
    alpha = beta := by
  by_contra hne
  have hfun : hedenmalmCausalVolterra alpha = hedenmalmCausalVolterra beta :=
    funext hflow
  have hzero : ∀ x : ℝ, hedenmalmCausalVolterra alpha x = 0 := by
    intro x
    have hodeAlpha := hedenmalmCausalVolterra_thetaEigen_ode halpha x
    have hodeBeta := hedenmalmCausalVolterra_thetaEigen_ode hbeta x
    rw [← hfun] at hodeBeta
    have hmul : (alpha - beta) * hedenmalmCausalVolterra alpha x = 0 := by
      linear_combination hodeAlpha - hodeBeta
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
  have hzeroFun : hedenmalmCausalVolterra alpha = 0 := funext hzero
  have hodeZero := hedenmalmCausalVolterra_thetaEigen_ode halpha 0
  rw [hzeroFun] at hodeZero
  simp only [Pi.zero_apply, deriv_zero, mul_zero, add_zero] at hodeZero
  have hsourceNeg : -thetaCuspFullSource 0 = 0 := by
    exact_mod_cast hodeZero.symm
  have hsourceZero : thetaCuspFullSource 0 = 0 := by
    linarith
  exact (ne_of_gt thetaCuspFullSource_zero_pos_for_cold_seam) hsourceZero

/-- Equality of the two actual source-pointed flows indexed by one multiplicity copy and its
critical-line-reflected copy.  No prime labels are summed and no carrier is scalarized. -/
def SourceZeroHedenmalmOrientationLaw (q : XiZeroCopy) : Prop :=
  ∀ x : ℝ,
    hedenmalmCausalVolterra (xiSpectralPoint q) x =
      hedenmalmCausalVolterra
        (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) x

/-- Every actual Xi spectral parameter lies in the analytic strip needed by the Hedenmalm ODE. -/
theorem abs_im_xiSpectralPoint_lt_one (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| < 1 := by
  rw [abs_lt]
  rcases xiSpectralPoint_im_mem_openHalf q with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- **Exact source classifier.**  Reflected causal-flow equality holds precisely when the
multiplicity copy lies on the critical line. -/
theorem sourceZeroHedenmalmOrientationLaw_iff_re_eq_half (q : XiZeroCopy) :
    SourceZeroHedenmalmOrientationLaw q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hsource
    have hspectral :
        xiSpectralPoint q =
          xiSpectralPoint (xiZeroCopyLineConjEquiv q) :=
      hedenmalmCausalVolterra_injective_on_strip
        (abs_im_xiSpectralPoint_lt_one q)
        (abs_im_xiSpectralPoint_lt_one (xiZeroCopyLineConjEquiv q))
        hsource
    rw [xiSpectralPoint_lineConj] at hspectral
    have him : (xiSpectralPoint q).im = 0 :=
      Complex.conj_eq_iff_im.mp hspectral.symm
    rw [xiSpectralPoint_im_eq] at him
    linarith
  · intro hline x
    have him : (xiSpectralPoint q).im = 0 := by
      rw [xiSpectralPoint_im_eq, hline]
      norm_num
    have hfixed : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q :=
      Complex.conj_eq_iff_im.mpr him
    rw [xiSpectralPoint_lineConj, hfixed]

/-- The concrete Hedenmalm source law has exactly the same pointwise zero radical as the full
source-zero horizontal carrier. -/
theorem sourceZeroHedenmalmOrientationLaw_iff_carrierAt_eq_zero
    (K : ℕ) (q : XiZeroCopy) :
    SourceZeroHedenmalmOrientationLaw q ↔
      sourceZeroHorizontalCarrierAt K q = 0 := by
  rw [sourceZeroHedenmalmOrientationLaw_iff_re_eq_half,
    sourceZeroHorizontalCarrierAt_eq_zero_iff]

/-- **Source law to pre-scalar annihilation.**  Reflected flow equality kills the complete source
edge, the ordered cofinal tail, every retained ordinary-prime coefficient separately, and both
full reflection orientations. -/
theorem sourceZeroHedenmalmOrientationLaw_annihilates_both_orientations
    (K : ℕ) (q : XiZeroCopy) (hsource : SourceZeroHedenmalmOrientationLaw q) :
    sourceZeroHorizontalResolutionCarrier K q = 0 ∧
      sourceZeroHorizontalTailLog q = 0 ∧
      (∀ p : Nat.Primes, sourceZeroHorizontalPrimeCarrier q p = 0) ∧
      sourceZeroHorizontalCarrierAt K q = 0 ∧
      sourceZeroHorizontalCarrierAt K (xiZeroCopyLineConjEquiv q) = 0 := by
  have hline : (q.1 : ℂ).re = 1 / 2 :=
    (sourceZeroHedenmalmOrientationLaw_iff_re_eq_half q).1 hsource
  have hcarrier : sourceZeroHorizontalCarrierAt K q = 0 :=
    (sourceZeroHorizontalCarrierAt_eq_zero_iff K q).2 hline
  refine ⟨
    (sourceZeroHorizontalResolutionCarrier_eq_zero_iff K q).2 hline,
    (sourceZeroHorizontalTailLog_eq_zero_iff K q).2 hline,
    fun p => (sourceZeroHorizontalPrimeCarrier_eq_zero_iff q p).2 hline,
    hcarrier, ?_⟩
  rw [sourceZeroHorizontalCarrierAt_reflection, hcarrier, neg_zero]

/-- Global concrete source law, still indexed by every analytic divisor-multiplicity copy. -/
def SourceZeroHedenmalmOrientationsAnnihilate : Prop :=
  ∀ q : XiZeroCopy, SourceZeroHedenmalmOrientationLaw q

/-- Exact endpoint audit: global equality of the actual reflected Hedenmalm source flows is RH. -/
theorem sourceZeroHedenmalmOrientationsAnnihilate_iff_riemannHypothesis :
    SourceZeroHedenmalmOrientationsAnnihilate ↔ RiemannHypothesis := by
  constructor
  · intro hsource
    apply (sourceZeroHorizontalCarrierVanishes_iff_riemannHypothesis 0).1
    funext q
    exact (sourceZeroHedenmalmOrientationLaw_iff_carrierAt_eq_zero 0 q).1
      (hsource q)
  · intro hRH q
    apply (sourceZeroHedenmalmOrientationLaw_iff_re_eq_half q).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end RHTower

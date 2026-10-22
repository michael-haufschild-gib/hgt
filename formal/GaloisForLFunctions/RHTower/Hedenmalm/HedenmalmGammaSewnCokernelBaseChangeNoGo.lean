import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmFredholmRangeDivisor
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnRouteRKreinGaugeBridge
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional
import GaloisForLFunctions.RHTower.XiHedenmalmThetaBorelHilbert
import GaloisForLFunctions.RHTower.SlabMassSquareCertificate

/-!
# Ambient cokernel base-change no-go

Every actual Xi cokernel conormal belongs to the ordinary weighted theta source space: its weighted
squared mass is the norm of the theta source character at doubled spectral parameter, and every Xi
zero lies in the required open half strip.  This ambient admission supplies no Gamma-sewn marked
landing.  On the full conormal strip the latter still has the independent sharp horizon
`|Im z| < u`.

Consequently, for each fixed `0 < u < 1/2`, no total ambient base change can send all weighted theta
cokernel conormals into the literal damping-`u` marked fibre; the explicit conormal at `z = i u`
falsifies it.  The missing operation must therefore be divisor-supported and singular, not a
bounded or even total map on the ambient conormal Hilbert space.  Restricting the landing to actual
Xi roots for every positive damping is proved exactly equivalent to RH, keeping the producer
obligation visible.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmQuantile HedenmalmFredholmRange HedenmalmThetaSource

def thetaCokernelWeightedMass (z : ℂ) (x : ℝ) : ℝ :=
  Complex.normSq (cokernelVector thetaSource z x) / thetaSource.k x

theorem thetaCokernelWeightedMass_eq (z : ℂ) (x : ℝ) :
    thetaCokernelWeightedMass z x =
      ‖(thetaSource.k x : ℂ) * sourceChar (2 * z) x‖ := by
  have hk : 0 < thetaSource.k x := thetaSource.pos_k x
  rw [thetaCokernelWeightedMass, cokernelVector, Complex.normSq_mul,
    Complex.normSq_ofReal, sourceChar, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hk.le, Complex.normSq_eq_norm_sq,
    Complex.norm_exp]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    neg_re, neg_im]
  field_simp [hk.ne']
  rw [Complex.norm_exp, Complex.conj_im]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    zero_mul, one_mul, mul_zero, sub_zero]
  rw [pow_two, ← Real.exp_add]
  congr 1
  norm_num
  ring

theorem integrable_thetaCokernelWeightedMass
    {z : ℂ} (hz : |(2 * z).im| < 1) :
    Integrable (thetaCokernelWeightedMass z) := by
  have hsource :=
    (integrable_k_sourceChar thetaSource
      (hasShiftedTail_thetaSource hz)).norm
  refine hsource.congr (ae_of_all _ fun x => ?_)
  exact (thetaCokernelWeightedMass_eq z x).symm

theorem integrable_thetaCokernelWeightedMass_of_XiC_eq_zero
    {z : ℂ} (hzero : XiC z = 0) :
    Integrable (thetaCokernelWeightedMass z) := by
  apply integrable_thetaCokernelWeightedMass
  have hhalf := abs_im_lt_half_of_XiC_eq_zero hzero
  have him : (2 * z).im = 2 * z.im := by
    norm_num [mul_im]
  rw [him, abs_mul]
  norm_num
  linarith

/-- On the full critical conormal strip, ambient weighted admission is automatic; the Gamma-sewn
marked landing has exactly the independent sharp damping horizon. -/
theorem thetaCokernelWeighted_and_markedLanding_iff
    (u : ℝ) {z : ℂ} (hz : |(2 * z).im| < 1) :
    (Integrable (thetaCokernelWeightedMass z) ∧
        GammaSewnHedenmalmDampedMarkedSummable u z) ↔
      |z.im| < u := by
  rw [gammaSewnHedenmalmDampedMarkedSummable_iff]
  exact and_iff_right (integrable_thetaCokernelWeightedMass hz)

/-- A total ambient landing would send every weighted theta cokernel conormal to the literal
Gamma-sewn marked Hilbert fibre at fixed damping. -/
def HasTotalThetaCokernelMarkedLanding (u : ℝ) : Prop :=
  ∀ z : ℂ, Integrable (thetaCokernelWeightedMass z) →
    GammaSewnHedenmalmDampedMarkedSummable u z

theorem not_hasTotalThetaCokernelMarkedLanding
    {u : ℝ} (hu0 : 0 < u) (huHalf : u < 1 / 2) :
    ¬ HasTotalThetaCokernelMarkedLanding u := by
  intro htotal
  let z : ℂ := (u : ℂ) * I
  have hzstrip : |(2 * z).im| < 1 := by
    dsimp [z]
    simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re,
      mul_one, zero_mul, add_zero]
    norm_num
    rw [abs_of_pos hu0]
    linarith
  have hin := integrable_thetaCokernelWeightedMass hzstrip
  have hout := htotal z hin
  rw [gammaSewnHedenmalmDampedMarkedSummable_iff] at hout
  dsimp [z] at hout
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re,
    mul_one, zero_mul, add_zero] at hout
  rw [abs_of_pos hu0] at hout
  exact (lt_irrefl u) hout

/-- Exact root-only target isolated by the ambient no-go: all actual Xi cokernel conormals land in
every positive-damping marked fibre. -/
def XiRootConormalAllPositiveDampingMarkedLanding : Prop :=
  ∀ z : ℂ, XiC z = 0 → ∀ u : ℝ, 0 < u →
    Integrable (thetaCokernelWeightedMass z) ∧
      GammaSewnHedenmalmDampedMarkedSummable u z

theorem xiRootConormalAllPositiveDampingMarkedLanding_iff_riemannHypothesis :
    XiRootConormalAllPositiveDampingMarkedLanding ↔ RiemannHypothesis := by
  rw [SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero]
  constructor
  · intro hlanding z hzero
    by_contra him
    have himPos : 0 < |z.im| := abs_pos.mpr him
    have h := (hlanding z hzero |z.im| himPos).2
    rw [gammaSewnHedenmalmDampedMarkedSummable_iff] at h
    exact (lt_irrefl |z.im|) h
  · intro hreal z hzero u hu
    refine ⟨integrable_thetaCokernelWeightedMass_of_XiC_eq_zero hzero, ?_⟩
    rw [gammaSewnHedenmalmDampedMarkedSummable_iff, hreal z hzero, abs_zero]
    exact hu

end

end RHTower

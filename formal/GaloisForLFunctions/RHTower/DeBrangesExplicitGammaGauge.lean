import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicQuadraticRoot
import GaloisForLFunctions.HTGeometry.HypertranscendentalExponentialPencil
import GaloisForLFunctions.HTGeometry.FixedModulusRealRootednessNonselection
import GaloisForLFunctions.HTGeometry.MeromorphicGammaReflection
import GaloisForLFunctions.HTGeometry.EvenPowerCanonicalProductDA
import GaloisForLFunctions.HTGeometry.HypertranscendencePolynomial
import GaloisForLFunctions.RHTower.DeBrangesGaugeInvariance

/-!
# The explicit reciprocal-Gamma de Branges gauge

The reflected reciprocal-Gamma sum

`q(z) = Γ(z)⁻¹ + Γ(1-z)⁻¹`

is entire, Schwarz-real, and hypertranscendental.  Its exponential is therefore an entire,
Schwarz-real, zero-free hypertranscendental gauge.  The proof of hypertranscendence is the literal
Euler-reflection quadratic argument from the de Branges saturation card.
-/

open Set Complex

namespace GaloisForLFunctions.RHTower

open HTGeometry
open HTGeometry.FixedModulusRealRootedness
open _root_.HTGeometry

noncomputable section

/-- The explicit reflected reciprocal-Gamma exponent. -/
def deBrangesReciprocalGammaExponent (z : ℂ) : ℂ :=
  reciprocalGammaEntire z + reciprocalGammaEntire (1 - z)

/-- The elementary reflection product `sin(πz)/π`, written as `z sinc(z)`. -/
def deBrangesReciprocalGammaProduct (z : ℂ) : ℂ := z * sincProduct z

theorem analyticOnNhd_reciprocalGammaEntire :
    AnalyticOnNhd ℂ reciprocalGammaEntire Set.univ := by
  simpa using analyticOnNhd_reciprocalGammaTranslate 0

theorem analyticOnNhd_reciprocalGammaOneSub :
    AnalyticOnNhd ℂ (fun z => reciprocalGammaEntire (1 - z)) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact (contDiff_reciprocalGammaEntire.differentiable (by simp)).comp (by fun_prop)

theorem analyticOnNhd_deBrangesReciprocalGammaExponent :
    AnalyticOnNhd ℂ deBrangesReciprocalGammaExponent Set.univ :=
  analyticOnNhd_reciprocalGammaEntire.add analyticOnNhd_reciprocalGammaOneSub

theorem analyticOnNhd_deBrangesReciprocalGammaProduct :
    AnalyticOnNhd ℂ deBrangesReciprocalGammaProduct Set.univ :=
  analyticOnNhd_id.mul analyticOnNhd_sincProduct

theorem differentiallyAlgebraic_deBrangesReciprocalGammaProduct :
    DifferentiallyAlgebraic deBrangesReciprocalGammaProduct := by
  exact differentiallyAlgebraic_mul analyticOnNhd_id analyticOnNhd_sincProduct
    (by simpa using differentiallyAlgebraic_polynomial Polynomial.X)
    differentiallyAlgebraic_sincProduct

theorem reciprocalGammaEntire_mul_one_sub_eq_deBrangesProduct (z : ℂ) :
    reciprocalGammaEntire z * reciprocalGammaEntire (1 - z) =
      deBrangesReciprocalGammaProduct z := by
  rw [deBrangesReciprocalGammaProduct, reciprocalGammaEntire_mul_one_sub]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply (div_eq_iff hpi).mpr
  rw [← pi_mul_sincProduct z]
  ring

/-- The reflected reciprocal-Gamma exponent is hypertranscendental. -/
theorem hypertranscendental_deBrangesReciprocalGammaExponent :
    Hypertranscendental deBrangesReciprocalGammaExponent := by
  intro hqDA
  apply hypertranscendental_reciprocalGammaEntire
  exact differentiallyAlgebraic_of_quadratic_relation
    analyticOnNhd_reciprocalGammaEntire
    analyticOnNhd_deBrangesReciprocalGammaExponent
    analyticOnNhd_deBrangesReciprocalGammaProduct
    (fun z => by
      rw [deBrangesReciprocalGammaExponent]
      have hp := reciprocalGammaEntire_mul_one_sub_eq_deBrangesProduct z
      calc
        reciprocalGammaEntire z ^ 2 -
              (reciprocalGammaEntire z + reciprocalGammaEntire (1 - z)) *
                reciprocalGammaEntire z + deBrangesReciprocalGammaProduct z =
            -(reciprocalGammaEntire z * reciprocalGammaEntire (1 - z)) +
              deBrangesReciprocalGammaProduct z := by ring
        _ = 0 := by rw [hp]; ring)
    hqDA differentiallyAlgebraic_deBrangesReciprocalGammaProduct

theorem reciprocalGammaEntire_conj (z : ℂ) :
    reciprocalGammaEntire ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (reciprocalGammaEntire z) := by
  change (Complex.Gamma ((starRingEnd ℂ) z))⁻¹ =
    (starRingEnd ℂ) ((Complex.Gamma z)⁻¹)
  rw [Complex.Gamma_conj, map_inv₀]

theorem schwarzReal_deBrangesReciprocalGammaExponent :
    SchwarzRealGauge deBrangesReciprocalGammaExponent := by
  intro z
  rw [suzukiEntireSharp]
  change (starRingEnd ℂ)
      (reciprocalGammaEntire ((starRingEnd ℂ) z) +
        reciprocalGammaEntire (1 - (starRingEnd ℂ) z)) = _
  rw [map_add, ← reciprocalGammaEntire_conj ((starRingEnd ℂ) z),
    ← reciprocalGammaEntire_conj (1 - (starRingEnd ℂ) z)]
  simp [deBrangesReciprocalGammaExponent]

/-- The explicit positive zero-free gauge. -/
def deBrangesReciprocalGammaGauge (z : ℂ) : ℂ :=
  Complex.exp (deBrangesReciprocalGammaExponent z)

theorem analyticOnNhd_deBrangesReciprocalGammaGauge :
    AnalyticOnNhd ℂ deBrangesReciprocalGammaGauge Set.univ :=
  analyticOnNhd_deBrangesReciprocalGammaExponent.cexp

theorem zeroFree_deBrangesReciprocalGammaGauge :
    ZeroFreeGauge deBrangesReciprocalGammaGauge :=
  fun _ => Complex.exp_ne_zero _

theorem schwarzReal_deBrangesReciprocalGammaGauge :
    SchwarzRealGauge deBrangesReciprocalGammaGauge := by
  intro z
  rw [suzukiEntireSharp]
  change (starRingEnd ℂ)
      (Complex.exp (deBrangesReciprocalGammaExponent ((starRingEnd ℂ) z))) =
    Complex.exp (deBrangesReciprocalGammaExponent z)
  rw [← Complex.exp_conj]
  congr 1
  exact schwarzReal_deBrangesReciprocalGammaExponent z

theorem hypertranscendental_deBrangesReciprocalGammaGauge :
    Hypertranscendental deBrangesReciprocalGammaGauge := by
  change Hypertranscendental
    (fun z => Complex.exp (deBrangesReciprocalGammaExponent z))
  simpa only [one_mul] using
    (hypertranscendental_cexp_const_mul_iff
      analyticOnNhd_deBrangesReciprocalGammaExponent (by norm_num : (1 : ℂ) ≠ 0)).mpr
      hypertranscendental_deBrangesReciprocalGammaExponent

/-! ## Explicit DA/HT Hermite--Biehler pair -/

/-- The elementary differentially algebraic Hermite--Biehler representative `exp(-iaz)`. -/
def deBrangesExponentialBase (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (a : ℂ) * z)

theorem suzukiEntireSharp_deBrangesExponentialBase (a : ℝ) (z : ℂ) :
    suzukiEntireSharp (deBrangesExponentialBase a) z =
      Complex.exp (Complex.I * (a : ℂ) * z) := by
  rw [suzukiEntireSharp, deBrangesExponentialBase]
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem suzukiHermiteBiehler_deBrangesExponentialBase {a : ℝ} (ha : 0 < a) :
    SuzukiHermiteBiehler (deBrangesExponentialBase a) := by
  intro z hz
  rw [suzukiEntireSharp_deBrangesExponentialBase, deBrangesExponentialBase,
    Complex.norm_exp, Complex.norm_exp]
  apply Real.exp_lt_exp.mpr
  simp only [mul_re, mul_im, I_re, ofReal_re, I_im, ofReal_im, zero_mul, mul_zero,
    sub_zero, neg_re, neg_im, neg_zero, neg_one_mul]
  nlinarith

theorem analyticOnNhd_deBrangesExponentialBase (a : ℝ) :
    AnalyticOnNhd ℂ (deBrangesExponentialBase a) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  unfold deBrangesExponentialBase
  fun_prop

theorem differentiallyAlgebraic_deBrangesExponentialBase (a : ℝ) :
    DifferentiallyAlgebraic (deBrangesExponentialBase a) := by
  change DifferentiallyAlgebraic (fun z => Complex.exp (-Complex.I * (a : ℂ) * z))
  exact differentiallyAlgebraic_cexp_linear (-Complex.I * (a : ℂ))

/-- The explicit hypertranscendental representative in the same gauge class. -/
def deBrangesReciprocalGammaRepresentative (a : ℝ) (z : ℂ) : ℂ :=
  deBrangesReciprocalGammaGauge z * deBrangesExponentialBase a z

theorem analyticOnNhd_deBrangesReciprocalGammaRepresentative (a : ℝ) :
    AnalyticOnNhd ℂ (deBrangesReciprocalGammaRepresentative a) Set.univ :=
  analyticOnNhd_deBrangesReciprocalGammaGauge.mul
    (analyticOnNhd_deBrangesExponentialBase a)

theorem suzukiHermiteBiehler_deBrangesReciprocalGammaRepresentative {a : ℝ}
    (ha : 0 < a) :
    SuzukiHermiteBiehler (deBrangesReciprocalGammaRepresentative a) := by
  exact (suzukiHermiteBiehler_mul_iff
    schwarzReal_deBrangesReciprocalGammaGauge
    zeroFree_deBrangesReciprocalGammaGauge).mpr
      (suzukiHermiteBiehler_deBrangesExponentialBase ha)

theorem hypertranscendental_deBrangesReciprocalGammaRepresentative (a : ℝ) :
    Hypertranscendental (deBrangesReciprocalGammaRepresentative a) := by
  intro hDA
  apply hypertranscendental_deBrangesReciprocalGammaGauge
  let Einv : ℂ → ℂ := fun z => Complex.exp (Complex.I * (a : ℂ) * z)
  have hEinvAn : AnalyticOnNhd ℂ Einv Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    fun_prop
  have hEinvDA : DifferentiallyAlgebraic Einv := by
    simpa [Einv] using differentiallyAlgebraic_cexp_linear (Complex.I * (a : ℂ))
  have hprodDA : DifferentiallyAlgebraic
      (fun z => deBrangesReciprocalGammaRepresentative a z * Einv z) :=
    differentiallyAlgebraic_mul
      (analyticOnNhd_deBrangesReciprocalGammaRepresentative a) hEinvAn hDA hEinvDA
  have hcancel :
      (fun z => deBrangesReciprocalGammaRepresentative a z * Einv z) =
        deBrangesReciprocalGammaGauge := by
    funext z
    dsimp [Einv]
    rw [deBrangesReciprocalGammaRepresentative, deBrangesExponentialBase,
      mul_assoc, ← Complex.exp_add]
    have : -Complex.I * (a : ℂ) * z + Complex.I * (a : ℂ) * z = 0 := by ring
    rw [this, Complex.exp_zero, mul_one]
  rw [hcancel] at hprodDA
  exact hprodDA

theorem deBrangesExplicitPair_innerQuotient (a : ℝ) (z : ℂ) :
    suzukiEntireSharp (deBrangesReciprocalGammaRepresentative a) z /
        deBrangesReciprocalGammaRepresentative a z =
      suzukiEntireSharp (deBrangesExponentialBase a) z /
        deBrangesExponentialBase a z :=
  deBrangesInnerQuotient_mul_of_schwarzReal
    schwarzReal_deBrangesReciprocalGammaGauge
    zeroFree_deBrangesReciprocalGammaGauge z

theorem deBrangesExplicitPair_canonicalSpectrum (a : ℝ) (alpha : ℝ) (z : ℂ) :
    deBrangesCanonicalPencil (deBrangesReciprocalGammaRepresentative a) alpha z = 0 ↔
      deBrangesCanonicalPencil (deBrangesExponentialBase a) alpha z = 0 :=
  deBrangesCanonicalPencil_mul_eq_zero_iff
    schwarzReal_deBrangesReciprocalGammaGauge
    zeroFree_deBrangesReciprocalGammaGauge alpha z

theorem deBrangesExplicitPair_kernel (a : ℝ) (z w : ℂ) :
    deBrangesKernel (deBrangesReciprocalGammaRepresentative a) z w =
      deBrangesReciprocalGammaGauge z * star (deBrangesReciprocalGammaGauge w) *
        deBrangesKernel (deBrangesExponentialBase a) z w :=
  deBrangesKernel_mul_of_schwarzReal schwarzReal_deBrangesReciprocalGammaGauge z w

end

end GaloisForLFunctions.RHTower

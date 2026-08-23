import GaloisForLFunctions.RHTower.ThetaCuspHawkingPartnerInstabilityEndpoint
import GaloisForLFunctions.RHTower.HedenmalmShiftedSourceEquationExact
import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati

/-!
# Conformal-anomaly backreaction generator endpoint

For the dynamical moving mirror of Kumar--Reyes--Wintergerst, the integrated anomalous equation
in ray-tracing coordinates is

`sqrt(f') - (q / 2) f'' / f' - P₊ = A`.

Writing `y = log sqrt(f')` gives `exp(y) - q y' - P₊ = A`.  On the positive theta ray this file
chooses the exact background velocity

`exp(y₀) = q * thetaCuspLogDecaySlope = -q k'/k`.

The rapidity linearization is therefore `-q (∂ + k'/k)`.  Multiplication by the full density `k`
conjugates it to `-i q D`, where `D = -i ∂` is the already-closed Hedenmalm derivative.  The mirror
momentum constant becomes the literal cokernel forcing `k`.  Hence the two-ended anomaly response
exists exactly when `XiC` vanishes.

The full-line theta background is signed: only `x > 0` is a future-oriented mirror branch; `x < 0`
is its time-reversed bifurcate partner.  No single-worldline or no-runaway claim is made here.
The remaining physical core is to derive admissible partner sewing or passivity from quantum
backreaction itself.  This file proves the generator and resonance identifications, not that core.
-/

open Complex Function MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmThetaSource
  HedenmalmPrimeTranslation HedenmalmFredholmRange HedenmalmClosedWeightedDerivative

/-- The logarithmic derivative used by the closed Hedenmalm operator is the first derivative of
the completed logarithmic theta source. -/
theorem sourceLogDeriv_eq_iteratedDeriv_thetaCuspLogSource (x : ℝ) :
    sourceLogDeriv x = iteratedDeriv 1 thetaCuspLogSource x := by
  unfold sourceLogDeriv sourceDeriv
  have h := (hasDerivAt_thetaCuspLogSource x).deriv
  simpa only [iteratedDeriv_one] using h.symm

/-- The positive-ray theta decay slope is minus the Hedenmalm logarithmic derivative. -/
theorem thetaCuspLogDecaySlope_eq_neg_sourceLogDeriv (x : ℝ) :
    thetaCuspLogDecaySlope x = -sourceLogDeriv x := by
  rw [thetaCuspLogDecaySlope, sourceLogDeriv_eq_iteratedDeriv_thetaCuspLogSource]

/-- Background null velocity selected by the theta logarithmic slope and anomaly length `q`. -/
def thetaCuspHawkingBackreactionVelocity (q x : ℝ) : ℝ :=
  q * thetaCuspLogDecaySlope x

/-- On the positive ray, positive anomaly length gives a future-oriented background velocity. -/
theorem thetaCuspHawkingBackreactionVelocity_pos
    {q x : ℝ} (hq : 0 < q) (hx : 0 < x) :
    0 < thetaCuspHawkingBackreactionVelocity q x := by
  exact mul_pos hq (neg_iteratedDeriv_one_thetaCuspLogSource_pos hx)

/-- Linearization of `exp(y) - q y'` at the theta background. -/
def thetaCuspHawkingAnomalyLinearization
    (q : ℝ) (eta eta' : ℝ → ℂ) (x : ℝ) : ℂ :=
  (thetaCuspHawkingBackreactionVelocity q x : ℂ) * eta x - (q : ℂ) * eta' x

/-- The linearized conformal-anomaly equation is the full logarithmic-density derivative. -/
theorem thetaCuspHawkingAnomalyLinearization_eq
    (q : ℝ) (eta eta' : ℝ → ℂ) (x : ℝ) :
    thetaCuspHawkingAnomalyLinearization q eta eta' x =
      -(q : ℂ) *
        (eta' x + ((sourceLogDeriv x : ℝ) : ℂ) * eta x) := by
  rw [thetaCuspHawkingAnomalyLinearization, thetaCuspHawkingBackreactionVelocity,
    thetaCuspLogDecaySlope_eq_neg_sourceLogDeriv]
  push_cast
  ring

/-- Full-density dressing from a rapidity perturbation to the Hedenmalm source coordinate. -/
def thetaCuspHawkingDensityDress (eta : ℝ → ℂ) (x : ℝ) : ℂ :=
  (thetaCuspFullSource x : ℂ) * eta x

/-- Product rule for the full-density dressing. -/
theorem hasDerivAt_thetaCuspHawkingDensityDress
    {eta eta' : ℝ → ℂ} (heta : ∀ x, HasDerivAt eta (eta' x) x) (x : ℝ) :
    HasDerivAt (thetaCuspHawkingDensityDress eta)
      ((thetaCuspFullSource x : ℂ) *
        (eta' x + ((sourceLogDeriv x : ℝ) : ℂ) * eta x)) x := by
  have hprod := (hasDerivAt_thetaCuspFullSource x).ofReal_comp.mul (heta x)
  refine hprod.congr_deriv ?_
  rw [sourceLogDeriv]
  rw [Complex.ofReal_div]
  have hk : (thetaCuspFullSource x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaCuspFullSource_pos_all x).ne'
  field_simp [hk]
  ring

/-- **[PROVED] Exact anomaly-generator conjugacy.** Full-density dressing turns the linearized moving-mirror
backreaction operator into `-i q D`, where `D = -i ∂` is Hedenmalm's source derivative. -/
theorem thetaCuspHawkingAnomalyLinearization_conjugacy
    (q : ℝ) {eta eta' : ℝ → ℂ}
    (heta : ∀ x, HasDerivAt eta (eta' x) x) (x : ℝ) :
    (thetaCuspFullSource x : ℂ) *
        thetaCuspHawkingAnomalyLinearization q eta eta' x =
      -Complex.I * (q : ℂ) * sourceD (thetaCuspHawkingDensityDress eta) x := by
  rw [sourceD, (hasDerivAt_thetaCuspHawkingDensityDress heta x).deriv,
    thetaCuspHawkingAnomalyLinearization_eq]
  have hI : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
    rw [neg_mul_neg, Complex.I_mul_I]
  calc
    (thetaCuspFullSource x : ℂ) *
          (-(q : ℂ) *
            (eta' x + ((sourceLogDeriv x : ℝ) : ℂ) * eta x)) =
        -(q : ℂ) * (thetaCuspFullSource x : ℂ) *
          (eta' x + ((sourceLogDeriv x : ℝ) : ℂ) * eta x) := by ring
    _ = ((-Complex.I) * (-Complex.I)) * (q : ℂ) *
          (thetaCuspFullSource x : ℂ) *
            (eta' x + ((sourceLogDeriv x : ℝ) : ℂ) * eta x) := by rw [hI]; ring
    _ = -Complex.I * (q : ℂ) *
          (-Complex.I * ((thetaCuspFullSource x : ℂ) *
            (eta' x + ((sourceLogDeriv x : ℝ) : ℂ) * eta x))) := by ring

/-- Frequency-translated linearized anomaly operator. -/
def thetaCuspHawkingBackreactionPencil
    (q : ℝ) (alpha : ℂ) (eta eta' : ℝ → ℂ) (x : ℝ) : ℂ :=
  thetaCuspHawkingAnomalyLinearization q eta eta' x -
    Complex.I * (q : ℂ) * alpha * eta x

/-- Exact conjugacy of the translated physical pencil to the shifted Hedenmalm derivative. -/
theorem thetaCuspHawkingBackreactionPencil_conjugacy
    (q : ℝ) (alpha : ℂ) {eta eta' : ℝ → ℂ}
    (heta : ∀ x, HasDerivAt eta (eta' x) x) (x : ℝ) :
    (thetaCuspFullSource x : ℂ) *
        thetaCuspHawkingBackreactionPencil q alpha eta eta' x =
      -Complex.I * (q : ℂ) *
        (sourceD (thetaCuspHawkingDensityDress eta) x +
          alpha * thetaCuspHawkingDensityDress eta x) := by
  unfold thetaCuspHawkingBackreactionPencil
  calc
    (thetaCuspFullSource x : ℂ) *
          (thetaCuspHawkingAnomalyLinearization q eta eta' x -
            Complex.I * (q : ℂ) * alpha * eta x) =
        (thetaCuspFullSource x : ℂ) *
            thetaCuspHawkingAnomalyLinearization q eta eta' x -
          (thetaCuspFullSource x : ℂ) *
            (Complex.I * (q : ℂ) * alpha * eta x) := by ring
    _ = -Complex.I * (q : ℂ) * sourceD (thetaCuspHawkingDensityDress eta) x -
          (thetaCuspFullSource x : ℂ) *
            (Complex.I * (q : ℂ) * alpha * eta x) := by
      rw [thetaCuspHawkingAnomalyLinearization_conjugacy q heta x]
    _ = -Complex.I * (q : ℂ) *
        (sourceD (thetaCuspHawkingDensityDress eta) x +
          alpha * thetaCuspHawkingDensityDress eta x) := by
      unfold thetaCuspHawkingDensityDress
      ring

/-- Canonical rapidity response obtained by undressing Hedenmalm's two-ended source solution. -/
def thetaCuspHawkingBackreactionRapidityMode (alpha : ℂ) (x : ℝ) : ℂ :=
  thetaTwoEndedSourceSolution alpha x / (thetaCuspFullSource x : ℂ)

theorem thetaCuspHawkingDensityDress_rapidityMode (alpha : ℂ) :
    thetaCuspHawkingDensityDress (thetaCuspHawkingBackreactionRapidityMode alpha) =
      thetaTwoEndedSourceSolution alpha := by
  funext x
  unfold thetaCuspHawkingDensityDress thetaCuspHawkingBackreactionRapidityMode
  field_simp [show (thetaCuspFullSource x : ℂ) ≠ 0 by
    exact_mod_cast (thetaCuspFullSource_pos_all x).ne']

theorem differentiableAt_thetaCuspHawkingBackreactionRapidityMode
    (alpha : ℂ) (x : ℝ) :
    DifferentiableAt ℝ (thetaCuspHawkingBackreactionRapidityMode alpha) x := by
  unfold thetaCuspHawkingBackreactionRapidityMode thetaTwoEndedSourceSolution
  exact ((hasDerivAt_twoEndedSolution thetaSource
    (hasShiftedTail_thetaSource_all alpha) x).div
      (hasDerivAt_thetaCuspFullSource x).ofReal_comp
      (by exact_mod_cast (thetaCuspFullSource_pos_all x).ne')).differentiableAt

theorem thetaTwoEndedSourceSolution_sourceEquation (alpha : ℂ) (x : ℝ) :
    sourceD (thetaTwoEndedSourceSolution alpha) x +
        alpha * thetaTwoEndedSourceSolution alpha x =
      -Complex.I * (thetaCuspFullSource x : ℂ) := by
  unfold thetaTwoEndedSourceSolution
  rw [sourceD,
    (hasDerivAt_twoEndedSolution thetaSource
      (hasShiftedTail_thetaSource_all alpha) x).deriv]
  exact twoEndedSolution_equation thetaSource alpha x

/-- The canonical undressed mode solves the literal linearized anomaly equation for every complex
frequency. Xi enters only through the second, future-ended boundary condition below. -/
theorem thetaCuspHawkingBackreactionRapidityMode_equation
    (q : ℝ) (alpha : ℂ) (x : ℝ) :
    thetaCuspHawkingBackreactionPencil q alpha
        (thetaCuspHawkingBackreactionRapidityMode alpha)
        (deriv (thetaCuspHawkingBackreactionRapidityMode alpha)) x =
      -(q : ℂ) := by
  have heta : ∀ y, HasDerivAt (thetaCuspHawkingBackreactionRapidityMode alpha)
      (deriv (thetaCuspHawkingBackreactionRapidityMode alpha) y) y :=
    fun y => (differentiableAt_thetaCuspHawkingBackreactionRapidityMode alpha y).hasDerivAt
  have hconj := thetaCuspHawkingBackreactionPencil_conjugacy q alpha heta x
  rw [thetaCuspHawkingDensityDress_rapidityMode,
    thetaTwoEndedSourceSolution_sourceEquation] at hconj
  have hk : (thetaCuspFullSource x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaCuspFullSource_pos_all x).ne'
  apply (mul_left_cancel₀ hk)
  calc
    (thetaCuspFullSource x : ℂ) *
          thetaCuspHawkingBackreactionPencil q alpha
            (thetaCuspHawkingBackreactionRapidityMode alpha)
            (deriv (thetaCuspHawkingBackreactionRapidityMode alpha)) x =
        -Complex.I * (q : ℂ) *
          (-Complex.I * (thetaCuspFullSource x : ℂ)) := hconj
    _ = (thetaCuspFullSource x : ℂ) * (-(q : ℂ)) := by
      have hI : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
        rw [neg_mul_neg, Complex.I_mul_I]
      calc
        -Complex.I * (q : ℂ) *
              (-Complex.I * (thetaCuspFullSource x : ℂ)) =
            ((-Complex.I) * (-Complex.I)) * (q : ℂ) *
              (thetaCuspFullSource x : ℂ) := by ring
        _ = (thetaCuspFullSource x : ℂ) * (-(q : ℂ)) := by rw [hI]; ring

/-- Future-ended rapidity response obtained from the complementary tail integral. -/
def thetaCuspHawkingBackreactionFutureRapidityMode (alpha : ℂ) (x : ℝ) : ℂ :=
  (-Complex.exp (-(Complex.I * alpha) * (x : ℂ)) *
      ∫ y in Ioi x, (thetaSource.k y : ℂ) * sourceChar alpha y) /
    (thetaCuspFullSource x : ℂ)

/-- A backreaction resonance is a canonical past-ended anomaly response that is simultaneously
future-ended.  This is a boundary condition, not an extra equation of motion. -/
def ThetaCuspHawkingBackreactionResonance (alpha : ℂ) : Prop :=
  ∀ x : ℝ,
    thetaCuspHawkingBackreactionRapidityMode alpha x =
      thetaCuspHawkingBackreactionFutureRapidityMode alpha x

/-- **[PROVED] Exact anomaly resonance determinant.** The completed Xi function vanishes exactly when the
canonical density-dressed linearized Hawking-backreaction response satisfies both endpoint
conditions. -/
theorem xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance (alpha : ℂ) :
    XiC alpha = 0 ↔ ThetaCuspHawkingBackreactionResonance alpha := by
  constructor
  · intro hXi x
    unfold thetaCuspHawkingBackreactionRapidityMode
      thetaCuspHawkingBackreactionFutureRapidityMode
    rw [thetaTwoEndedSourceSolution_right alpha hXi x]
  · intro hres
    have h0 := hres 0
    have hk : (thetaCuspFullSource 0 : ℂ) ≠ 0 := by
      exact_mod_cast (thetaCuspFullSource_pos_all 0).ne'
    unfold thetaCuspHawkingBackreactionRapidityMode
      thetaCuspHawkingBackreactionFutureRapidityMode at h0
    field_simp [hk] at h0
    have htail :
        sourceModeI thetaSource alpha 0 =
          -∫ y in Ioi (0 : ℝ),
            (thetaSource.k y : ℂ) * sourceChar alpha y := by
      have hraw :
          Complex.I * (Complex.I * sourceModeI thetaSource alpha 0) =
            ∫ y in Ioi (0 : ℝ),
              (thetaSource.k y : ℂ) * sourceChar alpha y := by
        simpa [thetaTwoEndedSourceSolution, sourceModeU] using h0
      have hneg :
          -sourceModeI thetaSource alpha 0 =
            ∫ y in Ioi (0 : ℝ),
              (thetaSource.k y : ℂ) * sourceChar alpha y := by
        calc
          -sourceModeI thetaSource alpha 0 =
              Complex.I * (Complex.I * sourceModeI thetaSource alpha 0) := by
                rw [← mul_assoc, Complex.I_mul_I]
                simp
          _ = _ := hraw
      calc
        sourceModeI thetaSource alpha 0 =
            -(-sourceModeI thetaSource alpha 0) := by ring
        _ = -∫ y in Ioi (0 : ℝ),
              (thetaSource.k y : ℂ) * sourceChar alpha y := by rw [hneg]
    have hsource := (sourceModeI_eq_neg_tail_iff thetaSource
      (hasShiftedTail_thetaSource_all alpha) 0).mp htail
    simpa only [xiC_thetaSource_all] using hsource

/-- The physical anomaly equation is automatic; Xi is exactly the missing future endpoint. -/
theorem xiC_eq_zero_iff_thetaCuspHawkingBackreaction_twoEnded
    (q : ℝ) (alpha : ℂ) :
    XiC alpha = 0 ↔
      (∀ x : ℝ,
        thetaCuspHawkingBackreactionPencil q alpha
            (thetaCuspHawkingBackreactionRapidityMode alpha)
            (deriv (thetaCuspHawkingBackreactionRapidityMode alpha)) x =
          -(q : ℂ)) ∧
        ThetaCuspHawkingBackreactionResonance alpha := by
  rw [xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance]
  constructor
  · intro hres
    exact ⟨thetaCuspHawkingBackreactionRapidityMode_equation q alpha, hres⟩
  · exact fun h => h.2

/-- **[PROVED] Closed-domain anomaly endpoint.** At a two-ended resonance, the density-dressed
rapidity response is not merely pointwise: it is the unique representative in the domain of the
closed shifted Hedenmalm derivative. -/
theorem xiC_eq_zero_iff_existsUnique_closedHawkingBackreactionMode
    (q : ℝ) (alpha : ℂ) :
    XiC alpha = 0 ↔
      (∃! u : (thetaShiftedWeightedDerivative alpha).domain,
        thetaShiftedWeightedDerivative alpha u = thetaSourceForcingVector ∧
          (let w : SourceSpace thetaSource :=
              (quantileUnitary thetaSource).symm
                (u : Lp ℂ 2 unitIntervalMeasure)
           (fun x => w x) =ᵐ[(volume : Measure ℝ)]
              thetaCuspHawkingDensityDress
                (thetaCuspHawkingBackreactionRapidityMode alpha))) ∧
        (∀ x : ℝ,
          thetaCuspHawkingBackreactionPencil q alpha
              (thetaCuspHawkingBackreactionRapidityMode alpha)
              (deriv (thetaCuspHawkingBackreactionRapidityMode alpha)) x =
            -(q : ℂ)) ∧
        ThetaCuspHawkingBackreactionResonance alpha := by
  constructor
  · intro hXi
    have hexact := (thetaShifted_sourceEquation_exact_iff alpha).mp hXi
    rcases hexact.1 with ⟨u, hu, huniq⟩
    refine ⟨⟨u, ?_, ?_⟩,
      thetaCuspHawkingBackreactionRapidityMode_equation q alpha,
      (xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance alpha).mp hXi⟩
    · refine ⟨hu.1, ?_⟩
      rw [thetaCuspHawkingDensityDress_rapidityMode]
      exact hu.2
    · intro v hv
      apply huniq v
      refine ⟨hv.1, ?_⟩
      rw [← thetaCuspHawkingDensityDress_rapidityMode]
      exact hv.2
  · rintro ⟨⟨u, hu, _⟩, _, _⟩
    exact (thetaSourceForcingVector_mem_shifted_range_iff alpha).mp ⟨u, hu.1⟩

/-- **[PROVED] Hawking-backreaction RH endpoint.** RH says exactly that every two-ended resonance of the
literal conformal-anomaly linearization lies on the real frequency axis. -/
theorem riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real :
    RiemannHypothesis ↔
      ∀ alpha : ℂ, ThetaCuspHawkingBackreactionResonance alpha → alpha.im = 0 := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro h alpha hres
    exact h alpha
      ((xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance alpha).mpr hres)
  · intro h alpha hXi
    exact h alpha
      ((xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance alpha).mp hXi)

end RHTower

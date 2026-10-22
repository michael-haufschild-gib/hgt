import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanStieltjesFlux
import GaloisForLFunctions.RHTower.LandauIntegralTransfer
import GaloisForLFunctions.RHTower.CCM.CCMRectangularScrewCurvature

/-!
# Suzuki screw Cesaro curvature recurrence

The paper theorem behind this module proves that Suzuki's initial screw average crosses the
central Xi curvature strictly in both directions at arbitrarily large apertures.  Its analytic
mechanism is Landau oscillation of the curvature-centered primitive: the primitive's Laplace
transform has genuine divisor poles up to its convergence abscissa but is regular at the real
boundary point.

This file formalizes the exact dependency-closed consumer layers already supported by the tree:

* the screw Cesaro mean and curvature-centered primitive;
* strict mean/primitive sign equivalence at positive aperture;
* equivalence between cofinal mean crossings and cofinal primitive sign changes;
* transfer of every negative crossing to an eventually valid dyadic negative-shift selector;
* the source-specific Xi screw-profile specialization;
* the contrapositive continuous Landau transfer used to rule out a nonnegative carrier when
  analytic continuation would force a divergent exponential moment to exist.

No RH hypothesis or numerical computation occurs here; every declaration is theorem-proved.
Formalizing the paper theorem's actual Xi Laplace-abscissa identification remains a
complex-analysis interface, not an assumed result in this module.
-/

open Complex Filter Topology MeasureTheory Set ProbabilityTheory
open scoped Interval NNReal ENNReal Topology

namespace RHTower

noncomputable section

/-- Cesaro mean of a real screw profile on the initial interval `[0,A]`. -/
def suzukiScrewCesaroMean (g : ℝ → ℝ) (A : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..A, g t) / A

/-- Primitive of a screw profile after subtracting a fixed curvature level. -/
def suzukiCurvatureCenteredPrimitive (g : ℝ → ℝ) (c A : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..A, (g t - c)

/-- Suzuki's convention `g=-Psi`, applied to the unconditional multiplicity-exact Xi screw
divisor. -/
def xiSuzukiScrewProfile (t : ℝ) : ℝ :=
  -(xiScrewDivisor t).re

/-- A real profile crosses a level strictly in both directions beyond every threshold. -/
def CofinallyCrosses (f : ℝ → ℝ) (c : ℝ) : Prop :=
  (∀ A0 : ℝ, ∃ A : ℝ, A0 < A ∧ f A < c) ∧
  (∀ A0 : ℝ, ∃ A : ℝ, A0 < A ∧ c < f A)

/-- The centered primitive is exactly aperture times the displacement of the Cesaro mean from
the curvature level. -/
theorem suzukiCurvatureCenteredPrimitive_eq
    {g : ℝ → ℝ} {c A : ℝ}
    (hg : IntervalIntegrable g volume 0 A) :
    suzukiCurvatureCenteredPrimitive g c A =
      A * (suzukiScrewCesaroMean g A - c) := by
  rw [suzukiCurvatureCenteredPrimitive, intervalIntegral.integral_sub hg
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume 0 A),
    intervalIntegral.integral_const, sub_zero, suzukiScrewCesaroMean]
  by_cases hA : A = 0
  · simp [hA]
  · field_simp [hA]
    ring

/-- At positive aperture, mean below curvature is exactly negativity of the centered primitive. -/
theorem suzukiScrewCesaroMean_lt_iff_centeredPrimitive_neg
    {g : ℝ → ℝ} {c A : ℝ}
    (hg : IntervalIntegrable g volume 0 A) (hA : 0 < A) :
    suzukiScrewCesaroMean g A < c ↔
      suzukiCurvatureCenteredPrimitive g c A < 0 := by
  rw [suzukiCurvatureCenteredPrimitive_eq hg]
  constructor <;> intro h
  · exact mul_neg_of_pos_of_neg hA (sub_neg.mpr h)
  · have : suzukiScrewCesaroMean g A - c < 0 := by nlinarith
    exact sub_neg.mp this

/-- Cofinal two-sided Cesaro crossing is equivalent to cofinal two-sided sign recurrence of the
curvature-centered primitive.  The `max A0 0` threshold records the required positive aperture. -/
theorem cofinallyCrosses_suzukiScrewCesaroMean_iff_centeredPrimitive
    {g : ℝ → ℝ} {c : ℝ}
    (hg : ∀ A : ℝ, IntervalIntegrable g volume 0 A) :
    CofinallyCrosses (suzukiScrewCesaroMean g) c ↔
      (∀ A0 : ℝ, ∃ A : ℝ, max A0 0 < A ∧
        suzukiCurvatureCenteredPrimitive g c A < 0) ∧
      (∀ A0 : ℝ, ∃ A : ℝ, max A0 0 < A ∧
        0 < suzukiCurvatureCenteredPrimitive g c A) := by
  constructor
  · rintro ⟨hbelow, habove⟩
    constructor
    · intro A0
      obtain ⟨A, hA, hbelowA⟩ := hbelow (max A0 0)
      refine ⟨A, hA, ?_⟩
      exact (suzukiScrewCesaroMean_lt_iff_centeredPrimitive_neg
        (hg A) (lt_of_le_of_lt (le_max_right A0 0) hA)).mp hbelowA
    · intro A0
      obtain ⟨A, hA, haboveA⟩ := habove (max A0 0)
      refine ⟨A, hA, ?_⟩
      rw [suzukiCurvatureCenteredPrimitive_eq (hg A)]
      exact mul_pos (lt_of_le_of_lt (le_max_right A0 0) hA) (sub_pos.mpr haboveA)
  · rintro ⟨hneg, hpos⟩
    constructor
    · intro A0
      obtain ⟨A, hA, hnegA⟩ := hneg A0
      refine ⟨A, lt_of_le_of_lt (le_max_left A0 0) hA, ?_⟩
      exact (suzukiScrewCesaroMean_lt_iff_centeredPrimitive_neg
        (hg A) (lt_of_le_of_lt (le_max_right A0 0) hA)).mpr hnegA
    · intro A0
      obtain ⟨A, hA, hposA⟩ := hpos A0
      refine ⟨A, lt_of_le_of_lt (le_max_left A0 0) hA, ?_⟩
      rw [suzukiCurvatureCenteredPrimitive_eq (hg A)] at hposA
      have hApos : 0 < A := lt_of_le_of_lt (le_max_right A0 0) hA
      have : 0 < suzukiScrewCesaroMean g A - c := by nlinarith
      exact sub_pos.mp this

/-- A dyadic affine intercept whose edge jet converges below a threshold is eventually below the
same threshold.  This is the positive counterpart to the small-aperture obstruction theorem. -/
theorem eventually_suzukiDyadicNegativeShiftIntercept_lt
    {q : ℝ → ℝ} {edgeLimit c : ℝ}
    (hq : Tendsto q atBot (nhds edgeLimit)) (hlimit : edgeLimit < c) :
    ∀ᶠ L in atTop, suzukiDyadicNegativeShiftIntercept q L < c := by
  have ht := tendsto_suzukiDyadicNegativeShiftIntercept_atTop hq
  exact (tendsto_order.1 ht).2 _ hlimit

/-- Every cofinal negative screw-average crossing selects an aperture at which the dyadic
negative-shift affine intercept eventually has the required strict central sign. -/
theorem cofinally_exists_eventually_suzukiDyadicNegativeShiftIntercept_lt
    {g : ℝ → ℝ} {c : ℝ} {q : ℝ → ℝ → ℝ}
    (hg : ∀ A : ℝ, IntervalIntegrable g volume 0 A)
    (hcross : CofinallyCrosses (suzukiScrewCesaroMean g) c)
    (hq : ∀ A : ℝ, Tendsto (q A) atBot (nhds (suzukiScrewCesaroMean g A))) :
    ∀ A0 : ℝ, ∃ A : ℝ, A0 < A ∧ 0 < A ∧
      ∀ᶠ L in atTop, suzukiDyadicNegativeShiftIntercept (q A) L < c := by
  intro A0
  obtain ⟨A, hA, hprim⟩ :=
    (cofinallyCrosses_suzukiScrewCesaroMean_iff_centeredPrimitive hg).mp hcross |>.1 A0
  have hApos : 0 < A := lt_of_le_of_lt (le_max_right A0 0) hA
  have havg : suzukiScrewCesaroMean g A < c :=
    (suzukiScrewCesaroMean_lt_iff_centeredPrimitive_neg (hg A) hApos).mpr hprim
  exact ⟨A, lt_of_le_of_lt (le_max_left A0 0) hA, hApos,
    eventually_suzukiDyadicNegativeShiftIntercept_lt (hq A) havg⟩

/-- Source-specific fixed-aperture connector.  Cofinal curvature crossing of Suzuki's actual Xi
screw profile selects arbitrarily large apertures whose sufficiently negative dyadic shift pair
has the strict central Herglotz residue sign. -/
theorem xiSuzukiScrewCesaroCrossing_selects_dyadicCentralFlux
    {q : ℝ → ℝ → ℝ}
    (hg : ∀ A : ℝ, IntervalIntegrable xiSuzukiScrewProfile volume 0 A)
    (hcross : CofinallyCrosses
      (suzukiScrewCesaroMean xiSuzukiScrewProfile)
      (deriv (deriv XiC) 0 / XiC 0).re)
    (hq : ∀ A : ℝ, Tendsto (q A) atBot
      (nhds (suzukiScrewCesaroMean xiSuzukiScrewProfile A))) :
    ∀ A0 : ℝ, ∃ A : ℝ, A0 < A ∧ 0 < A ∧
      ∀ᶠ L in atTop, suzukiDyadicNegativeShiftIntercept (q A) L <
        (deriv (deriv XiC) 0 / XiC 0).re :=
  cofinally_exists_eventually_suzukiDyadicNegativeShiftIntercept_lt hg hcross hq

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Contrapositive continuous Landau engine.  If a holomorphic MGF continuation would force a
known-divergent exponential moment to exist, the underlying carrier cannot be nonnegative almost
everywhere. -/
theorem not_ae_nonneg_of_landau_complexMGF_nonintegrable
    {X : Omega → ℝ} {mu : Measure Omega}
    (hzero : 0 ∈ interior (integrableExpSet X mu))
    {R : NNReal} {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G (Metric.closedBall 0 (R : ℝ)))
    (hagree : G =ᶠ[𝓝 0] complexMGF X mu)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrhoR : rho < (R : ℝ))
    (hdiverge : ¬ Integrable (fun omega => Real.exp (rho * X omega)) mu) :
    ¬ ∀ᵐ omega ∂mu, 0 ≤ X omega := by
  intro hX0
  exact hdiverge
    (landau_complexMGF_integrable_transfer hX0 hzero hGd hagree hrho0 hrhoR)

end

end RHTower

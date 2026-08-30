import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekAnalyticInfiniteBorelReflectionNoGo
import GaloisForLFunctions.HTGeometry.PeriodIncidenceFlatIntersection

/-!
# Singular all-orders-flat reflection carrier for Parikh--Wilczek

Exact critical-line Gamma reflection forces the positive-ray PW grade multiplier

`A(x^2) = x⁻¹ exp(x - 1/x)`.

The literal first finite-energy endpoint winding at backreaction scale `epsilon=x/4` is
`exp(-1/x)`, so the physical source constructs this forced multiplier exactly.  The multiplier
extends continuously by zero at the Borel origin, is positive on the positive ray, and is flatter
than every power there.  Its logarithmic profile is pointwise the reflected Gamma profile; hence
its Fourier transform is the exact functional-equation partner.

Fourier uniqueness proves positive-ray rigidity: every continuous-profile `L1` reflection carrier
has this multiplier.  No globally continuous complex extension analytic at zero can realize it,
by the prior analytic infinite-row no-go.  Thus this module discharges the singular/transseries
carrier premise in

`PW endpoint winding -> FE partner -> partner balance -> Deninger Ward -> RH`.

It does not assert the remaining source-dynamical balance law and uses no Xi-divisor data.

`[NEW] [EXISTENCE] [RIGIDITY] [PW-B PREMISE DISCHARGED] [LEAN-PROVED]`
-/

open Complex MeasureTheory Filter Set Topology Asymptotics
open scoped FourierTransform

namespace RHTower

noncomputable section

open GaloisForLFunctions

def schwarzschildParikhWilczekSingularFlatMultiplier (y : ℝ) : ℝ :=
  (Real.sqrt y)⁻¹ * Real.exp (Real.sqrt y - (Real.sqrt y)⁻¹)

theorem schwarzschildParikhWilczekSingularFlatMultiplier_nonneg (y : ℝ) :
    0 ≤ schwarzschildParikhWilczekSingularFlatMultiplier y := by
  rw [schwarzschildParikhWilczekSingularFlatMultiplier]
  positivity

theorem schwarzschildParikhWilczekSingularFlatMultiplier_pos
    {y : ℝ} (hy : 0 < y) :
    0 < schwarzschildParikhWilczekSingularFlatMultiplier y := by
  rw [schwarzschildParikhWilczekSingularFlatMultiplier]
  have hsqrt : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  exact mul_pos (inv_pos.mpr hsqrt) (Real.exp_pos _)

theorem schwarzschildParikhWilczekSingularFlatMultiplier_zero :
    schwarzschildParikhWilczekSingularFlatMultiplier 0 = 0 := by
  simp [schwarzschildParikhWilczekSingularFlatMultiplier]

theorem schwarzschildParikhWilczekSingularFlatMultiplier_le_sqrt
    (y : ℝ) :
    schwarzschildParikhWilczekSingularFlatMultiplier y ≤
      2 * Real.sqrt y * Real.exp (Real.sqrt y) := by
  by_cases hy : 0 < y
  · let t := Real.sqrt y
    have ht : 0 < t := Real.sqrt_pos.mpr hy
    have hflat := GaloisForLFunctions.exp_neg_inv_mul_inv_pow_le_factorial t ht 2
    norm_num at hflat
    rw [← inv_pow] at hflat
    change t⁻¹ * Real.exp (t - t⁻¹) ≤ 2 * t * Real.exp t
    calc
      t⁻¹ * Real.exp (t - t⁻¹) =
          (t * Real.exp t) * (Real.exp (-t⁻¹) * (t⁻¹) ^ 2) := by
        rw [sub_eq_add_neg, Real.exp_add]
        field_simp [ht.ne']
      _ ≤ (t * Real.exp t) * 2 :=
        mul_le_mul_of_nonneg_left hflat (by positivity)
      _ = 2 * t * Real.exp t := by ring
  · have hy' : y ≤ 0 := le_of_not_gt hy
    rw [schwarzschildParikhWilczekSingularFlatMultiplier,
      Real.sqrt_eq_zero_of_nonpos hy']
    norm_num

theorem continuousAt_schwarzschildParikhWilczekSingularFlatMultiplier_zero :
    ContinuousAt schwarzschildParikhWilczekSingularFlatMultiplier 0 := by
  have hupper : Tendsto
      (fun y : ℝ => 2 * Real.sqrt y * Real.exp (Real.sqrt y))
      (𝓝 0) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝 0) (𝓝 2) := tendsto_const_nhds
    have hsqrt : Tendsto (fun y : ℝ => Real.sqrt y) (𝓝 0) (𝓝 0) := by
      have h := (Real.continuous_sqrt.continuousAt :
        ContinuousAt (fun y : ℝ => Real.sqrt y) 0)
      simpa only [Real.sqrt_zero] using h.tendsto
    have hexp : Tendsto (fun y : ℝ => Real.exp (Real.sqrt y))
        (𝓝 0) (𝓝 1) := by
      have hexp0 : Tendsto Real.exp (𝓝 0) (𝓝 1) := by
        have h := (Real.continuous_exp.continuousAt :
          ContinuousAt Real.exp 0)
        simpa only [Real.exp_zero] using h.tendsto
      simpa [Function.comp_def] using hexp0.comp hsqrt
    simpa using (hc.mul hsqrt).mul hexp
  have hzero : Tendsto schwarzschildParikhWilczekSingularFlatMultiplier
      (𝓝 0) (𝓝 0) := by
    refine squeeze_zero' (g := fun y : ℝ =>
      2 * Real.sqrt y * Real.exp (Real.sqrt y)) ?_ ?_ hupper
    · exact Filter.Eventually.of_forall
        schwarzschildParikhWilczekSingularFlatMultiplier_nonneg
    · exact Filter.Eventually.of_forall
        schwarzschildParikhWilczekSingularFlatMultiplier_le_sqrt
  show Tendsto schwarzschildParikhWilczekSingularFlatMultiplier
    (𝓝 0) (𝓝 (schwarzschildParikhWilczekSingularFlatMultiplier 0))
  rw [schwarzschildParikhWilczekSingularFlatMultiplier_zero]
  exact hzero

theorem schwarzschildParikhWilczekSingularFlatMultiplier_div_pow_le
    (N : ℕ) {y : ℝ} (hy : 0 < y) :
    schwarzschildParikhWilczekSingularFlatMultiplier y / y ^ N ≤
      ((2 * N + 2).factorial : ℝ) * Real.sqrt y *
        Real.exp (Real.sqrt y) := by
  let t := Real.sqrt y
  have ht : 0 < t := Real.sqrt_pos.mpr hy
  have hy_sq : y = t ^ 2 := by
    symm
    exact Real.sq_sqrt hy.le
  have hflat := GaloisForLFunctions.exp_neg_inv_mul_inv_pow_le_factorial
    t ht (2 * N + 2)
  rw [schwarzschildParikhWilczekSingularFlatMultiplier, hy_sq]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
  change t⁻¹ * Real.exp (t - t⁻¹) / (t ^ 2) ^ N ≤
    ((2 * N + 2).factorial : ℝ) * t * Real.exp t
  have hpower :
      t⁻¹ / (t ^ 2) ^ N = t * (t⁻¹) ^ (2 * N + 2) := by
    have hpow : (t ^ 2) ^ N ≠ 0 := pow_ne_zero N (pow_ne_zero 2 ht.ne')
    rw [show 2 * N + 2 = 2 * N + 2 by omega, pow_add, pow_mul]
    field_simp [ht.ne', hpow]
    rw [← mul_pow]
    field_simp [ht.ne']
    simp
  calc
    t⁻¹ * Real.exp (t - t⁻¹) / (t ^ 2) ^ N =
        (t * Real.exp t) *
          (Real.exp (-t⁻¹) * (t⁻¹) ^ (2 * N + 2)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      rw [show t⁻¹ * (Real.exp t * Real.exp (-t⁻¹)) / (t ^ 2) ^ N =
        Real.exp t * Real.exp (-t⁻¹) * (t⁻¹ / (t ^ 2) ^ N) by ring]
      rw [hpower]
      ring
    _ ≤ (t * Real.exp t) * ((2 * N + 2).factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hflat (by positivity)
    _ = ((2 * N + 2).factorial : ℝ) * t * Real.exp t := by ring

theorem tendsto_schwarzschildParikhWilczekSingularFlatMultiplier_div_pow_zero
    (N : ℕ) :
    Tendsto (fun y : ℝ =>
      schwarzschildParikhWilczekSingularFlatMultiplier y / y ^ N)
      (𝓝[>] 0) (𝓝 0) := by
  have hupper : Tendsto
      (fun y : ℝ => ((2 * N + 2).factorial : ℝ) * Real.sqrt y *
        Real.exp (Real.sqrt y))
      (𝓝 0) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => ((2 * N + 2).factorial : ℝ))
        (𝓝 0) (𝓝 ((2 * N + 2).factorial : ℝ)) := tendsto_const_nhds
    have hsqrt : Tendsto (fun y : ℝ => Real.sqrt y) (𝓝 0) (𝓝 0) := by
      have h := (Real.continuous_sqrt.continuousAt :
        ContinuousAt (fun y : ℝ => Real.sqrt y) 0)
      simpa only [Real.sqrt_zero] using h.tendsto
    have hexp : Tendsto (fun y : ℝ => Real.exp (Real.sqrt y))
        (𝓝 0) (𝓝 1) := by
      have hexp0 : Tendsto Real.exp (𝓝 0) (𝓝 1) := by
        have h := (Real.continuous_exp.continuousAt :
          ContinuousAt Real.exp 0)
        simpa only [Real.exp_zero] using h.tendsto
      simpa [Function.comp_def] using hexp0.comp hsqrt
    simpa using (hc.mul hsqrt).mul hexp
  refine squeeze_zero'
    (g := fun y : ℝ => ((2 * N + 2).factorial : ℝ) * Real.sqrt y *
      Real.exp (Real.sqrt y)) ?_ ?_ (hupper.mono_left nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact div_nonneg
      (schwarzschildParikhWilczekSingularFlatMultiplier_nonneg y)
      (pow_nonneg hy.le N)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact schwarzschildParikhWilczekSingularFlatMultiplier_div_pow_le N hy

theorem continuous_schwarzschildParikhWilczekSingularFlatMultiplier :
    Continuous schwarzschildParikhWilczekSingularFlatMultiplier := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨-y, by linarith, ?_⟩
    intro z hz
    rw [Real.dist_eq] at hz
    have hzlt : z < 0 := by
      have hzsub : z - y < -y := (abs_lt.mp hz).2
      linarith
    simp [schwarzschildParikhWilczekSingularFlatMultiplier,
      Real.sqrt_eq_zero_of_nonpos hy.le,
      Real.sqrt_eq_zero_of_nonpos hzlt.le, hε]
  · exact continuousAt_schwarzschildParikhWilczekSingularFlatMultiplier_zero
  · change ContinuousAt (fun x : ℝ =>
      (Real.sqrt x)⁻¹ * Real.exp (Real.sqrt x - (Real.sqrt x)⁻¹)) y
    have hsqrt : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
    fun_prop

theorem schwarzschildParikhWilczekSingularFlatMultiplier_of_sq
    {x : ℝ} (hx : 0 < x) :
    schwarzschildParikhWilczekSingularFlatMultiplier (x ^ 2) =
      x⁻¹ * Real.exp (x - x⁻¹) := by
  rw [schwarzschildParikhWilczekSingularFlatMultiplier,
    Real.sqrt_sq_eq_abs, abs_of_pos hx]

theorem schwarzschildParikhWilczekFirstEndpointWinding_scaled
    {x : ℝ} (hx : 0 < x) :
    schwarzschildParikhWilczekWindingTerm 0 (x / 4)
        (schwarzschildParikhWilczekDimensionlessEnergyEndpoint (x / 4)) =
      Real.exp (-x⁻¹) := by
  rw [schwarzschildParikhWilczekWindingTerm_energyEndpoint 0 (by positivity),
    schwarzschildParikhWilczekEndpointAction_zero]
  congr 1
  field_simp [hx.ne']

theorem schwarzschildParikhWilczekSingularFlatMultiplier_eq_source
    {x : ℝ} (hx : 0 < x) :
    schwarzschildParikhWilczekSingularFlatMultiplier (x ^ 2) =
      x⁻¹ * Real.exp x *
        schwarzschildParikhWilczekWindingTerm 0 (x / 4)
          (schwarzschildParikhWilczekDimensionlessEnergyEndpoint (x / 4)) := by
  rw [schwarzschildParikhWilczekSingularFlatMultiplier_of_sq hx,
    schwarzschildParikhWilczekFirstEndpointWinding_scaled hx]
  calc
    x⁻¹ * Real.exp (x - x⁻¹) =
        x⁻¹ * (Real.exp x * Real.exp (-x⁻¹)) := by
      rw [← Real.exp_add]
      congr 2
    _ = x⁻¹ * Real.exp x * Real.exp (-x⁻¹) := by ring

def schwarzschildParikhWilczekSingularFlatLogProfile (u : ℝ) : ℂ :=
  expShiftC (1 / 2) u *
    (schwarzschildParikhWilczekSingularFlatMultiplier (Real.exp (2 * u)) : ℂ)

theorem schwarzschildParikhWilczekSingularFlatLogProfile_eq
    (u : ℝ) :
    schwarzschildParikhWilczekSingularFlatLogProfile u =
      schwarzschildParikhWilczekReflectedGammaLogProfile u := by
  have hx : 0 < Real.exp u := Real.exp_pos _
  have hsq : Real.exp (2 * u) = Real.exp u ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [schwarzschildParikhWilczekSingularFlatLogProfile,
    schwarzschildParikhWilczekReflectedGammaLogProfile, expShiftC, expShift]
  rw [
    hsq, schwarzschildParikhWilczekSingularFlatMultiplier_of_sq hx]
  norm_num
  rw [← Complex.exp_neg]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

def schwarzschildParikhWilczekPositiveRayBorelLogProfile
    (A : ℝ → ℂ) (u : ℝ) : ℂ :=
  expShiftC (1 / 2) u * A (Real.exp (2 * u))

theorem schwarzschildParikhWilczekSingularFlatLogProfile_eq_positiveRay
    (u : ℝ) :
    schwarzschildParikhWilczekSingularFlatLogProfile u =
      schwarzschildParikhWilczekPositiveRayBorelLogProfile
        (fun y => (schwarzschildParikhWilczekSingularFlatMultiplier y : ℂ)) u := rfl

theorem schwarzschildParikhWilczekSingularFlatLogProfile_fun_eq :
    schwarzschildParikhWilczekSingularFlatLogProfile =
      schwarzschildParikhWilczekReflectedGammaLogProfile := by
  funext u
  exact schwarzschildParikhWilczekSingularFlatLogProfile_eq u

structure PWPositiveRaySingularBorelReflectionData where
  multiplier : ℝ → ℂ
  continuous_logProfile :
    Continuous (schwarzschildParikhWilczekPositiveRayBorelLogProfile multiplier)
  integrable_logProfile :
    Integrable (schwarzschildParikhWilczekPositiveRayBorelLogProfile multiplier)
  reflects : ∀ ξ : ℝ,
    𝓕 (schwarzschildParikhWilczekPositiveRayBorelLogProfile multiplier) ξ =
      𝓕 schwarzschildParikhWilczekReflectedGammaLogProfile ξ

def schwarzschildParikhWilczekSingularBorelReflectionData :
    PWPositiveRaySingularBorelReflectionData where
  multiplier := fun y => (schwarzschildParikhWilczekSingularFlatMultiplier y : ℂ)
  continuous_logProfile := by
    change Continuous schwarzschildParikhWilczekSingularFlatLogProfile
    rw [schwarzschildParikhWilczekSingularFlatLogProfile_fun_eq]
    exact continuous_schwarzschildParikhWilczekReflectedGammaLogProfile
  integrable_logProfile := by
    change Integrable schwarzschildParikhWilczekSingularFlatLogProfile
    rw [schwarzschildParikhWilczekSingularFlatLogProfile_fun_eq]
    exact integrable_schwarzschildParikhWilczekReflectedGammaLogProfile
  reflects := by
    intro ξ
    change 𝓕 schwarzschildParikhWilczekSingularFlatLogProfile ξ = _
    rw [schwarzschildParikhWilczekSingularFlatLogProfile_fun_eq]

theorem fourier_schwarzschildParikhWilczekSingularFlatLogProfile (ξ : ℝ) :
    𝓕 schwarzschildParikhWilczekSingularFlatLogProfile ξ =
      Complex.Gamma (((1 / 2 : ℝ) : ℂ) +
        ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  rw [schwarzschildParikhWilczekSingularFlatLogProfile_fun_eq]
  exact fourier_schwarzschildParikhWilczekReflectedGammaLogProfile ξ

theorem PWPositiveRaySingularBorelReflectionData.logProfile_eq
    (D : PWPositiveRaySingularBorelReflectionData) (u : ℝ) :
    schwarzschildParikhWilczekPositiveRayBorelLogProfile D.multiplier u =
      schwarzschildParikhWilczekReflectedGammaLogProfile u := by
  have hae := HTGeometry.ae_eq_of_fourierIntegral_eq
    D.integrable_logProfile
    integrable_schwarzschildParikhWilczekReflectedGammaLogProfile D.reflects
  exact eq_at_of_ae_eq_of_continuousAt hae
    D.continuous_logProfile.continuousAt
    continuous_schwarzschildParikhWilczekReflectedGammaLogProfile.continuousAt

theorem PWPositiveRaySingularBorelReflectionData.multiplier_eq_source_of_pos
    (D : PWPositiveRaySingularBorelReflectionData) {y : ℝ} (hy : 0 < y) :
    D.multiplier y =
      (schwarzschildParikhWilczekSingularFlatMultiplier y : ℂ) := by
  let u : ℝ := Real.log y / 2
  have hexp : Real.exp (2 * u) = y := by
    rw [show 2 * u = Real.log y by dsimp [u]; ring]
    exact Real.exp_log hy
  have hD := D.logProfile_eq u
  have hS := schwarzschildParikhWilczekSingularFlatLogProfile_eq u
  rw [schwarzschildParikhWilczekPositiveRayBorelLogProfile, hexp] at hD
  rw [schwarzschildParikhWilczekSingularFlatLogProfile, hexp] at hS
  have hfactor : expShiftC (1 / 2) u ≠ 0 := by
    rw [expShiftC, expShift]
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  exact mul_left_cancel₀ hfactor (hD.trans hS.symm)

theorem no_continuous_analytic_schwarzschildParikhWilczekSingularFlatMultiplier_extension :
    ¬ ∃ B : ℂ → ℂ, Continuous B ∧ AnalyticAt ℂ B 0 ∧
      ∀ y : ℝ, 0 < y →
        B (y : ℂ) = (schwarzschildParikhWilczekSingularFlatMultiplier y : ℂ) := by
  rintro ⟨B, hBcont, hBanalytic, hBsource⟩
  have hprofile :
      schwarzschildParikhWilczekInfiniteBorelLogProfile B =
        schwarzschildParikhWilczekReflectedGammaLogProfile := by
    funext u
    rw [schwarzschildParikhWilczekInfiniteBorelLogProfile,
      hBsource (Real.exp (2 * u)) (Real.exp_pos _)]
    exact schwarzschildParikhWilczekSingularFlatLogProfile_eq u
  let D : PWAnalyticInfiniteBorelReflectionData := {
    multiplier := B
    analyticAt_zero := hBanalytic
    continuous := hBcont
    integrable_logProfile := by
      rw [hprofile]
      exact integrable_schwarzschildParikhWilczekReflectedGammaLogProfile
    reflects := by
      intro ξ
      rw [hprofile] }
  exact no_PWAnalyticInfiniteBorelReflectionData.false D

def SchwarzschildParikhWilczekSingularFlatReflectionCarrier : Prop :=
  ∃ D : PWPositiveRaySingularBorelReflectionData,
    ∀ E : PWPositiveRaySingularBorelReflectionData, ∀ y : ℝ, 0 < y →
      E.multiplier y = D.multiplier y

theorem schwarzschildParikhWilczek_singularFlatReflectionCarrier :
    SchwarzschildParikhWilczekSingularFlatReflectionCarrier := by
  refine ⟨schwarzschildParikhWilczekSingularBorelReflectionData, ?_⟩
  intro E y hy
  rw [E.multiplier_eq_source_of_pos hy]
  rfl

end

end RHTower

import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry
import GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationInformationProperness
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Local renewal action threshold

This module proves the event-level KL disintegration, exact exponential-aperture/polynomial-work
liminf coefficient, divergence through degree two, and compact product-action properness used by
ULF-CRG-1.  All estimates are symbolic and allow scale-dependent probability spaces.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X]

noncomputable def apertureIndicator (A : Set X) (x : X) : Bool := by
  classical
  exact if x ∈ A then true else false

theorem measurable_apertureIndicator {A : Set X} (hA : MeasurableSet A) :
    Measurable (apertureIndicator A) := by
  apply measurable_to_bool
  convert hA using 1
  ext x
  classical
  simp [apertureIndicator]

def apertureProbability (mu : Measure X) [IsProbabilityMeasure mu] (A : Set X) : unitInterval :=
  ⟨mu.real A, measureReal_nonneg, measureReal_le_one⟩

@[simp] theorem coe_apertureProbability (mu : Measure X) [IsProbabilityMeasure mu] (A : Set X) :
    ((apertureProbability mu A : unitInterval) : ℝ) = mu.real A := rfl

theorem map_apertureIndicator_eq_bernoulli
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) :
    mu.map (apertureIndicator A) = Ber(true, false, apertureProbability mu A) := by
  apply Measure.ext_of_measureReal_singleton
  intro b
  have hAne : mu A ≠ ∞ := measure_ne_top mu A
  rw [Measure.real, Measure.map_apply (measurable_apertureIndicator hA)
    (measurableSet_singleton b)]
  cases b
  · have hpre : apertureIndicator A ⁻¹' {false} = Aᶜ := by
      ext x
      classical
      simp [apertureIndicator]
    rw [hpre, measure_compl hA hAne]
    rw [measure_univ]
    have hAle0 : mu A ≤ mu (Set.univ : Set X) := measure_mono (subset_univ A)
    have hAle : mu A ≤ 1 := by simpa using hAle0
    have hsub : (1 - mu A).toReal = 1 - (mu A).toReal :=
      ENNReal.toReal_sub_of_le hAle (by simp)
    rw [hsub]
    simp [apertureProbability, Measure.real]
  · have hpre : apertureIndicator A ⁻¹' {true} = A := by
      ext x
      classical
      simp [apertureIndicator]
    rw [hpre]
    simp [apertureProbability, Measure.real]

/-- Exact binary relative entropy produced by observing one measurable aperture. -/
theorem toReal_klDiv_map_apertureIndicator
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : Set X) (hA : MeasurableSet A)
    (hnu0 : 0 < nu.real A) (hnu1 : nu.real A < 1)
    (hmu0 : 0 < mu.real A) (hmu1 : mu.real A < 1) :
    (klDiv (nu.map (apertureIndicator A)) (mu.map (apertureIndicator A))).toReal =
      nu.real A * Real.log (nu.real A / mu.real A) +
        (1 - nu.real A) * Real.log ((1 - nu.real A) / (1 - mu.real A)) := by
  rw [map_apertureIndicator_eq_bernoulli nu A hA,
    map_apertureIndicator_eq_bernoulli mu A hA]
  exact toReal_klDiv_bernoulli _ _ hnu0 hnu1 hmu0 hmu1

/-- Binary aperture information is the least possible renewal information at fixed aperture mass. -/
theorem aperture_binary_klDiv_le
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : Set X) (hA : MeasurableSet A) :
    klDiv Ber(true, false, apertureProbability nu A)
        Ber(true, false, apertureProbability mu A) ≤ klDiv nu mu := by
  rw [← map_apertureIndicator_eq_bernoulli nu A hA,
    ← map_apertureIndicator_eq_bernoulli mu A hA]
  exact klDiv_map_le_arbitrary nu mu (apertureIndicator A)
    (measurable_apertureIndicator hA)

/-- Uniform entropy form of the binary aperture lower bound. -/
theorem toReal_klDiv_bernoulli_lower
    (p r : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    (p : ℝ) * Real.log (1 / (r : ℝ)) - Real.log 2 ≤
      (klDiv Ber(true, false, p) Ber(true, false, r)).toReal := by
  rw [toReal_klDiv_bernoulli p r hp0 hp1 hr0 hr1]
  calc
    (p : ℝ) * Real.log (1 / (r : ℝ)) - Real.log 2 ≤
        (p : ℝ) * Real.log (1 / (r : ℝ)) - Real.binEntropy (p : ℝ) :=
      sub_le_sub_left Real.binEntropy_le_log_two _
    _ ≤ (p : ℝ) * Real.log ((p : ℝ) / (r : ℝ)) +
        (1 - (p : ℝ)) * Real.log ((1 - (p : ℝ)) / (1 - (r : ℝ))) := by
      have hcomp0 : 0 ≤ 1 - (r : ℝ) := (sub_pos.mpr hr1).le
      have hcomp1 : 1 - (r : ℝ) ≤ 1 := by linarith
      have hlogcomp : Real.log (1 - (r : ℝ)) ≤ 0 := Real.log_nonpos hcomp0 hcomp1
      have hnonneg : 0 ≤ (1 - (p : ℝ)) * (-Real.log (1 - (r : ℝ))) :=
        mul_nonneg (sub_pos.mpr hp1).le (neg_nonneg.mpr hlogcomp)
      rw [Real.binEntropy, Real.log_div hp0.ne' hr0.ne',
        Real.log_div (sub_pos.mpr hp1).ne' (sub_pos.mpr hr1).ne',
        one_div]
      simp only [Real.log_inv]
      nlinarith

noncomputable def aperturePotential (A : Set X) (t : ℝ) (x : X) : ℝ := by
  classical
  exact if x ∈ A then t else 0

theorem measurable_aperturePotential {A : Set X} (hA : MeasurableSet A) (t : ℝ) :
    Measurable (aperturePotential A t) := by
  classical
  exact Measurable.piecewise hA measurable_const measurable_const

theorem integrable_aperturePotential
    (nu : Measure X) [IsFiniteMeasure nu] {A : Set X} (hA : MeasurableSet A) (t : ℝ) :
    Integrable (aperturePotential A t) nu := by
  have heq : aperturePotential A t = A.indicator (fun _ => t) := by
    funext x
    classical
    by_cases hx : x ∈ A <;> simp [aperturePotential, Set.indicator, hx]
  rw [heq]
  exact (integrable_const t).indicator hA

theorem integral_aperturePotential
    (nu : Measure X) [IsProbabilityMeasure nu] {A : Set X} (hA : MeasurableSet A) (t : ℝ) :
    (∫ x, aperturePotential A t x ∂nu) = t * nu.real A := by
  have heq : aperturePotential A t = A.indicator (fun _ => t) := by
    funext x
    classical
    by_cases hx : x ∈ A <;> simp [aperturePotential, Set.indicator, hx]
  rw [heq, integral_indicator hA]
  simp [Measure.real, mul_comm]

theorem integrable_exp_aperturePotential
    (mu : Measure X) [IsFiniteMeasure mu] {A : Set X} (hA : MeasurableSet A) (t : ℝ) :
    Integrable (fun x => Real.exp (aperturePotential A t x)) mu := by
  have heq : (fun x => Real.exp (aperturePotential A t x)) =
      A.indicator (fun _ => Real.exp t) + Aᶜ.indicator (fun _ => 1) := by
    funext x
    classical
    by_cases hx : x ∈ A <;> simp [aperturePotential, Set.indicator, hx]
  rw [heq]
  exact ((integrable_const (Real.exp t)).indicator hA).add
    ((integrable_const 1).indicator hA.compl)

theorem integral_exp_aperturePotential
    (mu : Measure X) [IsProbabilityMeasure mu] {A : Set X} (hA : MeasurableSet A) (t : ℝ) :
    (∫ x, Real.exp (aperturePotential A t x) ∂mu) =
      Real.exp t * mu.real A + mu.real Aᶜ := by
  have heq : (fun x => Real.exp (aperturePotential A t x)) =
      A.indicator (fun _ => Real.exp t) + Aᶜ.indicator (fun _ => 1) := by
    funext x
    classical
    by_cases hx : x ∈ A <;> simp [aperturePotential, Set.indicator, hx]
  rw [heq]
  change (∫ x, A.indicator (fun _ => Real.exp t) x +
    Aᶜ.indicator (fun _ => 1) x ∂mu) = _
  rw [integral_add
      ((integrable_const (Real.exp t)).indicator hA)
      ((integrable_const 1).indicator hA.compl),
    integral_indicator hA, integral_indicator hA.compl]
  simp [Measure.real, mul_comm]

/-- One-event exponential tilt bound, valid on every measurable probability space. -/
theorem aperturePotential_entropy_lower
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : Set X) (hA : MeasurableSet A) (t : ℝ)
    (hfin : klDiv nu mu ≠ ⊤) :
    t * nu.real A - Real.log (Real.exp t * mu.real A + mu.real Aᶜ) ≤
      (klDiv nu mu).toReal := by
  have h := integral_le_klDiv_add_log_integral_exp mu nu (aperturePotential A t)
    (integrable_aperturePotential nu hA t)
    (integrable_exp_aperturePotential mu hA t) hfin
  rw [integral_aperturePotential nu hA t,
    integral_exp_aperturePotential mu hA t] at h
  linarith

theorem aperturePotential_entropy_lower_one_add
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : Set X) (hA : MeasurableSet A) (t : ℝ)
    (hfin : klDiv nu mu ≠ ⊤) :
    t * nu.real A - Real.log (1 + Real.exp t * mu.real A) ≤
      (klDiv nu mu).toReal := by
  have hbase := aperturePotential_entropy_lower mu nu A hA t hfin
  have hZpos : 0 < Real.exp t * mu.real A + mu.real Aᶜ := by
    have h := integral_exp_pos (integrable_exp_aperturePotential mu hA t)
    rw [integral_exp_aperturePotential mu hA t] at h
    exact h
  have hZle : Real.exp t * mu.real A + mu.real Aᶜ ≤
      1 + Real.exp t * mu.real A := by
    linarith [(measureReal_le_one (μ := mu) : mu.real Aᶜ ≤ 1)]
  have hlogle := Real.log_le_log hZpos hZle
  linarith

/-- Exponential aperture evacuation gives a tunable local renewal lower bound. -/
theorem exponentialAperture_localAction_lower
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : Set X) (hA : MeasurableSet A)
    (C beta delta t : ℝ)
    (hC : 0 ≤ C) (hdelta : delta = beta - t)
    (hmass : mu.real A ≤ C * Real.exp (-beta))
    (hfin : klDiv nu mu ≠ ⊤) :
    t * nu.real A - C * Real.exp (-delta) ≤ (klDiv nu mu).toReal := by
  have hbase := aperturePotential_entropy_lower_one_add mu nu A hA t hfin
  have hmassScaled : Real.exp t * mu.real A ≤ C * Real.exp (-delta) := by
    calc
      Real.exp t * mu.real A ≤ Real.exp t * (C * Real.exp (-beta)) :=
        mul_le_mul_of_nonneg_left hmass (Real.exp_pos t).le
      _ = C * (Real.exp t * Real.exp (-beta)) := by ring
      _ = C * Real.exp (-delta) := by
        rw [← Real.exp_add]
        have harg : t + -beta = -delta := by linarith
        rw [harg]
  have hres0 : 0 ≤ C * Real.exp (-delta) := mul_nonneg hC (Real.exp_pos _).le
  have hlogmajor : Real.log (1 + Real.exp t * mu.real A) ≤
      C * Real.exp (-delta) := by
    have harg0 : 0 < 1 + Real.exp t * mu.real A := by
      positivity
    calc
      Real.log (1 + Real.exp t * mu.real A) ≤ Real.exp t * mu.real A := by
        have := Real.log_le_sub_one_of_pos harg0
        linarith
      _ ≤ C * Real.exp (-delta) := hmassScaled
  linarith

/-- Pointwise scaled lower bound behind the cofinal liminf law. -/
theorem polynomialCurrent_scaledAction_lower
    (alpha W I : ℕ → ℝ) (K c d lambda C beta : ℝ) (n : ℕ)
    (hK : 0 < K) (hc : 0 < c) (hlambda : 0 < lambda)
    (halpha : 0 ≤ alpha n)
    (hwork : W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : c ≤ alpha n * W n)
    (hlocal : lambda * ((n + 1 : ℕ) : ℝ) * alpha n -
      C * Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) ≤ I n) :
    c * lambda / K - C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
        Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) ≤
      ((n + 1 : ℕ) : ℝ) ^ (d - 1) * I n := by
  let s : ℝ := ((n + 1 : ℕ) : ℝ)
  have hs : 0 < s := by positivity
  have hpow : 0 < s ^ d := Real.rpow_pos_of_pos hs _
  have hden : 0 < K * s ^ d := mul_pos hK hpow
  have hcwork : c ≤ alpha n * (K * s ^ d) :=
    hcurrent.trans (mul_le_mul_of_nonneg_left hwork halpha)
  have halphaLower : c / (K * s ^ d) ≤ alpha n :=
    (div_le_iff₀ hden).2 (by simpa [mul_assoc] using hcwork)
  have hbase : c * lambda / K * s ^ (1 - d) ≤ lambda * s * alpha n := by
    have hscaled := mul_le_mul_of_nonneg_left halphaLower
      (mul_nonneg hlambda.le hs.le)
    calc
      c * lambda / K * s ^ (1 - d) =
          (lambda * s) * (c / (K * s ^ d)) := by
        rw [Real.rpow_sub hs, Real.rpow_one]
        field_simp
      _ ≤ (lambda * s) * alpha n := hscaled
      _ = lambda * s * alpha n := by ring
  have hraw : c * lambda / K * s ^ (1 - d) -
      C * Real.exp (-(beta - lambda) * s) ≤ I n := by
    dsimp [s] at hlocal ⊢
    linarith
  have hscale0 : 0 ≤ s ^ (d - 1) := Real.rpow_nonneg hs.le _
  have hscaled := mul_le_mul_of_nonneg_left hraw hscale0
  dsimp [s] at hscaled ⊢
  calc
    c * lambda / K - C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
          Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) =
        ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
          (c * lambda / K * ((n + 1 : ℕ) : ℝ) ^ (1 - d) -
            C * Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ))) := by
      have hs' : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hcancel : ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
          ((n + 1 : ℕ) : ℝ) ^ (1 - d) = 1 := by
        rw [← Real.rpow_add hs']
        have hexp : d - 1 + (1 - d) = 0 := by ring
        rw [hexp, Real.rpow_zero]
      have hmain : ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
          (c * lambda / K * ((n + 1 : ℕ) : ℝ) ^ (1 - d)) =
          c * lambda / K := by
        calc
          ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
              (c * lambda / K * ((n + 1 : ℕ) : ℝ) ^ (1 - d)) =
              (c * lambda / K) *
                (((n + 1 : ℕ) : ℝ) ^ (d - 1) *
                  ((n + 1 : ℕ) : ℝ) ^ (1 - d)) := by ring
          _ = c * lambda / K := by rw [hcancel, mul_one]
      rw [mul_sub, hmain]
      ring
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (d - 1) * I n := hscaled

/-- Every strict exponential tilt rate gives a cofinal scaled-action liminf bound. -/
theorem polynomialCurrent_action_liminf_lower_of_rate
    (alpha W I : ℕ → ℝ) (K c d lambda C beta : ℝ)
    (hK : 0 < K) (hc : 0 < c) (hlambda : 0 < lambda) (hlt : lambda < beta)
    (halpha : ∀ n, 0 ≤ alpha n)
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ alpha n * W n)
    (hlocal : ∀ n, lambda * ((n + 1 : ℕ) : ℝ) * alpha n -
      C * Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) ≤ I n) :
    ((c * lambda / K : ℝ) : EReal) ≤
      liminf (fun n => ((((n + 1 : ℕ) : ℝ) ^ (d - 1) * I n : ℝ) : EReal)) atTop := by
  let L : EReal :=
    liminf (fun n => ((((n + 1 : ℕ) : ℝ) ^ (d - 1) * I n : ℝ) : EReal)) atTop
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hdecay : Tendsto
      (fun n : ℕ => C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
        Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    have hraw := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (d - 1) (beta - lambda) (sub_pos.mpr hlt)).comp hcast
    simpa only [Function.comp_apply, mul_assoc, mul_zero] using
      ((tendsto_const_nhds (x := C)).mul hraw)
  by_contra hbound
  have hLlt : L < ((c * lambda / K : ℝ) : EReal) := lt_of_not_ge hbound
  obtain ⟨a, hLa, hacoeff⟩ := EReal.exists_between_coe_real hLlt
  have hacoeffReal : a < c * lambda / K := EReal.coe_lt_coe_iff.mp hacoeff
  have hgap : 0 < c * lambda / K - a := sub_pos.mpr hacoeffReal
  have heventError : ∀ᶠ n : ℕ in atTop,
      C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
        Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) <
          c * lambda / K - a := hdecay.eventually_lt_const hgap
  have heventLower : ∀ᶠ n : ℕ in atTop,
      (a : EReal) ≤ ((((n + 1 : ℕ) : ℝ) ^ (d - 1) * I n : ℝ) : EReal) := by
    filter_upwards [heventError] with n hn
    have hscaled := polynomialCurrent_scaledAction_lower alpha W I K c d lambda C beta n
      hK hc hlambda (halpha n)
      (hwork n) (hcurrent n) (hlocal n)
    apply EReal.coe_le_coe_iff.mpr
    linarith
  have haL : (a : EReal) ≤ L := by
    exact Filter.le_liminf_of_le (by isBoundedDefault) heventLower
  exact (not_lt_of_ge haL hLa)

/-- A finite sum of local actions is impossible at or below the quadratic work wall. -/
theorem polynomialCurrent_action_not_summable_of_degree_le_two
    (alpha W I : ℕ → ℝ) (K c d lambda C beta : ℝ)
    (hK : 0 < K) (hc : 0 < c) (hlambda : 0 < lambda) (hlt : lambda < beta)
    (halpha : ∀ n, 0 ≤ alpha n)
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ alpha n * W n)
    (hlocal : ∀ n, lambda * ((n + 1 : ℕ) : ℝ) * alpha n -
      C * Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) ≤ I n)
    (hd : d ≤ 2) :
    ¬ Summable I := by
  let coeff : ℝ := c * lambda / K
  have hcoeff : 0 < coeff := div_pos (mul_pos hc hlambda) hK
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hdecay : Tendsto
      (fun n : ℕ => C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
        Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    have hraw := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (d - 1) (beta - lambda) (sub_pos.mpr hlt)).comp hcast
    simpa only [Function.comp_apply, mul_assoc, mul_zero] using
      ((tendsto_const_nhds (x := C)).mul hraw)
  have heventError : ∀ᶠ n : ℕ in atTop,
      C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
        Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) < coeff / 2 :=
    hdecay.eventually_lt_const (half_pos hcoeff)
  have heventLower : ∀ᶠ n : ℕ in atTop,
      coeff / 2 * ((n + 1 : ℕ) : ℝ) ^ (1 - d) ≤ I n := by
    filter_upwards [heventError] with n hn
    have hscaled := polynomialCurrent_scaledAction_lower alpha W I K c d lambda C beta n
      hK hc hlambda (halpha n) (hwork n) (hcurrent n) (hlocal n)
    let s : ℝ := ((n + 1 : ℕ) : ℝ)
    have hs : 0 < s := by positivity
    have hcancel : s ^ (1 - d) * s ^ (d - 1) = 1 := by
      rw [← Real.rpow_add hs]
      have hexp : 1 - d + (d - 1) = 0 := by ring
      rw [hexp, Real.rpow_zero]
    have hhalfScaled : coeff / 2 ≤ s ^ (d - 1) * I n := by
      dsimp [coeff, s] at hn hscaled ⊢
      linarith
    have hmult := mul_le_mul_of_nonneg_left hhalfScaled
      (Real.rpow_nonneg hs.le (1 - d))
    have hright : s ^ (1 - d) * (s ^ (d - 1) * I n) = I n := by
      calc
        s ^ (1 - d) * (s ^ (d - 1) * I n) =
            (s ^ (1 - d) * s ^ (d - 1)) * I n := by ring
        _ = I n := by rw [hcancel, one_mul]
    rw [hright] at hmult
    dsimp [s] at hmult
    rw [mul_comm] at hmult
    exact hmult
  intro hsum
  have hbase : Summable (fun n : ℕ =>
      coeff / 2 * ((n + 1 : ℕ) : ℝ) ^ (1 - d)) := by
    apply hsum.of_norm_bounded_eventually_nat
    filter_upwards [heventLower] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (div_nonneg hcoeff.le zero_le_two)
        (Real.rpow_nonneg (by positivity) _))]
    exact hn
  have hcoeffNe : coeff / 2 ≠ 0 := (half_pos hcoeff).ne'
  have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 - d)) :=
    (summable_mul_left_iff hcoeffNe).mp hbase
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (1 - d)) :=
    (summable_nat_add_iff 1).mp hshift
  have hexp := Real.summable_nat_rpow.mp hnat
  linarith

/-- Exact cofinal lower constant for exponential evacuation and polynomial work. -/
theorem polynomialCurrent_action_liminf_lower
    (alpha W I : ℕ → ℝ) (K c d C beta : ℝ)
    (hK : 0 < K) (hc : 0 < c) (hbeta : 0 < beta)
    (halpha : ∀ n, 0 ≤ alpha n)
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ alpha n * W n)
    (hlocal : ∀ lambda, 0 < lambda → lambda < beta → ∀ n,
      lambda * ((n + 1 : ℕ) : ℝ) * alpha n -
        C * Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) ≤ I n) :
    ((c * beta / K : ℝ) : EReal) ≤
      liminf (fun n => ((((n + 1 : ℕ) : ℝ) ^ (d - 1) * I n : ℝ) : EReal)) atTop := by
  let L : EReal :=
    liminf (fun n => ((((n + 1 : ℕ) : ℝ) ^ (d - 1) * I n : ℝ) : EReal)) atTop
  by_contra hbound
  have hLlt : L < ((c * beta / K : ℝ) : EReal) := lt_of_not_ge hbound
  obtain ⟨a, hLa, hatarget⟩ := EReal.exists_between_coe_real hLlt
  have hatargetReal : a < c * beta / K := EReal.coe_lt_coe_iff.mp hatarget
  have haK : a * K < c * beta := by
    calc
      a * K < (c * beta / K) * K := mul_lt_mul_of_pos_right hatargetReal hK
      _ = c * beta := by field_simp
  have hqbeta : a * K / c < beta := (div_lt_iff₀ hc).2 (by simpa [mul_comm] using haK)
  let q : ℝ := max 0 (a * K / c)
  have hqbeta' : q < beta := max_lt hbeta hqbeta
  let lambda : ℝ := (q + beta) / 2
  have hqlambda : q < lambda := by dsimp [lambda]; linarith
  have hlambdabeta : lambda < beta := by dsimp [lambda]; linarith
  have hlambda0 : 0 < lambda := (lt_of_le_of_lt (le_max_left 0 (a * K / c)) hqlambda)
  have hratio : a * K / c < lambda := (le_max_right 0 (a * K / c)).trans_lt hqlambda
  have haKlambda : a * K < lambda * c := (div_lt_iff₀ hc).1 hratio
  have halambda : a < c * lambda / K := (lt_div_iff₀ hK).2 (by
    simpa [mul_comm] using haKlambda)
  have hrate := polynomialCurrent_action_liminf_lower_of_rate
    alpha W I K c d lambda C beta hK hc hlambda0 hlambdabeta halpha hwork hcurrent
      (hlocal lambda hlambda0 hlambdabeta)
  have hrateL : ((c * lambda / K : ℝ) : EReal) ≤ L := hrate
  have haRate : (a : EReal) < ((c * lambda / K : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr halambda
  exact (not_lt_of_ge (haRate.le.trans hrateL) hLa)

/-- CRG.5 for genuinely scale-dependent probability spaces and apertures. -/
theorem exponentialAperture_polynomialCurrent_action_liminf
    {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (mu nu : ∀ n, Measure (Omega n))
    (hmu : ∀ n, IsProbabilityMeasure (mu n))
    (hnu : ∀ n, IsProbabilityMeasure (nu n))
    (A : ∀ n, Set (Omega n)) (hA : ∀ n, MeasurableSet (A n))
    (W : ℕ → ℝ) (C beta K c d : ℝ)
    (hC : 0 < C) (hbeta : 0 < beta) (hK : 0 < K) (hc : 0 < c)
    (hmass : ∀ n, (mu n).real (A n) ≤
      C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)))
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ (nu n).real (A n) * W n)
    (hfin : ∀ n, klDiv (nu n) (mu n) ≠ ⊤) :
    ((c * beta / K : ℝ) : EReal) ≤
      liminf (fun n =>
        (((((n + 1 : ℕ) : ℝ) ^ (d - 1) *
          (klDiv (nu n) (mu n)).toReal : ℝ)) : EReal)) atTop := by
  apply polynomialCurrent_action_liminf_lower
    (fun n => (nu n).real (A n)) W (fun n => (klDiv (nu n) (mu n)).toReal)
    K c d C beta hK hc hbeta (fun n => measureReal_nonneg)
    hwork hcurrent
  intro lambda hlambda hlt n
  letI : IsProbabilityMeasure (mu n) := hmu n
  letI : IsProbabilityMeasure (nu n) := hnu n
  have hlocal := exponentialAperture_localAction_lower
    (mu n) (nu n) (A n) (hA n)
    C (beta * ((n + 1 : ℕ) : ℝ))
    ((beta - lambda) * ((n + 1 : ℕ) : ℝ))
    (lambda * ((n + 1 : ℕ) : ℝ)) hC.le (by ring)
    (by
      simpa [mul_assoc] using hmass n)
    (hfin n)
  have harg : -((beta - lambda) * ((n + 1 : ℕ) : ℝ)) =
      (lambda - beta) * ((n + 1 : ℕ) : ℝ) := by ring
  rw [harg] at hlocal
  simpa [mul_assoc] using hlocal

/-- CRG.6 for genuinely scale-dependent spaces: at or below quadratic work growth, the extended
sum of per-scale relative entropies is exactly infinite.  No finiteness assumption is imposed on
individual coordinates; an infinite coordinate closes the claim immediately. -/
theorem exponentialAperture_polynomialCurrent_action_eq_top_of_degree_le_two
    {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (mu nu : ∀ n, Measure (Omega n))
    (hmu : ∀ n, IsProbabilityMeasure (mu n))
    (hnu : ∀ n, IsProbabilityMeasure (nu n))
    (A : ∀ n, Set (Omega n)) (hA : ∀ n, MeasurableSet (A n))
    (W : ℕ → ℝ) (C beta K c d : ℝ)
    (hC : 0 < C) (hbeta : 0 < beta) (hK : 0 < K) (hc : 0 < c)
    (hmass : ∀ n, (mu n).real (A n) ≤
      C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)))
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ (nu n).real (A n) * W n)
    (hd : d ≤ 2) :
    ∑' n, klDiv (nu n) (mu n) = ⊤ := by
  by_cases hfin : ∀ n, klDiv (nu n) (mu n) ≠ ⊤
  · by_contra hsumTop
    have hsum : Summable (fun n => (klDiv (nu n) (mu n)).toReal) := by
      apply ENNReal.summable_toReal
      simpa using hsumTop
    have hlocal (n : ℕ) :
        (beta / 2) * ((n + 1 : ℕ) : ℝ) * (nu n).real (A n) -
            C * Real.exp (-(beta - beta / 2) * ((n + 1 : ℕ) : ℝ)) ≤
          (klDiv (nu n) (mu n)).toReal := by
      letI : IsProbabilityMeasure (mu n) := hmu n
      letI : IsProbabilityMeasure (nu n) := hnu n
      have hbound := exponentialAperture_localAction_lower
        (mu n) (nu n) (A n) (hA n)
        C (beta * ((n + 1 : ℕ) : ℝ))
        ((beta - beta / 2) * ((n + 1 : ℕ) : ℝ))
        ((beta / 2) * ((n + 1 : ℕ) : ℝ)) hC.le (by ring)
        (by simpa [mul_assoc] using hmass n) (hfin n)
      have harg : -((beta - beta / 2) * ((n + 1 : ℕ) : ℝ)) =
          (beta / 2 - beta) * ((n + 1 : ℕ) : ℝ) := by ring
      rw [harg] at hbound
      simpa [mul_assoc] using hbound
    have hnot := polynomialCurrent_action_not_summable_of_degree_le_two
      (fun n => (nu n).real (A n)) W (fun n => (klDiv (nu n) (mu n)).toReal)
      K c d (beta / 2) C beta hK hc (half_pos hbeta) (half_lt_self hbeta)
      (fun n => measureReal_nonneg) hwork hcurrent hlocal hd
    exact hnot hsum
  · obtain ⟨n, hn⟩ := not_forall.mp hfin
    exact ENNReal.tsum_eq_top_of_eq_top ⟨n, not_ne_iff.mp hn⟩

/-! ## Product action properness -/

/-- Real binary relative-entropy coordinate, continuously extended to both renewed endpoints. -/
noncomputable def binaryRenewalCost (epsilon alpha : unitInterval) : ℝ :=
  -Real.binEntropy (alpha : ℝ) -
    (alpha : ℝ) * Real.log (epsilon : ℝ) -
    (1 - (alpha : ℝ)) * Real.log (1 - (epsilon : ℝ))

theorem continuous_binaryRenewalCost_right (epsilon : unitInterval) :
    Continuous (binaryRenewalCost epsilon) := by
  unfold binaryRenewalCost
  fun_prop

theorem binaryRenewalCost_eq_klDiv
    (epsilon alpha : unitInterval)
    (hepsilon0 : 0 < (epsilon : ℝ)) (hepsilon1 : (epsilon : ℝ) < 1)
    (halpha0 : 0 < (alpha : ℝ)) (halpha1 : (alpha : ℝ) < 1) :
    binaryRenewalCost epsilon alpha =
      (klDiv Ber(true, false, alpha) Ber(true, false, epsilon)).toReal := by
  rw [toReal_klDiv_bernoulli alpha epsilon halpha0 halpha1 hepsilon0 hepsilon1]
  unfold binaryRenewalCost Real.binEntropy
  rw [Real.log_div halpha0.ne' hepsilon0.ne',
    Real.log_div (sub_pos.mpr halpha1).ne' (sub_pos.mpr hepsilon1).ne']
  simp only [Real.log_inv]
  ring

/-- Gibbs variational lower bound for the exact binary KL coordinate, including renewed endpoint
`alpha = 1`. -/
theorem binaryRenewalCost_tilt_lower
    (epsilon alpha : unitInterval) (t : ℝ)
    (hepsilon0 : 0 < (epsilon : ℝ)) (hepsilon1 : (epsilon : ℝ) < 1)
    (halpha0 : 0 < (alpha : ℝ)) :
    t * (alpha : ℝ) - Real.log (1 + Real.exp t * (epsilon : ℝ)) ≤
      binaryRenewalCost epsilon alpha := by
  by_cases halpha1 : (alpha : ℝ) < 1
  · have hfin := klDiv_bernoulli_ne_top alpha epsilon
      halpha0 halpha1 hepsilon0 hepsilon1
    have h := aperturePotential_entropy_lower_one_add
      Ber(true, false, epsilon) Ber(true, false, alpha)
      ({true} : Set Bool) (measurableSet_singleton true) t hfin
    have hrenewed : Ber(true, false, alpha).real ({true} : Set Bool) = (alpha : ℝ) := by
      simp
    have hbaseline : Ber(true, false, epsilon).real ({true} : Set Bool) = (epsilon : ℝ) := by
      simp
    rw [hrenewed, hbaseline] at h
    rwa [binaryRenewalCost_eq_klDiv epsilon alpha hepsilon0 hepsilon1 halpha0 halpha1]
  · have halphaLe : (alpha : ℝ) ≤ 1 := alpha.property.2
    have halphaEqReal : (alpha : ℝ) = 1 := le_antisymm halphaLe (le_of_not_gt halpha1)
    have halphaEq : alpha = 1 := Subtype.ext halphaEqReal
    subst alpha
    have hx : 0 < Real.exp t * (epsilon : ℝ) :=
      mul_pos (Real.exp_pos t) hepsilon0
    have hxle : Real.exp t * (epsilon : ℝ) ≤ 1 + Real.exp t * (epsilon : ℝ) := by
      linarith
    have hlog := Real.log_le_log hx hxle
    rw [Real.log_mul (Real.exp_ne_zero t) hepsilon0.ne', Real.log_exp] at hlog
    simp [binaryRenewalCost]
    linarith

/-- Exponential evacuation specialized to the exact binary renewal coordinate. -/
theorem binaryRenewalCost_exponential_lower
    (epsilon alpha : unitInterval) (C beta delta t : ℝ)
    (hepsilon0 : 0 < (epsilon : ℝ)) (hepsilon1 : (epsilon : ℝ) < 1)
    (halpha0 : 0 < (alpha : ℝ))
    (hdelta : delta = beta - t)
    (hmass : (epsilon : ℝ) ≤ C * Real.exp (-beta)) :
    t * (alpha : ℝ) - C * Real.exp (-delta) ≤ binaryRenewalCost epsilon alpha := by
  have hbase := binaryRenewalCost_tilt_lower epsilon alpha t
    hepsilon0 hepsilon1 halpha0
  have hmassScaled : Real.exp t * (epsilon : ℝ) ≤ C * Real.exp (-delta) := by
    calc
      Real.exp t * (epsilon : ℝ) ≤ Real.exp t * (C * Real.exp (-beta)) :=
        mul_le_mul_of_nonneg_left hmass (Real.exp_pos t).le
      _ = C * (Real.exp t * Real.exp (-beta)) := by ring
      _ = C * Real.exp (-delta) := by
        rw [← Real.exp_add]
        have harg : t + -beta = -delta := by linarith
        rw [harg]
  have harg0 : 0 < 1 + Real.exp t * (epsilon : ℝ) := by positivity
  have hlogmajor : Real.log (1 + Real.exp t * (epsilon : ℝ)) ≤
      C * Real.exp (-delta) := by
    calc
      Real.log (1 + Real.exp t * (epsilon : ℝ)) ≤ Real.exp t * (epsilon : ℝ) := by
        have := Real.log_le_sub_one_of_pos harg0
        linarith
      _ ≤ C * Real.exp (-delta) := hmassScaled
  linarith

theorem binaryRenewalCost_nonneg
    (epsilon alpha : unitInterval)
    (hepsilon0 : 0 < (epsilon : ℝ)) (hepsilon1 : (epsilon : ℝ) < 1) :
    0 ≤ binaryRenewalCost epsilon alpha := by
  by_cases halpha0 : (alpha : ℝ) = 0
  · have hcomp0 : 0 ≤ 1 - (epsilon : ℝ) := (sub_pos.mpr hepsilon1).le
    have hcomp1 : 1 - (epsilon : ℝ) ≤ 1 := by linarith
    have hlog := Real.log_nonpos hcomp0 hcomp1
    simp [binaryRenewalCost, halpha0]
    linarith
  by_cases halpha1 : (alpha : ℝ) = 1
  · have hlog := Real.log_nonpos hepsilon0.le epsilon.property.2
    simp [binaryRenewalCost, halpha1]
    linarith
  · have halphaPos : 0 < (alpha : ℝ) := lt_of_le_of_ne alpha.property.1 (Ne.symm halpha0)
    have halphaLt : (alpha : ℝ) < 1 := lt_of_le_of_ne alpha.property.2 halpha1
    rw [binaryRenewalCost_eq_klDiv epsilon alpha hepsilon0 hepsilon1 halphaPos halphaLt]
    exact ENNReal.toReal_nonneg

/-- Minimal product-history action from the exact binary KL coordinates. -/
noncomputable def binaryRenewalAction
    (epsilon : ℕ → unitInterval) (alpha : ℕ → unitInterval) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (binaryRenewalCost (epsilon n) (alpha n))

theorem lowerSemicontinuous_binaryRenewalAction (epsilon : ℕ → unitInterval) :
    LowerSemicontinuous (binaryRenewalAction epsilon) := by
  apply lowerSemicontinuous_tsum
  intro n
  exact (ENNReal.continuous_ofReal.comp
    ((continuous_binaryRenewalCost_right (epsilon n)).comp (continuous_apply n))).lowerSemicontinuous

def binaryRenewalActionSublevel
    (epsilon : ℕ → unitInterval) (M : ℝ≥0∞) : Set (ℕ → unitInterval) :=
  {alpha | binaryRenewalAction epsilon alpha ≤ M}

theorem isClosed_binaryRenewalActionSublevel
    (epsilon : ℕ → unitInterval) (M : ℝ≥0∞) :
    IsClosed (binaryRenewalActionSublevel epsilon M) := by
  change IsClosed (binaryRenewalAction epsilon ⁻¹' Iic M)
  exact (lowerSemicontinuous_binaryRenewalAction epsilon).isClosed_preimage M

theorem isCompact_binaryRenewalActionSublevel
    (epsilon : ℕ → unitInterval) (M : ℝ≥0∞) :
    IsCompact (binaryRenewalActionSublevel epsilon M) :=
  (isClosed_binaryRenewalActionSublevel epsilon M).isCompact

def persistentCurrentLocus (W : ℕ → ℝ) (c : ℝ) : Set (ℕ → unitInterval) :=
  {alpha | ∀ n, c ≤ (alpha n : ℝ) * W n}

theorem persistentCurrentLocus_eq_iInter (W : ℕ → ℝ) (c : ℝ) :
    persistentCurrentLocus W c =
      ⋂ n, {alpha : ℕ → unitInterval | c ≤ (alpha n : ℝ) * W n} := by
  ext alpha
  simp [persistentCurrentLocus]

theorem isClosed_persistentCurrentLocus (W : ℕ → ℝ) (c : ℝ) :
    IsClosed (persistentCurrentLocus W c) := by
  rw [persistentCurrentLocus_eq_iInter]
  apply isClosed_iInter
  intro n
  have hcoord : Continuous (fun alpha : ℕ → unitInterval => (alpha n : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply n)
  exact isClosed_Ici.preimage (hcoord.mul continuous_const)

theorem isCompact_binaryRenewalActionSublevel_inter_persistentCurrentLocus
    (epsilon : ℕ → unitInterval) (W : ℕ → ℝ) (c : ℝ) (M : ℝ≥0∞) :
    IsCompact (binaryRenewalActionSublevel epsilon M ∩ persistentCurrentLocus W c) :=
  (isCompact_binaryRenewalActionSublevel epsilon M).inter_right
    (isClosed_persistentCurrentLocus W c)

/-- At degree at most two, every persistent-current binary schedule has infinite total action. -/
theorem binaryRenewalAction_eq_top_of_degree_le_two
    (epsilon alpha : ℕ → unitInterval) (W : ℕ → ℝ)
    (C beta K c d : ℝ)
    (hbeta : 0 < beta) (hK : 0 < K) (hc : 0 < c)
    (hepsilon0 : ∀ n, 0 < (epsilon n : ℝ))
    (hepsilon1 : ∀ n, (epsilon n : ℝ) < 1)
    (hmass : ∀ n, (epsilon n : ℝ) ≤
      C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)))
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ (alpha n : ℝ) * W n)
    (hd : d ≤ 2) :
    binaryRenewalAction epsilon alpha = ⊤ := by
  have halpha0 (n : ℕ) : 0 < (alpha n : ℝ) := by
    have hnonneg := (alpha n).property.1
    by_contra hnot
    have hz : (alpha n : ℝ) = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
    have hc0 := hcurrent n
    rw [hz, zero_mul] at hc0
    exact (not_lt_of_ge hc0 hc)
  by_contra htop
  have hsumOfReal : Summable (fun n =>
      (ENNReal.ofReal (binaryRenewalCost (epsilon n) (alpha n))).toReal) := by
    apply ENNReal.summable_toReal
    simpa [binaryRenewalAction] using htop
  have hsum : Summable (fun n => binaryRenewalCost (epsilon n) (alpha n)) := by
    apply hsumOfReal.congr
    intro n
    exact ENNReal.toReal_ofReal
      (binaryRenewalCost_nonneg (epsilon n) (alpha n) (hepsilon0 n) (hepsilon1 n))
  have hlocal (n : ℕ) :
      (beta / 2) * ((n + 1 : ℕ) : ℝ) * (alpha n : ℝ) -
        C * Real.exp (-(beta - beta / 2) * ((n + 1 : ℕ) : ℝ)) ≤
      binaryRenewalCost (epsilon n) (alpha n) := by
    have h := binaryRenewalCost_exponential_lower
      (epsilon n) (alpha n) C
      (beta * ((n + 1 : ℕ) : ℝ))
      ((beta - beta / 2) * ((n + 1 : ℕ) : ℝ))
      ((beta / 2) * ((n + 1 : ℕ) : ℝ))
      (hepsilon0 n) (hepsilon1 n) (halpha0 n)
      (by ring) (by
        have hm := hmass n
        have hneg : -beta * ((n + 1 : ℕ) : ℝ) =
            -(beta * ((n + 1 : ℕ) : ℝ)) := by ring
        rw [hneg] at hm
        exact hm)
    have harg : -((beta - beta / 2) * ((n + 1 : ℕ) : ℝ)) =
        (beta / 2 - beta) * ((n + 1 : ℕ) : ℝ) := by ring
    rw [harg] at h
    simpa [mul_assoc] using h
  have hnotSummable := polynomialCurrent_action_not_summable_of_degree_le_two
    (fun n => (alpha n : ℝ)) W
    (fun n => binaryRenewalCost (epsilon n) (alpha n))
    K c d (beta / 2) C beta hK hc (half_pos hbeta) (half_lt_self hbeta)
    (fun n => (alpha n).property.1) hwork hcurrent hlocal hd
  exact hnotSummable hsum

theorem binaryRenewalActionSublevel_inter_persistentCurrentLocus_eq_empty
    (epsilon : ℕ → unitInterval) (W : ℕ → ℝ)
    (C beta K c d : ℝ) (M : ℝ≥0∞)
    (hM : M ≠ ⊤)
    (hbeta : 0 < beta) (hK : 0 < K) (hc : 0 < c)
    (hepsilon0 : ∀ n, 0 < (epsilon n : ℝ))
    (hepsilon1 : ∀ n, (epsilon n : ℝ) < 1)
    (hmass : ∀ n, (epsilon n : ℝ) ≤
      C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)))
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hd : d ≤ 2) :
    binaryRenewalActionSublevel epsilon M ∩ persistentCurrentLocus W c = ∅ := by
  apply Set.Subset.antisymm
  · intro alpha halpha
    exfalso
    have htop := binaryRenewalAction_eq_top_of_degree_le_two
      epsilon alpha W C beta K c d hbeta hK hc hepsilon0 hepsilon1 hmass hwork
        halpha.2 hd
    have hle := halpha.1
    rw [binaryRenewalActionSublevel, Set.mem_setOf_eq, htop] at hle
    exact hM (top_le_iff.mp hle)
  · exact Set.empty_subset _

section Disintegration

variable [StandardBorelSpace X] [Nonempty X]

/-- Exact aperture disintegration: binary information plus nonnegative conditional information. -/
theorem aperture_klDiv_eq_binary_add_cond
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : Set X) (hA : MeasurableSet A) :
    klDiv nu mu =
      klDiv Ber(true, false, apertureProbability nu A)
        Ber(true, false, apertureProbability mu A) +
      klDiv
        ((jointLaw nu (apertureIndicator A)).fst ⊗ₘ
          (jointLaw nu (apertureIndicator A)).condKernel)
        ((jointLaw nu (apertureIndicator A)).fst ⊗ₘ
          (jointLaw mu (apertureIndicator A)).condKernel) := by
  rw [klDiv_eq_map_add_cond nu mu (measurable_apertureIndicator hA),
    map_apertureIndicator_eq_bernoulli nu A hA,
    map_apertureIndicator_eq_bernoulli mu A hA]

/-- Equality in the binary lower bound holds exactly when the two conditional aperture laws agree. -/
theorem aperture_binary_klDiv_eq_iff
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : Set X) (hA : MeasurableSet A) (hfin : klDiv nu mu ≠ ⊤) :
    klDiv Ber(true, false, apertureProbability nu A)
        Ber(true, false, apertureProbability mu A) = klDiv nu mu ↔
      (jointLaw nu (apertureIndicator A)).fst ⊗ₘ
          (jointLaw nu (apertureIndicator A)).condKernel =
        (jointLaw nu (apertureIndicator A)).fst ⊗ₘ
          (jointLaw mu (apertureIndicator A)).condKernel := by
  have hmapfin :
      klDiv (nu.map (apertureIndicator A)) (mu.map (apertureIndicator A)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hfin
      (klDiv_map_le nu mu (measurable_apertureIndicator hA))
  simpa [map_apertureIndicator_eq_bernoulli nu A hA,
    map_apertureIndicator_eq_bernoulli mu A hA] using
      (klDiv_map_eq_iff nu mu (measurable_apertureIndicator hA) hmapfin)

end Disintegration

end

end GaloisForLFunctions.HTGeometry

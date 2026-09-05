import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolBaseNuclearSynthesis

/-!
# Pole Hankel form versus the Euler source on the radial carrier

On the common radial carrier `L²((0,∞), dL)` every real-rate object of the theta/Xi lane is a
Hankel form: its quadratic form on `h` is `∫ |F_h(u)|² dν(u)`, where
`F_h(u) = ∫ L e^{-uL} h(L) dL` is the real-rate conormal report of `h` and `ν` is a measure on
rates.  The literal all-prime Burnol source is the Hankel form of the Euler rate measure
`∑ Λ(n)/n · δ_{log n}`; the Euler pole `s = 1` is the Hankel form of Lebesgue measure `du`, the
Carleman form.  The prime-density explicit formula identifies the anomaly-subtracted divisor side
of the same object with `pole − source`.

This module proves that the pole form does not dominate the source form.  An explicit carrier
vector — a polynomial–exponential spike concentrated at rate `log 2` — has Carleman energy strictly
smaller than the single `p = 2` atom of its Euler source energy, hence strictly smaller than the
full source quadratic form.  The anomaly-subtracted divisor side is therefore an indefinite Hankel
form on the carrier; it cannot be a positive, sub-unit, source-factored covariance.

The mechanism is Carleman's: point evaluation of a half-line Laplace transform at an interior rate
is unbounded relative to the ray `L²` norm, while the Euler source is a positive sum of exactly
such point evaluations.

No zero, divisor copy, ordinate, or RH hypothesis enters any statement.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

local instance radialCarrierFactTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) :=
  ⟨by norm_num⟩

local instance : MeasurableSpace RoutePPrimitiveIndex := ⊤

/-! ## Real-rate report and Carleman energy -/

/-- Real-rate conormal report of a carrier function: its pairing against `L ↦ L e^{-uL}`. -/
def radialRateReport (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ L : ℝ in Ioi 0, ((L : ℂ) * Complex.exp (-((u : ℂ) * (L : ℂ)))) * h L

/-- Carleman (Euler-pole) Hankel energy: the ray `L²` energy of the real-rate report. -/
def poleHankelEnergy (h : ℝ → ℂ) : ℝ :=
  ∫ u : ℝ in Ioi 0, ‖radialRateReport h u‖ ^ 2

/-! ## Monomial Laplace integrals -/

private theorem integrableOn_pow_mul_exp_neg_mul_Ioi' {r : ℝ} (hr : 0 < r) (j : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ j * Real.exp (-(r * t))) (Ioi (0:ℝ)) := by
  have hG : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1)) (Ioi (0:ℝ)) :=
    Real.GammaIntegral_convergent (by positivity)
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1)) 0 hr).mpr (by simpa using hG)
  have hc : IntegrableOn
      (fun x : ℝ => (r ^ j)⁻¹ * (Real.exp (-(r * x)) * (r * x) ^ (((j : ℝ) + 1) - 1)))
      (Ioi (0:ℝ)) := hscale.const_mul _
  refine MeasureTheory.IntegrableOn.congr_fun hc ?_ measurableSet_Ioi
  intro x hx
  have hx0 : (0:ℝ) < x := hx
  have hrj : (r : ℝ) ^ j ≠ 0 := by positivity
  have hexp : ((r * x) : ℝ) ^ (((j : ℝ) + 1) - 1) = r ^ j * x ^ j := by
    rw [show ((j : ℝ) + 1) - 1 = (j : ℝ) by ring, Real.rpow_natCast, mul_pow]
  simp only [hexp]
  field_simp

private theorem integral_pow_mul_exp_neg_mul_Ioi' {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ∫ t in Ioi (0:ℝ), t ^ j * Real.exp (-(r * t)) = (j.factorial : ℝ) / r ^ (j + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j : ℝ) + 1) (r := r)
    (by positivity) hr
  rw [Real.Gamma_nat_eq_factorial] at h
  have hcongr : ∫ t in Ioi (0:ℝ), t ^ (((j : ℝ) + 1) - 1) * Real.exp (-(r * t))
      = ∫ t in Ioi (0:ℝ), t ^ j * Real.exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show ((j : ℝ) + 1) - 1 = (j : ℝ) by ring, Real.rpow_natCast]
  rw [hcongr] at h
  rw [h, one_div, Real.inv_rpow hr.le, show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  field_simp

/-! ## The spike vector -/

/-- Polynomial--exponential spike seed concentrated at the real rate `u₀`. -/
def radialSpikeSeed (u₀ : ℝ) (n : ℕ) (L : ℝ) : ℝ :=
  (4 * u₀) ^ n * Real.exp (-(u₀ * L)) *
    ∑ j ∈ Finset.range (n + 1),
      ((n.choose j : ℝ) * (-u₀) ^ (n - j) / ((2 * n - j).factorial : ℝ)) * L ^ (2 * n - j - 1)

/-- The spike as a complex carrier function. -/
def radialSpike (u₀ : ℝ) (n : ℕ) (L : ℝ) : ℂ := (radialSpikeSeed u₀ n L : ℂ)

theorem continuous_radialSpikeSeed (u₀ : ℝ) (n : ℕ) : Continuous (radialSpikeSeed u₀ n) := by
  unfold radialSpikeSeed
  fun_prop

theorem continuous_radialSpike (u₀ : ℝ) (n : ℕ) : Continuous (radialSpike u₀ n) :=
  Complex.continuous_ofReal.comp (continuous_radialSpikeSeed u₀ n)

theorem radialSpikeSeed_report_integrand (u₀ u : ℝ) {n : ℕ} (hn : 1 ≤ n) (L : ℝ) :
    L * Real.exp (-(u * L)) * radialSpikeSeed u₀ n L =
      (4 * u₀) ^ n * ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) * (-u₀) ^ (n - j) / ((2 * n - j).factorial : ℝ)) *
          (L ^ (2 * n - j) * Real.exp (-((u + u₀) * L))) := by
  unfold radialSpikeSeed
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < n + 1 := Finset.mem_range.mp hj
  have hpow : L ^ (2 * n - j) = L ^ (2 * n - j - 1) * L := by
    rw [← pow_succ]
    congr 1
    omega
  have hexp : Real.exp (-((u + u₀) * L)) = Real.exp (-(u * L)) * Real.exp (-(u₀ * L)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hpow, hexp]
  ring

/-- Exact real-rate report of the spike: a Landau-type kernel in the rate variable. -/
theorem radialRateReport_radialSpike {u₀ u : ℝ} (hu₀ : 0 < u₀) (hu : 0 < u) {n : ℕ}
    (hn : 1 ≤ n) :
    radialRateReport (radialSpike u₀ n) u =
      (((4 * u * u₀) ^ n / (u + u₀) ^ (2 * n + 1) : ℝ) : ℂ) := by
  have hc : 0 < u + u₀ := by linarith
  have hreal : ∀ L : ℝ,
      ((L : ℂ) * Complex.exp (-((u : ℂ) * (L : ℂ)))) * radialSpike u₀ n L =
        ((L * Real.exp (-(u * L)) * radialSpikeSeed u₀ n L : ℝ) : ℂ) := by
    intro L
    simp only [radialSpike, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
  unfold radialRateReport
  rw [setIntegral_congr_fun measurableSet_Ioi (fun L _ => hreal L), integral_complex_ofReal]
  congr 1
  calc (∫ L in Ioi (0:ℝ), L * Real.exp (-(u * L)) * radialSpikeSeed u₀ n L)
      = ∫ L in Ioi (0:ℝ), (4 * u₀) ^ n * ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℝ) * (-u₀) ^ (n - j) / ((2 * n - j).factorial : ℝ)) *
            (L ^ (2 * n - j) * Real.exp (-((u + u₀) * L))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro L _
        exact radialSpikeSeed_report_integrand u₀ u hn L
    _ = (4 * u₀) ^ n * ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℝ) * (-u₀) ^ (n - j) / ((2 * n - j).factorial : ℝ)) *
            (((2 * n - j).factorial : ℝ) / (u + u₀) ^ (2 * n - j + 1)) := by
        rw [integral_const_mul, integral_finsetSum]
        · congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi' hc]
        · intro j _
          exact (integrableOn_pow_mul_exp_neg_mul_Ioi' hc _).const_mul _
    _ = (4 * u * u₀) ^ n / (u + u₀) ^ (2 * n + 1) := by
        have hu' : u = (u + u₀) + (-u₀) := by ring
        have hun : u ^ n =
            ∑ j ∈ Finset.range (n + 1), (u + u₀) ^ j * (-u₀) ^ (n - j) * (n.choose j : ℝ) := by
          conv_lhs => rw [hu']
          exact add_pow _ _ _
        rw [show (4 * u * u₀) ^ n = (4 * u₀) ^ n * u ^ n by ring, hun]
        simp only [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < n + 1 := Finset.mem_range.mp hj
        have hfac : ((2 * n - j).factorial : ℝ) ≠ 0 := by positivity
        have hpow : (u + u₀) ^ (2 * n + 1) = (u + u₀) ^ (2 * n - j + 1) * (u + u₀) ^ j := by
          rw [← pow_add]
          congr 1
          omega
        rw [hpow]
        field_simp

/-- At its own rate the spike report is exactly `1/(2u₀)`. -/
theorem radialRateReport_radialSpike_self {u₀ : ℝ} (hu₀ : 0 < u₀) {n : ℕ} (hn : 1 ≤ n) :
    radialRateReport (radialSpike u₀ n) u₀ = ((1 / (2 * u₀) : ℝ) : ℂ) := by
  rw [radialRateReport_radialSpike hu₀ hu₀ hn]
  congr 1
  have h2 : (4 * u₀ * u₀) ^ n = (2 * u₀) ^ (2 * n) := by
    rw [pow_mul]
    congr 1
    ring
  rw [show u₀ + u₀ = 2 * u₀ by ring, h2, pow_succ]
  field_simp

/-! ## Carleman energy of the spike -/

theorem radialSpike_energy_pointwise {u₀ u δ : ℝ} (hu₀ : 0 < u₀) (hu : 0 < u)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ) :
    ((4 * u * u₀) ^ n / (u + u₀) ^ (2 * n + 1)) ^ 2 ≤
      (1 - δ ^ 2) ^ (2 * n) * (1 / (u + u₀) ^ 2) +
        (Ioo (u₀ * (1 - δ) / (1 + δ)) (u₀ * (1 + δ) / (1 - δ))).indicator
          (fun _ => 1 / u₀ ^ 2) u := by
  have hc : 0 < u + u₀ := by linarith
  have hδ2 : 0 ≤ 1 - δ ^ 2 := by nlinarith
  set q : ℝ := 4 * u * u₀ / (u + u₀) ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q = 1 - ((u - u₀) / (u + u₀)) ^ 2 := by
    rw [hq]
    field_simp
    ring
  have hlhs : ((4 * u * u₀) ^ n / (u + u₀) ^ (2 * n + 1)) ^ 2 = q ^ (2 * n) * (1 / (u + u₀) ^ 2) := by
    have e1 : ((u + u₀) ^ 2) ^ (2 * n) = (u + u₀) ^ (2 * (2 * n)) := by rw [← pow_mul]
    have e2 : ((u + u₀) ^ (2 * n + 1)) ^ 2 = (u + u₀) ^ (2 * (2 * n)) * (u + u₀) ^ 2 := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    have e3 : ((4 * u * u₀) ^ n) ^ 2 = (4 * u * u₀) ^ (2 * n) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [hq, div_pow, div_pow, e1, e2, e3]
    field_simp
  rw [hlhs]
  have hind : 0 ≤ (Ioo (u₀ * (1 - δ) / (1 + δ)) (u₀ * (1 + δ) / (1 - δ))).indicator
      (fun _ : ℝ => 1 / u₀ ^ 2) u :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  by_cases hfar : δ ^ 2 ≤ ((u - u₀) / (u + u₀)) ^ 2
  · have hqle : q ≤ 1 - δ ^ 2 := by rw [hq1]; linarith
    have hpow : q ^ (2 * n) ≤ (1 - δ ^ 2) ^ (2 * n) := pow_le_pow_left₀ hq0 hqle _
    calc q ^ (2 * n) * (1 / (u + u₀) ^ 2) ≤ (1 - δ ^ 2) ^ (2 * n) * (1 / (u + u₀) ^ 2) := by
          gcongr
      _ ≤ _ := le_add_of_nonneg_right hind
  · rw [not_le] at hfar
    have habs : |(u - u₀) / (u + u₀)| < δ := abs_lt_of_sq_lt_sq hfar hδ0.le
    rw [abs_lt] at habs
    obtain ⟨h1, h2⟩ := habs
    rw [lt_div_iff₀ hc] at h1
    rw [div_lt_iff₀ hc] at h2
    have hmem : u ∈ Ioo (u₀ * (1 - δ) / (1 + δ)) (u₀ * (1 + δ) / (1 - δ)) := by
      constructor
      · rw [div_lt_iff₀ (by linarith)]
        nlinarith
      · rw [lt_div_iff₀ (by linarith)]
        nlinarith
    rw [Set.indicator_of_mem hmem]
    have hq1' : q ≤ 1 := by
      rw [hq1]
      nlinarith [sq_nonneg ((u - u₀) / (u + u₀))]
    have hpow : q ^ (2 * n) ≤ 1 := pow_le_one₀ hq0 hq1'
    have hfirst : 0 ≤ (1 - δ ^ 2) ^ (2 * n) * (1 / (u + u₀) ^ 2) := by positivity
    calc q ^ (2 * n) * (1 / (u + u₀) ^ 2) ≤ 1 * (1 / (u + u₀) ^ 2) := by gcongr
      _ ≤ 1 / u₀ ^ 2 := by
          rw [one_mul]
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
      _ ≤ _ := le_add_of_nonneg_left hfirst

/-- The shifted inverse square has ray integral `1/u₀` and is integrable. -/
theorem integral_Ioi_one_div_add_sq {u₀ : ℝ} (hu₀ : 0 < u₀) :
    (∫ u in Ioi (0:ℝ), 1 / (u + u₀) ^ 2) = 1 / u₀ ∧
      IntegrableOn (fun u : ℝ => 1 / (u + u₀) ^ 2) (Ioi 0) := by
  have hderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun u : ℝ => -(u + u₀)⁻¹) (1 / (x + u₀) ^ 2) x := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    have hne : x + u₀ ≠ 0 := by positivity
    have h := (((hasDerivAt_id x).add_const u₀).inv hne).neg
    exact h.congr_deriv (by simp [id_eq, neg_div])
  have hcont : ContinuousWithinAt (fun u : ℝ => -(u + u₀)⁻¹) (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.neg
    exact ContinuousAt.inv₀ (continuousAt_id.add continuousAt_const) (by simp [hu₀.ne'])
  have hnn : ∀ x ∈ Ioi (0:ℝ), 0 ≤ 1 / (x + u₀) ^ 2 := fun x _ => by positivity
  have htend : Tendsto (fun u : ℝ => -(u + u₀)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right atTop u₀ tendsto_id)).neg
    simpa using h
  refine ⟨?_, integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn htend⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn htend]
  simp

/-- Carleman energy budget of the spike: a rate-window plus a Landau tail. -/
theorem poleHankelEnergy_radialSpike_le {u₀ δ : ℝ} (hu₀ : 0 < u₀) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    poleHankelEnergy (radialSpike u₀ n) ≤
      ((1 - δ ^ 2) ^ (2 * n) + 4 * δ / (1 - δ ^ 2)) / u₀ := by
  have hδ2 : 0 < 1 - δ ^ 2 := by nlinarith
  obtain ⟨hint, hintg⟩ := integral_Ioi_one_div_add_sq hu₀
  set a : ℝ := u₀ * (1 - δ) / (1 + δ) with ha
  set b : ℝ := u₀ * (1 + δ) / (1 - δ) with hb
  have hne1 : (1 : ℝ) - δ ≠ 0 := by linarith
  have hne2 : (1 : ℝ) + δ ≠ 0 := by linarith
  have hne3 : (1 : ℝ) - δ ^ 2 ≠ 0 := hδ2.ne'
  have hab : b - a = u₀ * (4 * δ / (1 - δ ^ 2)) := by
    rw [ha, hb]
    field_simp
    ring
  have hab' : a ≤ b := by
    have : 0 ≤ b - a := by rw [hab]; positivity
    linarith
  have hcongr : poleHankelEnergy (radialSpike u₀ n) =
      ∫ u in Ioi (0:ℝ), ((4 * u * u₀) ^ n / (u + u₀) ^ (2 * n + 1)) ^ 2 := by
    unfold poleHankelEnergy
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [radialRateReport_radialSpike hu₀ hu hn, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hcongr]
  have hind_int : Integrable ((Ioo a b).indicator (fun _ : ℝ => 1 / u₀ ^ 2))
      (volume.restrict (Ioi 0)) := by
    have h1 : IntegrableOn (fun _ : ℝ => 1 / u₀ ^ 2) (Ioo a b) (volume.restrict (Ioi 0)) := by
      refine integrableOn_const ?_ enorm_ne_top
      rw [Measure.restrict_apply measurableSet_Ioo]
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_left) measure_Ioo_lt_top)
    exact h1.integrable_indicator measurableSet_Ioo
  have hg_int : IntegrableOn (fun u : ℝ => (1 - δ ^ 2) ^ (2 * n) * (1 / (u + u₀) ^ 2) +
      (Ioo a b).indicator (fun _ : ℝ => 1 / u₀ ^ 2) u) (Ioi 0) :=
    (hintg.const_mul _).add hind_int
  have hf_meas : AEStronglyMeasurable
      (fun u : ℝ => ((4 * u * u₀) ^ n / (u + u₀) ^ (2 * n + 1)) ^ 2)
      (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hf_int : IntegrableOn
      (fun u : ℝ => ((4 * u * u₀) ^ n / (u + u₀) ^ (2 * n + 1)) ^ 2) (Ioi 0) := by
    refine hg_int.mono' hf_meas ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact radialSpike_energy_pointwise hu₀ hu hδ0 hδ1 n
  calc (∫ u in Ioi (0:ℝ), ((4 * u * u₀) ^ n / (u + u₀) ^ (2 * n + 1)) ^ 2)
      ≤ ∫ u in Ioi (0:ℝ), ((1 - δ ^ 2) ^ (2 * n) * (1 / (u + u₀) ^ 2) +
          (Ioo a b).indicator (fun _ : ℝ => 1 / u₀ ^ 2) u) :=
        setIntegral_mono_on hf_int hg_int measurableSet_Ioi
          (fun u hu => radialSpike_energy_pointwise hu₀ hu hδ0 hδ1 n)
    _ = (1 - δ ^ 2) ^ (2 * n) * (1 / u₀) +
          ∫ u in Ioi (0:ℝ), (Ioo a b).indicator (fun _ : ℝ => 1 / u₀ ^ 2) u := by
        rw [integral_add (hintg.const_mul _) hind_int, integral_const_mul, hint]
    _ ≤ (1 - δ ^ 2) ^ (2 * n) * (1 / u₀) + (4 * δ / (1 - δ ^ 2)) / u₀ := by
        gcongr
        rw [setIntegral_indicator measurableSet_Ioo, setIntegral_const, smul_eq_mul]
        have hmeas : volume.real (Ioi (0:ℝ) ∩ Ioo a b) ≤ b - a := by
          calc volume.real (Ioi (0:ℝ) ∩ Ioo a b) ≤ volume.real (Ioo a b) :=
                measureReal_mono inter_subset_right measure_Ioo_lt_top.ne
            _ = b - a := by
                rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
        calc volume.real (Ioi (0:ℝ) ∩ Ioo a b) * (1 / u₀ ^ 2) ≤ (b - a) * (1 / u₀ ^ 2) := by
              gcongr
          _ = (4 * δ / (1 - δ ^ 2)) / u₀ := by
              rw [hab]
              field_simp
    _ = _ := by ring

/-! ## The explicit sub-unit budget -/

/-- At `δ = 1/64`, `n = 6144` the Carleman budget is below the single `p = 2` atom `1/8`. -/
theorem radialSpike_budget_lt :
    (1 - (1 / 64 : ℝ) ^ 2) ^ (2 * 6144) + 4 * (1 / 64) / (1 - (1 / 64 : ℝ) ^ 2) < 1 / 8 := by
  have h1 : (1 - (1 / 64 : ℝ) ^ 2) ^ (2 * 6144) ≤ Real.exp (-3) := by
    have hb : 1 - (1 / 64 : ℝ) ^ 2 ≤ Real.exp (-(1 / 64 : ℝ) ^ 2) := by
      have := Real.add_one_le_exp (-(1 / 64 : ℝ) ^ 2)
      linarith
    calc (1 - (1 / 64 : ℝ) ^ 2) ^ (2 * 6144)
        ≤ (Real.exp (-(1 / 64 : ℝ) ^ 2)) ^ (2 * 6144) :=
          pow_le_pow_left₀ (by norm_num) hb _
      _ = Real.exp (-3) := by
          rw [← Real.exp_nat_mul]
          norm_num
  have h2 : Real.exp (-3) < 1 / 20 := by
    have he : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hgt : (20 : ℝ) < Real.exp 3 := by
      rw [he]
      have h := Real.exp_one_gt_d9
      have h3 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
        pow_lt_pow_left₀ h (by norm_num) (by norm_num)
      norm_num at h3
      linarith
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    exact hgt
  have h3 : (4 : ℝ) * (1 / 64) / (1 - (1 / 64 : ℝ) ^ 2) = 256 / 4095 := by norm_num
  rw [h3]
  have h4 : (1 - (1 / 64 : ℝ) ^ 2) ^ (2 * 6144) < 1 / 20 := lt_of_le_of_lt h1 h2
  generalize (1 - (1 / 64 : ℝ) ^ 2) ^ (2 * 6144) = X at h4 ⊢
  have h5 : (1 / 20 : ℝ) + 256 / 4095 < 1 / 8 := by norm_num
  linarith

/-- **Carleman defeat of the pole form.**  On the spike at rate `log 2`, the Euler-pole Hankel
energy is strictly smaller than the single `p = 2` Euler atom of the source energy. -/
theorem poleHankelEnergy_radialSpike_lt_eulerAtom :
    poleHankelEnergy (radialSpike (Real.log 2) 6144) <
      (Real.log 2 / 2) *
        ‖radialRateReport (radialSpike (Real.log 2) 6144) (Real.log 2)‖ ^ 2 := by
  have hu₀ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle := poleHankelEnergy_radialSpike_le hu₀ (δ := 1 / 64) (by norm_num) (by norm_num)
    (n := 6144) (by norm_num)
  rw [radialRateReport_radialSpike_self hu₀ (by norm_num), Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  have hrhs : Real.log 2 / 2 * (1 / (2 * Real.log 2)) ^ 2 = (1 / 8) / Real.log 2 := by
    field_simp
    ring
  rw [hrhs]
  calc poleHankelEnergy (radialSpike (Real.log 2) 6144)
      ≤ ((1 - (1 / 64 : ℝ) ^ 2) ^ (2 * 6144) + 4 * (1 / 64) / (1 - (1 / 64 : ℝ) ^ 2)) /
          Real.log 2 := hle
    _ < (1 / 8) / Real.log 2 := by
        exact div_lt_div_of_pos_right radialSpike_budget_lt hu₀

/-! ## The spike as a carrier vector -/

/-- The squared spike is integrable on the ray: it is a finite sum of exponential monomials. -/
theorem radialSpike_sq_integrableOn {u₀ : ℝ} (hu₀ : 0 < u₀) (n : ℕ) :
    IntegrableOn (fun L : ℝ => ‖radialSpike u₀ n L‖ ^ 2) (Ioi 0) := by
  have h2 : 0 < 2 * u₀ := by linarith
  set c : ℕ → ℝ := fun j => (n.choose j : ℝ) * (-u₀) ^ (n - j) / ((2 * n - j).factorial : ℝ)
    with hc
  have hpt : ∀ L : ℝ, ‖radialSpike u₀ n L‖ ^ 2 =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        (((4 * u₀) ^ n) ^ 2 * (c j * c k)) *
          (L ^ ((2 * n - j - 1) + (2 * n - k - 1)) * Real.exp (-((2 * u₀) * L))) := by
    intro L
    have hE : Real.exp (-(u₀ * L)) ^ 2 = Real.exp (-((2 * u₀) * L)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    calc ‖radialSpike u₀ n L‖ ^ 2 = (radialSpikeSeed u₀ n L) ^ 2 := by
          rw [radialSpike, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ = ((4 * u₀) ^ n) ^ 2 * Real.exp (-(u₀ * L)) ^ 2 *
            ((∑ j ∈ Finset.range (n + 1), c j * L ^ (2 * n - j - 1)) *
              (∑ k ∈ Finset.range (n + 1), c k * L ^ (2 * n - k - 1))) := by
          rw [radialSpikeSeed]
          ring
      _ = _ := by
          rw [hE, Finset.sum_mul_sum]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          rw [pow_add]
          ring
  have hint : Integrable (fun L : ℝ =>
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        (((4 * u₀) ^ n) ^ 2 * (c j * c k)) *
          (L ^ ((2 * n - j - 1) + (2 * n - k - 1)) * Real.exp (-((2 * u₀) * L))))
      (volume.restrict (Ioi 0)) := by
    refine integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => ?_))
    exact (integrableOn_pow_mul_exp_neg_mul_Ioi' h2 _).const_mul _
  exact (IntegrableOn.congr_fun hint (fun L _ => (hpt L).symm) measurableSet_Ioi)

/-- The spike as an element of the common radial carrier. -/
def radialSpikeLp {u₀ : ℝ} (hu₀ : 0 < u₀) (n : ℕ) : routePBurnolHalfLineL2 :=
  routePBurnolHalfLineL2Of (radialSpike u₀ n) (continuous_radialSpike u₀ n)
    (radialSpike_sq_integrableOn hu₀ n)

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- The spike at rate `log 2`, order `6144`, as a carrier vector. -/
def radialSpikeLogTwo : routePBurnolHalfLineL2 := radialSpikeLp log_two_pos' 6144

/-! ## The `p = 2` Euler column -/

/-- The prime-depth index of the literal `p = 2`, depth-one Euler cell. -/
def primeTwoIndex : RoutePPrimitiveIndex := (⟨2, Nat.prime_two⟩, 0)

theorem routePPrimitiveBurnolWindowFeature_primeTwo (L : ℝ) :
    routePPrimitiveBurnolWindowFeature primeTwoIndex 0 L =
      ((Real.sqrt (Real.log 2 / 2) * (L * Real.exp (-(Real.log 2 * L))) : ℝ) : ℂ) := by
  have hval : xiGammaEulerValuationNat primeTwoIndex = 2 := by
    simp [xiGammaEulerValuationNat, primeTwoIndex]
  have hamp : finiteVonMangoldtDepthOneAmplitude 2 = (Real.sqrt (Real.log 2 / 2) : ℂ) := by
    rw [finiteVonMangoldtDepthOneAmplitude, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hfreq : xiGammaEulerPrimitiveLogFrequency primeTwoIndex = Real.log 2 := by
    rw [xiGammaEulerPrimitiveLogFrequency, hval]
    norm_num
  rw [routePPrimitiveBurnolWindowFeature, hval, hamp, xiWardCubicBurnolWindowConormalFeature,
    burnolCoPoissonCenteredConormalCharacter, routePPrimitiveBurnolSpectralPoint, hfreq]
  have hchar : (L : ℂ) * ((((1 / 2 + Real.log 2 : ℝ)) : ℂ) + I * ((0 : ℝ) : ℂ) - 1 / 2) =
      ((Real.log 2 * L : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hchar, ← Complex.ofReal_exp, ← Complex.ofReal_inv, ← Real.exp_neg]
  push_cast
  ring

/-- The `p = 2` Euler column pairs with the spike through its real-rate report at `log 2`. -/
theorem inner_baseField_primeTwo_radialSpikeLp (n : ℕ) :
    inner ℂ (routePPrimitiveBurnolBaseField primeTwoIndex) (radialSpikeLp log_two_pos' n) =
      (Real.sqrt (Real.log 2 / 2) : ℂ) *
        radialRateReport (radialSpike (Real.log 2) n) (Real.log 2) := by
  rw [routePPrimitiveBurnolBaseField, routePPrimitiveBurnolWindowFeatureLp, radialSpikeLp,
    routePBurnolHalfLineL2Of, routePBurnolHalfLineL2Of,
    inner_toLp_routePBurnolHalfLine_eq_pairing, routePBurnolHalfLinePairing, radialRateReport,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro L _
  dsimp only
  rw [routePPrimitiveBurnolWindowFeature_primeTwo, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-! ## Covariance lower bound from one column -/

theorem forall_eq_of_ae_count {α β : Type*} [MeasurableSpace α] {f g : α → β}
    (h : f =ᵐ[(Measure.count : Measure α)] g) : ∀ x, f x = g x := by
  intro x
  by_contra hx
  have hset : (Measure.count : Measure α) {y | ¬ f y = g y} = 0 := ae_iff.mp h
  rw [Measure.count_eq_zero_iff] at hset
  exact (Set.eq_empty_iff_forall_notMem.mp hset x) hx

/-- The Euler source quadratic form dominates the squared overlap with any one of its columns. -/
theorem norm_sq_inner_baseField_le_re_inner_baseNuclearSource
    (pe : RoutePPrimitiveIndex) (h : routePBurnolHalfLineL2) :
    ‖inner ℂ (routePPrimitiveBurnolBaseField pe) h‖ ^ 2 ≤
      (inner ℂ h (routePPrimitiveBurnolBaseNuclearSource h)).re := by
  set g := ContinuousLinearMap.adjoint routePPrimitiveBurnolBaseSynthesis h with hg
  have h1 : inner ℂ h (routePPrimitiveBurnolBaseNuclearSource h) = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [routePPrimitiveBurnolBaseNuclearSource, rangeCovariance, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K, hg]
    push_cast
    rfl
  rw [h1, Complex.ofReal_re, HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  have hgfun : g = l2ObserverAnalysis Measure.count routePPrimitiveBurnolBaseFieldLp h := by
    rw [hg, routePPrimitiveBurnolBaseSynthesis, adjoint_l2Synthesis]
  have hae : (g : RoutePPrimitiveIndex → ℂ) =ᵐ[(Measure.count : Measure RoutePPrimitiveIndex)]
      fun x => inner ℂ (routePPrimitiveBurnolBaseFieldLp x) h := by
    rw [hgfun]
    exact l2ObserverAnalysis_coeFn _ _ _
  have hfield : (routePPrimitiveBurnolBaseFieldLp : RoutePPrimitiveIndex → routePBurnolHalfLineL2)
      =ᵐ[(Measure.count : Measure RoutePPrimitiveIndex)] routePPrimitiveBurnolBaseField :=
    memLp_two_routePPrimitiveBurnolBaseField.coeFn_toLp
  have hpt : ∀ x, (g : RoutePPrimitiveIndex → ℂ) x = inner ℂ (routePPrimitiveBurnolBaseField x) h := by
    apply forall_eq_of_ae_count
    filter_upwards [hae, hfield] with x hx hx'
    rw [hx, hx']
  have hint : Integrable (fun x => ‖(g : RoutePPrimitiveIndex → ℂ) x‖ ^ 2)
      (Measure.count : Measure RoutePPrimitiveIndex) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).mp (Lp.memLp g)
  calc ‖inner ℂ (routePPrimitiveBurnolBaseField pe) h‖ ^ 2
      = ∫ x in ({pe} : Set RoutePPrimitiveIndex), ‖(g : RoutePPrimitiveIndex → ℂ) x‖ ^ 2
          ∂(Measure.count : Measure RoutePPrimitiveIndex) := by
        rw [integral_singleton, measureReal_def, Measure.count_singleton, ENNReal.toReal_one,
          one_smul, hpt]
    _ ≤ ∫ x, ‖(g : RoutePPrimitiveIndex → ℂ) x‖ ^ 2
          ∂(Measure.count : Measure RoutePPrimitiveIndex) :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall (fun x => by positivity))

/-! ## Main theorem -/

/-- **The pole form does not dominate the Euler source.**  On the explicit spike carrier vector,
the Carleman (Euler-pole) Hankel energy is strictly smaller than the literal all-prime Burnol
source quadratic form.  Hence `pole − source`, the anomaly-subtracted divisor side of the
prime-density explicit formula on the radial carrier, is an indefinite Hankel form. -/
theorem poleHankelEnergy_radialSpike_lt_re_inner_baseNuclearSource :
    poleHankelEnergy (radialSpike (Real.log 2) 6144) <
      (inner ℂ radialSpikeLogTwo
        (routePPrimitiveBurnolBaseNuclearSource radialSpikeLogTwo)).re := by
  calc poleHankelEnergy (radialSpike (Real.log 2) 6144)
      < (Real.log 2 / 2) *
          ‖radialRateReport (radialSpike (Real.log 2) 6144) (Real.log 2)‖ ^ 2 :=
        poleHankelEnergy_radialSpike_lt_eulerAtom
    _ = ‖inner ℂ (routePPrimitiveBurnolBaseField primeTwoIndex) radialSpikeLogTwo‖ ^ 2 := by
        rw [radialSpikeLogTwo, inner_baseField_primeTwo_radialSpikeLp, norm_mul, mul_pow,
          Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
          Real.sq_sqrt (by positivity)]
    _ ≤ _ := norm_sq_inner_baseField_le_re_inner_baseNuclearSource _ _

/-! ## The Euler source is the Hankel operator of `-ζ'/ζ` -/

/-- One Euler column at two radial points: the resolved von Mangoldt term of the log-derivative
Dirichlet series at `s = 1 + L₁ + L₂`, times `L₁ L₂`. -/
theorem routePPrimitiveBurnolWindowFeature_mul_eq_term (pe : RoutePPrimitiveIndex) (L₁ L₂ : ℝ) :
    routePPrimitiveBurnolWindowFeature pe 0 L₁ * routePPrimitiveBurnolWindowFeature pe 0 L₂ =
      ((L₁ * L₂ : ℝ) : ℂ) *
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (1 + ((L₁ + L₂ : ℝ) : ℂ)) (xiGammaEulerValuationNat pe) := by
  set n := xiGammaEulerValuationNat pe with hn
  have hn0 : n ≠ 0 := by
    rw [hn, xiGammaEulerValuationNat]
    exact pow_ne_zero _ pe.1.property.ne_zero
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  rw [LSeries.term_of_ne_zero hn0]
  simp only [routePPrimitiveBurnolWindowFeature, xiWardCubicBurnolWindowConormalFeature,
    burnolCoPoissonCenteredConormalCharacter, routePPrimitiveBurnolSpectralPoint,
    xiGammaEulerPrimitiveLogFrequency, ← hn]
  have hchar : ∀ L : ℝ,
      (L : ℂ) * ((((1 / 2 + Real.log (n : ℝ) : ℝ)) : ℂ) + I * ((0 : ℝ) : ℂ) - 1 / 2) =
        (L : ℂ) * Complex.log (n : ℂ) := by
    intro L
    push_cast
    ring
  simp only [hchar]
  have hamp : finiteVonMangoldtDepthOneAmplitude n * finiteVonMangoldtDepthOneAmplitude n =
      (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) := by
    rw [← sq, finiteVonMangoldtDepthOneAmplitude_sq hn0, finiteVonMangoldtWeight,
      LSeries.term_of_ne_zero hn0, Complex.cpow_one]
  have hexp : (Complex.exp ((L₁ : ℂ) * Complex.log (n : ℂ)))⁻¹ *
      (Complex.exp ((L₂ : ℂ) * Complex.log (n : ℂ)))⁻¹ =
        ((n : ℂ) ^ ((L₁ + L₂ : ℝ) : ℂ))⁻¹ := by
    rw [Complex.cpow_def_of_ne_zero hnC, ← mul_inv, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hpow : (n : ℂ) ^ ((L₁ + L₂ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnC]
    exact Complex.exp_ne_zero _
  calc finiteVonMangoldtDepthOneAmplitude n *
          ((L₁ : ℂ) * (Complex.exp ((L₁ : ℂ) * Complex.log (n : ℂ)))⁻¹) *
        (finiteVonMangoldtDepthOneAmplitude n *
          ((L₂ : ℂ) * (Complex.exp ((L₂ : ℂ) * Complex.log (n : ℂ)))⁻¹))
      = (finiteVonMangoldtDepthOneAmplitude n * finiteVonMangoldtDepthOneAmplitude n) *
          (((L₁ : ℂ) * (L₂ : ℂ)) *
            ((Complex.exp ((L₁ : ℂ) * Complex.log (n : ℂ)))⁻¹ *
              (Complex.exp ((L₂ : ℂ) * Complex.log (n : ℂ)))⁻¹)) := by ring
    _ = _ := by
        rw [hamp, hexp, Complex.cpow_add _ _ hnC, Complex.cpow_one]
        push_cast
        field_simp

/-- **The Euler source is the Hankel operator of `−ζ'/ζ`.**  Summed over every prime-depth cell,
the kernel of the literal all-prime Burnol columns at real radial points `L₁, L₂ > 0` is
`−L₁ L₂ · (ζ'/ζ)(1 + L₁ + L₂)`: a Hankel kernel whose rate measure is `∑ Λ(n)/n · δ_{log n}`. -/
theorem tsum_routePPrimitiveBurnolWindowFeature_mul_eq_neg_logDeriv_zeta
    {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    ∑' pe : RoutePPrimitiveIndex,
      routePPrimitiveBurnolWindowFeature pe 0 L₁ * routePPrimitiveBurnolWindowFeature pe 0 L₂ =
        -((L₁ * L₂ : ℝ) : ℂ) * (deriv riemannZeta (1 + ((L₁ + L₂ : ℝ) : ℂ)) /
          riemannZeta (1 + ((L₁ + L₂ : ℝ) : ℂ))) := by
  set s : ℂ := 1 + ((L₁ + L₂ : ℝ) : ℂ) with hs
  have hsre : 1 < s.re := by
    rw [hs]
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hterm : ∀ pe : RoutePPrimitiveIndex,
      routePPrimitiveBurnolWindowFeature pe 0 L₁ * routePPrimitiveBurnolWindowFeature pe 0 L₂ =
        ((L₁ * L₂ : ℝ) : ℂ) * LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s
          (xiGammaEulerValuationNat pe) :=
    fun pe => routePPrimitiveBurnolWindowFeature_mul_eq_term pe L₁ L₂
  rw [tsum_congr hterm, tsum_mul_left]
  have hsupp : Function.support
      (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s) ⊆
        {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hcon
    apply hn
    have hz : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hcon
    by_cases hn0 : n = 0
    · rw [hn0]
      exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero hn0, hz]
      simp
  have hre : ∑' pe : RoutePPrimitiveIndex,
      LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s
        (xiGammaEulerValuationNat pe) =
      LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s := by
    rw [LSeries]
    calc ∑' pe : RoutePPrimitiveIndex,
          LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s
            (xiGammaEulerValuationNat pe)
        = ∑' x : {n : ℕ // IsPrimePow n},
            LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s (x : ℕ) := by
          rw [← Nat.Primes.prodNatEquiv.tsum_eq (fun x : {n : ℕ // IsPrimePow n} =>
            LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s (x : ℕ))]
          apply tsum_congr
          rintro ⟨p, k⟩
          rfl
      _ = _ := tsum_subtype_eq_of_support_subset hsupp
  rw [hre, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hsre]
  ring

end

end RHTower

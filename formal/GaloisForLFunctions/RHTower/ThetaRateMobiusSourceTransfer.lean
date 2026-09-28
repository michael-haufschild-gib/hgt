import GaloisForLFunctions.RHTower.ThetaRateLaplaceBernstein
import GaloisForLFunctions.RHTower.ThetaAllSieveSeedProjector
import GaloisForLFunctions.RHTower.CausalMobiusThetaMovingCusp

/-!
# Source-level Möbius reconstruction of the all-sieve theta rate cone

Let `f` be a continuous source with finite normalized tail flux
`b_f(t) = t^{-3/2} ∫_{[log t/2, ∞)} e^{x/2} f`.  Suppose `b_f` and every finite-prime-deleted flux
`b_{D_S f}` are completely monotone, and the positive Bernstein measure `ν` of `b_f` has a positive
rate gap or a finite negative moment `M_q(ν)`, `q > 3/2`.

* Bernstein–Widder and Laplace order turn the deletion tests into positivity of every rate
  deletion `D_S ν`; the measure-level classification gives a unique positive seed `ξ` with
  `ν = Σ_n A_n ξ`.
* **Representation (7).**  `f(x) = ∫ k(x+s) dη(s)` for the literal completed theta source `k`, with
  `η` obtained from `(2π e^{5s/2})⁻¹ dξ(λ)` under `λ = π e^{2s}`, and `η` is the unique positive
  translation measure representing `f`.  The mixture is pointwise finite and continuous: the right
  Gaussian tail of `k` dominates every polynomial in `λ`, and evenness of `k` gives a left Gaussian
  tail dominating the weight `e^{-5s/2}`.  Tonelli identifies its flux with `L_ν`, and the flux
  determines a continuous source.
* In the rate-gap case `η` vanishes below `log(λ₀/π)/2`.
* **Charge rigidity.**  If `f` also has the ordinary mass and both reflected half-density charges of
  `k`, then `η = δ₀` and `f = k`; for even `f` the positive half-charge suffices.
* The literal theta rate measure `2π Σ n² δ_{πn²}` is the Bernstein measure of `b_k`; it has the gap
  `π` and `M_q = 2π π^{-q} Σ n^{2-2q} < ∞` for `q > 3/2`.
-/
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Gaussian tails of the completed theta source -/

theorem exp_mul_sub_exp_le {D c : ℝ} (hD : 0 ≤ D) (hc : 0 < c) (y : ℝ) :
    Real.exp (D * y - c * Real.exp (2 * y)) ≤ Real.exp (D ^ 2 / (8 * c)) := by
  rw [Real.exp_le_exp]
  rcases le_or_gt 0 y with hy | hy
  · have h := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * y)
    have h2 : 2 * y ^ 2 ≤ Real.exp (2 * y) := by nlinarith
    have h3 : D * y - c * (2 * y ^ 2) ≤ D ^ 2 / (8 * c) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (4 * c * y - D)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
  · have h1 : D * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD hy.le
    have h2 : 0 ≤ c * Real.exp (2 * y) := by positivity
    have h3 : 0 ≤ D ^ 2 / (8 * c) := by positivity
    linarith

/-- The right tail: `k(y) ≤ C e^{-(π/2) e^{2y}}` for `y ≥ 0`. -/
theorem exists_thetaCuspFullSource_le_halfGaussian :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y →
      thetaCuspFullSource y ≤ C * Real.exp (-(Real.pi / 2) * Real.exp (2 * y)) := by
  obtain ⟨C, D, hC, hD, h⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le_gaussian 0
  refine ⟨C * Real.exp (D ^ 2 / (8 * (Real.pi / 2))), mul_nonneg hC (Real.exp_pos _).le,
    fun y hy => ?_⟩
  have h1 := h y hy
  rw [iteratedDeriv_zero] at h1
  have heq : C * Real.exp (D * y) * Real.exp (-Real.pi * Real.exp (2 * y)) =
      C * Real.exp (D * y - Real.pi / 2 * Real.exp (2 * y)) *
        Real.exp (-(Real.pi / 2) * Real.exp (2 * y)) := by
    rw [mul_assoc C, mul_assoc C, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  calc thetaCuspFullSource y ≤ |thetaCuspFullSource y| := le_abs_self _
    _ ≤ _ := h1
    _ = _ := heq
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (exp_mul_sub_exp_le (c := Real.pi / 2) hD (by positivity) y) hC) (Real.exp_pos _).le

/-! ## Rate seeds and translation measures -/

/-- The inverse seed weight `(2π e^{5s/2})⁻¹`. -/
def thetaRateWeight (s : ℝ) : ℝ := (2 * Real.pi * Real.exp (5 * s / 2))⁻¹

theorem thetaRateWeight_pos (s : ℝ) : 0 < thetaRateWeight s := by
  unfold thetaRateWeight; positivity

theorem continuous_thetaRateWeight : Continuous thetaRateWeight := by
  unfold thetaRateWeight
  exact (by fun_prop : Continuous fun s : ℝ => 2 * Real.pi * Real.exp (5 * s / 2)).inv₀
    fun s => by positivity

/-- The rate seed of a translation measure `η`: the push-forward of `2π e^{5s/2} dη(s)` under the
rate map `s ↦ π e^{2s}`. -/
def thetaRateSeed (η : Measure ℝ) : Measure ℝ :=
  (η.withDensity fun s => ENNReal.ofReal (2 * Real.pi * Real.exp (5 * s / 2))).map thetaSeedRate

/-- The translation measure of a rate seed `ξ`: `(2π e^{5s/2})⁻¹` times the pull-back of `ξ` under
`s ↦ π e^{2s}`, i.e. the push-forward of `(2π (λ/π)^{5/4})⁻¹ dξ(λ)` under `λ ↦ log(λ/π)/2`. -/
def thetaRateTranslation (ξ : Measure ℝ) : Measure ℝ :=
  (ξ.comap thetaSeedRate).withDensity fun s => ENNReal.ofReal (thetaRateWeight s)

theorem range_thetaSeedRate : range thetaSeedRate = Ioi 0 := by
  ext r
  constructor
  · rintro ⟨s, rfl⟩
    exact mem_Ioi.mpr (by unfold thetaSeedRate; positivity)
  · intro hr
    refine ⟨Real.log (r / Real.pi) / 2, ?_⟩
    unfold thetaSeedRate
    rw [show 2 * (Real.log (r / Real.pi) / 2) = Real.log (r / Real.pi) by ring,
      Real.exp_log (div_pos hr Real.pi_pos)]
    field_simp

theorem measurable_seedDensity :
    Measurable fun s : ℝ => ENNReal.ofReal (2 * Real.pi * Real.exp (5 * s / 2)) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

theorem measurable_rateWeightDensity : Measurable fun s : ℝ => ENNReal.ofReal (thetaRateWeight s) :=
  ENNReal.measurable_ofReal.comp continuous_thetaRateWeight.measurable

theorem seedDensity_mul_rateWeight :
    ((fun s : ℝ => ENNReal.ofReal (2 * Real.pi * Real.exp (5 * s / 2))) *
      fun s => ENNReal.ofReal (thetaRateWeight s)) = 1 := by
  funext s
  simp only [Pi.mul_apply, Pi.one_apply]
  rw [← ENNReal.ofReal_mul (by positivity), thetaRateWeight,
    mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem thetaRateSeed_thetaRateTranslation {ξ : Measure ℝ} (hξ : ξ (Iic 0) = 0) :
    thetaRateSeed (thetaRateTranslation ξ) = ξ := by
  unfold thetaRateSeed thetaRateTranslation
  rw [← withDensity_mul _ measurable_rateWeightDensity measurable_seedDensity, mul_comm,
    seedDensity_mul_rateWeight, withDensity_one, measurableEmbedding_thetaSeedRate.map_comap,
    range_thetaSeedRate]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  refine measure_mono_null (fun l hl => ?_) hξ
  simp only [mem_setOf_eq, mem_Ioi, not_lt] at hl
  exact hl

theorem thetaRateTranslation_thetaRateSeed (η : Measure ℝ) :
    thetaRateTranslation (thetaRateSeed η) = η := by
  unfold thetaRateSeed thetaRateTranslation
  rw [measurableEmbedding_thetaSeedRate.comap_map,
    ← withDensity_mul _ measurable_seedDensity measurable_rateWeightDensity,
    seedDensity_mul_rateWeight, withDensity_one]

/-- The logarithmic coordinate `λ ↦ log(λ/π)/2`, inverse to the rate map on `(0, ∞)`. -/
def thetaSeedLog (l : ℝ) : ℝ := Real.log (l / Real.pi) / 2

theorem measurable_thetaSeedLog : Measurable thetaSeedLog :=
  (Real.measurable_log.comp (measurable_id.div_const _)).div_const _

theorem thetaSeedLog_thetaSeedRate (s : ℝ) : thetaSeedLog (thetaSeedRate s) = s := by
  unfold thetaSeedLog thetaSeedRate
  rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, Real.log_exp]
  ring

/-- The translation measure is the push-forward of `(2π e^{5s/2})⁻¹ dξ(λ)` under `λ ↦ log(λ/π)/2`,
`s = log(λ/π)/2`. -/
theorem thetaRateTranslation_eq_map {ξ : Measure ℝ} (hξ : ξ (Iic 0) = 0) :
    thetaRateTranslation ξ = (ξ.withDensity fun l =>
      ENNReal.ofReal (thetaRateWeight (thetaSeedLog l))).map thetaSeedLog := by
  ext E hE
  rw [Measure.map_apply measurable_thetaSeedLog hE, withDensity_apply _ (measurable_thetaSeedLog hE),
    thetaRateTranslation, withDensity_apply _ hE, ← lintegral_indicator hE,
    ← lintegral_indicator (measurable_thetaSeedLog hE)]
  have hcomp : ∀ s, E.indicator (fun s => ENNReal.ofReal (thetaRateWeight s)) s =
      (thetaSeedLog ⁻¹' E).indicator (fun l => ENNReal.ofReal (thetaRateWeight (thetaSeedLog l)))
        (thetaSeedRate s) := fun s => by
    by_cases h : s ∈ E
    · rw [indicator_of_mem h, indicator_of_mem (show thetaSeedRate s ∈ thetaSeedLog ⁻¹' E by
        rw [mem_preimage, thetaSeedLog_thetaSeedRate]; exact h), thetaSeedLog_thetaSeedRate]
    · rw [indicator_of_notMem h, indicator_of_notMem (show thetaSeedRate s ∉ thetaSeedLog ⁻¹' E by
        rw [mem_preimage, thetaSeedLog_thetaSeedRate]; exact h)]
  simp_rw [hcomp]
  rw [← measurableEmbedding_thetaSeedRate.lintegral_map, measurableEmbedding_thetaSeedRate.map_comap,
    range_thetaSeedRate, Measure.restrict_eq_self_of_ae_mem]
  rw [ae_iff]
  refine measure_mono_null (fun l hl => ?_) hξ
  simp only [mem_setOf_eq, mem_Ioi, not_lt] at hl
  exact hl

theorem thetaRateSeed_compl_Ici (η : Measure ℝ) : thetaRateSeed η (Ici 0)ᶜ = 0 := by
  unfold thetaRateSeed
  rw [measurableEmbedding_thetaSeedRate.map_apply]
  have : thetaSeedRate ⁻¹' (Ici 0)ᶜ = ∅ := by
    ext s
    simp only [mem_preimage, mem_compl_iff, mem_Ici, not_le, mem_empty_iff_false, iff_false,
      not_lt]
    unfold thetaSeedRate
    positivity
  rw [this, measure_empty]

theorem rateLaplace_thetaRateSeed (η : Measure ℝ) (u : ℝ) :
    rateLaplace (thetaRateSeed η) u = ∫⁻ s, ENNReal.ofReal (2 * Real.pi * Real.exp (5 * s / 2) *
      Real.exp (-(u * thetaSeedRate s))) ∂η := by
  unfold rateLaplace thetaRateSeed
  rw [measurableEmbedding_thetaSeedRate.lintegral_map,
    lintegral_withDensity_eq_lintegral_mul _ measurable_seedDensity
      (show Measurable fun a => ENNReal.ofReal (Real.exp (-(u * thetaSeedRate a))) from
        ENNReal.measurable_ofReal.comp (by unfold thetaSeedRate; fun_prop))]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (by positivity)]

theorem rateLaplace_rateEuler (ξ : Measure ℝ) (t : ℝ) :
    rateLaplace (rateEuler ξ) t = ∑' m : ℕ, (m : ℝ≥0∞) ^ 2 * rateLaplace ξ ((m : ℝ) ^ 2 * t) := by
  rw [rateEuler_eq_sum, rateLaplace, lintegral_sum_measure]
  exact tsum_congr fun m => by rw [← rateLaplace, rateLaplace_rateDilate]

/-! ## The flux of a positive translation mixture -/

/-- **Tonelli flux law.**  For every s-finite positive translation measure `η`,
`∫_{x > X} e^{x/2} ∫ k(x+s) dη(s) dx = e^{3X} L_{Σ_n A_n ξ}(e^{2X})` with `ξ` the rate seed of `η`. -/
theorem lintegral_Ioi_thetaMixture (η : Measure ℝ) [SFinite η] (X : ℝ) :
    ∫⁻ x in Ioi X, ∫⁻ s, ENNReal.ofReal (Real.exp (x / 2) * thetaCuspFullSource (x + s)) ∂η =
      ENNReal.ofReal (Real.exp (3 * X)) *
        rateLaplace (rateEuler (thetaRateSeed η)) (Real.exp (2 * X)) := by
  set F : ℝ → ℕ → ℝ≥0∞ := fun s m => ENNReal.ofReal (Real.exp (3 * X) *
    (2 * Real.pi * Real.exp (5 * s / 2)) * ((m : ℝ) ^ 2 *
      Real.exp (-Real.pi * (m : ℝ) ^ 2 * (Real.exp (2 * s) * Real.exp (2 * X)))))
  have hFm : ∀ m, Measurable fun s => F s m := fun m =>
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hmeas : Measurable (Function.uncurry fun x s =>
      ENNReal.ofReal (Real.exp (x / 2) * thetaCuspFullSource (x + s))) :=
    ENNReal.measurable_ofReal.comp (Continuous.measurable (by
      have := continuous_thetaCuspFullSource
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (p.1 / 2) * thetaCuspFullSource (p.1 + p.2))))
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hinner : ∀ s, ∫⁻ x in Ioi X, ENNReal.ofReal (Real.exp (x / 2) *
      thetaCuspFullSource (x + s)) = ∑' m, F s m := by
    intro s
    have hint := (thetaFluxSource_thetaCuspFullSource.comp_add s).2 X
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x =>
      mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_nonneg _))]
    have hI : (∫ x in Ioi X, Real.exp (x / 2) * thetaCuspFullSource (x + s)) =
        Real.exp (3 * X) * thetaNormalizedFlux (fun x => thetaCuspFullSource (x + s))
          (Real.exp (2 * X)) := by
      rw [thetaNormalizedFlux_exp, ← mul_assoc, ← Real.exp_add]
      simp
    have hsum := summable_pow_mul_exp_neg_nat_sq 2
      (mul_pos Real.pi_pos (mul_pos (Real.exp_pos (2 * s)) (Real.exp_pos (2 * X))))
    rw [hI, thetaNormalizedFlux_comp_add _ _ (Real.exp_pos _),
      thetaNormalizedFlux_thetaCuspFullSource (by positivity), ← tsum_mul_left, ← tsum_mul_left,
      ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity)]
    · refine tsum_congr fun m => ?_
      simp only [F]
      congr 1
      ring
    · refine (((hsum.mul_left (2 * Real.pi)).mul_left (Real.exp (5 * s / 2))).mul_left
        (Real.exp (3 * X))).congr fun m => ?_
      ring_nf
  simp_rw [hinner]
  rw [lintegral_tsum fun m => (hFm m).aemeasurable, rateLaplace_rateEuler, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [rateLaplace_thetaRateSeed,
    ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.natCast_ne_top m)),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun s => ?_
  simp only [F]
  rw [show ((m : ℝ≥0∞) ^ 2) = ENNReal.ofReal ((m : ℝ) ^ 2) by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold thetaSeedRate
  ring_nf

/-! ## Local finiteness of translation measures with a pointwise finite mixture -/

theorem isFiniteMeasureOnCompacts_of_lintegral_thetaCuspFullSource {η : Measure ℝ}
    (h : ∫⁻ s, ENNReal.ofReal (thetaCuspFullSource s) ∂η ≠ ∞) : IsFiniteMeasureOnCompacts η := by
  refine ⟨fun C hC => ?_⟩
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨y, hy, hmin⟩ := hC.exists_isMinOn hne continuous_thetaCuspFullSource.continuousOn
  have hK : ENNReal.ofReal (thetaCuspFullSource y) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (thetaCuspFullSource_pos_all y)).ne'
  have hle : ENNReal.ofReal (thetaCuspFullSource y) * η C ≤
      ∫⁻ s, ENNReal.ofReal (thetaCuspFullSource s) ∂η := by
    calc ENNReal.ofReal (thetaCuspFullSource y) * η C =
          ∫⁻ _ in C, ENNReal.ofReal (thetaCuspFullSource y) ∂η := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ s in C, ENNReal.ofReal (thetaCuspFullSource s) ∂η :=
          setLIntegral_mono (ENNReal.measurable_ofReal.comp continuous_thetaCuspFullSource.measurable)
            fun _ hs => ENNReal.ofReal_le_ofReal (hmin hs)
      _ ≤ _ := setLIntegral_le_lintegral _ _
  refine lt_top_iff_ne_top.2 fun htop => h (top_le_iff.1 ?_)
  rw [htop, ENNReal.mul_top hK] at hle
  exact hle

theorem sigmaFinite_of_integrable_thetaCuspFullSource {η : Measure ℝ}
    (h : Integrable (fun s => thetaCuspFullSource (0 + s)) η) : SigmaFinite η := by
  have h0 := h.lintegral_lt_top
  simp only [zero_add] at h0
  haveI := isFiniteMeasureOnCompacts_of_lintegral_thetaCuspFullSource h0.ne
  infer_instance

/-- **Flux of a positive translation mixture.**  If `s ↦ k(x+s)` is `η`-integrable for every `x`,
then `∫_{x > X} e^{x/2} (∫ k(x+s) dη(s)) dx = e^{3X} L_{Σ_n A_n ξ}(e^{2X})` with `ξ` the rate
seed of `η`. -/
theorem lintegral_Ioi_thetaMeasureGauge {η : Measure ℝ}
    (hint : ∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) η) (X : ℝ) :
    ∫⁻ x in Ioi X, ENNReal.ofReal (Real.exp (x / 2) * thetaMeasureGauge η thetaCuspFullSource x) =
      ENNReal.ofReal (Real.exp (3 * X)) *
        rateLaplace (rateEuler (thetaRateSeed η)) (Real.exp (2 * X)) := by
  haveI := sigmaFinite_of_integrable_thetaCuspFullSource (hint 0)
  rw [← lintegral_Ioi_thetaMixture η X]
  refine lintegral_congr fun x => ?_
  unfold thetaMeasureGauge
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal ((hint x).const_mul _)
    (ae_of_all _ fun s => mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_nonneg _))]

theorem thetaMeasureGauge_nonneg (η : Measure ℝ) (x : ℝ) :
    0 ≤ thetaMeasureGauge η thetaCuspFullSource x :=
  integral_nonneg fun _ => thetaCuspFullSource_nonneg _

/-! ## Domination of the rate kernel -/

theorem thetaRateWeight_eq (s : ℝ) :
    thetaRateWeight s = Real.exp (-(5 * s / 2)) / (2 * Real.pi) := by
  unfold thetaRateWeight
  rw [Real.exp_neg]
  ring

/-- Right tail of the rate kernel, uniformly for `x ≥ a`. -/
theorem thetaRateWeight_mul_le_right {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ y : ℝ, 0 ≤ y →
      thetaCuspFullSource y ≤ C₁ * Real.exp (-(Real.pi / 2) * Real.exp (2 * y)))
    {a x s : ℝ} (hax : a ≤ x) (hs : -a ≤ s) :
    thetaRateWeight s * thetaCuspFullSource (x + s) ≤
      C₁ * Real.exp (5 * a / 2) / (2 * Real.pi) *
        Real.exp (-(Real.exp (2 * a) / 2 * thetaSeedRate s)) := by
  have hw : thetaRateWeight s ≤ Real.exp (5 * a / 2) / (2 * Real.pi) := by
    rw [thetaRateWeight_eq]
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (by positivity)
  have hK : thetaCuspFullSource (x + s) ≤
      C₁ * Real.exp (-(Real.exp (2 * a) / 2 * thetaSeedRate s)) := by
    refine (hC₁ (x + s) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁0)
    unfold thetaSeedRate
    have h : Real.exp (2 * a) * Real.exp (2 * s) ≤ Real.exp (2 * (x + s)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    nlinarith [Real.pi_pos]
  calc thetaRateWeight s * thetaCuspFullSource (x + s) ≤
        Real.exp (5 * a / 2) / (2 * Real.pi) *
          (C₁ * Real.exp (-(Real.exp (2 * a) / 2 * thetaSeedRate s))) :=
        mul_le_mul hw hK (thetaCuspFullSource_nonneg _) (by positivity)
    _ = _ := by ring

/-- The left constant `C₁/(2π) (e^{5b/2} + e^{(5/2)²/(4π e^{-2b})})`. -/
def thetaRateLeftConst (C₁ b : ℝ) : ℝ :=
  C₁ / (2 * Real.pi) * (Real.exp (5 * b / 2) +
    Real.exp ((5 / 2) ^ 2 / (8 * (Real.pi / 2 * Real.exp (-(2 * b))))))

/-- Left tail of the rate kernel, uniformly for `x ≤ b`: evenness of `k` turns the right Gaussian
tail into a left tail dominating the weight `e^{-5s/2}`. -/
theorem thetaRateWeight_mul_le_left {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ y : ℝ, 0 ≤ y →
      thetaCuspFullSource y ≤ C₁ * Real.exp (-(Real.pi / 2) * Real.exp (2 * y)))
    {b x s : ℝ} (hxb : x ≤ b) :
    thetaRateWeight s * thetaCuspFullSource (x + s) ≤ thetaRateLeftConst C₁ b := by
  rw [thetaRateWeight_eq]
  have hE1 : 0 < Real.exp (5 * b / 2) := Real.exp_pos _
  have hE2 : 0 < Real.exp ((5 / 2) ^ 2 / (8 * (Real.pi / 2 * Real.exp (-(2 * b))))) :=
    Real.exp_pos _
  unfold thetaRateLeftConst
  rcases le_or_gt 0 (x + s) with hxs | hxs
  · have hK : thetaCuspFullSource (x + s) ≤ C₁ := by
      refine (hC₁ _ hxs).trans (mul_le_of_le_one_right hC₁0 ?_)
      rw [Real.exp_le_one_iff]
      have := Real.exp_pos (2 * (x + s))
      nlinarith [Real.pi_pos]
    have hw : Real.exp (-(5 * s / 2)) ≤ Real.exp (5 * b / 2) := Real.exp_le_exp.2 (by linarith)
    calc Real.exp (-(5 * s / 2)) / (2 * Real.pi) * thetaCuspFullSource (x + s) ≤
          Real.exp (5 * b / 2) / (2 * Real.pi) * C₁ :=
          mul_le_mul (div_le_div_of_nonneg_right hw (by positivity)) hK
            (thetaCuspFullSource_nonneg _) (by positivity)
      _ ≤ _ := by
          rw [div_mul_eq_mul_div, mul_comm (Real.exp _) C₁, ← div_mul_eq_mul_div]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hy : 0 ≤ -(x + s) := by linarith
    have hK : thetaCuspFullSource (x + s) ≤
        C₁ * Real.exp (-(Real.pi / 2 * Real.exp (-(2 * b))) * Real.exp (2 * (-s))) := by
      rw [← thetaCuspFullSource_neg]
      refine (hC₁ _ hy).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁0)
      have h : Real.exp (-(2 * b)) * Real.exp (2 * -s) ≤ Real.exp (2 * -(x + s)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith)
      nlinarith [Real.pi_pos]
    have hmain := exp_mul_sub_exp_le (D := 5 / 2) (c := Real.pi / 2 * Real.exp (-(2 * b)))
      (by norm_num) (by positivity) (-s)
    calc Real.exp (-(5 * s / 2)) / (2 * Real.pi) * thetaCuspFullSource (x + s) ≤
          Real.exp (-(5 * s / 2)) / (2 * Real.pi) *
            (C₁ * Real.exp (-(Real.pi / 2 * Real.exp (-(2 * b))) * Real.exp (2 * (-s)))) :=
          mul_le_mul_of_nonneg_left hK (by positivity)
      _ = C₁ / (2 * Real.pi) * Real.exp (5 / 2 * -s -
            Real.pi / 2 * Real.exp (-(2 * b)) * Real.exp (2 * -s)) := by
          rw [show 5 / 2 * -s - Real.pi / 2 * Real.exp (-(2 * b)) * Real.exp (2 * -s) =
            -(5 * s / 2) + -(Real.pi / 2 * Real.exp (-(2 * b))) * Real.exp (2 * -s) by ring,
            Real.exp_add]
          ring
      _ ≤ C₁ / (2 * Real.pi) *
            Real.exp ((5 / 2) ^ 2 / (8 * (Real.pi / 2 * Real.exp (-(2 * b))))) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-! ## The translation mixture of a rate seed -/

theorem comap_thetaSeedRate_Iio_le (ξ : Measure ℝ) (a : ℝ) :
    ξ.comap thetaSeedRate (Iio (-a)) ≤ ξ (Iic (Real.pi * Real.exp (-(2 * a)))) := by
  rw [measurableEmbedding_thetaSeedRate.comap_apply]
  refine measure_mono ?_
  rintro _ ⟨s, hs, rfl⟩
  simp only [mem_Iic]
  simp only [mem_Iio] at hs
  unfold thetaSeedRate
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) Real.pi_pos.le

theorem lintegral_comap_thetaSeedRate_le (ξ : Measure ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ s, g (thetaSeedRate s) ∂ξ.comap thetaSeedRate ≤ ∫⁻ l, g l ∂ξ := by
  rw [← measurableEmbedding_thetaSeedRate.lintegral_map, measurableEmbedding_thetaSeedRate.map_comap]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

theorem thetaMeasureGauge_thetaRateTranslation (ξ : Measure ℝ) (x : ℝ) :
    thetaMeasureGauge (thetaRateTranslation ξ) thetaCuspFullSource x =
      ∫ s, thetaRateWeight s * thetaCuspFullSource (x + s) ∂ξ.comap thetaSeedRate := by
  unfold thetaMeasureGauge thetaRateTranslation
  rw [show (fun s => ENNReal.ofReal (thetaRateWeight s)) =
      fun s => (((thetaRateWeight s).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul continuous_thetaRateWeight.measurable.real_toNNReal]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (thetaRateWeight_pos s).le]

theorem integrable_thetaRateTranslation_iff (ξ : Measure ℝ) (x : ℝ) :
    Integrable (fun s => thetaCuspFullSource (x + s)) (thetaRateTranslation ξ) ↔
      Integrable (fun s => thetaRateWeight s * thetaCuspFullSource (x + s))
        (ξ.comap thetaSeedRate) := by
  unfold thetaRateTranslation
  rw [show (fun s => ENNReal.ofReal (thetaRateWeight s)) =
      fun s => (((thetaRateWeight s).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    integrable_withDensity_iff_integrable_smul continuous_thetaRateWeight.measurable.real_toNNReal]
  refine integrable_congr (ae_of_all _ fun s => ?_)
  simp only
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (thetaRateWeight_pos s).le]

/-- The dominating function of the rate kernel on `[a, b]`. -/
def thetaRateBound (C₁ a b : ℝ) (s : ℝ) : ℝ :=
  thetaRateLeftConst C₁ b * (Iio (-a)).indicator (fun _ => (1 : ℝ)) s +
    C₁ * Real.exp (5 * a / 2) / (2 * Real.pi) *
      Real.exp (-(Real.exp (2 * a) / 2 * thetaSeedRate s))

theorem thetaRateWeight_mul_le_bound {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ y : ℝ, 0 ≤ y →
      thetaCuspFullSource y ≤ C₁ * Real.exp (-(Real.pi / 2) * Real.exp (2 * y)))
    {a b x s : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    thetaRateWeight s * thetaCuspFullSource (x + s) ≤ thetaRateBound C₁ a b s := by
  unfold thetaRateBound
  by_cases hs : s < -a
  · rw [indicator_of_mem (show s ∈ Iio (-a) from hs), mul_one]
    have h1 := thetaRateWeight_mul_le_left hC₁0 hC₁ (s := s) hxb
    have h2 : 0 ≤ C₁ * Real.exp (5 * a / 2) / (2 * Real.pi) *
        Real.exp (-(Real.exp (2 * a) / 2 * thetaSeedRate s)) := by positivity
    linarith
  · rw [indicator_of_notMem (show s ∉ Iio (-a) from hs), mul_zero, zero_add]
    exact thetaRateWeight_mul_le_right hC₁0 hC₁ hax (not_lt.1 hs)

theorem integrable_thetaRateBound {ξ : Measure ℝ} (hfin : ∀ t, 0 < t → rateLaplace ξ t ≠ ∞)
    (C₁ a b : ℝ) : Integrable (thetaRateBound C₁ a b) (ξ.comap thetaSeedRate) := by
  have hIic : ξ (Iic (Real.pi * Real.exp (-(2 * a)))) ≠ ∞ :=
    measure_Iic_ne_top_of_laplace (by simpa [rateLaplace] using hfin 1 one_pos) _
  refine Integrable.add (Integrable.const_mul ?_ _) (Integrable.const_mul ?_ _)
  · rw [integrable_indicator_iff measurableSet_Iio]
    exact integrableOn_const ((comap_thetaSeedRate_Iio_le ξ a).trans_lt
      (lt_top_iff_ne_top.2 hIic)).ne
  · refine ⟨(by unfold thetaSeedRate; fun_prop : Continuous fun s =>
      Real.exp (-(Real.exp (2 * a) / 2 * thetaSeedRate s))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun s => (Real.exp_pos _).le)]
    exact (lintegral_comap_thetaSeedRate_le ξ
      (fun l => ENNReal.ofReal (Real.exp (-(Real.exp (2 * a) / 2 * l))))).trans_lt
      (lt_top_iff_ne_top.2 (hfin _ (by positivity)))

/-- **The Euler translation mixture is pointwise finite and continuous.**  For a rate seed with
finite Laplace transform, `s ↦ k(x+s)` is integrable against its translation measure for every `x`
and `x ↦ ∫ k(x+s) dη(s)` is continuous: the right Gaussian tail of `k` dominates every polynomial
in `λ = π e^{2s}`, and evenness gives a left tail dominating the weight `e^{-5s/2}`. -/
theorem thetaRateTranslation_mixture {ξ : Measure ℝ} (hfin : ∀ t, 0 < t → rateLaplace ξ t ≠ ∞) :
    (∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) (thetaRateTranslation ξ)) ∧
      Continuous (thetaMeasureGauge (thetaRateTranslation ξ) thetaCuspFullSource) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_thetaCuspFullSource_le_halfGaussian
  have hmeas : ∀ x, AEStronglyMeasurable (fun s => thetaRateWeight s * thetaCuspFullSource (x + s))
      (ξ.comap thetaSeedRate) := fun x =>
    (continuous_thetaRateWeight.mul (continuous_thetaCuspFullSource.comp
      (continuous_const.add continuous_id))).aestronglyMeasurable
  have hdom : ∀ a b x, a ≤ x → x ≤ b → ∀ s,
      ‖thetaRateWeight s * thetaCuspFullSource (x + s)‖ ≤ thetaRateBound C₁ a b s :=
    fun a b x hax hxb s => by
      rw [Real.norm_of_nonneg (mul_nonneg (thetaRateWeight_pos s).le
        (thetaCuspFullSource_nonneg _))]
      exact thetaRateWeight_mul_le_bound hC₁0 hC₁ hax hxb
  refine ⟨fun x => (integrable_thetaRateTranslation_iff ξ x).2 ?_, ?_⟩
  · exact (integrable_thetaRateBound hfin C₁ x x).mono' (hmeas x)
      (ae_of_all _ (hdom x x x le_rfl le_rfl))
  · have heq : thetaMeasureGauge (thetaRateTranslation ξ) thetaCuspFullSource = fun x =>
        ∫ s, thetaRateWeight s * thetaCuspFullSource (x + s) ∂ξ.comap thetaSeedRate :=
      funext (thetaMeasureGauge_thetaRateTranslation ξ)
    rw [heq, continuous_iff_continuousAt]
    intro x₀
    refine continuousAt_of_dominated (bound := thetaRateBound C₁ (x₀ - 1) (x₀ + 1))
      (Eventually.of_forall hmeas) ?_ (integrable_thetaRateBound hfin _ _ _)
      (ae_of_all _ fun s => ?_)
    · filter_upwards [Icc_mem_nhds (by linarith : x₀ - 1 < x₀) (by linarith : x₀ < x₀ + 1)]
        with x hx
      exact ae_of_all _ (hdom _ _ x hx.1 hx.2)
    · exact (continuous_const.mul (continuous_thetaCuspFullSource.comp
        (continuous_id.add continuous_const))).continuousAt

/-- **Flux of the Euler translation mixture.**  For a rate seed `ξ` on `(0, ∞)` whose Euler sum
`ν = Σ_n A_n ξ` has finite Laplace transform, the mixture `∫ k(·+s) dη_ξ(s)` is a flux source with
`b = L_ν`. -/
theorem thetaFluxSource_thetaRateTranslation {ξ : Measure ℝ} (hξ0 : ξ (Iic 0) = 0)
    (hfin : ∀ t, 0 < t → rateLaplace (rateEuler ξ) t ≠ ∞) :
    (∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) (thetaRateTranslation ξ)) ∧
      ThetaFluxSource (thetaMeasureGauge (thetaRateTranslation ξ) thetaCuspFullSource) ∧
      ∀ t, 0 < t → thetaNormalizedFlux
        (thetaMeasureGauge (thetaRateTranslation ξ) thetaCuspFullSource) t =
          (rateLaplace (rateEuler ξ) t).toReal := by
  have hξfin : ∀ t, 0 < t → rateLaplace ξ t ≠ ∞ := fun t ht =>
    ne_top_of_le_ne_top (hfin t ht) (lintegral_mono' (le_rateEuler ξ) le_rfl)
  obtain ⟨hint, hcont⟩ := thetaRateTranslation_mixture hξfin
  set M := thetaMeasureGauge (thetaRateTranslation ξ) thetaCuspFullSource with hM
  have hflux : ∀ X, ∫⁻ x in Ioi X, ENNReal.ofReal (Real.exp (x / 2) * M x) =
      ENNReal.ofReal (Real.exp (3 * X)) * rateLaplace (rateEuler ξ) (Real.exp (2 * X)) :=
    fun X => by rw [hM, lintegral_Ioi_thetaMeasureGauge hint X, thetaRateSeed_thetaRateTranslation hξ0]
  have hnn : ∀ x, 0 ≤ Real.exp (x / 2) * M x := fun x =>
    mul_nonneg (Real.exp_pos _).le (thetaMeasureGauge_nonneg _ _)
  have hcM : Continuous fun x => Real.exp (x / 2) * M x :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).mul hcont
  have hIO : ∀ X, IntegrableOn (fun x => Real.exp (x / 2) * M x) (Ioi X) := fun X =>
    ⟨hcM.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => hnn x)).2 (by
      rw [hflux X]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_top_iff_ne_top.2 (hfin _ (Real.exp_pos _))))⟩
  refine ⟨hint, ⟨hcont, hIO⟩, fun t ht => ?_⟩
  obtain ⟨X, rfl⟩ : ∃ X, Real.exp (2 * X) = t :=
    ⟨Real.log t / 2, by rw [show 2 * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]⟩
  rw [thetaNormalizedFlux_exp, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => hnn x)
    hcM.aestronglyMeasurable, hflux X, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
  simp

/-! ## Source-level Möbius reconstruction -/

/-- The two control conditions on a rate measure: a positive rate gap, or a finite negative
moment `M_q` for some `q > 3/2`. -/
def RateControlled (ν : Measure ℝ) : Prop :=
  (∃ l₀ : ℝ, 0 < l₀ ∧ ν (Iio l₀) = 0) ∨ ∃ q : ℝ, 3 / 2 < q ∧ rateNegMoment q ν ≠ ∞

/-- `ν` is a positive Bernstein measure of the normalized flux of `f`. -/
def IsThetaFluxRateMeasure (f : ℝ → ℝ) (ν : Measure ℝ) : Prop :=
  ν (Ici 0)ᶜ = 0 ∧ (∀ t, 0 < t → rateLaplace ν t ≠ ∞) ∧
    ∀ t, 0 < t → thetaNormalizedFlux f t = (rateLaplace ν t).toReal

theorem rateEuler_compl_Ici {ξ : Measure ℝ} (hξ : ξ (Ici 0)ᶜ = 0) : rateEuler ξ (Ici 0)ᶜ = 0 := by
  rw [rateEuler_eq_sum, Measure.sum_apply _ measurableSet_Ici.compl]
  exact ENNReal.tsum_eq_zero.2 fun m => rateDilate_compl_Ici hξ m

theorem RateControlled.rateWindowFinite {ν : Measure ℝ} (h : RateControlled ν) (hν0 : ν (Iic 0) = 0)
    (hfin : rateLaplace ν 1 ≠ ∞) : RateWindowFinite ν := by
  rcases h with ⟨l₀, hl₀, hgap⟩ | ⟨q, hq, hM⟩
  · exact rateWindowFinite_of_gap hl₀ hgap (by simpa [rateLaplace] using hfin)
  · exact rateWindowFinite_of_negMoment hq hν0 hM

/-- **Uniqueness of the positive translation measure.**  If the flux of `f` has a window-finite
Bernstein measure `ν = Σ_n A_n ξ`, then every positive translation measure `η` with
`f = ∫ k(·+s) dη(s)` (pointwise integrable) is the translation measure of the seed `ξ`. -/
theorem eq_thetaRateTranslation_of_thetaMeasureGauge {f : ℝ → ℝ} (hf : ThetaFluxSource f)
    {ν ξ : Measure ℝ} (hν : IsThetaFluxRateMeasure f ν) (hW : RateWindowFinite ν)
    (hξ : rateEuler ξ = ν) {η : Measure ℝ}
    (hη : ∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) η)
    (hfη : f = thetaMeasureGauge η thetaCuspFullSource) : η = thetaRateTranslation ξ := by
  obtain ⟨hν0, hνfin, hrep⟩ := hν
  have hL : ∀ t, 0 < t → rateLaplace (rateEuler (thetaRateSeed η)) t = rateLaplace ν t := by
    intro t ht
    obtain ⟨X, rfl⟩ : ∃ X, Real.exp (2 * X) = t :=
      ⟨Real.log t / 2, by rw [show 2 * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]⟩
    have h1 := lintegral_Ioi_thetaMeasureGauge hη X
    rw [← hfη] at h1
    have hI : (∫ x in Ioi X, Real.exp (x / 2) * f x) =
        Real.exp (3 * X) * (rateLaplace ν (Real.exp (2 * X))).toReal := by
      have h := thetaNormalizedFlux_exp f X
      rw [hrep _ (Real.exp_pos _)] at h
      rw [h, ← mul_assoc, ← Real.exp_add]
      simp
    have h2 : ∫⁻ x in Ioi X, ENNReal.ofReal (Real.exp (x / 2) * f x) =
        ENNReal.ofReal (Real.exp (3 * X)) * rateLaplace ν (Real.exp (2 * X)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hf.2 X) (ae_of_all _ fun x =>
        mul_nonneg (Real.exp_pos _).le (by rw [hfη]; exact thetaMeasureGauge_nonneg η x)), hI,
        ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (hνfin _ (Real.exp_pos _))]
    exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top).1 (h1.symm.trans h2)
  have hE : rateEuler (thetaRateSeed η) = ν :=
    eq_of_rateLaplace_eq (rateEuler_compl_Ici (thetaRateSeed_compl_Ici η)) hν0
      (by rw [hL 1 one_pos]; exact hνfin 1 one_pos) (hνfin 1 one_pos) hL
  rw [← thetaRateTranslation_thetaRateSeed η, rateMobius_unique hW hE hξ]

/-- **Source-level Möbius reconstruction (7).**  Let `f` be a flux source such that `b_f` and every
finite-prime-deleted flux `b_{D_S f}` are completely monotone, and suppose the positive Bernstein
measure of `b_f` has a positive rate gap or a finite negative moment `M_q`, `q > 3/2`.  Then
`b_f = L_ν` with `ν = Σ_n A_n ξ` for a unique positive seed `ξ` on `(0, ∞)`, and
`f(x) = ∫ k(x+s) dη(s)` for the positive measure `η` obtained from `(2π e^{5s/2})⁻¹ dξ(λ)` under
`λ = π e^{2s}`; this `η` is the only positive measure representing `f` as a translation mixture
of `k`. -/
theorem thetaRate_mobius_source_representation {f : ℝ → ℝ} (hf : ThetaFluxSource f)
    (hCM : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      CompletelyMonotoneOn (thetaNormalizedFlux (thetaPrimeDeletion S f)))
    (hctrl : ∀ ν, IsThetaFluxRateMeasure f ν → RateControlled ν) :
    ∃ ν ξ : Measure ℝ, IsThetaFluxRateMeasure f ν ∧ RateWindowFinite ν ∧ rateEuler ξ = ν ∧
      ξ (Iic 0) = 0 ∧
      (∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) (thetaRateTranslation ξ)) ∧
      f = thetaMeasureGauge (thetaRateTranslation ξ) thetaCuspFullSource ∧
      ∀ η : Measure ℝ, (∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) η) →
        f = thetaMeasureGauge η thetaCuspFullSource → η = thetaRateTranslation ξ := by
  have hCMf : CompletelyMonotoneOn (thetaNormalizedFlux f) := by
    simpa [thetaPrimeDeletion_empty] using hCM ∅ (by simp)
  obtain ⟨ν, hν0, hνfin, hrep⟩ := exists_rateMeasure_of_completelyMonotoneOn hCMf
  have hν : IsThetaFluxRateMeasure f ν := ⟨hν0, hνfin, hrep⟩
  have hIic := rateMeasure_Iic_zero_of_flux hf hν0 hνfin hrep
  have hW := (hctrl ν hν).rateWindowFinite hIic (hνfin 1 one_pos)
  obtain ⟨ξ, hξ, -⟩ := (rateMobius_classification hW).1 fun S hS =>
    rateDeletionPart_le_of_completelyMonotoneOn hf hν0 hνfin hrep hS (hCM S hS)
  have hξν : ξ ≤ ν := hξ ▸ le_rateEuler ξ
  have hξ0 : ξ (Iic 0) = 0 := le_antisymm ((Measure.le_iff'.1 hξν _).trans hIic.le) zero_le
  obtain ⟨hint, hMsrc, hMflux⟩ := thetaFluxSource_thetaRateTranslation hξ0 (hξ ▸ hνfin)
  have hfeq : f = thetaMeasureGauge (thetaRateTranslation ξ) thetaCuspFullSource :=
    eq_of_thetaNormalizedFlux_eq hf.1 hMsrc.1 hf.2 hMsrc.2 fun t ht => by
      rw [hrep t ht, hMflux t ht, hξ]
  exact ⟨ν, ξ, hν, hW, hξ, hξ0, hint, hfeq, fun η hη hfη =>
    eq_thetaRateTranslation_of_thetaMeasureGauge hf hν hW hξ hη hfη⟩

/-- **Positive theta-translation representation.**  Under the all-sieve complete-monotonicity
tests and either control condition, `f` is a translation mixture of the completed theta source
by a unique positive measure. -/
theorem existsUnique_thetaTranslationMeasure {f : ℝ → ℝ} (hf : ThetaFluxSource f)
    (hCM : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      CompletelyMonotoneOn (thetaNormalizedFlux (thetaPrimeDeletion S f)))
    (hctrl : ∀ ν, IsThetaFluxRateMeasure f ν → RateControlled ν) :
    ∃! η : Measure ℝ, (∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) η) ∧
      f = thetaMeasureGauge η thetaCuspFullSource := by
  obtain ⟨_, ξ, -, -, -, -, hint, hfeq, huniq⟩ := thetaRate_mobius_source_representation hf hCM hctrl
  exact ⟨thetaRateTranslation ξ, ⟨hint, hfeq⟩, fun η hη => huniq η hη.1 hη.2⟩

/-- Translation measures of gapped seeds have support bounded below. -/
theorem thetaRateTranslation_Iio_eq_zero {ξ : Measure ℝ} {l₀ : ℝ} (hl₀ : 0 < l₀)
    (hgap : ξ (Iio l₀) = 0) :
    thetaRateTranslation ξ (Iio (Real.log (l₀ / Real.pi) / 2)) = 0 := by
  unfold thetaRateTranslation
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [measurableEmbedding_thetaSeedRate.comap_apply]
  refine measure_mono_null ?_ hgap
  rintro _ ⟨s, hs, rfl⟩
  simp only [mem_Iio] at hs ⊢
  unfold thetaSeedRate
  have h : Real.exp (2 * s) < l₀ / Real.pi := by
    rw [← Real.exp_log (div_pos hl₀ Real.pi_pos)]
    exact Real.exp_lt_exp.2 (by linarith)
  rwa [lt_div_iff₀ Real.pi_pos, mul_comm] at h

/-- **Rate-gap case.**  If the Bernstein measure of `b_f` vanishes below `l₀ > 0`, the
representing translation measure vanishes below `log(l₀/π)/2`. -/
theorem thetaTranslationMeasure_Iio_eq_zero_of_gap {f : ℝ → ℝ} (hf : ThetaFluxSource f)
    (hCM : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      CompletelyMonotoneOn (thetaNormalizedFlux (thetaPrimeDeletion S f)))
    {ν : Measure ℝ} (hν : IsThetaFluxRateMeasure f ν) {l₀ : ℝ} (hl₀ : 0 < l₀)
    (hgap : ν (Iio l₀) = 0) {η : Measure ℝ}
    (hη : ∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) η)
    (hfη : f = thetaMeasureGauge η thetaCuspFullSource) :
    η (Iio (Real.log (l₀ / Real.pi) / 2)) = 0 := by
  have hIic := rateMeasure_Iic_zero_of_flux hf hν.1 hν.2.1 hν.2.2
  have hW := RateControlled.rateWindowFinite (Or.inl ⟨l₀, hl₀, hgap⟩) hIic (hν.2.1 1 one_pos)
  obtain ⟨ξ, hξ, -⟩ := (rateMobius_classification hW).1 fun S hS =>
    rateDeletionPart_le_of_completelyMonotoneOn hf hν.1 hν.2.1 hν.2.2 hS (hCM S hS)
  rw [eq_thetaRateTranslation_of_thetaMeasureGauge hf hν hW hξ hη hfη]
  exact thetaRateTranslation_Iio_eq_zero hl₀
    (le_antisymm ((Measure.le_iff'.1 (hξ ▸ le_rateEuler ξ) _).trans hgap.le) zero_le)

/-! ## Charge rigidity -/

/-- Weighted Tonelli law in `[0, ∞]`:
`∫ e^{wx} (∫ k(x+s) dη(s)) dx = (∫ e^{-ws} dη(s)) · ∫ e^{wy} k(y) dy`. -/
theorem lintegral_exp_mul_thetaMeasureGauge {η : Measure ℝ}
    (hη : ∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) η) (w : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (w * x) * thetaMeasureGauge η thetaCuspFullSource x) =
      (∫⁻ s, ENNReal.ofReal (Real.exp (-(w * s))) ∂η) *
        ∫⁻ y, ENNReal.ofReal (Real.exp (w * y) * thetaCuspFullSource y) := by
  haveI := sigmaFinite_of_integrable_thetaCuspFullSource (hη 0)
  have hin : ∀ x, ENNReal.ofReal (Real.exp (w * x) * thetaMeasureGauge η thetaCuspFullSource x) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (w * x) * thetaCuspFullSource (x + s)) ∂η := fun x => by
    unfold thetaMeasureGauge
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal ((hη x).const_mul _)
      (ae_of_all _ fun s => mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_nonneg _))]
  have hmeas : Measurable (Function.uncurry fun x s =>
      ENNReal.ofReal (Real.exp (w * x) * thetaCuspFullSource (x + s))) :=
    ENNReal.measurable_ofReal.comp (Continuous.measurable (by
      have := continuous_thetaCuspFullSource
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (w * p.1) * thetaCuspFullSource (p.1 + p.2))))
  simp_rw [hin]
  have hmc := lintegral_mul_const (μ := η)
    (∫⁻ y, ENNReal.ofReal (Real.exp (w * y) * thetaCuspFullSource y))
    (show Measurable fun s : ℝ => ENNReal.ofReal (Real.exp (-(w * s))) from
      ENNReal.measurable_ofReal.comp (by fun_prop))
  rw [lintegral_lintegral_swap hmeas.aemeasurable, ← hmc]
  refine lintegral_congr fun s => ?_
  rw [← lintegral_add_right_eq_self
      (fun y => ENNReal.ofReal (Real.exp (w * y) * thetaCuspFullSource y)) s,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_comm]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
  congr 3
  ring

theorem lintegral_exp_neg_eq_one_of_charge {η : Measure ℝ}
    (hη : ∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) η) (w : ℝ)
    (h : ∫ x, Real.exp (w * x) * thetaMeasureGauge η thetaCuspFullSource x =
      ∫ x, Real.exp (w * x) * thetaCuspFullSource x) :
    ∫⁻ s, ENNReal.ofReal (Real.exp (-(w * s))) ∂η = 1 := by
  have hc := integral_exp_mul_thetaCuspFullSource_pos w
  have hKint := HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource w
  have hGint : Integrable fun x => Real.exp (w * x) * thetaMeasureGauge η thetaCuspFullSource x := by
    by_contra hni
    rw [integral_undef hni] at h
    linarith
  have hK : ∫⁻ y, ENNReal.ofReal (Real.exp (w * y) * thetaCuspFullSource y) =
      ENNReal.ofReal (∫ x, Real.exp (w * x) * thetaCuspFullSource x) :=
    (ofReal_integral_eq_lintegral_ofReal hKint (ae_of_all _ fun x =>
      mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_nonneg _))).symm
  have hG := ofReal_integral_eq_lintegral_ofReal hGint (ae_of_all _ fun x =>
    mul_nonneg (Real.exp_pos _).le (thetaMeasureGauge_nonneg η x))
  rw [h, lintegral_exp_mul_thetaMeasureGauge hη w, hK, mul_comm] at hG
  have hne : ENNReal.ofReal (∫ x, Real.exp (w * x) * thetaCuspFullSource x) ≠ 0 :=
    (ENNReal.ofReal_pos.2 hc).ne'
  exact ((ENNReal.mul_right_inj hne ENNReal.ofReal_ne_top).1 (by rw [mul_one]; exact hG)).symm

theorem integrable_exp_of_lintegral_eq_one {η : Measure ℝ} {w : ℝ}
    (h : ∫⁻ s, ENNReal.ofReal (Real.exp (-(w * s))) ∂η = 1) :
    Integrable (fun s => Real.exp (-(w * s))) η ∧ ∫ s, Real.exp (-(w * s)) ∂η = 1 := by
  have hm : AEStronglyMeasurable (fun s => Real.exp (-(w * s))) η :=
    (by fun_prop : Continuous fun s : ℝ => Real.exp (-(w * s))).aestronglyMeasurable
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun s => (Real.exp_pos _).le)).2
    (by rw [h]; exact ENNReal.one_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s => (Real.exp_pos _).le) hm, h,
    ENNReal.toReal_one]

/-- **Charge rigidity.**  A positive translation mixture of `k` with the ordinary mass and both
reflected half-density charges of `k` has translation measure `δ₀`. -/
theorem thetaMeasureGauge_charge_rigidity {η : Measure ℝ}
    (hη : ∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) η)
    (hmass : ∫ x, thetaMeasureGauge η thetaCuspFullSource x = ∫ x, thetaCuspFullSource x)
    (hplus : ∫ x, Real.exp (x / 2) * thetaMeasureGauge η thetaCuspFullSource x =
      ∫ x, Real.exp (x / 2) * thetaCuspFullSource x)
    (hminus : ∫ x, Real.exp (-(x / 2)) * thetaMeasureGauge η thetaCuspFullSource x =
      ∫ x, Real.exp (-(x / 2)) * thetaCuspFullSource x) :
    η = Measure.dirac 0 := by
  have h0 := lintegral_exp_neg_eq_one_of_charge hη 0 (by simpa using hmass)
  have hp := lintegral_exp_neg_eq_one_of_charge hη (1 / 2) (by
    simp_rw [show ∀ x : ℝ, 1 / 2 * x = x / 2 from fun x => by ring]; exact hplus)
  have hm := lintegral_exp_neg_eq_one_of_charge hη (-(1 / 2)) (by
    simp_rw [show ∀ x : ℝ, -(1 / 2) * x = -(x / 2) from fun x => by ring]; exact hminus)
  simp only [zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one, lintegral_const,
    one_mul] at h0
  haveI : IsProbabilityMeasure η := ⟨h0⟩
  obtain ⟨hpi, hpv⟩ := integrable_exp_of_lintegral_eq_one hp
  obtain ⟨hmi, hmv⟩ := integrable_exp_of_lintegral_eq_one hm
  simp_rw [show ∀ s : ℝ, -(1 / 2 * s) = -(s / 2) from fun s => by ring] at hpi hpv
  simp_rw [show ∀ s : ℝ, -(-(1 / 2) * s) = s / 2 from fun s => by ring] at hmi hmv
  have habs : Integrable (fun s => Real.exp (|s| / 2)) η :=
    (hpi.add hmi).mono' (by fun_prop : Continuous fun s : ℝ => Real.exp (|s| / 2)).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        show Real.exp (|s| / 2) ≤ Real.exp (-(s / 2)) + Real.exp (s / 2)
        rcases le_or_gt 0 s with hs | hs
        · rw [abs_of_nonneg hs]; linarith [Real.exp_pos (-(s / 2))]
        · rw [abs_of_neg hs, show -s / 2 = -(s / 2) by ring]; linarith [Real.exp_pos (s / 2)])
  refine measure_eq_dirac_of_cosh_half habs ?_
  rw [integral_cosh_half_eq habs, hmv, hpv]
  norm_num

/-- **Source rigidity.**  Under the all-sieve tests and either control condition, a flux source with
the ordinary mass and both reflected half-density charges of `k` is `k`. -/
theorem eq_thetaCuspFullSource_of_charges {f : ℝ → ℝ} (hf : ThetaFluxSource f)
    (hCM : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      CompletelyMonotoneOn (thetaNormalizedFlux (thetaPrimeDeletion S f)))
    (hctrl : ∀ ν, IsThetaFluxRateMeasure f ν → RateControlled ν)
    (hmass : ∫ x, f x = ∫ x, thetaCuspFullSource x)
    (hplus : ∫ x, Real.exp (x / 2) * f x = ∫ x, Real.exp (x / 2) * thetaCuspFullSource x)
    (hminus : ∫ x, Real.exp (-(x / 2)) * f x = ∫ x, Real.exp (-(x / 2)) * thetaCuspFullSource x) :
    f = thetaCuspFullSource := by
  obtain ⟨η, ⟨hη, hfη⟩, -⟩ := existsUnique_thetaTranslationMeasure hf hCM hctrl
  subst hfη
  rw [thetaMeasureGauge_charge_rigidity hη hmass hplus hminus, thetaMeasureGauge_dirac_zero]

theorem integral_exp_neg_half_mul_of_even {g : ℝ → ℝ} (hg : ∀ x, g (-x) = g x) :
    ∫ x, Real.exp (-(x / 2)) * g x = ∫ x, Real.exp (x / 2) * g x := by
  rw [← integral_neg_eq_self (fun x => Real.exp (x / 2) * g x) volume]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [hg]
  ring_nf

/-- For an even source, equality of the positive half-charge supplies the reflected charge. -/
theorem eq_thetaCuspFullSource_of_even_charges {f : ℝ → ℝ} (hf : ThetaFluxSource f)
    (hCM : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      CompletelyMonotoneOn (thetaNormalizedFlux (thetaPrimeDeletion S f)))
    (hctrl : ∀ ν, IsThetaFluxRateMeasure f ν → RateControlled ν) (heven : ∀ x, f (-x) = f x)
    (hmass : ∫ x, f x = ∫ x, thetaCuspFullSource x)
    (hplus : ∫ x, Real.exp (x / 2) * f x = ∫ x, Real.exp (x / 2) * thetaCuspFullSource x) :
    f = thetaCuspFullSource :=
  eq_thetaCuspFullSource_of_charges hf hCM hctrl hmass hplus (by
    rw [integral_exp_neg_half_mul_of_even heven,
      integral_exp_neg_half_mul_of_even thetaCuspFullSource_neg, hplus])

/-! ## The literal theta rate measure -/

/-- Every positive translation mixture of `k` that is a flux source has Bernstein measure
`Σ_n A_n ξ`, `ξ` its rate seed. -/
theorem isThetaFluxRateMeasure_thetaMeasureGauge {η : Measure ℝ}
    (hη : ∀ x, Integrable (fun s => thetaCuspFullSource (x + s)) η)
    (hG : ThetaFluxSource (thetaMeasureGauge η thetaCuspFullSource)) :
    IsThetaFluxRateMeasure (thetaMeasureGauge η thetaCuspFullSource)
      (rateEuler (thetaRateSeed η)) := by
  have hkey : ∀ X, ENNReal.ofReal (Real.exp (3 * X)) *
      rateLaplace (rateEuler (thetaRateSeed η)) (Real.exp (2 * X)) =
      ENNReal.ofReal (∫ x in Ioi X, Real.exp (x / 2) * thetaMeasureGauge η thetaCuspFullSource x) :=
    fun X => by
      rw [← lintegral_Ioi_thetaMeasureGauge hη X, ofReal_integral_eq_lintegral_ofReal (hG.2 X)
        (ae_of_all _ fun x => mul_nonneg (Real.exp_pos _).le (thetaMeasureGauge_nonneg η x))]
  have hexp : ∀ t, 0 < t → ∃ X, Real.exp (2 * X) = t := fun t ht =>
    ⟨Real.log t / 2, by rw [show 2 * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]⟩
  have hfin : ∀ t, 0 < t → rateLaplace (rateEuler (thetaRateSeed η)) t ≠ ∞ := by
    intro t ht
    obtain ⟨X, rfl⟩ := hexp t ht
    intro htop
    have h := hkey X
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'] at h
    exact ENNReal.ofReal_ne_top h.symm
  refine ⟨rateEuler_compl_Ici (thetaRateSeed_compl_Ici η), hfin, fun t ht => ?_⟩
  obtain ⟨X, rfl⟩ := hexp t ht
  rw [thetaNormalizedFlux_exp, ← ENNReal.toReal_ofReal (integral_nonneg fun x =>
    mul_nonneg (Real.exp_pos _).le (thetaMeasureGauge_nonneg η x)), ← hkey X, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
  simp

theorem thetaRateSeed_dirac_zero :
    thetaRateSeed (Measure.dirac 0) = ENNReal.ofReal (2 * Real.pi) • Measure.dirac Real.pi := by
  classical
  ext E hE
  have hpre := measurableEmbedding_thetaSeedRate.measurable hE
  rw [thetaRateSeed, Measure.map_apply measurableEmbedding_thetaSeedRate.measurable hE,
    withDensity_apply _ hpre, Measure.smul_apply, smul_eq_mul, setLIntegral_dirac,
    Measure.dirac_apply' _ hE]
  have h0 : thetaSeedRate 0 = Real.pi := by simp [thetaSeedRate]
  by_cases h : Real.pi ∈ E
  · rw [if_pos (show (0 : ℝ) ∈ thetaSeedRate ⁻¹' E by simp [mem_preimage, h0, h]),
      indicator_of_mem h]
    simp
  · rw [if_neg (show (0 : ℝ) ∉ thetaSeedRate ⁻¹' E by simp [mem_preimage, h0, h]),
      indicator_of_notMem h, mul_zero]

/-- The literal theta rate measure `ν_k = 2π Σ_{n ≥ 1} n² δ_{π n²}`. -/
def thetaRateMeasure : Measure ℝ := rateEuler (ENNReal.ofReal (2 * Real.pi) • Measure.dirac Real.pi)

theorem isThetaFluxRateMeasure_thetaCuspFullSource :
    IsThetaFluxRateMeasure thetaCuspFullSource thetaRateMeasure := by
  obtain ⟨C, hC⟩ := exists_abs_thetaCuspFullSource_le_const
  have h := isThetaFluxRateMeasure_thetaMeasureGauge (η := Measure.dirac 0)
    (integrable_comp_add_of_bounded continuous_thetaCuspFullSource hC)
    (by rw [thetaMeasureGauge_dirac_zero]; exact thetaFluxSource_thetaCuspFullSource)
  rwa [thetaMeasureGauge_dirac_zero, thetaRateSeed_dirac_zero] at h

/-- The theta rate measure has the rate gap `λ₀ = π`. -/
theorem thetaRateMeasure_Iio_pi : thetaRateMeasure (Iio Real.pi) = 0 := by
  rw [thetaRateMeasure, rateEuler_apply _ measurableSet_Iio]
  refine ENNReal.tsum_eq_zero.2 fun m => ?_
  rw [rateDilate_apply _ _ measurableSet_Iio, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurable_rateScale m measurableSet_Iio)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [indicator_of_notMem]
    · simp
    · simp only [mem_preimage, rateScale, mem_Iio, not_lt]
      have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hm)
      nlinarith [Real.pi_pos]

/-- The negative moments of the theta rate measure:
`M_q(ν_k) = 2π π^{-q} Σ_{n ≥ 1} n^{2-2q}`, finite for every `q > 3/2`. -/
theorem rateNegMoment_thetaRateMeasure {q : ℝ} (hq : 3 / 2 < q) :
    rateNegMoment q thetaRateMeasure =
      (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ (2 - 2 * q))) *
        (ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (Real.pi ^ (-q))) ∧
    rateNegMoment q thetaRateMeasure ≠ ∞ := by
  have hM : rateNegMoment q (ENNReal.ofReal (2 * Real.pi) • Measure.dirac Real.pi) =
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (Real.pi ^ (-q)) := by
    rw [rateNegMoment, lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
      indicator_of_mem (show Real.pi ∈ Ioi (0 : ℝ) from Real.pi_pos)]
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ (2 - 2 * q) :=
    Real.summable_nat_rpow.2 (by linarith)
  have heq : rateNegMoment q thetaRateMeasure =
      (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ (2 - 2 * q))) *
        (ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (Real.pi ^ (-q))) := by
    rw [thetaRateMeasure, rateNegMoment_rateEuler (by linarith), hM]
  refine ⟨heq, ?_⟩
  rw [heq, ← ENNReal.ofReal_tsum_of_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) hsum]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- Both reconstruction mechanisms apply to the literal theta source. -/
theorem rateControlled_thetaRateMeasure : RateControlled thetaRateMeasure :=
  Or.inl ⟨Real.pi, Real.pi_pos, thetaRateMeasure_Iio_pi⟩

end

end RHTower

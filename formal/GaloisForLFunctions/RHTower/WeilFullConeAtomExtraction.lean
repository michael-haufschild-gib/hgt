import GaloisForLFunctions.RHTower.WeilFullConeDeviationResidue
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# Atoms of the boundary measure of a Weil-positive system

Let `lam` be full-cone Weil-positive with boundary measure `μ_lam` and Herglotz continuation
`Φ_lam` on `Re s > 1/2`.

**Atom extraction** (`tendsto_mul_re_weilContinuation_atom`).  For every `a ∈ ℝ`,
`b · Re Φ_lam(1/2 + b + ia) → μ_lam({a})` as `b → 0⁺`.

**Atoms of `Λ`** (`boundaryMeasure_vonMangoldt_real_singleton`).  If `Λ` itself is Weil-positive,
equivalently under RH, then `μ_Λ({a}) = ord_{1/2+ia} ξ` for every `a`.

**Proof.**  By the Poisson representation, `b · Re Φ_lam(1/2+b+ia) = ∫ b²/(b² + (r−a)²) dμ_lam(r)`.
The integrand tends to the indicator of `{a}` and is dominated by `2/(1+(r−a)²)`, which is
`μ_lam`-integrable.  For `Λ`, `Φ_Λ = ξ'/ξ` on `Re s > 1/2`: both are holomorphic there under RH and
agree on `Re s > 1`.  Then `b · ξ'/ξ(1/2+b+ia) → ord ξ` by the residue law.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

theorem integrable_inv_one_add_sq_sub {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a : ℝ) :
    Integrable (fun r : ℝ => 1 / (1 + (r - a) ^ 2)) (boundaryMeasure hW) := by
  have hw : 0 < ((1 : ℂ) + a * I).re := by simp
  have hfin := lintegral_poissonDensity_lt_top hW hw
  have hpt : ∀ r : ℝ, ENNReal.ofReal (1 / (1 + (r - a) ^ 2)) = poissonDensity (1 + a * I) r := by
    intro r
    rw [← ENNReal.ofReal_toReal (poissonDensity_ne_top _ r), poissonDensity_toReal]
    congr 1
    simp
  have hc : Continuous fun r : ℝ => 1 / (1 + (r - a) ^ 2) :=
    continuous_const.div (by fun_prop) fun r => by positivity
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun r => by positivity)]
  simp_rw [hpt]
  exact hfin

theorem mul_re_weilContinuation_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {a b : ℝ}
    (hb : 0 < b) :
    b * (weilContinuation hW (((1 / 2 + b : ℝ) : ℂ) + a * I)).re =
      ∫ r, b ^ 2 / (b ^ 2 + (r - a) ^ 2) ∂boundaryMeasure hW := by
  set s : ℂ := ((1 / 2 + b : ℝ) : ℂ) + a * I with hs
  have hsre : s.re = 1 / 2 + b := by simp [hs]
  have hw : (s - 1 / 2) = (b : ℂ) + a * I := by rw [hs]; push_cast; ring
  rw [re_weilContinuation_eq hW (by rw [hsre]; linarith), hsre, hw]
  have hint : (∫⁻ r, poissonDensity ((b : ℂ) + a * I) r ∂boundaryMeasure hW).toReal =
      ∫ r, (poissonDensity ((b : ℂ) + a * I) r).toReal ∂boundaryMeasure hW :=
    (integral_toReal (measurable_poissonDensity _).aemeasurable
      (Eventually.of_forall fun r => (poissonDensity_ne_top _ r).lt_top)).symm
  have hre : ((b : ℂ) + a * I).re = b := by simp
  have him : ((b : ℂ) + a * I).im = a := by simp
  calc b * ((1 / 2 + b - 1 / 2) * (∫⁻ r, poissonDensity ((b : ℂ) + a * I) r
        ∂boundaryMeasure hW).toReal)
      = b ^ 2 * ∫ r, (poissonDensity ((b : ℂ) + a * I) r).toReal ∂boundaryMeasure hW := by
        rw [hint]; ring
    _ = ∫ r, b ^ 2 * (poissonDensity ((b : ℂ) + a * I) r).toReal ∂boundaryMeasure hW :=
        (integral_const_mul _ _).symm
    _ = ∫ r, b ^ 2 / (b ^ 2 + (r - a) ^ 2) ∂boundaryMeasure hW := by
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        simp only
        rw [poissonDensity_toReal, hre, him, mul_one_div]

/-- **Atom extraction.**  `b · Re Φ_lam(1/2 + b + ia) → μ_lam({a})` as `b → 0⁺`. -/
theorem tendsto_mul_re_weilContinuation_atom {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a : ℝ) :
    Tendsto (fun b : ℝ => b * (weilContinuation hW (((1 / 2 + b : ℝ) : ℂ) + a * I)).re)
      (𝓝[>] 0) (𝓝 ((boundaryMeasure hW).real {a})) := by
  have hlim : Tendsto (fun b : ℝ => ∫ r, b ^ 2 / (b ^ 2 + (r - a) ^ 2) ∂boundaryMeasure hW)
      (𝓝[>] 0) (𝓝 (∫ r, ({a} : Set ℝ).indicator (fun _ => (1 : ℝ)) r ∂boundaryMeasure hW)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun r => 2 * (1 / (1 + (r - a) ^ 2)))
      ?_ ?_ ((integrable_inv_one_add_sq_sub hW a).const_mul 2) ?_
    · filter_upwards [self_mem_nhdsWithin] with b hb
      have hb' : (0 : ℝ) < b := hb
      exact (continuous_const.div (by fun_prop) fun r => by positivity :
        Continuous fun r : ℝ => b ^ 2 / (b ^ 2 + (r - a) ^ 2)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with b hb
      refine Eventually.of_forall fun r => ?_
      have hb0 := hb.1
      have hb1 := hb.2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hx : 0 ≤ (r - a) ^ 2 := sq_nonneg _
      rw [div_le_iff₀ (by positivity)]
      have h1 : b ^ 2 ≤ 1 := by nlinarith
      rw [show 2 * (1 / (1 + (r - a) ^ 2)) * (b ^ 2 + (r - a) ^ 2) =
        2 * (b ^ 2 + (r - a) ^ 2) / (1 + (r - a) ^ 2) by ring, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hx (sq_nonneg b)]
    · refine Eventually.of_forall fun r => ?_
      by_cases hr : r = a
      · subst hr
        simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
          Set.indicator_of_mem (Set.mem_singleton r)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with b hb
        have hb' : b ≠ 0 := (show (0 : ℝ) < b from hb).ne'
        field_simp
      · rw [Set.indicator_of_notMem (by simpa using hr)]
        have hra : 0 < (r - a) ^ 2 := by
          have : r - a ≠ 0 := sub_ne_zero.mpr hr
          positivity
        have hc : ContinuousAt (fun b : ℝ => b ^ 2 / (b ^ 2 + (r - a) ^ 2)) 0 :=
          (by fun_prop : Continuous fun b : ℝ => b ^ 2).continuousAt.div (by fun_prop)
            (by rw [show (0 : ℝ) ^ 2 + (r - a) ^ 2 = (r - a) ^ 2 by ring]; exact hra.ne')
        have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using this
  have hval : (∫ r, ({a} : Set ℝ).indicator (fun _ => (1 : ℝ)) r ∂boundaryMeasure hW) =
      (boundaryMeasure hW).real {a} := by
    rw [integral_indicator_const _ (measurableSet_singleton a), smul_eq_mul, mul_one]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with b hb
  exact (mul_re_weilContinuation_eq hW hb).symm

/-- Under `Λ ∈ W`, the Herglotz continuation of `Λ` is `ξ'/ξ` on `Re s > 1/2`. -/
theorem weilContinuation_vonMangoldt_eq
    (hΛ : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) {s : ℂ}
    (hs : 1 / 2 < s.re) : weilContinuation hΛ s = logDeriv xi s := by
  have hRH := riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr hΛ
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hxi : ∀ z ∈ U, xi z ≠ 0 := by
    intro z hz h0
    have := xi_zero_re_eq_half_of_RH hRH h0
    have hz' : 1 / 2 < z.re := hz
    linarith
  have hLd : DifferentiableOn ℂ (logDeriv xi) U := by
    intro z hz
    have hd : DifferentiableAt ℂ xi z := xi_differentiable z
    exact (((xi_differentiable.analyticAt z).deriv.differentiableAt).div hd
      (hxi z hz)).differentiableWithinAt
  have hΦd := differentiableOn_weilContinuation hΛ
  have heq := (hΦd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hLd.analyticOnNhd hUo)
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected (show (2 : ℂ) ∈ U by simp [hU]; norm_num) ?_
  · exact heq hs
  · have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hV] with z hz
    have h := logDeriv_xi_sub_weilContinuation_eq hΛ hz
    have hL : LSeries (lamC fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) z =
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z := by
      refine LSeries_congr (fun {n} hn => ?_) z
      unfold lamC
      split_ifs with h2
      · rfl
      · have : n = 1 := by omega
        subst this
        simp
    rw [hL, sub_self, sub_eq_zero] at h
    exact h.symm

/-- **Atoms of `μ_Λ` are the multiplicities of the critical zeros.** -/
theorem boundaryMeasure_vonMangoldt_real_singleton
    (hΛ : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (a : ℝ) :
    (boundaryMeasure hΛ).real {a} = analyticOrderNatAt xi ((1 / 2 : ℂ) + a * I) := by
  have h1 := tendsto_mul_re_weilContinuation_atom hΛ a
  set s₀ : ℂ := (1 / 2 : ℂ) + a * I with hs₀
  have hres := RiemannGaussian.AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (xi_differentiable.analyticAt s₀) (xi_orderAt_ne_top s₀)
  have hpath : Tendsto (fun b : ℝ => (((1 / 2 + b : ℝ) : ℂ) + a * I)) (𝓝[>] 0) (𝓝[≠] s₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun b : ℝ => (((1 / 2 + b : ℝ) : ℂ) + a * I) := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa [hs₀] using this
    · filter_upwards [self_mem_nhdsWithin] with b hb
      intro h
      have := congrArg Complex.re h
      simp [hs₀] at this
      exact (show (0 : ℝ) < b from hb).ne' this
  have h2 := ((Complex.continuous_re.tendsto _).comp (hres.comp hpath))
  simp only [Function.comp_def, Complex.natCast_re] at h2
  have h3 : Tendsto (fun b : ℝ => b * (weilContinuation hΛ (((1 / 2 + b : ℝ) : ℂ) + a * I)).re)
      (𝓝[>] 0) (𝓝 (analyticOrderNatAt xi s₀ : ℝ)) := by
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with b hb
    have hb' : (0 : ℝ) < b := hb
    rw [weilContinuation_vonMangoldt_eq hΛ (by simp; linarith)]
    have : (((1 / 2 + b : ℝ) : ℂ) + a * I) - s₀ = (b : ℂ) := by rw [hs₀]; push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  exact tendsto_nhds_unique h1 h3

end RHTower.WeilSpectral

end

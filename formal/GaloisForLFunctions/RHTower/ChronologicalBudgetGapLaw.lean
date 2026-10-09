import GaloisForLFunctions.RHTower.ChronologicalMobiusEscape

/-!
# The coefficient budget of chronological approximation has a gap at exponent `2`

For a finite row `a` the chronological heat error is
`r_a(t) = e^{-t} + Σ_{k ≤ N} a_k (1/(kt) - 1/(e^{kt} - 1))`.  Rows with unbounded coefficients
approximate `e^{-t}` unconditionally (`exists_chronologicalHeatError_lt`), while bounded rows
force RH (`riemannHypothesis_of_forall_exists_chronologicalL2Norm_lt`).  This file measures the
price of approximation in the coefficient bound.

**Charge on a dyadic window** (`abs_chronologicalHarmonicCharge_le_sqrt`).  Averaging
`|c|/t ≤ |r(t)| + (1+4C)e^{-t}` over `[T, 2T]` against `dt/t` gives
`|c| ≤ √(2T) ‖r‖ + 2T(1+4C)e^{-T}`, a `√T` gain over the unit-window bound.

**Floor with the exact displacement exponent** (`norm_Gamma_le_chronological_offLine_sharp`).  At
a zero with `½ < σ = Re s < 1`, for every `U ≥ 1`,
`‖Γ(s)‖ ≤ ‖r‖ U^{σ-½} (1/√(2σ-1) + √2/(1-σ)) + (1+4C) e^{-U} (1 + 2U^σ/(1-σ))`.

**Gap law** (`two_mul_re_sub_half_ge_of_chronological_budget`,
`riemannHypothesis_of_chronological_budget_le_two`).  If every accuracy `ε > 0` is reached by a
row with coefficients at most `exp(ε^{-θ})`, then every zeta zero in the open strip has
`Re s = ½` or `θ (Re s - ½) ≥ 1`.  For `θ ≤ 2` this is RH: budgets growing like
`exp(ε^{-2})` still force every zero onto the line, and any slower-than-`exp(ε^{-2})` rate is
already full RH.  An off-line zero `β` forces `log C(ε) ≳ ε^{-1/(β-½)}`, so zeros close to the
critical line are the most expensive and no intermediate budget rate exists.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry.ChronologicalTensor

private theorem integral_Ioc_one_div_sq {T : ℝ} (hT : 0 < T) :
    (∫ t in Ioc T (2 * T), 1 / t ^ 2) = 1 / (2 * T) := by
  have h2T : T ≤ 2 * T := by linarith
  rw [← intervalIntegral.integral_of_le h2T]
  have hderiv : ∀ x ∈ Set.uIcc T (2 * T), HasDerivAt (fun t : ℝ => -1 / t) (1 / x ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le h2T] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h2 := (hasDerivAt_inv hx0).const_mul (-1 : ℝ)
    refine (h2.congr_deriv (by rw [one_div]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · simp only [neg_div]
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
    intro x hx; rw [Set.uIcc_of_le h2T] at hx; have : 0 < x := hT.trans_le hx.1; positivity

/-- **Dyadic-window charge bound.**  For `T ≥ 1`, rows bounded by `C` satisfy
`|charge| ≤ √(2T) ‖r‖ + 2T(1+4C)e^{-T}`. -/
theorem abs_chronologicalHarmonicCharge_le_sqrt (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C) {T : ℝ} (hT : 1 ≤ T) :
    |chronologicalHarmonicCharge a N| ≤
      Real.sqrt (2 * T) * chronologicalL2Norm (chronologicalHeatError a N) +
        2 * T * ((1 + 4 * C) * Real.exp (-T)) := by
  set c := |chronologicalHarmonicCharge a N| with hc
  set r := chronologicalHeatError a N with hr
  set E := chronologicalL2Norm r with hE
  have hT0 : 0 < T := by linarith
  have h2T : T ≤ 2 * T := by linarith
  have hrm : MemLp r 2 chronologicalPositiveVolume := chronologicalHeatError_memLp a N
  -- pointwise: `c/t ≤ |r t| + (1+4C) e^{-T}` on `(T, 2T]`
  have hpt : ∀ t ∈ Ioc T (2 * T), c / t ≤ |r t| + (1 + 4 * C) * Real.exp (-T) := by
    intro t ht
    have ht1 : 1 ≤ t := hT.trans ht.1.le
    have ht0 : 0 < t := by linarith
    have hdec := chronologicalHeatError_charge_decomposition a N ht0
    have hB := chronologicalBoseSum_uniform_bound a N C hC ha ht1
    have hexp : Real.exp (-t) ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith [ht.1])
    have hB' : |chronologicalBoseSum a N t| ≤ 4 * C * Real.exp (-T) :=
      hB.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
    have hct : c / t = |chronologicalHarmonicCharge a N / t| := by
      rw [abs_div, abs_of_pos ht0]
    rw [hct]
    have : chronologicalHarmonicCharge a N / t =
        r t - Real.exp (-t) + chronologicalBoseSum a N t := by rw [hr, hdec]; ring
    rw [this]
    calc |r t - Real.exp (-t) + chronologicalBoseSum a N t|
        ≤ |r t| + Real.exp (-t) + |chronologicalBoseSum a N t| := by
          have h1 := abs_add_le (r t - Real.exp (-t)) (chronologicalBoseSum a N t)
          have h2 := abs_sub (r t) (Real.exp (-t))
          rw [abs_of_pos (Real.exp_pos (-t))] at h2
          linarith
      _ ≤ |r t| + Real.exp (-T) + 4 * C * Real.exp (-T) := by linarith
      _ = |r t| + (1 + 4 * C) * Real.exp (-T) := by ring
  -- integrate against `dt/t` on `(T, 2T]`
  have hint_lhs : (∫ t in Ioc T (2 * T), c / t ^ 2) = c / (2 * T) := by
    have : (fun t : ℝ => c / t ^ 2) = fun t => c * (1 / t ^ 2) := by ext t; ring
    rw [this, integral_const_mul, integral_Ioc_one_div_sq hT0]; ring
  -- Cauchy–Schwarz for the `|r|/t` term
  have hrIoc : MemLp r 2 (volume.restrict (Ioc T (2 * T))) :=
    hrm.mono_measure (Measure.restrict_mono (fun x hx => hT0.trans hx.1) le_rfl)
  have hinvm : MemLp (fun t : ℝ => 1 / t) 2 (volume.restrict (Ioc T (2 * T))) := by
    refine MemLp.of_bound (C := 1 / T) ?_ ?_
    · exact (measurable_const.div measurable_id).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := hT0.trans ht.1
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le hT0 ht.1.le
  have hcs := abs_integral_mul_le_sqrt_mul_sqrt (μ := volume.restrict (Ioc T (2 * T)))
    (f := fun t => |r t|) (g := fun t => 1 / t) hrIoc.abs hinvm
  have hsqr : (∫ t in Ioc T (2 * T), |r t| ^ 2) ≤ ∫ t in Ioi (0 : ℝ), r t ^ 2 := by
    have : (fun t => |r t| ^ 2) = fun t => r t ^ 2 := by ext t; rw [sq_abs]
    rw [this]
    exact setIntegral_mono_set hrm.integrable_sq (Eventually.of_forall fun t => sq_nonneg _)
      (Eventually.of_forall fun x hx => hT0.trans hx.1)
  have hsqinv : (∫ t in Ioc T (2 * T), (1 / t) ^ 2) = 1 / (2 * T) := by
    have : (fun t : ℝ => (1 / t) ^ 2) = fun t => 1 / t ^ 2 := by ext t; ring
    rw [this, integral_Ioc_one_div_sq hT0]
  have hmid : (∫ t in Ioc T (2 * T), |r t| * (1 / t)) ≤ E * Real.sqrt (1 / (2 * T)) := by
    have h1 := le_abs_self (∫ t in Ioc T (2 * T), |r t| * (1 / t))
    refine h1.trans (hcs.trans ?_)
    rw [hsqinv]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    rw [hE, chronologicalL2Norm_eq_sqrt hrm.1]
    exact Real.sqrt_le_sqrt hsqr
  -- assemble
  have hrint : IntegrableOn (fun t => |r t| * (1 / t)) (Ioc T (2 * T)) :=
    hrIoc.abs.integrable_mul hinvm
  have hconst : IntegrableOn (fun _t : ℝ => (1 + 4 * C) * Real.exp (-T) * (1 / T)) (Ioc T (2 * T)) :=
    continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hle : (∫ t in Ioc T (2 * T), c / t ^ 2) ≤
      ∫ t in Ioc T (2 * T), (|r t| * (1 / t) + (1 + 4 * C) * Real.exp (-T) * (1 / T)) := by
    refine setIntegral_mono_on ?_ (hrint.add hconst) measurableSet_Ioc fun t ht => ?_
    · apply ContinuousOn.integrableOn_Icc (ContinuousOn.div continuousOn_const (continuousOn_pow 2)
        fun x hx => by have : 0 < x := hT0.trans_le hx.1; positivity) |>.mono_set Ioc_subset_Icc_self
    · have ht0 : 0 < t := hT0.trans ht.1
      have h := hpt t ht
      have hinv : 1 / t ≤ 1 / T := one_div_le_one_div_of_le hT0 ht.1.le
      have hpos : 0 ≤ (1 + 4 * C) * Real.exp (-T) := by positivity
      calc c / t ^ 2 = (c / t) * (1 / t) := by field_simp
        _ ≤ (|r t| + (1 + 4 * C) * Real.exp (-T)) * (1 / t) :=
            mul_le_mul_of_nonneg_right h (by positivity)
        _ = |r t| * (1 / t) + (1 + 4 * C) * Real.exp (-T) * (1 / t) := by ring
        _ ≤ |r t| * (1 / t) + (1 + 4 * C) * Real.exp (-T) * (1 / T) := by
            have := mul_le_mul_of_nonneg_left hinv hpos; linarith
  rw [hint_lhs, integral_add hrint hconst, setIntegral_const, Real.volume_real_Ioc_of_le h2T] at hle
  simp only [smul_eq_mul] at hle
  have hstep : c ≤ 2 * T * (E * Real.sqrt (1 / (2 * T))) +
      2 * T * ((2 * T - T) * ((1 + 4 * C) * Real.exp (-T) * (1 / T))) := by
    have := mul_le_mul_of_nonneg_left (hle.trans (add_le_add hmid le_rfl)) (by positivity : 0 ≤ 2 * T)
    rw [mul_div_cancel₀ _ (by positivity : (2 * T) ≠ 0)] at this
    linarith
  have h2 : 2 * T * (E * Real.sqrt (1 / (2 * T))) = Real.sqrt (2 * T) * E := by
    have hs : 0 < Real.sqrt (2 * T) := Real.sqrt_pos.mpr (by positivity)
    have hsq := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 * T)
    rw [one_div, Real.sqrt_inv]
    calc 2 * T * (E * (Real.sqrt (2 * T))⁻¹)
        = (Real.sqrt (2 * T) * Real.sqrt (2 * T)) * (E * (Real.sqrt (2 * T))⁻¹) := by rw [hsq]
      _ = Real.sqrt (2 * T) * E := by field_simp
  have h3 : 2 * T * ((2 * T - T) * ((1 + 4 * C) * Real.exp (-T) * (1 / T))) =
      2 * T * ((1 + 4 * C) * Real.exp (-T)) := by
    field_simp; ring
  linarith

/-- **Sharp off-line bound.**  At a zero with `½ < σ < 1`, every row bounded by `C` satisfies, for
`U ≥ 1`, `‖Γ(s)‖ ≤ ‖r‖ U^{σ-½}(1/√(2σ-1) + √2/(1-σ)) + (1+4C)e^{-U}(1 + 2U^σ/(1-σ))`. -/
theorem norm_Gamma_le_chronological_offLine_sharp (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C)
    {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 1) (hz : riemannZeta s = 0)
    {U : ℝ} (hU : 1 ≤ U) :
    ‖Complex.Gamma s‖ ≤
      chronologicalL2Norm (chronologicalHeatError a N) *
          (U ^ (s.re - 1 / 2) * (1 / Real.sqrt (2 * s.re - 1) + Real.sqrt 2 / (1 - s.re))) +
        (1 + 4 * C) * Real.exp (-U) * (1 + 2 * U ^ s.re / (1 - s.re)) := by
  set σ := s.re with hσ
  set E := chronologicalL2Norm (chronologicalHeatError a N) with hE
  set c := |chronologicalHarmonicCharge a N| with hc
  have hU0 : 0 < U := by linarith
  have h1σ : 0 < 1 - σ := by linarith
  have h2σ : 0 < 2 * σ - 1 := by linarith
  have hE0 : 0 ≤ E := chronologicalL2Norm_nonneg _
  have hmain := norm_Gamma_le_chronological_offLine a N C hC ha hs1 hs2 hz hU
  have hcharge := abs_chronologicalHarmonicCharge_le_sqrt a N C hC ha hU
  rw [← hσ, ← hE] at hmain
  rw [← hE, ← hc] at hcharge
  have hV : U ^ (σ - 1 / 2) = Real.sqrt U * U ^ (σ - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hU0]; congr 1; ring
  have hK : Real.sqrt (U ^ (2 * σ - 1) / (2 * σ - 1)) =
      U ^ (σ - 1 / 2) * (1 / Real.sqrt (2 * σ - 1)) := by
    rw [Real.sqrt_div (Real.rpow_nonneg hU0.le _), Real.sqrt_eq_rpow (U ^ (2 * σ - 1)),
      ← Real.rpow_mul hU0.le]
    rw [show (2 * σ - 1) * (1 / 2) = σ - 1 / 2 by ring]; ring
  have hUs : U * U ^ (σ - 1) = U ^ σ := by
    rw [← Real.rpow_one_add' hU0.le (by linarith)]; congr 1; ring
  have hsq2 : Real.sqrt (2 * U) = Real.sqrt 2 * Real.sqrt U := Real.sqrt_mul (by norm_num) U
  have hpow0 : 0 ≤ U ^ (σ - 1) := Real.rpow_nonneg hU0.le _
  have hT : c * (U ^ (σ - 1) / (1 - σ)) ≤
      (Real.sqrt 2 * U ^ (σ - 1 / 2) * E + 2 * U ^ σ * ((1 + 4 * C) * Real.exp (-U))) /
        (1 - σ) := by
    have hfrac0 : 0 ≤ U ^ (σ - 1) / (1 - σ) := div_nonneg hpow0 h1σ.le
    calc c * (U ^ (σ - 1) / (1 - σ))
        ≤ (Real.sqrt (2 * U) * E + 2 * U * ((1 + 4 * C) * Real.exp (-U))) *
            (U ^ (σ - 1) / (1 - σ)) := mul_le_mul_of_nonneg_right hcharge hfrac0
      _ = _ := by
          rw [hsq2, hV]
          field_simp
          rw [← hUs]
          ring
  calc ‖Complex.Gamma s‖
      ≤ E * Real.sqrt (U ^ (2 * σ - 1) / (2 * σ - 1)) + c * (U ^ (σ - 1) / (1 - σ)) +
          (1 + 4 * C) * Real.exp (-U) := hmain
    _ ≤ E * Real.sqrt (U ^ (2 * σ - 1) / (2 * σ - 1)) +
          (Real.sqrt 2 * U ^ (σ - 1 / 2) * E + 2 * U ^ σ * ((1 + 4 * C) * Real.exp (-U))) /
            (1 - σ) + (1 + 4 * C) * Real.exp (-U) := by linarith
    _ = _ := by rw [hK]; field_simp; ring

/-- **Budget gap law.**  If every accuracy `ε > 0` is reached by a row with coefficients at most
`exp(ε^{-θ})`, then every zeta zero `s` with `½ < Re s < 1` satisfies `θ (Re s - ½) ≥ 1`. -/
theorem two_mul_re_sub_half_ge_of_chronological_budget {θ : ℝ} (hθ : 0 < θ)
    (hbudget : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : ℕ → ℝ,
      (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ Real.exp (ε ^ (-θ))) ∧
        chronologicalL2Norm (chronologicalHeatError a N) ≤ ε)
    {s : ℂ} (hz : riemannZeta s = 0) (hs1 : 1 / 2 < s.re) (hs2 : s.re < 1) :
    1 ≤ θ * (s.re - 1 / 2) := by
  set σ := s.re with hσ
  by_contra hlt
  push Not at hlt
  set p := 1 - θ * (σ - 1 / 2) with hp
  have hp0 : 0 < p := by linarith
  have h1σ : 0 < 1 - σ := by linarith
  have h2σ : 0 < 2 * σ - 1 := by linarith
  set G := ‖Complex.Gamma s‖ with hG
  have hG0 : 0 < G := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  set D := 1 / Real.sqrt (2 * σ - 1) + Real.sqrt 2 / (1 - σ) with hD
  have hD0 : 0 ≤ D := by positivity
  -- the right side tends to `0` as `ε → 0⁺`
  set f : ℝ → ℝ := fun ε => 2 ^ (σ - 1 / 2) * D * ε ^ p +
      5 * Real.exp (-(ε ^ (-θ))) + (10 * 2 ^ σ / (1 - σ)) *
        ((ε ^ (-θ)) ^ σ * Real.exp (-1 * ε ^ (-θ))) with hf
  have hx : Tendsto (fun ε : ℝ => ε ^ (-θ)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by linarith)
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ p) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 p (Or.inr hp0.le)).tendsto
      rw [Real.zero_rpow hp0.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ε : ℝ => Real.exp (-(ε ^ (-θ)))) (𝓝[>] 0) (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hx
    have h3 : Tendsto (fun ε : ℝ => (ε ^ (-θ)) ^ σ * Real.exp (-1 * ε ^ (-θ))) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero σ 1 one_pos).comp hx
    have := ((h1.const_mul (2 ^ (σ - 1 / 2) * D)).add (h2.const_mul 5)).add
      (h3.const_mul (10 * 2 ^ σ / (1 - σ)))
    simp only [mul_zero, add_zero] at this
    exact this
  obtain ⟨ε, hfε, hε0, hε1⟩ : ∃ ε, f ε < G ∧ 0 < ε ∧ ε < 1 := by
    obtain ⟨ε, h1, h2⟩ := ((hlim.eventually (gt_mem_nhds hG0)).and
      (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))).exists
    exact ⟨ε, h1, h2.1, h2.2⟩
  -- the budget row at accuracy `ε`
  obtain ⟨N, a, ha, hE⟩ := hbudget ε hε0
  set x := ε ^ (-θ) with hxdef
  have hx1 : 1 ≤ x := by
    rw [hxdef]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1.le (by linarith)
  set U := 2 * x with hU
  have hU1 : 1 ≤ U := by linarith
  have hC0 : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have hbound := norm_Gamma_le_chronological_offLine_sharp a N (Real.exp x) hC0 ha hs1 hs2 hz hU1
  rw [← hσ, ← hG, ← hD] at hbound
  set E := chronologicalL2Norm (chronologicalHeatError a N) with hEdef
  have hE0 : 0 ≤ E := chronologicalL2Norm_nonneg _
  -- first term
  have hUpow : U ^ (σ - 1 / 2) = 2 ^ (σ - 1 / 2) * ε ^ (-θ * (σ - 1 / 2)) := by
    rw [hU, Real.mul_rpow (by norm_num) (by positivity), hxdef, ← Real.rpow_mul hε0.le]
  have hterm1 : E * (U ^ (σ - 1 / 2) * D) ≤ 2 ^ (σ - 1 / 2) * D * ε ^ p := by
    rw [hUpow]
    have hε' : ε * ε ^ (-θ * (σ - 1 / 2)) = ε ^ p := by
      rw [hp, show 1 - θ * (σ - 1 / 2) = 1 + (-θ * (σ - 1 / 2)) by ring,
        Real.rpow_add hε0, Real.rpow_one]
    have hpos : 0 ≤ 2 ^ (σ - 1 / 2) * ε ^ (-θ * (σ - 1 / 2)) * D := by positivity
    calc E * (2 ^ (σ - 1 / 2) * ε ^ (-θ * (σ - 1 / 2)) * D)
        ≤ ε * (2 ^ (σ - 1 / 2) * ε ^ (-θ * (σ - 1 / 2)) * D) :=
          mul_le_mul_of_nonneg_right hE hpos
      _ = 2 ^ (σ - 1 / 2) * D * (ε * ε ^ (-θ * (σ - 1 / 2))) := by ring
      _ = 2 ^ (σ - 1 / 2) * D * ε ^ p := by rw [hε']
  -- second term
  have hexp : (1 + 4 * Real.exp x) * Real.exp (-U) ≤ 5 * Real.exp (-x) := by
    have h1 : 1 ≤ Real.exp x := Real.one_le_exp (by linarith)
    have hmul : Real.exp x * Real.exp (-U) = Real.exp (-x) := by
      rw [← Real.exp_add, hU]; congr 1; ring
    have hpos : 0 ≤ Real.exp (-U) := (Real.exp_pos _).le
    nlinarith [Real.exp_pos (-U)]
  have hUσ : U ^ σ = 2 ^ σ * x ^ σ := by
    rw [hU, Real.mul_rpow (by norm_num) (by linarith)]
  have hterm2 : (1 + 4 * Real.exp x) * Real.exp (-U) * (1 + 2 * U ^ σ / (1 - σ)) ≤
      5 * Real.exp (-x) + (10 * 2 ^ σ / (1 - σ)) * (x ^ σ * Real.exp (-1 * x)) := by
    have hnn : 0 ≤ 1 + 2 * U ^ σ / (1 - σ) := by
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ U by linarith) σ; positivity
    calc (1 + 4 * Real.exp x) * Real.exp (-U) * (1 + 2 * U ^ σ / (1 - σ))
        ≤ 5 * Real.exp (-x) * (1 + 2 * U ^ σ / (1 - σ)) := mul_le_mul_of_nonneg_right hexp hnn
      _ = 5 * Real.exp (-x) + (10 * 2 ^ σ / (1 - σ)) * (x ^ σ * Real.exp (-1 * x)) := by
          rw [hUσ, neg_one_mul]; field_simp; ring
  have hfval : f ε = 2 ^ (σ - 1 / 2) * D * ε ^ p + 5 * Real.exp (-x) +
      (10 * 2 ^ σ / (1 - σ)) * (x ^ σ * Real.exp (-1 * x)) := by
    rw [hf]
  have : G ≤ f ε := by
    rw [hfval]
    calc G ≤ E * (U ^ (σ - 1 / 2) * D) +
          (1 + 4 * Real.exp x) * Real.exp (-U) * (1 + 2 * U ^ σ / (1 - σ)) := hbound
      _ ≤ _ := by linarith
  linarith

/-- **Budgets below `exp(ε^{-2})` force RH.**  If every accuracy `ε > 0` is reached by a row with
coefficients at most `exp(ε^{-θ})` for one `θ ≤ 2`, then RH holds. -/
theorem riemannHypothesis_of_chronological_budget_le_two {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ ≤ 2)
    (hbudget : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : ℕ → ℝ,
      (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ Real.exp (ε ^ (-θ))) ∧
        chronologicalL2Norm (chronologicalHeatError a N) ≤ ε) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hxi
  have hs1 : 1 / 2 < s.re := hs
  have hsne : s ≠ 1 := by
    rintro rfl; rw [xi_one] at hxi; norm_num at hxi
  have hz : riemannZeta s = 0 := (xi_eq_zero_iff (by linarith) hsne).mp hxi
  by_cases hs2 : s.re < 1
  · have h := two_mul_re_sub_half_ge_of_chronological_budget hθ hbudget hz hs1 hs2
    have : θ * (s.re - 1 / 2) < 1 := by nlinarith
    linarith
  · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hs2) hz

end RHTower

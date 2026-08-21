import Mathlib

/-!
# The analytic core of Connes' local trace formula (Theorem V.3)

Formalization of the estimate (31)-(33) inside the proof of Theorem 3 of §V of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Theorem V.3 states that for a local field `K` with basic character `α` and `h ∈ 𝒮(K^*)` compactly
supported, the cut-off trace satisfies

  `Trace (R_Λ U(h)) = 2 h(1) log' Λ + ∫' h(u^{-1}) |1-u|^{-1} d^*u + o(1)`.

Its proof computes the symbol `σ(x,ξ) = ρ^{-1} ĝ(xξ)` of `U(h)`, with
`g(λ) = h((λ+1)^{-1})|λ+1|^{-1} ∈ C_c^∞(K)` (proved in `ConnesSymbolChart`), rewrites

  `Trace (R_Λ T) = ρ^{-1} ∫_{|x| ≤ Λ, |ξ| ≤ Λ} ĝ(xξ) dx dξ`                        (29)
                `= ∫_{|u| ≤ Λ²} ĝ(u)(2 log' Λ - log|u|) du`                        (31)
                `= 2 g(0) log' Λ - ∫ ĝ(u) log|u| du + o(1)`,                        (33)

the last step because the tails (32) are `O(Λ^{-N})`, and finishes with the Fourier transform of
`-log|u|` (Appendix II (32), proved in `ConnesGaussianLogMoment`) and Parseval.

This file proves the limit step (31) ⟶ (33) unconditionally for `ĝ` in the Schwartz class — which
is exactly where `g ∈ C_c^∞` is used — together with the two tail estimates it rests on:

* `connes_schwartz_tail_bound` - the `O(R^{-k})` decay of the tail mass of a Schwartz function.
* `connes_schwartz_integrable_log` - a Schwartz function is integrable against `log |u|`.
* `connes_traceCore_tendsto` - the statement (31) ⟶ (33).
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Set Real Filter Topology SchwartzMap

/-- Schwartz tail bound: the mass beyond radius `R` decays like `R^{-k}`. -/
theorem connes_schwartz_tail_bound (G : SchwartzMap ℝ ℂ) (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ∫ u in {u : ℝ | R < |u|}, ‖G u‖ ≤ (R ^ k)⁻¹ * ∫ u : ℝ, ‖u‖ ^ k * ‖G u‖ := by
  have hmeasS : MeasurableSet {u : ℝ | R < |u|} :=
    measurableSet_lt measurable_const measurable_norm
  have hint : Integrable (fun u : ℝ => ‖u‖ ^ k * ‖G u‖) :=
    SchwartzMap.integrable_pow_mul (volume : Measure ℝ) G k
  have hIG : Integrable (fun u : ℝ => ‖G u‖) := G.integrable.norm
  have hstep : ∫ u in {u : ℝ | R < |u|}, ‖G u‖
      ≤ ∫ u in {u : ℝ | R < |u|}, (R ^ k)⁻¹ * (‖u‖ ^ k * ‖G u‖) := by
    refine setIntegral_mono_on hIG.integrableOn ((hint.const_mul _).integrableOn) hmeasS ?_
    intro u hu
    have hu' : R < |u| := hu
    have hpow : R ^ k ≤ ‖u‖ ^ k := by
      refine pow_le_pow_left₀ hR.le ?_ k
      simpa [Real.norm_eq_abs] using hu'.le
    have hRk : (0:ℝ) < R ^ k := by positivity
    rw [← mul_assoc]
    have hle : (1:ℝ) ≤ (R ^ k)⁻¹ * ‖u‖ ^ k := by
      rw [le_inv_mul_iff₀ hRk, mul_one]
      exact hpow
    nlinarith [norm_nonneg (G u), hle]
  refine hstep.trans ?_
  rw [integral_const_mul]
  have hnn : ∀ u : ℝ, 0 ≤ ‖u‖ ^ k * ‖G u‖ := fun u => by positivity
  have hmono : ∫ u in {u : ℝ | R < |u|}, ‖u‖ ^ k * ‖G u‖ ≤ ∫ u : ℝ, ‖u‖ ^ k * ‖G u‖ :=
    setIntegral_le_integral hint (by filter_upwards with u using hnn u)
  have hRkinv : (0:ℝ) ≤ (R ^ k)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hmono hRkinv

/-- A Schwartz function is integrable against `log |u|`. -/
theorem connes_schwartz_integrable_log (G : SchwartzMap ℝ ℂ) :
    Integrable (fun u : ℝ => G u * ((Real.log |u| : ℝ) : ℂ)) := by
  set M : ℝ := (SchwartzMap.seminorm ℝ 0 0) G with hM
  have hMbound : ∀ u : ℝ, ‖G u‖ ≤ M := fun u => SchwartzMap.norm_le_seminorm ℝ G u
  have hlogInt : IntegrableOn (fun u : ℝ => abs (Real.log |u|)) (Icc (-1:ℝ) 1) := by
    have h : IntervalIntegrable (fun u : ℝ => Real.log |u|) volume (-1) 1 := by
      have h1 : IntervalIntegrable (fun u : ℝ => Real.log u) volume (-1) 1 :=
        intervalIntegral.intervalIntegrable_log'
      refine h1.congr ?_
      intro u hu
      exact (Real.log_abs u).symm
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at h
    exact h.norm.congr (by filter_upwards with u using rfl)
  have hbound : Integrable (fun u : ℝ =>
      M * Set.indicator (Icc (-1:ℝ) 1) (fun u : ℝ => abs (Real.log |u|)) u
        + ‖u‖ * ‖G u‖) := by
    refine Integrable.add ?_ (SchwartzMap.integrable_pow_mul (volume : Measure ℝ) G 1
      |>.congr (by filter_upwards with u using by rw [pow_one]))
    have hind : Integrable (Set.indicator (Icc (-1:ℝ) 1) (fun u : ℝ => abs (Real.log |u|))) := by
      rw [← integrableOn_univ, integrableOn_indicator_iff measurableSet_Icc]
      simpa using hlogInt
    exact hind.const_mul M
  refine Integrable.mono' hbound ?_ ?_
  · exact G.continuous.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
        ((measurable_norm.log).aestronglyMeasurable))
  · filter_upwards with u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hu : u ∈ Icc (-1:ℝ) 1
    · rw [Set.indicator_of_mem hu]
      have h1 : ‖G u‖ * abs (Real.log |u|) ≤ M * abs (Real.log |u|) :=
        mul_le_mul_of_nonneg_right (hMbound u) (abs_nonneg _)
      have h2 : (0:ℝ) ≤ ‖u‖ * ‖G u‖ := by positivity
      linarith
    · rw [Set.indicator_of_notMem hu, mul_zero, zero_add]
      have hu1 : 1 < |u| := by
        simp only [mem_Icc, not_and, not_le] at hu
        rcases le_or_gt u 0 with h | h
        · rcases lt_or_ge u (-1) with h' | h'
          · rw [abs_of_nonpos h]; linarith
          · exact absurd (hu h' ) (by push Not; linarith)
        · rw [abs_of_pos h]
          by_contra hc
          push Not at hc
          exact absurd (hu (by linarith)) (by push Not; linarith)
      have hlogle : abs (Real.log |u|) ≤ |u| := by
        rw [abs_of_nonneg (Real.log_nonneg (le_of_lt hu1))]
        have := Real.log_le_sub_one_of_pos (lt_trans one_pos hu1)
        linarith
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hlogle (norm_nonneg _) |>.trans
        (le_of_eq (mul_comm _ _))

/-- **Theorem V.3, (31) ⟶ (33).**  The cut-off symbol integral of `ĝ` converges to
`2 g(0) log' Λ - ∫ ĝ(u) log|u| du`: the two tail errors (32) vanish. -/
theorem connes_traceCore_tendsto (G : SchwartzMap ℝ ℂ) :
    Tendsto (fun Λ : ℝ =>
      (∫ u in {u : ℝ | |u| ≤ Λ ^ 2}, (G u) * (((2 * Real.log Λ - Real.log |u|) : ℝ) : ℂ))
        - (((2 * Real.log Λ : ℝ) : ℂ) * (∫ u : ℝ, G u)
            - ∫ u : ℝ, G u * ((Real.log |u| : ℝ) : ℂ)))
      atTop (𝓝 0) := by
  set C : ℝ := ∫ u : ℝ, ‖u‖ ^ 2 * ‖G u‖ with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact integral_nonneg (fun u => by positivity)
  have hGint : Integrable (fun u : ℝ => G u) := G.integrable
  have hGlog : Integrable (fun u : ℝ => G u * ((Real.log |u| : ℝ) : ℂ)) :=
    connes_schwartz_integrable_log G
  have hsq : Integrable (fun u : ℝ => ‖u‖ ^ 2 * ‖G u‖) :=
    SchwartzMap.integrable_pow_mul (volume : Measure ℝ) G 2
  have hbound : ∀ᶠ Λ : ℝ in atTop,
      ‖(∫ u in {u : ℝ | |u| ≤ Λ ^ 2}, (G u) * (((2 * Real.log Λ - Real.log |u|) : ℝ) : ℂ))
        - (((2 * Real.log Λ : ℝ) : ℂ) * (∫ u : ℝ, G u)
            - ∫ u : ℝ, G u * ((Real.log |u| : ℝ) : ℂ))‖
        ≤ 2 * |Real.log Λ| * ((Λ ^ 4)⁻¹ * C) + (Λ ^ 2)⁻¹ * C := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with Λ hΛ
    have hΛ0 : (0:ℝ) < Λ := lt_trans one_pos hΛ
    have hΛ2 : (1:ℝ) < Λ ^ 2 := by nlinarith
    set S : Set ℝ := {u : ℝ | |u| ≤ Λ ^ 2} with hS
    set T : Set ℝ := {u : ℝ | Λ ^ 2 < |u|} with hT
    have hSmeas : MeasurableSet S := measurableSet_le measurable_norm measurable_const
    have hTmeas : MeasurableSet T := measurableSet_lt measurable_const measurable_norm
    have hcompl : T = Sᶜ := by
      ext u; simp only [hS, hT, mem_setOf_eq, mem_compl_iff, not_le]
    -- split both integrals
    have hsplitG : (∫ u : ℝ, G u) = (∫ u in S, G u) + ∫ u in T, G u := by
      rw [hcompl, integral_add_compl hSmeas hGint]
    have hsplitL : (∫ u : ℝ, G u * ((Real.log |u| : ℝ) : ℂ))
        = (∫ u in S, G u * ((Real.log |u| : ℝ) : ℂ))
          + ∫ u in T, G u * ((Real.log |u| : ℝ) : ℂ) := by
      rw [hcompl, integral_add_compl hSmeas hGlog]
    have hexpand : (∫ u in S, (G u) * (((2 * Real.log Λ - Real.log |u|) : ℝ) : ℂ))
        = ((2 * Real.log Λ : ℝ) : ℂ) * (∫ u in S, G u)
          - ∫ u in S, G u * ((Real.log |u| : ℝ) : ℂ) := by
      have hpt : ∀ u : ℝ, (G u) * (((2 * Real.log Λ - Real.log |u|) : ℝ) : ℂ)
          = ((2 * Real.log Λ : ℝ) : ℂ) * G u - G u * ((Real.log |u| : ℝ) : ℂ) := by
        intro u; push_cast; ring
      simp only [hpt]
      rw [integral_sub ((hGint.integrableOn).const_mul _) (hGlog.integrableOn),
        integral_const_mul]
    have hkey : (∫ u in S, (G u) * (((2 * Real.log Λ - Real.log |u|) : ℝ) : ℂ))
        - (((2 * Real.log Λ : ℝ) : ℂ) * (∫ u : ℝ, G u)
            - ∫ u : ℝ, G u * ((Real.log |u| : ℝ) : ℂ))
        = -(((2 * Real.log Λ : ℝ) : ℂ) * ∫ u in T, G u)
          + ∫ u in T, G u * ((Real.log |u| : ℝ) : ℂ) := by
      rw [hexpand, hsplitG, hsplitL]
      ring
    rw [hkey]
    -- tail estimates
    have hT1 : ∫ u in T, ‖G u‖ ≤ (Λ ^ 4)⁻¹ * C := by
      have h := connes_schwartz_tail_bound G 2 (show (0:ℝ) < Λ ^ 2 by positivity)
      have hpow : ((Λ ^ 2) ^ 2 : ℝ) = Λ ^ 4 := by ring
      rwa [hpow] at h
    have hT2 : ∫ u in T, ‖G u‖ * abs (Real.log |u|) ≤ (Λ ^ 2)⁻¹ * C := by
      have hintT : IntegrableOn (fun u : ℝ => ‖G u‖ * abs (Real.log |u|)) T := by
        have := hGlog.norm.integrableOn (s := T)
        refine this.congr ?_
        filter_upwards with u
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hstep : ∫ u in T, ‖G u‖ * abs (Real.log |u|)
          ≤ ∫ u in T, (Λ ^ 2)⁻¹ * (‖u‖ ^ 2 * ‖G u‖) := by
        refine setIntegral_mono_on hintT ((hsq.const_mul _).integrableOn) hTmeas ?_
        intro u hu
        have hu' : Λ ^ 2 < |u| := hu
        have hu1 : (1:ℝ) < |u| := lt_trans hΛ2 hu'
        have hlog : abs (Real.log |u|) ≤ |u| := by
          rw [abs_of_nonneg (Real.log_nonneg (le_of_lt hu1))]
          have := Real.log_le_sub_one_of_pos (lt_trans one_pos hu1)
          linarith
        have hΛ2pos : (0:ℝ) < Λ ^ 2 := by positivity
        have habs : ‖u‖ = |u| := Real.norm_eq_abs u
        have hquot : |u| ≤ (Λ ^ 2)⁻¹ * ‖u‖ ^ 2 := by
          rw [habs, inv_mul_eq_div, le_div_iff₀ hΛ2pos]
          nlinarith [hu', abs_nonneg u]
        calc ‖G u‖ * abs (Real.log |u|) ≤ ‖G u‖ * |u| :=
              mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
          _ ≤ ‖G u‖ * ((Λ ^ 2)⁻¹ * ‖u‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hquot (norm_nonneg _)
          _ = (Λ ^ 2)⁻¹ * (‖u‖ ^ 2 * ‖G u‖) := by ring
      refine hstep.trans ?_
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact setIntegral_le_integral hsq (by filter_upwards with u using by positivity)
    have hn1 : ‖((2 * Real.log Λ : ℝ) : ℂ) * ∫ u in T, G u‖
        ≤ 2 * |Real.log Λ| * ((Λ ^ 4)⁻¹ * C) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have hnorm : ‖∫ u in T, G u‖ ≤ ∫ u in T, ‖G u‖ := norm_integral_le_integral_norm _
      exact mul_le_mul_of_nonneg_left (hnorm.trans hT1) (by positivity)
    have hn2 : ‖∫ u in T, G u * ((Real.log |u| : ℝ) : ℂ)‖ ≤ (Λ ^ 2)⁻¹ * C := by
      refine (norm_integral_le_integral_norm _).trans ?_
      have hcongr : ∫ u in T, ‖G u * ((Real.log |u| : ℝ) : ℂ)‖
          = ∫ u in T, ‖G u‖ * abs (Real.log |u|) := by
        refine setIntegral_congr_fun hTmeas fun u _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [hcongr]
      exact hT2
    calc ‖-(((2 * Real.log Λ : ℝ) : ℂ) * ∫ u in T, G u)
            + ∫ u in T, G u * ((Real.log |u| : ℝ) : ℂ)‖
        ≤ ‖((2 * Real.log Λ : ℝ) : ℂ) * ∫ u in T, G u‖
          + ‖∫ u in T, G u * ((Real.log |u| : ℝ) : ℂ)‖ := by
          simpa using norm_add_le (-(((2 * Real.log Λ : ℝ) : ℂ) * ∫ u in T, G u))
            (∫ u in T, G u * ((Real.log |u| : ℝ) : ℂ))
      _ ≤ 2 * |Real.log Λ| * ((Λ ^ 4)⁻¹ * C) + (Λ ^ 2)⁻¹ * C := add_le_add hn1 hn2
  have hBtend : Tendsto (fun Λ : ℝ => 2 * |Real.log Λ| * ((Λ ^ 4)⁻¹ * C) + (Λ ^ 2)⁻¹ * C)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun Λ : ℝ => 2 * |Real.log Λ| * ((Λ ^ 4)⁻¹ * C)) atTop (𝓝 0) := by
      have hlogpow : Tendsto (fun Λ : ℝ => |Real.log Λ| * (Λ ^ 4)⁻¹) atTop (𝓝 0) := by
        have h := isLittleO_log_rpow_atTop (r := (4:ℝ)) (by norm_num)
        have h2 : Tendsto (fun Λ : ℝ => Real.log Λ / Λ ^ (4:ℝ)) atTop (𝓝 0) :=
          h.tendsto_div_nhds_zero
        refine h2.congr' ?_
        filter_upwards [eventually_gt_atTop (1:ℝ)] with Λ hΛ
        rw [abs_of_nonneg (Real.log_nonneg (le_of_lt hΛ)),
          show (Λ:ℝ) ^ (4:ℝ) = Λ ^ (4:ℕ) by
            rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast],
          div_eq_mul_inv]
      have := (hlogpow.const_mul (2:ℝ)).mul_const C
      simpa using this.congr (fun Λ => by ring)
    have h2 : Tendsto (fun Λ : ℝ => (Λ ^ 2)⁻¹ * C) atTop (𝓝 0) := by
      have hinv : Tendsto (fun Λ : ℝ => (Λ ^ 2)⁻¹) atTop (𝓝 0) :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).inv_tendsto_atTop
      simpa using hinv.mul_const C
    simpa using h1.add h2
  refine squeeze_zero_norm' hbound hBtend

end

end GaloisForLFunctions.RHTower

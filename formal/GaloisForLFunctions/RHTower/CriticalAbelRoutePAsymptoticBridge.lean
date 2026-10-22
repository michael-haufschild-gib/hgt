import GaloisForLFunctions.RHTower.CriticalAbelSourceRealIntegral
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszResolventRHCriterion
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceFixedAmplitudeOscillation

/-!
# Critical Abel–Route P asymptotic source bridge

The terminal Abel source and Route P source are the same log-time Chebyshev orbit
up to a positive, exponentially decaying floor/Euler correction. The exact
bridge transfers Route P's unconditional fixed-amplitude two-sided oscillation
to the normalized terminal Abel source. It does not prove an RH-strength upper
bound or pay the growing-core signed covariance.
-/

open MeasureTheory Set Filter Topology
namespace RHTower

private theorem criticalAbel_sqrt_exp (h : ℝ) :
    Real.sqrt (Real.exp h) = Real.exp (h / 2) := by
  rw [← Real.exp_half]

theorem criticalContinuousAbel_exp_eq_log_integral
    {t : ℝ} (ht : 0 ≤ t) :
    2 * criticalContinuousAbel (Real.exp t) =
      ∫ h in (0 : ℝ)..t,
        Real.exp (h / 2) * psiDefect ⌊Real.exp h⌋₊ := by
  let g : ℝ → ℝ := fun y =>
    (Real.sqrt y / y) * psiDefect ⌊y⌋₊
  have himage : Real.exp '' Ioo (0 : ℝ) t = Ioo 1 (Real.exp t) := by
    simp only [Real.image_exp_Ioo, Real.exp_zero]
  have hchange :
      (∫ y in Real.exp '' Ioo (0 : ℝ) t, g y) =
        ∫ h in Ioo (0 : ℝ) t, |Real.exp h| • g (Real.exp h) := by
    exact integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioo
      (by intro h _hh; exact (Real.hasDerivAt_exp h).hasDerivWithinAt)
      (by intro a _ha b _hb hab; exact Real.exp_injective hab)
      g
  rw [himage] at hchange
  have hfun :
      (fun h : ℝ => |Real.exp h| • g (Real.exp h)) =
      fun h : ℝ => Real.exp (h / 2) * psiDefect ⌊Real.exp h⌋₊ := by
    funext h
    dsimp [g]
    rw [abs_of_pos (Real.exp_pos h), criticalAbel_sqrt_exp]
    have he : Real.exp h ≠ 0 := (Real.exp_pos h).ne'
    field_simp [he]
  rw [hfun] at hchange
  have hX : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hC := criticalContinuousAbel_eq_source_real_integral hX
  calc
    2 * criticalContinuousAbel (Real.exp t) =
        ∫ y in Ioo (1 : ℝ) (Real.exp t), g y := by
      rw [hC, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro y _hy
      dsimp [g]
      ring
    _ = ∫ h in Ioo (0 : ℝ) t,
          Real.exp (h / 2) * psiDefect ⌊Real.exp h⌋₊ := hchange
    _ = ∫ h in (0 : ℝ)..t,
          Real.exp (h / 2) * psiDefect ⌊Real.exp h⌋₊ := by
      rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]

end RHTower

namespace RHTower

private noncomputable def criticalAbelRoutePCorrection (h : ℝ) : ℝ :=
  Real.exp (h / 2) *
    (Real.exp h - (⌊Real.exp h⌋₊ : ℝ) +
      2 * Real.eulerMascheroniConstant)

private theorem criticalAbelRoutePCorrection_measurable :
    Measurable criticalAbelRoutePCorrection := by
  have hf : Measurable (fun h : ℝ => (⌊Real.exp h⌋₊ : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      Real.measurable_exp.nat_floor
  exact (Real.measurable_exp.comp (measurable_id.div_const 2)).mul
    ((Real.measurable_exp.sub hf).add_const _)

private theorem criticalAbelRoutePCorrection_intervalIntegrable
    {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable criticalAbelRoutePCorrection volume 0 t := by
  apply GaloisForLFunctions.RHTower.intervalIntegrable_of_bound_on
    criticalAbelRoutePCorrection_measurable ht
    (C := 3 * Real.exp (t / 2))
  intro h hh
  have he : (0 : ℝ) < Real.exp h := Real.exp_pos h
  have hfl : (⌊Real.exp h⌋₊ : ℝ) ≤ Real.exp h := Nat.floor_le he.le
  have hfl' : Real.exp h < (⌊Real.exp h⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hg0 : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  have hg1 : Real.eulerMascheroniConstant < 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  have hδ0 : 0 ≤ Real.exp h - (⌊Real.exp h⌋₊ : ℝ) +
      2 * Real.eulerMascheroniConstant := by linarith
  have hδ3 : Real.exp h - (⌊Real.exp h⌋₊ : ℝ) +
      2 * Real.eulerMascheroniConstant ≤ 3 := by linarith
  have hE : Real.exp (h / 2) ≤ Real.exp (t / 2) :=
    Real.exp_le_exp.mpr (by linarith [hh.2])
  dsimp [criticalAbelRoutePCorrection]
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hδ0)]
  calc
    Real.exp (h / 2) *
        (Real.exp h - (⌊Real.exp h⌋₊ : ℝ) +
          2 * Real.eulerMascheroniConstant) ≤
        Real.exp (h / 2) * 3 :=
      mul_le_mul_of_nonneg_left hδ3 (Real.exp_pos _).le
    _ ≤ Real.exp (t / 2) * 3 :=
      mul_le_mul_of_nonneg_right hE (by norm_num)
    _ = 3 * Real.exp (t / 2) := by ring

private theorem criticalAbel_routeP_density_eq (h : ℝ) :
    Real.exp (h / 2) * psiDefect ⌊Real.exp h⌋₊ =
      GaloisForLFunctions.RHTower.criticalMellinChebyshevRayDensity h +
        criticalAbelRoutePCorrection h := by
  have hP : GaloisForLFunctions.RHTower.criticalMellinChebyshevRayDensity h =
      Real.exp (h / 2) *
        (Chebyshev.psi (Real.exp h) - Real.exp h) := by
    rw [GaloisForLFunctions.RHTower.criticalMellinChebyshevRayDensity,
      GaloisForLFunctions.RHTower.criticalMellinNormalizedChebyshevError_eq_apertureError,
      criticalMellinChebyshevError_eq_exp]
    have he : Real.exp h * Real.exp (-h / 2) = Real.exp (h / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp h * ((Chebyshev.psi (Real.exp h) - Real.exp h) *
        Real.exp (-h / 2)) =
          (Real.exp h * Real.exp (-h / 2)) *
            (Chebyshev.psi (Real.exp h) - Real.exp h) := by ring
      _ = _ := by rw [he]
  rw [hP, criticalAbelRoutePCorrection, psiDefect,
    ← psi_eq_chebyshevPsi_floor]
  ring

theorem criticalAbel_routeP_exact_bridge {t : ℝ} (ht : 0 ≤ t) :
    2 * Real.exp (-t) * criticalContinuousAbel (Real.exp t) -
        routePSourceRay t =
      Real.exp (-t) *
        (2 / 3 + ∫ h in (0 : ℝ)..t, criticalAbelRoutePCorrection h) := by
  have habel := criticalContinuousAbel_exp_eq_log_integral ht
  have hP :
      (∫ h in (0 : ℝ)..t,
        Real.exp (h / 2) * psiDefect ⌊Real.exp h⌋₊) =
        GaloisForLFunctions.RHTower.unitRieszChebyshevRayIntegral t +
          ∫ h in (0 : ℝ)..t, criticalAbelRoutePCorrection h := by
    calc
      (∫ h in (0 : ℝ)..t,
        Real.exp (h / 2) * psiDefect ⌊Real.exp h⌋₊) =
          ∫ h in (0 : ℝ)..t,
            (GaloisForLFunctions.RHTower.criticalMellinChebyshevRayDensity h +
              criticalAbelRoutePCorrection h) :=
        intervalIntegral.integral_congr (fun h _ => criticalAbel_routeP_density_eq h)
      _ = (∫ h in (0 : ℝ)..t,
          GaloisForLFunctions.RHTower.criticalMellinChebyshevRayDensity h) +
          ∫ h in (0 : ℝ)..t, criticalAbelRoutePCorrection h :=
        intervalIntegral.integral_add
          (GaloisForLFunctions.RHTower.intervalIntegrable_criticalMellinChebyshevRayDensity 0 t)
          (criticalAbelRoutePCorrection_intervalIntegrable ht)
      _ = _ := rfl
  have hR : routePSourceRay t = Real.exp (-t) *
      (GaloisForLFunctions.RHTower.unitRieszChebyshevRayIntegral t - 2 / 3) := by
    rw [routePSourceRay,
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative,
      max_eq_right ht]
  calc
    2 * Real.exp (-t) * criticalContinuousAbel (Real.exp t) -
        routePSourceRay t =
      Real.exp (-t) * (2 * criticalContinuousAbel (Real.exp t)) -
        routePSourceRay t := by ring
    _ = Real.exp (-t) *
          (∫ h in (0 : ℝ)..t,
            Real.exp (h / 2) * psiDefect ⌊Real.exp h⌋₊) -
          routePSourceRay t := by rw [habel]
    _ = Real.exp (-t) *
          (GaloisForLFunctions.RHTower.unitRieszChebyshevRayIntegral t +
            ∫ h in (0 : ℝ)..t, criticalAbelRoutePCorrection h) -
          Real.exp (-t) *
            (GaloisForLFunctions.RHTower.unitRieszChebyshevRayIntegral t - 2 / 3) := by
        rw [hP, hR]
    _ = _ := by ring

private theorem criticalAbelRoutePCorrection_bounds (h : ℝ) :
    0 ≤ criticalAbelRoutePCorrection h ∧
      criticalAbelRoutePCorrection h ≤ 3 * Real.exp (h / 2) := by
  have he : 0 < Real.exp h := Real.exp_pos h
  have hfl : (⌊Real.exp h⌋₊ : ℝ) ≤ Real.exp h := Nat.floor_le he.le
  have hfl' : Real.exp h < (⌊Real.exp h⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hg0 := Real.one_half_lt_eulerMascheroniConstant
  have hg1 := Real.eulerMascheroniConstant_lt_two_thirds
  dsimp [criticalAbelRoutePCorrection]
  constructor
  · apply mul_nonneg (Real.exp_pos _).le
    linarith
  · have hδ : Real.exp h - (⌊Real.exp h⌋₊ : ℝ) +
        2 * Real.eulerMascheroniConstant ≤ 3 := by linarith
    nlinarith [Real.exp_pos (h / 2)]

private theorem criticalAbelRoutePCorrection_integral_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (∫ h in (0 : ℝ)..t, criticalAbelRoutePCorrection h) ∧
      (∫ h in (0 : ℝ)..t, criticalAbelRoutePCorrection h) ≤
        6 * (Real.exp (t / 2) - 1) := by
  have hE : IntervalIntegrable (fun h : ℝ => Real.exp (h / 2)) volume 0 t :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).intervalIntegrable 0 t
  have hE3 : IntervalIntegrable (fun h : ℝ => 3 * Real.exp (h / 2)) volume 0 t :=
    hE.const_mul 3
  have hEval : (∫ h in (0 : ℝ)..t, Real.exp (h / 2)) =
      2 * (Real.exp (t / 2) - 1) := by
    have hcomp := intervalIntegral.integral_comp_div (f := Real.exp)
      (a := (0 : ℝ)) (b := t) (c := (2 : ℝ))
      (by norm_num : (2 : ℝ) ≠ 0)
    simpa [smul_eq_mul, Real.exp_zero, integral_exp] using hcomp
  constructor
  · exact intervalIntegral.integral_nonneg ht
      (fun h _ => (criticalAbelRoutePCorrection_bounds h).1)
  · calc
      (∫ h in (0 : ℝ)..t, criticalAbelRoutePCorrection h) ≤
          ∫ h in (0 : ℝ)..t, 3 * Real.exp (h / 2) := by
        exact intervalIntegral.integral_mono_on ht
          (criticalAbelRoutePCorrection_intervalIntegrable ht) hE3
          (fun h _ => (criticalAbelRoutePCorrection_bounds h).2)
      _ = 6 * (Real.exp (t / 2) - 1) := by
        rw [intervalIntegral.integral_const_mul, hEval]
        ring

theorem criticalAbel_routeP_difference_le {t : ℝ} (ht : 0 ≤ t) :
    0 < 2 * Real.exp (-t) * criticalContinuousAbel (Real.exp t) -
        routePSourceRay t ∧
      2 * Real.exp (-t) * criticalContinuousAbel (Real.exp t) -
        routePSourceRay t ≤ (20 / 3) * Real.exp (-t / 2) := by
  rw [criticalAbel_routeP_exact_bridge ht]
  obtain ⟨hlo, hhi⟩ := criticalAbelRoutePCorrection_integral_bounds ht
  have he0 : 0 < Real.exp (-t) := Real.exp_pos _
  have he1 : 1 ≤ Real.exp (t / 2) := Real.one_le_exp (by linarith)
  have hmul : Real.exp (-t) * Real.exp (t / 2) = Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · exact mul_pos he0 (by linarith)
  · calc
      Real.exp (-t) *
          (2 / 3 + ∫ h in (0 : ℝ)..t, criticalAbelRoutePCorrection h) ≤
        Real.exp (-t) * (20 / 3 * Real.exp (t / 2)) := by
          apply mul_le_mul_of_nonneg_left _ he0.le
          nlinarith
      _ = (20 / 3) * Real.exp (-t / 2) := by
        calc
          Real.exp (-t) * (20 / 3 * Real.exp (t / 2)) =
              (20 / 3) * (Real.exp (-t) * Real.exp (t / 2)) := by ring
          _ = _ := by rw [hmul]

theorem criticalContinuousAbel_fixed_amplitude_two_sided :
    ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℝ,
      (∃ t : ℝ, T < t ∧
        δ < 2 * Real.exp (-t) * criticalContinuousAbel (Real.exp t)) ∧
      (∃ t : ℝ, T < t ∧
        2 * Real.exp (-t) * criticalContinuousAbel (Real.exp t) < -δ) := by
  obtain ⟨δ, hδ, hpm⟩ := exists_routePSource_fixed_amplitude_two_sided
  have he : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (𝓝 0) := by
    have hraw := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    change Tendsto (fun t : ℝ => Real.exp (-(t / 2))) atTop (𝓝 0) at hraw
    simpa only [neg_div] using hraw
  have hdecay : Tendsto (fun t : ℝ => (20 / 3) * Real.exp (-t / 2))
      atTop (𝓝 0) := by
    simpa using he.const_mul (20 / 3 : ℝ)
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.1
    (hdecay.eventually (eventually_lt_nhds (show 0 < δ / 2 by linarith)))
  refine ⟨δ / 2, by linarith, fun T => ?_⟩
  let U : ℝ := max T (max T0 0)
  have hUT : T ≤ U := le_max_left _ _
  have hU0 : 0 ≤ U := (le_max_right T0 0).trans (le_max_right T _)
  have hUT0 : T0 ≤ U := (le_max_left T0 0).trans (le_max_right T _)
  obtain ⟨tp, htpU, htpP⟩ := (hpm U).1
  obtain ⟨tn, htnU, htnP⟩ := (hpm U).2
  refine ⟨⟨tp, lt_of_le_of_lt hUT htpU, ?_⟩,
    ⟨tn, lt_of_le_of_lt hUT htnU, ?_⟩⟩
  · have hd := (criticalAbel_routeP_difference_le
        (le_trans hU0 htpU.le)).1
    linarith
  · have hd := (criticalAbel_routeP_difference_le
        (le_trans hU0 htnU.le)).2
    have hs := hT0 tn (le_trans hUT0 htnU.le)
    linarith

end RHTower

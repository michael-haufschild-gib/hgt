import GaloisForLFunctions.RHTower.PrimeLogZetaAbelPole
import GaloisForLFunctions.RHTower.ConnesCutoffTailDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The `L¹` mass of the cutoff excess against a Schwartz tail

§VII (48) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The second half of the Besov estimate needs `‖ε_Λ (C_{α,v} * η)‖₁ = O(Λ^{-N})`.  The cutoff
excess `ε_Λ(x) = (log|x| − log T)^+` vanishes below the threshold `T`, so the whole mass sits in
the tail, where a rapidly decreasing function is bounded by `S/x^m`.  The exact tail integral

  `∫_T^∞ (log x − log T) x^{-δ-1} dx = T^{-δ}/δ²`

(the substitution `x = T u` and the corpus's `∫_1^∞ u^{-δ-1} log u du = 1/δ²`) then gives decay
faster than every power of the threshold.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **The exact logarithmic-excess tail integral.**  `∫_T^∞ (log x − log T) x^{-δ-1} dx
= T^{-δ}/δ²`. -/
theorem connes_logExcess_tail_powerIntegral {T : ℝ} (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in Ioi T, (Real.log x - Real.log T) * x ^ (-δ - 1)) = T ^ (-δ) / δ ^ 2 := by
  set g : ℝ → ℝ := fun x => (Real.log x - Real.log T) * x ^ (-δ - 1) with hg
  have hcv := integral_comp_mul_left_Ioi g 1 hT
  rw [mul_one, smul_eq_mul] at hcv
  have hpt : ∀ u : ℝ, u ∈ Ioi (1 : ℝ) →
      g (T * u) = T ^ (-δ - 1) * (u ^ (-δ - 1) * Real.log u) := by
    intro u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
    have hlog : Real.log (T * u) = Real.log T + Real.log u :=
      Real.log_mul (ne_of_gt hT) (ne_of_gt hu0)
    have hpow : (T * u) ^ (-δ - 1) = T ^ (-δ - 1) * u ^ (-δ - 1) :=
      Real.mul_rpow hT.le hu0.le
    simp only [hg]
    rw [hlog, hpow]
    ring
  have hinner : (∫ u in Ioi (1 : ℝ), g (T * u))
      = T ^ (-δ - 1) * ∫ u in Ioi (1 : ℝ), u ^ (-δ - 1) * Real.log u := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi hpt
  rw [hinner, _root_.RHTower.integral_rpow_mul_log_Ioi_one hδ] at hcv
  have hTne : T ≠ 0 := ne_of_gt hT
  have hval : (∫ x in Ioi T, g x) = T * (T ^ (-δ - 1) * (1 / δ ^ 2)) := by
    rw [hcv, ← mul_assoc, mul_inv_cancel₀ hTne, one_mul]
  rw [hval]
  have hTpow : T * T ^ (-δ - 1) = T ^ (-δ) := by
    have h1 : T ^ (-δ) = T ^ ((1 : ℝ) + (-δ - 1)) := by congr 1; ring
    rw [h1, Real.rpow_add hT, Real.rpow_one]
  rw [← mul_assoc, hTpow]
  field_simp

/-- **§VII (48).**  The `L¹` mass of the logarithmic cutoff excess against a Schwartz tail decays
faster than every power of the threshold. -/
theorem connes_logExcess_schwartz_rapidDecay (η : SchwartzMap ℝ ℂ) (N : ℕ) :
    Tendsto (fun T : ℝ => T ^ N *
        ∫ x in Ioi T, (Real.log x - Real.log T) * ‖η x‖) atTop (𝓝 0) := by
  set m : ℕ := N + 2 with hm
  set S : ℝ := (SchwartzMap.seminorm ℂ m 0) η with hS
  have hS0 : (0 : ℝ) ≤ S := apply_nonneg _ η
  set δ : ℝ := (N : ℝ) + 1 with hδdef
  have hδ : (0 : ℝ) < δ := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    rw [hδdef]; linarith
  have hexp : -δ - 1 = -((m : ℕ) : ℝ) := by
    rw [hδdef, hm]
    push_cast
    ring
  have hbound : ∀ T : ℝ, 1 ≤ T →
      (∫ x in Ioi T, (Real.log x - Real.log T) * ‖η x‖) ≤ S * (T ^ (-δ) / δ ^ 2) := by
    intro T hT
    have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
    have hmajint : IntegrableOn
        (fun x : ℝ => S * ((Real.log x - Real.log T) * x ^ (-δ - 1))) (Ioi T) volume := by
      have hcomp : IntegrableOn
          (fun u : ℝ => (Real.log (T * u) - Real.log T) * (T * u) ^ (-δ - 1))
          (Ioi (1 : ℝ)) volume := by
        have hbase := _root_.RHTower.integrableOn_rpow_mul_log_Ioi_one hδ
        have hbase' : IntegrableOn
            (fun u : ℝ => T ^ (-δ - 1) * (u ^ (-δ - 1) * Real.log u)) (Ioi (1 : ℝ)) volume :=
          hbase.const_mul (T ^ (-δ - 1))
        refine MeasureTheory.IntegrableOn.congr_fun hbase' ?_ measurableSet_Ioi
        intro u hu
        have hu1 : (1 : ℝ) < u := hu
        have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
        have hlog : Real.log (T * u) = Real.log T + Real.log u :=
          Real.log_mul (ne_of_gt hT0) (ne_of_gt hu0)
        have hpow : (T * u) ^ (-δ - 1) = T ^ (-δ - 1) * u ^ (-δ - 1) :=
          Real.mul_rpow hT0.le hu0.le
        show T ^ (-δ - 1) * (u ^ (-δ - 1) * Real.log u)
          = (Real.log (T * u) - Real.log T) * (T * u) ^ (-δ - 1)
        rw [hlog, hpow]
        ring
      have hpos : IntegrableOn
          (fun x : ℝ => (Real.log x - Real.log T) * x ^ (-δ - 1)) (Ioi T) volume := by
        have h := (integrableOn_Ioi_comp_mul_left_iff
          (fun x : ℝ => (Real.log x - Real.log T) * x ^ (-δ - 1)) 1 hT0).mp hcomp
        rwa [mul_one] at h
      exact hpos.const_mul _
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi T)]
        fun x : ℝ => (Real.log x - Real.log T) * ‖η x‖ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxT : T < x := hx
      have hlognn : 0 ≤ Real.log x - Real.log T := by
        have := Real.log_le_log (by linarith) hxT.le
        linarith
      exact mul_nonneg hlognn (norm_nonneg _)
    have hle : (fun x : ℝ => (Real.log x - Real.log T) * ‖η x‖)
        ≤ᵐ[volume.restrict (Ioi T)]
        fun x : ℝ => S * ((Real.log x - Real.log T) * x ^ (-δ - 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxT : T < x := hx
      have hx0 : (0 : ℝ) < x := lt_trans hT0 hxT
      have hlognn : 0 ≤ Real.log x - Real.log T := by
        have := Real.log_le_log (by linarith) hxT.le
        linarith
      have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ η m x
      have hnorm : ‖η x‖ ≤ S * x ^ (-δ - 1) := by
        have hxabs : |x| = x := abs_of_pos hx0
        have hsem' : x ^ m * ‖η x‖ ≤ S := by
          have hz : ‖x‖ ^ m * ‖η x‖ ≤ S := hsem
          rwa [Real.norm_eq_abs, hxabs] at hz
        have hxm : (0 : ℝ) < x ^ m := pow_pos hx0 m
        rw [hexp, Real.rpow_neg hx0.le, Real.rpow_natCast, ← div_eq_mul_inv,
          le_div_iff₀ hxm]
        calc ‖η x‖ * x ^ m = x ^ m * ‖η x‖ := by ring
          _ ≤ S := hsem'
      calc (Real.log x - Real.log T) * ‖η x‖
          ≤ (Real.log x - Real.log T) * (S * x ^ (-δ - 1)) :=
            mul_le_mul_of_nonneg_left hnorm hlognn
        _ = S * ((Real.log x - Real.log T) * x ^ (-δ - 1)) := by ring
    refine le_trans (integral_mono_of_nonneg hnn hmajint hle) (le_of_eq ?_)
    rw [integral_const_mul, connes_logExcess_tail_powerIntegral hT0 hδ]
  have hlim : Tendsto (fun T : ℝ => T ^ N * (S * (T ^ (-δ) / δ ^ 2))) atTop (𝓝 0) := by
    have hrw : ∀ T : ℝ, 0 < T → T ^ N * (S * (T ^ (-δ) / δ ^ 2))
        = (S / δ ^ 2) * T ^ (-(1 : ℝ)) := by
      intro T hT
      rw [← Real.rpow_natCast T N, ← mul_assoc]
      rw [show S / δ ^ 2 * T ^ (-(1 : ℝ)) = (S / δ ^ 2) * T ^ (-(1 : ℝ)) from rfl]
      have hcomb : T ^ ((N : ℝ)) * T ^ (-δ) = T ^ (-(1 : ℝ)) := by
        rw [← Real.rpow_add hT]
        congr 1
        rw [hδdef]
        ring
      field_simp
      rw [mul_comm (T ^ ((N : ℝ))) S, mul_assoc, hcomb]
    have h0 : Tendsto (fun T : ℝ => T ^ (-(1 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have h1 : Tendsto (fun T : ℝ => (S / δ ^ 2) * T ^ (-(1 : ℝ))) atTop (𝓝 0) := by
      simpa using h0.const_mul (S / δ ^ 2)
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (hrw T hT).symm
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
    refine mul_nonneg (by positivity) ?_
    refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
    have hxT : T < x := hx
    have hlognn : 0 ≤ Real.log x - Real.log T := by
      have := Real.log_le_log (by linarith) hxT.le
      linarith
    exact mul_nonneg hlognn (norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
    exact mul_le_mul_of_nonneg_left (hbound T hT) (by positivity)

end

end GaloisForLFunctions.RHTower

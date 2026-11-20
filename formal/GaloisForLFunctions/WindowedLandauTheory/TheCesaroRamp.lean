import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.TaylorCoefficientsOfLaplaceTransforms

/-!
# The Cesàro ramp and its Laplace transform

For coefficients `a(n)` the Cesàro ramp is `R_a(y) = Σ_{1 ≤ n ≤ y} a(n)(y/n - 1)`. When the
Dirichlet series of `a` converges absolutely at `s` with `Re s > 1`,

```text
∫_0^∞ R_a(e^u) e^{-su} du = L(a, s) / (s(s - 1))      (`integral_cesaroRamp_exp_mul`).
```

In the variable `u = log y` the ramp is a series of steps `a(n)(e^u/n - 1)` switched on at
`u = log n`; each step has transform `a(n) n^{-s}(1/(s-1) - 1/s)`, and the steps are integrated
termwise by absolute convergence. The linear corrections have transforms
`∫_0^∞ e^u e^{-su} du = 1/(s-1)` and `∫_0^∞ u e^u e^{-su} du = 1/(s-1)^2`.
-/

open MeasureTheory Set Complex Filter Topology

namespace WindowedLandauTheory

noncomputable section

/-- The Cesàro ramp `R_a(y) = Σ_{1 ≤ n ≤ y} a(n)(y/n - 1)`. -/
def cesaroRamp (a : ℕ → ℂ) (y : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * ((y : ℂ) / n - 1)

/-- One step of the ramp in the variable `u = log y`: `a(n)(e^u/n - 1)` for `u ≥ log n`. -/
def rampStep (a : ℕ → ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  if n = 0 then 0 else (Ici (Real.log n)).indicator (fun t : ℝ => a n * (cexp t / n - 1)) u

theorem cesaroRamp_exp_eq_tsum (a : ℕ → ℂ) (u : ℝ) :
    cesaroRamp a (Real.exp u) = ∑' n : ℕ, rampStep a n u := by
  classical
  unfold cesaroRamp
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp u⌋₊)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hle : (n : ℝ) ≤ Real.exp u :=
      le_trans (by exact_mod_cast hn.2) (Nat.floor_le (Real.exp_pos u).le)
    have hlog : Real.log n ≤ u := by
      rw [Real.log_le_iff_le_exp (by linarith)]
      exact hle
    rw [rampStep, if_neg hn0, Set.indicator_of_mem (show u ∈ Ici (Real.log n) from hlog),
      Complex.ofReal_exp]
  · intro n hn
    rw [Finset.mem_Icc, not_and_or] at hn
    by_cases hn0 : n = 0
    · rw [rampStep, if_pos hn0]
    · rw [rampStep, if_neg hn0]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      rcases hn with h | h
      · exact absurd hn1 h
      · have hgt : Real.exp u < n := by
          by_contra hle
          exact h (Nat.le_floor (le_of_not_gt hle))
        have hlog : u < Real.log n := by
          rw [Real.lt_log_iff_exp_lt (by exact_mod_cast hn1)]
          exact hgt
        exact Set.indicator_of_notMem (fun h' : u ∈ Ici (Real.log n) => by
          simp only [Set.mem_Ici] at h'
          linarith) _

theorem rampStep_mul_eq_indicator (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (s : ℂ) (u : ℝ) :
    rampStep a n u * cexp (-s * u) = (Ici (Real.log n)).indicator
      (fun t : ℝ => a n * ((cexp t / n - 1) * cexp (-s * t))) u := by
  rw [rampStep, if_neg hn]
  by_cases hu : u ∈ Ici (Real.log n)
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, mul_assoc]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]

/-- Integrals over `Ioi 0 ∩ Ici (log n)` are integrals over `Ioi (log n)`, as `log n ≥ 0`. -/
theorem setIntegral_Ioi_inter_Ici_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {n : ℕ} (hn : 1 ≤ n) :
    ∫ u in Ioi (0 : ℝ) ∩ Ici (Real.log n), f u = ∫ u in Ioi (Real.log n), f u := by
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rcases eq_or_lt_of_le hlog0 with h0 | hpos
  · rw [← h0, Set.inter_eq_left.mpr Set.Ioi_subset_Ici_self]
  · rw [Set.inter_eq_right.mpr (fun t ht => lt_of_lt_of_le hpos ht),
      integral_Ici_eq_integral_Ioi]

/-- `∫_{log n}^∞ (e^u/n - 1) e^{-su} du = n^{-s}/(s(s-1))` for `Re s > 1`. -/
theorem integral_rampStep_shape {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (Real.log n), (cexp u / n - 1) * cexp (-s * u) =
      (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by
    rw [sub_eq_zero.mp h, Complex.one_re] at hs
    linarith
  have hs1' : 1 - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  have ha1 : (1 - s).re < 0 := by simp; linarith
  have ha2 : (-s).re < 0 := by simp; linarith
  have hpt : ∀ u : ℝ, (cexp u / n - 1) * cexp (-s * u) =
      1 / (n : ℂ) * cexp ((1 - s) * u) - cexp (-s * u) := by
    intro u
    rw [show (1 - s) * (u : ℂ) = u + -s * u by ring, Complex.exp_add]
    ring
  simp_rw [hpt]
  rw [integral_sub ((integrableOn_exp_mul_complex_Ioi ha1 _).const_mul _)
      (integrableOn_exp_mul_complex_Ioi ha2 _), integral_const_mul,
    integral_exp_mul_complex_Ioi ha1, integral_exp_mul_complex_Ioi ha2]
  have hL : cexp (Real.log n) = n := by
    rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hn)]
    exact Complex.ofReal_natCast n
  have hlog : Complex.log n = (Real.log n : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]
  have hcpow : (n : ℂ) ^ (-s) = cexp (-s * Real.log n) := by
    rw [Complex.cpow_def_of_ne_zero hn0, hlog]
    congr 1
    ring
  rw [show (1 - s) * ((Real.log n : ℝ) : ℂ) = (Real.log n : ℂ) + -s * Real.log n by ring,
    Complex.exp_add, hL, ← hcpow]
  field_simp
  ring

/-- The real form: `∫_{log n}^∞ (e^u/n - 1) e^{-σu} du = n^{-σ}/(σ(σ-1))` for `σ > 1`. -/
theorem integral_rampStep_shape_real {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    ∫ u in Ioi (Real.log n), (Real.exp u / n - 1) * Real.exp (-σ * u) =
      (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hn0'.ne'
  have hσ0 : σ ≠ 0 := by linarith
  have hσ1 : σ - 1 ≠ 0 := by linarith
  have hσ1' : 1 - σ ≠ 0 := by linarith
  have hpt : ∀ u : ℝ, (Real.exp u / n - 1) * Real.exp (-σ * u) =
      1 / (n : ℝ) * Real.exp ((1 - σ) * u) - Real.exp (-σ * u) := by
    intro u
    rw [show (1 - σ) * u = u + -σ * u by ring, Real.exp_add]
    field_simp
  simp_rw [hpt]
  rw [integral_sub ((integrableOn_exp_mul_Ioi (by linarith) _).const_mul _)
      (integrableOn_exp_mul_Ioi (by linarith) _), integral_const_mul,
    integral_exp_mul_Ioi (by linarith), integral_exp_mul_Ioi (by linarith),
    show (1 - σ) * Real.log n = Real.log n + -σ * Real.log n by ring, Real.exp_add,
    Real.exp_log hn0',
    show Real.exp (-σ * Real.log n) = (n : ℝ) ^ (-σ) by
      rw [Real.rpow_def_of_pos hn0']
      congr 1
      ring]
  field_simp
  ring

/-- The transform of one step: `a(n) n^{-s} / (s(s-1))`. -/
theorem integral_rampStep_mul (a : ℕ → ℂ) (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), rampStep a n u * cexp (-s * u) = a n * (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : -s ≠ 0 := fun h => by
      rw [neg_eq_zero] at h
      rw [h, Complex.zero_re] at hs
      linarith
    simp [rampStep, Complex.zero_cpow hs0]
  · simp_rw [rampStep_mul_eq_indicator a hn.ne' s]
    rw [setIntegral_indicator measurableSet_Ici, setIntegral_Ioi_inter_Ici_log _ hn,
      integral_const_mul, integral_rampStep_shape hn hs, mul_div_assoc]

/-- The absolute transform of one step: `|a(n)| n^{-σ} / (σ(σ-1))` with `σ = Re s`. -/
theorem integral_norm_rampStep_mul (a : ℕ → ℂ) (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), ‖rampStep a n u * cexp (-s * u)‖ =
      ‖a n‖ * (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rampStep, Real.zero_rpow (by linarith : -s.re ≠ 0)]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have heq : ∀ u : ℝ, ‖rampStep a n u * cexp (-s * u)‖ = (Ici (Real.log n)).indicator
        (fun t : ℝ => ‖a n‖ * ((Real.exp t / n - 1) * Real.exp (-s.re * t))) u := by
      intro u
      rw [rampStep_mul_eq_indicator a hn.ne' s]
      by_cases hu : u ∈ Ici (Real.log n)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        have hle : 1 ≤ Real.exp u / n := by
          rw [le_div_iff₀ hn', one_mul, ← Real.exp_log hn']
          exact Real.exp_le_exp.mpr hu
        have e1 : cexp u / n - 1 = ((Real.exp u / n - 1 : ℝ) : ℂ) := by
          rw [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_exp, Complex.ofReal_natCast,
            Complex.ofReal_one]
        rw [norm_mul, norm_mul, e1, Complex.norm_real, Real.norm_of_nonneg (by linarith),
          Complex.norm_exp, show (-s * (u : ℂ)).re = -s.re * u by simp]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, norm_zero]
    simp_rw [heq]
    rw [setIntegral_indicator measurableSet_Ici, setIntegral_Ioi_inter_Ici_log _ hn,
      integral_const_mul, integral_rampStep_shape_real hn hs, mul_div_assoc]

theorem integrable_rampStep_mul (a : ℕ → ℂ) (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun u => rampStep a n u * cexp (-s * u)) (volume.restrict (Ioi (0 : ℝ))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rampStep]
  · have ha1 : (1 - s).re < 0 := by simp; linarith
    have ha2 : (-s).re < 0 := by simp; linarith
    have hf : IntegrableOn (fun t : ℝ => a n * ((cexp t / n - 1) * cexp (-s * t))) (Ioi 0) := by
      have h1 := ((integrableOn_exp_mul_complex_Ioi ha1 0).const_mul (1 / (n : ℂ))).sub
        (integrableOn_exp_mul_complex_Ioi ha2 0)
      refine (h1.const_mul (a n)).congr_fun (fun t _ => ?_) measurableSet_Ioi
      show a n * (1 / (n : ℂ) * cexp ((1 - s) * t) - cexp (-s * t)) = _
      rw [show (1 - s) * (t : ℂ) = t + -s * t by ring, Complex.exp_add]
      ring
    exact (hf.indicator measurableSet_Ici).congr
      (Eventually.of_forall fun u => (rampStep_mul_eq_indicator a hn.ne' s u).symm)

/-- **The Laplace transform of the Cesàro ramp.** For `Re s > 1` with `L(a, ·)` absolutely
convergent at `s`: `∫_0^∞ R_a(e^u) e^{-su} du = L(a, s)/(s(s-1))`. -/
theorem integral_cesaroRamp_exp_mul {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (ha : LSeriesSummable a s) :
    ∫ u in Ioi (0 : ℝ), cesaroRamp a (Real.exp u) * cexp (-s * u) =
      LSeries a s / (s * (s - 1)) := by
  have hs0' : -s ≠ 0 := fun h => by
    rw [neg_eq_zero] at h
    rw [h, Complex.zero_re] at hs
    linarith
  have hsum : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-s.re) := by
    refine (summable_norm_iff.mpr ha).congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (by linarith : -s.re ≠ 0)]
    · rw [if_neg hn.ne', Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hnorm : Summable fun n : ℕ => ∫ u in Ioi (0 : ℝ), ‖rampStep a n u * cexp (-s * u)‖ := by
    have e : (fun n : ℕ => ∫ u in Ioi (0 : ℝ), ‖rampStep a n u * cexp (-s * u)‖) =
        fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) :=
      funext fun n => integral_norm_rampStep_mul a n hs
    rw [e]
    exact hsum.div_const _
  have hpt : ∀ u : ℝ, cesaroRamp a (Real.exp u) * cexp (-s * u) =
      ∑' n : ℕ, rampStep a n u * cexp (-s * u) := fun u => by
    rw [cesaroRamp_exp_eq_tsum, tsum_mul_right]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u),
    ← integral_tsum_of_summable_integral_norm (fun n => integrable_rampStep_mul a n hs) hnorm,
    tsum_congr fun n => integral_rampStep_mul a n hs, tsum_div_const, LSeries]
  congr 1
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Complex.zero_cpow hs0']
  · rw [if_neg hn.ne', Complex.cpow_neg, div_eq_mul_inv]

/-- `∫_0^∞ e^u e^{-su} du = 1/(s-1)` for `Re s > 1`. -/
theorem integral_exp_mul_exp {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), cexp u * cexp (-s * u) = 1 / (s - 1) := by
  have h1 : (1 - s).re < 0 := by simp; linarith
  have hpt : ∀ u : ℝ, cexp u * cexp (-s * u) = cexp ((1 - s) * u) := fun u => by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_exp_mul_complex_Ioi h1, Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div,
    ← div_neg, neg_sub]

/-- `∫_0^∞ u e^u e^{-su} du = 1/(s-1)^2` for `Re s > 1`: differentiate `1/(s-1)` under the
integral. -/
theorem integral_mul_exp_mul_exp {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) * cexp u * cexp (-s * u) = 1 / (s - 1) ^ 2 := by
  have hg : AEStronglyMeasurable (fun u : ℝ => cexp u) (volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Continuous fun u : ℝ => cexp u).aestronglyMeasurable
  have hgC : ∀ u : ℝ, 0 < u → ‖cexp u‖ ≤ 1 * Real.exp (1 * u) := fun u _ => by
    rw [Complex.norm_exp, Complex.ofReal_re, one_mul, one_mul]
  have hF := hasDerivAt_laplaceTerm hg hgC 0 hs
  have hs1 : s - 1 ≠ 0 := fun h => by
    rw [sub_eq_zero.mp h, Complex.one_re] at hs
    linarith
  have heq : (fun z : ℂ => ∫ u in Ioi (0 : ℝ), cexp u * (-(u : ℂ)) ^ 0 * cexp (-z * u)) =ᶠ[𝓝 s]
      fun z => (z - 1)⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    simp only [pow_zero, mul_one]
    rw [integral_exp_mul_exp hz, one_div]
  have hG : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-1 / (s - 1) ^ 2) s :=
    ((hasDerivAt_id s).sub_const 1).inv hs1
  have huniq := hF.unique (hG.congr_of_eventuallyEq heq)
  have e : ∀ u : ℝ, cexp u * (-(u : ℂ)) ^ (0 + 1) * cexp (-s * u) =
      -((u : ℂ) * cexp u * cexp (-s * u)) := fun u => by ring
  simp_rw [e, integral_neg] at huniq
  rw [neg_div] at huniq
  exact neg_injective huniq

theorem measurable_cesaroRamp (a : ℕ → ℂ) : Measurable (cesaroRamp a) := by
  have e : cesaroRamp a = fun y : ℝ =>
      (y : ℂ) * (fun m : ℕ => ∑ n ∈ Finset.Icc 1 m, a n / n) ⌊y⌋₊ -
        (fun m : ℕ => ∑ n ∈ Finset.Icc 1 m, a n) ⌊y⌋₊ := by
    funext y
    simp only [cesaroRamp, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [e]
  exact (Complex.measurable_ofReal.mul ((measurable_from_nat
    (f := fun m : ℕ => ∑ n ∈ Finset.Icc 1 m, a n / n)).comp Nat.measurable_floor)).sub
    ((measurable_from_nat (f := fun m : ℕ => ∑ n ∈ Finset.Icc 1 m, a n)).comp Nat.measurable_floor)

/-- Growth of the ramp: `|R_a(y)| ≤ K y^2` when `|a(n)| ≤ K n`. -/
theorem norm_cesaroRamp_le {a : ℕ → ℂ} {K : ℝ} (ha : ∀ n, ‖a n‖ ≤ K * n) {y : ℝ} (hy : 0 ≤ y) :
    ‖cesaroRamp a y‖ ≤ K * y ^ 2 := by
  have hK : 0 ≤ K := by
    have := (norm_nonneg _).trans (ha 1)
    simpa using this
  unfold cesaroRamp
  calc ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * ((y : ℂ) / n - 1)‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖a n * ((y : ℂ) / n - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, K * y := Finset.sum_le_sum fun n hn => by
        rw [Finset.mem_Icc] at hn
        have hn1 : (0 : ℝ) < n := by exact_mod_cast hn.1
        have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le hy)
        have hge : 0 ≤ y / n - 1 := sub_nonneg.mpr ((one_le_div hn1).mpr hny)
        have e1 : (y : ℂ) / n - 1 = ((y / n - 1 : ℝ) : ℂ) := by
          rw [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_one]
        rw [norm_mul, e1, Complex.norm_real, Real.norm_of_nonneg hge]
        calc ‖a n‖ * (y / n - 1) ≤ K * n * (y / n) :=
              mul_le_mul (ha n) (by linarith) hge (mul_nonneg hK hn1.le)
          _ = K * y := by field_simp
    _ = ⌊y⌋₊ * (K * y) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ ≤ y * (K * y) := mul_le_mul_of_nonneg_right (Nat.floor_le hy) (mul_nonneg hK hy)
    _ = K * y ^ 2 := by ring

end

end WindowedLandauTheory

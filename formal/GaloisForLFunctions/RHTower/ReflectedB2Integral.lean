/-
The reflected block's `B₂` integral, bounded via its Fourier mode sum.

This assembles the whole reflected-block estimate: the periodic `B₂` kernel is written as its Fourier
series with `1/(4π²n²)` coefficients (`fourier_exp_hasSum`, from the circle expansion), sum and integral
are interchanged (`intervalIntegral_tsum`, justified by the `1/n²` decay through an `L¹` certificate),
and each mode's oscillatory integral is bounded uniformly in the frequency by the second-derivative van
der Corput test — giving `‖∫_1^N B₂(x)·x^{−s−2}‖ ≤ (∑ 1/(4π²n²))·10N/√(−s.im)`.
-/
import GaloisForLFunctions.RHTower.ReflectedModeSum
import GaloisForLFunctions.RHTower.SawtoothModeSum
import GaloisForLFunctions.RHTower.BernoulliFourierBridge

open Complex intervalIntegral MeasureTheory Real
open scoped Interval BigOperators ENNReal

noncomputable section

namespace RHTower

theorem fourier_eq_exp (n : ℤ) (x : ℝ) :
    (fourier n (↑x : AddCircle (1 : ℝ))) = Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I) := by
  rw [fourier_coe_apply]; congr 1; push_cast; ring

theorem fourier_exp_hasSum (x : ℝ) :
    HasSum (fun n : ℤ => ((1 / (4 * π ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ)
        * Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I))
      ((((Int.fract x) ^ 2 - Int.fract x) / 2 + 1 / 12 : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (fourier_hasSum_bernoulli2 x).mul_left ((1 / (4 * π ^ 2) : ℂ))
  have hfun : (fun n : ℤ => (1 / (4 * π ^ 2) : ℂ)
        * ((1 / (n : ℂ) ^ 2) * fourier n (↑x : AddCircle (1 : ℝ))))
      = fun n : ℤ => ((1 / (4 * π ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ)
          * Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I) := by
    ext n; rw [fourier_eq_exp]; push_cast; field_simp
  have hval : (1 / (4 * π ^ 2) : ℂ)
        * (2 * (π : ℂ) ^ 2 * (((Int.fract x) ^ 2 - Int.fract x + 6⁻¹ : ℝ) : ℂ))
      = (((Int.fract x) ^ 2 - Int.fract x) / 2 + 1 / 12 : ℝ) := by
    push_cast; field_simp; ring
  rw [← hval, ← hfun]; exact h

theorem reflected_B2_integral_bound {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : -2 ≤ s.re) (hτ : s.im < 0) :
    ‖∫ x in (1 : ℝ)..(N : ℝ),
        ((((Int.fract x) ^ 2 - Int.fract x) / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2)‖
      ≤ (∑' n : ℤ, 1 / (4 * π ^ 2 * (n : ℝ) ^ 2)) * (10 * (N : ℝ) / Real.sqrt (-s.im)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set cf : ℤ → ℝ := fun n => 1 / (4 * π ^ 2 * (n : ℝ) ^ 2) with hcf
  set f : ℤ → ℝ → ℂ := fun n x => ((cf n : ℝ) : ℂ)
    * Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I) * (x : ℂ) ^ (-s - 2) with hf
  have hcfnn : ∀ n, 0 ≤ cf n := fun n => by rw [hcf]; positivity
  have hc : Summable cf := by
    have h := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
    have heq : cf = fun n : ℤ => (1 / (4 * π ^ 2)) * (1 / (n : ℝ) ^ 2) := by
      ext n; rw [hcf, mul_one_div, div_div]
    rw [heq]; exact h.mul_left _
  have hpoint : ∀ x : ℝ, 0 < x →
      ((((Int.fract x) ^ 2 - Int.fract x) / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2)
        = ∑' n : ℤ, f n x := by
    intro x hx
    rw [← (fourier_exp_hasSum x).tsum_eq, hf, ← tsum_mul_right]
  have hnorm : ∀ n : ℤ, ∀ x ∈ Set.Ioc (1 : ℝ) (N : ℝ), ‖f n x‖ ≤ cf n := by
    intro n x hx
    have hxpos : 0 < x := by linarith [hx.1]
    rw [hf]
    simp only
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcfnn n),
      norm_cpow_eq_rpow_re_of_pos hxpos, Complex.norm_exp]
    have he1 : (((2 * π * (n : ℝ)) * x : ℝ) * I).re = 0 := by simp
    rw [he1, Real.exp_zero, mul_one]
    have hre : (-s - 2).re = -s.re - 2 := by simp
    rw [hre]
    have hxle : x ^ (-s.re - 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1]) (by linarith)
    nlinarith [hcfnn n, hxle]
  -- continuity / measurability of each mode integrand on [1,N]
  have hcont : ∀ n : ℤ, ContinuousOn (f n) (Set.Ioc (1 : ℝ) (N : ℝ)) := by
    intro n
    rw [hf]
    apply ContinuousOn.mul
    · exact continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn (by fun_prop)).mul continuousOn_const))
    · apply ContinuousOn.cpow_const (by fun_prop)
      intro x hx
      exact Or.inl (by simpa using (by linarith [hx.1] : (0:ℝ) < x))
  have hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Set.Ioc (1 : ℝ) (N : ℝ))) :=
    fun n => (hcont n).aestronglyMeasurable measurableSet_Ioc
  -- the L¹ summability certificate
  have hsum : ∑' n : ℤ, ∫⁻ x in Set.Ioc (1 : ℝ) (N : ℝ), ‖f n x‖ₑ ≠ ⊤ := by
    have hNsub : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
    have hbnd : ∀ n, (∫⁻ x in Set.Ioc (1 : ℝ) (N : ℝ), ‖f n x‖ₑ)
        ≤ ENNReal.ofReal (cf n * ((N : ℝ) - 1)) := by
      intro n
      calc (∫⁻ x in Set.Ioc (1 : ℝ) (N : ℝ), ‖f n x‖ₑ)
          ≤ ∫⁻ _x in Set.Ioc (1 : ℝ) (N : ℝ), ENNReal.ofReal (cf n) := by
            apply setLIntegral_mono' measurableSet_Ioc
            intro x hx
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hnorm n x hx)
        _ = ENNReal.ofReal (cf n) * volume (Set.Ioc (1 : ℝ) (N : ℝ)) := by
            rw [setLIntegral_const]
        _ = ENNReal.ofReal (cf n * ((N : ℝ) - 1)) := by
            rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (hcfnn n)]
    have hsummable : Summable (fun n => cf n * ((N : ℝ) - 1)) := hc.mul_right _
    apply ne_top_of_le_ne_top (b := ENNReal.ofReal (∑' n, cf n * ((N : ℝ) - 1)))
    · exact ENNReal.ofReal_ne_top
    · calc ∑' n : ℤ, ∫⁻ x in Set.Ioc (1 : ℝ) (N : ℝ), ‖f n x‖ₑ
          ≤ ∑' n, ENNReal.ofReal (cf n * ((N : ℝ) - 1)) := ENNReal.tsum_le_tsum hbnd
        _ = ENNReal.ofReal (∑' n, cf n * ((N : ℝ) - 1)) :=
            (ENNReal.ofReal_tsum_of_nonneg
              (fun n => mul_nonneg (hcfnn n) hNsub) hsummable).symm
  -- pull the constant out of each mode integral
  have hintf : ∀ n : ℤ, (∫ x in (1 : ℝ)..(N : ℝ), f n x)
      = ((cf n : ℝ) : ℂ) * ∫ x in (1 : ℝ)..(N : ℝ),
          (x : ℂ) ^ (-s - 2) * Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I) := by
    intro n
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    rw [hf]; simp only; ring
  -- rewrite the B₂ integral as the mode sum and apply the uniform bound
  have hcongr : (∫ x in (1 : ℝ)..(N : ℝ),
        ((((Int.fract x) ^ 2 - Int.fract x) / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2))
      = ∫ x in (1 : ℝ)..(N : ℝ), ∑' n : ℤ, f n x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hN1] at hx
    exact hpoint x (by linarith [hx.1])
  rw [hcongr, intervalIntegral_tsum hN1 hmeas hsum, tsum_congr hintf]
  exact reflected_mode_sum_bound hN hσ hτ

end RHTower

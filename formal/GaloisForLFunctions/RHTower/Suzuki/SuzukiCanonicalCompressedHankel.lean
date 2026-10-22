import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalArithmeticLocalL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Square-integrability of Suzuki's compressed multiplicative Hankel kernel

This file proves the literal two-variable analytic estimate used in Suzuki's Lemma 4.2.  For
`ω > 1/2`, the arithmetic kernel `hω` is locally square-integrable; after the multiplicative
substitution `(x,y) ↦ xy`, the compressed kernel `(x,y) ↦ hω(xy)` belongs to `L²((0,a]²)`.
-/

open ArithmeticFunction Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- Suzuki's incomplete-beta tail is pointwise real for all real parameters. -/
theorem conj_suzukiBetaTail (omega x : ℝ) :
    (starRingEnd ℂ) (suzukiBetaTail omega x) = suzukiBetaTail omega x := by
  rw [suzukiBetaTail, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht0 : 0 ≤ t := le_trans (sq_nonneg x) ht.1.le
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hexp : (omega : ℂ) - ((1 : ℝ) : ℂ) = ((omega - 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub]
  change (starRingEnd ℂ)
      ((t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
        (1 - (t : ℂ)) ^ ((omega : ℂ) - 1)) =
      (t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
        (1 - (t : ℂ)) ^ ((omega : ℂ) - 1)
  rw [map_mul,
    ← Complex.ofReal_cpow ht0 (1 / 2 - omega),
    ← Complex.ofReal_one, ← Complex.ofReal_sub, hexp,
    ← Complex.ofReal_cpow h1t (omega - 1)]
  simp

/-- Suzuki's literal source kernel `gω` is pointwise real, including its totalized endpoints. -/
theorem conj_suzukiSourceG (omega x : ℝ) :
    (starRingEnd ℂ) (suzukiSourceG omega x) = suzukiSourceG omega x := by
  by_cases hx : 0 < x ∧ x < 1
  · have hx0 : 0 ≤ x := hx.1.le
    have h1x2 : 0 ≤ 1 - x ^ (2 : ℕ) := by nlinarith
    have hexp : (omega : ℂ) - ((1 : ℝ) : ℂ) = ((omega - 1 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sub]
    rw [suzukiSourceG, if_pos hx,
      ← Complex.ofReal_cpow Real.pi_nonneg omega,
      Complex.Gamma_ofReal,
      ← Complex.ofReal_cpow hx0 (2 - omega),
      ← Complex.ofReal_pow,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, hexp,
      ← Complex.ofReal_cpow h1x2 (omega - 1),
      ← Complex.ofReal_cpow hx0 (omega - 1)]
    have hcoeff :
        (starRingEnd ℂ) (2 * ((Real.pi ^ omega : ℝ) : ℂ) / (Real.Gamma omega : ℂ)) =
          2 * ((Real.pi ^ omega : ℝ) : ℂ) / (Real.Gamma omega : ℂ) := by
      change star (2 * ((Real.pi ^ omega : ℝ) : ℂ) / (Real.Gamma omega : ℂ)) = _
      rw [star_div₀, star_mul]
      simp
      ring
    rw [map_mul, hcoeff, map_sub]
    simp only [map_mul, conj_ofReal, conj_suzukiBetaTail]
  · rw [suzukiSourceG, if_neg hx]
    simp

/-- The complete floor-truncated arithmetic kernel `hω` is pointwise real. -/
theorem conj_suzukiSourceHFinite (omega x : ℝ) :
    (starRingEnd ℂ) (suzukiSourceHFinite omega x) = suzukiSourceHFinite omega x := by
  by_cases hx : 1 < x
  · rw [suzukiSourceHFinite, if_pos hx, map_mul, map_sum]
    congr 1
    · simp
    apply Finset.sum_congr rfl
    intro n hn
    simp only [map_mul, conj_ofReal, conj_suzukiSourceG]
  · rw [suzukiSourceHFinite, if_neg hx]
    simp

/-- Pointwise Hermitian symmetry of Suzuki's literal compressed kernel. -/
theorem suzukiCompressedHankelKernel_conj_swap (omega x y : ℝ) :
    (starRingEnd ℂ) (suzukiSourceHFinite omega (y * x)) =
      suzukiSourceHFinite omega (x * y) := by
  rw [conj_suzukiSourceHFinite, mul_comm]

/-- For `0 < a ≤ 1`, Suzuki's compressed kernel vanishes pointwise on `(0,a]²`. -/
theorem suzukiCompressedHankelKernel_eq_zero_of_le_one
    {omega a x y : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hx : x ∈ Ioc 0 a) (hy : y ∈ Ioc 0 a) :
    suzukiSourceHFinite omega (x * y) = 0 := by
  rw [suzukiSourceHFinite, if_neg]
  exact not_lt_of_ge (by nlinarith [hx.1, hx.2, hy.1, hy.2])

/-- Every row of Suzuki's literal compressed multiplicative Hankel kernel has finite energy. -/
theorem integrableOn_sq_norm_suzukiCompressedHankelKernel_slice {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) {x : ℝ} (hx : x ∈ Ioc 0 a) :
    IntegrableOn (fun y : ℝ => ‖suzukiSourceHFinite omega (x * y)‖ ^ (2 : ℕ)) (Ioc 0 a) := by
  let q : ℝ → ℝ := fun u => ‖suzukiSourceHFinite omega u‖ ^ (2 : ℕ)
  have ha2 : 1 < a ^ (2 : ℕ) := by nlinarith
  have hH := memLp_suzukiSourceHFinite_local_two homega ha2
  have hq : IntegrableOn q (Ioc 1 (a ^ (2 : ℕ))) :=
    (memLp_two_iff_integrable_sq_norm (by
      have heq : suzukiSourceHFinite omega = suzukiSourceH omega := by
        funext u
        exact (suzukiSourceH_eq_finite omega u).symm
      rw [heq]
      exact (measurable_suzukiSourceH omega).aestronglyMeasurable)).mp hH
  by_cases hsmall : x * a ≤ 1
  · refine integrableOn_zero.congr_fun ?_ measurableSet_Ioc
    intro y hy
    dsimp only [q]
    symm
    rw [suzukiSourceHFinite, if_neg]
    · simp
    · exact not_lt_of_ge (le_trans (mul_le_mul_of_nonneg_left hy.2 hx.1.le) hsmall)
  · have hx0 : 0 < x := hx.1
    have hxa : 1 < x * a := lt_of_not_ge hsmall
    have hroot : 0 < 1 / x := one_div_pos.mpr hx0
    have hroota : 1 / x < a := (div_lt_iff₀ hx0).2 (by simpa [mul_comm] using hxa)
    have hzero : ∀ y ∈ Ioc (0 : ℝ) (1 / x), q (x * y) = 0 := by
      intro y hy
      dsimp only [q]
      rw [suzukiSourceHFinite, if_neg]
      · simp
      · have hyx : y * x ≤ 1 := (le_div_iff₀ hx0).1 hy.2
        exact not_lt_of_ge (by simpa [mul_comm] using hyx)
    have hqInt : IntervalIntegrable q volume 1 (a ^ (2 : ℕ)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha2.le).mpr hq
    have hxa2 : x * a ≤ a ^ (2 : ℕ) := by nlinarith [hx.2, ha]
    have hqShort : IntervalIntegrable q volume 1 (x * a) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hxa.le).mpr
        (hq.mono_set (Ioc_subset_Ioc le_rfl hxa2))
    have hcompInt : IntervalIntegrable (fun y => q (x * y)) volume (1 / x) a := by
      have hscaleInt := hqShort.comp_mul_left (c := x)
      convert hscaleInt using 1
      all_goals field_simp
    have hlowInt : IntervalIntegrable (fun y => q (x * y)) volume 0 (1 / x) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hroot.le]
      refine integrableOn_zero.congr_fun ?_ measurableSet_Ioc
      exact fun y hy => (hzero y hy).symm
    have hfull := hlowInt.trans hcompInt
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (le_trans zero_le_one ha.le)).mp hfull

/-- Uniform row-energy bound for Suzuki's literal compressed kernel on `(0,a]²`. -/
theorem exists_uniform_sq_norm_suzukiCompressedHankelKernel_slice_bound
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) :
    ∃ C : ℝ, ∀ x ∈ Ioc 0 a,
      ∫ y in Ioc 0 a, ‖suzukiSourceHFinite omega (x * y)‖ ^ (2 : ℕ) ≤ C := by
  let q : ℝ → ℝ := fun u => ‖suzukiSourceHFinite omega u‖ ^ (2 : ℕ)
  have ha2 : 1 < a ^ (2 : ℕ) := by nlinarith
  have hH := memLp_suzukiSourceHFinite_local_two homega ha2
  have hq : IntegrableOn q (Ioc 1 (a ^ (2 : ℕ))) :=
    (memLp_two_iff_integrable_sq_norm
      (by
        have heq : suzukiSourceHFinite omega = suzukiSourceH omega := by
          funext u
          exact (suzukiSourceH_eq_finite omega u).symm
        rw [heq]
        exact (measurable_suzukiSourceH omega).aestronglyMeasurable)).mp hH
  let C : ℝ := a * ∫ u in Ioc 1 (a ^ (2 : ℕ)), q u
  refine ⟨C, ?_⟩
  intro x hx
  by_cases hsmall : x * a ≤ 1
  · have hzero : ∀ y ∈ Ioc (0 : ℝ) a, q (x * y) = 0 := by
      intro y hy
      dsimp only [q]
      rw [suzukiSourceHFinite, if_neg]
      · simp
      · exact not_lt_of_ge (le_trans (mul_le_mul_of_nonneg_left hy.2 hx.1.le) hsmall)
    rw [setIntegral_congr_fun measurableSet_Ioc hzero]
    simp [C]
    exact mul_nonneg (le_trans zero_le_one ha.le) (integral_nonneg fun _ => sq_nonneg _)
  · have hx0 : 0 < x := hx.1
    have hxa : 1 < x * a := lt_of_not_ge hsmall
    have hroot : 0 < 1 / x := one_div_pos.mpr hx0
    have hroota : 1 / x < a := (div_lt_iff₀ hx0).2 (by simpa [mul_comm] using hxa)
    have hzero : ∀ y ∈ Ioc (0 : ℝ) (1 / x), q (x * y) = 0 := by
      intro y hy
      dsimp only [q]
      rw [suzukiSourceHFinite, if_neg]
      · simp
      · have hyx : y * x ≤ 1 := (le_div_iff₀ hx0).1 hy.2
        exact not_lt_of_ge (by simpa [mul_comm] using hyx)
    have hlow : ∫ y in (0 : ℝ)..(1 / x), q (x * y) = 0 := by
      rw [intervalIntegral.integral_of_le hroot.le,
        setIntegral_congr_fun measurableSet_Ioc hzero]
      simp
    have hqInt : IntervalIntegrable q volume 1 (a ^ (2 : ℕ)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha2.le).mpr hq
    have hxa2 : x * a ≤ a ^ (2 : ℕ) := by nlinarith [hx.2, ha]
    have hqShort : IntervalIntegrable q volume 1 (x * a) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hxa.le).mpr
        (hq.mono_set (Ioc_subset_Ioc le_rfl hxa2))
    have hcompInt : IntervalIntegrable (fun y => q (x * y)) volume (1 / x) a := by
      have hscaleInt := hqShort.comp_mul_left (c := x)
      convert hscaleInt using 1
      all_goals field_simp
    change (∫ y in Ioc (0 : ℝ) a, q (x * y)) ≤ C
    rw [← intervalIntegral.integral_of_le (le_trans zero_le_one ha.le)]
    calc
      (∫ y in (0 : ℝ)..a, q (x * y)) =
          ∫ y in (1 / x)..a, q (x * y) := by
            rw [← intervalIntegral.integral_add_adjacent_intervals
              (a := 0) (b := 1 / x) (c := a)
              (by
                rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hroot.le]
                refine integrableOn_zero.congr_fun ?_ measurableSet_Ioc
                exact fun y hy => (hzero y hy).symm)
              hcompInt, hlow, zero_add]
      _ = x⁻¹ * ∫ u in (1 : ℝ)..(x * a), q u := by
            have hident : x * (1 / x) = 1 := by field_simp
            simpa only [smul_eq_mul, hident] using
              (intervalIntegral.integral_comp_mul_left (a := 1 / x) (b := a)
                q hx0.ne')
      _ ≤ x⁻¹ * ∫ u in (1 : ℝ)..(a ^ (2 : ℕ)), q u := by
            gcongr
            exact intervalIntegral.integral_mono_interval le_rfl hxa.le hxa2
              (Filter.Eventually.of_forall fun _ => sq_nonneg _) hqInt
      _ ≤ a * ∫ u in (1 : ℝ)..(a ^ (2 : ℕ)), q u := by
            have hxinv : x⁻¹ < a := by
              simpa only [one_div] using hroota
            exact mul_le_mul_of_nonneg_right hxinv.le
              (intervalIntegral.integral_nonneg ha2.le (fun _ _ => sq_nonneg _))
      _ = C := by
            dsimp only [C]
            rw [intervalIntegral.integral_of_le ha2.le]

/-- Suzuki's literal kernel `(x,y) ↦ hω(xy)` is square-integrable on every compressed square
`(0,a]²` once `ω > 1/2`.  This is the analytic content behind the Hilbert--Schmidt half of
Suzuki's Lemma 4.2, before packaging the kernel as an operator on `L²(0,a)`. -/
theorem memLp_suzukiCompressedHankelKernel_two
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) :
    MemLp (fun p : ℝ × ℝ => suzukiSourceHFinite omega (p.1 * p.2)) 2
      ((volume.restrict (Ioc 0 a)).prod (volume.restrict (Ioc 0 a))) := by
  let mu : Measure ℝ := volume.restrict (Ioc 0 a)
  let K : ℝ × ℝ → ℂ := fun p => suzukiSourceHFinite omega (p.1 * p.2)
  let f : ℝ × ℝ → ℝ := fun p => ‖K p‖ ^ (2 : ℕ)
  have hKmeas : Measurable K := by
    have heq : suzukiSourceHFinite omega = suzukiSourceH omega := by
      funext u
      exact (suzukiSourceH_eq_finite omega u).symm
    dsimp only [K]
    rw [heq]
    exact (measurable_suzukiSourceH omega).comp (by fun_prop)
  have hfmeas : Measurable f := hKmeas.norm.pow_const 2
  obtain ⟨C, hC⟩ :=
    exists_uniform_sq_norm_suzukiCompressedHankelKernel_slice_bound homega ha
  have hfae : AEStronglyMeasurable f (mu.prod mu) := hfmeas.aestronglyMeasurable
  have hslices : ∀ᵐ x ∂mu, Integrable (fun y => f (x, y)) mu := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    change IntegrableOn (fun y : ℝ =>
      ‖suzukiSourceHFinite omega (x * y)‖ ^ (2 : ℕ)) (Ioc 0 a)
    exact integrableOn_sq_norm_suzukiCompressedHankelKernel_slice homega ha hx
  have hinnerMeas : AEStronglyMeasurable (fun x => ∫ y, ‖f (x, y)‖ ∂mu) mu :=
    hfae.norm.integral_prod_right'
  have hinnerBound : ∀ᵐ x ∂mu, ‖∫ y, ‖f (x, y)‖ ∂mu‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hnonneg : 0 ≤ ∫ y, ‖f (x, y)‖ ∂mu := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    change (∫ y in Ioc 0 a, ‖‖K (x, y)‖ ^ (2 : ℕ)‖) ≤ C
    convert hC x hx using 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    dsimp only [K]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hinnerInt : Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂mu) mu :=
    Integrable.of_bound hinnerMeas C hinnerBound
  have hfInt : Integrable f (mu.prod mu) :=
    (integrable_prod_iff hfae).mpr ⟨hslices, hinnerInt⟩
  have hKae : AEStronglyMeasurable K (mu.prod mu) := hKmeas.aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq_norm hKae).mpr hfInt

end RHTower

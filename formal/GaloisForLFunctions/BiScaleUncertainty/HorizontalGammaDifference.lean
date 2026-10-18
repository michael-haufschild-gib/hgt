import GaloisForLFunctions.HTGeometry.GammaDigammaStirlingBound

/-!
# The algebraic baseline of a horizontal Gamma difference

Two fixed complex offsets cancel the common logarithmic growth. The surviving first
order term is exact; it must be retained when comparing a logarithmic-grid arithmetic
source, whose Euler-safe tail decays exponentially, with its Gamma completion.
-/

open Complex Filter
open scoped Topology

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
open GaloisForLFunctions.HTGeometry

private theorem inv_natScale_tendsto :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ)⁻¹) atTop (𝓝 0) := by
  simpa only [Function.comp_def, one_div, Complex.ofReal_inv, Complex.ofReal_zero] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Exact first-order logarithmic zoom, with arbitrary fixed complex offset. -/
theorem tendsto_natScale_log_one_add (a : ℂ) :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ) *
      Complex.log (1 + a / (((m : ℝ) + 1 : ℝ) : ℂ))) atTop (𝓝 a) := by
  have hg : HasDerivAt (fun z : ℂ => 1 + a * z) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul a).const_add 1
  have hl : HasDerivAt (fun z : ℂ => Complex.log (1 + a * z)) a 0 := by
    have hlog : HasDerivAt Complex.log 1 (1 + a * (0 : ℂ)) := by
      simpa using Complex.hasDerivAt_log (by simp : (1 : ℂ) ∈ Complex.slitPlane)
    simpa only [Function.comp_def, one_mul] using hlog.comp (0 : ℂ) hg
  have hi : Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ)⁻¹)
      atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨inv_natScale_tendsto, Eventually.of_forall fun m => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  simpa only [Function.comp_def, zero_add, mul_zero, add_zero, Complex.log_one, sub_zero,
    smul_eq_mul, inv_inv, div_eq_mul_inv] using hl.tendsto_slope_zero.comp hi

/-- The rational pole baseline is independent of its fixed offset at first order. -/
theorem tendsto_natScale_div_shift (a : ℂ) :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ) /
      ((((m : ℝ) + 1 : ℝ) : ℂ) + a)) atTop (𝓝 1) := by
  have h : Tendsto (fun m : ℕ =>
      (1 + a * (((m : ℝ) + 1 : ℝ) : ℂ)⁻¹)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (inv_natScale_tendsto.const_mul a)).inv₀
      (by norm_num : (1 + a * (0 : ℂ)) ≠ 0)
  apply h.congr
  intro m
  have ht : (((m : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [← div_eq_mul_inv,
    show 1 + a / (((m : ℝ) + 1 : ℝ) : ℂ) =
      ((((m : ℝ) + 1 : ℝ) : ℂ) + a) / (((m : ℝ) + 1 : ℝ) : ℂ) by field_simp,
    inv_div]

private theorem scaled_stirlingDefect_tendsto (a : ℂ) (ha : 0 < a.re) :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ) *
      digammaStirlingDefect ((((m : ℝ) + 1 : ℝ) : ℂ) / 2 + a)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun m : ℕ => 24 / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 24
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 3] with m hm
  let t : ℝ := (m : ℝ) + 1
  let z : ℂ := (t : ℂ) / 2 + a
  have ht : 0 < t := by dsimp [t]; positivity
  have ht4 : 4 ≤ t := by dsimp [t]; exact_mod_cast (by omega : 4 ≤ m + 1)
  have hzre : 0 < z.re := by dsimp [z]; simp only [Complex.div_ofNat_re, Complex.ofReal_re]; linarith
  have hzn : t / 2 ≤ ‖z‖ := by
    have h := Complex.re_le_norm z
    dsimp [z] at h
    simp only [Complex.div_ofNat_re, Complex.ofReal_re] at h
    linarith
  have hz2 : 2 ≤ ‖z‖ := by linarith
  have hbound := norm_digammaStirlingDefect_le hzre hz2
  change ‖(t : ℂ) * digammaStirlingDefect z‖ ≤ 24 / t
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  calc
    t * ‖digammaStirlingDefect z‖ ≤ t * (6 / ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound ht.le
    _ ≤ 24 / t := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) ht]
      nlinarith [mul_nonneg (sub_nonneg.mpr hzn)
        (show 0 ≤ ‖z‖ + t / 2 by positivity)]

private theorem log_halfScale_add (m : ℕ) (a : ℂ) (ha : 0 < a.re) :
    Complex.log ((((m : ℝ) + 1 : ℝ) : ℂ) / 2 + a) =
      (Real.log (((m : ℝ) + 1) / 2) : ℂ) +
        Complex.log (1 + 2 * a / (((m : ℝ) + 1 : ℝ) : ℂ)) := by
  let t : ℝ := (m : ℝ) + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hz : (t : ℂ) / 2 + a ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re, Complex.zero_re] at h
    linarith
  have hfac : (t : ℂ) / 2 + a = ((t / 2 : ℝ) : ℂ) * (1 + 2 * a / (t : ℂ)) := by
    push_cast
    field_simp
  have hf : 1 + 2 * a / (t : ℂ) ≠ 0 := by
    intro hf
    rw [hf, mul_zero] at hfac
    exact hz hfac
  change Complex.log ((t : ℂ) / 2 + a) = _
  rw [hfac, Complex.log_ofReal_mul (by positivity) hf]

/-- Sharp first-order Gamma pair law. The common logarithm and reciprocal term cancel,
but the offset difference survives with its exact coefficient. -/
theorem tendsto_natScale_digamma_pair (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ) *
      (Complex.digamma ((((m : ℝ) + 1 : ℝ) : ℂ) / 2 + a) -
        Complex.digamma ((((m : ℝ) + 1 : ℝ) : ℂ) / 2 + b)))
      atTop (𝓝 (2 * (a - b))) := by
  have h := (((tendsto_natScale_log_one_add (2 * a)).sub
      (tendsto_natScale_log_one_add (2 * b))).sub
      ((tendsto_natScale_div_shift (2 * a)).sub
        (tendsto_natScale_div_shift (2 * b)))).add
      ((scaled_stirlingDefect_tendsto a ha).sub (scaled_stirlingDefect_tendsto b hb))
  convert h using 1
  · funext m
    simp only [digammaStirlingDefect, log_halfScale_add m a ha, log_halfScale_add m b hb]
    have hden (c : ℂ) : 2 * ((((m : ℝ) + 1 : ℝ) : ℂ) / 2 + c) =
        (((m : ℝ) + 1 : ℝ) : ℂ) + 2 * c := by ring
    rw [hden a, hden b]
    ring
  · ring

end
end GaloisForLFunctions.BiScaleUncertainty

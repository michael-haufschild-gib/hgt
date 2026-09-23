import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The double integration of a power-dominated integrand

The step of the analytic clock iteration integrates the operator twice, once along each
characteristic. What the Ovsyannikov recursion asks of that step is exactly this: an integrand
dominated by `c sᵐ tᵐ` on the rectangle integrates to at most `c x^{m+1} y^{m+1}/(m+1)²`.

Both factorials of the recursion come from here — one from each direction — and they are what
compensates the derivative loss.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory intervalIntegral

open scoped Interval

theorem integral_pow_zero_left (m : ℕ) (x : ℝ) :
    (∫ s in (0 : ℝ)..x, s ^ m) = x ^ (m + 1) / ((m : ℝ) + 1) := by
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) x,
      HasDerivAt (fun u : ℝ => u ^ (m + 1) / ((m : ℝ) + 1)) (s ^ m) s := by
    intro s _
    have h := hasDerivAt_pow (m + 1) s
    have h2 : HasDerivAt (fun u : ℝ => u ^ (m + 1) / ((m : ℝ) + 1))
        (((m + 1 : ℕ) : ℝ) * s ^ (m + 1 - 1) / ((m : ℝ) + 1)) s := h.div_const _
    have hval : ((m + 1 : ℕ) : ℝ) * s ^ (m + 1 - 1) / ((m : ℝ) + 1) = s ^ m := by
      simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
    rwa [hval] at h2
  have hint : IntervalIntegrable (fun s : ℝ => s ^ m) volume 0 x :=
    (continuous_pow m).intervalIntegrable 0 x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **A power-dominated integrand integrates to a power.** -/
theorem abs_integral_pow_bound {m : ℕ} {c y : ℝ} (hy : 0 ≤ y) {f : ℝ → ℝ}
    (hf : Continuous f) (hb : ∀ t ∈ Icc (0 : ℝ) y, |f t| ≤ c * t ^ m) :
    |∫ t in (0 : ℝ)..y, f t| ≤ c * y ^ (m + 1) / ((m : ℝ) + 1) := by
  have habs : |∫ t in (0 : ℝ)..y, f t| ≤ ∫ t in (0 : ℝ)..y, |f t| :=
    abs_integral_le_integral_abs hy
  have hmono : (∫ t in (0 : ℝ)..y, |f t|) ≤ ∫ t in (0 : ℝ)..y, c * t ^ m := by
    refine integral_mono_on hy (hf.abs.intervalIntegrable 0 y)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable 0 y) ?_
    intro t ht
    exact hb t ht
  have hval : (∫ t in (0 : ℝ)..y, c * t ^ m) = c * y ^ (m + 1) / ((m : ℝ) + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow_zero_left]
    ring
  linarith [habs, hmono, hval.le, hval.ge]

/-- **The double integration of a power-dominated integrand.** -/
theorem abs_iterated_integral_le {m : ℕ} {c x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {F : ℝ → ℝ → ℝ} (hFc : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hFb : ∀ s ∈ Icc (0 : ℝ) x, ∀ t ∈ Icc (0 : ℝ) y, |F s t| ≤ c * s ^ m * t ^ m) :
    |∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..y, F s t|
      ≤ c * (x ^ (m + 1) * y ^ (m + 1)) / ((m : ℝ) + 1) ^ (2 : ℕ) := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hslice : ∀ s : ℝ, Continuous fun t => F s t :=
    fun s => hFc.comp (continuous_const.prodMk continuous_id)
  have hinner : Continuous fun s : ℝ => ∫ t in (0 : ℝ)..y, F s t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hFc continuous_const
  have hbound : ∀ s ∈ Icc (0 : ℝ) x,
      |∫ t in (0 : ℝ)..y, F s t| ≤ c * s ^ m * y ^ (m + 1) / ((m : ℝ) + 1) := by
    intro s hs
    exact abs_integral_pow_bound hy (hslice s) fun t ht => hFb s hs t ht
  have habs : |∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..y, F s t|
      ≤ ∫ s in (0 : ℝ)..x, |∫ t in (0 : ℝ)..y, F s t| :=
    abs_integral_le_integral_abs hx
  have hmono : (∫ s in (0 : ℝ)..x, |∫ t in (0 : ℝ)..y, F s t|)
      ≤ ∫ s in (0 : ℝ)..x, c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m := by
    refine integral_mono_on hx (hinner.abs.intervalIntegrable 0 x)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable 0 x) ?_
    intro s hs
    have h := hbound s hs
    calc |∫ t in (0 : ℝ)..y, F s t| ≤ c * s ^ m * y ^ (m + 1) / ((m : ℝ) + 1) := h
      _ = c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m := by ring
  have hval : (∫ s in (0 : ℝ)..x, c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m)
      = c * (x ^ (m + 1) * y ^ (m + 1)) / ((m : ℝ) + 1) ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_const_mul, integral_pow_zero_left]
    field_simp
  linarith [habs, hmono, hval.le, hval.ge]

/-! ## The vector-valued form

The iteration of the clock equation integrates a function with values in a space of holomorphic
functions, so the bound is needed for a Banach-valued integrand. Nothing changes: the norm of an
integral is at most the integral of the norm, and the comparison is then between real integrals.
-/

section Vector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_integral_pow_bound {m : ℕ} {c y : ℝ} (hy : 0 ≤ y) {f : ℝ → E}
    (hf : Continuous f) (hb : ∀ t ∈ Icc (0 : ℝ) y, ‖f t‖ ≤ c * t ^ m) :
    ‖∫ t in (0 : ℝ)..y, f t‖ ≤ c * y ^ (m + 1) / ((m : ℝ) + 1) := by
  have hnorm : ‖∫ t in (0 : ℝ)..y, f t‖ ≤ ∫ t in (0 : ℝ)..y, ‖f t‖ :=
    norm_integral_le_integral_norm hy
  have hmono : (∫ t in (0 : ℝ)..y, ‖f t‖) ≤ ∫ t in (0 : ℝ)..y, c * t ^ m := by
    refine integral_mono_on hy (hf.norm.intervalIntegrable 0 y)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable 0 y) ?_
    intro t ht
    exact hb t ht
  have hval : (∫ t in (0 : ℝ)..y, c * t ^ m) = c * y ^ (m + 1) / ((m : ℝ) + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow_zero_left]
    ring
  linarith [hnorm, hmono, hval.le, hval.ge]

/-- **The double integration of a power-dominated Banach-valued integrand.** -/
theorem norm_iterated_integral_le {m : ℕ} {c x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {F : ℝ → ℝ → E} (hFc : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hFb : ∀ s ∈ Icc (0 : ℝ) x, ∀ t ∈ Icc (0 : ℝ) y, ‖F s t‖ ≤ c * s ^ m * t ^ m) :
    ‖∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..y, F s t‖
      ≤ c * (x ^ (m + 1) * y ^ (m + 1)) / ((m : ℝ) + 1) ^ (2 : ℕ) := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hslice : ∀ s : ℝ, Continuous fun t => F s t :=
    fun s => hFc.comp (continuous_const.prodMk continuous_id)
  have hinner : Continuous fun s : ℝ => ∫ t in (0 : ℝ)..y, F s t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hFc continuous_const
  have hbound : ∀ s ∈ Icc (0 : ℝ) x,
      ‖∫ t in (0 : ℝ)..y, F s t‖ ≤ c * s ^ m * y ^ (m + 1) / ((m : ℝ) + 1) := by
    intro s hs
    exact norm_integral_pow_bound hy (hslice s) fun t ht => hFb s hs t ht
  have hnorm : ‖∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..y, F s t‖
      ≤ ∫ s in (0 : ℝ)..x, ‖∫ t in (0 : ℝ)..y, F s t‖ :=
    norm_integral_le_integral_norm hx
  have hmono : (∫ s in (0 : ℝ)..x, ‖∫ t in (0 : ℝ)..y, F s t‖)
      ≤ ∫ s in (0 : ℝ)..x, c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m := by
    refine integral_mono_on hx (hinner.norm.intervalIntegrable 0 x)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable 0 x) ?_
    intro s hs
    have h := hbound s hs
    calc ‖∫ t in (0 : ℝ)..y, F s t‖ ≤ c * s ^ m * y ^ (m + 1) / ((m : ℝ) + 1) := h
      _ = c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m := by ring
  have hval : (∫ s in (0 : ℝ)..x, c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m)
      = c * (x ^ (m + 1) * y ^ (m + 1)) / ((m : ℝ) + 1) ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_const_mul, integral_pow_zero_left]
    field_simp
  linarith [hnorm, hmono, hval.le, hval.ge]

end Vector

/-! ## Two-sided endpoints

The clock construction needs the estimate on a two-sided neighbourhood of the base point, so the
endpoints may have either sign. Only the bookkeeping changes: the interval integral of a nonnegative
integrand is controlled in absolute value, and the model integral `∫₀ʸ |t|ᵐ` has absolute value
`|y|^{m+1}/(m+1)` whatever the sign of `y`.
-/

theorem abs_integral_abs_pow (m : ℕ) (y : ℝ) :
    |∫ t in (0 : ℝ)..y, |t| ^ m| = |y| ^ (m + 1) / ((m : ℝ) + 1) := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rcases le_or_gt 0 y with hy | hy
  · have hcongr : (∫ t in (0 : ℝ)..y, |t| ^ m) = ∫ t in (0 : ℝ)..y, t ^ m := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hy] at ht
      rw [abs_of_nonneg ht.1]
    rw [hcongr, integral_pow_zero_left, abs_of_nonneg hy,
      abs_of_nonneg (div_nonneg (pow_nonneg hy _) (by positivity))]
  · have hy' : y < 0 := hy
    have hcongr : (∫ t in (0 : ℝ)..y, |t| ^ m) = ∫ t in (0 : ℝ)..y, (-t) ^ m := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_ge hy'.le] at ht
      rw [abs_of_nonpos ht.2]
    have hneg : (∫ t in (0 : ℝ)..y, (-t) ^ m) = -∫ u in (0 : ℝ)..(-y), u ^ m := by
      rw [intervalIntegral.integral_comp_neg fun u : ℝ => u ^ m, neg_zero,
        intervalIntegral.integral_symm]
    have hynn : (0 : ℝ) ≤ -y := by linarith
    rw [hcongr, hneg, integral_pow_zero_left, abs_neg, abs_of_neg hy',
      abs_of_nonneg (div_nonneg (pow_nonneg hynn _) (by positivity))]

theorem norm_integral_le_abs_of_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {f : ℝ → E} {g : ℝ → ℝ}
    (hf : IntervalIntegrable (fun t => ‖f t‖) volume a b)
    (hg : IntervalIntegrable g volume a b) (h : ∀ t ∈ Ι a b, ‖f t‖ ≤ g t) :
    ‖∫ t in a..b, f t‖ ≤ |∫ t in a..b, g t| := by
  refine le_trans (intervalIntegral.norm_integral_le_abs_integral_norm) ?_
  rcases le_total a b with hab | hab
  · rw [uIoc_of_le hab] at h
    have hmono : (∫ t in a..b, ‖f t‖) ≤ ∫ t in a..b, g t := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact setIntegral_mono_on hf.1 hg.1 measurableSet_Ioc h
    have hnn : (0 : ℝ) ≤ ∫ t in a..b, ‖f t‖ := by
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_nonneg measurableSet_Ioc fun t _ => norm_nonneg _
    rw [abs_of_nonneg hnn]
    exact le_trans hmono (le_abs_self _)
  · rw [uIoc_of_ge hab] at h
    have hmono : (∫ t in b..a, ‖f t‖) ≤ ∫ t in b..a, g t := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact setIntegral_mono_on hf.symm.1 hg.symm.1 measurableSet_Ioc h
    have hnn : (0 : ℝ) ≤ ∫ t in b..a, ‖f t‖ := by
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_nonneg measurableSet_Ioc fun t _ => norm_nonneg _
    rw [intervalIntegral.integral_symm b a, abs_neg, abs_of_nonneg hnn,
      intervalIntegral.integral_symm b a, abs_neg]
    exact le_trans hmono (le_abs_self _)

/-- **The double integration of a power-dominated integrand, with endpoints of either sign.** -/
theorem norm_iterated_integral_le_abs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {c x y : ℝ} (hc : 0 ≤ c) {F : ℝ → ℝ → E}
    (hFc : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hFb : ∀ s ∈ uIcc (0 : ℝ) x, ∀ t ∈ uIcc (0 : ℝ) y, ‖F s t‖ ≤ c * |s| ^ m * |t| ^ m) :
    ‖∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..y, F s t‖
      ≤ c * (|x| ^ (m + 1) * |y| ^ (m + 1)) / ((m : ℝ) + 1) ^ (2 : ℕ) := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hslice : ∀ s : ℝ, Continuous fun t => F s t :=
    fun s => hFc.comp (continuous_const.prodMk continuous_id)
  have hinner : Continuous fun s : ℝ => ∫ t in (0 : ℝ)..y, F s t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hFc continuous_const
  have habsm : Continuous fun t : ℝ => |t| ^ m := continuous_abs.pow m
  have hbound : ∀ s ∈ uIcc (0 : ℝ) x,
      ‖∫ t in (0 : ℝ)..y, F s t‖ ≤ c * |s| ^ m * (|y| ^ (m + 1) / ((m : ℝ) + 1)) := by
    intro s hs
    have hle := norm_integral_le_abs_of_norm_le
      (f := fun t => F s t) (g := fun t => c * |s| ^ m * |t| ^ m)
      ((hslice s).norm.intervalIntegrable 0 y)
      ((continuous_const.mul habsm).intervalIntegrable 0 y)
      (fun t ht => hFb s hs t (uIoc_subset_uIcc ht))
    have hval : |∫ t in (0 : ℝ)..y, c * |s| ^ m * |t| ^ m|
        = c * |s| ^ m * (|y| ^ (m + 1) / ((m : ℝ) + 1)) := by
      rw [intervalIntegral.integral_const_mul, abs_mul, abs_integral_abs_pow,
        abs_of_nonneg (by positivity)]
    rw [hval] at hle
    exact hle
  have hle2 := norm_integral_le_abs_of_norm_le
    (f := fun s => ∫ t in (0 : ℝ)..y, F s t)
    (g := fun s => c * (|y| ^ (m + 1) / ((m : ℝ) + 1)) * |s| ^ m)
    (hinner.norm.intervalIntegrable 0 x)
    ((continuous_const.mul habsm).intervalIntegrable 0 x)
    (fun s hs => by
      have hb := hbound s (uIoc_subset_uIcc hs)
      calc ‖∫ t in (0 : ℝ)..y, F s t‖
          ≤ c * |s| ^ m * (|y| ^ (m + 1) / ((m : ℝ) + 1)) := hb
        _ = c * (|y| ^ (m + 1) / ((m : ℝ) + 1)) * |s| ^ m := by ring)
  have hval2 : |∫ s in (0 : ℝ)..x, c * (|y| ^ (m + 1) / ((m : ℝ) + 1)) * |s| ^ m|
      = c * (|x| ^ (m + 1) * |y| ^ (m + 1)) / ((m : ℝ) + 1) ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_integral_abs_pow,
      abs_of_nonneg (by positivity)]
    field_simp
  rw [hval2] at hle2
  exact hle2

/-- A point of the interval spanned by `0` and `x` is no further from the origin than `x` is. -/
theorem abs_le_abs_of_mem_uIcc_zero {t x : ℝ} (h : t ∈ uIcc (0 : ℝ) x) : |t| ≤ |x| := by
  rcases Set.mem_uIcc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (le_trans h1 h2)]
    exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (le_trans h1 h2)]
    linarith

/-- The same bound for the half-open interval used by interval integrals. -/
theorem abs_le_abs_of_mem_uIoc_zero {t x : ℝ} (h : t ∈ Ι (0 : ℝ) x) : |t| ≤ |x| :=
  abs_le_abs_of_mem_uIcc_zero (uIoc_subset_uIcc h)

end GaloisForLFunctions.HTGeometry

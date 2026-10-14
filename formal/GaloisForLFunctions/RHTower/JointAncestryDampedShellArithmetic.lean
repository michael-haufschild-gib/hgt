import GaloisForLFunctions.RHTower.JointAncestryDampedShellCriterion

/-!
# The damped shell power sums are Riesz means of the explicit-formula error

Let `𝓔(X)` be the prime side of the genus-kernel explicit formula (`lagPrimeSide`) and
`𝓔̃(x) = 𝓔(x)` for `x > 1`, `𝓔̃(x) = x 𝓔(1/x)` for `0 < x < 1` (`lagPrimeSideExt`).  The
order-`(m+1)` Riesz mean is

`𝓡_m(X) = (1/m!) ∫_0^∞ 𝓔̃(X e^{−t}) t^m e^{−t} dt`   (`lagRieszMean`).

**Theorem** (`jasShellDampedPowerSum_eq_rieszSum`).  For `k ≥ 1`,

`D_k(N) = Σ_ρ (U_ρ(N)/(ρ+1)²)^k/(ρ(1−ρ)) = Σ_{p₁,…,p_k ∈ (N,2N]} (p₁⋯p_k)^{−3/2} 𝓡_{2k−1}(p₁⋯p_k)`.

**Capstone** (`riemannHypothesis_iff_shellRiesz_growth`).  RH holds iff, for every `ε > 0`, on
infinitely many shells every `k`-fold prime average of the order-`2k` Riesz mean of the
explicit-formula error is at most `N^{εk}`.  The statement is purely arithmetic and carries no
large-height hypothesis.

**Proof.**  Per zero, `X^ρ/(ρ+1)^{m+1} = (1/m!) ∫_0^∞ (X e^{−t})^ρ t^m e^{−t} dt` by the complex
Laplace integral `∫_0^∞ t^m e^{−zt} dt = m!/z^{m+1}` (`integral_pow_mul_cexp_neg_mul_Ioi`, by
integration by parts).  The zero sum and the integral commute because
`|(Xe^{−t})^ρ| ≤ max(1, X)`.  Off the single point `X e^{−t} = 1`, the zero sum is `𝓔̃` by the
explicit formula and the reflection `ρ ↦ 1 − ρ`.  The multinomial expansion of `U_ρ(N)^k` is that
of `JointAncestryShellArithmeticCriterion`.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RHTower

noncomputable section

/-! ## The complex Laplace integral -/

theorem integrableOn_pow_mul_cexp_neg_mul {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ m * cexp (-(z * t))) (Ioi 0) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (m : ℝ)) (p := 1) (b := z.re)
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) le_rfl hz
  refine hb.mono' ((Continuous.continuousOn (by fun_prop)).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0.le, Complex.norm_exp,
    Real.rpow_natCast, Real.rpow_one]
  apply le_of_eq
  congr 2
  simp [Complex.mul_re]

theorem tendsto_pow_mul_cexp_neg_mul {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ m * cexp (-(z * t))) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
    (tendsto_id.const_mul_atTop hz)
  have h2 := h.div_const (z.re ^ m)
  rw [zero_div] at h2
  refine h2.congr' ((eventually_gt_atTop 0).mono fun t ht => ?_)
  simp only [Function.comp, id]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, Complex.norm_exp]
  have : (-(z * (t : ℂ))).re = -(z.re * t) := by simp [Complex.mul_re]
  rw [this, mul_pow]
  field_simp

theorem integral_pow_mul_cexp_neg_mul_Ioi {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * cexp (-(z * t)) = (m.factorial : ℂ) / z ^ (m + 1) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl _ hz
  induction m with
  | zero =>
    have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t : ℝ => -cexp (-(z * t)) / z)
      (f' := fun t : ℝ => (t : ℂ) ^ 0 * cexp (-(z * t))) (a := 0) (m := 0)
      (Continuous.continuousWithinAt (by fun_prop))
      (fun t _ => by
        have h1 : HasDerivAt (fun t : ℝ => -(z * (t : ℂ))) (-(z * 1)) t :=
          ((hasDerivAt_id t).ofReal_comp.const_mul z).neg
        refine ((h1.cexp.neg).div_const z).congr_deriv ?_
        field_simp)
      (integrableOn_pow_mul_cexp_neg_mul hz 0)
      (by
        have := (tendsto_pow_mul_cexp_neg_mul hz 0).neg.div_const z
        simpa using this)
    rw [h]
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, zero_sub, neg_div,
      neg_neg, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
  | succ m ih =>
    -- integration by parts through `F(t) = −t^{m+1} e^{−zt}/z`
    have hint1 := integrableOn_pow_mul_cexp_neg_mul hz (m + 1)
    have hint0 := integrableOn_pow_mul_cexp_neg_mul hz m
    have h := integral_Ioi_of_hasDerivAt_of_tendsto
      (f := fun t : ℝ => -((t : ℂ) ^ (m + 1) * cexp (-(z * t))) / z)
      (f' := fun t : ℝ => (t : ℂ) ^ (m + 1) * cexp (-(z * t)) -
        ((m + 1 : ℕ) : ℂ) / z * ((t : ℂ) ^ m * cexp (-(z * t)))) (a := 0) (m := 0)
      (Continuous.continuousWithinAt (by fun_prop))
      (fun t _ => by
        have h1 : HasDerivAt (fun t : ℝ => -(z * (t : ℂ))) (-(z * 1)) t :=
          ((hasDerivAt_id t).ofReal_comp.const_mul z).neg
        have hp : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (t : ℂ) ^ m) t := by
          simpa using (hasDerivAt_pow (m + 1) (t : ℂ)).comp_ofReal
        refine (((hp.mul h1.cexp).neg).div_const z).congr_deriv ?_
        field_simp
        ring)
      (hint1.sub (hint0.const_mul _))
      (by
        have := (tendsto_pow_mul_cexp_neg_mul hz (m + 1)).neg.div_const z
        simpa using this)
    rw [integral_sub hint1 (hint0.const_mul _), integral_const_mul, ih] at h
    simp at h
    have e : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (m + 1) * cexp (-(z * t)) =
        ((m + 1 : ℕ) : ℂ) / z * ((m.factorial : ℂ) / z ^ (m + 1)) := by
      push_cast at h ⊢
      linear_combination h
    rw [e, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-! ## The extended explicit-formula error -/

/-- `𝓔̃(x) = 𝓔(x)` for `x > 1`, `x 𝓔(1/x)` for `0 < x < 1`, and `0` otherwise. -/
def lagPrimeSideExt (x : ℝ) : ℂ :=
  if 1 < x then lagPrimeSide x else if 0 < x ∧ x < 1 then (x : ℂ) * lagPrimeSide (1 / x) else 0

theorem norm_ofReal_cpow_xiZeroCopy_le {x : ℝ} (hx : 0 < x) (q : XiZeroCopy) :
    ‖(x : ℂ) ^ (q.1 : ℂ)‖ ≤ max 1 x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  rcases le_or_gt x 1 with h | h
  · exact (Real.rpow_le_one hx.le h h0.le).trans (le_max_left _ _)
  · calc x ^ (q.1 : ℂ).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le h1.le
      _ = x := Real.rpow_one x
      _ ≤ max 1 x := le_max_right _ _

theorem summable_lagZeroSum_terms {x : ℝ} (hx : 0 < x) :
    Summable fun q : XiZeroCopy =>
      (x : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
  refine Summable.of_norm_bounded (summable_inv_mul_one_sub.norm.mul_left (max 1 x)) fun q => ?_
  rw [div_eq_mul_one_div, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_ofReal_cpow_xiZeroCopy_le hx q) (norm_nonneg _)

/-- **The zero sum is the extended explicit-formula error off `x = 1`.** -/
theorem lagZeroSum_eq_lagPrimeSideExt {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    lagZeroSum x = lagPrimeSideExt x := by
  rcases lt_or_gt_of_ne hx1 with h | h
  · -- reflection `ρ ↦ 1 − ρ`
    have hinv : 1 < 1 / x := by rw [lt_div_iff₀ hx]; linarith
    have hlag := lag_explicit_formula hinv
    rw [← lagPrimeSide] at hlag
    rw [lagPrimeSideExt, if_neg (by linarith), if_pos ⟨hx, h⟩, lagZeroSum,
      ← Equiv.tsum_eq xiZeroCopyReflectEquiv, ← hlag, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [xiZeroCopy_reflect_val]
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have harg : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne
    have e1 : (x : ℂ) ^ (1 - (q.1 : ℂ)) = (x : ℂ) * ((x : ℂ) ^ (q.1 : ℂ))⁻¹ := by
      rw [Complex.cpow_sub _ _ hxc, Complex.cpow_one, div_eq_mul_inv]
    have e2 : (((1 / x : ℝ)) : ℂ) ^ (q.1 : ℂ) = ((x : ℂ) ^ (q.1 : ℂ))⁻¹ := by
      rw [one_div, Complex.ofReal_inv, Complex.inv_cpow _ _ harg]
    have e3 : (1 : ℂ) - (1 - (q.1 : ℂ)) = (q.1 : ℂ) := by ring
    rw [e1, e2, e3]
    ring
  · have hlag := lag_explicit_formula h
    rw [← lagPrimeSide] at hlag
    rw [lagPrimeSideExt, if_pos h, ← hlag, lagZeroSum]

/-! ## Riesz means -/

/-- The order-`(m+1)` Riesz mean `𝓡_m(X) = (1/m!) ∫_0^∞ 𝓔̃(X e^{−t}) t^m e^{−t} dt`. -/
def lagRieszMean (m : ℕ) (X : ℝ) : ℂ :=
  (1 / (m.factorial : ℂ)) *
    ∫ t in Ioi (0 : ℝ), lagPrimeSideExt (X * Real.exp (-t)) * ((t : ℂ) ^ m * cexp (-(1 * (t : ℂ))))

theorem ofReal_exp_neg_cpow (t : ℝ) (q : ℂ) :
    ((Real.exp (-t) : ℝ) : ℂ) ^ q = cexp (-(q * t)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos (-t)).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  congr 1; push_cast; ring

theorem ofReal_mul_exp_neg_cpow {X : ℝ} (hX : 0 < X) (t : ℝ) (q : ℂ) :
    (((X * Real.exp (-t)) : ℝ) : ℂ) ^ q = (X : ℂ) ^ q * cexp (-(q * t)) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hX.le (Real.exp_pos _).le,
    ofReal_exp_neg_cpow]

theorem zeroLaplace_integrand_eq {X : ℝ} (hX : 0 < X) (q : ℂ) (m : ℕ) (t : ℝ) :
    (((X * Real.exp (-t)) : ℝ) : ℂ) ^ q * ((t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))) =
      (X : ℂ) ^ q * ((t : ℂ) ^ m * cexp (-((q + 1) * t))) := by
  rw [ofReal_mul_exp_neg_cpow hX,
    show -((q + 1) * (t : ℂ)) = -(q * t) + -(1 * t) by ring, Complex.exp_add]
  ring

/-- **Per zero:** `X^ρ/(ρ+1)^{m+1} = (1/m!) ∫_0^∞ (X e^{−t})^ρ t^m e^{−t} dt`. -/
theorem cpow_div_pow_eq_integral {X : ℝ} (hX : 0 < X) (q : XiZeroCopy) (m : ℕ) :
    (X : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) + 1) ^ (m + 1) =
      (1 / (m.factorial : ℂ)) * ∫ t in Ioi (0 : ℝ),
        (((X * Real.exp (-t)) : ℝ) : ℂ) ^ (q.1 : ℂ) * ((t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))) := by
  have hz : 0 < ((q.1 : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith [xiZeroCopy_re_pos q]
  simp_rw [zeroLaplace_integrand_eq hX]
  rw [integral_const_mul, integral_pow_mul_cexp_neg_mul_Ioi hz]
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hq : ((q.1 : ℂ) + 1) ^ (m + 1) ≠ 0 := pow_ne_zero _ fun h => by
    rw [h, Complex.zero_re] at hz; exact lt_irrefl _ hz
  field_simp

theorem integrableOn_zeroLaplace {X : ℝ} (hX : 0 < X) (q : XiZeroCopy) (m : ℕ) :
    IntegrableOn (fun t : ℝ => (((X * Real.exp (-t)) : ℝ) : ℂ) ^ (q.1 : ℂ) *
      ((t : ℂ) ^ m * cexp (-(1 * (t : ℂ))))) (Ioi 0) := by
  have hz : 0 < ((q.1 : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith [xiZeroCopy_re_pos q]
  have h : IntegrableOn (fun t : ℝ => (X : ℂ) ^ (q.1 : ℂ) *
      ((t : ℂ) ^ m * cexp (-(((q.1 : ℂ) + 1) * t)))) (Ioi 0) :=
    (integrableOn_pow_mul_cexp_neg_mul hz m).const_mul ((X : ℂ) ^ (q.1 : ℂ))
  exact IntegrableOn.congr_fun h (fun t _ => (zeroLaplace_integrand_eq hX _ m t).symm)
    measurableSet_Ioi

/-- **Interchange.**  `Σ_ρ X^ρ/((ρ+1)^{m+1} ρ(1−ρ)) = (1/m!) ∫_0^∞ Z(X e^{−t}) t^m e^{−t} dt`. -/
theorem tsum_cpow_div_pow_eq_integral_lagZeroSum {X : ℝ} (hX : 0 < X) (m : ℕ) :
    ∑' q : XiZeroCopy, (X : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) + 1) ^ (m + 1) *
        (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) =
      (1 / (m.factorial : ℂ)) * ∫ t in Ioi (0 : ℝ),
        lagZeroSum (X * Real.exp (-t)) * ((t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))) := by
  obtain ⟨F, hF⟩ : ∃ F : XiZeroCopy → ℝ → ℂ, F = fun q t =>
      (((X * Real.exp (-t)) : ℝ) : ℂ) ^ (q.1 : ℂ) * ((t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))) *
        (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := ⟨_, rfl⟩
  have hFint : ∀ q, Integrable (F q) (volume.restrict (Ioi 0)) := fun q => by
    rw [hF]; exact (integrableOn_zeroLaplace hX q m).mul_const _
  have hgint : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))‖) (Ioi 0) :=
    (integrableOn_pow_mul_cexp_neg_mul (z := 1) (by simp) m).norm
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))‖ :=
    ⟨_, rfl⟩
  have hFnorm : ∀ q, ∫ t in Ioi (0 : ℝ), ‖F q t‖ ≤
      max 1 X * C * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
    intro q
    have hb : ∀ t ∈ Ioi (0 : ℝ), ‖F q t‖ ≤ max 1 X * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
        ‖(t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))‖ := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      have h1 := norm_ofReal_cpow_xiZeroCopy_le (x := X * Real.exp (-t))
        (mul_pos hX (Real.exp_pos _)) q
      have h2 : max 1 (X * Real.exp (-t)) ≤ max 1 X :=
        max_le_max le_rfl (mul_le_of_le_one_right hX.le (Real.exp_le_one_iff.mpr (by linarith)))
      have h3 := h1.trans h2
      rw [hF]
      simp only
      rw [norm_mul, norm_mul]
      calc ‖(((X * Real.exp (-t)) : ℝ) : ℂ) ^ (q.1 : ℂ)‖ * ‖(t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))‖ *
            ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
          ≤ max 1 X * ‖(t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))‖ *
            ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by gcongr
        _ = max 1 X * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
            ‖(t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))‖ := by ring
    calc ∫ t in Ioi (0 : ℝ), ‖F q t‖ ≤ ∫ t in Ioi (0 : ℝ),
          max 1 X * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ * ‖(t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))‖ :=
        setIntegral_mono_on (hFint q).norm (hgint.const_mul _) measurableSet_Ioi hb
      _ = max 1 X * C * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
        rw [integral_const_mul, ← hC]; ring
  have hsum : Summable fun q => ∫ t in Ioi (0 : ℝ), ‖F q t‖ :=
    Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hFnorm
      (summable_inv_mul_one_sub.norm.mul_left (max 1 X * C))
  have hswap := integral_tsum_of_summable_integral_norm hFint hsum
  have hpt : ∀ t : ℝ, ∑' q, F q t =
      lagZeroSum (X * Real.exp (-t)) * ((t : ℂ) ^ m * cexp (-(1 * (t : ℂ)))) := by
    intro t
    rw [hF, lagZeroSum, ← tsum_mul_right]
    refine tsum_congr fun q => ?_
    rw [div_eq_mul_one_div]; ring
  simp_rw [hpt] at hswap
  rw [← hswap, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [cpow_div_pow_eq_integral hX q m, hF]
  simp only
  rw [integral_mul_const]
  ring

/-- **The Riesz mean is the zero sum.** -/
theorem tsum_cpow_div_pow_eq_lagRieszMean {X : ℝ} (hX : 0 < X) (m : ℕ) :
    ∑' q : XiZeroCopy, (X : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) + 1) ^ (m + 1) *
        (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) = lagRieszMean m X := by
  rw [tsum_cpow_div_pow_eq_integral_lagZeroSum hX m, lagRieszMean]
  congr 1
  refine integral_congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [Measure.ae_ne volume (Real.log X)] with t hne ht
  have hpos : 0 < X * Real.exp (-t) := mul_pos hX (Real.exp_pos _)
  have hne1 : X * Real.exp (-t) ≠ 1 := by
    intro h
    apply hne
    have := congrArg Real.log h
    rw [Real.log_mul hX.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_one] at this
    linarith
  rw [lagZeroSum_eq_lagPrimeSideExt hpos hne1]

/-! ## The damped shell sums -/

/-- The arithmetic damped shell sum `Σ_{p₁…p_k ∈ (N,2N]} (p₁⋯p_k)^{−3/2} 𝓡_{2k−1}(p₁⋯p_k)`. -/
def jasShellRieszSum (N k : ℕ) : ℂ :=
  ∑ t ∈ Fintype.piFinset (fun _ : Fin k => jasPrimeWindow N (2 * N)),
    (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (-(3 / 2 : ℂ)) *
      lagRieszMean (2 * k - 1) (∏ i, (((t i : ℕ) : ℝ)))

/-- **The damped shell power sum is an arithmetic Riesz sum.** -/
theorem jasShellDampedPowerSum_eq_rieszSum (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    jasShellDampedPowerSum N k = jasShellRieszSum N k := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Finset Nat.Primes, P = jasPrimeWindow N (2 * N) := ⟨_, rfl⟩
  have hexp : ∀ s : ℂ, jasShellUniformSum N s ^ k =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin k => P),
        ∏ i, cexp (-(3 / 2 - s) * (Real.log ((t i : ℕ) : ℝ) : ℂ)) := by
    intro s
    rw [jasShellUniformSum, jasCpowSum, ← hP, ← Fin.prod_const, Finset.prod_univ_sum]
  have hm : 2 * k - 1 + 1 = 2 * k := by omega
  have hpow : ∀ q : XiZeroCopy, (jasShellDampedSum N (q.1 : ℂ)) ^ k =
      jasShellUniformSum N (q.1 : ℂ) ^ k / ((q.1 : ℂ) + 1) ^ (2 * k - 1 + 1) := by
    intro q
    rw [jasShellDampedSum, div_pow, hm, ← pow_mul, mul_comm 2 k]
  have hmpos : ∀ t : Fin k → Nat.Primes, (0 : ℝ) < ∏ i, (((t i : ℕ) : ℝ)) :=
    fun t => Finset.prod_pos fun i _ => by exact_mod_cast (t i).2.pos
  -- each term is summable over the zeros
  have hsumm : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => P), Summable fun q : XiZeroCopy =>
      (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) + 1) ^ (2 * k - 1 + 1) *
        (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    intro t _
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ∏ i, (((t i : ℕ) : ℝ)) := ⟨_, rfl⟩
    rw [← hx]
    have hx0 : 0 < x := hx ▸ hmpos t
    refine Summable.of_norm_bounded (summable_inv_mul_one_sub.norm.mul_left (max 1 x))
      fun q => ?_
    rw [norm_mul, norm_div, norm_pow]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 : 1 ≤ ‖(q.1 : ℂ) + 1‖ := by
      have := one_add_im_sq_le_normSq_add_one q
      nlinarith [sq_nonneg (q.1 : ℂ).im, norm_nonneg ((q.1 : ℂ) + 1)]
    have h2 : 1 ≤ ‖(q.1 : ℂ) + 1‖ ^ (2 * k - 1 + 1) := one_le_pow₀ h1
    exact (div_le_self (norm_nonneg _) h2).trans (norm_ofReal_cpow_xiZeroCopy_le hx0 q)
  rw [jasShellDampedPowerSum, jasShellRieszSum, ← hP]
  simp_rw [hpow, hexp, Finset.sum_div, Finset.sum_mul, prod_cexp_eq_cpow]
  rw [Summable.tsum_finsetSum (fun t ht => by
    have := (hsumm t ht).mul_right ((((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (-(3 / 2 : ℂ)))
    refine this.congr fun q => ?_
    ring)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← tsum_cpow_div_pow_eq_lagRieszMean (hmpos t), ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  ring

/-- **RH ⟺ subexponential growth of the arithmetic Riesz shell sums on infinitely many shells.**
No large-height hypothesis. -/
theorem riemannHypothesis_iff_shellRiesz_growth :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε →
      ∃ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → ‖jasShellRieszSum N k‖ ≤ (N : ℝ) ^ (ε * k) := by
  rw [riemannHypothesis_iff_shellDamped_growth]
  refine forall_congr' fun ε => imp_congr_right fun _ => ?_
  refine Filter.frequently_congr (Filter.Eventually.of_forall fun N => ?_)
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  rw [jasShellDampedPowerSum_eq_rieszSum N hk]

end

end RHTower

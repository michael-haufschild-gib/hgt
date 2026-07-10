import GaloisForLFunctions.RHTower.VariablePerronKink
import GaloisForLFunctions.RHTower.ZetaCarrier

/-!
# Archimedean-balanced third-order Perron extraction

The completed carrier `archFactor * L` cannot be fed directly to the ordinary Perron kernel.
Cancelling the boundary zero at `s = 1` leaves the multiplier `s - 1`; this spends one power of
vertical decay.  The second-order kernel is then only `O(|t|⁻¹)`, outside the absolute-integral
interface used by the Perron contour.

This file constructs the minimal scalar repair.  Its physical smoothing weight is

`b(u) = max(1-u,0) * (3u-1)/2`,

whose Mellin transform is `(s-1)/(s(s+1)(s+2))`.  Four symmetric knots take a third difference,
annihilate every quadratic contribution away from the selected integer, and extract exactly
`3δ²/4` times its Dirichlet coefficient.

The second half constructs the entire boundary-balanced decompletion

`D∞(s) = 2 * dslope (fun z => Gammaℝ(z)⁻¹) 0 s`.

On the right half-plane `archFactor(s) * D∞(s) = s-1`.  This makes the completed coefficient
charge exact, but also records the scalar no-go: the Gamma factor is cancelled rather than
transported, so this theorem does not supply completed-carrier flank decay.
-/

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set

noncomputable section

namespace RHTower

/-! ## 1. The balanced third-order Mellin kernel -/

/-- The continuous compactly right-supported weight
`b(u) = max(1-u,0) * (3u-1)/2`. -/
def balancedPerronKernelG (u : ℝ) : ℂ :=
  ((max (1 - u) 0 * (3 * u - 1) / 2 : ℝ) : ℂ)

theorem continuous_balancedPerronKernelG : Continuous balancedPerronKernelG := by
  unfold balancedPerronKernelG
  fun_prop

/-- **Mellin transform of the balanced kernel.**  On `Re s > 0`,

`mellin b(s) = (s-1)/(s(s+1)(s+2))`.

The numerator `s-1` is the boundary charge left by entire decompletion of `archFactor`; the third
denominator is the extra smoothing order that restores absolute vertical integrability. -/
theorem balancedPerronKernel_mellin {s : ℂ} (hs : 0 < s.re) :
    mellin balancedPerronKernelG s = (s - 1) / (s * (s + 1) * (s + 2)) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hreal
    linarith
  have hs2 : s + 2 ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num [Complex.add_re] at hreal
    linarith
  rw [mellin]
  have hrestrict :
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • balancedPerronKernelG t =
        ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • balancedPerronKernelG t := by
    rw [← MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (t := Ioi (0 : ℝ)) (s := Ioc (0 : ℝ) 1) measurableSet_Ioi Ioc_subset_Ioi_self ?_]
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    simp only [mem_Ioi] at hx0
    simp only [mem_Ioc, not_and, not_le] at hx1
    have hgt : 1 < x := hx1 hx0
    have hz : balancedPerronKernelG x = 0 := by
      simp only [balancedPerronKernelG]
      rw [max_eq_right (by linarith)]
      norm_num
    rw [hz, smul_zero]
  rw [hrestrict, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hcongr :
      ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) • balancedPerronKernelG t =
        ∫ t in (0 : ℝ)..1,
          (-(1 / 2 : ℂ)) * (t : ℂ) ^ (s - 1) + 2 * (t : ℂ) ^ s -
            (3 / 2 : ℂ) * (t : ℂ) ^ (s + 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have hg : balancedPerronKernelG t =
        ((((1 - t) * (3 * t - 1) / 2 : ℝ)) : ℂ) := by
      simp only [balancedPerronKernelG]
      rw [max_eq_left (by linarith)]
    change (t : ℂ) ^ (s - 1) • balancedPerronKernelG t =
      (-(1 / 2 : ℂ)) * (t : ℂ) ^ (s - 1) + 2 * (t : ℂ) ^ s -
        (3 / 2 : ℂ) * (t : ℂ) ^ (s + 1)
    rw [hg, smul_eq_mul]
    push_cast
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · subst t
      simp only [Complex.ofReal_zero, mul_zero, sub_zero,
        zero_sub, one_mul, Complex.zero_cpow hs0, Complex.zero_cpow hs1]
      ring
    · have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
      have hcp1 : (t : ℂ) ^ s = (t : ℂ) ^ (s - 1) * (t : ℂ) := by
        conv_lhs => rw [show s = (s - 1) + 1 by ring]
        rw [Complex.cpow_add _ _ htne, Complex.cpow_one]
      have hcp2 : (t : ℂ) ^ (s + 1) = (t : ℂ) ^ s * (t : ℂ) := by
        rw [Complex.cpow_add _ _ htne, Complex.cpow_one]
      rw [hcp2, hcp1]
      ring
  rw [hcongr]
  have hi0 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1)) volume 0 1 :=
    (intervalIntegrable_cpow' (by simp only [Complex.sub_re, Complex.one_re]; linarith)).symm
  have hi1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ s) volume 0 1 :=
    (intervalIntegrable_cpow' (by linarith)).symm
  have hi2 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s + 1)) volume 0 1 :=
    (intervalIntegrable_cpow' (by simp only [Complex.add_re, Complex.one_re]; linarith)).symm
  rw [intervalIntegral.integral_sub (hi0.const_mul _ |>.add (hi1.const_mul _))
      (hi2.const_mul _),
    intervalIntegral.integral_add (hi0.const_mul _) (hi1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_cpow (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith)),
    integral_cpow (Or.inl (by linarith)),
    integral_cpow (Or.inl (by simp only [Complex.add_re, Complex.one_re]; linarith))]
  have he0 : s - 1 + 1 = s := by ring
  have he1 : s + 1 + 1 = s + 2 := by ring
  rw [he0, he1]
  simp only [Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero,
    Complex.zero_cpow hs0, Complex.zero_cpow hs1, Complex.zero_cpow hs2]
  field_simp
  ring

/-- Mellin convergence of the balanced kernel on every positive abscissa. -/
theorem balancedPerronKernel_mellinConvergent {c : ℝ} (hc : 0 < c) :
    MellinConvergent balancedPerronKernelG (c : ℂ) := by
  apply mellinConvergent_of_isBigO_rpow (a := c + 1) (b := 0)
  · exact (continuous_balancedPerronKernelG.locallyIntegrable).locallyIntegrableOn _
  · have h0 : balancedPerronKernelG =ᶠ[atTop] (fun _ => (0 : ℂ)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      simp only [balancedPerronKernelG]
      rw [max_eq_right (by linarith)]
      norm_num
    exact h0.isBigO.trans (isBigO_zero _ _)
  · simp only [Complex.ofReal_re]
    linarith
  · have h1 : (fun x : ℝ => x ^ (-(0 : ℝ))) = fun _ => (1 : ℝ) := by
      funext x
      rw [neg_zero, Real.rpow_zero]
    rw [h1]
    exact ((continuous_balancedPerronKernelG.tendsto 0).mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  · simp only [Complex.ofReal_re]
    exact hc

private theorem balanced_factor_norm_le_three {c t : ℝ} (hc : 0 < c) :
    ‖(((c : ℂ) + (t : ℂ) * I) - 1) / (((c : ℂ) + (t : ℂ) * I) + 2)‖ ≤ 3 := by
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
  have hre : (s + 2).re = c + 2 := by
    rw [hs]
    simp
  have hden : c + 2 ≤ ‖s + 2‖ := by
    calc
      c + 2 = |(s + 2).re| := by rw [hre, abs_of_pos (by linarith)]
      _ ≤ ‖s + 2‖ := Complex.abs_re_le_norm _
  have hdenpos : 0 < ‖s + 2‖ := lt_of_lt_of_le (by linarith) hden
  have hnum : ‖s - 1‖ ≤ ‖s + 2‖ + 3 := by
    have heq : s - 1 = (s + 2) - 3 := by ring
    rw [heq]
    calc
      ‖s + 2 - 3‖ ≤ ‖s + 2‖ + ‖(3 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s + 2‖ + 3 := by norm_num
  have hthree : ‖s - 1‖ ≤ 3 * ‖s + 2‖ := by
    calc
      ‖s - 1‖ ≤ ‖s + 2‖ + 3 := hnum
      _ ≤ 3 * ‖s + 2‖ := by nlinarith
  rw [norm_div]
  exact (div_le_iff₀ hdenpos).2 (by simpa [mul_comm] using hthree)

/-- The balanced kernel remains absolutely integrable on every positive vertical line.  It is the
ordinary quadratic Perron kernel multiplied by `(s-1)/(s+2)`, whose norm is uniformly bounded. -/
theorem balancedPerronKernel_verticalIntegrable {c : ℝ} (hc : 0 < c) :
    VerticalIntegrable (mellin balancedPerronKernelG) c volume := by
  have hbase : Integrable (fun t : ℝ => mellin perronKernelG ((c : ℂ) + (t : ℂ) * I)) :=
    perronKernel_verticalIntegrable hc
  have hval : (fun t : ℝ => mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ => mellin perronKernelG ((c : ℂ) + (t : ℂ) * I) *
        ((((c : ℂ) + (t : ℂ) * I) - 1) / (((c : ℂ) + (t : ℂ) * I) + 2)) := by
    funext t
    have hre : 0 < (((c : ℂ) + (t : ℂ) * I).re) := by simp; exact hc
    rw [balancedPerronKernel_mellin hre, perronKernel_mellin hre]
    have h0 : ((c : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have h1 : ((c : ℂ) + (t : ℂ) * I) + 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have h2 : ((c : ℂ) + (t : ℂ) * I) + 2 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
      linarith
    field_simp
  rw [VerticalIntegrable, hval]
  have hfactor_cont : Continuous (fun t : ℝ =>
      ((((c : ℂ) + (t : ℂ) * I) - 1) / (((c : ℂ) + (t : ℂ) * I) + 2))) := by
    apply Continuous.div₀ (by fun_prop) (by fun_prop)
    intro t h
    have hreal := congrArg Complex.re h
    norm_num at hreal
    linarith
  refine (hbase.norm.const_mul 3).mono' ?_ ?_
  · exact hbase.aestronglyMeasurable.mul hfactor_cont.aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (balanced_factor_norm_le_three hc)
      (norm_nonneg (mellin perronKernelG ((c : ℂ) + (t : ℂ) * I)))

/-- Mellin inversion for the balanced kernel. -/
theorem balancedPerronKernel_inversion {c : ℝ} (hc : 0 < c) {y : ℝ} (hy : 0 < y) :
    (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
          ((((c : ℂ) + (t : ℂ) * I) - 1) /
            (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1) *
              (((c : ℂ) + (t : ℂ) * I) + 2)))
      = balancedPerronKernelG (1 / y) := by
  have hintegrand :
      (fun t : ℝ =>
        (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
          ((((c : ℂ) + (t : ℂ) * I) - 1) /
            (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1) *
              (((c : ℂ) + (t : ℂ) * I) + 2)))) =
      (fun t : ℝ =>
        ((1 / y : ℝ) : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I)) •
          mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)) := by
    funext t
    have hre : 0 < (((c : ℂ) + (t : ℂ) * I).re) := by simp; exact hc
    have hbase : ((1 / y : ℝ) : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I)) =
        (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) := by
      rw [one_div, Complex.ofReal_inv,
        Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne'.symm),
        Complex.cpow_neg, inv_inv]
    rw [balancedPerronKernel_mellin hre, smul_eq_mul, hbase]
  rw [hintegrand]
  have key : mellinInv c (mellin balancedPerronKernelG) (1 / y) =
      balancedPerronKernelG (1 / y) :=
    mellinInv_mellin_eq c balancedPerronKernelG (by positivity)
      (balancedPerronKernel_mellinConvergent hc)
      (balancedPerronKernel_verticalIntegrable hc)
      continuous_balancedPerronKernelG.continuousAt
  rw [show (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, ((1 / y : ℝ) : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I)) •
          mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)
      = mellinInv c (mellin balancedPerronKernelG) (1 / y) from rfl, key]

/-! ## 2. Balanced Perron summation -/

/-- The physical weight attached to a Perron knot `x` and an integer frequency `m`. -/
def balancedPerronWeight (x : ℝ) (m : ℕ) : ℂ :=
  (x : ℂ) ^ 2 * balancedPerronKernelG ((m : ℝ) / x)

private theorem balanced_term_line_continuous (a : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term a ((c : ℂ) + (t : ℂ) * I) n) := by
  rcases eq_or_ne n 0 with h | h
  · subst h
    simp only [LSeries.term_zero]
    exact continuous_const
  · have heq : (fun t : ℝ => LSeries.term a ((c : ℂ) + (t : ℂ) * I) n) =
        fun t : ℝ => a n * (n : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I)) := by
      funext t
      rw [LSeries.term_of_ne_zero h, Complex.cpow_neg, div_eq_mul_inv]
    rw [heq]
    exact continuous_const.mul
      (Continuous.const_cpow (by fun_prop)
        (Or.inl (by exact_mod_cast Nat.cast_ne_zero.mpr h)))

/-- **Balanced Perron summation.**  The extra denominator makes the boundary-balanced multiplier
absolutely integrable, so an absolutely convergent Dirichlet series can be expanded term by term:

`sum a_m W_x(m) = (1/(2*pi)) integral L(c+it) x^(c+it+2) mellin(b)(c+it) dt`. -/
theorem balanced_perron_sum {a : ℕ → ℂ} {c : ℝ} (hc : 0 < c)
    (hsum : LSeriesSummable a c) {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, (if n = 0 then (0 : ℂ) else a n * balancedPerronWeight x n) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) *
          ((x : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 2) *
            mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)) := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  have hKint : Integrable (fun t : ℝ =>
      mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)) :=
    balancedPerronKernel_verticalIntegrable hc
  set F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term a ((c : ℂ) + (t : ℂ) * I) n *
      (x : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 2) *
        mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I) with hF
  set Cn : ℕ → ℝ := fun n => ‖LSeries.term a (c : ℂ) n‖ * x ^ (c + 2) with hCn
  have hCn_nonneg : ∀ n, 0 ≤ Cn n := fun n =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx.le _)
  have hre : ∀ t : ℝ, (((c : ℂ) + (t : ℂ) * I).re) = c := fun t => by simp
  have hFnorm : ∀ n t, ‖F n t‖ = Cn n *
      ‖mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)‖ := by
    intro n t
    have h1 : ‖LSeries.term a ((c : ℂ) + (t : ℂ) * I) n‖ =
        ‖LSeries.term a (c : ℂ) n‖ := by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre, Complex.ofReal_re]
    have h2 : ‖(x : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 2)‖ = x ^ (c + 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      rw [Complex.add_re, hre]
      norm_num
    simp only [hF, hCn, norm_mul]
    rw [h1, h2]
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) := by
    intro n
    simp only [hF]
    exact ((balanced_term_line_continuous a c n).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl hxc))).aestronglyMeasurable.mul
        hKint.aestronglyMeasurable
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    refine (hKint.norm.const_mul (Cn n)).mono' (hFmeas n) ?_
    filter_upwards [] with t
    rw [hFnorm]
  set M : ℝ := ∫ t : ℝ,
    ‖mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)‖ with hM
  have hSummable : Summable (fun n => ∫ t : ℝ, ‖F n t‖) := by
    have hCM : Summable (fun n => Cn n * M) := by
      have hbase : Summable (fun n => ‖LSeries.term a (c : ℂ) n‖) :=
        summable_norm_iff.mpr hsum
      have hmul := hbase.mul_right (x ^ (c + 2) * M)
      refine hmul.congr (fun n => ?_)
      simp only [hCn]
      ring
    refine hCM.congr (fun n => ?_)
    have heq : (fun t : ℝ => ‖F n t‖) = fun t : ℝ =>
        Cn n * ‖mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)‖ := by
      funext t
      exact hFnorm n t
    rw [heq, MeasureTheory.integral_const_mul, ← hM]
  have hExpand : ∀ t : ℝ,
      LSeries a ((c : ℂ) + (t : ℂ) * I) *
          ((x : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 2) *
            mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)) =
        ∑' n, F n t := by
    intro t
    rw [show LSeries a ((c : ℂ) + (t : ℂ) * I) =
      ∑' n, LSeries.term a ((c : ℂ) + (t : ℂ) * I) n from rfl,
      ← tsum_mul_right]
    apply tsum_congr
    intro n
    simp only [hF]
    ring
  have hswap :
      ∫ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) *
          ((x : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 2) *
            mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)) =
        ∑' n, ∫ t : ℝ, F n t := by
    simp_rw [hExpand]
    exact (integral_tsum_of_summable_integral_norm hFint hSummable).symm
  rw [hswap]
  have hIntSummable : Summable (fun n => ∫ t : ℝ, F n t) :=
    Summable.of_norm_bounded hSummable (fun n => norm_integral_le_integral_norm _)
  rw [← Summable.tsum_const_smul (1 / (2 * Real.pi) : ℝ) hIntSummable]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [if_pos rfl]
    simp only [hF, LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, smul_zero]
  · rw [if_neg hn]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpt : F n = fun t : ℝ =>
        (a n * (x : ℂ) ^ 2) *
          (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
            mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)) := by
      funext t
      set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
      have harg : ((n : ℝ) : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hnpos.le]
        exact Real.pi_pos.ne'.symm
      have hdiv : ((x / n : ℝ) : ℂ) ^ s =
          (x : ℂ) ^ s * (n : ℂ) ^ (-s) := by
        rw [Complex.ofReal_div, div_eq_mul_inv, ← Complex.ofReal_inv,
          Complex.mul_cpow_ofReal_nonneg hx.le (by positivity), Complex.ofReal_inv,
          Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, Complex.ofReal_natCast]
      have hx2 : (x : ℂ) ^ (s + 2) = (x : ℂ) ^ s * (x : ℂ) ^ 2 := by
        rw [Complex.cpow_add _ _ hxc, Complex.cpow_two]
      simp only [hF]
      rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, hs, hx2, hdiv]
      ring
    have hintFn : ∫ t : ℝ, F n t = (a n * (x : ℂ) ^ 2) *
        ∫ t : ℝ, (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
          mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)) := by
      rw [hpt, MeasureTheory.integral_const_mul]
    have hJ : (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
          mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)) =
        balancedPerronKernelG (1 / (x / n)) := by
      have hInv := balancedPerronKernel_inversion hc (show 0 < x / (n : ℝ) by positivity)
      have hfun : (fun t : ℝ =>
          (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
            mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I))) =
          fun t : ℝ =>
            (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
              ((((c : ℂ) + (t : ℂ) * I) - 1) /
                (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1) *
                  (((c : ℂ) + (t : ℂ) * I) + 2)))) := by
        funext t
        rw [balancedPerronKernel_mellin (by simp; exact hc)]
      rw [hfun]
      exact hInv
    rw [hintFn, ← mul_smul_comm, hJ]
    have harg : 1 / (x / (n : ℝ)) = (n : ℝ) / x := by field_simp
    rw [harg]
    simp only [balancedPerronWeight]
    ring

/-- The single-knot balanced Perron integrand is integrable; this is the linearity interface used
when four knots are combined. -/
theorem balanced_perron_integrable {a : ℕ → ℂ} {c : ℝ} (hc : 0 < c)
    (hsum : LSeriesSummable a c) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => LSeries a ((c : ℂ) + (t : ℂ) * I) *
      ((x : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 2) *
        mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I))) := by
  obtain ⟨B, hB⟩ := lseries_bounded_on_halfplane hsum
  have hKint : Integrable (fun t : ℝ =>
      mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)) :=
    balancedPerronKernel_verticalIntegrable hc
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  have hLmeas : AEStronglyMeasurable (fun t : ℝ =>
      LSeries a ((c : ℂ) + (t : ℂ) * I)) := by
    have hm : Measurable (fun t : ℝ => LSeries a ((c : ℂ) + (t : ℂ) * I)) := by
      change Measurable (fun t : ℝ =>
        ∑' n, LSeries.term a ((c : ℂ) + (t : ℂ) * I) n)
      exact Measurable.tsum (fun n => (balanced_term_line_continuous a c n).measurable)
    exact hm.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      LSeries a ((c : ℂ) + (t : ℂ) * I) *
        ((x : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 2) *
          mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I))) :=
    hLmeas.mul ((Continuous.const_cpow (by fun_prop) (Or.inl hxc)).aestronglyMeasurable.mul
      hKint.aestronglyMeasurable)
  refine (hKint.norm.const_mul (B * x ^ (c + 2))).mono' hmeas ?_
  filter_upwards [] with t
  have hre : (((c : ℂ) + (t : ℂ) * I).re) = c := by simp
  have hL : ‖LSeries a ((c : ℂ) + (t : ℂ) * I)‖ ≤ B :=
    hB _ (by rw [hre])
  have hxpow : ‖(x : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 2)‖ = x ^ (c + 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    rw [Complex.add_re, hre]
    norm_num
  simp only [norm_mul, hxpow]
  have hnonneg : 0 ≤ x ^ (c + 2) *
      ‖mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I)‖ :=
    mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hL hnonneg

/-- In the active region `m < x`, the balanced physical weight is the quadratic
`-x²/2 + 2mx - 3m²/2`. -/
theorem balancedPerronWeight_of_lt {x : ℝ} {m : ℕ} (hx : 0 < x) (hm : (m : ℝ) < x) :
    balancedPerronWeight x m =
      -(x : ℂ) ^ 2 / 2 + 2 * (m : ℂ) * (x : ℂ) - 3 * (m : ℂ) ^ 2 / 2 := by
  have hmax : max (1 - (m : ℝ) / x) 0 = 1 - (m : ℝ) / x := by
    rw [max_eq_left]
    exact sub_nonneg.mpr ((div_le_iff₀ hx).2 (by simpa using hm.le))
  unfold balancedPerronWeight balancedPerronKernelG
  rw [hmax]
  push_cast
  field_simp [ne_of_gt hx]
  ring

/-- Beyond the knot, the balanced physical weight vanishes. -/
theorem balancedPerronWeight_of_le {x : ℝ} {m : ℕ} (hx : 0 < x) (hm : x ≤ (m : ℝ)) :
    balancedPerronWeight x m = 0 := by
  have hmax : max (1 - (m : ℝ) / x) 0 = 0 := by
    rw [max_eq_right]
    exact sub_nonpos.mpr ((le_div_iff₀ hx).2 (by simpa using hm))
  unfold balancedPerronWeight balancedPerronKernelG
  rw [hmax]
  norm_num

/-- The four symmetric knots used by the third finite difference. -/
def perronThirdX0 (n : ℕ) (δ : ℝ) : ℝ := (n : ℝ) - 3 * δ / 2
def perronThirdX1 (n : ℕ) (δ : ℝ) : ℝ := (n : ℝ) - δ / 2
def perronThirdX2 (n : ℕ) (δ : ℝ) : ℝ := (n : ℝ) + δ / 2
def perronThirdX3 (n : ℕ) (δ : ℝ) : ℝ := (n : ℝ) + 3 * δ / 2

private theorem perronThird_knots_pos {n : ℕ} {δ : ℝ} (hn : 1 ≤ n)
    (hδ0 : 0 < δ) (hδ : δ < 2 / 3) :
    0 < perronThirdX0 n δ ∧ 0 < perronThirdX1 n δ ∧
      0 < perronThirdX2 n δ ∧ 0 < perronThirdX3 n δ := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold perronThirdX0 perronThirdX1 perronThirdX2 perronThirdX3
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · constructor <;> nlinarith

/-- **Four-knot balanced charge.**  For `0 < δ < 2/3`, the signed third difference of the
balanced physical sums isolates exactly one integer and returns `3δ²/4 * a_n`. -/
theorem balancedPerronWeight_third_difference (a : ℕ → ℂ) {n : ℕ} {δ : ℝ}
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ : δ < 2 / 3) :
    (∑' m : ℕ, if m = 0 then (0 : ℂ) else a m * balancedPerronWeight (perronThirdX0 n δ) m)
      - 3 * (∑' m : ℕ, if m = 0 then (0 : ℂ) else
          a m * balancedPerronWeight (perronThirdX1 n δ) m)
      + 3 * (∑' m : ℕ, if m = 0 then (0 : ℂ) else
          a m * balancedPerronWeight (perronThirdX2 n δ) m)
      - (∑' m : ℕ, if m = 0 then (0 : ℂ) else
          a m * balancedPerronWeight (perronThirdX3 n δ) m) =
        a n * (3 * (δ : ℂ) ^ 2 / 4) := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := perronThird_knots_pos hn hδ0 hδ
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hx3lt : perronThirdX3 n δ < (n : ℝ) + 1 := by
    unfold perronThirdX3
    nlinarith
  have hvanish : ∀ x : ℝ, 0 < x → x ≤ perronThirdX3 n δ →
      ∀ m ∉ Finset.range (n + 1),
        (if m = 0 then (0 : ℂ) else a m * balancedPerronWeight x m) = 0 := by
    intro x hxp hx m hm
    rw [Finset.mem_range, not_lt] at hm
    have hmn : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
    rw [if_neg (by omega : m ≠ 0), balancedPerronWeight_of_le hxp (by linarith), mul_zero]
  rw [tsum_eq_sum (hvanish _ hx0 (by
        unfold perronThirdX0 perronThirdX3; linarith)),
      tsum_eq_sum (hvanish _ hx1 (by
        unfold perronThirdX1 perronThirdX3; linarith)),
      tsum_eq_sum (hvanish _ hx2 (by
        unfold perronThirdX2 perronThirdX3; linarith)),
      tsum_eq_sum (hvanish _ hx3 (le_refl _))]
  rw [show
      (∑ m ∈ Finset.range (n + 1),
          (if m = 0 then (0 : ℂ) else a m * balancedPerronWeight (perronThirdX0 n δ) m))
        - 3 * (∑ m ∈ Finset.range (n + 1),
          (if m = 0 then (0 : ℂ) else a m * balancedPerronWeight (perronThirdX1 n δ) m))
        + 3 * (∑ m ∈ Finset.range (n + 1),
          (if m = 0 then (0 : ℂ) else a m * balancedPerronWeight (perronThirdX2 n δ) m))
        - (∑ m ∈ Finset.range (n + 1),
          (if m = 0 then (0 : ℂ) else a m * balancedPerronWeight (perronThirdX3 n δ) m)) =
      ∑ m ∈ Finset.range (n + 1),
        ((if m = 0 then (0 : ℂ) else a m * balancedPerronWeight (perronThirdX0 n δ) m)
          - 3 * (if m = 0 then (0 : ℂ) else a m * balancedPerronWeight (perronThirdX1 n δ) m)
          + 3 * (if m = 0 then (0 : ℂ) else a m * balancedPerronWeight (perronThirdX2 n δ) m)
          - (if m = 0 then (0 : ℂ) else a m * balancedPerronWeight (perronThirdX3 n δ) m))
      from by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]]
  rw [Finset.sum_eq_single n]
  · rw [if_neg hn0, if_neg hn0, if_neg hn0, if_neg hn0,
      balancedPerronWeight_of_le hx0 (by unfold perronThirdX0; linarith),
      balancedPerronWeight_of_le hx1 (by unfold perronThirdX1; linarith),
      balancedPerronWeight_of_lt hx2 (by unfold perronThirdX2; linarith),
      balancedPerronWeight_of_lt hx3 (by unfold perronThirdX3; linarith)]
    unfold perronThirdX2 perronThirdX3
    push_cast
    ring
  · intro m hmem hmn
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      simp
    · have hmlt : m < n := lt_of_le_of_ne
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)) hmn
      have hmr : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmlt
      have hmX0 : (m : ℝ) < perronThirdX0 n δ := by
        unfold perronThirdX0
        nlinarith
      rw [if_neg hm0.ne', if_neg hm0.ne', if_neg hm0.ne', if_neg hm0.ne',
        balancedPerronWeight_of_lt hx0 hmX0,
        balancedPerronWeight_of_lt hx1 (lt_trans hmX0 (by
          unfold perronThirdX0 perronThirdX1; linarith)),
        balancedPerronWeight_of_lt hx2 (lt_trans hmX0 (by
          unfold perronThirdX0 perronThirdX2; linarith)),
        balancedPerronWeight_of_lt hx3 (lt_trans hmX0 (by
          unfold perronThirdX0 perronThirdX3; linarith))]
      unfold perronThirdX0 perronThirdX1 perronThirdX2 perronThirdX3
      push_cast
      ring
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h

/-! ## 3. The entire four-knot regularization -/

/-- The symmetric signed third-difference numerator. -/
def perronThirdKink (n : ℕ) (δ : ℝ) (s : ℂ) : ℂ :=
  (perronThirdX0 n δ : ℂ) ^ (s + 2) -
    3 * (perronThirdX1 n δ : ℂ) ^ (s + 2) +
    3 * (perronThirdX2 n δ : ℂ) ^ (s + 2) -
    (perronThirdX3 n δ : ℂ) ^ (s + 2)

theorem perronThirdKink_zero (n : ℕ) (δ : ℝ) : perronThirdKink n δ 0 = 0 := by
  unfold perronThirdKink
  rw [show (0 : ℂ) + 2 = 2 by ring, Complex.cpow_two, Complex.cpow_two,
    Complex.cpow_two, Complex.cpow_two]
  unfold perronThirdX0 perronThirdX1 perronThirdX2 perronThirdX3
  push_cast
  ring

theorem perronThirdKink_negOne (n : ℕ) (δ : ℝ) : perronThirdKink n δ (-1) = 0 := by
  unfold perronThirdKink
  rw [show (-1 : ℂ) + 2 = 1 by ring, Complex.cpow_one, Complex.cpow_one,
    Complex.cpow_one, Complex.cpow_one]
  unfold perronThirdX0 perronThirdX1 perronThirdX2 perronThirdX3
  push_cast
  ring

theorem perronThirdKink_negTwo (n : ℕ) (δ : ℝ) : perronThirdKink n δ (-2) = 0 := by
  unfold perronThirdKink
  rw [show (-2 : ℂ) + 2 = 0 by ring, Complex.cpow_zero, Complex.cpow_zero,
    Complex.cpow_zero, Complex.cpow_zero]
  ring

theorem perronThirdKink_differentiable {n : ℕ} {δ : ℝ} (hn : 1 ≤ n)
    (hδ0 : 0 < δ) (hδ : δ < 2 / 3) : Differentiable ℂ (perronThirdKink n δ) := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := perronThird_knots_pos hn hδ0 hδ
  have hb0 : (perronThirdX0 n δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx0
  have hb1 : (perronThirdX1 n δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx1
  have hb2 : (perronThirdX2 n δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx2
  have hb3 : (perronThirdX3 n δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx3
  have d0 : Differentiable ℂ (fun s : ℂ => (perronThirdX0 n δ : ℂ) ^ (s + 2)) :=
    fun s => (differentiableAt_id.add_const 2).const_cpow (Or.inl hb0)
  have d1 : Differentiable ℂ (fun s : ℂ => (perronThirdX1 n δ : ℂ) ^ (s + 2)) :=
    fun s => (differentiableAt_id.add_const 2).const_cpow (Or.inl hb1)
  have d2 : Differentiable ℂ (fun s : ℂ => (perronThirdX2 n δ : ℂ) ^ (s + 2)) :=
    fun s => (differentiableAt_id.add_const 2).const_cpow (Or.inl hb2)
  have d3 : Differentiable ℂ (fun s : ℂ => (perronThirdX3 n δ : ℂ) ^ (s + 2)) :=
    fun s => (differentiableAt_id.add_const 2).const_cpow (Or.inl hb3)
  exact ((d0.sub (d1.const_mul 3)).add (d2.const_mul 3)).sub d3

/-- Triple removable-singularity regularization of the third-difference numerator. -/
def perronThirdE (n : ℕ) (δ : ℝ) : ℂ → ℂ :=
  dslope (dslope (dslope (perronThirdKink n δ) 0) (-1)) (-2)

theorem perronThirdE_differentiable {n : ℕ} {δ : ℝ} (hn : 1 ≤ n)
    (hδ0 : 0 < δ) (hδ : δ < 2 / 3) : Differentiable ℂ (perronThirdE n δ) := by
  have d0 : Differentiable ℂ (dslope (perronThirdKink n δ) 0) := by
    rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
    exact (perronThirdKink_differentiable hn hδ0 hδ).differentiableOn
  have d1 : Differentiable ℂ (dslope (dslope (perronThirdKink n δ) 0) (-1)) := by
    rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
    exact d0.differentiableOn
  unfold perronThirdE
  rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
  exact d1.differentiableOn

/-- Away from the three removed points, the regularization is the cubic Perron quotient. -/
theorem perronThirdE_eq (n : ℕ) (δ : ℝ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ -1) (h2 : s ≠ -2) :
    perronThirdE n δ s = perronThirdKink n δ s / (s * (s + 1) * (s + 2)) := by
  have e0 : dslope (perronThirdKink n δ) 0 s = perronThirdKink n δ s / s := by
    rw [dslope_of_ne _ h0, slope_def_field, perronThirdKink_zero, sub_zero, sub_zero]
  have em1 : dslope (perronThirdKink n δ) 0 (-1) = 0 := by
    rw [dslope_of_ne _ (by norm_num : (-1 : ℂ) ≠ 0), slope_def_field,
      perronThirdKink_zero, perronThirdKink_negOne, sub_zero, zero_div]
  have e1 : dslope (dslope (perronThirdKink n δ) 0) (-1) s =
      perronThirdKink n δ s / (s * (s + 1)) := by
    rw [dslope_of_ne _ h1, slope_def_field, e0, em1, sub_zero, sub_neg_eq_add, div_div]
  have em2 : dslope (dslope (perronThirdKink n δ) 0) (-1) (-2) = 0 := by
    have ez : dslope (perronThirdKink n δ) 0 (-2) = 0 := by
      rw [dslope_of_ne _ (by norm_num : (-2 : ℂ) ≠ 0), slope_def_field,
        perronThirdKink_zero, perronThirdKink_negTwo, sub_zero, zero_div]
    rw [dslope_of_ne _ (by norm_num : (-2 : ℂ) ≠ -1), slope_def_field, ez, em1,
      sub_self, zero_div]
  unfold perronThirdE
  rw [dslope_of_ne _ h2, slope_def_field, e1, em2, sub_zero, sub_neg_eq_add, div_div]

/-- The entire boundary-balanced third-order probe. -/
def perronThirdBalancedE (n : ℕ) (δ : ℝ) (s : ℂ) : ℂ :=
  (s - 1) * perronThirdE n δ s

theorem perronThirdBalancedE_differentiable {n : ℕ} {δ : ℝ} (hn : 1 ≤ n)
    (hδ0 : 0 < δ) (hδ : δ < 2 / 3) :
    Differentiable ℂ (perronThirdBalancedE n δ) :=
  differentiable_id.sub_const 1 |>.mul (perronThirdE_differentiable hn hδ0 hδ)

/-- **Exact balanced coefficient charge.**  The right-edge integral of the entire balanced probe
extracts `3δ²/4` times the selected Dirichlet coefficient. -/
theorem perronThirdBalancedCharge {a : ℕ → ℂ} {c : ℝ} (hc : 0 < c)
    (hsum : LSeriesSummable a c) {n : ℕ} {δ : ℝ}
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ : δ < 2 / 3) :
    a n * (3 * (δ : ℂ) ^ 2 / 4) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) *
          perronThirdBalancedE n δ ((c : ℂ) + (t : ℂ) * I) := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := perronThird_knots_pos hn hδ0 hδ
  let K : ℝ → ℝ → ℂ := fun x t =>
    LSeries a ((c : ℂ) + (t : ℂ) * I) *
      ((x : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 2) *
        mellin balancedPerronKernelG ((c : ℂ) + (t : ℂ) * I))
  have hI0 : Integrable (K (perronThirdX0 n δ)) := balanced_perron_integrable hc hsum hx0
  have hI1 : Integrable (K (perronThirdX1 n δ)) := balanced_perron_integrable hc hsum hx1
  have hI2 : Integrable (K (perronThirdX2 n δ)) := balanced_perron_integrable hc hsum hx2
  have hI3 : Integrable (K (perronThirdX3 n δ)) := balanced_perron_integrable hc hsum hx3
  have hpt : ∀ t : ℝ,
      LSeries a ((c : ℂ) + (t : ℂ) * I) *
          perronThirdBalancedE n δ ((c : ℂ) + (t : ℂ) * I) =
        K (perronThirdX0 n δ) t - 3 * K (perronThirdX1 n δ) t +
          3 * K (perronThirdX2 n δ) t - K (perronThirdX3 n δ) t := by
    intro t
    set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
    have hs0 : s ≠ 0 := by
      intro h
      have hreal := congrArg Complex.re h
      rw [hs] at hreal
      simp at hreal
      linarith
    have hs1 : s ≠ -1 := by
      intro h
      have hreal := congrArg Complex.re h
      rw [hs] at hreal
      simp at hreal
      linarith
    have hs2 : s ≠ -2 := by
      intro h
      have hreal := congrArg Complex.re h
      rw [hs] at hreal
      norm_num at hreal
      linarith
    have hsre : 0 < s.re := by rw [hs]; simp; exact hc
    simp only [K]
    rw [perronThirdBalancedE, perronThirdE_eq n δ hs0 hs1 hs2,
      balancedPerronKernel_mellin hsre]
    unfold perronThirdKink
    ring
  rw [← balancedPerronWeight_third_difference a hn hδ0 hδ,
    balanced_perron_sum hc hsum hx0, balanced_perron_sum hc hsum hx1,
    balanced_perron_sum hc hsum hx2, balanced_perron_sum hc hsum hx3]
  have hcomb :
      (∫ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) *
          perronThirdBalancedE n δ ((c : ℂ) + (t : ℂ) * I)) =
        (∫ t : ℝ, K (perronThirdX0 n δ) t) -
          3 * (∫ t : ℝ, K (perronThirdX1 n δ) t) +
          3 * (∫ t : ℝ, K (perronThirdX2 n δ) t) -
          (∫ t : ℝ, K (perronThirdX3 n δ) t) := by
    calc
      (∫ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) *
          perronThirdBalancedE n δ ((c : ℂ) + (t : ℂ) * I)) =
          ∫ t : ℝ, K (perronThirdX0 n δ) t - 3 * K (perronThirdX1 n δ) t +
            3 * K (perronThirdX2 n δ) t - K (perronThirdX3 n δ) t :=
        MeasureTheory.integral_congr_ae (Eventually.of_forall hpt)
      _ = _ := by
        have h01 :
            (∫ t : ℝ, K (perronThirdX0 n δ) t - 3 * K (perronThirdX1 n δ) t) =
              (∫ t : ℝ, K (perronThirdX0 n δ) t) -
                3 * (∫ t : ℝ, K (perronThirdX1 n δ) t) := by
          rw [MeasureTheory.integral_sub hI0 (hI1.const_mul 3),
            MeasureTheory.integral_const_mul]
        have h012 :
            (∫ t : ℝ, (K (perronThirdX0 n δ) t - 3 * K (perronThirdX1 n δ) t) +
              3 * K (perronThirdX2 n δ) t) =
              ((∫ t : ℝ, K (perronThirdX0 n δ) t) -
                3 * (∫ t : ℝ, K (perronThirdX1 n δ) t)) +
                3 * (∫ t : ℝ, K (perronThirdX2 n δ) t) := by
          have hadd := MeasureTheory.integral_add (hI0.sub (hI1.const_mul 3))
            (hI2.const_mul 3)
          calc
            (∫ t : ℝ, (K (perronThirdX0 n δ) t - 3 * K (perronThirdX1 n δ) t) +
                3 * K (perronThirdX2 n δ) t) =
                (∫ t : ℝ, K (perronThirdX0 n δ) t - 3 * K (perronThirdX1 n δ) t) +
                  ∫ t : ℝ, 3 * K (perronThirdX2 n δ) t := by
              simpa only [Pi.sub_apply, Pi.add_apply] using hadd
            _ = _ := by rw [h01, MeasureTheory.integral_const_mul]
        have hsub := MeasureTheory.integral_sub
          ((hI0.sub (hI1.const_mul 3)).add (hI2.const_mul 3)) hI3
        calc
          (∫ t : ℝ, K (perronThirdX0 n δ) t - 3 * K (perronThirdX1 n δ) t +
              3 * K (perronThirdX2 n δ) t - K (perronThirdX3 n δ) t) =
              (∫ t : ℝ, (K (perronThirdX0 n δ) t - 3 * K (perronThirdX1 n δ) t) +
                3 * K (perronThirdX2 n δ) t) -
                ∫ t : ℝ, K (perronThirdX3 n δ) t := by
            simpa only [Pi.sub_apply, Pi.add_apply] using hsub
          _ = _ := by rw [h012]
  rw [hcomb]
  simp only [Complex.real_smul]
  ring

/-! ## 4. Entire boundary decompletion and the scalar no-go -/

private theorem Gammaℝ_inv_zero : (Gammaℝ 0)⁻¹ = 0 := by
  rw [Gammaℝ_def]
  simp

/-- The entire boundary-balanced decompletion.  Away from `s=0` it is
`2/(s Gammaℝ(s))`; the zero of `Gammaℝ⁻¹` at the origin removes the apparent pole. -/
def boundaryDecompletion : ℂ → ℂ := fun s =>
  2 * dslope (fun z : ℂ => (Gammaℝ z)⁻¹) 0 s

theorem boundaryDecompletion_differentiable : Differentiable ℂ boundaryDecompletion := by
  have hd : Differentiable ℂ (dslope (fun z : ℂ => (Gammaℝ z)⁻¹) 0) := by
    rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
    exact differentiable_Gammaℝ_inv.differentiableOn
  exact hd.const_mul 2

theorem boundaryDecompletion_eq {s : ℂ} (h0 : s ≠ 0) :
    boundaryDecompletion s = 2 * (Gammaℝ s)⁻¹ / s := by
  unfold boundaryDecompletion
  rw [dslope_of_ne _ h0, slope_def_field, Gammaℝ_inv_zero, sub_zero, sub_zero]
  ring

/-- The completed archimedean factor times the entire decompletion is exactly the boundary
multiplier `s-1`. -/
theorem archFactor_mul_boundaryDecompletion {s : ℂ} (h0 : s ≠ 0)
    (hG : Gammaℝ s ≠ 0) :
    archFactor s * boundaryDecompletion s = s - 1 := by
  rw [boundaryDecompletion_eq h0]
  unfold archFactor
  field_simp

/-- **Scalar uniqueness.**  At a nonzero, non-boundary, non-Gamma point, any scalar decompletion
that turns `archFactor` into `s-1` is forced to be `boundaryDecompletion`.  Thus an exact
pointwise scalar arithmetic probe has no freedom to retain the Gamma factor. -/
theorem boundaryDecompletion_unique {K : ℂ → ℂ} {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hG : Gammaℝ s ≠ 0)
    (hK : archFactor s * K s = s - 1) :
    K s = boundaryDecompletion s := by
  have haf : archFactor s ≠ 0 := archFactor_ne_zero h0 h1 hG
  apply mul_left_cancel₀ haf
  rw [hK, archFactor_mul_boundaryDecompletion h0 hG]

/-- For `xi`, scalar decompletion is exactly the pole-cancelled raw zeta carrier.  This identity is
the formal obstruction: the Gamma decay has been cancelled, not moved into a new coordinate. -/
theorem xi_mul_boundaryDecompletion {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) :
    xi s * boundaryDecompletion s = (s - 1) * riemannZeta s := by
  rw [xi_eq_archFactor_mul_zeta h0 h1 hG]
  calc
    archFactor s * riemannZeta s * boundaryDecompletion s =
        (archFactor s * boundaryDecompletion s) * riemannZeta s := by ring
    _ = (s - 1) * riemannZeta s := by
      rw [archFactor_mul_boundaryDecompletion h0 hG]

/-! ## 5. Completed Dirichlet coefficient extraction -/

/-- **Completed third-order coefficient charge.**  A carrier that is `archFactor * LSeries` on the
right edge admits an exact entire scalar coefficient probe.  No auxiliary decomposition Prop is
needed: the pointwise completed-shape identity is composed directly with the balanced charge. -/
theorem completedPerronThirdCharge {F : ℂ → ℂ} {a : ℕ → ℂ} {c : ℝ}
    (hc : 0 < c) (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = archFactor s * LSeries a s)
    {n : ℕ} {δ : ℝ} (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ : δ < 2 / 3) :
    a n * (3 * (δ : ℂ) ^ 2 / 4) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, F ((c : ℂ) + (t : ℂ) * I) *
          boundaryDecompletion ((c : ℂ) + (t : ℂ) * I) *
            perronThirdE n δ ((c : ℂ) + (t : ℂ) * I) := by
  calc
    a n * (3 * (δ : ℂ) ^ 2 / 4) =
        (1 / (2 * Real.pi) : ℝ) •
          ∫ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) *
            perronThirdBalancedE n δ ((c : ℂ) + (t : ℂ) * I) :=
      perronThirdBalancedCharge hc hsum hn hδ0 hδ
    _ = _ := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
      have hsre : s.re = c := by rw [hs]; simp
      have hs0 : s ≠ 0 := by
        intro h
        have hreal := congrArg Complex.re h
        rw [hsre] at hreal
        simp at hreal
        linarith
      have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; exact hc)
      rw [hFeq s (by rw [hsre])]
      unfold perronThirdBalancedE
      rw [← archFactor_mul_boundaryDecompletion hs0 hG]
      ring

/-- **Concrete completed zeta charge.**  Every coefficient of zeta is `1`, so the entire scalar
probe of `xi` has right-edge charge exactly `3δ²/4`. -/
theorem xi_completedPerronThirdCharge {c : ℝ} (hc : 1 < c)
    {n : ℕ} {δ : ℝ} (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ : δ < 2 / 3) :
    (3 * (δ : ℂ) ^ 2 / 4) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, xi ((c : ℂ) + (t : ℂ) * I) *
          boundaryDecompletion ((c : ℂ) + (t : ℂ) * I) *
            perronThirdE n δ ((c : ℂ) + (t : ℂ) * I) := by
  have hsum : LSeriesSummable (1 : ℕ → ℂ) c := (LSeriesHasSum_one hc).summable
  have hshape : ∀ s : ℂ, c ≤ s.re →
      xi s = archFactor s * LSeries (1 : ℕ → ℂ) s := by
    intro s hs
    have hs1 : 1 < s.re := lt_of_lt_of_le hc hs
    have hs0 : 0 < s.re := lt_trans (by norm_num) hs1
    have h0 : s ≠ 0 := by
      intro h
      rw [h] at hs0
      simp at hs0
    have h1 : s ≠ 1 := by
      intro h
      rw [h] at hs1
      simp at hs1
    have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
    rw [xi_eq_archFactor_mul_zeta h0 h1 hG, ← LSeries_one_eq_riemannZeta hs1]
  have hcharge := completedPerronThirdCharge (F := xi) (by linarith : 0 < c)
    hsum hshape hn hδ0 hδ
  simpa using hcharge

end RHTower

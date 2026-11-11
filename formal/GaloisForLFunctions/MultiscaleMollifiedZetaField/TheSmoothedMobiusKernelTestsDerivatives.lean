import GaloisForLFunctions.RHTower.Sieve.MoebiusLogPowerHomogeneousBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The smoothed Möbius kernel under logarithmic dilation

The bounded kernel `Σ μ(n) log(exp(y)/n)/n` tends to one.
Its finite positive-part representation gives continuity across cutoff jumps,
which permits dominated convergence against fixed smooth test functions.
-/

open ArithmeticFunction Filter MeasureTheory Set Topology
open RHTower.Sieve
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The first smoothed logarithmic Möbius kernel, in logarithmic coordinates. -/
def smoothedMobiusKernel (y : ℝ) : ℝ := moebiusLogPowerKernelReal 1 (Real.exp y)

/-- Above a bounded logarithmic interval one fixed finite sum represents every cutoff. -/
theorem smoothedMobiusKernel_eq_finite_max {H y : ℝ} (hy : 0 ≤ y) (hyH : y ≤ H) :
    smoothedMobiusKernel y =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp H⌋₊,
        ((moebius n : ℤ) : ℝ) / (n : ℝ) * max (y - Real.log n) 0 := by
  have hsub : Finset.Icc 1 ⌊Real.exp y⌋₊ ⊆ Finset.Icc 1 ⌊Real.exp H⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (Real.exp_le_exp.mpr hyH))
  unfold smoothedMobiusKernel moebiusLogPowerKernelReal
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ (⌊Real.exp y⌋₊ : ℕ) := by
      exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hnexp : (n : ℝ) ≤ Real.exp y := hnN.trans (Nat.floor_le (Real.exp_pos y).le)
    have hnlog : Real.log n ≤ y := by
      simpa only [Real.log_exp] using Real.log_le_log hn0 hnexp
    rw [Real.log_div (Real.exp_pos y).ne' hn0.ne', Real.log_exp,
      pow_one, max_eq_left (sub_nonneg.mpr hnlog)]
  · intro n hn hnsmall
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnlarge : ⌊Real.exp y⌋₊ < n := by
      by_contra h
      exact hnsmall (Finset.mem_Icc.mpr ⟨hn1, le_of_not_gt h⟩)
    have hnexp : Real.exp y < n := (Nat.floor_lt (Real.exp_pos y).le).mp hnlarge
    have hnlog : y < Real.log n := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos y) hnexp
    rw [max_eq_right (by linarith only [hnlog]), mul_zero]

/-- Positive-part summands remove every apparent floor discontinuity. -/
theorem continuousOn_smoothedMobiusKernel {H : ℝ} (hH : 0 ≤ H) :
    ContinuousOn smoothedMobiusKernel (Icc 0 H) := by
  have hc : Continuous (fun y : ℝ => ∑ n ∈ Finset.Icc 1 ⌊Real.exp H⌋₊,
      ((moebius n : ℤ) : ℝ) / (n : ℝ) * max (y - Real.log n) 0) := by fun_prop
  exact hc.continuousOn.congr (fun y hy => smoothedMobiusKernel_eq_finite_max hy.1 hy.2)

/-- The globally bounded logarithmic kernel converges to one. -/
theorem smoothedMobiusKernel_bounded_and_tendsto :
    (∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ, 0 ≤ y → |smoothedMobiusKernel y| ≤ D) ∧
      Tendsto smoothedMobiusKernel atTop (𝓝 1) := by
  constructor
  · obtain ⟨D, hD, hb⟩ := exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow 0
    refine ⟨D, hD, fun y hy => ?_⟩
    simpa only [Nat.zero_add, pow_zero, mul_one, smoothedMobiusKernel] using
      hb (Real.exp y) (Real.one_le_exp hy)
  · have hh := (tendsto_moebiusLogPowerKernelReal_div_log_pow 0).comp Real.tendsto_exp_atTop
    change Tendsto (fun y => moebiusLogPowerKernelReal 1 (Real.exp y)) atTop (𝓝 1)
    simpa only [Nat.zero_add, Nat.cast_one, pow_zero, div_one, Function.comp_def,
      smoothedMobiusKernel] using hh

/-- Every fixed continuous test sees the limiting constant under logarithmic dilation. -/
theorem tendsto_integral_smoothedMobiusKernel_dilation {u : ℝ} (hu : 0 < u)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 u)) :
    Tendsto (fun L : ℝ => ∫ x in (0 : ℝ)..u, g x * smoothedMobiusKernel (L * x))
      atTop (𝓝 (∫ x in (0 : ℝ)..u, g x)) := by
  obtain ⟨⟨D, hD, hb⟩, hlim⟩ := smoothedMobiusKernel_bounded_and_tendsto
  have hmeas : ∀ᶠ L : ℝ in atTop,
      AEStronglyMeasurable (fun x => g x * smoothedMobiusKernel (L * x))
        (volume.restrict (uIoc 0 u)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    have hK := continuousOn_smoothedMobiusKernel (mul_nonneg hL hu.le)
    have hm : MapsTo (fun x => L * x) (Icc 0 u) (Icc 0 (L * u)) :=
      fun x hx => ⟨mul_nonneg hL hx.1, mul_le_mul_of_nonneg_left hx.2 hL⟩
    have hc := hg.mul (hK.comp (continuous_const.mul continuous_id).continuousOn hm)
    rw [uIoc_of_le hu.le]
    exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᶠ L : ℝ in atTop, ∀ᵐ x : ℝ,
      x ∈ uIoc (0 : ℝ) u → ‖g x * smoothedMobiusKernel (L * x)‖ ≤ |g x| * D := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    filter_upwards with x
    intro hx
    rw [uIoc_of_le hu.le] at hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hb _ (mul_nonneg hL hx.1.le)) (abs_nonneg _)
  have hpoint : ∀ᵐ x : ℝ, x ∈ uIoc (0 : ℝ) u →
      Tendsto (fun L : ℝ => g x * smoothedMobiusKernel (L * x)) atTop (𝓝 (g x)) := by
    filter_upwards with x
    intro hx
    rw [uIoc_of_le hu.le] at hx
    simpa only [mul_one, Function.comp_def, id_eq] using (hlim.comp (tendsto_id.atTop_mul_const hx.1)).const_mul (g x)
  have hi : IntervalIntegrable (fun x => |g x| * D) volume 0 u :=
    (hg.abs.mul continuous_const.continuousOn).intervalIntegrable_of_Icc hu.le
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => |g x| * D) hmeas hbound hi hpoint

private theorem integral_linear_second_jet {f f₁ f₂ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hc₂ : Continuous f₂) (u a : ℝ) :
    (∫ x in a..u, f₂ (u - x) * (x - a)) =
      f (u - a) - f 0 - (u - a) * f₁ 0 := by
  have hder (x : ℝ) : HasDerivAt
      (fun x => -(x - a) * f₁ (u - x) - f (u - x))
      (f₂ (u - x) * (x - a)) x := by
    have h₀ : HasDerivAt (fun x => f (u - x)) (-f₁ (u - x)) x :=
      ((hf (u - x)).comp x ((hasDerivAt_id x).const_sub u)).congr_deriv (by ring)
    have h₁ : HasDerivAt (fun x => f₁ (u - x)) (-f₂ (u - x)) x :=
      ((hf₁ (u - x)).comp x ((hasDerivAt_id x).const_sub u)).congr_deriv (by ring)
    have hh := ((((hasDerivAt_id x).sub_const a).neg).mul h₁).sub h₀
    apply hh.congr_deriv
    simp only [Pi.neg_apply, id_eq]
    ring
  have hi : IntervalIntegrable (fun x => f₂ (u - x) * (x - a)) volume a u :=
    ((hc₂.comp (continuous_const.sub continuous_id)).mul
      (continuous_id.sub continuous_const)).intervalIntegrable a u
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x) hi
  refine hh.trans ?_
  simp only [sub_self, neg_zero, zero_mul]
  ring

/-- Twice-integrated finite cutoffs depend only on the bounded first logarithmic kernel. -/
theorem integral_positive_part_second_jet {f f₁ f₂ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hc₂ : Continuous f₂) {L u a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hau : a ≤ u) :
    (∫ x in (0 : ℝ)..u, f₂ (u - x) * max (L * (x - a)) 0) =
      L * (f (u - a) - f 0 - (u - a) * f₁ 0) := by
  have hc : Continuous (fun x => f₂ (u - x) * max (L * (x - a)) 0) := by fun_prop
  have hleft : (∫ x in (0 : ℝ)..a, f₂ (u - x) * max (L * (x - a)) 0) = 0 := by
    calc
      _ = ∫ _ : ℝ in (0 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ha] at hx
        dsimp only
        rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hL.le (sub_nonpos.mpr hx.2)), mul_zero]
      _ = 0 := by simp
  have hright : (∫ x in a..u, f₂ (u - x) * max (L * (x - a)) 0) =
      L * (∫ x in a..u, f₂ (u - x) * (x - a)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hau] at hx
    dsimp only
    rw [max_eq_left (mul_nonneg hL.le (sub_nonneg.mpr hx.1))]
    ring
  have hs := intervalIntegral.integral_add_adjacent_intervals («μ» := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a u)
  rw [hleft, hright, zero_add, integral_linear_second_jet hf hf₁ hc₂ u a] at hs
  exact hs.symm

/-- A smooth logarithmic test is an exact linear-cutoff term plus its second-jet integral. -/
theorem mobius_log_test_eq_kernel_integral {f f₁ f₂ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hc₂ : Continuous f₂) (hf0 : f 0 = 0) {L u : ℝ} (hL : 0 < L) (hu : 0 ≤ u) :
    L * (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L * u)⌋₊,
      ((moebius n : ℤ) : ℝ) / (n : ℝ) * f (u - Real.log n / L)) =
      f₁ 0 * smoothedMobiusKernel (L * u) +
        ∫ x in (0 : ℝ)..u, f₂ (u - x) * smoothedMobiusKernel (L * x) := by
  let S := Finset.Icc 1 ⌊Real.exp (L * u)⌋₊
  let c : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ) / (n : ℝ)
  have hdata (n : ℕ) (hn : n ∈ S) : 0 ≤ Real.log n ∧ Real.log n ≤ L * u := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ (⌊Real.exp (L * u)⌋₊ : ℕ) := by
      exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hnexp : (n : ℝ) ≤ Real.exp (L * u) := hnN.trans (Nat.floor_le (Real.exp_pos _).le)
    exact ⟨Real.log_nonneg hn1, by
      simpa only [Real.log_exp] using Real.log_le_log (zero_lt_one.trans_le hn1) hnexp⟩
  have hi : (∫ x in (0 : ℝ)..u, f₂ (u - x) * smoothedMobiusKernel (L * x)) =
      ∑ n ∈ S, c n * L *
        (f (u - Real.log n / L) - (u - Real.log n / L) * f₁ 0) := by
    calc
      _ = ∫ x in (0 : ℝ)..u, ∑ n ∈ S,
          c n * (f₂ (u - x) * max (L * (x - Real.log n / L)) 0) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hu] at hx
        dsimp only
        rw [smoothedMobiusKernel_eq_finite_max (mul_nonneg hL.le hx.1)
          (mul_le_mul_of_nonneg_left hx.2 hL.le), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        have he : L * (x - Real.log n / L) = L * x - Real.log n := by
          field_simp [hL.ne'] <;> ring
        rw [he]
        dsimp only [c]
        ring
      _ = ∑ n ∈ S, ∫ x in (0 : ℝ)..u,
          c n * (f₂ (u - x) * max (L * (x - Real.log n / L)) 0) := by
        apply intervalIntegral.integral_finsetSum
        intro n hn
        exact (by fun_prop : Continuous (fun x =>
          c n * (f₂ (u - x) * max (L * (x - Real.log n / L)) 0))).intervalIntegrable 0 u
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [intervalIntegral.integral_const_mul,
          integral_positive_part_second_jet hf hf₁ hc₂ hL
            (div_nonneg (hdata n hn).1 hL.le) ((div_le_iff₀ hL).mpr (by
              simpa only [mul_comm] using (hdata n hn).2)), hf0, sub_zero]
        ring
  rw [hi, smoothedMobiusKernel_eq_finite_max (mul_nonneg hL.le hu) le_rfl]
  change L * (∑ n ∈ S, c n * f (u - Real.log n / L)) =
    f₁ 0 * (∑ n ∈ S, c n * max (L * u - Real.log n) 0) + _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [max_eq_left (sub_nonneg.mpr (hdata n hn).2)]
  field_simp [hL.ne'] <;> ring

/-- Logarithmically rescaled Möbius coefficients evaluate the first derivative of every smooth test. -/
theorem tendsto_mobius_log_test {f f₁ f₂ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hc₂ : Continuous f₂) (hf0 : f 0 = 0) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun L : ℝ => L * (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L * u)⌋₊,
      ((moebius n : ℤ) : ℝ) / (n : ℝ) * f (u - Real.log n / L)))
      atTop (𝓝 (f₁ u)) := by
  have hfirst := (smoothedMobiusKernel_bounded_and_tendsto.2.comp
    (tendsto_id.atTop_mul_const hu)).const_mul (f₁ 0)
  simp only [Function.comp_def, id_eq] at hfirst
  have hsecond := tendsto_integral_smoothedMobiusKernel_dilation hu (g := fun x => f₂ (u - x))
    ((hc₂.comp (continuous_const.sub continuous_id)).continuousOn)
  have heval : (∫ x in (0 : ℝ)..u, f₂ (u - x)) = f₁ u - f₁ 0 := by
    have hd (x : ℝ) : HasDerivAt (fun x => -f₁ (u - x)) (f₂ (u - x)) x := by
      exact (((hf₁ (u - x)).comp x ((hasDerivAt_id x).const_sub u)).neg).congr_deriv (by ring)
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((hc₂.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 u)
    exact hh.trans (by simp only [sub_self, sub_zero]; ring)
  have hh := hfirst.add hsecond
  rw [mul_one, heval, show f₁ 0 + (f₁ u - f₁ 0) = f₁ u by ring] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact (mobius_log_test_eq_kernel_integral hf hf₁ hc₂ hf0 hL hu.le).symm

/-- The logarithmic Möbius kernel with a power shift on its natural scaling ray. -/
def powerShiftedMobiusKernel (L u v : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L * u)⌋₊,
    ((moebius n : ℤ) : ℝ) / (n : ℝ) * Real.exp (v * Real.log n / L) * (L * u - Real.log n)

/-- A reciprocal-logarithmic power shift changes the linear kernel limit from one to `1−vu`. -/
theorem tendsto_powerShiftedMobiusKernel {u : ℝ} (hu : 0 < u) (v : ℝ) :
    Tendsto (fun L => powerShiftedMobiusKernel L u v) atTop (𝓝 (1 - v * u)) := by
  let f : ℝ → ℝ := fun x => x * Real.exp (-v * x)
  let f₁ : ℝ → ℝ := fun x => (1 - v * x) * Real.exp (-v * x)
  let f₂ : ℝ → ℝ := fun x => (v ^ 2 * x - 2 * v) * Real.exp (-v * x)
  have he (x : ℝ) : HasDerivAt (fun x => Real.exp (-v * x))
      (-v * Real.exp (-v * x)) x := by
    exact ((Real.hasDerivAt_exp _).comp x ((hasDerivAt_id x).const_mul (-v))).congr_deriv (by simp only [id_eq]; ring)
  have hf (x : ℝ) : HasDerivAt f (f₁ x) x := by
    apply ((hasDerivAt_id x).mul (he x)).congr_deriv
    dsimp only [f₁, id_eq]
    ring
  have hf₁ (x : ℝ) : HasDerivAt f₁ (f₂ x) x := by
    apply ((((hasDerivAt_id x).const_mul v).const_sub 1).mul (he x)).congr_deriv
    dsimp only [f₂, id_eq]
    ring
  have hc₂ : Continuous f₂ := by dsimp only [f₂]; fun_prop
  have hh := (tendsto_mobius_log_test hf hf₁ hc₂ (by simp [f]) hu).const_mul (Real.exp (v * u))
  have hvalue : Real.exp (v * u) * f₁ u = 1 - v * u := by
    have he' : Real.exp (v * u) * Real.exp (-v * u) = 1 := by
      rw [← Real.exp_add, show v * u + -v * u = 0 by ring, Real.exp_zero]
    dsimp only [f₁]
    calc
      _ = (1 - v * u) * (Real.exp (v * u) * Real.exp (-v * u)) := by ring
      _ = _ := by rw [he', mul_one]
  rw [hvalue] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  unfold powerShiftedMobiusKernel
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hexp : Real.exp (v * u) * Real.exp (-v * (u - Real.log n / L)) =
      Real.exp (v * Real.log n / L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlinear : L * (u - Real.log n / L) = L * u - Real.log n := by
    field_simp [hL.ne'] <;> ring
  dsimp only [f]
  calc
    _ = (((moebius n : ℤ) : ℝ) / (n : ℝ)) *
        (Real.exp (v * u) * Real.exp (-v * (u - Real.log n / L))) *
        (L * (u - Real.log n / L)) := by ring
    _ = _ := by rw [hexp, hlinear]

end GaloisForLFunctions.MultiscaleMollifiedZetaField

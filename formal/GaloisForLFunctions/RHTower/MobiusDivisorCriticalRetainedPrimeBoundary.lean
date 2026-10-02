import GaloisForLFunctions.RHTower.MobiusDivisorCriticalAbelBoundaryMoments
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Right boundary slope with the retained prime cutoff

The prime cutoff stays inside the source integral. Its logarithmic harmonic
moment is dominated by the actual Abel source's absolute quadratic moment.
This admits a right derivative without assuming a power saving or extending
the transform to an open neighborhood of its boundary.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

/-- Prime indices at most the real source coordinate, including its endpoint. -/
def retainedPrimeCutoff (y : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊y⌋₊).filter Nat.Prime

/-- The finite harmonic prime kernel with its complete boundary damping. -/
def retainedPrimeBoundaryKernel (δ y : ℝ) : ℝ :=
  ∑ p ∈ retainedPrimeCutoff y,
    (p : ℝ)⁻¹ * Real.exp (-δ * (Real.log p + Real.log y))

/-- The first logarithmic moment of the retained finite prime kernel. -/
def retainedPrimeBoundaryMoment (y : ℝ) : ℝ :=
  ∑ p ∈ retainedPrimeCutoff y, (p : ℝ)⁻¹ * (Real.log p + Real.log y)

/-- Boundary transform with the actual retained cutoff `p ≤ y` inside its
source integral. The relation to the moving square-root prime head is a
separate change-of-variables identity. -/
def criticalRetainedPrimeBoundaryTransform (δ : ℝ) : ℝ :=
  ∫ y in Ioi (1 : ℝ), criticalContinuousAbel y / y ^ (5 / 2 : ℝ) *
    retainedPrimeBoundaryKernel δ y

/-- Measurability of the literal Abel source, from its exact unit-cell formula. -/
theorem measurable_criticalContinuousAbel : Measurable criticalContinuousAbel := by
  let g : ℝ → ℝ := fun x => criticalContinuousAbel (⌊x⌋₊ : ℝ) +
    (Real.sqrt x - Real.sqrt (⌊x⌋₊ : ℝ)) * psiDefect ⌊x⌋₊
  have hg : Measurable g := by
    have hm : Measurable (fun x : ℝ => ⌊x⌋₊) := measurable_id.nat_floor
    exact ((measurable_of_countable (fun n : ℕ => criticalContinuousAbel n)).comp hm).add
      ((measurable_id.sqrt.sub
        ((measurable_of_countable (fun n : ℕ => Real.sqrt n)).comp hm)).mul
          ((measurable_of_countable psiDefect).comp hm))
  have he : criticalContinuousAbel = fun x : ℝ => if 1 < x then g x else 0 := by
    funext x
    split_ifs with hx
    · have hx0 : 0 ≤ x := by linarith
      have hk : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx.le)
      have he := congrArg Complex.re (squareRootSummatoryPrimitive_between
        criticalSourceCoeff hk (Nat.floor_le hx0)
        (show x ≤ (⌊x⌋₊ + 1 : ℕ) by exact_mod_cast (Nat.lt_floor_add_one x).le))
      rw [criticalSourceCoeff_cumulative _ hk] at he
      simpa only [criticalContinuousAbel, g, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero] using he
    · rw [criticalContinuousAbel, squareRootSummatoryPrimitive_eq_integral]
      simp [Set.Ioo_eq_empty_of_le (le_of_not_gt hx)]
  rw [he]
  exact Measurable.ite measurableSet_Ioi hg measurable_const

private theorem measurable_retainedPrimeBoundaryKernel (δ : ℝ) :
    Measurable (retainedPrimeBoundaryKernel δ) := by
  have hm : Measurable (fun z : ℕ × ℝ =>
      ∑ p ∈ (Finset.Icc 1 z.1).filter Nat.Prime,
        (p : ℝ)⁻¹ * Real.exp (-δ * (Real.log p + Real.log z.2))) := by
    apply measurable_from_prod_countable_right
    intro N
    dsimp only
    apply Finset.measurable_sum
    intro p _
    fun_prop
  exact hm.comp (measurable_id.nat_floor.prodMk measurable_id)

private theorem retainedPrimeCutoff_data {y : ℝ} {p : ℕ}
    (hp : p ∈ retainedPrimeCutoff y) : 0 < (p : ℝ) ∧ 1 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y := by
  obtain ⟨hpN, hprime⟩ := Finset.mem_filter.mp hp
  have hp1 := (Finset.mem_Icc.mp hpN).1
  have hpy := (Finset.mem_Icc.mp hpN).2
  refine ⟨by exact_mod_cast hprime.pos, by exact_mod_cast hp1, ?_⟩
  exact (Nat.le_floor_iff (by
    have : 0 < ⌊y⌋₊ := lt_of_lt_of_le hprime.pos hpy
    exact (Nat.floor_pos.mp this).trans' (by norm_num))).mp hpy

private theorem retainedPrime_harmonic_le {y : ℝ} (hy : 1 ≤ y) :
    (∑ p ∈ retainedPrimeCutoff y, (p : ℝ)⁻¹) ≤ 1 + Real.log y := by
  calc
    _ ≤ ∑ p ∈ Finset.Icc 1 ⌊y⌋₊, (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = (harmonic ⌊y⌋₊ : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := harmonic_floor_le_one_add_log y hy

private theorem retainedPrimeBoundaryMoment_bound {y : ℝ} (hy : 1 < y) :
    retainedPrimeBoundaryMoment y ≤ 3 * (1 + Real.log y ^ (2 : ℕ)) := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy.le
  calc
    _ ≤ ∑ p ∈ retainedPrimeCutoff y, (p : ℝ)⁻¹ * (2 * Real.log y) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp0, _, hpy⟩ := retainedPrimeCutoff_data hp
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp0.le)
      have := Real.log_le_log hp0 hpy
      linarith
    _ = (∑ p ∈ retainedPrimeCutoff y, (p : ℝ)⁻¹) * (2 * Real.log y) := by
      rw [Finset.sum_mul]
    _ ≤ (1 + Real.log y) * (2 * Real.log y) :=
      mul_le_mul_of_nonneg_right (retainedPrime_harmonic_le hy.le) (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg (Real.log y - 1)]

private theorem retainedPrimeBoundaryKernel_bound {δ y : ℝ}
    (hδ : 0 ≤ δ) (hy : 1 < y) :
    |retainedPrimeBoundaryKernel δ y| ≤ 3 * (1 + Real.log y ^ (2 : ℕ)) := by
  have hnonneg : 0 ≤ retainedPrimeBoundaryKernel δ y :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ ∑ p ∈ retainedPrimeCutoff y, (p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp0, hp1, _⟩ := retainedPrimeCutoff_data hp
      have he : Real.exp (-δ * (Real.log p + Real.log y)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr hδ) (add_nonneg (Real.log_nonneg hp1) (Real.log_nonneg hy.le)))
      simpa using mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp0.le)
    _ ≤ 1 + Real.log y := retainedPrime_harmonic_le hy.le
    _ ≤ _ := by nlinarith [sq_nonneg (Real.log y - 1)]

private theorem exp_negative_slope_bound {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    |(Real.exp (-δ * t) - 1) / δ| ≤ t := by
  have he : Real.exp (-δ * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) ht)
  rw [abs_div, abs_of_pos hδ, abs_of_nonpos (sub_nonpos.mpr he)]
  apply (div_le_iff₀ hδ).mpr
  have := Real.add_one_le_exp (-δ * t)
  nlinarith

private theorem retainedPrimeBoundaryKernel_slope_bound {δ y : ℝ}
    (hδ : 0 < δ) (hy : 1 < y) :
    |(retainedPrimeBoundaryKernel δ y - retainedPrimeBoundaryKernel 0 y) / δ| ≤
      3 * (1 + Real.log y ^ (2 : ℕ)) := by
  have he : (retainedPrimeBoundaryKernel δ y - retainedPrimeBoundaryKernel 0 y) / δ =
      ∑ p ∈ retainedPrimeCutoff y, (p : ℝ)⁻¹ *
        ((Real.exp (-δ * (Real.log p + Real.log y)) - 1) / δ) := by
    simp only [retainedPrimeBoundaryKernel, neg_zero, zero_mul, Real.exp_zero, mul_one]
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he]
  apply ((Finset.abs_sum_le_sum_abs _ _).trans _).trans (retainedPrimeBoundaryMoment_bound hy)
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp0, hp1, _⟩ := retainedPrimeCutoff_data hp
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hp0.le)]
  exact mul_le_mul_of_nonneg_left (exp_negative_slope_bound hδ
    (add_nonneg (Real.log_nonneg hp1) (Real.log_nonneg hy.le))) (inv_nonneg.mpr hp0.le)

private theorem retainedPrimeBoundaryKernel_slope (y : ℝ) :
    Tendsto (fun δ : ℝ =>
      (retainedPrimeBoundaryKernel δ y - retainedPrimeBoundaryKernel 0 y) / δ)
      (𝓝[>] 0) (𝓝 (-retainedPrimeBoundaryMoment y)) := by
  have hd (p : ℕ) : HasDerivAt
      (fun δ : ℝ => (p : ℝ)⁻¹ * Real.exp (-δ * (Real.log p + Real.log y)))
      (-(p : ℝ)⁻¹ * (Real.log p + Real.log y)) 0 := by
    simpa only [Pi.neg_apply, id_eq, neg_zero, zero_mul, Real.exp_zero,
      one_mul, neg_one_mul, mul_neg, neg_mul]
      using (((hasDerivAt_id (0 : ℝ)).neg.mul_const
        (Real.log p + Real.log y)).exp.const_mul (p : ℝ)⁻¹)
  have hs := (HasDerivAt.fun_sum (fun p (_ : p ∈ retainedPrimeCutoff y) => hd p)).tendsto_slope_zero_right
  convert hs using 1
  · funext δ
    simp only [zero_add, smul_eq_mul, retainedPrimeBoundaryKernel]
    ring
  · congr 1
    simp only [retainedPrimeBoundaryMoment, ← Finset.sum_neg_distrib, neg_mul]

private def retainedPrimeBoundaryMajorant (y : ℝ) : ℝ :=
  3 * (|criticalContinuousAbel y| * (1 + Real.log y ^ (2 : ℕ)) / y ^ (5 / 2 : ℝ))

private theorem retainedPrimeBoundary_integrable_majorant :
    IntegrableOn retainedPrimeBoundaryMajorant (Ioi (1 : ℝ)) :=
  integrableOn_criticalContinuousAbel_boundary_log_sq.const_mul 3

private theorem retainedPrimeBoundary_weighted_bound {y b : ℝ} (hy : 1 < y)
    (hb : |b| ≤ 3 * (1 + Real.log y ^ (2 : ℕ))) :
    ‖criticalContinuousAbel y / y ^ (5 / 2 : ℝ) * b‖ ≤ retainedPrimeBoundaryMajorant y := by
  have hp : 0 < y ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hp]
  calc
    _ ≤ |criticalContinuousAbel y| / y ^ (5 / 2 : ℝ) *
        (3 * (1 + Real.log y ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by dsimp [retainedPrimeBoundaryMajorant]; ring

private theorem retainedPrimeBoundary_integrable {δ : ℝ} (hδ : 0 ≤ δ) :
    IntegrableOn (fun y : ℝ => criticalContinuousAbel y / y ^ (5 / 2 : ℝ) *
      retainedPrimeBoundaryKernel δ y) (Ioi (1 : ℝ)) := by
  apply retainedPrimeBoundary_integrable_majorant.mono'
    (((measurable_criticalContinuousAbel.div (measurable_id.pow_const (5 / 2 : ℝ))).mul
      (measurable_retainedPrimeBoundaryKernel δ)).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact retainedPrimeBoundary_weighted_bound hy (retainedPrimeBoundaryKernel_bound hδ hy)

/-- Absolute admission of the actual retained source integrand, including the
critical endpoint. This supplies product integrability for the prime sum. -/
theorem integrableOn_criticalRetainedPrimeAbsoluteBoundary {δ : ℝ} (hδ : 0 ≤ δ) :
    IntegrableOn (fun y : ℝ => |criticalContinuousAbel y| / y ^ (5 / 2 : ℝ) *
      retainedPrimeBoundaryKernel δ y) (Ioi (1 : ℝ)) := by
  apply IntegrableOn.congr_fun (retainedPrimeBoundary_integrable hδ).norm _ measurableSet_Ioi
  intro y hy
  have hp : 0 < y ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (lt_trans zero_lt_one hy) _
  have hk : 0 ≤ retainedPrimeBoundaryKernel δ y := Finset.sum_nonneg (fun _ _ => by positivity)
  simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hp, abs_of_nonneg hk]

/-- The literal source integral with the retained prime cutoff has a finite
right boundary slope. No differentiability across the boundary is assumed. -/
theorem criticalRetainedPrimeBoundaryTransform_right_slope :
    Tendsto (fun δ : ℝ =>
      (criticalRetainedPrimeBoundaryTransform δ - criticalRetainedPrimeBoundaryTransform 0) / δ)
      (𝓝[>] 0)
      (𝓝 (-(∫ y in Ioi (1 : ℝ), criticalContinuousAbel y / y ^ (5 / 2 : ℝ) *
        retainedPrimeBoundaryMoment y))) := by
  let F : ℝ → ℝ → ℝ := fun δ y => criticalContinuousAbel y / y ^ (5 / 2 : ℝ) *
    ((retainedPrimeBoundaryKernel δ y - retainedPrimeBoundaryKernel 0 y) / δ)
  have hmeas (δ : ℝ) : Measurable (F δ) :=
    (measurable_criticalContinuousAbel.div (measurable_id.pow_const (5 / 2 : ℝ))).mul
      (((measurable_retainedPrimeBoundaryKernel δ).sub
        (measurable_retainedPrimeBoundaryKernel 0)).div measurable_const)
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ y ∂volume.restrict (Ioi (1 : ℝ)),
      ‖F δ y‖ ≤ retainedPrimeBoundaryMajorant y := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact retainedPrimeBoundary_weighted_bound hy
      (retainedPrimeBoundaryKernel_slope_bound hδ hy)
  have hlim : ∀ᵐ y ∂volume.restrict (Ioi (1 : ℝ)),
      Tendsto (fun δ => F δ y) (𝓝[>] 0)
        (𝓝 (-(criticalContinuousAbel y / y ^ (5 / 2 : ℝ) * retainedPrimeBoundaryMoment y))) := by
    filter_upwards with y
    simpa only [F, mul_neg] using
      (retainedPrimeBoundaryKernel_slope y).const_mul (criticalContinuousAbel y / y ^ (5 / 2 : ℝ))
  have ht := tendsto_integral_filter_of_dominated_convergence retainedPrimeBoundaryMajorant
    (Eventually.of_forall (fun δ => (hmeas δ).aestronglyMeasurable.restrict))
    hbound retainedPrimeBoundary_integrable_majorant hlim
  rw [integral_neg] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  dsimp [F, criticalRetainedPrimeBoundaryTransform]
  rw [← integral_sub (retainedPrimeBoundary_integrable (le_of_lt hδ))
    (retainedPrimeBoundary_integrable le_rfl), ← integral_div]
  apply integral_congr_ae
  filter_upwards with y
  ring

end RHTower

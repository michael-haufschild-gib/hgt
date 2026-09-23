import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The half-plane Poisson kernel and its semigroup

The kernel `P_c (t) = c / (π (c² + t²))` is a probability density for every height `c > 0`, and the
family is a convolution semigroup: `P_c ⋆ P_d = P_{c+d}`.  The semigroup reduces to the shifted
rational integral

`∫ ds / ((c² + (s-t)²) (d² + s²)) = π (c+d) / (c d ((c+d)² + t²))`,

whose partial fraction splits into two even pieces — evaluated by the unshifted Poisson
normalisation — and one odd piece whose antiderivative
`(1/2) log ((c² + (s-t)²) / (d² + s²))` has equal limits at both ends, so the odd piece integrates
to zero.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ### Two elementary decay limits -/

theorem tendsto_lin_div_sq_atTop (c : ℝ) :
    Tendsto (fun u : ℝ => u / (c ^ (2 : ℕ) + u ^ (2 : ℕ))) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hu]
    nlinarith [sq_nonneg c]

theorem tendsto_one_div_sq_atTop (c : ℝ) :
    Tendsto (fun u : ℝ => (1 : ℝ) / (c ^ (2 : ℕ) + u ^ (2 : ℕ))) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hu0]
    nlinarith [sq_nonneg c, hu]

/-! ### The Poisson kernel -/

/-- The half-plane Poisson kernel at height `c`. -/
def halfPlanePoisson (c t : ℝ) : ℝ := c / (Real.pi * (c ^ (2 : ℕ) + t ^ (2 : ℕ)))

theorem halfPlanePoisson_pos {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 < halfPlanePoisson c t := by
  rw [halfPlanePoisson]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

theorem integrable_halfPlanePoisson {c : ℝ} (hc : 0 < c) : Integrable (halfPlanePoisson c) := by
  have hbase := integrable_inv_sq_add_sq hc
  refine (hbase.const_mul (c / Real.pi)).congr (Filter.Eventually.of_forall fun t => ?_)
  rw [halfPlanePoisson]
  field_simp

theorem integral_halfPlanePoisson {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, halfPlanePoisson c t) = 1 := by
  have hcongr : ∀ t : ℝ, halfPlanePoisson c t = (c / Real.pi) * ((c ^ (2 : ℕ) + t ^ (2 : ℕ))⁻¹) := by
    intro t
    rw [halfPlanePoisson]
    field_simp
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_const_mul, integral_inv_sq_add_sq hc]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-! ### The shifted rational Poisson integral -/

theorem integral_inv_shifted_sq_add_sq {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (∫ s : ℝ, ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹)) = Real.pi / c := by
  have hshift : (∫ u : ℝ, ((c ^ (2 : ℕ) + (u + -t) ^ (2 : ℕ))⁻¹)) = ∫ u : ℝ, ((c ^ (2 : ℕ) + u ^ (2 : ℕ))⁻¹) :=
    MeasureTheory.integral_add_right_eq_self (μ := volume) (fun u : ℝ => ((c ^ (2 : ℕ) + u ^ (2 : ℕ))⁻¹)) (-t)
  simp only [sub_eq_add_neg]
  rw [hshift]
  exact integral_inv_sq_add_sq hc

theorem integrable_inv_shifted_sq_add_sq {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Integrable fun s : ℝ => ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹) :=
  (integrable_inv_sq_add_sq hc).comp_sub_right t

theorem integrable_shifted_product {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (t : ℝ) :
    Integrable fun s : ℝ => (((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (d ^ (2 : ℕ) + s ^ (2 : ℕ)))⁻¹) := by
  have hcont : Continuous fun s : ℝ => (((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (d ^ (2 : ℕ) + s ^ (2 : ℕ)))⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun s => ?_
    positivity
  refine ((integrable_inv_sq_add_sq hd).const_mul ((c ^ (2 : ℕ))⁻¹)).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards with s
  have h1 : (0 : ℝ) < c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ) := by positivity
  have h2 : (0 : ℝ) < d ^ (2 : ℕ) + s ^ (2 : ℕ) := by positivity
  have hc2 : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
  have hle : (c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹ ≤ (c ^ (2 : ℕ))⁻¹ := by
    have hstep : c ^ (2 : ℕ) ≤ c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ) := by nlinarith [sq_nonneg (s - t)]
    simpa [one_div] using one_div_le_one_div_of_le hc2 hstep
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_inv]
  exact mul_le_mul_of_nonneg_right hle (le_of_lt (inv_pos.mpr h2))

/-- The odd part of the shifted Poisson partial fraction. -/
def poissonOdd (c d t s : ℝ) : ℝ := (s - t) / (c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) - s / (d ^ (2 : ℕ) + s ^ (2 : ℕ))

/-- Its explicit logarithmic primitive. -/
def poissonOddPrimitive (c d t s : ℝ) : ℝ :=
  (Real.log (c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) - Real.log (d ^ (2 : ℕ) + s ^ (2 : ℕ))) / 2

theorem hasDerivAt_poissonOddPrimitive {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (t s : ℝ) :
    HasDerivAt (poissonOddPrimitive c d t) (poissonOdd c d t s) s := by
  have hQ : (0 : ℝ) < c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ) := by positivity
  have hR : (0 : ℝ) < d ^ (2 : ℕ) + s ^ (2 : ℕ) := by positivity
  have h1 : HasDerivAt (fun u : ℝ => c ^ (2 : ℕ) + (u - t) ^ (2 : ℕ)) (2 * (s - t)) s := by
    have hb : HasDerivAt (fun u : ℝ => (u - t) ^ (2 : ℕ)) (2 * (s - t) ^ (1 : ℕ) * 1) s :=
      ((hasDerivAt_id s).sub_const t).pow 2
    simpa using hb.const_add (c ^ (2 : ℕ))
  have h2 : HasDerivAt (fun u : ℝ => d ^ (2 : ℕ) + u ^ (2 : ℕ)) (2 * s) s := by
    have hb : HasDerivAt (fun u : ℝ => u ^ (2 : ℕ)) (2 * s ^ (1 : ℕ) * 1) s := (hasDerivAt_id s).pow 2
    simpa using hb.const_add (d ^ (2 : ℕ))
  have hl1 : HasDerivAt (fun u : ℝ => Real.log (c ^ (2 : ℕ) + (u - t) ^ (2 : ℕ)))
      (2 * (s - t) / (c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))) s := h1.log (ne_of_gt hQ)
  have hl2 : HasDerivAt (fun u : ℝ => Real.log (d ^ (2 : ℕ) + u ^ (2 : ℕ))) (2 * s / (d ^ (2 : ℕ) + s ^ (2 : ℕ))) s :=
    h2.log (ne_of_gt hR)
  have hsub := (hl1.sub hl2).div_const 2
  refine hsub.congr_deriv ?_
  rw [poissonOdd]
  field_simp

theorem continuous_poissonOdd {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (t : ℝ) :
    Continuous (poissonOdd c d t) := by
  unfold poissonOdd
  refine Continuous.sub (Continuous.div (by fun_prop) (by fun_prop) fun s => ?_)
    (Continuous.div (by fun_prop) (by fun_prop) fun s => ?_)
  · positivity
  · positivity

theorem integral_poissonOdd_interval {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (t M : ℝ) :
    (∫ s in (-M)..M, poissonOdd c d t s)
      = (Real.log (c ^ (2 : ℕ) + (M - t) ^ (2 : ℕ)) - Real.log (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ))) / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_poissonOddPrimitive hc hd t s)
    ((continuous_poissonOdd hc hd t).intervalIntegrable _ _)]
  rw [poissonOddPrimitive, poissonOddPrimitive]
  have hsq : (-M - t) ^ (2 : ℕ) = (M + t) ^ (2 : ℕ) := by ring
  have hsq' : (-M) ^ (2 : ℕ) = M ^ (2 : ℕ) := by ring
  rw [hsq, hsq']
  ring

theorem tendsto_poissonOdd_boundary {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Tendsto (fun M : ℝ => (Real.log (c ^ (2 : ℕ) + (M - t) ^ (2 : ℕ))
      - Real.log (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ))) / 2) atTop (𝓝 0) := by
  have hne : ∀ M : ℝ, c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ) ≠ 0 := fun M => by positivity
  have hne' : ∀ M : ℝ, c ^ (2 : ℕ) + (M - t) ^ (2 : ℕ) ≠ 0 := fun M => by positivity
  have hshift : Tendsto (fun M : ℝ => M + t) atTop atTop :=
    tendsto_atTop_add_const_right _ t tendsto_id
  have h1 : Tendsto (fun M : ℝ => (M + t) / (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ))) atTop (𝓝 0) :=
    (tendsto_lin_div_sq_atTop c).comp hshift
  have h2 : Tendsto (fun M : ℝ => (1 : ℝ) / (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ))) atTop (𝓝 0) :=
    (tendsto_one_div_sq_atTop c).comp hshift
  have hkey : Tendsto (fun M : ℝ => (-4 * t) * ((M + t) / (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ)))
      + (4 * t ^ (2 : ℕ)) * ((1 : ℝ) / (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ)))) atTop (𝓝 0) := by
    simpa using (h1.const_mul (-4 * t)).add (h2.const_mul (4 * t ^ (2 : ℕ)))
  have hratio : Tendsto (fun M : ℝ => (c ^ (2 : ℕ) + (M - t) ^ (2 : ℕ)) / (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ)))
      atTop (𝓝 1) := by
    have hcongr : ∀ M : ℝ, (c ^ (2 : ℕ) + (M - t) ^ (2 : ℕ)) / (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ))
        = 1 + ((-4 * t) * ((M + t) / (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ)))
          + (4 * t ^ (2 : ℕ)) * ((1 : ℝ) / (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ)))) := by
      intro M
      field_simp
      ring
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hsum := hone.add hkey
    rw [add_zero] at hsum
    exact hsum.congr fun M => (hcongr M).symm
  have hlog : Tendsto (fun M : ℝ =>
      Real.log ((c ^ (2 : ℕ) + (M - t) ^ (2 : ℕ)) / (c ^ (2 : ℕ) + (M + t) ^ (2 : ℕ)))) atTop (𝓝 0) := by
    have hc1 := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    simpa [Function.comp_def] using hc1
  have hdiv := hlog.div_const 2
  rw [zero_div] at hdiv
  exact hdiv.congr fun M => by rw [Real.log_div (hne' M) (hne M)]

theorem integral_poissonOdd {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (t : ℝ)
    (hint : Integrable (poissonOdd c d t)) :
    (∫ s : ℝ, poissonOdd c d t s) = 0 := by
  have hidt : Tendsto (fun M : ℝ => M) atTop atTop := tendsto_id
  have hneg : Tendsto (fun M : ℝ => -M) atTop atBot := tendsto_neg_atTop_atBot
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral hint hneg hidt
  have hval : Tendsto (fun M : ℝ => ∫ s in (-M)..M, poissonOdd c d t s) atTop (𝓝 0) := by
    refine (tendsto_poissonOdd_boundary hc t).congr fun M => ?_
    exact (integral_poissonOdd_interval hc hd t M).symm
  exact tendsto_nhds_unique hlim hval

theorem continuous_halfPlanePoisson {c : ℝ} (hc : 0 < c) : Continuous (halfPlanePoisson c) := by
  unfold halfPlanePoisson
  refine Continuous.div continuous_const (by fun_prop) fun u => ?_
  have hpi := Real.pi_pos
  positivity

theorem halfPlanePoisson_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    halfPlanePoisson c u ≤ 1 / (Real.pi * c) := by
  have hpi := Real.pi_pos
  rw [halfPlanePoisson, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg u, hpi, hc]

/-! ### The shifted product integral and the semigroup -/

/-- The partial-fraction denominator of the shifted Poisson product. -/
def poissonPartialDen (c d t : ℝ) : ℝ := ((c + d) ^ (2 : ℕ) + t ^ (2 : ℕ)) * ((c - d) ^ (2 : ℕ) + t ^ (2 : ℕ))

theorem poissonPartialDen_pos {c d t : ℝ} (ht : t ≠ 0) :
    0 < poissonPartialDen c d t := by
  have ht2 : (0 : ℝ) < t ^ (2 : ℕ) := by positivity
  have h1 : (0 : ℝ) < (c + d) ^ (2 : ℕ) + t ^ (2 : ℕ) := by nlinarith [sq_nonneg (c + d)]
  have h2 : (0 : ℝ) < (c - d) ^ (2 : ℕ) + t ^ (2 : ℕ) := by nlinarith [sq_nonneg (c - d)]
  exact mul_pos h1 h2

theorem poisson_partial_fraction {c d t : ℝ} (hc : 0 < c) (hd : 0 < d) (ht : t ≠ 0) (s : ℝ) :
    (((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (d ^ (2 : ℕ) + s ^ (2 : ℕ)))⁻¹)
      = (-2 * t / poissonPartialDen c d t) * poissonOdd c d t s
        + ((t ^ (2 : ℕ) - c ^ (2 : ℕ) + d ^ (2 : ℕ)) / poissonPartialDen c d t) * ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹)
        + ((c ^ (2 : ℕ) + t ^ (2 : ℕ) - d ^ (2 : ℕ)) / poissonPartialDen c d t) * ((d ^ (2 : ℕ) + s ^ (2 : ℕ))⁻¹) := by
  have hQ : (0 : ℝ) < c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ) := by positivity
  have hR : (0 : ℝ) < d ^ (2 : ℕ) + s ^ (2 : ℕ) := by positivity
  have hG : poissonPartialDen c d t ≠ 0 := ne_of_gt (poissonPartialDen_pos ht)
  rw [poissonOdd, poissonPartialDen] at *
  field_simp
  ring

theorem integrable_poissonOdd {c d t : ℝ} (hc : 0 < c) (hd : 0 < d) (ht : t ≠ 0) :
    Integrable (poissonOdd c d t) := by
  have hG : poissonPartialDen c d t ≠ 0 := ne_of_gt (poissonPartialDen_pos ht)
  have hA : (-2 * t / poissonPartialDen c d t) ≠ 0 := by
    refine div_ne_zero ?_ hG
    simpa using ht
  have hcomb : Integrable fun s : ℝ =>
      (((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (d ^ (2 : ℕ) + s ^ (2 : ℕ)))⁻¹)
        - ((t ^ (2 : ℕ) - c ^ (2 : ℕ) + d ^ (2 : ℕ)) / poissonPartialDen c d t) * ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹)
        - ((c ^ (2 : ℕ) + t ^ (2 : ℕ) - d ^ (2 : ℕ)) / poissonPartialDen c d t) * ((d ^ (2 : ℕ) + s ^ (2 : ℕ))⁻¹) :=
    ((integrable_shifted_product hc hd t).sub
      ((integrable_inv_shifted_sq_add_sq hc t).const_mul _)).sub
      ((integrable_inv_sq_add_sq hd).const_mul _)
  refine (hcomb.const_mul ((-2 * t / poissonPartialDen c d t)⁻¹)).congr
    (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  rw [poisson_partial_fraction hc hd ht s]
  field_simp
  ring

theorem integral_shifted_poisson_product {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (t : ℝ) :
    (∫ s : ℝ, (((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (d ^ (2 : ℕ) + s ^ (2 : ℕ)))⁻¹))
      = Real.pi * (c + d) / (c * d * ((c + d) ^ (2 : ℕ) + t ^ (2 : ℕ))) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hdne : d ≠ 0 := ne_of_gt hd
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [sub_zero]
    rw [integral_inv_sq_add_sq_mul' hc hd]
    have hsum : c + d ≠ 0 := by positivity
    field_simp
    ring
  · have hG : poissonPartialDen c d t ≠ 0 := ne_of_gt (poissonPartialDen_pos ht)
    have hint1 : Integrable fun s : ℝ =>
        (-2 * t / poissonPartialDen c d t) * poissonOdd c d t s :=
      (integrable_poissonOdd hc hd ht).const_mul _
    have hint2 : Integrable fun s : ℝ =>
        ((t ^ (2 : ℕ) - c ^ (2 : ℕ) + d ^ (2 : ℕ)) / poissonPartialDen c d t) * ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹) :=
      (integrable_inv_shifted_sq_add_sq hc t).const_mul _
    have hint3 : Integrable fun s : ℝ =>
        ((c ^ (2 : ℕ) + t ^ (2 : ℕ) - d ^ (2 : ℕ)) / poissonPartialDen c d t) * ((d ^ (2 : ℕ) + s ^ (2 : ℕ))⁻¹) :=
      (integrable_inv_sq_add_sq hd).const_mul _
    have hint12 : Integrable fun s : ℝ =>
        (-2 * t / poissonPartialDen c d t) * poissonOdd c d t s
          + ((t ^ (2 : ℕ) - c ^ (2 : ℕ) + d ^ (2 : ℕ)) / poissonPartialDen c d t) * ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹) :=
      hint1.add hint2
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (poisson_partial_fraction hc hd ht)),
      MeasureTheory.integral_add hint12 hint3,
      MeasureTheory.integral_add hint1 hint2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul,
      integral_poissonOdd hc hd t (integrable_poissonOdd hc hd ht),
      integral_inv_shifted_sq_add_sq hc t, integral_inv_sq_add_sq hd, poissonPartialDen]
    have hs1 : ((c + d) ^ (2 : ℕ) + t ^ (2 : ℕ)) ≠ 0 := by positivity
    have ht2 : (0 : ℝ) < t ^ (2 : ℕ) := by positivity
    have hs2 : ((c - d) ^ (2 : ℕ) + t ^ (2 : ℕ)) ≠ 0 := by nlinarith [sq_nonneg (c - d)]
    field_simp
    ring

/-- **The Poisson semigroup.**  Convolution adds the heights. -/
theorem halfPlanePoisson_convolution {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (t : ℝ) :
    (∫ s : ℝ, halfPlanePoisson c (t - s) * halfPlanePoisson d s)
      = halfPlanePoisson (c + d) t := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hcne : c ≠ 0 := ne_of_gt hc
  have hdne : d ≠ 0 := ne_of_gt hd
  have hcongr : ∀ s : ℝ, halfPlanePoisson c (t - s) * halfPlanePoisson d s
      = (c * d / Real.pi ^ (2 : ℕ)) * (((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (d ^ (2 : ℕ) + s ^ (2 : ℕ)))⁻¹) := by
    intro s
    have hsq : (t - s) ^ (2 : ℕ) = (s - t) ^ (2 : ℕ) := by ring
    rw [halfPlanePoisson, halfPlanePoisson, hsq]
    have hQ : (0 : ℝ) < c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ) := by positivity
    have hR : (0 : ℝ) < d ^ (2 : ℕ) + s ^ (2 : ℕ) := by positivity
    field_simp
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_const_mul, integral_shifted_poisson_product hc hd t,
    halfPlanePoisson]
  have hs1 : ((c + d) ^ (2 : ℕ) + t ^ (2 : ℕ)) ≠ 0 := by positivity
  field_simp

theorem integrable_poisson_shift_product {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (t r : ℝ) :
    Integrable fun s : ℝ => halfPlanePoisson c (t - s) * halfPlanePoisson d (s - r) := by
  have hbase : Integrable fun s : ℝ => halfPlanePoisson d (s - r) :=
    (integrable_halfPlanePoisson hd).comp_sub_right r
  have hcont : Continuous fun s : ℝ => halfPlanePoisson c (t - s) * halfPlanePoisson d (s - r) :=
    ((continuous_halfPlanePoisson hc).comp (by fun_prop)).mul
      ((continuous_halfPlanePoisson hd).comp (by fun_prop))
  refine (hbase.const_mul (1 / (Real.pi * c))).mono' hcont.aestronglyMeasurable ?_
  filter_upwards with s
  have h1 := halfPlanePoisson_pos hc (t - s)
  have h2 := halfPlanePoisson_pos hd (s - r)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (halfPlanePoisson_le hc _) (le_of_lt h2)

/-- **The shifted Poisson semigroup.** -/
theorem integral_poisson_shift_product {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (t r : ℝ) :
    (∫ s : ℝ, halfPlanePoisson c (t - s) * halfPlanePoisson d (s - r))
      = halfPlanePoisson (c + d) (t - r) := by
  have hshift : (∫ s : ℝ, halfPlanePoisson c ((t - r) - (s + -r)) * halfPlanePoisson d (s + -r))
      = ∫ s : ℝ, halfPlanePoisson c ((t - r) - s) * halfPlanePoisson d s :=
    MeasureTheory.integral_add_right_eq_self
      (fun s : ℝ => halfPlanePoisson c ((t - r) - s) * halfPlanePoisson d s) (-r)
  have hcongr : ∀ s : ℝ, halfPlanePoisson c (t - s) * halfPlanePoisson d (s - r)
      = halfPlanePoisson c ((t - r) - (s + -r)) * halfPlanePoisson d (s + -r) := by
    intro s
    congr 2
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr), hshift,
    halfPlanePoisson_convolution hc hd]

/-! ### The conjugate Poisson kernel -/

/-- The conjugate half-plane Poisson kernel at height `p`. -/
def conjugatePoisson (p x : ℝ) : ℝ := x / (Real.pi * (p ^ (2 : ℕ) + x ^ (2 : ℕ)))

theorem conjugatePoisson_neg (p x : ℝ) : conjugatePoisson p (-x) = -conjugatePoisson p x := by
  rw [conjugatePoisson, conjugatePoisson]
  have hsq : (-x) ^ (2 : ℕ) = x ^ (2 : ℕ) := by ring
  rw [hsq, neg_div]

theorem integrable_conjugate_product {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (t : ℝ) :
    Integrable fun s : ℝ => (s / ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + s ^ (2 : ℕ)))) := by
  have hcont : Continuous fun s : ℝ => (s / ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + s ^ (2 : ℕ)))) := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun s => ?_
    positivity
  refine ((integrable_inv_shifted_sq_add_sq hc t).const_mul (1 / (2 * p))).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards with s
  have h1 : (0 : ℝ) < c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ) := by positivity
  have h2 : (0 : ℝ) < p ^ (2 : ℕ) + s ^ (2 : ℕ) := by positivity
  have h2p : (0 : ℝ) < 2 * p := by linarith
  have hbound : |s| / (p ^ (2 : ℕ) + s ^ (2 : ℕ)) ≤ 1 / (2 * p) := by
    rw [div_le_div_iff₀ h2 h2p]
    nlinarith [sq_nonneg (|s| - p), abs_nonneg s, sq_abs s]
  have hval : ‖s / ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + s ^ (2 : ℕ)))‖
      = (|s| / (p ^ (2 : ℕ) + s ^ (2 : ℕ))) * (c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹ := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos h1 h2)]
    field_simp
  rw [hval]
  exact mul_le_mul_of_nonneg_right hbound (le_of_lt (inv_pos.mpr h1))

/-- **The conjugate Poisson product integral.** -/
theorem integral_conjugate_product {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (t : ℝ) :
    (∫ s : ℝ, (s / ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + s ^ (2 : ℕ)))))
      = Real.pi * t / (c * ((c + p) ^ (2 : ℕ) + t ^ (2 : ℕ))) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hpne : p ≠ 0 := ne_of_gt hp
  rcases eq_or_ne t 0 with rfl | ht
  · have hodd : ∀ s : ℝ, ((-s) / ((c ^ (2 : ℕ) + ((-s) - 0) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + (-s) ^ (2 : ℕ))))
        = -(s / ((c ^ (2 : ℕ) + (s - 0) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + s ^ (2 : ℕ)))) := by
      intro s
      have h1 : ((-s) - 0) ^ (2 : ℕ) = (s - 0) ^ (2 : ℕ) := by ring
      have h2 : (-s) ^ (2 : ℕ) = s ^ (2 : ℕ) := by ring
      rw [h1, h2, neg_div]
    have hself := MeasureTheory.integral_neg_eq_self
      (fun s : ℝ => (s / ((c ^ (2 : ℕ) + (s - 0) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + s ^ (2 : ℕ))))) (μ := volume)
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hodd),
      MeasureTheory.integral_neg] at hself
    have : (∫ s : ℝ, (s / ((c ^ (2 : ℕ) + (s - 0) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + s ^ (2 : ℕ))))) = 0 := by linarith
    rw [this]
    simp
  · have hG : poissonPartialDen c p t ≠ 0 := ne_of_gt (poissonPartialDen_pos ht)
    have hpf : ∀ s : ℝ, (s / ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + s ^ (2 : ℕ))))
        = (-(c ^ (2 : ℕ) + t ^ (2 : ℕ) - p ^ (2 : ℕ)) / poissonPartialDen c p t) * poissonOdd c p t s
          + (t * (c ^ (2 : ℕ) + t ^ (2 : ℕ) + p ^ (2 : ℕ)) / poissonPartialDen c p t) * ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹)
          + (-2 * t * p ^ (2 : ℕ) / poissonPartialDen c p t) * ((p ^ (2 : ℕ) + s ^ (2 : ℕ))⁻¹) := by
      intro s
      have hQ : (0 : ℝ) < c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ) := by positivity
      have hR : (0 : ℝ) < p ^ (2 : ℕ) + s ^ (2 : ℕ) := by positivity
      rw [poissonOdd, poissonPartialDen] at *
      field_simp
      ring
    have hint1 : Integrable fun s : ℝ =>
        (-(c ^ (2 : ℕ) + t ^ (2 : ℕ) - p ^ (2 : ℕ)) / poissonPartialDen c p t) * poissonOdd c p t s :=
      (integrable_poissonOdd hc hp ht).const_mul _
    have hint2 : Integrable fun s : ℝ =>
        (t * (c ^ (2 : ℕ) + t ^ (2 : ℕ) + p ^ (2 : ℕ)) / poissonPartialDen c p t) * ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹) :=
      (integrable_inv_shifted_sq_add_sq hc t).const_mul _
    have hint3 : Integrable fun s : ℝ =>
        (-2 * t * p ^ (2 : ℕ) / poissonPartialDen c p t) * ((p ^ (2 : ℕ) + s ^ (2 : ℕ))⁻¹) :=
      (integrable_inv_sq_add_sq hp).const_mul _
    have hint12 : Integrable fun s : ℝ =>
        (-(c ^ (2 : ℕ) + t ^ (2 : ℕ) - p ^ (2 : ℕ)) / poissonPartialDen c p t) * poissonOdd c p t s
          + (t * (c ^ (2 : ℕ) + t ^ (2 : ℕ) + p ^ (2 : ℕ)) / poissonPartialDen c p t)
            * ((c ^ (2 : ℕ) + (s - t) ^ (2 : ℕ))⁻¹) := hint1.add hint2
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpf),
      MeasureTheory.integral_add hint12 hint3, MeasureTheory.integral_add hint1 hint2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul,
      integral_poissonOdd hc hp t (integrable_poissonOdd hc hp ht),
      integral_inv_shifted_sq_add_sq hc t, integral_inv_sq_add_sq hp, poissonPartialDen]
    have hs1 : ((c + p) ^ (2 : ℕ) + t ^ (2 : ℕ)) ≠ 0 := by positivity
    have ht2 : (0 : ℝ) < t ^ (2 : ℕ) := by positivity
    have hs2 : ((c - p) ^ (2 : ℕ) + t ^ (2 : ℕ)) ≠ 0 := by nlinarith [sq_nonneg (c - p)]
    field_simp
    ring

/-- **The conjugate Poisson semigroup.** -/
theorem conjugatePoisson_convolution {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (t r : ℝ) :
    (∫ s : ℝ, halfPlanePoisson c (t - s) * conjugatePoisson p (s - r))
      = conjugatePoisson (c + p) (t - r) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hcne : c ≠ 0 := ne_of_gt hc
  have hshift : (∫ s : ℝ, ((s + -r) / ((c ^ (2 : ℕ) + ((s + -r) - (t - r)) ^ (2 : ℕ))
        * (p ^ (2 : ℕ) + (s + -r) ^ (2 : ℕ)))))
      = ∫ s : ℝ, (s / ((c ^ (2 : ℕ) + (s - (t - r)) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + s ^ (2 : ℕ)))) :=
    MeasureTheory.integral_add_right_eq_self
      (fun s : ℝ => (s / ((c ^ (2 : ℕ) + (s - (t - r)) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + s ^ (2 : ℕ))))) (-r)
  have hcongr : ∀ s : ℝ, halfPlanePoisson c (t - s) * conjugatePoisson p (s - r)
      = (c / Real.pi ^ (2 : ℕ))
        * ((s + -r) / ((c ^ (2 : ℕ) + ((s + -r) - (t - r)) ^ (2 : ℕ)) * (p ^ (2 : ℕ) + (s + -r) ^ (2 : ℕ)))) := by
    intro s
    have h1 : ((s + -r) - (t - r)) ^ (2 : ℕ) = (t - s) ^ (2 : ℕ) := by ring
    have h2 : (s + -r) ^ (2 : ℕ) = (s - r) ^ (2 : ℕ) := by ring
    have h3 : s + -r = s - r := by ring
    rw [halfPlanePoisson, conjugatePoisson, h1, h2, h3]
    have hQ : (0 : ℝ) < c ^ (2 : ℕ) + (t - s) ^ (2 : ℕ) := by positivity
    have hR : (0 : ℝ) < p ^ (2 : ℕ) + (s - r) ^ (2 : ℕ) := by positivity
    field_simp
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_const_mul, hshift, integral_conjugate_product hc hp (t - r),
    conjugatePoisson]
  have hs1 : ((c + p) ^ (2 : ℕ) + (t - r) ^ (2 : ℕ)) ≠ 0 := by positivity
  field_simp

end GaloisForLFunctions.HTGeometry

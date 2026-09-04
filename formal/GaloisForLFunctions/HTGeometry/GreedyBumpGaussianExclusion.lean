import Mathlib

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unit-width Gaussian-template overlap from the paper's worked model. -/
def greedyBumpGaussianOverlap (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / 4)

/-- Symmetric conditional derivative variance in principal coordinates. -/
def greedyBumpGaussianDPlus (x : ℝ) : ℝ :=
  1 / 2 + (1 / 2 - x ^ 2 / 4) * greedyBumpGaussianOverlap x

/-- Antisymmetric conditional derivative variance after value conditioning. -/
def greedyBumpGaussianLambdaMinus (x : ℝ) : ℝ :=
  1 - greedyBumpGaussianOverlap x -
    x ^ 2 * greedyBumpGaussianOverlap x ^ 2 /
      (4 * greedyBumpGaussianDPlus x)

/-- Polynomially simplified numerator of the conditioned variance. -/
def greedyBumpGaussianNumerator (t : ℝ) : ℝ :=
  2 - t * Real.exp (-t / 4) - 2 * Real.exp (-t / 2)

/-- Principal conditional variance as a function of squared separation. -/
def greedyBumpGaussianDPlusSq (t : ℝ) : ℝ :=
  1 / 2 + (1 / 2 - t / 4) * Real.exp (-t / 4)

/-- Conditioned antisymmetric variance as a function of squared separation. -/
def greedyBumpGaussianLambdaMinusSq (t : ℝ) : ℝ :=
  1 - Real.exp (-t / 4) -
    t * Real.exp (-t / 2) / (4 * greedyBumpGaussianDPlusSq t)

/-- Admissible squared separation; denominator nondegeneracy is data. -/
abbrev GaussianAdmissibleSquaredSeparation :=
  {t : ℝ // greedyBumpGaussianDPlusSq t ≠ 0}

/-- Exact rational reduction exposing the sixth-order numerator. -/
theorem greedyBumpGaussianLambdaMinusSq_eq_numerator
    (t : GaussianAdmissibleSquaredSeparation) :
    greedyBumpGaussianLambdaMinusSq t =
      greedyBumpGaussianNumerator t /
        (4 * greedyBumpGaussianDPlusSq t) := by
  have hd : 4 * greedyBumpGaussianDPlusSq (t : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) t.property
  have hexp : Real.exp (-((t : ℝ) / 2)) =
      Real.exp (-((t : ℝ) / 4)) * Real.exp (-((t : ℝ) / 4)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [eq_div_iff hd]
  unfold greedyBumpGaussianLambdaMinusSq greedyBumpGaussianNumerator
  field_simp [hd, t.property]
  rw [hexp]
  unfold greedyBumpGaussianDPlusSq
  ring_nf

/-- Exact coincidence values of overlap and conditional variances. -/
theorem greedyBumpGaussian_coincidence :
    greedyBumpGaussianOverlap 0 = 1 ∧
    greedyBumpGaussianDPlus 0 = 1 ∧
    greedyBumpGaussianLambdaMinus 0 = 0 := by
  norm_num [greedyBumpGaussianOverlap, greedyBumpGaussianDPlus,
    greedyBumpGaussianLambdaMinus]

/-- Cubic numerator cancellation in squared separation. -/
theorem greedyBumpGaussianNumerator_ratio_tendsto :
    Tendsto (fun t : ℝ => greedyBumpGaussianNumerator t / t ^ 3)
      (𝓝[≠] 0) (𝓝 (1 / 96 : ℝ)) := by
  have htend : Tendsto (fun t : ℝ => -t / 4) (𝓝 0) (𝓝 0) := by
    simpa using (by fun_prop : ContinuousAt (fun t : ℝ => -t / 4) 0).tendsto
  have h4raw := (Real.exp_sub_sum_range_succ_isLittleO_pow 2).comp_tendsto htend
  have h4 :
      (fun t : ℝ => Real.exp (-t / 4) - (1 - t / 4 + t ^ 2 / 32)) =o[𝓝 0]
        (fun t => t ^ 2) := by
    have hrhs : (fun t : ℝ => (-t / 4) ^ 2) =O[𝓝 0] (fun t => t ^ 2) := by
      apply (isBigO_const_mul_self (1 / 16 : ℝ) (fun t : ℝ => t ^ 2) (𝓝 0)).congr'
      · filter_upwards with t
        ring
      · rfl
    apply (h4raw.trans_isBigO hrhs).congr'
    · filter_upwards with t
      norm_num [Finset.sum_range_succ]
      ring
    · rfl
  have htend2 : Tendsto (fun t : ℝ => -t / 2) (𝓝 0) (𝓝 0) := by
    simpa using (by fun_prop : ContinuousAt (fun t : ℝ => -t / 2) 0).tendsto
  have h2raw := (Real.exp_sub_sum_range_succ_isLittleO_pow 3).comp_tendsto htend2
  have h2 :
      (fun t : ℝ => Real.exp (-t / 2) -
        (1 - t / 2 + t ^ 2 / 8 - t ^ 3 / 48)) =o[𝓝 0]
          (fun t => t ^ 3) := by
    have hrhs : (fun t : ℝ => (-t / 2) ^ 3) =O[𝓝 0] (fun t => t ^ 3) := by
      apply (isBigO_const_mul_self (-1 / 8 : ℝ) (fun t : ℝ => t ^ 3) (𝓝 0)).congr'
      · filter_upwards with t
        ring
      · rfl
    apply (h2raw.trans_isBigO hrhs).congr'
    · filter_upwards with t
      norm_num [Finset.sum_range_succ]
      ring
    · rfl
  have ht : (fun t : ℝ => t) =O[𝓝 0] (fun t => t) := isBigO_refl _ _
  have h4mul :
      (fun t : ℝ => -t *
        (Real.exp (-t / 4) - (1 - t / 4 + t ^ 2 / 32))) =o[𝓝 0]
          (fun t => t ^ 3) := by
    apply (ht.neg_left.mul_isLittleO h4).congr'
    · filter_upwards with t
      rfl
    · filter_upwards with t
      ring
  have h2mul :
      (fun t : ℝ => -2 * (Real.exp (-t / 2) -
        (1 - t / 2 + t ^ 2 / 8 - t ^ 3 / 48))) =o[𝓝 0]
          (fun t => t ^ 3) := h2.const_mul_left (-2)
  have hnum :
      (fun t : ℝ => greedyBumpGaussianNumerator t - t ^ 3 / 96) =o[𝓝 0]
        (fun t => t ^ 3) := by
    apply (h4mul.add h2mul).congr'
    · filter_upwards with t
      simp only [greedyBumpGaussianNumerator]
      ring
    · rfl
  have hzero := hnum.tendsto_div_nhds_zero
  have hsum0 := hzero.add (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (1 / 96 : ℝ)) (𝓝 0) (𝓝 (1 / 96 : ℝ)))
  have hsum0' : Tendsto
      (fun x => (greedyBumpGaussianNumerator x - x ^ 3 / 96) / x ^ 3 + 1 / 96)
      (𝓝 0) (𝓝 (1 / 96 : ℝ)) := by simpa using hsum0
  have hsum : Tendsto
      (fun x => (greedyBumpGaussianNumerator x - x ^ 3 / 96) / x ^ 3 + 1 / 96)
      (𝓝[≠] 0) (𝓝 (1 / 96 : ℝ)) := tendsto_nhdsWithin_of_tendsto_nhds hsum0'
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htz : t ≠ 0 := by simpa using ht
  field_simp [htz]
  ring

/-- Sixth-order conditioned-variance cancellation in squared separation. -/
theorem greedyBumpGaussianLambdaMinusSq_ratio_tendsto :
    Tendsto (fun t : ℝ => greedyBumpGaussianLambdaMinusSq t / t ^ 3)
      (𝓝[≠] 0) (𝓝 (1 / 384 : ℝ)) := by
  have hden : Tendsto (fun t : ℝ => 4 * greedyBumpGaussianDPlusSq t)
      (𝓝[≠] 0) (𝓝 4) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun t : ℝ => 4 * greedyBumpGaussianDPlusSq t) 0 := by
      unfold greedyBumpGaussianDPlusSq
      fun_prop
    have hzero : greedyBumpGaussianDPlusSq 0 = 1 := by
      norm_num [greedyBumpGaussianDPlusSq]
    simpa only [hzero, mul_one] using hc.tendsto
  have hquot := greedyBumpGaussianNumerator_ratio_tendsto.div hden (by norm_num)
  have hquot' : Tendsto
      (fun t : ℝ => (greedyBumpGaussianNumerator t / t ^ 3) /
        (4 * greedyBumpGaussianDPlusSq t))
      (𝓝[≠] 0) (𝓝 (1 / 384 : ℝ)) := by
    norm_num at hquot ⊢
    exact hquot
  have hden0 : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      4 * greedyBumpGaussianDPlusSq t ≠ 0 :=
    hden.eventually_ne (by norm_num)
  refine hquot'.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hden0] with t ht hdt
  have ht0 : t ≠ 0 := by simpa using ht
  have hd0 : greedyBumpGaussianDPlusSq t ≠ 0 := by
    intro h
    apply hdt
    simp [h]
  rw [greedyBumpGaussianLambdaMinusSq_eq_numerator
    (t := ⟨t, hd0⟩)]
  field_simp [ht0, hd0]

end

end GaloisForLFunctions.HTGeometry

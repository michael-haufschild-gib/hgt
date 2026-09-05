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

/-- Squared-separation and physical-separation conditional variances agree exactly. -/
theorem greedyBumpGaussianLambdaMinus_eq_sq (x : ℝ) :
    greedyBumpGaussianLambdaMinus x =
      greedyBumpGaussianLambdaMinusSq (x ^ 2) := by
  have hexp : greedyBumpGaussianOverlap x ^ 2 = Real.exp (-(x ^ 2) / 2) := by
    unfold greedyBumpGaussianOverlap
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  unfold greedyBumpGaussianLambdaMinus greedyBumpGaussianLambdaMinusSq
  unfold greedyBumpGaussianDPlusSq greedyBumpGaussianDPlus
  rw [hexp]
  rfl

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

/-- Paper's physical sixth-order exclusion law: `λ₋(x) / x⁶ → 1/384`. -/
theorem greedyBumpGaussianLambdaMinus_ratio_six_tendsto :
    Tendsto (fun x : ℝ => greedyBumpGaussianLambdaMinus x / x ^ 6)
      (𝓝[≠] 0) (𝓝 (1 / 384 : ℝ)) := by
  have hmap : Tendsto (fun x : ℝ => x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hsq : Tendsto (fun x : ℝ => x ^ 2)
          (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using (by fun_prop : ContinuousAt (fun x : ℝ => x ^ 2) 0).tendsto
      exact hsq.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact pow_ne_zero 2 hx
  have hcomp := greedyBumpGaussianLambdaMinusSq_ratio_tendsto.comp hmap
  change Tendsto
    (fun x : ℝ => greedyBumpGaussianLambdaMinusSq (x ^ 2) / (x ^ 2) ^ 3)
      (𝓝[≠] 0) (𝓝 (1 / 384 : ℝ)) at hcomp
  refine hcomp.congr' ?_
  filter_upwards with x
  rw [greedyBumpGaussianLambdaMinus_eq_sq]
  congr 1
  ring

/-! ## Symmetric height mode and derivative exclusion -/

/-- Antisymmetric derivative-covariance eigenvalue at unit template width. -/
def greedyBumpGaussianDMinus (x : ℝ) : ℝ :=
  1 / 2 - (1 / 2 - x ^ 2 / 4) * greedyBumpGaussianOverlap x

/-- Symmetric height variance after conditioning both slopes to vanish. -/
def greedyBumpGaussianLambdaPlus (x : ℝ) : ℝ :=
  1 + greedyBumpGaussianOverlap x -
    x ^ 2 * greedyBumpGaussianOverlap x ^ 2 /
      (4 * greedyBumpGaussianDMinus x)

/-- Antisymmetric derivative variance as a function of squared separation. -/
def greedyBumpGaussianDMinusSq (t : ℝ) : ℝ :=
  1 / 2 - (1 / 2 - t / 4) * Real.exp (-t / 4)

/-- Symmetric conditional height variance as a function of squared separation. -/
def greedyBumpGaussianLambdaPlusSq (t : ℝ) : ℝ :=
  1 + Real.exp (-t / 4) -
    t * Real.exp (-t / 2) / (4 * greedyBumpGaussianDMinusSq t)

/-- Simplified numerator for the symmetric conditional height variance. -/
def greedyBumpGaussianSymmetricNumerator (t : ℝ) : ℝ :=
  2 + t * Real.exp (-t / 4) - 2 * Real.exp (-t / 2)

/-- Squared separation where the antisymmetric derivative mode is nondegenerate. -/
abbrev GaussianSymmetricAdmissibleSquaredSeparation :=
  {t : ℝ // greedyBumpGaussianDMinusSq t ≠ 0}

/-- Physical and squared-separation derivative eigenvalues agree. -/
theorem greedyBumpGaussianDMinus_eq_sq (x : ℝ) :
    greedyBumpGaussianDMinus x = greedyBumpGaussianDMinusSq (x ^ 2) := by
  rfl

/-- Physical and squared-separation symmetric height variances agree. -/
theorem greedyBumpGaussianLambdaPlus_eq_sq (x : ℝ) :
    greedyBumpGaussianLambdaPlus x = greedyBumpGaussianLambdaPlusSq (x ^ 2) := by
  have hexp : greedyBumpGaussianOverlap x ^ 2 = Real.exp (-(x ^ 2) / 2) := by
    unfold greedyBumpGaussianOverlap
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  unfold greedyBumpGaussianLambdaPlus greedyBumpGaussianLambdaPlusSq
  unfold greedyBumpGaussianDMinusSq greedyBumpGaussianDMinus
  rw [hexp]
  rfl

/-- Exact rational reduction for the symmetric conditional height mode. -/
theorem greedyBumpGaussianLambdaPlusSq_eq_numerator
    (t : GaussianSymmetricAdmissibleSquaredSeparation) :
    greedyBumpGaussianLambdaPlusSq t =
      greedyBumpGaussianSymmetricNumerator t /
        (4 * greedyBumpGaussianDMinusSq t) := by
  have hd : 4 * greedyBumpGaussianDMinusSq (t : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) t.property
  have hexp : Real.exp (-((t : ℝ) / 2)) =
      Real.exp (-((t : ℝ) / 4)) * Real.exp (-((t : ℝ) / 4)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [eq_div_iff hd]
  unfold greedyBumpGaussianLambdaPlusSq greedyBumpGaussianSymmetricNumerator
  field_simp [hd, t.property]
  rw [hexp]
  unfold greedyBumpGaussianDMinusSq
  ring_nf

/-- First-order symmetric numerator after coincidence cancellation. -/
theorem greedyBumpGaussianSymmetricNumerator_hasDerivAt :
    HasDerivAt greedyBumpGaussianSymmetricNumerator 2 0 := by
  unfold greedyBumpGaussianSymmetricNumerator
  have he4 : HasDerivAt (fun t : ℝ => Real.exp (-t / 4)) (-1 / 4) 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).neg.div_const 4).exp
  have he2 : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (-1 / 2) 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).neg.div_const 2).exp
  have h := ((hasDerivAt_const (x := 0) (c := (2 : ℝ))).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).mul he4)).sub (he2.const_mul 2)
  change HasDerivAt
    (fun t : ℝ => 2 + t * Real.exp (-t / 4) - 2 * Real.exp (-t / 2))
    (0 + (1 * Real.exp (-0 / 4) + 0 * (-1 / 4)) - 2 * (-1 / 2)) 0 at h
  norm_num at h ⊢
  exact h

/-- The antisymmetric derivative variance opens with slope `3/8`. -/
theorem greedyBumpGaussianDMinusSq_hasDerivAt :
    HasDerivAt greedyBumpGaussianDMinusSq (3 / 8) 0 := by
  unfold greedyBumpGaussianDMinusSq
  have he4 : HasDerivAt (fun t : ℝ => Real.exp (-t / 4)) (-1 / 4) 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).neg.div_const 4).exp
  have ha : HasDerivAt (fun t : ℝ => 1 / 2 - t / 4) (-1 / 4) 0 := by
    have h := (hasDerivAt_const (x := 0) (c := (1 / 2 : ℝ))).sub
      ((hasDerivAt_id (𝕜 := ℝ) 0).div_const 4)
    change HasDerivAt (fun t : ℝ => 1 / 2 - t / 4) (0 - 1 / 4) 0 at h
    norm_num at h ⊢
    exact h
  have h := (hasDerivAt_const (x := 0) (c := (1 / 2 : ℝ))).sub (ha.mul he4)
  change HasDerivAt
    (fun t : ℝ => 1 / 2 - (1 / 2 - t / 4) * Real.exp (-t / 4))
    (0 - ((-1 / 4) * Real.exp (-0 / 4) + (1 / 2 - 0 / 4) * (-1 / 4))) 0 at h
  norm_num at h ⊢
  exact h

/-- The simplified symmetric numerator is asymptotic to `2t`. -/
theorem greedyBumpGaussianSymmetricNumerator_ratio_tendsto :
    Tendsto (fun t : ℝ => greedyBumpGaussianSymmetricNumerator t / t)
      (𝓝[≠] 0) (𝓝 2) := by
  have h := greedyBumpGaussianSymmetricNumerator_hasDerivAt.tendsto_slope_zero
  simpa [slope, greedyBumpGaussianSymmetricNumerator, div_eq_mul_inv,
    mul_comm] using h

/-- The derivative exclusion eigenvalue is asymptotic to `3t/8`. -/
theorem greedyBumpGaussianDMinusSq_ratio_tendsto :
    Tendsto (fun t : ℝ => greedyBumpGaussianDMinusSq t / t)
      (𝓝[≠] 0) (𝓝 (3 / 8 : ℝ)) := by
  have h := greedyBumpGaussianDMinusSq_hasDerivAt.tendsto_slope_zero
  simpa [slope, greedyBumpGaussianDMinusSq, div_eq_mul_inv,
    mul_comm] using h

/-- The symmetric conditional height variance remains finite, tending to `4/3`. -/
theorem greedyBumpGaussianLambdaPlusSq_tendsto :
    Tendsto greedyBumpGaussianLambdaPlusSq (𝓝[≠] 0) (𝓝 (4 / 3 : ℝ)) := by
  have hden := greedyBumpGaussianDMinusSq_ratio_tendsto.const_mul 4
  have hquot := greedyBumpGaussianSymmetricNumerator_ratio_tendsto.div hden
    (by norm_num)
  have hden0 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), greedyBumpGaussianDMinusSq t ≠ 0 := by
    have hscaled : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        4 * (greedyBumpGaussianDMinusSq t / t) ≠ 0 :=
      hden.eventually_ne (by norm_num)
    filter_upwards [self_mem_nhdsWithin, hscaled] with t ht hs
    intro hd
    apply hs
    simp [hd]
  have hquot' : Tendsto
      (fun t : ℝ => (greedyBumpGaussianSymmetricNumerator t / t) /
        (4 * (greedyBumpGaussianDMinusSq t / t)))
      (𝓝[≠] 0) (𝓝 (4 / 3 : ℝ)) := by
    norm_num at hquot ⊢
    exact hquot
  refine hquot'.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hden0] with t ht hd
  have ht0 : t ≠ 0 := by simpa using ht
  rw [greedyBumpGaussianLambdaPlusSq_eq_numerator (t := ⟨t, hd⟩)]
  field_simp [ht0, hd]

/-- In physical separation, the derivative exclusion mode opens as `3x²/8`. -/
theorem greedyBumpGaussianDMinus_ratio_sq_tendsto :
    Tendsto (fun x : ℝ => greedyBumpGaussianDMinus x / x ^ 2)
      (𝓝[≠] 0) (𝓝 (3 / 8 : ℝ)) := by
  have hmap : Tendsto (fun x : ℝ => x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hsq : Tendsto (fun x : ℝ => x ^ 2)
          (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using (by fun_prop : ContinuousAt (fun x : ℝ => x ^ 2) 0).tendsto
      exact hsq.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact pow_ne_zero 2 hx
  have hcomp := greedyBumpGaussianDMinusSq_ratio_tendsto.comp hmap
  refine hcomp.congr' ?_
  filter_upwards with x
  simp only [Function.comp_apply]
  rw [greedyBumpGaussianDMinus_eq_sq]

/-- In physical separation, the symmetric conditional variance tends to `4/3`. -/
theorem greedyBumpGaussianLambdaPlus_tendsto :
    Tendsto greedyBumpGaussianLambdaPlus (𝓝[≠] 0) (𝓝 (4 / 3 : ℝ)) := by
  have hmap : Tendsto (fun x : ℝ => x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hsq : Tendsto (fun x : ℝ => x ^ 2)
          (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using (by fun_prop : ContinuousAt (fun x : ℝ => x ^ 2) 0).tendsto
      exact hsq.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact pow_ne_zero 2 hx
  have hcomp := greedyBumpGaussianLambdaPlusSq_tendsto.comp hmap
  refine hcomp.congr' ?_
  filter_upwards with x
  simp only [Function.comp_apply]
  rw [greedyBumpGaussianLambdaPlus_eq_sq]

/-- Paper's principal-mode separation: `Λ₋/Λ₊` is asymptotic to `x⁶/512`. -/
theorem greedyBumpGaussian_heightMode_ratio_six_tendsto :
    Tendsto (fun x : ℝ =>
      (greedyBumpGaussianLambdaMinus x / greedyBumpGaussianLambdaPlus x) / x ^ 6)
      (𝓝[≠] 0) (𝓝 (1 / 512 : ℝ)) := by
  have hquot := (greedyBumpGaussianLambdaMinus_ratio_six_tendsto).div
    greedyBumpGaussianLambdaPlus_tendsto (by norm_num)
  have hplus0 : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      greedyBumpGaussianLambdaPlus x ≠ 0 :=
    greedyBumpGaussianLambdaPlus_tendsto.eventually_ne (by norm_num)
  have hquot' : Tendsto
      (fun x : ℝ => (greedyBumpGaussianLambdaMinus x / x ^ 6) /
        greedyBumpGaussianLambdaPlus x)
      (𝓝[≠] 0) (𝓝 (1 / 512 : ℝ)) := by
    norm_num at hquot ⊢
    exact hquot
  refine hquot'.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hplus0] with x hx hp
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0, hp]

/-! ## Singular two-slope density -/

/-- Determinant of the two derivative-covariance principal modes. -/
def greedyBumpGaussianDerivativeDeterminant (x : ℝ) : ℝ :=
  greedyBumpGaussianDPlus x * greedyBumpGaussianDMinus x

/-- Joint density of the two slopes at zero in the unit-width Gaussian model. -/
def greedyBumpGaussianZeroSlopeDensity (x : ℝ) : ℝ :=
  1 / (2 * Real.pi * Real.sqrt (greedyBumpGaussianDerivativeDeterminant x))

/-- The nondegenerate derivative mode tends to unit variance at coincidence. -/
theorem greedyBumpGaussianDPlus_tendsto_right :
    Tendsto greedyBumpGaussianDPlus (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt greedyBumpGaussianDPlus 0 := by
    unfold greedyBumpGaussianDPlus greedyBumpGaussianOverlap
    fun_prop
  have h := hc.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  convert h using 1 <;> norm_num [greedyBumpGaussianDPlus, greedyBumpGaussianOverlap]

/-- The vanishing derivative mode has normalized limit `3/8` on positive separations. -/
theorem greedyBumpGaussianDMinus_ratio_sq_tendsto_right :
    Tendsto (fun x : ℝ => greedyBumpGaussianDMinus x / x ^ 2)
      (𝓝[>] 0) (𝓝 (3 / 8 : ℝ)) := by
  exact greedyBumpGaussianDMinus_ratio_sq_tendsto.mono_left
    (nhdsWithin_mono 0 (by
      intro x hx
      simp only [Set.mem_Ioi] at hx
      simp [ne_of_gt hx]))

/-- The derivative determinant divided by `x²` tends to `3/8`. -/
theorem greedyBumpGaussianDerivativeDeterminant_ratio_sq_tendsto :
    Tendsto (fun x : ℝ => greedyBumpGaussianDerivativeDeterminant x / x ^ 2)
      (𝓝[>] 0) (𝓝 (3 / 8 : ℝ)) := by
  have h := greedyBumpGaussianDPlus_tendsto_right.mul
    greedyBumpGaussianDMinus_ratio_sq_tendsto_right
  simpa only [greedyBumpGaussianDerivativeDeterminant, mul_div_assoc, one_mul] using h

/-- Square root of the derivative determinant, after division by positive separation. -/
theorem greedyBumpGaussianSqrtDerivativeDeterminant_ratio_tendsto :
    Tendsto (fun x : ℝ =>
      Real.sqrt (greedyBumpGaussianDerivativeDeterminant x) / x)
      (𝓝[>] 0) (𝓝 (Real.sqrt (3 / 8))) := by
  have hroot : Tendsto
      (fun x : ℝ => Real.sqrt
        (greedyBumpGaussianDerivativeDeterminant x / x ^ 2))
      (𝓝[>] 0) (𝓝 (Real.sqrt (3 / 8))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp
      greedyBumpGaussianDerivativeDeterminant_ratio_sq_tendsto
  refine hroot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hdiv : greedyBumpGaussianDerivativeDeterminant x / x ^ 2 =
      (1 / x ^ 2) * greedyBumpGaussianDerivativeDeterminant x := by ring
  rw [hdiv, Real.sqrt_mul (by positivity : 0 ≤ (1 / x ^ 2 : ℝ)),
    Real.sqrt_div (by positivity : 0 ≤ (1 : ℝ)), Real.sqrt_sq (le_of_lt hx)]
  norm_num
  field_simp [hx0]

/-- Exact radical identity for the paper's zero-slope coefficient. -/
theorem greedyBumpGaussianZeroSlopeCoefficient_eq :
    1 / (2 * Real.pi * Real.sqrt (3 / 8)) =
      Real.sqrt 6 / (3 * Real.pi) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hs38 : Real.sqrt (3 / 8 : ℝ) ≠ 0 := by positivity
  have hm : Real.sqrt (3 / 8 : ℝ) * Real.sqrt 6 = Real.sqrt (9 / 4) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (3 / 8 : ℝ))]
    congr 1
    norm_num
  have hs94 : Real.sqrt (9 / 4 : ℝ) = 3 / 2 := by
    rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hs94] at hm
  field_simp [hpi, hs38]
  nlinarith

/-- Appendix B, Eq. (222): the two-slope density has its exact `1/x` coefficient. -/
theorem greedyBumpGaussianZeroSlopeDensity_scaled_tendsto :
    Tendsto (fun x : ℝ => x * greedyBumpGaussianZeroSlopeDensity x)
      (𝓝[>] 0) (𝓝 (Real.sqrt 6 / (3 * Real.pi))) := by
  have hroot := greedyBumpGaussianSqrtDerivativeDeterminant_ratio_tendsto
  have hquot : Tendsto
      (fun x : ℝ => 1 / (2 * Real.pi *
        (Real.sqrt (greedyBumpGaussianDerivativeDeterminant x) / x)))
      (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi * Real.sqrt (3 / 8)))) := by
    exact tendsto_const_nhds.div
      ((tendsto_const_nhds.mul tendsto_const_nhds).mul hroot)
      (by positivity)
  rw [greedyBumpGaussianZeroSlopeCoefficient_eq] at hquot
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  simp only [greedyBumpGaussianZeroSlopeDensity]
  field_simp [hx0]

end

end GaloisForLFunctions.HTGeometry

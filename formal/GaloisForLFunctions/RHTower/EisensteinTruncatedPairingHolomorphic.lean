import GaloisForLFunctions.RHTower.EisensteinMaassSelbergRegion

/-!
# Holomorphy of the truncated pairing in each parameter

For `Y ≥ 1` and `v ∈ Ω`, the truncated pairing `P(u) = ∫_𝒟 Λ^Y E_u · Λ^Y E_v dμ` is holomorphic in
`u` on the quarter-plane `Ω`.  The integrand is holomorphic in `u` for every `z` and bounded,
uniformly on closed balls in `Ω` and on `𝒟`, by an explicit constant; a Cauchy estimate turns the
value bound into a derivative bound, and dominated differentiation under the integral applies.
The parameter derivative is measurable in `z` as a pointwise limit of difference quotients.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## A bound of the truncated line model valid for every parameter -/

theorem rpow_le_add_of_mem_Icc {y Y : ℝ} (hy : 1 / 2 ≤ y) (hyY : y ≤ Y) (a : ℝ) :
    y ^ a ≤ (1 / 2 : ℝ) ^ a + Y ^ a := by
  have hy0 : 0 < y := by linarith
  have h1 : 0 ≤ (1 / 2 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) _
  have h2 : 0 ≤ Y ^ a := Real.rpow_nonneg (by linarith) _
  rcases le_or_gt 0 a with ha | ha
  · have := Real.rpow_le_rpow hy0.le hyY ha
    linarith
  · have := Real.rpow_le_rpow_of_nonpos (by norm_num) hy ha.le
    linarith

/-- The bound of the truncated line model on `𝒟`, for every parameter. -/
def truncBound' (u : ℂ) (Y : ℝ) : ℝ :=
  ‖msB u‖ * ((1 / 2 : ℝ) ^ (1 / 2 - u.re) + Y ^ (1 / 2 - u.re)) +
    ‖msA u‖ * ((1 / 2 : ℝ) ^ (1 / 2 + u.re) + Y ^ (1 / 2 + u.re)) + tailConst u

theorem norm_truncatedLineModel_le_truncBound' (u : ℂ) {Y : ℝ} (hY : 1 ≤ Y) {z : ℍ}
    (hz : z ∈ fd) : ‖truncatedLineModel u Y z‖ ≤ truncBound' u Y := by
  have hy := half_lt_im_of_mem_fd' hz
  have hT := tailConst_nonneg u
  have hB := norm_nonneg (msB u)
  have hA := norm_nonneg (msA u)
  have hp1 : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 - u.re) + Y ^ (1 / 2 - u.re) := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (1 / 2 - u.re)
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) (1 / 2 - u.re)
    linarith
  have hp2 : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 + u.re) + Y ^ (1 / 2 + u.re) := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (1 / 2 + u.re)
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) (1 / 2 + u.re)
    linarith
  rcases le_or_gt z.im Y with hzY | hzY
  · unfold truncatedLineModel
    rw [if_neg (not_lt.mpr hzY), sub_zero]
    refine (norm_eisensteinLineModel_le u hy.le).trans ?_
    unfold truncBound'
    have h1 := rpow_le_add_of_mem_Icc hy.le hzY (1 / 2 - u.re)
    have h2 := rpow_le_add_of_mem_Icc hy.le hzY (1 / 2 + u.re)
    have h3 : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, z.im_pos])
    nlinarith [mul_le_mul_of_nonneg_left h1 hB, mul_le_mul_of_nonneg_left h2 hA,
      mul_le_mul_of_nonneg_left h3 hT]
  · refine (norm_truncatedLineModel_le_of_gt' hz hzY).trans ?_
    unfold truncBound'
    have h3 : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, z.im_pos])
    nlinarith [mul_le_mul_of_nonneg_left h3 hT, mul_nonneg hB hp1, mul_nonneg hA hp2]

/-! ## Uniform bounds on closed balls -/

/-- A norm-monotone majorant of `tailConst`. -/
def tailConstBound (R : ℝ) : ℝ :=
  4 * Real.exp ((R + 1) ^ 2 / (2 * Real.pi)) *
    ∑' N : ℕ, ((N : ℝ) + 1) ^ (⌈3 * (R + 1) + 1⌉₊) * Real.exp (-Real.pi * (N : ℝ))

theorem summable_tailBoundTerm (R : ℝ) :
    Summable (fun N : ℕ => ((N : ℝ) + 1) ^ (⌈3 * (R + 1) + 1⌉₊) * Real.exp (-Real.pi * (N : ℝ))) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul (⌈3 * (R + 1) + 1⌉₊) Real.pi_pos
  have h' := (summable_nat_add_iff 1).mpr h
  have h'' : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (⌈3 * (R + 1) + 1⌉₊) *
      Real.exp (-Real.pi * ((n : ℝ) + 1)) := by
    refine h'.congr fun n => ?_
    push_cast
    ring_nf
  have h3 := h''.mul_right (Real.exp Real.pi)
  refine h3.congr fun n => ?_
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

theorem tailConst_le_of_norm_le {u : ℂ} {R : ℝ} (hR : 0 ≤ R) (hu : ‖u‖ ≤ R) :
    tailConst u ≤ tailConstBound R := by
  unfold tailConst tailConstBound tailSeriesSum
  have h1 : Real.exp ((‖u‖ + 1) ^ 2 / (2 * Real.pi)) ≤ Real.exp ((R + 1) ^ 2 / (2 * Real.pi)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := norm_nonneg u
    nlinarith
  have h2 : (∑' N : ℕ, tailSeriesTerm u N) ≤
      ∑' N : ℕ, ((N : ℝ) + 1) ^ (⌈3 * (R + 1) + 1⌉₊) * Real.exp (-Real.pi * (N : ℝ)) := by
    refine Summable.tsum_le_tsum (fun N => ?_) (summable_tailSeriesTerm u) (summable_tailBoundTerm R)
    unfold tailSeriesTerm
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply pow_le_pow_right₀ (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
    apply Nat.ceil_le_ceil
    have := norm_nonneg u
    linarith
  have hs := tailSeriesSum_nonneg u
  have hs' : 0 ≤ ∑' N : ℕ, ((N : ℝ) + 1) ^ (⌈3 * (R + 1) + 1⌉₊) * Real.exp (-Real.pi * (N : ℝ)) :=
    tsum_nonneg fun N => by positivity
  unfold tailSeriesSum at hs
  calc 4 * Real.exp ((‖u‖ + 1) ^ 2 / (2 * Real.pi)) * ∑' N : ℕ, tailSeriesTerm u N
      ≤ 4 * Real.exp ((R + 1) ^ 2 / (2 * Real.pi)) * ∑' N : ℕ, tailSeriesTerm u N := by gcongr
    _ ≤ _ := by gcongr

theorem norm_le_of_mem_closedBall {u₀ u : ℂ} {r : ℝ} (hu : u ∈ Metric.closedBall u₀ r) :
    ‖u‖ ≤ ‖u₀‖ + r := by
  have h := Metric.mem_closedBall.mp hu
  rw [dist_eq_norm] at h
  calc ‖u‖ = ‖u₀ + (u - u₀)‖ := by ring_nf
    _ ≤ ‖u₀‖ + ‖u - u₀‖ := norm_add_le _ _
    _ ≤ ‖u₀‖ + r := by linarith

theorem continuousOn_msA : ContinuousOn msA eisensteinLineDomain := by
  intro u hu
  exact (hasDerivAt_msA hu).continuousAt.continuousWithinAt

theorem continuousOn_msB : ContinuousOn msB eisensteinLineDomain := by
  intro u hu
  exact (hasDerivAt_msB hu).continuousAt.continuousWithinAt

/-- **Uniform bound on a closed ball inside `Ω`.** -/
theorem exists_truncBound_closedBall {u₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall u₀ r ⊆ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Metric.closedBall u₀ r, ∀ z ∈ fd, ‖truncatedLineModel u Y z‖ ≤ M := by
  obtain ⟨CA, hCA⟩ := (isCompact_closedBall u₀ r).exists_bound_of_continuousOn
    (continuousOn_msA.mono hball)
  obtain ⟨CB, hCB⟩ := (isCompact_closedBall u₀ r).exists_bound_of_continuousOn
    (continuousOn_msB.mono hball)
  set R : ℝ := ‖u₀‖ + r with hR
  have hR0 : 0 ≤ R := by have := norm_nonneg u₀; linarith
  -- exponent bounds
  have hpow : ∀ a : ℝ, |a| ≤ R → (1 / 2 : ℝ) ^ (1 / 2 - a) + Y ^ (1 / 2 - a) ≤
      (1 / 2 : ℝ) ^ (1 / 2 - R) + Y ^ (1 / 2 + R) := by
    intro a ha
    have ha' := abs_le.mp ha
    have e1 : (1 / 2 : ℝ) ^ (1 / 2 - a) ≤ (1 / 2 : ℝ) ^ (1 / 2 - R) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    have e2 : Y ^ (1 / 2 - a) ≤ Y ^ (1 / 2 + R) :=
      Real.rpow_le_rpow_of_exponent_le hY (by linarith)
    linarith
  have hpow' : ∀ a : ℝ, |a| ≤ R → (1 / 2 : ℝ) ^ (1 / 2 + a) + Y ^ (1 / 2 + a) ≤
      (1 / 2 : ℝ) ^ (1 / 2 - R) + Y ^ (1 / 2 + R) := by
    intro a ha
    have ha' := abs_le.mp ha
    have e1 : (1 / 2 : ℝ) ^ (1 / 2 + a) ≤ (1 / 2 : ℝ) ^ (1 / 2 - R) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    have e2 : Y ^ (1 / 2 + a) ≤ Y ^ (1 / 2 + R) :=
      Real.rpow_le_rpow_of_exponent_le hY (by linarith)
    linarith
  set K : ℝ := (1 / 2 : ℝ) ^ (1 / 2 - R) + Y ^ (1 / 2 + R) with hK
  have hK0 : 0 ≤ K := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (1 / 2 - R)
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) (1 / 2 + R)
    rw [hK]; linarith
  refine ⟨|CB| * K + |CA| * K + tailConstBound R, by
    have := tailConst_nonneg 0
    have : 0 ≤ tailConstBound R := le_trans (tailConst_nonneg 0)
      (tailConst_le_of_norm_le hR0 (by simp; exact hR0))
    positivity, fun u hu z hz => ?_⟩
  refine (norm_truncatedLineModel_le_truncBound' u hY hz).trans ?_
  unfold truncBound'
  have hnu : ‖u‖ ≤ R := norm_le_of_mem_closedBall hu
  have hre : |u.re| ≤ R := (Complex.abs_re_le_norm u).trans hnu
  have hB := (hCB u hu).trans (le_abs_self CB)
  have hA := (hCA u hu).trans (le_abs_self CA)
  have hT := tailConst_le_of_norm_le hR0 hnu
  have p1 := hpow u.re hre
  have p2 := hpow' u.re hre
  have hp1 : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 - u.re) + Y ^ (1 / 2 - u.re) := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (1 / 2 - u.re)
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) (1 / 2 - u.re)
    linarith
  have hp2 : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 + u.re) + Y ^ (1 / 2 + u.re) := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (1 / 2 + u.re)
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) (1 / 2 + u.re)
    linarith
  have hB0 := norm_nonneg (msB u)
  have hA0 := norm_nonneg (msA u)
  nlinarith [mul_le_mul hB p1 hp1 (abs_nonneg CB), mul_le_mul hA p2 hp2 (abs_nonneg CA)]

/-! ## Holomorphy of the integrand in the parameter -/

theorem differentiableOn_truncatedLineModel_param (Y : ℝ) (z : ℍ) :
    DifferentiableOn ℂ (fun u => truncatedLineModel u Y z) eisensteinLineDomain := by
  intro u hu
  unfold truncatedLineModel eisensteinLineModel
  refine DifferentiableWithinAt.sub ?_ ?_
  · exact (differentiableOn_cuspLeg z.re z.im_pos u hu)
  · by_cases h : Y < z.im
    · simp only [if_pos h]
      exact (differentiableAt_cuspConstantPart z.im_pos hu).differentiableWithinAt
    · simp only [if_neg h]
      exact differentiableWithinAt_const _

/-- The integrand of the truncated pairing. -/
def pairingIntegrand (v : ℂ) (Y : ℝ) (u : ℂ) (z : ℍ) : ℂ :=
  truncatedLineModel u Y z * truncatedLineModel v Y z

theorem differentiableOn_pairingIntegrand_param (v : ℂ) (Y : ℝ) (z : ℍ) :
    DifferentiableOn ℂ (fun u => pairingIntegrand v Y u z) eisensteinLineDomain :=
  (differentiableOn_truncatedLineModel_param Y z).mul_const _

theorem measurable_pairingIntegrand (v : ℂ) (Y : ℝ) (u : ℂ) :
    Measurable (pairingIntegrand v Y u) :=
  (measurable_truncatedLineModel u Y).mul (measurable_truncatedLineModel v Y)

/-- The parameter derivative is measurable in `z`: it is the limit of difference quotients. -/
theorem measurable_deriv_param {v : ℂ} (Y : ℝ) {u₀ : ℂ} (hu₀ : u₀ ∈ eisensteinLineDomain) :
    Measurable (fun z : ℍ => deriv (fun u => pairingIntegrand v Y u z) u₀) := by
  let h : ℕ → ℂ := fun n => u₀ + 1 / ((n : ℂ) + 1)
  have hne : ∀ n, h n ≠ u₀ := by
    intro n habs
    have h1 : (1 : ℂ) / ((n : ℂ) + 1) = 0 := by
      have := congrArg (fun w => w - u₀) habs
      simpa [h] using this
    exact one_div_ne_zero (Nat.cast_add_one_ne_zero n) h1
  have hlim : Tendsto h atTop (𝓝[≠] u₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall hne⟩
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).const_add u₀
    simpa [h] using this
  refine measurable_of_tendsto_metrizable (f := fun n z =>
    slope (fun u => pairingIntegrand v Y u z) u₀ (h n)) (fun n => ?_) ?_
  · simp_rw [slope_def_field]
    exact ((measurable_pairingIntegrand v Y (h n)).sub (measurable_pairingIntegrand v Y u₀)).div_const _
  · rw [tendsto_pi_nhds]
    intro z
    have hd : HasDerivAt (fun u => pairingIntegrand v Y u z)
        (deriv (fun u => pairingIntegrand v Y u z) u₀) u₀ :=
      ((differentiableOn_pairingIntegrand_param v Y z).differentiableAt
        (isOpen_eisensteinLineDomain.mem_nhds hu₀)).hasDerivAt
    exact (hasDerivAt_iff_tendsto_slope.mp hd).comp hlim

/-! ## Dominated differentiation -/

theorem exists_ball_subset {u₀ : ℂ} (hu₀ : u₀ ∈ eisensteinLineDomain) :
    ∃ r > 0, Metric.closedBall u₀ (2 * r) ⊆ eisensteinLineDomain := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_eisensteinLineDomain.mem_nhds hu₀)
  refine ⟨ε / 4, by positivity, ?_⟩
  refine (Metric.closedBall_subset_ball (by linarith)).trans hball

/-- **The truncated pairing is differentiable in the first parameter.** -/
theorem hasDerivAt_truncatedPairing {v : ℂ} {Y : ℝ} (hY : 1 ≤ Y) {u₀ : ℂ}
    (hu₀ : u₀ ∈ eisensteinLineDomain) :
    HasDerivAt (fun u => ∫ z in fd, pairingIntegrand v Y u z)
      (∫ z in fd, deriv (fun u => pairingIntegrand v Y u z) u₀) u₀ := by
  obtain ⟨r, hr, hball⟩ := exists_ball_subset hu₀
  obtain ⟨M, hM0, hM⟩ := exists_truncBound_closedBall (by positivity) hball hY
  -- the value bound on the ball of radius `2r`
  have hval : ∀ u ∈ Metric.closedBall u₀ (2 * r), ∀ z ∈ fd,
      ‖pairingIntegrand v Y u z‖ ≤ M * truncBound' v Y := by
    intro u hu z hz
    unfold pairingIntegrand
    rw [norm_mul]
    exact mul_le_mul (hM u hu z hz) (norm_truncatedLineModel_le_truncBound' v hY hz)
      (norm_nonneg _) hM0
  -- the derivative bound on the ball of radius `r` by the Cauchy estimate
  have hderiv : ∀ u ∈ Metric.ball u₀ r, ∀ z ∈ fd,
      ‖deriv (fun u => pairingIntegrand v Y u z) u‖ ≤ M * truncBound' v Y / r := by
    intro u hu z hz
    have hsub : Metric.closedBall u r ⊆ Metric.closedBall u₀ (2 * r) := by
      intro w hw
      rw [Metric.mem_closedBall] at hw ⊢
      have := Metric.mem_ball.mp hu
      linarith [dist_triangle w u u₀]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
      ((differentiableOn_pairingIntegrand_param v Y z).diffContOnCl_ball (hsub.trans hball))
      fun w hw => ?_
    exact hval w (hsub (Metric.sphere_subset_closedBall hw)) z hz
  have hs : Metric.ball u₀ r ∈ 𝓝 u₀ := Metric.ball_mem_nhds u₀ hr
  have hmeas : ∀ᶠ u in 𝓝 u₀, AEStronglyMeasurable (pairingIntegrand v Y u) (volume.restrict fd) :=
    Filter.Eventually.of_forall fun u => (measurable_pairingIntegrand v Y u).aestronglyMeasurable
  have hint : Integrable (pairingIntegrand v Y u₀) (volume.restrict fd) := by
    refine Integrable.mono' (integrableOn_const (C := M * truncBound' v Y) (by simp [volume_fd_ne_top]))
      (measurable_pairingIntegrand v Y u₀).aestronglyMeasurable ?_
    exact (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Filter.Eventually.of_forall fun z hz =>
      hval u₀ (Metric.mem_closedBall_self (by positivity)) z hz)
  have hF'meas : AEStronglyMeasurable (fun z => deriv (fun u => pairingIntegrand v Y u z) u₀)
      (volume.restrict fd) := (measurable_deriv_param Y hu₀).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(volume.restrict fd), ∀ u ∈ Metric.ball u₀ r,
      ‖deriv (fun u => pairingIntegrand v Y u z) u‖ ≤ M * truncBound' v Y / r :=
    (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Filter.Eventually.of_forall fun z hz u hu =>
      hderiv u hu z hz)
  have hbint : Integrable (fun _ : ℍ => M * truncBound' v Y / r) (volume.restrict fd) :=
    integrableOn_const (by simp [volume_fd_ne_top])
  have hdiff : ∀ᵐ z ∂(volume.restrict fd), ∀ u ∈ Metric.ball u₀ r,
      HasDerivAt (fun u => pairingIntegrand v Y u z) (deriv (fun u => pairingIntegrand v Y u z) u) u := by
    refine Filter.Eventually.of_forall fun z w hw => ?_
    have hwmem : w ∈ eisensteinLineDomain :=
      hball (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hw)
    exact ((differentiableOn_pairingIntegrand_param v Y z).differentiableAt
      (isOpen_eisensteinLineDomain.mem_nhds hwmem)).hasDerivAt
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint hF'meas hbound hbint hdiff).2

/-- **Holomorphy of the truncated pairing in the first parameter.** -/
theorem differentiableOn_truncatedPairing_left (v : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    DifferentiableOn ℂ (fun u => ∫ z in fd, truncatedLineModel u Y z * truncatedLineModel v Y z)
      eisensteinLineDomain :=
  fun _ hu => (hasDerivAt_truncatedPairing (v := v) hY hu).differentiableAt.differentiableWithinAt

/-- **Holomorphy of the truncated pairing in the second parameter.** -/
theorem differentiableOn_truncatedPairing_right (u : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    DifferentiableOn ℂ (fun v => ∫ z in fd, truncatedLineModel u Y z * truncatedLineModel v Y z)
      eisensteinLineDomain := by
  have h := differentiableOn_truncatedPairing_left u hY
  refine h.congr fun v _ => ?_
  simp_rw [mul_comm]

end

end RHTower

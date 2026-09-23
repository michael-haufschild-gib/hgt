import GaloisForLFunctions.RHTower.LevinsonLinearOptimization

/-!
# Interior mollifier length from the endpoint scalar optimization

Young's analytic mollified-moment theorem is applied at a fixed
`0 < theta < 1/2`, whereas the clean scalar evaluation occurs at the limiting
value `theta = 1/2`.  This file proves the missing continuity bridge and
extracts an actual interior parameter retaining the strict `> 1/3` margin.
-/

noncomputable section

namespace RHTower

open MeasureTheory Filter Topology

/-- Young's linear integrand derivative at variable mollifier exponent
`theta`, with `R = 13/10`. -/
def levinsonLinearOptimizationDerivativeAt (theta u v : ℝ) : ℝ :=
  (1 - v) * (1 + ((13 / 10) * theta) * u) - theta * u

/-- Young's linear mollified-moment constant at variable mollifier exponent. -/
def levinsonLinearOptimizationConstantAt (theta : ℝ) : ℝ :=
  1 + theta⁻¹ * ∫ v in (0 : ℝ)..1,
    Real.exp ((13 / 5) * v) *
      (∫ u in (0 : ℝ)..1,
        levinsonLinearOptimizationDerivativeAt theta u v ^ (2 : ℕ))

lemma levinsonLinearOptimizationDerivativeAt_half (u v : ℝ) :
    levinsonLinearOptimizationDerivativeAt (1 / 2) u v =
      levinsonLinearOptimizationDerivative u v := by
  unfold levinsonLinearOptimizationDerivativeAt
    levinsonLinearOptimizationDerivative
  norm_num

theorem levinsonLinearOptimizationConstantAt_half :
    levinsonLinearOptimizationConstantAt (1 / 2) =
      levinsonLinearOptimizationConstant := by
  unfold levinsonLinearOptimizationConstantAt
    levinsonLinearOptimizationConstant
  norm_num
  simp_rw [levinsonLinearOptimizationDerivativeAt_half]

private def levinsonLinearOptimizationBase (v : ℝ) : ℝ := 1 - v

private def levinsonLinearOptimizationSlope (v : ℝ) : ℝ :=
  (13 / 10) * (1 - v) - 1

private def levinsonLinearOptimizationOuterBaseMoment : ℝ :=
  ∫ v in (0 : ℝ)..1, Real.exp ((13 / 5) * v) *
    levinsonLinearOptimizationBase v ^ (2 : ℕ)

private def levinsonLinearOptimizationOuterCrossMoment : ℝ :=
  ∫ v in (0 : ℝ)..1, Real.exp ((13 / 5) * v) *
    (levinsonLinearOptimizationBase v * levinsonLinearOptimizationSlope v)

private def levinsonLinearOptimizationOuterDerivativeMoment : ℝ :=
  ∫ v in (0 : ℝ)..1, Real.exp ((13 / 5) * v) *
    (levinsonLinearOptimizationSlope v ^ (2 : ℕ) / 3)

private lemma integral_levinsonLinearOptimizationDerivativeAt_sq (theta v : ℝ) :
    (∫ u in (0 : ℝ)..1,
      levinsonLinearOptimizationDerivativeAt theta u v ^ (2 : ℕ)) =
      levinsonLinearOptimizationBase v ^ (2 : ℕ) +
        theta * levinsonLinearOptimizationBase v *
          levinsonLinearOptimizationSlope v +
        theta ^ (2 : ℕ) * levinsonLinearOptimizationSlope v ^ (2 : ℕ) / 3 := by
  let A : ℝ := levinsonLinearOptimizationBase v
  let B : ℝ := levinsonLinearOptimizationSlope v
  let F : ℝ → ℝ := fun u =>
    A ^ (2 : ℕ) * u + (theta * A * B) * u ^ (2 : ℕ) +
      (theta ^ (2 : ℕ) * B ^ (2 : ℕ) / 3) * u ^ (3 : ℕ)
  have hderiv : ∀ u : ℝ,
      HasDerivAt F (levinsonLinearOptimizationDerivativeAt theta u v ^ (2 : ℕ)) u := by
    intro u
    have hraw := (((hasDerivAt_id u).const_mul (A ^ (2 : ℕ))).add
        (((hasDerivAt_id u).pow 2).const_mul (theta * A * B))).add
          (((hasDerivAt_id u).pow 3).const_mul (theta ^ (2 : ℕ) * B ^ (2 : ℕ) / 3))
    change HasDerivAt F _ u at hraw
    exact hraw.congr_deriv (by
      dsimp only [F, A, B, levinsonLinearOptimizationBase,
        levinsonLinearOptimizationSlope,
        levinsonLinearOptimizationDerivativeAt] at *
      simp only [id_eq] at *
      ring)
  have hint : IntervalIntegrable
      (fun u : ℝ => levinsonLinearOptimizationDerivativeAt theta u v ^ (2 : ℕ))
      volume 0 1 :=
    (show Continuous (fun u : ℝ =>
      levinsonLinearOptimizationDerivativeAt theta u v ^ (2 : ℕ)) by
        unfold levinsonLinearOptimizationDerivativeAt
        fun_prop).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hderiv u) hint]
  dsimp only [F, A, B]
  norm_num

private lemma levinsonLinearOptimizationOuterIntegral_eq (theta : ℝ) :
    (∫ v in (0 : ℝ)..1, Real.exp ((13 / 5) * v) *
      (∫ u in (0 : ℝ)..1,
        levinsonLinearOptimizationDerivativeAt theta u v ^ (2 : ℕ))) =
      levinsonLinearOptimizationOuterBaseMoment +
        theta * levinsonLinearOptimizationOuterCrossMoment +
        theta ^ (2 : ℕ) * levinsonLinearOptimizationOuterDerivativeMoment := by
  simp_rw [integral_levinsonLinearOptimizationDerivativeAt_sq]
  let f0 : ℝ → ℝ := fun v => Real.exp ((13 / 5) * v) *
    levinsonLinearOptimizationBase v ^ (2 : ℕ)
  let f1 : ℝ → ℝ := fun v => Real.exp ((13 / 5) * v) *
    (levinsonLinearOptimizationBase v * levinsonLinearOptimizationSlope v)
  let f2 : ℝ → ℝ := fun v => Real.exp ((13 / 5) * v) *
    (levinsonLinearOptimizationSlope v ^ (2 : ℕ) / 3)
  have h0 : IntervalIntegrable f0 volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [f0, levinsonLinearOptimizationBase]
    fun_prop
  have h1 : IntervalIntegrable f1 volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [f1, levinsonLinearOptimizationBase,
      levinsonLinearOptimizationSlope]
    fun_prop
  have h2 : IntervalIntegrable f2 volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [f2, levinsonLinearOptimizationSlope]
    fun_prop
  have hpoint : ∀ v : ℝ,
      Real.exp ((13 / 5) * v) *
          (levinsonLinearOptimizationBase v ^ (2 : ℕ) +
            theta * levinsonLinearOptimizationBase v *
              levinsonLinearOptimizationSlope v +
            theta ^ (2 : ℕ) * levinsonLinearOptimizationSlope v ^ (2 : ℕ) / 3) =
        f0 v + theta * f1 v + theta ^ (2 : ℕ) * f2 v := by
    intro v
    dsimp only [f0, f1, f2]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add
      (h0.add (h1.const_mul theta)) (h2.const_mul (theta ^ (2 : ℕ))),
    intervalIntegral.integral_add h0 (h1.const_mul theta),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rfl

private theorem levinsonLinearOptimizationConstantAt_eq (theta : ℝ) :
    levinsonLinearOptimizationConstantAt theta =
      1 + theta⁻¹ * (levinsonLinearOptimizationOuterBaseMoment +
        theta * levinsonLinearOptimizationOuterCrossMoment +
        theta ^ (2 : ℕ) * levinsonLinearOptimizationOuterDerivativeMoment) := by
  rw [levinsonLinearOptimizationConstantAt,
    levinsonLinearOptimizationOuterIntegral_eq]

theorem continuousAt_levinsonLinearOptimizationConstantAt_half :
    ContinuousAt levinsonLinearOptimizationConstantAt (1 / 2) := by
  rw [show levinsonLinearOptimizationConstantAt = fun theta =>
      1 + theta⁻¹ * (levinsonLinearOptimizationOuterBaseMoment +
        theta * levinsonLinearOptimizationOuterCrossMoment +
        theta ^ (2 : ℕ) * levinsonLinearOptimizationOuterDerivativeMoment) by
    funext theta
    exact levinsonLinearOptimizationConstantAt_eq theta]
  have hne : (1 / 2 : ℝ) ≠ 0 := by norm_num
  fun_prop

lemma levinsonLinearOptimizationConstantAt_pos {theta : ℝ}
    (htheta : 0 < theta) :
    0 < levinsonLinearOptimizationConstantAt theta := by
  have hinner : ∀ v : ℝ,
      0 ≤ ∫ u in (0 : ℝ)..1,
        levinsonLinearOptimizationDerivativeAt theta u v ^ (2 : ℕ) := by
    intro v
    exact intervalIntegral.integral_nonneg (by norm_num) fun u hu => sq_nonneg _
  have houter : 0 ≤ ∫ v in (0 : ℝ)..1,
      Real.exp ((13 / 5) * v) *
        (∫ u in (0 : ℝ)..1,
          levinsonLinearOptimizationDerivativeAt theta u v ^ (2 : ℕ)) := by
    exact intervalIntegral.integral_nonneg (by norm_num) fun v hv =>
      mul_nonneg (Real.exp_pos _).le (hinner v)
  unfold levinsonLinearOptimizationConstantAt
  have hinv : 0 < theta⁻¹ := inv_pos.mpr htheta
  nlinarith

/-- Levinson proportion supplied by Young's linear scalar constant at
mollifier exponent `theta`. -/
def levinsonLinearOptimizationProportionAt (theta : ℝ) : ℝ :=
  1 - Real.log (levinsonLinearOptimizationConstantAt theta) / (13 / 10)

theorem continuousAt_levinsonLinearOptimizationProportionAt_half :
    ContinuousAt levinsonLinearOptimizationProportionAt (1 / 2) := by
  unfold levinsonLinearOptimizationProportionAt
  have hcne : levinsonLinearOptimizationConstantAt (1 / 2) ≠ 0 :=
    (levinsonLinearOptimizationConstantAt_pos (by norm_num)).ne'
  exact continuousAt_const.sub
    ((continuousAt_levinsonLinearOptimizationConstantAt_half.log hcne).div_const _)

/-- An actual admissible mollifier exponent strictly below `1/2` retains
Young's strict `> 1/3` scalar margin. -/
theorem exists_levinsonLinearOptimizationProportion_gt_one_third :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 / 2 ∧
      levinsonLinearOptimizationProportionAt theta > 1 / 3 := by
  have hhalf : levinsonLinearOptimizationProportionAt (1 / 2) > 1 / 3 := by
    rw [levinsonLinearOptimizationProportionAt,
      levinsonLinearOptimizationConstantAt_half]
    exact one_sub_log_levinsonLinearOptimizationConstant_div_gt_one_third
  have hevent : ∀ᶠ theta in 𝓝 (1 / 2 : ℝ),
      levinsonLinearOptimizationProportionAt theta > 1 / 3 :=
    continuousAt_levinsonLinearOptimizationProportionAt_half.eventually_const_lt hhalf
  rw [Metric.eventually_nhds_iff] at hevent
  obtain ⟨epsilon, hepsilon, hball⟩ := hevent
  let delta : ℝ := min (epsilon / 2) (1 / 4)
  refine ⟨1 / 2 - delta, ?_, ?_, ?_⟩
  · have hdle : delta ≤ 1 / 4 := min_le_right _ _
    dsimp only [delta] at hdle ⊢
    linarith
  · have hdpos : 0 < delta := lt_min (by linarith) (by norm_num)
    dsimp only [delta] at hdpos ⊢
    linarith
  · apply hball
    rw [Real.dist_eq]
    have hdpos : 0 < delta := lt_min (by linarith) (by norm_num)
    have hdle : delta ≤ epsilon / 2 := min_le_left _ _
    have hdlt : delta < epsilon := by linarith
    rw [show 1 / 2 - delta - 1 / 2 = -delta by ring, abs_neg,
      abs_of_pos hdpos]
    exact hdlt

end RHTower

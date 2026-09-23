import GaloisForLFunctions.HTGeometry.GammaCommonInverseCollar

/-!
# Capacity congruence of the two Gamma inverse charts

The normalized inverse-Gamma branch and the intrinsic moving-base branch differ by the exact
Möbius chart `z ↦ z / (1 - a z)`.  On the common collar the factorial shell satisfies
`‖a z‖ < 1/2`.  The differential of the chart is multiplication by `(1 - a z)⁻²`; consequently
the two Hermitian tangent metrics are uniformly congruent, with constants independent of the
Gamma pole depth.  This closes the metric part of the previously proved analytic comparison of
the two filtrations.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions

/-- The derivative of the tangent Möbius comparison chart is its inverse-square half-density
factor. -/
theorem hasDerivAt_mobiusTangentGerm
    {a z : ℂ} (hden : 1 - a * z ≠ 0) :
    HasDerivAt (mobiusTangentGerm a) ((1 - a * z)⁻¹ ^ (2 : ℕ)) z := by
  have hnum : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
  have hden' : HasDerivAt (fun w : ℂ => 1 - a * w) (-a) z := by
    simpa using!
      (hasDerivAt_const z (1 : ℂ)).sub
        ((hasDerivAt_const z a).mul (hasDerivAt_id z))
  change HasDerivAt (fun w : ℂ => w / (1 - a * w)) ((1 - a * z)⁻¹ ^ (2 : ℕ)) z
  convert! hnum.div hden' hden using 1
  field_simp [hden]
  ring

/-- Exact differential transport through the moving-base Gamma chart. -/
theorem hasDerivAt_gammaMovingBaseTransition_of_branch
    {n : ℕ} {t v : ℂ}
    (hbranch : HasDerivAt (gammaCommonInverseCollar.branch n) v t)
    (hden : 1 - gammaMovingBaseShell n * gammaCommonInverseCollar.branch n t ≠ 0) :
    HasDerivAt (gammaMovingBaseTransition n)
      ((1 - gammaMovingBaseShell n * gammaCommonInverseCollar.branch n t)⁻¹ ^ (2 : ℕ) * v) t := by
  have hmobius := hasDerivAt_mobiusTangentGerm hden
  simpa [gammaMovingBaseTransition, mobiusTangentGerm] using! hmobius.comp t hbranch

/-- Exact conformal change of the squared tangent metric under a Möbius comparison chart. -/
theorem norm_sq_mobiusTangentDifferential
    (u v : ℂ) :
    ‖(1 - u)⁻¹ ^ (2 : ℕ) * v‖ ^ (2 : ℕ) = ‖v‖ ^ (2 : ℕ) / ‖1 - u‖ ^ (4 : ℕ) := by
  rw [norm_mul, norm_pow, norm_inv, mul_pow]
  field_simp

/-- On the source collar `‖u‖ < 1/2`, the moving-base tangent metric is uniformly equivalent to
the normalized-branch metric.  The constants are absolute and independent of the pole depth. -/
theorem mobiusTangentDifferential_capacity_congruent
    {u v : ℂ} (hu : ‖u‖ < (1 / 2 : ℝ)) :
    (16 / 81 : ℝ) * ‖v‖ ^ (2 : ℕ) ≤ ‖(1 - u)⁻¹ ^ (2 : ℕ) * v‖ ^ (2 : ℕ) ∧
      ‖(1 - u)⁻¹ ^ (2 : ℕ) * v‖ ^ (2 : ℕ) ≤ 16 * ‖v‖ ^ (2 : ℕ) := by
  have hlower : (1 / 2 : ℝ) < ‖1 - u‖ := by
    have htri : ‖(1 : ℂ)‖ ≤ ‖1 - u‖ + ‖u‖ := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        norm_add_le (1 - u) u
    norm_num at htri
    linarith
  have hupper : ‖1 - u‖ < (3 / 2 : ℝ) := by
    calc
      ‖1 - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
      _ < 3 / 2 := by norm_num; linarith
  have hpos : 0 < ‖1 - u‖ := lt_trans (by norm_num) hlower
  rw [norm_sq_mobiusTangentDifferential]
  constructor
  · have hfour : ‖1 - u‖ ^ (4 : ℕ) < (81 / 16 : ℝ) := by
      calc
        ‖1 - u‖ ^ (4 : ℕ) < (3 / 2 : ℝ) ^ (4 : ℕ) := by gcongr
        _ = 81 / 16 := by norm_num
    have hinv : (16 / 81 : ℝ) ≤ 1 / ‖1 - u‖ ^ (4 : ℕ) := by
      apply (le_div_iff₀ (pow_pos hpos 4)).2
      nlinarith [hfour.le]
    calc
      (16 / 81 : ℝ) * ‖v‖ ^ (2 : ℕ) ≤ (1 / ‖1 - u‖ ^ (4 : ℕ)) * ‖v‖ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hinv (sq_nonneg ‖v‖)
      _ = ‖v‖ ^ (2 : ℕ) / ‖1 - u‖ ^ (4 : ℕ) := by ring
  · have hfour : (1 / 16 : ℝ) < ‖1 - u‖ ^ (4 : ℕ) := by
      calc
        (1 / 16 : ℝ) = (1 / 2 : ℝ) ^ (4 : ℕ) := by norm_num
        _ < ‖1 - u‖ ^ (4 : ℕ) := by gcongr
    have hinv : 1 / ‖1 - u‖ ^ (4 : ℕ) ≤ (16 : ℝ) := by
      apply (div_le_iff₀ (pow_pos hpos 4)).2
      nlinarith [hfour.le]
    calc
      ‖v‖ ^ (2 : ℕ) / ‖1 - u‖ ^ (4 : ℕ) = (1 / ‖1 - u‖ ^ (4 : ℕ)) * ‖v‖ ^ (2 : ℕ) := by ring
      _ ≤ 16 * ‖v‖ ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hinv (sq_nonneg ‖v‖)

/-- Gamma specialization of the absolute capacity-congruence law on the selected common inverse
collar. -/
theorem gammaMovingBaseTransition_capacity_congruent
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {t v : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) (1 / 4))
    (hshell : ‖gammaMovingBaseShell n‖ < (1 / 2 : ℝ)) :
    (16 / 81 : ℝ) * ‖v‖ ^ (2 : ℕ) ≤
        ‖(1 - gammaMovingBaseShell n * gammaCommonInverseCollar.branch n t)⁻¹ ^ (2 : ℕ) * v‖ ^ (2 : ℕ) ∧
      ‖(1 - gammaMovingBaseShell n * gammaCommonInverseCollar.branch n t)⁻¹ ^ (2 : ℕ) * v‖ ^ (2 : ℕ) ≤
        16 * ‖v‖ ^ (2 : ℕ) := by
  have hbranch := gammaCommonInverseCollar_branch_mem hn ht
  have hbranchNorm : ‖gammaCommonInverseCollar.branch n t‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_left] using hbranch
  apply mobiusTangentDifferential_capacity_congruent
  rw [norm_mul]
  calc
    ‖gammaMovingBaseShell n‖ * ‖gammaCommonInverseCollar.branch n t‖
        ≤ ‖gammaMovingBaseShell n‖ * 1 :=
      mul_le_mul_of_nonneg_left hbranchNorm.le (norm_nonneg _)
    _ < 1 / 2 := by simpa using hshell

/-- The differential comparison factor tends to the identity at every point of the common
collar.  Thus the bounded congruence above is asymptotically isometric, not merely uniformly
equivalent. -/
theorem tendsto_gammaMovingBaseTangentFactor_one
    {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) (1 / 4)) :
    Tendsto
      (fun n : ℕ =>
        (1 - gammaMovingBaseShell n * gammaCommonInverseCollar.branch n t)⁻¹ ^ (2 : ℕ))
      atTop (nhds 1) := by
  have hbranch : Tendsto (fun n : ℕ => gammaCommonInverseCollar.branch n t)
      atTop (nhds t) :=
    tendsto_gammaCommonInverseCollar_branch_uniformlyOn.tendsto_at ht
  have hprod : Tendsto
      (fun n : ℕ => gammaMovingBaseShell n * gammaCommonInverseCollar.branch n t)
      atTop (nhds 0) := by
    simpa using tendsto_gammaMovingBaseShell_zero.mul hbranch
  have hden : Tendsto
      (fun n : ℕ => 1 - gammaMovingBaseShell n * gammaCommonInverseCollar.branch n t)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hprod
  simpa using (hden.inv₀ one_ne_zero).pow 2

end GaloisForLFunctions

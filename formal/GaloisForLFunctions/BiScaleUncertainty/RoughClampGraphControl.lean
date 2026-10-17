import GaloisForLFunctions.BiScaleUncertainty.RoughSobolevClamp
import GaloisForLFunctions.BiScaleUncertainty.CompactSourceGraphCoercivity

/-!
# Firm graph contraction and rigidity of the actual rough clamp

Clamping and its residual split additive path budgets exactly, while their
jump energies obey a firm contraction inequality. Compact-source coercivity
controls the removed state's variance and classifies every equality case.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
open SobolevShear
set_option autoImplicit false

private theorem jump_clamp_square (q : Velocity) (c : ℝ) (e : Edge) :
    jump (clampVelocity q c) e = ENNReal.ofReal
      ((unitClamp (c+logPrimitive q (e.2+e.1))-unitClamp (c+logPrimitive q e.2))^2) := by
  have he : logPrimitive (clampVelocity q c) (e.2+e.1)-logPrimitive (clampVelocity q c) e.2 =
      unitClamp (c+logPrimitive q (e.2+e.1))-unitClamp (c+logPrimitive q e.2) := by
    linarith [logPrimitive_clampVelocity q c (e.2+e.1), logPrimitive_clampVelocity q c e.2]
  simp only [jump, he]

private theorem jump_clampResidual_square (q : Velocity) (c : ℝ) (e : Edge) :
    jump (clampResidualVelocity q c) e = ENNReal.ofReal
      (((c+logPrimitive q (e.2+e.1)-unitClamp (c+logPrimitive q (e.2+e.1))) -
        (c+logPrimitive q e.2-unitClamp (c+logPrimitive q e.2)))^2) := by
  have he : logPrimitive (clampResidualVelocity q c) (e.2+e.1)-
      logPrimitive (clampResidualVelocity q c) e.2 =
      (c+logPrimitive q (e.2+e.1)-unitClamp (c+logPrimitive q (e.2+e.1))) -
        (c+logPrimitive q e.2-unitClamp (c+logPrimitive q e.2)) := by
    linarith [logPrimitive_clampResidualVelocity q c (e.2+e.1),
      logPrimitive_clampResidualVelocity q c e.2]
  simp only [jump, he]

theorem jump_clamp_firm (q : Velocity) (c : ℝ) (e : Edge) :
    jump (clampVelocity q c) e + jump (clampResidualVelocity q c) e ≤ jump q e := by
  rw [jump_clamp_square, jump_clampResidual_square,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have h := unitClamp_firm_sq (c+logPrimitive q e.2) (c+logPrimitive q (e.2+e.1))
  have he : (c+logPrimitive q (e.2+e.1))-(c+logPrimitive q e.2) =
      logPrimitive q (e.2+e.1)-logPrimitive q e.2 := by ring
  rw [he] at h
  exact h

theorem jumpEnergy_clamp_firm (D : EdgeMixture) (q : Velocity) (c : ℝ) :
    jumpEnergy D (clampVelocity q c) + jumpEnergy D (clampResidualVelocity q c) ≤
      jumpEnergy D q := by
  rw [jumpEnergy, jumpEnergy, jumpEnergy, ← lintegral_add_left (measurable_jump _)]
  exact lintegral_mono (jump_clamp_firm q c)

theorem jumpEnergy_clamp_le (D : EdgeMixture) (q : Velocity) (c : ℝ) :
    jumpEnergy D (clampVelocity q c) ≤ jumpEnergy D q :=
  (le_add_of_nonneg_right zero_le).trans (jumpEnergy_clamp_firm D q c)

theorem budget_clamp_split (q : Velocity) (c : ℝ) (e : Edge) :
    budget q e = budget (clampVelocity q c) e + budget (clampResidualVelocity q c) e := by
  have hab := Real.exp_le_exp.mpr (lower_le_upper e)
  have hn (v : Velocity) : 0 ≤ energy v (Real.exp (lower e)) (Real.exp (upper e)) :=
    intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _)
  rw [budget_eq_physical, budget_eq_physical, budget_eq_physical,
    energy_clamp_split q c, ENNReal.ofReal_add (hn _) (hn _), mul_add]

/-- The exact split allows infinite total congestion energies. -/
theorem congestionEnergy_clamp_split (D : EdgeMixture) (q : Velocity) (c : ℝ) :
    congestionEnergy D q =
      congestionEnergy D (clampVelocity q c) + congestionEnergy D (clampResidualVelocity q c) := by
  simp_rw [congestionEnergy_eq_budget, budget_clamp_split q c]
  exact lintegral_add_left (measurable_budget _) _

theorem sourceMass_clamp_firm (ψ : C_c(ℝ, ℝ)) (q : Velocity) (c : ℝ) :
    sourceMass ψ (clampVelocity q c) (unitClamp c) +
      sourceMass ψ (clampResidualVelocity q c) (c-unitClamp c) ≤ sourceMass ψ q c := by
  have hm : Measurable (fun y => ENNReal.ofReal
      (ψ y ^ 2 * (unitClamp c+logPrimitive (clampVelocity q c) y)^2)) := by
    have hc := continuous_logPrimitive (clampVelocity q c)
    have hp := ψ.continuous
    fun_prop
  unfold sourceMass
  rw [← lintegral_add_left hm]
  apply lintegral_mono
  intro y
  dsimp only
  rw [logPrimitive_clampVelocity, logPrimitive_clampResidualVelocity,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h := unitClamp_firm_sq 0 (c+logPrimitive q y)
  simp only [unitClamp_of_nonpos 0 le_rfl, sub_zero] at h
  simpa only [mul_add] using mul_le_mul_of_nonneg_left h (sq_nonneg (ψ y))

theorem compact_formEnergy_clamp_firm (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    (sourceMass ψ (clampVelocity q c) (unitClamp c) +
      jumpEnergy (compactMixture ψ weights) (clampVelocity q c)) +
      (sourceMass ψ (clampResidualVelocity q c) (c-unitClamp c) +
        jumpEnergy (compactMixture ψ weights) (clampResidualVelocity q c)) ≤
      sourceMass ψ q c + jumpEnergy (compactMixture ψ weights) q := by
  have h := add_le_add (sourceMass_clamp_firm ψ q c)
    (jumpEnergy_clamp_firm (compactMixture ψ weights) q c)
  convert h using 1 <;> ac_rfl

theorem compact_residualEnergy_le_clamp_loss (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    (jumpEnergy (compactMixture ψ weights) (clampResidualVelocity q c)).toReal ≤
      (jumpEnergy (compactMixture ψ weights) q).toReal -
        (jumpEnergy (compactMixture ψ weights) (clampVelocity q c)).toReal := by
  have h := ENNReal.toReal_mono (compact_jumpEnergy_ne_top ψ weights q)
    (jumpEnergy_clamp_firm (compactMixture ψ weights) q c)
  rw [ENNReal.toReal_add (compact_jumpEnergy_ne_top ψ weights (clampVelocity q c))
    (compact_jumpEnergy_ne_top ψ weights (clampResidualVelocity q c))] at h
  linarith

/-- Quantitative control of the sourcewise variation removed by clamping. -/
theorem compact_residualVariance_le_clamp_loss (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    weightedVariance ψ (logarithmicState (clampResidualVelocity q c) (c-unitClamp c)) ≤
      coercivityScale ψ * ((jumpEnergy (compactMixture ψ weights) q).toReal -
        (jumpEnergy (compactMixture ψ weights) (clampVelocity q c)).toReal) := by
  exact (compact_variance_le_jumpEnergy ψ weights (clampResidualVelocity q c) (c-unitClamp c)).trans
    (mul_le_mul_of_nonneg_left (compact_residualEnergy_le_clamp_loss ψ weights q c)
      (coercivityScale_pos ψ).le)

theorem compact_clamp_energy_eq_iff_residual_zero (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    jumpEnergy (compactMixture ψ weights) (clampVelocity q c) =
      jumpEnergy (compactMixture ψ weights) q ↔
      jumpEnergy (compactMixture ψ weights) (clampResidualVelocity q c) = 0 := by
  constructor
  · intro he
    have h := jumpEnergy_clamp_firm (compactMixture ψ weights) q c
    rw [← he] at h
    have hz : jumpEnergy (compactMixture ψ weights) (clampResidualVelocity q c) ≤ 0 :=
      (ENNReal.add_le_add_iff_left (compact_jumpEnergy_ne_top ψ weights (clampVelocity q c))).mp
        (by simpa only [add_zero] using h)
    exact le_antisymm hz zero_le
  · intro hr
    have hae := (lintegral_eq_zero_iff (measurable_jump (clampResidualVelocity q c))).mp hr
    apply lintegral_congr_ae
    filter_upwards [hae] with e he
    have hs : (logPrimitive (clampResidualVelocity q c) (e.2+e.1)-
        logPrimitive (clampResidualVelocity q c) e.2)^2 ≤ 0 := ENNReal.ofReal_eq_zero.mp he
    have hz := sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
    dsimp [logPrimitive, clampResidualVelocity] at hz
    rw [primitive_velocity_sub, primitive_velocity_sub] at hz
    have hd : logPrimitive q (e.2+e.1)-logPrimitive q e.2 =
        logPrimitive (clampVelocity q c) (e.2+e.1)-logPrimitive (clampVelocity q c) e.2 := by
      dsimp [logPrimitive]
      linarith
    simp only [jump, hd]

/-- Equality permits arbitrary constant states, including constants outside the band. -/
theorem compact_clamp_energy_eq_iff (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    jumpEnergy (compactMixture ψ weights) (clampVelocity q c) =
      jumpEnergy (compactMixture ψ weights) q ↔
      (∀ u v, ψ u ≠ 0 → ψ v ≠ 0 → logarithmicState q c u = logarithmicState q c v) ∨
      (∀ u, ψ u ≠ 0 → 0 ≤ logarithmicState q c u ∧ logarithmicState q c u ≤ 1) := by
  rw [compact_clamp_energy_eq_iff_residual_zero,
    compact_jumpEnergy_eq_zero_iff ψ weights (clampResidualVelocity q c) (c-unitClamp c)]
  have hstate (x : ℝ) : logarithmicState (clampResidualVelocity q c) (c-unitClamp c) x =
      logarithmicState q c x-unitClamp (logarithmicState q c x) :=
    logPrimitive_clampResidualVelocity q c x
  simp_rw [hstate]
  constructor
  · intro hr
    by_cases hc : ∀ u v, ψ u ≠ 0 → ψ v ≠ 0 → logarithmicState q c u = logarithmicState q c v
    · exact Or.inl hc
    · right
      intro u hu
      have hout : ¬(logarithmicState q c u < 0 ∨ 1 < logarithmicState q c u) := by
        intro ho
        apply hc
        intro v w hv hw
        exact (unitClamp_residual_injective_outside _ _ ho (hr u v hu hv)).symm.trans
          (unitClamp_residual_injective_outside _ _ ho (hr u w hu hw))
      exact ⟨le_of_not_gt (fun h => hout (Or.inl h)),
        le_of_not_gt (fun h => hout (Or.inr h))⟩
  · rintro (hc | hb) u v hu hv
    · rw [hc u v hu hv]
    · rw [unitClamp_eq_self _ (hb u hu).1 (hb u hu).2,
        unitClamp_eq_self _ (hb v hv).1 (hb v hv).2, sub_self, sub_self]

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion

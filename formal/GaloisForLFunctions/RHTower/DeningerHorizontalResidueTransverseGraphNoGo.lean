import GaloisForLFunctions.RHTower.DeningerTateGraphGreenPrimeSector

/-!
# Horizontal residue is invisible to transverse-only graph control

At a pro-log Stein residue chart, evaluating a horizontal character coordinate is an actual
component of the arithmetic Poincare residue.  Normalized one-sided Dirichlet packets have unit
horizontal `L²` mass and aligned evaluation `sqrt N`.  Tensoring them with one fixed transverse
Tate mode leaves every transverse graph-power mass constant.  Therefore no finite family of
transverse graph-power seminorms can bound horizontal residue evaluation.

The theorem is a topology obstruction, not an objection to the existing holomorphic pro-Stein
topology: compact-open/Cauchy seminorms do control evaluation.  It proves that such horizontal
control cannot be discarded when the Tate graph scale is introduced.
-/

namespace RHTower

open Filter

/-- Common coefficient of the normalized one-sided horizontal Dirichlet packet. -/
noncomputable def deningerHorizontalDirichletCoefficient (N : ℕ) : ℝ :=
  (Real.sqrt N)⁻¹

/-- Squared `L²` mass of the normalized horizontal Dirichlet packet. -/
noncomputable def deningerHorizontalDirichletMass (N : ℕ) : ℝ :=
  ∑ _k ∈ Finset.range N, deningerHorizontalDirichletCoefficient N ^ 2

/-- Value of the normalized horizontal Dirichlet packet at its aligned character. -/
noncomputable def deningerHorizontalDirichletEvaluation (N : ℕ) : ℝ :=
  ∑ _k ∈ Finset.range N, deningerHorizontalDirichletCoefficient N

/-- Applying a fixed transverse generator power only rescales horizontal `L²` mass. -/
noncomputable def deningerHorizontalTransversePowerMass
    (lam : ℝ) (m N : ℕ) : ℝ :=
  |lam| ^ (2 * m) * deningerHorizontalDirichletMass N

/-- Nonempty normalized horizontal Dirichlet packets have unit `L²` mass. -/
theorem deningerHorizontalDirichletMass_eq_one {N : ℕ} (hN : 0 < N) :
    deningerHorizontalDirichletMass N = 1 := by
  rw [deningerHorizontalDirichletMass]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [deningerHorizontalDirichletCoefficient, inv_pow]
  nth_rewrite 1 [← Real.sq_sqrt (Nat.cast_nonneg N)]
  exact mul_inv_cancel₀
    (pow_ne_zero 2 (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)))

/-- Evaluation at the aligned character has exact size `sqrt N`. -/
theorem deningerHorizontalDirichletEvaluation_eq_sqrt (N : ℕ) :
    deningerHorizontalDirichletEvaluation N = Real.sqrt N := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [deningerHorizontalDirichletEvaluation]
  · rw [deningerHorizontalDirichletEvaluation]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [deningerHorizontalDirichletCoefficient]
    nth_rewrite 1 [← Real.sq_sqrt (Nat.cast_nonneg N)]
    rw [pow_two, mul_assoc,
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)),
      mul_one]

/-- Every fixed transverse graph-power mass is independent of horizontal aperture. -/
theorem deningerHorizontalTransversePowerMass_eq
    (lam : ℝ) (m : ℕ) {N : ℕ} (hN : 0 < N) :
    deningerHorizontalTransversePowerMass lam m N = |lam| ^ (2 * m) := by
  rw [deningerHorizontalTransversePowerMass,
    deningerHorizontalDirichletMass_eq_one hN, mul_one]

/-- Aligned horizontal character evaluation is unbounded. -/
theorem deningerHorizontalDirichletEvaluation_tendsto_atTop :
    Tendsto deningerHorizontalDirichletEvaluation atTop atTop := by
  refine (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).congr' ?_
  exact Filter.Eventually.of_forall fun N =>
    (deningerHorizontalDirichletEvaluation_eq_sqrt N).symm

/-- No constant bounds aligned evaluation by normalized horizontal `L²` mass. -/
theorem deningerHorizontalDirichletEvaluation_unbounded
    (C : ℝ) :
    ∃ N : ℕ, 0 < N ∧
      C < deningerHorizontalDirichletEvaluation N ∧
      deningerHorizontalDirichletMass N = 1 := by
  have hlarge :
      ∀ᶠ N : ℕ in atTop, C < deningerHorizontalDirichletEvaluation N :=
    deningerHorizontalDirichletEvaluation_tendsto_atTop.eventually
      (eventually_gt_atTop C)
  have hpositive : ∀ᶠ N : ℕ in atTop, 0 < N :=
    Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩
  obtain ⟨N, hlargeN, hN⟩ := (hlarge.and hpositive).exists
  exact ⟨N, hN, hlargeN, deningerHorizontalDirichletMass_eq_one hN⟩

/-- Even one fixed transverse graph-power seminorm cannot bound horizontal evaluation. -/
theorem deningerHorizontalEvaluation_not_bounded_by_transversePower
    (lam : ℝ) (m : ℕ) (C : ℝ) :
    ∃ N : ℕ, 0 < N ∧
      C * deningerHorizontalTransversePowerMass lam m N <
        deningerHorizontalDirichletEvaluation N := by
  obtain ⟨N, hN, hlarge, _⟩ :=
    deningerHorizontalDirichletEvaluation_unbounded
      (C * |lam| ^ (2 * m))
  refine ⟨N, hN, ?_⟩
  rw [deningerHorizontalTransversePowerMass_eq lam m hN]
  exact hlarge

/-- No finite family of transverse graph-power masses controls horizontal evaluation. -/
theorem deningerHorizontalEvaluation_not_bounded_by_finiteTransverseProfile
    (lam C : ℝ) (orders : Finset ℕ) :
    ∃ N : ℕ, 0 < N ∧
      C * (∑ m ∈ orders,
        deningerHorizontalTransversePowerMass lam m N) <
          deningerHorizontalDirichletEvaluation N ∧
      ∀ m ∈ orders,
        deningerHorizontalTransversePowerMass lam m N =
          |lam| ^ (2 * m) := by
  obtain ⟨N, hN, hlarge, _⟩ :=
    deningerHorizontalDirichletEvaluation_unbounded
      (C * ∑ m ∈ orders, |lam| ^ (2 * m))
  refine ⟨N, hN, ?_, ?_⟩
  · rw [Finset.sum_congr rfl fun m hm =>
      deningerHorizontalTransversePowerMass_eq lam m hN]
    exact hlarge
  · intro m hm
    exact deningerHorizontalTransversePowerMass_eq lam m hN

/-- Squared evaluation-to-Sobolev ratio of the rank-`d` two-mode tensor cube. -/
noncomputable def deningerRankCubeSobolevEvaluationRatioSq
    (s d : ℕ) : ℝ :=
  (2 : ℝ) ^ d / (d + 1 : ℝ) ^ s

/-- In unbounded horizontal rank, every fixed Sobolev order loses point evaluation. -/
theorem deningerRankCubeSobolevEvaluationRatioSq_tendsto_atTop
    (s : ℕ) :
    Tendsto (deningerRankCubeSobolevEvaluationRatioSq s) atTop atTop := by
  let small : ℕ → ℝ := fun d => (d + 1 : ℝ) ^ s / (2 : ℝ) ^ d
  have hbase :
      Tendsto (fun n : ℕ => (n : ℝ) ^ s / (2 : ℝ) ^ n)
        atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt s one_lt_two
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto small atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun d : ℕ => (2 : ℝ) * ((d + 1 : ℝ) ^ s / (2 : ℝ) ^ (d + 1)))
          atTop (nhds 0) := by
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero] using
        hshift.const_mul (2 : ℝ)
    refine hmul.congr' (Filter.Eventually.of_forall fun d => ?_)
    dsimp [small]
    rw [pow_succ']
    field_simp
  have hpositive : ∀ᶠ d : ℕ in atTop, 0 < small d :=
    Filter.Eventually.of_forall fun d => div_pos (pow_pos (by positivity) _)
      (pow_pos (by positivity) _)
  have hsmallGT : Tendsto small atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsmall, hpositive⟩
  refine hsmallGT.inv_tendsto_nhdsGT_zero.congr' ?_
  exact Filter.Eventually.of_forall fun d => by
    rw [deningerRankCubeSobolevEvaluationRatioSq]
    dsimp [small]
    rw [inv_div]

end RHTower

import GaloisForLFunctions.HTGeometry.ExponentialWallBurnolPartner
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# The exponential wall operator is a trace-one strict contraction

For the wall operator `A = V*V` on `L²(e^{-x} dx)` and its Burnol partner `B = VV*`:

* `A` and `B` are positive and Schatten-one, `tr A = tr B = ‖V‖²_HS = 1`, they share nonzero
  eigenvalues with multiplicities, and `det(1 - zA) = det(1 - zB)` for every `z`;
* `tr(A²) = ‖A‖²_HS = ∬ κ² dμ dμ = 16/35`, so `‖A‖ = ‖B‖ ≤ 4/√35 < 1`;
* `1 - A` and `1 - B` are invertible with norm-convergent Neumann series;
* `det(1 - zA) = det(1 - zB) ≠ 0` for `|z| < √35/4`;
* the second Fredholm coefficient is `e₂(A) = ((tr A)² - tr(A²))/2 = 19/70`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance isProbabilityMeasure_expMeasure_one_wall : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

local instance factTwoNeTopWall : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

theorem hsInner_self_eq_ofReal {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (T : E →L[ℂ] F) :
    hsInner T T = (hsNormSq T : ℂ) := by
  rw [hsInner, hsNormSq, Complex.ofReal_tsum]
  exact tsum_congr fun i => by rw [inner_self_eq_norm_sq_to_K]; norm_cast

/-! ## Theorem A -/

/-- `‖V‖²_HS = 1`. -/
theorem hsNormSq_burnolSynthesis : hsNormSq burnolSynthesis = 1 := by
  rw [burnolSynthesis, burnolKernel.hsNormSq_op, burnolKernel_energy, ENNReal.toReal_one]

theorem opTrace_adjoint_comp_burnolSynthesis :
    opTrace (adjoint burnolSynthesis ∘L burnolSynthesis) = 1 := by
  rw [opTrace_adjoint_comp_self, hsInner_self_eq_ofReal, hsNormSq_burnolSynthesis,
    Complex.ofReal_one]

/-- **(EWHC.2).**  `A ≥ 0`. -/
theorem isPositive_wallOperator : wallOperator.IsPositive := by
  rw [wallOperator_eq_adjoint_comp]
  exact isPositive_adjoint_comp_self _

/-- **(EWHC.2).**  `A = A*`. -/
theorem isSelfAdjoint_wallOperator : IsSelfAdjoint wallOperator :=
  isPositive_wallOperator.isSelfAdjoint

theorem adjoint_wallOperator : adjoint wallOperator = wallOperator :=
  isSelfAdjoint_wallOperator

/-- **(EWHC.2).**  `A` is Schatten-one. -/
theorem memSchattenClass_one_wallOperator : RHTower.MemSchattenClass 1 wallOperator := by
  rw [wallOperator_eq_adjoint_comp]
  exact RHTower.memSchattenClass_one_comp isHilbertSchmidt_burnolSynthesis.adjoint
    isHilbertSchmidt_burnolSynthesis

theorem isHilbertSchmidt_wallOperator : IsHilbertSchmidt wallOperator :=
  wallKernel.isHilbertSchmidt_op

/-- **(EWHC.2).**  `tr A = 1`. -/
theorem opTrace_wallOperator : opTrace wallOperator = 1 := by
  rw [wallOperator_eq_adjoint_comp, opTrace_adjoint_comp_burnolSynthesis]

/-- `B ≥ 0`. -/
theorem isPositive_partnerOperator : partnerOperator.IsPositive := by
  have h := isPositive_adjoint_comp_self (adjoint burnolSynthesis)
  rwa [adjoint_adjoint] at h

/-- `B` is Schatten-one. -/
theorem memSchattenClass_one_partnerOperator : RHTower.MemSchattenClass 1 partnerOperator :=
  RHTower.memSchattenClass_one_comp isHilbertSchmidt_burnolSynthesis
    isHilbertSchmidt_burnolSynthesis.adjoint

theorem isHilbertSchmidt_partnerOperator : IsHilbertSchmidt partnerOperator :=
  isHilbertSchmidt_burnolSynthesis.adjoint.comp_left _

/-- `tr B = 1`. -/
theorem opTrace_partnerOperator : opTrace partnerOperator = 1 := by
  rw [partnerOperator, opTrace_comp_comm isHilbertSchmidt_burnolSynthesis
    isHilbertSchmidt_burnolSynthesis.adjoint, opTrace_adjoint_comp_burnolSynthesis]

/-- **Theorem A.**  `A` and `B` have the same nonzero eigenvalues with the same multiplicities. -/
theorem finrank_eigenspace_wallOperator_eq {c : ℂ} (hc : c ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace
        ((wallOperator : Lp ℂ 2 (expMeasure 1) →L[ℂ] Lp ℂ 2 (expMeasure 1)) :
          Lp ℂ 2 (expMeasure 1) →ₗ[ℂ] Lp ℂ 2 (expMeasure 1)) c)
      = Module.finrank ℂ (Module.End.eigenspace
        ((partnerOperator : Lp ℂ 2 halfLineMeasure →L[ℂ] Lp ℂ 2 halfLineMeasure) :
          Lp ℂ 2 halfLineMeasure →ₗ[ℂ] Lp ℂ 2 halfLineMeasure) c) := by
  rw [wallOperator_eq_adjoint_comp, partnerOperator]
  exact finrank_eigenspace_adjoint_comp_self_eq burnolSynthesis hc

/-- **Theorem A.**  The ordinary Fredholm determinants agree: `det(1 - zA) = det(1 - zB)`. -/
theorem detOneSub_wallOperator_eq {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (expMeasure 1)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 halfLineMeasure)) :
    detOneSub b₁ wallOperator = detOneSub b₂ partnerOperator := by
  rw [wallOperator_eq_adjoint_comp, partnerOperator]
  exact detOneSub_adjoint_comp_self_eq b₁ b₂ isHilbertSchmidt_burnolSynthesis

/-! ## Theorem B -/

/-- **(EWHC.6).**  `‖A‖²_HS = ∬ κ² dμ dμ = 16/35`. -/
theorem hsNormSq_wallOperator : hsNormSq wallOperator = 16 / 35 := by
  rw [wallOperator, wallKernel.hsNormSq_op, wallKernel_energy, ENNReal.toReal_ofReal (by norm_num)]

/-- **(EWHC.6).**  `tr(A²) = ‖A‖²_HS = 16/35`. -/
theorem opTrace_wallOperator_sq : opTrace (wallOperator ^ 2) = 16 / 35 := by
  rw [_root_.HTGeometry.opTrace_sq_eq_ofReal_hsNormSq isHilbertSchmidt_wallOperator
    adjoint_wallOperator, hsNormSq_wallOperator]
  push_cast
  ring

theorem norm_wallOperator_le : ‖wallOperator‖ ≤ 4 / Real.sqrt 35 := by
  refine (opNorm_le_hsNorm isHilbertSchmidt_wallOperator).trans (le_of_eq ?_)
  rw [hsNorm, hsNormSq_wallOperator, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 35),
    show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `‖B‖ = ‖A‖`. -/
theorem norm_partnerOperator : ‖partnerOperator‖ = ‖wallOperator‖ := by
  rw [wallOperator_eq_adjoint_comp, norm_adjoint_comp_self, partnerOperator]
  have h := norm_adjoint_comp_self (adjoint burnolSynthesis)
  rw [adjoint_adjoint] at h
  rw [h, LinearIsometryEquiv.norm_map]

theorem four_div_sqrt_thirtyFive_lt_one : 4 / Real.sqrt 35 < 1 := by
  rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num))]
  rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **(EWHC.7).**  `‖A‖ = ‖B‖ ≤ 4/√35 < 1`. -/
theorem norm_wallOperator_lt_one : ‖wallOperator‖ < 1 :=
  norm_wallOperator_le.trans_lt four_div_sqrt_thirtyFive_lt_one

theorem norm_partnerOperator_lt_one : ‖partnerOperator‖ < 1 := by
  rw [norm_partnerOperator]
  exact norm_wallOperator_lt_one

/-- **Theorem B.**  `1 - A` is invertible with the norm-convergent Neumann series `∑ Aⁿ`. -/
theorem wallOperator_neumann :
    IsUnit (1 - wallOperator) ∧ HasSum (fun n => wallOperator ^ n) (∑' n, wallOperator ^ n) ∧
      (1 - wallOperator) * (∑' n, wallOperator ^ n) = 1 ∧
      (∑' n, wallOperator ^ n) * (1 - wallOperator) = 1 :=
  ⟨(Units.oneSub wallOperator norm_wallOperator_lt_one).isUnit,
    (summable_geometric_of_norm_lt_one norm_wallOperator_lt_one).hasSum,
    mul_neg_geom_series _ norm_wallOperator_lt_one, geom_series_mul_neg _ norm_wallOperator_lt_one⟩

/-- **Theorem B.**  `1 - B` is invertible with the norm-convergent Neumann series `∑ Bⁿ`. -/
theorem partnerOperator_neumann :
    IsUnit (1 - partnerOperator) ∧
      HasSum (fun n => partnerOperator ^ n) (∑' n, partnerOperator ^ n) ∧
      (1 - partnerOperator) * (∑' n, partnerOperator ^ n) = 1 ∧
      (∑' n, partnerOperator ^ n) * (1 - partnerOperator) = 1 :=
  ⟨(Units.oneSub partnerOperator norm_partnerOperator_lt_one).isUnit,
    (summable_geometric_of_norm_lt_one norm_partnerOperator_lt_one).hasSum,
    mul_neg_geom_series _ norm_partnerOperator_lt_one,
    geom_series_mul_neg _ norm_partnerOperator_lt_one⟩

theorem norm_mul_norm_wallOperator_lt_one {z : ℂ} (hz : ‖z‖ < Real.sqrt 35 / 4) :
    ‖z‖ * ‖wallOperator‖ < 1 := by
  have hs : 0 < Real.sqrt 35 := Real.sqrt_pos.mpr (by norm_num)
  calc ‖z‖ * ‖wallOperator‖ ≤ ‖z‖ * (4 / Real.sqrt 35) :=
        mul_le_mul_of_nonneg_left norm_wallOperator_le (norm_nonneg _)
    _ < Real.sqrt 35 / 4 * (4 / Real.sqrt 35) :=
        mul_lt_mul_of_pos_right hz (by positivity)
    _ = 1 := by field_simp

/-- **(EWHC.8).**  `det(1 - zA) = det(1 - zB) ≠ 0` for `|z| < √35/4`. -/
theorem detOneSub_wallOperator_ne_zero {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (expMeasure 1)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 halfLineMeasure))
    {z : ℂ} (hz : ‖z‖ < Real.sqrt 35 / 4) :
    detOneSub b₁ wallOperator z = detOneSub b₂ partnerOperator z ∧
      detOneSub b₁ wallOperator z ≠ 0 :=
  ⟨congrFun (detOneSub_wallOperator_eq b₁ b₂) z,
    detOneSub_ne_zero b₁ isHilbertSchmidt_wallOperator (norm_mul_norm_wallOperator_lt_one hz)⟩

/-- **(EWHC.9).**  The second Fredholm coefficient of `A` is
`e₂(A) = ((tr A)² - tr(A²))/2 = 19/70`. -/
theorem taylorCoeff_detOneSub_wallOperator_two {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (expMeasure 1))) :
    taylorCoeff (detOneSub b wallOperator) 2
      = (opTrace wallOperator ^ 2 - opTrace (wallOperator ^ 2)) / 2 ∧
      taylorCoeff (detOneSub b wallOperator) 2 = 19 / 70 := by
  have h := taylorCoeff_detOneSub_two b isHilbertSchmidt_wallOperator
  refine ⟨h, ?_⟩
  rw [h, opTrace_wallOperator, opTrace_wallOperator_sq]
  norm_num

end GaloisForLFunctions.HTGeometry

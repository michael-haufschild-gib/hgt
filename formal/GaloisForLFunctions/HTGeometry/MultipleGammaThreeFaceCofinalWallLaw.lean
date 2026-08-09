import GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionLawstack
import GaloisForLFunctions.HTGeometry.PeriodIncidenceUniformEffectivity
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Multiple-Gamma three-face cofinal-wall law

This module specializes the all-parameter multiple elliptic Gamma dichotomy, the marked-period
action law, and the period-incidence multiplier to the explicit family
`(i, 2i + pi/m)` and its cofinal boundary `(i, 2i)`.  It proves the simultaneous differential,
integral-relation, and closed-range transition, together with finite-coordinate blindness,
surviving product reflection, and the identity-weight constitutive countermodel.
-/

open Set
open scoped ENNReal

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

/-! ## Differential face -/

/-- Every finite packet has a rank-three minor. -/
theorem finiteMultipleGammaFunctionPeriods_hasRankThreeMinor (m : ℕ+) :
    MultipleEllipticGammaHasRankThreeMinor (finiteMultipleGammaFunctionPeriods m) := by
  refine ⟨0, 1, by decide, ?_⟩
  exact linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
    (finiteMultipleGammaFunctionPeriods m)
    (finiteMultipleGammaFunctionPeriods_integrallyIndependent m) (by decide)

/-- Every finite raw two-period multiple elliptic Gamma is hypertranscendental. -/
theorem finiteMultipleGammaMero_hypertranscendental (m : ℕ+) :
    HypertranscendentalOver (RatFunc ℂ)
      (multipleEllipticGammaMero (finiteMultipleGammaFunctionPeriods m)
        (finiteMultipleGammaFunctionPeriods_im_pos m)) :=
  (hypertranscendentalOver_multipleEllipticGammaMero_iff_rankThreeMinor
    (finiteMultipleGammaFunctionPeriods m)
    (finiteMultipleGammaFunctionPeriods_im_pos m)).2
      (finiteMultipleGammaFunctionPeriods_hasRankThreeMinor m)

/-- Every finite logarithmic derivative is hypertranscendental. -/
theorem finiteMultipleGammaLogDerivMero_hypertranscendental (m : ℕ+) :
    HypertranscendentalOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivMero (finiteMultipleGammaFunctionPeriods m)
        (finiteMultipleGammaFunctionPeriods_im_pos m)) :=
  (hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_rankThreeMinor
    (finiteMultipleGammaFunctionPeriods m)
    (finiteMultipleGammaFunctionPeriods_im_pos m)).2
      (finiteMultipleGammaFunctionPeriods_hasRankThreeMinor m)

/-- Boundary raw multiple elliptic Gamma is differentially algebraic. -/
theorem boundaryMultipleGammaMero_differentialAlgebraic :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaMero boundaryMultipleGammaFunctionPeriods
        boundaryMultipleGammaFunctionPeriods_im_pos) :=
  (differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor
    boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos).2
      boundaryMultipleGammaFunctionPeriods_no_rankThreeMinor

/-- Boundary logarithmic derivative is differentially algebraic. -/
theorem boundaryMultipleGammaLogDerivMero_differentialAlgebraic :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivMero boundaryMultipleGammaFunctionPeriods
        boundaryMultipleGammaFunctionPeriods_im_pos) :=
  (differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor
    boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos).2
      boundaryMultipleGammaFunctionPeriods_no_rankThreeMinor

/-- Exact finite differential-depth/marked-excess value. -/
theorem finiteMultipleGammaDepth_excess_calibration (m : ℕ+) :
    multipleEllipticGammaTransverseDADepth
          (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) = 1 ∧
      markedPeriodExcess (finiteMultipleGammaPeriodMap m) = 1 :=
  ⟨finiteMultipleGammaTransverseDADepth m,
    finiteMultipleGammaMarkedPeriodExcess_eq_one m⟩

/-- Exact boundary differential-depth/marked-excess value. -/
theorem boundaryMultipleGammaDepth_excess_calibration :
    multipleEllipticGammaTransverseDADepth
          boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos = 0 ∧
      markedPeriodExcess boundaryMultipleGammaPeriodMap = 0 :=
  ⟨boundaryMultipleGammaTransverseDADepth,
    boundaryMultipleGammaMarkedPeriodExcess_eq_zero⟩

/-! ## Integral clock and multiplicative-nome face -/

/-- The second boundary analytic period is twice the first. -/
theorem boundaryMultipleGammaFunctionPeriods_one_eq_two_mul_zero :
    boundaryMultipleGammaFunctionPeriods 1 =
      2 * boundaryMultipleGammaFunctionPeriods 0 := by
  simp [boundaryMultipleGammaFunctionPeriods]

/-- Standard multiplicative nome attached to an additive period. -/
def multipleGammaMultiplicativeNome (τ : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ)

/-- At the boundary the second nome is the square of the first. -/
theorem boundaryMultipleGammaMultiplicativeNome_one_eq_sq_zero :
    multipleGammaMultiplicativeNome (boundaryMultipleGammaFunctionPeriods 1) =
      multipleGammaMultiplicativeNome (boundaryMultipleGammaFunctionPeriods 0) ^ 2 := by
  rw [multipleGammaMultiplicativeNome, multipleGammaMultiplicativeNome,
    ← Complex.exp_nat_mul]
  congr 1
  simp [boundaryMultipleGammaFunctionPeriods]
  ring

/-- No finite packet has the boundary multiplicative-nome relation. -/
theorem finiteMultipleGammaMultiplicativeNome_one_ne_sq_zero (m : ℕ+) :
    multipleGammaMultiplicativeNome (finiteMultipleGammaFunctionPeriods m 1) ≠
      multipleGammaMultiplicativeNome (finiteMultipleGammaFunctionPeriods m 0) ^ 2 := by
  intro hnome
  rw [multipleGammaMultiplicativeNome, multipleGammaMultiplicativeNome,
    ← Complex.exp_nat_mul] at hnome
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hnome
  let A : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hA : A ≠ 0 := by
    dsimp [A]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hscaled : A *
      (finiteMultipleGammaFunctionPeriods m 1 -
        2 * finiteMultipleGammaFunctionPeriods m 0 - (n : ℂ)) = 0 := by
    dsimp [A] at hn ⊢
    linear_combination hn
  have hperiod : finiteMultipleGammaFunctionPeriods m 1 -
      2 * finiteMultipleGammaFunctionPeriods m 0 - (n : ℂ) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hA
  let r : MultipleGammaPeriodSource := ![-n, -2, 1]
  have hrker : r ∈ (finiteMultipleGammaPeriodMap m).ker := by
    rw [AddMonoidHom.mem_ker, finiteMultipleGammaPeriodMap_apply]
    dsimp [r]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_mul]
    simp [finiteMultipleGammaFunctionPeriods] at hperiod ⊢
    linear_combination hperiod
  rw [finiteMultipleGammaPeriodMap_ker] at hrker
  have hrzero : r = 0 := by simpa using hrker
  have := congrFun hrzero 2
  simp [r] at this

/-! ## Incidence face -/

/-- Integral-module presentation of the finite augmented period group. -/
abbrev finiteMultipleGammaIncidenceLattice (m : ℕ+) : Submodule ℤ ℂ :=
  (finiteMultipleGammaPeriodSubgroup m).toIntSubmodule

/-- Integral-module presentation of the boundary augmented period group. -/
abbrev boundaryMultipleGammaIncidenceLattice : Submodule ℤ ℂ :=
  boundaryMultipleGammaPeriodSubgroup.toIntSubmodule

/-- Every finite incidence lattice is nondiscrete. -/
theorem finiteMultipleGammaIncidenceLattice_not_discrete (m : ℕ+) :
    ¬ DiscreteTopology (finiteMultipleGammaIncidenceLattice m) := by
  intro hdiscrete
  letI : DiscreteTopology (finiteMultipleGammaIncidenceLattice m) := hdiscrete
  apply finiteMultipleGammaPeriodSubgroup_not_isClosed m
  simpa [finiteMultipleGammaIncidenceLattice] using
    (finiteMultipleGammaIncidenceLattice m).toAddSubgroup.isClosed_of_discrete

/-- The boundary incidence lattice is discrete. -/
theorem boundaryMultipleGammaIncidenceLattice_discrete :
    DiscreteTopology boundaryMultipleGammaIncidenceLattice := by
  let f : MultipleGammaPeriodSource → boundaryMultipleGammaIncidenceLattice :=
    fun n ↦ ⟨boundaryMultipleGammaPeriodMap n, ⟨n, rfl⟩⟩
  letI : Countable boundaryMultipleGammaIncidenceLattice :=
    Function.Surjective.countable (f := f) (by
      rintro ⟨z, n, rfl⟩
      exact ⟨n, rfl⟩)
  apply discrete_of_countable_isClosed_intSubmodule
  simpa [boundaryMultipleGammaIncidenceLattice] using
    boundaryMultipleGammaPeriodSubgroup_isClosed

/-- Every finite canonical incidence operator is injective. -/
theorem finiteMultipleGammaPeriodIncidence_injective (m : ℕ+) :
    Function.Injective (periodIncidenceMultiplier (finiteMultipleGammaIncidenceLattice m)) :=
  periodIncidenceMultiplier_injective _

/-- Every finite canonical incidence operator has nonclosed range. -/
theorem finiteMultipleGammaPeriodIncidence_not_isClosed_range (m : ℕ+) :
    ¬ IsClosed (Set.range
      (periodIncidenceMultiplier (finiteMultipleGammaIncidenceLattice m))) :=
  periodIncidenceMultiplier_not_isClosed_range_of_not_discrete _
    (finiteMultipleGammaIncidenceLattice_not_discrete m)

/-- Every finite canonical incidence operator is nonsurjective. -/
theorem finiteMultipleGammaPeriodIncidence_not_surjective (m : ℕ+) :
    ¬ Function.Surjective
      (periodIncidenceMultiplier (finiteMultipleGammaIncidenceLattice m)) := by
  rw [periodIncidenceMultiplier_surjective_iff_discrete]
  exact finiteMultipleGammaIncidenceLattice_not_discrete m

/-- A uniform nonzero-period gap upgrades the canonical multiplier to a bounded linear
equivalence with its explicit diagonal inverse. -/
noncomputable def periodIncidenceContinuousLinearEquivOfGap
    (L : Submodule ℤ ℂ) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ q : NonzeroPeriod L, ε ≤ ‖(q.1.1 : ℂ)‖) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ ≃L[ℂ]
      lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ where
  toFun := periodIncidenceMultiplier L
  invFun := periodIncidenceInverse L ε hε hgap
  left_inv x := by
    apply lp.ext
    funext q
    rw [periodIncidenceInverse_apply, periodIncidenceMultiplier_apply,
      ← mul_assoc, inv_mul_cancel₀ (regularizedPeriodWeight_ne_zero q.2), one_mul]
  right_inv x := by
    apply lp.ext
    funext q
    rw [periodIncidenceMultiplier_apply, periodIncidenceInverse_apply,
      ← mul_assoc, mul_inv_cancel₀ (regularizedPeriodWeight_ne_zero q.2), one_mul]
  map_add' x y := map_add (periodIncidenceMultiplier L) x y
  map_smul' c x := map_smul (periodIncidenceMultiplier L) c x
  continuous_toFun := (periodIncidenceMultiplier L).continuous
  continuous_invFun := (periodIncidenceInverse L ε hε hgap).continuous

/-- Boundary incidence is boundedly invertible. -/
noncomputable def boundaryMultipleGammaPeriodIncidenceEquiv :
    lp (fun _ : NonzeroPeriod boundaryMultipleGammaIncidenceLattice ↦ ℂ) ∞ ≃L[ℂ]
      lp (fun _ : NonzeroPeriod boundaryMultipleGammaIncidenceLattice ↦ ℂ) ∞ := by
  letI : DiscreteTopology boundaryMultipleGammaIncidenceLattice :=
    boundaryMultipleGammaIncidenceLattice_discrete
  let hex := exists_period_norm_gap_of_discrete boundaryMultipleGammaIncidenceLattice
  let ε := Classical.choose hex
  let hε := (Classical.choose_spec hex).1
  let hgap := (Classical.choose_spec hex).2
  exact periodIncidenceContinuousLinearEquivOfGap
    boundaryMultipleGammaIncidenceLattice ε hε hgap

/-- Boundary canonical incidence is surjective. -/
theorem boundaryMultipleGammaPeriodIncidence_surjective :
    Function.Surjective
      (periodIncidenceMultiplier boundaryMultipleGammaIncidenceLattice) := by
  rw [periodIncidenceMultiplier_surjective_iff_discrete]
  exact boundaryMultipleGammaIncidenceLattice_discrete

/-- Boundary canonical incidence has closed range. -/
theorem boundaryMultipleGammaPeriodIncidence_isClosed_range :
    IsClosed (Set.range
      (periodIncidenceMultiplier boundaryMultipleGammaIncidenceLattice)) := by
  rw [periodIncidenceMultiplier_isClosed_range_iff_discrete]
  exact boundaryMultipleGammaIncidenceLattice_discrete

/-- Every finite nonzero-coordinate restriction is bijective, for any period lattice. -/
theorem periodIncidenceFiniteRestriction_bijective
    (L : Submodule ℤ ℂ) {n : ℕ} (q : Fin n → NonzeroPeriod L) :
    Function.Bijective (fun x : Fin n → ℂ ↦ fun i ↦
      regularizedPeriodWeight (q i).1.1 * x i) :=
  finiteNonzeroDiagonal_bijective _
    (fun i ↦ regularizedPeriodWeight_ne_zero (q i).2)

/-! ## Reflection and constitutive underdetermination -/

/-- Identity-weight incidence operator on the same nonzero-period coordinate space. -/
def identityPeriodIncidenceMultiplier (L : Submodule ℤ ℂ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ →L[ℂ]
      lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ContinuousLinearMap.id ℂ _

/-- Identity weight is boundedly invertible for every period lattice. -/
def identityPeriodIncidenceEquiv (L : Submodule ℤ ℂ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ ≃L[ℂ]
      lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ContinuousLinearEquiv.refl ℂ _

/-- On every finite packet, canonical and identity weights act on the identical period space but
have opposite global admission behavior. -/
theorem finiteMultipleGammaConstitutiveCountermodel (m : ℕ+) :
    (¬ Function.Surjective
      (periodIncidenceMultiplier (finiteMultipleGammaIncidenceLattice m))) ∧
    Function.Surjective
      (identityPeriodIncidenceMultiplier (finiteMultipleGammaIncidenceLattice m)) ∧
    (finiteMultipleGammaPeriodMap m).ker = ⊥ ∧
    markedPeriodExcess (finiteMultipleGammaPeriodMap m) = 1 ∧
    (∀ z : ℂ,
      multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m)
          (finiteMultipleGammaAnalyticReflectionCenter m - z) =
        (multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) z)⁻¹) := by
  refine ⟨finiteMultipleGammaPeriodIncidence_not_surjective m, ?_,
    finiteMultipleGammaPeriodMap_ker m,
    finiteMultipleGammaMarkedPeriodExcess_eq_one m,
    finiteMultipleGammaProduct_reflection m⟩
  intro x
  exact ⟨x, rfl⟩

/-- Full explicit three-face wall ledger, including the invariants that survive the wall. -/
theorem multipleGammaThreeFaceCofinalWallCalibration (m : ℕ+) :
    HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaMero (finiteMultipleGammaFunctionPeriods m)
          (finiteMultipleGammaFunctionPeriods_im_pos m)) ∧
    HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero (finiteMultipleGammaFunctionPeriods m)
          (finiteMultipleGammaFunctionPeriods_im_pos m)) ∧
    DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaMero boundaryMultipleGammaFunctionPeriods
          boundaryMultipleGammaFunctionPeriods_im_pos) ∧
    DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero boundaryMultipleGammaFunctionPeriods
          boundaryMultipleGammaFunctionPeriods_im_pos) ∧
    (finiteMultipleGammaPeriodMap m).ker = ⊥ ∧
    boundaryMultipleGammaPeriodMap.ker =
      AddSubgroup.zmultiples boundaryMultipleGammaRelation ∧
    (¬ DiscreteTopology (finiteMultipleGammaIncidenceLattice m)) ∧
    DiscreteTopology boundaryMultipleGammaIncidenceLattice ∧
    (¬ IsClosed (Set.range
      (periodIncidenceMultiplier (finiteMultipleGammaIncidenceLattice m))) ∧
      IsClosed (Set.range
        (periodIncidenceMultiplier boundaryMultipleGammaIncidenceLattice))) ∧
    (∀ z : ℂ,
      multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m)
          (finiteMultipleGammaAnalyticReflectionCenter m - z) =
        (multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) z)⁻¹) ∧
    (∀ z : ℂ,
      multipleEllipticGammaProduct boundaryMultipleGammaFunctionPeriods
          (boundaryMultipleGammaAnalyticReflectionCenter - z) =
        (multipleEllipticGammaProduct boundaryMultipleGammaFunctionPeriods z)⁻¹) := by
  exact ⟨finiteMultipleGammaMero_hypertranscendental m,
    finiteMultipleGammaLogDerivMero_hypertranscendental m,
    boundaryMultipleGammaMero_differentialAlgebraic,
    boundaryMultipleGammaLogDerivMero_differentialAlgebraic,
    finiteMultipleGammaPeriodMap_ker m,
    boundaryMultipleGammaPeriodMap_ker,
    finiteMultipleGammaIncidenceLattice_not_discrete m,
    boundaryMultipleGammaIncidenceLattice_discrete,
    ⟨finiteMultipleGammaPeriodIncidence_not_isClosed_range m,
      boundaryMultipleGammaPeriodIncidence_isClosed_range⟩,
    finiteMultipleGammaProduct_reflection m,
    boundaryMultipleGammaProduct_reflection⟩

end

end HTGeometry
end GaloisForLFunctions

import GaloisForLFunctions.RHTower.DeningerMeyerInvariantEvaluationGaugeFrontier
import GaloisForLFunctions.RHTower.DeningerQuotientSeminorm
import GaloisForLFunctions.RHTower.DeningerSeminormInducedCompleted
import GaloisForLFunctions.RHTower.DeningerScaleFactorization

/-!
# Canonical half-density L1 completion of literal Meyer cohomology

The centered logarithmic dilation acts on the strong Meyer target by
`g(t) ↦ exp(-c / 2) g(t - c)`.  The weighted integral

`p(g) = ∫ exp(t / 2) * ‖g(t)‖ dt`

is therefore exactly invariant.  This file constructs that seminorm on the literal source,
descends it through the actual Poisson boundary by the quotient infimum, and completes its
Hausdorff seminorm quotient.  The centered flow extends to a surjective linear isometry of the
completion.

Mellin evaluation is bounded by this seminorm on the critical line.  For every actual Xi divisor
point, its nonzero descended zeroth evaluation is bounded by the quotient seminorm if and only if
the point lies on the critical line.  Thus this source-defined completion has exactly the critical
Xi continuity spectrum; no RH premise is used in constructing it.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- Critical half-density weight in logarithmic radius. -/
def deningerMeyerHalfDensityWeight (t : ℝ) : ℝ :=
  Real.exp (t / 2)

theorem deningerMeyerHalfDensityWeight_pos (t : ℝ) :
    0 < deningerMeyerHalfDensityWeight t :=
  Real.exp_pos _

/-- Weighted `L1` functional on the literal all-weight Meyer target. -/
def deningerMeyerHalfDensityL1Fun
    (g : DeningerMeyerStrongLogTarget) : ℝ :=
  ∫ t : ℝ, deningerMeyerHalfDensityWeight t * ‖(g : ℝ → ℂ) t‖

theorem integrable_deningerMeyerHalfDensityL1
    (g : DeningerMeyerStrongLogTarget) :
    Integrable
      (fun t : ℝ =>
        deningerMeyerHalfDensityWeight t * ‖(g : ℝ → ℂ) t‖) := by
  have h :=
    (integrable_deningerMeyerStrongLogMellinJet
      g.property 0 (((1 / 2 : ℝ) : ℂ))).norm
  simpa only [norm_deningerMeyerStrongLogMellinJet,
    pow_zero, one_mul, Complex.ofReal_re,
    deningerMeyerHalfDensityWeight, one_div, div_eq_mul_inv,
    mul_comm] using h

/-- Canonical source seminorm selected by centered dilation invariance. -/
noncomputable def deningerMeyerHalfDensityL1Seminorm :
    Seminorm ℂ DeningerMeyerStrongLogTarget :=
  Seminorm.ofSMulLE deningerMeyerHalfDensityL1Fun
    (by simp [deningerMeyerHalfDensityL1Fun])
    (by
      intro g h
      have hgh := integrable_deningerMeyerHalfDensityL1 (g + h)
      have hg := integrable_deningerMeyerHalfDensityL1 g
      have hh := integrable_deningerMeyerHalfDensityL1 h
      refine (integral_mono hgh (hg.add hh) ?_).trans_eq ?_
      · intro t
        change
          deningerMeyerHalfDensityWeight t *
              ‖(g : ℝ → ℂ) t + (h : ℝ → ℂ) t‖ ≤
            deningerMeyerHalfDensityWeight t * ‖(g : ℝ → ℂ) t‖ +
              deningerMeyerHalfDensityWeight t * ‖(h : ℝ → ℂ) t‖
        calc
          deningerMeyerHalfDensityWeight t *
                ‖(g : ℝ → ℂ) t + (h : ℝ → ℂ) t‖ ≤
              deningerMeyerHalfDensityWeight t *
                (‖(g : ℝ → ℂ) t‖ + ‖(h : ℝ → ℂ) t‖) :=
            mul_le_mul_of_nonneg_left
              (norm_add_le ((g : ℝ → ℂ) t) ((h : ℝ → ℂ) t))
              (deningerMeyerHalfDensityWeight_pos t).le
          _ = _ := by ring
      · exact integral_add hg hh)
    (by
      intro c g
      have hfun :
          (fun t : ℝ =>
            deningerMeyerHalfDensityWeight t *
              ‖((c • g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t‖) =
            fun t : ℝ =>
              ‖c‖ *
                (deningerMeyerHalfDensityWeight t * ‖(g : ℝ → ℂ) t‖) := by
        funext t
        rw [show ((c • g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t =
          c * (g : ℝ → ℂ) t by rfl, norm_mul]
        ring
      change
        (∫ t : ℝ,
          deningerMeyerHalfDensityWeight t *
            ‖((c • g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t‖) ≤
          ‖c‖ *
            ∫ t : ℝ,
              deningerMeyerHalfDensityWeight t * ‖(g : ℝ → ℂ) t‖
      rw [hfun, integral_const_mul])

@[simp]
theorem deningerMeyerHalfDensityL1Seminorm_apply
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHalfDensityL1Seminorm g =
      ∫ t : ℝ, deningerMeyerHalfDensityWeight t * ‖(g : ℝ → ℂ) t‖ :=
  rfl

/-- Centered logarithmic dilation on the literal strong target. -/
def deningerMeyerStrongLogCenteredFlow (c : ℝ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget :=
  Complex.exp (-(c : ℂ) / 2) • deningerMeyerStrongLogFlow c

@[simp]
theorem deningerMeyerStrongLogCenteredFlow_apply
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    ((deningerMeyerStrongLogCenteredFlow c g :
      DeningerMeyerStrongLogTarget) : ℝ → ℂ) t =
      Complex.exp (-(c : ℂ) / 2) * (g : ℝ → ℂ) (t - c) :=
  rfl

theorem deningerMeyerStrongLogCenteredFlow_add
    (a b : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogCenteredFlow a
        (deningerMeyerStrongLogCenteredFlow b g) =
      deningerMeyerStrongLogCenteredFlow (a + b) g := by
  rw [deningerMeyerStrongLogCenteredFlow,
    deningerMeyerStrongLogCenteredFlow,
    deningerMeyerStrongLogCenteredFlow,
    LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, map_smul,
    deningerMeyerStrongLogFlow_add, smul_smul]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp]
theorem deningerMeyerStrongLogCenteredFlow_zero
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogCenteredFlow 0 g = g := by
  simp [deningerMeyerStrongLogCenteredFlow]

/-- Exact source isometry.  The half-density scalar cancels the translated weight. -/
theorem deningerMeyerHalfDensityL1Seminorm_centeredFlow
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHalfDensityL1Seminorm
        (deningerMeyerStrongLogCenteredFlow c g) =
      deningerMeyerHalfDensityL1Seminorm g := by
  rw [deningerMeyerHalfDensityL1Seminorm_apply,
    deningerMeyerHalfDensityL1Seminorm_apply]
  let F : ℝ → ℝ := fun u =>
    deningerMeyerHalfDensityWeight u * ‖(g : ℝ → ℂ) u‖
  have hscale :
      ‖Complex.exp (-(c : ℂ) / 2)‖ = Real.exp (-c / 2) := by
    rw [Complex.norm_exp]
    simp
  have hpoint : ∀ t : ℝ,
      deningerMeyerHalfDensityWeight t *
          ‖((deningerMeyerStrongLogCenteredFlow c g :
            DeningerMeyerStrongLogTarget) : ℝ → ℂ) t‖ =
        F (t - c) := by
    intro t
    rw [deningerMeyerStrongLogCenteredFlow_apply,
      norm_mul, hscale]
    dsimp [F, deningerMeyerHalfDensityWeight]
    have hexp :
        Real.exp (t / 2) * Real.exp (-c / 2) =
          Real.exp ((t - c) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← mul_assoc, hexp]
  calc
    (∫ t : ℝ,
      deningerMeyerHalfDensityWeight t *
        ‖((deningerMeyerStrongLogCenteredFlow c g :
          DeningerMeyerStrongLogTarget) : ℝ → ℂ) t‖) =
        ∫ t : ℝ, F (t - c) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ t : ℝ, F t := integral_sub_right_eq_self F c

/-- Quotient half-density seminorm on literal Meyer middle cohomology. -/
noncomputable def deningerMeyerHalfDensityCohomologySeminorm :
    Seminorm ℂ DeningerMeyerStrongLogCohomology :=
  deningerQuotientSeminorm
    (LinearMap.range deningerMeyerStrongLogSumLM)
    deningerMeyerHalfDensityL1Seminorm

@[simp]
theorem deningerMeyerStrongLogCenteredCohomologyFlow_mk
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogCenteredCohomologyFlow c
        (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (deningerMeyerStrongLogCenteredFlow c g) := by
  rw [deningerMeyerStrongLogCenteredCohomologyFlow,
    deningerMeyerStrongLogCenteredFlow,
    LinearMap.smul_apply, LinearMap.smul_apply,
    deningerMeyerStrongLogCohomologyFlow_mk,
    Submodule.Quotient.mk_smul]

theorem deningerMeyerStrongLogCenteredCohomologyFlow_add
    (a b : ℝ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerStrongLogCenteredCohomologyFlow a
        (deningerMeyerStrongLogCenteredCohomologyFlow b u) =
      deningerMeyerStrongLogCenteredCohomologyFlow (a + b) u := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
      simp only [deningerMeyerStrongLogCenteredCohomologyFlow_mk,
        deningerMeyerStrongLogCenteredFlow_add]

@[simp]
theorem deningerMeyerStrongLogCenteredCohomologyFlow_zero
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerStrongLogCenteredCohomologyFlow 0 u = u := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
      simp

private theorem deningerMeyerHalfDensityCohomologySeminorm_centeredFlow_le
    (c : ℝ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHalfDensityCohomologySeminorm
        (deningerMeyerStrongLogCenteredCohomologyFlow c u) ≤
      deningerMeyerHalfDensityCohomologySeminorm u := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, hg, hlt⟩ :=
    deningerQuotientSeminorm_exists_lt
      (LinearMap.range deningerMeyerStrongLogSumLM)
      deningerMeyerHalfDensityL1Seminorm u hε
  have hmk :
      Submodule.Quotient.mk (deningerMeyerStrongLogCenteredFlow c g) =
        deningerMeyerStrongLogCenteredCohomologyFlow c u := by
    rw [← hg, deningerMeyerStrongLogCenteredCohomologyFlow_mk]
  have hle :=
    deningerQuotientSeminorm_mk_le
      (LinearMap.range deningerMeyerStrongLogSumLM)
      deningerMeyerHalfDensityL1Seminorm
      (deningerMeyerStrongLogCenteredFlow c g)
  change
    deningerMeyerHalfDensityCohomologySeminorm
        (Submodule.Quotient.mk
          (deningerMeyerStrongLogCenteredFlow c g)) ≤ _ at hle
  change
    deningerMeyerHalfDensityL1Seminorm g <
      deningerMeyerHalfDensityCohomologySeminorm u + ε at hlt
  rw [hmk, deningerMeyerHalfDensityL1Seminorm_centeredFlow] at hle
  linarith

/-- Exact centered-flow isometry on the literal quotient seminorm. -/
theorem deningerMeyerHalfDensityCohomologySeminorm_centeredFlow
    (c : ℝ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHalfDensityCohomologySeminorm
        (deningerMeyerStrongLogCenteredCohomologyFlow c u) =
      deningerMeyerHalfDensityCohomologySeminorm u := by
  apply le_antisymm
  · exact deningerMeyerHalfDensityCohomologySeminorm_centeredFlow_le c u
  · have h :=
      deningerMeyerHalfDensityCohomologySeminorm_centeredFlow_le
        (-c) (deningerMeyerStrongLogCenteredCohomologyFlow c u)
    rw [deningerMeyerStrongLogCenteredCohomologyFlow_add] at h
    simpa using h

/-- Critical-line Mellin evaluation is contractive for the raw half-density seminorm. -/
theorem norm_deningerMeyerStrongLogMellin_le_halfDensityL1
    (g : DeningerMeyerStrongLogTarget) (s : ℂ)
    (hs : s.re = 1 / 2) :
    ‖deningerMeyerStrongLogMellin g s‖ ≤
      deningerMeyerHalfDensityL1Seminorm g := by
  calc
    ‖deningerMeyerStrongLogMellin g s‖ =
        ‖∫ t : ℝ, deningerMeyerStrongLogMellinJet 0 s g t‖ := rfl
    _ ≤ ∫ t : ℝ, ‖deningerMeyerStrongLogMellinJet 0 s g t‖ :=
      norm_integral_le_integral_norm _
    _ = deningerMeyerHalfDensityL1Seminorm g := by
      rw [deningerMeyerHalfDensityL1Seminorm_apply]
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_deningerMeyerStrongLogMellinJet,
        pow_zero, one_mul, hs]
      congr 2
      ring

/-- At a critical actual Xi point, its descended nonzero evaluation is contractive for the
quotient half-density seminorm. -/
theorem norm_deningerMeyerXiSupportEvaluation_le_halfDensityCohomology
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    ‖deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho) u‖ ≤
      deningerMeyerHalfDensityCohomologySeminorm u := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, hg, hlt⟩ :=
    deningerQuotientSeminorm_exists_lt
      (LinearMap.range deningerMeyerStrongLogSumLM)
      deningerMeyerHalfDensityL1Seminorm u hε
  have heval :
      deningerMeyerXiSupportJetEvaluationLM rho
          (⟨0, xiSupportMultiplicity_pos rho⟩ :
            DeningerArithmeticJetIndex rho) u =
        deningerMeyerStrongLogMellinJetLM 0 (rho : ℂ) g := by
    rw [← hg, deningerMeyerXiSupportJetEvaluationLM_mk]
  have hmellin :
      ‖deningerMeyerStrongLogMellinJetLM 0 (rho : ℂ) g‖ ≤
        deningerMeyerHalfDensityL1Seminorm g := by
    change ‖deningerMeyerStrongLogMellin g (rho : ℂ)‖ ≤ _
    exact norm_deningerMeyerStrongLogMellin_le_halfDensityL1 g (rho : ℂ) hrho
  change
    deningerMeyerHalfDensityL1Seminorm g <
      deningerMeyerHalfDensityCohomologySeminorm u + ε at hlt
  rw [heval]
  linarith

/-- Boundedness of one actual Xi evaluation for the concrete half-density quotient topology. -/
def DeningerMeyerHalfDensityXiEvaluationBounded
    (rho : XiDivisorSupport) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : DeningerMeyerStrongLogCohomology,
    ‖deningerMeyerXiSupportJetEvaluationLM rho
      (⟨0, xiSupportMultiplicity_pos rho⟩ :
        DeningerArithmeticJetIndex rho) u‖ ≤
      C * deningerMeyerHalfDensityCohomologySeminorm u

/-- Exact continuity spectrum: the concrete source topology retains an actual Xi evaluation
continuously exactly on the critical line. -/
theorem deningerMeyerHalfDensityXiEvaluationBounded_iff
    (rho : XiDivisorSupport) :
    DeningerMeyerHalfDensityXiEvaluationBounded rho ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hbounded
    apply xiDivisorSupport_re_eq_half_of_pointwiseInvariantEvaluationGauge
      rho deningerMeyerHalfDensityCohomologySeminorm
    exact ⟨fun u => apply_nonneg _ u,
      deningerMeyerHalfDensityCohomologySeminorm_centeredFlow,
      hbounded⟩
  · intro hrho
    refine ⟨1, zero_le_one, ?_⟩
    intro u
    simpa using
      norm_deningerMeyerXiSupportEvaluation_le_halfDensityCohomology rho hrho u

/-- Source-topological reformulation of RH: every actual Xi evaluation is continuous for the one
canonical half-density quotient seminorm if and only if RH. -/
theorem riemannHypothesis_iff_deningerMeyerHalfDensityXiEvaluationsBounded :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        DeningerMeyerHalfDensityXiEvaluationBounded rho := by
  constructor
  · intro hRH rho
    rw [deningerMeyerHalfDensityXiEvaluationBounded_iff]
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).1
        ((xiBoundaryCharacterNeutral_iff_riemannHypothesis.mpr hRH) rho)
  · intro hbounded
    rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
    intro rho
    apply (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).2
    exact deningerMeyerHalfDensityXiEvaluationBounded_iff rho |>.mp (hbounded rho)

/-- Hausdorff Banach completion selected by the concrete quotient seminorm.  Its canonical map
from literal Meyer cohomology may have a kernel; faithfulness is a separate source theorem. -/
abbrev DeningerMeyerHalfDensityCompletion : Type _ :=
  DeningerSeminormCompletion deningerMeyerHalfDensityCohomologySeminorm

/-- Canonical map from literal Meyer cohomology into the half-density completion. -/
noncomputable def deningerMeyerHalfDensityCompletionMk :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerHalfDensityCompletion :=
  deningerSeminormMkC deningerMeyerHalfDensityCohomologySeminorm

@[simp]
theorem deningerMeyerHalfDensityCompletionMk_norm
    (u : DeningerMeyerStrongLogCohomology) :
    ‖deningerMeyerHalfDensityCompletionMk u‖ =
      deningerMeyerHalfDensityCohomologySeminorm u :=
  deningerSeminormMkC_norm _ u

/-- Centered flow extended continuously to the concrete Banach completion. -/
noncomputable def deningerMeyerHalfDensityCompletedFlow (c : ℝ) :
    DeningerMeyerHalfDensityCompletion →L[ℂ]
      DeningerMeyerHalfDensityCompletion :=
  deningerSeminormInducedC
    (deningerMeyerStrongLogCenteredCohomologyFlow c)
    (fun u => by
      rw [deningerMeyerHalfDensityCohomologySeminorm_centeredFlow,
        one_mul])

@[simp]
theorem deningerMeyerHalfDensityCompletedFlow_mk
    (c : ℝ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHalfDensityCompletedFlow c
        (deningerMeyerHalfDensityCompletionMk u) =
      deningerMeyerHalfDensityCompletionMk
        (deningerMeyerStrongLogCenteredCohomologyFlow c u) :=
  deningerSeminormInducedC_mkC _ _ u

theorem deningerMeyerHalfDensityCompletedFlow_norm_le_one (c : ℝ) :
    ‖deningerMeyerHalfDensityCompletedFlow c‖ ≤ 1 :=
  deningerSeminormInducedC_norm_le zero_le_one _ _

theorem deningerMeyerHalfDensityCompletedFlow_add
    (a b : ℝ) (z : DeningerMeyerHalfDensityCompletion) :
    deningerMeyerHalfDensityCompletedFlow a
        (deningerMeyerHalfDensityCompletedFlow b z) =
      deningerMeyerHalfDensityCompletedFlow (a + b) z := by
  let F :=
    (deningerMeyerHalfDensityCompletedFlow a).comp
      (deningerMeyerHalfDensityCompletedFlow b)
  let G := deningerMeyerHalfDensityCompletedFlow (a + b)
  have hFG : F = G := by
    refine DFunLike.coe_injective ?_
    refine (deningerSeminormMkC_denseRange
      deningerMeyerHalfDensityCohomologySeminorm).equalizer
        F.continuous G.continuous ?_
    funext u
    change F (deningerMeyerHalfDensityCompletionMk u) =
      G (deningerMeyerHalfDensityCompletionMk u)
    change
      deningerMeyerHalfDensityCompletedFlow a
          (deningerMeyerHalfDensityCompletedFlow b
            (deningerMeyerHalfDensityCompletionMk u)) =
        deningerMeyerHalfDensityCompletedFlow (a + b)
          (deningerMeyerHalfDensityCompletionMk u)
    rw [deningerMeyerHalfDensityCompletedFlow_mk,
      deningerMeyerHalfDensityCompletedFlow_mk,
      deningerMeyerHalfDensityCompletedFlow_mk,
      deningerMeyerStrongLogCenteredCohomologyFlow_add]
  exact DFunLike.congr_fun hFG z

@[simp]
theorem deningerMeyerHalfDensityCompletedFlow_zero
    (z : DeningerMeyerHalfDensityCompletion) :
    deningerMeyerHalfDensityCompletedFlow 0 z = z := by
  have h := deningerMeyerHalfDensityCompletedFlow_add 0 0 z
  rw [zero_add] at h
  have hfix :
      ∀ u : DeningerMeyerStrongLogCohomology,
        deningerMeyerHalfDensityCompletedFlow 0
          (deningerMeyerHalfDensityCompletionMk u) =
            deningerMeyerHalfDensityCompletionMk u := by
    intro u
    rw [deningerMeyerHalfDensityCompletedFlow_mk,
      deningerMeyerStrongLogCenteredCohomologyFlow_zero]
  let F := deningerMeyerHalfDensityCompletedFlow 0
  let G : DeningerMeyerHalfDensityCompletion →L[ℂ]
      DeningerMeyerHalfDensityCompletion := ContinuousLinearMap.id ℂ _
  have hFG : F = G := by
    refine DFunLike.coe_injective ?_
    refine (deningerSeminormMkC_denseRange
      deningerMeyerHalfDensityCohomologySeminorm).equalizer
        F.continuous G.continuous ?_
    funext u
    exact hfix u
  exact DFunLike.congr_fun hFG z

/-- Every completed centered flow is an exact norm isometry. -/
theorem deningerMeyerHalfDensityCompletedFlow_norm
    (c : ℝ) (z : DeningerMeyerHalfDensityCompletion) :
    ‖deningerMeyerHalfDensityCompletedFlow c z‖ = ‖z‖ := by
  apply le_antisymm
  · have h := ContinuousLinearMap.le_of_opNorm_le
      (deningerMeyerHalfDensityCompletedFlow c)
      (deningerMeyerHalfDensityCompletedFlow_norm_le_one c) z
    simpa using h
  · have h := ContinuousLinearMap.le_of_opNorm_le
      (deningerMeyerHalfDensityCompletedFlow (-c))
      (deningerMeyerHalfDensityCompletedFlow_norm_le_one (-c))
      (deningerMeyerHalfDensityCompletedFlow c z)
    rw [deningerMeyerHalfDensityCompletedFlow_add] at h
    simpa using h

/-- Completed centered flow is surjective, with inverse flow time `-c`. -/
theorem deningerMeyerHalfDensityCompletedFlow_surjective (c : ℝ) :
    Function.Surjective (deningerMeyerHalfDensityCompletedFlow c) := by
  intro z
  refine ⟨deningerMeyerHalfDensityCompletedFlow (-c) z, ?_⟩
  rw [deningerMeyerHalfDensityCompletedFlow_add]
  simp

/-- At a critical actual Xi point, the algebraic evaluation extends to the concrete completion. -/
noncomputable def deningerMeyerHalfDensityXiEvaluationCLM
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re = 1 / 2) :
    DeningerMeyerHalfDensityCompletion →L[ℂ] ℂ :=
  deningerSeminormFactorC (C := 1)
    (T := deningerMeyerXiSupportJetEvaluationLM rho
      (⟨0, xiSupportMultiplicity_pos rho⟩ :
        DeningerArithmeticJetIndex rho))
    (fun u => by
      rw [one_mul]
      exact
        norm_deningerMeyerXiSupportEvaluation_le_halfDensityCohomology
          rho hrho u)

@[simp]
theorem deningerMeyerHalfDensityXiEvaluationCLM_mk
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHalfDensityXiEvaluationCLM rho hrho
        (deningerMeyerHalfDensityCompletionMk u) =
      deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho) u :=
  by
    rw [deningerMeyerHalfDensityXiEvaluationCLM,
      deningerMeyerHalfDensityCompletionMk]
    exact deningerSeminormFactorC_coe _ u

/-- Critical Xi evaluation remains nonzero after completion. -/
theorem deningerMeyerHalfDensityXiEvaluationCLM_ne_zero
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re = 1 / 2) :
    deningerMeyerHalfDensityXiEvaluationCLM rho hrho ≠ 0 := by
  intro hzero
  apply deningerMeyerXiSupportEvaluationLM_ne_zero rho
  apply LinearMap.ext
  intro u
  have h := DFunLike.congr_fun hzero
    (deningerMeyerHalfDensityCompletionMk u)
  rw [deningerMeyerHalfDensityXiEvaluationCLM_mk] at h
  simpa using h

end

end RHTower

import GaloisForLFunctions.RHTower.MobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw

/-!
# Four-unit operator-norm transport criterion

The canonical finite source completions have a bottom Schur-complement
capacity and an associated finite self-adjoint operator.  Operator-norm
convergence already controls that capacity: it is one diagonal matrix
coefficient, hence its error is bounded by the operator error.

Consequently every operator-norm-faithful cofinal source schedule has the
same asymptotic minimum budget

`4 + mobiusGammaXiCoupledErrorSingularGraphDebt`.

This removes the budget term from the convergence premise.  RH is exactly
existence of one strictly cofinal operator-norm-faithful schedule whose
minimum source budget reaches the intrinsic four-unit Fisher floor.  If RH
is false, every such schedule retains the same strictly positive graph
excess.
-/

open Complex Filter Set Topology Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace RHTower

/-- The bottom Schur-complement budget is an observable matrix coefficient,
so its error is bounded by the operator norm of the completion error. -/
theorem abs_mobiusGammaXiCoupledErrorBudget_sub_le_operatorNorm
    (j N : ℕ) :
    |mobiusGammaXiCoupledErrorSourceBudget j N -
        mobiusGammaXiCoupledErrorSingularBudget N| ≤
      ‖mobiusGammaXiCoupledErrorSourceOperator j N -
        mobiusGammaXiCoupledErrorSingularOperator N‖ := by
  have h :=
    GaloisForLFunctions.HTGeometry.norm_entry_le_l2_opNorm
      (mobiusGammaXiCoupledErrorSourceCompletion j N -
        mobiusGammaXiCoupledErrorSingularCompletion N)
      (Sum.inr ()) (Sum.inr ())
  change
    ‖finiteHardyMinimumCapacity
          (mobiusGammaXiCoupledErrorHeadGram N)
          (mobiusGammaXiCoupledErrorHeadGram_posDef N)
          (mobiusGammaXiCoupledErrorSourceResponse j N) () () -
        finiteHardyMinimumCapacity
          (mobiusGammaXiCoupledErrorHeadGram N)
          (mobiusGammaXiCoupledErrorHeadGram_posDef N)
          (mobiusGammaXiCoupledErrorSingularResponse N) () ()‖ ≤ _ at h
  rw [finiteHardyMinimumCapacity_entry_eq_budget,
    finiteHardyMinimumCapacity_entry_eq_budget] at h
  have norm_ofReal_sub (a b : ℝ) :
      ‖(a : ℂ) - (b : ℂ)‖ = |a - b| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_ofReal_sub] at h
  rw [Matrix.cstar_norm_def] at h
  simpa [mobiusGammaXiCoupledErrorSourceOperator,
    mobiusGammaXiCoupledErrorSingularOperator,
    mobiusGammaXiCoupledErrorSourceBudget,
    mobiusGammaXiCoupledErrorSingularBudget,
    Real.norm_eq_abs] using h

/-- Operator-norm fidelity alone forces every cofinal source schedule to
retain the exact singular graph budget.  No separate budget-convergence
hypothesis is needed. -/
theorem
    tendsto_mobiusGammaXiCoupledErrorSourceBudget_graphBudget_of_operatorNorm
    (depth : ℕ → ℕ)
    (hop : Tendsto (fun N =>
      ‖mobiusGammaXiCoupledErrorSourceOperator (depth N) N -
        mobiusGammaXiCoupledErrorSingularOperator N‖)
      atTop (𝓝 0)) :
    Tendsto (fun N => mobiusGammaXiCoupledErrorSourceBudget (depth N) N)
      atTop (𝓝 (4 + mobiusGammaXiCoupledErrorSingularGraphDebt)) := by
  have hbudgetAbs : Tendsto (fun N =>
      |mobiusGammaXiCoupledErrorSourceBudget (depth N) N -
        mobiusGammaXiCoupledErrorSingularBudget N|) atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall fun N =>
        abs_mobiusGammaXiCoupledErrorBudget_sub_le_operatorNorm (depth N) N)
      hop
  have hbudgetSub : Tendsto (fun N =>
      mobiusGammaXiCoupledErrorSourceBudget (depth N) N -
        mobiusGammaXiCoupledErrorSingularBudget N) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.norm_eq_abs] using hbudgetAbs
  have hsum := hbudgetSub.add
    tendsto_mobiusGammaXiCoupledErrorSingularBudget_graphBudget
  simpa using hsum

/-- Falsifiable source-side synthesis: one strictly cofinal family of
canonical finite self-adjoint completions converges in operator norm to the
singular boundary heads while its minimum completion energy collapses to the
intrinsic four-unit Fisher floor. -/
def MobiusGammaXiFourUnitOperatorNormTransport : Prop :=
  ∃ depth : ℕ → ℕ, StrictMono depth ∧
    Tendsto (fun N =>
      ‖mobiusGammaXiCoupledErrorSourceOperator (depth N) N -
        mobiusGammaXiCoupledErrorSingularOperator N‖)
      atTop (𝓝 0) ∧
    Tendsto (fun N => mobiusGammaXiCoupledErrorSourceBudget (depth N) N)
      atTop (𝓝 4)

/-- **Four-unit operator-norm transport criterion.** RH holds exactly when
one source-native cofinal finite self-adjoint realization reaches the
uncompleted Fisher floor without losing operator-norm fidelity. -/
theorem mobiusGammaXiFourUnitOperatorNormTransport_iff_riemannHypothesis :
    MobiusGammaXiFourUnitOperatorNormTransport ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨depth, _hdepth, hop, hfour⟩
    have hgraph :=
      tendsto_mobiusGammaXiCoupledErrorSourceBudget_graphBudget_of_operatorNorm
        depth hop
    have heq : (4 : ℝ) =
        4 + mobiusGammaXiCoupledErrorSingularGraphDebt :=
      tendsto_nhds_unique hfour hgraph
    apply mobiusGammaXiCoupledErrorSingularGraphDebt_eq_zero_iff_rh.mp
    linarith
  · intro hRH
    obtain ⟨depth, hdepth, _hsource, _hsingular, hop, _hcolumn,
        _hpoint, hbudget⟩ :=
      exists_mobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport
    refine ⟨depth, hdepth, hop, ?_⟩
    have hdebt : mobiusGammaXiCoupledErrorSingularGraphDebt = 0 :=
      mobiusGammaXiCoupledErrorSingularGraphDebt_eq_zero_iff_rh.mpr hRH
    simpa [hdebt] using hbudget

/-- Failure of RH makes the universal graph excess strictly positive. -/
theorem mobiusGammaXiCoupledErrorSingularGraphDebt_pos_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    0 < mobiusGammaXiCoupledErrorSingularGraphDebt := by
  have hne : mobiusGammaXiCoupledErrorSingularGraphDebt ≠ 0 := by
    intro hzero
    exact hRH
      (mobiusGammaXiCoupledErrorSingularGraphDebt_eq_zero_iff_rh.mp hzero)
  exact lt_of_le_of_ne
    (Complex.normSq_nonneg mobiusGammaXiCoupledErrorCriticalCoefficient)
    (Ne.symm hne)

/-- **Hostile falsification branch.** If RH is false, every operator-norm
faithful source schedule converges to a budget strictly above four; changing
the cofinal schedule cannot hide the graph debt. -/
theorem
    mobiusGammaXiCoupledErrorSourceBudget_strictlyAboveFour_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) (depth : ℕ → ℕ)
    (hop : Tendsto (fun N =>
      ‖mobiusGammaXiCoupledErrorSourceOperator (depth N) N -
        mobiusGammaXiCoupledErrorSingularOperator N‖)
      atTop (𝓝 0)) :
    4 < 4 + mobiusGammaXiCoupledErrorSingularGraphDebt ∧
      Tendsto (fun N => mobiusGammaXiCoupledErrorSourceBudget (depth N) N)
        atTop (𝓝 (4 + mobiusGammaXiCoupledErrorSingularGraphDebt)) := by
  exact ⟨by
      linarith [
        mobiusGammaXiCoupledErrorSingularGraphDebt_pos_of_not_riemannHypothesis
          hRH],
    tendsto_mobiusGammaXiCoupledErrorSourceBudget_graphBudget_of_operatorNorm
      depth hop⟩

end RHTower

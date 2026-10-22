import GaloisForLFunctions.RHTower.PrimeHodgeHistorySurvivalFredholmColligation
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.RHTower.Suzuki.SuzukiDiagonalResolventInstantiation
import GaloisForLFunctions.HTGeometry.HarmonicOrdinateDivergence
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# Theta-survival relative curvature reconstruction

The forced theta-survival shift has two positive compact defect metrics.  Neither metric is
trace class, but their canonical relative difference is a positive trace-class self-commutator.
Its diagonal curvature has total mass one and operator norm one third, and it reconstructs the
complete prime-Hodge exit history without divisor, zero, or RH input.
-/

open Filter Topology BigOperators

namespace PrimeHodgeHistory

noncomputable section

/-- First difference of the forced survival ratio, including its boundary jump from zero. -/
def relativeCurvatureWeight : ℕ → ℝ
  | 0 => survivalRatio 0
  | n + 1 => survivalRatio (n + 1) - survivalRatio n

theorem relativeCurvatureWeight_zero : relativeCurvatureWeight 0 = 1 / 3 := by
  rw [relativeCurvatureWeight, survivalRatio_formula]
  norm_num

theorem relativeCurvatureWeight_succ (n : ℕ) :
    relativeCurvatureWeight (n + 1) =
      12 / (((2 * n + 9 : ℕ) : ℝ) * ((2 * n + 11 : ℕ) : ℝ)) := by
  rw [relativeCurvatureWeight, survivalRatio_formula, survivalRatio_formula]
  push_cast
  field_simp
  ring

theorem relativeCurvatureWeight_pos (n : ℕ) : 0 < relativeCurvatureWeight n := by
  rcases n with _ | n
  · rw [relativeCurvatureWeight_zero]
    norm_num
  · rw [relativeCurvatureWeight_succ]
    positivity

theorem relativeCurvatureWeight_le_one_third (n : ℕ) :
    relativeCurvatureWeight n ≤ 1 / 3 := by
  rcases n with _ | n
  · rw [relativeCurvatureWeight_zero]
  · rw [relativeCurvatureWeight_succ]
    push_cast
    apply (div_le_iff₀ (by positivity)).2
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg (n : ℝ)]

theorem sum_range_succ_relativeCurvatureWeight (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), relativeCurvatureWeight n) = survivalRatio N := by
  induction N with
  | zero => simp [relativeCurvatureWeight]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, relativeCurvatureWeight]
      ring

theorem survivalRatio_tendsto_one : Tendsto survivalRatio atTop (nhds 1) := by
  have hden : Tendsto (fun n : ℕ => ((2 * n + 9 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      tendsto_atTop_add_const_right atTop 9
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hzero : Tendsto (fun n : ℕ => 6 / (((2 * n + 9 : ℕ) : ℝ))) atTop (nhds 0) :=
    (tendsto_const_nhds (x := (6 : ℝ))).div_atTop hden
  have hformula : survivalRatio = fun n : ℕ => 1 - 6 / (((2 * n + 9 : ℕ) : ℝ)) := by
    funext n
    rw [survivalRatio_formula]
    push_cast
    field_simp
    ring
  rw [hformula]
  simpa using tendsto_const_nhds.sub hzero

theorem exitHazard_tendsto_zero : Tendsto exitHazard atTop (nhds 0) := by
  change Tendsto (fun n => 1 - survivalRatio n) atTop (nhds 0)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub survivalRatio_tendsto_one

/-- Outgoing defect coefficient: the boundary grade is fully missing, and every later grade
inherits the previous incoming loss. -/
def outgoingMetricWeight : ℕ → ℝ
  | 0 => 1
  | n + 1 => exitHazard n

theorem outgoingMetricWeight_pos (n : ℕ) : 0 < outgoingMetricWeight n := by
  rcases n with _ | n
  · simp [outgoingMetricWeight]
  · simpa [outgoingMetricWeight] using exitHazard_pos n

theorem outgoingMetricWeight_le_one (n : ℕ) : outgoingMetricWeight n ≤ 1 := by
  rcases n with _ | n
  · simp [outgoingMetricWeight]
  · simpa [outgoingMetricWeight] using exitHazard_le_one n

theorem outgoingMetricWeight_tendsto_zero :
    Tendsto outgoingMetricWeight atTop (nhds 0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  simpa [outgoingMetricWeight] using exitHazard_tendsto_zero

theorem outgoing_sub_incoming_eq_relativeCurvatureWeight (n : ℕ) :
    outgoingMetricWeight n - exitHazard n = relativeCurvatureWeight n := by
  rcases n with _ | n
  · rw [outgoingMetricWeight, exitHazard, relativeCurvatureWeight]
    ring
  · rw [outgoingMetricWeight, exitHazard, exitHazard, relativeCurvatureWeight]
    ring

theorem not_summable_exitHazard : ¬ Summable exitHazard := by
  let gamma : ℕ → ℝ := fun n => ((2 * n + 9 : ℕ) : ℝ)
  have hgamma : ¬ Summable fun n => (gamma n)⁻¹ :=
    GaloisForLFunctions.HTGeometry.not_summable_inv_of_le_linear
      (γ := gamma) (c := 9) (by norm_num)
      (fun n => by dsimp [gamma]; positivity) (by
        filter_upwards [] with n
        dsimp [gamma]
        push_cast
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith)
  intro h
  apply hgamma
  refine (h.div_const 6).congr fun n => ?_
  rw [exitHazard_formula]
  dsimp [gamma]
  push_cast
  field_simp

theorem not_summable_outgoingMetricWeight : ¬ Summable outgoingMetricWeight := by
  intro h
  apply not_summable_exitHazard
  have htail : Summable fun n => outgoingMetricWeight (n + 1) :=
    (summable_nat_add_iff 1).2 h
  exact htail.congr fun n => by simp [outgoingMetricWeight]

theorem hasSum_relativeCurvatureWeight : HasSum relativeCurvatureWeight 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => (relativeCurvatureWeight_pos n).le)]
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  simpa [sum_range_succ_relativeCurvatureWeight] using survivalRatio_tendsto_one

theorem summable_relativeCurvatureWeight : Summable relativeCurvatureWeight :=
  hasSum_relativeCurvatureWeight.summable

theorem tsum_relativeCurvatureWeight : ∑' n, relativeCurvatureWeight n = 1 :=
  hasSum_relativeCurvatureWeight.tsum_eq

theorem survivalRatio_eq_sum_range_relativeCurvatureWeight (n : ℕ) :
    survivalRatio n = ∑ j ∈ Finset.range (n + 1), relativeCurvatureWeight j := by
  exact (sum_range_succ_relativeCurvatureWeight n).symm

theorem m_eq_prod_survivalRatio (n : ℕ) :
    m n = ∏ j ∈ Finset.range n, survivalRatio j := by
  have h := survival_product 0 n
  rw [m_zero, div_one] at h
  simpa only [zero_add] using h.symm

theorem w_eq_m_mul_one_sub_survivalRatio (n : ℕ) :
    w n = m n * (1 - survivalRatio n) := by
  rw [w_eq_m_mul_exitHazard, exitHazard]

end

end PrimeHodgeHistory

namespace RHTower

open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

/-- Outgoing compact defect metric `I - C C*`. -/
def primeHodgeHistoryOutgoingMetric :
    ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert :=
  diagonalOperator
    (fun n => (PrimeHodgeHistory.outgoingMetricWeight n : ℂ))
    (C := 1) (fun n => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (PrimeHodgeHistory.outgoingMetricWeight_pos n)]
      exact PrimeHodgeHistory.outgoingMetricWeight_le_one n)

theorem primeHodgeHistoryOutgoingMetric_apply_basis (n : ℕ) :
    primeHodgeHistoryOutgoingMetric (HTGeometry.ellTwoCoordinateBasis ℕ n) =
      (PrimeHodgeHistory.outgoingMetricWeight n : ℂ) •
        HTGeometry.ellTwoCoordinateBasis ℕ n := by
  rw [HTGeometry.ellTwoCoordinateBasis_apply]
  unfold primeHodgeHistoryOutgoingMetric
  rw [diagonalOperator_single]
  rw [← lp.single_smul]
  simp

theorem primeHodgeHistoryIncomingMetric_apply_basis (n : ℕ) :
    primeHodgeHistoryExitDefect (HTGeometry.ellTwoCoordinateBasis ℕ n) =
      (PrimeHodgeHistory.exitHazard n : ℂ) •
        HTGeometry.ellTwoCoordinateBasis ℕ n := by
  exact HTGeometry.ellTwoDiagonal_coordinateBasis _ _ n

theorem primeHodgeHistoryOutgoingMetric_isPositive :
    primeHodgeHistoryOutgoingMetric.IsPositive := by
  exact GaloisForLFunctions.RHTower.isPositive_diagonalOperator_ofReal
    PrimeHodgeHistory.outgoingMetricWeight
    (fun n => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (PrimeHodgeHistory.outgoingMetricWeight_pos n)]
      exact PrimeHodgeHistory.outgoingMetricWeight_le_one n)
    (fun n => (PrimeHodgeHistory.outgoingMetricWeight_pos n).le)

theorem primeHodgeHistoryIncomingMetric_isPositive :
    primeHodgeHistoryExitDefect.IsPositive := by
  have heq : primeHodgeHistoryExitDefect =
      diagonalOperator (fun n => (PrimeHodgeHistory.exitHazard n : ℂ))
        (C := 1) (fun n => by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (PrimeHodgeHistory.exitHazard_pos n)]
          exact PrimeHodgeHistory.exitHazard_le_one n) := by
    ext f n
    simp [primeHodgeHistoryExitDefect, HTGeometry.ellTwoDiagonal_apply,
      diagonalOperator_apply]
  rw [heq]
  exact GaloisForLFunctions.RHTower.isPositive_diagonalOperator_ofReal
    PrimeHodgeHistory.exitHazard
    (fun n => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (PrimeHodgeHistory.exitHazard_pos n)]
      exact PrimeHodgeHistory.exitHazard_le_one n)
    (fun n => (PrimeHodgeHistory.exitHazard_pos n).le)

theorem primeHodgeHistoryOutgoingMetric_isCompactOperator :
    IsCompactOperator primeHodgeHistoryOutgoingMetric := by
  apply GaloisForLFunctions.HTGeometry.isCompactOperator_of_diag_tendsto_cofinite
    (HTGeometry.ellTwoCoordinateBasis ℕ)
    primeHodgeHistoryOutgoingMetric_apply_basis
  rw [Nat.cofinite_eq_atTop]
  simpa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (PrimeHodgeHistory.outgoingMetricWeight_pos _)] using
      PrimeHodgeHistory.outgoingMetricWeight_tendsto_zero

theorem primeHodgeHistoryIncomingMetric_isCompactOperator :
    IsCompactOperator primeHodgeHistoryExitDefect := by
  apply GaloisForLFunctions.HTGeometry.isCompactOperator_of_diag_tendsto_cofinite
    (HTGeometry.ellTwoCoordinateBasis ℕ)
    primeHodgeHistoryIncomingMetric_apply_basis
  rw [Nat.cofinite_eq_atTop]
  simpa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (PrimeHodgeHistory.exitHazard_pos _)] using
      PrimeHodgeHistory.exitHazard_tendsto_zero

theorem primeHodgeHistoryOutgoingMetric_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 primeHodgeHistoryOutgoingMetric := by
  intro h
  have hdiag := h.one_summable_norm_inner_diag_basis
    (HTGeometry.ellTwoCoordinateBasis ℕ)
  apply PrimeHodgeHistory.not_summable_outgoingMetricWeight
  refine hdiag.congr fun n => ?_
  rw [primeHodgeHistoryOutgoingMetric_apply_basis, inner_smul_right,
    inner_self_eq_norm_sq_to_K,
    (HTGeometry.ellTwoCoordinateBasis ℕ).orthonormal.norm_eq_one]
  norm_num
  exact (PrimeHodgeHistory.outgoingMetricWeight_pos n).le

theorem primeHodgeHistoryIncomingMetric_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 primeHodgeHistoryExitDefect := by
  intro h
  have hdiag := h.one_summable_norm_inner_diag_basis
    (HTGeometry.ellTwoCoordinateBasis ℕ)
  apply PrimeHodgeHistory.not_summable_exitHazard
  refine hdiag.congr fun n => ?_
  rw [primeHodgeHistoryIncomingMetric_apply_basis, inner_smul_right,
    inner_self_eq_norm_sq_to_K,
    (HTGeometry.ellTwoCoordinateBasis ℕ).orthonormal.norm_eq_one]
  norm_num
  exact (PrimeHodgeHistory.exitHazard_pos n).le

theorem adjoint_primeHodgeHistorySurvivalShift :
    ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift =
      primeHodgeHistorySurvivalDiagonal ∘L
        GaloisForLFunctions.HTGeometry.backOp 1 := by
  rw [primeHodgeHistorySurvivalShift, ContinuousLinearMap.adjoint_comp,
    adjoint_primeHodgeHistorySurvivalDiagonal,
    GaloisForLFunctions.HTGeometry.adjoint_shiftOp]

theorem primeHodgeHistorySurvivalWeight_sq (n : ℕ) :
    primeHodgeHistorySurvivalWeight n * primeHodgeHistorySurvivalWeight n =
      (PrimeHodgeHistory.survivalRatio n : ℂ) := by
  rw [primeHodgeHistorySurvivalWeight, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (PrimeHodgeHistory.survivalRatio_pos n).le]

theorem primeHodgeHistoryOutgoingMetric_eq_adjoint_fracture :
    primeHodgeHistoryOutgoingMetric =
      ContinuousLinearMap.id ℂ PrimeHodgeHistorySpace -
        primeHodgeHistorySurvivalShift ∘L
          ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift := by
  ext f n
  change (PrimeHodgeHistory.outgoingMetricWeight n : ℂ) * f n =
    f n - (primeHodgeHistorySurvivalShift
      (ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift f)) n
  rcases n with _ | n
  · rw [primeHodgeHistorySurvivalShift_zero]
    simp [PrimeHodgeHistory.outgoingMetricWeight]
  · rw [primeHodgeHistorySurvivalShift_apply,
      adjoint_primeHodgeHistorySurvivalShift, ContinuousLinearMap.comp_apply,
      primeHodgeHistorySurvivalDiagonal, HTGeometry.ellTwoDiagonal_apply,
      GaloisForLFunctions.HTGeometry.backOp_apply]
    rw [PrimeHodgeHistory.outgoingMetricWeight,
      ← mul_assoc, primeHodgeHistorySurvivalWeight_sq]
    change (PrimeHodgeHistory.exitHazard n : ℂ) * f (n + 1) =
      f (n + 1) - (PrimeHodgeHistory.survivalRatio n : ℂ) * f (n + 1)
    rw [PrimeHodgeHistory.exitHazard]
    push_cast
    ring

/-- Positive relative curvature of the two theta-survival defect metrics. -/
def primeHodgeHistoryRelativeCurvatureOperator :
    ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert :=
  absoluteMatrixOperator
    (HilbertSchmidt.diagMul fun n => (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ))

theorem summable_norm_relativeCurvatureWeight :
    Summable fun n => ‖(PrimeHodgeHistory.relativeCurvatureWeight n : ℂ)‖ := by
  have hnorm :
      (fun n => ‖(PrimeHodgeHistory.relativeCurvatureWeight n : ℂ)‖) =
        PrimeHodgeHistory.relativeCurvatureWeight := by
    funext n
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (PrimeHodgeHistory.relativeCurvatureWeight_pos n)]
  rw [hnorm]
  exact PrimeHodgeHistory.summable_relativeCurvatureWeight

theorem primeHodgeHistoryRelativeCurvatureOperator_memSchattenClass_one :
    MemSchattenClass 1 primeHodgeHistoryRelativeCurvatureOperator := by
  exact absoluteMatrixOperator_memSchattenClass_one
    (summable_norm_diagMul_of_summable_norm summable_norm_relativeCurvatureWeight)

theorem primeHodgeHistoryRelativeCurvatureOperator_isPositive :
    primeHodgeHistoryRelativeCurvatureOperator.IsPositive := by
  exact absoluteMatrixOperator_diagMul_isPositive_ofReal
    PrimeHodgeHistory.relativeCurvatureWeight
    summable_norm_relativeCurvatureWeight
    (fun n => (PrimeHodgeHistory.relativeCurvatureWeight_pos n).le)

theorem primeHodgeHistoryRelativeCurvatureOperator_apply_basis (n : ℕ) :
    primeHodgeHistoryRelativeCurvatureOperator (HilbertSchmidt.lpBasis ℕ n) =
      (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ) •
        HilbertSchmidt.lpBasis ℕ n := by
  exact absoluteMatrixOperator_diagMul_apply_basis _
    summable_norm_relativeCurvatureWeight n

theorem inner_basis_primeHodgeHistoryRelativeCurvatureOperator_basis (n : ℕ) :
    inner ℂ (HilbertSchmidt.lpBasis ℕ n)
      (primeHodgeHistoryRelativeCurvatureOperator (HilbertSchmidt.lpBasis ℕ n)) =
      (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ) := by
  rw [primeHodgeHistoryRelativeCurvatureOperator_apply_basis, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K,
    (HilbertSchmidt.lpBasis ℕ).orthonormal.norm_eq_one]
  simp

theorem opTrace_primeHodgeHistoryRelativeCurvatureOperator :
    ContinuousLinearMap.opTrace primeHodgeHistoryRelativeCurvatureOperator = 1 := by
  let b := HilbertSchmidt.lpBasis ℕ
  have hsum : Summable fun n =>
      inner ℂ (b n) (primeHodgeHistoryRelativeCurvatureOperator (b n)) := by
    exact (Complex.summable_ofReal.mpr
      PrimeHodgeHistory.summable_relativeCurvatureWeight).congr
      (fun n => (inner_basis_primeHodgeHistoryRelativeCurvatureOperator_basis n).symm)
  rw [opTrace_eq_tsum_basis_of_isPositive_of_summable_diagonal b
    primeHodgeHistoryRelativeCurvatureOperator_isPositive hsum]
  rw [tsum_congr inner_basis_primeHodgeHistoryRelativeCurvatureOperator_basis,
    ← Complex.ofReal_tsum, PrimeHodgeHistory.tsum_relativeCurvatureWeight]
  norm_num

theorem primeHodgeHistoryRelativeCurvatureOperator_eq_diagonalOperator :
    primeHodgeHistoryRelativeCurvatureOperator =
      diagonalOperator
        (fun n => (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ))
        (C := 1 / 3) (fun n => by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (PrimeHodgeHistory.relativeCurvatureWeight_pos n)]
          exact PrimeHodgeHistory.relativeCurvatureWeight_le_one_third n) := by
  rw [primeHodgeHistoryRelativeCurvatureOperator,
    absoluteMatrixOperator_diagMul_eq_diagonalOperator _
      summable_norm_relativeCurvatureWeight]
  ext f n
  simp only [diagonalOperator_apply]

theorem norm_primeHodgeHistoryRelativeCurvatureOperator :
    ‖primeHodgeHistoryRelativeCurvatureOperator‖ = 1 / 3 := by
  rw [primeHodgeHistoryRelativeCurvatureOperator_eq_diagonalOperator]
  apply norm_diagonalOperator_eq (m := 0)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (PrimeHodgeHistory.relativeCurvatureWeight_pos 0),
    PrimeHodgeHistory.relativeCurvatureWeight_zero]

theorem traceNorm_primeHodgeHistoryRelativeCurvatureOperator :
    traceNorm ArithmeticDilationHilbert primeHodgeHistoryRelativeCurvatureOperator = 1 := by
  rw [traceNorm_eq_re_opTrace_of_isPositive
    primeHodgeHistoryRelativeCurvatureOperator_memSchattenClass_one
    primeHodgeHistoryRelativeCurvatureOperator_isPositive,
    opTrace_primeHodgeHistoryRelativeCurvatureOperator]
  norm_num

/-- Relative curvature is the trace-class cancellation of two compact, non-trace-class
defect metrics. -/
theorem primeHodgeHistoryRelativeCurvatureOperator_eq_metric_sub :
    primeHodgeHistoryRelativeCurvatureOperator =
      primeHodgeHistoryOutgoingMetric - primeHodgeHistoryExitDefect := by
  rw [primeHodgeHistoryRelativeCurvatureOperator_eq_diagonalOperator]
  ext f n
  change (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ) * f n =
    (PrimeHodgeHistory.outgoingMetricWeight n : ℂ) * f n -
      (PrimeHodgeHistory.exitHazard n : ℂ) * f n
  rw [← sub_mul]
  have hweight : (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ) =
      (PrimeHodgeHistory.outgoingMetricWeight n : ℂ) -
        (PrimeHodgeHistory.exitHazard n : ℂ) := by
    exact_mod_cast
      (PrimeHodgeHistory.outgoing_sub_incoming_eq_relativeCurvatureWeight n).symm
  rw [hweight]

/-- The curvature operator is the positive self-commutator of the forced survival shift. -/
theorem primeHodgeHistoryRelativeCurvatureOperator_eq_selfCommutator :
    primeHodgeHistoryRelativeCurvatureOperator =
      ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift ∘L
          primeHodgeHistorySurvivalShift -
        primeHodgeHistorySurvivalShift ∘L
          ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift := by
  rw [primeHodgeHistoryRelativeCurvatureOperator_eq_metric_sub,
    primeHodgeHistoryOutgoingMetric_eq_adjoint_fracture,
    primeHodgeHistoryExitDefect_eq_adjoint_fracture]
  abel

theorem primeHodgeHistory_relativeCurvature_trace_index_integralNuclear :
    ContinuousLinearMap.opTrace primeHodgeHistoryRelativeCurvatureOperator =
        ((-primeHodgeHistorySurvivalShiftIndex : ℤ) : ℂ) ∧
      ContinuousLinearMap.opTrace primeHodgeHistoryRelativeCurvatureOperator =
        ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT := by
  rw [opTrace_primeHodgeHistoryRelativeCurvatureOperator,
    primeHodgeHistorySurvivalShiftIndex_eq_neg_one,
    primeHodgeHistoryIntegralNuclearDefect_closed.2.2.1]
  norm_num

/-- Unconditional closed certificate for the complete scalar relative-metric and
flux--curvature reconstruction theorem. -/
theorem primeHodgeHistoryRelativeCurvature_closed :
    primeHodgeHistoryOutgoingMetric.IsPositive ∧
      IsCompactOperator primeHodgeHistoryOutgoingMetric ∧
      ¬ MemSchattenClass 1 primeHodgeHistoryOutgoingMetric ∧
      primeHodgeHistoryExitDefect.IsPositive ∧
      IsCompactOperator primeHodgeHistoryExitDefect ∧
      ¬ MemSchattenClass 1 primeHodgeHistoryExitDefect ∧
      primeHodgeHistoryRelativeCurvatureOperator =
        primeHodgeHistoryOutgoingMetric - primeHodgeHistoryExitDefect ∧
      primeHodgeHistoryRelativeCurvatureOperator =
        ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift ∘L
            primeHodgeHistorySurvivalShift -
          primeHodgeHistorySurvivalShift ∘L
            ContinuousLinearMap.adjoint primeHodgeHistorySurvivalShift ∧
      primeHodgeHistoryRelativeCurvatureOperator.IsPositive ∧
      MemSchattenClass 1 primeHodgeHistoryRelativeCurvatureOperator ∧
      ContinuousLinearMap.opTrace primeHodgeHistoryRelativeCurvatureOperator = 1 ∧
      traceNorm ArithmeticDilationHilbert primeHodgeHistoryRelativeCurvatureOperator = 1 ∧
      ‖primeHodgeHistoryRelativeCurvatureOperator‖ = 1 / 3 ∧
      ContinuousLinearMap.opTrace primeHodgeHistoryRelativeCurvatureOperator =
        ((-primeHodgeHistorySurvivalShiftIndex : ℤ) : ℂ) ∧
      ContinuousLinearMap.opTrace primeHodgeHistoryRelativeCurvatureOperator =
        ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT ∧
      (∀ n, (∑' k, PrimeHodgeHistory.w (k + n)) = PrimeHodgeHistory.m n) ∧
      (∀ n,
        PrimeHodgeHistory.survivalRatio n =
          ∑ j ∈ Finset.range (n + 1),
            PrimeHodgeHistory.relativeCurvatureWeight j) ∧
      (∀ n,
        PrimeHodgeHistory.m n =
          ∏ j ∈ Finset.range n, PrimeHodgeHistory.survivalRatio j) ∧
      (∀ n,
        PrimeHodgeHistory.w n = PrimeHodgeHistory.m n *
          (1 - PrimeHodgeHistory.survivalRatio n)) := by
  exact ⟨primeHodgeHistoryOutgoingMetric_isPositive,
    primeHodgeHistoryOutgoingMetric_isCompactOperator,
    primeHodgeHistoryOutgoingMetric_not_memSchattenClass_one,
    primeHodgeHistoryIncomingMetric_isPositive,
    primeHodgeHistoryIncomingMetric_isCompactOperator,
    primeHodgeHistoryIncomingMetric_not_memSchattenClass_one,
    primeHodgeHistoryRelativeCurvatureOperator_eq_metric_sub,
    primeHodgeHistoryRelativeCurvatureOperator_eq_selfCommutator,
    primeHodgeHistoryRelativeCurvatureOperator_isPositive,
    primeHodgeHistoryRelativeCurvatureOperator_memSchattenClass_one,
    opTrace_primeHodgeHistoryRelativeCurvatureOperator,
    traceNorm_primeHodgeHistoryRelativeCurvatureOperator,
    norm_primeHodgeHistoryRelativeCurvatureOperator,
    primeHodgeHistory_relativeCurvature_trace_index_integralNuclear.1,
    primeHodgeHistory_relativeCurvature_trace_index_integralNuclear.2,
    PrimeHodgeHistory.tail_tsum_w,
    PrimeHodgeHistory.survivalRatio_eq_sum_range_relativeCurvatureWeight,
    PrimeHodgeHistory.m_eq_prod_survivalRatio,
    PrimeHodgeHistory.w_eq_m_mul_one_sub_survivalRatio⟩

end

end RHTower

import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.TraceRecovery
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.RootComparison
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison

/-! # Quantitative recovery of the critical operator from one fourth trace

The norm loss in the squared propagator is controlled by the Hilbert–Schmidt
mass in the omitted range. Operator monotonicity transfers that control to
the physical propagator.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

abbrev Propagator := {G : GasOp // G.IsPositive ∧ Conserving G}

def traceLoss (G : GasOp) : ℝ := (riemannZeta 2).re - (opTrace (G^4)).re

theorem critical_norm_le_one : ‖criticalOperator‖ ≤ 1 :=
  HTGeometry.LpDiagonal.norm_lpDiag_le _ 1 zero_le_one _

private theorem gram_pair_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) : ‖star T*T‖ = ‖T*star T‖ :=
  (CStarRing.norm_star_mul_self (x := T)).trans (CStarRing.norm_self_mul_star (x := T)).symm

/-- The positive square deficit is a Gram operator. Its squared norm is at most the trace loss. -/
theorem square_trace_stability (G : Propagator) :
    (criticalOperator^2-G.val^2).IsPositive ∧ ‖criticalOperator^2-G.val^2‖^2 ≤ traceLoss G.val := by
  let D := criticalOperator
  obtain ⟨U,hu,_⟩ := (full_isometry_iff G.val).mp G.property.2
  let Q := omitted U
  let T := Q*D
  have hD : star D = D := critical_isPositive.isSelfAdjoint.star_eq
  have hQ : star Q = Q := omitted_self U
  have hQQ : Q*Q = Q := omitted_idempotent U
  have hproj : IsStarProjection Q := ⟨hQQ,hQ⟩
  have hout : D^2-G.val^2 = D*Q*D := by
    change D^2-G.val^2 = D*(1-U.toContinuousLinearMap*star U.toContinuousLinearMap)*D
    rw [show G.val^2 = G.val*star G.val by rw [G.property.1.isSelfAdjoint.star_eq,pow_two],hu,star_mul,
      show star criticalOperator = criticalOperator from hD]
    change D^2 - (D*U.toContinuousLinearMap)*(star U.toContinuousLinearMap*D) = _
    noncomm_ring
  have hgram : D^2-G.val^2 = star T*T := by
    rw [hout]
    change D*Q*D = star (Q*D)*(Q*D)
    rw [star_mul,hD,hQ]
    calc
      D*Q*D = D*(Q*Q)*D := by rw [hQQ]
      _ = _ := by noncomm_ring
  have hother : T*star T = (Q*squareHeat.val)*Q := by
    change (Q*D)*star (Q*D) = (Q*D^2)*Q
    rw [star_mul,hD,hQ,pow_two]
    noncomm_ring
  have hn : ‖D^2-G.val^2‖ ≤ hsNorm (Q*squareHeat.val) := calc
    _ = ‖T*star T‖ := (congrArg norm hgram).trans (gram_pair_norm T)
    _ = ‖(Q*squareHeat.val)*Q‖ := congrArg norm hother
    _ ≤ ‖Q*squareHeat.val‖*‖Q‖ := norm_mul_le _ _
    _ ≤ ‖Q*squareHeat.val‖ := mul_le_of_le_one_right (norm_nonneg _) (IsStarProjection.norm_le Q hproj)
    _ ≤ _ := norm_le_hsNorm (squareHeat.property.2.comp_left Q)
  have h := fourth_trace_defect U
  rw [← hu,fourthMoment_of_positive G.property.1] at h
  have hl : hsNormSq (Q*squareHeat.val) ≤ traceLoss G.val :=
    (le_add_of_nonneg_right (hsNormSq_nonneg _)).trans_eq h.symm
  refine ⟨?_,(pow_le_pow_left₀ (norm_nonneg _) hn 2).trans ((sq_hsNorm _).le.trans hl)⟩
  change (D^2-G.val^2).IsPositive
  rw [hgram]
  exact isPositive_adjoint_comp_self T

/-- Every positive conserving propagator lies below critical heat, with fourth-power stability. -/
theorem trace_stability (G : Propagator) :
    (criticalOperator-G.val).IsPositive ∧ ‖criticalOperator-G.val‖ ≤ 1 ∧
      ‖criticalOperator-G.val‖^4 ≤ traceLoss G.val := by
  obtain ⟨hs,ht⟩ := square_trace_stability G
  obtain ⟨hp,hn,hg⟩ := positive_square_comparison critical_isPositive G.property.1 hs
  refine ⟨hp,hn.trans critical_norm_le_one,?_⟩
  rw [show (4:ℕ) = 2*2 from rfl,pow_mul]
  exact (pow_le_pow_left₀ (sq_nonneg _) hg 2).trans ht

#print axioms square_trace_stability
#print axioms trace_stability

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

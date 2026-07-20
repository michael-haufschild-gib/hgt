import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage

/-!
# BRST--Hodge master constraints

For a bounded operator `Q`, the BRST/Hodge Hamiltonian is the anticommutator

`H_Q = {Q, Q†} = Q†Q + QQ†`.

Its expectation is the sum of the squared `Q`- and `Q†`-residuals, so its kernel is exactly
`ker Q ∩ ker Q†`.  Thus one positive, automatically self-adjoint constraint packages the closed
and coclosed conditions.  When `Q² = 0`, the same Hamiltonian commutes with both supercharges and
is the square of both self-adjoint supercharges `Q + Q†` and `i(Q - Q†)`; the two supercharges
anticommute.  An off-diagonal corner `(1-P)AP` of an idempotent is automatically nilpotent, so
projection geometry supplies the BRST premise algebraically.

The final declarations feed this single constraint directly into the existing Ward-value and
two-sided constraint-ideal surfaces.  Nothing here introduces a time flow.
-/

namespace HTGeometry

section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The bounded BRST/Hodge Hamiltonian `H_Q = Q†Q + QQ†`. -/
noncomputable def brstHodgeHamiltonian (Q : E →L[𝕜] E) : E →L[𝕜] E :=
  quantumMasterConstraint Q + quantumMasterConstraint Q.adjoint

/-- The BRST/Hodge Hamiltonian written as the anticommutator of `Q` and `Q†`. -/
theorem brstHodgeHamiltonian_eq_adjoint_mul_add_mul_adjoint
    (Q : E →L[𝕜] E) :
    brstHodgeHamiltonian Q = Q.adjoint * Q + Q * Q.adjoint := by
  simp [brstHodgeHamiltonian, quantumMasterConstraint,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_adjoint]

/-- `H_Q` is self-adjoint for every bounded `Q`; no symmetry premise on `Q` is needed. -/
theorem brstHodgeHamiltonian_isSelfAdjoint (Q : E →L[𝕜] E) :
    IsSelfAdjoint (brstHodgeHamiltonian Q) := by
  exact (quantumMasterConstraint_isSelfAdjoint Q).add
    (quantumMasterConstraint_isSelfAdjoint Q.adjoint)

/-- The BRST/Hodge expectation is the sum of the two squared constraint residuals. -/
theorem re_inner_brstHodgeHamiltonian_eq_sum_normSq
    (Q : E →L[𝕜] E) (ψ : E) :
    RCLike.re (inner 𝕜 ψ (brstHodgeHamiltonian Q ψ)) =
      ‖Q ψ‖ ^ 2 + ‖Q.adjoint ψ‖ ^ 2 := by
  simp only [brstHodgeHamiltonian, ContinuousLinearMap.add_apply,
    inner_add_right, map_add]
  rw [re_inner_quantumMasterConstraint_eq_normSq,
    re_inner_quantumMasterConstraint_eq_normSq]

/-- Positivity of `H_Q` is automatic. -/
theorem re_inner_brstHodgeHamiltonian_nonneg
    (Q : E →L[𝕜] E) (ψ : E) :
    0 ≤ RCLike.re (inner 𝕜 ψ (brstHodgeHamiltonian Q ψ)) := by
  rw [re_inner_brstHodgeHamiltonian_eq_sum_normSq]
  positivity

/-- A vector is annihilated by `H_Q` exactly when both `Q` and `Q†` annihilate it. -/
theorem brstHodgeHamiltonian_apply_eq_zero_iff
    (Q : E →L[𝕜] E) (ψ : E) :
    brstHodgeHamiltonian Q ψ = 0 ↔ Q ψ = 0 ∧ Q.adjoint ψ = 0 := by
  constructor
  · intro hH
    have hsum : ‖Q ψ‖ ^ 2 + ‖Q.adjoint ψ‖ ^ 2 = 0 := by
      rw [← re_inner_brstHodgeHamiltonian_eq_sum_normSq Q ψ, hH]
      simp
    have hQsq : ‖Q ψ‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖Q ψ‖, sq_nonneg ‖Q.adjoint ψ‖]
    have hQasq : ‖Q.adjoint ψ‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖Q ψ‖, sq_nonneg ‖Q.adjoint ψ‖]
    exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp hQsq),
      norm_eq_zero.mp (sq_eq_zero_iff.mp hQasq)⟩
  · rintro ⟨hQ, hQa⟩
    simp [brstHodgeHamiltonian, quantumMasterConstraint, hQ, hQa]

/-- The single physical-state condition for `H_Q` is exactly simultaneous `Q`-closedness and
`Q†`-closedness. -/
theorem physicalState_brstHodgeHamiltonian_iff
    (Q : E →L[𝕜] E) (ψ : E) :
    GaloisForLFunctions.PhysicalState (brstHodgeHamiltonian Q).toLinearMap ψ ↔
      GaloisForLFunctions.PhysicalState Q.toLinearMap ψ ∧
        GaloisForLFunctions.PhysicalState Q.adjoint.toLinearMap ψ := by
  simpa only [GaloisForLFunctions.PhysicalState] using
    brstHodgeHamiltonian_apply_eq_zero_iff Q ψ

/-- A joint `Q`/`Q†` physical state gives a Ward value for one self-adjoint Hodge constraint. -/
theorem brstHodgeHamiltonian_WardValue_eq_zero
    (Q A : E →L[𝕜] E) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState Q.toLinearMap ψ ∧
      GaloisForLFunctions.PhysicalState Q.adjoint.toLinearMap ψ) :
    inner 𝕜 ψ (brstHodgeHamiltonian Q (A ψ)) = 0 := by
  exact constraintWardValue_eq_zero (brstHodgeHamiltonian Q) A
    (brstHodgeHamiltonian_isSelfAdjoint Q)
    ((physicalState_brstHodgeHamiltonian_iff Q ψ).mpr hψ)

/-- The corresponding Hodge-Hamiltonian commutator Ward value also vanishes. -/
theorem brstHodgeHamiltonian_commutatorWardValue_eq_zero
    (Q A : E →L[𝕜] E) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState Q.toLinearMap ψ ∧
      GaloisForLFunctions.PhysicalState Q.adjoint.toLinearMap ψ) :
    inner 𝕜 ψ
      (((brstHodgeHamiltonian Q * A - A * brstHodgeHamiltonian Q) : E →L[𝕜] E) ψ) = 0 := by
  exact constraintCommutatorWardValue_eq_zero (brstHodgeHamiltonian Q) A
    (brstHodgeHamiltonian_isSelfAdjoint Q)
    ((physicalState_brstHodgeHamiltonian_iff Q ψ).mpr hψ)

/-- Equality modulo the ideal generated by `H_Q` is invisible between jointly closed/coclosed
states. -/
theorem physicalMatrixElement_congr_mod_brstHodgeHamiltonianIdeal
    (Q A B L R : E →L[𝕜] E)
    (hmod : B = A +
      (brstHodgeHamiltonian Q * L + R * brstHodgeHamiltonian Q))
    {φ ψ : E}
    (hφ : GaloisForLFunctions.PhysicalState Q.toLinearMap φ ∧
      GaloisForLFunctions.PhysicalState Q.adjoint.toLinearMap φ)
    (hψ : GaloisForLFunctions.PhysicalState Q.toLinearMap ψ ∧
      GaloisForLFunctions.PhysicalState Q.adjoint.toLinearMap ψ) :
    inner 𝕜 φ (B ψ) = inner 𝕜 φ (A ψ) := by
  exact physicalMatrixElement_congr_mod_constraintTwoSidedIdeal
    (brstHodgeHamiltonian Q) A B L R
    (brstHodgeHamiltonian_isSelfAdjoint Q) hmod
    ((physicalState_brstHodgeHamiltonian_iff Q φ).mpr hφ)
    ((physicalState_brstHodgeHamiltonian_iff Q ψ).mpr hψ)

/-! ## Nilpotent supercharge algebra -/

omit [CompleteSpace E] in
/-- An off-diagonal corner of an idempotent is automatically nilpotent.  This is the static
projection value relation that turns a normal corner into a BRST charge without a separate
nilpotence hypothesis. -/
theorem offDiagonalProjectionCorner_sq_eq_zero
    (P A : E →L[𝕜] E) (hP2 : P * P = P) :
    ((1 - P) * A * P) * ((1 - P) * A * P) = 0 := by
  have hPcomp : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP2, sub_self]
  calc
    ((1 - P) * A * P) * ((1 - P) * A * P) =
        (1 - P) * A * (P * (1 - P)) * A * P := by
      simp only [mul_assoc]
    _ = 0 := by rw [hPcomp]; simp

/-- Nilpotence passes from `Q` to its adjoint. -/
theorem adjoint_mul_self_eq_zero_of_self_mul_self_eq_zero
    (Q : E →L[𝕜] E) (hQ : Q * Q = 0) :
    Q.adjoint * Q.adjoint = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint hQ
  simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint] using h

/-- Under the BRST nilpotence relation, the Hodge Hamiltonian commutes with `Q`. -/
theorem brstHodgeHamiltonian_mul_eq_mul_brstCharge
    (Q : E →L[𝕜] E) (hQ : Q * Q = 0) :
    brstHodgeHamiltonian Q * Q = Q * brstHodgeHamiltonian Q := by
  rw [brstHodgeHamiltonian_eq_adjoint_mul_add_mul_adjoint]
  simp only [add_mul, mul_add]
  have hleftzero : (Q.adjoint * Q) * Q = 0 := by
    rw [mul_assoc, hQ, mul_zero]
  have hrightzero : Q * (Q * Q.adjoint) = 0 := by
    rw [← mul_assoc, hQ, zero_mul]
  rw [hleftzero, hrightzero, zero_add, add_zero, mul_assoc]

/-- Under the same nilpotence relation, the Hodge Hamiltonian commutes with `Q†`. -/
theorem brstHodgeHamiltonian_mul_adjoint_eq_adjoint_mul
    (Q : E →L[𝕜] E) (hQ : Q * Q = 0) :
    brstHodgeHamiltonian Q * Q.adjoint = Q.adjoint * brstHodgeHamiltonian Q := by
  have hQa : Q.adjoint * Q.adjoint = 0 :=
    adjoint_mul_self_eq_zero_of_self_mul_self_eq_zero Q hQ
  simpa [brstHodgeHamiltonian, quantumMasterConstraint,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_adjoint, add_comm] using
    (brstHodgeHamiltonian_mul_eq_mul_brstCharge (Q := Q.adjoint) hQa)

/-! ## Green operator and Hodge chain homotopy -/

/-- If a Green operator commutes with the BRST charge, multiplying the Hodge Hamiltonian by it
is already the standard chain-homotopy anticommutator with `Q†G`. -/
theorem brstHodgeHamiltonian_mul_green_eq_chainHomotopy
    (Q G : E →L[𝕜] E) (hQG : Q * G = G * Q) :
    brstHodgeHamiltonian Q * G =
      Q * (Q.adjoint * G) + (Q.adjoint * G) * Q := by
  rw [brstHodgeHamiltonian_eq_adjoint_mul_add_mul_adjoint, add_mul]
  calc
    (Q.adjoint * Q) * G + (Q * Q.adjoint) * G =
        Q.adjoint * (Q * G) + Q * (Q.adjoint * G) := by
      simp only [mul_assoc]
    _ = Q.adjoint * (G * Q) + Q * (Q.adjoint * G) := by rw [hQG]
    _ = Q * (Q.adjoint * G) + (Q.adjoint * G) * Q := by
      rw [← mul_assoc]
      exact add_comm _ _

/-- For self-adjoint operators, a left Green equation is automatically the corresponding right
Green equation.  This is the operator-adjoint value relation behind the usual self-adjoint Hodge
Green operator: only one of `H G = 1 - P` and `G H = 1 - P` needs to be supplied. -/
theorem rightGreen_eq_of_leftGreen_of_selfAdjoint
    (H G P : E →L[𝕜] E)
    (hH : IsSelfAdjoint H) (hG : IsSelfAdjoint G) (hP : IsSelfAdjoint P)
    (hHG : H * G = 1 - P) :
    G * H = 1 - P := by
  have hstar := congrArg star hHG
  simpa only [star_mul, star_sub, star_one, hH.star_eq, hG.star_eq, hP.star_eq]
    using hstar

/-- The two Green equations are equivalent once the Hamiltonian, Green operator, and harmonic
projection are self-adjoint. -/
theorem leftGreen_eq_iff_rightGreen_of_selfAdjoint
    (H G P : E →L[𝕜] E)
    (hH : IsSelfAdjoint H) (hG : IsSelfAdjoint G) (hP : IsSelfAdjoint P) :
    H * G = 1 - P ↔ G * H = 1 - P := by
  constructor
  · exact rightGreen_eq_of_leftGreen_of_selfAdjoint H G P hH hG hP
  · exact rightGreen_eq_of_leftGreen_of_selfAdjoint G H P hG hH hP

/-- A two-sided Green inverse on the complement of a harmonic projection automatically commutes
with a nilpotent BRST charge, provided the harmonic sector is annihilated on both sides.  This
removes a separate Green/charge commutation premise from the Hodge relation. -/
theorem brstGreen_commutes_charge
    (Q G P : E →L[𝕜] E)
    (hQ : Q * Q = 0)
    (hHG : brstHodgeHamiltonian Q * G = 1 - P)
    (hGH : G * brstHodgeHamiltonian Q = 1 - P)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    Q * G = G * Q := by
  have hHQ := brstHodgeHamiltonian_mul_eq_mul_brstCharge Q hQ
  have hleftQ : (1 - P) * Q = Q := by rw [sub_mul, one_mul, hPQ, sub_zero]
  have hrightQ : Q * (1 - P) = Q := by rw [mul_sub, mul_one, hQP, sub_zero]
  calc
    Q * G = ((1 - P) * Q) * G := by rw [hleftQ]
    _ = (G * brstHodgeHamiltonian Q) * Q * G := by rw [hGH]
    _ = G * (brstHodgeHamiltonian Q * Q) * G := by
      simp only [mul_assoc]
    _ = G * (Q * brstHodgeHamiltonian Q) * G := by rw [hHQ]
    _ = G * Q * (brstHodgeHamiltonian Q * G) := by
      simp only [mul_assoc]
    _ = G * Q * (1 - P) := by rw [hHG]
    _ = G * Q := by rw [mul_assoc, hrightQ]

/-- A self-adjoint Green operator and self-adjoint harmonic projection reduce the two-sided Green
premise to one equation.  The missing right equation is its adjoint, so BRST/Green commutation
follows without asking the source to prove it separately. -/
theorem brstGreen_commutes_charge_of_selfAdjoint
    (Q G P : E →L[𝕜] E)
    (hQ : Q * Q = 0)
    (hG : IsSelfAdjoint G) (hP : IsSelfAdjoint P)
    (hHG : brstHodgeHamiltonian Q * G = 1 - P)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    Q * G = G * Q := by
  have hGH : G * brstHodgeHamiltonian Q = 1 - P :=
    rightGreen_eq_of_leftGreen_of_selfAdjoint
      (brstHodgeHamiltonian Q) G P
      (brstHodgeHamiltonian_isSelfAdjoint Q) hG hP hHG
  exact brstGreen_commutes_charge Q G P hQ hHG hGH hPQ hQP

/-- **Hodge relation from the master constraint.**  Under the two Green equations and harmonic
annihilation laws, the complement of the harmonic projection is the chain anticommutator
`Qh + hQ` with the canonical homotopy `h = Q†G`.  This is the operator identity needed by
cohomological trace compression; constructing the source-specific `P` and `G` remains separate. -/
theorem one_sub_eq_brstChainHomotopy_of_green
    (Q G P : E →L[𝕜] E)
    (hQ : Q * Q = 0)
    (hHG : brstHodgeHamiltonian Q * G = 1 - P)
    (hGH : G * brstHodgeHamiltonian Q = 1 - P)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    1 - P = Q * (Q.adjoint * G) + (Q.adjoint * G) * Q := by
  rw [← hHG]
  exact brstHodgeHamiltonian_mul_green_eq_chainHomotopy Q G
    (brstGreen_commutes_charge Q G P hQ hHG hGH hPQ hQP)

/-- **One-equation self-adjoint Hodge relation.**  For a self-adjoint Green operator and harmonic
projection, the single Green equation `H_Q G = 1 - P` supplies its right-handed mate by adjunction.
Thus the BRST chain homotopy needs one fewer source hypothesis than the general two-sided theorem. -/
theorem one_sub_eq_brstChainHomotopy_of_selfAdjoint_green
    (Q G P : E →L[𝕜] E)
    (hQ : Q * Q = 0)
    (hG : IsSelfAdjoint G) (hP : IsSelfAdjoint P)
    (hHG : brstHodgeHamiltonian Q * G = 1 - P)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    1 - P = Q * (Q.adjoint * G) + (Q.adjoint * G) * Q := by
  have hGH : G * brstHodgeHamiltonian Q = 1 - P :=
    rightGreen_eq_of_leftGreen_of_selfAdjoint
      (brstHodgeHamiltonian Q) G P
      (brstHodgeHamiltonian_isSelfAdjoint Q) hG hP hHG
  exact one_sub_eq_brstChainHomotopy_of_green Q G P hQ hHG hGH hPQ hQP

/-- The self-adjoint Hodge--Dirac supercharge `D_Q = Q + Q†`. -/
noncomputable def brstHodgeDiracOperator (Q : E →L[𝕜] E) : E →L[𝕜] E :=
  Q + Q.adjoint

/-- `D_Q` is self-adjoint without any nilpotence premise. -/
theorem brstHodgeDiracOperator_isSelfAdjoint (Q : E →L[𝕜] E) :
    IsSelfAdjoint (brstHodgeDiracOperator Q) := by
  simpa [brstHodgeDiracOperator, ContinuousLinearMap.star_eq_adjoint] using
    (IsSelfAdjoint.add_star_self Q)

/-- If `Q² = 0`, then the Hodge Hamiltonian is exactly the square of `D_Q`. -/
theorem brstHodgeDiracOperator_sq_eq_hamiltonian
    (Q : E →L[𝕜] E) (hQ : Q * Q = 0) :
    brstHodgeDiracOperator Q * brstHodgeDiracOperator Q =
      brstHodgeHamiltonian Q := by
  have hQa : Q.adjoint * Q.adjoint = 0 :=
    adjoint_mul_self_eq_zero_of_self_mul_self_eq_zero Q hQ
  rw [brstHodgeDiracOperator, brstHodgeHamiltonian_eq_adjoint_mul_add_mul_adjoint]
  calc
    (Q + Q.adjoint) * (Q + Q.adjoint) =
        Q * Q + Q * Q.adjoint + Q.adjoint * Q + Q.adjoint * Q.adjoint := by
      noncomm_ring
    _ = Q * Q.adjoint + Q.adjoint * Q := by rw [hQ, hQa]; simp
    _ = Q.adjoint * Q + Q * Q.adjoint := add_comm _ _

end

section Complex

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The second Hermitian `N = 2` supercharge `J_Q = i(Q - Q†)`. -/
noncomputable def brstHodgeCoDiracOperator (Q : E →L[ℂ] E) : E →L[ℂ] E :=
  Complex.I • (Q - Q.adjoint)

/-- The second supercharge is self-adjoint without a nilpotence premise. -/
theorem brstHodgeCoDiracOperator_isSelfAdjoint (Q : E →L[ℂ] E) :
    IsSelfAdjoint (brstHodgeCoDiracOperator Q) := by
  unfold brstHodgeCoDiracOperator
  change star (Complex.I • (Q - Q.adjoint)) = _
  rw [star_smul, star_sub]
  rw [show star (Complex.I : ℂ) = -Complex.I by exact Complex.conj_I]
  change -Complex.I • (Q.adjoint - Q.adjoint.adjoint) = _
  rw [ContinuousLinearMap.adjoint_adjoint]
  module

/-- For a nilpotent complex supercharge, `i(Q-Q†)` has the same square as `Q+Q†`: the
BRST--Hodge Hamiltonian. -/
theorem brstHodgeCoDiracOperator_sq_eq_hamiltonian
    (Q : E →L[ℂ] E) (hQ : Q * Q = 0) :
    brstHodgeCoDiracOperator Q * brstHodgeCoDiracOperator Q =
      brstHodgeHamiltonian Q := by
  have hQa : Q.adjoint * Q.adjoint = 0 :=
    adjoint_mul_self_eq_zero_of_self_mul_self_eq_zero Q hQ
  have hskew :
      (Q - Q.adjoint) * (Q - Q.adjoint) = -brstHodgeHamiltonian Q := by
    rw [brstHodgeHamiltonian_eq_adjoint_mul_add_mul_adjoint]
    noncomm_ring [hQ, hQa]
  unfold brstHodgeCoDiracOperator
  calc
    (Complex.I • (Q - Q.adjoint)) * (Complex.I • (Q - Q.adjoint)) =
        Complex.I • (Complex.I •
          ((Q - Q.adjoint) * (Q - Q.adjoint))) := by
      rw [smul_mul_assoc, mul_smul_comm]
    _ = -((Q - Q.adjoint) * (Q - Q.adjoint)) := by
      rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    _ = brstHodgeHamiltonian Q := by rw [hskew, neg_neg]

/-- The two Hermitian supercharges have identical statewise norm energy. -/
theorem norm_brstHodgeCoDiracOperator_apply_sq_eq_norm_diracOperator_apply_sq
    (Q : E →L[ℂ] E) (hQ : Q * Q = 0) (psi : E) :
    ‖brstHodgeCoDiracOperator Q psi‖ ^ 2 =
      ‖brstHodgeDiracOperator Q psi‖ ^ 2 := by
  have hCoAdj :
      ContinuousLinearMap.adjoint (brstHodgeCoDiracOperator Q) =
        brstHodgeCoDiracOperator Q := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (brstHodgeCoDiracOperator_isSelfAdjoint Q).star_eq
  have hDiracAdj :
      ContinuousLinearMap.adjoint (brstHodgeDiracOperator Q) =
        brstHodgeDiracOperator Q := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (brstHodgeDiracOperator_isSelfAdjoint Q).star_eq
  have hmasterCo :
      quantumMasterConstraint (brstHodgeCoDiracOperator Q) =
        brstHodgeCoDiracOperator Q * brstHodgeCoDiracOperator Q := by
    rw [quantumMasterConstraint]
    change ContinuousLinearMap.adjoint (brstHodgeCoDiracOperator Q) *
      brstHodgeCoDiracOperator Q = _
    rw [hCoAdj]
  have hmasterDirac :
      quantumMasterConstraint (brstHodgeDiracOperator Q) =
        brstHodgeDiracOperator Q * brstHodgeDiracOperator Q := by
    rw [quantumMasterConstraint]
    change ContinuousLinearMap.adjoint (brstHodgeDiracOperator Q) *
      brstHodgeDiracOperator Q = _
    rw [hDiracAdj]
  have hmasterEq :
      quantumMasterConstraint (brstHodgeCoDiracOperator Q) =
        quantumMasterConstraint (brstHodgeDiracOperator Q) := by
    rw [hmasterCo, hmasterDirac,
      brstHodgeCoDiracOperator_sq_eq_hamiltonian Q hQ,
      brstHodgeDiracOperator_sq_eq_hamiltonian Q hQ]
  calc
    ‖brstHodgeCoDiracOperator Q psi‖ ^ 2 =
        RCLike.re (inner ℂ psi
          (quantumMasterConstraint (brstHodgeCoDiracOperator Q) psi)) :=
      (re_inner_quantumMasterConstraint_eq_normSq
        (brstHodgeCoDiracOperator Q) psi).symm
    _ = RCLike.re (inner ℂ psi
        (quantumMasterConstraint (brstHodgeDiracOperator Q) psi)) := by
      rw [hmasterEq]
    _ = ‖brstHodgeDiracOperator Q psi‖ ^ 2 :=
      re_inner_quantumMasterConstraint_eq_normSq (brstHodgeDiracOperator Q) psi

/-- The two Hermitian `N = 2` supercharges anticommute. -/
theorem brstHodgeDiracOperator_anticommutes_coDiracOperator
    (Q : E →L[ℂ] E) (hQ : Q * Q = 0) :
    brstHodgeDiracOperator Q * brstHodgeCoDiracOperator Q +
        brstHodgeCoDiracOperator Q * brstHodgeDiracOperator Q = 0 := by
  have hQa : Q.adjoint * Q.adjoint = 0 :=
    adjoint_mul_self_eq_zero_of_self_mul_self_eq_zero Q hQ
  have hanti :
      (Q + Q.adjoint) * (Q - Q.adjoint) +
          (Q - Q.adjoint) * (Q + Q.adjoint) = 0 := by
    noncomm_ring [hQ, hQa]
  unfold brstHodgeDiracOperator brstHodgeCoDiracOperator
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, hanti, smul_zero]

end Complex

end HTGeometry

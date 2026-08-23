import GaloisForLFunctions.RHTower.SoninBurnolConductorReflection

/-!
# The conductor commutator is translation covariant

The half-line cutoffs of the logarithmic Sonin model are translates of one another,
`P_τ = U_τ P_0 U_τ⁻¹`, and the real-place conductor is dilation invariant, hence commutes with
those translations.  Therefore the conductor commutator at aperture `τ` is the conjugate of the
one at aperture `0`, and since the conjugating map is unitary, all of them have the same norm.

The algebra is unit-free: only invertibility of the conjugating element and commutation of the
conductor with it are used.
-/

noncomputable section

namespace RHTower

variable {R : Type*} [Ring R]

/-- Conjugating an element by an invertible pair. -/
def conjBy (U V B : R) : R := U * B * V

/-- **Translation covariance of a commutator.**  If `A` commutes with `U`, and `V` is a two-sided
inverse of `U`, then the commutator of `A` with the conjugate of `B` is the conjugate of the
commutator of `A` with `B`. -/
theorem ccmCommutator_conjBy
    (A B U V : R) (hUV : U * V = 1) (hVU : V * U = 1) (hAU : A * U = U * A) :
    ccmCommutator A (conjBy U V B) = conjBy U V (ccmCommutator A B) := by
  have hVA : V * A = A * V := by
    calc V * A = V * A * (U * V) := by rw [hUV, mul_one]
      _ = V * (A * U) * V := by noncomm_ring
      _ = V * (U * A) * V := by rw [hAU]
      _ = (V * U) * A * V := by noncomm_ring
      _ = A * V := by rw [hVU, one_mul]
  rw [ccmCommutator, ccmCommutator, conjBy, conjBy]
  calc A * (U * B * V) - U * B * V * A
      = (A * U) * B * V - U * B * (V * A) := by noncomm_ring
    _ = (U * A) * B * V - U * B * (A * V) := by rw [hAU, hVA]
    _ = U * (A * B - B * A) * V := by noncomm_ring

/-- The conductor commutes with any element the position channel and the reflection both commute
with. -/
theorem burnolConductor_commute
    (M J U : R) (hMU : M * U = U * M) (hJU : J * U = U * J) :
    burnolConductor M J * U = U * burnolConductor M J := by
  rw [burnolConductor]
  calc (M + J * M * J) * U = M * U + J * M * (J * U) := by noncomm_ring
    _ = U * M + J * M * (U * J) := by rw [hMU, hJU]
    _ = U * M + J * (M * U) * J := by noncomm_ring
    _ = U * M + J * (U * M) * J := by rw [hMU]
    _ = U * M + (J * U) * M * J := by noncomm_ring
    _ = U * M + (U * J) * M * J := by rw [hJU]
    _ = U * (M + J * M * J) := by noncomm_ring

/-- **Card equation (3), algebraic form.**  The conductor commutator at a translated cutoff is the
conjugate of the one at the base cutoff. -/
theorem ccmCommutator_burnolConductor_translated
    (M J A U V : R) (hUV : U * V = 1) (hVU : V * U = 1)
    (hMU : M * U = U * M) (hJU : J * U = U * J) :
    ccmCommutator (burnolConductor M J) (conjBy U V A)
      = conjBy U V (ccmCommutator (burnolConductor M J) A) :=
  ccmCommutator_conjBy _ _ _ _ hUV hVU (burnolConductor_commute M J U hMU hJU)

/-! ## The norm is aperture independent -/

section Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Conjugation by a surjective isometry preserves the operator norm. -/
theorem norm_conjBy_isometry (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    ‖(U.toContinuousLinearEquiv : H →L[ℂ] H) * T
        * ((U.symm).toContinuousLinearEquiv : H →L[ℂ] H)‖ = ‖T‖ := by
  have h1 : ∀ y : H, ‖((U.symm).toContinuousLinearEquiv : H →L[ℂ] H) y‖ = ‖y‖ :=
    fun y => U.symm.norm_map y
  have h2 : ∀ y : H, ‖(U.toContinuousLinearEquiv : H →L[ℂ] H) y‖ = ‖y‖ :=
    fun y => U.norm_map y
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (fun x => ?_)
    calc ‖((U.toContinuousLinearEquiv : H →L[ℂ] H) * T
            * ((U.symm).toContinuousLinearEquiv : H →L[ℂ] H)) x‖
        = ‖T (((U.symm).toContinuousLinearEquiv : H →L[ℂ] H) x)‖ := by
          simp
      _ ≤ ‖T‖ * ‖((U.symm).toContinuousLinearEquiv : H →L[ℂ] H) x‖ :=
          T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := by rw [h1]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
    set S : H →L[ℂ] H := (U.toContinuousLinearEquiv : H →L[ℂ] H) * T
      * ((U.symm).toContinuousLinearEquiv : H →L[ℂ] H) with hS
    have hTx : T x = ((U.symm).toContinuousLinearEquiv : H →L[ℂ] H)
        (S ((U.toContinuousLinearEquiv : H →L[ℂ] H) x)) := by
      simp [hS]
    calc ‖T x‖ = ‖S ((U.toContinuousLinearEquiv : H →L[ℂ] H) x)‖ := by
          rw [hTx, h1]
      _ ≤ ‖S‖ * ‖(U.toContinuousLinearEquiv : H →L[ℂ] H) x‖ := S.le_opNorm _
      _ = ‖S‖ * ‖x‖ := by rw [h2]

end Operator

end RHTower

import GaloisForLFunctions.HTGeometry.FiniteClockStarKadison
import GaloisForLFunctions.HTGeometry.FiniteClockObservableFixedPoint

/-!
# Multiplicative domain of a finite quantum-clock twirl

A finite cyclic unitary twirl is a conditional expectation onto the clock commutant.  This file
formalizes its operator-valued star-Kadison identity and faithfulness:

`Phi(X† X) - Phi(X)† Phi(X) = Phi((X - Phi X)† (X - Phi X))`,

and the right-hand side vanishes exactly when `X` commutes with the clock.  Thus the complete
multiplicative-domain criterion holds for arbitrary bounded operators, without self-adjointness,
positivity, or a chosen stationary state.

The result is the finite cyclic form of the multiplicative-domain theory of unital quantum
channels.  It is static: `Phi` records which observables survive the clock's conditional
expectation and does not propagate a state in time.
-/

namespace HTGeometry

noncomputable section

open scoped BigOperators

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Finite cyclic observable twirling is star preserving.  This is the operator-algebraic
ingredient that upgrades the existing self-adjoint Kadison identity to arbitrary operators. -/
theorem finiteCyclicObservableTwirl_adjoint
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) :
    (finiteCyclicObservableTwirl U X N).adjoint =
      finiteCyclicObservableTwirl U X.adjoint N := by
  rw [finiteCyclicObservableTwirl, finiteCyclicObservableTwirl]
  change star (((N : 𝕜)⁻¹) • finiteCyclicObservableTwirlNumerator U X N) = _
  rw [star_smul]
  have hscalar : star ((N : 𝕜)⁻¹) = (N : 𝕜)⁻¹ := by simp
  rw [hscalar]
  congr 1
  rw [finiteCyclicObservableTwirlNumerator_eq_sum,
    finiteCyclicObservableTwirlNumerator_eq_sum]
  let adj : (E →L[𝕜] E) ≃ₗᵢ⋆[𝕜] (E →L[𝕜] E) :=
    ContinuousLinearMap.adjoint
  change adj (∑ k ∈ Finset.range N, U ^ k * X * U ^ (N - k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := Nat.le_of_lt (Finset.mem_range.mp hk)
  have hleft := adjoint_pow_eq_period_sub_of_periodic_isometry
    U N k hN hkN hadjoint_mul hperiod
  have hright := adjoint_pow_eq_period_sub_of_periodic_isometry
    U N (N - k) hN (Nat.sub_le N k) hadjoint_mul hperiod
  rw [Nat.sub_sub_self hkN] at hright
  change ContinuousLinearMap.adjoint
      (((U ^ k) ∘L X) ∘L (U ^ (N - k))) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    hleft, hright]
  rfl

/-- **Operator-valued conditional variance identity.**  The star-Kadison defect is exactly the
clock twirl of the master constraint of the erased observable component. -/
theorem finiteCyclicObservableTwirlStarKadisonDefect_eq_twirl_quantumMasterConstraint
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) :
    finiteCyclicObservableTwirlStarKadisonDefect U X N =
      finiteCyclicObservableTwirl U
        (quantumMasterConstraint
          (X - finiteCyclicObservableTwirl U X N)) N := by
  let M : E →L[𝕜] E := finiteCyclicObservableTwirl U X N
  have hMcomm : U * M = M * U :=
    finiteCyclicObservableTwirl_commutes U X N hperiod
  have hPhiAdj : finiteCyclicObservableTwirl U X.adjoint N = M.adjoint := by
    exact (finiteCyclicObservableTwirl_adjoint U X N hN hadjoint_mul hperiod).symm
  have hMadjcomm : U * M.adjoint = M.adjoint * U := by
    rw [← hPhiAdj]
    exact finiteCyclicObservableTwirl_commutes U X.adjoint N hperiod
  have hright : finiteCyclicObservableTwirl U (X.adjoint * M) N = M.adjoint * M := by
    rw [finiteCyclicObservableTwirl_mul_right_of_commutes U X.adjoint M N hMcomm,
      hPhiAdj]
  have hleft : finiteCyclicObservableTwirl U (M.adjoint * X) N = M.adjoint * M := by
    rw [finiteCyclicObservableTwirl_mul_left_of_commutes U X M.adjoint N hMadjcomm]
  have hprodcomm : U * (M.adjoint * M) = (M.adjoint * M) * U := by
    calc
      U * (M.adjoint * M) = (U * M.adjoint) * M := (mul_assoc _ _ _).symm
      _ = (M.adjoint * U) * M := by rw [hMadjcomm]
      _ = M.adjoint * (U * M) := mul_assoc _ _ _
      _ = M.adjoint * (M * U) := by rw [hMcomm]
      _ = (M.adjoint * M) * U := (mul_assoc _ _ _).symm
  have hprod : finiteCyclicObservableTwirl U (M.adjoint * M) N = M.adjoint * M :=
    finiteCyclicObservableTwirl_eq_self_of_commutes U (M.adjoint * M) N
      hN hperiod hprodcomm
  have hexpand :
      (X - M).adjoint * (X - M) =
        X.adjoint * X - X.adjoint * M - M.adjoint * X + M.adjoint * M := by
    simp only [map_sub]
    noncomm_ring
  rw [finiteCyclicObservableTwirlStarKadisonDefect]
  change finiteCyclicObservableTwirl U (X.adjoint * X) N - M.adjoint * M = _
  change finiteCyclicObservableTwirl U (X.adjoint * X) N - M.adjoint * M =
    finiteCyclicObservableTwirl U ((X - M).adjoint * (X - M)) N
  rw [hexpand,
    finiteCyclicObservableTwirl_add U
      (X.adjoint * X - X.adjoint * M - M.adjoint * X) (M.adjoint * M) N,
    finiteCyclicObservableTwirl_sub U
      (X.adjoint * X - X.adjoint * M) (M.adjoint * X) N,
    finiteCyclicObservableTwirl_sub U (X.adjoint * X) (X.adjoint * M) N,
    hright, hleft, hprod]
  noncomm_ring

/-- Exact orbit-energy formula behind faithfulness of the finite clock conditional expectation.
Every summand is a squared master-constraint residual. -/
theorem re_inner_finiteCyclicObservableTwirlNumerator_quantumMasterConstraint_eq_sum_normSq
    (U D : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) (ψ : E) :
    RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlNumerator U (quantumMasterConstraint D) N ψ)) =
      ∑ k ∈ Finset.range N, ‖D ((U ^ (N - k)) ψ)‖ ^ 2 := by
  rw [finiteCyclicObservableTwirlNumerator_eq_sum]
  simp only [quantumMasterConstraint, _root_.sum_apply, inner_sum, map_sum,
    ContinuousLinearMap.mul_def]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := Nat.le_of_lt (Finset.mem_range.mp hk)
  have hpowAdj := adjoint_pow_eq_period_sub_of_periodic_isometry
    U N k hN hkN hadjoint_mul hperiod
  simp only [ContinuousLinearMap.comp_apply]
  have hinter :
      inner 𝕜 ψ ((U ^ k) (D.adjoint (D ((U ^ (N - k)) ψ)))) =
        inner 𝕜 ((U ^ k).adjoint ψ) (D.adjoint (D ((U ^ (N - k)) ψ))) :=
    (ContinuousLinearMap.adjoint_inner_left (U ^ k)
      (D.adjoint (D ((U ^ (N - k)) ψ))) ψ).symm
  rw [hinter, hpowAdj]
  simpa only using
    (D.apply_norm_sq_eq_inner_adjoint_right ((U ^ (N - k)) ψ)).symm

/-- **Faithfulness of finite clock twirling on positive effects.**  Twirling a master constraint
can vanish only when the underlying residual operator already vanishes. -/
theorem finiteCyclicObservableTwirl_quantumMasterConstraint_eq_zero_iff
    (U D : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) :
    finiteCyclicObservableTwirl U (quantumMasterConstraint D) N = 0 ↔ D = 0 := by
  constructor
  · intro htwirl
    have hscalar : ((N : 𝕜)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hN)
    have hnum : finiteCyclicObservableTwirlNumerator U (quantumMasterConstraint D) N = 0 := by
      rw [finiteCyclicObservableTwirl] at htwirl
      exact (smul_eq_zero.mp htwirl).resolve_left hscalar
    apply ContinuousLinearMap.ext
    intro ψ
    have hsum :
        (∑ k ∈ Finset.range N, ‖D ((U ^ (N - k)) ψ)‖ ^ 2) = 0 := by
      rw [← re_inner_finiteCyclicObservableTwirlNumerator_quantumMasterConstraint_eq_sum_normSq
        U D N hN hadjoint_mul hperiod ψ, hnum]
      simp
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => sq_nonneg ‖D ((U ^ (N - k)) ψ)‖)).mp hsum
      0 (Finset.mem_range.mpr (Nat.pos_of_ne_zero hN))
    have hnorm : ‖D ψ‖ ^ 2 = 0 := by
      simpa [hperiod] using hzero
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  · rintro rfl
    rw [finiteCyclicObservableTwirl, finiteCyclicObservableTwirlNumerator_eq_sum]
    simp [quantumMasterConstraint]

/-- The star-Kadison defect vanishes exactly when no observable component is erased by the
finite clock. -/
theorem finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_twirl_fixed
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) :
    finiteCyclicObservableTwirlStarKadisonDefect U X N = 0 ↔
      finiteCyclicObservableTwirl U X N = X := by
  rw [finiteCyclicObservableTwirlStarKadisonDefect_eq_twirl_quantumMasterConstraint
      U X N hN hadjoint_mul hperiod,
    finiteCyclicObservableTwirl_quantumMasterConstraint_eq_zero_iff U
      (X - finiteCyclicObservableTwirl U X N) N hN hadjoint_mul hperiod,
    sub_eq_zero]
  exact eq_comm

/-- **Finite-clock multiplicative-domain theorem.**  For arbitrary bounded `X`, zero complete
conditional variance is equivalent to membership in the clock commutant. -/
theorem finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_commutes
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) :
    finiteCyclicObservableTwirlStarKadisonDefect U X N = 0 ↔
      U * X = X * U := by
  rw [finiteCyclicObservableTwirlStarKadisonDefect_eq_twirl_quantumMasterConstraint
      U X N hN hadjoint_mul hperiod,
    finiteCyclicObservableTwirl_quantumMasterConstraint_eq_zero_iff U
      (X - finiteCyclicObservableTwirl U X N) N hN hadjoint_mul hperiod]
  exact sub_finiteCyclicObservableTwirl_eq_zero_iff_commutes U X N hN hperiod

end

end HTGeometry

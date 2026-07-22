import GaloisForLFunctions.HTGeometry.QuantumConstraintWard
import Mathlib.Algebra.Ring.GeomSum

/-!
# Master constraints and finite cyclic group averaging

For a bounded gauge step `U` of finite period `N`, the orbit sum

`S_N = 1 + U + ... + U^(N-1)`

satisfies `(U - 1) * S_N = U^N - 1`.  Thus `U^N = 1` makes every averaged
kinematic vector a physical vector for the static constraint `U - 1`.  If
`N ≠ 0`, the normalized average is an idempotent whose fixed vectors are
exactly the physical vectors.

This is the finite-group algebra behind group averaging in refined algebraic
quantization.  It constructs constraint solutions without introducing a time
flow.  Before constructing the average, the file also formalizes the bounded
master constraint `C†C`: it has the same kernel as `C` and is automatically
self-adjoint.  The final theorems feed both relations directly into the
existing Ward-value and constraint-ideal surfaces.
-/

open scoped BigOperators

namespace HTGeometry

section MasterConstraint

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The positive effect `C†C` of an arbitrary rectangular Hilbert-space channel vanishes
exactly when the channel vanishes.  This is the nondegeneracy law used by Kraus effects,
including channels whose input and output spaces differ. -/
theorem adjoint_comp_self_eq_zero_iff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (C : E →L[𝕜] F) :
    C.adjoint ∘L C = 0 ↔ C = 0 := by
  constructor
  · intro heffect
    apply ContinuousLinearMap.ext
    intro ψ
    have hnormSq : ‖C ψ‖ ^ 2 = 0 := by
      calc
        ‖C ψ‖ ^ 2 =
            RCLike.re (inner 𝕜 ψ ((C.adjoint ∘L C) ψ)) := by
          exact C.apply_norm_sq_eq_inner_adjoint_right ψ
        _ = 0 := by rw [heffect]; simp
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)
  · rintro rfl
    simp

/-- Equivalently, passing from any rectangular channel to its positive input effect preserves
nondegeneracy exactly. -/
theorem adjoint_comp_self_ne_zero_iff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (C : E →L[𝕜] F) :
    C.adjoint ∘L C ≠ 0 ↔ C ≠ 0 :=
  not_congr (adjoint_comp_self_eq_zero_iff C)

/-- The bounded quantum master constraint associated with `C`: `C† C`. -/
noncomputable def quantumMasterConstraint (C : E →L[𝕜] E) : E →L[𝕜] E :=
  C.adjoint ∘L C

/-- A bounded master constraint is canonically self-adjoint. -/
theorem quantumMasterConstraint_isSelfAdjoint (C : E →L[𝕜] E) :
    IsSelfAdjoint (quantumMasterConstraint C) := by
  simpa [quantumMasterConstraint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.star_eq_adjoint] using (IsSelfAdjoint.star_mul_self C)

/-- **Bounded optical theorem.**  If `U` is unitary, the positive master constraint of its
scattering defect `U-1` is already its Hermitian discontinuity:
`(U-1)†(U-1) = 2-U-U†`.  This is the operator form of the S-matrix optical theorem, stated
without introducing an evolution parameter or an asymptotic limit. -/
theorem quantumMasterConstraint_unitarySubOne_eq_two_sub_self_sub_adjoint
    (U : E →L[𝕜] E) (hadjoint_mul : U.adjoint * U = 1) :
    quantumMasterConstraint (U - 1) = 2 - U - U.adjoint := by
  have hsub : ContinuousLinearMap.adjoint (U - 1) = U.adjoint - 1 := by
    let adj : (E →L[𝕜] E) ≃ₗᵢ⋆[𝕜] (E →L[𝕜] E) :=
      ContinuousLinearMap.adjoint
    simpa [adj, ContinuousLinearMap.adjoint_one] using
      adj.map_sub U (1 : E →L[𝕜] E)
  rw [quantumMasterConstraint, hsub]
  change (U.adjoint - 1) * (U - 1) = 2 - U - U.adjoint
  rw [show (2 : E →L[𝕜] E) = 1 + 1 by norm_num]
  noncomm_ring [hadjoint_mul]

/-- **Supersymmetric partner intertwining.**  The constraint maps its master Hamiltonian
`C†C` into the partner Hamiltonian `CC†`.  This is the exact bounded-operator relation behind
boson/fermion pairing and resolvent-regularized Witten-index constructions. -/
theorem quantumMasterConstraint_partner_intertwining (C : E →L[𝕜] E) :
    C * quantumMasterConstraint C = quantumMasterConstraint C.adjoint * C := by
  change C ∘L (C.adjoint ∘L C) =
    (C.adjoint.adjoint ∘L C.adjoint) ∘L C
  rw [ContinuousLinearMap.adjoint_adjoint]
  exact (ContinuousLinearMap.comp_assoc C C.adjoint C).symm

/-- Adjoint form of the supersymmetric partner intertwining relation. -/
theorem quantumMasterConstraint_partner_intertwining_adjoint (C : E →L[𝕜] E) :
    quantumMasterConstraint C * C.adjoint =
      C.adjoint * quantumMasterConstraint C.adjoint := by
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    (quantumMasterConstraint_partner_intertwining C.adjoint).symm

/-- The master-constraint expectation is exactly the squared constraint residual. -/
theorem re_inner_quantumMasterConstraint_eq_normSq
    (C : E →L[𝕜] E) (ψ : E) :
    RCLike.re (inner 𝕜 ψ (quantumMasterConstraint C ψ)) = ‖C ψ‖ ^ 2 := by
  simpa [quantumMasterConstraint] using
    (C.apply_norm_sq_eq_inner_adjoint_right ψ).symm

/-- Master-constraint expectations are nonnegative without an extra positivity premise. -/
theorem re_inner_quantumMasterConstraint_nonneg
    (C : E →L[𝕜] E) (ψ : E) :
    0 ≤ RCLike.re (inner 𝕜 ψ (quantumMasterConstraint C ψ)) := by
  rw [re_inner_quantumMasterConstraint_eq_normSq]
  positivity

/-- Passing from `C` to `C†C` preserves exactly the physical-state kernel. -/
theorem physicalState_quantumMasterConstraint_iff
    (C : E →L[𝕜] E) (ψ : E) :
    GaloisForLFunctions.PhysicalState (quantumMasterConstraint C).toLinearMap ψ ↔
      GaloisForLFunctions.PhysicalState C.toLinearMap ψ := by
  constructor
  · intro hmaster
    rw [GaloisForLFunctions.PhysicalState] at hmaster ⊢
    change quantumMasterConstraint C ψ = 0 at hmaster
    change C ψ = 0
    apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
    calc
      inner 𝕜 (C ψ) (C ψ) = inner 𝕜 ψ (C.adjoint (C ψ)) :=
        (C.adjoint_inner_right ψ (C ψ)).symm
      _ = inner 𝕜 ψ (quantumMasterConstraint C ψ) := by
        rfl
      _ = 0 := by simp [hmaster]
  · intro hC
    rw [GaloisForLFunctions.PhysicalState] at hC ⊢
    change C ψ = 0 at hC
    change quantumMasterConstraint C ψ = 0
    simp [quantumMasterConstraint, hC]

/-- **Master-constraint kernel identity.**  Passing from a bounded constraint to its positive
master effect preserves the complete physical subspace, not only pointwise physicality. -/
theorem quantumMasterConstraint_ker_eq (C : E →L[𝕜] E) :
    (quantumMasterConstraint C).toLinearMap.ker = C.toLinearMap.ker := by
  ext ψ
  exact physicalState_quantumMasterConstraint_iff C ψ

/-- The positive effect `C†C` vanishes exactly when the underlying constraint channel vanishes.
This is the operator-level nondegeneracy law behind Kraus effects and master constraints. -/
theorem quantumMasterConstraint_eq_zero_iff (C : E →L[𝕜] E) :
    quantumMasterConstraint C = 0 ↔ C = 0 := by
  simpa [quantumMasterConstraint] using adjoint_comp_self_eq_zero_iff C

/-- Equivalently, forming the positive master effect introduces no new nondegeneracy premise. -/
theorem quantumMasterConstraint_ne_zero_iff (C : E →L[𝕜] E) :
    quantumMasterConstraint C ≠ 0 ↔ C ≠ 0 :=
  not_congr (quantumMasterConstraint_eq_zero_iff C)

/-- The master constraint removes self-adjointness of the original constraint from the Ward
value: physicality for an arbitrary bounded `C` is enough. -/
theorem quantumMasterConstraint_WardValue_eq_zero
    (C A : E →L[𝕜] E) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    inner 𝕜 ψ (quantumMasterConstraint C (A ψ)) = 0 := by
  exact constraintWardValue_eq_zero (quantumMasterConstraint C) A
    (quantumMasterConstraint_isSelfAdjoint C)
    ((physicalState_quantumMasterConstraint_iff C ψ).mpr hψ)

/-- The master constraint likewise removes self-adjointness of `C` from the commutator Ward
value. -/
theorem quantumMasterConstraint_commutatorWardValue_eq_zero
    (C A : E →L[𝕜] E) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    inner 𝕜 ψ
      (((quantumMasterConstraint C * A - A * quantumMasterConstraint C) : E →L[𝕜] E) ψ) = 0 := by
  exact constraintCommutatorWardValue_eq_zero (quantumMasterConstraint C) A
    (quantumMasterConstraint_isSelfAdjoint C)
    ((physicalState_quantumMasterConstraint_iff C ψ).mpr hψ)

/-- Operators equal modulo the two-sided ideal generated by `C†C` have identical physical matrix
elements, with no self-adjointness assumption on `C`. -/
theorem physicalMatrixElement_congr_mod_quantumMasterConstraintIdeal
    (C A B L R : E →L[𝕜] E)
    (hmod : B = A + (quantumMasterConstraint C * L + R * quantumMasterConstraint C))
    {φ ψ : E}
    (hφ : GaloisForLFunctions.PhysicalState C.toLinearMap φ)
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    inner 𝕜 φ (B ψ) = inner 𝕜 φ (A ψ) := by
  exact physicalMatrixElement_congr_mod_constraintTwoSidedIdeal
    (quantumMasterConstraint C) A B L R
    (quantumMasterConstraint_isSelfAdjoint C) hmod
    ((physicalState_quantumMasterConstraint_iff C φ).mpr hφ)
    ((physicalState_quantumMasterConstraint_iff C ψ).mpr hψ)

/-! ### Finite families of constraints -/

variable {ι : Type*} [Fintype ι]

/-- The finite-family master constraint is the sum of the individual positive squares. -/
noncomputable def finiteQuantumMasterConstraint
    (C : ι → E →L[𝕜] E) : E →L[𝕜] E :=
  ∑ i, quantumMasterConstraint (C i)

/-- A finite-family master constraint is canonically self-adjoint. -/
theorem finiteQuantumMasterConstraint_isSelfAdjoint
    (C : ι → E →L[𝕜] E) :
    IsSelfAdjoint (finiteQuantumMasterConstraint C) := by
  classical
  exact isSelfAdjoint_sum Finset.univ fun i _ =>
    quantumMasterConstraint_isSelfAdjoint (C i)

/-- The finite master expectation is the sum of all squared constraint residuals. -/
theorem re_inner_finiteQuantumMasterConstraint_eq_sum_normSq
    (C : ι → E →L[𝕜] E) (ψ : E) :
    RCLike.re (inner 𝕜 ψ (finiteQuantumMasterConstraint C ψ)) =
      ∑ i, ‖C i ψ‖ ^ 2 := by
  classical
  simp only [finiteQuantumMasterConstraint, ContinuousLinearMap.sum_apply,
    inner_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    re_inner_quantumMasterConstraint_eq_normSq (C i) ψ

/-- One finite master constraint has exactly the intersection of all individual constraint
kernels as its physical space. -/
theorem physicalState_finiteQuantumMasterConstraint_iff
    (C : ι → E →L[𝕜] E) (ψ : E) :
    GaloisForLFunctions.PhysicalState (finiteQuantumMasterConstraint C).toLinearMap ψ ↔
      ∀ i, GaloisForLFunctions.PhysicalState (C i).toLinearMap ψ := by
  classical
  constructor
  · intro hmaster i
    rw [GaloisForLFunctions.PhysicalState] at hmaster ⊢
    change finiteQuantumMasterConstraint C ψ = 0 at hmaster
    change C i ψ = 0
    have hsum : ∑ j, ‖C j ψ‖ ^ 2 = 0 := by
      rw [← re_inner_finiteQuantumMasterConstraint_eq_sum_normSq C ψ, hmaster]
      simp
    have hi : ‖C i ψ‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg ‖C j ψ‖)).mp hsum i (Finset.mem_univ i)
    exact norm_eq_zero.mp (by simpa using hi)
  · intro hfamily
    have hzero : ∀ i, C i ψ = 0 := by
      intro i
      simpa only [GaloisForLFunctions.PhysicalState] using hfamily i
    rw [GaloisForLFunctions.PhysicalState]
    change finiteQuantumMasterConstraint C ψ = 0
    simp [finiteQuantumMasterConstraint, quantumMasterConstraint, hzero]

/-- The finite master-constraint kernel is preserved by every observable whose commutators close
in the existing finite first-class family interface.  The consumer only needs one master-state
premise rather than a separately supplied physical-state proof for every constraint. -/
theorem finiteQuantumMasterConstraint_preserves_physicalState_of_closes_mod_constraints
    (C : ι → E →L[𝕜] E) (A : E →L[𝕜] E)
    (B : ι → ι → Module.End 𝕜 E)
    (hclose : ∀ i, (C i).toLinearMap * A.toLinearMap =
      A.toLinearMap * (C i).toLinearMap + ∑ j, B i j * (C j).toLinearMap)
    {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState
      (finiteQuantumMasterConstraint C).toLinearMap ψ) :
    GaloisForLFunctions.PhysicalState
      (finiteQuantumMasterConstraint C).toLinearMap (A ψ) := by
  apply (physicalState_finiteQuantumMasterConstraint_iff C (A ψ)).mpr
  exact GaloisForLFunctions.preserves_jointPhysicalState_of_closes_mod_constraints
    (fun i => (C i).toLinearMap) A.toLinearMap B hclose
    ((physicalState_finiteQuantumMasterConstraint_iff C ψ).mp hψ)

/-- Joint physicality for a finite constraint family is enough for one master-constraint Ward
value; no self-adjointness premise is required for any member of the family. -/
theorem finiteQuantumMasterConstraint_WardValue_eq_zero
    (C : ι → E →L[𝕜] E) (A : E →L[𝕜] E) {ψ : E}
    (hψ : ∀ i, GaloisForLFunctions.PhysicalState (C i).toLinearMap ψ) :
    inner 𝕜 ψ (finiteQuantumMasterConstraint C (A ψ)) = 0 := by
  exact constraintWardValue_eq_zero (finiteQuantumMasterConstraint C) A
    (finiteQuantumMasterConstraint_isSelfAdjoint C)
    ((physicalState_finiteQuantumMasterConstraint_iff C ψ).mpr hψ)

/-- The commutator Ward value likewise packages a finite joint constraint family into one
automatically self-adjoint master constraint. -/
theorem finiteQuantumMasterConstraint_commutatorWardValue_eq_zero
    (C : ι → E →L[𝕜] E) (A : E →L[𝕜] E) {ψ : E}
    (hψ : ∀ i, GaloisForLFunctions.PhysicalState (C i).toLinearMap ψ) :
    inner 𝕜 ψ
      (((finiteQuantumMasterConstraint C * A - A * finiteQuantumMasterConstraint C) :
        E →L[𝕜] E) ψ) = 0 := by
  exact constraintCommutatorWardValue_eq_zero (finiteQuantumMasterConstraint C) A
    (finiteQuantumMasterConstraint_isSelfAdjoint C)
    ((physicalState_finiteQuantumMasterConstraint_iff C ψ).mpr hψ)

/-- Operators equal modulo the ideal generated by the finite master constraint have identical
matrix elements between jointly physical states, without self-adjointness assumptions on the
individual constraints. -/
theorem physicalMatrixElement_congr_mod_finiteQuantumMasterConstraintIdeal
    (C : ι → E →L[𝕜] E) (A B L R : E →L[𝕜] E)
    (hmod : B = A +
      (finiteQuantumMasterConstraint C * L + R * finiteQuantumMasterConstraint C))
    {φ ψ : E}
    (hφ : ∀ i, GaloisForLFunctions.PhysicalState (C i).toLinearMap φ)
    (hψ : ∀ i, GaloisForLFunctions.PhysicalState (C i).toLinearMap ψ) :
    inner 𝕜 φ (B ψ) = inner 𝕜 φ (A ψ) := by
  exact physicalMatrixElement_congr_mod_constraintTwoSidedIdeal
    (finiteQuantumMasterConstraint C) A B L R
    (finiteQuantumMasterConstraint_isSelfAdjoint C) hmod
    ((physicalState_finiteQuantumMasterConstraint_iff C φ).mpr hφ)
    ((physicalState_finiteQuantumMasterConstraint_iff C ψ).mpr hψ)

end MasterConstraint

section AlgebraicAverage

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The unnormalized orbit sum for the first `N` iterates of a bounded gauge step. -/
def finiteCyclicGaugeSum (U : E →L[𝕜] E) (N : ℕ) : E →L[𝕜] E :=
  ∑ k ∈ Finset.range N, U ^ k

/-- The normalized finite cyclic orbit average. -/
def finiteCyclicGaugeAverage (U : E →L[𝕜] E) (N : ℕ) : E →L[𝕜] E :=
  ((N : 𝕜)⁻¹) • finiteCyclicGaugeSum U N

/-- The constraint acting on the orbit sum telescopes to the periodicity defect. -/
theorem finiteCyclicGaugeSum_telescope (U : E →L[𝕜] E) (N : ℕ) :
    (U - 1) * finiteCyclicGaugeSum U N = U ^ N - 1 := by
  simpa [finiteCyclicGaugeSum] using (mul_geom_sum U N)

/-- A finite-period orbit sum is a physical vector for the constraint `U - 1`. -/
theorem finiteCyclicGaugeSum_physical
    (U : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) (ψ : E) :
    GaloisForLFunctions.PhysicalState (U - 1).toLinearMap
      (finiteCyclicGaugeSum U N ψ) := by
  rw [GaloisForLFunctions.PhysicalState]
  change (U - 1) (finiteCyclicGaugeSum U N ψ) = 0
  rw [← ContinuousLinearMap.mul_apply, finiteCyclicGaugeSum_telescope, hperiod]
  simp

/-- Normalization preserves the constraint solution constructed by the orbit sum. -/
theorem finiteCyclicGaugeAverage_physical
    (U : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) (ψ : E) :
    GaloisForLFunctions.PhysicalState (U - 1).toLinearMap
      (finiteCyclicGaugeAverage U N ψ) := by
  have hsum := finiteCyclicGaugeSum_physical U N hperiod ψ
  rw [GaloisForLFunctions.PhysicalState] at hsum ⊢
  change (U - 1) (finiteCyclicGaugeSum U N ψ) = 0 at hsum
  change (U - 1) (finiteCyclicGaugeAverage U N ψ) = 0
  simp [finiteCyclicGaugeAverage, hsum]

/-- The unnormalized orbit sum acts by the scalar `N` on every fixed vector. -/
theorem finiteCyclicGaugeSum_apply_of_fixed
    (U : E →L[𝕜] E) (N : ℕ) {ψ : E} (hfix : U ψ = ψ) :
    finiteCyclicGaugeSum U N ψ = (N : 𝕜) • ψ := by
  have hpow : ∀ k : ℕ, (U ^ k) ψ = ψ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply, hfix, ih]
  calc
    finiteCyclicGaugeSum U N ψ = ∑ k ∈ Finset.range N, (U ^ k) ψ := by
      simp [finiteCyclicGaugeSum]
    _ = ∑ _k ∈ Finset.range N, ψ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hpow k]
    _ = (N : 𝕜) • ψ := by
      simpa only [Finset.sum_const, Finset.card_range] using
        (Nat.cast_smul_eq_nsmul 𝕜 N ψ).symm

/-- A nonempty normalized orbit average fixes every invariant vector. -/
theorem finiteCyclicGaugeAverage_apply_of_fixed
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) {ψ : E} (hfix : U ψ = ψ) :
    finiteCyclicGaugeAverage U N ψ = ψ := by
  rw [finiteCyclicGaugeAverage, ContinuousLinearMap.smul_apply,
    finiteCyclicGaugeSum_apply_of_fixed U N hfix]
  simp [Nat.cast_ne_zero.mpr hN]

/-- For a nonempty finite-period action, physicality is exactly fixedness under averaging. -/
theorem physicalState_iff_finiteCyclicGaugeAverage_fixed
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) (hperiod : U ^ N = 1) (ψ : E) :
    GaloisForLFunctions.PhysicalState (U - 1).toLinearMap ψ ↔
      finiteCyclicGaugeAverage U N ψ = ψ := by
  constructor
  · intro hψ
    rw [GaloisForLFunctions.PhysicalState] at hψ
    change (U - 1) ψ = 0 at hψ
    have hfix : U ψ = ψ := by
      apply sub_eq_zero.mp
      simpa using hψ
    exact finiteCyclicGaugeAverage_apply_of_fixed U N hN hfix
  · intro haverage
    have hphysical := finiteCyclicGaugeAverage_physical U N hperiod ψ
    simpa [haverage] using hphysical

/-- The normalized finite-period orbit average is idempotent. -/
theorem finiteCyclicGaugeAverage_idempotent
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) (hperiod : U ^ N = 1) :
    finiteCyclicGaugeAverage U N * finiteCyclicGaugeAverage U N =
      finiteCyclicGaugeAverage U N := by
  ext ψ
  rw [ContinuousLinearMap.mul_apply]
  exact (physicalState_iff_finiteCyclicGaugeAverage_fixed U N hN hperiod
    (finiteCyclicGaugeAverage U N ψ)).mp
      (finiteCyclicGaugeAverage_physical U N hperiod ψ)

/-- **Exact physical-range classification.**  A nonempty finite-period orbit average has image
exactly the kernel of its static clock constraint.  Thus no separate surjectivity onto the
physical sector is required. -/
theorem finiteCyclicGaugeAverage_range_eq_constraint_ker
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) (hperiod : U ^ N = 1) :
    (finiteCyclicGaugeAverage U N).toLinearMap.range =
      LinearMap.ker (U - 1).toLinearMap := by
  ext ψ
  constructor
  · rintro ⟨φ, rfl⟩
    exact finiteCyclicGaugeAverage_physical U N hperiod φ
  · intro hψ
    refine ⟨ψ, ?_⟩
    exact (physicalState_iff_finiteCyclicGaugeAverage_fixed
      U N hN hperiod ψ).mp hψ

/-! ### Heisenberg-picture observable twirling -/

/-- The unnormalized finite cyclic conjugation average, written recursively without inverse
powers.  Its `N` terms are `U^k A U^(N-k)` for `0 ≤ k < N`; when `U^N = 1`, these are the usual
conjugates `U^k A U^(-k)`. -/
def finiteCyclicObservableTwirlNumerator
    (U A : E →L[𝕜] E) : ℕ → E →L[𝕜] E
  | 0 => 0
  | n + 1 => U * finiteCyclicObservableTwirlNumerator U A n + A * U ^ (n + 1)

/-- The normalized finite cyclic twirl of an observable. -/
def finiteCyclicObservableTwirl
    (U A : E →L[𝕜] E) (N : ℕ) : E →L[𝕜] E :=
  ((N : 𝕜)⁻¹) • finiteCyclicObservableTwirlNumerator U A N

/-- Observable-twirl numerators are additive in the observed quantity. -/
theorem finiteCyclicObservableTwirlNumerator_add
    (U A B : E →L[𝕜] E) : ∀ N : ℕ,
    finiteCyclicObservableTwirlNumerator U (A + B) N =
      finiteCyclicObservableTwirlNumerator U A N +
        finiteCyclicObservableTwirlNumerator U B N
  | 0 => by simp [finiteCyclicObservableTwirlNumerator]
  | n + 1 => by
      simp only [finiteCyclicObservableTwirlNumerator]
      rw [finiteCyclicObservableTwirlNumerator_add U A B n]
      noncomm_ring

/-- Observable-twirl numerators preserve subtraction. -/
theorem finiteCyclicObservableTwirlNumerator_sub
    (U A B : E →L[𝕜] E) : ∀ N : ℕ,
    finiteCyclicObservableTwirlNumerator U (A - B) N =
      finiteCyclicObservableTwirlNumerator U A N -
        finiteCyclicObservableTwirlNumerator U B N
  | 0 => by simp [finiteCyclicObservableTwirlNumerator]
  | n + 1 => by
      simp only [finiteCyclicObservableTwirlNumerator]
      rw [finiteCyclicObservableTwirlNumerator_sub U A B n]
      noncomm_ring

/-- Normalized observable twirling is additive. -/
theorem finiteCyclicObservableTwirl_add
    (U A B : E →L[𝕜] E) (N : ℕ) :
    finiteCyclicObservableTwirl U (A + B) N =
      finiteCyclicObservableTwirl U A N + finiteCyclicObservableTwirl U B N := by
  simp only [finiteCyclicObservableTwirl,
    finiteCyclicObservableTwirlNumerator_add, smul_add]

/-- Normalized observable twirling preserves subtraction. -/
theorem finiteCyclicObservableTwirl_sub
    (U A B : E →L[𝕜] E) (N : ℕ) :
    finiteCyclicObservableTwirl U (A - B) N =
      finiteCyclicObservableTwirl U A N - finiteCyclicObservableTwirl U B N := by
  simp only [finiteCyclicObservableTwirl,
    finiteCyclicObservableTwirlNumerator_sub, smul_sub]

/-- Commutation with one gauge step implies commutation with every natural power. -/
theorem pow_mul_eq_mul_pow_of_commutes
    (U B : E →L[𝕜] E) (hcomm : U * B = B * U) : ∀ n : ℕ,
    U ^ n * B = B * U ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        U ^ (n + 1) * B = U ^ n * (U * B) := by rw [pow_succ, mul_assoc]
        _ = U ^ n * (B * U) := by rw [hcomm]
        _ = (U ^ n * B) * U := by rw [mul_assoc]
        _ = (B * U ^ n) * U := by rw [pow_mul_eq_mul_pow_of_commutes U B hcomm n]
        _ = B * U ^ (n + 1) := by rw [pow_succ, mul_assoc]

/-- Twirling is a right module map over observables in the clock commutant. -/
theorem finiteCyclicObservableTwirlNumerator_mul_right_of_commutes
    (U A B : E →L[𝕜] E) (hcomm : U * B = B * U) : ∀ N : ℕ,
    finiteCyclicObservableTwirlNumerator U (A * B) N =
      finiteCyclicObservableTwirlNumerator U A N * B
  | 0 => by simp [finiteCyclicObservableTwirlNumerator]
  | n + 1 => by
      simp only [finiteCyclicObservableTwirlNumerator]
      rw [finiteCyclicObservableTwirlNumerator_mul_right_of_commutes U A B hcomm n]
      have htail : A * B * U ^ (n + 1) = A * U ^ (n + 1) * B := by
        calc
          A * B * U ^ (n + 1) = A * (B * U ^ (n + 1)) := by rw [mul_assoc]
          _ = A * (U ^ (n + 1) * B) := by
            rw [pow_mul_eq_mul_pow_of_commutes U B hcomm (n + 1)]
          _ = A * U ^ (n + 1) * B := by rw [mul_assoc]
      rw [htail]
      noncomm_ring

/-- Twirling is a left module map over observables in the clock commutant. -/
theorem finiteCyclicObservableTwirlNumerator_mul_left_of_commutes
    (U A B : E →L[𝕜] E) (hcomm : U * B = B * U) : ∀ N : ℕ,
    finiteCyclicObservableTwirlNumerator U (B * A) N =
      B * finiteCyclicObservableTwirlNumerator U A N
  | 0 => by simp [finiteCyclicObservableTwirlNumerator]
  | n + 1 => by
      simp only [finiteCyclicObservableTwirlNumerator]
      rw [finiteCyclicObservableTwirlNumerator_mul_left_of_commutes U A B hcomm n]
      have hstep :
          U * (B * finiteCyclicObservableTwirlNumerator U A n) =
            B * (U * finiteCyclicObservableTwirlNumerator U A n) := by
        calc
          U * (B * finiteCyclicObservableTwirlNumerator U A n) =
              (U * B) * finiteCyclicObservableTwirlNumerator U A n := by rw [mul_assoc]
          _ = (B * U) * finiteCyclicObservableTwirlNumerator U A n := by rw [hcomm]
          _ = B * (U * finiteCyclicObservableTwirlNumerator U A n) := by rw [mul_assoc]
      rw [hstep]
      noncomm_ring

/-- Normalized twirling is a right module map over the clock commutant. -/
theorem finiteCyclicObservableTwirl_mul_right_of_commutes
    (U A B : E →L[𝕜] E) (N : ℕ) (hcomm : U * B = B * U) :
    finiteCyclicObservableTwirl U (A * B) N =
      finiteCyclicObservableTwirl U A N * B := by
  rw [finiteCyclicObservableTwirl, finiteCyclicObservableTwirl,
    finiteCyclicObservableTwirlNumerator_mul_right_of_commutes U A B hcomm N,
    smul_mul_assoc]

/-- Normalized twirling is a left module map over the clock commutant. -/
theorem finiteCyclicObservableTwirl_mul_left_of_commutes
    (U A B : E →L[𝕜] E) (N : ℕ) (hcomm : U * B = B * U) :
    finiteCyclicObservableTwirl U (B * A) N =
      B * finiteCyclicObservableTwirl U A N := by
  rw [finiteCyclicObservableTwirl, finiteCyclicObservableTwirl,
    finiteCyclicObservableTwirlNumerator_mul_left_of_commutes U A B hcomm N,
    mul_smul_comm]

/-- **Observable-twirl boundary law.**  The failure of the finite conjugation numerator to
commute with `U` is exactly its two endpoint terms. -/
theorem finiteCyclicObservableTwirlNumerator_commutator_telescope
    (U A : E →L[𝕜] E) : ∀ N : ℕ,
    U * finiteCyclicObservableTwirlNumerator U A N -
        finiteCyclicObservableTwirlNumerator U A N * U =
      U ^ N * A * U - A * U ^ (N + 1)
  | 0 => by simp [finiteCyclicObservableTwirlNumerator]
  | n + 1 => by
      have ih := finiteCyclicObservableTwirlNumerator_commutator_telescope U A n
      simp only [finiteCyclicObservableTwirlNumerator]
      calc
        U * (U * finiteCyclicObservableTwirlNumerator U A n + A * U ^ (n + 1)) -
            (U * finiteCyclicObservableTwirlNumerator U A n + A * U ^ (n + 1)) * U =
          U * (U * finiteCyclicObservableTwirlNumerator U A n -
              finiteCyclicObservableTwirlNumerator U A n * U) +
            U * A * U ^ (n + 1) - A * U ^ (n + 1) * U := by
              noncomm_ring
        _ = U * (U ^ n * A * U - A * U ^ (n + 1)) +
            U * A * U ^ (n + 1) - A * U ^ (n + 1) * U := by rw [ih]
        _ = (U * U ^ n) * A * U - A * (U ^ (n + 1) * U) := by
          noncomm_ring
        _ = U ^ (n + 1) * A * U - A * U ^ (n + 1 + 1) := by
          rw [← pow_succ' U n, ← pow_succ U (n + 1)]

/-- A finite-period gauge step commutes with every observable twirl numerator. -/
theorem finiteCyclicObservableTwirlNumerator_commutes
    (U A : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) :
    U * finiteCyclicObservableTwirlNumerator U A N =
      finiteCyclicObservableTwirlNumerator U A N * U := by
  have htel := finiteCyclicObservableTwirlNumerator_commutator_telescope U A N
  apply sub_eq_zero.mp
  rw [htel, hperiod, show U ^ (N + 1) = U by rw [pow_succ, hperiod, one_mul]]
  simp

/-- Normalization preserves the commutant-valued property of finite cyclic twirling. -/
theorem finiteCyclicObservableTwirl_commutes
    (U A : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) :
    U * finiteCyclicObservableTwirl U A N =
      finiteCyclicObservableTwirl U A N * U := by
  simp only [finiteCyclicObservableTwirl]
  rw [mul_smul_comm, smul_mul_assoc,
    finiteCyclicObservableTwirlNumerator_commutes U A N hperiod]

/-- If the seed observable already commutes with the gauge step, its unnormalized twirl is just
`N` copies of the same observable followed by the common endpoint power `U^N`. -/
theorem finiteCyclicObservableTwirlNumerator_eq_smul_mul_pow_of_commutes
    (U A : E →L[𝕜] E) (hcomm : U * A = A * U) : ∀ N : ℕ,
    finiteCyclicObservableTwirlNumerator U A N =
      (N : 𝕜) • (A * U ^ N)
  | 0 => by simp [finiteCyclicObservableTwirlNumerator]
  | n + 1 => by
      rw [finiteCyclicObservableTwirlNumerator,
        finiteCyclicObservableTwirlNumerator_eq_smul_mul_pow_of_commutes U A hcomm n,
        mul_smul_comm]
      have hstep : U * (A * U ^ n) = A * U ^ (n + 1) := by
        rw [← mul_assoc, hcomm, mul_assoc, ← pow_succ' U n]
      rw [hstep]
      simp [Nat.cast_succ, add_smul]

/-- Finite cyclic twirling fixes every observable already in the gauge commutant.  Thus the
twirl is a genuine conditional expectation onto invariant observables, not merely a map whose
outputs happen to commute with the constraint. -/
theorem finiteCyclicObservableTwirl_eq_self_of_commutes
    (U A : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) (hperiod : U ^ N = 1)
    (hcomm : U * A = A * U) :
    finiteCyclicObservableTwirl U A N = A := by
  rw [finiteCyclicObservableTwirl,
    finiteCyclicObservableTwirlNumerator_eq_smul_mul_pow_of_commutes U A hcomm N,
    hperiod]
  simp [Nat.cast_ne_zero.mpr hN]

/-- Applying finite cyclic twirling twice is the same as applying it once.  This is the exact
finite analogue of modular zero-mode projection in observer algebras. -/
theorem finiteCyclicObservableTwirl_idempotent
    (U A : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) (hperiod : U ^ N = 1) :
    finiteCyclicObservableTwirl U (finiteCyclicObservableTwirl U A N) N =
      finiteCyclicObservableTwirl U A N := by
  exact finiteCyclicObservableTwirl_eq_self_of_commutes U
    (finiteCyclicObservableTwirl U A N) N hN hperiod
    (finiteCyclicObservableTwirl_commutes U A N hperiod)

/-- Multiplicativity defect of an arbitrary finite cyclic clock-observer twirl. -/
def finiteCyclicObservableTwirlKadisonDefect
    (U X : E →L[𝕜] E) (N : ℕ) : E →L[𝕜] E :=
  finiteCyclicObservableTwirl U (X * X) N -
    finiteCyclicObservableTwirl U X N * finiteCyclicObservableTwirl U X N

/-- **Finite-clock conditional variance identity.**  For every nonempty finite-period clock,
the twirl's multiplicativity defect is the twirl of the square of the erased observable
component.  This is the finite cyclic conditional-expectation variance law; no state or time
parameter is involved. -/
theorem finiteCyclicObservableTwirlKadisonDefect_eq_twirl_disturbance_sq
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) (hperiod : U ^ N = 1) :
    finiteCyclicObservableTwirlKadisonDefect U X N =
      finiteCyclicObservableTwirl U
        ((X - finiteCyclicObservableTwirl U X N) *
          (X - finiteCyclicObservableTwirl U X N)) N := by
  let M : E →L[𝕜] E := finiteCyclicObservableTwirl U X N
  have hMcomm : U * M = M * U := by
    exact finiteCyclicObservableTwirl_commutes U X N hperiod
  have hM2comm : U * (M * M) = (M * M) * U := by
    calc
      U * (M * M) = (U * M) * M := (mul_assoc U M M).symm
      _ = (M * U) * M := by rw [hMcomm]
      _ = M * (U * M) := mul_assoc M U M
      _ = M * (M * U) := by rw [hMcomm]
      _ = (M * M) * U := (mul_assoc M M U).symm
  have hright : finiteCyclicObservableTwirl U (X * M) N = M * M := by
    rw [finiteCyclicObservableTwirl_mul_right_of_commutes U X M N hMcomm]
  have hleft : finiteCyclicObservableTwirl U (M * X) N = M * M := by
    rw [finiteCyclicObservableTwirl_mul_left_of_commutes U X M N hMcomm]
  have hM2 : finiteCyclicObservableTwirl U (M * M) N = M * M :=
    finiteCyclicObservableTwirl_eq_self_of_commutes U (M * M) N hN hperiod hM2comm
  have hexpand :
      (X - M) * (X - M) = X * X - X * M - M * X + M * M := by
    noncomm_ring
  rw [finiteCyclicObservableTwirlKadisonDefect]
  change finiteCyclicObservableTwirl U (X * X) N - M * M =
    finiteCyclicObservableTwirl U ((X - M) * (X - M)) N
  rw [hexpand,
    finiteCyclicObservableTwirl_add U (X * X - X * M - M * X) (M * M) N,
    finiteCyclicObservableTwirl_sub U (X * X - X * M) (M * X) N,
    finiteCyclicObservableTwirl_sub U (X * X) (X * M) N,
    hright, hleft, hM2]
  noncomm_ring

/-- A twirled observable commutes with the static constraint `U - 1`. -/
theorem finiteCyclicObservableTwirl_commutes_constraint
    (U A : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) :
    (U - 1) * finiteCyclicObservableTwirl U A N =
      finiteCyclicObservableTwirl U A N * (U - 1) := by
  have hcomm := finiteCyclicObservableTwirl_commutes U A N hperiod
  calc
    (U - 1) * finiteCyclicObservableTwirl U A N =
        U * finiteCyclicObservableTwirl U A N -
          finiteCyclicObservableTwirl U A N := by noncomm_ring
    _ = finiteCyclicObservableTwirl U A N * U -
          finiteCyclicObservableTwirl U A N := by rw [hcomm]
    _ = finiteCyclicObservableTwirl U A N * (U - 1) := by noncomm_ring

/-- Group twirling constructs a Dirac observable: it preserves every physical vector for the
finite cyclic constraint `U - 1`, with no commutator premise left to supply. -/
theorem finiteCyclicObservableTwirl_preserves_physicalState
    (U A : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState (U - 1).toLinearMap ψ) :
    GaloisForLFunctions.PhysicalState (U - 1).toLinearMap
      (finiteCyclicObservableTwirl U A N ψ) := by
  rw [GaloisForLFunctions.PhysicalState] at hψ ⊢
  change (U - 1) ψ = 0 at hψ
  change (U - 1) (finiteCyclicObservableTwirl U A N ψ) = 0
  rw [← ContinuousLinearMap.mul_apply,
    finiteCyclicObservableTwirl_commutes_constraint U A N hperiod,
    ContinuousLinearMap.mul_apply, hψ]
  simp

end AlgebraicAverage

section RelationalClockObservables

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Between a left-invariant and a right-invariant state, the unnormalized observable twirl has
exactly `N` times the matrix element of its seed.  This is the finite stationary-observable
identity behind Page--Wootters conditioning and periodic relational clocks. -/
theorem inner_finiteCyclicObservableTwirlNumerator_of_fixed
    (U A : E →L[𝕜] E) {φ ψ : E}
    (hφ : U.adjoint φ = φ) (hψ : U ψ = ψ) : ∀ N : ℕ,
    inner 𝕜 φ (finiteCyclicObservableTwirlNumerator U A N ψ) =
      (N : 𝕜) * inner 𝕜 φ (A ψ)
  | 0 => by simp [finiteCyclicObservableTwirlNumerator]
  | n + 1 => by
      have hpow : (U ^ (n + 1)) ψ = ψ := by
        induction n + 1 with
        | zero => simp
        | succ k ih =>
            rw [pow_succ, ContinuousLinearMap.mul_apply, hψ, ih]
      simp only [finiteCyclicObservableTwirlNumerator,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, inner_add_right]
      calc
        inner 𝕜 φ (U (finiteCyclicObservableTwirlNumerator U A n ψ)) +
            inner 𝕜 φ (A ((U ^ (n + 1)) ψ)) =
          inner 𝕜 (U.adjoint φ)
              (finiteCyclicObservableTwirlNumerator U A n ψ) +
            inner 𝕜 φ (A ψ) := by
              rw [ContinuousLinearMap.adjoint_inner_left, hpow]
        _ = (n : 𝕜) * inner 𝕜 φ (A ψ) + inner 𝕜 φ (A ψ) := by
          rw [hφ, inner_finiteCyclicObservableTwirlNumerator_of_fixed U A hφ hψ n]
        _ = (n + 1 : ℕ) * inner 𝕜 φ (A ψ) := by
          push_cast
          ring

/-- Observable twirling changes the kinematic representative but preserves every matrix element
between invariant states.  No period assumption is needed: only a nonempty normalized orbit and
the stationary left/right constraints enter the value. -/
theorem inner_finiteCyclicObservableTwirl_of_fixed
    (U A : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) {φ ψ : E}
    (hφ : U.adjoint φ = φ) (hψ : U ψ = ψ) :
    inner 𝕜 φ (finiteCyclicObservableTwirl U A N ψ) =
      inner 𝕜 φ (A ψ) := by
  rw [finiteCyclicObservableTwirl, ContinuousLinearMap.smul_apply, inner_smul_right,
    inner_finiteCyclicObservableTwirlNumerator_of_fixed U A hφ hψ N]
  simp [Nat.cast_ne_zero.mpr hN]

/-- **Stationary finite-clock variance value.**  Between invariant left and right states, the
Kadison defect of an arbitrary finite cyclic clock has exactly the matrix element of the squared
observable component erased by the clock.  All apparent clock motion has disappeared; only the
conditional observational variance remains. -/
theorem inner_finiteCyclicObservableTwirlKadisonDefect_of_fixed
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) (hperiod : U ^ N = 1) {φ ψ : E}
    (hφ : U.adjoint φ = φ) (hψ : U ψ = ψ) :
    inner 𝕜 φ (finiteCyclicObservableTwirlKadisonDefect U X N ψ) =
      inner 𝕜 φ
        (((X - finiteCyclicObservableTwirl U X N) *
          (X - finiteCyclicObservableTwirl U X N)) ψ) := by
  rw [finiteCyclicObservableTwirlKadisonDefect_eq_twirl_disturbance_sq
    U X N hN hperiod]
  exact inner_finiteCyclicObservableTwirl_of_fixed U
    ((X - finiteCyclicObservableTwirl U X N) *
      (X - finiteCyclicObservableTwirl U X N)) N hN hφ hψ

/-- Constraint form of physical matrix-element preservation.  It is the exact finite bridge
between Dirac/group-averaged observables and conditional relational observables. -/
theorem physicalMatrixElement_finiteCyclicObservableTwirl_eq
    (U A : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) {φ ψ : E}
    (hφ : GaloisForLFunctions.PhysicalState (U.adjoint - 1).toLinearMap φ)
    (hψ : GaloisForLFunctions.PhysicalState (U - 1).toLinearMap ψ) :
    inner 𝕜 φ (finiteCyclicObservableTwirl U A N ψ) =
      inner 𝕜 φ (A ψ) := by
  rw [GaloisForLFunctions.PhysicalState] at hφ hψ
  have hφfix : U.adjoint φ = φ := by
    apply sub_eq_zero.mp
    simpa using hφ
  have hψfix : U ψ = ψ := by
    apply sub_eq_zero.mp
    simpa using hψ
  exact inner_finiteCyclicObservableTwirl_of_fixed U A N hN hφfix hψfix

/-- Both numerator and denominator of a relational conditional value are invariant under
observable twirling.  The ratio therefore contains the observable clock structure even when the
global state is stationary. -/
theorem physicalConditionalValue_finiteCyclicObservableTwirl_eq
    (U A B : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) {φ ψ : E}
    (hφ : GaloisForLFunctions.PhysicalState (U.adjoint - 1).toLinearMap φ)
    (hψ : GaloisForLFunctions.PhysicalState (U - 1).toLinearMap ψ) :
    inner 𝕜 φ (finiteCyclicObservableTwirl U A N ψ) /
        inner 𝕜 φ (finiteCyclicObservableTwirl U B N ψ) =
      inner 𝕜 φ (A ψ) / inner 𝕜 φ (B ψ) := by
  rw [physicalMatrixElement_finiteCyclicObservableTwirl_eq U A N hN hφ hψ,
    physicalMatrixElement_finiteCyclicObservableTwirl_eq U B N hN hφ hψ]

/-- **Uniform stationary clock marginal.**  If one clock effect resolves the identity under a
finite cyclic twirl, every constrained left/right matrix element assigns it exactly `1/N` of the
unconditioned weight.  Hence a stationary clock has no informative raw time marginal; its time
information lives in conditional correlations. -/
theorem stationaryClockEffect_matrixElement_eq_uniform
    (U e : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) {φ ψ : E}
    (hφ : GaloisForLFunctions.PhysicalState (U.adjoint - 1).toLinearMap φ)
    (hψ : GaloisForLFunctions.PhysicalState (U - 1).toLinearMap ψ)
    (hresolve : finiteCyclicObservableTwirl U e N = ((N : 𝕜)⁻¹) • 1) :
    inner 𝕜 φ (e ψ) = (N : 𝕜)⁻¹ * inner 𝕜 φ ψ := by
  calc
    inner 𝕜 φ (e ψ) =
        inner 𝕜 φ (finiteCyclicObservableTwirl U e N ψ) :=
      (physicalMatrixElement_finiteCyclicObservableTwirl_eq U e N hN hφ hψ).symm
    _ = (N : 𝕜)⁻¹ * inner 𝕜 φ ψ := by
      rw [hresolve, ContinuousLinearMap.smul_apply, inner_smul_right]
      simp

end RelationalClockObservables

section OrthogonalAverage

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Finite cyclic averaging also has image exactly the kernel of the positive master constraint
of the clock defect.  The master-effect representation introduces no new physical vectors. -/
theorem finiteCyclicGaugeAverage_range_eq_masterConstraint_ker
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) (hperiod : U ^ N = 1) :
    (finiteCyclicGaugeAverage U N).toLinearMap.range =
      (quantumMasterConstraint (U - 1)).toLinearMap.ker := by
  rw [quantumMasterConstraint_ker_eq]
  exact finiteCyclicGaugeAverage_range_eq_constraint_ker U N hN hperiod

/-- Averaging powers of a self-adjoint gauge step gives a self-adjoint orbit sum. -/
theorem finiteCyclicGaugeSum_isSelfAdjoint
    (U : E →L[𝕜] E) (N : ℕ) (hU : IsSelfAdjoint U) :
    IsSelfAdjoint (finiteCyclicGaugeSum U N) := by
  rw [finiteCyclicGaugeSum]
  exact isSelfAdjoint_sum (Finset.range N) fun k _ => hU.pow k

/-- A normalized finite cyclic average of a self-adjoint gauge step is self-adjoint. -/
theorem finiteCyclicGaugeAverage_isSelfAdjoint
    (U : E →L[𝕜] E) (N : ℕ) (hU : IsSelfAdjoint U) :
    IsSelfAdjoint (finiteCyclicGaugeAverage U N) := by
  have hscalar : IsSelfAdjoint (((N : 𝕜)⁻¹) : 𝕜) := by
    rw [isSelfAdjoint_iff]
    simp
  exact hscalar.smul (finiteCyclicGaugeSum_isSelfAdjoint U N hU)

/-- A norm-preserving involution is automatically self-adjoint.  Algebraically, the adjoint is
a left inverse while the involution itself is a right inverse, so they coincide. -/
theorem isSelfAdjoint_of_adjoint_mul_self_of_sq_eq_one
    (U : E →L[𝕜] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) : IsSelfAdjoint U := by
  rw [isSelfAdjoint_iff]
  change U.adjoint = U
  calc
    U.adjoint = U.adjoint * 1 := by simp
    _ = U.adjoint * (U * U) := by rw [← pow_two, hsq]
    _ = (U.adjoint * U) * U := by rw [← mul_assoc]
    _ = U := by rw [hadjoint_mul, one_mul]

/-- For involutive unitary scattering, the optical theorem becomes linear: the quadratic master
constraint is exactly twice the complementary scattering sector.  Thus no genuinely new
quadratic hypothesis is introduced by replacing `U-1` with its master constraint. -/
theorem quantumMasterConstraint_involutiveScattering_eq_two_mul_complement
    (U : E →L[𝕜] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) :
    quantumMasterConstraint (U - 1) = 2 * (1 - U) := by
  have hUAdj : U.adjoint = U :=
    (isSelfAdjoint_of_adjoint_mul_self_of_sq_eq_one U hadjoint_mul hsq).star_eq
  rw [quantumMasterConstraint_unitarySubOne_eq_two_sub_self_sub_adjoint
    U hadjoint_mul, hUAdj]
  rw [show (2 : E →L[𝕜] E) = 1 + 1 by norm_num]
  noncomm_ring

/-- The `Z₂` group average of an involutive isometry is self-adjoint, hence (together with the
existing idempotence theorem) an orthogonal projection onto the invariant sector. -/
theorem finiteInvolutiveGaugeAverage_isSelfAdjoint
    (U : E →L[𝕜] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) :
    IsSelfAdjoint (finiteCyclicGaugeAverage U 2) :=
  finiteCyclicGaugeAverage_isSelfAdjoint U 2
    (isSelfAdjoint_of_adjoint_mul_self_of_sq_eq_one U hadjoint_mul hsq)

/-- The `Z₂` group average is idempotent with no separately supplied projection premise. -/
theorem finiteInvolutiveGaugeAverage_isIdempotentElem
    (U : E →L[𝕜] E) (hsq : U ^ 2 = 1) :
    IsIdempotentElem (finiteCyclicGaugeAverage U 2) := by
  change finiteCyclicGaugeAverage U 2 * finiteCyclicGaugeAverage U 2 =
    finiteCyclicGaugeAverage U 2
  exact finiteCyclicGaugeAverage_idempotent U 2 two_ne_zero hsq

/-- **Invariant/gauge-variant energy partition.**  The `Z₂` average of an involutive
isometry splits every kinematic vector orthogonally into its invariant part and its rejected
constraint residual.  Both orthogonality and idempotence are consequences of the two supplied
operator relations, so downstream users do not need a separate projection hypothesis. -/
theorem norm_finiteInvolutiveGaugeAverage_sq_add_complement_sq
    (U : E →L[𝕜] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (ψ : E) :
    ‖finiteCyclicGaugeAverage U 2 ψ‖ ^ 2 +
        ‖(1 - finiteCyclicGaugeAverage U 2) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  let P : E →L[𝕜] E := finiteCyclicGaugeAverage U 2
  have hPAdj : P.adjoint = P := by
    simpa only [P, ContinuousLinearMap.star_eq_adjoint] using
      (finiteInvolutiveGaugeAverage_isSelfAdjoint U hadjoint_mul hsq).star_eq
  have hPP : P * P = P :=
    finiteInvolutiveGaugeAverage_isIdempotentElem U hsq
  have horth : inner 𝕜 (P ψ) ((1 - P) ψ) = 0 := by
    have hfix : P (P ψ) = P ψ := by
      rw [← ContinuousLinearMap.mul_apply, hPP]
    calc
      inner 𝕜 (P ψ) ((1 - P) ψ) = inner 𝕜 (P ψ) (ψ - P ψ) := by simp
      _ = inner 𝕜 ψ (P.adjoint (ψ - P ψ)) :=
        (P.adjoint_inner_right ψ (ψ - P ψ)).symm
      _ = inner 𝕜 ψ (P (ψ - P ψ)) := by rw [hPAdj]
      _ = inner 𝕜 ψ (P ψ - P (P ψ)) := by rw [map_sub]
      _ = 0 := by rw [hfix, sub_self, inner_zero_right]
  have hsum : P ψ + (1 - P) ψ = ψ := by simp
  have hpyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P ψ) ((1 - P) ψ) horth
  change ‖P ψ‖ ^ 2 + ‖(1 - P) ψ‖ ^ 2 = ‖ψ‖ ^ 2
  simp only [pow_two]
  calc
    ‖P ψ‖ * ‖P ψ‖ + ‖(1 - P) ψ‖ * ‖(1 - P) ψ‖ =
        ‖P ψ + (1 - P) ψ‖ * ‖P ψ + (1 - P) ψ‖ := hpyth.symm
    _ = ‖ψ‖ * ‖ψ‖ := by rw [hsum]

end OrthogonalAverage

section WardConsumers

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Group averaging removes the physical-ket premise from the right Ward matrix element. -/
theorem finiteCyclicGaugeAverage_constraintRightWardMatrixElement_eq_zero
    (U R : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) (φ ψ : E) :
    inner 𝕜 φ (R ((U - 1) (finiteCyclicGaugeAverage U N ψ))) = 0 := by
  exact constraintRightWardMatrixElement_eq_zero (U - 1) R (φ := φ)
    (ψ := finiteCyclicGaugeAverage U N ψ)
    (finiteCyclicGaugeAverage_physical U N hperiod ψ)

/-- Group averaging removes the physical-state premise from the constraint Ward value. -/
theorem finiteCyclicGaugeAverage_constraintWardValue_eq_zero
    (U A : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1)
    (hC : IsSelfAdjoint (U - 1)) (ψ : E) :
    inner 𝕜 (finiteCyclicGaugeAverage U N ψ)
      ((U - 1) (A (finiteCyclicGaugeAverage U N ψ))) = 0 := by
  exact constraintWardValue_eq_zero (U - 1) A hC
    (finiteCyclicGaugeAverage_physical U N hperiod ψ)

/-- Group averaging removes both physical-state premises from constraint-ideal representative
independence. -/
theorem finiteCyclicGaugeAverage_matrixElement_congr_mod_constraintTwoSidedIdeal
    (U A B L R : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1)
    (hC : IsSelfAdjoint (U - 1))
    (hmod : B = A + ((U - 1) * L + R * (U - 1))) (φ ψ : E) :
    inner 𝕜 (finiteCyclicGaugeAverage U N φ)
        (B (finiteCyclicGaugeAverage U N ψ)) =
      inner 𝕜 (finiteCyclicGaugeAverage U N φ)
        (A (finiteCyclicGaugeAverage U N ψ)) := by
  exact physicalMatrixElement_congr_mod_constraintTwoSidedIdeal
    (U - 1) A B L R hC hmod
    (finiteCyclicGaugeAverage_physical U N hperiod φ)
    (finiteCyclicGaugeAverage_physical U N hperiod ψ)

/-- Combining group averaging with the master constraint removes both the assumed physical-state
premise and the assumed self-adjointness premise from the Ward value. -/
theorem finiteCyclicGaugeAverage_masterConstraintWardValue_eq_zero
    (U A : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) (ψ : E) :
    inner 𝕜 (finiteCyclicGaugeAverage U N ψ)
      (quantumMasterConstraint (U - 1)
        (A (finiteCyclicGaugeAverage U N ψ))) = 0 := by
  exact quantumMasterConstraint_WardValue_eq_zero (U - 1) A
    (finiteCyclicGaugeAverage_physical U N hperiod ψ)

/-- Combining group averaging with the master constraint gives constraint-ideal representative
independence for arbitrary input vectors and an arbitrary bounded gauge step of finite period. -/
theorem finiteCyclicGaugeAverage_matrixElement_congr_mod_masterConstraintIdeal
    (U A B L R : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1)
    (hmod : B = A +
      (quantumMasterConstraint (U - 1) * L + R * quantumMasterConstraint (U - 1)))
    (φ ψ : E) :
    inner 𝕜 (finiteCyclicGaugeAverage U N φ)
        (B (finiteCyclicGaugeAverage U N ψ)) =
      inner 𝕜 (finiteCyclicGaugeAverage U N φ)
        (A (finiteCyclicGaugeAverage U N ψ)) := by
  exact physicalMatrixElement_congr_mod_quantumMasterConstraintIdeal
    (U - 1) A B L R hmod
    (finiteCyclicGaugeAverage_physical U N hperiod φ)
    (finiteCyclicGaugeAverage_physical U N hperiod ψ)

end WardConsumers

end HTGeometry

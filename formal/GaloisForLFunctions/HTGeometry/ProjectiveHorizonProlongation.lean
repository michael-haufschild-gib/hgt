import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPrincipalSymbol
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchwarzianMeet

/-!
# The prolongation formula

Differentiating an observable of order zero `m` times produces an observable of order `m` whose
derivative along the `j`-th coordinate is a binomial coefficient times the `(m-j)`-th derivative of
its own order-zero derivative.

The two commutation rules do all the work: the jet shift commutes with the zeroth coordinate
derivation and lowers every later one by one, so the binomial coefficients appear exactly through
Pascal's rule.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
theorem freeJetShift_comm_zero (f : FreeScalarJetField C) :
    freeCoordinateDerivation C ℕ 0 (freeJetShift C f) =
      freeJetShift C (freeCoordinateDerivation C ℕ 0 f) := by
  have h := congrArg
    (fun D : Derivation C (FreeScalarJetField C) (FreeScalarJetField C) => D f)
    (freeCoordinateDerivation_zero_lie_shift C)
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact (sub_eq_zero.1 h).symm

omit [CharZero C] in
/-- **The prolongation formula.**  For an observable of order zero, the derivative of its `m`-th jet
along the `j`-th coordinate is `m choose j` times the `(m-j)`-th jet of its order-zero
derivative. -/
theorem freeCoordinateDerivation_shift_iterate_binomial {u : FreeScalarJetField C}
    (hu : ∀ j : ℕ, 0 < j → freeCoordinateDerivation C ℕ j u = 0) :
    ∀ (m j : ℕ), j ≤ m →
      freeCoordinateDerivation C ℕ j ((freeJetShift C)^[m] u) =
        (Nat.choose m j : FreeScalarJetField C) *
          (freeJetShift C)^[m - j] (freeCoordinateDerivation C ℕ 0 u) := by
  intro m
  induction m with
  | zero =>
      intro j hj
      obtain rfl : j = 0 := by omega
      rw [Function.iterate_zero_apply, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_self, Function.iterate_zero_apply]
  | succ m ih =>
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rw [Function.iterate_succ_apply', freeJetShift_comm_zero, ih 0 (by omega),
          Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
          Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
          Function.iterate_succ_apply']
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hcast : freeJetShift C
            (((Nat.choose m (j' + 1) : ℕ) : FreeScalarJetField C)) = 0 := by
          rw [show ((Nat.choose m (j' + 1) : ℕ) : FreeScalarJetField C) =
            algebraMap C (FreeScalarJetField C) ((Nat.choose m (j' + 1) : ℕ) : C) from by
            push_cast
            ring]
          exact Derivation.map_algebraMap _ _
        rw [Function.iterate_succ_apply', freeCoordinateDerivation_shift_apply]
        rcases Nat.lt_or_ge m (j' + 1) with hlt | hge
        · obtain rfl : m = j' := by omega
          rw [freeCoordinateDerivation_shift_iterate_of_gt hu m (m + 1) (by omega),
            map_zero, zero_add, ih m le_rfl]
          simp
        · rw [ih (j' + 1) hge, ih j' (by omega), Derivation.leibniz, hcast, smul_zero,
            add_zero, smul_eq_mul,
            show m + 1 - (j' + 1) = m - j' from by omega,
            show m - j' = m - (j' + 1) + 1 from by omega,
            Function.iterate_succ_apply', Nat.choose_succ_succ]
          push_cast
          ring

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.SelbergClass.Primon.KestenShiftResolvent
import GaloisForLFunctions.SelbergClass.Primon.KestenGreenResolventIdentity

/-!
# The rank-one boundary correction to geometric covariance

Let `F = (I-qS)⁻¹`, with `q=1/p`. The geometric covariance `F* F`
has kernel `q^|n-m|/(1-q²)`. The prime Green operator is exactly
`q F* F - q²/(1-q²) |W_p⟩⟨W_p|`. Both factorizations of its inverse
pencil identify the boundary term, and give an exact energy identity.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem inner_state_smul_left (a : ℝ) (f g : KestenLikelihoodHilbert) :
    inner ℝ (a • f) g = a * inner ℝ f g := by
  simpa only [conj_trivial] using (_root_.inner_smul_left (𝕜 := ℝ) f g a)

private theorem inner_state_smul_right (a : ℝ) (f g : KestenLikelihoodHilbert) :
    inner ℝ f (a • g) = a * inner ℝ f g :=
  _root_.inner_smul_right (𝕜 := ℝ) f g a

/-- The positive Gram operator of the geometric shift inverse. -/
def kestenGeometricCovariance (p : Nat.Primes) :
    KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert :=
  (kestenShiftResolvent p).adjoint * kestenShiftResolvent p

@[simp] theorem kestenGeometricCovariance_apply (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenGeometricCovariance p f =
      (kestenShiftResolvent p).adjoint (kestenShiftResolvent p f) := rfl

/-- Geometric covariance is the actual Gram form of the bounded shift inverse. -/
theorem inner_kestenGeometricCovariance (p : Nat.Primes) (f g : KestenLikelihoodHilbert) :
    inner ℝ f (kestenGeometricCovariance p g) =
      inner ℝ (kestenShiftResolvent p f) (kestenShiftResolvent p g) := by
  rw [kestenGeometricCovariance_apply, ContinuousLinearMap.adjoint_inner_right]

theorem inner_kestenGeometricCovariance_self (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    inner ℝ f (kestenGeometricCovariance p f) = ‖kestenShiftResolvent p f‖ ^ 2 := by
  rw [inner_kestenGeometricCovariance, real_inner_self_eq_norm_sq]

/-- The geometric covariance has stationary character matrix entries. -/
theorem inner_kestenGeometricCovariance_characters (p : Nat.Primes) (n m : ℕ) :
    inner ℝ (kestenCharacterState n) (kestenGeometricCovariance p (kestenCharacterState m)) =
      primeReciprocal p ^ Nat.dist n m / (1 - primeReciprocal p ^ 2) := by
  rw [inner_kestenGeometricCovariance, inner_kestenShiftResolvent_characters]

/-- The covariance response to the constant character is a scalar prime likelihood. -/
theorem kestenGeometricCovariance_vacuum (p : Nat.Primes) :
    kestenGeometricCovariance p (kestenCharacterState 0) =
      (1 - primeReciprocal p ^ 2)⁻¹ • kestenPrimeState p := by
  rw [kestenGeometricCovariance_apply, kestenShiftResolvent_vacuum,
    kestenShiftResolvent_adjoint_prime]

/-- The constant covariance coordinate is the likelihood readout of the source. -/
theorem hardyCoordinate_kestenGeometricCovariance_zero (p : Nat.Primes)
    (f : KestenLikelihoodHilbert) :
    hardyLikelihoodUnitary.symm (kestenGeometricCovariance p f) 0 =
      (1 - primeReciprocal p ^ 2)⁻¹ * inner ℝ (kestenPrimeState p) f := by
  rw [← inner_kestenCharacterState, inner_kestenGeometricCovariance,
    kestenShiftResolvent_vacuum, ← ContinuousLinearMap.adjoint_inner_left,
    kestenShiftResolvent_adjoint_prime, inner_state_smul_left]

/-- The forward-first factorization has a positive rank-one constant-coordinate remainder. -/
theorem kestenPrimePencil_factor_forward (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenPrimePencil p f =
      kestenShiftPencil p f - primeReciprocal p • kestenBackshift (kestenShiftPencil p f) +
        (primeReciprocal p * hardyLikelihoodUnitary.symm f 0) • kestenCharacterState 0 := by
  rw [kestenPrimePencil_apply, kestenSquareJacobi_eq_shift, kestenShiftPencil_apply,
    map_sub, map_smul, kestenBackshift_shift]
  module

/-- Reversing the first-order factors changes the boundary coefficient to `q(1+q)`. -/
theorem kestenPrimePencil_factor_backward (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenPrimePencil p f =
      kestenShiftPencil p (f - primeReciprocal p • kestenBackshift f) +
        (primeReciprocal p * (1 + primeReciprocal p) * hardyLikelihoodUnitary.symm f 0) •
          kestenCharacterState 0 := by
  rw [kestenPrimePencil_apply, kestenSquareJacobi_eq_shift, kestenShiftPencil_apply,
    map_sub, map_smul, kestenShift_backshift]
  module

/-- The prime pencil energy is a squared first-order difference plus an exact boundary energy. -/
theorem inner_kestenPrimePencil_energy (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    inner ℝ f (kestenPrimePencil p f) =
      ‖kestenShiftPencil p f‖ ^ 2 + primeReciprocal p * (hardyLikelihoodUnitary.symm f 0) ^ 2 := by
  rw [kestenPrimePencil_factor_forward, inner_add_right, ← inner_kestenShiftPencil,
    real_inner_self_eq_norm_sq, inner_state_smul_right,
    real_inner_comm (kestenCharacterState 0) f, inner_kestenCharacterState]
  ring

/-- Applying the prime pencil to geometric covariance leaves only a constant boundary source. -/
theorem kestenPrimePencil_geometricCovariance (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenPrimePencil p (kestenGeometricCovariance p f) = f +
      (primeReciprocal p * (1 + primeReciprocal p) * (1 - primeReciprocal p ^ 2)⁻¹ *
        inner ℝ (kestenPrimeState p) f) • kestenCharacterState 0 := by
  rw [kestenPrimePencil_factor_backward, hardyCoordinate_kestenGeometricCovariance_zero,
    kestenGeometricCovariance_apply, kestenBackshiftPencil_adjoint_resolvent,
    kestenShiftPencil_resolvent]
  module

/-- The Green operator is geometric covariance minus an exact likelihood rank-one correction. -/
theorem kestenGreenOperator_boundary_correction (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenGreenOperator p f = primeReciprocal p • kestenGeometricCovariance p f -
      (primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) * inner ℝ (kestenPrimeState p) f) •
        kestenPrimeState p := by
  calc
    _ = kestenPrimeResolvent p (primeReciprocal p • f) := by
      rw [map_smul, kestenGreenOperator_apply]
    _ = kestenPrimeResolvent p (kestenPrimePencil p
        (primeReciprocal p • kestenGeometricCovariance p f -
          (primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) *
            inner ℝ (kestenPrimeState p) f) • kestenPrimeState p)) := by
      congr 1
      rw [map_sub, map_smul, map_smul, kestenPrimePencil_geometricCovariance,
        kestenPrimePencil_prime]
      simp only [div_eq_mul_inv]
      module
    _ = _ := kestenPrimeResolvent_pencil p _

/-- Green energy is a geometric-filter energy minus a single likelihood-coordinate square. -/
theorem inner_kestenGreenOperator_boundary_energy (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    inner ℝ f (kestenGreenOperator p f) =
      primeReciprocal p * ‖kestenShiftResolvent p f‖ ^ 2 -
        primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) * (inner ℝ (kestenPrimeState p) f) ^ 2 := by
  rw [kestenGreenOperator_boundary_correction, inner_sub_right,
    inner_state_smul_right, inner_state_smul_right, inner_kestenGeometricCovariance_self,
    real_inner_comm (kestenPrimeState p) f]
  ring

/-- The opposite covariance order has an unamplified boundary likelihood readout. -/
theorem kestenPrimePencil_causalCovariance (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenPrimePencil p (kestenShiftResolvent p ((kestenShiftResolvent p).adjoint f)) =
      f + (primeReciprocal p * inner ℝ (kestenPrimeState p) f) • kestenCharacterState 0 := by
  have hc : hardyLikelihoodUnitary.symm
      (kestenShiftResolvent p ((kestenShiftResolvent p).adjoint f)) 0 =
        inner ℝ (kestenPrimeState p) f := by
    rw [hardyCoordinate_kestenShiftResolvent_zero, ← inner_kestenCharacterState,
      ContinuousLinearMap.adjoint_inner_right, kestenShiftResolvent_vacuum]
  rw [kestenPrimePencil_factor_forward, kestenShiftPencil_resolvent,
    kestenBackshiftPencil_adjoint_resolvent, hc]

/-- The Green operator also has a causal covariance factorization with a boundary rank-one correction. -/
theorem kestenGreenOperator_causal_correction (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenGreenOperator p f =
      primeReciprocal p • kestenShiftResolvent p ((kestenShiftResolvent p).adjoint f) -
        (primeReciprocal p ^ 2 / (1 + primeReciprocal p) * inner ℝ (kestenPrimeState p) f) •
          kestenPrimeState p := by
  have hne : 1 + primeReciprocal p ≠ 0 := by have := primeReciprocal_pos p; positivity
  have hs : (primeReciprocal p ^ 2 / (1 + primeReciprocal p) * inner ℝ (kestenPrimeState p) f) *
      (1 + primeReciprocal p) = primeReciprocal p ^ 2 * inner ℝ (kestenPrimeState p) f := by
    field_simp
  calc
    _ = kestenPrimeResolvent p (primeReciprocal p • f) := by
      rw [map_smul, kestenGreenOperator_apply]
    _ = kestenPrimeResolvent p (kestenPrimePencil p
        (primeReciprocal p • kestenShiftResolvent p ((kestenShiftResolvent p).adjoint f) -
          (primeReciprocal p ^ 2 / (1 + primeReciprocal p) *
            inner ℝ (kestenPrimeState p) f) • kestenPrimeState p)) := by
      congr 1
      rw [map_sub, map_smul, map_smul, kestenPrimePencil_causalCovariance,
        kestenPrimePencil_prime]
      simp only [smul_add, smul_smul]
      rw [hs]
      module
    _ = _ := kestenPrimeResolvent_pencil p _

end
end GaloisForLFunctions.SelbergClass.Primon

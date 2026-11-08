import GaloisForLFunctions.SelbergClass.Primon.KestenShiftCyclicity
import GaloisForLFunctions.HTGeometry.CoerciveOperatorInvertible

/-!
# The geometric shift resolvent on prime likelihoods

The difference `I - p⁻¹ S` is coercive and has a bounded inverse on the
whole likelihood space. Its columns are exactly the normalized prime
tails. Consequently its Gram operator has the geometric half-line
kernel, and its adjoint acts explicitly on prime likelihoods.
-/

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem inner_state_smul_left (a : ℝ) (f g : KestenLikelihoodHilbert) :
    inner ℝ (a • f) g = a * inner ℝ f g := by
  simpa only [conj_trivial] using (_root_.inner_smul_left (𝕜 := ℝ) f g a)

private theorem inner_state_smul_right (a : ℝ) (f g : KestenLikelihoodHilbert) :
    inner ℝ f (a • g) = a * inner ℝ f g :=
  _root_.inner_smul_right (𝕜 := ℝ) f g a

/-- The geometric difference of the even-character shift. -/
def kestenShiftPencil (p : Nat.Primes) : KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert :=
  ContinuousLinearMap.id ℝ KestenLikelihoodHilbert - primeReciprocal p • kestenShift.toContinuousLinearMap

@[simp] theorem kestenShiftPencil_apply (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenShiftPencil p f = f - primeReciprocal p • kestenShift f := rfl

/-- The first-order prime difference has the positive coercive floor `1-1/p`. -/
theorem kestenShiftPencil_coercive (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    (1 - primeReciprocal p) * ‖f‖ * ‖f‖ ≤ inner ℝ (kestenShiftPencil p f) f := by
  have hs : inner ℝ (kestenShift f) f ≤ ‖f‖ * ‖f‖ := by
    simpa only [kestenShift.norm_map] using real_inner_le_norm (kestenShift f) f
  rw [kestenShiftPencil_apply, inner_sub_left, inner_state_smul_left, real_inner_self_eq_norm_sq]
  nlinarith only [mul_le_mul_of_nonneg_left hs (primeReciprocal_pos p).le]

private def shiftPencilEquiv (p : Nat.Primes) :
    KestenLikelihoodHilbert ≃L[ℝ] KestenLikelihoodHilbert :=
  coerciveEquiv (sub_pos.mpr (primeReciprocal_lt_one p)) (kestenShiftPencil_coercive p)

private theorem shiftPencilEquiv_apply (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    shiftPencilEquiv p f = kestenShiftPencil p f :=
  coerciveEquiv_apply (sub_pos.mpr (primeReciprocal_lt_one p)) (kestenShiftPencil_coercive p) f

/-- The bounded inverse of `I - p⁻¹ S`. -/
def kestenShiftResolvent (p : Nat.Primes) : KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert :=
  (shiftPencilEquiv p).symm.toContinuousLinearMap

theorem kestenShiftPencil_resolvent (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenShiftPencil p (kestenShiftResolvent p f) = f := by
  change kestenShiftPencil p ((shiftPencilEquiv p).symm f) = f
  rw [← shiftPencilEquiv_apply]
  exact (shiftPencilEquiv p).apply_symm_apply f

theorem kestenShiftResolvent_pencil (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenShiftResolvent p (kestenShiftPencil p f) = f := by
  change (shiftPencilEquiv p).symm (kestenShiftPencil p f) = f
  rw [← shiftPencilEquiv_apply]
  exact (shiftPencilEquiv p).symm_apply_apply f

/-- A geometric difference extracts the leading character from a prime tail. -/
theorem kestenShiftPencil_tail (p : Nat.Primes) (n : ℕ) :
    kestenShiftPencil p (kestenTailState p n) = kestenCharacterState n := by
  rw [kestenShiftPencil_apply, kestenShift_tail, kestenTailState_innovation]

/-- Every column of the bounded inverse is an actual normalized likelihood tail. -/
theorem kestenShiftResolvent_character (p : Nat.Primes) (n : ℕ) :
    kestenShiftResolvent p (kestenCharacterState n) = kestenTailState p n := by
  rw [← kestenShiftPencil_tail p n, kestenShiftResolvent_pencil]

theorem kestenShiftResolvent_vacuum (p : Nat.Primes) :
    kestenShiftResolvent p (kestenCharacterState 0) = kestenPrimeState p := by
  rw [kestenShiftResolvent_character, kestenTailState_zero]

/-- The causal geometric inverse preserves the constant coordinate of every source. -/
theorem hardyCoordinate_kestenShiftResolvent_zero (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    hardyLikelihoodUnitary.symm (kestenShiftResolvent p f) 0 = hardyLikelihoodUnitary.symm f 0 := by
  have h := congrArg (fun g : KestenLikelihoodHilbert => hardyLikelihoodUnitary.symm g 0)
    (kestenShiftPencil_resolvent p f)
  simpa [kestenShiftPencil_apply, map_sub, map_smul, hardyCoordinate_kestenShift, shiftSeq_zero] using h

/-- The inverse has the lower triangular geometric matrix in character coordinates. -/
theorem hardyCoordinate_kestenShiftResolvent_character (p : Nat.Primes) (n m : ℕ) :
    hardyLikelihoodUnitary.symm (kestenShiftResolvent p (kestenCharacterState n)) m =
      if n ≤ m then primeReciprocal p ^ (m - n) else 0 := by
  rw [kestenShiftResolvent_character, hardyCoordinate_kestenTailState]

/-- The inverse norm is bounded by the reciprocal coercive gap. -/
theorem norm_kestenShiftResolvent_le (p : Nat.Primes) :
    ‖kestenShiftResolvent p‖ ≤ (1 - primeReciprocal p)⁻¹ := by
  have hgap : 0 < 1 - primeReciprocal p := sub_pos.mpr (primeReciprocal_lt_one p)
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hgap.le)
  intro f
  have h := kestenShiftPencil_coercive p (kestenShiftResolvent p f)
  rw [kestenShiftPencil_resolvent] at h
  have hh := h.trans (real_inner_le_norm f (kestenShiftResolvent p f))
  rcases eq_or_lt_of_le (norm_nonneg (kestenShiftResolvent p f)) with hz | hz
  · rw [← hz]
    positivity
  · have hb := le_of_mul_le_mul_right hh hz
    have hd : ‖kestenShiftResolvent p f‖ ≤ ‖f‖ / (1 - primeReciprocal p) :=
      (le_div_iff₀ hgap).2 (by simpa only [mul_comm] using hb)
    simpa only [div_eq_mul_inv, mul_comm] using hd

/-- The adjoint geometric inverse has the transposed triangular matrix. -/
theorem hardyCoordinate_kestenShiftResolvent_adjoint_character (p : Nat.Primes) (n m : ℕ) :
    hardyLikelihoodUnitary.symm ((kestenShiftResolvent p).adjoint (kestenCharacterState n)) m =
      if m ≤ n then primeReciprocal p ^ (n - m) else 0 := by
  rw [← inner_kestenCharacterState,
    ContinuousLinearMap.adjoint_inner_right, real_inner_comm (kestenCharacterState n),
    inner_kestenCharacterState, hardyCoordinate_kestenShiftResolvent_character]

/-- The shift resolvent Gram kernel is the exact geometric tail kernel. -/
theorem inner_kestenShiftResolvent_characters (p : Nat.Primes) (n m : ℕ) :
    inner ℝ (kestenShiftResolvent p (kestenCharacterState n))
      (kestenShiftResolvent p (kestenCharacterState m)) =
        primeReciprocal p ^ Nat.dist n m / (1 - primeReciprocal p ^ 2) := by
  rw [kestenShiftResolvent_character, kestenShiftResolvent_character]
  change inner ℝ (kestenNormalizedTail p n) (kestenNormalizedTail p m) = _
  exact inner_kestenNormalizedTail p n m

/-- A prime likelihood is an eigenvector of the adjoint geometric resolvent. -/
theorem kestenShiftResolvent_adjoint_prime (p : Nat.Primes) :
    (kestenShiftResolvent p).adjoint (kestenPrimeState p) =
      (1 - primeReciprocal p ^ 2)⁻¹ • kestenPrimeState p := by
  apply hardyLikelihoodUnitary.symm.injective
  apply lp.ext
  funext n
  rw [← inner_kestenCharacterState]
  calc
    _ = inner ℝ (kestenShiftResolvent p (kestenCharacterState n))
        (kestenShiftResolvent p (kestenCharacterState 0)) := by
      rw [ContinuousLinearMap.adjoint_inner_right, kestenShiftResolvent_vacuum]
    _ = primeReciprocal p ^ n / (1 - primeReciprocal p ^ 2) := by
      rw [inner_kestenShiftResolvent_characters,
        Nat.dist_eq_sub_of_le_right (Nat.zero_le n), Nat.sub_zero]
    _ = _ := by
      simp only [map_smul, kestenPrimeState, hardyLikelihoodUnitary.symm_apply_apply,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, primeHardyKernel, hardyKernel_apply,
        div_eq_mul_inv]
      ring

/-- The backward difference is the adjoint of the forward difference. -/
theorem inner_kestenShiftPencil (p : Nat.Primes) (f g : KestenLikelihoodHilbert) :
    inner ℝ (kestenShiftPencil p f) g = inner ℝ f (g - primeReciprocal p • kestenBackshift g) := by
  rw [kestenShiftPencil_apply, inner_sub_left, inner_sub_right,
    inner_state_smul_left, inner_state_smul_right]
  congr 1
  congr 1
  exact (ContinuousLinearMap.adjoint_inner_right kestenShift.toContinuousLinearMap f g).symm

/-- The adjoint resolvent solves the backward first-order difference equation. -/
theorem kestenBackshiftPencil_adjoint_resolvent (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    (kestenShiftResolvent p).adjoint f -
      primeReciprocal p • kestenBackshift ((kestenShiftResolvent p).adjoint f) = f := by
  apply ext_inner_left ℝ
  intro g
  rw [← inner_kestenShiftPencil, ContinuousLinearMap.adjoint_inner_right, kestenShiftResolvent_pencil]

/-- Applying the backward difference before the adjoint resolvent also cancels. -/
theorem kestenShiftResolvent_adjoint_backshiftPencil (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    (kestenShiftResolvent p).adjoint (f - primeReciprocal p • kestenBackshift f) = f := by
  apply ext_inner_left ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_kestenShiftPencil, kestenShiftPencil_resolvent]

end
end GaloisForLFunctions.SelbergClass.Primon

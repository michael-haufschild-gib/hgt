import GaloisForLFunctions.SelbergClass.Primon.KestenSquareJacobi
import GaloisForLFunctions.HTGeometry.CoerciveOperatorInvertible

/-!
# Prime likelihoods are bounded square-Jacobi resolvents

For `q = 1/p`, the operator `(1+q)² I - q J` has coercive floor `(1-q)²`.
Real Lax–Milgram therefore gives an actual bounded inverse on the whole
likelihood Hilbert space. Its action is multiplication by `W_p/(1+q)`, and
its constant-source response recovers the prime likelihood itself.
-/

open MeasureTheory
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

/-- The prime evaluation of the square-coordinate resolvent pencil. -/
def kestenPrimePencil (p : Nat.Primes) : KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert :=
  ((1 + primeReciprocal p) ^ 2) • ContinuousLinearMap.id ℝ KestenLikelihoodHilbert -
    primeReciprocal p • kestenSquareJacobi

@[simp] theorem kestenPrimePencil_apply (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenPrimePencil p f = ((1 + primeReciprocal p) ^ 2) • f -
      primeReciprocal p • kestenSquareJacobi f := rfl

/-- Every reciprocal-prime resolvent has a strictly positive gap from the square spectral interval. -/
theorem kestenPrimePencil_gap_pos (p : Nat.Primes) : 0 < (1 - primeReciprocal p) ^ 2 := by
  have h : 0 < 1 - primeReciprocal p := sub_pos.mpr (primeReciprocal_lt_one p)
  positivity

/-- The prime pencil has the unconditional coercive floor `(1 - 1/p)²`. -/
theorem kestenPrimePencil_coercive (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    (1 - primeReciprocal p) ^ 2 * ‖f‖ * ‖f‖ ≤ inner ℝ (kestenPrimePencil p f) f := by
  have hj : inner ℝ (kestenSquareJacobi f) f ≤ 4 * ‖f‖ * ‖f‖ := by
    apply (real_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
    exact (kestenSquareJacobi.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right norm_kestenSquareJacobi_le (norm_nonneg f))
  rw [kestenPrimePencil_apply, inner_sub_left, inner_state_smul_left, inner_state_smul_left]
  simp only [conj_trivial, real_inner_self_eq_norm_sq]
  nlinarith only [mul_le_mul_of_nonneg_left hj (primeReciprocal_pos p).le]

/-- The prime pencil is self-adjoint. -/
theorem inner_kestenPrimePencil (p : Nat.Primes) (f g : KestenLikelihoodHilbert) :
    inner ℝ (kestenPrimePencil p f) g = inner ℝ f (kestenPrimePencil p g) := by
  simp only [kestenPrimePencil_apply, inner_sub_left, inner_sub_right,
    inner_state_smul_left, inner_state_smul_right, inner_kestenSquareJacobi]

private def kestenPrimePencilEquiv (p : Nat.Primes) : KestenLikelihoodHilbert ≃L[ℝ] KestenLikelihoodHilbert :=
  coerciveEquiv (kestenPrimePencil_gap_pos p) (kestenPrimePencil_coercive p)

private theorem kestenPrimePencilEquiv_apply (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenPrimePencilEquiv p f = kestenPrimePencil p f :=
  coerciveEquiv_apply (kestenPrimePencil_gap_pos p) (kestenPrimePencil_coercive p) f

/-- The bounded inverse of the prime square-coordinate pencil, constructed by real Lax–Milgram. -/
def kestenPrimeResolvent (p : Nat.Primes) : KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert :=
  (kestenPrimePencilEquiv p).symm.toContinuousLinearMap

/-- The constructed resolvent solves every likelihood-space source equation. -/
theorem kestenPrimePencil_resolvent (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenPrimePencil p (kestenPrimeResolvent p f) = f := by
  change kestenPrimePencil p ((kestenPrimePencilEquiv p).symm f) = f
  rw [← kestenPrimePencilEquiv_apply]
  exact (kestenPrimePencilEquiv p).apply_symm_apply f

/-- The constructed resolvent is also a left inverse, so the solution is unique. -/
theorem kestenPrimeResolvent_pencil (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenPrimeResolvent p (kestenPrimePencil p f) = f := by
  change (kestenPrimePencilEquiv p).symm (kestenPrimePencil p f) = f
  rw [← kestenPrimePencilEquiv_apply]
  exact (kestenPrimePencilEquiv p).symm_apply_apply f

/-- The prime likelihood solves the pencil equation with constant source `1 + 1/p`. -/
theorem kestenPrimePencil_prime (p : Nat.Primes) :
    kestenPrimePencil p (kestenPrimeState p) = (1 + primeReciprocal p) • kestenCharacterState 0 :=
  kestenSquareJacobi_prime_resolvent p

/-- The inverse applied to the constant state is the normalized prime likelihood. -/
theorem kestenPrimeResolvent_vacuum (p : Nat.Primes) :
    kestenPrimeResolvent p (kestenCharacterState 0) =
      (1 + primeReciprocal p)⁻¹ • kestenPrimeState p := by
  have h := kestenPrimeResolvent_pencil p (kestenPrimeState p)
  rw [kestenPrimePencil_prime, map_smul] at h
  have hne : 1 + primeReciprocal p ≠ 0 := by have := primeReciprocal_pos p; positivity
  calc
    _ = (1 + primeReciprocal p)⁻¹ •
        ((1 + primeReciprocal p) • kestenPrimeResolvent p (kestenCharacterState 0)) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = _ := by rw [h]

/-- The constant-state resolvent average is the exact reciprocal `1/(1 + 1/p)`. -/
theorem kestenPrimeResolvent_vacuum_average (p : Nat.Primes) :
    inner ℝ (kestenCharacterState 0) (kestenPrimeResolvent p (kestenCharacterState 0)) =
      (1 + primeReciprocal p)⁻¹ := by
  rw [kestenPrimeResolvent_vacuum, inner_state_smul_right, inner_kestenCharacterState]
  simp [kestenPrimeState, primeHardyKernel, hardyKernel_apply]

/-- The inverse norm is bounded by the reciprocal of the explicit coercive gap. -/
theorem norm_kestenPrimeResolvent_le (p : Nat.Primes) :
    ‖kestenPrimeResolvent p‖ ≤ ((1 - primeReciprocal p) ^ 2)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have hc := kestenPrimePencil_gap_pos p
  have h := kestenPrimePencil_coercive p (kestenPrimeResolvent p f)
  rw [kestenPrimePencil_resolvent] at h
  have hh := h.trans (real_inner_le_norm f (kestenPrimeResolvent p f))
  rcases eq_or_lt_of_le (norm_nonneg (kestenPrimeResolvent p f)) with hz | hz
  · rw [← hz]
    positivity
  · have hb := le_of_mul_le_mul_right hh hz
    have hd : ‖kestenPrimeResolvent p f‖ ≤ ‖f‖ / (1 - primeReciprocal p) ^ 2 :=
      (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hb)
    simpa only [div_eq_mul_inv, mul_comm] using hd

/-- Inverting the self-adjoint pencil preserves self-adjointness. -/
theorem inner_kestenPrimeResolvent (p : Nat.Primes) (f g : KestenLikelihoodHilbert) :
    inner ℝ (kestenPrimeResolvent p f) g = inner ℝ f (kestenPrimeResolvent p g) := by
  have h := inner_kestenPrimePencil p (kestenPrimeResolvent p f) (kestenPrimeResolvent p g)
  rw [kestenPrimePencil_resolvent, kestenPrimePencil_resolvent] at h
  exact h.symm

/-- Every prime resolvent is a positive operator. -/
theorem inner_kestenPrimeResolvent_nonneg (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    0 ≤ inner ℝ f (kestenPrimeResolvent p f) := by
  have h := kestenPrimePencil_coercive p (kestenPrimeResolvent p f)
  rw [kestenPrimePencil_resolvent] at h
  exact (mul_nonneg (mul_nonneg (kestenPrimePencil_gap_pos p).le (norm_nonneg _))
    (norm_nonneg _)).trans h

/-- The pencil is literal multiplication by its quadratic spectral denominator. -/
theorem kestenPrimePencil_ae (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    (kestenPrimePencil p f : SemicircleL2) =ᵐ[(semicircleSpectralLaw : Measure ℝ)]
      fun x => ((1 + primeReciprocal p) ^ 2 - primeReciprocal p * x ^ 2) * (f : SemicircleL2) x := by
  change (((1 + primeReciprocal p) ^ 2) • (f : SemicircleL2) -
    primeReciprocal p • semicircleSquareMul (f : SemicircleL2) : SemicircleL2) =ᵐ[_] _
  filter_upwards [Lp.coeFn_sub (((1 + primeReciprocal p) ^ 2) • (f : SemicircleL2))
    (primeReciprocal p • semicircleSquareMul (f : SemicircleL2)),
    Lp.coeFn_smul ((1 + primeReciprocal p) ^ 2) (f : SemicircleL2),
    Lp.coeFn_smul (primeReciprocal p) (semicircleSquareMul (f : SemicircleL2)),
    semicircleSquareMul_ae (f : SemicircleL2)] with x hs hl hr hm
  simp only [hs, Pi.sub_apply, hl, hr, Pi.smul_apply, smul_eq_mul, hm]
  ring

private theorem kestenPrimeState_ae (p : Nat.Primes) :
    (kestenPrimeState p : SemicircleL2) =ᵐ[(semicircleSpectralLaw : Measure ℝ)] kestenLikelihood p := by
  rw [coe_kestenPrimeState]
  exact coeFn_semicircleL2Observable ⟨_, continuous_kestenLikelihood p⟩

private theorem kestenVacuumState_ae :
    (kestenCharacterState 0 : SemicircleL2) =ᵐ[(semicircleSpectralLaw : Measure ℝ)] fun _ => 1 := by
  rw [coe_kestenCharacterState]
  change semicircleL2Observable (spectralCharacter 0) =ᵐ[_] _
  filter_upwards [coeFn_semicircleL2Observable (spectralCharacter 0)] with x hx
  rw [hx, spectralCharacter_zero]

/-- The actual likelihood cancels the prime quadratic spectral denominator almost everywhere. -/
theorem kestenPrimePencil_likelihood_ae (p : Nat.Primes) :
    (fun x => ((1 + primeReciprocal p) ^ 2 - primeReciprocal p * x ^ 2) * kestenLikelihood p x)
      =ᵐ[(semicircleSpectralLaw : Measure ℝ)] fun _ => 1 + primeReciprocal p := by
  have h := kestenPrimePencil_ae p (kestenPrimeState p)
  rw [kestenPrimePencil_prime] at h
  filter_upwards [h, Lp.coeFn_smul (1 + primeReciprocal p) (kestenCharacterState 0 : SemicircleL2),
    kestenVacuumState_ae, kestenPrimeState_ae p] with x hx hs hv hw
  change ((1 + primeReciprocal p) • (kestenCharacterState 0 : SemicircleL2) : SemicircleL2) x = _ at hx
  simp only [hs, Pi.smul_apply, smul_eq_mul, hv, hw, mul_one] at hx
  exact hx.symm

/-- The constructed inverse is actual multiplication by the normalized prime likelihood. -/
theorem kestenPrimeResolvent_ae (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    (kestenPrimeResolvent p f : SemicircleL2) =ᵐ[(semicircleSpectralLaw : Measure ℝ)]
      fun x => (kestenLikelihood p x / (1 + primeReciprocal p)) * (f : SemicircleL2) x := by
  have h := kestenPrimePencil_ae p (kestenPrimeResolvent p f)
  rw [kestenPrimePencil_resolvent] at h
  have hne : 1 + primeReciprocal p ≠ 0 := by have := primeReciprocal_pos p; positivity
  filter_upwards [h, kestenPrimePencil_likelihood_ae p] with x hf hw
  have hm : (1 + primeReciprocal p) * (kestenPrimeResolvent p f : SemicircleL2) x =
      kestenLikelihood p x * (f : SemicircleL2) x := by
    calc
      _ = (((1 + primeReciprocal p) ^ 2 - primeReciprocal p * x ^ 2) * kestenLikelihood p x) *
          (kestenPrimeResolvent p f : SemicircleL2) x := by rw [hw]
      _ = kestenLikelihood p x * (((1 + primeReciprocal p) ^ 2 - primeReciprocal p * x ^ 2) *
          (kestenPrimeResolvent p f : SemicircleL2) x) := by ring
      _ = _ := by rw [← hf]
  calc
    _ = (1 + primeReciprocal p)⁻¹ *
        ((1 + primeReciprocal p) * (kestenPrimeResolvent p f : SemicircleL2) x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ = _ := by rw [hm]; ring

end
end GaloisForLFunctions.SelbergClass.Primon


import GaloisForLFunctions.SelbergClass.Primon.KestenGreenResolventIdentity
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Spectral calculus at prime Green parameters

The constructed prime Green operator is the Banach-algebra resolvent of
the square-Jacobi operator. Differentiation in the continuous spectral
parameter turns its response Gram kernel into the negative derivative
of the resolvent's quadratic forms.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem shift_mul_green (p : Nat.Primes) :
    (algebraMap ℝ (KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert)
      (kestenGreenParameter p) - kestenSquareJacobi) * kestenGreenOperator p = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact kestenGreenOperator_right_inverse p f

private theorem green_mul_shift (p : Nat.Primes) :
    kestenGreenOperator p *
      (algebraMap ℝ (KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert)
        (kestenGreenParameter p) - kestenSquareJacobi) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact kestenGreenOperator_left_inverse p f

/-- Every prime parameter belongs to the actual real resolvent set. -/
theorem kestenGreenParameter_mem_resolventSet (p : Nat.Primes) :
    kestenGreenParameter p ∈ resolventSet ℝ kestenSquareJacobi :=
  spectrum.mem_resolventSet_of_left_right_inverse (shift_mul_green p) (green_mul_shift p)

/-- The explicit likelihood Green operator equals the canonical Banach-algebra inverse. -/
theorem resolvent_kestenSquareJacobi (p : Nat.Primes) :
    resolvent kestenSquareJacobi (kestenGreenParameter p) = kestenGreenOperator p := by
  exact left_inv_eq_right_inv
    (Ring.inverse_mul_cancel _ (kestenGreenParameter_mem_resolventSet p)) (shift_mul_green p)

/-- The continuous spectral derivative is the negative square of the prime Green operator. -/
theorem hasDerivAt_kestenSquareJacobi_resolvent (p : Nat.Primes) :
    HasDerivAt (resolvent kestenSquareJacobi) (-(kestenGreenOperator p) ^ 2)
      (kestenGreenParameter p) := by
  have h : HasDerivAt (resolvent kestenSquareJacobi)
      (-(resolvent kestenSquareJacobi (kestenGreenParameter p)) ^ 2) (kestenGreenParameter p) :=
    spectrum.hasDerivAt_resolvent_const_left (𝕜 := ℝ) (a := kestenSquareJacobi)
      (kestenGreenParameter_mem_resolventSet p)
  rw [resolvent_kestenSquareJacobi] at h
  exact h

/-- Polarized Green response inner products are exact spectral derivatives. -/
theorem hasDerivAt_inner_kestenSquareJacobi_resolvent (p : Nat.Primes)
    (f g : KestenLikelihoodHilbert) :
    HasDerivAt (fun t : ℝ => inner ℝ f ((resolvent kestenSquareJacobi t) g))
      (-inner ℝ (kestenGreenOperator p f) (kestenGreenOperator p g))
      (kestenGreenParameter p) := by
  let L : (KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert) →L[ℝ] ℝ :=
    (innerSL ℝ f).comp (ContinuousLinearMap.apply ℝ KestenLikelihoodHilbert g)
  have hL : HasFDerivAt (fun T : KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert =>
      inner ℝ f (T g)) L (resolvent kestenSquareJacobi (kestenGreenParameter p)) := L.hasFDerivAt
  have h := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
    (F := KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert) (E := ℝ)
    (kestenGreenParameter p) hL (hasDerivAt_kestenSquareJacobi_resolvent p)
  change HasDerivAt (fun t : ℝ => inner ℝ f ((resolvent kestenSquareJacobi t) g))
    (inner ℝ f ((-(kestenGreenOperator p) ^ 2) g)) (kestenGreenParameter p) at h
  simpa only [neg_apply, pow_two, mul_apply_eq_comp,
    inner_neg_right, ← inner_kestenGreenOperator] using h

/-- Each quadratic response has derivative equal to minus the squared Green-response norm. -/
theorem hasDerivAt_quadratic_kestenSquareJacobi_resolvent (p : Nat.Primes)
    (f : KestenLikelihoodHilbert) :
    HasDerivAt (fun t : ℝ => inner ℝ f ((resolvent kestenSquareJacobi t) f))
      (-‖kestenGreenOperator p f‖ ^ 2) (kestenGreenParameter p) := by
  simpa only [real_inner_self_eq_norm_sq] using
    hasDerivAt_inner_kestenSquareJacobi_resolvent p f f

/-- A quadratic Green response decreases strictly at every prime parameter exactly for nonzero sources. -/
theorem deriv_quadratic_kestenSquareJacobi_resolvent_neg_iff (p : Nat.Primes)
    (f : KestenLikelihoodHilbert) :
    deriv (fun t : ℝ => inner ℝ f ((resolvent kestenSquareJacobi t) f))
      (kestenGreenParameter p) < 0 ↔ f ≠ 0 := by
  rw [(hasDerivAt_quadratic_kestenSquareJacobi_resolvent p f).deriv,
    neg_lt_zero, sq_pos_iff, ne_eq, norm_eq_zero]
  constructor
  · intro h hf
    exact h (by rw [hf, map_zero])
  · intro h hf
    exact h (kestenGreenOperator_injective p (hf.trans (map_zero (kestenGreenOperator p)).symm))

/-- The vacuum derivative is the diagonal of the exact normalized likelihood Gram kernel. -/
theorem hasDerivAt_vacuum_kestenSquareJacobi_resolvent (p : Nat.Primes) :
    HasDerivAt (fun t : ℝ => inner ℝ (kestenCharacterState 0)
      ((resolvent kestenSquareJacobi t) (kestenCharacterState 0)))
      (-(((p : ℝ) + 1)⁻¹ ^ 2 / (1 - primeReciprocal p ^ 2))) (kestenGreenParameter p) := by
  simpa only [inner_kestenGreenOperator_vacua, pow_two] using
    hasDerivAt_inner_kestenSquareJacobi_resolvent p (kestenCharacterState 0) (kestenCharacterState 0)

end
end GaloisForLFunctions.SelbergClass.Primon

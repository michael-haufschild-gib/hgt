import GaloisForLFunctions.SelbergClass.Primon.KestenShiftOperators
import GaloisForLFunctions.SelbergClass.Primon.SemicircleSquareOperator

/-!
# The square spectral law as a creation-annihilation Jacobi operator

In the complete even-character basis, multiplication by `x²` has diagonal
`1,2,2,...` and off-diagonal entries `1`. It equals `(I + S)(I + S*)`, with
the lower-boundary correction supplied by the shift's constant-character
defect. Its vacuum moments are the Catalan numbers of the square spectral law.
-/

open MeasureTheory
open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The first Jacobi row has diagonal entry `1` and one raising edge. -/
theorem kestenSquareJacobi_vacuum :
    kestenSquareJacobi (kestenCharacterState 0) = kestenCharacterState 1 + kestenCharacterState 0 := by
  apply Subtype.ext
  change (kestenSquareJacobi (kestenCharacterState 0) : SemicircleL2) =
    (kestenCharacterState 1 : SemicircleL2) + (kestenCharacterState 0 : SemicircleL2)
  simp only [coe_kestenSquareJacobi, coe_kestenCharacterState, Nat.mul_zero,
    Nat.mul_one, semicircleSquareMul_character_zero]

/-- Every later Jacobi row has the constant coefficients `1,2,1`. -/
theorem kestenSquareJacobi_character_succ (n : ℕ) :
    kestenSquareJacobi (kestenCharacterState (n + 1)) =
      kestenCharacterState (n + 2) + (2 : ℝ) • kestenCharacterState (n + 1) + kestenCharacterState n := by
  apply Subtype.ext
  change (kestenSquareJacobi (kestenCharacterState (n + 1)) : SemicircleL2) =
    (kestenCharacterState (n + 2) : SemicircleL2) +
      (2 : ℝ) • (kestenCharacterState (n + 1) : SemicircleL2) + (kestenCharacterState n : SemicircleL2)
  simp only [coe_kestenSquareJacobi, coe_kestenCharacterState, semicircleSquareMul_character_succ]

/-- The constant coordinate of the square operator is the sum of the first two coordinates. -/
theorem hardyCoordinate_kestenSquareJacobi_zero (f : KestenLikelihoodHilbert) :
    hardyLikelihoodUnitary.symm (kestenSquareJacobi f) 0 =
      hardyLikelihoodUnitary.symm f 1 + hardyLikelihoodUnitary.symm f 0 := by
  rw [← inner_kestenCharacterState, ← inner_kestenSquareJacobi, kestenSquareJacobi_vacuum,
    inner_add_left, inner_kestenCharacterState, inner_kestenCharacterState]

/-- All later square-operator coordinates obey the free three-term Jacobi recurrence. -/
theorem hardyCoordinate_kestenSquareJacobi_succ (f : KestenLikelihoodHilbert) (n : ℕ) :
    hardyLikelihoodUnitary.symm (kestenSquareJacobi f) (n + 1) =
      hardyLikelihoodUnitary.symm f (n + 2) + 2 * hardyLikelihoodUnitary.symm f (n + 1) +
        hardyLikelihoodUnitary.symm f n := by
  calc
    _ = inner ℝ (kestenCharacterState (n + 1)) (kestenSquareJacobi f) :=
      (inner_kestenCharacterState _ _).symm
    _ = inner ℝ (kestenSquareJacobi (kestenCharacterState (n + 1))) f :=
      (inner_kestenSquareJacobi _ _).symm
    _ = inner ℝ (kestenCharacterState (n + 2) +
        (2 : ℝ) • kestenCharacterState (n + 1) + kestenCharacterState n) f :=
      congrArg (fun v : KestenLikelihoodHilbert => inner ℝ v f) (kestenSquareJacobi_character_succ n)
    _ = inner ℝ (kestenCharacterState (n + 2)) f +
        2 * inner ℝ (kestenCharacterState (n + 1)) f + inner ℝ (kestenCharacterState n) f := by
      have htwo : inner ℝ ((2 : ℝ) • kestenCharacterState (n + 1)) f =
          2 * inner ℝ (kestenCharacterState (n + 1)) f := by
        simpa only [conj_trivial] using
          (_root_.inner_smul_left (𝕜 := ℝ) (kestenCharacterState (n + 1)) f (2 : ℝ))
      rw [inner_add_left, inner_add_left, htwo]
    _ = _ := by rw [inner_kestenCharacterState, inner_kestenCharacterState, inner_kestenCharacterState]

/-- The actual square coordinate is the shift plus its adjoint with one boundary correction. -/
theorem kestenSquareJacobi_eq_shift (f : KestenLikelihoodHilbert) :
    kestenSquareJacobi f = kestenShift f + kestenBackshift f + (2 : ℝ) • f -
      hardyLikelihoodUnitary.symm f 0 • kestenCharacterState 0 := by
  apply hardyLikelihoodUnitary.symm.injective
  apply lp.ext
  funext n
  cases n with
  | zero =>
      rw [hardyCoordinate_kestenSquareJacobi_zero]
      simp only [map_sub, map_add, map_smul, lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        hardyCoordinate_kestenShift, shiftSeq_zero, hardyCoordinate_kestenBackshift]
      simp [kestenCharacterState, lp.single_apply]
      ring
  | succ n =>
      rw [hardyCoordinate_kestenSquareJacobi_succ]
      simp only [map_sub, map_add, map_smul, lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        hardyCoordinate_kestenShift, shiftSeq_succ, hardyCoordinate_kestenBackshift]
      simp [kestenCharacterState, lp.single_apply]
      ring

/-- The square-coordinate Jacobi operator factors as `(I + S)(I + S*)`. -/
theorem kestenSquareJacobi_factor (f : KestenLikelihoodHilbert) :
    kestenSquareJacobi f = (f + kestenBackshift f) + kestenShift (f + kestenBackshift f) := by
  rw [map_add, kestenShift_backshift, kestenSquareJacobi_eq_shift]
  module

/-- The Jacobi quadratic form is the exact squared norm of `f + S* f`. -/
theorem inner_kestenSquareJacobi_eq_norm (f : KestenLikelihoodHilbert) :
    inner ℝ f (kestenSquareJacobi f) = ‖f + kestenBackshift f‖ ^ 2 := by
  rw [kestenSquareJacobi_factor, inner_add_right]
  have h := ContinuousLinearMap.adjoint_inner_left kestenShift.toContinuousLinearMap
    (f + kestenBackshift f) f
  change inner ℝ (kestenBackshift f) (f + kestenBackshift f) =
    inner ℝ f (kestenShift (f + kestenBackshift f)) at h
  rw [← h, ← inner_add_left, real_inner_self_eq_norm_sq]

/-- Iterating the Jacobi operator on the constant state gives literal even monomials. -/
theorem coe_iterate_kestenSquareJacobi_vacuum (n : ℕ) :
    ((kestenSquareJacobi : KestenLikelihoodHilbert → KestenLikelihoodHilbert)^[n]
      (kestenCharacterState 0) : SemicircleL2) =
        semicircleL2Observable ⟨fun x => x ^ (2 * n), by fun_prop⟩ := by
  induction n with
  | zero =>
      change (kestenCharacterState 0 : SemicircleL2) = _
      rw [coe_kestenCharacterState]
      change semicircleL2Observable (spectralCharacter 0) = _
      congr 1
      ext x
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', coe_kestenSquareJacobi, ih, semicircleSquareMul_observable]
      congr 1
      ext x
      change x ^ 2 * x ^ (2 * n) = x ^ (2 * (n + 1))
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
      ring

/-- The actual square-coordinate Jacobi operator has Catalan vacuum moments. -/
theorem kestenSquareJacobi_vacuum_moment (n : ℕ) :
    inner ℝ (kestenCharacterState 0)
      ((kestenSquareJacobi : KestenLikelihoodHilbert → KestenLikelihoodHilbert)^[n]
        (kestenCharacterState 0)) = (catalan n : ℝ) := by
  change inner ℝ (kestenCharacterState 0 : SemicircleL2)
    ((kestenSquareJacobi : KestenLikelihoodHilbert → KestenLikelihoodHilbert)^[n]
      (kestenCharacterState 0) : SemicircleL2) = _
  rw [coe_kestenCharacterState, coe_iterate_kestenSquareJacobi_vacuum]
  change inner ℝ (semicircleL2Observable (spectralCharacter 0)) (semicircleL2Observable _) = _
  rw [inner_semicircleL2Observable]
  simp only [spectralCharacter_zero, ContinuousMap.coe_mk, one_mul]
  rw [(semicircleSpectralLaw_hasMoments _).2, semicircleMoment_even]

/-- Prime likelihoods solve the square-Jacobi resolvent equation with constant source. -/
theorem kestenSquareJacobi_prime_resolvent (p : Nat.Primes) :
    ((1 + primeReciprocal p) ^ 2) • kestenPrimeState p -
      primeReciprocal p • kestenSquareJacobi (kestenPrimeState p) =
        (1 + primeReciprocal p) • kestenCharacterState 0 := by
  have hv : hardyLikelihoodUnitary.symm (kestenPrimeState p) 0 = 1 := by
    simp [kestenPrimeState, primeHardyKernel, hardyKernel_apply]
  have hs := kestenShift_backshift (kestenPrimeState p)
  rw [kestenBackshift_prime, map_smul, hv, one_smul] at hs
  rw [kestenSquareJacobi_eq_shift, kestenBackshift_prime, hv, one_smul]
  simp only [smul_sub, smul_add, smul_smul]
  rw [hs]
  module

end
end GaloisForLFunctions.SelbergClass.Primon


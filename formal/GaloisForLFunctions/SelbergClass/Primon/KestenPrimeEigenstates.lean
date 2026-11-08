import GaloisForLFunctions.SelbergClass.Primon.KestenShiftOperators

/-!
# Rigidity of prime backward-shift states

The backward-shift equation forces every character coefficient to be
geometric. Thus its reciprocal-prime eigenspace is exactly the likelihood
line, and the constant coefficient uniquely normalizes that likelihood.
The same state solves the first-order shift equation with a constant source.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The reciprocal-prime eigenspace of lowering is exactly the prime-likelihood line. -/
theorem kestenBackshift_prime_eigen_iff (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenBackshift f = primeReciprocal p • f ↔
      f = hardyLikelihoodUnitary.symm f 0 • kestenPrimeState p := by
  constructor
  · intro h
    have hstep (n : ℕ) : hardyLikelihoodUnitary.symm f (n + 1) =
        primeReciprocal p * hardyLikelihoodUnitary.symm f n := by
      have hh := congrArg (fun g : KestenLikelihoodHilbert => hardyLikelihoodUnitary.symm g n) h
      simpa only [hardyCoordinate_kestenBackshift, map_smul, lp.coeFn_smul,
        Pi.smul_apply, smul_eq_mul] using hh
    have hc (n : ℕ) : hardyLikelihoodUnitary.symm f n =
        hardyLikelihoodUnitary.symm f 0 * primeReciprocal p ^ n := by
      induction n with
      | zero => simp
      | succ n ih => rw [hstep, ih, pow_succ]; ring
    apply hardyLikelihoodUnitary.symm.injective
    apply lp.ext
    funext n
    simp only [map_smul, kestenPrimeState, hardyLikelihoodUnitary.symm_apply_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, primeHardyKernel, hardyKernel_apply]
    exact hc n
  · intro h
    rw [h, map_smul, kestenBackshift_prime, smul_smul, smul_smul, mul_comm]

/-- Prescribing the constant coefficient uniquely selects a scalar prime likelihood. -/
theorem kestenBackshift_prime_normalized_iff (p : Nat.Primes) (a : ℝ)
    (f : KestenLikelihoodHilbert) :
    (kestenBackshift f = primeReciprocal p • f ∧ inner ℝ (kestenCharacterState 0) f = a) ↔
      f = a • kestenPrimeState p := by
  constructor
  · rintro ⟨he, ha⟩
    rw [inner_kestenCharacterState] at ha
    rw [(kestenBackshift_prime_eigen_iff p f).mp he, ha]
  · intro h
    subst f
    constructor
    · rw [map_smul, kestenBackshift_prime, smul_smul, smul_smul, mul_comm]
    · rw [inner_kestenCharacterState]
      simp [map_smul, kestenPrimeState, primeHardyKernel, hardyKernel_apply]

/-- A constant-source first-order shift equation has the same unique likelihood solution. -/
theorem kestenShift_prime_source_iff (p : Nat.Primes) (a : ℝ) (f : KestenLikelihoodHilbert) :
    f - primeReciprocal p • kestenShift f = a • kestenCharacterState 0 ↔
      f = a • kestenPrimeState p := by
  constructor
  · intro h
    apply (kestenBackshift_prime_normalized_iff p a f).mp
    constructor
    · have hh := congrArg kestenBackshift h
      rw [map_sub, map_smul, kestenBackshift_shift, map_smul,
        kestenBackshift_vacuum, smul_zero] at hh
      exact sub_eq_zero.mp hh
    · have hh := congrArg (fun g : KestenLikelihoodHilbert => hardyLikelihoodUnitary.symm g 0) h
      rw [inner_kestenCharacterState]
      simpa [map_sub, map_smul, hardyCoordinate_kestenShift, shiftSeq_zero,
        kestenCharacterState, lp.single_apply] using hh
  · intro h
    have he := (kestenBackshift_prime_normalized_iff p a f).mpr h
    have hs := kestenShift_backshift f
    rw [he.1, map_smul, ← inner_kestenCharacterState, he.2] at hs
    rw [hs]
    module

end
end GaloisForLFunctions.SelbergClass.Primon

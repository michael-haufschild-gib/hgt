import GaloisForLFunctions.SelbergClass.Primon.KestenGreenBoundaryFactorization

/-!
# Exact innovations of the prime Green covariance

Conjugating the Green operator by the first-order shift difference makes
its covariance diagonal. The constant innovation has variance `q/(1+q)`;
every later innovation has variance `q`. Thus the entire boundary effect
is confined to the initial variance.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem inner_state_smul_left (a : ℝ) (f g : KestenLikelihoodHilbert) :
    inner ℝ (a • f) g = a * inner ℝ f g := by
  simpa only [conj_trivial] using (_root_.inner_smul_left (𝕜 := ℝ) f g a)

/-- First-order differences diagonalize the Green operator except for its explicit constant component. -/
theorem kestenGreenOperator_whitening (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenShiftPencil p (kestenGreenOperator p (f - primeReciprocal p • kestenBackshift f)) =
      primeReciprocal p • f -
        (primeReciprocal p ^ 2 / (1 + primeReciprocal p) * hardyLikelihoodUnitary.symm f 0) •
          kestenCharacterState 0 := by
  have hw : kestenShiftPencil p (kestenPrimeState p) = kestenCharacterState 0 := by
    rw [← kestenShiftResolvent_vacuum p, kestenShiftPencil_resolvent]
  have hr : inner ℝ (kestenPrimeState p) (f - primeReciprocal p • kestenBackshift f) =
      hardyLikelihoodUnitary.symm f 0 := by
    rw [← inner_kestenShiftPencil, hw, inner_kestenCharacterState]
  rw [kestenGreenOperator_causal_correction, kestenShiftResolvent_adjoint_backshiftPencil,
    hr, map_sub, map_smul, map_smul, kestenShiftPencil_resolvent, hw]

/-- The whitened Green form is the scalar inner product with one constant-coordinate correction. -/
theorem inner_kestenGreenOperator_whitened (p : Nat.Primes) (f g : KestenLikelihoodHilbert) :
    inner ℝ (f - primeReciprocal p • kestenBackshift f)
      (kestenGreenOperator p (g - primeReciprocal p • kestenBackshift g)) =
        primeReciprocal p * inner ℝ f g -
          primeReciprocal p ^ 2 / (1 + primeReciprocal p) *
            hardyLikelihoodUnitary.symm f 0 * hardyLikelihoodUnitary.symm g 0 := by
  calc
    _ = inner ℝ (kestenGreenOperator p (g - primeReciprocal p • kestenBackshift g))
        (f - primeReciprocal p • kestenBackshift f) := real_inner_comm _ _
    _ = inner ℝ (kestenShiftPencil p
        (kestenGreenOperator p (g - primeReciprocal p • kestenBackshift g))) f :=
      (inner_kestenShiftPencil p _ f).symm
    _ = _ := by
      rw [kestenGreenOperator_whitening, inner_sub_left, inner_state_smul_left,
        inner_state_smul_left, inner_kestenCharacterState, real_inner_comm f g]
      ring

/-- The whitened Green energy separates all nonconstant energy from the initial variance. -/
theorem inner_kestenGreenOperator_whitened_self (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    inner ℝ (f - primeReciprocal p • kestenBackshift f)
      (kestenGreenOperator p (f - primeReciprocal p • kestenBackshift f)) =
        primeReciprocal p * ‖f‖ ^ 2 -
          primeReciprocal p ^ 2 / (1 + primeReciprocal p) * (hardyLikelihoodUnitary.symm f 0) ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq, pow_two, mul_assoc] using
    inner_kestenGreenOperator_whitened p f f

/-- The first-order backward difference of one character source. -/
def kestenGreenInnovation (p : Nat.Primes) (n : ℕ) : KestenLikelihoodHilbert :=
  kestenCharacterState n - primeReciprocal p • kestenBackshift (kestenCharacterState n)

theorem kestenGreenInnovation_zero (p : Nat.Primes) :
    kestenGreenInnovation p 0 = kestenCharacterState 0 := by
  rw [kestenGreenInnovation, kestenBackshift_vacuum, smul_zero, sub_zero]

theorem kestenGreenInnovation_succ (p : Nat.Primes) (n : ℕ) :
    kestenGreenInnovation p (n + 1) = kestenCharacterState (n + 1) -
      primeReciprocal p • kestenCharacterState n := by
  rw [kestenGreenInnovation, kestenBackshift_character_succ]

private theorem inner_characters (n m : ℕ) :
    inner ℝ (kestenCharacterState n) (kestenCharacterState m) = if n = m then 1 else 0 := by
  rw [inner_kestenCharacterState]
  simp [kestenCharacterState, lp.single_apply, Pi.single_apply]

private theorem character_coordinate_zero (n : ℕ) :
    hardyLikelihoodUnitary.symm (kestenCharacterState n) 0 = if n = 0 then 1 else 0 := by
  simp [kestenCharacterState, lp.single_apply, Pi.single_apply, eq_comm]

/-- The innovation covariance is exactly diagonal, with the unique boundary variance `q/(1+q)`. -/
theorem inner_kestenGreenInnovations (p : Nat.Primes) (n m : ℕ) :
    inner ℝ (kestenGreenInnovation p n) (kestenGreenOperator p (kestenGreenInnovation p m)) =
      if n = m then (if n = 0 then primeReciprocal p / (1 + primeReciprocal p)
        else primeReciprocal p) else 0 := by
  rw [kestenGreenInnovation, kestenGreenInnovation, inner_kestenGreenOperator_whitened,
    inner_characters, character_coordinate_zero, character_coordinate_zero]
  by_cases hnm : n = m
  · subst m
    by_cases hn : n = 0
    · subst n
      simp only [ite_true, mul_one]
      have hne : 1 + primeReciprocal p ≠ 0 := by have := primeReciprocal_pos p; positivity
      field_simp
      ring
    · simp [hn]
  · by_cases hn : n = 0
    · have hm : m ≠ 0 := by intro hm; exact hnm (hn.trans hm.symm)
      simp [hn, hm, eq_comm]
    · simp [hnm, hn]

end
end GaloisForLFunctions.SelbergClass.Primon

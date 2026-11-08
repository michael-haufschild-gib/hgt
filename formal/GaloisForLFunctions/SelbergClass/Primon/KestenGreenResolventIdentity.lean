import GaloisForLFunctions.SelbergClass.Primon.KestenGreenOperator

/-!
# Two-prime Green identities

All prime Green operators invert scalar shifts of the same square-Jacobi
operator. They commute and obey the resolvent identity, including equal
primes. Vacuum matrix elements identify the likelihood Gram kernel with
the divided difference of the scalar Green response.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- A Green operator commutes with the square-coordinate observable. -/
theorem kestenGreenOperator_jacobi (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenGreenOperator p (kestenSquareJacobi f) =
      kestenSquareJacobi (kestenGreenOperator p f) := by
  have h := kestenGreenOperator_left_inverse p f
  rw [map_sub, map_smul] at h
  exact sub_right_inj.mp (h.trans (kestenGreenOperator_right_inverse p f).symm)

/-- The Green operator loses no source information. -/
theorem kestenGreenOperator_injective (p : Nat.Primes) :
    Function.Injective (kestenGreenOperator p) := by
  intro f g h
  rw [← kestenGreenOperator_right_inverse p f, h, kestenGreenOperator_right_inverse]

private theorem pencil_injective (p : Nat.Primes) :
    Function.Injective (fun f : KestenLikelihoodHilbert =>
      kestenGreenParameter p • f - kestenSquareJacobi f) := by
  intro f g h
  have hh := congrArg (kestenGreenOperator p) h
  simpa only [kestenGreenOperator_left_inverse] using hh

/-- Green operators at any two primes commute on the entire likelihood space. -/
theorem kestenGreenOperator_commute (p q : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenGreenOperator p (kestenGreenOperator q f) =
      kestenGreenOperator q (kestenGreenOperator p f) := by
  apply pencil_injective p
  change kestenGreenParameter p • kestenGreenOperator p (kestenGreenOperator q f) -
    kestenSquareJacobi (kestenGreenOperator p (kestenGreenOperator q f)) =
      kestenGreenParameter p • kestenGreenOperator q (kestenGreenOperator p f) -
        kestenSquareJacobi (kestenGreenOperator q (kestenGreenOperator p f))
  rw [kestenGreenOperator_right_inverse, ← kestenGreenOperator_jacobi,
    ← map_smul, ← map_sub, kestenGreenOperator_right_inverse]

/-- The sourcewise resolvent identity needs no separation hypothesis on the primes. -/
theorem kestenGreenOperator_difference_apply (p q : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenGreenOperator p f - kestenGreenOperator q f =
      (kestenGreenParameter q - kestenGreenParameter p) •
        kestenGreenOperator p (kestenGreenOperator q f) := by
  calc
    _ = kestenGreenOperator p (kestenGreenParameter q • kestenGreenOperator q f -
          kestenSquareJacobi (kestenGreenOperator q f)) -
        kestenGreenOperator p (kestenGreenParameter p • kestenGreenOperator q f -
          kestenSquareJacobi (kestenGreenOperator q f)) := by
      rw [kestenGreenOperator_right_inverse, kestenGreenOperator_left_inverse]
    _ = _ := by simp only [map_sub, map_smul]; module

/-- The same identity holds in the Banach algebra of bounded operators. -/
theorem kestenGreenOperator_difference (p q : Nat.Primes) :
    kestenGreenOperator p - kestenGreenOperator q =
      (kestenGreenParameter q - kestenGreenParameter p) •
        (kestenGreenOperator p * kestenGreenOperator q) := by
  apply ContinuousLinearMap.ext
  intro f
  exact kestenGreenOperator_difference_apply p q f

/-- Green response inner products are polarized resolvent differences. -/
theorem inner_kestenGreenOperator_difference (p q : Nat.Primes) (f g : KestenLikelihoodHilbert) :
    inner ℝ f (kestenGreenOperator p g) - inner ℝ f (kestenGreenOperator q g) =
      (kestenGreenParameter q - kestenGreenParameter p) *
        inner ℝ (kestenGreenOperator p f) (kestenGreenOperator q g) := by
  rw [← inner_sub_right, kestenGreenOperator_difference_apply,
    _root_.inner_smul_right (𝕜 := ℝ) f
      (kestenGreenOperator p (kestenGreenOperator q g))
      (kestenGreenParameter q - kestenGreenParameter p), ← inner_kestenGreenOperator]

/-- Prime states have the exact real Hardy kernel as their Gram matrix. -/
theorem inner_kestenPrimeState (p q : Nat.Primes) :
    inner ℝ (kestenPrimeState p) (kestenPrimeState q) =
      1 / (1 - primeReciprocal p * primeReciprocal q) := by
  rw [kestenPrimeState, kestenPrimeState, hardyLikelihoodUnitary.inner_map_map,
    inner_primeHardyKernel]

/-- The normalized likelihood Gram kernel is the vacuum Green-response kernel. -/
theorem inner_kestenGreenOperator_vacua (p q : Nat.Primes) :
    inner ℝ (kestenGreenOperator p (kestenCharacterState 0))
      (kestenGreenOperator q (kestenCharacterState 0)) =
        ((p : ℝ) + 1)⁻¹ * ((q : ℝ) + 1)⁻¹ /
          (1 - primeReciprocal p * primeReciprocal q) := by
  rw [kestenGreenOperator_vacuum, kestenGreenOperator_vacuum,
    _root_.inner_smul_left (𝕜 := ℝ) (kestenPrimeState p)
      (((q : ℝ) + 1)⁻¹ • kestenPrimeState q) (((p : ℝ) + 1)⁻¹),
    _root_.inner_smul_right (𝕜 := ℝ) (kestenPrimeState p) (kestenPrimeState q)
      (((q : ℝ) + 1)⁻¹)]
  simp only [conj_trivial, inner_kestenPrimeState]
  ring

/-- The scalar Green divided difference equals the Gram kernel, without division by a gap. -/
theorem kestenGreen_vacuum_divided_difference (p q : Nat.Primes) :
    ((p : ℝ) + 1)⁻¹ - ((q : ℝ) + 1)⁻¹ =
      (kestenGreenParameter q - kestenGreenParameter p) *
        inner ℝ (kestenGreenOperator p (kestenCharacterState 0))
          (kestenGreenOperator q (kestenCharacterState 0)) := by
  simpa only [kestenGreenOperator_vacuum_average] using
    inner_kestenGreenOperator_difference p q (kestenCharacterState 0) (kestenCharacterState 0)

end
end GaloisForLFunctions.SelbergClass.Primon

import GaloisForLFunctions.SelbergClass.Primon.KestenPrimeResolvent

/-!
# Prime evaluations of the square-coordinate Green operator

The prime likelihood divided by `p+1` is the multiplier of
`(λ_p I - J)⁻¹`, where `λ_p = p + 2 + 1/p > 4` and `J` is multiplication
by the squared semicircle coordinate. Its vacuum average satisfies the
quadratic Stieltjes equation `λ m (1-m) = 1`.
-/

open MeasureTheory
open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The spectral parameter selected by a prime reciprocal. -/
def kestenGreenParameter (p : Nat.Primes) : ℝ :=
  (1 + primeReciprocal p) ^ 2 / primeReciprocal p

theorem kestenGreenParameter_mul_reciprocal (p : Nat.Primes) :
    kestenGreenParameter p * primeReciprocal p = (1 + primeReciprocal p) ^ 2 := by
  exact div_mul_cancel₀ _ (primeReciprocal_pos p).ne'

theorem kestenGreenParameter_eq (p : Nat.Primes) :
    kestenGreenParameter p = (p : ℝ) + 2 + (p : ℝ)⁻¹ := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  simp only [kestenGreenParameter, primeReciprocal]
  field_simp
  ring

/-- The gap from the upper square-spectral edge is strictly positive. -/
theorem kestenGreenParameter_gap (p : Nat.Primes) :
    kestenGreenParameter p - 4 = (1 - primeReciprocal p) ^ 2 / primeReciprocal p := by
  unfold kestenGreenParameter
  field_simp [(primeReciprocal_pos p).ne']
  ring

theorem kestenGreenParameter_gt_four (p : Nat.Primes) : 4 < kestenGreenParameter p := by
  have h := div_pos (kestenPrimePencil_gap_pos p) (primeReciprocal_pos p)
  rw [← kestenGreenParameter_gap] at h
  exact sub_pos.mp h

/-- The canonical Green operator at the prime spectral parameter. -/
def kestenGreenOperator (p : Nat.Primes) : KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert :=
  primeReciprocal p • kestenPrimeResolvent p

@[simp] theorem kestenGreenOperator_apply (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenGreenOperator p f = primeReciprocal p • kestenPrimeResolvent p f := rfl

/-- The Green operator solves every source equation at `λ_p`. -/
theorem kestenGreenOperator_right_inverse (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenGreenParameter p • kestenGreenOperator p f -
      kestenSquareJacobi (kestenGreenOperator p f) = f := by
  rw [kestenGreenOperator_apply, map_smul, smul_smul, kestenGreenParameter_mul_reciprocal]
  exact kestenPrimePencil_resolvent p f

/-- The source equation has a unique solution. -/
theorem kestenGreenOperator_left_inverse (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenGreenOperator p (kestenGreenParameter p • f - kestenSquareJacobi f) = f := by
  rw [kestenGreenOperator_apply, ← map_smul]
  have h : primeReciprocal p • (kestenGreenParameter p • f - kestenSquareJacobi f) =
      kestenPrimePencil p f := by
    rw [smul_sub, smul_smul, mul_comm, kestenGreenParameter_mul_reciprocal]
    rfl
  rw [h, kestenPrimeResolvent_pencil]

private theorem reciprocal_normalization (p : Nat.Primes) :
    primeReciprocal p * (1 + primeReciprocal p)⁻¹ = ((p : ℝ) + 1)⁻¹ := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hq1 : 1 + primeReciprocal p ≠ 0 := by have := primeReciprocal_pos p; positivity
  unfold primeReciprocal at *
  field_simp

/-- A constant source produces the prime likelihood divided by `p+1`. -/
theorem kestenGreenOperator_vacuum (p : Nat.Primes) :
    kestenGreenOperator p (kestenCharacterState 0) = ((p : ℝ) + 1)⁻¹ • kestenPrimeState p := by
  rw [kestenGreenOperator_apply, kestenPrimeResolvent_vacuum, smul_smul,
    reciprocal_normalization]

/-- The vacuum Green average is the reciprocal `1/(p+1)`. -/
theorem kestenGreenOperator_vacuum_average (p : Nat.Primes) :
    inner ℝ (kestenCharacterState 0) (kestenGreenOperator p (kestenCharacterState 0)) =
      ((p : ℝ) + 1)⁻¹ := by
  rw [kestenGreenOperator_apply,
    _root_.inner_smul_right (𝕜 := ℝ) (kestenCharacterState 0)
      (kestenPrimeResolvent p (kestenCharacterState 0)) (primeReciprocal p),
    kestenPrimeResolvent_vacuum_average, reciprocal_normalization]

/-- The inverse norm is at most the reciprocal distance from `[0,4]`. -/
theorem norm_kestenGreenOperator_le (p : Nat.Primes) :
    ‖kestenGreenOperator p‖ ≤ (kestenGreenParameter p - 4)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    exact inv_nonneg.mpr (sub_pos.mpr (kestenGreenParameter_gt_four p)).le)
  intro f
  calc
    _ = primeReciprocal p * ‖kestenPrimeResolvent p f‖ := by
      rw [kestenGreenOperator_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (primeReciprocal_pos p)]
    _ ≤ primeReciprocal p * (((1 - primeReciprocal p) ^ 2)⁻¹ * ‖f‖) :=
      mul_le_mul_of_nonneg_left ((kestenPrimeResolvent p).le_opNorm f |>.trans
        (mul_le_mul_of_nonneg_right (norm_kestenPrimeResolvent_le p) (norm_nonneg f)))
        (primeReciprocal_pos p).le
    _ = _ := by rw [kestenGreenParameter_gap, inv_div]; ring

/-- The Green operator is self-adjoint. -/
theorem inner_kestenGreenOperator (p : Nat.Primes) (f g : KestenLikelihoodHilbert) :
    inner ℝ (kestenGreenOperator p f) g = inner ℝ f (kestenGreenOperator p g) := by
  rw [kestenGreenOperator_apply, kestenGreenOperator_apply,
    _root_.inner_smul_left (𝕜 := ℝ) (kestenPrimeResolvent p f) g (primeReciprocal p),
    _root_.inner_smul_right (𝕜 := ℝ) f (kestenPrimeResolvent p g) (primeReciprocal p)]
  simp only [conj_trivial, inner_kestenPrimeResolvent]

theorem inner_kestenGreenOperator_nonneg (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    0 ≤ inner ℝ f (kestenGreenOperator p f) := by
  rw [kestenGreenOperator_apply,
    _root_.inner_smul_right (𝕜 := ℝ) f (kestenPrimeResolvent p f) (primeReciprocal p)]
  exact mul_nonneg (primeReciprocal_pos p).le (inner_kestenPrimeResolvent_nonneg p f)

/-- The bounded Green operator is multiplication by the normalized likelihood. -/
theorem kestenGreenOperator_ae (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    (kestenGreenOperator p f : SemicircleL2) =ᵐ[(semicircleSpectralLaw : Measure ℝ)]
      fun x => (kestenLikelihood p x / ((p : ℝ) + 1)) * (f : SemicircleL2) x := by
  change (primeReciprocal p • (kestenPrimeResolvent p f : SemicircleL2) : SemicircleL2) =ᵐ[_] _
  filter_upwards [Lp.coeFn_smul (primeReciprocal p) (kestenPrimeResolvent p f : SemicircleL2),
    kestenPrimeResolvent_ae p f] with x hs hr
  simp only [hs, Pi.smul_apply, smul_eq_mul, hr, div_eq_mul_inv]
  calc
    _ = (primeReciprocal p * (1 + primeReciprocal p)⁻¹) *
        kestenLikelihood p x * (f : SemicircleL2) x := by ring
    _ = _ := by rw [reciprocal_normalization]; ring

/-- The actual vacuum Green average obeys the square-semicircle Stieltjes equation. -/
theorem kestenGreenOperator_stieltjes_equation (p : Nat.Primes) :
    let m := inner ℝ (kestenCharacterState 0) (kestenGreenOperator p (kestenCharacterState 0))
    kestenGreenParameter p * m * (1 - m) = 1 := by
  dsimp only
  rw [kestenGreenOperator_vacuum_average, kestenGreenParameter_eq]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

end
end GaloisForLFunctions.SelbergClass.Primon

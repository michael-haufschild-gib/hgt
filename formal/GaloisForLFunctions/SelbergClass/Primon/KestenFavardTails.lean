import GaloisForLFunctions.SelbergClass.Primon.KestenTailGeometry
import GaloisForLFunctions.SelbergClass.Primon.SemicircleObservableLinear
import GaloisForLFunctions.SelbergClass.Primon.SpectralCharacterAlgebra
import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodRatios

/-!
# Favard factorization of normalized likelihood tails

Every positive-depth likelihood tail is the likelihood multiplied by the
corresponding even prime orthogonal polynomial. Thus the geometric depth
Gram kernel is also an exact weighted Favard-polynomial Gram kernel.
-/

open MeasureTheory Set
open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The likelihood is the quadratic spectral resolvent on its support. -/
theorem kestenLikelihood_resolvent (p : Nat.Primes) (x : Icc (-2 : ℝ) 2) :
    kestenLikelihood p x * (((p : ℝ) + 1) ^ 2 - (p : ℝ) * (x : ℝ) ^ 2) =
      (p : ℝ) * ((p : ℝ) + 1) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have h := mul_inv_cancel₀ (kestenLikelihood_pos p x).ne'
  rw [kestenLikelihood_inv_on_interval] at h
  field_simp [hp, hp1] at h
  nlinarith only [h]

/-- A scaled prime likelihood times an even Favard polynomial. -/
def kestenFavardTail (p : Nat.Primes) (n : ℕ) : C(ℝ, ℝ) :=
  ⟨fun x => (p : ℝ) / ((p : ℝ) + 1) * kestenLikelihood p x *
    (kestenPolynomial p (2 * n + 2)).eval x,
    (continuous_const.mul (continuous_kestenLikelihood p)).mul (by fun_prop)⟩

private theorem kestenFavardTail_zero (p : Nat.Primes) (x : Icc (-2 : ℝ) 2) :
    kestenFavardTail p 0 x = (p : ℝ) * (kestenLikelihood p x - 1) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have h := kestenLikelihood_resolvent p x
  change (p : ℝ) / ((p : ℝ) + 1) * kestenLikelihood p x *
    (kestenPolynomial p 2).eval (x : ℝ) = _
  rw [kestenPolynomial_two, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  field_simp [hp, hp1]
  nlinarith only [h]

private theorem kestenFavardTail_succ (p : Nat.Primes) (n : ℕ)
    (x : Icc (-2 : ℝ) 2) :
    kestenFavardTail p (n + 1) x =
      (p : ℝ) * (kestenFavardTail p n x - spectralCharacter (2 * n + 2) x) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have h := kestenLikelihood_resolvent p x
  simp only [kestenFavardTail, ContinuousMap.coe_mk, kestenPolynomial_eval_spectral]
  rw [show 2 * (n + 1) + 2 = 2 * n + 4 by omega, spectralCharacter_add_four]
  rw [show 2 * (n + 1) = 2 * n + 2 by omega]
  field_simp [hp, hp1]
  nlinarith only [congrArg (fun a : ℝ => spectralCharacter (2 * n + 2) x * a) h]

/-- The normalized tail is exactly its likelihood-weighted Favard polynomial. -/
theorem kestenNormalizedTail_eq_favard (p : Nat.Primes) (n : ℕ) :
    kestenNormalizedTail p (n + 1) = semicircleL2Observable (kestenFavardTail p n) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hs (N : ℕ) : kestenNormalizedTail p (N + 1) =
      (p : ℝ) • (kestenNormalizedTail p N - spectralCharacterVector (2 * N)) := by
    rw [kestenNormalizedTail_step p N, add_sub_cancel_left, smul_smul,
      mul_inv_cancel₀ hp, one_smul]
  induction n with
  | zero =>
      rw [hs, kestenNormalizedTail_zero]
      change (p : ℝ) • (semicircleObservableMap ⟨_, continuous_kestenLikelihood p⟩ -
        semicircleObservableMap (spectralCharacter 0)) = _
      rw [← map_sub, ← map_smul]
      apply semicircleL2Observable_eq_of_interval
      intro x
      simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply,
        ContinuousMap.coe_mk, smul_eq_mul, spectralCharacter_zero, kestenFavardTail_zero]
  | succ n ih =>
      rw [hs, ih]
      change (p : ℝ) • (semicircleObservableMap (kestenFavardTail p n) -
        semicircleObservableMap (spectralCharacter (2 * (n + 1)))) = _
      rw [← map_sub, ← map_smul]
      apply semicircleL2Observable_eq_of_interval
      intro x
      simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul,
        kestenFavardTail_succ, show 2 * (n + 1) = 2 * n + 2 by omega]

/-- Likelihood-weighted even Favard polynomials have a stationary geometric Gram kernel. -/
theorem integral_kestenFavardTail_mul (p : Nat.Primes) (n m : ℕ) :
    (∫ x, kestenFavardTail p n x * kestenFavardTail p m x
      ∂(semicircleSpectralLaw : Measure ℝ)) =
      primeReciprocal p ^ Nat.dist n m / (1 - primeReciprocal p ^ 2) := by
  rw [← inner_semicircleL2Observable, ← kestenNormalizedTail_eq_favard,
    ← kestenNormalizedTail_eq_favard, inner_kestenNormalizedTail, Nat.dist_succ_succ]


/-- Every positive even Favard polynomial has the same squared likelihood-weighted norm. -/
theorem integral_likelihood_favard_sq (p : Nat.Primes) (n : ℕ) :
    (∫ x, (kestenLikelihood p x * (kestenPolynomial p (2 * n + 2)).eval x) ^ 2
      ∂(semicircleSpectralLaw : Measure ℝ)) = ((p : ℝ) + 1) / ((p : ℝ) - 1) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hp2 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast p.property.ne_one)
  have hpSq : (p : ℝ) ^ 2 - 1 ≠ 0 := by
    rw [show (p : ℝ) ^ 2 - 1 = ((p : ℝ) - 1) * ((p : ℝ) + 1) by ring]
    exact mul_ne_zero hp2 hp1
  have he : (fun x => kestenFavardTail p n x * kestenFavardTail p n x) =
      fun x => ((p : ℝ) / ((p : ℝ) + 1)) ^ 2 *
        (kestenLikelihood p x * (kestenPolynomial p (2 * n + 2)).eval x) ^ 2 := by
    funext x
    simp only [kestenFavardTail, ContinuousMap.coe_mk]
    ring
  have h := integral_kestenFavardTail_mul p n n
  rw [he, integral_const_mul] at h
  simp only [Nat.dist_self, pow_zero] at h
  apply mul_left_cancel₀ (pow_ne_zero 2 (div_ne_zero hp hp1))
  rw [h]
  unfold primeReciprocal
  field_simp [hp, hp1, hp2, hpSq]
  ring


/-- Different prime Favard families retain the same cross-prime Gram geometry at every order. -/
theorem integral_likelihood_favard_cross (p q : Nat.Primes) (n : ℕ) :
    (∫ x, (kestenLikelihood p x * (kestenPolynomial p (2 * n + 2)).eval x) *
        (kestenLikelihood q x * (kestenPolynomial q (2 * n + 2)).eval x)
      ∂(semicircleSpectralLaw : Measure ℝ)) =
        (((p : ℝ) + 1) * ((q : ℝ) + 1)) / ((p : ℝ) * (q : ℝ) - 1) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast q.property.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  have hd : (p : ℝ) * (q : ℝ) - 1 ≠ 0 := by
    have hpgt : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
    have hqgt : 1 < (q : ℝ) := by exact_mod_cast q.property.one_lt
    have hm := mul_lt_mul_of_pos_left hqgt (show 0 < (p : ℝ) by linarith only [hpgt])
    nlinarith only [hm, hpgt]
  have he : (fun x => kestenFavardTail p n x * kestenFavardTail q n x) =
      fun x => ((p : ℝ) / ((p : ℝ) + 1) * ((q : ℝ) / ((q : ℝ) + 1))) *
        ((kestenLikelihood p x * (kestenPolynomial p (2 * n + 2)).eval x) *
          (kestenLikelihood q x * (kestenPolynomial q (2 * n + 2)).eval x)) := by
    funext x
    simp only [kestenFavardTail, ContinuousMap.coe_mk]
    ring
  have h := inner_kestenNormalizedTail_sameDepth p q (n + 1)
  rw [kestenNormalizedTail_eq_favard, kestenNormalizedTail_eq_favard,
    inner_semicircleL2Observable, he, integral_const_mul] at h
  apply mul_left_cancel₀ (mul_ne_zero (div_ne_zero hp hp1) (div_ne_zero hq hq1))
  rw [h]
  unfold primeReciprocal
  field_simp [hp, hq, hp1, hq1, hd]

end
end GaloisForLFunctions.SelbergClass.Primon



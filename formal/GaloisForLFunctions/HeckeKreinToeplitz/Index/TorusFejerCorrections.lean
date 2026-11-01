import GaloisForLFunctions.HeckeKreinToeplitz.Index.BoundedPontryaginCorrections
import GaloisForLFunctions.HTGeometry.TorusPolynomialParseval

/-!
# Uniform masses of torus correction densities

Normalize the squares of the correction packets by the number of lattice
points. Haar orthogonality identifies their mass with the average squared
correction coefficients, hence bounds it uniformly in every injective window.
-/

noncomputable section

open Complex Finset MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {I : Type*} [Countable I] {n m : ℕ}

/-- The real normalized Toeplitz density on a finite lattice window. -/
def torusKernelDensity (k : Multiplicative (I →₀ ℤ) → ℂ)
    (x : Fin n → I →₀ ℤ) (θ : UnitAddTorus I) : ℝ :=
  hermQuad (gram k (fun a => Multiplicative.ofAdd (x a)))
    (fun a => torusCharacter (-x a) θ) / n

omit [Countable I] in
theorem continuous_torusKernelDensity (k : Multiplicative (I →₀ ℤ) → ℂ)
    (x : Fin n → I →₀ ℤ) : Continuous (torusKernelDensity k x) := by
  unfold torusKernelDensity hermQuad dotProduct Matrix.mulVec
  simp only [Pi.star_apply, Complex.star_def]
  exact (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ =>
    (Complex.continuous_conj.comp (torusCharacter (-x a)).continuous).mul
      (continuous_finsetSum _ fun b _ =>
        continuous_const.mul (torusCharacter (-x b)).continuous))).div_const _

/-- The nonnegative density supplied by finitely many correction functions. -/
def torusCorrectionDensity (x : Fin n → I →₀ ℤ) (φ : Fin m → Fin n → ℂ)
    (θ : UnitAddTorus I) : ℝ :=
  (∑ i, ‖∑ a, φ i a * torusCharacter (-x a) θ‖ ^ 2) / n

omit [Countable I] in
theorem torusCorrectionDensity_nonneg (x : Fin n → I →₀ ℤ)
    (φ : Fin m → Fin n → ℂ) (θ : UnitAddTorus I) :
    0 ≤ torusCorrectionDensity x φ θ := by
  unfold torusCorrectionDensity
  positivity

omit [Countable I] in
/-- The same correction squares that repair every Gram form repair its
torus density pointwise. -/
theorem torusKernelDensity_add_correction_nonneg
    (k : Multiplicative (I →₀ ℤ) → ℂ)
    (φ : Fin m → Multiplicative (I →₀ ℤ) → ℂ)
    (hφ : ∀ (r : ℕ) (y : Fin r → Multiplicative (I →₀ ℤ)) (c : Fin r → ℂ),
      0 ≤ hermQuad (gram k y) c + ∑ i, normSq (∑ a, c a * φ i (y a)))
    (x : Fin n → I →₀ ℤ) (θ : UnitAddTorus I) :
    0 ≤ torusKernelDensity k x θ +
      torusCorrectionDensity x (fun i a => φ i (Multiplicative.ofAdd (x a))) θ := by
  have h := hφ n (fun a => Multiplicative.ofAdd (x a))
    (fun a => torusCharacter (-x a) θ)
  simp only [normSq_eq_norm_sq] at h
  unfold torusKernelDensity torusCorrectionDensity
  rw [← add_div]
  apply div_nonneg _ (Nat.cast_nonneg n)
  simpa only [mul_comm] using h

omit [Countable I] in
theorem continuous_torusCorrectionDensity (x : Fin n → I →₀ ℤ)
    (φ : Fin m → Fin n → ℂ) : Continuous (torusCorrectionDensity x φ) := by
  unfold torusCorrectionDensity
  exact (continuous_finsetSum _ fun i _ =>
    ((continuous_finsetSum _ fun a _ =>
      continuous_const.mul (torusCharacter (-x a)).continuous).norm.pow 2)).div_const _

/-- Parseval turns a correction density's mass into its coefficient average. -/
theorem integral_torusCorrectionDensity (x : Fin n → I →₀ ℤ)
    (hx : Function.Injective x) (φ : Fin m → Fin n → ℂ) :
    (∫ θ, torusCorrectionDensity x φ θ ∂torusHaar I) =
      (∑ i, ∑ a, ‖φ i a‖ ^ 2) / n := by
  have hint (i : Fin m) : Integrable
      (fun θ => ‖∑ a, φ i a * torusCharacter (-x a) θ‖ ^ 2) (torusHaar I) := by
    have hc : Continuous (fun θ => ‖∑ a, φ i a * torusCharacter (-x a) θ‖ ^ 2) :=
      (continuous_finsetSum _ fun a _ =>
        continuous_const.mul (torusCharacter (-x a)).continuous).norm.pow 2
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [torusCorrectionDensity]
  rw [integral_div,
    integral_finsetSum _ fun i _ => hint i]
  congr 1
  exact sum_congr rfl fun i _ =>
    integral_norm_sq_torusCharacter_sum_of_injective (fun a => -x a)
      (neg_injective.comp hx) (φ i)

/-- A common coefficient bound controls all normalized correction masses. -/
theorem integral_torusCorrectionDensity_le (x : Fin n → I →₀ ℤ)
    (hx : Function.Injective x) (φ : Fin m → Fin n → ℂ)
    {C : ℝ} (hφ : ∀ i a, ‖φ i a‖ ≤ C) :
    (∫ θ, torusCorrectionDensity x φ θ ∂torusHaar I) ≤ m * C ^ 2 := by
  rw [integral_torusCorrectionDensity x hx φ]
  have hsum : (∑ i, ∑ a, ‖φ i a‖ ^ 2) ≤ (m : ℝ) * ((n : ℝ) * C ^ 2) := by
    calc
      (∑ i, ∑ a, ‖φ i a‖ ^ 2) ≤ ∑ _i : Fin m, ∑ _a : Fin n, C ^ 2 :=
        sum_le_sum fun i _ => sum_le_sum fun a _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hφ i a) 2
      _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa only [Nat.cast_zero, div_zero] using
      mul_nonneg (Nat.cast_nonneg m) (sq_nonneg C)
  · apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
    nlinarith only [hsum]

end GaloisForLFunctions.HeckeKreinToeplitz

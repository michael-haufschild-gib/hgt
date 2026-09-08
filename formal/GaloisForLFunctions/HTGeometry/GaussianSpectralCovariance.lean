import GaloisForLFunctions.HTGeometry.GaussianDisplacedSpectralPole
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Correlated spectral poles under Gaussian displacement

The quadratic pole model in equation (21) of arXiv:2608.26494 applied to
finite families of spectral observations. Exact Gaussian integration gives
a covariance of rank at most two, its full null-contrast criterion, and
pointwise cancellation across three lines. These are consequences of the
shared-displacement model, beyond the paper's single-pole linewidth formula.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry


/-- Shared linear and quadratic displacement produces exactly two covariance channels. -/
theorem gaussianPole_centered_crossMoment (v : ℝ≥0) (e g b E G B : ℝ) :
    (∫ x, (gaussianPolePosition e g b x - (e + b * v)) *
      (gaussianPolePosition E G B x - (E + B * v)) ∂gaussianReal 0 v) =
        g * G * v + 2 * b * B * (v : ℝ) ^ 2 := by
  let c : Fin 5 → ℝ := ![b * B * (v : ℝ) ^ 2, -(g * B + G * b) * v,
    g * G - 2 * b * B * v, g * B + G * b, b * B]
  have hp : (fun x => (gaussianPolePosition e g b x - (e + b * v)) *
      (gaussianPolePosition E G B x - (E + B * v))) =
      (fun x => ∑ i : Fin 5, c i * x ^ i.val) := by
    funext x
    simp only [c, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero, add_zero, pow_zero,
      gaussianPolePosition]
    ring
  rw [hp, integral_gaussianFinitePolynomial]
  rcases gaussianMoments_two_through_six v with ⟨h2, h3, h4, _, _⟩
  simp [c, Fin.sum_univ_succ, h2, h3, h4, integral_id_gaussianReal]
  ring

/-- Covariance of any finite family of poles driven by one Gaussian displacement. -/
def gaussianPoleCovariance {m : ℕ} (v : ℝ≥0) (g b : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => g i * g j * v + 2 * b i * b j * (v : ℝ) ^ 2

theorem gaussianPoleCovariance_eq_integral {m : ℕ} (v : ℝ≥0) (e g b : Fin m → ℝ)
    (i j : Fin m) :
    gaussianPoleCovariance v g b i j =
      ∫ x, (gaussianPolePosition (e i) (g i) (b i) x - (e i + b i * v)) *
        (gaussianPolePosition (e j) (g j) (b j) x - (e j + b j * v)) ∂gaussianReal 0 v :=
  (gaussianPole_centered_crossMoment v _ _ _ _ _ _).symm

theorem gaussianPoleCovariance_hermitian {m : ℕ} (v : ℝ≥0) (g b : Fin m → ℝ) :
    (gaussianPoleCovariance v g b).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, gaussianPoleCovariance]
  ring

/-- A detector contrast sees only its two projections onto the linear and quadratic couplings. -/
theorem gaussianPoleCovariance_quadratic {m : ℕ} (v : ℝ≥0) (g b c : Fin m → ℝ) :
    c ⬝ᵥ (gaussianPoleCovariance v g b *ᵥ c) =
      (v : ℝ) * (∑ i, c i * g i) ^ 2 + 2 * (v : ℝ) ^ 2 * (∑ i, c i * b i) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, gaussianPoleCovariance]
  simp only [Finset.mul_sum, pow_two]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gaussianPoleCovariance_posSemidef {m : ℕ} (v : ℝ≥0) (g b : Fin m → ℝ) :
    (gaussianPoleCovariance v g b).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨gaussianPoleCovariance_hermitian v g b, ?_⟩
  intro c
  simpa only [star_trivial, gaussianPoleCovariance_quadratic] using
    (show 0 ≤ (v : ℝ) * (∑ i, c i * g i) ^ 2 +
      2 * (v : ℝ) ^ 2 * (∑ i, c i * b i) ^ 2 by positivity)

/-- Covariance factors through a two-dimensional feature space, independent of the number of poles. -/
theorem gaussianPoleCovariance_factorization {m : ℕ} (v : ℝ≥0) (g b : Fin m → ℝ) :
    gaussianPoleCovariance v g b =
      (Matrix.of fun i k => (![g i, b i] : Fin 2 → ℝ) k) *
        (Matrix.of fun k j => (![(v : ℝ) * g j, 2 * (v : ℝ) ^ 2 * b j] : Fin 2 → ℝ) k) := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ, gaussianPoleCovariance]
  ring

/-- Arbitrarily many quadratic spectral observations contain at most two covariance directions. -/
theorem gaussianPoleCovariance_rank_le_two {m : ℕ} (v : ℝ≥0) (g b : Fin m → ℝ) :
    (gaussianPoleCovariance v g b).rank ≤ 2 := by
  rw [gaussianPoleCovariance_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- The exact weighted pole fluctuation is itself a pole with aggregated couplings. -/
theorem gaussianPole_weighted_fluctuation {m : ℕ} (v : ℝ≥0) (e g b c : Fin m → ℝ)
    (x : ℝ) :
    (∑ i, c i * (gaussianPolePosition (e i) (g i) (b i) x - (e i + b i * v))) =
      gaussianPolePosition 0 (∑ i, c i * g i) (∑ i, c i * b i) x -
        (0 + (∑ i, c i * b i) * v) := by
  simp only [gaussianPolePosition, Finset.sum_mul, ← Finset.sum_sub_distrib,
    zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The finite covariance quadratic form is the exact variance of the detector contrast. -/
theorem gaussianPole_weighted_centered_second {m : ℕ} (v : ℝ≥0)
    (e g b c : Fin m → ℝ) :
    (∫ x, (∑ i, c i * (gaussianPolePosition (e i) (g i) (b i) x -
      (e i + b i * v))) ^ 2 ∂gaussianReal 0 v) =
        c ⬝ᵥ (gaussianPoleCovariance v g b *ᵥ c) := by
  simp_rw [gaussianPole_weighted_fluctuation]
  rw [gaussianPolePosition_centered_second, gaussianPoleCovariance_quadratic]
  ring

/-- At positive Gaussian variance, a contrast is dark exactly when both coupling projections vanish. -/
theorem gaussianPoleCovariance_dark_iff {m : ℕ} (a : ℝ) (g b c : Fin m → ℝ) :
    c ⬝ᵥ (gaussianPoleCovariance ⟨Real.exp a, (Real.exp_pos a).le⟩ g b *ᵥ c) = 0 ↔
      (∑ i, c i * g i) = 0 ∧ (∑ i, c i * b i) = 0 := by
  rw [gaussianPoleCovariance_quadratic]
  change Real.exp a * (∑ i, c i * g i) ^ 2 +
    2 * (Real.exp a) ^ 2 * (∑ i, c i * b i) ^ 2 = 0 ↔ _
  rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)]
  simp [mul_eq_zero, Real.exp_ne_zero]

/-- A pair resolves two independent fluctuation channels precisely through its coupling area. -/
theorem gaussianPoleCovariance_pair_minor {m : ℕ} (v : ℝ≥0) (g b : Fin m → ℝ)
    (i j : Fin m) :
    gaussianPoleCovariance v g b i i * gaussianPoleCovariance v g b j j -
      gaussianPoleCovariance v g b i j ^ 2 =
        2 * (v : ℝ) ^ 3 * (g i * b j - g j * b i) ^ 2 := by
  simp only [gaussianPoleCovariance]
  ring

/-- Three spectral lines admit an explicit displacement-cancelling contrast. -/
def gaussianPoleTripleContrast (g b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![g 1 * b 2 - g 2 * b 1, g 2 * b 0 - g 0 * b 2, g 0 * b 1 - g 1 * b 0]

theorem gaussianPoleTripleContrast_projections (g b : Fin 3 → ℝ) :
    (∑ i, gaussianPoleTripleContrast g b i * g i) = 0 ∧
      (∑ i, gaussianPoleTripleContrast g b i * b i) = 0 := by
  simp [gaussianPoleTripleContrast, Fin.sum_univ_succ]
  constructor <;> ring

/-- Cancellation holds for every displacement value, stronger than zero Gaussian variance. -/
theorem gaussianPoleTripleContrast_pointwise (v : ℝ≥0) (e g b : Fin 3 → ℝ) (x : ℝ) :
    (∑ i, gaussianPoleTripleContrast g b i *
      (gaussianPolePosition (e i) (g i) (b i) x - (e i + b i * v))) = 0 := by
  rw [gaussianPole_weighted_fluctuation, (gaussianPoleTripleContrast_projections g b).1,
    (gaussianPoleTripleContrast_projections g b).2]
  simp [gaussianPolePosition]

end GaloisForLFunctions.HTGeometry

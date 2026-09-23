import GaloisForLFunctions.RHTower.Sieve.LSeriesBlockDecomposition
import GaloisForLFunctions.RHTower.Sieve.GhsStepFour
/-!
# The mean square of a Dirichlet polynomial, block by block

Minkowski for the weighted mean square applied to the dyadic block decomposition gives

`(∫ ‖L(a,σ+iy)‖² dy/(1+y²))^{1/2} ≤ ∑_j (∫ ‖L(a_j,σ+iy)‖² dy/(1+y²))^{1/2}`,

`a_j` the coefficients carried by `2^j ≤ n < 2^{j+1}`.  Each block inherits the prime support of `a`, so each
may be sieved separately — and the sieve level `(z_j, Y_j)` is then free on each block, which is what the
Selberg count requires: its main term `2·(window)/log Y` is sharp only when `log Y` is comparable to the
logarithm of the primes in play, and on the block that logarithm is `j log 2`.

The parameters are arbitrary functions of the block index in the statement; nothing is assumed about them
beyond admissibility of each level.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Finset

/-- **The mean square of a Dirichlet polynomial against its dyadic blocks.**  Minkowski for the weighted
mean square, applied to the dyadic block decomposition. -/
theorem sqrt_integral_lorentz_normSq_LSeries_le_sum_blocks {a : ℕ → ℂ} {M : ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 M) (σ : ℝ) :
    Real.sqrt (∫ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ (2 : ℕ) * (1 + y ^ (2 : ℕ))⁻¹)
      ≤ ∑ j ∈ Finset.range (Nat.log 2 M + 1),
          Real.sqrt (∫ y : ℝ,
            ‖LSeries (coeffBlock a (fun n => Nat.log 2 n) j) ((σ : ℂ) + (y : ℝ) * I)‖ ^ (2 : ℕ)
              * (1 + y ^ (2 : ℕ))⁻¹) := by
  classical
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  set W : ℝ → ℂ := fun y => (((1 + y ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) with hW
  have hWnorm : ∀ y : ℝ, ‖W y‖ = (1 + y ^ (2 : ℕ))⁻¹ := by
    intro y
    rw [hW, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmW : AEStronglyMeasurable W volume := by
    refine Continuous.aestronglyMeasurable ?_
    rw [hW]
    refine Complex.continuous_ofReal.comp ?_
    have hdiv : Continuous fun y : ℝ => 1 / (1 + y ^ (2 : ℕ)) :=
      continuous_const.div (by fun_prop) fun y => by positivity
    simpa [one_div] using hdiv
  set g : ℕ → ℝ → ℂ := fun j y =>
    LSeries (coeffBlock a (fun n => Nat.log 2 n) j) ((σ : ℂ) + (y : ℝ) * I) with hg
  have hmg : ∀ j ∈ Finset.range (Nat.log 2 M + 1), AEStronglyMeasurable (g j) volume := by
    intro j _
    exact (continuous_LSeries_line_of_support hs0 (coeffBlock_support hsupp) σ).aestronglyMeasurable
  have hig : ∀ j ∈ Finset.range (Nat.log 2 M + 1),
      Integrable fun y => ‖g j y‖ ^ (2 : ℕ) * ‖W y‖ := by
    intro j _
    have h := integrable_lorentz_normSq_LSeries hs0 (coeffBlock_support (κ := fun n => Nat.log 2 n)
      (j := j) hsupp) σ
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hWnorm y]
  have hpt : ∀ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ (2 : ℕ) * (1 + y ^ (2 : ℕ))⁻¹
      = ‖∑ j ∈ Finset.range (Nat.log 2 M + 1), g j y‖ ^ (2 : ℕ) * ‖W y‖ := by
    intro y
    rw [hWnorm y, hg, LSeries_eq_sum_dyadic_blocks hsupp ((σ : ℂ) + (y : ℝ) * I)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  refine le_trans (GaloisForLFunctions.HTGeometry.sqrt_integral_normSq_sum_mul_weight_le _ g W hmg hmW hig) (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [hWnorm y]

/-- **The per-block sieve bound.**  Each dyadic block of a prime-supported polynomial may be sieved at its
own level: the mean square of the whole polynomial is at most the square of the sum of the block roots, and
the level `(z_j, Y_j)` is free on each block.  This is what the Selberg count requires, being sharp only when
`log Y` is comparable to the logarithm of the primes in play. -/
theorem sqrt_integral_lorentz_normSq_LSeries_le_sum_prime_sieve {a : ℕ → ℂ} {M : ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 M)
    (hprime : ∀ n ∈ Finset.Icc 1 M, a n ≠ 0 → n.Prime) (σ : ℝ) (Z Yl : ℕ → ℕ)
    (hY : ∀ j, 1 ≤ Yl j) (hYz : ∀ j, Yl j ≤ Z j) (hz : ∀ j, 2 ≤ Z j)
    (hlog : ∀ j, 0 < Real.log (Yl j)) :
    Real.sqrt (∫ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ (2 : ℕ) * (1 + y ^ (2 : ℕ))⁻¹)
      ≤ ∑ j ∈ Finset.range (Nat.log 2 M + 1),
          Real.sqrt (25 * Real.pi ^ (2 : ℕ)
            * sieveMeanSquare (coeffBlock a (fun n => Nat.log 2 n) j) (Finset.Icc 1 M) σ
                (Z j) (Yl j)) := by
  classical
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  refine le_trans (sqrt_integral_lorentz_normSq_LSeries_le_sum_blocks hsupp σ) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine Real.sqrt_le_sqrt ?_
  have hb := integral_lorentz_normSq_LSeries_le_sieveMeanSquare hs0
    (coeffBlock_support (κ := fun n => Nat.log 2 n) (j := j) hsupp)
    (coeffBlock_prime (κ := fun n => Nat.log 2 n) (j := j) hprime) σ (Z j) (Yl j)
    (hY j) (hYz j) (hz j) (hlog j)
  exact hb

end RHTower.Sieve
end

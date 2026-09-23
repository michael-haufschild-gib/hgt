import GaloisForLFunctions.RHTower.Sieve.SquareSieve

/-!
# Dirichlet rows and the Halász–Montgomery frame

A Dirichlet polynomial `∑_{n ≤ N} a_n n^{it}` is the coefficient of the vector `a` against the row

`n ↦ n^{it} = exp(i t log n)`,

exactly as a trigonometric polynomial is a coefficient against `expRow`.  The rows are unimodular,
so each has squared length `N`, and their Gram entries are the exponential sums `∑_{n ≤ N} n^{i(u-t)}`.

Feeding these rows to the almost-orthogonality bound gives the Halász–Montgomery inequality in the
form used for mean values of Dirichlet polynomials: the mean square at a family of frequencies is
controlled by the largest Gram row.  What remains analytic — and is not proved here — is the
estimate for `∑_{n ≤ N} n^{iu}` at `u ≠ 0`, which is what makes the Gram rows small.

Indices run over `Fin N` with `n` standing for `n + 1`, so the row is `1^{it}, …, N^{it}`.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- The Dirichlet row `n ↦ n^{it}`, of length `N`. -/
noncomputable def dirRow (N : ℕ) (t : ℝ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun n : Fin N =>
    Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I))

/-- Dirichlet rows are unimodular in each coordinate. -/
theorem norm_dirRow_coord (N : ℕ) (t : ℝ) (n : Fin N) : ‖(dirRow N t) n‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The squared length of a Dirichlet row is the number of terms. -/
theorem norm_dirRow_sq (N : ℕ) (t : ℝ) : ‖dirRow N t‖ ^ (2 : ℕ) = (N : ℝ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have hone : ∀ n : Fin N, ‖(dirRow N t) n‖ ^ (2 : ℕ) = 1 := by
    intro n
    rw [norm_dirRow_coord]
    norm_num
  rw [Finset.sum_congr rfl (fun n _ => hone n), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The Gram entry of two Dirichlet rows is the exponential sum of the frequency difference. -/
theorem inner_dirRow (N : ℕ) (t u : ℝ) :
    ⟪dirRow N t, dirRow N u⟫_ℂ
      = ∑ n : Fin N,
          Complex.exp ((((u - t) * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hconj : (starRingEnd ℂ)
      (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((-(t * Real.log ((n : ℕ) + 1)) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  have hsum : Complex.exp (((u * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((-(t * Real.log ((n : ℕ) + 1)) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((u - t) * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [dirRow, RCLike.inner_apply]
  rw [hconj, hsum]

/-- **Halász–Montgomery for Dirichlet rows.**  The mean square of a Dirichlet polynomial over a
family of frequencies is controlled by the largest Gram row. -/
theorem dirichlet_bessel {ι : Type*} (N : ℕ) (s : Finset ι) (τ : ι → ℝ) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hrow : ∀ r ∈ s, ∑ t ∈ s, ‖⟪dirRow N (τ r), dirRow N (τ t)⟫_ℂ‖ ≤ Δ)
    (a : EuclideanSpace ℂ (Fin N)) :
    ∑ r ∈ s, ‖⟪dirRow N (τ r), a⟫_ℂ‖ ^ (2 : ℕ) ≤ Δ * ‖a‖ ^ (2 : ℕ) :=
  sum_norm_inner_sq_le_of_schur s (fun r => dirRow N (τ r)) hΔ0 hrow a

/-- **The bilinear form of Dirichlet rows.** -/
theorem dirichlet_bilinear {ι : Type*} (N : ℕ) (s : Finset ι) (τ : ι → ℝ) {Δ : ℝ}
    (hrow : ∀ r ∈ s, ∑ t ∈ s, ‖⟪dirRow N (τ r), dirRow N (τ t)⟫_ℂ‖ ≤ Δ)
    (c : ι → ℂ) :
    ‖∑ r ∈ s, c r • dirRow N (τ r)‖ ^ (2 : ℕ) ≤ Δ * ∑ r ∈ s, ‖c r‖ ^ (2 : ℕ) :=
  norm_sum_smul_sq_le_of_schur s (fun r => dirRow N (τ r)) hrow c

end RHTower.Sieve

import GaloisForLFunctions.RHTower.Sieve.DirichletMeanSquare

/-!
# Extracting the diagonal from the mean square

Splitting each inner sum of `integral_normSq_dirPoly_eq` at `n = m` isolates the diagonal, whose
phase integral is `T`:

`∫_0^T |F|² - T ∑_n |a_n|² = ∑_m ∑_{n ≠ m} a_m conj(a_n) ∫_0^T e^{it(log m - log n)} dt`,

and hence

`‖∫_0^T |F|² - T ∑_n |a_n|²‖ ≤ ∑_m ∑_{n ≠ m} |a_m| |a_n| · 2/|log(m/n)|`.

This is the mean value theorem for Dirichlet polynomials reduced to a single inequality: the entire
content still missing is a bound for the right-hand side, which is a Hilbert inequality for the
frequencies `log n`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **The mean square minus its diagonal.** -/
theorem integral_normSq_dirPoly_sub_diag (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ((‖dirPoly N a t‖ ^ 2 : ℝ) : ℂ))
        - (T : ℂ) * ∑ m : Fin N, ((‖a m‖ ^ 2 : ℝ) : ℂ)
      = ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
          (a m * (starRingEnd ℂ) (a n))
            * (∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
                - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)) := by
  classical
  rw [integral_normSq_dirPoly_eq]
  have hsplit : ∀ m : Fin N,
      (∑ n : Fin N, (a m * (starRingEnd ℂ) (a n))
          * (∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
              - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)))
        = (a m * (starRingEnd ℂ) (a m))
            * (∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
                - Real.log (((m : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
          + ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, (a m * (starRingEnd ℂ) (a n))
            * (∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
                - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)) :=
    fun m => (Finset.add_sum_erase _ _ (Finset.mem_univ m)).symm
  rw [Finset.sum_congr rfl (fun m _ => hsplit m), Finset.sum_add_distrib]
  have hdiag : ∀ m : Fin N, (a m * (starRingEnd ℂ) (a m))
      * (∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
          - Real.log (((m : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
      = (T : ℂ) * ((‖a m‖ ^ 2 : ℝ) : ℂ) := by
    intro m
    rw [integral_dirPhase_diag ((m : ℕ)) T, mul_comm (a m) ((starRingEnd ℂ) (a m)),
      conj_mul_self]
    ring
  rw [Finset.sum_congr rfl (fun m _ => hdiag m), ← Finset.mul_sum]
  ring

/-- **The mean value theorem for Dirichlet polynomials, reduced to its off-diagonal sum.** -/
theorem norm_integral_normSq_dirPoly_sub_diag_le (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    ‖(∫ t in (0 : ℝ)..T, ((‖dirPoly N a t‖ ^ 2 : ℝ) : ℂ))
        - (T : ℂ) * ∑ m : Fin N, ((‖a m‖ ^ 2 : ℝ) : ℂ)‖
      ≤ ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
          ‖a m‖ * ‖a n‖
            * (2 / |Real.log (((m : ℕ) : ℝ) + 1) - Real.log (((n : ℕ) : ℝ) + 1)|) := by
  classical
  rw [integral_normSq_dirPoly_sub_diag]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun m _ => ?_
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun n hn => ?_
  have hmn : ((m : ℕ)) ≠ ((n : ℕ)) := by
    have hne : n ≠ m := (Finset.mem_erase.mp hn).1
    exact fun hcon => hne (Fin.val_injective hcon).symm
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  refine mul_le_mul_of_nonneg_left (norm_integral_dirPhase_off hmn T) ?_
  positivity

end RHTower.Sieve

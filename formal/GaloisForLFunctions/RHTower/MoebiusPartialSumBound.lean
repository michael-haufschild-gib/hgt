import GaloisForLFunctions.RHTower.ZetaOneLineUniformLower
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.RHTower.Sieve.PerronNearDiagonal

/-!
# The Möbius series, bounded uniformly on the shifted line

The corpus's `LSeries_moebius_eq_inv_riemannZeta` identifies the Möbius Dirichlet series with
`1/ζ` right of the one-line, so the uniform lower bound for `ζ` on the shifted line becomes a
uniform upper bound for the series — the pointwise input of the Perron and Halász layers.

* `norm_LSeries_moebius_le_uniform`.
-/

namespace RHTower

open Complex

noncomputable section

/-- **The Möbius series is bounded by a power of the logarithm on the shifted line**, uniformly in
the frequency.  This is the pointwise input of the Perron and Halász layers. -/
theorem norm_LSeries_moebius_le_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 5 / 4 →
      ‖LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ K * (Real.log (|t| + Real.exp 1)) ^ 11 := by
  obtain ⟨K, hK0, hK⟩ := exists_uniform_upper_bound_inv_riemannZeta
  refine ⟨K, hK0, ?_⟩
  intro σ t hσ1 hσ2
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have hs : 1 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by rw [hre]; exact hσ1
  rw [LSeries_moebius_eq_inv_riemannZeta hs]
  exact hK σ t hσ1 hσ2


/-- The Möbius values have modulus at most one. -/
theorem norm_moebius_le_one_moebiusPartialSumBound (n : ℕ) : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  have h : (ArithmeticFunction.moebius n : ℤ) = 0 ∨ (ArithmeticFunction.moebius n : ℤ) = 1
      ∨ (ArithmeticFunction.moebius n : ℤ) = -1 := by
    rcases eq_or_ne (ArithmeticFunction.moebius n) 0 with h | h
    · exact Or.inl (by exact_mod_cast h)
    · rcases (ArithmeticFunction.moebius_ne_zero_iff_eq_or).mp h with h1 | h1
      · exact Or.inr (Or.inl (by exact_mod_cast h1))
      · exact Or.inr (Or.inr (by exact_mod_cast h1))
  rcases h with h | h | h <;> rw [h] <;> simp

/-- **The trivial bound on a truncated Möbius polynomial**: it is dominated termwise by the
truncated real series `∑ n^{−σ}`.  This is the baseline against which the `1/ζ` bound is a saving,
and it is what fixes the abscissa at which the saving is real. -/
theorem norm_moebius_partialSum_le_trivial (s : ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N,
        LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s n‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
  refine LSeries.norm_term_le s ?_
  simpa using norm_moebius_le_one_moebiusPartialSumBound n


/-- **The abscissa transfer.**  A truncated Dirichlet polynomial on the one-line is bounded by the
same polynomial at a shifted abscissa, at the cost of `N^{σ−1}`.  With `σ = 1 + A/log N` that cost
is `e^A`, which is what makes the shifted abscissa usable: the saving there has to beat it. -/
theorem norm_partialSum_le_abscissa_shift (a : ℕ → ℂ) (N : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, LSeries.term a ((1 : ℂ) + (t : ℂ) * Complex.I) n‖
      ≤ ((N : ℝ)) ^ (σ - 1)
        * ∑ n ∈ Finset.Icc 1 N,
            ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hre1 : ((1 : ℂ) + (t : ℂ) * Complex.I).re = 1 := by simp
  have hres : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn0, if_neg hn0, hre1, hres]
  have hstep : ‖a n‖ / (n : ℝ) ^ (1 : ℝ)
      = (n : ℝ) ^ (σ - 1) * (‖a n‖ / (n : ℝ) ^ σ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hnR.le, ← Real.rpow_neg hnR.le]
    rw [show (n : ℝ) ^ (σ - 1) * (‖a n‖ * (n : ℝ) ^ (-σ))
        = ‖a n‖ * ((n : ℝ) ^ (σ - 1) * (n : ℝ) ^ (-σ)) by ring]
    rw [← Real.rpow_add hnR]
    congr 2
    ring
  rw [hstep]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine Real.rpow_le_rpow hnR.le ?_ (by linarith)
  exact_mod_cast hnN


/-- **The Perron integrand of the Möbius series is bounded by a power of the logarithm.**  This is
the form in which the uniform `ζ` bound enters a contour integral: the modulus of the integrand
factors, the `N^s` contributes `N^σ`, and the reciprocal zeta contributes the logarithmic power. -/
theorem exists_norm_moebius_perron_integrand_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (σ t : ℝ), 1 ≤ N → 1 < σ → σ ≤ 5 / 4 →
      ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          * ((N : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ K * (Real.log (|t| + Real.exp 1)) ^ 11 * ((N : ℝ) ^ σ)
            / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_uniform_upper_bound_inv_riemannZeta
  refine ⟨K, hK0, ?_⟩
  intro N σ t hN hσ1 hσ2
  have hN0 : 0 < N := hN
  have hpow : ‖(N : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ = (N : ℝ) ^ σ := by
    rw [Complex.norm_natCast_cpow_of_pos hN0]
    congr 1
    simp
  have hzeta := hK σ t hσ1 hσ2
  rw [norm_div, norm_mul, hpow]
  refine div_le_div_of_nonneg_right ?_ ?_ |>.trans_eq rfl
  · have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ σ := by positivity
    have hmul := mul_le_mul_of_nonneg_right hzeta hNpow
    calc ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ * (N : ℝ) ^ σ
        ≤ (K * (Real.log (|t| + Real.exp 1)) ^ 11) * (N : ℝ) ^ σ := hmul
      _ = K * (Real.log (|t| + Real.exp 1)) ^ 11 * ((N : ℝ) ^ σ) := by ring
  · exact norm_nonneg _


/-- **The truncated Perron formula at the Möbius coefficients.**  The Mertens sum is the truncated
vertical integral of its own Dirichlet polynomial against the Perron kernel, with an explicit
error. -/
theorem norm_mertens_sub_perron_integral_le (N : ℕ) {σ T : ℝ} (hσ : 1 ≤ σ) (hT : 0 < T) :
    ‖(∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
            (∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℂ)
                * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * Complex.I))))
              * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * Complex.I)
                  / ((σ : ℂ) + (t : ℝ) * Complex.I))‖
      ≤ (((N : ℝ) + 1 / 2)) ^ σ
          * (5 * (1 + Real.log N) + 4 * (1 + Real.log N)) / (Real.pi * T) := by
  have hmin : min N N = N := min_self N
  have hmain := RHTower.Sieve.norm_sum_Icc_sub_perron_integral_near_le
    (c := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (M := N) (N := N)
    (B := 1) norm_moebius_le_one_moebiusPartialSumBound hσ hT
  rw [hmin, one_mul] at hmain
  exact hmain

end

end RHTower

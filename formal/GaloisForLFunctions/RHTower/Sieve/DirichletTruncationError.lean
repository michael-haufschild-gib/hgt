import GaloisForLFunctions.RHTower.Sieve.PrimeAbscissaSumBound

/-!
# Truncating a bounded multiplicative Dirichlet series

The mean-square estimates of the corpus are stated for Dirichlet *polynomials*, while the Euler bound is
stated for the whole series.  Passing between them costs the tail

`‖∑_n f(n)n^{-s} − ∑_{n ≤ L} f(n)n^{-s}‖ ≤ ∑_{n > L} n^{-σ} ≤ L^{1-σ}/(σ−1)`,

the last step by the integral test.  At `σ = 1 + 1/log L` the bound is `e·log L`, and at
`σ = 1 + A/log L` it is `e^{-A} log L / A`: the truncation is harmless once the polynomial is longer than
the abscissa's reciprocal scale.

This is the entry point for the mean-square route, which needs a polynomial of finite length.
-/

namespace RHTower.Sieve

open MeasureTheory Set

/-- **The tail of the `p`-series beyond `L`**, by the integral test. -/
theorem tsum_tail_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) {L : ℕ} (hL : 1 ≤ L) :
    ∑' j : ℕ, (((j + L + 1 : ℕ) : ℝ)) ^ (-σ) ≤ ((L : ℝ)) ^ (1 - σ) / (σ - 1) := by
  have hL0 : (0 : ℝ) < ((L : ℕ) : ℝ) := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ ((L : ℕ) : ℝ) := by exact_mod_cast hL
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici ((L : ℕ) : ℝ)) := by
    refine (antitoneOn_rpow_neg_Ici (by linarith : (0 : ℝ) < σ)).mono ?_
    intro x hx
    exact le_trans hL1 hx
  have hint : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Set.Ioi ((L : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) hL0
  have hnn : ∀ t ∈ Set.Ioi ((L : ℕ) : ℝ), (0 : ℝ) ≤ t ^ (-σ) := by
    intro t ht
    exact Real.rpow_nonneg (le_of_lt (lt_trans hL0 ht)) _
  have hval : (∫ x in Set.Ioi ((L : ℕ) : ℝ), x ^ (-σ))
      = ((L : ℝ)) ^ (1 - σ) / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hL0,
      show (-σ + 1) = -(σ - 1) by ring, show (1 - σ) = -(σ - 1) by ring, neg_div_neg_eq]
  have hmain := AntitoneOn.tsum_comp_add_le_integral L hanti hint hnn
  rw [hval] at hmain
  exact hmain

section

variable {f : ℕ → ℂ} {s : ℂ}

/-- **The truncation error of the twisted series.** -/
theorem norm_tsum_sub_sum_range_le (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) (L : ℕ) :
    ‖(∑' n : ℕ, twistedSummand f s n) -
        ∑ n ∈ Finset.range (L + 1), twistedSummand f s n‖
      ≤ ∑' j : ℕ, (((j + L + 1 : ℕ) : ℝ)) ^ (-s.re) := by
  have hnormsum := summable_norm_twistedSummand hbdd hs
  have hsum : Summable (fun n : ℕ => twistedSummand f s n) := Summable.of_norm hnormsum
  have hsplit := hsum.sum_add_tsum_nat_add (L + 1)
  have heq : (∑' n : ℕ, twistedSummand f s n) -
      ∑ n ∈ Finset.range (L + 1), twistedSummand f s n
      = ∑' j : ℕ, twistedSummand f s (j + (L + 1)) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [heq]
  -- shifted summability with the shifted functions named, so no summand is unfolded
  have hshiftnorm : Summable (fun j : ℕ => ‖twistedSummand f s (j + (L + 1))‖) :=
    (summable_nat_add_iff (f := fun n : ℕ => ‖twistedSummand f s n‖) (L + 1)).2 hnormsum
  refine le_trans (norm_tsum_le_tsum_norm hshiftnorm) ?_
  refine Summable.tsum_le_tsum (fun j => ?_) hshiftnorm
    ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-s.re)) (L + 1)).2
      (summable_nat_rpow_neg hs))
  exact norm_twistedSummand_le hbdd (by omega : 0 < j + (L + 1))

/-- The truncation error in closed form. -/
theorem norm_tsum_sub_sum_range_le_pow (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re)
    {L : ℕ} (hL : 1 ≤ L) :
    ‖(∑' n : ℕ, twistedSummand f s n) -
        ∑ n ∈ Finset.range (L + 1), twistedSummand f s n‖
      ≤ ((L : ℝ)) ^ (1 - s.re) / (s.re - 1) :=
  le_trans (norm_tsum_sub_sum_range_le hbdd hs L) (tsum_tail_rpow_neg_le hs hL)

end

end RHTower.Sieve

import GaloisForLFunctions.HTGeometry.TrigammaLeadingAsymptotic
import GaloisForLFunctions.HTGeometry.PolygammaShift
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary

/-!
# The polygamma series from the shift law

The all-order integer shift law `ψ⁽ʲ⁾(z+N) = ψ⁽ʲ⁾(z) + Σ_{i<N} (−1)ʲ j!/(z+i)^{j+1}` together with
the far-field anchor `ψ⁽ᵐ⁺¹⁾(z+N) → 0` turns the partial sums of `Σ (z+n)^{−(m+2)}` into a convergent
series with an explicit limit:

`Σ_n (z+n)^{−(m+2)} = (−1)^m/(m+1)! · ψ⁽ᵐ⁺¹⁾(z)`.

For `m = 0` this is the trigamma series.  The representation is the input for the leading asymptotic
of every polygamma jet on a vertical line.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- A shifted `p`-series with exponent at least two is summable. -/
theorem summable_one_div_shift_pow {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun n : ℕ => 1 / (σ + n) ^ k) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < σ + n := fun n => by positivity
  have hmaj : Summable (fun n : ℕ => (1 / σ ^ (k - 2)) * ((1 + 1 / σ)
      * (1 / ((σ + n) * (σ + n + 1))))) :=
    (((hasSum_one_div_shift_mul_succ hσ).summable).mul_left _).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  have h1 : (0 : ℝ) < σ + n := hpos n
  have hle : σ ≤ σ + (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsplit : (σ + n) ^ k = (σ + n) ^ (k - 2) * (σ + n) ^ (2 : ℕ) := by
    rw [← pow_add]
    congr 1
    omega
  have hstep : 1 / (σ + n) ^ k ≤ 1 / (σ ^ (k - 2) * (σ + n) ^ (2 : ℕ)) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσ.le hle _) (by positivity)
  have hsq : 1 / (σ + n) ^ (2 : ℕ) ≤ (1 + 1 / σ) * (1 / ((σ + n) * (σ + n + 1))) := by
    have hstep2 : 1 / ((σ + n) ^ (2 : ℕ)) = (1 / ((σ + n) * (σ + n + 1))) * ((σ + n + 1) / (σ + n)) := by
      field_simp
    have hfrac : (σ + n + 1) / (σ + n) ≤ 1 + 1 / σ := by
      rw [div_le_iff₀ h1]
      have hinv : 1 ≤ 1 / σ * (σ + (n : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 1 / σ)
        rw [one_div, inv_mul_cancel₀ hσ.ne'] at hmul
        rwa [one_div]
      nlinarith
    rw [hstep2]
    have hnn : (0 : ℝ) ≤ 1 / ((σ + n) * (σ + n + 1)) := by positivity
    calc (1 / ((σ + n) * (σ + n + 1))) * ((σ + n + 1) / (σ + n))
        ≤ (1 / ((σ + n) * (σ + n + 1))) * (1 + 1 / σ) := mul_le_mul_of_nonneg_left hfrac hnn
      _ = (1 + 1 / σ) * (1 / ((σ + n) * (σ + n + 1))) := by ring
  have hinvsplit : 1 / (σ ^ (k - 2) * (σ + n) ^ (2 : ℕ)) = (1 / σ ^ (k - 2)) * (1 / (σ + n) ^ (2 : ℕ)) := by
    field_simp
  calc 1 / (σ + n) ^ k ≤ 1 / (σ ^ (k - 2) * (σ + n) ^ (2 : ℕ)) := hstep
    _ = (1 / σ ^ (k - 2)) * (1 / (σ + n) ^ (2 : ℕ)) := hinvsplit
    _ ≤ (1 / σ ^ (k - 2)) * ((1 + 1 / σ) * (1 / ((σ + n) * (σ + n + 1)))) := by
        have hnn : (0 : ℝ) ≤ 1 / σ ^ (k - 2) := by positivity
        exact mul_le_mul_of_nonneg_left hsq hnn

/-- The polygamma terms are dominated by a shifted `p`-series. -/
theorem summable_polygamma_terms {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (m : ℕ) :
    Summable (fun n : ℕ => (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹) := by
  refine Summable.of_norm_bounded (summable_one_div_shift_pow hσ (m + 2) (by omega))
    (fun n => ?_)
  have hge : σ + n ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
    norm_vertical_add_nat_ge_re t n
  have hpos : (0 : ℝ) < σ + n := by positivity
  rw [norm_inv, norm_pow, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hge _)

/-- **The polygamma series.**  On the right half-plane the `(m+2)`-nd reciprocal powers sum to the
`(m+1)`-st digamma jet up to the explicit constant `(−1)^m/(m+1)!`. -/
theorem hasSum_polygamma_series {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (m : ℕ) :
    HasSum (fun n : ℕ => (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)
      ((-1 : ℂ) ^ m / ((m + 1).factorial : ℂ)
        * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsummable := summable_polygamma_terms hσ t m
  have hoff : ∀ p : ℕ, s ≠ -(p : ℂ) := by
    intro p hp
    have hre : s.re = σ := by rw [hs]; simp
    rw [hp] at hre
    simp at hre
    have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    linarith
  have hfact : ((m + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 1))
  rw [hsummable.hasSum_iff_tendsto_nat]
  have hshift : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((s + (n : ℂ)) ^ (m + 2))⁻¹
      = ((-1 : ℂ) ^ (m + 1) / ((m + 1).factorial : ℂ))
        * (iteratedDeriv (m + 1) Complex.digamma (s + (N : ℂ))
          - iteratedDeriv (m + 1) Complex.digamma s) := by
    intro N
    have hlaw := HTGeometry.iteratedDeriv_digamma_add_nat (m + 1) s hoff N
    have hterm : ∀ n ∈ Finset.range N,
        (-1 : ℂ) ^ (m + 1) * (((m + 1).factorial : ℕ) : ℂ) / (s + (n : ℂ)) ^ (m + 1 + 1)
          = ((-1 : ℂ) ^ (m + 1) * (((m + 1).factorial : ℕ) : ℂ))
            * ((s + (n : ℂ)) ^ (m + 2))⁻¹ := by
      intro n _
      rw [div_eq_mul_inv]
    have hcancel : ((-1 : ℂ) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℂ))
        * ((-1 : ℂ) ^ (m + 1) * (((m + 1).factorial : ℕ) : ℂ)) = 1 := by
      have hfactor : ((-1 : ℂ) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℂ))
          * ((-1 : ℂ) ^ (m + 1) * (((m + 1).factorial : ℕ) : ℂ))
          = ((-1 : ℂ) ^ (m + 1) * (-1 : ℂ) ^ (m + 1))
            * ((((m + 1).factorial : ℕ) : ℂ) / (((m + 1).factorial : ℕ) : ℂ)) := by
        ring
      rw [hfactor, div_self hfact, mul_one, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hlaw, add_sub_cancel_left, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← mul_assoc,
      hcancel, one_mul]
  have hfar : Tendsto (fun N : ℕ => iteratedDeriv (m + 1) Complex.digamma (s + (N : ℂ)))
      atTop (nhds 0) := iteratedDeriv_digamma_add_nat_tendsto m s
  have hlim := (hfar.sub
      (tendsto_const_nhds (x := iteratedDeriv (m + 1) Complex.digamma s)
        (f := atTop (α := ℕ)))).const_mul
    ((-1 : ℂ) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℂ))
  have hval : ((-1 : ℂ) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℂ))
      * (0 - iteratedDeriv (m + 1) Complex.digamma s)
      = (-1 : ℂ) ^ m / (((m + 1).factorial : ℕ) : ℂ)
        * iteratedDeriv (m + 1) Complex.digamma s := by
    rw [zero_sub, pow_succ]
    field_simp
  rw [hval] at hlim
  exact hlim.congr (fun N => (hshift N).symm)

end GaloisForLFunctions

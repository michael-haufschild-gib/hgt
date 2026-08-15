import GaloisForLFunctions.HTGeometry.PolygammaSeries
import GaloisForLFunctions.HTGeometry.DigammaBounds

/-!
# Sharp vertical decay of the polygamma tower

On a vertical line the order-`m+1` polygamma jet decays like the exact power `|t|^{-(m+1)}`, with a
constant that does not depend on the abscissa at all:

`‖ψ⁽ᵐ⁺¹⁾(σ + it)‖ ≤ (m+1)! (1 + π/2) |t|^{-(m+1)}`,   `σ > 0`,  `|t| ≥ 1`.

The mechanism is the polygamma series `ψ⁽ᵐ⁺¹⁾(s) = (−1)ᵐ (m+1)! Σ_n (s+n)^{−(m+2)}` together with
the elementary factorization

`|s+n|^{m+2} = ((σ+n)² + t²) · |s+n|^m ≥ ((σ+n)² + t²) · |t|^m`,

which pulls the whole excess power out of the sum and leaves the trigamma sum
`Σ_n ((σ+n)² + t²)^{-1} ≤ |t|^{-2} + π/(2|t|)`, itself the arctan telescope.

A Cauchy estimate on a disc of fixed radius produces only `O(|t|^{-1})` for every order; the series
route is what gives the sharp order, and it is what a derivative bound on the Gamma frequency symbol
consumes.
-/

open Complex Filter

namespace GaloisForLFunctions

/-- The modulus of a vertical shift, squared. -/
theorem norm_sq_vertical_add_nat (σ t : ℝ) (n : ℕ) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2 = (σ + n) ^ 2 + |t| ^ 2 := by
  have hw : (σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)
      = ((σ + n : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hw, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity), sq_abs]

/-- The height is a lower bound for the modulus of a vertical shift. -/
theorem abs_le_norm_vertical_add_nat (σ t : ℝ) (n : ℕ) :
    |t| ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
  have hsq := norm_sq_vertical_add_nat σ t n
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [norm_nonneg ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)), abs_nonneg t,
    sq_nonneg (σ + (n : ℝ))]

/-- **Termwise excess-power extraction.**  Every term of the polygamma series is the corresponding
trigamma term divided by the exact excess power of the height. -/
theorem norm_polygamma_term_le {σ t : ℝ} (ht : t ≠ 0) (m n : ℕ) :
    ‖(((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹‖
      ≤ (1 / |t| ^ m) * (1 / ((σ + n) ^ 2 + |t| ^ 2)) := by
  set w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) with hwdef
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hsq : ‖w‖ ^ 2 = (σ + n) ^ 2 + |t| ^ 2 := norm_sq_vertical_add_nat σ t n
  have hge : |t| ≤ ‖w‖ := abs_le_norm_vertical_add_nat σ t n
  have hApos : (0 : ℝ) < (σ + n) ^ 2 + |t| ^ 2 := by positivity
  have hpow : ‖w‖ ^ (m + 2) = ((σ + n) ^ 2 + |t| ^ 2) * ‖w‖ ^ m := by
    rw [show m + 2 = 2 + m from by omega, pow_add, hsq]
  have hlow : ((σ + n) ^ 2 + |t| ^ 2) * |t| ^ m ≤ ‖w‖ ^ (m + 2) := by
    rw [hpow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) hge m) hApos.le
  have hstep : 1 / ‖w‖ ^ (m + 2) ≤ 1 / (((σ + n) ^ 2 + |t| ^ 2) * |t| ^ m) :=
    one_div_le_one_div_of_le (by positivity) hlow
  have hfin : 1 / (((σ + n) ^ 2 + |t| ^ 2) * |t| ^ m)
      = (1 / |t| ^ m) * (1 / ((σ + n) ^ 2 + |t| ^ 2)) := by
    rw [one_div, mul_inv, one_div, one_div]
    ring
  rw [norm_inv, norm_pow, inv_eq_one_div]
  exact hstep.trans (le_of_eq hfin)

/-- **The sharp vertical polygamma bound.**  The whole excess power of the height comes out of the
series, leaving the arctan telescope; the constant is independent of the abscissa. -/
theorem norm_iteratedDeriv_succ_digamma_vertical_sharp {σ t : ℝ} (hσ : 0 < σ) (ht : t ≠ 0) (m : ℕ) :
    ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ((m + 1).factorial : ℝ) * ((1 / |t| ^ m) * (1 / |t| ^ 2 + Real.pi / (2 * |t|))) := by
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hsum := hasSum_polygamma_series hσ t m
  have hfactpos : (0 : ℝ) < ((m + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m + 1)
  -- the series is bounded termwise by the trigamma sum with the excess power extracted
  have hpartial : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, ‖(((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹‖
        ≤ (1 / |t| ^ m) * (1 / |t| ^ 2 + Real.pi / (2 * |t|)) := by
    intro N
    have hterm : ∑ n ∈ Finset.range N,
        ‖(((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹‖
          ≤ ∑ n ∈ Finset.range N, (1 / |t| ^ m) * (1 / ((σ + n) ^ 2 + |t| ^ 2)) :=
      Finset.sum_le_sum fun n _ => norm_polygamma_term_le ht m n
    have hpull : ∑ n ∈ Finset.range N, (1 / |t| ^ m) * (1 / ((σ + n) ^ 2 + |t| ^ 2))
        = (1 / |t| ^ m) * ∑ n ∈ Finset.range N, 1 / ((σ + n) ^ 2 + |t| ^ 2) := by
      rw [Finset.mul_sum]
    have harctan : ∑ n ∈ Finset.range N, 1 / ((σ + n) ^ 2 + |t| ^ 2)
        ≤ 1 / |t| ^ 2 + Real.pi / (2 * |t|) := RHTower.sum_inv_sq_add_le hσ.le htpos N
    calc ∑ n ∈ Finset.range N, ‖(((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹‖
        ≤ ∑ n ∈ Finset.range N, (1 / |t| ^ m) * (1 / ((σ + n) ^ 2 + |t| ^ 2)) := hterm
      _ = (1 / |t| ^ m) * ∑ n ∈ Finset.range N, 1 / ((σ + n) ^ 2 + |t| ^ 2) := hpull
      _ ≤ (1 / |t| ^ m) * (1 / |t| ^ 2 + Real.pi / (2 * |t|)) :=
          mul_le_mul_of_nonneg_left harctan (by positivity)
  have htsum : ∑' n : ℕ, ‖(((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹‖
      ≤ (1 / |t| ^ m) * (1 / |t| ^ 2 + Real.pi / (2 * |t|)) :=
    Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) hpartial
  have hnormtsum : ‖(-1 : ℂ) ^ m / ((m + 1).factorial : ℂ)
        * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ∑' n : ℕ, ‖(((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹‖ := by
    rw [← hsum.tsum_eq]
    exact norm_tsum_le_tsum_norm hsum.summable.norm
  have hleft : ‖(-1 : ℂ) ^ m / ((m + 1).factorial : ℂ)
        * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        / ((m + 1).factorial : ℝ) := by
    rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow]
    simp only [Complex.norm_natCast, div_eq_mul_inv, one_mul]
    ring
  rw [hleft] at hnormtsum
  have := hnormtsum.trans htsum
  rw [div_le_iff₀ hfactpos] at this
  calc ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (1 / |t| ^ m) * (1 / |t| ^ 2 + Real.pi / (2 * |t|)) * ((m + 1).factorial : ℝ) := this
    _ = ((m + 1).factorial : ℝ) * ((1 / |t| ^ m) * (1 / |t| ^ 2 + Real.pi / (2 * |t|))) := by ring

/-- **The sharp vertical polygamma order.**  Past unit height the order-`m+1` jet is bounded by the
exact power `|t|^{-(m+1)}` with an absolute constant. -/
theorem norm_iteratedDeriv_succ_digamma_vertical_pow {σ t : ℝ} (hσ : 0 < σ) (ht : 1 ≤ |t|) (m : ℕ) :
    ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ((m + 1).factorial : ℝ) * (1 + Real.pi / 2) / |t| ^ (m + 1) := by
  have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le one_pos ht
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
    linarith
  have hbase := norm_iteratedDeriv_succ_digamma_vertical_sharp hσ ht0 m
  have hsq : 1 / |t| ^ 2 ≤ 1 / |t| := by
    apply one_div_le_one_div_of_le htpos
    nlinarith
  have hstep : 1 / |t| ^ 2 + Real.pi / (2 * |t|) ≤ (1 + Real.pi / 2) / |t| := by
    have hpi : Real.pi / (2 * |t|) = Real.pi / 2 / |t| := (div_div Real.pi 2 |t|).symm
    have hsplit : (1 + Real.pi / 2) / |t| = 1 / |t| + Real.pi / 2 / |t| := add_div 1 _ _
    rw [hpi, hsplit]
    linarith [hsq]
  have hcomb : (1 / |t| ^ m) * (1 / |t| ^ 2 + Real.pi / (2 * |t|))
      ≤ (1 + Real.pi / 2) / |t| ^ (m + 1) := by
    have hpos : (0 : ℝ) ≤ 1 / |t| ^ m := by positivity
    have := mul_le_mul_of_nonneg_left hstep hpos
    refine this.trans (le_of_eq ?_)
    rw [pow_succ]
    field_simp
  have hfactnn : (0 : ℝ) ≤ ((m + 1).factorial : ℝ) := by positivity
  calc ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ((m + 1).factorial : ℝ) * ((1 / |t| ^ m) * (1 / |t| ^ 2 + Real.pi / (2 * |t|))) := hbase
    _ ≤ ((m + 1).factorial : ℝ) * ((1 + Real.pi / 2) / |t| ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left hcomb hfactnn
    _ = ((m + 1).factorial : ℝ) * (1 + Real.pi / 2) / |t| ^ (m + 1) := by ring

end GaloisForLFunctions

import GaloisForLFunctions.RHTower.Sieve.PrimeSieveAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.GhsStepFour

/-!
# The vertical Perron integral of a prime-supported series

Assembling the sharp Perron kernel with the prime-sieve mean square: the modulus of the Perron
integrand factors as `‖D(σ+it)‖·x^σ/‖σ+it‖`, the second factor is at most `x^σ/t`, and the first has an
affine mean square.  The dyadic height split then gives

`∫_{t₀}^{t₀2^M} ‖D(σ+it)·x^{σ+it}/(σ+it)‖ dt
   ≤ x^σ·√(sieveMeanSquareConst)·√2(1 − √2/2)⁻¹/√t₀ + 2x^σ·√(sieveMeanSquareRate)·M`

for a series supported on primes in a finite set.  The first term is independent of the height of the
range; the second grows only with the *number* of dyadic blocks.

This is the analytic half of a Halász-type mean value estimate in the shape the truncated Perron
formula consumes: the sieve constants are the only arithmetic input, and both are sums over the support
with no divisor function and no short-interval count.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The modulus of the Perron integrand factors into the modulus of the Dirichlet series and the
modulus of the kernel. -/
theorem norm_perron_integrand {x : ℝ} (hx : 0 < x) (D : ℂ) (σ t : ℝ) :
    ‖D * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      = ‖D‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖) := by
  have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
  rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]

/-- The modulus of the Perron kernel is continuous on a line with positive abscissa. -/
theorem continuous_perron_kernel_norm {x σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖) := by
  have hden : ∀ t : ℝ, ‖(σ : ℂ) + (t : ℝ) * I‖ ≠ 0 := by
    intro t h
    rw [norm_eq_zero] at h
    have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    exact absurd hre.symm (ne_of_gt hσ)
  exact continuous_const.div (by fun_prop) hden

/-- The Perron kernel decays like `x^σ/t` in the height. -/
theorem perron_kernel_norm_le {x σ : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 < t) :
    x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ≤ x ^ σ / t := by
  refine div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le σ) ht ?_
  have him : ((σ : ℂ) + (t : ℝ) * I).im = t := by simp
  calc t = |((σ : ℂ) + (t : ℝ) * I).im| := by rw [him, abs_of_pos ht]
    _ ≤ ‖(σ : ℂ) + (t : ℝ) * I‖ := Complex.abs_im_le_norm _

/-- **The vertical Perron integral of a prime-supported series.**  The dyadic height split against the
sharp Perron kernel, with the prime-sieve mean square supplying the block moments. -/
theorem integral_norm_perron_integrand_le {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (hprime : ∀ n ∈ s, a n ≠ 0 → n.Prime)
    {σ x t₀ : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) (M : ℕ) :
    (∫ t in t₀..(t₀ * 2 ^ M),
        ‖LSeries a ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ (x ^ σ * Real.sqrt (sieveMeanSquareConst a s σ Y) * Real.sqrt 2 / Real.sqrt t₀)
            * (1 - Real.sqrt 2 / 2)⁻¹
          + 2 * x ^ σ * Real.sqrt (sieveMeanSquareRate a s σ z Y) * M := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hD : Continuous fun t : ℝ => LSeries a ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hs0 hsupp σ
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ‖LSeries a ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖))
    (fun t _ => norm_perron_integrand hx _ σ t)]
  refine GaloisForLFunctions.HTGeometry.integral_norm_mul_kernel_le_of_affine_meanSquare hD
    (continuous_perron_kernel_norm hσ)
    (sieveMeanSquareConst_nonneg a s σ hlog) (sieveMeanSquareRate_nonneg a s σ hz hlog)
    (Real.rpow_nonneg hx.le σ) ht₀0 (fun U hU => ?_) M (fun t ht _ => ?_)
  · exact integral_Icc_normSq_LSeries_le_affine hs0 hsupp hprime σ (by linarith) z Y hY hYz hz hlog
  · exact perron_kernel_norm_le hx (lt_of_lt_of_le ht₀0 ht)

end RHTower.Sieve
end

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The modulus of the Perron kernel is even in the height. -/
theorem perron_kernel_norm_neg (x σ t : ℝ) :
    x ^ σ / ‖(σ : ℂ) + ((-t : ℝ) : ℂ) * I‖ = x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ := by
  rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I]
  congr 2
  ring

/-- On the whole line the Perron kernel is at most `x^σ/σ`. -/
theorem perron_kernel_norm_le_const {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) (t : ℝ) :
    x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ≤ x ^ σ / σ := by
  refine div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le σ) hσ ?_
  have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
  calc σ = |((σ : ℂ) + (t : ℝ) * I).re| := by rw [hre, abs_of_pos hσ]
    _ ≤ ‖(σ : ℂ) + (t : ℝ) * I‖ := Complex.abs_re_le_norm _

/-- **The vertical Perron integral of a prime-supported series over a symmetric range.**  Both flanks
carry the dyadic bound — the negative one because the kernel is even and the mean square reflection
invariant — and the low range `|t| ≤ t₀` carries the bounded-kernel term.  Only the block count `M`
depends on the height of the truncation. -/
theorem integral_symm_norm_perron_integrand_le {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (hprime : ∀ n ∈ s, a n ≠ 0 → n.Prime)
    {σ x t₀ : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) (M : ℕ) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries a ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ 2 * ((x ^ σ * Real.sqrt (sieveMeanSquareConst a s σ Y) * Real.sqrt 2 / Real.sqrt t₀)
                * (1 - Real.sqrt 2 / 2)⁻¹
              + 2 * x ^ σ * Real.sqrt (sieveMeanSquareRate a s σ z Y) * M)
          + (x ^ σ / σ) * (Real.sqrt (2 * t₀)
              * Real.sqrt (sieveMeanSquareConst a s σ Y + sieveMeanSquareRate a s σ z Y * t₀)) := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hD : Continuous fun t : ℝ => LSeries a ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hs0 hsupp σ
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ‖LSeries a ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖))
    (fun t _ => norm_perron_integrand hx _ σ t)]
  refine GaloisForLFunctions.HTGeometry.integral_symm_norm_mul_kernel_le hD
    (continuous_perron_kernel_norm hσ) (fun t => perron_kernel_norm_neg x σ t)
    (Real.rpow_nonneg hx.le σ) (by positivity)
    (sieveMeanSquareConst_nonneg a s σ hlog) (sieveMeanSquareRate_nonneg a s σ hz hlog) ht₀0
    (fun t _ => perron_kernel_norm_le_const hx hσ t) (fun U hU => ?_) M (fun t ht _ => ?_)
  · exact integral_Icc_normSq_LSeries_le_affine hs0 hsupp hprime σ (by linarith) z Y hY hYz hz hlog
  · exact perron_kernel_norm_le hx (lt_of_lt_of_le ht₀0 ht)

end RHTower.Sieve
end

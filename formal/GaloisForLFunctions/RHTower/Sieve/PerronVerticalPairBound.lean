import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.PerronVerticalTripleBound

/-!
# The vertical Perron integral of a pair, one factor by its mean square

Grouping the Perron integrand of a threefold convolution as `L(c,s)·L(g,s)·x^s/s` with `c = A ⍟ B`
charges the two outer factors *together* through a single mean square instead of splitting them by
Cauchy–Schwarz.  The gain is arithmetic rather than analytic: the mean square of a product of two prime
weights carries the `n`-weighted mass of the *convolution*,

`∑_{n} n‖(A ⍟ B)_n n^{−σ}‖² = (∑_p p‖A_p p^{−σ}‖²)·(∑_q q‖B_q q^{−σ}‖²)/…`,

which is a product of two convergent prime sums rather than a product of two mean squares each of which
already contains a factor `(log)²`.  The estimate itself needs nothing but the affine mean square of the
first factor and a pointwise bound on the second:

`∫_{|t| ≤ t₀2^M} ‖L(c)L(g)x^s/s‖ ≤ 2((Vx^σ√Q√2/√t₀)(1−√2/2)⁻¹ + 2Vx^σ√κM) + (Vx^σ/σ)√(2t₀)√(Q+κt₀)`.

The majorant kernel `V·x^σ/‖s‖` is even, which is what lets both flanks be read from one bound.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The modulus of the pair Perron integrand, grouped as one Dirichlet polynomial against a kernel
carrying the second factor. -/
theorem norm_perron_pair_integrand {x : ℝ} (hx : 0 < x) (a b : ℂ) (σ t : ℝ) :
    ‖a * b * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      = ‖a‖ * (‖b‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)) := by
  have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
  rw [norm_mul, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
  ring

/-- The analytic bound for the vertical integral of a pair Perron integrand over a symmetric dyadic
range, in terms of the affine mean square `Q + κU` of the first factor. -/
def perronVerticalPairBound (σ x t₀ V Q κ : ℝ) (M : ℕ) : ℝ :=
  2 * ((V * x ^ σ * Real.sqrt Q * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹
        + 2 * (V * x ^ σ) * Real.sqrt κ * M)
    + (V * x ^ σ / σ) * (Real.sqrt (2 * t₀) * Real.sqrt (Q + κ * t₀))

/-- **The vertical Perron integral of a pair over a symmetric range.**  The first factor enters through
an affine mean square, the second through a pointwise bound on the range of integration. -/
theorem integral_symm_norm_perron_pair_le {c g : ℕ → ℂ} {sc : Finset ℕ}
    (hc0 : 0 ∉ sc) (hcsupp : ∀ n : ℕ, c n ≠ 0 → n ∈ sc)
    {σ x t₀ V Q κ : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V)
    (hQ : 0 ≤ Q) (hκ : 0 ≤ κ)
    (hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I))
    (hms : ∀ U : ℝ, 1 ≤ U →
      (∫ y in Set.Icc (-U) U, ‖LSeries c ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2) ≤ Q + κ * U)
    (M : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ M → ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ perronVerticalPairBound σ x t₀ V Q κ M := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hone : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
  have hb : t₀ ≤ t₀ * 2 ^ M := by nlinarith [ht₀0.le]
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hDc : Continuous fun t : ℝ => LSeries c ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hc0 hcsupp σ
  have hKc : Continuous fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ :=
    continuous_perron_kernel_norm hσ
  have hGc : Continuous fun t : ℝ => V * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖) :=
    continuous_const.mul hKc
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ‖LSeries c ((σ : ℂ) + (t : ℝ) * I)‖
        * (‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)))
    (fun t _ => norm_perron_pair_integrand hx _ _ σ t)]
  -- majorise the second factor by its pointwise bound, giving an even kernel
  have hmono : (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries c ((σ : ℂ) + (t : ℝ) * I)‖
          * (‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)))
      ≤ ∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries c ((σ : ℂ) + (t : ℝ) * I)‖ * (V * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)) := by
    refine intervalIntegral.integral_mono_on (by linarith)
      ((hDc.norm.mul (hgc.norm.mul hKc)).intervalIntegrable _ _)
      ((hDc.norm.mul hGc).intervalIntegrable _ _) ?_
    intro t ht
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (hgV t (abs_le.2 ⟨ht.1, ht.2⟩)) (by positivity)
  refine le_trans hmono ?_
  rw [perronVerticalPairBound]
  refine GaloisForLFunctions.HTGeometry.integral_symm_norm_mul_kernel_le hDc hGc ?_
    (by positivity) (by positivity) hQ hκ ht₀0 ?_ (fun U hU => hms U (by linarith)) M ?_
  · intro t
    rw [perron_kernel_norm_neg x σ t]
  · intro t _
    calc V * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖) ≤ V * (x ^ σ / σ) :=
          mul_le_mul_of_nonneg_left (perron_kernel_norm_le_const hx hσ t) hV
      _ = V * x ^ σ / σ := by ring
  · intro t ht _
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ht₀0 ht
    calc V * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖) ≤ V * (x ^ σ / t) :=
          mul_le_mul_of_nonneg_left (perron_kernel_norm_le hx ht0) hV
      _ = V * x ^ σ / t := by ring

/-- **The vertical Perron integral of a pair, at the general affine mean square.**  No primality and no
sieve: the first factor may be any finitely supported sequence. -/
theorem integral_symm_norm_perron_pair_general_le {c g : ℕ → ℂ} {sc : Finset ℕ}
    (hc0 : 0 ∉ sc) (hcsupp : ∀ n : ℕ, c n ≠ 0 → n ∈ sc)
    {σ x t₀ V : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V)
    (hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I)) (M : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ M → ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ perronVerticalPairBound σ x t₀ V (generalMeanSquareConst c sc σ)
          (generalMeanSquareRate c sc σ) M :=
  integral_symm_norm_perron_pair_le hc0 hcsupp hσ hx ht₀ hV
    (generalMeanSquareConst_nonneg c sc σ) (generalMeanSquareRate_nonneg c sc σ) hgc
    (fun _ hU => integral_Icc_normSq_LSeries_le_general_affine hc0 hcsupp σ hU) M hgV

end RHTower.Sieve
end

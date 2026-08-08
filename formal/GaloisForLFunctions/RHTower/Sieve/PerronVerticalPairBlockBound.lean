import GaloisForLFunctions.RHTower.Sieve.PerronVerticalPairBound
import GaloisForLFunctions.HTGeometry.VerticalKernelBlockConstants

/-!
# The vertical Perron integral of a pair, with the second factor charged block by block

A single pointwise bound `V` on the second factor throws away everything the arithmetic of that factor
knows about the *height*.  The dyadic split has room for more: it charges the kernel once per block, so
it can charge the second factor its block maximum `V_m` instead of its maximum over the whole range,

`∫_{|t| ≤ t₀2^M} ‖L(c)L(g)x^s/s‖
    ≤ 2·∑_{m < M} V_m x^σ((√Q√2/√t₀)(√2/2)^m + 2√κ) + (V₀x^σ/σ)√(2t₀)√(Q + κt₀)`.

Nothing is lost when `V_m` is constant — the two geometric sums are `(1 − √2/2)⁻¹` and `M` — and a `V_m`
that decays in `m` beats the constant bound by the whole weighted sum.  This is the shape Halász's
`(1 + m)e^{−m}` lives in: the multiplicative distance of `f` from the characters grows with the height,
so `V_m` decays, and the weighted sum of a decaying `V_m` converges where `M·max V` does not.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- On the whole line the Perron kernel is at most `x^σ/|t|`. -/
theorem perron_kernel_norm_le_abs {x σ : ℝ} (hx : 0 < x) {t : ℝ} (ht : t ≠ 0) :
    x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ≤ x ^ σ / |t| := by
  refine div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le σ) (abs_pos.2 ht) ?_
  have him : ((σ : ℂ) + (t : ℝ) * I).im = t := by simp
  calc |t| = |((σ : ℂ) + (t : ℝ) * I).im| := by rw [him]
    _ ≤ ‖(σ : ℂ) + (t : ℝ) * I‖ := Complex.abs_im_le_norm _

/-- The analytic bound for the vertical integral of a pair Perron integrand with the second factor
charged its block maxima. -/
def perronVerticalPairBlockBound (σ x t₀ V₀ Q κ : ℝ) (V : ℕ → ℝ) (M : ℕ) : ℝ :=
  2 * (∑ m ∈ Finset.range M, (V m * x ^ σ)
        * ((Real.sqrt Q * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m
            + 2 * Real.sqrt κ))
    + (V₀ * x ^ σ / σ) * (Real.sqrt (2 * t₀) * Real.sqrt (Q + κ * t₀))

/-- **The vertical Perron integral of a pair, with the second factor charged block by block.**  The
first factor enters through an affine mean square, the second through one pointwise bound per dyadic
block and one on the low range. -/
theorem integral_symm_norm_perron_pair_block_le {c g : ℕ → ℂ} {sc : Finset ℕ}
    (hc0 : 0 ∉ sc) (hcsupp : ∀ n : ℕ, c n ≠ 0 → n ∈ sc)
    {σ x t₀ V₀ Q κ : ℝ} {V : ℕ → ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀)
    (hV : ∀ m, 0 ≤ V m) (hV₀ : 0 ≤ V₀) (hQ : 0 ≤ Q) (hκ : 0 ≤ κ)
    (hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I))
    (hms : ∀ U : ℝ, 1 ≤ U →
      (∫ y in Set.Icc (-U) U, ‖LSeries c ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2) ≤ Q + κ * U)
    (M : ℕ)
    (hgV : ∀ m, m < M → ∀ t : ℝ, t₀ * 2 ^ m ≤ |t| → |t| ≤ t₀ * 2 ^ (m + 1) →
      ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V m)
    (hgV₀ : ∀ t : ℝ, |t| ≤ t₀ → ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V₀) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ perronVerticalPairBlockBound σ x t₀ V₀ Q κ V M := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hDc : Continuous fun t : ℝ => LSeries c ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hc0 hcsupp σ
  have hKc : Continuous fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ :=
    continuous_perron_kernel_norm hσ
  have hGc : Continuous fun t : ℝ =>
      ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖) := hgc.norm.mul hKc
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ‖LSeries c ((σ : ℂ) + (t : ℝ) * I)‖
        * (‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)))
    (fun t _ => norm_perron_pair_integrand hx _ _ σ t)]
  rw [perronVerticalPairBlockBound]
  refine GaloisForLFunctions.HTGeometry.integral_symm_norm_mul_kernel_var_le hDc hGc
    (fun m => mul_nonneg (hV m) hxσ) (div_nonneg (mul_nonneg hV₀ hxσ) hσ.le) hQ hκ ht₀0 ?_
    (fun U hU => hms U (by linarith)) M ?_
  · intro t ht
    calc ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)
        ≤ V₀ * (x ^ σ / σ) :=
          mul_le_mul (hgV₀ t ht) (perron_kernel_norm_le_const hx hσ t) (by positivity) hV₀
      _ = V₀ * x ^ σ / σ := by ring
  · intro m hm t ht htop
    have hblockpos : (0 : ℝ) < t₀ * 2 ^ m := by positivity
    have habs : (0 : ℝ) < |t| := lt_of_lt_of_le hblockpos ht
    have htne : t ≠ 0 := by
      intro h
      rw [h, abs_zero] at habs
      exact absurd habs (lt_irrefl 0)
    calc ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)
        ≤ V m * (x ^ σ / |t|) :=
          mul_le_mul (hgV m hm t ht htop) (perron_kernel_norm_le_abs hx htne)
            (by positivity) (hV m)
      _ = V m * x ^ σ / |t| := by ring

end RHTower.Sieve
end

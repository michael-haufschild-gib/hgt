import GaloisForLFunctions.RHTower.Sieve.PerronVerticalPrimeBound
import GaloisForLFunctions.RHTower.Sieve.EulerBoundLSeries

/-!
# The vertical Perron integral of a triple product

The integrand of the Perron step for a threefold convolution is `L(A,s)L(B,s)L(f,s)·x^s/s`.  Its
modulus factors as `(‖L(A)‖·‖L(B)‖)·(‖L(f)‖·x^σ/‖s‖)`, so with a pointwise bound `V` on the third factor
the second group is a kernel bounded by `V x^σ/t`, and the first group is a product of two Dirichlet
polynomials whose block moments come from two affine mean squares.  The dyadic height split then gives

`∫ ‖L(A)L(B)L(f)x^s/s‖ ≤ 2Vx^σ√(Q_AQ_B)/t₀ + Vx^σ(√(Q_Aκ_B)+√(κ_AQ_B))√2(1−√2/2)⁻¹/√t₀
                            + 2Vx^σ√(κ_Aκ_B)M`.

The two prime weights enter only through the sieve constants; the third factor enters only through its
size on the line.  For a bounded multiplicative `f` that size is the Euler bound
`(1 + 1/(σ−1))e^{7/2}`, which makes the estimate free of hypotheses beyond boundedness and
multiplicativity — and it is exactly the place where a distance saving would replace the trivial size.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The modulus of the triple Perron integrand, grouped as a product of two Dirichlet polynomials
against a kernel carrying the third factor. -/
theorem norm_perron_triple_integrand {x : ℝ} (hx : 0 < x) (a b f : ℂ) (σ t : ℝ) :
    ‖a * b * f * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      = (‖a‖ * ‖b‖) * (‖f‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)) := by
  have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
  rw [norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
  ring

/-- The analytic bound for the vertical integral of a triple Perron integrand over a dyadic range. -/
def perronVerticalProductBound (A B : ℕ → ℂ) (sA sB : Finset ℕ) (σ x t₀ V : ℝ)
    (zA YA zB YB : ℕ) (M : ℕ) : ℝ :=
  2 * (V * x ^ σ * (Real.sqrt (sieveMeanSquareConst A sA σ YA)
          * Real.sqrt (sieveMeanSquareConst B sB σ YB)) / t₀)
    + (V * x ^ σ * (Real.sqrt (sieveMeanSquareConst A sA σ YA)
              * Real.sqrt (sieveMeanSquareRate B sB σ zB YB)
            + Real.sqrt (sieveMeanSquareRate A sA σ zA YA)
              * Real.sqrt (sieveMeanSquareConst B sB σ YB))
        * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹
    + 2 * (V * x ^ σ) * (Real.sqrt (sieveMeanSquareRate A sA σ zA YA)
        * Real.sqrt (sieveMeanSquareRate B sB σ zB YB)) * M

/-- **The vertical Perron integral of a triple product.**  Two prime-supported factors through the
sieve, and the third factor through a pointwise bound on the line. -/
theorem integral_norm_perron_triple_le {A B f : ℕ → ℂ} {sA sB : Finset ℕ}
    (hA0 : 0 ∉ sA) (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ sA)
    (hAprime : ∀ n ∈ sA, A n ≠ 0 → n.Prime)
    (hB0 : 0 ∉ sB) (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ sB)
    (hBprime : ∀ n ∈ sB, B n ≠ 0 → n.Prime)
    {σ x t₀ V : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V)
    (hFc : Continuous fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℝ) * I))
    (hFbound : ∀ t : ℝ, ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (M : ℕ) :
    (∫ t in t₀..(t₀ * 2 ^ M),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries f ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ perronVerticalProductBound A B sA sB σ x t₀ V zA YA zB YB M := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hAc : Continuous fun t : ℝ => LSeries A ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hA0 hAsupp σ
  have hBc : Continuous fun t : ℝ => LSeries B ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hB0 hBsupp σ
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      (‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ * ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖)
        * (‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)))
    (fun t _ => norm_perron_triple_integrand hx _ _ _ σ t)]
  rw [perronVerticalProductBound]
  refine GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_mul_kernel_le hAc hBc
    (hFc.norm.mul (continuous_perron_kernel_norm hσ))
    (sieveMeanSquareConst_nonneg A sA σ hlogA) (sieveMeanSquareRate_nonneg A sA σ hzA hlogA)
    (sieveMeanSquareConst_nonneg B sB σ hlogB) (sieveMeanSquareRate_nonneg B sB σ hzB hlogB)
    (by positivity) ht₀0 (fun U hU => ?_) (fun U hU => ?_) (fun t ht => ?_) M
  · exact integral_Icc_normSq_LSeries_le_affine hA0 hAsupp hAprime σ (by linarith) zA YA hYA hYzA
      hzA hlogA
  · exact integral_Icc_normSq_LSeries_le_affine hB0 hBsupp hBprime σ (by linarith) zB YB hYB hYzB
      hzB hlogB
  · have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ht₀0 ht
    calc ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)
        ≤ V * (x ^ σ / t) := by
          refine mul_le_mul (hFbound t) (perron_kernel_norm_le hx ht0) (by positivity) hV
      _ = V * x ^ σ / t := by ring

/-- **The triple product with the third factor at its Euler size.**  For a bounded multiplicative `f`
the pointwise input is the corpus's trivial bound `(1 + 1/(σ−1))e^{7/2}`, so the estimate needs no
hypothesis on `f` beyond boundedness and multiplicativity on coprimes. -/
theorem integral_norm_perron_triple_euler_le {A B f : ℕ → ℂ} {sA sB : Finset ℕ}
    (hA0 : 0 ∉ sA) (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ sA)
    (hAprime : ∀ n ∈ sA, A n ≠ 0 → n.Prime)
    (hB0 : 0 ∉ sB) (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ sB)
    (hBprime : ∀ n ∈ sB, B n ≠ 0 → n.Prime)
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {σ x t₀ : ℝ} (hσ : 1 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (M : ℕ) :
    (∫ t in t₀..(t₀ * 2 ^ M),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries f ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ perronVerticalProductBound A B sA sB σ x t₀
          ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) zA YA zB YB M := by
  have hVnn : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by
    have h1 : (0 : ℝ) < σ - 1 := by linarith
    positivity
  exact integral_norm_perron_triple_le hA0 hAsupp hAprime hB0 hBsupp hBprime (by linarith) hx ht₀
    hVnn (continuous_LSeries_line_of_bounded hbdd hσ)
    (fun t => norm_LSeries_line_le_trivial hf1 hmul hbdd hσ t)
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB M

end RHTower.Sieve
end

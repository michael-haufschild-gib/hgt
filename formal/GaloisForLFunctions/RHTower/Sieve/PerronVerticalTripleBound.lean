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
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (M : ℕ)
    (hFbound : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ M → ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
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
    (by positivity) ht₀0 (fun U hU => ?_) (fun U hU => ?_) M (fun t ht htop => ?_)
  · exact integral_Icc_normSq_LSeries_le_affine hA0 hAsupp hAprime σ (by linarith) zA YA hYA hYzA
      hzA hlogA
  · exact integral_Icc_normSq_LSeries_le_affine hB0 hBsupp hBprime σ (by linarith) zB YB hYB hYzB
      hzB hlogB
  · have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ht₀0 ht
    have habs : |t| ≤ t₀ * 2 ^ M := by rw [abs_of_pos ht0]; exact htop
    calc ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)
        ≤ V * (x ^ σ / t) := by
          refine mul_le_mul (hFbound t habs) (perron_kernel_norm_le hx ht0) (by positivity) hV
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
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB M
    (fun t _ => norm_LSeries_line_le_trivial hf1 hmul hbdd hσ t)

end RHTower.Sieve
end

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The triple Perron integral over a symmetric range.**  The flank splitting with the negative side
read through the reflection: the kernel is even, the mean squares are reflection invariant, and the
pointwise bound on the third factor holds on the whole line, so both flanks carry the same bound and the
low range `|t| ≤ t₀` carries the bounded-kernel term. -/
theorem integral_symm_norm_perron_triple_le {A B f : ℕ → ℂ} {sA sB : Finset ℕ}
    (hA0 : 0 ∉ sA) (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ sA)
    (hAprime : ∀ n ∈ sA, A n ≠ 0 → n.Prime)
    (hB0 : 0 ∉ sB) (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ sB)
    (hBprime : ∀ n ∈ sB, B n ≠ 0 → n.Prime)
    {σ x t₀ V : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V)
    (hFc : Continuous fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℝ) * I))
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (M : ℕ)
    (hFbound : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ M → ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries f ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ 2 * perronVerticalProductBound A B sA sB σ x t₀ V zA YA zB YB M
          + (V * x ^ σ / σ)
              * (Real.sqrt (sieveMeanSquareConst A sA σ YA
                    + sieveMeanSquareRate A sA σ zA YA * t₀)
                  * Real.sqrt (sieveMeanSquareConst B sB σ YB
                    + sieveMeanSquareRate B sB σ zB YB * t₀)) := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hAc : Continuous fun t : ℝ => LSeries A ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hA0 hAsupp σ
  have hBc : Continuous fun t : ℝ => LSeries B ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hB0 hBsupp σ
  set FA : ℝ → ℂ := fun t => LSeries A ((σ : ℂ) + (t : ℝ) * I) with hFA
  set FB : ℝ → ℂ := fun t => LSeries B ((σ : ℂ) + (t : ℝ) * I) with hFB
  set G : ℝ → ℝ := fun t =>
    ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖) with hG
  have hGc : Continuous G := hFc.norm.mul (continuous_perron_kernel_norm hσ)
  have hFprod : Continuous fun t : ℝ => ‖FA t‖ * ‖FB t‖ := hAc.norm.mul hBc.norm
  -- the kernel bound on either flank
  have hGle : ∀ t : ℝ, 0 < t → t ≤ t₀ * 2 ^ M → G t ≤ V * x ^ σ / t := by
    intro t ht htop
    have habs : |t| ≤ t₀ * 2 ^ M := by rw [abs_of_pos ht]; exact htop
    calc G t ≤ V * (x ^ σ / t) := by
          refine mul_le_mul (hFbound t habs) (perron_kernel_norm_le hx ht) (by positivity) hV
      _ = V * x ^ σ / t := by ring
  have hGleneg : ∀ t : ℝ, 0 < t → t ≤ t₀ * 2 ^ M → G (-t) ≤ V * x ^ σ / t := by
    intro t ht htop
    have habs : |(-t)| ≤ t₀ * 2 ^ M := by rw [abs_neg, abs_of_pos ht]; exact htop
    have hker : x ^ σ / ‖(σ : ℂ) + ((-t : ℝ) : ℂ) * I‖ ≤ x ^ σ / t := by
      rw [perron_kernel_norm_neg x σ t]
      exact perron_kernel_norm_le hx ht
    calc G (-t) ≤ V * (x ^ σ / t) := by
          refine mul_le_mul (hFbound (-t) habs) hker (by positivity) hV
      _ = V * x ^ σ / t := by ring
  -- both flanks
  have hpos : (∫ t in t₀..(t₀ * 2 ^ M), (‖FA t‖ * ‖FB t‖) * G t)
      ≤ perronVerticalProductBound A B sA sB σ x t₀ V zA YA zB YB M := by
    rw [perronVerticalProductBound]
    refine GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_mul_kernel_le hAc hBc hGc
      (sieveMeanSquareConst_nonneg A sA σ hlogA) (sieveMeanSquareRate_nonneg A sA σ hzA hlogA)
      (sieveMeanSquareConst_nonneg B sB σ hlogB) (sieveMeanSquareRate_nonneg B sB σ hzB hlogB)
      (by positivity) ht₀0 (fun U hU => ?_) (fun U hU => ?_) M
      (fun t ht htop => hGle t (by linarith) htop)
    · exact integral_Icc_normSq_LSeries_le_affine hA0 hAsupp hAprime σ (by linarith) zA YA hYA
        hYzA hzA hlogA
    · exact integral_Icc_normSq_LSeries_le_affine hB0 hBsupp hBprime σ (by linarith) zB YB hYB
        hYzB hzB hlogB
  have hneg : (∫ t in t₀..(t₀ * 2 ^ M),
        (‖FA (-t)‖ * ‖FB (-t)‖) * G (-t))
      ≤ perronVerticalProductBound A B sA sB σ x t₀ V zA YA zB YB M := by
    rw [perronVerticalProductBound]
    refine GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_mul_kernel_le
      (A := fun t => FA (-t)) (B := fun t => FB (-t)) (G := fun t => G (-t))
      (hAc.comp continuous_neg) (hBc.comp continuous_neg) (hGc.comp continuous_neg)
      (sieveMeanSquareConst_nonneg A sA σ hlogA) (sieveMeanSquareRate_nonneg A sA σ hzA hlogA)
      (sieveMeanSquareConst_nonneg B sB σ hlogB) (sieveMeanSquareRate_nonneg B sB σ hzB hlogB)
      (by positivity) ht₀0 (fun U hU => ?_) (fun U hU => ?_) M
      (fun t ht htop => hGleneg t (by linarith) htop)
    · rw [GaloisForLFunctions.HTGeometry.integral_Icc_normSq_comp_neg FA (by linarith)]
      exact integral_Icc_normSq_LSeries_le_affine hA0 hAsupp hAprime σ (by linarith) zA YA hYA
        hYzA hzA hlogA
    · rw [GaloisForLFunctions.HTGeometry.integral_Icc_normSq_comp_neg FB (by linarith)]
      exact integral_Icc_normSq_LSeries_le_affine hB0 hBsupp hBprime σ (by linarith) zB YB hYB
        hYzB hzB hlogB
  -- the low range
  have hlow : (∫ t in (-t₀)..t₀, (‖FA t‖ * ‖FB t‖) * G t)
      ≤ (V * x ^ σ / σ)
          * (Real.sqrt (sieveMeanSquareConst A sA σ YA + sieveMeanSquareRate A sA σ zA YA * t₀)
              * Real.sqrt (sieveMeanSquareConst B sB σ YB
                + sieveMeanSquareRate B sB σ zB YB * t₀)) := by
    refine GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_low_le hAc hBc hGc
      (by positivity) ht₀0 (fun t ht => ?_) ?_ ?_
    · have habs : |t| ≤ t₀ * 2 ^ M := by
        refine le_trans ht ?_
        have h1 : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
        nlinarith [ht₀0.le]
      calc G t ≤ V * (x ^ σ / σ) := by
            refine mul_le_mul (hFbound t habs) (perron_kernel_norm_le_const hx hσ t)
              (by positivity) hV
        _ = V * x ^ σ / σ := by ring
    · exact integral_Icc_normSq_LSeries_le_affine hA0 hAsupp hAprime σ ht₀ zA YA hYA hYzA hzA hlogA
    · exact integral_Icc_normSq_LSeries_le_affine hB0 hBsupp hBprime σ ht₀ zB YB hYB hYzB hzB hlogB
  -- assemble
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => (‖FA t‖ * ‖FB t‖) * G t)
    (fun t _ => norm_perron_triple_integrand hx _ _ _ σ t)]
  exact GaloisForLFunctions.HTGeometry.integral_symm_le_of_flanks hFprod hGc hpos hneg hlow

end RHTower.Sieve
end

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The triple Perron integral with the low range charged pointwise.**  Away from the flanks the
kernel is bounded and the two prime polynomials may be charged their pointwise sizes instead of their
mean squares.  For a prime weight the damped `ℓ¹` mass is smaller than the square root of the
`n`-weighted mass by a logarithm, so on a bounded low range this is the better estimate. -/
theorem integral_symm_norm_perron_triple_l1_low_le {A B f : ℕ → ℂ} {sA sB : Finset ℕ}
    (hA0 : 0 ∉ sA) (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ sA)
    (hAprime : ∀ n ∈ sA, A n ≠ 0 → n.Prime)
    (hB0 : 0 ∉ sB) (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ sB)
    (hBprime : ∀ n ∈ sB, B n ≠ 0 → n.Prime)
    {σ x t₀ V VA VB : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V)
    (hVA : 0 ≤ VA) (hVB : 0 ≤ VB)
    (hFc : Continuous fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℝ) * I))
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (M : ℕ)
    (hFbound : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ M → ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V)
    (hAb : ∀ t : ℝ, |t| ≤ t₀ → ‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ ≤ VA)
    (hBb : ∀ t : ℝ, |t| ≤ t₀ → ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖ ≤ VB) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries f ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ 2 * perronVerticalProductBound A B sA sB σ x t₀ V zA YA zB YB M
          + (2 * t₀) * (VA * VB * (V * x ^ σ / σ)) := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hone : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
  have hAc : Continuous fun t : ℝ => LSeries A ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hA0 hAsupp σ
  have hBc : Continuous fun t : ℝ => LSeries B ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hB0 hBsupp σ
  set FA : ℝ → ℂ := fun t => LSeries A ((σ : ℂ) + (t : ℝ) * I) with hFA
  set FB : ℝ → ℂ := fun t => LSeries B ((σ : ℂ) + (t : ℝ) * I) with hFB
  set G : ℝ → ℝ := fun t =>
    ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖) with hG
  have hGc : Continuous G := hFc.norm.mul (continuous_perron_kernel_norm hσ)
  have hFprod : Continuous fun t : ℝ => ‖FA t‖ * ‖FB t‖ := hAc.norm.mul hBc.norm
  have hG0 : ∀ t, 0 ≤ G t := by
    intro t
    rw [hG]
    have : (0 : ℝ) ≤ x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ := by positivity
    positivity
  have hGle : ∀ t : ℝ, 0 < t → t ≤ t₀ * 2 ^ M → G t ≤ V * x ^ σ / t := by
    intro t ht htop
    have habs : |t| ≤ t₀ * 2 ^ M := by rw [abs_of_pos ht]; exact htop
    calc G t ≤ V * (x ^ σ / t) := by
          refine mul_le_mul (hFbound t habs) (perron_kernel_norm_le hx ht) (by positivity) hV
      _ = V * x ^ σ / t := by ring
  have hGleneg : ∀ t : ℝ, 0 < t → t ≤ t₀ * 2 ^ M → G (-t) ≤ V * x ^ σ / t := by
    intro t ht htop
    have habs : |(-t)| ≤ t₀ * 2 ^ M := by rw [abs_neg, abs_of_pos ht]; exact htop
    have hker : x ^ σ / ‖(σ : ℂ) + ((-t : ℝ) : ℂ) * I‖ ≤ x ^ σ / t := by
      rw [perron_kernel_norm_neg x σ t]
      exact perron_kernel_norm_le hx ht
    calc G (-t) ≤ V * (x ^ σ / t) := by
          refine mul_le_mul (hFbound (-t) habs) hker (by positivity) hV
      _ = V * x ^ σ / t := by ring
  have hpos : (∫ t in t₀..(t₀ * 2 ^ M), (‖FA t‖ * ‖FB t‖) * G t)
      ≤ perronVerticalProductBound A B sA sB σ x t₀ V zA YA zB YB M := by
    rw [perronVerticalProductBound]
    refine GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_mul_kernel_le hAc hBc hGc
      (sieveMeanSquareConst_nonneg A sA σ hlogA) (sieveMeanSquareRate_nonneg A sA σ hzA hlogA)
      (sieveMeanSquareConst_nonneg B sB σ hlogB) (sieveMeanSquareRate_nonneg B sB σ hzB hlogB)
      (by positivity) ht₀0 (fun U hU => ?_) (fun U hU => ?_) M
      (fun t ht htop => hGle t (by linarith) htop)
    · exact integral_Icc_normSq_LSeries_le_affine hA0 hAsupp hAprime σ (by linarith) zA YA hYA
        hYzA hzA hlogA
    · exact integral_Icc_normSq_LSeries_le_affine hB0 hBsupp hBprime σ (by linarith) zB YB hYB
        hYzB hzB hlogB
  have hneg : (∫ t in t₀..(t₀ * 2 ^ M), (‖FA (-t)‖ * ‖FB (-t)‖) * G (-t))
      ≤ perronVerticalProductBound A B sA sB σ x t₀ V zA YA zB YB M := by
    rw [perronVerticalProductBound]
    refine GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_mul_kernel_le
      (A := fun t => FA (-t)) (B := fun t => FB (-t)) (G := fun t => G (-t))
      (hAc.comp continuous_neg) (hBc.comp continuous_neg) (hGc.comp continuous_neg)
      (sieveMeanSquareConst_nonneg A sA σ hlogA) (sieveMeanSquareRate_nonneg A sA σ hzA hlogA)
      (sieveMeanSquareConst_nonneg B sB σ hlogB) (sieveMeanSquareRate_nonneg B sB σ hzB hlogB)
      (by positivity) ht₀0 (fun U hU => ?_) (fun U hU => ?_) M
      (fun t ht htop => hGleneg t (by linarith) htop)
    · rw [GaloisForLFunctions.HTGeometry.integral_Icc_normSq_comp_neg FA (by linarith)]
      exact integral_Icc_normSq_LSeries_le_affine hA0 hAsupp hAprime σ (by linarith) zA YA hYA
        hYzA hzA hlogA
    · rw [GaloisForLFunctions.HTGeometry.integral_Icc_normSq_comp_neg FB (by linarith)]
      exact integral_Icc_normSq_LSeries_le_affine hB0 hBsupp hBprime σ (by linarith) zB YB hYB
        hYzB hzB hlogB
  have hlow : (∫ t in (-t₀)..t₀, (‖FA t‖ * ‖FB t‖) * G t)
      ≤ (2 * t₀) * (VA * VB * (V * x ^ σ / σ)) := by
    refine GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_low_le_pointwise hAc hBc hGc
      ht₀0 hVA hVB hG0 (fun t ht => ?_) (fun t ht => hAb t ht) (fun t ht => hBb t ht)
    have habs : |t| ≤ t₀ * 2 ^ M := by
      refine le_trans ht ?_
      nlinarith [ht₀0.le]
    calc G t ≤ V * (x ^ σ / σ) := by
          refine mul_le_mul (hFbound t habs) (perron_kernel_norm_le_const hx hσ t)
            (by positivity) hV
      _ = V * x ^ σ / σ := by ring
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => (‖FA t‖ * ‖FB t‖) * G t)
    (fun t _ => norm_perron_triple_integrand hx _ _ _ σ t)]
  exact GaloisForLFunctions.HTGeometry.integral_symm_le_of_flanks hFprod hGc hpos hneg hlow

end RHTower.Sieve
end

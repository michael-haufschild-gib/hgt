import GaloisForLFunctions.RHTower.Sieve.DirichletExceptionalSplit
import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly

/-!
# The core inequality of Soundararajan's exposé §4

Once the exceptional set is fixed, the whole of `(36)`–`(40)` is one inequality between named
quantities: a mean-square bound `A₁` for the second factor on the full range (supplied by the mean
value theorem, Lemma 2.4) and a mean-square bound `A₂` for it on the exceptional set (supplied by
Halász–Montgomery, Lemma 2.6, once Lemma 2.5 has bounded the measure) give

```text
        ∫_{|t| ≤ T} ‖F‖²‖G‖²  ≤  V²·A₁ + (sup‖F‖)²·A₂ .
```

`V` is the cancellation threshold `P_j/(log P_j)²` of `(35)` and `sup‖F‖` the trivial bound `P_j`.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- **The §4 product bound.** -/
theorem section4_product_bound (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    {T V Bf A₁ A₂ : ℝ} (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf)
    (hA₁ : (∫ t in Set.Icc (-T) T, ‖dirPoly M b t‖ ^ 2) ≤ A₁)
    (hA₂ : (∫ t in Set.Icc (-T) T ∩ {t : ℝ | V ≤ ‖dirPoly N a t‖},
        ‖dirPoly M b t‖ ^ 2) ≤ A₂) :
    (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ 2 * A₁ + Bf ^ 2 * A₂ := by
  have hsplit := integral_normSq_mul_split_exceptional N M a b (T := T) (V := V) hBf
  have hV2 : (0 : ℝ) ≤ V ^ 2 := sq_nonneg V
  have hBf2 : (0 : ℝ) ≤ Bf ^ 2 := sq_nonneg Bf
  have h1 : V ^ 2 * (∫ t in Set.Icc (-T) T, ‖dirPoly M b t‖ ^ 2) ≤ V ^ 2 * A₁ :=
    mul_le_mul_of_nonneg_left hA₁ hV2
  have h2 : Bf ^ 2 * (∫ t in Set.Icc (-T) T ∩ {t : ℝ | V ≤ ‖dirPoly N a t‖},
      ‖dirPoly M b t‖ ^ 2) ≤ Bf ^ 2 * A₂ := mul_le_mul_of_nonneg_left hA₂ hBf2
  linarith [hsplit, h1, h2]

/-- **The `(40)` shape.**  The two cases of §4 with their sources named: `A₁` is the mean value
theorem's output and `A₂` is Halász–Montgomery's, and the conclusion is the single quantity the
reduction `(34)` consumes. -/
theorem section4_product_bound_scaled (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    {T V Bf A₁ A₂ C : ℝ} (hC : 0 ≤ C) (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf)
    (hA₁ : (∫ t in Set.Icc (-T) T, ‖dirPoly M b t‖ ^ 2) ≤ A₁)
    (hA₂ : (∫ t in Set.Icc (-T) T ∩ {t : ℝ | V ≤ ‖dirPoly N a t‖},
        ‖dirPoly M b t‖ ^ 2) ≤ A₂) :
    C * (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ C * (V ^ 2 * A₁) + C * (Bf ^ 2 * A₂) := by
  have hbase := section4_product_bound N M a b hBf hA₁ hA₂
  have := mul_le_mul_of_nonneg_left hbase hC
  linarith [this]

/-- **The `A₁` half of `(40)`, discharged.**  The non-exceptional case needs nothing but the mean
value theorem for the second factor. -/
theorem section4_product_bound_mvt (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    {T V Bf A₂ : ℝ} (hT : 0 ≤ T) (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf)
    (hA₂ : (∫ t in Set.Icc (-T) T ∩ {t : ℝ | V ≤ ‖dirPoly N a t‖},
        ‖dirPoly M b t‖ ^ 2) ≤ A₂) :
    (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ 2 * (2 * ((T + 4 * (M : ℝ) * (1 + Real.log M)) * ∑ m : Fin M, ‖b m‖ ^ 2))
        + Bf ^ 2 * A₂ :=
  section4_product_bound N M a b hBf (integral_Icc_normSq_dirPoly_symm_le M b hT) hA₂

end RHTower.Sieve

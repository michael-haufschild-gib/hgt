import Mathlib

/-!
# The second moment controls the tail of the integral

A function with a finite second moment has uniformly small integral tails:

```text
∫_{ξ > K} |f|  ≤  sqrt( (∫_{ξ > K} ξ² f²) / K ) .
```

This is the Cauchy–Schwarz bound `∫ |f| = ∫ (1/ξ)(ξ|f|) ≤ ‖1/ξ‖₂ ‖ξ f‖₂`, but it is obtained here
without any Hölder machinery: the pointwise arithmetic–geometric inequality

```text
|f ξ|  ≤  (t/2)(1/ξ²) + (1/(2t)) ξ² f(ξ)²          (t > 0, ξ > 0)
```

is integrated term by term against `∫_{ξ > K} ξ^(−2) = 1/K`, and the free parameter is then set to
`t = sqrt(N K)`, at which the two halves of the bound coincide.

For a family of profiles with a uniform second-moment bound this makes the tails of `∫ f` uniformly
small, which is exactly what turns locally uniform convergence of the family into convergence of the
integrals — the coordinate half of a prolate-to-Hermite limit.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-- The tail integral of `ξ^(−2)`. -/
theorem integral_Ioi_one_div_sq {K : ℝ} (hK : 0 < K) :
    ∫ ξ in Ioi K, 1 / ξ ^ 2 = 1 / K := by
  have hcongr : ∀ ξ ∈ Ioi K, (1 : ℝ) / ξ ^ 2 = ξ ^ (-2 : ℝ) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := lt_trans hK hξ
    rw [Real.rpow_neg hξ0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_Ioi_rpow_of_lt (by norm_num) hK]
  norm_num
  rw [Real.rpow_neg_one]

/-- The tail of `ξ^(−2)` is integrable. -/
theorem integrableOn_Ioi_one_div_sq {K : ℝ} (hK : 0 < K) :
    IntegrableOn (fun ξ : ℝ => 1 / ξ ^ 2) (Ioi K) := by
  have hcongr : ∀ ξ ∈ Ioi K, (1 : ℝ) / ξ ^ 2 = ξ ^ (-2 : ℝ) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := lt_trans hK hξ
    rw [Real.rpow_neg hξ0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  refine (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hK).congr_fun ?_
    measurableSet_Ioi
  intro ξ hξ
  exact (hcongr ξ hξ).symm

/-- **The pointwise arithmetic–geometric split.** -/
theorem abs_le_secondMoment_split {f : ℝ → ℝ} {ξ t : ℝ} (ht : 0 < t) (hξ : 0 < ξ) :
    |f ξ| ≤ t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2) := by
  have habs : |f ξ| ^ 2 = f ξ ^ 2 := sq_abs _
  have key : 2 * t * ξ ^ 2 * |f ξ| ≤ t ^ 2 + ξ ^ 4 * f ξ ^ 2 := by
    have hsq2 : (ξ ^ 2 * |f ξ|) ^ 2 = ξ ^ 4 * f ξ ^ 2 := by
      rw [mul_pow, habs]
      ring
    nlinarith [sq_nonneg (t - ξ ^ 2 * |f ξ|), hsq2]
  rw [← sub_nonneg]
  have hval : t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2) - |f ξ|
      = (t ^ 2 + ξ ^ 4 * f ξ ^ 2 - 2 * t * ξ ^ 2 * |f ξ|) / (2 * t * ξ ^ 2) := by
    field_simp
  rw [hval]
  refine div_nonneg ?_ (by positivity)
  linarith [key]

/-- **The tail bound with a free parameter.** -/
theorem integral_Ioi_abs_le_param {f : ℝ → ℝ} {K t : ℝ} (hK : 0 < K) (ht : 0 < t)
    (h1 : IntegrableOn (fun ξ => |f ξ|) (Ioi K))
    (h2 : IntegrableOn (fun ξ => ξ ^ 2 * f ξ ^ 2) (Ioi K)) :
    (∫ ξ in Ioi K, |f ξ|)
      ≤ t / (2 * K) + 1 / (2 * t) * ∫ ξ in Ioi K, ξ ^ 2 * f ξ ^ 2 := by
  have hmaj : IntegrableOn
      (fun ξ : ℝ => t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2)) (Ioi K) :=
    ((integrableOn_Ioi_one_div_sq hK).const_mul (t / 2)).add (h2.const_mul (1 / (2 * t)))
  have hmono : (∫ ξ in Ioi K, |f ξ|)
      ≤ ∫ ξ in Ioi K, (t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2)) := by
    refine setIntegral_mono_on h1 hmaj measurableSet_Ioi fun ξ hξ => ?_
    exact abs_le_secondMoment_split ht (lt_trans hK hξ)
  have hval : (∫ ξ in Ioi K, (t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2)))
      = t / (2 * K) + 1 / (2 * t) * ∫ ξ in Ioi K, ξ ^ 2 * f ξ ^ 2 := by
    rw [integral_add ((integrableOn_Ioi_one_div_sq hK).const_mul (t / 2))
      (h2.const_mul (1 / (2 * t))), integral_const_mul, integral_const_mul,
      integral_Ioi_one_div_sq hK]
    ring
  linarith [hmono, hval.le, hval.ge]

/-- **The sharp tail bound.**  Choosing `t = sqrt(N K)` balances the two halves. -/
theorem integral_Ioi_abs_le_sqrt {f : ℝ → ℝ} {K N : ℝ} (hK : 0 < K) (hN : 0 < N)
    (h1 : IntegrableOn (fun ξ => |f ξ|) (Ioi K))
    (h2 : IntegrableOn (fun ξ => ξ ^ 2 * f ξ ^ 2) (Ioi K))
    (hbd : (∫ ξ in Ioi K, ξ ^ 2 * f ξ ^ 2) ≤ N) :
    (∫ ξ in Ioi K, |f ξ|) ≤ Real.sqrt (N / K) := by
  have hNK : 0 < N * K := by positivity
  have ht : 0 < Real.sqrt (N * K) := Real.sqrt_pos.2 hNK
  have hmain := integral_Ioi_abs_le_param (f := f) hK ht h1 h2
  have hstep : Real.sqrt (N * K) / (2 * K)
      + 1 / (2 * Real.sqrt (N * K)) * ∫ ξ in Ioi K, ξ ^ 2 * f ξ ^ 2
      ≤ Real.sqrt (N * K) / (2 * K) + 1 / (2 * Real.sqrt (N * K)) * N := by
    have hpos : (0 : ℝ) < 1 / (2 * Real.sqrt (N * K)) := by positivity
    nlinarith [hbd, hpos]
  refine le_trans hmain (le_trans hstep (le_of_eq ?_))
  have hsq : Real.sqrt (N * K) * Real.sqrt (N * K) = N * K := Real.mul_self_sqrt hNK.le
  have hval : Real.sqrt (N / K) * Real.sqrt (N * K) = N := by
    rw [← Real.sqrt_mul (by positivity)]
    have hprod : N / K * (N * K) = N ^ 2 := by
      field_simp
    rw [hprod, Real.sqrt_sq hN.le]
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hK
  field_simp
  nlinarith [hsq, hval, ht, hK]

end GaloisForLFunctions.RHTower

end

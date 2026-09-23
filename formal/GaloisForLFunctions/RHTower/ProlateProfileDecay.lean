import GaloisForLFunctions.RHTower.SlepianBandCommutation

/-!
# The global prolate profile decays like `1/|x|`

A global prolate profile is produced by the corpus as an eigenfunction of the time–band transform,

```text
(T̃_c Φ)(x) = ∫_{-1}^{1} sinc_c(x − y) Φ(y) dy = χ² Φ(x) ,
```

and the sinc kernel decays: `|sinc_c(u)| = |sin(cu)|/(π|u|) ≤ 1/(π|u|)`.  Since the integration
variable is confined to `[-1,1]`, every `x` with `|x| > 1` has `|x − y| ≥ |x| − 1`, and the eigen
relation turns the kernel decay directly into decay of `Φ`:

```text
|Φ(x)| ≤ (∫_{-1}^{1} |Φ|) / (|χ²| π (|x| − 1)) .
```

No asymptotic analysis of the prolate differential equation is used — only the integral equation the
profile already satisfies.  This is what makes the profile pair legitimately against Gaussian
weights: every boundary term in an integration by parts against a Hermite function vanishes.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

/-- The sinc kernel decays like `1/|u|`. -/
theorem abs_sincSmooth_le_inv {c u : ℝ} (hu : u ≠ 0) :
    |sincSmooth c u| ≤ 1 / (Real.pi * |u|) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu0 : (0 : ℝ) < |u| := abs_pos.mpr hu
  rw [sincSmooth_eq_off hu, sincScalar, abs_div, abs_mul, abs_of_pos hpi]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  · exact Real.abs_sin_le_one _

/-- **A time–band eigenfunction decays like `1/|x|`.** -/
theorem abs_le_of_bandTransform_eigen {c chi2 : ℝ} (hchi : chi2 ≠ 0) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (heig : ∀ x, bandTransform c Φ x = chi2 * Φ x)
    {x : ℝ} (hx : 1 < |x|) :
    |Φ x| ≤ (∫ y in (-1 : ℝ)..1, |Φ y|) / (|chi2| * (Real.pi * (|x| - 1))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hgap : (0 : ℝ) < |x| - 1 := by linarith
  have hchi0 : (0 : ℝ) < |chi2| := abs_pos.mpr hchi
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  -- the kernel is uniformly small on the band
  have hker : ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |sincSmooth c (x - y) * Φ y| ≤ 1 / (Real.pi * (|x| - 1)) * |Φ y| := by
    intro y hy
    have hgapy : |x| - 1 ≤ |x - y| := by
      have h1 : |y| ≤ 1 := abs_le.mpr ⟨hy.1, hy.2⟩
      have h2 : |x| - |y| ≤ |x - y| := abs_sub_abs_le_abs_sub x y
      linarith
    have hxy : x - y ≠ 0 := by
      intro h
      rw [h, abs_zero] at hgapy
      linarith
    have hkerle : |sincSmooth c (x - y)| ≤ 1 / (Real.pi * (|x| - 1)) := by
      refine (abs_sincSmooth_le_inv (c := c) hxy).trans ?_
      gcongr
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hkerle (abs_nonneg _)
  -- integrate
  have hint : IntervalIntegrable (fun y => sincSmooth c (x - y) * Φ y) volume (-1) 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    exact (((contDiff_sincSmooth c).continuous.comp
      (continuous_const.sub continuous_id)).mul hΦ).continuousOn
  have hintabs : IntervalIntegrable (fun y => |sincSmooth c (x - y) * Φ y|) volume (-1) 1 :=
    hint.abs
  have hintR : IntervalIntegrable (fun y => 1 / (Real.pi * (|x| - 1)) * |Φ y|) volume (-1) 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul hΦ.abs.continuousOn
  have habs : |∫ y in (-1 : ℝ)..1, sincSmooth c (x - y) * Φ y|
      ≤ ∫ y in (-1 : ℝ)..1, |sincSmooth c (x - y) * Φ y| :=
    intervalIntegral.abs_integral_le_integral_abs hle
  have hmono : (∫ y in (-1 : ℝ)..1, |sincSmooth c (x - y) * Φ y|)
      ≤ ∫ y in (-1 : ℝ)..1, 1 / (Real.pi * (|x| - 1)) * |Φ y| :=
    intervalIntegral.integral_mono_on hle hintabs hintR hker
  have hval : (∫ y in (-1 : ℝ)..1, 1 / (Real.pi * (|x| - 1)) * |Φ y|)
      = (∫ y in (-1 : ℝ)..1, |Φ y|) / (Real.pi * (|x| - 1)) := by
    rw [intervalIntegral.integral_const_mul]
    field_simp
  have hchain : |chi2| * |Φ x| ≤ (∫ y in (-1 : ℝ)..1, |Φ y|) / (Real.pi * (|x| - 1)) := by
    have hEq : |chi2 * Φ x| = |∫ y in (-1 : ℝ)..1, sincSmooth c (x - y) * Φ y| := by
      rw [← heig x, bandTransform]
      rfl
    rw [abs_mul] at hEq
    rw [hEq]
    exact habs.trans (hmono.trans (le_of_eq hval))
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < |chi2| * (Real.pi * (|x| - 1)))]
  have h := mul_le_mul_of_nonneg_right hchain
    (by positivity : (0 : ℝ) ≤ Real.pi * (|x| - 1))
  rw [div_mul_cancel₀ _ (by positivity : (Real.pi * (|x| - 1)) ≠ 0)] at h
  have hEq : |Φ x| * (|chi2| * (Real.pi * (|x| - 1)))
      = |chi2| * |Φ x| * (Real.pi * (|x| - 1)) := by ring
  rw [hEq]
  exact h

/-! ## The derivative decays too -/

/-- The differentiated sinc kernel decays like `1/|u|`. -/
theorem abs_deriv_sincSmooth_le {c u : ℝ} (hu : u ≠ 0) :
    |deriv (sincSmooth c) u| ≤ (|c| * |u| + 1) / (Real.pi * u ^ (2 : ℕ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu2 : (0 : ℝ) < u ^ (2 : ℕ) := by positivity
  rw [deriv_sincSmooth_off hu, (hasDerivAt_sincScalar hu).deriv, sincScalarD]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.pi * u ^ (2 : ℕ))]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (abs_sub _ _).trans ?_
  have h1 : |c * u * Real.cos (c * u)| ≤ |c| * |u| := by
    rw [abs_mul, abs_mul]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  have h2 : |Real.sin (c * u)| ≤ 1 := Real.abs_sin_le_one _
  linarith

/-- **The derivative of a time–band eigenfunction decays like `1/|x|`.** -/
theorem abs_deriv_le_of_bandTransform_eigen {c chi2 : ℝ} (hchi : chi2 ≠ 0) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (heig : ∀ x, bandTransform c Φ x = chi2 * Φ x)
    {x : ℝ} (hx : 1 < |x|) :
    |deriv Φ x|
      ≤ (|c| * (|x| + 1) + 1) * (∫ y in (-1 : ℝ)..1, |Φ y|)
          / (|chi2| * (Real.pi * (|x| - 1) ^ (2 : ℕ))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hgap : (0 : ℝ) < |x| - 1 := by linarith
  have hchi0 : (0 : ℝ) < |chi2| := abs_pos.mpr hchi
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  -- the differentiated kernel is uniformly small on the band
  have hker : ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |deriv (sincSmooth c) (x - y) * Φ y|
        ≤ (|c| * (|x| + 1) + 1) / (Real.pi * (|x| - 1) ^ (2 : ℕ)) * |Φ y| := by
    intro y hy
    have hy1 : |y| ≤ 1 := abs_le.mpr ⟨hy.1, hy.2⟩
    have hlow : |x| - 1 ≤ |x - y| := by
      have h2 : |x| - |y| ≤ |x - y| := abs_sub_abs_le_abs_sub x y
      linarith
    have hup : |x - y| ≤ |x| + 1 := by
      have h2 : |x - y| ≤ |x| + |y| := abs_sub _ _
      linarith
    have hxy : x - y ≠ 0 := by
      intro h
      rw [h, abs_zero] at hlow
      linarith
    have hsq : (|x| - 1) ^ (2 : ℕ) ≤ (x - y) ^ (2 : ℕ) := by
      have := sq_abs (x - y)
      nlinarith [hlow, hgap]
    have hkerle : |deriv (sincSmooth c) (x - y)|
        ≤ (|c| * (|x| + 1) + 1) / (Real.pi * (|x| - 1) ^ (2 : ℕ)) := by
      refine (abs_deriv_sincSmooth_le (c := c) hxy).trans ?_
      have hnum : |c| * |x - y| + 1 ≤ |c| * (|x| + 1) + 1 := by
        have : |c| * |x - y| ≤ |c| * (|x| + 1) :=
          mul_le_mul_of_nonneg_left hup (abs_nonneg c)
        linarith
      have hden : (0 : ℝ) < Real.pi * (|x| - 1) ^ (2 : ℕ) := by positivity
      have hden2 : (0 : ℝ) < Real.pi * (x - y) ^ (2 : ℕ) := by
        have : (0 : ℝ) < (x - y) ^ (2 : ℕ) := by positivity
        positivity
      rw [div_le_div_iff₀ hden2 hden]
      have hS : (0 : ℝ) ≤ Real.pi * (|x| - 1) ^ (2 : ℕ) := by positivity
      have hB : (0 : ℝ) ≤ |c| * (|x| + 1) + 1 := by positivity
      have hT : Real.pi * (|x| - 1) ^ (2 : ℕ) ≤ Real.pi * (x - y) ^ (2 : ℕ) := by
        nlinarith [hsq, hpi.le]
      calc (|c| * |x - y| + 1) * (Real.pi * (|x| - 1) ^ (2 : ℕ))
          ≤ (|c| * (|x| + 1) + 1) * (Real.pi * (|x| - 1) ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_right hnum hS
        _ ≤ (|c| * (|x| + 1) + 1) * (Real.pi * (x - y) ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hT hB
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hkerle (abs_nonneg _)
  -- integrate
  have hcont : Continuous fun y : ℝ => deriv (sincSmooth c) (x - y) * Φ y :=
    (((contDiff_deriv_sincSmooth c).continuous.comp
      (continuous_const.sub continuous_id)).mul hΦ)
  have hint : IntervalIntegrable (fun y => deriv (sincSmooth c) (x - y) * Φ y) volume (-1) 1 :=
    hcont.intervalIntegrable _ _
  have hintR : IntervalIntegrable
      (fun y => (|c| * (|x| + 1) + 1) / (Real.pi * (|x| - 1) ^ (2 : ℕ)) * |Φ y|) volume (-1) 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul hΦ.abs.continuousOn
  have habs : |∫ y in (-1 : ℝ)..1, deriv (sincSmooth c) (x - y) * Φ y|
      ≤ ∫ y in (-1 : ℝ)..1, |deriv (sincSmooth c) (x - y) * Φ y| :=
    intervalIntegral.abs_integral_le_integral_abs hle
  have hmono : (∫ y in (-1 : ℝ)..1, |deriv (sincSmooth c) (x - y) * Φ y|)
      ≤ ∫ y in (-1 : ℝ)..1, (|c| * (|x| + 1) + 1) / (Real.pi * (|x| - 1) ^ (2 : ℕ)) * |Φ y| :=
    intervalIntegral.integral_mono_on hle hint.abs hintR hker
  have hval : (∫ y in (-1 : ℝ)..1, (|c| * (|x| + 1) + 1) / (Real.pi * (|x| - 1) ^ (2 : ℕ)) * |Φ y|)
      = (|c| * (|x| + 1) + 1) * (∫ y in (-1 : ℝ)..1, |Φ y|) / (Real.pi * (|x| - 1) ^ (2 : ℕ)) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  -- the eigen relation differentiates
  have hderivEig : deriv (bandTransform c Φ) x = chi2 * deriv Φ x := by
    have hfun : bandTransform c Φ = fun y => chi2 * Φ y := funext heig
    rw [hfun, deriv_const_mul_field]
  have hderivBand : deriv (bandTransform c Φ) x
      = ∫ y in (-1 : ℝ)..1, deriv (sincSmooth c) (x - y) * Φ y := by
    rw [deriv_bandTransform c hΦ]
  have hchain : |chi2| * |deriv Φ x|
      ≤ (|c| * (|x| + 1) + 1) * (∫ y in (-1 : ℝ)..1, |Φ y|) / (Real.pi * (|x| - 1) ^ (2 : ℕ)) := by
    have hEq : |chi2| * |deriv Φ x|
        = |∫ y in (-1 : ℝ)..1, deriv (sincSmooth c) (x - y) * Φ y| := by
      rw [← abs_mul, ← hderivEig, hderivBand]
    rw [hEq]
    exact habs.trans (hmono.trans (le_of_eq hval))
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < |chi2| * (Real.pi * (|x| - 1) ^ (2 : ℕ)))]
  have h := mul_le_mul_of_nonneg_right hchain
    (by positivity : (0 : ℝ) ≤ Real.pi * (|x| - 1) ^ (2 : ℕ))
  rw [div_mul_cancel₀ _ (by positivity : (Real.pi * (|x| - 1) ^ (2 : ℕ)) ≠ 0)] at h
  have hEq2 : |deriv Φ x| * (|chi2| * (Real.pi * (|x| - 1) ^ (2 : ℕ)))
      = |chi2| * |deriv Φ x| * (Real.pi * (|x| - 1) ^ (2 : ℕ)) := by ring
  rw [hEq2]
  exact h

end RHTower

end

import GaloisForLFunctions.RHTower.ProlateProfileDecay
import GaloisForLFunctions.RHTower.ProlateEvenCrossSpectralContinuity
import GaloisForLFunctions.RHTower.ProlateSourcePolarPrimitive

/-!
# Global derivative bounds for a band eigenfunction

`exists_bound_of_bandTransform_eigen` bounds a global band eigenfunction itself, by putting the
uniform kernel bound `|sinc_c| ≤ |c|/π` under the band integral.  The same argument bounds its
derivatives, because differentiating a band transform differentiates only the kernel:

```text
lam · Φ′  = ∫_{-1}^{1} sinc_c′(x − y) Φ(y) dy ,
lam · Φ″  = ∫_{-1}^{1} sinc_c″(x − y) Φ(y) dy .
```

The second kernel derivative has the exact integral model
`sinc_c″(u) = −c³/(2π) ∫_{-1}^{1} t² cos(cut) dt`, uniformly bounded by `|c|³/(3π)`.  The first is
bounded by combining its `1/u²` decay off the diagonal with continuity on the unit window.

These bounds are what let a genuine prolate mode be paired against a Hermite function with all
integrability and boundary hypotheses discharged: after the Hermite rescaling every derivative of
the profile is a bounded function, and a bounded function against a Gaussian-decaying weight is
integrable and vanishes at infinity.
-/

noncomputable section

open MeasureTheory

namespace RHTower

/-! ## Uniform bounds on the kernel derivatives -/

/-- The differentiated sinc kernel is globally bounded. -/
theorem exists_global_bound_deriv_sincSmooth (c : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, |deriv (sincSmooth c) u| ≤ M := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((contDiff_deriv_sincSmooth c).continuous.continuousOn)
  refine ⟨max (max C 0) ((|c| + 1) / Real.pi),
    le_trans (le_max_right C 0) (le_trans (le_max_left _ _) le_rfl), fun u => ?_⟩
  rcases le_or_gt |u| 1 with hu | hu
  · have hmem : u ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le u]; linarith [le_abs_self u]]
    have h := hC u hmem
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_trans (le_max_left C 0) (le_max_left _ _))
  · have hu0 : u ≠ 0 := by
      intro h
      rw [h] at hu
      simp at hu
      linarith
    have habs : (0 : ℝ) < |u| := abs_pos.2 hu0
    have h := abs_deriv_sincSmooth_le (c := c) hu0
    have hsq : |u| ≤ u ^ (2 : ℕ) := by
      have hmul : |u| * 1 ≤ |u| * |u| := by nlinarith
      have hid : |u| * |u| = u ^ (2 : ℕ) := by rw [← sq_abs u]; ring
      calc |u| = |u| * 1 := by ring
        _ ≤ |u| * |u| := hmul
        _ = u ^ (2 : ℕ) := hid
    have hstep : (|c| * |u| + 1) / (Real.pi * u ^ (2 : ℕ)) ≤ (|c| + 1) / Real.pi := by
      rw [div_le_div_iff₀ (by positivity) hpi]
      have h1 : |c| * |u| * Real.pi + Real.pi ≤ (|c| + 1) * (Real.pi * u ^ (2 : ℕ)) := by
        have hc0 : (0 : ℝ) ≤ |c| := abs_nonneg c
        have hu2 : (1 : ℝ) < u ^ (2 : ℕ) := lt_of_lt_of_le hu hsq
        have e1 : |c| * Real.pi * |u| ≤ |c| * Real.pi * u ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        have e2 : Real.pi * 1 ≤ Real.pi * u ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hu2.le hpi.le
        nlinarith [e1, e2]
      linarith
    exact le_trans (le_trans h hstep) (le_max_right _ _)

/-- The twice-differentiated sinc kernel is globally bounded by `|c|³/(3π)`. -/
theorem abs_deriv2_sincSmooth_le (c u : ℝ) :
    |deriv (deriv (sincSmooth c)) u| ≤ |c| ^ (3 : ℕ) / (3 * Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [deriv2_sincSmooth_eq_sincSecondIntegralProfile, sincSecondIntegralProfile, abs_mul]
  have hcoef : |(-(c ^ (3 : ℕ)) / (2 * Real.pi))| = |c| ^ (3 : ℕ) / (2 * Real.pi) := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_pow]
  have hmoment : (∫ t in (-1 : ℝ)..1, t ^ (2 : ℕ)) = 2 / 3 := by
    rw [integral_pow]
    norm_num
  have hint1 : IntervalIntegrable (fun t : ℝ => t ^ (2 : ℕ) * Real.cos (c * u * t)) volume (-1) 1 :=
    (by fun_prop : Continuous fun t : ℝ => t ^ (2 : ℕ) * Real.cos (c * u * t)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t : ℝ => t ^ (2 : ℕ)) volume (-1) 1 :=
    (by fun_prop : Continuous fun t : ℝ => t ^ (2 : ℕ)).intervalIntegrable _ _
  have hbound : |∫ t in (-1 : ℝ)..1, t ^ (2 : ℕ) * Real.cos (c * u * t)| ≤ 2 / 3 := by
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (f := fun t : ℝ => t ^ (2 : ℕ) * Real.cos (c * u * t)) (μ := volume)
      (by norm_num : (-1 : ℝ) ≤ 1)
    refine le_trans habs ?_
    rw [← hmoment]
    refine intervalIntegral.integral_mono_on (by norm_num) hint1.abs hint2 fun t _ => ?_
    rw [abs_mul, abs_pow, sq_abs]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  rw [hcoef]
  calc |c| ^ (3 : ℕ) / (2 * Real.pi) * |∫ t in (-1 : ℝ)..1, t ^ (2 : ℕ) * Real.cos (c * u * t)|
      ≤ |c| ^ (3 : ℕ) / (2 * Real.pi) * (2 / 3) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = |c| ^ (3 : ℕ) / (3 * Real.pi) := by field_simp


/-! ## Global bounds on a band eigenfunction and its derivatives -/

/-- A global band eigenfunction has the band transform as its own scalar multiple, so it inherits
the smoothness of the kernel. -/
theorem hasDerivAt_of_bandTransform_eigen {c lam : ℝ} (hlam : lam ≠ 0) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (hband : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x) (x : ℝ) :
    HasDerivAt Φ (lam⁻¹ * ∫ y in (-1 : ℝ)..1, deriv (sincSmooth c) (x - y) * Φ y) x := by
  have hb := hasDerivAt_bandTransform c hΦ x
  have heq : bandTransform c Φ = fun z => lam * Φ z := funext hband
  rw [heq] at hb
  have h2 := hb.const_mul lam⁻¹
  have h3 : (fun z : ℝ => lam⁻¹ * (lam * Φ z)) = Φ := by
    funext z
    field_simp
  rwa [h3] at h2

theorem differentiable_of_bandTransform_eigen {c lam : ℝ} (hlam : lam ≠ 0) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (hband : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x) :
    Differentiable ℝ Φ :=
  fun x => (hasDerivAt_of_bandTransform_eigen hlam hΦ hband x).differentiableAt

theorem deriv_eq_of_bandTransform_eigen {c lam : ℝ} (hlam : lam ≠ 0) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (hband : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x) :
    deriv Φ = fun x => lam⁻¹ * ∫ y in (-1 : ℝ)..1, deriv (sincSmooth c) (x - y) * Φ y :=
  funext fun x => (hasDerivAt_of_bandTransform_eigen hlam hΦ hband x).deriv

/-- The second derivative of a global band eigenfunction, with both derivatives on the kernel. -/
theorem hasDerivAt_deriv_of_bandTransform_eigen {c lam : ℝ} (hlam : lam ≠ 0) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (hband : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x) (x : ℝ) :
    HasDerivAt (deriv Φ)
      (lam⁻¹ * ∫ y in (-1 : ℝ)..1, deriv (deriv (sincSmooth c)) (x - y) * Φ y) x := by
  rw [deriv_eq_of_bandTransform_eigen hlam hΦ hband]
  exact (hasDerivAt_bandTranslationTransform (differentiable_deriv_sincSmooth c)
    (continuous_deriv2_sincSmooth c) hΦ x).const_mul lam⁻¹

/-- A band integral against a uniformly bounded kernel is bounded by the kernel bound times the
window mass. -/
theorem abs_bandIntegral_le {M : ℝ} {g Φ : ℝ → ℝ} (hg : Continuous g) (hΦ : Continuous Φ)
    (hM : ∀ u : ℝ, |g u| ≤ M) (x : ℝ) :
    |∫ y in (-1 : ℝ)..1, g (x - y) * Φ y| ≤ M * ∫ y in (-1 : ℝ)..1, |Φ y| := by
  have hint1 : IntervalIntegrable (fun y : ℝ => g (x - y) * Φ y) volume (-1) 1 :=
    ((hg.comp (continuous_const.sub continuous_id)).mul hΦ).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun y : ℝ => M * |Φ y|) volume (-1) 1 :=
    (continuous_const.mul hΦ.abs).intervalIntegrable _ _
  have habs := intervalIntegral.abs_integral_le_integral_abs
    (f := fun y : ℝ => g (x - y) * Φ y) (μ := volume) (by norm_num : (-1 : ℝ) ≤ 1)
  refine le_trans habs ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num) hint1.abs hint2 fun y _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hM (x - y)) (abs_nonneg _)

/-- **The derivative of a global band eigenfunction is globally bounded.** -/
theorem exists_bound_deriv_of_bandTransform_eigen {c lam : ℝ} (hlam : lam ≠ 0) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (hband : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv Φ x| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_global_bound_deriv_sincSmooth c
  have hI0 : (0 : ℝ) ≤ ∫ y in (-1 : ℝ)..1, |Φ y| :=
    intervalIntegral.integral_nonneg (by norm_num) fun y _ => abs_nonneg _
  refine ⟨|lam|⁻¹ * (M * ∫ y in (-1 : ℝ)..1, |Φ y|), by positivity, fun x => ?_⟩
  rw [(hasDerivAt_of_bandTransform_eigen hlam hΦ hband x).deriv, abs_mul, abs_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact abs_bandIntegral_le (contDiff_deriv_sincSmooth c).continuous hΦ hM x

/-- **The second derivative of a global band eigenfunction is globally bounded.** -/
theorem exists_bound_deriv2_of_bandTransform_eigen {c lam : ℝ} (hlam : lam ≠ 0) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (hband : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv (deriv Φ) x| ≤ C := by
  have hI0 : (0 : ℝ) ≤ ∫ y in (-1 : ℝ)..1, |Φ y| :=
    intervalIntegral.integral_nonneg (by norm_num) fun y _ => abs_nonneg _
  refine ⟨|lam|⁻¹ * (|c| ^ (3 : ℕ) / (3 * Real.pi) * ∫ y in (-1 : ℝ)..1, |Φ y|),
    by positivity, fun x => ?_⟩
  rw [(hasDerivAt_deriv_of_bandTransform_eigen hlam hΦ hband x).deriv, abs_mul, abs_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact abs_bandIntegral_le (continuous_deriv2_sincSmooth c) hΦ (abs_deriv2_sincSmooth_le c) x

end RHTower

end

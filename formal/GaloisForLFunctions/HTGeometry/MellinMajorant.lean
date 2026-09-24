import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# The Mellin majorant and vertical boundedness of `Λ₀`

The Mellin transform is dominated by the real Mellin transform of the norm, and the majorant
depends only on the abscissa:

```text
‖mellin f s‖ ≤ ∫_0^∞ t^{Re s - 1} ‖f t‖ dt.
```

For a weak functional-equation pair the modified function `f_modif` is Mellin convergent at every
point, so `Λ₀ = mellin f_modif` is **bounded on every vertical strip, uniformly in the height**.
This is the input a Phragmén--Lindelöf argument needs for a completed `L`-function: all the growth
in the height sits in the Gamma factor one divides by.
-/

open MeasureTheory Complex Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The real Mellin majorant of `f` at abscissa `σ`. -/
def mellinMajorant (f : ℝ → E) (σ : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * ‖f t‖

omit [NormedSpace ℂ E] in
theorem mellinMajorant_nonneg (f : ℝ → E) (σ : ℝ) : 0 ≤ mellinMajorant f σ := by
  refine setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  positivity

/-- **The Mellin transform is dominated by the Mellin majorant at its abscissa.** -/
theorem norm_mellin_le (f : ℝ → E) (s : ℂ) : ‖mellin f s‖ ≤ mellinMajorant f s.re := by
  rw [mellin, mellinMajorant]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  simp

theorem integrableOn_mellinMajorant {f : ℝ → E} {σ : ℝ} (h : MellinConvergent f (σ : ℂ)) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖f t‖) (Ioi 0) := by
  have hn : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((σ : ℂ) - 1) • f t‖) (Ioi 0) :=
    MeasureTheory.Integrable.norm h
  refine hn.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  show ‖(t : ℂ) ^ ((σ : ℂ) - 1) • f t‖ = t ^ (σ - 1) * ‖f t‖
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  simp

/-- The majorant at an intermediate abscissa is at most the sum of the two endpoint majorants. -/
theorem mellinMajorant_le {f : ℝ → E} {σ σ₀ σ₁ : ℝ}
    (h : MellinConvergent f (σ : ℂ)) (h0 : MellinConvergent f (σ₀ : ℂ))
    (h1 : MellinConvergent f (σ₁ : ℂ)) (hle0 : σ₀ ≤ σ) (hle1 : σ ≤ σ₁) :
    mellinMajorant f σ ≤ mellinMajorant f σ₀ + mellinMajorant f σ₁ := by
  have hi := integrableOn_mellinMajorant h
  have hi0 := integrableOn_mellinMajorant h0
  have hi1 := integrableOn_mellinMajorant h1
  rw [mellinMajorant, mellinMajorant, mellinMajorant, ← integral_add hi0 hi1]
  refine setIntegral_mono_on hi (hi0.add hi1) measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  have hpt : t ^ (σ - 1) ≤ t ^ (σ₀ - 1) + t ^ (σ₁ - 1) := by
    rcases le_total t 1 with hle | hle
    · have hstep : t ^ (σ - 1) ≤ t ^ (σ₀ - 1) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 hle (by linarith)
      have hnn : (0 : ℝ) ≤ t ^ (σ₁ - 1) := Real.rpow_nonneg ht0.le _
      linarith
    · have hstep : t ^ (σ - 1) ≤ t ^ (σ₁ - 1) :=
        Real.rpow_le_rpow_of_exponent_le hle (by linarith)
      have hnn : (0 : ℝ) ≤ t ^ (σ₀ - 1) := Real.rpow_nonneg ht0.le _
      linarith
  have hfn : (0 : ℝ) ≤ ‖f t‖ := norm_nonneg _
  nlinarith [hpt, hfn]

/-- `f_modif` is Mellin convergent at every point. -/
theorem mellinConvergent_f_modif (P : WeakFEPair ℂ) (s : ℂ) :
    MellinConvergent P.f_modif s :=
  (P.isStrongFEPair_toStrongFEPair.hasMellin s).1

/-- **`Λ₀` is bounded on every vertical strip, uniformly in the height.** -/
theorem exists_bound_norm_WeakFEPair_Λ₀ (P : WeakFEPair ℂ) (σ₀ σ₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → ‖P.Λ₀ s‖ ≤ C := by
  refine ⟨mellinMajorant P.f_modif σ₀ + mellinMajorant P.f_modif σ₁,
    add_nonneg (mellinMajorant_nonneg _ _) (mellinMajorant_nonneg _ _), fun s h0 h1 => ?_⟩
  refine le_trans (norm_mellin_le P.f_modif s) ?_
  exact mellinMajorant_le (mellinConvergent_f_modif P _) (mellinConvergent_f_modif P _)
    (mellinConvergent_f_modif P _) h0 h1

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistPerronIdentity
import GaloisForLFunctions.RHTower.Sieve.PoleTermSplit

/-!
# The divided-difference term of the twisted Chebyshev integrand

The twisted Perron integrand splits into a divided difference, a pure pole and a regular part.  The
pure pole sits at `1 - iτ`, and the divided difference `dslope W (1-iτ)` is holomorphic there — that
is the defining property of `dslope`.  So on a rectangle `[c,d] × [-T,T]` straddling both the
abscissa and the twist pole, this term shifts across the abscissa with no residue.

Together with the shift for the regular part, the entire residue of the twisted integrand is
carried by the pure pole `W(1-iτ)·(s + iτ - 1)⁻¹`, whose coefficient is the twisted main term.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

@[simp] theorem twistPole_re (τ : ℝ) : (twistPole τ).re = 1 := by
  simp [twistPole]

@[simp] theorem twistPole_im (τ : ℝ) : (twistPole τ).im = -τ := by
  simp [twistPole]

/-- A closed rectangle straddling the twist pole is a neighbourhood of it. -/
theorem rect_mem_nhds_twistPole {c d T τ : ℝ} (hc : c < 1) (hd : 1 < d) (hτ : |τ| < T) :
    Set.uIcc c d ×ℂ Set.uIcc (-T) T ∈ nhds (twistPole τ) := by
  have hcd : c ≤ d := by linarith
  have hT0 : (0 : ℝ) < T := lt_of_le_of_lt (abs_nonneg τ) hτ
  have hTT : (-T : ℝ) ≤ T := by linarith
  have habs := abs_lt.mp hτ
  refine Filter.mem_of_superset (?_ : Set.Ioo c d ×ℂ Set.Ioo (-T) T ∈ nhds (twistPole τ)) ?_
  · have hopen : IsOpen (Set.Ioo c d ×ℂ Set.Ioo (-T) T) := by
      have h1 : IsOpen (Complex.re ⁻¹' Set.Ioo c d) :=
        isOpen_Ioo.preimage Complex.continuous_re
      have h2 : IsOpen (Complex.im ⁻¹' Set.Ioo (-T) T) :=
        isOpen_Ioo.preimage Complex.continuous_im
      exact h1.inter h2
    refine hopen.mem_nhds ?_
    rw [Complex.mem_reProdIm]
    constructor
    · simp only [twistPole_re, Set.mem_Ioo]
      exact ⟨hc, hd⟩
    · simp only [twistPole_im, Set.mem_Ioo]
      exact ⟨by linarith [habs.2], by linarith [habs.1]⟩
  · intro z hz
    rw [Complex.mem_reProdIm] at hz ⊢
    rw [Set.uIcc_of_le hcd, Set.uIcc_of_le hTT]
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩

/-- **The divided difference of the cutoff's transform at the twist pole is holomorphic on the
rectangle.** -/
theorem differentiableOn_dslope_mellin_twist_rect {N H : ℝ} (hH : 0 < H) {c d T τ : ℝ}
    (hc0 : 0 < c) (hc : c < 1) (hd : 1 < d) (hτ : |τ| < T) :
    DifferentiableOn ℂ
      (dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ))
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  have hT0 : (0 : ℝ) < T := lt_of_le_of_lt (abs_nonneg τ) hτ
  refine (Complex.differentiableOn_dslope (rect_mem_nhds_twistPole hc hd hτ)).2 ?_
  exact (differentiableOn_mellin_smoothWeight_strip hH hc0).mono
    (rect_subset_verticalStrip (by linarith) T)

/-- **The truncated contour shift for the divided-difference term of the twisted integrand.**  No
residue: the divided difference is holomorphic at the twist pole itself. -/
theorem integral_dslope_mellin_twist_vertical_sub_eq_horizontal_rect {N H : ℝ} (hH : 0 < H)
    {c d T τ : ℝ} (hc0 : 0 < c) (hc : c < 1) (hd : 1 < d) (hτ : |τ| < T) :
    (Complex.I • (∫ y : ℝ in (-T)..T,
          dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
            ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T,
          dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
            ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d,
            dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
              ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d,
            dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
              ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
  integral_vertical_sub_eq_horizontal_rect T
    (differentiableOn_dslope_mellin_twist_rect hH hc0 hc hd hτ)

end RHTower.Sieve

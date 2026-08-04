import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegShift

/-!
# Splitting the pole term

The residue of the Chebyshev integrand sits entirely in `W(s)/(s-1)`.  Splitting that further,

    W(s)/(s-1) = dslope W 1 s + W(1)/(s-1),

isolates the residue completely: the divided difference `dslope W 1` is holomorphic wherever `W` is,
including at `s = 1` itself, so its contour integral vanishes and the whole residue is `W(1)` times
the integral of `(s-1)⁻¹`.

Mathlib's `Complex.differentiableOn_dslope` supplies the holomorphy, provided the rectangle is a
neighbourhood of `1` — which it is when the abscissae straddle `1` strictly.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- A closed rectangle straddling `1` is a neighbourhood of it. -/
theorem rect_mem_nhds_one {c d T : ℝ} (hc : c < 1) (hd : 1 < d) (hT : 0 < T) :
    Set.uIcc c d ×ℂ Set.uIcc (-T) T ∈ nhds (1 : ℂ) := by
  have hcd : c ≤ d := by linarith
  have hTT : (-T : ℝ) ≤ T := by linarith
  refine Filter.mem_of_superset (?_ : Set.Ioo c d ×ℂ Set.Ioo (-T) T ∈ nhds (1 : ℂ)) ?_
  · have hopen : IsOpen (Set.Ioo c d ×ℂ Set.Ioo (-T) T) := by
      have h1 : IsOpen (Complex.re ⁻¹' Set.Ioo c d) :=
        isOpen_Ioo.preimage Complex.continuous_re
      have h2 : IsOpen (Complex.im ⁻¹' Set.Ioo (-T) T) :=
        isOpen_Ioo.preimage Complex.continuous_im
      exact h1.inter h2
    refine hopen.mem_nhds ?_
    rw [Complex.mem_reProdIm]
    constructor
    · simp only [Complex.one_re, Set.mem_Ioo]
      exact ⟨hc, hd⟩
    · simp only [Complex.one_im, Set.mem_Ioo]
      constructor <;> linarith
  · intro z hz
    rw [Complex.mem_reProdIm] at hz ⊢
    rw [Set.uIcc_of_le hcd, Set.uIcc_of_le hTT]
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩

/-- **The divided difference of the cutoff's transform is holomorphic on the rectangle.** -/
theorem differentiableOn_dslope_mellin_rect {N H : ℝ} (hH : 0 < H) {c d T : ℝ} (hc0 : 0 < c)
    (hc : c < 1) (hd : 1 < d) (hT : 0 < T) :
    DifferentiableOn ℂ
      (dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  refine (Complex.differentiableOn_dslope (rect_mem_nhds_one hc hd hT)).2 ?_
  exact (differentiableOn_mellin_smoothWeight_strip hH hc0).mono
    (rect_subset_verticalStrip (by linarith) T)

/-- **The pole term splits.**  Off the pole, `W(s)/(s-1)` is the divided difference plus the pure
pole `W(1)/(s-1)`. -/
theorem mellin_div_sub_one_split {N H : ℝ} {s : ℂ} (hs : s ≠ 1) :
    (s - 1)⁻¹ * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s
      = dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1 s
        + (s - 1)⁻¹ * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1 := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [dslope_of_ne _ hs, slope_def_field]
  field_simp
  ring

/-- **The divided difference shifts with no residue.** -/
theorem integral_dslope_mellin_vertical_sub_eq_horizontal_rect {N H : ℝ} (hH : 0 < H)
    {c d T : ℝ} (hc0 : 0 < c) (hc : c < 1) (hd : 1 < d) (hT : 0 < T) :
    (Complex.I • (∫ y : ℝ in (-T)..T,
          dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
            ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T,
          dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
            ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
            ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
            ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
  integral_vertical_sub_eq_horizontal_rect T
    (differentiableOn_dslope_mellin_rect hH hc0 hc hd hT)

end RHTower.Sieve

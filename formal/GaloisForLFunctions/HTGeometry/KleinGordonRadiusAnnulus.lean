import GaloisForLFunctions.HTGeometry.KleinGordonSymmetricStability

/-!
# The spectral radius itself lies in the annulus

Statement 392 confines each Floquet multiplier to `e^{−b|T|} ≤ |k| ≤ e^{b|T|}`. The spectral radius is
the supremum of their moduli, so the same annulus holds for it — the upper bound because a supremum of
things below a bound is below it, the lower bound because the spectrum is inhabited (statement 341) and
a supremum dominates any one of its terms.

`e^{−b|T|} ≤ spectralRadius M ≤ e^{b|T|}`.

The two elementary facts about suprema this needs — that a spectral value is dominated by the radius,
and that a uniform bound on the values bounds the radius — are recorded here once, having been inlined
twice already.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ENNReal

/-! ## Two facts about the spectral radius -/

section Radius

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The extended norm of a complex number is the extended real of its norm. -/
theorem enorm_eq_ofReal_norm (k : ℂ) : ((‖k‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖k‖ := by
  rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg k)]
  congr 1

/-- **A spectral value is dominated by the spectral radius.** -/
theorem norm_le_spectralRadius {a : A} {k : ℂ} (hk : k ∈ spectrum ℂ a) :
    ((‖k‖₊ : ℝ≥0∞)) ≤ spectralRadius ℂ a := by
  show ((‖k‖₊ : ℝ≥0∞)) ≤ ⨆ z ∈ spectrum ℂ a, ((‖z‖₊ : ℝ≥0∞))
  exact le_iSup₂ (f := fun z (_ : z ∈ spectrum ℂ a) => ((‖z‖₊ : ℝ≥0∞))) k hk

/-- **A uniform bound on the spectral values bounds the spectral radius.** -/
theorem spectralRadius_le_ofReal_of_forall {a : A} {c : ℝ}
    (h : ∀ k ∈ spectrum ℂ a, ‖k‖ ≤ c) : spectralRadius ℂ a ≤ ENNReal.ofReal c := by
  show (⨆ z ∈ spectrum ℂ a, ((‖z‖₊ : ℝ≥0∞))) ≤ ENNReal.ofReal c
  refine iSup₂_le fun z hz => ?_
  rw [enorm_eq_ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h z hz)

end Radius

/-! ## The annulus for the radius -/

section MonodromyRadius

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The spectral radius of a monodromy lies in the annulus the energy estimate cuts out.** -/
theorem spectralRadius_kgMonodromy_mem_annulus (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) :
    ENNReal.ofReal (Real.exp (-(b * |T|)))
        ≤ spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)
      ∧ spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)
        ≤ ENNReal.ofReal (Real.exp (b * |T|)) := by
  constructor
  · obtain ⟨k₀, hk₀⟩ := spectrum_kgMonodromy_nonempty (T := T) hb0 hWb hWs
    have hge := exp_neg_le_norm_of_mem_spectrum_kgMonodromy hb0 hWb hWs hper hk₀
    have hlow : ENNReal.ofReal (Real.exp (-(b * |T|))) ≤ ((‖k₀‖₊ : ℝ≥0∞)) := by
      rw [enorm_eq_ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hge
    exact hlow.trans (norm_le_spectralRadius hk₀)
  · exact spectralRadius_le_ofReal_of_forall fun k hk =>
      norm_le_of_mem_spectrum_kgMonodromy hb0 hWb hWs hk

end MonodromyRadius

end GaloisForLFunctions.HTGeometry

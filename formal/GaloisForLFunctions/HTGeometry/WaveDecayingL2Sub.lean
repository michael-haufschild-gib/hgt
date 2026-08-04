import GaloisForLFunctions.HTGeometry.WaveDecayingL2
import GaloisForLFunctions.HTGeometry.WaveCauchyUniqueness

/-!
# The square-integrability criterion is closed under differences

The bundle of decay hypotheses is not closed under differences: its fields are products of two
derivatives, and the difference of two solutions produces cross terms. The square-integrability
criterion has no such defect, because `MemLp _ 2` is a linear condition. So two solutions meeting
the criterion have a difference that meets it as well, and the uniqueness theorem applies to them.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Sub

variable {d : ℕ} {u₁ u₂ : ℝ × (Fin d → ℝ) → ℝ}

theorem slice_sub (t : ℝ) :
    slice (fun q => u₁ q - u₂ q) t = fun x : Fin d → ℝ => slice u₁ t x - slice u₂ t x := rfl

theorem coordPartial_sub_fun {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i : Fin d) :
    coordPartial i (fun x : Fin d → ℝ => f x - g x)
      = fun x => coordPartial i f x - coordPartial i g x := by
  funext x
  have hd : HasFDerivAt (fun y : Fin d → ℝ => f y - g y) (fderiv ℝ f x - fderiv ℝ g x) x :=
    (differentiableAt_of_contDiff_infty hf x).hasFDerivAt.sub
      (differentiableAt_of_contDiff_infty hg x).hasFDerivAt
  rw [coordPartial, hd.fderiv]
  simp [coordPartial]

/-- **Square integrability of the slices passes to a difference.** -/
theorem memLp_two_slice_sub {t : ℝ} (h₁ : MemLp (slice u₁ t) 2 (volume : Measure (Fin d → ℝ)))
    (h₂ : MemLp (slice u₂ t) 2 (volume : Measure (Fin d → ℝ))) :
    MemLp (slice (fun q => u₁ q - u₂ q) t) 2 (volume : Measure (Fin d → ℝ)) := by
  rw [slice_sub]
  exact h₁.sub h₂

/-- **Square integrability of a directional derivative passes to a difference.** -/
theorem memLp_two_slice_dirDeriv_sub (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    {v : ℝ × (Fin d → ℝ)} {t : ℝ}
    (h₁ : MemLp (fun x : Fin d → ℝ => waveDirDeriv v u₁ (t, x)) 2
      (volume : Measure (Fin d → ℝ)))
    (h₂ : MemLp (fun x : Fin d → ℝ => waveDirDeriv v u₂ (t, x)) 2
      (volume : Measure (Fin d → ℝ))) :
    MemLp (fun x : Fin d → ℝ => waveDirDeriv v (fun q => u₁ q - u₂ q) (t, x)) 2
      (volume : Measure (Fin d → ℝ)) := by
  have heq : (fun x : Fin d → ℝ => waveDirDeriv v (fun q => u₁ q - u₂ q) (t, x))
      = fun x : Fin d → ℝ => waveDirDeriv v u₁ (t, x) - waveDirDeriv v u₂ (t, x) := by
    funext x
    exact waveDirDeriv_sub hu₁ hu₂ v (t, x)
  rw [heq]
  exact h₁.sub h₂

/-- **Square integrability of a spatial derivative of a slice passes to a difference.** -/
theorem memLp_two_coordPartial_slice_sub (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    {t : ℝ} {i : Fin d}
    (h₁ : MemLp (coordPartial i (slice u₁ t)) 2 (volume : Measure (Fin d → ℝ)))
    (h₂ : MemLp (coordPartial i (slice u₂ t)) 2 (volume : Measure (Fin d → ℝ))) :
    MemLp (coordPartial i (slice (fun q => u₁ q - u₂ q) t)) 2
      (volume : Measure (Fin d → ℝ)) := by
  rw [slice_sub, coordPartial_sub_fun (contDiff_slice hu₁ t) (contDiff_slice hu₂ t)]
  exact h₁.sub h₂

end Sub

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.PiMeasureAbsoluteContinuity

/-!
# The centred product Gaussian is invariant under signed permutations

A centred real Gaussian is invariant under sign reversal, and a product of identical factors is
invariant under permuting the coordinates.  Composing the two, the centred product Gaussian law on
a finite coefficient space is preserved by every signed permutation of the coordinates.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The centred product Gaussian law on a finite coefficient space. -/
def centredProductGaussian (ι : Type*) [Fintype ι] (v : NNReal) : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => gaussianReal 0 v

instance instIsProbabilityMeasureCentredProductGaussian (v : NNReal) :
    IsProbabilityMeasure (centredProductGaussian ι v) := by
  rw [centredProductGaussian]
  infer_instance

/-- A centred real Gaussian is invariant under sign reversal. -/
theorem gaussianReal_map_neg (v : NNReal) :
    (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
  have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := v) (-1)
  have hfun : (fun x : ℝ => (-1 : ℝ) * x) = fun x : ℝ => -x := by
    funext x
    ring
  rw [hfun] at h
  rw [h]
  norm_num

/-- Sign reversal on one coordinate preserves the centred Gaussian. -/
theorem measurePreserving_neg_gaussianReal (v : NNReal) :
    MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 v) (gaussianReal 0 v) :=
  ⟨measurable_neg, gaussianReal_map_neg v⟩

/-- Coordinatewise sign reversal. -/
def gaussianSignFlip (ε : ι → ℝ) : (ι → ℝ) → (ι → ℝ) := fun J i => ε i * J i

theorem measurePreserving_gaussianSignFlip {ε : ι → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) (v : NNReal) :
    MeasurePreserving (gaussianSignFlip ε) (centredProductGaussian ι v) (centredProductGaussian ι v) := by
  classical
  refine measurePreserving_pi (fun _ : ι => gaussianReal 0 v) (fun _ : ι => gaussianReal 0 v)
    fun i => ?_
  show MeasurePreserving (fun x : ℝ => ε i * x) (gaussianReal 0 v) (gaussianReal 0 v)
  rcases hε i with h | h
  · have hfun : (fun x : ℝ => ε i * x) = fun x : ℝ => x := by
      funext x
      rw [h, one_mul]
    rw [hfun]
    exact MeasurePreserving.id _
  · have hfun : (fun x : ℝ => ε i * x) = fun x : ℝ => -x := by
      funext x
      rw [h]
      ring
    rw [hfun]
    exact measurePreserving_neg_gaussianReal v

/-- Coordinate permutation. -/
def permMap (π : Equiv.Perm ι) : (ι → ℝ) → (ι → ℝ) := fun J i => J (π i)

theorem measurePreserving_permMap (π : Equiv.Perm ι) (v : NNReal) :
    MeasurePreserving (permMap π) (centredProductGaussian ι v) (centredProductGaussian ι v) := by
  classical
  have h := measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 v) π.symm
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) π.symm) = permMap π := by
    funext J i
    show (Equiv.piCongrLeft (fun _ : ι => ℝ) π.symm) J i = J (π i)
    have hpt := Equiv.piCongrLeft_apply_apply (fun _ : ι => ℝ) π.symm J (π i)
    rw [Equiv.symm_apply_apply] at hpt
    exact hpt
  rw [hfun] at h
  exact h

/-- **Signed permutations preserve the centred product Gaussian.** -/
theorem measurePreserving_signedPerm (π : Equiv.Perm ι) {ε : ι → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (v : NNReal) :
    MeasurePreserving (fun J : ι → ℝ => fun i => ε i * J (π i))
      (centredProductGaussian ι v) (centredProductGaussian ι v) := by
  have h := (measurePreserving_gaussianSignFlip hε v).comp (measurePreserving_permMap π v)
  have hfun : (gaussianSignFlip ε ∘ permMap π) = fun J : ι → ℝ => fun i => ε i * J (π i) := by
    funext J i
    rfl
  rw [hfun] at h
  exact h

end GaloisForLFunctions.HTGeometry

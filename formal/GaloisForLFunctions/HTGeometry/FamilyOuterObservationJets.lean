import GaloisForLFunctions.HTGeometry.FamilyOuterObservation
import GaloisForLFunctions.HTGeometry.OuterCauchyOrbitBoundary

/-!
# The family observation reads the jets of the outer background

The observation of the mass parameter used by the transversality argument was built by charting the
Cauchy jet packet.  Here it is identified with what it is supposed to be: the derivatives, at the
evaluation points, of the real translates of the Cayley exponential of the Cauchy transform.

Three steps: the packet chart computes the jets of the composite, the Cauchy jet packet is the jets
of the Cauchy transform at the combined nodes, and a jet at a combined node is a jet of the
corresponding translate at the evaluation point.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The discrete mass attached to a bounded exponential mass parameter. -/
def massMeasure (x ε : ℕ → ℝ) (u : MassParameter) : Measure ℝ :=
  _root_.HTGeometry.countableWeightedDirac (fun n => ε n * Real.exp (u n)) x

/-- The outer background of a bounded exponential mass parameter: the Cayley exponential of the
Cauchy transform of its discrete mass. -/
def massOuterBackground (x ε : ℕ → ℝ) (u : MassParameter) : ℂ → ℂ :=
  outerBackground (massMeasure x ε u)

theorem isFiniteMeasure_massMeasure {x ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Summable ε)
    (u : MassParameter) : IsFiniteMeasure (massMeasure x ε u) :=
  isFiniteMeasure_countableWeightedDirac (x := x)
    (fun n => (mul_pos (hεpos n) (Real.exp_pos _)).le)
    (summable_expParameter (fun n => (hεpos n).le) hε u)

/-- The open upper half plane. -/
theorem isOpen_upperHalfSet : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

/-- **The outer background is smooth on the upper half plane and its Cauchy transform never meets
`-i` there.**  These are the two hypotheses the packet chart needs. -/
theorem contDiffOn_cauchyTransform_upper (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ContDiffOn ℂ (⊤ : ℕ∞) (cauchyTransform ν) {z : ℂ | 0 < z.im} :=
  fun _ hz => (contDiffAt_cauchyTransform ν (ne_of_gt hz)).contDiffWithinAt

theorem cauchyTransform_add_I_ne_zero_upper (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∀ z ∈ {z : ℂ | 0 < z.im}, cauchyTransform ν z + Complex.I ≠ 0 := fun _ hz =>
  add_I_ne_zero_of_im_nonneg (im_cauchyTransform_nonneg ν hz)

/-- **The family observation is the jet packet of the translated outer backgrounds.**  Its
`(b, j)` entry is the `k`-th derivative at the evaluation point `z b` of the translate by `t i`,
where `(i, k)` is the pair the folded index `j` encodes. -/
theorem familyOuterObservation_apply {row : Type*} (r d D : ℕ) (h : r * (d + 1) = D)
    (z : row → ℂ) (t : Fin r → ℝ) (hupper : ∀ b, 0 < (z b).im) (x : ℕ → ℝ) {ε : ℕ → ℝ}
    (hεpos : ∀ n, 0 < ε n) (hε : Summable ε) (u : MassParameter) (b : row) (j : Fin D) :
    familyOuterObservation r d D h z t x ε u (b, j)
      = iteratedDeriv ((finProdFinEquiv.symm ((finCongr h).symm j)).2 : ℕ)
        (fun w => massOuterBackground x ε u
          (w + (t (finProdFinEquiv.symm ((finCongr h).symm j)).1 : ℂ))) (z b) := by
  haveI := isFiniteMeasure_massMeasure (x := x) hεpos hε u
  set i := (finProdFinEquiv.symm ((finCongr h).symm j)).1 with hi
  set k := (finProdFinEquiv.symm ((finCongr h).symm j)).2 with hk
  have hcU : combinedNodes z t (b, i) ∈ {ζ : ℂ | 0 < ζ.im} := by
    show 0 < (combinedNodes z t (b, i)).im
    rw [im_combinedNodes]
    exact hupper b
  have hchart := chiJetPacket_iteratedDeriv (f := cauchyTransform (massMeasure x ε u))
    (U := {ζ : ℂ | 0 < ζ.im}) isOpen_upperHalfSet
    (contDiffOn_cauchyTransform_upper _) (cauchyTransform_add_I_ne_zero_upper _) hcU d k
  have hobs : familyOuterObservation r d D h z t x ε u (b, j)
      = chiJetPacket d (fun k' : Fin (d + 1) => iteratedDeriv (k' : ℕ)
          (cauchyTransform (massMeasure x ε u)) (combinedNodes z t (b, i))) k := rfl
  rw [hobs, hchart, iteratedDeriv_translate]
  rfl

end

end GaloisForLFunctions.HTGeometry

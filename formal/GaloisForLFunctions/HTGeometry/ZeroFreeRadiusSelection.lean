import GaloisForLFunctions.HTGeometry.LogDerivProximityBound

/-!
# A radius whose circle carries no zero

The zeros of a nonzero entire function inside a compact disc are finitely many, so their moduli form
a finite set of radii.  Every interval of positive length therefore contains a radius whose circle is
free of zeros — which is exactly the hypothesis under which the logarithmic-derivative estimate is
stated.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric MeromorphicOn

/-- The divisor of an entire function vanishes at a point where the function does not. -/
theorem divisor_eq_zero_at_of_ne_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g) {U : Set ℂ} {u : ℂ}
    (hu : u ∈ U) (hne : g u ≠ 0) : MeromorphicOn.divisor g U u = 0 := by
  rw [MeromorphicOn.divisor_apply (fun w _ => (hg.analyticAt w).meromorphicAt) hu]
  have hA : AnalyticAt ℂ g u := hg.analyticAt u
  rw [hA.meromorphicOrderAt_eq, hA.analyticOrderAt_eq_zero.mpr hne]
  simp

/-- **A zero-free circle in every interval of radii.** -/
theorem exists_radius_divisor_sphere_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (horder : ∀ z : ℂ, meromorphicOrderAt g z ≠ ⊤) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ R ∈ Set.Icc a b, ∀ u ∈ sphere (0 : ℂ) |R|,
      MeromorphicOn.divisor g (closedBall (0 : ℂ) |R|) u = 0 := by
  classical
  set D := MeromorphicOn.divisor g (closedBall (0 : ℂ) |b|) with hD
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall (0 : ℂ) |b|)
  set S : Set ℝ := (fun u : ℂ => ‖u‖) '' D.support with hS
  have hSfin : S.Finite := hfin.image _
  have hsub : ¬ (Set.Icc a b ⊆ S) := by
    intro hcon
    exact (Set.Icc_infinite hab) (hSfin.subset hcon)
  obtain ⟨R, hRmem, hRnot⟩ := Set.not_subset.mp hsub
  refine ⟨R, hRmem, ?_⟩
  intro u hu
  have hRpos : 0 < R := lt_of_lt_of_le ha hRmem.1
  have hunorm : ‖u‖ = R := by
    rw [mem_sphere_iff_norm, sub_zero] at hu
    rw [hu, abs_of_pos hRpos]
  have hne : g u ≠ 0 := by
    intro hzero
    refine hRnot ?_
    rw [hS]
    refine ⟨u, ?_, hunorm⟩
    have hub : u ∈ closedBall (0 : ℂ) |b| := by
      rw [mem_closedBall_zero_iff, hunorm, abs_of_pos (lt_trans ha hab)]
      exact hRmem.2
    have hDu : D u ≠ 0 := by
      intro hzero'
      refine (ne_zero_of_divisor_eq_zero hg horder
        (fun w _ => (hg.analyticAt w).meromorphicAt) hub ?_) hzero
      rw [← hD]
      exact hzero'
    exact Function.mem_support.mpr hDu
  refine divisor_eq_zero_at_of_ne_zero hg ?_ hne
  rw [mem_closedBall_zero_iff, hunorm, abs_of_pos hRpos]

end GaloisForLFunctions.HTGeometry

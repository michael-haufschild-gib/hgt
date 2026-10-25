import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WeilEnergyIsUnboundedAtEveryAperture

/-!
# Ampleness requires faithful primitive readings

A source-effective class of ample degree zero has both fibre degrees zero. Thus ampleness
holds exactly when every source with nonpositive reserve lies in the defect radical.
Normalized finite-dimensional readings fail this condition at every positive aperture:
their kernels contain sources of positive Weil energy.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- Ampleness detects precisely whether unpaid primitive sources are numerically trivial. -/
theorem sourceCone_ample_iff_defect_radical {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.AmpleAxiom (S.sourceCone Φ) ↔
      ∀ x : C, Φ x ≤ 0 → ∀ y : C, S.defect x y = 0 := by
  constructor
  · intro hA x hx y
    have hmem : S.withFibreDegrees x 0 0 ∈ S.sourceCone Φ := by
      rw [S.mem_sourceCone_iff, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V,
        S.source_withFibreDegrees hfib, S.polar_self,
        S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
      exact ⟨le_rfl, le_rfl, by simpa only [mul_zero] using hx⟩
    have hdeg : S.pair (S.withFibreDegrees x 0 0) S.ample = 0 := by
      rw [S.pair_ample, S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V, add_zero]
    have h := hA _ hmem hdeg (S.withFibreDegrees y 0 0)
    rw [S.pair_withFibreDegrees] at h
    linarith only [h]
  · intro h x hx hdeg y
    obtain ⟨hxH, hxV, hxΦ⟩ := (S.mem_sourceCone_iff Φ x).mp hx
    rw [S.pair_ample] at hdeg
    have hH : S.pair x S.H = 0 := by linarith only [hxH, hxV, hdeg]
    have hV : S.pair x S.V = 0 := by linarith only [hxH, hxV, hdeg]
    have hΦ : Φ x ≤ 0 := by
      simpa only [S.polar_self, hH, hV, mul_zero] using hxΦ
    have hxy := h x hΦ y
    simp only [defect, polar, hH, hV, zero_mul, zero_add] at hxy
    linarith only [hxy]

end PolarSurface

/-- A normalized finite linear reading misses effective, nontrivial classes of ample degree zero. -/
theorem normalizedFiniteLinearReadingSourceCone_not_ample {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) (F : V → ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).AmpleAxiom
      ((scalingSubsurface (realTestsAt r)).sourceCone
        (fun x => F (L x.2.2) - F 0)) := by
  let Φ : (ℝ × ℝ × realTestsAt r) → ℝ := fun x => F (L x.2.2) - F 0
  have hfib : ∀ (x : ℝ × ℝ × realTestsAt r) (a b : ℝ),
      Φ (x + a • (scalingSubsurface (realTestsAt r)).H +
        b • (scalingSubsurface (realTestsAt r)).V) = Φ x := by
    intro x a b
    simp [Φ, scalingSubsurface, scalingSurface]
  intro hA
  obtain ⟨f, hW, hker⟩ := exists_realTestAt_in_ker_weilPair_gt hr 0 L
  have hΦ : Φ (0, 0, f) ≤ 0 := by
    dsimp only [Φ]
    rw [hker, sub_self]
  have h := ((scalingSubsurface (realTestsAt r)).sourceCone_ample_iff_defect_radical
    hfib).mp hA (0, 0, f) hΦ (0, 0, f)
  rw [scalingSubsurface_defect_self] at h
  linarith only [h, hW]

/-- Both intersection axioms fail for every normalized finite-dimensional source reading. -/
theorem normalizedFiniteLinearReadingSourceCone_not_ample_and_not_bezout
    {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) (F : V → ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).AmpleAxiom
        ((scalingSubsurface (realTestsAt r)).sourceCone (fun x => F (L x.2.2) - F 0)) ∧
      ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom
        ((scalingSubsurface (realTestsAt r)).sourceCone (fun x => F (L x.2.2) - F 0)) :=
  ⟨normalizedFiniteLinearReadingSourceCone_not_ample hr L F,
    finiteLinearReadingSourceCone_not_bezout hr L (fun v => F v - F 0)⟩

/-- Allowing signed fibre degrees does not repair the finite-reading ampleness failure. -/
theorem normalizedFiniteLinearReadingGradedSourceCone_not_ample {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) (F : V → ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).AmpleAxiom
      ((scalingSubsurface (realTestsAt r)).gradedSourceCone
        (fun x => F (L x.2.2) - F 0)) := by
  intro hA
  apply normalizedFiniteLinearReadingSourceCone_not_ample hr L F
  intro x hx
  exact hA x ((scalingSubsurface (realTestsAt r)).sourceCone_subset_gradedSourceCone _ hx)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface.sourceCone_ample_iff_defect_radical
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.normalizedFiniteLinearReadingSourceCone_not_ample_and_not_bezout
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.normalizedFiniteLinearReadingGradedSourceCone_not_ample

import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ExactArithmeticSourceEffectivity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteDegreeConesCannotSatisfyBezout

/-!
# Exact arithmetic effectivity cannot be read from finitely many linear degrees

Every finite-reading fibre contains negative-square classes. The exact arithmetic cone equals
the positive cone, so no finite readings force its membership, even at an effective class.
This obstruction is unconditional and does not assume Bézout for the exact source cone.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- On the original surface, arbitrarily small source changes preserve finite readings while driving the square down. -/
theorem scalingSurface_self_pair_unbounded_below_with_small_source_mass
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : ScalingCycle →ₗ[ℝ] V) (x : ScalingCycle) (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ScalingCycle, L y = L x ∧
      scalingSurface.pair y scalingSurface.H = scalingSurface.pair x scalingSurface.H ∧
      scalingSurface.pair y scalingSurface.V = scalingSurface.pair x scalingSurface.V ∧
      (∫ u : ℝ, (y.2.2.1 u - x.2.2.1 u) ^ 2) < ε ∧
      scalingSurface.pair y y < M := by
  obtain ⟨r, hr, hf⟩ := exists_pos_aperture_of_realTest x.2.2
  let e := scalingSubsurfaceInclusion (realTestsAt r)
  let X : ℝ × ℝ × realTestsAt r := (x.1, x.2.1, ⟨x.2.2, hf⟩)
  obtain ⟨y, hy, hH, hV, hm, hyy⟩ :=
    scalingSubsurface_self_pair_unbounded_below_with_small_source_mass hr (L.comp e) X M hε
  exact ⟨e y, hy, hH, hV, hm, hyy⟩

/-- Exact arithmetic effectivity has no source-mass neighbourhood, even with finite readings and both degrees fixed. -/
theorem exists_same_finite_readings_small_mass_not_exactArithmeticEffective
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : ScalingCycle →ₗ[ℝ] V) (x : ScalingCycle) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ScalingCycle, L y = L x ∧
      scalingSurface.pair y scalingSurface.H = scalingSurface.pair x scalingSurface.H ∧
      scalingSurface.pair y scalingSurface.V = scalingSurface.pair x scalingSurface.V ∧
      (∫ u : ℝ, (y.2.2.1 u - x.2.2.1 u) ^ 2) < ε ∧
      y ∉ globalExactArithmeticSourceCone := by
  obtain ⟨y, hy, hH, hV, hm, hyy⟩ :=
    scalingSurface_self_pair_unbounded_below_with_small_source_mass L x 0 hε
  refine ⟨y, hy, hH, hV, hm, ?_⟩
  intro he
  rw [globalExactArithmeticSourceCone_eq_positiveCone] at he
  exact (not_lt_of_ge he.1) hyy

/-- Every finite-reading fibre contains a class outside the exact arithmetic source cone. -/
theorem exists_same_finite_readings_not_exactArithmeticEffective
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : ScalingCycle →ₗ[ℝ] V) (x : ScalingCycle) :
    ∃ y : ScalingCycle, L y = L x ∧ y ∉ globalExactArithmeticSourceCone := by
  obtain ⟨y, hy, hyy⟩ :=
    scalingSurface_self_pair_unbounded_below_on_finite_reading_fibre L x 0
  refine ⟨y, hy, ?_⟩
  intro he
  rw [globalExactArithmeticSourceCone_eq_positiveCone] at he
  exact (not_lt_of_ge he.1) hyy

/-- The exact arithmetic RR cone has no finite-dimensional linear degree description. -/
theorem globalExactArithmeticSourceCone_not_finiteLinearReading
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : ScalingCycle →ₗ[ℝ] V) :
    ¬ ∃ A : Set V, globalExactArithmeticSourceCone = L ⁻¹' A := by
  rintro ⟨A, hA⟩
  have hAA : scalingSurface.pair scalingSurface.ample scalingSurface.ample = 2 := by
    simp only [PolarSurface.ample, map_add, LinearMap.add_apply,
      scalingSurface.pair_H_H, scalingSurface.pair_V_H,
      scalingSurface.pair_H_V, scalingSurface.pair_V_V]
    norm_num
  have he : scalingSurface.ample ∈ globalExactArithmeticSourceCone := by
    rw [globalExactArithmeticSourceCone_eq_positiveCone]
    exact ⟨by rw [hAA]; norm_num, by rw [hAA]; norm_num⟩
  obtain ⟨y, hy, hye⟩ :=
    exists_same_finite_readings_not_exactArithmeticEffective L scalingSurface.ample
  apply hye
  rw [hA] at he ⊢
  change L y ∈ A
  rw [hy]
  exact he

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

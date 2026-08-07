import GaloisForLFunctions.HTGeometry.RadialAnalyticZeroSetNullLaw
import GaloisForLFunctions.HTGeometry.RegularLevelSetHausdorffDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Observer critical-carrier confinement

A single observer-Jacobian minor that is nonzero at one reference point controls
all exact targets at once.  If that minor is radially analytic, its zero set is
volume-null.  Outside it the observer differential is surjective, so every
exact target fibre has the full observer codimension.

This is a target-independent replacement for a union of target-by-target
transversality statements.  It also identifies the quantitative successor:
lower tails of this observer minor, rather than the minimum spectral gap.
-/

open MeasureTheory Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The square observer minor obtained by evaluating a differential on selected
coefficient directions. -/
def observerMinor
    {m v : ℕ}
    (D : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin v))
    (u : Fin v → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) : Matrix (Fin v) (Fin v) ℝ :=
  fun i j => D x (u j) i

/-- A nonzero selected observer minor is an explicit right-inverse certificate
for the complete observer differential. -/
theorem observerMinor_surjective_of_det_ne_zero
    {m v : ℕ}
    {D : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin v)}
    {u : Fin v → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hdet : (observerMinor D u x).det ≠ 0) :
    Function.Surjective (D x) := by
  classical
  intro y
  let A := observerMinor D u x
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  let c : Fin v → ℝ := A⁻¹.mulVec y
  refine ⟨∑ j, c j • u j, ?_⟩
  have hmap : D x (∑ j, c j • u j) = A.mulVec c := by
    ext i
    simp [A, observerMinor, Matrix.mulVec, dotProduct, mul_comm]
  have hc : A.mulVec c = y := by
    change A.mulVec (A⁻¹.mulVec (y : Fin v → ℝ)) = (y : Fin v → ℝ)
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit]
    simp
  ext i
  exact congrFun (hmap.trans hc) i

/-- **Universal critical-locus nullity.**  One radially analytic full-rank
observer minor makes the rank-deficient locus volume-null.  No union over
targets occurs. -/
theorem observerMinor_criticalSet_volume_zero
    {m v : ℕ}
    {D : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin v)}
    {u : Fin v → EuclideanSpace ℝ (Fin m)}
    (hmeas : Measurable fun x => (observerMinor D u x).det)
    (hran : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      AnalyticOnNhd ℝ
        (fun r : ℝ => (observerMinor D u (r • (ω : EuclideanSpace ℝ (Fin m)))).det)
        univ)
    (hdet0 : (observerMinor D u 0).det ≠ 0) :
    volume {x | ¬Function.Surjective (D x)} = 0 := by
  apply measure_mono_null (t := {x | (observerMinor D u x).det = 0})
  · intro x hx
    by_contra hne
    exact hx (observerMinor_surjective_of_det_ne_zero hne)
  · exact volume_zero_zeroSet_of_radial_analytic hmeas hran hdet0

/-- The same universal critical locus is null for the standard Gaussian
coefficient ensemble. -/
theorem observerMinor_criticalSet_stdGaussian_zero
    {m v : ℕ}
    {D : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin v)}
    {u : Fin v → EuclideanSpace ℝ (Fin m)}
    (hmeas : Measurable fun x => (observerMinor D u x).det)
    (hran : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      AnalyticOnNhd ℝ
        (fun r : ℝ => (observerMinor D u (r • (ω : EuclideanSpace ℝ (Fin m)))).det)
        univ)
    (hdet0 : (observerMinor D u 0).det ≠ 0) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {x | ¬Function.Surjective (D x)} = 0 := by
  rw [stdGaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _
    (observerMinor_criticalSet_volume_zero hmeas hran hdet0)

end

end GaloisForLFunctions.HTGeometry

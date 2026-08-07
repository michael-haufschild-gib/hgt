import GaloisForLFunctions.HTGeometry.RadialAnalyticZeroSetNullLaw
import GaloisForLFunctions.HTGeometry.RegularLevelSetHausdorffDimension
import GaloisForLFunctions.HTGeometry.RegularLevelSetStratification
import Mathlib.Analysis.Calculus.FDeriv.Analytic
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

open MeasureTheory ProbabilityTheory Metric Set
open scoped BigOperators

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

/-- Analyticity of an endpoint map automatically propagates through its
differential, selected observer entries, and determinant. -/
theorem analyticOnNhd_observerMinor_fderiv
    {m v : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin v)}
    (hF : AnalyticOnNhd ℝ F univ)
    (u : Fin v → EuclideanSpace ℝ (Fin m)) :
    AnalyticOnNhd ℝ
      (fun x => (observerMinor (fun z => fderiv ℝ F z) u x).det) univ := by
  classical
  have hDf : AnalyticOnNhd ℝ (fderiv ℝ F) univ := hF.fderiv
  have hentry : ∀ i j : Fin v,
      AnalyticOnNhd ℝ
        (fun x => observerMinor (fun z => fderiv ℝ F z) u x i j) univ := by
    intro i j
    let ev : EuclideanSpace ℝ (Fin v) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin v => ℝ)).toContinuousLinearMap
    have happly : AnalyticOnNhd ℝ
        (fun x => (fderiv ℝ F x) (u j)) univ :=
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin v)) (u j)).comp_analyticOnNhd hDf
    have hev := ev.comp_analyticOnNhd happly
    convert hev using 1
    ext x
    rfl
  have hexp :
      (fun x => (observerMinor (fun z => fderiv ℝ F z) u x).det) =
        fun x => ∑ σ : Equiv.Perm (Fin v),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ i, observerMinor (fun z => fderiv ℝ F z) u x (σ i) i := by
    funext x
    simpa using Matrix.det_apply' (observerMinor (fun z => fderiv ℝ F z) u x)
  rw [hexp]
  have hterm : ∀ σ : Equiv.Perm (Fin v),
      AnalyticOnNhd ℝ
        (fun x => (Equiv.Perm.sign σ : ℝ) *
          ∏ i, observerMinor (fun z => fderiv ℝ F z) u x (σ i) i) univ := by
    intro σ
    have hp : AnalyticOnNhd ℝ
        (∏ i, fun x => observerMinor (fun z => fderiv ℝ F z) u x (σ i) i) univ :=
      Finset.analyticOnNhd_prod _ fun i _ => hentry (σ i) i
    have hp' : AnalyticOnNhd ℝ
        (fun x => ∏ i, observerMinor (fun z => fderiv ℝ F z) u x (σ i) i) univ := by
      convert hp using 1
      ext x
      simp
    exact analyticOnNhd_const.mul hp'
  have hsum : AnalyticOnNhd ℝ
      (∑ σ : Equiv.Perm (Fin v), fun x => (Equiv.Perm.sign σ : ℝ) *
        ∏ i, observerMinor (fun z => fderiv ℝ F z) u x (σ i) i) univ :=
    Finset.analyticOnNhd_sum _ fun σ _ => hterm σ
  convert hsum using 1
  ext x
  simp

/-- **Analytic observer critical-set law.**  For an analytic endpoint map, one
nonzero observer minor at the origin forces surjectivity almost everywhere. -/
theorem analytic_observer_criticalSet_volume_zero
    {m v : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin v)}
    (hF : AnalyticOnNhd ℝ F univ)
    (u : Fin v → EuclideanSpace ℝ (Fin m))
    (hdet0 : (observerMinor (fun z => fderiv ℝ F z) u 0).det ≠ 0) :
    volume {x | ¬Function.Surjective (fderiv ℝ F x)} = 0 := by
  have hminor := analyticOnNhd_observerMinor_fderiv hF u
  apply observerMinor_criticalSet_volume_zero hminor.continuous.measurable
  · intro ω
    have hray : AnalyticOnNhd ℝ
        (fun r : ℝ => r • (ω : EuclideanSpace ℝ (Fin m))) univ :=
      analyticOnNhd_id.smul analyticOnNhd_const
    simpa [Function.comp_def] using hminor.comp hray (mapsTo_univ _ _)
  · exact hdet0

/-- The analytic observer critical-set law for the standard Gaussian
coefficient ensemble. -/
theorem analytic_observer_criticalSet_stdGaussian_zero
    {m v : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin v)}
    (hF : AnalyticOnNhd ℝ F univ)
    (u : Fin v → EuclideanSpace ℝ (Fin m))
    (hdet0 : (observerMinor (fun z => fderiv ℝ F z) u 0).det ≠ 0) :
    stdGaussian (EuclideanSpace ℝ (Fin m))
      {x | ¬Function.Surjective (fderiv ℝ F x)} = 0 := by
  rw [stdGaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _
    (analytic_observer_criticalSet_volume_zero hF u hdet0)

/-- Every exact target fibre of a smooth observer endpoint has full observer
codimension on its regular locus. -/
theorem observer_regularFiber_isLocalRegularLevelSet
    {m v : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin v)}
    (hF : ContDiff ℝ ⊤ F)
    (y : EuclideanSpace ℝ (Fin v)) :
    IsLocalRegularLevelSetOfCodimAtLeast
      ({x | F x = y} ∩ {x | Function.Surjective (fderiv ℝ F x)}) v := by
  let g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin v) := fun x => F x - y
  have hg : ContDiff ℝ ⊤ g := hF.sub contDiff_const
  have hO : IsOpen {x | Function.Surjective (fderiv ℝ F x)} :=
    isOpen_surjectiveContinuousLinearMapLocus.preimage
      (hF.continuous_fderiv (by simp))
  have hreg := isLocalRegularLevelSetOfCodimAtLeast_zeroSet_inter_isOpen_finiteDimensional
    (c := v) g (by simp) hg hO (by
      intro x _ hxO
      simpa [g, fderiv_sub_const] using hxO)
  simpa [g, sub_eq_zero] using hreg

/-- Every exact target carrier outside the common critical locus has Hausdorff
dimension at most parameter dimension minus observer dimension. -/
theorem observer_exactCarrier_dimH_le
    {m v : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin v)}
    (hF : ContDiff ℝ ⊤ F)
    (y : EuclideanSpace ℝ (Fin v))
    {M : Set (EuclideanSpace ℝ (Fin m))}
    (hM : M ⊆ {x | F x = y} ∩ {x | Function.Surjective (fderiv ℝ F x)}) :
    dimH M ≤ (m - v : ℕ) := by
  have hfiber := dimH_le_finrank_sub_of_isLocalRegularLevelSetOfCodimAtLeast
    (observer_regularFiber_isLocalRegularLevelSet hF y)
  exact (dimH_mono hM).trans (by simpa using hfiber)

/-- **Universal exact-carrier confinement law.**  A single full-rank analytic
jet produces one Gaussian-null critical set, independent of target, and every
exact target carrier on its complement obeys the sharp observer-codimension
bound. -/
theorem analytic_observer_universal_exactCarrierLaw
    {m v : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin v)}
    (hF : AnalyticOnNhd ℝ F univ)
    (u : Fin v → EuclideanSpace ℝ (Fin m))
    (hdet0 : (observerMinor (fun z => fderiv ℝ F z) u 0).det ≠ 0) :
    stdGaussian (EuclideanSpace ℝ (Fin m))
        {x | ¬Function.Surjective (fderiv ℝ F x)} = 0 ∧
      ∀ (y : EuclideanSpace ℝ (Fin v))
        (M : Set (EuclideanSpace ℝ (Fin m))),
        M ⊆ {x | F x = y} ∩ {x | Function.Surjective (fderiv ℝ F x)} →
        dimH M ≤ (m - v : ℕ) := by
  refine ⟨analytic_observer_criticalSet_stdGaussian_zero hF u hdet0, ?_⟩
  intro y M hM
  exact observer_exactCarrier_dimH_le hF.contDiff y hM

end

end GaloisForLFunctions.HTGeometry

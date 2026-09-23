import GaloisForLFunctions.HTGeometry.BoundedTargetDOptimalIncidenceLaw
import GaloisForLFunctions.RHTower.StaticChoiOperatorCovarianceFirstEntryLaw

open Filter MeasureTheory Matrix Set ProbabilityTheory
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A uniform one-target moment bound over an arbitrary bounded occupied
family excludes every continuous post-ramp re-entry once its dimension budget
falls below one Gaussian time cell. -/
theorem no_second_capture_of_boundedDOptimalMoment
    {C : Type*} [Nonempty C] {n : ℕ}
    (D : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ) → ℝ)
    (psi : ℝ → Fin (n + 1) → ℂ)
    (target : C → Fin (n + 1) → ℂ)
    {speed epsn epsw T threshold : ℝ}
    (hspeed : 0 < speed) (hTpos : 0 < T)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hT : epsw / speed ≤ T) (hthreshold : 0 < threshold)
    (htriangle : ∀ t u c,
      D (psi t) (target c) ≤ D (psi t) (psi u) + D (psi u) (target c))
    (hLip : ∀ t u, D (psi t) (psi u) ≤ speed * |t - u|)
    (hfidelity : ∀ t c, D (psi t) (target c) ≤ epsw →
      threshold ≤ finitePureStateFidelity (psi t) (target c))
    (hbounded : Bornology.IsBounded (Set.range target))
    (hspan : Submodule.span ℂ (Set.range target) = ⊤)
    (hprod : ∀ i j, Integrable
      (fun x ↦ psi (T * x) i * star (psi (T * x) j))
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ))
    (q : ℝ)
    (hmoment : ∀ c, ∫ x,
      ‖finiteComplexInner (psi (T * x)) (target c)‖ ^ (2 : ℕ)
        ∂((gaussianReal 0 1).restrict
          (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ) ≤ q)
    (hbudget : (n + 1 : ℝ) * q <
      threshold *
        (gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)))) :
    ¬ ∃ t ∈ Icc
        (epsw / speed + (epsw - epsn) / speed) T,
      ∃ c, D (psi t) (target c) ≤ epsn := by
  let mu := (gaussianReal 0 1).restrict
    (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ
  let state : ℝ → Fin (n + 1) → ℂ := fun x ↦ psi (T * x)
  have hcapture := boundedTarget_completeCapture_le_dim_mul_worstRayMoment
    mu target state threshold hthreshold hbounded hspan hprod q hmoment
  have hevent :
      finitePositiveReporterCaptureEvent target state threshold =
        {x | ∃ c, threshold ≤
          finitePureStateFidelity (psi (T * x)) (target c)} := by
    ext x
    simp only [finitePositiveReporterCaptureEvent, finitePureStateFidelity,
      state, Set.mem_setOf_eq]
  have hmeasure :
      mu.real {x | ∃ c, threshold ≤
          finitePureStateFidelity (psi (T * x)) (target c)} <
        gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)) := by
    rw [← hevent]
    nlinarith
  exact no_second_capture_of_returnExcised_gaussianMeasure_lt
    D psi target hspeed hTpos hepsn hgap hT htriangle hLip hfidelity
      (by simpa [mu] using hmeasure)

end

end RHTower

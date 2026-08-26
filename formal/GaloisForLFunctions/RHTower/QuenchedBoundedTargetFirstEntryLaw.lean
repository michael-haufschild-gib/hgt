import GaloisForLFunctions.HTGeometry.QuenchedBoundedTargetDOptimalIncidenceLaw
import GaloisForLFunctions.RHTower.StaticChoiOperatorCovarianceFirstEntryLaw

open Filter MeasureTheory Matrix Set ProbabilityTheory
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Annealed one-target moments bound the probability, over one quenched draw,
of any continuous post-ramp re-entry into an arbitrary bounded target
continuum. -/
theorem measure_draws_with_boundedTarget_postRampReentry_le
    {Y C : Type*} [MeasurableSpace Y] [Nonempty C] {n : ℕ}
    (nu : Measure Y) [IsProbabilityMeasure nu]
    (D : Y → (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ) → ℝ)
    (psi : Y → ℝ → Fin (n + 1) → ℂ)
    (target : C → Fin (n + 1) → ℂ)
    {speed epsn epsw T threshold : ℝ}
    (hspeed : 0 < speed) (hTpos : 0 < T)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hT : epsw / speed ≤ T) (hthreshold : 0 < threshold)
    (htriangle : ∀ y t u c,
      D y (psi y t) (target c) ≤
        D y (psi y t) (psi y u) + D y (psi y u) (target c))
    (hLip : ∀ y t u,
      D y (psi y t) (psi y u) ≤ speed * |t - u|)
    (hfidelity : ∀ y t c, D y (psi y t) (target c) ≤ epsw →
      threshold ≤ finitePureStateFidelity (psi y t) (target c))
    (hbounded : Bornology.IsBounded (Set.range target))
    (hspan : Submodule.span ℂ (Set.range target) = ⊤)
    (hprodJoint : ∀ i j, Integrable
      (fun p : Y × ℝ ↦
        psi p.1 (T * p.2) i * star (psi p.1 (T * p.2) j))
      (nu.prod ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ)))
    (hprodSection : ∀ y i j, Integrable
      (fun x ↦ psi y (T * x) i * star (psi y (T * x) j))
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ))
    (hmeasCapture : Measurable (fun y ↦
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ).real
        (finitePositiveReporterCaptureEvent target
          (fun x ↦ psi y (T * x)) threshold)))
    (q : ℝ)
    (hmomentJoint : ∀ c, ∫ p : Y × ℝ,
      ‖finiteComplexInner (psi p.1 (T * p.2)) (target c)‖ ^ 2
        ∂(nu.prod ((gaussianReal 0 1).restrict
          (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ)) ≤ q) :
    nu.real {y | ∃ t ∈ Icc
        (epsw / speed + (epsw - epsn) / speed) T,
      ∃ c, D y (psi y t) (target c) ≤ epsn} ≤
      ((n + 1 : ℝ) * q) /
        (threshold *
          (gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)))) := by
  let mu := (gaussianReal 0 1).restrict
    (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ
  let state : Y → ℝ → Fin (n + 1) → ℂ :=
    fun y x ↦ psi y (T * x)
  let cell := gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T))
  have hcell : 0 < cell := by
    dsimp [cell]
    exact mul_pos gaussianFloorTwo_pos
      (div_pos (div_pos (sub_pos.mpr hgap) hspeed) (by positivity))
  have hmu : mu.real Set.univ ≤ 1 := by
    have hgauss : (gaussianReal 0 1).real
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ ≤ 1 :=
      measureReal_le_one
    simp [mu] at hgauss ⊢
  have hbad := measure_draws_with_large_boundedTargetCapture_le
    nu mu hmu target state threshold hthreshold hbounded hspan
      hprodJoint hprodSection hmeasCapture q hmomentJoint
      (threshold * cell) (mul_pos hthreshold hcell)
  have hsubset :
      {y | ∃ t ∈ Icc
          (epsw / speed + (epsw - epsn) / speed) T,
        ∃ c, D y (psi y t) (target c) ≤ epsn} ⊆
      {y | threshold * cell ≤ threshold *
        mu.real (finitePositiveReporterCaptureEvent
          target (state y) threshold)} := by
    intro y hy
    by_contra hnot
    have hmeasure :
        mu.real (finitePositiveReporterCaptureEvent
          target (state y) threshold) < cell := by
      change ¬ threshold * cell ≤ threshold *
        mu.real (finitePositiveReporterCaptureEvent
          target (state y) threshold) at hnot
      have hstrict := lt_of_not_ge hnot
      nlinarith
    have hevent :
        finitePositiveReporterCaptureEvent target (state y) threshold =
          {x | ∃ c, threshold ≤
            finitePureStateFidelity (psi y (T * x)) (target c)} := by
      ext x
      simp only [finitePositiveReporterCaptureEvent, finitePureStateFidelity,
        state, Set.mem_setOf_eq]
    have hno := no_second_capture_of_returnExcised_gaussianMeasure_lt
      (D y) (psi y) target hspeed hTpos hepsn hgap hT
        (htriangle y) (hLip y) (hfidelity y)
        (by simpa [mu, cell, hevent] using hmeasure)
    exact hno hy
  exact (measureReal_mono hsubset).trans (by simpa [mu, state, cell] using hbad)

end

end RHTower

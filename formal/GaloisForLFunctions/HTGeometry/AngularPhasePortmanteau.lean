/-
# Portmanteau for the joint angular-phase laws

Weak convergence of the joint angular-phase laws, packaged as convergence of probability measures,
gives the card's Portmanteau step: the upper limit in time of the joint law of a closed set is at
most its product-law value.  The easy-circuit tube of Theorem C is exactly such a closed set, so
this is the transport that turns the quenched incidence bound into a statement about physical time.

Main results:
* `anglePhaseLaw`, `angleProductLaw` — the joint law and its limit, as probability measures.
* `tendsto_anglePhaseLaw` — **weak convergence as probability measures**.
* `limsup_measure_closed_anglePhase` — **the Portmanteau upper bound on every closed set**.
* `limsup_measureReal_preimage_anglePhase` — the same in the pullback form the card uses.
-/
import GaloisForLFunctions.HTGeometry.AngularPhaseLaw

open Filter Topology MeasureTheory Metric

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance isProbabilityMeasureCirclePortmanteau :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

/-- The joint angular-phase law at time `t`, as a probability measure. -/
def anglePhaseLaw (hN : 0 < N) (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D) (t : ℝ) :
    ProbabilityMeasure (coeffSphere N × UnitAddTorus (phaseIndex i₀)) :=
  ⟨Measure.map (anglePhaseMap hP i₀ t) (sphereLaw N), by
    haveI := isProbabilityMeasure_sphereLaw hN
    constructor
    rw [Measure.map_apply (measurable_anglePhaseMap hP i₀ t) MeasurableSet.univ,
      Set.preimage_univ]
    exact measure_univ⟩

/-- The limit law: the fixed-shell law times Haar measure on the phase torus. -/
def angleProductLaw (hN : 0 < N) (D : ℕ) (i₀ : Fin D) :
    ProbabilityMeasure (coeffSphere N × UnitAddTorus (phaseIndex i₀)) :=
  ⟨(sphereLaw N).prod volume, by
    haveI := isProbabilityMeasure_sphereLaw hN
    infer_instance⟩

/-- **Weak convergence of the joint angular-phase laws, as probability measures.** -/
theorem tendsto_anglePhaseLaw (hN : 0 < N) (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (hRL : ∀ a : Fin D → ℝ, (∑ i, a i = 0) → a ≠ 0 →
      ∀ g : coeffSphere N → ℂ, Measurable g → ∀ C : ℝ, 0 ≤ C → (∀ x, ‖g x‖ ≤ C) →
        Tendsto (fun s : ℝ => ∫ x, g x *
            Complex.exp (-((s * sortedSpectralAction hP a (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) (cocompact ℝ) (nhds 0)) :
    Tendsto (fun t : ℝ => anglePhaseLaw hN hP i₀ t) atTop (nhds (angleProductLaw hN D i₀)) := by
  haveI := isProbabilityMeasure_sphereLaw hN
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  have hcont := tendsto_integral_anglePhase hN hP i₀ hRL f.toContinuousMap
  have hleft : ∀ t : ℝ,
      (∫ y, f y ∂(anglePhaseLaw hN hP i₀ t : Measure _))
        = ∫ x, f.toContinuousMap (anglePhaseMap hP i₀ t x) ∂(sphereLaw N) := by
    intro t
    exact integral_map (measurable_anglePhaseMap hP i₀ t).aemeasurable
      f.continuous.aestronglyMeasurable
  simp only [hleft]
  exact hcont

/-- **The Portmanteau upper bound on every closed set.** -/
theorem limsup_measure_closed_anglePhase (hN : 0 < N) (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (hRL : ∀ a : Fin D → ℝ, (∑ i, a i = 0) → a ≠ 0 →
      ∀ g : coeffSphere N → ℂ, Measurable g → ∀ C : ℝ, 0 ≤ C → (∀ x, ‖g x‖ ≤ C) →
        Tendsto (fun s : ℝ => ∫ x, g x *
            Complex.exp (-((s * sortedSpectralAction hP a (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) (cocompact ℝ) (nhds 0))
    {A : Set (coeffSphere N × UnitAddTorus (phaseIndex i₀))} (hA : IsClosed A) :
    (atTop.limsup fun t : ℝ => (anglePhaseLaw hN hP i₀ t : Measure _) A)
      ≤ ((sphereLaw N).prod volume) A :=
  ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (tendsto_anglePhaseLaw hN hP i₀ hRL) hA

/-- The Portmanteau bound in the pullback form: the shell mass of the set of directions whose
rescaled phase enters a closed target is asymptotically at most the product mass of the target. -/
theorem limsup_measure_preimage_anglePhase (hN : 0 < N) (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (hRL : ∀ a : Fin D → ℝ, (∑ i, a i = 0) → a ≠ 0 →
      ∀ g : coeffSphere N → ℂ, Measurable g → ∀ C : ℝ, 0 ≤ C → (∀ x, ‖g x‖ ≤ C) →
        Tendsto (fun s : ℝ => ∫ x, g x *
            Complex.exp (-((s * sortedSpectralAction hP a (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) (cocompact ℝ) (nhds 0))
    {A : Set (coeffSphere N × UnitAddTorus (phaseIndex i₀))} (hA : IsClosed A) :
    (atTop.limsup fun t : ℝ => (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹' A))
      ≤ ((sphereLaw N).prod volume) A := by
  have hcongr : ∀ t : ℝ, (anglePhaseLaw hN hP i₀ t : Measure _) A
      = (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹' A) := by
    intro t
    exact Measure.map_apply (measurable_anglePhaseMap hP i₀ t) hA.measurableSet
  have hmain := limsup_measure_closed_anglePhase hN hP i₀ hRL hA
  simpa only [hcongr] using hmain

/-- **The card's `(20)` bookkeeping.**  If the closed target has fibre mass at most `ε` over a good
set of directions whose complement has shell mass at most `δ`, then the shell mass of the directions
entering the target is asymptotically at most `ε + δ`. -/
theorem limsup_measure_preimage_anglePhase_le_of_good (hN : 0 < N)
    (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (hRL : ∀ a : Fin D → ℝ, (∑ i, a i = 0) → a ≠ 0 →
      ∀ g : coeffSphere N → ℂ, Measurable g → ∀ C : ℝ, 0 ≤ C → (∀ x, ‖g x‖ ≤ C) →
        Tendsto (fun s : ℝ => ∫ x, g x *
            Complex.exp (-((s * sortedSpectralAction hP a (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) (cocompact ℝ) (nhds 0))
    {A : Set (coeffSphere N × UnitAddTorus (phaseIndex i₀))} (hA : IsClosed A)
    {G : Set (coeffSphere N)} (hG : MeasurableSet G) {ε δ : ENNReal}
    (hgood : ∀ x ∈ G,
      (volume : Measure (UnitAddTorus (phaseIndex i₀))) (Prod.mk x ⁻¹' A) ≤ ε)
    (hGc : (sphereLaw N) Gᶜ ≤ δ) :
    (atTop.limsup fun t : ℝ => (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹' A)) ≤ ε + δ := by
  haveI := isProbabilityMeasure_sphereLaw hN
  refine le_trans (limsup_measure_preimage_anglePhase hN hP i₀ hRL hA) ?_
  rw [Measure.prod_apply hA.measurableSet]
  have hsplit :
      (∫⁻ x in G, (volume : Measure (UnitAddTorus (phaseIndex i₀))) (Prod.mk x ⁻¹' A)
          ∂(sphereLaw N))
        + ∫⁻ x in Gᶜ, (volume : Measure (UnitAddTorus (phaseIndex i₀))) (Prod.mk x ⁻¹' A)
          ∂(sphereLaw N)
      = ∫⁻ x, (volume : Measure (UnitAddTorus (phaseIndex i₀))) (Prod.mk x ⁻¹' A)
          ∂(sphereLaw N) :=
    lintegral_add_compl _ hG
  rw [← hsplit]
  have hgoodInt :
      (∫⁻ x in G, (volume : Measure (UnitAddTorus (phaseIndex i₀))) (Prod.mk x ⁻¹' A)
        ∂(sphereLaw N)) ≤ ε := by
    refine le_trans (setLIntegral_mono' hG (fun x hx => hgood x hx)) ?_
    rw [setLIntegral_const]
    calc ε * (sphereLaw N) G ≤ ε * 1 := by
          gcongr
          exact le_trans (measure_mono (Set.subset_univ G)) (le_of_eq measure_univ)
      _ = ε := mul_one ε
  have hbadInt :
      (∫⁻ x in Gᶜ, (volume : Measure (UnitAddTorus (phaseIndex i₀))) (Prod.mk x ⁻¹' A)
        ∂(sphereLaw N)) ≤ δ := by
    refine le_trans (setLIntegral_mono' hG.compl
      (fun x _ => le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ))) ?_
    rw [setLIntegral_const, one_mul]
    exact hGc
  exact add_le_add hgoodInt hbadInt

end

end GaloisForLFunctions.HTGeometry

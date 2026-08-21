/-
# The compact exhaustion of the easy-circuit tube

The easy-circuit tube is closed only over a compact subset of the open simple-spectrum locus,
because the gauge-invariant cross-weights are continuous only there.  Since the degenerate locus is
null for the shell law, the tube can be replaced by its intersection with such a compact slab at the
cost of the slab's complement, which the inner regularity of a finite Borel measure on the compact
coefficient sphere makes arbitrarily small.

Main results:
* `limsup_add_const` — a constant passes through an upper limit of extended nonnegative reals.
* `sphereLaw_eq_zero_of_toSphere_eq_zero` — a sphere-null set is null for the normalized law.
* `limsup_measure_preimage_anglePhase_le_of_good_of_exhaustion` — **the `(20)` bookkeeping for a
  tube that is only locally closed**.
-/
import GaloisForLFunctions.HTGeometry.AngularPhasePortmanteau

open Filter Topology MeasureTheory Metric

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A constant passes through an upper limit of extended nonnegative reals. -/
theorem limsup_add_const (u : ℝ → ENNReal) (c : ENNReal) :
    atTop.limsup (fun t => u t + c) = atTop.limsup u + c := by
  have hmono : Monotone (fun x : ENNReal => x + c) := fun _ _ h => add_le_add h le_rfl
  have hmap := hmono.map_limsSup_of_continuousAt (F := (atTop : Filter ℝ).map u)
    (f_cont := (SeparatelyContinuousAdd.continuous_add_const (M := ENNReal)).continuousAt)
  simpa [Filter.limsup, Function.comp_def] using hmap.symm

variable {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

theorem sphereLaw_eq_zero_of_toSphere_eq_zero {B : Set (coeffSphere N)}
    (hB : (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere B = 0) :
    (sphereLaw N) B = 0 := by
  rw [sphereLaw, Measure.smul_apply, hB, smul_eq_mul, mul_zero]

/-- **The `(20)` bookkeeping for a tube that is closed only over compact slabs of a full-measure
locus.** -/
theorem limsup_measure_preimage_anglePhase_le_of_good_of_exhaustion (hN : 0 < N)
    (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (hRL : ∀ a : Fin D → ℝ, (∑ i, a i = 0) → a ≠ 0 →
      ∀ g : coeffSphere N → ℂ, Measurable g → ∀ C : ℝ, 0 ≤ C → (∀ x, ‖g x‖ ≤ C) →
        Tendsto (fun s : ℝ => ∫ x, g x *
            Complex.exp (-((s * sortedSpectralAction hP a (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) (cocompact ℝ) (nhds 0))
    {A : Set (coeffSphere N × UnitAddTorus (phaseIndex i₀))}
    {S : Set (coeffSphere N)} (hSmeas : MeasurableSet S) (hSnull : (sphereLaw N) Sᶜ = 0)
    (hclosed : ∀ K : Set (coeffSphere N), IsCompact K → K ⊆ S →
      IsClosed (A ∩ (K ×ˢ (Set.univ : Set (UnitAddTorus (phaseIndex i₀))))))
    {G : Set (coeffSphere N)} (hG : MeasurableSet G) {ε δ : ENNReal}
    (hgood : ∀ x ∈ G,
      (volume : Measure (UnitAddTorus (phaseIndex i₀))) (Prod.mk x ⁻¹' A) ≤ ε)
    (hGc : (sphereLaw N) Gᶜ ≤ δ) :
    (atTop.limsup fun t : ℝ => (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹' A)) ≤ ε + δ := by
  haveI := isProbabilityMeasure_sphereLaw hN
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro η hη _
  obtain ⟨K, hKS, hKcpt, hK⟩ := hSmeas.exists_isCompact_lt_add
    (measure_ne_top (sphereLaw N) S) (ε := ((η : ENNReal)))
    (ENNReal.coe_ne_zero.mpr hη.ne')
  have hKmeas : MeasurableSet K := hKcpt.measurableSet
  have hKc : (sphereLaw N) Kᶜ ≤ (η : ENNReal) := by
    have hsub : (Kᶜ : Set (coeffSphere N)) ⊆ (S \ K) ∪ Sᶜ := by
      intro x hx
      by_cases hS : x ∈ S
      · exact Or.inl ⟨hS, hx⟩
      · exact Or.inr hS
    have hdiff : (sphereLaw N) (S \ K) ≤ (η : ENNReal) := by
      rw [measure_sdiff hKS hKmeas.nullMeasurableSet (measure_ne_top _ _)]
      exact tsub_le_iff_left.mpr (le_of_lt hK)
    calc (sphereLaw N) Kᶜ ≤ (sphereLaw N) ((S \ K) ∪ Sᶜ) := measure_mono hsub
      _ ≤ (sphereLaw N) (S \ K) + (sphereLaw N) Sᶜ := measure_union_le _ _
      _ ≤ (η : ENNReal) + 0 := add_le_add hdiff (le_of_eq hSnull)
      _ = (η : ENNReal) := add_zero _
  have hAK := hclosed K hKcpt hKS
  have hgoodK : ∀ x ∈ G, (volume : Measure (UnitAddTorus (phaseIndex i₀)))
      (Prod.mk x ⁻¹' (A ∩ (K ×ˢ (Set.univ : Set (UnitAddTorus (phaseIndex i₀)))))) ≤ ε := by
    intro x hx
    refine le_trans (measure_mono ?_) (hgood x hx)
    intro y hy
    exact hy.1
  have hbook := limsup_measure_preimage_anglePhase_le_of_good hN hP i₀ hRL hAK hG hgoodK hGc
  have hstep : ∀ t : ℝ, (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹' A)
      ≤ (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹'
          (A ∩ (K ×ˢ (Set.univ : Set (UnitAddTorus (phaseIndex i₀))))))
        + (sphereLaw N) Kᶜ := by
    intro t
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx, hxK, Set.mem_univ _⟩
    · exact Or.inr hxK
  calc (atTop.limsup fun t : ℝ => (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹' A))
      ≤ atTop.limsup (fun t : ℝ => (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹'
          (A ∩ (K ×ˢ (Set.univ : Set (UnitAddTorus (phaseIndex i₀))))))
            + (sphereLaw N) Kᶜ) :=
        limsup_le_limsup (Filter.Eventually.of_forall hstep)
    _ = (atTop.limsup fun t : ℝ => (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹'
          (A ∩ (K ×ˢ (Set.univ : Set (UnitAddTorus (phaseIndex i₀)))))))
            + (sphereLaw N) Kᶜ := limsup_add_const _ _
    _ ≤ (ε + δ) + (η : ENNReal) := add_le_add hbook hKc

end

end GaloisForLFunctions.HTGeometry

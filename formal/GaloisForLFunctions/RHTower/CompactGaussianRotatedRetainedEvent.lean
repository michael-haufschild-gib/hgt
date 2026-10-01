import GaloisForLFunctions.RHTower.CompactGaussianRetainedSmallCentre
import GaloisForLFunctions.RHTower.SmoothAFEReflectedCovarianceEvent

open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
noncomputable section
namespace RHTower
open SteinhausModel

/-- The measure-preserving representative and raw logarithmic shift have
identical arithmetic characters, even at the index zero convention. -/
theorem steinhausCharacter_verticalRotation_neg_eq_logPhaseShift
    (n : ℕ) (tau : ℝ) (ω : Omega) :
    X n (steinhausEulerVerticalRotation (-tau) ω) = X n (steinhausLogPhaseShift ω tau) := by
  change X n (steinhausCoordinateRotation (fun p => -(-tau) * Real.log p / (2 * Real.pi)) ω) =
    X n (fun p => ω p + tau * Real.log p / (2 * Real.pi))
  simpa only [neg_neg] using
    steinhausCharacter_coordinateRotation n (fun p => -(-tau) * Real.log p / (2 * Real.pi)) ω

/-- A shifted cell condition is exactly the original phase cell with oppositely shifted centre. -/
theorem steinhausCharacterCell_logPhaseShift_iff
    (B : ℕ) (ω η : Omega) (δ tau : ℝ) :
    steinhausLogPhaseShift η tau ∈ steinhausCharacterCell B ω δ ↔
      η ∈ steinhausCharacterCell B (steinhausLogPhaseShift ω (-tau)) δ := by
  have hcancel : steinhausLogPhaseShift (steinhausLogPhaseShift ω (-tau)) tau = ω := by
    funext p
    simp only [steinhausLogPhaseShift]
    ring
  have heq (n : ℕ) : ‖X n (steinhausLogPhaseShift η tau) - X n ω‖ =
      ‖X n η - X n (steinhausLogPhaseShift ω (-tau))‖ := by
    have h := norm_steinhausCharacter_sub_add_phase n (steinhausLogPhaseShift ω (-tau)) η
      (fun p => tau * Real.log p / (2 * Real.pi))
    change ‖X n (steinhausLogPhaseShift η tau) -
      X n (steinhausLogPhaseShift (steinhausLogPhaseShift ω (-tau)) tau)‖ = _ at h
    rwa [hcancel] at h
  simp only [steinhausCharacterCell, Set.mem_setOf_eq, heq]

/-- Exact compact retained-carrier compatibility with the actual measure-preserving rotation. -/
theorem compactGaussianRetainedCarrier_verticalRotation_neg
    (s : ℂ) (N : ℝ) (L : ℕ) (S : Finset ℕ) (tau : ℝ) (ω : Omega) :
    compactGaussianRetainedCarrier s N L S (steinhausEulerVerticalRotation (-tau) ω) =
      compactGaussianRetainedCarrier s N L S (steinhausLogPhaseShift ω tau) := by
  simp only [compactGaussianRetainedCarrier,
    steinhausCharacter_verticalRotation_neg_eq_logPhaseShift]

/-- A fixed positive-mass retained cell and compact small centre survive every
common-height phase rotation, with one mass and threshold independent of height. -/
theorem exists_compactGaussian_rotatedRetained_event
    (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hc0 : 1 / 2 < c.re - R) (hc1 : c.re + R < 1)
    (B : ℕ) (ω : Omega) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ S : Finset ℕ,
      Nat.primesLE B ⊆ S → ∀ tau : ℝ,
      ∃ E : Set Omega, MeasurableSet E ∧ m ≤ steinhausMeasure.real E ∧
        (∀ η ξ : Omega, (∀ p ∈ S, η p = ξ p) → (η ∈ E ↔ ξ ∈ E)) ∧
        ∀ η ∈ E, steinhausLogPhaseShift η tau ∈ steinhausCharacterCell B ω δ ∧
          ∀ s ∈ closedBall c r,
            ‖compactGaussianRetainedCarrier s N L S (steinhausLogPhaseShift η tau)‖ < ε := by
  let C := steinhausCharacterCell B ω δ
  have hCm : MeasurableSet C := (isOpen_steinhausCharacterCell B ω δ).measurableSet
  have hmass : 0 < steinhausMeasure.real C :=
    ENNReal.toReal_pos (steinhausMeasure_characterCell_pos B ω hδ).ne' (measure_ne_top _ _)
  refine ⟨steinhausMeasure.real C / 2, half_pos hmass, ?_⟩
  filter_upwards [eventually_compactGaussianRetainedSmallCentre_inter_mass
    c hr hrR hc0 hc1 hε hmass, eventually_ge_atTop (1 : ℕ)] with N hgoodN hN
  intro L S hS tau
  let G := C ∩ compactGaussianRetainedSmallCentreEvent c r R N L S ε
  have hG : MeasurableSet G := hCm.inter
    (measurableSet_compactGaussianRetainedSmallCentreEvent c r R hN L S ε)
  let rot := steinhausEulerVerticalRotation (-tau)
  let E := rot ⁻¹' G
  have hrotm : Measurable rot := measurable_steinhausEulerVerticalRotation _
  have heq : steinhausMeasure.real E = steinhausMeasure.real G := by
    unfold Measure.real
    change (steinhausMeasure (rot ⁻¹' G)).toReal = _
    rw [← Measure.map_apply hrotm hG, map_steinhausEulerVerticalRotation]
  refine ⟨E, hG.preimage hrotm, heq.symm ▸ hgoodN L S C le_rfl, ?_, ?_⟩
  · intro η ξ hphase
    have hrot : ∀ p ∈ S, rot η p = rot ξ p := by
      intro p hp
      simp only [rot, steinhausEulerVerticalRotation, steinhausCoordinateRotation, hphase p hp]
    change rot η ∈ G ↔ rot ξ ∈ G
    exact and_congr (steinhausCharacterCell_congr_smallPrimes B ω δ
      (fun p hp => hrot p (hS hp)))
      (compactGaussianRetainedSmallCentreEvent_congr_retained c r R N L S ε hrot)
  · intro η hη
    change rot η ∈ G at hη
    refine ⟨?_, ?_⟩
    · intro n hn
      rw [← steinhausCharacter_verticalRotation_neg_eq_logPhaseShift]
      exact hη.1 n hn
    · intro s hs
      rw [← compactGaussianRetainedCarrier_verticalRotation_neg]
      exact norm_compactGaussianRetainedCarrier_lt_of_mem_smallCentre c hr hrR hN L S hε hη.2 hs

end RHTower

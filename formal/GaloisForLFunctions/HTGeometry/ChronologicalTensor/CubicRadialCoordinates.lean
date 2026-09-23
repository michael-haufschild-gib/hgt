import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryGeometry
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspFlow

/-!
# Every physical observation has a radial edge representative

The boundary coordinate is one minus the absolute outer-gap imbalance. The
physical (first-mode, middle-gap) coordinates equal a contraction of the realized
edge probe at that coordinate. Total real division handles the degenerate zero
coordinate, and the identities include that corner. Every polynomial observation
therefore agrees with pullback of an actual edge observation.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial

def cubicRadialEdgeCoordinate (g : cubicProbeSection) : ℝ := 1-|g.val 0-g.val 4|

theorem cubicRadialEdgeCoordinate_bounds (g : cubicProbeSection) :
    g.val 2 ≤ cubicRadialEdgeCoordinate g ∧ cubicRadialEdgeCoordinate g ≤ 1 := by
  have ha := g.property.1 0
  have he := g.property.1 4
  have habs : |g.val 0-g.val 4| ≤ g.val 0+g.val 4 := by
    rw [abs_le]
    constructor <;> linarith
  have hsum := g.property.2.1
  unfold cubicRadialEdgeCoordinate
  constructor
  · linarith [g.property.1 1,g.property.1 3]
  · exact sub_le_self _ (abs_nonneg _)

def cubicRadialBoundaryProbe (g : cubicProbeSection) : cubicProbeSection :=
  cubicRecoveryEdge ⟨cubicRadialEdgeCoordinate g,
    ⟨(g.property.1 2).trans (cubicRadialEdgeCoordinate_bounds g).1,
      (cubicRadialEdgeCoordinate_bounds g).2⟩⟩

def cubicRadialParameter (g : cubicProbeSection) : Icc (0:ℝ) 1 :=
  ⟨g.val 2/cubicRadialEdgeCoordinate g,by
    have hc := g.property.1 2
    have hC := cubicRadialEdgeCoordinate_bounds g
    have hC0 : 0 ≤ cubicRadialEdgeCoordinate g := hc.trans hC.1
    refine ⟨div_nonneg hc hC0,?_⟩
    by_cases hz : cubicRadialEdgeCoordinate g=0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne hC0 (Ne.symm hz))).mpr hC.1⟩

theorem cubicRadialCoordinates_middle (g : cubicProbeSection) :
    g.val 2=(cubicRadialParameter g).val*(cubicRadialBoundaryProbe g).val 2 := by
  change g.val 2=(g.val 2/cubicRadialEdgeCoordinate g)*cubicRadialEdgeCoordinate g
  by_cases hz : cubicRadialEdgeCoordinate g=0
  · have hc : g.val 2=0 := by linarith [(cubicRadialEdgeCoordinate_bounds g).1,g.property.1 2]
    simp [hc]
  · exact (div_mul_cancel₀ _ hz).symm

theorem cubicRadialBoundaryProbe_mode (g : cubicProbeSection) :
    cubicDecayMode 0 (cubicRadialBoundaryProbe g).val=
      cubicRadialEdgeCoordinate g*(1-(g.val 0-g.val 4)^(2 : ℕ))/4 := by
  rw [cubicRadialBoundaryProbe,cubicRecoveryEdge_mode]
  change cubicRecoveryLower (cubicRadialEdgeCoordinate g)=_
  have h (c : ℝ) : cubicRecoveryLower c=c*(1-(1-c)^(2 : ℕ))/4 := by
    unfold cubicRecoveryLower
    ring
  rw [h]
  simp only [cubicRadialEdgeCoordinate,sub_sub_cancel,sq_abs]

theorem cubicRadialCoordinates_mode (g : cubicProbeSection) :
    cubicDecayMode 0 g.val=(cubicRadialParameter g).val*cubicDecayMode 0 (cubicRadialBoundaryProbe g).val := by
  rw [cubicRadialBoundaryProbe_mode]
  change g.val 2*(1-(g.val 0-g.val 4)^(2 : ℕ))/4=_
  have h := cubicRadialCoordinates_middle g
  change g.val 2=(cubicRadialParameter g).val*cubicRadialEdgeCoordinate g at h
  rw [h]
  ring

theorem cubicRadialCoordinates_observation (P : Polynomial (Polynomial ℝ)) (g : cubicProbeSection) :
    cubicPolynomialObservation P g=
      cubicSectionPullback (cubicRadialParameter g) (cubicPolynomialObservation P)
        (cubicRadialBoundaryProbe g) := by
  change Polynomial.eval₂ (Polynomial.evalRingHom (cubicDecayMode 0 g.val)) (g.val 2) P=
    Polynomial.eval₂ (Polynomial.evalRingHom
      (cubicDecayMode 0 (cubicFlow (cubicRadialParameter g) (cubicRadialBoundaryProbe g).val)))
      ((cubicFlow (cubicRadialParameter g) (cubicRadialBoundaryProbe g).val) 2) P
  rw [cubicDecayMode_spectrum]
  simp only [Fin.val_zero,zero_add,pow_one]
  have hc : (cubicFlow (cubicRadialParameter g) (cubicRadialBoundaryProbe g).val) 2=
      (cubicRadialParameter g).val*(cubicRadialBoundaryProbe g).val 2 := by
    simp [cubicFlow,cubicCollapse]
  rw [hc,← cubicRadialCoordinates_middle g,← cubicRadialCoordinates_mode g]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor

import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRadialCoordinates
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicEquivariantAlgebra
import Mathlib.Topology.Algebra.Polynomial

/-!
# Homogeneous observation norms reduce to one physical edge

The half-retraction eigenspace of weight k obeys full homogeneous scaling.
Its value at every physical probe is a factor q^k, with q in [0,1], times
its value at a realized boundary probe. The edge profile is continuous,
so its absolute value attains a maximum that bounds every physical value.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicHomogeneousSpace (k : ℕ) : Submodule ℝ (Polynomial (Polynomial ℝ)) :=
  LinearMap.ker ((cubicPolynomialFlow (1/2)).toLinearMap-(1/2:ℝ)^k • LinearMap.id)

theorem cubicHomogeneousSpace_mem (k : ℕ) (P : Polynomial (Polynomial ℝ)) :
    P ∈ cubicHomogeneousSpace k ↔ cubicPolynomialFlow (1/2) P=(1/2:ℝ)^k • P := by
  simp [cubicHomogeneousSpace,LinearMap.mem_ker,sub_eq_zero]

theorem cubicHomogeneousSpace_flow (k : ℕ) (P : cubicHomogeneousSpace k) (q : ℝ) :
    cubicPolynomialFlow q P.val=q^k • P.val :=
  (cubicPolynomialFlow_halfWeight_fullFlow P.val k).mp
    ((cubicHomogeneousSpace_mem k P.val).mp P.property) q

theorem cubicHomogeneousSpace_radial (k : ℕ) (P : cubicHomogeneousSpace k) (g : cubicProbeSection) :
    cubicPolynomialObservation P.val g=(cubicRadialParameter g).val^k*
      cubicPolynomialObservation P.val (cubicRadialBoundaryProbe g) := by
  rw [cubicRadialCoordinates_observation,← cubicPolynomialFlow_observation,
    cubicHomogeneousSpace_flow,map_smul]
  rfl

theorem cubicHomogeneousSpace_edgeDominates (k : ℕ) (P : cubicHomogeneousSpace k) (g : cubicProbeSection) :
    |cubicPolynomialObservation P.val g| ≤
      |cubicPolynomialObservation P.val (cubicRadialBoundaryProbe g)| := by
  rw [cubicHomogeneousSpace_radial,abs_mul,abs_of_nonneg (pow_nonneg (cubicRadialParameter g).property.1 k)]
  have hq : (cubicRadialParameter g).val^k ≤ 1 :=
    pow_le_one₀ (cubicRadialParameter g).property.1 (cubicRadialParameter g).property.2
  simpa using mul_le_mul_of_nonneg_right hq (abs_nonneg (cubicPolynomialObservation P.val (cubicRadialBoundaryProbe g)))

def cubicEdgeProfile (P : Polynomial (Polynomial ℝ)) (c : ℝ) : ℝ :=
  Polynomial.eval₂ (Polynomial.evalRingHom (cubicRecoveryLower c)) c P

theorem cubicEdgeProfile_continuous (P : Polynomial (Polynomial ℝ)) : Continuous (cubicEdgeProfile P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    change Continuous (fun c : ℝ => Polynomial.eval₂ (Polynomial.evalRingHom (cubicRecoveryLower c)) c (P+Q))
    simp only [Polynomial.eval₂_add]
    exact hP.add hQ
  | monomial n p =>
    change Continuous (fun c : ℝ => Polynomial.eval₂ (Polynomial.evalRingHom (cubicRecoveryLower c)) c (Polynomial.monomial n p))
    simp only [Polynomial.eval₂_monomial]
    change Continuous (fun c : ℝ => p.eval (cubicRecoveryLower c)*c^n)
    have hL : Continuous cubicRecoveryLower := by unfold cubicRecoveryLower; fun_prop
    exact (p.continuous.comp hL).mul (continuous_id.pow n)

theorem cubicEdgeProfile_observation (P : Polynomial (Polynomial ℝ)) (c : Icc (0:ℝ) 1) :
    cubicEdgeProfile P c.val=cubicPolynomialObservation P (cubicRecoveryEdge c) := by
  change Polynomial.eval₂ (Polynomial.evalRingHom (cubicRecoveryLower c.val)) c.val P=
    Polynomial.eval₂ (Polynomial.evalRingHom (cubicDecayMode 0 (cubicRecoveryEdge c).val))
      ((cubicRecoveryEdge c).val 2) P
  rw [cubicRecoveryEdge_mode,cubicRecoveryEdge_middle]

theorem cubicHomogeneousSpace_edgeMaximum (k : ℕ) (P : cubicHomogeneousSpace k) :
    ∃ c : Icc (0:ℝ) 1, ∀ g : cubicProbeSection,
      |cubicPolynomialObservation P.val g| ≤ |cubicEdgeProfile P.val c.val| := by
  obtain ⟨c,hc,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) 1).Nonempty from ⟨0,le_rfl,zero_le_one⟩)
    (cubicEdgeProfile_continuous P.val).abs.continuousOn
  refine ⟨⟨c,hc⟩,?_⟩
  intro g
  apply (cubicHomogeneousSpace_edgeDominates k P g).trans
  change |cubicPolynomialObservation P.val (cubicRecoveryEdge _)| ≤ _
  rw [← cubicEdgeProfile_observation]
  exact hmax ⟨(g.property.1 2).trans (cubicRadialEdgeCoordinate_bounds g).1,
    (cubicRadialEdgeCoordinate_bounds g).2⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor

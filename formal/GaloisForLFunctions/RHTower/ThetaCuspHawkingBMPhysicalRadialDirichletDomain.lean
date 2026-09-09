import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalRadialAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadialDirichletGraph

/-! The actual physical cusp response retains the original radial Dirichlet graph. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Admitted physical contraction preserves the completed original radial boundary domain. -/
theorem physicalJointProjection_radialDirichlet_mem (r : XiZeroCopy) (u : jointDomain)
    (h0 : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*jointEmbedding u p)
      2 (radialMeasure.prod D4BMModularCore.measure))
    (h1 : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*((u : JointEnergySpace) 1) p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    WithLp.toLp 2 ![physicalJointProjection r (h0.toLp _),physicalJointProjection r (h1.toLp _)]
      ∈ radialDirichletDomain := by
  apply radialDirichletDomain_of_pairing_limit
    (fun n => radialGraphContraction (fieldVector (physicalCoreCutoff r n)) u)
    (fun n => radialGraphContraction_mem _ u)
  · intro h
    change Tendsto (fun n => inner ℂ h (angularContraction (fieldVector (physicalCoreCutoff r n)) (jointEmbedding u)))
      atTop (𝓝 (inner ℂ h (physicalJointProjection r (h0.toLp _))))
    simp_rw [angularContraction_inner]
    exact physicalCoreCutoff_inner_tendsto r h (jointEmbedding u) h0
  · intro h
    change Tendsto (fun n => inner ℂ h (angularContraction (fieldVector (physicalCoreCutoff r n)) ((u : JointEnergySpace) 1)))
      atTop (𝓝 (inner ℂ h (physicalJointProjection r (h1.toLp _))))
    simp_rw [angularContraction_inner]
    exact physicalCoreCutoff_inner_tendsto r h ((u : JointEnergySpace) 1) h1

/-- The derivative projection uses the actual radial component of the original complete response. -/
def physicalCuspRadialDerivative (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) : RadialSpace :=
  physicalJointProjection r ((completeCuspResponse_radial_height_memLp q branch w a hw hd hwi hwr).toLp _)

/-- The original complete causal response's physical value and actual radial derivative lie in its Dirichlet domain. -/
theorem physicalCuspResponse_radialDirichlet_mem (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    WithLp.toLp 2 ![physicalCuspResponse q r branch w a hw hd hwi hwr,
      physicalCuspRadialDerivative q r branch w a hw hd hwi hwr] ∈ radialDirichletDomain :=
  physicalJointProjection_radialDirichlet_mem r _ (completeCuspResponse_height_memLp q branch w a hw hd hwi hwr)
    (completeCuspResponse_radial_height_memLp q branch w a hw hd hwi hwr)

end
end RHTower.D4BMJointSource

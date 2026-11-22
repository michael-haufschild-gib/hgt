import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.ChordDiameter
import GaloisForLFunctions.RHTower.Deninger.DeningerUnitaryHarmonicAction
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Operator-norm diameter of a fixed-angle cap on the unitary group -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AngularError
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Apply the spherical cap inequality to the images of each unit vector.
Angles add even if the three unitary operators do not commute. -/
theorem common_unitary_chord {X Y Z : Mat I} (hX : X ∈ unitary (Mat I))
    (hY : Y ∈ unitary (Mat I)) (hZ : Z ∈ unitary (Mat I)) {θ : ℝ}
    (ht : 0 ≤ θ) (hθ : 2*θ ≤ π/2) (hx : ‖X-Y‖ ≤ 2*sin θ) (hz : ‖Z-Y‖ ≤ 2*sin θ) :
    ‖X-Z‖ ≤ 2*sin (2*θ) := by
  let L := Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ)
  have norm_image (U : Mat I) (hU : U ∈ unitary (Mat I)) (v : EuclideanSpace ℂ I) :
      ‖L U v‖=‖v‖ := by
    apply RHTower.deningerUnitary_norm_apply
    have h := congrArg L (Unitary.mem_iff.mp hU).1
    simpa only [map_mul,map_one,map_star] using h
  have dist_image (U : Mat I) (he : ‖U-Y‖ ≤ 2*sin θ) (v : EuclideanSpace ℂ I) :
      ‖L U v-L Y v‖ ≤ 2*sin θ*‖v‖ := by
    have h := (L (U-Y)).le_opNorm v
    rw [map_sub,ContinuousLinearMap.sub_apply] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [←map_sub]
    exact he
  have hs := sin_nonneg_of_nonneg_of_le_pi (mul_nonneg two_pos.le ht) (by linarith only [hθ,pi_pos])
  change ‖L (X-Z)‖ ≤ _
  rw [map_sub]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg two_pos.le hs)
  intro v
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ I) := InnerProductSpace.complexToReal
  have h := common_chord (x:=L X v) (y:=L Y v) (z:=L Z v) ht hθ
    ((norm_image X hX v).trans (norm_image Y hY v).symm)
    ((norm_image Z hZ v).trans (norm_image Y hY v).symm)
    (by rw [norm_image Y hY]; exact dist_image X hx v)
    (by rw [norm_image Y hY]; exact dist_image Z hz v)
  simpa only [ContinuousLinearMap.sub_apply,norm_image Y hY] using h

end
end GaloisForLFunctions.HTGeometry.AngularError

import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw
import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-! # Mixed-state witnesses for distance from a circuit to spectral phases -/
open Matrix Finset Complex
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.DensityWitnesses
open StaticLocalLaboratoryComplexityGrowthLaw
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where

/-- Each coefficient retains its phase until the date is chosen. -/
def weight (ρ W : Mat I) (i : I) := (ρ*star W) i i

/-- Every density matrix gives a scalar lower bound for the
operator error, uniformly over all spectral phases and all circuits. -/
theorem packet_bound (W : unitaryGroup I ℂ) (ρ : Mat I) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (f : I → ℂ) (hf : ∀ i, ‖f i‖=1) :
    2-2*(∑ i, weight ρ W.val i*f i).re ≤ ‖diagonal f-W.val‖^2 := by
  let D := diagonal f
  let Z := D-W.val
  have hD : D∈unitary (Mat I) := mem_unitaryGroup_diagonal_general _ hf
  have hG : star Z*Z=1+1-star D*W.val-star W.val*D := by
    dsimp only [Z]
    rw [star_sub,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,(Unitary.mem_iff.mp hD).1,
      (Unitary.mem_iff.mp W.property).1]
    abel
  have hstar (A : Mat I) : (star A).trace=star A.trace := Matrix.trace_conjTranspose A
  have hconj : (ρ*(star D*W.val)).trace=star (ρ*(star W.val*D)).trace := by
    rw [←hstar,star_mul,star_mul,star_star,show star ρ=ρ from hρ.isHermitian,Matrix.trace_mul_comm]
  have hsum : (ρ*(star W.val*D)).trace=∑ i, weight ρ W.val i*f i := by
    rw [←mul_assoc]
    simp only [Matrix.trace,Matrix.diag,D,Matrix.mul_diagonal,weight]
  have h := (Complex.re_le_norm (ρ*(star Z*Z)).trace).trans
    (norm_trace_densityMatrix_mul_le hρ htr (star Z*Z))
  rw [CStarRing.norm_star_mul_self,←sq,hG,Matrix.mul_sub,Matrix.mul_sub,Matrix.mul_add,mul_one,
    Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_add,htr,hconj,hsum] at h
  simpa only [Complex.sub_re,Complex.add_re,Complex.one_re,Complex.star_def,Complex.conj_re,
    two_mul,show (1:ℝ)+1=2 by norm_num,sub_sub] using h

/-- One state with a small absolute coefficient sum excludes a circuit
from the full spectral torus, independently of observation time. -/
theorem absolute_bound (W : unitaryGroup I ℂ) (ρ : Mat I) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (f : I → ℂ) (hf : ∀ i, ‖f i‖=1) :
    2-2*∑ i, ‖weight ρ W.val i‖ ≤ ‖diagonal f-W.val‖^2 := by
  have h := (Complex.re_le_norm _).trans (norm_sum_le univ (fun i => weight ρ W.val i*f i))
  simp only [norm_mul,hf,mul_one] at h
  linarith only [h,packet_bound W ρ hρ htr f hf]

#print axioms absolute_bound
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.DensityWitnesses

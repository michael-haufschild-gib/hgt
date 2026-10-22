import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAngularCutoffCalculus

/-! Exact physical eigenvalue and both original cusp cutoff commutators on the full modular cell. -/
open Complex Set Filter Topology
open scoped ContDiff ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The conjugated physical testing field satisfies the original modular eigen-equation with the conjugated coefficient. -/
theorem physicalTestField_laplacian (q : XiZeroCopy) (z : UpperHalfPlane) :
    chartLaplacian (physicalTestField q) z =
      conj ((physicalAngularParameter q^(2 : ℕ)-1/4)*scalar (physicalAngularParameter q) (coordinates z)) := by
  change chartLaplacian (fun w => (fun x => conj (scalar (physicalAngularParameter q) x)) (coordinates w)) z = _
  rw [chartLaplacian_coordinates (fun x => conj (scalar (physicalAngularParameter q) x)) z,
    hyperbolicLaplacian_conj]
  exact congrArg conj (scalarCusp_hyperbolicLaplacian (physicalAngularParameter q) (coordinates z) z.im_pos)

/-- Every compact physical core test retains the exact height-cutoff first and second derivative terms. -/
theorem physicalCoreCutoff_laplacian (q : XiZeroCopy) (n : ℕ) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) :
    (physicalCoreCutoff q n).laplacian.field z =
      (scaledCuspCutoff ((n:ℝ)+1) z.im:ℂ)*
        conj ((physicalAngularParameter q^(2 : ℕ)-1/4)*scalar (physicalAngularParameter q) (coordinates z))+
      2*((z.im*deriv (scaledCuspCutoff ((n:ℝ)+1)) z.im:ℝ):ℂ)*(z.im:ℂ)*
        conj (coordDeriv 1 (scalar (physicalAngularParameter q)) (coordinates z))+
      ((z.im^(2 : ℕ)*deriv (deriv (scaledCuspCutoff ((n:ℝ)+1))) z.im:ℝ):ℂ)*
        conj (scalar (physicalAngularParameter q) (coordinates z)) := by
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have : (0:ℝ) ≤ n := by positivity
    linarith
  have he : (physicalCoreCutoff q n).field =ᶠ[𝓝 z] fun w =>
      (scaledCuspCutoff ((n:ℝ)+1) w.im:ℂ)*conj (scalar (physicalAngularParameter q) (coordinates w)) := by
    filter_upwards [modularCuspCutoff_germ _ hN z hz] with w hw
    change modularCuspCutoff ((n:ℝ)+1) w*physicalTestField q w = _
    rw [hw]
    rfl
  rw [CoreField.laplacian_field,chartLaplacian_congr he]
  change chartLaplacian (fun w =>
    (fun x : Fin 2 → ℝ => (scaledCuspCutoff ((n:ℝ)+1) (x 1):ℂ)*
      conj (scalar (physicalAngularParameter q) x)) (coordinates w)) z = _
  rw [chartLaplacian_coordinates (fun x : Fin 2 → ℝ =>
    (scaledCuspCutoff ((n:ℝ)+1) (x 1):ℂ)*conj (scalar (physicalAngularParameter q) x)) z]
  have hf : ContDiffAt ℝ 2 (fun x => conj (scalar (physicalAngularParameter q) x)) (coordinates z) :=
    Complex.conjCLE.contDiff.contDiffAt.comp (coordinates z)
      (cuspLeg_contDiffAt .scalar (physicalAngularParameter q) 2 (coordinates z) z.im_pos)
  have hs : hyperbolicLaplacian (scalar (physicalAngularParameter q)) (coordinates z) =
      (physicalAngularParameter q^(2 : ℕ)-1/4)*scalar (physicalAngularParameter q) (coordinates z) :=
    scalarCusp_hyperbolicLaplacian (physicalAngularParameter q) (coordinates z) z.im_pos
  rw [hyperbolicLaplacian_height_mul _ (scaledCuspCutoff_smooth _) _ _ hf,
    hyperbolicLaplacian_conj,coordDeriv_conj,hs]
  change _ = (scaledCuspCutoff ((n:ℝ)+1) z.im:ℂ)*
    conj ((physicalAngularParameter q^(2 : ℕ)-1/4)*scalar (physicalAngularParameter q) (coordinates z))+
    2*((z.im*deriv (scaledCuspCutoff ((n:ℝ)+1)) z.im:ℝ):ℂ)*(z.im:ℂ)*
      conj (coordDeriv 1 (scalar (physicalAngularParameter q)) (coordinates z))+
    ((z.im^(2 : ℕ)*deriv (deriv (scaledCuspCutoff ((n:ℝ)+1))) z.im:ℝ):ℂ)*
      conj (scalar (physicalAngularParameter q) (coordinates z))
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  change (scaledCuspCutoff ((n:ℝ)+1) z.im:ℂ)*
      conj ((physicalAngularParameter q^(2 : ℕ)-1/4)*scalar (physicalAngularParameter q) (coordinates z))+
    2*(z.im:ℂ)^(2 : ℕ)*((deriv (scaledCuspCutoff ((n:ℝ)+1)) z.im:ℝ):ℂ)*
      conj (coordDeriv 1 (scalar (physicalAngularParameter q)) (coordinates z))+
    (z.im:ℂ)^(2 : ℕ)*((deriv (deriv (scaledCuspCutoff ((n:ℝ)+1))) z.im:ℝ):ℂ)*
      conj (scalar (physicalAngularParameter q) (coordinates z)) = _
  ring

end
end RHTower.D4BMJointSource

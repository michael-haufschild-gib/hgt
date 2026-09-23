import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularAssembly
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHorizonCovectorEquation

/-!
The constructed full angular response yields an actual smooth divergence-free coexact covector. Its forced rough Laplacian retains the curvature shift and the original squared scalar source.
-/

open Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMHorizon
noncomputable section

/-- The constructed complete response in the original angular metric coordinates. -/
def fullAngularField (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ) : ℂ :=
  fullAngular q branch (ofComplex (angularCoordinates.symm z))

private theorem field_coordinates (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane) :
    fullAngularField q branch (coordinates z) = fullAngular q branch z := by
  change fullAngular q branch (ofComplex (angularCoordinates.symm (angularCoordinates (z:ℂ)))) = _
  rw [angularCoordinates.symm_apply_apply,ofComplex_apply]

/-- The actual full response has every coordinate derivative at positive height. -/
theorem fullAngularField_smooth (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (fullAngularField q branch) z := by
  have hi : 0 < (angularCoordinates.symm z).im := by change 0 < ((z 0 : ℂ)+(z 1 : ℂ)*Complex.I).im; simpa using hz
  have h := fullAngular_smooth q branch (ofComplex (angularCoordinates.symm z))
  change ContDiffAt ℝ ∞ (fullAngular q branch ∘ ofComplex) _ at h
  rw [ofComplex_apply_of_im_pos hi] at h
  change ContDiffAt ℝ ∞ ((fullAngular q branch ∘ ofComplex) ∘ angularCoordinates.symm) z
  exact h.comp z angularCoordinates.symm.contDiff.contDiffAt

/-- The original scalar Laplace--Beltrami operator satisfies the full forcing equation. -/
theorem fullAngularField_equation (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    scalarLaplacian (fullAngularField q branch) z =
      parameter q branch*fullAngularField q branch z +
        (parameter q branch/2)*scalar (center q) z^(2 : ℕ) := by
  let w : UpperHalfPlane := ⟨angularCoordinates.symm z,by change 0 < ((z 0 : ℂ)+(z 1 : ℂ)*Complex.I).im; simpa using hz⟩
  have hw : coordinates w = z := by
    change angularCoordinates (angularCoordinates.symm z) = z
    exact angularCoordinates.apply_symm_apply z
  have hf : (fun v => fullAngularField q branch (coordinates v)) = fullAngular q branch :=
    funext (field_coordinates q branch)
  have he := fullAngular_classical_equation q branch w
  rw [← hf,chartLaplacian_coordinates,hw] at he
  dsimp only at he
  rw [hw] at he
  rw [scalarLaplacian_eq _ z hz]
  change hyperbolicLaplacian (fullAngularField q branch) z = _
  linear_combination he

/-- The actual coexact response used by the vector stream. -/
def fullAngularCovector (q : XiZeroCopy) (branch : Bool) : Covector :=
  coexact (fullAngularField q branch)

/-- The retained quadratic angular source, using actual scalar derivatives. -/
def fullSquareCovector (q : XiZeroCopy) : Covector := fun k z =>
  scalar (center q) z * coexact (scalar (center q)) k z

/-- The response covector is smooth in the original angular coordinates. -/
theorem fullAngularCovector_smooth (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) (k : Fin 2) : ContDiffAt ℝ ∞ (fullAngularCovector q branch k) z := by
  apply coexact_contDiffAt
  simpa using fullAngularField_smooth q branch z hz

/-- The actual covariant divergence vanishes, as required by the vector stream metric. -/
theorem fullAngularCovector_divergence (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) : divergence (fullAngularCovector q branch) z = 0 := by
  apply coexact_divergence _ z hz
  have h := (contDiffAt_infty.mp (fullAngularField_smooth q branch z hz)) 2
  norm_num at h
  exact h

/-- Differentiating the constructed equation gives the actual forced coexact equation. -/
theorem fullAngularCovector_forced (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) (k : Fin 2) :
    coexact (scalarLaplacian (fullAngularField q branch)) k z =
      parameter q branch*fullAngularCovector q branch k z +
        parameter q branch*fullSquareCovector q k z := by
  let H := fullAngularField q branch
  let S := scalar (center q)
  let L := parameter q branch
  have he : scalarLaplacian H =ᶠ[𝓝 z] (fun w => L*H w+(L/2)*S w^(2 : ℕ)) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    exact fullAngularField_equation q branch w hw
  have hH := ((fullAngularField_smooth q branch z hz).differentiableAt (by simp)).hasFDerivAt
  have hS := ((cuspLeg_contDiffAt .scalar (center q) 1 z hz).differentiableAt (by norm_num)).hasFDerivAt
  have hd := ((hH.const_mul L).add ((hS.pow 2).const_mul (L/2))).congr_of_eventuallyEq he
  have hi (j : Fin 2) : coordDeriv j (scalarLaplacian H) z =
      L*coordDeriv j H z + L*S z*coordDeriv j S z := by
    rw [coordDeriv,hd.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,nsmul_eq_mul]
    change L*coordDeriv j H z+(L/2)*(2*S z^(2-1)*coordDeriv j S z) = _
    ring
  change coexact (scalarLaplacian H) k z = L*coexact H k z+L*(S z*coexact S k z)
  fin_cases k <;> simp [coexact,hi] <;> ring

/-- The curvature shift is retained in the full forced rough covector Laplacian. -/
theorem fullAngularCovector_rough_equation (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) (k : Fin 2) :
    roughLaplacian (fullAngularCovector q branch) k z + fullAngularCovector q branch k z =
      parameter q branch*fullAngularCovector q branch k z +
        parameter q branch*fullSquareCovector q k z := by
  have h := (contDiffAt_infty.mp (fullAngularField_smooth q branch z hz)) 3
  norm_num at h
  rw [fullAngularCovector,coexact_roughLaplacian _ z hz h,sub_add_cancel]
  exact fullAngularCovector_forced q branch z hz k

end
end RHTower.D4BMModularCore

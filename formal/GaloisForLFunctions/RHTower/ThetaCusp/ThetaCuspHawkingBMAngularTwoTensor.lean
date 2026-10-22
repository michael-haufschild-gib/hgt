import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAngularTwoRegularity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCuspMetricSource
import Mathlib.Analysis.Complex.Conformal

/-!
# The holomorphic tensor remainder of the original squared source

The constructed shift-two inverse and literal scalar eigen-equation force both coordinate
divergences of `[dS tensor dS]^TF + lambda HessTF(U)` to vanish. Its components are identified
using the actual inverse metric and connection. Their Cauchy--Riemann equations construct two
independent holomorphic polarizations on the full half-plane, without a reality premise.

Modular weight, cusp admission and vanishing of this tensor are separate obligations.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMAngularTwoTensor
open D4BMHorizon D4BMAngularTwo
noncomputable section
set_option autoImplicit false

/-- The first coordinate of the trace-free quadratic differential. -/
def componentA (S U : Field) (μ : ℂ) (z : Point) : ℂ :=
  (coordDeriv 0 S z^(2 : ℕ)-coordDeriv 1 S z^(2 : ℕ))/2 +
    μ*((coordDeriv 0 (coordDeriv 0 U) z-coordDeriv 1 (coordDeriv 1 U) z)/2-
      (z 1 : ℂ)⁻¹*coordDeriv 1 U z)

/-- The off-diagonal coordinate of the same complex trace-free tensor. -/
def componentB (S U : Field) (μ : ℂ) (z : Point) : ℂ :=
  coordDeriv 0 S z*coordDeriv 1 S z +
    μ*(coordDeriv 0 (coordDeriv 1 U) z+(z 1 : ℂ)⁻¹*coordDeriv 0 U z)

private theorem partial_add {f g : Field} {z : Point}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    coordDeriv i (fun q => f q+g q) z = coordDeriv i f z+coordDeriv i g z := by
  simp only [coordDeriv,fderiv_fun_add hf hg,add_apply]

private theorem partial_sub {f g : Field} {z : Point}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    coordDeriv i (fun q => f q-g q) z = coordDeriv i f z-coordDeriv i g z := by
  simp only [coordDeriv,fderiv_fun_sub hf hg,sub_apply]

private theorem partial_mul {f g : Field} {z : Point}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    coordDeriv i (fun q => f q*g q) z = coordDeriv i f z*g z+f z*coordDeriv i g z := by
  simp only [coordDeriv,fderiv_fun_mul hf hg,add_apply,smul_apply,smul_eq_mul]
  ring

private theorem partial_const_mul {f : Field} {z : Point}
    (hf : DifferentiableAt ℝ f z) (c : ℂ) (i : Fin 2) :
    coordDeriv i (fun q => c*f q) z = c*coordDeriv i f z := by
  rw [coordDeriv,(hf.hasFDerivAt.const_mul c).fderiv]
  rfl

private theorem inv_height_hasFDerivAt (z : Point) (hz : 0 < z 1) :
    HasFDerivAt (fun q : Point => (q 1 : ℂ)⁻¹)
      ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).smulRight (-(z 1 : ℂ)⁻¹ ^ (2 : ℕ))) z := by
  have hY := Complex.ofRealCLM.hasFDerivAt.comp z
    ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt)
  have h := (hasDerivAt_inv (Complex.ofReal_ne_zero.mpr hz.ne')).comp_hasFDerivAt z hY
  convert! h using 1
  ext v
  simp [Complex.real_smul,smul_eq_mul]
  ring

private theorem inv_mul_partial {f : Field} {z : Point}
    (hz : 0 < z 1) (hf : DifferentiableAt ℝ f z) (i : Fin 2) :
    coordDeriv i (fun q => (q 1 : ℂ)⁻¹*f q) z =
      (if i = 1 then -(z 1 : ℂ)⁻¹^(2 : ℕ) else 0)*f z+(z 1 : ℂ)⁻¹*coordDeriv i f z := by
  change fderiv ℝ ((fun q : Point => (q 1 : ℂ)⁻¹)*f) z (Pi.single i 1) = _
  rw [((inv_height_hasFDerivAt z hz).mul hf.hasFDerivAt).fderiv]
  fin_cases i <;> simp [coordDeriv,smul_eq_mul]
  ring

private theorem third_inner_commute {S : Field} {z : Point}
    (hS : ContDiffAt ℝ 3 S z) (i j k : Fin 2) :
    coordDeriv i (coordDeriv j (coordDeriv k S)) z =
      coordDeriv i (coordDeriv k (coordDeriv j S)) z := by
  have h2 : ContDiffAt ℝ 2 S z := hS.of_le (by norm_num)
  have he : coordDeriv j (coordDeriv k S) =ᶠ[𝓝 z] coordDeriv k (coordDeriv j S) := by
    filter_upwards [h2.eventually (by simp)] with q hq
    exact coordDeriv_commute hq j k
  exact congrArg (fun L => L (Pi.single i 1)) (he.fderiv_eq (𝕜 := ℝ))

private theorem third_cycle {S : Field} {z : Point}
    (hS : ContDiffAt ℝ 3 S z) (i j k : Fin 2) :
    coordDeriv i (coordDeriv j (coordDeriv k S)) z =
      coordDeriv k (coordDeriv i (coordDeriv j S)) z := by
  rw [third_inner_commute hS i j k]
  exact coordDeriv_commute (coordDeriv_contDiffAt (m := 2) hS j) i k

private theorem componentA_partial (S U : Field) (μ : ℂ) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ 2 S z) (hU : ContDiffAt ℝ 3 U z) (i : Fin 2) :
    coordDeriv i (componentA S U μ) z =
      coordDeriv 0 S z*coordDeriv i (coordDeriv 0 S) z-
      coordDeriv 1 S z*coordDeriv i (coordDeriv 1 S) z+
      μ*((coordDeriv i (coordDeriv 0 (coordDeriv 0 U)) z-
        coordDeriv i (coordDeriv 1 (coordDeriv 1 U)) z)/2-
        ((if i = 1 then -(z 1 : ℂ)⁻¹^(2 : ℕ) else 0)*coordDeriv 1 U z+
          (z 1 : ℂ)⁻¹*coordDeriv i (coordDeriv 1 U) z)) := by
  have hS0 := (coordDeriv_hasFDerivAt hS 0).differentiableAt
  have hS1 := (coordDeriv_hasFDerivAt hS 1).differentiableAt
  have hU1 := (coordDeriv_hasFDerivAt (hU.of_le (by norm_num)) 1).differentiableAt
  have hU00 := (coordDeriv_hasFDerivAt (coordDeriv_contDiffAt (m := 2) hU 0) 0).differentiableAt
  have hU11 := (coordDeriv_hasFDerivAt (coordDeriv_contDiffAt (m := 2) hU 1) 1).differentiableAt
  have hInv := (inv_height_hasFDerivAt z hz).differentiableAt
  have hProd : DifferentiableAt ℝ (fun w => (w 1 : ℂ)⁻¹*coordDeriv 1 U w) z :=
    hInv.fun_mul hU1
  have hInner : DifferentiableAt ℝ (fun w =>
      (1/2:ℂ)*(coordDeriv 0 (coordDeriv 0 U) w-coordDeriv 1 (coordDeriv 1 U) w)-
      (w 1 : ℂ)⁻¹*coordDeriv 1 U w) z :=
    ((hU00.fun_sub hU11).const_mul (1/2:ℂ)).fun_sub hProd
  have hMu := hInner.const_mul μ
  have hform : componentA S U μ = (fun w =>
      (1/2:ℂ)*(coordDeriv 0 S w*coordDeriv 0 S w-coordDeriv 1 S w*coordDeriv 1 S w)+
      μ*((1/2:ℂ)*(coordDeriv 0 (coordDeriv 0 U) w-coordDeriv 1 (coordDeriv 1 U) w)-
        (w 1 : ℂ)⁻¹*coordDeriv 1 U w)) := by
    funext w
    simp only [componentA]
    ring
  rw [hform,partial_add,partial_const_mul,partial_sub,partial_mul hS0 hS0,
    partial_mul hS1 hS1,partial_const_mul,partial_sub,partial_const_mul,partial_sub,
    inv_mul_partial hz hU1]
  all_goals first | assumption | fun_prop | ring

private theorem componentB_partial (S U : Field) (μ : ℂ) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ 2 S z) (hU : ContDiffAt ℝ 3 U z) (i : Fin 2) :
    coordDeriv i (componentB S U μ) z =
      coordDeriv i (coordDeriv 0 S) z*coordDeriv 1 S z+
      coordDeriv 0 S z*coordDeriv i (coordDeriv 1 S) z+
      μ*(coordDeriv i (coordDeriv 0 (coordDeriv 1 U)) z+
        ((if i = 1 then -(z 1 : ℂ)⁻¹^(2 : ℕ) else 0)*coordDeriv 0 U z+
          (z 1 : ℂ)⁻¹*coordDeriv i (coordDeriv 0 U) z)) := by
  have hS0 := (coordDeriv_hasFDerivAt hS 0).differentiableAt
  have hS1 := (coordDeriv_hasFDerivAt hS 1).differentiableAt
  have hU0 := (coordDeriv_hasFDerivAt (hU.of_le (by norm_num)) 0).differentiableAt
  have hU01 := (coordDeriv_hasFDerivAt (coordDeriv_contDiffAt (m := 2) hU 1) 0).differentiableAt
  have hInv := (inv_height_hasFDerivAt z hz).differentiableAt
  have hProd : DifferentiableAt ℝ (fun w => (w 1 : ℂ)⁻¹*coordDeriv 0 U w) z :=
    hInv.fun_mul hU0
  have hInner : DifferentiableAt ℝ (fun w =>
      coordDeriv 0 (coordDeriv 1 U) w+(w 1 : ℂ)⁻¹*coordDeriv 0 U w) z :=
    hU01.fun_add hProd
  have hMu := hInner.const_mul μ
  unfold componentB
  rw [partial_add,partial_mul hS0 hS1,partial_const_mul,partial_add,inv_mul_partial hz hU0]
  all_goals first | assumption | fun_prop

/-- Exact horizontal divergence of the actual coordinate tensor, retaining curvature. -/
theorem components_divergence_x (S U : Field) (μ : ℂ) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ 2 S z) (hU : ContDiffAt ℝ 3 U z) :
    2*(z 1 : ℂ)^(2 : ℕ)*(coordDeriv 0 (componentA S U μ) z+coordDeriv 1 (componentB S U μ) z) =
      2*coordDeriv 0 S z*scalarLaplacian S z+
        μ*(coordDeriv 0 (scalarLaplacian U) z-2*coordDeriv 0 U z) := by
  rw [componentA_partial S U μ z hz hS hU,componentB_partial S U μ z hz hS hU,
    scalarLaplacian_eq S z hz,scalarLaplacian_partial U z hz hU]
  simp only [Fin.zero_ne_one,ite_false,ite_true]
  rw [coordDeriv_commute hS 1 0,
    coordDeriv_commute (coordDeriv_contDiffAt (m := 2) hU 1) 1 0,
    coordDeriv_commute (hU.of_le (by norm_num)) 1 0]
  have hy : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  field_simp
  ring

/-- Exact vertical divergence of the actual coordinate tensor, retaining curvature. -/
theorem components_divergence_y (S U : Field) (μ : ℂ) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ 2 S z) (hU : ContDiffAt ℝ 3 U z) :
    2*(z 1 : ℂ)^(2 : ℕ)*(coordDeriv 0 (componentB S U μ) z-coordDeriv 1 (componentA S U μ) z) =
      2*coordDeriv 1 S z*scalarLaplacian S z+
        μ*(coordDeriv 1 (scalarLaplacian U) z-2*coordDeriv 1 U z) := by
  rw [componentB_partial S U μ z hz hS hU,componentA_partial S U μ z hz hS hU,
    scalarLaplacian_eq S z hz,scalarLaplacian_partial U z hz hU]
  simp only [Fin.zero_ne_one,ite_false,ite_true]
  rw [coordDeriv_commute hS 1 0,← third_cycle hU 0 0 1]
  have hy : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  field_simp
  ring

/-- The original scalar eigenfield at the actual Xi occurrence. -/
def source (q : XiZeroCopy) : Field :=
  D4BMLiteralCusp.scalar (D4BMGlobalAngularResponse.center q)

/-- Its original Laplace--Beltrami eigenvalue. -/
def eigenvalue (q : XiZeroCopy) : ℂ :=
  -D4BMLiteralCusp.scalarQ (D4BMGlobalAngularResponse.center q)

/-- The first component of the specific source decomposition remainder. -/
def defectA (q : XiZeroCopy) : Field :=
  componentA (source q) (coordinateResponse q) (eigenvalue q)

/-- The second component of the same specific remainder. -/
def defectB (q : XiZeroCopy) : Field :=
  componentB (source q) (coordinateResponse q) (eigenvalue q)

private theorem source_eigen (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (source q) z = eigenvalue q*source q z :=
  D4BMLiteralCusp.scalar_equation _ z hz

private theorem response_equation (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (coordinateResponse q) z = 2*coordinateResponse q z-source q z^(2 : ℕ) := by
  have he := coordinateResponse_equation q z hz
  rw [scalarLaplacian_eq _ z hz]
  change D4BMAngularSeries.hyperbolicLaplacian (coordinateResponse q) z = _
  change 2*coordinateResponse q z-D4BMAngularSeries.hyperbolicLaplacian (coordinateResponse q) z =
    source q z^(2 : ℕ) at he
  linear_combination -he

private theorem response_laplacian_partial (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (i : Fin 2) :
    coordDeriv i (scalarLaplacian (coordinateResponse q)) z =
      2*coordDeriv i (coordinateResponse q) z-2*source q z*coordDeriv i (source q) z := by
  have he : scalarLaplacian (coordinateResponse q) =ᶠ[𝓝 z]
      (fun w => 2*coordinateResponse q w-source q w*source q w) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    rw [response_equation q w hw,pow_two]
  change fderiv ℝ (scalarLaplacian (coordinateResponse q)) z (Pi.single i 1) = _
  rw [he.fderiv_eq]
  change coordDeriv i (fun w => 2*coordinateResponse q w-source q w*source q w) z = _
  have hU := (coordinateResponse_smooth q z hz).differentiableAt (by simp)
  have hS := (D4BMLiteralCusp.scalar_contDiffAt (D4BMGlobalAngularResponse.center q) 1 z hz).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (source q) z at hS
  rw [partial_sub,partial_const_mul hU,partial_mul hS hS]
  all_goals first | exact hU.const_mul 2 | exact hS.fun_mul hS | ring

/-- The horizontal Cauchy--Riemann equation is forced by the two actual scalar equations. -/
theorem defect_cauchyRiemann_x (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    coordDeriv 0 (defectA q) z+coordDeriv 1 (defectB q) z = 0 := by
  have he := components_divergence_x (source q) (coordinateResponse q) (eigenvalue q) z hz
    (D4BMLiteralCusp.scalar_contDiffAt _ 2 z hz)
    ((contDiffAt_infty.mp (coordinateResponse_smooth q z hz)) 3)
  rw [source_eigen q z hz,response_laplacian_partial q z hz] at he
  have hzero : 2*(z 1 : ℂ)^(2 : ℕ)*(coordDeriv 0 (defectA q) z+coordDeriv 1 (defectB q) z) = 0 := by
    change 2*(z 1 : ℂ)^(2 : ℕ)*(coordDeriv 0 (componentA _ _ _) z+coordDeriv 1 (componentB _ _ _) z) = 0
    rw [he]
    ring
  exact (mul_eq_zero.mp hzero).resolve_left
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz.ne')))

/-- The vertical Cauchy--Riemann equation retains the second complex polarization. -/
theorem defect_cauchyRiemann_y (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    coordDeriv 0 (defectB q) z-coordDeriv 1 (defectA q) z = 0 := by
  have he := components_divergence_y (source q) (coordinateResponse q) (eigenvalue q) z hz
    (D4BMLiteralCusp.scalar_contDiffAt _ 2 z hz)
    ((contDiffAt_infty.mp (coordinateResponse_smooth q z hz)) 3)
  rw [source_eigen q z hz,response_laplacian_partial q z hz] at he
  have hzero : 2*(z 1 : ℂ)^(2 : ℕ)*(coordDeriv 0 (defectB q) z-coordDeriv 1 (defectA q) z) = 0 := by
    change 2*(z 1 : ℂ)^(2 : ℕ)*(coordDeriv 0 (componentB _ _ _) z-coordDeriv 1 (componentA _ _ _) z) = 0
    rw [he]
    ring
  exact (mul_eq_zero.mp hzero).resolve_left
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz.ne')))

/-- The trace-free part of the actual covariant square of a scalar gradient. -/
def gradientTensor (S : Field) (z : Point) (i j : Fin 2) : ℂ :=
  coordDeriv i S z*coordDeriv j S z-
    (∑ k : Fin 2, ∑ l : Fin 2, (metric z)⁻¹ k l*coordDeriv k S z*coordDeriv l S z)/2*metric z i j

/-- The trace-free Hessian formed with the original metric connection and metric trace. -/
def hessianTensor (U : Field) (z : Point) (i j : Fin 2) : ℂ :=
  covariant (fun k => coordDeriv k U) i j z-scalarLaplacian U z/2*metric z i j

/-- The actual geometric remainder in the proposed source-potential identification. -/
def defectTensor (q : XiZeroCopy) (z : Point) (i j : Fin 2) : ℂ :=
  gradientTensor (source q) z i j+eigenvalue q*hessianTensor (coordinateResponse q) z i j

/-- Both computed components belong to the actual tensor with the original connection. -/
theorem defectTensor_components (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    defectTensor q z = !![defectA q z,defectB q z;defectB q z,-defectA q z] := by
  have hU : ContDiffAt ℝ 2 (coordinateResponse q) z :=
    (contDiffAt_infty.mp (coordinateResponse_smooth q z hz)) 2
  have hy : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  ext i j
  simp only [defectTensor,gradientTensor,hessianTensor,covariant_eq _ z hz,
    scalarLaplacian_eq _ z hz,metric_inverse z hz]
  fin_cases i <;> fin_cases j
  all_goals simp [covariantFormula,metric,defectA,defectB,componentA,componentB,
    Fin.sum_univ_two,coordDeriv_commute hU 1 0]
  all_goals field_simp [hy]
  all_goals ring

private theorem components_differentiable (S U : Field) (μ : ℂ) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ 2 S z) (hU : ContDiffAt ℝ 3 U z) :
    DifferentiableAt ℝ (componentA S U μ) z ∧ DifferentiableAt ℝ (componentB S U μ) z := by
  have hS0 := (coordDeriv_hasFDerivAt hS 0).differentiableAt
  have hS1 := (coordDeriv_hasFDerivAt hS 1).differentiableAt
  have hU0 := (coordDeriv_hasFDerivAt (hU.of_le (by norm_num)) 0).differentiableAt
  have hU1 := (coordDeriv_hasFDerivAt (hU.of_le (by norm_num)) 1).differentiableAt
  have hU00 := (coordDeriv_hasFDerivAt (coordDeriv_contDiffAt (m := 2) hU 0) 0).differentiableAt
  have hU01 := (coordDeriv_hasFDerivAt (coordDeriv_contDiffAt (m := 2) hU 1) 0).differentiableAt
  have hU11 := (coordDeriv_hasFDerivAt (coordDeriv_contDiffAt (m := 2) hU 1) 1).differentiableAt
  have hInv := (inv_height_hasFDerivAt z hz).differentiableAt
  constructor
  · unfold componentA
    simpa only [pow_two,div_eq_mul_inv] using
      (((hS0.fun_mul hS0).fun_sub (hS1.fun_mul hS1)).mul_const (2:ℂ)⁻¹).fun_add
        ((((hU00.fun_sub hU11).mul_const (2:ℂ)⁻¹).fun_sub (hInv.fun_mul hU1)).const_mul μ)
  · exact (hS0.fun_mul hS1).fun_add ((hU01.fun_add (hInv.fun_mul hU0)).const_mul μ)

private theorem coordinate_polarization_holomorphic (A B : Field) (z : ℂ)
    (hA : DifferentiableAt ℝ A (D4BMModularCore.angularCoordinates z))
    (hB : DifferentiableAt ℝ B (D4BMModularCore.angularCoordinates z))
    (hx : coordDeriv 0 A (D4BMModularCore.angularCoordinates z)+
      coordDeriv 1 B (D4BMModularCore.angularCoordinates z)=0)
    (hy : coordDeriv 0 B (D4BMModularCore.angularCoordinates z)-
      coordDeriv 1 A (D4BMModularCore.angularCoordinates z)=0) :
    DifferentiableAt ℂ ((fun w => A w-Complex.I*B w) ∘ D4BMModularCore.angularCoordinates) z := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨(hA.fun_sub (hB.const_mul Complex.I)).comp z
    D4BMModularCore.angularCoordinates.differentiableAt,?_⟩
  have hd (i : Fin 2) :
      coordDeriv i (fun w => A w-Complex.I*B w) (D4BMModularCore.angularCoordinates z) =
        coordDeriv i A (D4BMModularCore.angularCoordinates z)-
          Complex.I*coordDeriv i B (D4BMModularCore.angularCoordinates z) := by
    rw [partial_sub,partial_const_mul hB]
    · exact hA
    · exact hB.const_mul Complex.I
  change fderiv ℝ ((fun w => A w-Complex.I*B w) ∘ D4BMModularCore.angularCoordinates) z
      (D4BMModularCore.direction 1) =
    Complex.I*fderiv ℝ ((fun w => A w-Complex.I*B w) ∘ D4BMModularCore.angularCoordinates) z
      (D4BMModularCore.direction 0)
  rw [D4BMModularCore.angularCoordinates_derivative,D4BMModularCore.angularCoordinates_derivative,hd,hd]
  have hby : coordDeriv 1 B (D4BMModularCore.angularCoordinates z) =
      -coordDeriv 0 A (D4BMModularCore.angularCoordinates z) := by linear_combination hx
  have hay := (sub_eq_zero.mp hy).symm
  rw [hby,hay]
  ring_nf
  simp only [Complex.I_sq,mul_neg_one,neg_neg]

private theorem partial_conj {f : Field} {z : Point}
    (hf : DifferentiableAt ℝ f z) (i : Fin 2) :
    coordDeriv i (fun w => conj (f w)) z = conj (coordDeriv i f z) := by
  have hd := (Complex.conjCLE.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  exact congrArg (fun a : Point →L[ℝ] ℂ => a (Pi.single i 1)) hd

/-- The holomorphic polarization of the actual complex tensor remainder. -/
def holomorphicPolarization (q : XiZeroCopy) : ℂ → ℂ :=
  (fun w => defectA q w-Complex.I*defectB q w) ∘ D4BMModularCore.angularCoordinates

/-- The conjugate of the independent antiholomorphic polarization. -/
def conjugatePolarization (q : XiZeroCopy) : ℂ → ℂ :=
  (fun w => conj (defectA q w)-Complex.I*conj (defectB q w)) ∘ D4BMModularCore.angularCoordinates

/-- The first polarization is genuinely complex differentiable at every positive-height point. -/
theorem holomorphicPolarization_differentiableAt (q : XiZeroCopy) (z : ℂ) (hz : 0 < z.im) :
    DifferentiableAt ℂ (holomorphicPolarization q) z := by
  have hp : 0 < D4BMModularCore.angularCoordinates z 1 := hz
  obtain ⟨hA,hB⟩ := components_differentiable (source q) (coordinateResponse q) (eigenvalue q)
    (D4BMModularCore.angularCoordinates z) hp (D4BMLiteralCusp.scalar_contDiffAt _ 2 _ hp)
    ((contDiffAt_infty.mp (coordinateResponse_smooth q _ hp)) 3)
  exact coordinate_polarization_holomorphic (defectA q) (defectB q) z hA hB
    (defect_cauchyRiemann_x q _ hp) (defect_cauchyRiemann_y q _ hp)

/-- The other complex tensor polarization also supplies a holomorphic field after conjugation. -/
theorem conjugatePolarization_differentiableAt (q : XiZeroCopy) (z : ℂ) (hz : 0 < z.im) :
    DifferentiableAt ℂ (conjugatePolarization q) z := by
  have hp : 0 < D4BMModularCore.angularCoordinates z 1 := hz
  obtain ⟨hA,hB⟩ := components_differentiable (source q) (coordinateResponse q) (eigenvalue q)
    (D4BMModularCore.angularCoordinates z) hp (D4BMLiteralCusp.scalar_contDiffAt _ 2 _ hp)
    ((contDiffAt_infty.mp (coordinateResponse_smooth q _ hp)) 3)
  change DifferentiableAt ℝ (defectA q) _ at hA
  change DifferentiableAt ℝ (defectB q) _ at hB
  apply coordinate_polarization_holomorphic (fun w => conj (defectA q w))
    (fun w => conj (defectB q w)) z
    (Complex.conjCLE.differentiableAt.comp _ hA) (Complex.conjCLE.differentiableAt.comp _ hB)
  · rw [partial_conj hA,partial_conj hB,← map_add,defect_cauchyRiemann_x q _ hp,map_zero]
  · rw [partial_conj hB,partial_conj hA,← map_sub,defect_cauchyRiemann_y q _ hp,map_zero]

end
end RHTower.D4BMAngularTwoTensor

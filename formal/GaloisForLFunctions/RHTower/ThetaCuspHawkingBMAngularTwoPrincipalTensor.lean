import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularTwoTensor
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamLaurentMaster

/-!
# Exact cancellation of the complete cusp principal tensor

The original scalar's two Weyl powers and its constructed three-power inverse
cancel in the trace-free tensor with the actual metric and connection. The
proof combines the genuine Euler derivative with the already established
shift-two response equation. All principal coefficients and the mixed Weyl
term survive until the exact algebraic cancellation. Nonresonance is derived
for every original Xi occurrence.
-/

open Complex Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMAngularTwoPrincipalTensor
open D4BMAngularSeries D4BMQuadraticMixedSource D4BMAngularTwoTensor D4BMHorizon
noncomputable section
set_option autoImplicit false

private abbrev Field := (Fin 2 → ℝ) → ℂ

private def monomial (a p : ℂ) : Field := fun z => a*(z 1:ℂ)^p

private theorem monomial_smooth (a p : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (monomial a p) z :=
  contDiffAt_const.mul ((height_cpow_contDiffOn p ∞).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz))

private theorem monomial_partial_zero (a p : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 0 (monomial a p) z = 0 := by
  unfold monomial
  rw [coordDeriv,((height_cpow_hasFDerivAt p z hz).const_mul a).fderiv]
  simp [D4BMAngularSeries.gradient,smul_eq_mul]

private theorem monomial_euler (a p : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (z 1:ℂ)*coordDeriv 1 (monomial a p) z = p*monomial a p z := by
  have hn : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  unfold monomial
  rw [coordDeriv,((height_cpow_hasFDerivAt p z hz).const_mul a).fderiv]
  simp only [smul_apply,smul_eq_mul]
  simp [D4BMAngularSeries.gradient]
  have hp : (z 1:ℂ)*(z 1:ℂ)^(p-1) = (z 1:ℂ)^p := by
    calc
      _ = (z 1:ℂ)^(1:ℂ)*(z 1:ℂ)^(p-1) := by rw [Complex.cpow_one]
      _ = (z 1:ℂ)^(1+(p-1)) := (Complex.cpow_add _ _ hn).symm
      _ = _ := by congr 1; ring
  calc
    _ = (p*a)*((z 1:ℂ)*(z 1:ℂ)^(p-1)) := by ring
    _ = _ := by rw [hp]; ring

private theorem partial_add {f g : Field} {z : Fin 2 → ℝ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    coordDeriv i (fun w => f w+g w) z = coordDeriv i f z+coordDeriv i g z := by
  simp only [coordDeriv,fderiv_fun_add hf hg,add_apply]

private def principalField (r A D : ℂ) : Field :=
  fun z => monomial A r z+monomial D (1-r) z

private theorem principal_smooth (r A D : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (principalField r A D) z :=
  (monomial_smooth A r z hz).add (monomial_smooth D (1-r) z hz)

private theorem principal_horizontal (r A D : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 0 (principalField r A D) z = 0 := by
  change coordDeriv 0 (fun w => monomial A r w+monomial D (1-r) w) z = 0
  rw [partial_add ((monomial_smooth A r z hz).differentiableAt (by simp))
    ((monomial_smooth D (1-r) z hz).differentiableAt (by simp)),
    monomial_partial_zero A r z hz,monomial_partial_zero D (1-r) z hz,add_zero]

private theorem principal_euler (r A D : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (z 1:ℂ)*coordDeriv 1 (principalField r A D) z =
      principalField r (r*A) ((1-r)*D) z := by
  change (z 1:ℂ)*coordDeriv 1 (fun w => monomial A r w+monomial D (1-r) w) z = _
  rw [partial_add ((monomial_smooth A r z hz).differentiableAt (by simp))
    ((monomial_smooth D (1-r) z hz).differentiableAt (by simp)),mul_add,
    monomial_euler A r z hz,monomial_euler D (1-r) z hz]
  simp only [principalField,monomial]
  ring

private theorem response_smooth (r A D : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (cuspPowerResponse 2 r A D) z :=
  ((monomial_smooth _ _ z hz).add (monomial_smooth _ _ z hz)).add (monomial_smooth _ _ z hz)

private theorem response_partial (r A D : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) (i : Fin 2) :
    coordDeriv i (cuspPowerResponse 2 r A D) z =
      coordDeriv i (monomial (A^2/((2*r)*(2*r-1)-2)) (2*r)) z+
      coordDeriv i (monomial (2*A*D/(-2)) 1) z+
      coordDeriv i (monomial (D^2/((2-2*r)*(1-2*r)-2)) (2-2*r)) z := by
  have he : cuspPowerResponse 2 r A D = fun w =>
      monomial (A^2/((2*r)*(2*r-1)-2)) (2*r) w+
      monomial (2*A*D/(-2)) 1 w+
      monomial (D^2/((2-2*r)*(1-2*r)-2)) (2-2*r) w := by
    funext w
    simp only [cuspPowerResponse,powerResponse,monomial]
    congr 2 <;> ring
  rw [he,partial_add,partial_add]
  all_goals
    first
    | exact (monomial_smooth _ _ z hz).differentiableAt (by simp)
    | exact ((monomial_smooth _ _ z hz).add (monomial_smooth _ _ z hz)).differentiableAt (by simp)

private theorem response_horizontal (r A D : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 0 (cuspPowerResponse 2 r A D) z = 0 := by
  rw [response_partial r A D z hz]
  simp only [monomial_partial_zero _ _ z hz,add_zero]

private theorem response_euler (r A D : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (z 1:ℂ)*coordDeriv 1 (cuspPowerResponse 2 r A D) z =
      (2*r)*monomial (A^2/((2*r)*(2*r-1)-2)) (2*r) z+
      monomial (2*A*D/(-2)) 1 z+
      (2-2*r)*monomial (D^2/((2-2*r)*(1-2*r)-2)) (2-2*r) z := by
  rw [response_partial r A D z hz,mul_add,mul_add]
  simp only [monomial_euler _ _ z hz,one_mul]

private theorem principal_balance (q : XiZeroCopy) (A D : ℂ) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) :
    (q.1:ℂ)*((q.1:ℂ)-1)*((principalField (q.1:ℂ) A D z)^2+
      2*cuspPowerResponse 2 (q.1:ℂ) A D z+
      2*(z 1:ℂ)*coordDeriv 1 (cuspPowerResponse 2 (q.1:ℂ) A D) z) =
        ((z 1:ℂ)*coordDeriv 1 (principalField (q.1:ℂ) A D) z)^2 := by
  obtain ⟨h0,h2⟩ := D4BMScalarStream.xi_cusp_two_denominators q
  let r : ℂ := q.1
  let d0 := (2*r)*(2*r-1)-2
  let d2 := (2-2*r)*(1-2*r)-2
  change d0 ≠ 0 at h0
  change d2 ≠ 0 at h2
  have hp : r*(r-1)*(1+2*(1+2*r)/d0) = r^2 := by
    calc
      _ = (r*(r-1)*(d0+2*(1+2*r)))/d0 := by
        simp only [mul_add,add_div,mul_div_assoc,div_self h0,mul_one]
      _ = _ := (div_eq_iff h0).2 (by dsimp only [d0]; ring)
  have hm : r*(r-1)*(1+2*(1+(2-2*r))/d2) = (1-r)^2 := by
    calc
      _ = (r*(r-1)*(d2+2*(1+(2-2*r))))/d2 := by
        simp only [mul_add,add_div,mul_div_assoc,div_self h2,mul_one]
      _ = _ := (div_eq_iff h2).2 (by dsimp only [d2]; ring)
  dsimp only [r,d0,d2] at hp hm
  rw [principal_euler _ _ _ z hz]
  have h1 := cusp_power_square (q.1:ℂ) A D z hz
  have h3 := cusp_power_square (q.1:ℂ) ((q.1:ℂ)*A) ((1-(q.1:ℂ))*D) z hz
  change _ = (principalField (q.1:ℂ) A D z)^2 at h1
  change _ = (principalField (q.1:ℂ) ((q.1:ℂ)*A) ((1-(q.1:ℂ))*D) z)^2 at h3
  rw [← h1,← h3,show 2*(z 1:ℂ)*coordDeriv 1 (cuspPowerResponse 2 (q.1:ℂ) A D) z =
    2*((z 1:ℂ)*coordDeriv 1 (cuspPowerResponse 2 (q.1:ℂ) A D) z) by ring,
    response_euler _ _ _ z hz]
  simp only [cuspPowerResponse,powerResponse,monomial]
  have he : (2-2*(q.1:ℂ))*(2-2*(q.1:ℂ)-1)-2 =
      (2-2*(q.1:ℂ))*(1-2*(q.1:ℂ))-2 := by ring
  rw [he]
  norm_num only [sub_self,mul_zero,zero_sub]
  linear_combination (A^2*(z 1:ℂ)^(2*(q.1:ℂ)))*hp+
    (D^2*(z 1:ℂ)^(2-2*(q.1:ℂ)))*hm

private theorem partial_neg (f : Field) (i : Fin 2) (z : Fin 2 → ℝ) :
    coordDeriv i (fun w => -f w) z = -coordDeriv i f z := by
  simp only [coordDeriv,fderiv_fun_neg,neg_apply]

private theorem partial_neg_fun (f : Field) (i : Fin 2) :
    coordDeriv i (fun w => -f w) = fun w => -coordDeriv i f w :=
  funext (partial_neg f i)

private theorem response_second_horizontal (r A D : ℂ) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) (i : Fin 2) :
    coordDeriv i (coordDeriv 0 (cuspPowerResponse 2 r A D)) z = 0 := by
  have he : coordDeriv 0 (cuspPowerResponse 2 r A D) =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    exact response_horizontal r A D w hw
  rw [coordDeriv,he.fderiv_eq]
  simp

/-- The complete original three-power response cancels both principal tensor components. -/
private theorem principal_components_zero (q : XiZeroCopy) (A D : ℂ) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) :
    componentA (principalField (q.1:ℂ) A D) (fun w => -cuspPowerResponse 2 (q.1:ℂ) A D w)
      ((q.1:ℂ)*((q.1:ℂ)-1)) z = 0 ∧
    componentB (principalField (q.1:ℂ) A D) (fun w => -cuspPowerResponse 2 (q.1:ℂ) A D w)
      ((q.1:ℂ)*((q.1:ℂ)-1)) z = 0 := by
  have hy : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hxx := response_second_horizontal (q.1:ℂ) A D z hz 0
  have hxy : coordDeriv 0 (coordDeriv 1 (cuspPowerResponse 2 (q.1:ℂ) A D)) z = 0 := by
    rw [coordDeriv_commute ((contDiffAt_infty.mp (response_smooth (q.1:ℂ) A D z hz)) 2) 0 1]
    exact response_second_horizontal (q.1:ℂ) A D z hz 1
  constructor
  · have he := D4BMScalarStream.xi_cusp_two_response_equation q A D z hz
    change (z 1:ℂ)^2*(coordDeriv 0 (coordDeriv 0 (cuspPowerResponse 2 (q.1:ℂ) A D)) z+
      coordDeriv 1 (coordDeriv 1 (cuspPowerResponse 2 (q.1:ℂ) A D)) z)-
      2*cuspPowerResponse 2 (q.1:ℂ) A D z = (principalField (q.1:ℂ) A D z)^2 at he
    rw [hxx,zero_add] at he
    have hb := principal_balance q A D z hz
    have hn : 2*(z 1:ℂ)^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)
    apply (mul_eq_zero.mp (show 2*(z 1:ℂ)^2*
      componentA (principalField (q.1:ℂ) A D) (fun w => -cuspPowerResponse 2 (q.1:ℂ) A D w)
        ((q.1:ℂ)*((q.1:ℂ)-1)) z = 0 from ?_)).resolve_left hn
    simp only [componentA,principal_horizontal _ _ _ z hz,zero_pow (by norm_num : 2 ≠ 0),zero_sub]
    simp_rw [partial_neg_fun,partial_neg]
    rw [hxx,neg_zero,zero_sub]
    field_simp [hy]
    linear_combination hb+((q.1:ℂ)*((q.1:ℂ)-1))*he
  · simp only [componentB,principal_horizontal _ _ _ z hz,zero_mul]
    simp_rw [partial_neg_fun,partial_neg]
    rw [hxy,response_horizontal _ _ _ z hz]
    ring

private theorem principal_eq (q : XiZeroCopy) :
    D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q) =
      principalField (q.1:ℂ)
        (d4BMCompletedEisensteinCuspConstantCoefficient (D4BMGlobalAngularResponse.center q) true)
        (d4BMCompletedEisensteinCuspConstantCoefficient (D4BMGlobalAngularResponse.center q) false) := by
  funext z
  have hm : d4BMCompletedEisensteinCuspWeylExponent (D4BMGlobalAngularResponse.center q) false = 1-(q.1:ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,D4BMGlobalAngularResponse.center]
    ring
  have hp : d4BMCompletedEisensteinCuspWeylExponent (D4BMGlobalAngularResponse.center q) true = (q.1:ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,D4BMGlobalAngularResponse.center]
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,
    mul_one,hm,hp,principalField,monomial]
  ring

private theorem eigenvalue_eq (q : XiZeroCopy) :
    eigenvalue q = (q.1:ℂ)*((q.1:ℂ)-1) := by
  simp only [eigenvalue,D4BMLiteralCusp.scalarQ,D4BMGlobalAngularResponse.center]
  ring

/-- Both actual principal tensor components vanish at every positive-height point. -/
theorem actual_principal_components_zero (q : XiZeroCopy) (z : UpperHalfPlane) :
    componentA (D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q))
      (fun w => -D4BMAngularTwo.cuspResponse q w) (eigenvalue q) (D4BMGlobalAngularResponse.coordinates z) = 0 ∧
    componentB (D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q))
      (fun w => -D4BMAngularTwo.cuspResponse q w) (eigenvalue q) (D4BMGlobalAngularResponse.coordinates z) = 0 := by
  rw [principal_eq,eigenvalue_eq]
  exact principal_components_zero q _ _ _ z.im_pos

open D4BMHorizon

private theorem tensor_components (S U : Field) (μ : ℂ) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) (hU : ContDiffAt ℝ 2 U z) :
    (fun i j : Fin 2 => gradientTensor S z i j+μ*hessianTensor U z i j) =
      !![componentA S U μ z,componentB S U μ z;componentB S U μ z,-componentA S U μ z] := by
  have hy : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  ext i j
  simp only [gradientTensor,hessianTensor,covariant_eq _ z hz,
    scalarLaplacian_eq _ z hz,metric_inverse z hz]
  fin_cases i <;> fin_cases j
  all_goals simp [covariantFormula,metric,componentA,componentB,
    Fin.sum_univ_two,coordDeriv_commute hU 1 0]
  all_goals field_simp [hy]
  all_goals ring

/-- The complete original cusp principal tensor vanishes with the actual metric and connection. -/
theorem actual_principal_tensor_zero (q : XiZeroCopy) (z : UpperHalfPlane) :
    (fun i j : Fin 2 =>
      gradientTensor (D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q))
        (D4BMGlobalAngularResponse.coordinates z) i j+
      eigenvalue q*hessianTensor (fun w => -D4BMAngularTwo.cuspResponse q w)
        (D4BMGlobalAngularResponse.coordinates z) i j) = 0 := by
  have hU : ContDiffAt ℝ 2 (fun w => -D4BMAngularTwo.cuspResponse q w)
      (D4BMGlobalAngularResponse.coordinates z) :=
    (contDiffAt_infty.mp ((response_smooth _ _ _ _ z.im_pos).neg)) 2
  rw [tensor_components _ _ _ _ z.im_pos hU]
  obtain ⟨hA,hB⟩ := actual_principal_components_zero q z
  rw [hA,hB]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end
end RHTower.D4BMAngularTwoPrincipalTensor

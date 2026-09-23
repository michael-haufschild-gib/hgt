import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticResidualGreen
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticContactBalance

/-! Native physical transport of the literal quartic contact balance. The proof
factors the retained spin-two operator before taking finite convolutions, so the
analytic Weyl coefficients remain opaque. The original cutoff subtraction and
all Mellin terms satisfy the same balance. Physical Green transport then gives
an exact JRQ period identity at the unchanged Hawking parameter. This angular
identity does not assert cancellation of the complete nonlinear left-QNM action. -/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMQuarticNativeBalance
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMSquareCuspJets
open D4BMJointSource D4BMQuarticPrincipalExpansion D4BMQuarticCutoffMellin
open D4BMQuarticContactBalance D4BMQuarticResidualGreen
noncomputable section
set_option autoImplicit false

private def convolve (a b : Fin 3 → ℂ) : Fin 5 → ℂ :=
  ![a 0*b 0,a 0*b 1+a 1*b 0,a 0*b 2+a 1*b 1+a 2*b 0,a 1*b 2+a 2*b 1,a 2*b 2]
private def qcoeff (A B : ℂ) : Fin 3 → ℂ := ![B^(2 : ℕ)/2,B*A,A^(2 : ℕ)/2]
private def rexponent (s : ℂ) : Fin 3 → ℂ := ![2-2*s,1,2*s]
private def kexponent (s : ℂ) (j : Fin 5) : ℂ := 4-(j:ℂ)+(2*(j:ℂ)-4)*s
private def jcoeff (s A B : ℂ) (i : Fin 3) : ℂ :=
  let c := 7*((s-1/2)^(2 : ℕ)-1/4)-2
  let r := rexponent s i
  (c-2*r*(r-1))*qcoeff A B i/8
private def rcoeff (s A B : ℂ) (i : Fin 3) : ℂ :=
  let r := rexponent s i
  (-r)*(r-1)*(r*(r-1)-2)*qcoeff A B i
private def coefficient (s A B : ℂ) (slot : Fin 6) : Fin 5 → ℂ :=
  let c := 7*((s-1/2)^(2 : ℕ)-1/4)-2
  let Q2 := convolve (qcoeff A B) (qcoeff A B)
  let J2 := convolve (jcoeff s A B) (jcoeff s A B)
  let LJ := fun i => rexponent s i*(rexponent s i-1)*jcoeff s A B i
  let H := fun j => 2*J2 j+(c*(c-4)/96)*Q2 j
  ![Q2,J2,fun j => (1/2:ℂ)*(kexponent s j*(kexponent s j-1)*J2 j)+
      (-1:ℂ)*convolve (jcoeff s A B) LJ j,
    convolve (jcoeff s A B) (rcoeff s A B),H,
    fun j => kexponent s j*(kexponent s j-1)*H j] slot

private theorem convolve_linear (a b d e : Fin 3 → ℂ) (t u v : ℂ) (j : Fin 5) :
    convolve a (fun i => t*b i+u*d i+v*e i) j=
      t*convolve a b j+u*convolve a d j+v*convolve a e j := by
  fin_cases j <;> norm_num [convolve] <;> ring

private theorem rcoeff_factor (s A B : ℂ) :
    rcoeff s A B=fun i =>
      4*(rexponent s i*(rexponent s i-1)*jcoeff s A B i)+
      2*(7*((s-1/2)^(2 : ℕ)-1/4)-6)*jcoeff s A B i+
      (-(7*((s-1/2)^(2 : ℕ)-1/4)-2)*(7*((s-1/2)^(2 : ℕ)-1/4)-6)/4)*qcoeff A B i := by
  funext i
  dsimp only [rcoeff,jcoeff]
  ring

private theorem qcoeff_balance (s A B : ℂ) (j : Fin 5) :
    let lam := (s-1/2)^(2 : ℕ)-1/4
    kexponent s j*(kexponent s j-1)*convolve (qcoeff A B) (qcoeff A B) j=
      (13*lam-6)*convolve (qcoeff A B) (qcoeff A B) j-
        24*convolve (jcoeff s A B) (qcoeff A B) j := by
  dsimp only
  fin_cases j <;> norm_num [convolve,qcoeff,jcoeff,rexponent,kexponent,Matrix.cons_val_two] <;> ring

private theorem coefficient_balance (s A B : ℂ) (j : Fin 5) :
    let lam := (s-1/2)^(2 : ℕ)-1/4
    let c := 7*lam-2
    coefficient s A B 3 j=coefficient s A B 5 j+2*(c-4)*coefficient s A B 1 j-
      4*coefficient s A B 2 j-(c*(c-4)/96)*(13*lam-6)*coefficient s A B 0 j := by
  dsimp only
  have hq := qcoeff_balance s A B j
  have hr := convolve_linear (jcoeff s A B)
    (fun i => rexponent s i*(rexponent s i-1)*jcoeff s A B i)
    (jcoeff s A B) (qcoeff A B) 4
    (2*(7*((s-1/2)^(2 : ℕ)-1/4)-6))
    (-(7*((s-1/2)^(2 : ℕ)-1/4)-2)*(7*((s-1/2)^(2 : ℕ)-1/4)-6)/4) j
  rw [← rcoeff_factor] at hr
  change convolve (jcoeff s A B) (rcoeff s A B) j=_
  rw [hr]
  change _=kexponent s j*(kexponent s j-1)*
    (2*convolve (jcoeff s A B) (jcoeff s A B) j+
      ((7*((s-1/2)^(2 : ℕ)-1/4)-2)*(7*((s-1/2)^(2 : ℕ)-1/4)-2-4)/96)*convolve (qcoeff A B) (qcoeff A B) j)+
    2*(7*((s-1/2)^(2 : ℕ)-1/4)-2-4)*convolve (jcoeff s A B) (jcoeff s A B) j-
    4*((1/2:ℂ)*(kexponent s j*(kexponent s j-1)*convolve (jcoeff s A B) (jcoeff s A B) j)+
      (-1:ℂ)*convolve (jcoeff s A B) (fun i => rexponent s i*(rexponent s i-1)*jcoeff s A B i) j)-
    ((7*((s-1/2)^(2 : ℕ)-1/4)-2)*(7*((s-1/2)^(2 : ℕ)-1/4)-2-4)/96)*
      (13*((s-1/2)^(2 : ℕ)-1/4)-6)*convolve (qcoeff A B) (qcoeff A B) j
  linear_combination -((7*((s-1/2)^(2 : ℕ)-1/4)-2)*(7*((s-1/2)^(2 : ℕ)-1/4)-6)/96)*hq

private theorem actual_coefficient (q : XiZeroCopy) (slot : Fin 6) (j : Fin 5) :
    quarticPrincipalCoefficient q slot j=coefficient (q.1:ℂ)
      (reflectedCompletedLambda (2*(q.1:ℂ))) (reflectedCompletedLambda (2*(q.1:ℂ)-1)) slot j := rfl

/-- The literal five-coefficient contact balance retains every original Weyl product. -/
theorem quarticPrincipalCoefficient_balance (q : XiZeroCopy) (j : Fin 5) :
    let c := 7*((center q)^(2 : ℕ)-1/4)-2
    let a := c*(c-4)/96
    quarticPrincipalCoefficient q 3 j=quarticPrincipalCoefficient q 5 j+
      2*(c-4)*quarticPrincipalCoefficient q 1 j-4*quarticPrincipalCoefficient q 2 j-
        a*(13*((center q)^(2 : ℕ)-1/4)-6)*quarticPrincipalCoefficient q 0 j := by
  simp_rw [actual_coefficient]
  exact coefficient_balance (q.1:ℂ) _ _ j

private theorem weighted_coefficient_balance (q : XiZeroCopy) (w : Fin 5 → ℂ) :
    let c := 7*((center q)^(2 : ℕ)-1/4)-2
    let d := (c*(c-4)/96)*(13*((center q)^(2 : ℕ)-1/4)-6)
    (∑ j,quarticPrincipalCoefficient q 3 j*w j)=
      (∑ j,quarticPrincipalCoefficient q 5 j*w j)+
      2*(c-4)*(∑ j,quarticPrincipalCoefficient q 1 j*w j)-
      4*(∑ j,quarticPrincipalCoefficient q 2 j*w j)-
      d*(∑ j,quarticPrincipalCoefficient q 0 j*w j) := by
  dsimp only
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [quarticPrincipalCoefficient_balance]
  ring

/-- The complete principal contact balance, before any height subtraction. -/
theorem quarticContactPrincipal_balance (q : XiZeroCopy) (z : UpperHalfPlane) :
    let c := 7*((center q)^(2 : ℕ)-1/4)-2
    let d := (c*(c-4)/96)*(13*((center q)^(2 : ℕ)-1/4)-6)
    quarticContactPrincipal q 3 (coordinates z)=
      quarticContactPrincipal q 5 (coordinates z)+2*(c-4)*quarticContactPrincipal q 1 (coordinates z)-
      4*quarticContactPrincipal q 2 (coordinates z)-d*quarticContactPrincipal q 0 (coordinates z) := by
  simp_rw [quarticContactPrincipal_eq_power_sum]
  exact weighted_coefficient_balance q _

/-- The original source cutoff preserves the exact residual contact balance. -/
theorem quarticContactResidual_balance (q : XiZeroCopy) (z : UpperHalfPlane) :
    let c := 7*((center q)^(2 : ℕ)-1/4)-2
    let d := (c*(c-4)/96)*(13*((center q)^(2 : ℕ)-1/4)-6)
    quarticContactResidual q 3 (coordinates z)=
      quarticContactResidual q 5 (coordinates z)+2*(c-4)*quarticContactResidual q 1 (coordinates z)-
      4*quarticContactResidual q 2 (coordinates z)-d*quarticContactResidual q 0 (coordinates z) := by
  dsimp only
  simp only [quarticContactResidual]
  rw [quarticContactField_balance,quarticContactPrincipal_balance]
  ring

/-- The native physical period of JRQ retains the full contact identity and every Mellin term. -/
theorem quarticNativePhysicalPeriod_balance (q : XiZeroCopy) :
    let c := 7*((center q)^(2 : ℕ)-1/4)-2
    let d := (c*(c-4)/96)*(13*((center q)^(2 : ℕ)-1/4)-6)
    quarticNativePhysicalPeriod q 3=quarticNativePhysicalPeriod q 5+
      2*(c-4)*quarticNativePhysicalPeriod q 1-4*quarticNativePhysicalPeriod q 2-
      d*quarticNativePhysicalPeriod q 0 := by
  let b : ℂ := 2*(7*((center q)^(2 : ℕ)-1/4)-6)
  let d : ℂ := ((7*((center q)^(2 : ℕ)-1/4)-2)*(7*((center q)^(2 : ℕ)-1/4)-6)/96)*
    (13*((center q)^(2 : ℕ)-1/4)-6)
  let f := fun slot z => scalar (physicalAngularParameter q) (coordinates z)*
    quarticContactResidual q slot (coordinates z)
  have hi (slot : Fin 6) : Integrable (f slot) D4BMModularCore.measure :=
    quarticContactResidual_scalar_integrable q slot (physicalAngularParameter q)
  have he (z : UpperHalfPlane) : f 3 z=f 5 z+b*f 1 z-4*f 2 z-d*f 0 z := by
    dsimp only [f]
    rw [quarticContactResidual_balance]
    dsimp only [b,d]
    ring
  have hI : (∫ z,f 3 z ∂D4BMModularCore.measure)=
      (∫ z,f 5 z ∂D4BMModularCore.measure)+b*(∫ z,f 1 z ∂D4BMModularCore.measure)-
      4*(∫ z,f 2 z ∂D4BMModularCore.measure)-d*(∫ z,f 0 z ∂D4BMModularCore.measure) := by
    simp_rw [he]
    rw [integral_sub (f := fun z => f 5 z+b*f 1 z-4*f 2 z) (g := fun z => d*f 0 z)
      (((hi 5).add ((hi 1).const_mul b)).sub ((hi 2).const_mul 4)) ((hi 0).const_mul d),
      integral_sub (f := fun z => f 5 z+b*f 1 z) (g := fun z => 4*f 2 z)
        ((hi 5).add ((hi 1).const_mul b)) ((hi 2).const_mul 4),
      integral_add (f := fun z => f 5 z) (g := fun z => b*f 1 z) (hi 5) ((hi 1).const_mul b)]
    simp only [integral_const_mul]
  have hM := weighted_coefficient_balance q (fun j =>
    nativeCutoffMellinContinuation (quarticPhysicalMellinExponent q j))
  dsimp only [f,b,d] at hI
  unfold quarticNativePhysicalPeriod
  dsimp only
  linear_combination hI-reflectedCompletedLambda ((q.1:ℂ)-1)*hM

private theorem residual_H (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    let c := 7*((center q)^(2 : ℕ)-1/4)-2
    quarticContactResidual q 4 z=2*quarticContactResidual q 1 z+
      (c*(c-4)/96)*quarticContactResidual q 0 z := by
  change (2*quarticContactField q 1 z+_ *quarticContactField q 0 z)-
    cutoff z*(2*quarticContactPrincipal q 1 z+_ *quarticContactPrincipal q 0 z)=_
  simp only [quarticContactResidual]
  ring

/-- The original H combination survives the native physical finite part. -/
theorem quarticNativePhysicalPeriod_H (q : XiZeroCopy) :
    let c := 7*((center q)^(2 : ℕ)-1/4)-2
    quarticNativePhysicalPeriod q 4=2*quarticNativePhysicalPeriod q 1+
      (c*(c-4)/96)*quarticNativePhysicalPeriod q 0 := by
  let a : ℂ := (7*((center q)^(2 : ℕ)-1/4)-2)*(7*((center q)^(2 : ℕ)-1/4)-2-4)/96
  have hc (j : Fin 5) : quarticPrincipalCoefficient q 4 j=
      2*quarticPrincipalCoefficient q 1 j+a*quarticPrincipalCoefficient q 0 j := rfl
  have hI : (∫ z : UpperHalfPlane,scalar (physicalAngularParameter q) (coordinates z)*
      quarticContactResidual q 4 (coordinates z) ∂D4BMModularCore.measure)=
      2*(∫ z : UpperHalfPlane,scalar (physicalAngularParameter q) (coordinates z)*
        quarticContactResidual q 1 (coordinates z) ∂D4BMModularCore.measure)+
      a*(∫ z : UpperHalfPlane,scalar (physicalAngularParameter q) (coordinates z)*
        quarticContactResidual q 0 (coordinates z) ∂D4BMModularCore.measure) := by
    simp_rw [residual_H,mul_add,mul_left_comm (scalar (physicalAngularParameter q) _)]
    rw [integral_add
      ((quarticContactResidual_scalar_integrable q 1 (physicalAngularParameter q)).const_mul 2)
      ((quarticContactResidual_scalar_integrable q 0 (physicalAngularParameter q)).const_mul a)]
    simp only [integral_const_mul]
  unfold quarticNativePhysicalPeriod
  rw [hI]
  simp only [hc,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  dsimp only [a]
  ring

/-- Exact physical JRQ period at the unchanged Hawking parameter.
Both spin-two Laplacians, the bilinear gradient and native cusp contacts are retained. -/
theorem quarticNativePhysicalPeriod_spinTwo (q : XiZeroCopy) :
    let lam := (center q)^(2 : ℕ)-1/4
    let c := 7*lam-2
    let a := c*(c-4)/96
    let mu := physicalAngularParameter q^(2 : ℕ)-1/4
    quarticNativePhysicalPeriod q 3=(2*mu+2*c-8)*quarticNativePhysicalPeriod q 1-
      4*quarticNativePhysicalPeriod q 2-a*(13*lam-6-mu)*quarticNativePhysicalPeriod q 0 := by
  dsimp only
  rw [quarticNativePhysicalPeriod_balance,quarticNativePhysicalPeriod_H_green,
    quarticNativePhysicalPeriod_H]
  ring

end
end RHTower.D4BMQuarticNativeBalance

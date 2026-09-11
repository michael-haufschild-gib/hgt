import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullIncomingCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFixedClockSourceTranslation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareSourceDifferential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceOnsetReduction

/-!
# Incoming physical-clock balance and literal source work

All four original horizon components retain their squared onset, mixed onset
and derivative-energy profiles. Their translation moment is determined by the
mass coefficient. In the original time measure a finite late slab retains an
explicit contribution of the same coefficient. Its radial coefficient separates
into two actual angular divergences and work against the literal half-square
Laplacian. The original pulse retains its radial vanishing factor. These are
incoming-face and source laws, not cancellation of the completed left-QNM action.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMIncomingClockTranslation
open D4BMFullIncomingCurrent D4BMPhysicalLiftCurrent D4BMHorizon
open D4BMSourceClockTranslation
noncomputable section
set_option autoImplicit false


private theorem profile_shift_integral (f : ℝ → ℂ) (A : ℂ) (hc : Continuous f)
    (hz : ∀ u < 0, f u=0) (ho : ∀ u, 1<u → f u=A) (h : NNReal) :
    (∫ u in -(h:ℝ)..1, f (u+h)-f u) = (h:ℂ)*A := by
  have hl : (∫ u in -(h:ℝ)..0, f u)=0 := by
    calc
      _ = ∫ _u in -(h:ℝ)..0, (0:ℂ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le
          (show -(h:ℝ) ≤ 0 from neg_nonpos.mpr h.2)
        intro u hu
        exact hz u hu.2
      _ = 0 := by simp
  have hr : (∫ u in (1:ℝ)..1+h, f u) = (h:ℂ)*A := by
    calc
      _ = ∫ _u in (1:ℝ)..1+h, A := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [h.2])
        intro u hu
        exact ho u hu.1
      _ = _ := by simp [Complex.real_smul]
  have hi : IntervalIntegrable (fun u : ℝ => f (u+(h:ℝ))) volume (-(h:ℝ)) 1 :=
    (show Continuous (fun u : ℝ => f (u+(h:ℝ))) from
      hc.comp (continuous_id.add_const (h:ℝ))).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi (hc.intervalIntegrable _ _),
    intervalIntegral.integral_comp_add_right]
  simp only [neg_add_cancel]
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) 0 1) (hc.intervalIntegrable (μ:=volume) 1 (1+h))
  have hb := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) (-(h:ℝ)) 0) (hc.intervalIntegrable (μ:=volume) 0 1)
  rw [hr] at ha
  rw [hl,zero_add] at hb
  linear_combination -ha+hb

/-- All three original temporal profiles, before their common physical exponential. -/
def horizonProfile (A B C : ℂ) (u : ℝ) : ℂ :=
  A*(Real.smoothTransition u:ℂ)^2+
    B*(Real.smoothTransition u:ℂ)*((deriv Real.smoothTransition u:ℝ):ℂ)+
    C*((deriv Real.smoothTransition u:ℝ):ℂ)^2

private theorem horizonProfile_continuous (A B C : ℂ) : Continuous (horizonProfile A B C) := by
  have hd := continuous_deriv_smoothTransition
  unfold horizonProfile
  fun_prop

private theorem horizonProfile_zero (A B C : ℂ) (u : ℝ) (hu : u<0) :
    horizonProfile A B C u=0 := by
  have hd := deriv_smoothTransition_eq_zero_of_notMem
    (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.1)
  simp [horizonProfile,Real.smoothTransition.zero_of_nonpos hu.le,hd]

private theorem horizonProfile_one (A B C : ℂ) (u : ℝ) (hu : 1<u) :
    horizonProfile A B C u=A := by
  have hd := deriv_smoothTransition_eq_zero_of_notMem
    (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.2)
  simp [horizonProfile,Real.smoothTransition.one_of_one_le hu.le,hd]

private theorem weighted_difference (v : ℂ) (h u : ℝ) (f : ℝ → ℂ) :
    Complex.exp (-v*(u:ℂ))*clockDifference v h (fun x => f x*Complex.exp (v*(x:ℂ))) u =
      Complex.exp (v*(h:ℂ))*(f (u+h)-f u) := by
  have he : Complex.exp (-v*(u:ℂ))*Complex.exp (v*((u+h:ℝ):ℂ)) =
      Complex.exp (v*(h:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hz : Complex.exp (-v*(u:ℂ))*Complex.exp (v*(u:ℂ))=1 := by
    rw [← Complex.exp_add]
    simp
  dsimp only [clockDifference]
  linear_combination f (u+h)*he-Complex.exp (v*(h:ℂ))*f u*hz

/-- The retained mixed and derivative-energy channels cannot alter the translation mass. -/
theorem horizonProfile_clockMoment (A B C : ℂ) (h : NNReal) :
    clockMoment (-6) h (fun u => horizonProfile A B C u*Complex.exp (-6*(u:ℂ))) =
      (h:ℂ)*Complex.exp (-6*(h:ℂ))*A := by
  unfold clockMoment
  simp only [weighted_difference]
  rw [intervalIntegral.integral_const_mul,profile_shift_integral _ A
    (horizonProfile_continuous A B C) (horizonProfile_zero A B C) (horizonProfile_one A B C)]
  ring

private theorem incoming_factor (q : XiZeroCopy) (a b : ℂ) (z : Point) (j : Fin 4) :
    (fun u => incomingHorizonCurrent q a b u z j) =
      fun u => horizonProfile (clockCoefficients q a b z j 0)
        (clockCoefficients q a b z j 1) (clockCoefficients q a b z j 2) u*
          Complex.exp (-6*(u:ℂ)) := by
  funext u
  dsimp only [incomingHorizonCurrent,horizonProfile,onsetSquare,onsetMixed,onsetDerivativeSquare]
  ring

/-- Every original horizon-current component has the exact common-clock translation mass. -/
theorem incomingHorizonCurrent_clockMoment (q : XiZeroCopy) (a b : ℂ)
    (z : Point) (j : Fin 4) (h : NNReal) :
    clockMoment (-6) h (fun u => incomingHorizonCurrent q a b u z j) =
      (h:ℂ)*Complex.exp (-6*(h:ℂ))*clockCoefficients q a b z j 0 := by
  rw [incoming_factor,horizonProfile_clockMoment]

/-- The same law for the evaluated full incoming Einstein-action current. -/
theorem incomingCurrent_horizon_clockMoment (q : XiZeroCopy) (a b : ℂ)
    (z : Point) (j : Fin 4) (h : NNReal) :
    clockMoment (-6) h (fun u => incomingCurrent q a b 1 u z j) =
      (h:ℂ)*Complex.exp (-6*(h:ℂ))*clockCoefficients q a b z j 0 := by
  simp only [incoming_current_horizon_value]
  exact incomingHorizonCurrent_clockMoment q a b z j h

private theorem incoming_continuous (q : XiZeroCopy) (a b : ℂ) (z : Point) (j : Fin 4) :
    Continuous (fun u => incomingHorizonCurrent q a b u z j) := by
  rw [incoming_factor]
  exact (horizonProfile_continuous _ _ _).mul (by fun_prop)

private theorem translated_integral (f : ℝ → ℂ) (hc : Continuous f) (h T : ℝ) :
    (∫ u in (0:ℝ)..T, f (u+h)-f u) =
      (∫ u in T..T+h, f u)-(∫ u in (0:ℝ)..h, f u) := by
  have hi : IntervalIntegrable (fun u => f (u+h)) volume 0 T :=
    (show Continuous (fun u => f (u+h)) from hc.comp (continuous_id.add_const h)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi (hc.intervalIntegrable _ _),
    intervalIntegral.integral_comp_add_right]
  simp only [zero_add]
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) 0 h) (hc.intervalIntegrable (μ:=volume) h (T+h))
  have hb := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) 0 T) (hc.intervalIntegrable (μ:=volume) T (T+h))
  linear_combination ha-hb

/-- In the original time measure, finite translation retains both temporal caps. -/
theorem incomingHorizonCurrent_finite_translation (q : XiZeroCopy) (a b : ℂ)
    (z : Point) (j : Fin 4) (h T : ℝ) :
    (∫ u in (0:ℝ)..T, incomingHorizonCurrent q a b (u+h) z j-
      incomingHorizonCurrent q a b u z j) =
      (∫ u in T..T+h, incomingHorizonCurrent q a b u z j)-
        (∫ u in (0:ℝ)..h, incomingHorizonCurrent q a b u z j) :=
  translated_integral _ (incoming_continuous q a b z j) h T

/-- The original-measure late time slab retains the full incoming mass coefficient. -/
theorem incomingHorizonCurrent_late_slab (q : XiZeroCopy) (a b : ℂ)
    (z : Point) (j : Fin 4) (T h : NNReal) :
    (∫ u in (1+(T:ℝ))..(1+T+h), incomingHorizonCurrent q a b u z j) =
      clockCoefficients q a b z j 0*Complex.exp (-6*((1+(T:ℝ):ℝ):ℂ))*
        (1-Complex.exp (-6*(h:ℂ)))/6 := by
  have heq : (∫ u in (1+(T:ℝ))..(1+T+h), incomingHorizonCurrent q a b u z j) =
      ∫ u in (1+(T:ℝ))..(1+T+h), clockCoefficients q a b z j 0*Complex.exp (-6*(u:ℂ)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [h.2])
    intro u hu
    have hu1 : 1<u := by linarith [T.2,hu.1]
    have hf := congrFun (incoming_factor q a b z j) u
    rw [horizonProfile_one _ _ _ u hu1] at hf
    exact hf
  rw [heq,intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (show (-6:ℂ) ≠ 0 by norm_num)]
  have he : Complex.exp (-6*((1+(T:ℝ)+(h:ℝ):ℝ):ℂ)) =
      Complex.exp (-6*((1+(T:ℝ):ℝ):ℂ))*Complex.exp (-6*(h:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

end
end RHTower.D4BMIncomingClockTranslation

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMIncomingClockTranslation
open D4BMHorizon D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- Densitized angular boundary current of the two actual forced responses. -/
def angularResponseGreen (q : XiZeroCopy) (j : Fin 2) (w : Point) : ℂ :=
  parameter q false*coordDeriv j (fullAngularField q true) w*
    (fullAngularField q false w+fullSquarePotential q w)-
  parameter q true*coordDeriv j (fullAngularField q false) w*
    (fullAngularField q true w+fullSquarePotential q w)

/-- The full forced angular exchange is an actual divergence, with its original
source half-square retained in the current. -/
theorem angularResponseGreen_divergence (q : XiZeroCopy) (z : UpperHalfPlane) :
    (∑ j : Fin 2, coordDeriv j (angularResponseGreen q j) (coordinates z)) =
      ∑ k : Fin 2,
        (fullAngularCovector q true k (coordinates z)*
          (roughLaplacian (fullAngularCovector q false) k (coordinates z)+
            fullAngularCovector q false k (coordinates z))-
        fullAngularCovector q false k (coordinates z)*
          (roughLaplacian (fullAngularCovector q true) k (coordinates z)+
            fullAngularCovector q true k (coordinates z))) := by
  let w := coordinates z
  let H := fullAngularField q true
  let K := fullAngularField q false
  let Q := fullSquarePotential q
  let A := parameter q true
  let B := parameter q false
  have hH : ContDiffAt ℝ 2 H w := by
    simpa [H,w] using (contDiffAt_infty.mp (fullAngularField_smooth q true _ z.im_pos)) 2
  have hK : ContDiffAt ℝ 2 K w := by
    simpa [K,w] using (contDiffAt_infty.mp (fullAngularField_smooth q false _ z.im_pos)) 2
  have hQ : ContDiffAt ℝ 2 Q w := fullSquarePotential_smooth q _ z.im_pos 2
  have dH := (hH.differentiableAt (by norm_num)).hasFDerivAt
  have dK := (hK.differentiableAt (by norm_num)).hasFDerivAt
  have dQ := (hQ.differentiableAt (by norm_num)).hasFDerivAt
  have hd (j : Fin 2) : coordDeriv j (angularResponseGreen q j) w =
      B*(coordDeriv j (coordDeriv j H) w*(K w+Q w)+
        coordDeriv j H w*(coordDeriv j K w+coordDeriv j Q w))-
      A*(coordDeriv j (coordDeriv j K) w*(H w+Q w)+
        coordDeriv j K w*(coordDeriv j H w+coordDeriv j Q w)) := by
    have dh := (ScalarTwoJet.coordDeriv_hasFDerivAt hH j).differentiableAt.hasFDerivAt
    have dk := (ScalarTwoJet.coordDeriv_hasFDerivAt hK j).differentiableAt.hasFDerivAt
    have hh := ((dh.const_mul B).mul (dK.add dQ)).sub
      ((dk.const_mul A).mul (dH.add dQ))
    change HasFDerivAt (angularResponseGreen q j) _ w at hh
    simp only [coordDeriv,hh.fderiv]
    simp only [sub_apply,add_apply,smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  have hs : (w 1:ℂ)^2*(coordDeriv 0 (coordDeriv 0 H) w+
      coordDeriv 1 (coordDeriv 1 H) w)=A*(H w+Q w) := by
    have h := fullAngularField_equation q true w z.im_pos
    rw [scalarLaplacian_eq _ w z.im_pos] at h
    dsimp only [H,Q,A,fullSquarePotential]
    linear_combination h
  have ht : (w 1:ℂ)^2*(coordDeriv 0 (coordDeriv 0 K) w+
      coordDeriv 1 (coordDeriv 1 K) w)=B*(K w+Q w) := by
    have h := fullAngularField_equation q false w z.im_pos
    rw [scalarLaplacian_eq _ w z.im_pos] at h
    dsimp only [K,Q,B,fullSquarePotential]
    linear_combination h
  change (∑ j : Fin 2, coordDeriv j (angularResponseGreen q j) w) = _
  simp only [hd,fullAngularCovector_rough_equation q false (coordinates z) z.im_pos,
    fullAngularCovector_rough_equation q true (coordinates z) z.im_pos,
    ← fullSquarePotential_coexact q (coordinates z) z.im_pos]
  change (∑ j : Fin 2,
      (B*(coordDeriv j (coordDeriv j H) w*(K w+Q w)+
        coordDeriv j H w*(coordDeriv j K w+coordDeriv j Q w))-
      A*(coordDeriv j (coordDeriv j K) w*(H w+Q w)+
        coordDeriv j K w*(coordDeriv j H w+coordDeriv j Q w)))) =
      ∑ k : Fin 2, (coexact H k w*(B*coexact K k w+B*coexact Q k w)-
        coexact K k w*(A*coexact H k w+A*coexact Q k w))
  simp only [Fin.sum_univ_two,coexact,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hy : (w 1:ℂ)^2 ≠ 0 := pow_ne_zero 2
    (Complex.ofReal_ne_zero.mpr (ne_of_gt z.im_pos))
  apply mul_left_cancel₀ hy
  linear_combination B*(K w+Q w)*hs-A*(H w+Q w)*ht

end
end RHTower.D4BMIncomingClockTranslation

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMIncomingClockTranslation
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- Boundary current transferring the original half-square's full Laplacian. -/
def angularSourceWorkCurrent (q : XiZeroCopy) (a b c : ℂ) (j : Fin 2) (w : Point) : ℂ :=
  (a*fullAngularField q true w+b*fullAngularField q false w+c*fullSquarePotential q w)*
    coordDeriv j (fullSquarePotential q) w

/-- The source-response remainder is a boundary divergence minus work against the
literal half-square Laplacian, retaining its complete gradient-energy forcing. -/
theorem angularSourceWorkCurrent_divergence (q : XiZeroCopy) (a b c : ℂ)
    (z : UpperHalfPlane) :
    let w := coordinates z
    (w 1:ℂ)^2*(∑ j : Fin 2, coordDeriv j (angularSourceWorkCurrent q a b c j) w) =
      (w 1:ℂ)^2*(∑ j : Fin 2,
        (a*fullAngularCovector q true j w+b*fullAngularCovector q false j w+
          c*fullSquareCovector q j w)*fullSquareCovector q j w)+
      (a*fullAngularField q true w+b*fullAngularField q false w+c*fullSquarePotential q w)*
        (2*(physicalRate q true+1)*(physicalRate q true+2)*fullSquarePotential q w+
          fullGradientEnergy q w) := by
  dsimp only
  let w := coordinates z
  let H := fullAngularField q true
  let K := fullAngularField q false
  let Q := fullSquarePotential q
  have hH : ContDiffAt ℝ 2 H w := by
    simpa [H,w] using (contDiffAt_infty.mp (fullAngularField_smooth q true _ z.im_pos)) 2
  have hK : ContDiffAt ℝ 2 K w := by
    simpa [K,w] using (contDiffAt_infty.mp (fullAngularField_smooth q false _ z.im_pos)) 2
  have hQ : ContDiffAt ℝ 2 Q w := fullSquarePotential_smooth q _ z.im_pos 2
  have dH := (hH.differentiableAt (by norm_num)).hasFDerivAt
  have dK := (hK.differentiableAt (by norm_num)).hasFDerivAt
  have dQ := (hQ.differentiableAt (by norm_num)).hasFDerivAt
  have hd (j : Fin 2) : coordDeriv j (angularSourceWorkCurrent q a b c j) w =
      (a*coordDeriv j H w+b*coordDeriv j K w+c*coordDeriv j Q w)*coordDeriv j Q w+
      (a*H w+b*K w+c*Q w)*coordDeriv j (coordDeriv j Q) w := by
    have dq := (ScalarTwoJet.coordDeriv_hasFDerivAt hQ j).differentiableAt.hasFDerivAt
    have hh := (((dH.const_mul a).add (dK.const_mul b)).add (dQ.const_mul c)).mul dq
    change HasFDerivAt (angularSourceWorkCurrent q a b c j) _ w at hh
    simp only [coordDeriv,hh.fderiv]
    simp only [add_apply,smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  have he := fullSquarePotential_laplacian q true w z.im_pos
  rw [scalarLaplacian_eq _ w z.im_pos] at he
  change (w 1:ℂ)^2*(∑ j : Fin 2, coordDeriv j (angularSourceWorkCurrent q a b c j) w) = _
  simp only [hd,← fullSquarePotential_coexact q (coordinates z) z.im_pos]
  change (w 1:ℂ)^2*(∑ j : Fin 2,
      ((a*coordDeriv j H w+b*coordDeriv j K w+c*coordDeriv j Q w)*coordDeriv j Q w+
        (a*H w+b*K w+c*Q w)*coordDeriv j (coordDeriv j Q) w)) =
    (w 1:ℂ)^2*(∑ j : Fin 2,
      (a*coexact H j w+b*coexact K j w+c*coexact Q j w)*coexact Q j w)+
    (a*H w+b*K w+c*Q w)*
      (2*(physicalRate q true+1)*(physicalRate q true+2)*Q w+fullGradientEnergy q w)
  simp only [Fin.sum_univ_two,coexact,Matrix.cons_val_zero,Matrix.cons_val_one]
  linear_combination (a*H w+b*K w+c*Q w)*he

end
end RHTower.D4BMIncomingClockTranslation

open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMIncomingClockTranslation
open D4BMFullIncomingCurrent D4BMPhysicalLiftCurrent D4BMHorizon D4BMModularCore
open D4BMGlobalAngularResponse D4BMQuadraticMixedSource
noncomputable section
set_option autoImplicit false

/-- The actual incoming radial mass separates into angular operator exchange and
three explicit source-response terms. None of the source terms is discarded. -/
theorem incoming_radial_mass_angular_exchange (q : XiZeroCopy) (a b : ℂ)
    (z : UpperHalfPlane) :
    let w := coordinates z
    let s := physicalRate q true
    let t := physicalRate q false
    let ds := s*(s-1)/4
    let dt := t*(t-1)/4
    let U := fun k => fullAngularCovector q true k w
    let V := fun k => fullAngularCovector q false k w
    let Q := fun k => fullSquareCovector q k w
    let E := ∑ k : Fin 2,
      (U k*(roughLaplacian (fullAngularCovector q false) k w+V k)-
        V k*(roughLaplacian (fullAngularCovector q true) k w+U k))
    clockCoefficients q a b w 1 0 =
      4*(a^2*b^2/64)*(-(s*t/3)*E+
        (-2*s*dt*((t+1)^2-s*t)+(s*t/3)*(2*t+1)*(2*t+2))*(∑ k, U k*Q k)+
        (2*t*ds*((s+1)^2-s*t)-(s*t/3)*(2*s+1)*(2*s+2))*(∑ k, V k*Q k)+
        2*ds*dt*(s-t)*(1-s*t)*(∑ k, Q k*Q k)) := by
  dsimp only
  simp_rw [fullAngularCovector_rough_equation q false (coordinates z) z.im_pos,
    fullAngularCovector_rough_equation q true (coordinates z) z.im_pos,
    parameter_physicalRate]
  dsimp only [resolventParameter]
  let s := physicalRate q true
  let t := physicalRate q false
  let U := fun k => fullAngularCovector q true k (coordinates z)
  let V := fun k => fullAngularCovector q false k (coordinates z)
  let Q := fun k => fullSquareCovector q k (coordinates z)
  change 4*(a^2*b^2/64)*
    (t*(2*s+1)*(∑ k : Fin 2,
      (1*V k+(-t*(t-1)/4)*Q k)*(-s*U k+s*(s-1)*(s+2)/4*Q k))-
     s*(2*t+1)*(∑ k : Fin 2,
      (1*U k+(-s*(s-1)/4)*Q k)*(-t*V k+t*(t-1)*(t+2)/4*Q k))) = _
  have ht : physicalRate q false = -physicalRate q true-3 := by
    simp only [physicalRate, Bool.false_eq_true, if_false, if_true]
    ring
  dsimp only [s,t,U,V,Q]
  rw [ht]
  simp only [Fin.sum_univ_two]
  ring

end
end RHTower.D4BMIncomingClockTranslation

open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMIncomingClockTranslation
open D4BMFullIncomingCurrent D4BMModularCore D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- Exact incoming radial balance: both angular boundary currents and the work
against the literal half-square Laplacian are retained. -/
theorem incoming_radial_mass_source_balance (q : XiZeroCopy) (a b : ℂ)
    (z : UpperHalfPlane) :
    let w := coordinates z
    let s := physicalRate q true
    let t := physicalRate q false
    let ds := s*(s-1)/4
    let dt := t*(t-1)/4
    let rs := -2*s*dt*((t+1)^2-s*t)+(s*t/3)*(2*t+1)*(2*t+2)
    let rt := 2*t*ds*((s+1)^2-s*t)-(s*t/3)*(2*s+1)*(2*s+2)
    let rQ := 2*ds*dt*(s-t)*(1-s*t)
    (w 1:ℂ)^2*clockCoefficients q a b w 1 0 =
      4*(a^2*b^2/64)*(
        -(s*t/3)*(w 1:ℂ)^2*(∑ j : Fin 2, coordDeriv j (angularResponseGreen q j) w)+
        (w 1:ℂ)^2*(∑ j : Fin 2,
          coordDeriv j (angularSourceWorkCurrent q rs rt rQ j) w)-
        (rs*fullAngularField q true w+rt*fullAngularField q false w+rQ*fullSquarePotential q w)*
          (2*(s+1)*(s+2)*fullSquarePotential q w+fullGradientEnergy q w)) := by
  dsimp only
  let s := physicalRate q true
  let t := physicalRate q false
  let ds := s*(s-1)/4
  let dt := t*(t-1)/4
  let rs := -2*s*dt*((t+1)^2-s*t)+(s*t/3)*(2*t+1)*(2*t+2)
  let rt := 2*t*ds*((s+1)^2-s*t)-(s*t/3)*(2*s+1)*(2*s+2)
  let rQ := 2*ds*dt*(s-t)*(1-s*t)
  have he := incoming_radial_mass_angular_exchange q a b z
  have hw := angularSourceWorkCurrent_divergence q rs rt rQ z
  rw [angularResponseGreen_divergence]
  dsimp only [s,t,ds,dt,rs,rt,rQ] at hw
  dsimp only at he
  simp only [Fin.sum_univ_two] at he hw ⊢
  linear_combination (coordinates z 1:ℂ)^2*he-4*(a^2*b^2/64)*hw

end
end RHTower.D4BMIncomingClockTranslation

open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMIncomingClockTranslation
open D4BMJointSource D4BMModularCore D4BMGlobalAngularResponse D4BMHorizon
open D4BMQuadraticMixedSource
noncomputable section
set_option autoImplicit false

/-- The literal scalar pulse retains the geometric factor that cancels against
the original scalar-to-master normalization at the horizon. -/
theorem fullSourceOnsetPulse_radial_factor (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ x : ℝ) (z : Point) :
    let s := physicalRate q branch
    let u : ℂ := radialUnit x
    fullSourceOnsetPulse q branch a τ x z =
      2*parameter q branch*sourceAmplitude s 0 a 1 x*(1-u)*
        (-((2*s+1)*u+1)*fullAngularField q branch z+
          s*(s-1)/4*u^2*((2*s+3)*u+3)*fullSquarePotential q z)*
        ((deriv Real.smoothTransition (τ+x):ℝ):ℂ)*
        Complex.exp (2*s*((τ+x:ℝ):ℂ)) := by
  dsimp only
  rw [fullSourceOnsetPulse_transition]
  simp only [parameter_physicalRate]
  dsimp only [sourceSeedFieldFirst,sourceSeedPolynomial,sourceSeedFirst,
    radialLiftFirst,liftFirstPolynomial,amplitudeRate,resolventParameter]
  ring

end
end RHTower.D4BMIncomingClockTranslation
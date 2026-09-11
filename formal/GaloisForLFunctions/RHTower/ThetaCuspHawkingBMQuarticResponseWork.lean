import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingClockTranslation

/-!
# Actual radial response work at the original physical clock

The constructed angular responses satisfy `ΔA = α(A + Q)` and `ΔB = β(B + Q)`.
Transferring the source derivatives to these responses isolates the original incoming
SV-SV radial clock-mass coefficient as two angular divergences minus explicit response
work. The local `Q²` multiplier factors through a cubic that has no zero in the relevant
half-plane. Its nonvanishing leaves response and boundary compensation to be proved.

The finite-clock translation moment and the unshifted horizon integral retain the
common rate `-6`, the onset endpoint, and the derivative-clock energy. No integrated
angular boundary cancellation, independent-channel cancellation, or complete left-QNM
extinction is asserted here.
-/

open Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMQuarticResponseWork
open D4BMFullIncomingCurrent D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open D4BMIncomingClockTranslation D4BMPhysicalLiftCurrent D4BMSourceClockTranslation
noncomputable section
set_option autoImplicit false

/-- Original three coefficients in the incoming radial source-work balance. -/
def sourceWorkWeights (q : XiZeroCopy) : Fin 3 → ℂ :=
  let s := physicalRate q true
  let t := physicalRate q false
  let ds := s*(s-1)/4
  let dt := t*(t-1)/4
  ![-2*s*dt*((t+1)^2-s*t)+(s*t/3)*(2*t+1)*(2*t+2),
    2*t*ds*((s+1)^2-s*t)-(s*t/3)*(2*s+1)*(2*s+2),
    2*ds*dt*(s-t)*(1-s*t)]

private def gradientCurrent (q : XiZeroCopy) (a b c : ℂ) (j : Fin 2) (w : Point) : ℂ :=
  fullSquarePotential q w*(a*coordDeriv j (fullAngularField q true) w+
    b*coordDeriv j (fullAngularField q false) w+c*coordDeriv j (fullSquarePotential q) w)

private theorem gradientCurrent_divergence (q : XiZeroCopy) (a b c : ℂ) (z : UpperHalfPlane) :
    let w := coordinates z
    (w 1:ℂ)^2*(∑ j : Fin 2,coordDeriv j (gradientCurrent q a b c j) w)=
      (w 1:ℂ)^2*(∑ j : Fin 2,(a*fullAngularCovector q true j w+
        b*fullAngularCovector q false j w+c*fullSquareCovector q j w)*fullSquareCovector q j w)+
      fullSquarePotential q w*(a*parameter q true*(fullAngularField q true w+fullSquarePotential q w)+
        b*parameter q false*(fullAngularField q false w+fullSquarePotential q w)+
        c*(2*(physicalRate q true+1)*(physicalRate q true+2)*fullSquarePotential q w+
          fullGradientEnergy q w)) := by
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
  have dQ := (hQ.differentiableAt (by norm_num)).hasFDerivAt
  have hd (j : Fin 2) : coordDeriv j (gradientCurrent q a b c j) w=
      coordDeriv j Q w*(a*coordDeriv j H w+b*coordDeriv j K w+c*coordDeriv j Q w)+
      Q w*(a*coordDeriv j (coordDeriv j H) w+b*coordDeriv j (coordDeriv j K) w+
        c*coordDeriv j (coordDeriv j Q) w) := by
    have dh := (ScalarTwoJet.coordDeriv_hasFDerivAt hH j).differentiableAt.hasFDerivAt
    have dk := (ScalarTwoJet.coordDeriv_hasFDerivAt hK j).differentiableAt.hasFDerivAt
    have dq := (ScalarTwoJet.coordDeriv_hasFDerivAt hQ j).differentiableAt.hasFDerivAt
    have hh := dQ.mul (((dh.const_mul a).add (dk.const_mul b)).add (dq.const_mul c))
    change HasFDerivAt (gradientCurrent q a b c j) _ w at hh
    simp only [coordDeriv,hh.fderiv,add_apply,smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  have hA : (w 1:ℂ)^2*(coordDeriv 0 (coordDeriv 0 H) w+coordDeriv 1 (coordDeriv 1 H) w)=
      parameter q true*(H w+Q w) := by
    have he := fullAngularField_equation q true w z.im_pos
    rw [scalarLaplacian_eq _ w z.im_pos] at he
    dsimp only [H,Q,fullSquarePotential]
    linear_combination he
  have hB : (w 1:ℂ)^2*(coordDeriv 0 (coordDeriv 0 K) w+coordDeriv 1 (coordDeriv 1 K) w)=
      parameter q false*(K w+Q w) := by
    have he := fullAngularField_equation q false w z.im_pos
    rw [scalarLaplacian_eq _ w z.im_pos] at he
    dsimp only [K,Q,fullSquarePotential]
    linear_combination he
  have hS := fullSquarePotential_laplacian q true w z.im_pos
  rw [scalarLaplacian_eq _ w z.im_pos] at hS
  change (w 1:ℂ)^2*(∑ j : Fin 2,coordDeriv j (gradientCurrent q a b c j) w)=_
  simp only [hd,← fullSquarePotential_coexact q (coordinates z) z.im_pos]
  change (w 1:ℂ)^2*(∑ j : Fin 2,
      (coordDeriv j Q w*(a*coordDeriv j H w+b*coordDeriv j K w+c*coordDeriv j Q w)+
      Q w*(a*coordDeriv j (coordDeriv j H) w+b*coordDeriv j (coordDeriv j K) w+
        c*coordDeriv j (coordDeriv j Q) w)))=
    (w 1:ℂ)^2*(∑ j : Fin 2,(a*coexact H j w+b*coexact K j w+c*coexact Q j w)*coexact Q j w)+
      Q w*(a*parameter q true*(H w+Q w)+b*parameter q false*(K w+Q w)+
        c*(2*(physicalRate q true+1)*(physicalRate q true+2)*Q w+fullGradientEnergy q w))
  simp only [Fin.sum_univ_two,coexact,Matrix.cons_val_zero,Matrix.cons_val_one]
  change _=2*(physicalRate q true+1)*(physicalRate q true+2)*Q w+fullGradientEnergy q w at hS
  linear_combination (a*Q w)*hA+(b*Q w)*hB+(c*Q w)*hS

private theorem square_gradient (q : XiZeroCopy) (w : Point) :
    (w 1:ℂ)^2*(∑ j : Fin 2,fullSquareCovector q j w*fullSquareCovector q j w)=
      2*fullSquarePotential q w*fullGradientEnergy q w := by
  simp only [Fin.sum_univ_two,fullSquareCovector,coexact,Matrix.cons_val_zero,Matrix.cons_val_one,
    fullSquarePotential,fullGradientEnergy]
  ring

/-- Original response-source current after the scalar square identity removes gradient work. -/
def reducedSourceCurrent (q : XiZeroCopy) (j : Fin 2) : Point → ℂ :=
  gradientCurrent q (sourceWorkWeights q 0) (sourceWorkWeights q 1) (2*sourceWorkWeights q 2/3) j

/-- The remaining coefficient of the complete local half-square squared. -/
def squareWorkCoefficient (q : XiZeroCopy) : ℂ :=
  sourceWorkWeights q 0*parameter q true+sourceWorkWeights q 1*parameter q false+
    (4*(physicalRate q true+1)*(physicalRate q true+2)/3)*sourceWorkWeights q 2

/-- Actual response-source work; both constructed full responses are retained. -/
def reducedSourceWork (q : XiZeroCopy) (w : Point) : ℂ :=
  sourceWorkWeights q 0*parameter q true*fullSquarePotential q w*fullAngularField q true w+
  sourceWorkWeights q 1*parameter q false*fullSquarePotential q w*fullAngularField q false w+
  squareWorkCoefficient q*fullSquarePotential q w^2

/-- Exact original radial clock-mass balance with both angular fluxes and full response work. -/
theorem incoming_radial_mass_reduced_source_work (q : XiZeroCopy) (a b : ℂ) (z : UpperHalfPlane) :
    let w := coordinates z
    (w 1:ℂ)^2*clockCoefficients q a b w 1 0=
      4*(a^2*b^2/64)*(-(physicalRate q true*physicalRate q false/3)*(w 1:ℂ)^2*
        (∑ j : Fin 2,coordDeriv j (angularResponseGreen q j) w)+
        (w 1:ℂ)^2*(∑ j : Fin 2,coordDeriv j (reducedSourceCurrent q j) w)-
        reducedSourceWork q w) := by
  dsimp only
  have he := incoming_radial_mass_angular_exchange q a b z
  dsimp only at he
  rw [← angularResponseGreen_divergence] at he
  have hd := gradientCurrent_divergence q (sourceWorkWeights q 0) (sourceWorkWeights q 1)
    (2*sourceWorkWeights q 2/3) z
  have hs := square_gradient q (coordinates z)
  change clockCoefficients q a b (coordinates z) 1 0=4*(a^2*b^2/64)*
    (-(physicalRate q true*physicalRate q false/3)*
      (∑ j : Fin 2,coordDeriv j (angularResponseGreen q j) (coordinates z))+
      sourceWorkWeights q 0*(∑ j : Fin 2,fullAngularCovector q true j (coordinates z)*fullSquareCovector q j (coordinates z))+
      sourceWorkWeights q 1*(∑ j : Fin 2,fullAngularCovector q false j (coordinates z)*fullSquareCovector q j (coordinates z))+
      sourceWorkWeights q 2*(∑ j : Fin 2,fullSquareCovector q j (coordinates z)*fullSquareCovector q j (coordinates z))) at he
  change _=4*(a^2*b^2/64)*(_+_ -reducedSourceWork q (coordinates z))
  dsimp only [reducedSourceCurrent,reducedSourceWork,squareWorkCoefficient]
  dsimp only at hd
  simp only [Fin.sum_univ_two] at he hd hs ⊢
  linear_combination (coordinates z 1:ℂ)^2*he-4*(a^2*b^2/64)*hd+
    4*(a^2*b^2/64)*(sourceWorkWeights q 2/3)*hs

/-- The original finite-clock translation moment retains the full radial source work. -/
theorem incoming_radial_horizon_clockMoment_source_work (q : XiZeroCopy) (a b : ℂ)
    (z : UpperHalfPlane) (h : NNReal) :
    let w := coordinates z
    (w 1:ℂ)^2*clockMoment (-6) h (fun u => incomingCurrent q a b 1 u w 1)=
      (h:ℂ)*Complex.exp (-6*(h:ℂ))*4*(a^2*b^2/64)*
        (-(physicalRate q true*physicalRate q false/3)*(w 1:ℂ)^2*
          (∑ j : Fin 2,coordDeriv j (angularResponseGreen q j) w)+
          (w 1:ℂ)^2*(∑ j : Fin 2,coordDeriv j (reducedSourceCurrent q j) w)-
          reducedSourceWork q w) := by
  dsimp only
  rw [incomingCurrent_horizon_clockMoment]
  linear_combination ((h:ℂ)*Complex.exp (-6*(h:ℂ)))*
    incoming_radial_mass_reduced_source_work q a b z

/-- The unshifted physical horizon integral keeps its onset endpoint and derivative energy. -/
theorem incoming_radial_horizon_finite_source_work (q : XiZeroCopy) (a b : ℂ)
    (V : ℝ) (z : UpperHalfPlane) :
    let w := coordinates z
    (w 1:ℂ)^2*(∫ v in (0:ℝ)..V, incomingCurrent q a b 1 v w 1)=
      clockMass V*4*(a^2*b^2/64)*
        (-(physicalRate q true*physicalRate q false/3)*(w 1:ℂ)^2*
          (∑ j : Fin 2,coordDeriv j (angularResponseGreen q j) w)+
          (w 1:ℂ)^2*(∑ j : Fin 2,coordDeriv j (reducedSourceCurrent q j) w)-
          reducedSourceWork q w)+
        (w 1:ℂ)^2*(clockCoefficients q a b w 1 1*(3*clockMass V+onsetSquare V/2)+
          clockCoefficients q a b w 1 2*clockEnergy V) := by
  dsimp only
  simp only [incoming_current_horizon_value]
  rw [incoming_horizon_finite_integral]
  linear_combination clockMass V*incoming_radial_mass_reduced_source_work q a b z

/-- The remaining local coefficient is fixed by the original complementary rates. -/
theorem squareWorkCoefficient_factor (q : XiZeroCopy) :
    let s := physicalRate q true
    let t := physicalRate q false
    let p := s*t
    squareWorkCoefficient q=p*(s-t)*(p^3+25*p^2-28*p+20)/6 := by
  dsimp only
  norm_num [squareWorkCoefficient,sourceWorkWeights,parameter,physicalRate,
    D4BMQuadraticMixedSource.resolventParameter,D4BMQuadraticMixedSource.branchParameter,Matrix.cons_val_two]
  ring

private theorem stable_cubic_ne_zero (z : ℂ) (hz : 0 ≤ z.re) :
    z^3+31*z^2+84*z+72 ≠ 0 := by
  intro h
  have hR := congrArg Complex.re h
  have hI := congrArg Complex.im h
  norm_num [pow_succ,Complex.mul_re,Complex.mul_im] at hR hI
  have hy : z.im*(3*z.re^2+62*z.re+84-z.im^2)=0 := by
    linear_combination hI
  have hx3 : 0 ≤ z.re^3 := pow_nonneg hz 3
  rcases mul_eq_zero.mp hy with hy|hy
  · rw [hy] at hR
    nlinarith [sq_nonneg z.re]
  · have hn : -8*z.re^3-248*z.re^2-2090*z.re-2532=0 := by
      linear_combination hR-(3*z.re+31)*hy
    nlinarith [sq_nonneg z.re]

/-- The original physical rate product lies in the strict right half-plane beyond two. -/
theorem physical_rate_product_re (q : XiZeroCopy) :
    2 < (physicalRate q true*physicalRate q false).re := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  have hp := mul_pos hq.1 (sub_pos.mpr hq.2)
  norm_num [physicalRate,Complex.mul_re,Complex.sub_re,Complex.sub_im] at *
  nlinarith [sq_nonneg (q.1:ℂ).im]

/-- No Xi occurrence removes the local Q² work coefficient; compensation must retain responses or faces. -/
theorem squareWorkCoefficient_ne_zero (q : XiZeroCopy) : squareWorkCoefficient q ≠ 0 := by
  let p := physicalRate q true*physicalRate q false
  have hp : 2 < p.re := physical_rate_product_re q
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; norm_num at hp
  have hs : physicalRate q true-physicalRate q false ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    have hq := xi_divisor_support_im_ne_zero q.1
    norm_num [physicalRate,Complex.sub_im] at hi
    exact hq hi
  have hP : p^3+25*p^2-28*p+20 ≠ 0 := by
    have hz : 0 ≤ (p-2).re := by norm_num [Complex.sub_re]; linarith
    have he : (p-2)^3+31*(p-2)^2+84*(p-2)+72=p^3+25*p^2-28*p+20 := by ring
    exact he ▸ stable_cubic_ne_zero (p-2) hz
  rw [squareWorkCoefficient_factor]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hp0 hs) hP) (by norm_num)

end
end RHTower.D4BMQuarticResponseWork

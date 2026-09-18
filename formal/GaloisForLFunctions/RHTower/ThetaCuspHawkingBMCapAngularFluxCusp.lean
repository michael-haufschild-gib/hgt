import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSecondStokesBoundaryCancellation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalAngularCutoffCalibration
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareSourceDifferential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCuspMetricSource

/-!
The original scalar source current exposed by the leading cap's angular transposition.
The differential source equation retains its full gradient energy. Its actual vertical
flux equals the literal constant Weyl sectors plus a remainder that decays after every
complex height weight, at each fixed horizontal position. Specialization at the original
diagonal Xi reader has no constant sector. At independent Xi readers the exact surviving
constant sector is classified by two explicit resonances.

This does not identify an integrated physical finite part, admit an infinite angular
cutoff limit, cancel the other corrected action terms, or prove radiative extinction.
-/

set_option autoImplicit false
open Set
open scoped BigOperators ContDiff
namespace RHTower.D4BMCapAngularFluxCusp
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMModularCore D4BMGlobalAngularResponse D4BMJointSource D4BMHorizon
noncomputable section

private def reader (r : XiZeroCopy) : Point → ℂ :=
  D4BMLiteralCusp.scalar (physicalAngularParameter r)

/-- Original source current exposed by compact angular transposition of the leading cap. -/
def angularFlux (q r : XiZeroCopy) (j : Fin 2) (z : Point) : ℂ :=
  (physicalAngularParameter r^2-1/4)*reader r z*coordDeriv j (fullSquarePotential q) z-
    scalarLaplacian (fullSquarePotential q) z*coordDeriv j (reader r) z

/-- Public expansion of the literal cap source flux.  It exposes the exact
reader and square-potential slots needed by the same-branch cyclic cap
current, without suppressing the scalar action in the reader derivative. -/
theorem angularFlux_eq (q r : XiZeroCopy) (j : Fin 2) (z : Point) :
    angularFlux q r j z =
      (physicalAngularParameter r^2 - 1 / 4) *
        D4BMLiteralCusp.scalar (physicalAngularParameter r) z *
          coordDeriv j (fullSquarePotential q) z -
        scalarLaplacian (fullSquarePotential q) z *
          coordDeriv j (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z := by
  rfl

private theorem square_first (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (j : Fin 2) :
    coordDeriv j (fullSquarePotential q) z=
      scalar (center q) z*coordDeriv j (scalar (center q)) z := by
  have hs : ContDiffAt ℝ 2 (scalar (center q)) z :=
    D4BMAngularSeries.cuspLeg_contDiffAt .scalar (center q) 2 z hz
  have hh := congrArg (fun a => a.first j) (ofField_mul
    (contDiffAt_const (c := (1/2:ℂ))) (hs.mul hs))
  rw [ofField_mul hs hs,ofField_constant] at hh
  change coordDeriv j (fullSquarePotential q) z=_ at hh
  simp only [ofField,ScalarTwoJet.mul,constant] at hh
  linear_combination hh

/-- Every source term in the flux is retained, including the full gradient energy. -/
theorem angularFlux_original_source (q r : XiZeroCopy) (branch : Bool)
    (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    angularFlux q r j z.val=
      (physicalAngularParameter r^2-1/4)*reader r z.val*scalar (center q) z.val*
        coordDeriv j (scalar (center q)) z.val-
      (2*(physicalRate q branch+1)*(physicalRate q branch+2)*fullSquarePotential q z.val+
        fullGradientEnergy q z.val)*coordDeriv j (reader r) z.val := by
  rw [angularFlux,square_first q z.val z.property,
    fullSquarePotential_laplacian q branch z.val z.property]
  ring

/-- The vertical flux of the literal constant Weyl sectors, with its original height weights. -/
def constantVerticalFlux (u v : ℂ) (Y : ℝ) : ℂ :=
  let F := d4BMCompletedEisensteinCuspConstantPart .scalar u Y
  let S := d4BMCompletedEisensteinCuspConstantPart .scalar v Y
  let Fy := d4BMCanonicalCuspConstantVerticalFirstJet u Y
  let Sy := d4BMCanonicalCuspConstantVerticalFirstJet v Y
  (v^2-1/4)*S*F*Fy-((u^2-1/4)*F^2+(Y:ℂ)^2*Fy^2)*Sy

/-- Actual coefficient of each ordered source/source/reader Weyl term. -/
def constantCoefficient (u v : ℂ) (e1 e2 e3 : Bool) : ℂ :=
  d4BMCompletedEisensteinCuspConstantCoefficient u e1*
    d4BMCompletedEisensteinCuspConstantCoefficient u e2*
    d4BMCompletedEisensteinCuspConstantCoefficient v e3*
      ((v^2-1/4)*d4BMCompletedEisensteinCuspWeylExponent u e2-
        (u^2-1/4)*d4BMCompletedEisensteinCuspWeylExponent v e3-
        d4BMCompletedEisensteinCuspWeylExponent u e1*
          d4BMCompletedEisensteinCuspWeylExponent u e2*
          d4BMCompletedEisensteinCuspWeylExponent v e3)

def constantFamily (u v : ℂ) : D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ :=
  d4BMDiagonalEisensteinCuspBoundaryFamily (constantCoefficient u v)

/-- The family is exactly the literal constant-sector flux at every positive height. -/
theorem constantVerticalFlux_eq_family (u v : ℂ) (Y : Ioi (0:ℝ)) :
    constantVerticalFlux u v Y.val=
      d4BMEvaluateCuspAffineBoundaryFamily u v Y.val (constantFamily u v) := by
  have hy : (Y.val:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Y.property.ne'
  have hp (a b c : ℂ) :
      (Y.val:ℂ)^(-1+a+b+c)=(Y.val:ℂ)^(-1:ℂ)*(Y.val:ℂ)^a*(Y.val:ℂ)^b*(Y.val:ℂ)^c := by
    rw [show -1+a+b+c=((-1:ℂ)+a)+b+c by ring,
      Complex.cpow_add (((-1:ℂ)+a)+b) c hy,
      Complex.cpow_add ((-1:ℂ)+a) b hy,Complex.cpow_add (-1:ℂ) a hy]
  unfold constantFamily
  rw [d4BM_evaluateDiagonalCuspBoundaryFamily_eq_boolSum]
  simp only [Fintype.sum_bool]
  simp_rw [hp]
  unfold constantVerticalFlux constantCoefficient
    d4BMCanonicalCuspConstantVerticalFirstJet
    d4BMCompletedEisensteinCuspConstantPart d4BMCompletedEisensteinCuspConstantTerm
    d4BMCompletedEisensteinCuspConstantMaassFactor
  simp only [Complex.cpow_neg_one]
  field_simp [hy]
  ring

/-- Every actual diagonal source/source/physical-reader exponent is nonzero after specialization. -/
theorem diagonal_exponent_ne_zero (q : XiZeroCopy) (e1 e2 e3 : Bool) :
    d4BMSpecializeDiagonalCuspAffineExponent (center q) (physicalAngularParameter q)
      (d4BMDiagonalEisensteinCuspBoundaryExponent e1 e2 e3) ≠ 0 := by
  have hq := xi_divisor_support_im_ne_zero q.1
  rw [d4BM_diagonalCuspBoundaryExponent_specialization,physicalAngularParameter_eq]
  intro hh
  have hi := congrArg Complex.im hh
  cases e1 <;> cases e2 <;> cases e3 <;>
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,D4BMGlobalAngularResponse.center,
      Complex.mul_im,Complex.mul_re] at hi
  all_goals apply hq; linarith

/-- Coefficients grouped by their actual specialized height exponents. -/
def specializedFamily (q r : XiZeroCopy) : ℂ →₀ ℂ :=
  Finsupp.mapDomain (d4BMSpecializeDiagonalCuspAffineExponent (center q) (physicalAngularParameter r))
    (constantFamily (center q) (physicalAngularParameter r))

/-- No constant-height coefficient survives for the original diagonal source and reader.
This is specialization first; it does not replace an exponent by its unspecialized affine label. -/
theorem diagonal_specialized_constant_zero (q : XiZeroCopy) : specializedFamily q q 0=0 := by
  classical
  simp only [specializedFamily,constantFamily,d4BMDiagonalEisensteinCuspBoundaryFamily,
    Fintype.sum_bool,Finsupp.mapDomain_add,Finsupp.mapDomain_single,Finsupp.add_apply]
  simp [diagonal_exponent_ne_zero]


private def verticalFirst (u : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCanonicalCuspConstantVerticalFirstJet u Y+
    d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y

/-- The complete literal Fourier expression of the vertical source flux. -/
def fullVerticalFlux (u v : ℂ) (x Y : ℝ) : ℂ :=
  let F := d4BMCompletedEisensteinCuspLeg .scalar u x Y
  let S := d4BMCompletedEisensteinCuspLeg .scalar v x Y
  let Fx := d4BMCompletedEisensteinCuspHorizontalFirstJetTail u x Y
  let Fy := verticalFirst u x Y
  let Sy := verticalFirst v x Y
  (v^2-1/4)*S*F*Fy-((u^2-1/4)*F^2+(Y:ℂ)^2*(Fx^2+Fy^2))*Sy

private theorem scalar_partials (u : ℂ) (x : ℝ) (Y : Ici (1:ℝ)) :
    coordDeriv 0 (scalar u) ![x,Y.val]=d4BMCompletedEisensteinCuspHorizontalFirstJetTail u x Y.val ∧
    coordDeriv 1 (scalar u) ![x,Y.val]=verticalFirst u x Y.val := by
  let z : Point := ![x,Y.val]
  have hz : 0 < z 1 := zero_lt_one.trans_le Y.property
  have hf : DifferentiableAt ℝ (scalar u) z :=
    (D4BMAngularSeries.cuspLeg_contDiffAt .scalar u 1 z hz).differentiableAt (by norm_num)
  have hd (j : Fin 2) : HasDerivAt (fun t => scalar u (Function.update z j t))
      (coordDeriv j (scalar u) z) (z j) := by
    have hf' : HasFDerivAt (scalar u) (fderiv ℝ (scalar u) z)
        (Function.update z j (z j)) := by
      simpa only [Function.update_eq_self] using hf.hasFDerivAt
    have hh := hf'.comp_hasDerivAt (z j) (hasDerivAt_update z j (z j))
    convert hh using 1 <;> rfl
  have hx : HasDerivAt (fun t => d4BMCompletedEisensteinCuspLeg .scalar u t Y.val)
      (coordDeriv 0 (scalar u) z) x := by
    simpa [scalar,z,Function.update] using hd 0
  have hy : HasDerivAt (fun t => d4BMCompletedEisensteinCuspLeg .scalar u x t)
      (coordDeriv 1 (scalar u) z) Y.val := by
    simpa [scalar,z,Function.update] using hd 1
  have hX := hx.unique (hasDerivAt_d4BMCompletedEisensteinCanonicalCuspLeg_horizontal u x Y)
  have hY := hy.unique (hasDerivAt_d4BMCompletedEisensteinCanonicalCuspLeg_vertical u x Y)
  constructor
  · exact hX
  · rw [d4BM_canonicalCuspFullSecondJet_sigma_eq_constant_add_tail] at hY
    exact hY

/-- The canonical Fourier expression is the actual differentiated original source flux. -/
theorem angularFlux_full_cusp (q r : XiZeroCopy) (x : ℝ) (Y : Ici (1:ℝ)) :
    angularFlux q r 1 ![x,Y.val]=
      fullVerticalFlux (center q) (physicalAngularParameter r) x Y.val := by
  have hz : 0 < (![x,Y.val] : Point) 1 := zero_lt_one.trans_le Y.property
  have hq := scalar_partials (center q) x Y
  have hr := scalar_partials (physicalAngularParameter r) x Y
  have hl : (physicalRate q true+1)*(physicalRate q true+2)=center q^2-1/4 := by
    dsimp [physicalRate,D4BMGlobalAngularResponse.center]
    ring
  rw [angularFlux_original_source q r true ⟨![x,Y.val],hz⟩ 1]
  change (physicalAngularParameter r^2-1/4)*scalar (physicalAngularParameter r) ![x,Y.val]*
      scalar (center q) ![x,Y.val]*coordDeriv 1 (scalar (center q)) ![x,Y.val]-
      (2*(physicalRate q true+1)*(physicalRate q true+2)*fullSquarePotential q ![x,Y.val]+
        fullGradientEnergy q ![x,Y.val])*coordDeriv 1 (scalar (physicalAngularParameter r)) ![x,Y.val]=_
  rw [show 2*(physicalRate q true+1)*(physicalRate q true+2)=2*(center q^2-1/4) by rw [mul_assoc,hl]]
  simp only [fullSquarePotential,fullGradientEnergy,hq.1,hq.2,hr.2,Matrix.cons_val_one]
  change (physicalAngularParameter r^2-1/4)*scalar (physicalAngularParameter r) ![x,Y.val]*
      scalar (center q) ![x,Y.val]*verticalFirst (center q) x Y.val-
      (2*(center q^2-1/4)*(1/2*(scalar (center q) ![x,Y.val]*scalar (center q) ![x,Y.val]))+
        (Y.val:ℂ)^2*(d4BMCompletedEisensteinCuspHorizontalFirstJetTail (center q) x Y.val^2+
          verticalFirst (center q) x Y.val^2))*verticalFirst (physicalAngularParameter r) x Y.val=_
  dsimp only [fullVerticalFlux,scalar]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- Every nonconstant source term in the complete vertical flux decays faster than any height power. -/
theorem fullVerticalFlux_remainder_rapid (u v : ℂ) (x : ℝ) :
    D4BMCuspRapidDecay (fun Y => fullVerticalFlux u v x Y-constantVerticalFlux u v Y) := by
  let F := d4BMCompletedEisensteinCuspLeg .scalar u x
  let S := d4BMCompletedEisensteinCuspLeg .scalar v x
  let Fc := d4BMCompletedEisensteinCuspConstantPart .scalar u
  let Sc := d4BMCompletedEisensteinCuspConstantPart .scalar v
  let Fy := verticalFirst u x
  let Sy := verticalFirst v x
  let Fyc := d4BMCanonicalCuspConstantVerticalFirstJet u
  let Syc := d4BMCanonicalCuspConstantVerticalFirstJet v
  let Fx := d4BMCompletedEisensteinCuspHorizontalFirstJetTail u x
  have hF : D4BMCuspRapidDecay (fun Y => F Y-Fc Y) := by
    apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_cuspTailPart .scalar u x)
    intro Y
    simp [F,Fc,d4BMCompletedEisensteinCuspLeg]
  have hS : D4BMCuspRapidDecay (fun Y => S Y-Sc Y) := by
    apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_cuspTailPart .scalar v x)
    intro Y
    simp [S,Sc,d4BMCompletedEisensteinCuspLeg]
  have hFy : D4BMCuspRapidDecay (fun Y => Fy Y-Fyc Y) :=
    d4BMCuspRapidDecay_fullVerticalFirstJet_sub_constant u x
  have hSy : D4BMCuspRapidDecay (fun Y => Sy Y-Syc Y) :=
    d4BMCuspRapidDecay_fullVerticalFirstJet_sub_constant v x
  have mF := d4BMCuspModerateGrowth_cuspLeg .scalar u x
  have mS := d4BMCuspModerateGrowth_cuspLeg .scalar v x
  have mFc := d4BMCuspModerateGrowth_constantPart .scalar u
  have mSc := d4BMCuspModerateGrowth_constantPart .scalar v
  have mFy := d4BMCuspModerateGrowth_fullVerticalFirstJet u x
  have mSy := d4BMCuspModerateGrowth_fullVerticalFirstJet v x
  have mFyc := d4BMCuspModerateGrowth_constantVerticalFirstJet u
  have hA := d4BMCuspRapidDecay_product3_sub_product3 hS hF hFy mS mSc mF mFc mFy
  have hB := d4BMCuspRapidDecay_product3_sub_product3 hF hF hSy mF mFc mF mFc mSy
  have hC := d4BMCuspRapidDecay_product3_sub_product3 hFy hFy hSy mFy mFyc mFy mFyc mSy
  have hD := mSy _ (d4BMCuspRapidDecay_mul (d4BMCuspRapidDecay_horizontalFirstJetTail u x)
    (d4BMCuspRapidDecay_horizontalFirstJetTail u x))
  have h := d4BMCuspRapidDecay_sub
    (d4BMCuspRapidDecay_sub (d4BMCuspRapidDecay_const_mul hA (v^2-1/4))
      (d4BMCuspRapidDecay_const_mul hB (u^2-1/4)))
    (d4BMCuspRapidDecay_add (d4BMCuspRapidDecay_mul_cpow hC 2)
      (d4BMCuspRapidDecay_mul_cpow hD 2))
  apply d4BMCuspRapidDecay_congr h
  intro Y
  simp only [Complex.cpow_two]
  change (v^2-1/4)*(S Y*F Y*Fy Y-Sc Y*Fc Y*Fyc Y)-
      (u^2-1/4)*(F Y*F Y*Sy Y-Fc Y*Fc Y*Syc Y)-
      ((Fy Y*Fy Y*Sy Y-Fyc Y*Fyc Y*Syc Y)*(Y:ℂ)^2+
        (Fx Y*Fx Y*Sy Y)*(Y:ℂ)^2)=_
  dsimp only [fullVerticalFlux,constantVerticalFlux,F,S,Fc,Sc,Fy,Sy,Fyc,Syc,Fx]
  ring

/-- The actual source flux has precisely its constant-sector asymptotics, at unchanged parameters. -/
theorem angularFlux_remainder_rapid (q r : XiZeroCopy) (x : ℝ) :
    D4BMCuspRapidDecay (fun Y => angularFlux q r 1 ![x,Y]-
      constantVerticalFlux (center q) (physicalAngularParameter r) Y) := by
  intro w
  apply (fullVerticalFlux_remainder_rapid (center q) (physicalAngularParameter r) x w).congr'
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with Y hY
  rw [angularFlux_full_cusp q r x ⟨Y,hY⟩]

private theorem reader_plus_zero (r : XiZeroCopy) :
    d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter r) true=0 := by
  have h := physicalScalar_principal r (![0,1] : Point)
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,
    mul_one,Matrix.cons_val_one,Matrix.cons_val_zero,Complex.ofReal_one,Complex.one_cpow] at h
  have hm : d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter r) false=
      reflectedCompletedLambda ((r.1:ℂ)-1) := by
    rw [physicalAngularParameter_eq]
    simp only [d4BMCompletedEisensteinCuspConstantCoefficient,Bool.false_eq_true,ite_false]
    congr 1
    ring
  rw [hm] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

private theorem reader_plus_flux_zero (q r : XiZeroCopy) (e1 e2 : Bool) :
    constantCoefficient (center q) (physicalAngularParameter r) e1 e2 true=0 := by
  simp only [constantCoefficient,reader_plus_zero,mul_zero,zero_mul]

private theorem mixed_exponent_ne_zero (q r : XiZeroCopy) (e : Bool) :
    d4BMSpecializeDiagonalCuspAffineExponent (center q) (physicalAngularParameter r)
      (d4BMDiagonalEisensteinCuspBoundaryExponent e (!e) false) ≠ 0 := by
  have hr := xi_divisor_support_im_ne_zero r.1
  rw [d4BM_diagonalCuspBoundaryExponent_specialization,physicalAngularParameter_eq]
  intro hh
  have hi := congrArg Complex.im hh
  cases e <;> norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,
    D4BMGlobalAngularResponse.center,Complex.mul_im,Complex.mul_re] at hi
  all_goals apply hr; linarith

private theorem minus_exponent_zero_iff (q r : XiZeroCopy) :
    d4BMSpecializeDiagonalCuspAffineExponent (center q) (physicalAngularParameter r)
      (d4BMDiagonalEisensteinCuspBoundaryExponent false false false)=0 ↔
        (r.1:ℂ)=4-4*(q.1:ℂ) := by
  rw [d4BM_diagonalCuspBoundaryExponent_specialization,physicalAngularParameter_eq]
  simp only [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,
    D4BMGlobalAngularResponse.center,Bool.false_eq_true,↓reduceIte,Int.cast_neg,Int.cast_one,neg_one_mul]
  constructor
  · intro h
    linear_combination -2*h
  · intro h
    linear_combination -(1/2:ℂ)*h

private theorem plus_exponent_zero_iff (q r : XiZeroCopy) :
    d4BMSpecializeDiagonalCuspAffineExponent (center q) (physicalAngularParameter r)
      (d4BMDiagonalEisensteinCuspBoundaryExponent true true false)=0 ↔
        (r.1:ℂ)=4*(q.1:ℂ) := by
  rw [d4BM_diagonalCuspBoundaryExponent_specialization,physicalAngularParameter_eq]
  simp only [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,
    D4BMGlobalAngularResponse.center,Bool.false_eq_true,↓reduceIte,Int.cast_neg,Int.cast_one,neg_one_mul,one_mul]
  constructor
  · intro h
    linear_combination -2*h
  · intro h
    linear_combination -(1/2:ℂ)*h

/-- At independent original Xi occurrences, only two explicit spectral resonances can
contribute a constant height flux. The reader's vanishing Weyl branch and both mixed
source branches have been removed by the literal equations, without a nonresonance premise. -/
theorem independent_specialized_constant (q r : XiZeroCopy) :
    specializedFamily q r 0=
      (if (r.1:ℂ)=4-4*(q.1:ℂ) then
        constantCoefficient (center q) (physicalAngularParameter r) false false false else 0)+
      (if (r.1:ℂ)=4*(q.1:ℂ) then
        constantCoefficient (center q) (physicalAngularParameter r) true true false else 0) := by
  classical
  simp only [specializedFamily,constantFamily,d4BMDiagonalEisensteinCuspBoundaryFamily,
    Fintype.sum_bool,Finsupp.mapDomain_add,Finsupp.mapDomain_single,Finsupp.add_apply,
    reader_plus_flux_zero,Finsupp.single_zero,Finsupp.mapDomain_zero,Finsupp.zero_apply]
  have hm0 := mixed_exponent_ne_zero q r false
  have hm1 := mixed_exponent_ne_zero q r true
  simp only [Bool.not_false] at hm0
  simp only [Bool.not_true] at hm1
  simp only [Finsupp.single_apply,hm0,hm1,↓reduceIte,add_zero,zero_add,
    minus_exponent_zero_iff,plus_exponent_zero_iff]
  ring

end
end RHTower.D4BMCapAngularFluxCusp

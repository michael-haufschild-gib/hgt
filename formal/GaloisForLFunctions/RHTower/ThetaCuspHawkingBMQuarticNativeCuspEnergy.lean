import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticNativeCuspComparison
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Source-derived weighted native cusp derivative energy

The original forced modal equation yields an exact finite-height multiplier
identity and a first-derivative square estimate. Literal forcing Parseval and
rapid nonconstant response mass control polynomial cutoff errors uniformly
in height and finite frequency sets. Improper integration and positivity
then admit the complete weighted derivative energy. Independent gradient
Parseval restores the native zero-mode derivative explicitly.

No upper response trace or fixed-clock extinction is assumed or concluded.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.SelbergMaassMean
open GaloisForLFunctions.RHTower.SelbergMaassFourier
open scoped Polynomial
namespace RHTower.D4BMQuarticNativeCuspEnergy
open D4BMModularCore D4BMGlobalAngularResponse D4BMQuarticNativeCuspModes
open D4BMQuarticNativeCuspComparison
noncomputable section
set_option autoImplicit false

/-- The positive vertical and nonzero-frequency energy of an original mode. -/
def modeEnergy (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : ℝ) : ℝ :=
  2*Complex.normSq (deriv (responseMode q b n) y)+
    (signedFrequency 1 n)^2*modeMass q b n y

/-- The complete original forcing loss appearing in the source-derived square estimate. -/
def forcingLoss (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : ℝ) : ℝ :=
  Complex.normSq (forcingMode q b n y)/y^4

/-- The exact second mass derivative, retaining the signed work and changing metric. -/
def signedDensity (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : ℝ) : ℝ :=
  2*Complex.normSq (deriv (responseMode q b n) y)+
    2*((signedFrequency 1 n)^2+(parameter q b).re/y^2)*modeMass q b n y+
      2*modeWork q b n y

/-- Both terms in the finite-height multiplier boundary current are retained. -/
def multiplierBoundary (P : ℝ[X]) (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : ℝ) : ℝ :=
  (P^2).eval y*deriv (modeMass q b n) y-(P^2).derivative.eval y*modeMass q b n y

private theorem response_continuous (q : XiZeroCopy) (b : Bool) (n : ℤ)
    {y : ℝ} (hy : 0 < y) : ContinuousAt (responseMode q b n) y :=
  (coefficient_hasDerivAt 1 (by norm_num) n
    ((D4BMCuspResponse.responsePlanar_smooth q b).of_le
      (WithTop.coe_le_coe.mpr le_top)) hy).continuousAt

private theorem response_deriv_continuous (q : XiZeroCopy) (b : Bool) (n : ℤ)
    {y : ℝ} (hy : 0 < y) : ContinuousAt (deriv (responseMode q b n)) y :=
  (coefficient_second_hasDerivAt 1 (by norm_num) n
    ((D4BMCuspResponse.responsePlanar_smooth q b).of_le
      (WithTop.coe_le_coe.mpr le_top)) hy).continuousAt

private theorem forcing_continuous (q : XiZeroCopy) (b : Bool) (n : ℤ)
    {y : ℝ} (hy : 0 < y) : ContinuousAt (forcingMode q b n) y :=
  (coefficient_hasDerivAt 1 (by norm_num) n
    ((globalForcing_smooth q b).planar_contDiffOn.of_le
      (WithTop.coe_le_coe.mpr le_top)) hy).continuousAt

private theorem modeEnergy_continuous (q : XiZeroCopy) (b : Bool) (n : ℤ) :
    ContinuousOn (modeEnergy q b n) (Ioi (0:ℝ)) := by
  intro y hy
  have hc := response_continuous q b n hy
  have hd := response_deriv_continuous q b n hy
  have ht := ((hd.norm.pow 2).const_mul 2).add
    ((hc.norm.pow 2).const_mul ((signedFrequency 1 n)^2))
  change ContinuousAt (fun t : ℝ => 2*‖deriv (responseMode q b n) t‖^2+
    (signedFrequency 1 n)^2*‖responseMode q b n t‖^2) y at ht
  change ContinuousWithinAt (fun t : ℝ => 2*Complex.normSq (deriv (responseMode q b n) t)+
    (signedFrequency 1 n)^2*Complex.normSq (responseMode q b n t)) (Ioi (0:ℝ)) y
  simpa only [Complex.normSq_eq_norm_sq] using ht.continuousWithinAt (s := Ioi (0:ℝ))

private theorem forcingLoss_continuous (q : XiZeroCopy) (b : Bool) (n : ℤ) :
    ContinuousOn (forcingLoss q b n) (Ioi (0:ℝ)) := by
  intro y hy
  have hf := forcing_continuous q b n hy
  have ht := (hf.norm.pow 2).div (continuousAt_id.pow 4) (pow_ne_zero 4 (ne_of_gt hy))
  change ContinuousAt (fun t : ℝ => ‖forcingMode q b n t‖^2/t^4) y at ht
  change ContinuousWithinAt (fun t : ℝ => Complex.normSq (forcingMode q b n t)/t^4)
    (Ioi (0:ℝ)) y
  simpa only [Complex.normSq_eq_norm_sq] using ht.continuousWithinAt (s := Ioi (0:ℝ))

private theorem signedDensity_continuous (q : XiZeroCopy) (b : Bool) (n : ℤ) :
    ContinuousOn (signedDensity q b n) (Ioi (0:ℝ)) := by
  intro y hy
  have hc := response_continuous q b n hy
  have hd := response_deriv_continuous q b n hy
  have hf := forcing_continuous q b n hy
  have hz : y^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hy)
  have hpot : ContinuousAt (fun t : ℝ => (signedFrequency 1 n)^2+(parameter q b).re/t^2) y :=
    continuousAt_const.add (continuousAt_const.div (continuousAt_id.pow 2) hz)
  have hconj := (Complex.conjCLE : ℂ →L[ℝ] ℂ).continuous.continuousAt.comp hc
  have hwork := (Complex.reCLM.continuous.continuousAt.comp (hf.mul hconj)).div
    (continuousAt_id.pow 2) hz
  have ht := (((hd.norm.pow 2).const_mul 2).add
    ((hpot.const_mul 2).mul (hc.norm.pow 2))).add (hwork.const_mul 2)
  change ContinuousAt (fun t : ℝ =>
    2*‖deriv (responseMode q b n) t‖^2+
      2*((signedFrequency 1 n)^2+(parameter q b).re/t^2)*‖responseMode q b n t‖^2+
        2*((forcingMode q b n t*(starRingEnd ℂ) (responseMode q b n t)).re/t^2)) y at ht
  change ContinuousWithinAt (fun t : ℝ =>
    2*Complex.normSq (deriv (responseMode q b n) t)+
      2*((signedFrequency 1 n)^2+(parameter q b).re/t^2)*Complex.normSq (responseMode q b n t)+
        2*((forcingMode q b n t*(starRingEnd ℂ) (responseMode q b n t)).re/t^2)) (Ioi (0:ℝ)) y
  simpa only [Complex.normSq_eq_norm_sq] using ht.continuousWithinAt (s := Ioi (0:ℝ))

/-- Differentiating the actual multiplier current retains the full signed source density. -/
theorem multiplierBoundary_hasDerivAt (P : ℝ[X]) (q : XiZeroCopy) (b : Bool) (n : ℤ)
    (y : Ioi (0:ℝ)) :
    HasDerivAt (multiplierBoundary P q b n)
      ((P^2).eval y.val*signedDensity q b n y-
        (P^2).derivative.derivative.eval y.val*modeMass q b n y) y := by
  have hu := (modeMass_hasDerivAt q b n y).differentiableAt.hasDerivAt
  have hdu := modeMass_second_hasDerivAt q b n y
  change HasDerivAt (deriv (modeMass q b n)) (signedDensity q b n y) y at hdu
  have h := (((P^2).hasDerivAt y.val).mul hdu).sub
    (((P^2).derivative.hasDerivAt y.val).mul hu)
  convert h using 1 <;> try rfl
  ring

private theorem modeMass_continuous (q : XiZeroCopy) (b : Bool) (n : ℤ) :
    ContinuousOn (modeMass q b n) (Ioi (0:ℝ)) :=
  fun y hy => (modeMass_hasDerivAt q b n ⟨y,hy⟩).continuousAt.continuousWithinAt

/-- Exact finite-height source identity, before imposing any auxiliary multiplier endpoint. -/
theorem nativeMode_multiplier_identity (P : ℝ[X]) (q : XiZeroCopy) (b : Bool) (n : ℤ)
    (a c : Ioi (0:ℝ)) :
    (∫ y in a.val..c.val, (P^2).eval y*signedDensity q b n y) =
      multiplierBoundary P q b n c-multiplierBoundary P q b n a+
        ∫ y in a.val..c.val, (P^2).derivative.derivative.eval y*modeMass q b n y := by
  have hp : uIcc a.val c.val ⊆ Ioi (0:ℝ) :=
    fun y hy => (lt_min a.2 c.2).trans_le hy.1
  have hi := ((P^2).continuousOn.mul ((signedDensity_continuous q b n).mono hp)).intervalIntegrable (μ := volume)
  have hj := ((P^2).derivative.derivative.continuousOn.mul
    ((modeMass_continuous q b n).mono hp)).intervalIntegrable (μ := volume)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => multiplierBoundary_hasDerivAt P q b n ⟨y,hp hy⟩) (hi.sub hj)
  rw [intervalIntegral.integral_sub hi hj] at he
  change (∫ y in a.val..c.val, (P^2).eval y*signedDensity q b n y)-
    (∫ y in a.val..c.val, (P^2).derivative.derivative.eval y*modeMass q b n y) =
      multiplierBoundary P q b n c-multiplierBoundary P q b n a at he
  linarith only [he]

/-- The one-sided multiplier flux used to absorb the mixed derivative term. -/
def multiplierFlux (P : ℝ[X]) (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : ℝ) : ℝ :=
  (P^2).eval y*deriv (modeMass q b n) y

private theorem squareWeight_derivative (P : ℝ[X]) (y : ℝ) :
    (P^2).derivative.eval y=2*P.eval y*P.derivative.eval y := by
  rw [show P^2=P*P by ring,Polynomial.derivative_mul,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_mul]
  ring

private theorem multiplierFlux_hasDerivAt (P : ℝ[X]) (q : XiZeroCopy) (b : Bool) (n : ℤ)
    (y : Ioi (0:ℝ)) :
    HasDerivAt (multiplierFlux P q b n)
      ((P^2).derivative.eval y.val*deriv (modeMass q b n) y+
        (P^2).eval y.val*signedDensity q b n y) y := by
  have h := ((P^2).hasDerivAt y.val).mul (modeMass_second_hasDerivAt q b n y)
  exact h

private theorem multiplier_square (M D : ℝ) (c d : ℂ) :
    0 ≤ M^2*Complex.normSq d+4*D^2*Complex.normSq c+
      4*M*D*(d*(starRingEnd ℂ) c).re := by
  have h := Complex.normSq_nonneg ((M:ℂ)*d+((2*D:ℝ):ℂ)*c)
  convert h using 1
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
  ring

/-- A second square absorbs the mixed derivative and leaves only the first
multiplier-derivative error; the original source loss is retained. -/
theorem nativeMode_firstWeight_coercivity (P : ℝ[X]) (q : XiZeroCopy) (b : Bool)
    (n : {n : ℤ // n ≠ 0}) (a : Ici (coercivityHeight q b)) (h : NNReal) :
    (∫ y in a.val..(a.val+h), (P^2).eval y*modeEnergy q b n.val y) ≤
      2*(multiplierFlux P q b n.val (a.val+h)-multiplierFlux P q b n.val a)+
        8*(∫ y in a.val..(a.val+h), (P.derivative.eval y)^2*modeMass q b n.val y)+
        2*(∫ y in a.val..(a.val+h), (P^2).eval y*forcingLoss q b n.val y) := by
  have ha : 0 < a.val := by
    have ht : 1+2*|(parameter q b).re| ≤ a.val := a.2
    linarith [abs_nonneg (parameter q b).re]
  have hc : 0 < a.val+h := add_pos_of_pos_of_nonneg ha h.2
  have hab : a.val ≤ a.val+h := le_add_of_nonneg_right h.2
  have hp : uIcc a.val (a.val+h) ⊆ Ioi (0:ℝ) :=
    fun y hy => (lt_min ha hc).trans_le hy.1
  let R : ℝ → ℝ := fun y => (P^2).derivative.eval y*deriv (modeMass q b n.val) y+
    (P^2).eval y*signedDensity q b n.val y
  have hu' : ContinuousOn (deriv (modeMass q b n.val)) (Ioi (0:ℝ)) :=
    fun y hy => (modeMass_second_hasDerivAt q b n.val ⟨y,hy⟩).continuousAt.continuousWithinAt
  have hR : IntervalIntegrable R volume a.val (a.val+h) :=
    (((P^2).derivative.continuousOn.mul (hu'.mono hp)).add
      ((P^2).continuousOn.mul ((signedDensity_continuous q b n.val).mono hp))).intervalIntegrable
  have hE := ((P^2).continuousOn.mul ((modeEnergy_continuous q b n.val).mono hp)).intervalIntegrable (μ := volume)
  have hF := ((P^2).continuousOn.mul ((forcingLoss_continuous q b n.val).mono hp)).intervalIntegrable (μ := volume)
  have hW := ((P.derivative.continuousOn.pow 2).mul
    ((modeMass_continuous q b n.val).mono hp)).intervalIntegrable (μ := volume)
  have hpoint (y : ℝ) (hy : y ∈ Icc a.val (a.val+h)) :
      (P^2).eval y*modeEnergy q b n.val y ≤
        2*R y+8*((P.derivative.eval y)^2*modeMass q b n.val y)+
          2*((P^2).eval y*forcingLoss q b n.val y) := by
    have hsource := modeMass_cusp_coercivity q b n ⟨y,a.2.trans hy.1⟩
    rw [(modeMass_second_hasDerivAt q b n.val ⟨y,ha.trans_le hy.1⟩).deriv] at hsource
    change modeEnergy q b n.val y-forcingLoss q b n.val y ≤ signedDensity q b n.val y at hsource
    have hsourceW := mul_le_mul_of_nonneg_left hsource (sq_nonneg (P.eval y))
    have hsquare := multiplier_square (P.eval y) (P.derivative.eval y)
      (responseMode q b n.val y) (deriv (responseMode q b n.val) y)
    have hpos : 0 ≤ (P.eval y)^2*(signedFrequency 1 n.val)^2*modeMass q b n.val y :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Complex.normSq_nonneg _)
    simp only [R,squareWeight_derivative,Polynomial.eval_pow,
      (modeMass_hasDerivAt q b n.val ⟨y,ha.trans_le hy.1⟩).deriv]
    change _ ≤ 2*(2*P.eval y*P.derivative.eval y*
      (2*(deriv (responseMode q b n.val) y*(starRingEnd ℂ) (responseMode q b n.val y)).re)+
        (P.eval y)^2*signedDensity q b n.val y)+
      8*((P.derivative.eval y)^2*modeMass q b n.val y)+
        2*((P.eval y)^2*forcingLoss q b n.val y)
    simp only [modeEnergy,modeMass] at hsourceW hpos ⊢
    nlinarith only [hsourceW,hsquare,hpos]
  have hb := intervalIntegral.integral_mono_on hab hE
    (((hR.const_mul 2).add ((hW.const_mul 8))).add (hF.const_mul 2)) hpoint
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => multiplierFlux_hasDerivAt P q b n.val ⟨y,hp hy⟩) hR
  rw [intervalIntegral.integral_add ((hR.const_mul 2).add (hW.const_mul 8))
    (hF.const_mul 2),intervalIntegral.integral_add (hR.const_mul 2) (hW.const_mul 8)] at hb
  change (∫ y in a.val..(a.val+h), (P^2).eval y*modeEnergy q b n.val y) ≤
    ((∫ y in a.val..(a.val+h), 2*R y)+
      (∫ y in a.val..(a.val+h), 8*((P.derivative.eval y)^2*modeMass q b n.val y)))+
        (∫ y in a.val..(a.val+h), 2*((P^2).eval y*forcingLoss q b n.val y)) at hb
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,he] at hb
  exact hb

/-- The complete literal forcing slice, with the original y^-4 loss weight. -/
def forcingMass (q : XiZeroCopy) (b : Bool) (y : ℝ) : ℝ :=
  (∫ x in (-1/2:ℝ)..(1/2),
    Complex.normSq (globalForcing q b (ofComplex (point x y))))/y^4

private theorem forcing_periodic (q : XiZeroCopy) (b : Bool) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x : ℝ => globalForcing q b (ofComplex (point x y))) 1 := by
  intro x
  have hpos (t : ℝ) : 0 < (point t y).im := by simpa [point] using hy
  have ht : ofComplex (point (x+1) y)=ModularGroup.T • ofComplex (point x y) := by
    rw [ofComplex_apply_of_im_pos (hpos x),ofComplex_apply_of_im_pos (hpos (x+1))]
    apply UpperHalfPlane.ext_re_im
    · rw [ModularGroup.re_T_smul]
      simp [point]
    · rw [ModularGroup.im_T_smul]
      simp [point]
  have h := globalForcing_invariant q b (QuotientGroup.mk ModularGroup.T) (ofComplex (point x y))
  simpa only [ht,PSL2Z_mk_smul] using h

/-- Parseval restores the entire forcing loss; no uniform single-mode constant is
summed over infinitely many frequencies. -/
theorem forcingLoss_hasSum (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    HasSum (fun n : ℤ => forcingLoss q b n y) (forcingMass q b y) := by
  have hs := GaloisForLFunctions.RHTower.SelbergMaassParseval.coefficient_mass_hasSum 1
    (by norm_num) (globalForcing_smooth q b).planar_contDiffOn.continuousOn y.2
  have hp : Function.Periodic
      (fun x : ℝ => Complex.normSq (globalForcing q b (ofComplex (point x y)))) 1 :=
    fun x => congrArg Complex.normSq (forcing_periodic q b y.2 x)
  have hi := hp.intervalIntegral_add_eq 0 (-1/2)
  norm_num only [zero_add,show (-1/2:ℝ)+1=1/2 by ring] at hi
  simp only [inv_one,one_mul,Function.comp_apply] at hs
  rw [hi] at hs
  simpa only [forcingLoss,forcingMode,forcingMass,neg_div] using hs.div_const (y.val^4)

/-- Every polynomial weight of the complete forcing loss is bounded directly by
the literal theta square remainder on the original cusp cell. -/
theorem forcingMass_weighted_bound (q : XiZeroCopy) (b : Bool) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Ioi (3:ℝ), y.val^(2*N+4)*forcingMass q b y ≤ C := by
  obtain ⟨A,hA,hbound⟩ := weighted_squareRemainder_bounded (center q) (N:ℂ) 3 (by norm_num)
  let D : ℝ := ‖parameter q b/2‖*A
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) hA
  refine ⟨D^2,sq_nonneg D,?_⟩
  intro y
  have hy : 0 < y.val := lt_trans (by norm_num : (0:ℝ)<3) y.2
  let G : ℝ → ℝ := fun x => Complex.normSq (globalForcing q b (ofComplex (point x y)))
  have hpoint (x : ℝ) (hx : x ∈ Icc (-1/2:ℝ) (1/2)) : y.val^(2*N)*G x ≤ D^2 := by
    have hpos : 0 < (point x y).im := by simpa [point] using hy
    let z : UpperHalfPlane := ⟨point x y,hpos⟩
    have hzre : z.re=x := by simp [z,UpperHalfPlane.re,point]
    have hzim : z.im=y.val := by simp [z,UpperHalfPlane.im,point]
    have hfd : z ∈ ModularGroup.fd := by
      constructor
      · change 1 ≤ z.re*z.re+z.im*z.im
        rw [hzre,hzim]
        have hy3 : (3:ℝ) < y.val := y.2
        nlinarith [sq_nonneg x]
      · rw [hzre]
        exact abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
    have hs : ‖(z.im:ℂ)^(N:ℂ)*globalForcing q b z‖ ≤ D := by
      rw [globalForcing_eq_on_fd q b z hfd,forcing_high q b _
        (by change 3 < z.im; rw [hzim]; exact y.2)]
      have he : (z.im:ℂ)^(N:ℂ)*((parameter q b/2)*squareRemainder (center q) (coordinates z)) =
          (parameter q b/2)*((z.im:ℂ)^(N:ℂ)*squareRemainder (center q) (coordinates z)) := by ring
      rw [he,norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound (coordinates z) (by change 3 ≤ z.im; rw [hzim]; exact y.2.le))
        (norm_nonneg _)
    rw [hzim,Complex.cpow_natCast,norm_mul,norm_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hy] at hs
    have hh := mul_nonneg (sub_nonneg.mpr hs)
      (add_nonneg hD (mul_nonneg (pow_nonneg hy.le N) (norm_nonneg (globalForcing q b z))))
    have hs2 : (y.val^N*‖globalForcing q b z‖)^2 ≤ D^2 := by nlinarith only [hh]
    change y.val^(2*N)*Complex.normSq (globalForcing q b (ofComplex (point x y))) ≤ D^2
    rw [ofComplex_apply_of_im_pos hpos,Complex.normSq_eq_norm_sq,
      show 2*N=N*2 by omega,pow_mul]
    nlinarith only [hs2]
  have hG : Continuous G := by
    have ht := (slice_continuous (globalForcing_smooth q b).planar_contDiffOn.continuousOn hy).norm.pow 2
    change Continuous (fun x : ℝ => ‖globalForcing q b (ofComplex (point x y))‖^2) at ht
    change Continuous (fun x : ℝ => Complex.normSq (globalForcing q b (ofComplex (point x y))))
    simpa only [Complex.normSq_eq_norm_sq] using ht
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (-1/2:ℝ) ≤ 1/2)
    ((hG.const_mul (y.val^(2*N))).intervalIntegrable (-1/2) (1/2))
    (continuous_const.intervalIntegrable (-1/2) (1/2)) hpoint
  change (∫ x in (-1/2:ℝ)..(1/2), y.val^(2*N)*G x) ≤
    (∫ _x in (-1/2:ℝ)..(1/2), D^2) at hi
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hi
  norm_num only [show (1/2:ℝ)-(-1/2)=1 by ring,smul_eq_mul,one_mul] at hi
  change y.val^(2*N+4)*((∫ x in (-1/2:ℝ)..(1/2), G x)/y.val^4) ≤ D^2
  have he : y.val^(2*N+4)*((∫ x in (-1/2:ℝ)..(1/2), G x)/y.val^4) =
      y.val^(2*N)*(∫ x in (-1/2:ℝ)..(1/2), G x) := by
    rw [pow_add]
    field_simp [hy.ne']
  rw [he]
  simpa only [neg_div] using hi

private def energyCutoff (N : ℕ) (A B : ℝ) : ℝ[X] :=
  Polynomial.X^(N+1)*(Polynomial.X-Polynomial.C A)*(1-Polynomial.C B⁻¹*Polynomial.X)

private theorem energyCutoff_eval (N : ℕ) (A B y : ℝ) :
    (energyCutoff N A B).eval y=y^(N+1)*(y-A)*(1-y/B) := by
  simp only [energyCutoff,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_one]
  rw [div_eq_mul_inv,mul_comm B⁻¹ y]

private theorem energyCutoff_derivative (N : ℕ) (A B y : ℝ) :
    (energyCutoff N A B).derivative.eval y =
      (N+1:ℝ)*y^N*(y-A)*(1-y/B)+y^(N+1)*(1-y/B)-y^(N+1)*((y-A)/B) := by
  simp only [energyCutoff,Polynomial.derivative_mul,Polynomial.derivative_X_pow_succ,
    Polynomial.derivative_sub,Polynomial.derivative_one,Polynomial.derivative_X,
    Polynomial.derivative_C,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_sub,
    Polynomial.eval_one,Polynomial.eval_zero]
  simp only [div_eq_mul_inv]
  ring

private theorem energyCutoff_bounds (N : ℕ) {A B y : ℝ} (hA : 0 < A)
    (hy : y ∈ Icc A B) :
    0 ≤ (energyCutoff N A B).eval y ∧
      (energyCutoff N A B).eval y ≤ y^(N+2) ∧
        |(energyCutoff N A B).derivative.eval y| ≤ (N+3:ℝ)*y^(N+1) := by
  have hy0 : 0 < y := hA.trans_le hy.1
  have hB : 0 < B := hy0.trans_le hy.2
  have hlow : 0 ≤ y-A := sub_nonneg.mpr hy.1
  have hupp : y-A ≤ y := sub_le_self _ hA.le
  have hfrac : 0 ≤ y/B := div_nonneg hy0.le hB.le
  have hfrac1 : y/B ≤ 1 := (div_le_one hB).mpr hy.2
  have hu : 0 ≤ 1-y/B := sub_nonneg.mpr hfrac1
  have hu1 : 1-y/B ≤ 1 := sub_le_self _ hfrac
  have hsubfrac : 0 ≤ (y-A)/B := div_nonneg hlow hB.le
  have hsubfrac1 : (y-A)/B ≤ 1 := (div_le_one hB).mpr (hupp.trans hy.2)
  have hp : 0 ≤ y^(N+1) := pow_nonneg hy0.le _
  rw [energyCutoff_eval,energyCutoff_derivative]
  refine ⟨mul_nonneg (mul_nonneg hp hlow) hu,?_,?_⟩
  · calc
      _ ≤ y^(N+1)*y*1 := mul_le_mul (mul_le_mul_of_nonneg_left hupp hp) hu1
        hu (mul_nonneg hp hy0.le)
      _ = _ := by rw [mul_one,← pow_succ]
  · have h1 : (N+1:ℝ)*y^N*(y-A)*(1-y/B) ≤ (N+1:ℝ)*y^(N+1) := by
      calc
        _ ≤ (N+1:ℝ)*y^N*y*1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hupp (by positivity)) hu1 hu (by positivity)
        _ = _ := by rw [mul_one,pow_succ]; ring
    have h1z : 0 ≤ (N+1:ℝ)*y^N*(y-A)*(1-y/B) := by positivity
    have h2 : y^(N+1)*(1-y/B) ≤ y^(N+1) := mul_le_of_le_one_right hp hu1
    have h2z : 0 ≤ y^(N+1)*(1-y/B) := mul_nonneg hp hu
    have h3 : y^(N+1)*((y-A)/B) ≤ y^(N+1) := mul_le_of_le_one_right hp hsubfrac1
    have h3z : 0 ≤ y^(N+1)*((y-A)/B) := mul_nonneg hp hsubfrac
    exact abs_le.mpr ⟨by nlinarith only [h1z,h2z,h3,hp,Nat.cast_nonneg (α:=ℝ) N],
      by nlinarith only [h1,h2,h3z,hp]⟩

private theorem energyCutoff_interior (N : ℕ) {A T y : ℝ} (hA : 0 < A)
    (hy : y ∈ Icc (A+1) T) : y^(2*(N+1)) ≤ 4*((energyCutoff N A (2*T)).eval y)^2 := by
  have hy0 : 0 < y := by linarith [hy.1]
  have hT : 0 < T := hy0.trans_le hy.2
  have hlow : 1 ≤ y-A := by linarith [hy.1]
  have hu : (1/2:ℝ) ≤ 1-y/(2*T) := by
    have hdiv : y/(2*T) ≤ 1/2 := (div_le_iff₀ (by positivity : 0 < 2*T)).mpr (by linarith [hy.2])
    linarith
  have hp : 0 ≤ y^(N+1) := pow_nonneg hy0.le _
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hlow hp) hu
    (by norm_num : (0:ℝ)≤1/2) (mul_nonneg hp (by linarith))
  rw [energyCutoff_eval]
  rw [mul_one] at h
  have he : y^(2*(N+1))=(y^(N+1))^2 := by rw [mul_comm 2,pow_mul]
  rw [he]
  nlinarith only [h,hp]

private theorem modeEnergy_nonneg (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : ℝ) :
    0 ≤ modeEnergy q b n y :=
  add_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
    (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))

private theorem forcingLoss_nonneg (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : ℝ) :
    0 ≤ forcingLoss q b n y := div_nonneg (Complex.normSq_nonneg _) (by positivity)

private theorem source_weight_bounds (q : XiZeroCopy) (b : Bool) (N : ℕ) :
    ∃ A : ℝ, 4 ≤ A ∧ coercivityHeight q b ≤ A ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : Ici A, y.val^(2*(N+1)+2)*nonconstantMass q b y ≤ 1 ∧
        y.val^(2*(N+2)+2)*forcingMass q b y ≤ C := by
  obtain ⟨C,hC,hF⟩ := forcingMass_weighted_bound q b (N+1)
  have ht := (nonconstantMass_weighted_tendsto_zero q b ((2*(N+1)+2:ℕ):ℝ)).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨Y,hY⟩ := eventually_atTop.1 ht
  let A : ℝ := max 4 (max (coercivityHeight q b) Y)
  have hAY : Y ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨A,le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),C,hC,?_⟩
  intro y
  constructor
  · simpa only [Real.rpow_natCast] using (hY y (hAY.trans y.2)).le
  · have hy3 : (3:ℝ) < y.val := lt_of_lt_of_le (by norm_num : (3:ℝ)<4)
      ((le_max_left _ _).trans y.2)
    convert hF ⟨y.val,hy3⟩ using 1
    congr 1

private theorem square_weight_absorb (k : ℕ) {y D d m C : ℝ} (hy : 0 < y)
    (hm : 0 ≤ m) (hb : |d| ≤ D*y^k) (hc : y^(2*k+2)*m ≤ C) :
    d^2*m ≤ D^2*C/y^2 := by
  have hs := (sq_le_sq₀ (abs_nonneg d) ((abs_nonneg d).trans hb)).2 hb
  rw [sq_abs,mul_pow] at hs
  apply (le_div_iff₀ (sq_pos_of_pos hy)).mpr
  calc
    d^2*m*y^2 ≤ D^2*(y^k)^2*m*y^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hm) (sq_nonneg y)
    _ = D^2*(y^(2*k+2)*m) := by
      rw [pow_add,show 2*k=k*2 by omega,pow_mul]
      ring
    _ ≤ D^2*C := mul_le_mul_of_nonneg_left hc (sq_nonneg D)

private theorem inverseSquare_integral_bound {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    (∫ y in A..B, 1/y^2) ≤ 1/A := by
  have hp (y : ℝ) (hy : y ∈ uIcc A B) : 0 < y := by
    rw [uIcc_of_le hAB] at hy
    exact hA.trans_le hy.1
  have hi : IntervalIntegrable (fun y : ℝ => 1/y^2) volume A B :=
    (show ContinuousOn (fun y : ℝ => 1/y^2) (uIcc A B) from
      fun y hy => (continuousAt_const.div (continuousAt_id.pow 2)
        (pow_ne_zero _ (hp y hy).ne')).continuousWithinAt).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy =>
    (show HasDerivAt (fun y : ℝ => -(1/y)) (1/y^2) y from by
      convert ((hasDerivAt_id y).inv (hp y hy).ne').neg using 1 <;> try rfl
      · funext t
        change -(1/t)=-(t⁻¹)
        rw [one_div]
      · simp only [id_eq,one_div,neg_div,neg_neg])) hi
  have hb : 0 ≤ 1/B := div_nonneg (by norm_num) (hA.le.trans hAB)
  linarith only [he,hb]

private theorem finite_cutoff_bound (q : XiZeroCopy) (b : Bool) (N : ℕ)
    {A B C : ℝ} (hA : 0 < A) (hAC : coercivityHeight q b ≤ A) (hAB : A ≤ B) (hC : 0 ≤ C)
    (hsource : ∀ y : Ici A, y.val^(2*(N+1)+2)*nonconstantMass q b y ≤ 1 ∧
      y.val^(2*(N+2)+2)*forcingMass q b y ≤ C)
    (E : Finset {n : ℤ // n ≠ 0}) :
    (∫ y in A..B, ((energyCutoff N A B).eval y)^2*
      ∑ n ∈ E, modeEnergy q b n.val y) ≤ (8*(N+3:ℝ)^2+2*C)/A := by
  let P := energyCutoff N A B
  have hB : 0 < B := hA.trans_le hAB
  have hp : uIcc A B ⊆ Ioi (0:ℝ) := by
    rw [uIcc_of_le hAB]
    exact fun y hy => hA.trans_le hy.1
  have hiE (n : {n : ℤ // n ≠ 0}) : IntervalIntegrable
      (fun y : ℝ => (P.eval y)^2*modeEnergy q b n.val y) volume A B :=
    ((P.continuousOn.pow 2).mul ((modeEnergy_continuous q b n.val).mono hp)).intervalIntegrable
  have hiM (n : {n : ℤ // n ≠ 0}) : IntervalIntegrable
      (fun y : ℝ => (P.derivative.eval y)^2*modeMass q b n.val y) volume A B :=
    ((P.derivative.continuousOn.pow 2).mul ((modeMass_continuous q b n.val).mono hp)).intervalIntegrable
  have hiF (n : {n : ℤ // n ≠ 0}) : IntervalIntegrable
      (fun y : ℝ => (P.eval y)^2*forcingLoss q b n.val y) volume A B :=
    ((P.continuousOn.pow 2).mul ((forcingLoss_continuous q b n.val).mono hp)).intervalIntegrable
  have hmode (n : {n : ℤ // n ≠ 0}) :
      (∫ y in A..B, (P.eval y)^2*modeEnergy q b n.val y) ≤
        8*(∫ y in A..B, (P.derivative.eval y)^2*modeMass q b n.val y)+
          2*(∫ y in A..B, (P.eval y)^2*forcingLoss q b n.val y) := by
    have h := nativeMode_firstWeight_coercivity P q b n ⟨A,hAC⟩ ⟨B-A,sub_nonneg.mpr hAB⟩
    change (∫ y in A..(A+(B-A)), (P^2).eval y*modeEnergy q b n.val y) ≤
      2*(multiplierFlux P q b n.val (A+(B-A))-multiplierFlux P q b n.val A)+
        8*(∫ y in A..(A+(B-A)), (P.derivative.eval y)^2*modeMass q b n.val y)+
          2*(∫ y in A..(A+(B-A)), (P^2).eval y*forcingLoss q b n.val y) at h
    have hPA : P.eval A=0 := by simp only [P,energyCutoff_eval,sub_self,mul_zero,zero_mul]
    have hPB : P.eval B=0 := by simp only [P,energyCutoff_eval,div_self hB.ne',sub_self,mul_zero]
    simpa only [show A+(B-A)=B by ring,multiplierFlux,Polynomial.eval_pow,hPA,hPB,
      zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,sub_self,zero_add,mul_zero] using h
  let R : ℝ → ℝ := fun y => 8*((P.derivative.eval y)^2*∑ n ∈ E, modeMass q b n.val y)+
    2*((P.eval y)^2*∑ n ∈ E, forcingLoss q b n.val y)
  have hiMsum : IntervalIntegrable (fun y : ℝ => (P.derivative.eval y)^2*
      ∑ n ∈ E, modeMass q b n.val y) volume A B := by
    convert IntervalIntegrable.sum E (fun n (_ : n ∈ E) => hiM n) using 1 <;> try rfl
    funext y
    simp only [Finset.sum_apply,Finset.mul_sum]
  have hiFsum : IntervalIntegrable (fun y : ℝ => (P.eval y)^2*
      ∑ n ∈ E, forcingLoss q b n.val y) volume A B := by
    convert IntervalIntegrable.sum E (fun n (_ : n ∈ E) => hiF n) using 1 <;> try rfl
    funext y
    simp only [Finset.sum_apply,Finset.mul_sum]
  have hiR : IntervalIntegrable R volume A B := (hiMsum.const_mul 8).add (hiFsum.const_mul 2)
  have hsum : (∫ y in A..B, (P.eval y)^2*∑ n ∈ E, modeEnergy q b n.val y) ≤
      ∫ y in A..B, R y := by
    have hh := Finset.sum_le_sum (fun n (_ : n ∈ E) => hmode n)
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum] at hh
    simp_rw [← intervalIntegral.integral_finsetSum (fun n (_ : n ∈ E) => hiE n),
      ← intervalIntegral.integral_finsetSum (fun n (_ : n ∈ E) => hiM n),
      ← intervalIntegral.integral_finsetSum (fun n (_ : n ∈ E) => hiF n)] at hh
    change _ ≤ ∫ y in A..B, 8*((P.derivative.eval y)^2*∑ n ∈ E, modeMass q b n.val y)+
      2*((P.eval y)^2*∑ n ∈ E, forcingLoss q b n.val y)
    rw [intervalIntegral.integral_add (hiMsum.const_mul 8) (hiFsum.const_mul 2),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
    simpa only [Finset.mul_sum] using hh
  have hpoint (y : ℝ) (hy : y ∈ Icc A B) : R y ≤ (8*(N+3:ℝ)^2+2*C)*(1/y^2) := by
    have hy0 : 0 < y := hA.trans_le hy.1
    have hsm := (modeMass_hasSum q b ⟨y,hy0⟩).summable.subtype (fun n : ℤ => n ≠ 0)
    have hsf := (forcingLoss_hasSum q b ⟨y,hy0⟩).summable
    have hmass : (∑ n ∈ E, modeMass q b n.val y) ≤ nonconstantMass q b y :=
      hsm.sum_le_tsum E (fun n _ => Complex.normSq_nonneg _)
    have hforcing : (∑ n ∈ E, forcingLoss q b n.val y) ≤ forcingMass q b y := by
      have h := hsf.subtype (fun n : ℤ => n ≠ 0)
      have he := h.sum_le_tsum E (fun n _ => forcingLoss_nonneg q b n.val y)
      exact he.trans ((Summable.tsum_subtype_le (fun n : ℤ => forcingLoss q b n y)
        {n | n ≠ 0} (fun n => forcingLoss_nonneg q b n y) hsf).trans_eq
        (forcingLoss_hasSum q b ⟨y,hy0⟩).tsum_eq)
    have hc := hsource ⟨y,hy.1⟩
    have hmcap := (mul_le_mul_of_nonneg_left hmass (pow_nonneg hy0.le (2*(N+1)+2))).trans hc.1
    have hfcap := (mul_le_mul_of_nonneg_left hforcing (pow_nonneg hy0.le (2*(N+2)+2))).trans hc.2
    have hcut := energyCutoff_bounds N hA hy
    have hM := square_weight_absorb (N+1) hy0
      (Finset.sum_nonneg (fun n _ => Complex.normSq_nonneg _)) hcut.2.2 hmcap
    have hF := square_weight_absorb (N+2) (D := 1) (d := P.eval y) hy0
      (Finset.sum_nonneg (fun n _ => forcingLoss_nonneg q b n.val y))
      (by change |(energyCutoff N A B).eval y| ≤ 1*y^(N+2)
          rw [abs_of_nonneg hcut.1,one_mul]; exact hcut.2.1) hfcap
    change (P.derivative.eval y)^2*(∑ n ∈ E, modeMass q b n.val y) ≤
      (N+3:ℝ)^2*1/y^2 at hM
    dsimp only [R]
    dsimp only [P] at *
    simp only [mul_one,one_pow,one_mul,div_eq_mul_inv] at hM hF ⊢
    nlinarith only [hM,hF]
  have hiV : IntervalIntegrable (fun y : ℝ => 1/y^2) volume A B :=
    (show ContinuousOn (fun y : ℝ => 1/y^2) (uIcc A B) from
      fun y hy => (continuousAt_const.div (continuousAt_id.pow 2)
        (pow_ne_zero _ (hp hy).ne')).continuousWithinAt).intervalIntegrable
  have hbnd := intervalIntegral.integral_mono_on hAB hiR
    (hiV.const_mul (8*(N+3:ℝ)^2+2*C)) hpoint
  change (∫ y in A..B, R y) ≤ ∫ y in A..B, (8*(N+3:ℝ)^2+2*C)*(1/y^2) at hbnd
  rw [intervalIntegral.integral_const_mul] at hbnd
  have hx := mul_le_mul_of_nonneg_left (inverseSquare_integral_bound hA hAB)
    (by positivity : 0 ≤ 8*(N+3:ℝ)^2+2*C)
  exact (hsum.trans hbnd).trans (by simpa only [mul_one_div] using hx)

private theorem evenWeight_nonneg (N : ℕ) (y : ℝ) : 0 ≤ y^(2*(N+1)) := by
  rw [mul_comm 2,pow_mul]
  exact sq_nonneg _

private theorem finiteEnergy_continuous (q : XiZeroCopy) (b : Bool)
    (E : Finset {n : ℤ // n ≠ 0}) :
    ContinuousOn (fun y : ℝ => ∑ n ∈ E, modeEnergy q b n.val y) (Ioi (0:ℝ)) := by
  exact continuousOn_finsetSum E (fun n _ => modeEnergy_continuous q b n.val)

private theorem finite_energy_interval_bound (q : XiZeroCopy) (b : Bool) (N : ℕ) :
    ∃ A : ℝ, 4 ≤ A ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (E : Finset {n : ℤ // n ≠ 0}) (T : Ici (A+1)),
        (∫ y in (A+1)..T.val, y^(2*(N+1))*∑ n ∈ E, modeEnergy q b n.val y) ≤ K := by
  obtain ⟨A,hA,hAC,C,hC,hsource⟩ := source_weight_bounds q b N
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  let K : ℝ := 4*((8*(N+3:ℝ)^2+2*C)/A)
  refine ⟨A,hA,K,by dsimp [K]; positivity,?_⟩
  intro E T
  have hT : A+1 ≤ T.val := T.2
  have hT0 : 0 < T.val := by linarith
  have hAT : A ≤ 2*T.val := by linarith
  let P := energyCutoff N A (2*T.val)
  let F : ℝ → ℝ := fun y => (P.eval y)^2*∑ n ∈ E, modeEnergy q b n.val y
  have hn (y : ℝ) : 0 ≤ F y := mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg (fun n _ => modeEnergy_nonneg q b n.val y))
  have hp : uIcc A (2*T.val) ⊆ Ioi (0:ℝ) := by
    rw [uIcc_of_le hAT]
    exact fun y hy => hA0.trans_le hy.1
  have hc : ContinuousOn F (uIcc A (2*T.val)) :=
    (P.continuousOn.pow 2).mul ((finiteEnergy_continuous q b E).mono hp)
  have hiF : IntervalIntegrable F volume A (2*T.val) := hc.intervalIntegrable
  have hps : uIcc (A+1) T.val ⊆ Ioi (0:ℝ) := by
    rw [uIcc_of_le hT]
    exact fun y hy => (by linarith : 0 < A+1).trans_le hy.1
  have hiFs : IntervalIntegrable F volume (A+1) T.val :=
    ((P.continuousOn.pow 2).mul ((finiteEnergy_continuous q b E).mono hps)).intervalIntegrable
  have hiE : IntervalIntegrable
      (fun y : ℝ => y^(2*(N+1))*∑ n ∈ E, modeEnergy q b n.val y) volume (A+1) T.val :=
    ((continuousOn_id.pow (2*(N+1))).mul ((finiteEnergy_continuous q b E).mono hps)).intervalIntegrable
  have hm := intervalIntegral.integral_mono_on hT hiE (hiFs.const_mul 4)
    (fun y hy => show y^(2*(N+1))*(∑ n ∈ E, modeEnergy q b n.val y) ≤ 4*F y from by
      have hh := mul_le_mul_of_nonneg_right (energyCutoff_interior N hA0 hy)
        (Finset.sum_nonneg (s := E) (fun n _ => modeEnergy_nonneg q b n.val y))
      simpa only [F,P,mul_assoc] using hh)
  change _ ≤ ∫ y in (A+1)..T.val, 4*F y at hm
  rw [intervalIntegral.integral_const_mul] at hm
  have hsub := intervalIntegral.integral_mono_interval
    (by linarith : A ≤ A+1) hT (by linarith : T.val ≤ 2*T.val)
    (Filter.Eventually.of_forall hn) hiF
  have hb := finite_cutoff_bound q b N hA0 hAC hAT hC hsource E
  exact hm.trans ((mul_le_mul_of_nonneg_left (hsub.trans hb) (by norm_num : (0:ℝ)≤4)))

/-- Original source equations admit every finite nonconstant modal energy with
one bound independent of the mode set and upper cusp endpoint. -/
theorem nativeFiniteEnergy_admission (q : XiZeroCopy) (b : Bool) (N : ℕ) :
    ∃ A : ℝ, 4 ≤ A ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ E : Finset {n : ℤ // n ≠ 0},
        IntegrableOn (fun y : ℝ => y^(2*(N+1))*∑ n ∈ E, modeEnergy q b n.val y) (Ioi (A+1)) ∧
          (∫ y in Ioi (A+1), y^(2*(N+1))*∑ n ∈ E, modeEnergy q b n.val y) ≤ K := by
  obtain ⟨A,hA,K,hK,hbound⟩ := finite_energy_interval_bound q b N
  refine ⟨A,hA,K,hK,?_⟩
  intro E
  let f : ℝ → ℝ := fun y => y^(2*(N+1))*∑ n ∈ E, modeEnergy q b n.val y
  have hn (y : ℝ) : 0 ≤ f y := mul_nonneg (evenWeight_nonneg N y)
    (Finset.sum_nonneg (fun n _ => modeEnergy_nonneg q b n.val y))
  have hA0 : 0 < A+1 := by linarith
  have hi (T : ℝ) : IntervalIntegrable f volume (A+1) (max (A+1) T) := by
    have hp : uIcc (A+1) (max (A+1) T) ⊆ Ioi (0:ℝ) := by
      rw [uIcc_of_le (le_max_left _ _)]
      exact fun y hy => hA0.trans_le hy.1
    exact ((continuousOn_id.pow (2*(N+1))).mul
      ((finiteEnergy_continuous q b E).mono hp)).intervalIntegrable
  have ht : Tendsto (fun T : ℝ => max (A+1) T) atTop atTop :=
    tendsto_atTop_mono (fun T => le_max_right (A+1) T) tendsto_id
  have hint : IntegrableOn f (Ioi (A+1)) :=
    integrableOn_Ioi_of_intervalIntegral_norm_bounded K (A+1) (fun T => (hi T).1) ht
      (Filter.Eventually.of_forall (fun T => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hn _)] using
          hbound E ⟨max (A+1) T,by change A+1 ≤ max (A+1) T; exact le_max_left _ _⟩))
  refine ⟨hint,?_⟩
  have hlim := intervalIntegral_tendsto_integral_Ioi (A+1) hint (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (A+1)] with T hT
  exact hbound E ⟨T,hT⟩

/-- The complete nonconstant native derivative energy, with every frequency retained. -/
def nonconstantEnergy (q : XiZeroCopy) (b : Bool) (y : ℝ) : ℝ :=
  ∑' n : {n : ℤ // n ≠ 0}, modeEnergy q b n.val y

/-- Polynomially weighted derivative energy of the original source response is
integrable on a source-derived cusp tail, with no upper response trace assumed. -/
theorem nativeNonconstantEnergy_admission (q : XiZeroCopy) (b : Bool) (N : ℕ) :
    ∃ A : ℝ, 4 ≤ A ∧
      IntegrableOn (fun y : ℝ => y^(2*(N+1))*nonconstantEnergy q b y) (Ioi (A+1)) ∧
      Summable (fun n : {n : ℤ // n ≠ 0} => ∫ y in Ioi (A+1), y^(2*(N+1))*modeEnergy q b n.val y) := by
  obtain ⟨A,hA,K,hK,hbound⟩ := nativeFiniteEnergy_admission q b N
  let μ : Measure ℝ := volume.restrict (Ioi (A+1))
  let f : {n : ℤ // n ≠ 0} → ℝ → ℝ := fun n y => y^(2*(N+1))*modeEnergy q b n.val y
  have hn (n : {n : ℤ // n ≠ 0}) (y : ℝ) : 0 ≤ f n y :=
    mul_nonneg (evenWeight_nonneg N y) (modeEnergy_nonneg q b n.val y)
  have hi (n : {n : ℤ // n ≠ 0}) : Integrable (f n) μ := by
    change IntegrableOn (fun y : ℝ => y^(2*(N+1))*modeEnergy q b n.val y) (Ioi (A+1))
    simpa only [Finset.sum_singleton] using (hbound {n}).1
  have hs : Summable (fun n : {n : ℤ // n ≠ 0} => ∫ y, f n y ∂μ) := by
    apply summable_of_sum_le (fun n => integral_nonneg (hn n))
    intro E
    rw [← integral_finsetSum E (fun n _ => hi n)]
    simpa only [f,Finset.mul_sum] using (hbound E).2
  have hfin : (∑' n, ∫⁻ y, ENNReal.ofReal (f n y) ∂μ) < ⊤ := by
    have he (n : {n : ℤ // n ≠ 0}) :
        (∫⁻ y, ENNReal.ofReal (f n y) ∂μ)=ENNReal.ofReal (∫ y, f n y ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (hi n) (Filter.Eventually.of_forall (hn n))).symm
    simp_rw [he]
    exact hs.tsum_ofReal_lt_top
  have hmeas : AEMeasurable (fun y => ∑' n, f n y) μ :=
    AEMeasurable.tsum (fun n => (hi n).aestronglyMeasurable.aemeasurable)
  have htotal : Integrable (fun y => ∑' n, f n y) μ := by
    refine ⟨hmeas.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun y => tsum_nonneg (fun n => hn n y)))).mpr ?_⟩
    have hle : (∫⁻ y, ENNReal.ofReal (∑' n, f n y) ∂μ) ≤ ∑' n, ∫⁻ y, ENNReal.ofReal (f n y) ∂μ := by
      rw [← lintegral_tsum (fun n => (hi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
      apply lintegral_mono
      intro y
      change ENNReal.ofReal (∑' n, f n y) ≤ ∑' n, ENNReal.ofReal (f n y)
      by_cases hh : Summable (fun n => f n y)
      · exact (ENNReal.ofReal_tsum_of_nonneg (fun n => hn n y) hh).le
      · rw [tsum_eq_zero_of_not_summable hh,ENNReal.ofReal_zero]
        exact bot_le
    exact hle.trans_lt hfin
  refine ⟨A,hA,?_,hs⟩
  change Integrable (fun y => y^(2*(N+1))*nonconstantEnergy q b y) μ
  simpa only [f,tsum_mul_left,nonconstantEnergy] using htotal

/-- Literal first-gradient slice, with the same vertical factor as modal coercivity. -/
def nativeGradientSlice (q : XiZeroCopy) (b : Bool) (y : ℝ) : ℝ :=
  2*(∫ x in (0:ℝ)..1, Complex.normSq
    (directional Complex.I (D4BMCuspResponse.responsePlanar q b) (point x y)))+
      ∫ x in (0:ℝ)..1, Complex.normSq
        (directional 1 (D4BMCuspResponse.responsePlanar q b) (point x y))

/-- Parseval identifies every modal derivative with the original response gradient,
independently of the cusp-tail energy estimate. -/
theorem modeEnergy_hasSum (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    HasSum (fun n : ℤ => modeEnergy q b n y) (nativeGradientSlice q b y) := by
  let F := D4BMCuspResponse.responsePlanar q b
  have hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im} :=
    (D4BMCuspResponse.responsePlanar_smooth q b).of_le (WithTop.coe_le_coe.mpr le_top)
  have hv := directional_contDiffOn hf (m := 0) (by simp) Complex.I
  have hh := directional_contDiffOn hf (m := 0) (by simp) (1:ℂ)
  have hV : HasSum (fun n : ℤ => Complex.normSq (deriv (responseMode q b n) y))
      (∫ x in (0:ℝ)..1, Complex.normSq (directional Complex.I F (point x y))) := by
    have hs := GaloisForLFunctions.RHTower.SelbergMaassParseval.coefficient_mass_hasSum
      1 (by norm_num) hv.continuousOn y.2
    simp only [inv_one,one_mul] at hs
    apply hs.congr_fun
    intro n
    change Complex.normSq (deriv (coefficient 1 n F) y) = _
    rw [(coefficient_hasDerivAt 1 (by norm_num) n hf y.2).deriv]
  have hH : HasSum (fun n : ℤ => (signedFrequency 1 n)^2*modeMass q b n y)
      (∫ x in (0:ℝ)..1, Complex.normSq (directional 1 F (point x y))) := by
    have hs := GaloisForLFunctions.RHTower.SelbergMaassParseval.coefficient_mass_hasSum
      1 (by norm_num) hh.continuousOn y.2
    simp only [inv_one,one_mul] at hs
    apply hs.congr_fun
    intro n
    rw [GaloisForLFunctions.RHTower.SelbergMaassParseval.coefficient_horizontal 1
      (by norm_num) n hf y.2 (D4BMCuspResponse.responsePlanar_periodic q b y.2)]
    simp only [Complex.normSq_mul,Complex.normSq_ofReal,Complex.normSq_I,mul_one,
      modeMass,responseMode,F,pow_two]
  exact (hV.mul_left 2).add hH

/-- The actual gradient slice retains its original zero-frequency derivative energy
alongside the complete nonconstant contribution. -/
theorem nativeGradientSlice_decomposition (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    nativeGradientSlice q b y=modeEnergy q b 0 y+nonconstantEnergy q b y := by
  have hs := modeEnergy_hasSum q b y
  have he := hs.summable.sum_add_tsum_subtype_compl ({0}:Finset ℤ)
  have htail : (∑' n : {n : ℤ // n ∉ ({0}:Finset ℤ)}, modeEnergy q b n.val y)=
      nonconstantEnergy q b y := by
    unfold nonconstantEnergy
    exact tsum_congr_subtype (fun n : ℤ => modeEnergy q b n y)
      (fun _ => not_congr Finset.mem_singleton)
  rw [Finset.sum_singleton,hs.tsum_eq] at he
  exact he.symm.trans (congrArg (fun t : ℝ => modeEnergy q b 0 y+t) htail)

/-- The admitted energy is the complete literal gradient remainder, with the
native zero-mode derivative restored explicitly. -/
theorem nativeGradientRemainder_admission (q : XiZeroCopy) (b : Bool) (N : ℕ) :
    ∃ A : ℝ, 4 ≤ A ∧ IntegrableOn
      (fun y : ℝ => y^(2*(N+1))*(nativeGradientSlice q b y-modeEnergy q b 0 y)) (Ioi (A+1)) := by
  obtain ⟨A,hA,hi,_⟩ := nativeNonconstantEnergy_admission q b N
  refine ⟨A,hA,hi.congr_fun ?_ measurableSet_Ioi⟩
  intro y hy
  have hy0 : 0 < y := by have hh : A+1 < y := hy; linarith
  change y^(2*(N+1))*nonconstantEnergy q b y =
    y^(2*(N+1))*(nativeGradientSlice q b y-modeEnergy q b 0 y)
  rw [nativeGradientSlice_decomposition q b ⟨y,hy0⟩,add_sub_cancel_left]

end
end RHTower.D4BMQuarticNativeCuspEnergy

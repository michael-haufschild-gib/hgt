import GaloisForLFunctions.ThetaCuspSections.FifthEvenFourAtomRemainder
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTailMassFloor
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTailRateMoments
/-!
# Fixed-coordinate control of the integrated theta remainder

The reflected source after four atoms has a Cauchy bound with an explicit
exponential rate. Radial integration keeps that decay and compares the
result to the constant first-atom gamma moment matrix.
-/
noncomputable section
open MeasureTheory Set Filter Topology Matrix
namespace GaloisForLFunctions.ThetaCuspSections.FifthTailRemainder
open _root_.RHTower FifthAtomTail FifthRateTail TailMassFloor FourAtomCauchyTail FifthRemainder

/-- Reflection centre associated to a positive radial scale. -/
def radialCenter (t : ℝ) : ℝ := Real.log (t/Real.pi)/2
/-- Literal signed reflected remainder in radial integration coordinates. -/
def radialError (k : ℕ) (t : ℝ) : ℝ :=
 (Real.pi^(1/2:ℝ)/4)*((-1:ℝ)^k*
  (thetaCuspNativeReflectionJet (2*k) (radialCenter t)-
   thetaCuspFourAtomReflectionJet (2*k) (radialCenter t)))/t
/-- The integrated remainder after retaining every ordered pair among four atoms. -/
def errorMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 ∫ t in Ioi q, radialError (i.val+j.val) t

private theorem fourJet_eq (n : ℕ) (x : ℝ) :
 thetaCuspFourAtomReflectionJet n x=
  ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*iteratedDeriv i thetaCuspFourAtomSource x*
   ((-1:ℝ)^(n-i)*iteratedDeriv (n-i) thetaCuspFourAtomSource x) := by
 have hf : ContDiff ℝ n thetaCuspFourAtomSource := contDiff_thetaCuspFourAtomSource.of_le
   (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
 unfold thetaCuspFourAtomReflectionJet
 change iteratedDeriv n
  ((fun t => thetaCuspFourAtomSource (x+t))*(fun t => thetaCuspFourAtomSource (x-t))) 0= _
 have hl : ContDiffAt ℝ n (fun t : ℝ => thetaCuspFourAtomSource (x+t)) 0 :=
  (hf.comp (contDiff_const.add contDiff_id)).contDiffAt
 have hr : ContDiffAt ℝ n (fun t : ℝ => thetaCuspFourAtomSource (x-t)) 0 :=
  (hf.comp (contDiff_const.sub contDiff_id)).contDiffAt
 rw [iteratedDeriv_mul hl hr]
 simp only [iteratedDeriv_comp_const_add,iteratedDeriv_comp_const_sub,
  add_zero,sub_zero,smul_eq_mul]

private theorem fourJet_continuous (n : ℕ) : Continuous (thetaCuspFourAtomReflectionJet n) := by
 have hj (k : ℕ) : Continuous (iteratedDeriv k thetaCuspFourAtomSource) :=
  ContDiff.continuous_iteratedDeriv k contDiff_thetaCuspFourAtomSource (by
   exact_mod_cast (le_top : (k:ℕ∞)≤⊤))
 change Continuous (fun x => thetaCuspFourAtomReflectionJet n x)
 simp_rw [fourJet_eq]
 fun_prop

private theorem radialCenter_scale {t : ℝ} (ht : 0<t) :
 thetaCuspSingleAtomReflectionScale 1 (radialCenter t)=t := by
 unfold radialCenter thetaCuspSingleAtomReflectionScale
 rw [show 2*(Real.log (t/Real.pi)/2)=Real.log (t/Real.pi) by ring,
  Real.exp_log (div_pos ht Real.pi_pos)]
 norm_num
 field_simp

private theorem sourceUnit_scaled (x : ℝ) :
 (Real.pi^(1/2:ℝ)/4)*sourceUnit x/thetaCuspSingleAtomReflectionScale 1 x=
  boundary (thetaCuspSingleAtomReflectionScale 1 x) := by
 have hq : 0<thetaCuspSingleAtomReflectionScale 1 x := by
  unfold thetaCuspSingleAtomReflectionScale
  positivity
 have hscale : thetaCuspSingleAtomReflectionScale 1 x=Real.pi*Real.exp (2*x) := by
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one]
 have hp : (thetaCuspSingleAtomReflectionScale 1 x)^(3/2:ℝ)=
   thetaCuspSingleAtomReflectionScale 1 x*Real.pi^(1/2:ℝ)*Real.exp x := by
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hq,Real.rpow_one,hscale,
   Real.mul_rpow Real.pi_pos.le (Real.exp_pos _).le,← Real.exp_mul,
   show (2*x)*(1/2)=x by ring]
  ring
 have he : Real.exp (x-2*thetaCuspSingleAtomReflectionScale 1 x)=
   Real.exp x*Real.exp (-2*thetaCuspSingleAtomReflectionScale 1 x) := by
  rw [← Real.exp_add]
  congr 1
  ring
 unfold sourceUnit boundary
 rw [hp,he]
 field_simp [hq.ne']

/-- Fixed Cauchy coefficient of a signed even reflected jet. -/
def cauchyCoefficient (k : ℕ) : ℝ := ((2*k).factorial:ℝ)*(400/9)^k

private theorem radialError_point_bound (k : ℕ) {t : ℝ} (ht : 3≤t) :
 |radialError k t|≤cauchyCoefficient k*20000*boundary t*
   ((2*t-3)^2*Real.exp (-(431/25)*t)) := by
 have ht0 : 0<t := by linarith only [ht]
 have hscale := radialCenter_scale ht0
 have hq : 3≤thetaCuspSingleAtomReflectionScale 1 (radialCenter t) := by
  rw [hscale]
  exact ht
 have hC := native_fourAtom_cauchy_error (2*k) hq
 rw [hscale] at hC
 have hmass := _root_.RHTower.ThetaCuspOddFourCentralBound.sourceTerm_one_sq (radialCenter t)
 change thetaCuspSourceTerm (radialCenter t) 1^2=
  sourceUnit (radialCenter t)*(2*thetaCuspSingleAtomReflectionScale 1 (radialCenter t)-3)^2 at hmass
 rw [hscale] at hmass
 have hunit := sourceUnit_scaled (radialCenter t)
 rw [hscale] at hunit
 have hinv : ((3/20:ℝ)^(2*k))⁻¹=(400/9:ℝ)^k := by
  rw [pow_mul,← inv_pow]
  norm_num
 have hc0 : 0<Real.pi^(1/2:ℝ)/4 := by positivity
 calc
  _ = ((Real.pi^(1/2:ℝ)/4)/t)*
    |thetaCuspNativeReflectionJet (2*k) (radialCenter t)-
     thetaCuspFourAtomReflectionJet (2*k) (radialCenter t)| := by
   unfold radialError
   rw [abs_div,abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_pos hc0,abs_of_pos ht0]
   ring
  _ ≤ ((Real.pi^(1/2:ℝ)/4)/t)*
    (((2*k).factorial:ℝ)*(20000*thetaCuspSourceTerm (radialCenter t) 1^2*
     Real.exp (-(431/25)*t))/(3/20)^(2*k)) :=
   mul_le_mul_of_nonneg_left hC (by positivity)
  _ = (((2*k).factorial:ℝ)*((3/20:ℝ)^(2*k))⁻¹)*20000*
    ((Real.pi^(1/2:ℝ)/4)*sourceUnit (radialCenter t)/t)*
    ((2*t-3)^2*Real.exp (-(431/25)*t)) := by
   rw [hmass]
   ring
  _ = _ := by rw [hinv,hunit]; rfl

/-- The full omitted source retains a rate-nineteen integrable radial majorant. -/
theorem radialError_bound (k : ℕ) {t : ℝ} (ht : 3≤t) :
 |radialError k t|≤80000*cauchyCoefficient k*(rateBoundary 19 t*t^2) := by
 have ht0 : 0<t := by linarith only [ht]
 have hp : (2*t-3)^2≤4*t^2 := by nlinarith only [ht]
 have he : Real.exp (-(431/25)*t)≤Real.exp (-17*t) := by
  apply Real.exp_le_exp.mpr
  linarith only [ht]
 have hc : 0≤cauchyCoefficient k*20000*boundary t := by
  unfold cauchyCoefficient boundary
  positivity
 calc
  _ ≤ cauchyCoefficient k*20000*boundary t*((2*t-3)^2*Real.exp (-(431/25)*t)) :=
   radialError_point_bound k ht
  _ ≤ cauchyCoefficient k*20000*boundary t*(4*t^2*Real.exp (-17*t)) :=
   mul_le_mul_of_nonneg_left (mul_le_mul hp he (Real.exp_pos _).le (by positivity)) hc
  _ = _ := by
   rw [rateBoundary_relative]
   norm_num
   ring

private theorem radialError_continuousOn (k : ℕ) {q : ℝ} (hq : 0<q) :
 ContinuousOn (radialError k) (Ioi q) := by
 intro t ht
 have ht0 : 0<t := hq.trans ht
 have hcenter : ContinuousAt radialCenter t := by
  unfold radialCenter
  have hdiv : ContinuousAt (fun u : ℝ => u/Real.pi) t := continuousAt_id.div_const Real.pi
  exact (hdiv.log (div_ne_zero ht0.ne' Real.pi_ne_zero)).div_const 2
 have hn := (continuous_thetaCuspNativeReflectionJet (2*k)).continuousAt.comp hcenter
 have hf := (fourJet_continuous (2*k)).continuousAt.comp hcenter
 exact ((continuousAt_const.mul (continuousAt_const.mul (hn.sub hf))).div
   continuousAt_id ht0.ne').continuousWithinAt

/-- Every literal radial remainder entry is integrable on the scale-three ray. -/
theorem radialError_integrable (k : ℕ) {q : ℝ} (hq : 3≤q) :
 IntegrableOn (radialError k) (Ioi q) := by
 have hq0 : 0<q := by linarith only [hq]
 have hi := (weighted_power_integrable (by norm_num : (0:ℝ)<19) 2 hq0).const_mul
   (80000*cauchyCoefficient k)
 apply hi.mono' ((radialError_continuousOn k hq0).aestronglyMeasurable measurableSet_Ioi)
 filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
 simpa only [Real.norm_eq_abs] using radialError_bound k (hq.trans ht.le)

/-- The literal integrated remainder keeps its exponential decay in each signed moment. -/
theorem integral_radialError_bound (k : ℕ) {q : ℝ} (hq : 3≤q) :
 |∫ t in Ioi q, radialError k t|≤
  (80000/17)*cauchyCoefficient k*boundary q*q^2*Real.exp (-17*q) := by
 have hq0 : 0<q := by linarith only [hq]
 have hi := radialError_integrable k hq
 have hb := weighted_power_integrable (by norm_num : (0:ℝ)<19) 2 hq0
 have hC : 0≤80000*cauchyCoefficient k := by unfold cauchyCoefficient; positivity
 have hE : 0≤rateBoundary 19 q := by unfold rateBoundary; positivity
 calc
  _ ≤ ∫ t in Ioi q, |radialError k t| := abs_integral_le_integral_abs
  _ ≤ ∫ t in Ioi q, 80000*cauchyCoefficient k*(rateBoundary 19 t*t^2) := by
   apply integral_mono_ae hi.abs (hb.const_mul _)
   filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
   exact radialError_bound k (hq.trans ht.le)
  _ = 80000*cauchyCoefficient k*(rateBoundary 19 q*gRate 19 2 q (rateGammaMass 19 q)) := by
   rw [integral_const_mul,integral_rateBoundary_mul_pow (by norm_num : (0:ℝ)<19) 2 hq0]
  _ ≤ 80000*cauchyCoefficient k*(rateBoundary 19 q*(q^2/17)) :=
   mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rate_nineteen_second_le hq) hE) hC
  _ = _ := by
   rw [rateBoundary_relative]
   norm_num
   ring

/-- The remainder in fixed coordinates with weight `1000^i` on row `i`. -/
def scaledErrorMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 errorMatrix q i j/(1000:ℝ)^(i.val+j.val)

/-- Every integrated remainder entry fits the same fixed-coordinate envelope. -/
theorem scaledError_entry_bound {q : ℝ} (hq : 3≤q) (i j : Fin 5) :
 |scaledErrorMatrix q i j|≤(80000000/17)*boundary q*q^2*Real.exp (-17*q) := by
 have hq0 : 0<q := by linarith only [hq]
 have hD : 0<(1000:ℝ)^(i.val+j.val) := by positivity
 have hC := cauchy_coeff_bound (i.val+j.val) (by omega)
 change cauchyCoefficient (i.val+j.val)≤1000*(1000:ℝ)^(i.val+j.val) at hC
 rw [scaledErrorMatrix,abs_div,abs_of_pos hD]
 apply (div_le_iff₀ hD).mpr
 calc
  _ ≤ (80000/17)*cauchyCoefficient (i.val+j.val)*boundary q*q^2*Real.exp (-17*q) :=
   integral_radialError_bound (i.val+j.val) hq
  _ = cauchyCoefficient (i.val+j.val)*((80000/17)*boundary q*q^2*Real.exp (-17*q)) := by ring
  _ ≤ (1000*(1000:ℝ)^(i.val+j.val))*((80000/17)*boundary q*q^2*Real.exp (-17*q)) :=
   mul_le_mul_of_nonneg_right hC (by unfold boundary; positivity)
  _ = _ := by ring

private theorem fixed_coordinates (q : ℝ) (v : Fin 5 → ℝ) :
 v ⬝ᵥ (errorMatrix q *ᵥ v)=
  (fun i => (1000:ℝ)^i.val*v i) ⬝ᵥ
   (scaledErrorMatrix q *ᵥ (fun i => (1000:ℝ)^i.val*v i)) := by
 simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro i _
 apply Finset.sum_congr rfl
 intro j _
 dsimp only [scaledErrorMatrix]
 rw [pow_add]
 field_simp [show (1000:ℝ)^i.val≠0 by positivity,
  show (1000:ℝ)^j.val≠0 by positivity]

private theorem half_reserve_nonneg {q : ℝ} (hq : 3≤q) :
 0≤boundary q*((1/2)*(3/(32*q^2)-3/(128*q^3))) := by
 have hq0 : 0<q := by linarith only [hq]
 have he : 3/(32*q^2)-3/(128*q^3)=3*(4*q-1)/(128*q^3) := by
  field_simp [hq0.ne']
  ring
 rw [he]
 have hp : 0≤4*q-1 := by linarith only [hq]
 unfold boundary
 positivity

/-- Half the cubic gamma reserve controls the entire omitted integrated quadratic form. -/
theorem errorForm_bound {q : ℝ} (hq : 3≤q) (v : Fin 5 → ℝ) :
 |v ⬝ᵥ (errorMatrix q *ᵥ v)|≤
  boundary q*((1/2)*(3/(32*q^2)-3/(128*q^3)))*(v ⬝ᵥ (model 0 1 *ᵥ v)) := by
 have hq0 : 0<q := by linarith only [hq]
 let w : Fin 5 → ℝ := fun i => (1000:ℝ)^i.val*v i
 have hN : 0≤∑ i, w i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (w i))
 have h := _root_.RHTower.abs_dotProduct_mulVec_le (scaledErrorMatrix q)
  (show 0≤(80000000/17)*boundary q*q^2*Real.exp (-17*q) by unfold boundary; positivity)
  (scaledError_entry_bound hq) w
 norm_num only [Fintype.card_fin,Nat.cast_ofNat] at h
 have hError : |v ⬝ᵥ (errorMatrix q *ᵥ v)|≤
   (boundary q*((400000000/17)*q^2*Real.exp (-17*q)))*(∑ i, w i^2) := by
  rw [fixed_coordinates]
  convert h using 1
  ring
 have hpay := mul_le_mul_of_nonneg_right
  (mul_le_mul_of_nonneg_left (remainder_reserve_scalar hq) (boundary_pos hq0).le) hN
 have hA := mass_form_lower v
 change (1/100000000000:ℝ)*(∑ i, w i^2)≤v ⬝ᵥ (model 0 1 *ᵥ v) at hA
 calc
  _ ≤ (boundary q*((400000000/17)*q^2*Real.exp (-17*q)))*(∑ i, w i^2) := hError
  _ ≤ (boundary q*((1/2)*(3/(32*q^2)-3/(128*q^3))*(1/100000000000)))*
    (∑ i, w i^2) := hpay
  _ = (boundary q*((1/2)*(3/(32*q^2)-3/(128*q^3))))*
    ((1/100000000000)*(∑ i, w i^2)) := by ring
  _ ≤ _ := mul_le_mul_of_nonneg_left hA (half_reserve_nonneg hq)


private theorem qform_smul (c : ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℝ) :
 v ⬝ᵥ ((c • M) *ᵥ v)=c*(v ⬝ᵥ (M *ᵥ v)) := by
 simp only [dotProduct,Matrix.mulVec,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
 exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- Adding half the cubic gamma reserve makes the complete omitted tail nonnegative. -/
theorem errorMatrix_add_reserve_posSemidef {q : ℝ} (hq : 3≤q) :
 (errorMatrix q+(boundary q*((1/2)*(3/(32*q^2)-3/(128*q^3)))) • model 0 1).PosSemidef := by
 have hH : (errorMatrix q+
   (boundary q*((1/2)*(3/(32*q^2)-3/(128*q^3)))) • model 0 1).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,Matrix.add_apply,Matrix.smul_apply,
   smul_eq_mul,errorMatrix,model,Nat.add_comm]
 refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun v => ?_
 simp only [star_trivial,Matrix.add_mulVec,dotProduct_add]
 rw [qform_smul]
 have h := errorForm_bound hq v
 have hn := neg_abs_le (v ⬝ᵥ (errorMatrix q *ᵥ v))
 linarith only [h,hn]

end GaloisForLFunctions.ThetaCuspSections.FifthTailRemainder

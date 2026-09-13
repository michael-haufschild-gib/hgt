import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCirclePeriod
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeAngularCurrent

/-!
# Original circle scalar Green finite part

At fixed nonnegative radius, the actual native circle mean and unchanged
physical scalar reader have an exact three-power normal-flux expansion. Every
term containing a full source or reader remainder has arbitrary weighted cusp
decay. The scalar Green identity retains the complete curved modular core.

For the same-copy physical reader, the normal-flux principal terms are exactly
the original scalar counterterms multiplied by their angular gaps. The original
hyperbolic height-cutoff integral therefore gives zero finite part for the
reader's scalar differential defect, with no free constant or altered cutoff.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ContDiff NNReal ENNReal
open GaloisForLFunctions.HTGeometry ScalarTwoJet
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local instance : MeasureSpace ℂ := inferInstance
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalCircleFlux
open D4BMJointSource D4BMAngularSeries D4BMNativeCuspJets D4BMNativeAngularCurrent
open D4BMOriginalCircleGreen D4BMOriginalCuspFlux
open GaloisForLFunctions.RHTower
private abbrev Point := Fin 2 → ℝ
private abbrev Field := Point → ℂ
private abbrev D := @coordDeriv 2
private theorem positive_nhds {z : Point} (hz : 0 < z 1) : {v : Point | 0 < v 1} ∈ 𝓝 z :=
  (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
private def readerTail (r : XiZeroCopy) : Field := D4BMGlobalAngularResponse.tail (physicalAngularParameter r)
private theorem exp_cpow (a : ℂ) (k : ℝ) : (Real.exp k:ℂ)^a=Complex.exp (a*(k:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
    ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
  congr 1
  ring
private theorem principal_smooth (a w : ℂ) {z : Point} (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (fun v : Point => a*(v 1:ℂ)^w) z :=
  contDiffAt_const.mul ((height_cpow_contDiffOn w ∞).contDiffAt (positive_nhds hz))

private theorem reader_decomposition (r : XiZeroCopy) (z : Point) :
    D4BMLiteralCusp.scalar (physicalAngularParameter r) z=readerPrincipal r z+readerTail r z := by
  have hp := physicalScalar_principal r z
  change D4BMGlobalAngularResponse.principal (physicalAngularParameter r) z=readerPrincipal r z at hp
  rw [← hp]
  rfl

private def atHeight (F : Field) (z : Point) : ℂ := F ![z 0,Real.exp (z 1)]
private def E (a : ℂ) (z : Point) : ℂ := Complex.exp (a*(z 1:ℂ))
private def Rapid (F : Field) : Prop := ∀ w : ℂ, ∀ X : ℝ → ℝ,
  Tendsto (fun k : ℝ => E w ![X k,k]*F ![X k,k]) atTop (𝓝 0)
private theorem E_mul (a b : ℂ) (z : Point) : E a z*E b z=E (a+b) z := by
  rw [E,E,← Complex.exp_add]
  congr 1
  ring
private theorem Rapid.congr {F G : Field} (hF : Rapid F) (he : ∀ z, F z=G z) : Rapid G := by
  intro w X
  exact (hF w X).congr' (Eventually.of_forall (fun k => by rw [he]))
private theorem Rapid.add {F G : Field} (hF : Rapid F) (hG : Rapid G) : Rapid (fun z => F z+G z) := by
  intro w X
  simpa only [mul_add,add_zero] using (hF w X).add (hG w X)
private theorem Rapid.sub {F G : Field} (hF : Rapid F) (hG : Rapid G) : Rapid (fun z => F z-G z) := by
  intro w X
  simpa only [mul_sub,sub_zero] using (hF w X).sub (hG w X)
private theorem Rapid.scale {F : Field} (hF : Rapid F) (a : ℂ) : Rapid (fun z => a*F z) := by
  intro w X
  convert (hF w X).const_mul a using 1
  · funext k; ring
  · simp
private theorem Rapid.mul {F G : Field} (hF : Rapid F) (hG : Rapid G) : Rapid (fun z => F z*G z) := by
  intro w X
  have h := (hF w X).mul (hG 0 X)
  simpa only [E,zero_mul,Complex.exp_zero,one_mul,mul_zero,mul_assoc] using h
private theorem Rapid.exp_mul {F : Field} (hF : Rapid F) (a : ℂ) : Rapid (fun z => E a z*F z) := by
  intro w X
  simpa only [← mul_assoc,E_mul] using hF (w+a) X

private def Moderate (F : Field) : Prop := ∀ G : Field, Rapid G → Rapid (fun z => F z*G z)
private theorem Moderate.exp (a : ℂ) : Moderate (E a) := fun _ h => h.exp_mul a
private theorem Moderate.scale {F : Field} (hF : Moderate F) (a : ℂ) : Moderate (fun z => a*F z) := by
  intro G hG
  exact ((hF G hG).scale a).congr (fun z => by ring)
private theorem Moderate.add {F G : Field} (hF : Moderate F) (hG : Moderate G) :
    Moderate (fun z => F z+G z) := by
  intro H hH
  exact ((hF H hH).add (hG H hH)).congr (fun z => by ring)
private theorem Moderate.congr {F G : Field} (hF : Moderate F) (he : ∀ z, F z=G z) : Moderate G := by
  intro H hH
  exact (hF H hH).congr (fun z => by rw [he])
private theorem Rapid.mul_moderate {F G : Field} (hF : Rapid F) (hG : Moderate G) :
    Rapid (fun z => F z*G z) := (hG F hF).congr (fun _ => mul_comm _ _)
private theorem Moderate.sum_three (F : Fin 3 → Field) (hF : ∀ i, Moderate (F i)) :
    Moderate (fun z => ∑ i : Fin 3, F i z) := by
  simpa only [Fin.sum_univ_three] using ((hF 0).add (hF 1)).add (hF 2)

private theorem rapid_of_weighted_bound (F : Field)
    (hb : ∀ w : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Point, 1 ≤ z 1 → ‖(z 1:ℂ)^w*F z‖ ≤ C) :
    Rapid (atHeight F) := by
  intro w X
  obtain ⟨C,hC,hbound⟩ := hb (w+1)
  apply squeeze_zero_norm' _ (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with k hk
  have hY : 1 ≤ Real.exp k := Real.one_le_exp hk
  have hB := hbound ![X k,Real.exp k] hY
  simp only [Matrix.cons_val,exp_cpow] at hB
  have he : E w ![X k,k]*atHeight F ![X k,k]=
      E (-1) ![X k,k]*(E (w+1) ![X k,k]*atHeight F ![X k,k]) := by
    rw [← mul_assoc,E_mul,show (-1:ℂ)+(w+1)=w by ring]
  rw [he,norm_mul]
  have hn : ‖E (-1) ![X k,k]‖=Real.exp (-k) := by
    simp [E,Complex.norm_exp]
  rw [hn]
  change Real.exp (-k)*‖Complex.exp ((w+1)*(k:ℂ))*F ![X k,Real.exp k]‖ ≤ _
  calc
    _ ≤ Real.exp (-k)*C := mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
    _ = _ := mul_comm _ _

private theorem value_rapid (u nu : ℂ) (a : ℝ) (d : ℕ) (neg : Bool) :
    Rapid (atHeight (value u nu a d neg)) :=
  rapid_of_weighted_bound _ (fun w => weighted_value_bounded u nu w a d neg 1 (by norm_num))
private theorem tail_rapid (r : XiZeroCopy) : Rapid (atHeight (readerTail r)) :=
  rapid_of_weighted_bound _ (fun w => D4BMGlobalAngularResponse.weighted_tail_bounded
    (physicalAngularParameter r) w 1 (by norm_num))
private theorem value_derivative_rapid (u nu : ℂ) (a : ℝ) (d : ℕ) (neg : Bool) :
    Rapid (atHeight (D 1 (value u nu a d neg))) := by
  have h := ((value_rapid u nu (a-1) d neg).scale (a:ℂ)).sub
    (((value_rapid u (nu+1) a (d+1) neg).add (value_rapid u (nu-1) a (d+1) neg)).scale (Real.pi:ℂ))
  apply h.congr
  intro z
  exact (value_coordDeriv_one u nu a d neg ![z 0,Real.exp (z 1)] (Real.exp_pos _)).symm
private theorem tail_derivative_rapid (r : XiZeroCopy) : Rapid (atHeight (D 1 (readerTail r))) := by
  have h := ((value_derivative_rapid (physicalAngularParameter r) (physicalAngularParameter r)
    (1/2) 0 false).add (value_derivative_rapid (physicalAngularParameter r) (physicalAngularParameter r)
      (1/2) 0 true)).scale 2
  apply h.congr
  intro z
  exact (D4BMGlobalAngularResponse.tail_vertical_eq (physicalAngularParameter r)
    ![z 0,Real.exp (z 1)] (Real.exp_pos _)).symm


private theorem gradient_height (a b : ℂ) : gradient a b (Pi.single 1 1)=b := by
  change (0:ℝ) • a+(1:ℝ) • b=b
  simp

private theorem readerPrincipal_derivative (r : XiZeroCopy) {z : Point} (hz : 0 < z 1) :
    D 1 (readerPrincipal r) z=readerCoefficient r*readerExponent r*(z 1:ℂ)^(readerExponent r-1) := by
  have hd := (height_cpow_hasFDerivAt (readerExponent r) z hz).const_mul (readerCoefficient r)
  change fderiv ℝ (fun z : Point => readerCoefficient r*(z 1:ℂ)^(readerExponent r)) z (Pi.single 1 1)=_
  rw [hd.fderiv]
  simp only [smul_apply,smul_eq_mul,gradient_height]
  ring


private theorem reader_derivative (r : XiZeroCopy) {z : Point} (hz : 0 < z 1) :
    D 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z=
      D 1 (readerPrincipal r) z+D 1 (readerTail r) z := by
  have hS := (cuspLeg_contDiffOn .scalar (physicalAngularParameter r)).contDiffAt (positive_nhds hz)
  have hP := principal_smooth (readerCoefficient r) (readerExponent r) hz
  have he : readerTail r=fun z => D4BMLiteralCusp.scalar (physicalAngularParameter r) z-readerPrincipal r z := by
    funext z
    rw [reader_decomposition]
    ring
  have hT : ContDiffAt ℝ ∞ (readerTail r) z := by
    rw [he]
    exact hS.sub hP
  have h := funext (reader_decomposition r)
  change D 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z=_
  rw [h]
  exact coordDeriv_add (hP.differentiableAt (by simp)) (hT.differentiableAt (by simp)) 1


private theorem Rapid.uniform {F : Field} (hF : Rapid F) (w : ℂ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ k : ℝ in atTop, ∀ x : ℝ, ‖E w ![x,k]*F ![x,k]‖ < epsilon := by
  classical
  let X : ℝ → ℝ := fun k => if hx : ∃ x, epsilon ≤ ‖E w ![x,k]*F ![x,k]‖ then hx.choose else 0
  have ht := Metric.tendsto_nhds.mp (hF w X) epsilon hepsilon
  filter_upwards [ht] with k hk x
  rw [dist_zero_right] at hk
  by_contra hx
  have he : ∃ x, epsilon ≤ ‖E w ![x,k]*F ![x,k]‖ := ⟨x,le_of_not_gt hx⟩
  have hb : epsilon ≤ ‖E w ![X k,k]*F ![X k,k]‖ := by
    dsimp only [X]
    rw [dif_pos he]
    exact he.choose_spec
  exact (not_lt_of_ge hb) hk
private theorem Rapid.integral {F : Field} (hF : Rapid F) (w : ℂ) :
    Tendsto (fun k : ℝ => ∫ X in (-1/2:ℝ)..1/2, E w ![X,k]*F ![X,k]) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [hF.uniform w (epsilon/2) (half_pos hepsilon)] with k hk
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1/2:ℝ)) (b := (1/2:ℝ)) (fun X _ => (hk X).le)
  norm_num only [sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one] at hi
  rw [dist_zero_right]
  simpa only [neg_div] using hi.trans_lt (half_lt_self hepsilon)

private theorem source_smooth (q : XiZeroCopy) (d : ℝ)
    (z : Point) (hz : 0 < z 1) : ContDiffAt ℝ ∞ (circleField q d) z := by
  have hc : ContDiffAt ℝ ∞ (fun w : Point => (d,w 0,Real.log (w 1))) z :=
    contDiffAt_const.prodMk ((contDiff_apply ℝ ℝ (0:Fin 2)).contDiffAt.prodMk
      ((contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt.log hz.ne'))
  have hm : ContDiff ℝ ∞ (fun v : ℝ × ℝ × ℝ => D4BMNativeCircle.mean q v.1 v.2.1 v.2.2) :=
    D4BMNativeResponse.nativeMean_joint_smooth q
  have h := hm.contDiffAt.comp z hc
  change ContDiffAt ℝ ∞ ((fun v : ℝ × ℝ × ℝ =>
    D4BMNativeCircle.mean q v.1 v.2.1 v.2.2) ∘
      (fun w : Point => (d,w 0,Real.log (w 1)))) z at h
  exact h


private theorem native_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (nativeField q) := by
  have hm : ContDiff ℝ ∞ (fun v : ℝ × ℝ × ℝ => D4BMNativeCircle.mean q v.1 v.2.1 v.2.2) :=
    D4BMNativeResponse.nativeMean_joint_smooth q
  have h := hm.comp (show ContDiff ℝ ∞ (fun p : Fin 3 → ℝ => (p 0,p 1,p 2)) by fun_prop)
  simpa only [nativeField,Function.comp_def] using! h

private theorem circle_vertical (q : XiZeroCopy) (d : ℝ) {z : Point} (hz : 0 < z 1) :
    D 1 (circleField q d) z = (z 1:ℂ)⁻¹ * nativeJet [2] (nativeField q) ![d,z 0,Real.log (z 1)] := by
  let dc : Point →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi
    ![0,ContinuousLinearMap.proj 0,(z 1)⁻¹ • ContinuousLinearMap.proj 1]
  have hc : HasFDerivAt (fun v : Point => (![d,v 0,Real.log (v 1)] : Fin 3 → ℝ)) dc z := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasFDerivAt_const _ _
    · exact hasFDerivAt_apply (𝕜 := ℝ) 0 z
    · exact (hasFDerivAt_apply (𝕜 := ℝ) 1 z).log hz.ne'
  have hf := (native_smooth q).differentiable (by simp)
  have h := (hf ![d,z 0,Real.log (z 1)]).hasFDerivAt.comp z hc
  change HasFDerivAt (circleField q d) _ z at h
  change fderiv ℝ (circleField q d) z (Pi.single 1 1) = _
  rw [h.fderiv]
  change fderiv ℝ (nativeField q) ![d,z 0,Real.log (z 1)] (dc (Pi.single 1 1)) = _
  have he : dc (Pi.single 1 1)=(z 1)⁻¹ • Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [dc]
  rw [he,map_smul]
  simp [nativeJet,coordDeriv,Complex.real_smul]

private def P (q : XiZeroCopy) (d : ℝ) (n : ℕ) (z : Point) : ℂ :=
  ∑ i : Fin 3, D4BMOriginalCirclePeriod.coefficient q d i *
    (principalExponent q i)^n * E (principalExponent q i) z
private def R (q : XiZeroCopy) (d : ℝ) (word : List (Fin 3)) (z : Point) : ℂ :=
  nativeJet word (nativeRemainder q) ![d,z 0,z 1]

private theorem source_atHeight (q : XiZeroCopy) (d : ℝ) (z : Point) :
    atHeight (circleField q d) z=P q d 0 z+R q d [] z := by
  simp only [atHeight,circleField,Matrix.cons_val,Real.log_exp,P,pow_zero,mul_one,R,
    nativeJet,nativeRemainder,D4BMNativeCircle.cuspMeanRemainder,
    D4BMNativeCircle.transportedPrincipal,D4BMOriginalCirclePeriod.coefficient,
    exp_cpow,E]
  have h : (∑ i : Fin 3, principalAmplitude q i * Complex.exp (principalExponent q i * (z 1:ℂ)) *
      D4BMNativeCircle.powerCircle (principalExponent q i) d) =
      ∑ i : Fin 3, principalAmplitude q i * D4BMNativeCircle.powerCircle (principalExponent q i) d *
        Complex.exp (principalExponent q i * (z 1:ℂ)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  ring

private theorem source_vertical_atHeight (q : XiZeroCopy) (d : ℝ) (z : Point) :
    atHeight (D 1 (circleField q d)) z=E (-1) z*P q d 1 z+E (-1) z*R q d [2] z := by
  have h := (native_angular_jet_decomposition q ![d,z 0,z 1]).1
  have hp : D4BMNativeAngularCurrent.principalJet q 1 ![d,z 0,z 1]=P q d 1 z := by
    unfold D4BMNativeAngularCurrent.principalJet P D4BMOriginalCirclePeriod.coefficient
    apply Finset.sum_congr rfl
    intro i _
    change principalAmplitude q i*(principalExponent q i)^1*
      D4BMNativeCircle.powerCircle (principalExponent q i) d*
      Complex.exp (principalExponent q i*(z 1:ℂ)) =
      (principalAmplitude q i*D4BMNativeCircle.powerCircle (principalExponent q i) d)*
      (principalExponent q i)^1*E (principalExponent q i) z
    unfold E
    ring
  change D 1 (circleField q d) ![z 0,Real.exp (z 1)]=_
  rw [circle_vertical q d (Real.exp_pos _)]
  simp only [Matrix.cons_val,Real.log_exp,h,hp,mul_add]
  congr 1 <;> congr 1 <;> simp [E,Complex.ofReal_exp,Complex.exp_neg]

private theorem P_moderate (q : XiZeroCopy) (d : ℝ) (n : ℕ) : Moderate (P q d n) :=
  Moderate.sum_three _ (fun _ => (Moderate.exp _).scale _)
private theorem R_rapid (q : XiZeroCopy) (d : Ici (0:ℝ)) (word : List (Fin 3)) : Rapid (R q d word) :=
  fun w X => weighted_native_remainder_tendsto_zero q word d X w

private theorem principal_reader_atHeight (r : XiZeroCopy) (z : Point) :
    atHeight (readerPrincipal r) z=readerCoefficient r*E (readerExponent r) z := by
  simp only [atHeight,readerPrincipal,Matrix.cons_val,exp_cpow,E]
private theorem principal_reader_vertical_atHeight (r : XiZeroCopy) (z : Point) :
    atHeight (D 1 (readerPrincipal r)) z=readerCoefficient r*readerExponent r*E (readerExponent r-1) z := by
  change D 1 (readerPrincipal r) ![z 0,Real.exp (z 1)]=_
  rw [readerPrincipal_derivative r (Real.exp_pos _)]
  simp only [Matrix.cons_val,exp_cpow,E]

/-- Coefficients of the exact scalar normal flux of the original circle mean. -/
def scalarFluxCoefficient (q r : XiZeroCopy) (d : ℝ) (i : Fin 3) : ℂ :=
  readerCoefficient r * D4BMOriginalCirclePeriod.coefficient q d i *
    (principalExponent q i-readerExponent r)

private def principalNormal (q r : XiZeroCopy) (d : ℝ) (z : Point) : ℂ :=
  (readerCoefficient r*E (readerExponent r) z)*(E (-1) z*P q d 1 z) -
    P q d 0 z*(readerCoefficient r*readerExponent r*E (readerExponent r-1) z)

private theorem principal_normal_expansion (q r : XiZeroCopy) (d : ℝ) (z : Point) :
    principalNormal q r d z=∑ i : Fin 3,
      scalarFluxCoefficient q r d i * E (fluxExponent q r i) z := by
  unfold principalNormal P
  simp only [pow_one,pow_zero,mul_one,Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = readerCoefficient r*D4BMOriginalCirclePeriod.coefficient q d i*
      (principalExponent q i*(E (readerExponent r) z*E (-1) z*E (principalExponent q i) z)-
        readerExponent r*(E (principalExponent q i) z*E (readerExponent r-1) z)) := by ring
    _ = _ := by
      rw [E_mul,E_mul,E_mul]
      have h1 : readerExponent r+-1+principalExponent q i=fluxExponent q r i := by unfold fluxExponent; ring
      have h2 : principalExponent q i+(readerExponent r-1)=fluxExponent q r i := by unfold fluxExponent; ring
      rw [h1,h2]
      unfold scalarFluxCoefficient
      ring

private def normalRemainder (q r : XiZeroCopy) (d : ℝ) (z : Point) : ℂ :=
  atHeight (flux (circleField q d) (physicalAngularParameter r) 1) z-principalNormal q r d z

private theorem normalRemainder_rapid (q r : XiZeroCopy) (d : Ici (0:ℝ)) :
    Rapid (normalRemainder q r d) := by
  have hp : Moderate (fun z => E (-1) z*P q d 1 z) := by
    intro F hF
    exact ((P_moderate q d 1 F hF).exp_mul (-1)).congr (fun z => by ring)
  have hS : Moderate (atHeight (readerPrincipal r)) :=
    ((Moderate.exp (readerExponent r)).scale (readerCoefficient r)).congr
      (fun z => (principal_reader_atHeight r z).symm)
  have hD : Moderate (atHeight (D 1 (readerPrincipal r))) :=
    ((Moderate.exp (readerExponent r-1)).scale (readerCoefficient r*readerExponent r)).congr
      (fun z => (principal_reader_vertical_atHeight r z).symm)
  have hR := (R_rapid q d [2]).exp_mul (-1)
  have h := ((hS _ hR).add ((tail_rapid r).mul_moderate hp)).add ((tail_rapid r).mul hR)
  have h' := ((P_moderate q d 0 _ (tail_derivative_rapid r)).add
    ((R_rapid q d []).mul_moderate hD)).add ((R_rapid q d []).mul (tail_derivative_rapid r))
  apply (h.sub h').congr
  intro z
  unfold normalRemainder
  have hs := source_atHeight q d z
  have hd := source_vertical_atHeight q d z
  have hsd := reader_derivative r (z := ![z 0,Real.exp (z 1)]) (Real.exp_pos _)
  have hsr := reader_decomposition r ![z 0,Real.exp (z 1)]
  change _ = (atHeight (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z *
    atHeight (D 1 (circleField q d)) z-atHeight (circleField q d) z *
      atHeight (D 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r))) z)-_
  change atHeight (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z=
    atHeight (readerPrincipal r) z+atHeight (readerTail r) z at hsr
  change atHeight (D 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r))) z=
    atHeight (D 1 (readerPrincipal r)) z+atHeight (D 1 (readerTail r)) z at hsd
  rw [hs,hd,hsr,hsd,principal_reader_atHeight,principal_reader_vertical_atHeight,principalNormal]
  ring

private theorem flux_integrable (q r : XiZeroCopy) (d Y : ℝ) (hY : 0 < Y) :
    IntervalIntegrable (fun X : ℝ => flux (circleField q d) (physicalAngularParameter r) 1 ![X,Y])
      volume (-1/2:ℝ) (1/2:ℝ) := by
  have hm : Continuous (fun X : ℝ => (![X,Y] : Point)) := by fun_prop
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro X
  have hz : 0 < (![X,Y] : Point) 1 := hY
  have hS := (cuspLeg_contDiffOn .scalar (physicalAngularParameter r)).contDiffAt (positive_nhds hz)
  have hM := source_smooth q d ![X,Y] hz
  have hD : ContDiffAt ℝ ∞ (D 1 (circleField q d)) ![X,Y] :=
    coordDeriv_contDiffAt hM (by simp) (1:Fin 2)
  have hT : ContDiffAt ℝ ∞ (D 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r))) ![X,Y] :=
    coordDeriv_contDiffAt hS (by simp) (1:Fin 2)
  exact ((hS.mul hD).sub (hM.mul hT)).continuousAt.comp
    (f := fun t : ℝ => (![t,Y] : Point)) (x := X) hm.continuousAt

/-- The unchanged scalar normal flux has its complete three-power expansion;
its remainder decays with every complex height weight. -/
theorem original_normalFlux_expansion (q r : XiZeroCopy) (d : Ici (0:ℝ)) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ)) *
      (normalFlux q r d (Real.exp k)-∑ i : Fin 3,
        scalarFluxCoefficient q r d i*Complex.exp (fluxExponent q r i*(k:ℂ))))
      atTop (𝓝 0) := by
  have h := (normalRemainder_rapid q r d).integral w
  convert h using 1
  funext k
  simp only [E,normalRemainder,atHeight,Matrix.cons_val,principal_normal_expansion]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (flux_integrable q r d (Real.exp k) (Real.exp_pos k)) intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [normalFlux,neg_div,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,one_smul]

/-- The original counterterm under the reader's differential operator is exactly
the normal-flux principal term; its denominator cancels by the actual indicial factorization. -/
theorem counterterm_gap_eq_normal (q : XiZeroCopy) (d k : ℝ) :
    D4BMOriginalScalarRestoration.principalCounterterm q
      (fun i => physicalAngularGap q q i*D4BMOriginalCirclePeriod.coefficient q d i) (Real.exp k) =
      ∑ i : Fin 3, scalarFluxCoefficient q q d i*Complex.exp (fluxExponent q q i*(k:ℂ)) := by
  unfold D4BMOriginalScalarRestoration.principalCounterterm
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [physicalAngularGap_self_indicial,exp_cpow]
  have he : principalExponent q i-(q.1:ℂ)/2=fluxExponent q q i := by
    unfold fluxExponent readerExponent
    ring
  have hn := physicalPrincipal_mellinExponent_ne_zero q i
  rw [← he]
  unfold scalarFluxCoefficient readerCoefficient readerExponent
  apply (div_eq_iff hn).mpr
  ring

/-- The complete curved-domain scalar Green defect has zero finite part with
the unchanged three original counterterms and every complex height weight. -/
theorem original_scalar_green_finitePart (q : XiZeroCopy) (d : Ici (0:ℝ)) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ)) *
      ((∫ z in SelbergModularDomainSlices.domain (Real.exp k),
        defect (circleField q d) (physicalAngularParameter q) ![z.1,z.2])-
        D4BMOriginalScalarRestoration.principalCounterterm q
          (fun i => physicalAngularGap q q i*D4BMOriginalCirclePeriod.coefficient q d i) (Real.exp k)))
      atTop (𝓝 0) := by
  apply (original_normalFlux_expansion q q d w).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with k hk
  rw [original_modular_area q q d (Real.one_le_exp hk),counterterm_gap_eq_normal]

end RHTower.D4BMOriginalCircleFlux

namespace RHTower.D4BMOriginalCircleFlux
open GaloisForLFunctions.RHTower
open D4BMModularCore D4BMOriginalScalarRestoration SelbergMaassTraceStokes

private theorem domain_preimage (Y : ℝ) :
    Complex.measurableEquivRealProd ⁻¹' SelbergModularDomainSlices.domain Y =
      {z : ℂ | z.im ≤ Y} ∩ cellChart := by
  ext z
  change ((z.re ∈ Icc (-(1/2:ℝ)) (1/2) ∧ z.im ∈ Icc (1/2:ℝ) Y) ∧ arcHeight z.re ≤ z.im) ↔ _
  constructor
  · rintro ⟨⟨hx,hy⟩,ha⟩
    have hz : 0 < z.im := lt_of_lt_of_le (by norm_num) hy.1
    refine ⟨hy.2,⟨z,hz⟩,⟨?_,abs_le.mpr hx⟩,rfl⟩
    have hs := arcHeight_sq hx
    have hp := arcHeight_pos hx
    change 1 ≤ Complex.normSq z
    rw [Complex.normSq_apply]
    nlinarith
  · rintro ⟨hY,⟨u,hu,rfl⟩⟩
    have hx : u.re ∈ Icc (-(1/2:ℝ)) (1/2) := abs_le.mp hu.2
    have hs := arcHeight_sq hx
    have hp := arcHeight_pos hx
    have hn : 1 ≤ u.re^2+u.im^2 := by simpa only [Complex.normSq_apply,pow_two,coe_re,coe_im] using hu.1
    have ha : arcHeight u.re ≤ u.im := by nlinarith [u.im_pos]
    exact ⟨⟨hx,⟨(SelbergModularDomainSlices.arcHeight_half_le hx).trans ha,hY⟩⟩,ha⟩

/-- The actual hyperbolic height cutoff is the complete curved planar domain
with its original inverse-square density. -/
theorem original_truncatedIntegral_area (F : (Fin 2 → ℝ) → ℂ) (Y : ℝ) :
    truncatedIntegral (fun z => F ![z.re,z.im]) Y =
      ∫ w in SelbergModularDomainSlices.domain Y, F ![w.1,w.2]/(w.2:ℂ)^2 := by
  let G : ℂ → ℂ := fun z => F ![z.re,z.im]
  let H : Set ℂ := {z | z.im ≤ Y}
  have hH : MeasurableSet H := measurableSet_le Complex.continuous_im.measurable measurable_const
  have hden : Measurable chartDensity := by unfold chartDensity; fun_prop
  have hm := UpperHalfPlane.measurableEmbedding_coe.setIntegral_map (μ := measure) G H
  rw [map_measure_eq,restrict_withDensity hH,Measure.restrict_restrict hH,
    integral_withDensity_eq_integral_smul hden] at hm
  have harea := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun w : ℝ × ℝ => F ![w.1,w.2]/(w.2:ℂ)^2) (SelbergModularDomainSlices.domain Y)
  rw [domain_preimage] at harea
  calc
    _ = ∫ z in H ∩ cellChart, chartDensity z • G z := by
      simpa only [G,H,Set.preimage_setOf_eq,coe_re,coe_im,truncatedIntegral] using hm.symm
    _ = ∫ z in H ∩ cellChart, F ![z.re,z.im]/(z.im:ℂ)^2 := by
      apply setIntegral_congr_fun
        (hH.inter (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr isClosed_fd.measurableSet))
      rintro z ⟨_,u,hu,rfl⟩
      have hy : (u.im:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr u.im_pos.ne'
      simp only [G,chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
        coe_nnnorm,Real.norm_eq_abs,abs_of_pos u.im_pos,Complex.real_smul,
        Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,coe_im]
      field_simp [hy]
    _ = _ := harea

open D4BMJointSource D4BMOriginalCircleGreen

/-- The actual native circle mean's defect against the unchanged reader eigenvalue. -/
def scalarEquationDefect (q : XiZeroCopy) (d : ℝ) (z : Fin 2 → ℝ) : ℂ :=
  D4BMHorizon.scalarLaplacian (circleField q d) z-
    (physicalAngularParameter q^2-1/4)*circleField q d z

/-- The Green defect vanishes in the original hyperbolic finite part, with
exactly the counterterm obtained from the original principal coefficients. -/
theorem original_angular_measure_green_finitePart (q : XiZeroCopy) (d : Ici (0:ℝ)) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ)) *
      (truncatedIntegral (fun z : UpperHalfPlane =>
        D4BMLiteralCusp.scalar (physicalAngularParameter q) ![z.re,z.im] *
          scalarEquationDefect q d ![z.re,z.im]) (Real.exp k)-
        principalCounterterm q
          (fun i => physicalAngularGap q q i*D4BMOriginalCirclePeriod.coefficient q d i) (Real.exp k)))
      atTop (𝓝 0) := by
  have he (k : ℝ) :
      truncatedIntegral (fun z : UpperHalfPlane =>
        D4BMLiteralCusp.scalar (physicalAngularParameter q) ![z.re,z.im] *
          scalarEquationDefect q d ![z.re,z.im]) (Real.exp k) =
      ∫ z in SelbergModularDomainSlices.domain (Real.exp k),
        defect (circleField q d) (physicalAngularParameter q) ![z.1,z.2] := by
    rw [original_truncatedIntegral_area
      (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) z*scalarEquationDefect q d z)]
    apply setIntegral_congr_fun (SelbergModularDomainSlices.isCompact_domain _).measurableSet
    intro z _
    simp only [scalarEquationDefect,defect,Matrix.cons_val]
    congr 1
    ring
  apply (original_scalar_green_finitePart q d w).congr'
  filter_upwards with k
  rw [he]

end RHTower.D4BMOriginalCircleFlux

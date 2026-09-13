import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalAngularGreen
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCuspJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularVerticalBounds

/-!
The complete original causal angular-action and physical-pairing cusp fluxes.

The source's logarithmic jet bounds are transferred through the actual height
coordinate derivatives. The full signed reader tail and its genuine derivative
retain arbitrary weighted decay. Differentiating the original three principal
fields gives every coefficient; the six remaining source-reader terms give a
uniform, integrated remainder bound.

The resulting expansion is attached to OriginalAngularGreen.cuspFlux. Grouping
actual specialized exponents identifies the exact constant term, including both
possible independent-reader resonances. That term vanishes on the diagonal and
on the original functional-equation reflected pair. Subtracting only the derived
nonconstant powers gives an exact infinite-cusp angular-action limit with its
lower boundary preserved.

The one-derivative normal flux also has an exact three-term remainder and
source-derived principal coefficients. Its integrated finite part retains the
independent-reader constant and vanishes for the original diagonal and reflected
readers. This supplies the cusp correction for physical scalar projection.

Null coordinates remain fixed nonnegative parameters. No temporal/horizon limit
interchange, complete spacetime pairing, or RH conclusion is asserted.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry ScalarTwoJet
namespace RHTower.D4BMOriginalCuspFlux
open D4BMJointSource D4BMAngularSeries D4BMOriginalCuspJets
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev Point := Fin 2 → ℝ
private abbrev Field := Point → ℂ
private abbrev D := @coordDeriv 2
private abbrev L := hyperbolicLaplacian
private theorem point_eta (z : Point) : (![z 0,z 1] : Point)=z := by
  ext i
  fin_cases i <;> rfl

private def chart (z : Point) : Point := ![z 0,Real.log (z 1)]
private def pull (F : Field) : Field := fun z => F (chart z)
private theorem positive_nhds {z : Point} (hz : 0 < z 1) : {v : Point | 0 < v 1} ∈ 𝓝 z :=
  (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
private theorem chart_smooth {z : Point} (hz : 0 < z 1) : ContDiffAt ℝ ∞ chart z := by
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact (contDiff_apply ℝ ℝ (0:Fin 2)).contDiffAt
  · exact (contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt.log hz.ne'
private theorem pull_smooth {F : Field} (hF : ContDiff ℝ ∞ F) {z : Point} (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (pull F) z := hF.contDiffAt.comp z (chart_smooth hz)
private theorem D_smooth {F : Field} (hF : ContDiff ℝ ∞ F) (i : Fin 2) :
    ContDiff ℝ ∞ (D i F) := (hF.fderiv_right (by simp)).clm_apply contDiff_const

private theorem chart_first {F : Field} (hF : ContDiff ℝ ∞ F) {z : Point} (hz : 0 < z 1)
    (i : Fin 2) : D i (pull F) z=(if i=0 then 1 else (z 1:ℂ)⁻¹)*D i F (chart z) := by
  let dc : Point →L[ℝ] Point := ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj 0,(z 1)⁻¹ • ContinuousLinearMap.proj 1]
  have hchart : HasFDerivAt chart dc z := by
    apply hasFDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact hasFDerivAt_apply (𝕜 := ℝ) 0 z
    · exact (hasFDerivAt_apply (𝕜 := ℝ) 1 z).log hz.ne'
  have hc := ((hF.differentiable (by simp) (chart z)).hasFDerivAt).comp z hchart
  change HasFDerivAt (pull F) _ z at hc
  change fderiv ℝ (pull F) z (Pi.single i 1)=_
  rw [hc.fderiv]
  change (fderiv ℝ F (chart z)) (dc (Pi.single i 1))=_
  have he : dc (Pi.single i 1)=(if i=0 then 1 else (z 1)⁻¹) • Pi.single i 1 := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [dc]
  rw [he,map_smul]
  fin_cases i <;> simp [D,coordDeriv,Complex.real_smul]

private theorem chart_second_zero {F : Field} (hF : ContDiff ℝ ∞ F)
    {z : Point} (hz : 0 < z 1) : D 0 (D 0 (pull F)) z=D 0 (D 0 F) (chart z) := by
  have he : D 0 (pull F)=ᶠ[𝓝 z] pull (D 0 F) := by
    filter_upwards [positive_nhds hz] with v hv
    simpa only [ite_true,one_mul,pull] using chart_first hF hv 0
  change fderiv ℝ (D 0 (pull F)) z (Pi.single 0 1)=_
  rw [he.fderiv_eq]
  exact (chart_first (D_smooth hF 0) hz 0).trans (by simp)

private theorem chart_second_one {F : Field} (hF : ContDiff ℝ ∞ F)
    {z : Point} (hz : 0 < z 1) :
    (z 1:ℂ)^2*D 1 (D 1 (pull F)) z=D 1 (D 1 F) (chart z)-D 1 F (chart z) := by
  have he : D 1 (pull F)=ᶠ[𝓝 z] fun v => (v 1:ℂ)⁻¹*pull (D 1 F) v := by
    filter_upwards [positive_nhds hz] with v hv
    simpa only [show ¬(1:Fin 2)=0 by decide,if_false,pull] using chart_first hF hv 1
  have hn : (z 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hi : HasFDerivAt (fun v : Point => (v 1:ℂ)⁻¹)
      ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).smulRight (-(z 1:ℂ)⁻¹^2)) z := by
    have hy := Complex.ofRealCLM.hasFDerivAt.comp z
      ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt)
    have h := (hasDerivAt_inv hn).comp_hasFDerivAt z hy
    convert! h using 1
    ext v
    simp [Complex.real_smul,smul_eq_mul]
    ring
  have hd : D 1 (fun v : Point => (v 1:ℂ)⁻¹) z= -(z 1:ℂ)⁻¹^2 := by
    change fderiv ℝ _ z (Pi.single 1 1)=_
    rw [hi.fderiv]
    simp
  have hD := (pull_smooth (D_smooth hF 1) hz).differentiableAt (by simp)
  change (z 1:ℂ)^2*fderiv ℝ (D 1 (pull F)) z (Pi.single 1 1)=_
  rw [he.fderiv_eq]
  change (z 1:ℂ)^2*D 1 (fun v : Point => (v 1:ℂ)⁻¹*pull (D 1 F) v) z=_
  have hp : D 1 (fun v : Point => (v 1:ℂ)⁻¹*pull (D 1 F) v) z=
      D 1 (fun v : Point => (v 1:ℂ)⁻¹) z*pull (D 1 F) z+(z 1:ℂ)⁻¹*D 1 (pull (D 1 F)) z :=
    coordDeriv_mul hi.differentiableAt hD 1
  rw [hp,hd,chart_first (D_smooth hF 1) hz 1]
  simp only [show ¬(1:Fin 2)=0 by decide,if_false,pull]
  field_simp [hn]
  ring

/-- Genuine height-coordinate Laplacian of every smooth logarithmic source field. -/
private theorem pull_laplacian {F : Field} (hF : ContDiff ℝ ∞ F) {z : Point} (hz : 0 < z 1) :
    L (pull F) z=(z 1:ℂ)^2*D 0 (D 0 F) (chart z)+D 1 (D 1 F) (chart z)-D 1 F (chart z) := by
  change (z 1:ℂ)^2*(D 0 (D 0 (pull F)) z+D 1 (D 1 (pull F)) z)=_
  rw [mul_add,chart_second_zero hF hz,chart_second_one hF hz]
  ring

private theorem exp_cpow (a : ℂ) (k : ℝ) : (Real.exp k:ℂ)^a=Complex.exp (a*(k:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
    ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
  congr 1
  ring
private theorem remainder_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) :
    ContDiff ℝ ∞ (remainder q branch amp p v) := by
  have hf := (D4BMOriginalCausalPotential.originalPotential_angular_smooth q branch amp p v).comp
    (show ContDiff ℝ ∞ (fun z : Point => (z 0,z 1)) by fun_prop)
  have hp : ContDiff ℝ ∞ (D4BMOriginalCuspJets.principal q branch amp p v) := by
    unfold D4BMOriginalCuspJets.principal
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_apply ℝ ℝ (1:Fin 2)))).cexp)
  exact hf.sub hp

def sourceRemainder (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) : Field :=
  pull (remainder q branch amp p v)
def sourcePrincipal (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) (z : Point) : ℂ :=
  ∑ i : Fin 3, coefficient q branch amp p v i*(z 1:ℂ)^(principalExponent q i)
def readerExponent (r : XiZeroCopy) : ℂ := 1-(r.1:ℂ)/2
def readerCoefficient (r : XiZeroCopy) : ℂ := reflectedCompletedLambda ((r.1:ℂ)-1)
def readerPrincipal (r : XiZeroCopy) (z : Point) : ℂ :=
  readerCoefficient r*(z 1:ℂ)^(readerExponent r)
private def readerTail (r : XiZeroCopy) : Field := D4BMGlobalAngularResponse.tail (physicalAngularParameter r)

theorem source_decomposition (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (z : Point) (hz : 0 < z 1) :
    D4BMOriginalAngularGreen.source q branch amp p v z=
      sourcePrincipal q branch amp p v z+sourceRemainder q branch amp p v z := by
  have he (a : ℂ) : Complex.exp (a*(Real.log (z 1):ℂ))=(z 1:ℂ)^a := by
    rw [← exp_cpow,Real.exp_log hz]
  simp only [sourceRemainder,pull,remainder,chart,D4BMOriginalCuspJets.principal,
    Matrix.cons_val,he,sourcePrincipal,D4BMOriginalAngularGreen.source]
  ring
private theorem principal_smooth (a w : ℂ) {z : Point} (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (fun v : Point => a*(v 1:ℂ)^w) z :=
  contDiffAt_const.mul ((height_cpow_contDiffOn w ∞).contDiffAt (positive_nhds hz))
private theorem sourcePrincipal_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    {z : Point} (hz : 0 < z 1) : ContDiffAt ℝ ∞ (sourcePrincipal q branch amp p v) z := by
  apply ContDiffAt.sum
  intro i _
  exact principal_smooth _ _ hz
private theorem reader_decomposition (r : XiZeroCopy) (z : Point) :
    D4BMLiteralCusp.scalar (physicalAngularParameter r) z=readerPrincipal r z+readerTail r z := by
  have hp := physicalScalar_principal r z
  change D4BMGlobalAngularResponse.principal (physicalAngularParameter r) z=readerPrincipal r z at hp
  rw [← hp]
  rfl
private theorem reader_mu (r : XiZeroCopy) :
    physicalAngularParameter r^2-1/4=readerExponent r*(readerExponent r-1) := by
  rw [physicalAngularParameter_eq]
  unfold readerExponent
  ring

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

private theorem source_jet_rapid (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) (word : List (Fin 2)) :
    Rapid (D4BMSquareCuspJets.coordinateJet word (remainder q branch amp p v)) :=
  fun w X => original_remainder_jet_tendsto_zero q branch amp p v word X w
private theorem source_remainder_rapid (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) : Rapid (atHeight (sourceRemainder q branch amp p v)) := by
  apply (source_jet_rapid q branch amp p v []).congr
  intro z
  simp [atHeight,sourceRemainder,pull,chart,D4BMSquareCuspJets.coordinateJet,point_eta]
private theorem source_derivative_rapid (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) : Rapid (atHeight (D 1 (sourceRemainder q branch amp p v))) := by
  apply ((source_jet_rapid q branch amp p v [1]).exp_mul (-1)).congr
  intro z
  have h := chart_first (remainder_smooth q branch amp p v) (z := ![z 0,Real.exp (z 1)])
    (Real.exp_pos _) 1
  simpa only [atHeight,sourceRemainder,chart,Matrix.cons_val,Real.log_exp,E,neg_one_mul,
    Complex.exp_neg,← Complex.ofReal_exp,show ¬(1:Fin 2)=0 by decide,if_false,
    D4BMSquareCuspJets.coordinateJet,point_eta] using h.symm
private theorem source_laplacian_rapid (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) : Rapid (atHeight (L (sourceRemainder q branch amp p v))) := by
  have h := (((source_jet_rapid q branch amp p v [0,0]).exp_mul 2).add
    (source_jet_rapid q branch amp p v [1,1])).sub (source_jet_rapid q branch amp p v [1])
  apply h.congr
  intro z
  have hl := pull_laplacian (remainder_smooth q branch amp p v) (z := ![z 0,Real.exp (z 1)])
    (Real.exp_pos _)
  have he : Complex.exp ((2:ℂ)*(z 1:ℂ))=(Real.exp (z 1):ℂ)^2 := by
    rw [← exp_cpow,Complex.cpow_two]
  simpa only [atHeight,sourceRemainder,chart,Matrix.cons_val,Real.log_exp,E,he,
    D4BMSquareCuspJets.coordinateJet,point_eta] using hl.symm

private theorem c2 {F : Field} {z : Point} (h : ContDiffAt ℝ ∞ F z) : ContDiffAt ℝ 2 F z :=
  h.of_le (WithTop.coe_le_coe.mpr le_top)
private theorem gradient_height (a b : ℂ) : gradient a b (Pi.single 1 1)=b := by
  change (0:ℝ) • a+(1:ℝ) • b=b
  simp
private theorem sourcePrincipal_derivative (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : ℝ) {z : Point} (hz : 0 < z 1) :
    D 1 (sourcePrincipal q branch amp p v) z=∑ i : Fin 3,
      coefficient q branch amp p v i*principalExponent q i*(z 1:ℂ)^(principalExponent q i-1) := by
  have hd := HasFDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    (height_cpow_hasFDerivAt (principalExponent q i) z hz).const_mul (coefficient q branch amp p v i))
  change fderiv ℝ (fun z : Point => ∑ i : Fin 3,
    coefficient q branch amp p v i*(z 1:ℂ)^(principalExponent q i)) z (Pi.single 1 1)=_
  rw [hd.fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul,gradient_height]
  apply Finset.sum_congr rfl
  intro i _
  ring
private theorem power_laplacian_sum {ι : Type*} (s : Finset ι) (F : ι → Field)
    {z : Point} (hF : ∀ i ∈ s, ContDiffAt ℝ 2 (F i) z) :
    L (fun x => ∑ i ∈ s, F i x) z=∑ i ∈ s, L (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (z 1:ℂ)^2*(fderiv ℝ (fun x => fderiv ℝ (fun _ : Point => (0:ℂ)) x (Pi.single 0 1)) z (Pi.single 0 1)+
      fderiv ℝ (fun x => fderiv ℝ (fun _ : Point => (0:ℂ)) x (Pi.single 1 1)) z (Pi.single 1 1))=0
    simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hyperbolicLaplacian_add (hF i (Finset.mem_insert_self _ _))
      (ContDiffAt.sum (fun j hj => hF j (Finset.mem_insert_of_mem hj)))).trans
        (congrArg (fun a => L (F i) z+a) (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))))
private theorem sourcePrincipal_laplacian (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : ℝ) {z : Point} (hz : 0 < z 1) :
    L (sourcePrincipal q branch amp p v) z=∑ i : Fin 3,
      coefficient q branch amp p v i*principalExponent q i*(principalExponent q i-1)*
        (z 1:ℂ)^(principalExponent q i) := by
  unfold sourcePrincipal
  rw [power_laplacian_sum Finset.univ _ (fun i _ => c2 (principal_smooth _ _ hz))]
  apply Finset.sum_congr rfl
  intro i _
  have hp := (height_cpow_contDiffOn (principalExponent q i) 2).contDiffAt (positive_nhds hz)
  change hyperbolicLaplacian (fun z : Point => coefficient q branch amp p v i*(z 1:ℂ)^(principalExponent q i)) z=_
  rw [hyperbolicLaplacian_const_mul hp,height_cpow_hyperbolicLaplacian _ z hz]
  ring
private theorem readerPrincipal_derivative (r : XiZeroCopy) {z : Point} (hz : 0 < z 1) :
    D 1 (readerPrincipal r) z=readerCoefficient r*readerExponent r*(z 1:ℂ)^(readerExponent r-1) := by
  have hd := (height_cpow_hasFDerivAt (readerExponent r) z hz).const_mul (readerCoefficient r)
  change fderiv ℝ (fun z : Point => readerCoefficient r*(z 1:ℂ)^(readerExponent r)) z (Pi.single 1 1)=_
  rw [hd.fderiv]
  simp only [smul_apply,smul_eq_mul,gradient_height]
  ring

private theorem source_operators (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    {z : Point} (hz : 0 < z 1) :
    D 1 (D4BMOriginalAngularGreen.source q branch amp p v) z=
      D 1 (sourcePrincipal q branch amp p v) z+D 1 (sourceRemainder q branch amp p v) z ∧
    L (D4BMOriginalAngularGreen.source q branch amp p v) z=
      L (sourcePrincipal q branch amp p v) z+L (sourceRemainder q branch amp p v) z := by
  have he : D4BMOriginalAngularGreen.source q branch amp p v=ᶠ[𝓝 z]
      fun z => sourcePrincipal q branch amp p v z+sourceRemainder q branch amp p v z := by
    filter_upwards [positive_nhds hz] with t ht
    exact source_decomposition q branch amp p v t ht
  have hP := sourcePrincipal_smooth q branch amp p v hz
  have hR : ContDiffAt ℝ ∞ (sourceRemainder q branch amp p v) z :=
    pull_smooth (remainder_smooth q branch amp p v) hz
  have hd := congrArg (fun A : Point →L[ℝ] ℂ => A (Pi.single 1 1)) he.fderiv_eq
  refine ⟨hd.trans (coordDeriv_add (hP.differentiableAt (by simp)) (hR.differentiableAt (by simp)) 1),?_⟩
  exact (hyperbolicLaplacian_congr he).trans (hyperbolicLaplacian_add (c2 hP) (c2 hR))
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

/-- The principal flux is formed by differentiating the original principal fields. -/
def principalFlux (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) (z : Point) : ℂ :=
  L (sourcePrincipal q branch amp p v) z*D 1 (readerPrincipal r) z-
    (physicalAngularParameter r^2-1/4)*readerPrincipal r z*D 1 (sourcePrincipal q branch amp p v) z

def fluxCoefficient (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) (i : Fin 3) : ℂ :=
  coefficient q branch amp p v i*readerCoefficient r*principalExponent q i*readerExponent r*
    (principalExponent q i-readerExponent r)
def fluxExponent (q r : XiZeroCopy) (i : Fin 3) : ℂ := principalExponent q i+readerExponent r-1

/-- Actual differentiation gives every original indicial factor and cusp exponent. -/
theorem principalFlux_expansion (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : ℝ) {z : Point} (hz : 0 < z 1) :
    principalFlux q r branch amp p v z=∑ i : Fin 3,
      fluxCoefficient q r branch amp p v i*(z 1:ℂ)^(fluxExponent q r i) := by
  have hn : (z 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hp (a b : ℂ) : (z 1:ℂ)^a*(z 1:ℂ)^b=(z 1:ℂ)^(a+b) :=
    (Complex.cpow_add a b hn).symm
  rw [principalFlux,sourcePrincipal_laplacian q branch amp p v hz,readerPrincipal_derivative r hz,
    sourcePrincipal_derivative q branch amp p v hz,reader_mu,readerPrincipal]
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (coefficient q branch amp p v i*readerCoefficient r*principalExponent q i*readerExponent r)*
        ((principalExponent q i-1)*((z 1:ℂ)^(principalExponent q i)*(z 1:ℂ)^(readerExponent r-1))-
          (readerExponent r-1)*((z 1:ℂ)^(readerExponent r)*(z 1:ℂ)^(principalExponent q i-1))) := by ring
    _ = _ := by
      rw [hp,hp,show principalExponent q i+(readerExponent r-1)=fluxExponent q r i by unfold fluxExponent; ring,
        show readerExponent r+(principalExponent q i-1)=fluxExponent q r i by unfold fluxExponent; ring]
      unfold fluxCoefficient
      ring

/-- The original differentiated flux minus its complete three-power principal part. -/
def fluxRemainder (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) (z : Point) : ℂ :=
  D4BMOriginalAngularGreen.flux (D4BMOriginalAngularGreen.source q branch amp p v)
    (physicalAngularParameter r) 1 z-principalFlux q r branch amp p v z

/-- Exact six-term remainder; neither principal-tail contact nor derivative term is discarded. -/
theorem fluxRemainder_decomposition (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : ℝ) {z : Point} (hz : 0 < z 1) :
    fluxRemainder q r branch amp p v z=
      L (sourceRemainder q branch amp p v) z*D 1 (readerPrincipal r) z+
      L (sourcePrincipal q branch amp p v) z*D 1 (readerTail r) z+
      L (sourceRemainder q branch amp p v) z*D 1 (readerTail r) z-
      (physicalAngularParameter r^2-1/4)*
        (readerTail r z*D 1 (sourcePrincipal q branch amp p v) z+
          readerPrincipal r z*D 1 (sourceRemainder q branch amp p v) z+
          readerTail r z*D 1 (sourceRemainder q branch amp p v) z) := by
  obtain ⟨hd,hl⟩ := source_operators q branch amp p v hz
  unfold fluxRemainder D4BMOriginalAngularGreen.flux
  change L (D4BMOriginalAngularGreen.source q branch amp p v) z*
      D 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z-
      (physicalAngularParameter r^2-1/4)*D4BMLiteralCusp.scalar (physicalAngularParameter r) z*
        D 1 (D4BMOriginalAngularGreen.source q branch amp p v) z-principalFlux q r branch amp p v z=_
  rw [hd,hl,reader_derivative r hz,reader_decomposition,principalFlux]
  ring

private theorem sourcePrincipal_derivative_moderate (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : ℝ) : Moderate (atHeight (D 1 (sourcePrincipal q branch amp p v))) := by
  have h := Moderate.sum_three (fun i z => coefficient q branch amp p v i*principalExponent q i*
    E (principalExponent q i-1) z) (fun i => (Moderate.exp (principalExponent q i-1)).scale
      (coefficient q branch amp p v i*principalExponent q i))
  apply h.congr
  intro z
  have hd := sourcePrincipal_derivative q branch amp p v (z := ![z 0,Real.exp (z 1)]) (Real.exp_pos _)
  simpa only [atHeight,Matrix.cons_val,exp_cpow,E] using hd.symm
private theorem sourcePrincipal_laplacian_moderate (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : ℝ) : Moderate (atHeight (L (sourcePrincipal q branch amp p v))) := by
  have h := Moderate.sum_three (fun i z => coefficient q branch amp p v i*principalExponent q i*
    (principalExponent q i-1)*E (principalExponent q i) z)
      (fun i => (Moderate.exp (principalExponent q i)).scale
        (coefficient q branch amp p v i*principalExponent q i*(principalExponent q i-1)))
  apply h.congr
  intro z
  have hd := sourcePrincipal_laplacian q branch amp p v (z := ![z 0,Real.exp (z 1)]) (Real.exp_pos _)
  simpa only [atHeight,Matrix.cons_val,exp_cpow,E] using hd.symm
private theorem readerPrincipal_moderate (r : XiZeroCopy) : Moderate (atHeight (readerPrincipal r)) := by
  apply ((Moderate.exp (readerExponent r)).scale (readerCoefficient r)).congr
  intro z
  simp only [atHeight,readerPrincipal,Matrix.cons_val,exp_cpow,E]
private theorem readerPrincipal_derivative_moderate (r : XiZeroCopy) : Moderate (atHeight (D 1 (readerPrincipal r))) := by
  apply ((Moderate.exp (readerExponent r-1)).scale (readerCoefficient r*readerExponent r)).congr
  intro z
  have h := readerPrincipal_derivative r (z := ![z 0,Real.exp (z 1)]) (Real.exp_pos _)
  simpa only [atHeight,Matrix.cons_val,exp_cpow,E] using h.symm

private theorem fluxRemainder_rapid (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) : Rapid (atHeight (fluxRemainder q r branch amp p v)) := by
  have hL := source_laplacian_rapid q branch amp p v
  have hD := source_derivative_rapid q branch amp p v
  have hT := tail_rapid r
  have hTd := tail_derivative_rapid r
  have h := (((hL.mul_moderate (readerPrincipal_derivative_moderate r)).add
    ((sourcePrincipal_laplacian_moderate q branch amp p v) _ hTd)).add (hL.mul hTd)).sub
      ((((hT.mul_moderate (sourcePrincipal_derivative_moderate q branch amp p v)).add
        ((readerPrincipal_moderate r) _ hD)).add (hT.mul hD)).scale (physicalAngularParameter r^2-1/4))
  apply h.congr
  intro z
  exact (fluxRemainder_decomposition q r branch amp p v (z := ![z 0,Real.exp (z 1)]) (Real.exp_pos _)).symm

/-- Every nonprincipal term of the original differentiated physical flux decays
with every complex cusp weight, along any horizontal path. -/
theorem original_flux_expansion (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (D4BMOriginalAngularGreen.flux (D4BMOriginalAngularGreen.source q branch amp p v)
        (physicalAngularParameter r) 1 ![X k,Real.exp k]-
        ∑ i : Fin 3, fluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ))))
      atTop (𝓝 0) := by
  have h := fluxRemainder_rapid q r branch amp p v w X
  convert h using 1
  funext k
  have hp (x : ℝ) : principalFlux q r branch amp p v ![x,Real.exp k]=
      ∑ i : Fin 3, fluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ)) := by
    simpa only [Matrix.cons_val,exp_cpow] using
      principalFlux_expansion q r branch amp p v (z := ![x,Real.exp k]) (Real.exp_pos k)
  simp only [E,atHeight,fluxRemainder,Matrix.cons_val,hp]

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

private theorem source_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    {z : Point} (hz : 0 < z 1) : ContDiffAt ℝ ∞ (D4BMOriginalAngularGreen.source q branch amp p v) z := by
  have hf := (D4BMOriginalCausalPotential.originalPotential_angular_smooth q branch amp p v).comp
    (show ContDiff ℝ ∞ (fun z : Point => (z 0,z 1)) by fun_prop)
  exact pull_smooth hf hz
private theorem partial_smooth {F : Field} {z : Point} (hF : ContDiffAt ℝ ∞ F z) (i : Fin 2) :
    ContDiffAt ℝ ∞ (D i F) z := coordDeriv_contDiffAt hF (by simp) i
private theorem lap_smooth {F : Field} {z : Point} (hF : ContDiffAt ℝ ∞ F z) :
    ContDiffAt ℝ ∞ (L F) z := by
  have hy : ContDiffAt ℝ ∞ (fun v : Point => (v 1:ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt
  exact (hy.pow 2).mul ((partial_smooth (partial_smooth hF 0) 0).add (partial_smooth (partial_smooth hF 1) 1))
private theorem original_flux_smooth (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    {z : Point} (hz : 0 < z 1) : ContDiffAt ℝ ∞
      (D4BMOriginalAngularGreen.flux (D4BMOriginalAngularGreen.source q branch amp p v)
        (physicalAngularParameter r) 1) z := by
  have hS := (cuspLeg_contDiffOn .scalar (physicalAngularParameter r)).contDiffAt (positive_nhds hz)
  have hZ := source_smooth q branch amp p v hz
  exact ((lap_smooth hZ).mul (partial_smooth hS 1)).sub
    ((contDiffAt_const.mul hS).mul (partial_smooth hZ 1))
private theorem original_flux_integrable (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v Y : ℝ) (hY : 0 < Y) : IntervalIntegrable (fun X : ℝ =>
      D4BMOriginalAngularGreen.flux (D4BMOriginalAngularGreen.source q branch amp p v)
        (physicalAngularParameter r) 1 ![X,Y]) volume (-1/2:ℝ) (1/2:ℝ) := by
  have hmap : Continuous (fun X : ℝ => (![X,Y] : Point)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_id
    · exact continuous_const
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro X
  exact (original_flux_smooth q r branch amp p v (z := ![X,Y]) hY).continuousAt.comp (f := fun t : ℝ => (![t,Y] : Point)) (x := X) hmap.continuousAt

private theorem cuspFlux_interval (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v Y : ℝ) :
    D4BMOriginalAngularGreen.cuspFlux q branch amp p v (physicalAngularParameter r) Y=
      ∫ X in (-1/2:ℝ)..1/2,
        D4BMOriginalAngularGreen.flux (D4BMOriginalAngularGreen.source q branch amp p v)
          (physicalAngularParameter r) 1 ![X,Y] := by
  rw [intervalIntegral.integral_of_le (show (-1/2:ℝ)≤1/2 by norm_num)]
  change (∫ X in Ioc (-1/2:ℝ) (1/2:ℝ),
    D4BMOriginalAngularGreen.flux (D4BMOriginalAngularGreen.source q branch amp p v)
      (physicalAngularParameter r) 1 (D4BMModularCore.angularCoordinates (D4BMCuspResponse.point X Y)))=_
  apply integral_congr_ae
  filter_upwards with X
  have hz : D4BMModularCore.angularCoordinates (D4BMCuspResponse.point X Y)=![X,Y] := by
    ext i
    fin_cases i <;> simp [D4BMModularCore.angularCoordinates,D4BMCuspResponse.point]
  rw [hz]

/-- The original width-one cusp flux has the complete three-power expansion;
its integrated remainder vanishes with every complex height weight. -/
theorem original_cuspFlux_expansion (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (D4BMOriginalAngularGreen.cuspFlux q branch amp p v (physicalAngularParameter r) (Real.exp k)-
        ∑ i : Fin 3, fluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ))))
      atTop (𝓝 0) := by
  have h := (fluxRemainder_rapid q r branch amp p v).integral w
  convert h using 1
  funext k
  have hp (x : ℝ) : principalFlux q r branch amp p v ![x,Real.exp k]=
      ∑ i : Fin 3, fluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ)) := by
    simpa only [Matrix.cons_val,exp_cpow] using
      principalFlux_expansion q r branch amp p v (z := ![x,Real.exp k]) (Real.exp_pos k)
  simp only [E,atHeight,fluxRemainder,Matrix.cons_val,hp]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
    (original_flux_integrable q r branch amp p v (Real.exp k) (Real.exp_pos k)) intervalIntegrable_const,
    intervalIntegral.integral_const,cuspFlux_interval]
  simp only [neg_div,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,one_smul]

/-- Coefficients grouped by their actual specialized height exponents. -/
def fluxFamily (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) : ℂ →₀ ℂ :=
  ∑ i : Fin 3, Finsupp.single (fluxExponent q r i) (fluxCoefficient q r branch amp p v i)

private theorem exponent_nonzero_of_im_or (q r : XiZeroCopy)
    (h : (r.1:ℂ).im=(q.1:ℂ).im ∨ (r.1:ℂ).im= -(q.1:ℂ).im) (i : Fin 3) :
    fluxExponent q r i≠0 := by
  have hq := xi_divisor_support_im_ne_zero q.1
  intro he
  have hi := congrArg Complex.im he
  rcases h with h | h
  all_goals
    fin_cases i <;>
      norm_num [fluxExponent,principalExponent,readerExponent,Complex.mul_im,Complex.mul_re] at hi
  all_goals apply hq; linarith

private theorem family_zero_of_nonzero (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (h : ∀ i : Fin 3, fluxExponent q r i≠0) : fluxFamily q r branch amp p v 0=0 := by
  classical
  simp [fluxFamily,Fin.sum_univ_three,h]

/-- The complete original diagonal flux expansion has no constant-height coefficient. -/
theorem diagonal_constant_zero (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) :
    fluxFamily q q branch amp p v 0=0 :=
  family_zero_of_nonzero q q branch amp p v (exponent_nonzero_of_im_or q q (Or.inl rfl))

/-- The original functional-equation reflected reader also has no constant-height coefficient. -/
theorem reflected_constant_zero (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) :
    fluxFamily q (xiZeroCopyReflectEquiv q) branch amp p v 0=0 := by
  have h : ((xiZeroCopyReflectEquiv q).1:ℂ).im= -(q.1:ℂ).im := by
    rw [show ((xiZeroCopyReflectEquiv q).1:ℂ)=1-(q.1:ℂ) from xiZeroReflectEquiv_apply q.1]
    simp
  exact family_zero_of_nonzero q (xiZeroCopyReflectEquiv q) branch amp p v
    (exponent_nonzero_of_im_or q (xiZeroCopyReflectEquiv q) (Or.inr h))

private theorem first_exponent_zero (q r : XiZeroCopy) :
    fluxExponent q r 0=0 ↔ (r.1:ℂ)=4*(q.1:ℂ) := by
  change 2*(q.1:ℂ)+(1-(r.1:ℂ)/2)-1=0 ↔ _
  constructor
  · intro h; linear_combination -2*h
  · intro h; linear_combination -(1/2:ℂ)*h
private theorem last_exponent_zero (q r : XiZeroCopy) :
    fluxExponent q r 2=0 ↔ (r.1:ℂ)=4-4*(q.1:ℂ) := by
  change (2-2*(q.1:ℂ))+(1-(r.1:ℂ)/2)-1=0 ↔ _
  constructor
  · intro h; linear_combination -2*h
  · intro h; linear_combination -(1/2:ℂ)*h
private theorem middle_exponent_nonzero (q r : XiZeroCopy) : fluxExponent q r 1≠0 := by
  have hr := xi_divisor_support_im_ne_zero r.1
  intro he
  have hi := congrArg Complex.im he
  norm_num [fluxExponent,principalExponent,readerExponent] at hi
  apply hr
  linarith

/-- Exact constant-height contribution at independent Xi occurrences: all three
original causal coefficients are retained until their specialized exponents are tested. -/
theorem independent_constant_classification (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) :
    fluxFamily q r branch amp p v 0=
      (if (r.1:ℂ)=4*(q.1:ℂ) then fluxCoefficient q r branch amp p v 0 else 0)+
      (if (r.1:ℂ)=4-4*(q.1:ℂ) then fluxCoefficient q r branch amp p v 2 else 0) := by
  classical
  simp [fluxFamily,Fin.sum_univ_three,Finsupp.single_apply,first_exponent_zero,last_exponent_zero,
    middle_exponent_nonzero]

/-- The nonconstant terms of the original flux expansion at logarithmic height `k`.
Any genuine constant coefficient is retained in the finite part. -/
def nonconstantFlux (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v k : ℝ) : ℂ :=
  ∑ i : Fin 3, if fluxExponent q r i=0 then 0 else
    fluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ))

private theorem powerSum_sub_nonconstant (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v k : ℝ) :
    (∑ i : Fin 3, fluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ)))-
      nonconstantFlux q r branch amp p v k=fluxFamily q r branch amp p v 0 := by
  classical
  have ht (i : Fin 3) :
      fluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ))-
        (if fluxExponent q r i=0 then 0 else
          fluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ)))=
        (if fluxExponent q r i=0 then fluxCoefficient q r branch amp p v i else 0) := by
    by_cases hi : fluxExponent q r i=0 <;> simp [hi]
  simp only [nonconstantFlux,fluxFamily,Fin.sum_univ_three,Finsupp.add_apply,Finsupp.single_apply]
  linear_combination ht 0+ht 1+ht 2

/-- Removing exactly the nonconstant original powers leaves the actual constant
coefficient of the full integrated causal flux, including resonant independent readers. -/
theorem original_cuspFlux_finitePart (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) :
    Tendsto (fun k : ℝ =>
      D4BMOriginalAngularGreen.cuspFlux q branch amp p v (physicalAngularParameter r) (Real.exp k)-
        nonconstantFlux q r branch amp p v k) atTop (𝓝 (fluxFamily q r branch amp p v 0)) := by
  have h0 := original_cuspFlux_expansion q r branch amp p v 0
  simp only [zero_mul,Complex.exp_zero,one_mul] at h0
  have h := h0.add_const (fluxFamily q r branch amp p v 0)
  convert h using 1
  · funext k
    linear_combination powerSum_sub_nonconstant q r branch amp p v k
  · simp

/-- Exact finite part of the original angular-action transfer over the infinite
cusp. Its lower endpoint and any genuine resonant constant are preserved. -/
theorem original_cuspAction_finitePart (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) (a : Ioi (0:ℝ)) :
    Tendsto (fun k : ℝ =>
      (∫ Y in (a:ℝ)..Real.exp k, D4BMOriginalAngularGreen.cuspDefect q branch amp p v
        (physicalAngularParameter r) Y)-nonconstantFlux q r branch amp p v k) atTop
      (𝓝 (fluxFamily q r branch amp p v 0-
        D4BMOriginalAngularGreen.cuspFlux q branch amp p v (physicalAngularParameter r) a)) := by
  have h := (original_cuspFlux_finitePart q r branch amp p v).sub_const
    (D4BMOriginalAngularGreen.cuspFlux q branch amp p v (physicalAngularParameter r) a)
  convert h using 1
  funext k
  rw [D4BMOriginalAngularGreen.original_coexact_green q r branch amp p v a ⟨Real.exp k,Real.exp_pos k⟩]
  ring

/-- On the original reflection pair the infinite-cusp action has precisely its
retained lower boundary; there is no constant-height upper boundary contribution. -/
theorem reflected_cuspAction_finitePart (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) (a : Ioi (0:ℝ)) :
    Tendsto (fun k : ℝ =>
      (∫ Y in (a:ℝ)..Real.exp k, D4BMOriginalAngularGreen.cuspDefect q branch amp p v
        (physicalAngularParameter (xiZeroCopyReflectEquiv q)) Y)-
        nonconstantFlux q (xiZeroCopyReflectEquiv q) branch amp p v k) atTop
      (𝓝 (-D4BMOriginalAngularGreen.cuspFlux q branch amp p v
        (physicalAngularParameter (xiZeroCopyReflectEquiv q)) a)) := by
  simpa only [reflected_constant_zero,zero_sub] using
    original_cuspAction_finitePart q (xiZeroCopyReflectEquiv q) branch amp p v a

/-- Original normal flux for transferring one angular derivative onto the physical reader. -/
def pairingFlux (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) (z : Point) : ℂ :=
  D4BMOriginalAngularGreen.source q branch amp p v z*
    D 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z

def pairingFluxCoefficient (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) (i : Fin 3) : ℂ :=
  coefficient q branch amp p v i*readerCoefficient r*readerExponent r

def pairingPrincipalFlux (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) (z : Point) : ℂ :=
  sourcePrincipal q branch amp p v z*D 1 (readerPrincipal r) z

/-- All original principal coefficients survive the one-derivative transfer. -/
theorem pairingPrincipalFlux_expansion (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : ℝ) {z : Point} (hz : 0 < z 1) :
    pairingPrincipalFlux q r branch amp p v z=∑ i : Fin 3,
      pairingFluxCoefficient q r branch amp p v i*(z 1:ℂ)^(fluxExponent q r i) := by
  have hn : (z 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.ne'
  rw [pairingPrincipalFlux,readerPrincipal_derivative r hz,sourcePrincipal,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = pairingFluxCoefficient q r branch amp p v i*
        ((z 1:ℂ)^(principalExponent q i)*(z 1:ℂ)^(readerExponent r-1)) := by
      unfold pairingFluxCoefficient
      ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hn]
      congr 2
      unfold fluxExponent
      ring

def pairingFluxRemainder (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) (z : Point) : ℂ :=
  pairingFlux q r branch amp p v z-pairingPrincipalFlux q r branch amp p v z

/-- Exact normal-flux remainder: both principal-tail products and the tail-tail product. -/
theorem pairingFluxRemainder_decomposition (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : ℝ) {z : Point} (hz : 0 < z 1) :
    pairingFluxRemainder q r branch amp p v z=
      sourceRemainder q branch amp p v z*D 1 (readerPrincipal r) z+
      sourcePrincipal q branch amp p v z*D 1 (readerTail r) z+
      sourceRemainder q branch amp p v z*D 1 (readerTail r) z := by
  unfold pairingFluxRemainder pairingFlux pairingPrincipalFlux
  rw [source_decomposition q branch amp p v z hz,reader_derivative r hz]
  ring

private theorem sourcePrincipal_moderate (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : ℝ) : Moderate (atHeight (sourcePrincipal q branch amp p v)) := by
  have h := Moderate.sum_three (fun i z => coefficient q branch amp p v i*E (principalExponent q i) z)
    (fun i => (Moderate.exp (principalExponent q i)).scale (coefficient q branch amp p v i))
  apply h.congr
  intro z
  simp only [atHeight,sourcePrincipal,Matrix.cons_val,exp_cpow,E]

private theorem pairingFluxRemainder_rapid (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) : Rapid (atHeight (pairingFluxRemainder q r branch amp p v)) := by
  have hR := source_remainder_rapid q branch amp p v
  have hT := tail_derivative_rapid r
  have h := ((hR.mul_moderate (readerPrincipal_derivative_moderate r)).add
    ((sourcePrincipal_moderate q branch amp p v) _ hT)).add (hR.mul hT)
  apply h.congr
  intro z
  exact (pairingFluxRemainder_decomposition q r branch amp p v
    (z := ![z 0,Real.exp (z 1)]) (Real.exp_pos _)).symm

private theorem pairingFlux_integrable (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v Y : ℝ) (hY : 0 < Y) : IntervalIntegrable (fun X : ℝ =>
      pairingFlux q r branch amp p v ![X,Y]) volume (-1/2:ℝ) (1/2:ℝ) := by
  have hmap : Continuous (fun X : ℝ => (![X,Y] : Point)) := by
    apply continuous_pi; intro i; fin_cases i <;> fun_prop
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro X
  have hS := (cuspLeg_contDiffOn .scalar (physicalAngularParameter r)).contDiffAt
    (positive_nhds (z := ![X,Y]) hY)
  have h := (source_smooth q branch amp p v (z := ![X,Y]) hY).mul (partial_smooth hS 1)
  exact h.continuousAt.comp (f := fun t : ℝ => (![t,Y] : Point)) (x := X) hmap.continuousAt

/-- Complete original width-one normal flux; no boundary term is removed. -/
def pairingCuspFlux (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v Y : ℝ) : ℂ :=
  ∫ X in (-1/2:ℝ)..1/2, pairingFlux q r branch amp p v ![X,Y]

/-- The actual integrated normal-flux remainder decays with every complex cusp weight. -/
theorem original_pairingCuspFlux_expansion (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (pairingCuspFlux q r branch amp p v (Real.exp k)-
        ∑ i : Fin 3, pairingFluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ))))
      atTop (𝓝 0) := by
  have h := (pairingFluxRemainder_rapid q r branch amp p v).integral w
  convert h using 1
  funext k
  have hp (x : ℝ) : pairingPrincipalFlux q r branch amp p v ![x,Real.exp k]=
      ∑ i : Fin 3, pairingFluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ)) := by
    simpa only [Matrix.cons_val,exp_cpow] using
      pairingPrincipalFlux_expansion q r branch amp p v (z := ![x,Real.exp k]) (Real.exp_pos k)
  simp only [E,atHeight,pairingFluxRemainder,Matrix.cons_val,hp]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
    (pairingFlux_integrable q r branch amp p v (Real.exp k) (Real.exp_pos k)) intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [pairingCuspFlux,neg_div,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,one_smul]

/-- Constant-height normal-flux coefficient, grouping all original source powers. -/
def pairingFluxConstant (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) : ℂ :=
  ∑ i : Fin 3, if fluxExponent q r i=0 then pairingFluxCoefficient q r branch amp p v i else 0

/-- Only the derived nonconstant normal-flux powers are subtracted. -/
def pairingNonconstantFlux (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v k : ℝ) : ℂ :=
  ∑ i : Fin 3, if fluxExponent q r i=0 then 0 else
    pairingFluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ))

private theorem pairingPowerSum_sub_nonconstant (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v k : ℝ) :
    (∑ i : Fin 3, pairingFluxCoefficient q r branch amp p v i*Complex.exp (fluxExponent q r i*(k:ℂ)))-
      pairingNonconstantFlux q r branch amp p v k=pairingFluxConstant q r branch amp p v := by
  classical
  unfold pairingNonconstantFlux pairingFluxConstant
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : fluxExponent q r i=0 <;> simp [hi]

/-- The original normal-flux finite part retains precisely its actual resonant coefficient. -/
theorem original_pairingCuspFlux_finitePart (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) :
    Tendsto (fun k : ℝ => pairingCuspFlux q r branch amp p v (Real.exp k)-
      pairingNonconstantFlux q r branch amp p v k) atTop (𝓝 (pairingFluxConstant q r branch amp p v)) := by
  have h0 := original_pairingCuspFlux_expansion q r branch amp p v 0
  simp only [zero_mul,Complex.exp_zero,one_mul] at h0
  have h := h0.add_const (pairingFluxConstant q r branch amp p v)
  convert h using 1
  · funext k
    linear_combination pairingPowerSum_sub_nonconstant q r branch amp p v k
  · simp

/-- Only the two original independent-reader resonances can contribute to the normal finite part. -/
theorem pairingFluxConstant_classification (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) :
    pairingFluxConstant q r branch amp p v=
      (if (r.1:ℂ)=4*(q.1:ℂ) then pairingFluxCoefficient q r branch amp p v 0 else 0)+
      (if (r.1:ℂ)=4-4*(q.1:ℂ) then pairingFluxCoefficient q r branch amp p v 2 else 0) := by
  classical
  simp [pairingFluxConstant,Fin.sum_univ_three,first_exponent_zero,last_exponent_zero,middle_exponent_nonzero]

/-- The diagonal and reflected original readers have no constant normal-flux contribution. -/
theorem pairingFluxConstant_original_readers (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) :
    pairingFluxConstant q q branch amp p v=0 ∧
      pairingFluxConstant q (xiZeroCopyReflectEquiv q) branch amp p v=0 := by
  have hq := exponent_nonzero_of_im_or q q (Or.inl rfl)
  have hr : ((xiZeroCopyReflectEquiv q).1:ℂ).im= -(q.1:ℂ).im := by
    rw [show ((xiZeroCopyReflectEquiv q).1:ℂ)=1-(q.1:ℂ) from xiZeroReflectEquiv_apply q.1]
    simp
  have hf := exponent_nonzero_of_im_or q (xiZeroCopyReflectEquiv q) (Or.inr hr)
  constructor
  · simp [pairingFluxConstant,hq]
  · simp [pairingFluxConstant,hf]

end
end RHTower.D4BMOriginalCuspFlux

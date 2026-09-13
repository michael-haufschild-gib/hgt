import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCausalPotential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalResponseCusp
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalAngularCutoffCalibration

/-!
Angular cusp jets of the full original causal potential, with the onset lift.

The three principal coefficients are the original causal radial responses plus
the lifted original source amplitudes. Radius zero of the native circle gives
an exact decomposition of every angular remainder jet. Native and causal cusp
bounds then give decay with any complex height weight, uniformly in horizontal
position and after integration over the width-one cusp interval.

The null coordinates are fixed nonnegative parameters in the limit theorems.
No uniform infinite-time or horizon limit, physical flux cancellation, or RH
conclusion is asserted.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMOriginalCuspJets
open D4BMOriginalCausalPotential D4BMNativeResponse D4BMNativeCircle D4BMCausalCusp
open D4BMNativeAngularCurrent D4BMNativeCuspJets D4BMSquareCuspJets D4BMJointSource D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev Angular := Fin 2 → ℝ
private abbrev Native := Fin 3 → ℝ

def coefficient (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) (i : Fin 3) : ℂ :=
  principalNullResponse q (physicalRate q branch) amp i p r+
    nullLift (physicalRate q branch) amp p r*principalAmplitude q i

def principal (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) (z : Angular) : ℂ :=
  ∑ i : Fin 3, coefficient q branch amp p r i*Complex.exp (principalExponent q i*(z 1:ℂ))

def remainder (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) (z : Angular) : ℂ :=
  originalPotential q branch amp p r (z 0) (z 1)-principal q branch amp p r z

private theorem exp_cpow (a : ℂ) (k : ℝ) :
    (Real.exp k:ℂ)^a=Complex.exp (a*(k:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
    ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
  congr 1
  ring

private theorem circle_zero (a : ℂ) : powerCircle a 0=1 := by
  rw [powerCircle_eq_legendre,Real.cosh_zero,D4BMCausalKernel.legendreKernel_one]

private theorem remainder_decomposition (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) :
    remainder q branch amp p r=fun z => responseRemainder q (physicalRate q branch) amp p r z+
      nullLift (physicalRate q branch) amp p r*nativeRemainder q ![0,z 0,z 1] := by
  funext z
  simp only [remainder,originalPotential,sourceProfile,responseRemainder,principalResponse,
    nativeRemainder,cuspMeanRemainder,Matrix.cons_val,mean_zero,transportedPrincipal,
    circle_zero,mul_one,exp_cpow,principal,coefficient,add_mul,Finset.sum_add_distrib]
  simp only [mul_assoc,← Finset.mul_sum]
  ring

private theorem principal_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) :
    ContDiff ℝ ∞ (principal q branch amp p r) := by
  unfold principal
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_apply ℝ ℝ (1:Fin 2)))).cexp)

private theorem response_smooth (q : XiZeroCopy) (s amp : ℂ) (p r : ℝ) :
    ContDiff ℝ ∞ (responseRemainder q s amp p r) := by
  have hp : ContDiff ℝ ∞ (principalResponse q s amp p r) := by
    unfold principalResponse
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_apply ℝ ℝ (1:Fin 2)))).cexp)
  exact ((fullNullResponse_angular_smooth q s amp p r).comp
    (show ContDiff ℝ ∞ (fun z : Angular => (z 0,z 1)) by fun_prop)).sub hp

private theorem native_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (nativeRemainder q) := by
  have hc (a : ℂ) : ContDiff ℝ ∞ (powerCircle a) := by
    apply contDiff_iff_contDiffAt.mpr
    intro d
    have h := (D4BMCausalSourceKernel.legendre_contDiffAt (-a) (Real.cosh_pos d)).comp d
      (show ContDiffAt ℝ ∞ Real.cosh d by fun_prop)
    simpa only [Function.comp_def,← powerCircle_eq_legendre] using h
  have hp : ContDiff ℝ ∞ (fun z : Native => transportedPrincipal q (z 0) (z 2)) := by
    simp only [transportedPrincipal,exp_cpow]
    apply ContDiff.sum
    intro i _
    exact (contDiff_const.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_apply ℝ ℝ (2:Fin 3)))).cexp)).mul
        ((hc _).comp (contDiff_apply ℝ ℝ (0:Fin 3)))
  exact ((nativeMean_joint_smooth q).comp
    (show ContDiff ℝ ∞ (fun z : Native => (z 0,z 1,z 2)) by fun_prop)).sub hp

private theorem jet_smooth {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) : ContDiff ℝ ∞ (coordDeriv i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem native_jet_smooth (q : XiZeroCopy) (word : List (Fin 3)) :
    ContDiff ℝ ∞ (nativeJet word (nativeRemainder q)) := by
  induction word with
  | nil => exact native_smooth q
  | cons i word ih => exact jet_smooth ih i

private def insert : Angular →L[ℝ] Native :=
  ContinuousLinearMap.pi ![0,ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1]
private theorem insert_apply (z : Angular) : insert z=![0,z 0,z 1] := by
  ext i
  fin_cases i <;> rfl
private theorem derivative_insert {f : Native → ℂ} (hf : ContDiff ℝ ∞ f)
    (i : Fin 2) (z : Angular) :
    coordDeriv i (fun z => f ![0,z 0,z 1]) z=coordDeriv i.succ f ![0,z 0,z 1] := by
  have h := ((hf.differentiable (by simp) (insert z)).hasFDerivAt).comp z insert.hasFDerivAt
  have he : (fun z : Angular => f (insert z))=fun z => f ![0,z 0,z 1] := by
    funext z
    rw [insert_apply]
  change HasFDerivAt (fun z => f (insert z)) _ z at h
  rw [he] at h
  change fderiv ℝ _ z (Pi.single i 1)=_
  rw [h.fderiv]
  have hd : insert (Pi.single i 1)=Pi.single i.succ 1 := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [insert]
  change fderiv ℝ f (insert z) (insert (Pi.single i 1))=_
  rw [hd,insert_apply]

private theorem insert_jet (q : XiZeroCopy) (word : List (Fin 2)) :
    coordinateJet word (fun z => nativeRemainder q ![0,z 0,z 1])=
      fun z => nativeJet (word.map Fin.succ) (nativeRemainder q) ![0,z 0,z 1] := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    funext z
    simp only [coordinateJet,ih,List.map_cons,nativeJet]
    exact derivative_insert (native_jet_smooth q (word.map Fin.succ)) i z

private theorem angular_jet_smooth {f : Angular → ℂ} (hf : ContDiff ℝ ∞ f)
    (word : List (Fin 2)) : ContDiff ℝ ∞ (coordinateJet word f) := by
  induction word with
  | nil => exact hf
  | cons i word ih => exact jet_smooth ih i

private theorem jet_add_scale {f g : Angular → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (c : ℂ) (word : List (Fin 2)) :
    coordinateJet word (fun z => f z+c*g z)=
      fun z => coordinateJet word f z+c*coordinateJet word g z := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    funext z
    simp only [coordinateJet,ih]
    unfold coordDeriv
    have hf' := (angular_jet_smooth hf word).differentiable (by simp) z
    have hg' := (angular_jet_smooth hg word).differentiable (by simp) z
    rw [fderiv_fun_add hf' (hg'.const_mul c),fderiv_const_mul hg']
    simp only [add_apply,smul_apply,smul_eq_mul]

/-- Exact derivative decomposition for the restored original source, including its onset lift. -/
theorem original_remainder_jet (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : ℝ) (word : List (Fin 2)) (z : Angular) :
    coordinateJet word (remainder q branch amp p r) z=
      coordinateJet word (responseRemainder q (physicalRate q branch) amp p r) z+
        nullLift (physicalRate q branch) amp p r*
          nativeJet (word.map Fin.succ) (nativeRemainder q) ![0,z 0,z 1] := by
  have hn : ContDiff ℝ ∞ (fun z : Angular => nativeRemainder q ![0,z 0,z 1]) :=
    (native_smooth q).comp (show ContDiff ℝ ∞ (fun z : Angular => ![0,z 0,z 1]) by
      have hi : (fun z : Angular => ![0,z 0,z 1])=insert := funext (fun z => (insert_apply z).symm)
      rw [hi]
      exact insert.contDiff)
  rw [remainder_decomposition,jet_add_scale (response_smooth q _ amp p r) hn,insert_jet]

/-- Every angular jet of the full original remainder vanishes after any complex log-height weight. -/
theorem original_remainder_jet_tendsto_zero (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : Ici (0:ℝ)) (word : List (Fin 2)) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      coordinateJet word (remainder q branch amp p r) ![X k,k]) atTop (𝓝 0) := by
  let T : Ici (0:ℝ) := ⟨max p.val r.val,show 0 ≤ max p.val r.val from (show 0 ≤ p.val from p.property).trans (le_max_left _ _)⟩
  let pp : Icc 0 T.val := ⟨p.val,⟨p.property,le_max_left _ _⟩⟩
  let rr : Icc 0 T.val := ⟨r.val,⟨r.property,le_max_right _ _⟩⟩
  have hc := responseRemainder_jet_weighted_tendsto_zero q (physicalRate q branch) amp
    word T (fun _ => pp) (fun _ => rr) X w
  have hn : Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      nativeJet (word.map Fin.succ) (nativeRemainder q) ![0,X k,k]) atTop (𝓝 0) := by
    obtain ⟨N,hN⟩ := exists_nat_gt w.re
    obtain ⟨B,hB,hbound⟩ := nativeCuspJet_rapid_bound q (word.map Fin.succ) N ⟨0,show (0:ℝ) ≤ 0 from le_rfl⟩
    have ht := Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (sub_neg.mpr hN)).2 tendsto_id)
    apply squeeze_zero_norm' _ (by simpa using ht.const_mul B)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with k hk
    rw [norm_mul,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    calc
      _ ≤ Real.exp (w.re*k)*(B*Real.exp ((N:ℝ)*(0-k))) := by
        gcongr
        exact hbound 0 (X k) k le_rfl le_rfl hk
      _ = B*Real.exp ((w.re-(N:ℝ))*k) := by
        rw [← mul_assoc,mul_comm (Real.exp _) B,mul_assoc,← Real.exp_add]
        congr 2
        ring
  have h := hc.add (hn.const_mul (nullLift (physicalRate q branch) amp p r))
  convert h using 1
  · funext k
    rw [original_remainder_jet]
    dsimp only [pp,rr,nativeRemainder]
    simp only [Matrix.cons_val]
    ring
  · simp

private theorem uniform_of_arbitrary_paths (F : ℝ → ℝ → ℂ)
    (h : ∀ X : ℝ → ℝ, Tendsto (fun k => F k (X k)) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ k : ℝ in atTop, ∀ x : ℝ, ‖F k x‖ < epsilon := by
  classical
  let X : ℝ → ℝ := fun k => if hx : ∃ x, epsilon ≤ ‖F k x‖ then hx.choose else 0
  have ht := Metric.tendsto_nhds.mp (h X) epsilon hepsilon
  filter_upwards [ht] with k hk x
  rw [dist_zero_right] at hk
  by_contra hx
  have he : ∃ x, epsilon ≤ ‖F k x‖ := ⟨x,le_of_not_gt hx⟩
  have hb : epsilon ≤ ‖F k (X k)‖ := by
    dsimp only [X]
    rw [dif_pos he]
    exact he.choose_spec
  exact (not_lt_of_ge hb) hk

/-- The original remainder estimate is uniform in the full horizontal variable,
not merely at each fixed point of the cusp. -/
theorem original_remainder_jet_uniform (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : Ici (0:ℝ)) (word : List (Fin 2)) (w : ℂ) (epsilon : Ioi (0:ℝ)) :
    ∀ᶠ k : ℝ in atTop, ∀ X : ℝ,
      ‖Complex.exp (w*(k:ℂ))*coordinateJet word (remainder q branch amp p r) ![X,k]‖ < epsilon :=
  uniform_of_arbitrary_paths _ (fun X => original_remainder_jet_tendsto_zero q branch amp p r word X w)
    epsilon epsilon.property

/-- After the original three principal channels are subtracted, every angular
jet has zero integrated cusp limit with any complex height weight. -/
theorem original_remainder_jet_integral_tendsto_zero (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : Ici (0:ℝ)) (word : List (Fin 2)) (w : ℂ) :
    Tendsto (fun k : ℝ => ∫ X in (-1/2:ℝ)..1/2,
      Complex.exp (w*(k:ℂ))*coordinateJet word (remainder q branch amp p r) ![X,k])
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have he : 0 < epsilon/2 := half_pos hepsilon
  filter_upwards [original_remainder_jet_uniform q branch amp p r word w ⟨epsilon/2,he⟩] with k hk
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1/2:ℝ)) (b := (1/2:ℝ)) (fun X _ => (hk X).le)
  norm_num only [sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one] at hi
  rw [dist_zero_right]
  simpa only [neg_div] using hi.trans_lt (half_lt_self hepsilon)

end
end RHTower.D4BMOriginalCuspJets

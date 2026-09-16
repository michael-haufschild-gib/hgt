import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFuturePulseAssembly
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureSourceBridge

/-! Identification of the original future pulse with its complete compact source action. -/
namespace RHTower.D4BMFuturePulseIdentity
open Set Filter Topology MeasureTheory
open D4BMHorizon D4BMModularCore D4BMJointSource D4BMNativeCircle D4BMCausalKernel
open D4BMFullAngularCircle D4BMFullAngularReconstruction
open D4BMFuturePulseAssembly D4BMFuturePulseCorner D4BMFutureSourceBridge
open scoped ContDiff
noncomputable section
set_option autoImplicit false

private theorem average_unit (f : ℝ → ℂ) :
    D4BMNativeCircle.average f=∫ t in (0:ℝ)..1, f (2*Real.pi*t) := by
  unfold D4BMNativeCircle.average
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  have h := intervalIntegral.smul_integral_comp_add_mul
    (a := (0:ℝ)) (b := 1) f (2*Real.pi) 0
  simp only [mul_zero,mul_one,zero_add,Complex.real_smul] at h
  rw [← h]
  have hn : (2*Real.pi:ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
  push_cast
  field_simp

private def closedArm (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) (hy : ℝ × ℝ) : ℂ :=
  onsetAngularMean q branch amp ((p+r)/2+hy.1) hy.2
    (Real.arcosh (max 1 (invariant hy.1 ((p-r)/2) (if image then -hy.2 else hy.2)))) X k/2

private theorem closedArm_compact (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) (hy : ℝ × ℝ) :
    closedArm image q branch amp p r X k hy=
      2*(Real.exp (2*hy.2):ℂ)*compactMean image q branch amp r (r-p) X k
        ((p+r)/2+hy.1+hy.2) (Real.exp (2*hy.2)) := by
  let d := Real.arcosh (max 1 (invariant hy.1 ((p-r)/2) (if image then -hy.2 else hy.2)))
  have hs (c : ℝ) :
      compactSample image q branch amp r (r-p) X k ((p+r)/2+hy.1+hy.2) (Real.exp (2*hy.2)) c=
      fullSourceOnsetPulse q branch amp ((p+r)/2+hy.1) hy.2
        (logCircle d (2*Real.pi*c) X k)/(4*(Real.exp (2*hy.2):ℂ)) := by
    rw [compactSample_original]
    rw [show (p+r)/2+hy.1+hy.2-hy.2=(p+r)/2+hy.1 by ring,
      show r-(r-p)/2=(p+r)/2 by ring,show -(r-p)/2=(p-r)/2 by ring,
      show (p+r)/2+hy.1-(p+r)/2=hy.1 by ring]
  have hm : compactMean image q branch amp r (r-p) X k ((p+r)/2+hy.1+hy.2) (Real.exp (2*hy.2))=
      onsetAngularMean q branch amp ((p+r)/2+hy.1) hy.2 d X k/(4*(Real.exp (2*hy.2):ℂ)) := by
    unfold compactMean
    simp_rw [hs]
    rw [intervalIntegral.integral_div]
    congr 1
    exact (average_unit (fun theta => fullSourceOnsetPulse q branch amp ((p+r)/2+hy.1) hy.2
      (logCircle d theta X k))).symm
  rw [hm]
  have he : (Real.exp (2*hy.2):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  unfold closedArm
  change onsetAngularMean q branch amp ((p+r)/2+hy.1) hy.2 d X k/2=_
  field_simp [he]
  ring

private theorem closedArm_continuous (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) : Continuous (closedArm image q branch amp p r X k) := by
  have hc : Continuous (fun hy : ℝ × ℝ => (((p+r)/2+hy.1+hy.2),Real.exp (2*hy.2))) := by fun_prop
  have hM := (compactMean_clamped_continuous image q branch amp r (r-p) X k).comp hc
  have hm : Continuous (fun hy : ℝ × ℝ => compactMean image q branch amp r (r-p) X k
      ((p+r)/2+hy.1+hy.2) (Real.exp (2*hy.2))) := by
    convert hM using 1
    funext hy
    exact congrArg (compactMean image q branch amp r (r-p) X k ((p+r)/2+hy.1+hy.2))
      (max_eq_right (Real.exp_pos _).le).symm
  have hE : Continuous (fun hy : ℝ × ℝ => (Real.exp (2*hy.2):ℂ)) := by fun_prop
  have he : closedArm image q branch amp p r X k=fun hy =>
      2*(Real.exp (2*hy.2):ℂ)*compactMean image q branch amp r (r-p) X k
        ((p+r)/2+hy.1+hy.2) (Real.exp (2*hy.2)) :=
    funext (closedArm_compact image q branch amp p r X k)
  rw [he]
  exact (hE.const_mul 2).mul hm

private theorem closedArm_on_cone (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) (hy : ℝ × ℝ)
    (hc : |(p-r)/2-(if image then -hy.2 else hy.2)| ≤ hy.1) :
    closedArm image q branch amp p r X k hy=
      onsetAngularMean q branch amp ((p+r)/2+hy.1) hy.2
        (Real.arcosh (invariant hy.1 ((p-r)/2) (if image then -hy.2 else hy.2))) X k/2 := by
  rw [closedArm,max_eq_right (invariant_causal ⟨hy.1,(p-r)/2,_,hc⟩)]

private theorem gated_closedArm (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) (hy : ℝ × ℝ) :
    (if |(p-r)/2-(if image then -hy.2 else hy.2)| ≤ hy.1 then
      closedArm image q branch amp p r X k hy else 0)=
    (if |(p-r)/2-(if image then -hy.2 else hy.2)| ≤ hy.1 then
      onsetAngularMean q branch amp ((p+r)/2+hy.1) hy.2
        (Real.arcosh (invariant hy.1 ((p-r)/2) (if image then -hy.2 else hy.2))) X k else 0)/2 := by
  by_cases hc : |(p-r)/2-(if image then -hy.2 else hy.2)| ≤ hy.1
  · rw [if_pos hc,if_pos hc,closedArm_on_cone image q branch amp p r X k hy hc]
  · simp only [if_neg hc,zero_div]

private theorem density_gates (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) (hy : ℝ × ℝ) :
    D4BMFuturePulseAdmission.density q branch amp ((p+r)/2) ((p-r)/2) X k hy=
      (if |(p-r)/2-hy.2| ≤ hy.1 then closedArm false q branch amp p r X k hy else 0)-
      (if |(p-r)/2+hy.2| ≤ hy.1 then closedArm true q branch amp p r X k hy else 0) := by
  have h0 := gated_closedArm false q branch amp p r X k hy
  have h1 := gated_closedArm true q branch amp p r X k hy
  simp only [Bool.false_eq_true,↓reduceIte,sub_neg_eq_add] at h0 h1
  rw [h0,h1]
  dsimp only [D4BMFuturePulseAdmission.density,onsetDirichletKernel]
  ring

private theorem closedArm_null (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k v u : ℝ) :
    closedArm image q branch amp p r X k ((v+u)/2-(p+r)/2,(v-u)/2)/2=
      (Real.exp (v-u):ℂ)*compactMean image q branch amp r (r-p) X k v (Real.exp (v-u)) := by
  rw [closedArm_compact]
  change (2*(Real.exp (2*((v-u)/2)):ℂ)*compactMean image q branch amp r (r-p) X k
    ((p+r)/2+((v+u)/2-(p+r)/2)+(v-u)/2) (Real.exp (2*((v-u)/2))))/2=_
  rw [show 2*((v-u)/2)=v-u by ring,
    show (p+r)/2+((v+u)/2-(p+r)/2)+(v-u)/2=v by ring]
  ring

private theorem exponential_source_change (F : ℝ → ℂ) (v a b : ℝ) :
    (∫ u in a..b, (Real.exp (v-u):ℂ)*F (Real.exp (v-u)))=
      ∫ z in (Real.exp (v-b))..(Real.exp (v-a)),F z := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (f := fun u : ℝ => Real.exp (v-u)) (f' := fun u : ℝ => -Real.exp (v-u)) (g := F)
    (by fun_prop : ContinuousOn (fun u : ℝ => Real.exp (v-u)) (uIcc a b))
    (fun u _ => by simpa using ((hasDerivAt_const u v).sub (hasDerivAt_id u)).exp)
    (fun u _ => (neg_nonpos.mpr (Real.exp_pos _).le))
  simp only [Function.comp_apply,Complex.real_smul,Complex.ofReal_neg,neg_mul,
    intervalIntegral.integral_neg] at h
  rw [intervalIntegral.integral_symm (a := Real.exp (v-b)) (b := Real.exp (v-a))] at h
  exact neg_injective h

private def cutArm (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r L X k : ℝ) : ℂ :=
  (∫ v in (if image then r else p)..r, ∫ z in (Real.exp (v-L))..(Real.exp (v-r)),
    compactMean image q branch amp r (r-p) X k v z)+
  (∫ v in r..L, ∫ z in (Real.exp (v-L))..1,
    compactMean image q branch amp r (r-p) X k v z)

private theorem original_cut_eq_compact_cut (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r L X k : ℝ) (hpr : p ≤ r) (hrL : r ≤ L) :
    D4BMFuturePulseAdmission.truncatedResponse q branch amp ((p+r)/2) ((p-r)/2) X k L=
      cutArm false q branch amp p r L X k-cutArm true q branch amp p r L X k := by
  let F : Bool → (ℝ × ℝ) → ℂ := fun image => closedArm image q branch amp p r X k
  let G : Bool → (ℝ × ℝ) → ℂ := fun image hy =>
    if |(p-r)/2-(if image then -hy.2 else hy.2)| ≤ hy.1 then F image hy else 0
  have hF (image : Bool) : Continuous (F image) := closedArm_continuous image q branch amp p r X k
  have hG (image : Bool) : IntegrableOn (G image)
      (D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L) :=
    future_cone_cut_integrable (F image) (hF image) p r L hpr image
  have hcone (image : Bool) :
      (∫ hy in D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L,G image hy)=
      (∫ v in (if image then r else p)..r, ∫ u in r..L,F image ((v+u)/2-(p+r)/2,(v-u)/2)/2)+
      (∫ v in r..L, ∫ u in v..L,F image ((v+u)/2-(p+r)/2,(v-u)/2)/2) :=
    future_cone_cut_coordinates (F image) (hF image) p r L hpr hrL image
  calc
    _ = ∫ hy in D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L,G false hy-G true hy := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun hy => by
        simpa only [G,F,Bool.false_eq_true,↓reduceIte,sub_neg_eq_add] using
          density_gates q branch amp p r X k hy)
    _ = (∫ hy in D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L,G false hy)-
        ∫ hy in D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L,G true hy :=
      integral_sub (hG false) (hG true)
    _ = _ := by
      rw [hcone false,hcone true]
      simp only [F]
      simp_rw [closedArm_null,exponential_source_change]
      simp only [sub_self,Real.exp_zero]
      rfl

private theorem radial_clamp (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w X k v A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ z in A..B,compactMean image q branch amp r w X k v z)=
      ∫ z in A..B,compactMean image q branch amp r w X k v (max 0 z) := by
  apply intervalIntegral.integral_congr
  intro z hz
  exact congrArg (compactMean image q branch amp r w X k v)
    (max_eq_right ((le_min hA hB).trans hz.1)).symm

private theorem continuous_clamped_slice (F : ℝ → ℝ → ℂ)
    (hF : Continuous (fun vz : ℝ × ℝ => F vz.1 (max 0 vz.2))) (v : ℝ) :
    Continuous (fun z : ℝ => F v (max 0 z)) :=
  hF.comp (continuous_const.prodMk continuous_id)

private theorem radial_split (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w X k v A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ z in A..B,compactMean image q branch amp r w X k v z)=
      (∫ z in (0:ℝ)..B,compactMean image q branch amp r w X k v z)-
      (∫ z in (0:ℝ)..A,compactMean image q branch amp r w X k v z) := by
  rw [radial_clamp image q branch amp r w X k v A B hA hB,
    radial_clamp image q branch amp r w X k v 0 B le_rfl hB,
    radial_clamp image q branch amp r w X k v 0 A le_rfl hA]
  have hc : Continuous (fun z : ℝ => compactMean image q branch amp r w X k v (max 0 z)) :=
    continuous_clamped_slice (compactMean image q branch amp r w X k)
      (compactMean_clamped_continuous image q branch amp r w X k) v
  exact (intervalIntegral.integral_interval_sub_left
    (hc.intervalIntegrable 0 B) (hc.intervalIntegrable 0 A)).symm

private theorem primitive_continuous (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w X k : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (hp : ∀ v, 0 ≤ g v) :
    Continuous (fun v : ℝ => ∫ z in (0:ℝ)..(g v),compactMean image q branch amp r w X k v z) := by
  have hc : Continuous (fun v : ℝ => ∫ z in (0:ℝ)..(g v),
      compactMean image q branch amp r w X k v (max 0 z)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (compactMean_clamped_continuous image q branch amp r w X k) hg
  have he : (fun v : ℝ => ∫ z in (0:ℝ)..(g v),compactMean image q branch amp r w X k v z)=
      fun v : ℝ => ∫ z in (0:ℝ)..(g v),compactMean image q branch amp r w X k v (max 0 z) :=
    funext (fun v => radial_clamp image q branch amp r w X k v 0 (g v) le_rfl (hp v))
  rw [he]
  exact hc

private theorem upper_truncate (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w X k L M : ℝ) (hM : 1<M) (hML : M ≤ L) :
    (∫ v in r..L, ∫ z in (Real.exp (v-L))..1,compactMean image q branch amp r w X k v z)=
    ∫ v in r..M, ∫ z in (Real.exp (v-L))..1,compactMean image q branch amp r w X k v z := by
  have hA := primitive_continuous image q branch amp r w X k (fun _ => 1)
    continuous_const (fun _ => by norm_num)
  have hT := primitive_continuous image q branch amp r w X k (fun v => Real.exp (v-L))
    (by fun_prop) (fun v => (Real.exp_pos _).le)
  have he (v : ℝ) := radial_split image q branch amp r w X k v (Real.exp (v-L)) 1
    (Real.exp_pos _).le (by norm_num)
  have hJ : Continuous (fun v : ℝ => ∫ z in (Real.exp (v-L))..1,
      compactMean image q branch amp r w X k v z) := by
    simp_rw [he]
    exact hA.sub hT
  have hz : (∫ v in M..L, ∫ z in (Real.exp (v-L))..1,
      compactMean image q branch amp r w X k v z)=0 := by
    calc
      _ = ∫ v in M..L,(0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hv' : v ∈ Icc M L := by simpa only [uIcc_of_le hML] using hv
        have hv1 : v ∉ Icc (0:ℝ) 1 := fun h => (not_le_of_gt (hM.trans_le hv'.1)) h.2
        simp_rw [compactMean_zero_outside image q branch amp r w X k v _ hv1]
        simp
      _ = 0 := by simp
  have h := (intervalIntegral.integral_add_adjacent_intervals
    (hJ.intervalIntegrable (μ := volume) r M)
    (hJ.intervalIntegrable (μ := volume) M L)).symm
  simpa only [hz,add_zero] using h

private theorem cutArm_eq (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r L X k : ℝ) (hL : r+pulseSpan r ≤ L) :
    cutArm image q branch amp p r L X k=
      ((∫ v in (if image then r else p)..r, ∫ z in (0:ℝ)..(Real.exp (v-r)),
        compactMean image q branch amp r (r-p) X k v z)+
      upperIntegral image q branch amp r (r-p) (pulseSpan r) X k)-
      (∫ v in (if image then r else p)..r, ∫ z in (0:ℝ)..(Real.exp (v-L)),
        compactMean image q branch amp r (r-p) X k v z)-
      (∫ v in r..(r+pulseSpan r), ∫ z in (0:ℝ)..(Real.exp (v-L)),
        compactMean image q branch amp r (r-p) X k v z) := by
  have hM : 1<r+pulseSpan r := lt_of_lt_of_le (by norm_num) (pulseSpan_covers r)
  have hLow := primitive_continuous image q branch amp r (r-p) X k (fun v => Real.exp (v-r))
    (by fun_prop) (fun v => (Real.exp_pos _).le)
  have hUp := primitive_continuous image q branch amp r (r-p) X k (fun _ => 1)
    continuous_const (fun _ => by norm_num)
  have hTail := primitive_continuous image q branch amp r (r-p) X k (fun v => Real.exp (v-L))
    (by fun_prop) (fun v => (Real.exp_pos _).le)
  have heLow (v : ℝ) := radial_split image q branch amp r (r-p) X k v
    (Real.exp (v-L)) (Real.exp (v-r)) (Real.exp_pos _).le (Real.exp_pos _).le
  have heUp (v : ℝ) := radial_split image q branch amp r (r-p) X k v
    (Real.exp (v-L)) 1 (Real.exp_pos _).le (by norm_num)
  unfold cutArm
  rw [upper_truncate image q branch amp r (r-p) X k L (r+pulseSpan r) hM hL]
  simp_rw [heLow,heUp]
  rw [intervalIntegral.integral_sub (hLow.intervalIntegrable _ _) (hTail.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hUp.intervalIntegrable _ _) (hTail.intervalIntegrable _ _)]
  have hu : (∫ v in r..(r+pulseSpan r), ∫ z in (0:ℝ)..1,
      compactMean image q branch amp r (r-p) X k v z)=
      upperIntegral image q branch amp r (r-p) (pulseSpan r) X k := rfl
  rw [hu]
  ring

private theorem cutArm_limit (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) : Tendsto (fun L : ℝ => cutArm image q branch amp p r L X k) atTop
      (𝓝 ((∫ v in (if image then r else p)..r, ∫ z in (0:ℝ)..(Real.exp (v-r)),
        compactMean image q branch amp r (r-p) X k v z)+
      upperIntegral image q branch amp r (r-p) (pulseSpan r) X k)) := by
  have h0 := compactMean_cut_tail image q branch amp r (r-p) X k (if image then r else p) r
  have h1 := compactMean_cut_tail image q branch amp r (r-p) X k r (r+pulseSpan r)
  let C : ℂ := (∫ v in (if image then r else p)..r, ∫ z in (0:ℝ)..(Real.exp (v-r)),
    compactMean image q branch amp r (r-p) X k v z)+
    upperIntegral image q branch amp r (r-p) (pulseSpan r) X k
  have h := ((show Tendsto (fun _ : ℝ => C) atTop (𝓝 C) from tendsto_const_nhds).sub h0).sub h1
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (r+pulseSpan r)] with L hL
  exact (cutArm_eq image q branch amp p r L X k hL).symm

/-- The admitted original future pulse equals its full compact source formula. -/
theorem response_eq_compactFutureAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : Fin 4 → ℝ) :
    D4BMFuturePulseAdmission.response q branch amp (z 0-Real.exp (z 1)/2) (-Real.exp (z 1)/2)
      (z 2) (z 3)=compactFutureAction q branch amp z := by
  let p := z 0-Real.exp (z 1)
  let r := z 0
  have hpr : p ≤ r := by dsimp only [p,r]; linarith [Real.exp_pos (z 1)]
  have hd := cutArm_limit false q branch amp p r (z 2) (z 3)
  have hi := cutArm_limit true q branch amp p r (z 2) (z 3)
  have ht := hd.sub hi
  simp only [Bool.false_eq_true,↓reduceIte,intervalIntegral.integral_same,zero_add] at ht
  have hc :
      ((∫ v in p..r, ∫ u in (0:ℝ)..(Real.exp (v-r)),
        compactMean false q branch amp r (r-p) (z 2) (z 3) v u)+
        upperIntegral false q branch amp r (r-p) (pulseSpan r) (z 2) (z 3))-
        upperIntegral true q branch amp r (r-p) (pulseSpan r) (z 2) (z 3)=
      compactFutureAction q branch amp z := by
    dsimp only [p,r]
    rw [show z 0-(z 0-Real.exp (z 1))=Real.exp (z 1) by ring]
    rfl
  rw [hc] at ht
  have hcut : Tendsto
      (D4BMFuturePulseAdmission.truncatedResponse q branch amp ((p+r)/2) ((p-r)/2) (z 2) (z 3))
      atTop (𝓝 (compactFutureAction q branch amp z)) := by
    apply ht.congr'
    filter_upwards [eventually_ge_atTop r] with L hL
    exact (original_cut_eq_compact_cut q branch amp p r L (z 2) (z 3) hpr hL).symm
  have he := tendsto_nhds_unique
    (D4BMFuturePulseAdmission.truncatedResponse_limit q branch amp ((p+r)/2) ((p-r)/2) (z 2) (z 3)) hcut
  dsimp only [p,r] at he
  rwa [show (z 0-Real.exp (z 1)+z 0)/2=z 0-Real.exp (z 1)/2 by ring,
    show (z 0-Real.exp (z 1)-z 0)/2=-Real.exp (z 1)/2 by ring] at he

/-- Every derivative of the original full future pulse exists in physical interior coordinates. -/
theorem original_response_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (fun z : Fin 4 → ℝ =>
      D4BMFuturePulseAdmission.response q branch amp (z 0-Real.exp (z 1)/2) (-Real.exp (z 1)/2)
        (z 2) (z 3)) := by
  have he : (fun z : Fin 4 → ℝ =>
      D4BMFuturePulseAdmission.response q branch amp (z 0-Real.exp (z 1)/2) (-Real.exp (z 1)/2)
        (z 2) (z 3))=compactFutureAction q branch amp :=
    funext (response_eq_compactFutureAction q branch amp)
  rw [he]
  exact compactFutureAction_smooth q branch amp

end
end RHTower.D4BMFuturePulseIdentity

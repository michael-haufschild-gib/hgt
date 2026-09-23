import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceTimeFlux

/-! Source-time admission of the original improper radial Green transfer.
Both angular divergences and the direct/image characteristic signs are retained. -/
open Set Filter Topology MeasureTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMSourceTimeInterchange
open D4BMCommonSourceGreen D4BMSourceTimeFlux D4BMJointSource


/-- The actual signed truncated radial source-transfer integrals at source time `v`. -/
def truncatedRadialTransfer (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T target X k epsilon v : ℝ) : ℂ :=
  (∫ y in fractionalSourceCutoff false (T-v) target epsilon..0,
    radialTransferDensity q branch a v false (T-v) target X k y)-
  (∫ y in fractionalSourceCutoff true (T-v) target epsilon..0,
    radialTransferDensity q branch a v true (T-v) target X k y)

/-- Source-time integral of the actual truncated radial Green transfer. -/
def sourceTimeTruncatedTransfer (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T target X k epsilon : ℝ) : ℂ :=
  ∫ v in (0:ℝ)..T, truncatedRadialTransfer q branch a T target X k epsilon v

private def clip (d v : ℝ) : ℝ := max 0 (min d v)

private theorem clip_mem {d : ℝ} (hd : 0 ≤ d) (v : ℝ) : clip d v ∈ Icc 0 d :=
  ⟨le_max_left _ _,max_le hd (min_le_left _ _)⟩

private theorem clip_eq {d v : ℝ} (hv : v ∈ Icc 0 d) : clip d v=v := by
  simp only [clip,min_eq_right hv.2,max_eq_right hv.1]

private def clippedPair (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T target X k : ℝ) (z : ℝ × ℝ) : ℂ :=
  sourceCutoffTrace q branch a true T target X k (clip T z.1,clip (1/2) z.2)-
  sourceCutoffTrace q branch a false T target X k (clip T z.1,clip (1/2) z.2)

private theorem clippedPair_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T : Ici (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ) :
    Continuous (clippedPair q branch a T.val target.val X k) := by
  have hc : Continuous (fun z : ℝ × ℝ => (clip T.val z.1,clip (1/2) z.2)) := by
    unfold clip
    fun_prop
  have hm (z : ℝ × ℝ) : (clip T.val z.1,clip (1/2) z.2) ∈
      Icc (0:ℝ) T.val ×ˢ Icc (0:ℝ) (1/2) :=
    ⟨clip_mem T.property z.1,clip_mem (by norm_num) z.2⟩
  exact ((sourceCutoffTrace_continuousOn q branch a true T target X k).comp_continuous hc hm).sub
    ((sourceCutoffTrace_continuousOn q branch a false T target X k).comp_continuous hc hm)

private theorem fractionalCut_mem (image : Bool) (h : Ioi (0:ℝ)) (target : Iio (0:ℝ))
    (epsilon : Ioo (0:ℝ) (1/2)) :
    fractionalSourceCutoff image h.val target.val epsilon.val ∈
      Ioo (sourceCharacteristic image h.val target.val) 0 := by
  have hh : 0 < h.val := h.property
  have hx : target.val < 0 := target.property
  have he : sourceCharacteristic image h.val target.val < 0 := by
    cases image <;> simp only [sourceCharacteristic,Bool.false_eq_true,if_false,if_true]
    all_goals linarith
  have ep : 0 < epsilon.val := epsilon.property.1
  have eq : epsilon.val < 1/2 := epsilon.property.2
  unfold fractionalSourceCutoff
  constructor
  · nlinarith [mul_neg_of_pos_of_neg ep he]
  · exact mul_neg_of_pos_of_neg (by linarith) he

private theorem truncatedRadialTransfer_eq_trace (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T : Ici (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ) (epsilon : Ioo (0:ℝ) (1/2))
    {v : ℝ} (hv : v ∈ Ioo 0 T.val) :
    truncatedRadialTransfer q branch a T.val target.val X k epsilon.val v =
      clippedPair q branch a T.val target.val X k (v,epsilon.val) := by
  let h : Ioi (0:ℝ) := ⟨T.val-v,sub_pos.mpr hv.2⟩
  have hd := sourceRadialTransfer_integral q branch a v false h target X k
    ⟨_,fractionalCut_mem false h target epsilon⟩
  have hi := sourceRadialTransfer_integral q branch a v true h target X k
    ⟨_,fractionalCut_mem true h target epsilon⟩
  have heps : epsilon.val ∈ Icc (0:ℝ) (1/2) := ⟨epsilon.property.1.le,epsilon.property.2.le⟩
  unfold truncatedRadialTransfer
  rw [hd,hi]
  simp only [clippedPair,clip_eq ⟨hv.1.le,hv.2.le⟩,clip_eq heps,sourceCutoffTrace]
  dsimp only [h]
  ring

/-- The time-integrated original truncated source/transpose density is genuinely
integrable for every interior fractional cutoff; no regularity premise is supplied. -/
theorem sourceTimeTruncatedTransfer_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T : Ici (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ) (epsilon : Ioo (0:ℝ) (1/2)) :
    IntervalIntegrable (truncatedRadialTransfer q branch a T.val target.val X k epsilon.val)
      volume 0 T.val := by
  have hc : Continuous (fun v => clippedPair q branch a T.val target.val X k (v,epsilon.val)) :=
    (clippedPair_continuous q branch a T target X k).comp (continuous_id.prodMk continuous_const)
  apply (hc.intervalIntegrable 0 T.val).congr_uIoo
  intro v hv
  have hv' : v ∈ Ioo (0:ℝ) T.val := by simpa only [uIoo_of_le (show (0:ℝ) ≤ T.val from T.property)] using hv
  exact (truncatedRadialTransfer_eq_trace q branch a T target X k epsilon hv').symm

private theorem timeTransfer_eq_trace (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T : Ici (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ) (epsilon : Ioo (0:ℝ) (1/2)) :
    sourceTimeTruncatedTransfer q branch a T.val target.val X k epsilon.val =
      ∫ v in (0:ℝ)..T.val, clippedPair q branch a T.val target.val X k (v,epsilon.val) := by
  apply intervalIntegral.integral_congr_Ioo_of_le T.property
  intro v hv
  exact truncatedRadialTransfer_eq_trace q branch a T target X k epsilon hv

private theorem radialTrace_at_zero (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (image : Bool) (h target X k : ℝ) :
    sourceRadialTraceCurrent q branch a v image h target X k 0=0 := by
  change (radialUnit (0:ℝ):ℂ)^(4 : ℕ)*(1+(radialUnit (0:ℝ):ℂ))*_=0
  simp [radialUnit]

private theorem clippedPair_zero (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T : Ici (0:ℝ)) (target X k : ℝ) {v : ℝ} (hv : v ∈ Icc 0 T.val) :
    clippedPair q branch a T.val target X k (v,0)=
      signedRadialFace q branch a v (T.val-v) target X k := by
  simp only [clippedPair,clip_eq hv,clip_eq (show (0:ℝ) ∈ Icc 0 (1/2) by norm_num),
    sourceCutoffTrace,fractionalSourceCutoff,sub_zero,one_mul,signedRadialFace,
    radialTrace_at_zero,zero_sub]
  ring

/-- Source-time integration commutes with this original improper radial transfer.
The moving direct and image characteristics, both angular divergences, original
onset and full spin-two coupling are retained. -/
theorem sourceTimeTruncatedTransfer_tendsto (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T : Ici (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ) :
    Tendsto (sourceTimeTruncatedTransfer q branch a T.val target.val X k)
      (𝓝[>] (0:ℝ)) (𝓝 (sourceTimeRadialFlux q branch a target.val X k T.val)) := by
  have hc : Continuous (Function.uncurry (fun epsilon v : ℝ =>
      clippedPair q branch a T.val target.val X k (v,epsilon))) :=
    (clippedPair_continuous q branch a T target X k).comp continuous_swap
  have hi := intervalIntegral.continuous_parametric_primitive_of_continuous
    (a₀ := (0:ℝ)) (μ := volume) hc
  have ht : Tendsto (fun epsilon : ℝ => ∫ v in (0:ℝ)..T.val,
      clippedPair q branch a T.val target.val X k (v,epsilon)) (𝓝[>] (0:ℝ))
      (𝓝 (∫ v in (0:ℝ)..T.val, clippedPair q branch a T.val target.val X k (v,0))) :=
    ((hi.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => T.val)))).tendsto 0).mono_left inf_le_left
  have he : (∫ v in (0:ℝ)..T.val, clippedPair q branch a T.val target.val X k (v,0))=
      sourceTimeRadialFlux q branch a target.val X k T.val := by
    apply intervalIntegral.integral_congr
    intro v hv
    apply clippedPair_zero q branch a T target.val X k
    simpa only [uIcc_of_le (show (0:ℝ) ≤ T.val from T.property)] using hv
  rw [he] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with epsilon heps
  exact (timeTransfer_eq_trace q branch a T target X k ⟨epsilon,heps⟩).symm

/-- The admitted original radial transfer obeys the uniform quantitative bound. -/
theorem sourceTimeTruncatedTransfer_limit_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T : Ici (0:ℝ)) (target : Iio (0:ℝ)) (X k : ℝ) :
    ‖limUnder (𝓝[>] (0:ℝ)) (sourceTimeTruncatedTransfer q branch a T.val target.val X k)‖ ≤
      sourceTimeFluxBound q branch a X k*Real.exp (-T.val) := by
  rw [(sourceTimeTruncatedTransfer_tendsto q branch a T target X k).limUnder_eq]
  exact sourceTimeRadialFlux_exp_bound q branch a ⟨target.val,show target.val ≤ 0 from (show target.val < 0 from target.property).le⟩ X k T

/-- After admitting the original radial source integral, its full causal
source-time transfer decays along every exterior target-radius path. -/
theorem sourceTimeTruncatedTransfer_limit_tendsto_zero (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (target : ℝ → Iio (0:ℝ)) (X k : ℝ) :
    Tendsto (fun T : ℝ => limUnder (𝓝[>] (0:ℝ))
      (sourceTimeTruncatedTransfer q branch a T (target T).val X k)) atTop (𝓝 (0:ℂ)) := by
  have h := sourceTimeRadialFlux_tendsto_zero q branch a
    (fun T => ⟨(target T).val,show (target T).val ≤ 0 from (show (target T).val < 0 from (target T).property).le⟩) X k
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  exact (sourceTimeTruncatedTransfer_tendsto q branch a ⟨T,hT⟩ (target T) X k).limUnder_eq.symm

end RHTower.D4BMSourceTimeInterchange

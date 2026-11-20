import GaloisForLFunctions.ExceptionalLayerTheory.TheLandingLawForZeta
import GaloisForLFunctions.RHTower.XiLogDerivReFalsification

/-!
# The height error in the threshold of Hadamard positivity

An ordinate of a zero to the right of a cut is also an ordinate of a
negative logarithmic derivative to its right. Conversely a negative
reading lies in the open disk of a still deeper right zero. Splitting
these disks by depth, as in the small and large scale decomposition of
Borrin–Nariyoshi (arXiv:2608.08337, §6), makes the height error tend to
zero whenever the heights diverge under the zero approach law.
-/

open Complex Set Filter Topology Zeta23
open RHTower RHTower.BacklundConverse RHTower.LindelofSparse RHTower.DeBruijn
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem negative_nonzero {s : ℂ} (h : (logDeriv xi s).re < 0) : xi s ≠ 0 := by
  intro he
  rw [logDeriv_xi_eq_zero_of_xi_eq_zero he,Complex.zero_re] at h
  exact (lt_irrefl _) h

/-- A negative reading lies strictly inside a disk belonging to a zero
strictly to its right; its ordinate distance is less than that zero's depth. -/
theorem negative_reading_has_deeper_zero {s : ℂ} (hs : 1/2 < s.re) (hn : (logDeriv xi s).re < 0) :
    ∃ q : XiZeroCopy, s.re < (q.1:ℂ).re ∧
      (s.re-1/2)^2+(s.im-(q.1:ℂ).im)^2 < ((q.1:ℂ).re-1/2)^2 := by
  have han := xi_differentiable.analyticAt s
  have hc : ContinuousAt (logDeriv xi) s :=
    han.deriv.continuousAt.div han.continuousAt (negative_nonzero hn)
  have hshift : Tendsto (fun u : ℝ => s+(u:ℂ)) (𝓝[>] 0) (𝓝 s) := by
    simpa only [Complex.ofReal_zero,add_zero] using
      ((tendsto_const_nhds (x:=s)).add (Complex.continuous_ofReal.tendsto (0:ℝ))).mono_left
        (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hneg := (Complex.continuous_re.continuousAt.tendsto.comp (hc.tendsto.comp hshift)).eventually_lt_const hn
  obtain ⟨u,hu,hu'⟩ := ((eventually_mem_nhdsWithin (s := Ioi (0:ℝ)) (a := 0)).and hneg).exists
  have hu₀ : 0 < u := hu
  have hs' : 1/2 < (s+(u:ℂ)).re := by
    simpa only [Complex.add_re,Complex.ofReal_re] using hs.trans (lt_add_of_pos_right _ hu₀)
  obtain ⟨q,hq⟩ := exists_zero_disk_of_re_logDeriv_xi_neg hs' (negative_nonzero hu') hu'
  simp only [Complex.add_re,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,add_zero] at hq
  have hx := (sq_lt_sq₀ (sub_nonneg.mpr hs.le) (by linarith only [hs,hu₀] : 0 ≤ s.re+u-1/2)).mpr
    (by linarith only [hu₀] : s.re-1/2 < s.re+u-1/2)
  have hsq : (s.re-1/2)^2+(s.im-(q.1:ℂ).im)^2 < ((q.1:ℂ).re-1/2)^2 := by linarith only [hq,hx]
  have right (p : XiZeroCopy) (hp : 1/2 ≤ (p.1:ℂ).re)
      (hd : (s.re-1/2)^2+(s.im-(p.1:ℂ).im)^2 < ((p.1:ℂ).re-1/2)^2) : s.re < (p.1:ℂ).re := by
    have h := (sq_lt_sq₀ (sub_nonneg.mpr hs.le) (sub_nonneg.mpr hp)).mp
      (by linarith only [hd,sq_nonneg (s.im-(p.1:ℂ).im)])
    linarith only [h]
  by_cases hp : 1/2 ≤ (q.1:ℂ).re
  · exact ⟨q,right q hp hsq,hsq⟩
  let p := xiZeroCopyLineConjEquiv q
  have he : (p.1:ℂ) = 1-(starRingEnd ℂ) (q.1:ℂ) := xiZero_lineConj_eq q
  have hr : (p.1:ℂ).re = 1-(q.1:ℂ).re := by rw [he]; simp
  have hi : (p.1:ℂ).im = (q.1:ℂ).im := by rw [he]; simp
  have hd : (s.re-1/2)^2+(s.im-(p.1:ℂ).im)^2 < ((p.1:ℂ).re-1/2)^2 := by
    rw [hi,hr]; linarith only [hsq]
  exact ⟨p,right p (by rw [hr]; linarith only [le_of_not_ge hp]) hd,hd⟩

private theorem near_deeper_zero {s : ℂ} (hs : 1/2 < s.re) (hn : (logDeriv xi s).re < 0) :
    ∃ q : XiZeroCopy, s.re < (q.1:ℂ).re ∧ |s.im-(q.1:ℂ).im| < (q.1:ℂ).re-1/2 := by
  obtain ⟨q,hq,hd⟩ := negative_reading_has_deeper_zero hs hn
  refine ⟨q,hq,(sq_lt_sq₀ (abs_nonneg _) (sub_nonneg.mpr (hs.trans hq).le)).mp ?_⟩
  rw [sq_abs]
  linarith only [hd,sq_nonneg (s.re-1/2)]

private theorem depth_lt_half (q : XiZeroCopy) : (q.1:ℂ).re-1/2 < 1/2 := by
  have h := abs_spectral_im_lt_half q
  rw [spectral_im_eq,abs_sub_comm] at h
  exact (le_abs_self _).trans_lt h

/-- Under the zero approach law all late negative readings have a deeper
right zero at ordinate distance below any prescribed positive tolerance. -/
theorem high_negative_readings_have_vanishing_height_error (hZ : ZerosApproachLine)
    {ε : ℝ} (hε : 0 < ε) : ∃ T : ℝ, ∀ s : ℂ, 1/2 < s.re → T ≤ |s.im| →
      (logDeriv xi s).re < 0 → ∃ q : XiZeroCopy, s.re < (q.1:ℂ).re ∧ |s.im-(q.1:ℂ).im| < ε := by
  obtain ⟨B,hB⟩ := ((finite_abs_im_gt_of_zerosApproachLine hZ (half_pos hε)).image
    fun q => |(q.1:ℂ).im|).bddAbove
  refine ⟨B+1,fun s hs ht hn => ?_⟩
  obtain ⟨q,hq,hd⟩ := near_deeper_zero hs hn
  refine ⟨q,hq,?_⟩
  by_contra! hh
  have hspect : ε/2 < |(xiSpectralPoint q).im| := by
    rw [spectral_im_eq,abs_sub_comm,abs_of_pos (sub_pos.mpr (hs.trans hq))]
    linarith only [hh,hd,hε]
  have hγ := hB ⟨q,hspect,rfl⟩
  have htriangle := abs_sub_abs_le_abs_sub s.im (q.1:ℂ).im
  linarith only [hγ,htriangle,ht,hd,depth_lt_half q]

/-- Highest absolute ordinate of zeros strictly right of the cut, with zero
as the initial height. Under the approach law this is a finite maximum. -/
def topRightOrdinate (σ : ℝ) : ℝ :=
  sSup (insert 0 ((fun q : XiZeroCopy => |(q.1:ℂ).im|) '' {q | σ < (q.1:ℂ).re}))

private theorem height_blocks_zero {T σ : ℝ} (hT : T ∈ hadamardThresholdSet σ)
    (q : XiZeroCopy) (hq : σ < (q.1:ℂ).re) : |(q.1:ℂ).im| < T := by
  obtain ⟨u,_,hu,hn⟩ := exists_re_logDeriv_xi_neg_near_zero (xi_xiZeroCopy_eq_zero q) (sub_pos.mpr hq)
  by_contra! h
  apply (not_le_of_gt hn) (hT.2 _ ?_ ?_)
  · simp only [Complex.sub_re,Complex.ofReal_re]; linarith only [hu]
  · simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using h

private theorem top_le_budget {T σ : ℝ} (hT : T ∈ hadamardThresholdSet σ) :
    topRightOrdinate σ ≤ T := by
  apply csSup_le (insert_nonempty ..)
  rintro _ (rfl | ⟨q,hq,rfl⟩)
  · exact hT.1
  · exact (height_blocks_zero hT q hq).le

private theorem top_set_bdd {σ : ℝ} (hE : EventualHadamardPositivity) (hσ : 1/2 < σ) :
    BddAbove (insert 0 ((fun q : XiZeroCopy => |(q.1:ℂ).im|) '' {q | σ < (q.1:ℂ).re})) := by
  obtain ⟨T,hT⟩ := hadamardThresholdSet_nonempty hE hσ
  refine ⟨T,?_⟩
  rintro _ (rfl | ⟨q,hq,rfl⟩)
  · exact hT.1
  · exact (height_blocks_zero hT q hq).le

/-- The threshold lies within half a height unit of the highest deeper
zero. Both bounds apply to the original closed half-plane cut. -/
theorem hadamard_threshold_height_bracket (hE : EventualHadamardPositivity) {σ : ℝ} (hσ : 1/2 < σ) :
    topRightOrdinate σ ≤ hadamardThreshold σ ∧ hadamardThreshold σ ≤ topRightOrdinate σ + 1/2 := by
  have hb := top_set_bdd hE hσ
  have hn : 0 ≤ topRightOrdinate σ := le_csSup hb (mem_insert ..)
  refine ⟨le_csInf (hadamardThresholdSet_nonempty hE hσ) (fun _ => top_le_budget),
    csInf_le (bddBelow_hadamardThresholdSet σ) ⟨by linarith only [hn],fun s hs ht => ?_⟩⟩
  by_contra! h
  obtain ⟨q,hq,hd⟩ := near_deeper_zero (hσ.trans_le hs) h
  have hγ : |(q.1:ℂ).im| ≤ topRightOrdinate σ :=
    le_csSup hb (mem_insert_of_mem _ ⟨q,hs.trans_lt hq,rfl⟩)
  linarith only [ht,hd,depth_lt_half q,hγ,abs_sub_abs_le_abs_sub s.im (q.1:ℂ).im]

/-- On any family of cuts along which the highest deeper zero escapes, the
absolute height difference between that zero and the Hadamard threshold
converges to zero. No regularity or spacing of the selected cuts is needed. -/
theorem hadamard_threshold_additive_asymptotic {ι : Type*} {l : Filter ι} {σ : ι → ℝ}
    (hZ : ZerosApproachLine) (hσ : ∀ᶠ i in l, 1/2 < σ i)
    (hh : Tendsto (fun i => topRightOrdinate (σ i)) l atTop) :
    Tendsto (fun i => hadamardThreshold (σ i)-topRightOrdinate (σ i)) l (𝓝 0) := by
  have hE := eventualHadamardPositivity_iff_zerosApproachLine.mpr hZ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T,hT⟩ := high_negative_readings_have_vanishing_height_error hZ (half_pos hε)
  filter_upwards [hσ,hh.eventually_ge_atTop T] with i hi hiT
  have hb := top_set_bdd hE hi
  have hn : 0 ≤ topRightOrdinate (σ i) := le_csSup hb (mem_insert ..)
  have hu : hadamardThreshold (σ i) ≤ topRightOrdinate (σ i)+ε/2 := by
    apply csInf_le (bddBelow_hadamardThresholdSet _) ⟨by linarith only [hn,hε],?_⟩
    intro s hs ht
    by_contra! h
    obtain ⟨q,hq,hd⟩ := hT s (hi.trans_le hs) (by linarith only [ht,hiT,hε]) h
    have hγ : |(q.1:ℂ).im| ≤ topRightOrdinate (σ i) :=
      le_csSup hb (mem_insert_of_mem _ ⟨q,hs.trans_lt hq,rfl⟩)
    linarith only [ht,hd,hγ,abs_sub_abs_le_abs_sub s.im (q.1:ℂ).im]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (sub_nonneg.mpr (hadamard_threshold_height_bracket hE hi).1)]
  linarith only [hu,hε]

/-- On the actual failure branch for landing, the highest deeper ordinates
diverge while their additive discrepancy from the positivity threshold
tends to zero as the cuts approach the line. -/
theorem failure_of_landing_forces_additive_tracking :
    ¬ ZetaLandingLaw →
      Tendsto topRightOrdinate (𝓝[>] (1/2:ℝ)) atTop ∧
      Tendsto (fun σ => hadamardThreshold σ-topRightOrdinate σ) (𝓝[>] (1/2:ℝ)) (𝓝 0) := by
  classical
  intro h
  rw [ZetaLandingLaw,_root_.not_imp] at h
  obtain ⟨hZ,hF⟩ := h
  have hE := eventualHadamardPositivity_iff_zerosApproachLine.mpr hZ
  have high (A : ℝ) : ∃ q : XiZeroCopy, 1/2 < (q.1:ℂ).re ∧ A < |(q.1:ℂ).im| := by
    by_contra! hh
    apply hF (eventualHadamardPositivityRight_half_iff_finiteOffLine.mp ⟨A+1,?_⟩)
    intro s hs ht
    by_contra! hneg
    obtain ⟨q,hq,hd⟩ := near_deeper_zero hs hneg
    linarith only [hh q (hs.trans hq),hd,depth_lt_half q,ht,abs_sub_abs_le_abs_sub s.im (q.1:ℂ).im]
  have ht : Tendsto topRightOrdinate (𝓝[>] (1/2:ℝ)) atTop := by
    apply tendsto_atTop.mpr
    intro A
    obtain ⟨q,hq,hγ⟩ := high A
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hq)] with σ hσ hcut
    exact hγ.le.trans (le_csSup (top_set_bdd hE hσ) (mem_insert_of_mem _ ⟨q,hcut,rfl⟩))
  exact ⟨ht,hadamard_threshold_additive_asymptotic hZ self_mem_nhdsWithin ht⟩

#print axioms failure_of_landing_forces_additive_tracking
#print axioms negative_reading_has_deeper_zero
#print axioms high_negative_readings_have_vanishing_height_error
#print axioms hadamard_threshold_height_bracket
#print axioms hadamard_threshold_additive_asymptotic

end GaloisForLFunctions.ExceptionalLayerTheory

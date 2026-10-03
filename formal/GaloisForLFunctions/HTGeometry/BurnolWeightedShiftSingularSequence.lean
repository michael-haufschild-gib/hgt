import GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability

/-!
# Unimodular singular sequences of the Burnol weighted shift

For `h > 0`, `|η| = 1`, `η = e^{iθ}`, `N ≥ 2`, `R = N²h`, `L = Nh`, the packets
`u_N(t) = L^{-1/2} e^{iθt/h} 1_{[R,R+L)}(t)` are unit vectors, weakly null, and satisfy
`‖(K_h - η) u_N‖ ≤ √(2/N) + 1/N²`.  Consequently `‖K_h‖ = 1`, and for every compact `C`,
`‖(K_h + C - η) u_N‖ → 0`: compact perturbations cannot remove the boundary obstruction.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

/-! ## Real weights and cutoffs -/

theorem norm_ofReal_indicator_one_le (s : Set ℝ) (t : ℝ) (_ : 0 < t) :
    ‖((s.indicator (fun _ => (1 : ℝ)) t : ℝ) : ℂ)‖ ≤ 1 := by
  by_cases ht : t ∈ s <;> simp [ht]

/-- Multiplication by the cutoff `1_{[a,∞)}`. -/
def halfLineCutoff (a : ℝ) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  weightedLeftShift 0 (fun t => (((Ici a).indicator (fun _ => (1 : ℝ)) t : ℝ) : ℂ))
    (by
      refine Complex.measurable_ofReal.comp ?_
      exact measurable_const.indicator measurableSet_Ici)
    (norm_ofReal_indicator_one_le (Ici a))

theorem halfLineCutoff_coeFn (a : ℝ) (f : BurnolHalfLineL2) :
    (halfLineCutoff a f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => (((Ici a).indicator (fun _ => (1 : ℝ)) t : ℝ) : ℂ) * (f : ℝ → ℂ) t := by
  filter_upwards [weightedLeftShift_coeFn 0 _ (norm_ofReal_indicator_one_le (Ici a)) f] with t ht
  rw [halfLineCutoff, ht, NNReal.coe_zero, add_zero]

theorem adjoint_halfLineCutoff (a : ℝ) :
    ContinuousLinearMap.adjoint (halfLineCutoff a) = halfLineCutoff a := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun g f => ?_).symm
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [halfLineCutoff_coeFn a f, halfLineCutoff_coeFn a g] with s hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem norm_sq_halfLineCutoff (a : ℝ) (f : BurnolHalfLineL2) :
    ‖halfLineCutoff a f‖ ^ 2 = ∫ t in Ioi (0 : ℝ), (Ici a).indicator (fun t => ‖(f : ℝ → ℂ) t‖ ^ 2) t := by
  rw [Lp_two_norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [halfLineCutoff_coeFn a f] with t ht
  rw [ht]
  by_cases hmem : t ∈ Ici a <;> simp [hmem]

/-- The tail energy `∫_{t ≥ a} |f|²` of an `L²` class tends to zero as `a → ∞`. -/
theorem tendsto_norm_halfLineCutoff (f : BurnolHalfLineL2) {a : ℕ → ℝ}
    (ha : Monotone a) (hat : Tendsto a atTop atTop) :
    Tendsto (fun n => ‖halfLineCutoff (a n) f‖) atTop (𝓝 0) := by
  have hint : Integrable (fun t => ‖(f : ℝ → ℂ) t‖ ^ 2) (volume.restrict (Ioi 0)) :=
    integrable_norm_sq_burnol f
  have hset := tendsto_setIntegral_of_antitone (μ := volume.restrict (Ioi 0))
    (f := fun t => ‖(f : ℝ → ℂ) t‖ ^ 2) (s := fun n => Ici (a n))
    (fun n => measurableSet_Ici) (fun m n hmn => Ici_subset_Ici.2 (ha hmn)) ⟨0, hint.integrableOn⟩
  have hempty : (⋂ n, Ici (a n)) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun t ht => ?_
    obtain ⟨n, hn⟩ := (hat.eventually_gt_atTop t).exists
    exact absurd (mem_iInter.1 ht n) (by simp only [mem_Ici, not_le]; exact hn)
  rw [hempty, Measure.restrict_empty, integral_zero_measure] at hset
  have hsq : Tendsto (fun n => ‖halfLineCutoff (a n) f‖ ^ 2) atTop (𝓝 0) := by
    refine hset.congr fun n => ?_
    rw [norm_sq_halfLineCutoff, integral_indicator measurableSet_Ici]
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-! ## The packets -/

/-- The packet start `R = (N+2)² h`. -/
def singularPacketStart (h : ℝ≥0) (N : ℕ) : ℝ := ((N : ℝ) + 2) ^ 2 * h

/-- The packet length `L = (N+2) h`. -/
def singularPacketLength (h : ℝ≥0) (N : ℕ) : ℝ := ((N : ℝ) + 2) * h

/-- The phase `e^{iθt/h}`. -/
def singularPacketPhase (h : ℝ≥0) (θ t : ℝ) : ℂ := Complex.exp (((θ * t / h : ℝ) : ℂ) * Complex.I)

/-- The packet `L^{-1/2} e^{iθt/h} 1_{[R,R+L)}(t)`. -/
def singularPacketFun (h : ℝ≥0) (θ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  (Ico (singularPacketStart h N) (singularPacketStart h N + singularPacketLength h N)).indicator
    (fun t => (((Real.sqrt (singularPacketLength h N))⁻¹ : ℝ) : ℂ) * singularPacketPhase h θ t) t

theorem norm_packetPhase (h : ℝ≥0) (θ t : ℝ) : ‖singularPacketPhase h θ t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem packetLength_pos {h : ℝ≥0} (hh : 0 < h) (N : ℕ) : 0 < singularPacketLength h N := by
  unfold singularPacketLength
  have : (0 : ℝ) < h := hh
  positivity

theorem packetStart_pos {h : ℝ≥0} (hh : 0 < h) (N : ℕ) : 0 < singularPacketStart h N := by
  unfold singularPacketStart
  have : (0 : ℝ) < h := hh
  positivity

theorem norm_sq_packetFun {h : ℝ≥0} (hh : 0 < h) (θ : ℝ) (N : ℕ) (t : ℝ) :
    ‖singularPacketFun h θ N t‖ ^ 2 =
      (Ico (singularPacketStart h N) (singularPacketStart h N + singularPacketLength h N)).indicator
        (fun _ => (singularPacketLength h N)⁻¹) t := by
  unfold singularPacketFun
  by_cases hmem : t ∈ Ico (singularPacketStart h N) (singularPacketStart h N + singularPacketLength h N)
  · rw [indicator_of_mem hmem, indicator_of_mem hmem, norm_mul, norm_packetPhase, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_pow,
      Real.sq_sqrt (packetLength_pos hh N).le]
  · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, norm_zero, zero_pow two_ne_zero]

theorem continuous_packetPhase (h : ℝ≥0) (θ : ℝ) : Continuous (singularPacketPhase h θ) := by
  unfold singularPacketPhase
  fun_prop

theorem memLp_packetFun (h : ℝ≥0) (θ : ℝ) (N : ℕ) :
    MemLp (singularPacketFun h θ N) 2 (volume.restrict (Ioi 0)) := by
  unfold singularPacketFun
  rw [memLp_indicator_iff_restrict measurableSet_Ico]
  haveI : IsFiniteMeasure ((volume.restrict (Ioi (0 : ℝ))).restrict
      (Ico (singularPacketStart h N) (singularPacketStart h N + singularPacketLength h N))) := by
    refine isFiniteMeasure_restrict.2 ?_
    rw [Measure.restrict_apply measurableSet_Ico]
    exact ne_top_of_le_ne_top (by simp [Real.volume_Ico]) (measure_mono inter_subset_left)
  refine MemLp.of_bound ((continuous_const.mul (continuous_packetPhase h θ)).aestronglyMeasurable)
    ((Real.sqrt (singularPacketLength h N))⁻¹) (Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_packetPhase, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- The unit singular packet `u_N`. -/
def singularPacket (h : ℝ≥0) (θ : ℝ) (N : ℕ) : BurnolHalfLineL2 :=
  (memLp_packetFun h θ N).toLp (singularPacketFun h θ N)

theorem singularPacket_coeFn (h : ℝ≥0) (θ : ℝ) (N : ℕ) :
    (singularPacket h θ N : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] singularPacketFun h θ N :=
  (memLp_packetFun h θ N).coeFn_toLp

theorem measureReal_Ico_of_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (volume.restrict (Ioi (0 : ℝ))).real (Ico a b) = b - a := by
  rw [measureReal_restrict_apply measurableSet_Ico, Measure.real]
  have hsub : Ico a b ∩ Ioi 0 ⊆ Ico a b := inter_subset_left
  by_cases ha0 : a = 0
  · subst ha0
    have : Ico 0 b ∩ Ioi 0 = Ioo 0 b := by
      ext x
      simp only [mem_inter_iff, mem_Ico, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1.le, h2⟩, h1⟩
    rw [this, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
  · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [inter_eq_left.2 (show Ico a b ⊆ Ioi 0 from fun x hx => lt_of_lt_of_le hpos hx.1),
      Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]

/-- **Unit packets.**  `‖u_N‖ = 1`. -/
theorem norm_singularPacket {h : ℝ≥0} (hh : 0 < h) (θ : ℝ) (N : ℕ) :
    ‖singularPacket h θ N‖ = 1 := by
  have hsq : ‖singularPacket h θ N‖ ^ 2 = 1 := by
    rw [Lp_two_norm_sq_eq_integral]
    have h1 : ∫ t, ‖(singularPacket h θ N : ℝ → ℂ) t‖ ^ 2 ∂(volume.restrict (Ioi 0)) =
        ∫ t, (Ico (singularPacketStart h N) (singularPacketStart h N + singularPacketLength h N)).indicator
          (fun _ => (singularPacketLength h N)⁻¹) t ∂(volume.restrict (Ioi 0)) :=
      integral_congr_ae (by
        filter_upwards [singularPacket_coeFn h θ N] with t ht
        rw [ht, norm_sq_packetFun hh])
    rw [h1, integral_indicator_const _ measurableSet_Ico,
      measureReal_Ico_of_pos (packetStart_pos hh N).le
        (le_add_of_nonneg_right (packetLength_pos hh N).le), add_sub_cancel_left, smul_eq_mul,
      mul_inv_cancel₀ (packetLength_pos hh N).ne']
  have := norm_nonneg (singularPacket h θ N)
  nlinarith

/-! ## Shifting a packet -/

theorem packetPhase_add (h : ℝ≥0) (hh : 0 < h) (θ t : ℝ) :
    singularPacketPhase h θ (t + h) = Complex.exp ((θ : ℂ) * Complex.I) * singularPacketPhase h θ t := by
  have hh' : (h : ℝ) ≠ 0 := ne_of_gt hh
  have hreal : θ * (t + h) / h = θ + θ * t / h := by
    field_simp
    ring
  rw [singularPacketPhase, singularPacketPhase, ← Complex.exp_add, hreal]
  congr 1
  push_cast
  ring

/-- `u_N(t + h) = e^{iθ} L^{-1/2} e^{iθt/h} 1_{[R-h, R+L-h)}(t)`. -/
theorem singularPacketFun_add (h : ℝ≥0) (hh : 0 < h) (θ : ℝ) (N : ℕ) (t : ℝ) :
    singularPacketFun h θ N (t + h) = Complex.exp ((θ : ℂ) * Complex.I) *
      (Ico (singularPacketStart h N - h) (singularPacketStart h N + singularPacketLength h N - h)).indicator
        (fun t => (((Real.sqrt (singularPacketLength h N))⁻¹ : ℝ) : ℂ) * singularPacketPhase h θ t) t := by
  unfold singularPacketFun
  by_cases hmem : t ∈ Ico (singularPacketStart h N - h) (singularPacketStart h N + singularPacketLength h N - h)
  · have hmem' : t + h ∈ Ico (singularPacketStart h N) (singularPacketStart h N + singularPacketLength h N) := by
      simp only [mem_Ico] at hmem ⊢
      constructor <;> linarith [hmem.1, hmem.2]
    rw [indicator_of_mem hmem', indicator_of_mem hmem, packetPhase_add h hh]
    ring
  · have hmem' : t + h ∉ Ico (singularPacketStart h N) (singularPacketStart h N + singularPacketLength h N) := by
      intro h'
      apply hmem
      simp only [mem_Ico] at h' ⊢
      constructor <;> linarith [h'.1, h'.2]
    rw [indicator_of_notMem hmem', indicator_of_notMem hmem, mul_zero]

/-- `‖(S_h - e^{iθ}) u_N‖² = 2/(N+2)`. -/
theorem norm_sq_leftShift_sub_singularPacket {h : ℝ≥0} (hh : 0 < h) (θ : ℝ) (N : ℕ) :
    ‖burnolLeftShift h (singularPacket h θ N) -
        Complex.exp ((θ : ℂ) * Complex.I) • singularPacket h θ N‖ ^ 2 = 2 / ((N : ℝ) + 2) := by
  set R := singularPacketStart h N
  set L := singularPacketLength h N
  set A := Ico (R - h) (R + L - h)
  set B := Ico R (R + L)
  have hh' : (0 : ℝ) < h := hh
  have hL := packetLength_pos hh N
  have hR := packetStart_pos hh N
  have hRh : (h : ℝ) ≤ R := by
    simp only [R, singularPacketStart]
    have : (1 : ℝ) ≤ ((N : ℝ) + 2) ^ 2 := by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    nlinarith
  have hLh : (h : ℝ) ≤ L := by
    simp only [L, singularPacketLength]
    have : (1 : ℝ) ≤ (N : ℝ) + 2 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    nlinarith
  rw [Lp_two_norm_sq_eq_integral]
  have hpt : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      ‖((burnolLeftShift h (singularPacket h θ N) -
        Complex.exp ((θ : ℂ) * Complex.I) • singularPacket h θ N : BurnolHalfLineL2) : ℝ → ℂ) t‖ ^ 2 =
      L⁻¹ * (A.indicator (fun _ => (1 : ℝ)) t + B.indicator (fun _ => (1 : ℝ)) t -
        2 * (A ∩ B).indicator (fun _ => (1 : ℝ)) t) := by
    have hsh := (quasiMeasurePreserving_add_right_Ioi hh'.le).ae_eq_comp (singularPacket_coeFn h θ N)
    filter_upwards [Lp.coeFn_sub (burnolLeftShift h (singularPacket h θ N))
        (Complex.exp ((θ : ℂ) * Complex.I) • singularPacket h θ N),
      burnolLeftShift_coeFn h (singularPacket h θ N), hsh,
      Lp.coeFn_smul (Complex.exp ((θ : ℂ) * Complex.I)) (singularPacket h θ N),
      singularPacket_coeFn h θ N] with t e1 e2 e3 e4 e5
    simp only [Function.comp_apply] at e3
    rw [e1, Pi.sub_apply, e2, e3, e4, Pi.smul_apply, e5, singularPacketFun_add h hh, smul_eq_mul]
    unfold singularPacketFun
    have hnorm : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    have hc : ‖(((Real.sqrt L)⁻¹ : ℝ) : ℂ) * singularPacketPhase h θ t‖ ^ 2 = L⁻¹ := by
      rw [norm_mul, norm_packetPhase, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), inv_pow, Real.sq_sqrt hL.le]
    by_cases hA : t ∈ A <;> by_cases hB : t ∈ B
    · have hAB : t ∈ A ∩ B := ⟨hA, hB⟩
      simp only [A, B, R, L] at hA hB hAB hc ⊢
      rw [indicator_of_mem hA, indicator_of_mem hB, indicator_of_mem hA, indicator_of_mem hB,
        indicator_of_mem hAB, sub_self, norm_zero]
      norm_num
    · have hAB : t ∉ A ∩ B := fun h' => hB h'.2
      simp only [A, B, R, L] at hA hB hAB hc ⊢
      rw [indicator_of_mem hA, indicator_of_notMem hB, indicator_of_mem hA, indicator_of_notMem hB,
        indicator_of_notMem hAB, mul_zero, sub_zero, norm_mul, hnorm, one_mul, hc]
      ring
    · have hAB : t ∉ A ∩ B := fun h' => hA h'.1
      simp only [A, B, R, L] at hA hB hAB hc ⊢
      rw [indicator_of_notMem hA, indicator_of_mem hB, indicator_of_notMem hA, indicator_of_mem hB,
        indicator_of_notMem hAB, mul_zero, zero_sub, norm_neg, norm_mul, hnorm, one_mul, hc]
      ring
    · have hAB : t ∉ A ∩ B := fun h' => hA h'.1
      simp only [A, B, R, L] at hA hB hAB hc ⊢
      rw [indicator_of_notMem hA, indicator_of_notMem hB, indicator_of_notMem hA,
        indicator_of_notMem hB, indicator_of_notMem hAB, mul_zero, sub_zero, norm_zero]
      ring
  rw [integral_congr_ae hpt]
  have hiA : Integrable (A.indicator fun _ => (1 : ℝ)) (volume.restrict (Ioi 0)) :=
    (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by
      rw [Measure.restrict_apply measurableSet_Ico]
      exact ne_top_of_le_ne_top (by simp [Real.volume_Ico]) (measure_mono inter_subset_left)))
  have hiB : Integrable (B.indicator fun _ => (1 : ℝ)) (volume.restrict (Ioi 0)) :=
    (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by
      rw [Measure.restrict_apply measurableSet_Ico]
      exact ne_top_of_le_ne_top (by simp [Real.volume_Ico]) (measure_mono inter_subset_left)))
  have hiAB : Integrable ((A ∩ B).indicator fun _ => (1 : ℝ)) (volume.restrict (Ioi 0)) :=
    (integrable_indicator_iff (measurableSet_Ico.inter measurableSet_Ico)).2 (integrableOn_const (by
      rw [Measure.restrict_apply (measurableSet_Ico.inter measurableSet_Ico)]
      exact ne_top_of_le_ne_top (by simp [Real.volume_Ico])
        (measure_mono (inter_subset_left.trans inter_subset_left))))
  have hiAB' : Integrable (fun a => A.indicator (fun _ => (1 : ℝ)) a +
      B.indicator (fun _ => (1 : ℝ)) a) (volume.restrict (Ioi 0)) := hiA.add hiB
  rw [integral_const_mul, integral_sub hiAB' (hiAB.const_mul 2), integral_add hiA hiB,
    integral_const_mul, integral_indicator_const _ measurableSet_Ico,
    integral_indicator_const _ measurableSet_Ico,
    integral_indicator_const _ (measurableSet_Ico.inter measurableSet_Ico)]
  have hAB : A ∩ B = Ico R (R + L - h) := by
    simp only [A, B, Ico_inter_Ico]
    rw [max_eq_right (by linarith), min_eq_left (by linarith)]
  rw [hAB, measureReal_Ico_of_pos (by linarith) (by linarith),
    measureReal_Ico_of_pos (by linarith) (by linarith),
    measureReal_Ico_of_pos (by linarith) (by linarith)]
  simp only [smul_eq_mul, mul_one, L, singularPacketLength]
  field_simp
  ring

/-- `‖(K_h - S_h) u_N‖ ≤ 1/(N+2)²`. -/
theorem norm_weightedShift_sub_leftShift_singularPacket_le {h : ℝ≥0} (hh : 0 < h) (θ : ℝ)
    (N : ℕ) :
    ‖burnolWeightedShift h (singularPacket h θ N) - burnolLeftShift h (singularPacket h θ N)‖ ≤
      1 / ((N : ℝ) + 2) ^ 2 := by
  have hh' : (0 : ℝ) < h := hh
  have hR := packetStart_pos hh N
  have hle : ‖burnolWeightedShift h (singularPacket h θ N) -
      burnolLeftShift h (singularPacket h θ N)‖ ≤
      ‖((h : ℝ) / singularPacketStart h N : ℂ) • burnolLeftShift h (singularPacket h θ N)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    have hsh := (quasiMeasurePreserving_add_right_Ioi hh'.le).ae_eq_comp
      (singularPacket_coeFn h θ N)
    filter_upwards [Lp.coeFn_sub (burnolWeightedShift h (singularPacket h θ N))
        (burnolLeftShift h (singularPacket h θ N)),
      burnolWeightedShift_coeFn h (singularPacket h θ N),
      burnolLeftShift_coeFn h (singularPacket h θ N), hsh,
      Lp.coeFn_smul ((h : ℝ) / singularPacketStart h N : ℂ) (burnolLeftShift h (singularPacket h θ N)),
      ae_restrict_mem measurableSet_Ioi] with t e1 e2 e3 e4 e5 ht
    simp only [Function.comp_apply] at e4
    have ht' : (0 : ℝ) < t := ht
    rw [e1, Pi.sub_apply, e2, e3, e5, Pi.smul_apply, e3, e4, smul_eq_mul, ← sub_one_mul, norm_mul,
      norm_mul]
    by_cases hz : singularPacketFun h θ N (t + h) = 0
    · rw [hz, norm_zero, mul_zero, mul_zero]
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hmem : t + h ∈ Ico (singularPacketStart h N) (singularPacketStart h N + singularPacketLength h N) := by
        by_contra hn
        exact hz (by unfold singularPacketFun; rw [indicator_of_notMem hn])
      have htR : singularPacketStart h N ≤ t + h := hmem.1
      have hcast : ((t / (t + h) : ℝ) : ℂ) - 1 = (((-(h : ℝ)) / (t + h) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        congr 1
        field_simp
        ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hh',
        abs_of_pos (by linarith), show ((h : ℝ) / singularPacketStart h N : ℂ) =
          (((h : ℝ) / singularPacketStart h N : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_left hh'.le hR htR
  refine hle.trans ?_
  rw [norm_smul, show ((h : ℝ) / singularPacketStart h N : ℂ) = (((h : ℝ) / singularPacketStart h N : ℝ) : ℂ) by
    push_cast; rfl, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc (h : ℝ) / singularPacketStart h N * ‖burnolLeftShift h (singularPacket h θ N)‖
      ≤ (h : ℝ) / singularPacketStart h N * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖burnolLeftShift h (singularPacket h θ N)‖
            ≤ ‖burnolLeftShift h‖ * ‖singularPacket h θ N‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * 1 := by
              rw [norm_singularPacket hh]
              exact mul_le_mul_of_nonneg_right (norm_weightedLeftShift_le _ _ _) zero_le_one
          _ = 1 := one_mul 1
    _ = 1 / ((N : ℝ) + 2) ^ 2 := by
        rw [mul_one, singularPacketStart]
        field_simp

/-- **Singular-sequence estimate.**  `‖(K_h - e^{iθ}) u_N‖ ≤ √(2/(N+2)) + 1/(N+2)²`. -/
theorem norm_weightedShift_sub_smul_singularPacket_le {h : ℝ≥0} (hh : 0 < h) (θ : ℝ) (N : ℕ) :
    ‖burnolWeightedShift h (singularPacket h θ N) -
        Complex.exp ((θ : ℂ) * Complex.I) • singularPacket h θ N‖ ≤
      Real.sqrt (2 / ((N : ℝ) + 2)) + 1 / ((N : ℝ) + 2) ^ 2 := by
  have hsplit : burnolWeightedShift h (singularPacket h θ N) -
      Complex.exp ((θ : ℂ) * Complex.I) • singularPacket h θ N =
      (burnolLeftShift h (singularPacket h θ N) -
        Complex.exp ((θ : ℂ) * Complex.I) • singularPacket h θ N) +
      (burnolWeightedShift h (singularPacket h θ N) - burnolLeftShift h (singularPacket h θ N)) := by
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_weightedShift_sub_leftShift_singularPacket_le
    hh θ N))
  rw [← norm_sq_leftShift_sub_singularPacket hh θ N, Real.sqrt_sq (norm_nonneg _)]

/-- **Weak nullity.**  `⟪z, u_N⟫ → 0` for every `z`. -/
theorem tendsto_inner_singularPacket {h : ℝ≥0} (hh : 0 < h) (θ : ℝ) (z : BurnolHalfLineL2) :
    Tendsto (fun N => ⟪z, singularPacket h θ N⟫_ℂ) atTop (𝓝 0) := by
  have hcut : ∀ N, halfLineCutoff (singularPacketStart h N) (singularPacket h θ N) =
      singularPacket h θ N := fun N => by
    refine Lp.ext ?_
    filter_upwards [halfLineCutoff_coeFn (singularPacketStart h N) (singularPacket h θ N),
      singularPacket_coeFn h θ N] with t e1 e2
    rw [e1, e2]
    unfold singularPacketFun
    by_cases hmem : t ∈ Ico (singularPacketStart h N) (singularPacketStart h N + singularPacketLength h N)
    · rw [indicator_of_mem hmem, indicator_of_mem (show t ∈ Ici (singularPacketStart h N) from hmem.1)]
      simp
    · rw [indicator_of_notMem hmem, mul_zero]
  have hbound : ∀ N, ‖⟪z, singularPacket h θ N⟫_ℂ‖ ≤ ‖halfLineCutoff (singularPacketStart h N) z‖ :=
    fun N => by
      rw [← hcut N, ← ContinuousLinearMap.adjoint_inner_left, adjoint_halfLineCutoff]
      calc ‖⟪halfLineCutoff (singularPacketStart h N) z, singularPacket h θ N⟫_ℂ‖
          ≤ ‖halfLineCutoff (singularPacketStart h N) z‖ * ‖singularPacket h θ N‖ := norm_inner_le_norm _ _
        _ = ‖halfLineCutoff (singularPacketStart h N) z‖ := by rw [norm_singularPacket hh, mul_one]
  have hmono : Monotone (singularPacketStart h) := fun m n hmn => by
    unfold singularPacketStart
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hh0 : (0 : ℝ) ≤ h := h.coe_nonneg
    gcongr
  have htend : Tendsto (singularPacketStart h) atTop atTop := by
    have hh' : (0 : ℝ) < h := hh
    refine tendsto_atTop_mono (fun N => ?_) (tendsto_natCast_atTop_atTop.atTop_mul_const hh')
    unfold singularPacketStart
    have hN : (N : ℝ) ≤ ((N : ℝ) + 2) ^ 2 := by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact mul_le_mul_of_nonneg_right hN hh'.le
  exact squeeze_zero_norm hbound (tendsto_norm_halfLineCutoff z hmono htend)

/-! ## Consequences -/

/-- **Singular-sequence lemma.**  For `h > 0` and `|η| = 1` there is a weakly null unit sequence
with `‖(K_h - η)u_N‖ ≤ √(2/(N+2)) + 1/(N+2)²`. -/
theorem exists_singularSequence_burnolWeightedShift {h : ℝ≥0} (hh : 0 < h) {η : ℂ}
    (hη : ‖η‖ = 1) :
    ∃ u : ℕ → BurnolHalfLineL2, (∀ N, ‖u N‖ = 1) ∧
      (∀ z, Tendsto (fun N => ⟪z, u N⟫_ℂ) atTop (𝓝 0)) ∧
      ∀ N, ‖burnolWeightedShift h (u N) - η • u N‖ ≤
        Real.sqrt (2 / ((N : ℝ) + 2)) + 1 / ((N : ℝ) + 2) ^ 2 := by
  have hηe : Complex.exp ((η.arg : ℂ) * Complex.I) = η := by
    have := Complex.norm_mul_exp_arg_mul_I η
    rwa [hη, Complex.ofReal_one, one_mul] at this
  refine ⟨singularPacket h η.arg, norm_singularPacket hh η.arg,
    tendsto_inner_singularPacket hh η.arg, fun N => ?_⟩
  have := norm_weightedShift_sub_smul_singularPacket_le hh η.arg N
  rwa [hηe] at this

theorem tendsto_singularSequence_bound :
    Tendsto (fun N : ℕ => Real.sqrt (2 / ((N : ℝ) + 2)) + 1 / ((N : ℝ) + 2) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => 2 / ((N : ℝ) + 2)) atTop (𝓝 0) :=
    h1.const_div_atTop 2
  have h3 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 2) ^ 2) atTop (𝓝 0) :=
    ((tendsto_pow_atTop two_ne_zero).comp h1).const_div_atTop 1
  simpa using (h2.sqrt).add h3

/-- **Operator norm one.**  `‖K_h‖ = 1` for `h > 0`. -/
theorem norm_burnolWeightedShift {h : ℝ≥0} (hh : 0 < h) : ‖burnolWeightedShift h‖ = 1 := by
  refine le_antisymm (norm_burnolWeightedShift_le h) ?_
  obtain ⟨u, hu1, -, hu⟩ := exists_singularSequence_burnolWeightedShift hh (η := 1) (by simp)
  have hlim : Tendsto (fun N : ℕ => 1 - (Real.sqrt (2 / ((N : ℝ) + 2)) + 1 / ((N : ℝ) + 2) ^ 2))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_singularSequence_bound
  refine le_of_tendsto hlim (Eventually.of_forall fun N => ?_)
  have h1 : ‖u N‖ - ‖burnolWeightedShift h (u N) - u N‖ ≤ ‖burnolWeightedShift h (u N)‖ := by
    have := norm_sub_norm_le (u N) (u N - burnolWeightedShift h (u N))
    rwa [sub_sub_cancel, norm_sub_rev (u N)] at this
  have h2 : ‖burnolWeightedShift h (u N)‖ ≤ ‖burnolWeightedShift h‖ := by
    have := (burnolWeightedShift h).le_opNorm (u N)
    rwa [hu1, mul_one] at this
  have h3 := hu N
  rw [one_smul] at h3
  rw [hu1] at h1
  linarith

/-- **Compact perturbations.**  For every compact `C` and `|η| = 1`, the same unit weakly null
sequence satisfies `‖(K_h + C - η) u_N‖ → 0`. -/
theorem tendsto_weightedShift_add_compact_sub_singularSequence {h : ℝ≥0} (hh : 0 < h) {η : ℂ}
    (hη : ‖η‖ = 1) :
    ∃ u : ℕ → BurnolHalfLineL2, (∀ N, ‖u N‖ = 1) ∧
      (∀ z, Tendsto (fun N => ⟪z, u N⟫_ℂ) atTop (𝓝 0)) ∧
      ∀ C : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2, IsCompactOperator C →
        Tendsto (fun N => burnolWeightedShift h (u N) + C (u N) - η • u N) atTop (𝓝 0) := by
  obtain ⟨u, hu1, hweak, hu⟩ := exists_singularSequence_burnolWeightedShift hh hη
  refine ⟨u, hu1, hweak, fun C hC => ?_⟩
  have hK : Tendsto (fun N => burnolWeightedShift h (u N) - η • u N) atTop (𝓝 0) :=
    squeeze_zero_norm hu tendsto_singularSequence_bound
  have hCu := tendsto_norm_compact_of_weaklyNull C hC u (fun N => (hu1 N).le) hweak
  have := hK.add hCu
  rw [zero_add] at this
  refine this.congr fun N => ?_
  abel

end GaloisForLFunctions.HTGeometry

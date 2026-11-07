import GaloisForLFunctions.BlackHoleRingdown.TheMetricOfAPulse
import GaloisForLFunctions.BlackHoleRingdown.TheRingdownOfAPulse

/-!
# The ringdown of the metric

Every component of the gravitational wave of a pulse rings down in the modes of the zeros. At fixed `r, x, y` each
block of the metric is `e^{-τ/2}` or `(r/F) e^{-τ/2}` times the rotated gradient of the field of a pulse `g = c h + h'`,
with `c = F - ½` in the temporal block and `c = -½` in the radial block. So the contour package applies with the jets of
the numerator.

The holomorphy in `u` of the jets `N_x, N_y` of the numerator is soft: it is the locally uniform limit of difference
quotients, by the uniform bound on the second jets.

The pole at a zero `p` has top coefficient proportional to `(F - ½ + p) a(-ip) ∇N(p)` in the temporal block and to
`(p - ½) a(-ip) ∇N(p)` in the radial block, which is the separated gravitational mode of `p`, with `w = p - ½`:
`h_t = e^{wτ}(F + w) V`, `h_r = w e^{wτ} (r/F) V`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff BigOperators

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry
open GaloisForLFunctions.HTGeometry.ScalarTwoJet (coordDeriv)

/-! ### Holomorphy of the jets -/

/-- **A derivative with a locally uniform second bound is holomorphic in the parameter.** -/
theorem differentiableAt_of_second_bound {f f₁ f₂ : ℂ → ℝ → ℂ} {u₀ : ℂ} {Y₀ δ K : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K)
    (hf : ∀ q ∈ Icc Y₀ (Y₀ + δ), ∀ v ∈ Metric.ball u₀ 1, DifferentiableAt ℂ (fun w => f w q) v)
    (h1 : ∀ v ∈ Metric.ball u₀ 1, ∀ q ∈ Icc Y₀ (Y₀ + δ), HasDerivAt (f v) (f₁ v q) q)
    (h2 : ∀ v ∈ Metric.ball u₀ 1, ∀ q ∈ Icc Y₀ (Y₀ + δ), HasDerivAt (f₁ v) (f₂ v q) q)
    (hb : ∀ v ∈ Metric.ball u₀ 1, ∀ q ∈ Icc Y₀ (Y₀ + δ), ‖f₂ v q‖ ≤ K) :
    DifferentiableAt ℂ (fun v => f₁ v Y₀) u₀ := by
  set h : ℕ → ℝ := fun n => δ * (1 / ((n : ℝ) + 1)) with hh
  have hpos : ∀ n, 0 < h n := fun n => by positivity
  have hle : ∀ n, h n ≤ δ := fun n => by
    have h1' : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc h n ≤ δ * 1 := mul_le_mul_of_nonneg_left h1' hδ.le
      _ = δ := mul_one δ
  have hlim : Tendsto h atTop (𝓝 0) := by
    have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
    rwa [mul_zero] at h0
  set F : ℕ → ℂ → ℂ := fun n v => ((h n : ℝ) : ℂ)⁻¹ * (f v (Y₀ + h n) - f v Y₀) with hF
  have hest : ∀ n, ∀ v ∈ Metric.ball u₀ 1, ‖f₁ v Y₀ - F n v‖ ≤ K * h n := by
    intro n v hv
    have hs : Icc Y₀ (Y₀ + h n) ⊆ Icc Y₀ (Y₀ + δ) :=
      Icc_subset_Icc le_rfl (by linarith [hle n])
    have hleft : Y₀ ∈ Icc Y₀ (Y₀ + h n) := ⟨le_rfl, by linarith [hpos n]⟩
    have hright : Y₀ + h n ∈ Icc Y₀ (Y₀ + h n) := ⟨by linarith [hpos n], le_rfl⟩
    have hd1 : ∀ q ∈ Icc Y₀ (Y₀ + h n), ‖f₁ v q - f₁ v Y₀‖ ≤ K * h n := fun q hq => by
      have h3 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f₁ v) (f' := f₂ v) (C := K)
        (s := Icc Y₀ (Y₀ + h n)) (fun t ht => (h2 v hv t (hs ht)).hasDerivWithinAt)
        (fun t ht => hb v hv t (hs ht)) (convex_Icc _ _) hleft hq
      refine h3.trans (mul_le_mul_of_nonneg_left ?_ hK)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hq.1])]
      linarith [hq.2]
    have hφ : ∀ q ∈ Icc Y₀ (Y₀ + h n), HasDerivWithinAt
        (fun t : ℝ => f v t - (t : ℂ) * f₁ v Y₀) (f₁ v q - f₁ v Y₀) (Icc Y₀ (Y₀ + h n)) q := fun q hq => by
      have h3 := (h1 v hv q (hs hq)).sub
        (((hasDerivAt_id q).ofReal_comp).mul_const (f₁ v Y₀))
      refine (h3.congr_deriv ?_).hasDerivWithinAt
      simp
    have h4 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hd1 (convex_Icc _ _) hleft hright
    have hsub : ‖(Y₀ + h n) - Y₀‖ = h n := by
      rw [add_sub_cancel_left, Real.norm_eq_abs, abs_of_pos (hpos n)]
    rw [hsub] at h4
    have hne : ((h n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    have hval : f₁ v Y₀ - F n v = -((h n : ℝ) : ℂ)⁻¹ * ((f v (Y₀ + h n) - ((Y₀ + h n : ℝ) : ℂ) * f₁ v Y₀) -
        (f v Y₀ - (Y₀ : ℂ) * f₁ v Y₀)) := by
      simp only [hF]
      push_cast
      field_simp
      ring
    rw [hval, norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hpos n).le]
    calc (h n)⁻¹ * _ ≤ (h n)⁻¹ * (K * h n * h n) := mul_le_mul_of_nonneg_left h4 (by have := hpos n; positivity)
      _ = K * h n := by
        have := (hpos n).ne'
        field_simp
  have hT : TendstoUniformlyOn F (fun v => f₁ v Y₀) atTop (Metric.ball u₀ 1) := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    have hl : Tendsto (fun n => K * h n) atTop (𝓝 0) := by simpa using hlim.const_mul K
    filter_upwards [hl.eventually (gt_mem_nhds hε)] with n hn v hv
    rw [dist_eq_norm]
    exact (hest n v hv).trans_lt hn
  have hdiff : ∀ n, DifferentiableOn ℂ (F n) (Metric.ball u₀ 1) := fun n v hv => by
    have ha := hf (Y₀ + h n) ⟨by linarith [hpos n], by linarith [hle n]⟩ v hv
    have hb' := hf Y₀ ⟨le_rfl, by linarith⟩ v hv
    exact ((ha.sub hb').const_mul _).differentiableWithinAt
  have hon := hT.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall hdiff)
    Metric.isOpen_ball
  exact hon.differentiableAt (Metric.ball_mem_nhds _ one_pos)

section TailJets

variable (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) (u : ℂ)

include hY

theorem exists_second_jet_bound_ball :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ Metric.ball u 1, ∀ (x q : ℝ), q ∈ Icc Y (Y + Y) →
      ‖weightedTailYY v negative x q‖ ≤ K ∧ ‖weightedTailXX v negative x Y‖ ≤ K := by
  obtain ⟨C, M, hC, hb⟩ := exists_weightedTail_jets_le_sharp hY (R := |u.re| + 1) (by positivity)
  refine ⟨C * (2 + |u.im|) ^ M, by positivity, fun v hv x q hq => ?_⟩
  have hdist : ‖v - u‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hre : |v.re| ≤ |u.re| + 1 := by
    have := Complex.abs_re_le_norm (v - u)
    have h2 := abs_sub_abs_le_abs_sub v.re u.re
    simp at this
    linarith
  have him : |v.im| ≤ |u.im| + 1 := by
    have := Complex.abs_im_le_norm (v - u)
    have h2 := abs_sub_abs_le_abs_sub v.im u.im
    simp at this
    linarith
  have hexp : Real.exp (-(Real.pi * |v.im| / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := Real.pi_pos; have := abs_nonneg v.im; simp only [neg_nonpos]; positivity)
  have hmax : ∀ a : ℝ, a ≤ C * (1 + |v.im|) ^ M * Real.exp (-(Real.pi * |v.im| / 2)) →
      a ≤ C * (2 + |u.im|) ^ M := fun a ha => by
    have h1 : (1 + |v.im|) ^ M ≤ (2 + |u.im|) ^ M :=
      pow_le_pow_left₀ (by positivity) (by linarith) M
    calc a ≤ C * (1 + |v.im|) ^ M * Real.exp (-(Real.pi * |v.im| / 2)) := ha
      _ ≤ C * (1 + |v.im|) ^ M * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ C * (2 + |u.im|) ^ M := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left h1 hC
  have hq' : q ∈ Icc (Y / 2) (2 * Y) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨-, -, -, -, h5⟩ := hb v negative x q hre hq'
  obtain ⟨-, -, h3, -, -⟩ := hb v negative x Y hre (mem_window_self hY)
  exact ⟨hmax _ h5, hmax _ h3⟩

omit hY in
theorem differentiableAt_weightedTail_param {q : ℝ} (hq : 0 < q) (x : ℝ) (v : ℂ) :
    DifferentiableAt ℂ (fun w => weightedTail w negative x q) v := by
  simp only [weightedTail_eq_signedSqrtWhittakerTail]
  exact differentiableAt_signedSqrtWhittakerTail negative x hq v

theorem differentiableAt_weightedTailY :
    DifferentiableAt ℂ (fun v => weightedTailY v negative x Y) u := by
  obtain ⟨K, hK, hb⟩ := exists_second_jet_bound_ball negative hY u
  refine differentiableAt_of_second_bound (f := fun v q => weightedTail v negative x q)
    (f₁ := fun v q => weightedTailY v negative x q) (Y₀ := Y)
    (f₂ := fun v q => weightedTailYY v negative x q) (δ := Y) hY hK (K := K) (fun q hq v _ => ?_)
    (fun v _ q hq => ?_) (fun v _ q hq => ?_) (fun v hv q hq => (hb v hv x q hq).1)
  · exact differentiableAt_weightedTail_param negative (by linarith [hq.1]) x v
  · exact hasDerivAt_weightedTail_y v negative x (by linarith [hq.1])
  · exact hasDerivAt_weightedTailY_y v negative x (by linarith [hq.1])

theorem differentiableAt_weightedTailX :
    DifferentiableAt ℂ (fun v => weightedTailX v negative x Y) u := by
  obtain ⟨K, hK, hb⟩ := exists_second_jet_bound_ball negative hY u
  refine differentiableAt_of_second_bound (f := fun v q => weightedTail v negative q Y)
    (f₁ := fun v q => weightedTailX v negative q Y) (Y₀ := x)
    (f₂ := fun v q => weightedTailXX v negative q Y) (δ := 1) one_pos hK (K := K) (fun q _ v _ => ?_)
    (fun v _ q _ => ?_) (fun v _ q _ => ?_)
    (fun v hv q _ => (hb v hv q Y ⟨le_rfl, by linarith⟩).2)
  · exact differentiableAt_weightedTail_param negative hY q v
  · exact hasDerivAt_weightedTail_x v negative q hY
  · exact hasDerivAt_weightedTailX_x v negative q hY

end TailJets

/-! ### The numerators of the covector -/

/-- The numerator of the rotated gradient. -/
def covNum (i : Fin 2) (u : ℂ) (x Y : ℝ) : ℂ := if i = 0 then numY u x Y else -numX u x Y

/-- The rotated gradient of the Eisenstein function. -/
def covE (i : Fin 2) (u : ℂ) (x Y : ℝ) : ℂ := if i = 0 then eisensteinY u x Y else -eisensteinX u x Y

theorem covE_eq_div (i : Fin 2) {u : ℂ} (h : xi (1 + 2 * u) ≠ 0) (x Y : ℝ) :
    covNum i u x Y / xi (1 + 2 * u) = covE i u x Y := by
  have hX := mul_inv_cancel₀ h
  by_cases hi : i = 0
  · simp only [covNum, covE, hi, if_true]
    rw [div_eq_iff h]
    simp only [numY, eisensteinY, scatteringPhase, tailWeight]
    generalize xi (1 + 2 * u) = X at hX ⊢
    generalize (1 + 2 * u) / (2 * u - 1) = b
    generalize (Y : ℂ) ^ (1 / 2 - u - 1) = B
    generalize (Y : ℂ) ^ (1 / 2 + u - 1) = A
    simp only [div_eq_mul_inv]
    linear_combination (-(b * xi (2 * u) * ((1 / 2 - u) * B)) - (1 + 2 * u) * (2 * u) * eisTailY u x Y) * hX
  · simp only [covNum, covE, hi, if_false]
    rw [div_eq_iff h]
    simp only [numX, eisensteinX, tailWeight]
    generalize xi (1 + 2 * u) = X at hX ⊢
    simp only [div_eq_mul_inv]
    linear_combination ((1 + 2 * u) * (2 * u) * eisTailX u x Y) * hX

theorem norm_covE_le {K : ℝ} {u : ℂ} {x Y : ℝ} (h : EisensteinJetsLE K u x Y) (i : Fin 2) :
    ‖covE i u x Y‖ ≤ K := by
  obtain ⟨-, a, -, b, -⟩ := h
  by_cases hi : i = 0
  · simpa [covE, hi] using b
  · simpa [covE, hi] using a

theorem differentiableAt_covNum (i : Fin 2) (x : ℝ) {Y : ℝ} (hY : 0 < Y) {u : ℂ} (hu : u.re < 1 / 2) :
    DifferentiableAt ℂ (fun v => covNum i v x Y) u := by
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hp : DifferentiableAt ℂ (fun v : ℂ => (1 + 2 * v) * (2 * v)) u := by fun_prop
  by_cases hi : i = 0
  · simp only [covNum, hi, if_true, numY, eisTailY]
    have h1 : DifferentiableAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 + v - 1)) u :=
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 + v - 1) u).const_cpow (Or.inl hYC)
    have h2 : DifferentiableAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 - v - 1)) u :=
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 - v - 1) u).const_cpow (Or.inl hYC)
    have hx1 : DifferentiableAt ℂ (fun v : ℂ => xi (1 + 2 * v)) u := differentiable_xi_shift u
    have hx2 : DifferentiableAt ℂ (fun v : ℂ => xi (2 * v)) u :=
      (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) u
    have hne : 2 * u - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hq : DifferentiableAt ℂ (fun v : ℂ => (1 + 2 * v) / (2 * v - 1)) u :=
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) u).div (by fun_prop) hne
    have ha : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 + v) u := by fun_prop
    have hb : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 - v) u := by fun_prop
    exact ((ha.mul h1).mul hx1).add ((hq.mul hx2).mul (hb.mul h2)) |>.add
      (hp.mul ((differentiableAt_weightedTailY false x hY u).add
        (differentiableAt_weightedTailY true x hY u)))
  · simp only [covNum, hi, if_false, numX, eisTailX]
    exact (hp.mul ((differentiableAt_weightedTailX false x hY u).add
      (differentiableAt_weightedTailX true x hY u))).neg

theorem analyticAt_covNum (i : Fin 2) (x : ℝ) {Y : ℝ} (hY : 0 < Y) {u : ℂ} (hu : u.re ≤ 0) :
    AnalyticAt ℂ (fun v => covNum i v x Y) u := by
  have hopen : IsOpen {v : ℂ | v.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  have hd : DifferentiableOn ℂ (fun v => covNum i v x Y) {v : ℂ | v.re < 1 / 2} :=
    fun v hv => (differentiableAt_covNum i x hY hv).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds (by simp only [mem_setOf_eq]; linarith))

/-- The numerator of the rotated gradient of a pulse. -/
def covPulseNum (g : ℝ → ℂ) (i : Fin 2) (x Y : ℝ) (u : ℂ) : ℂ :=
  pulseAmplitude g (-I * u) * covNum i u x Y

theorem inverseXiQuotient_covPulseNum (g : ℝ → ℂ) (i : Fin 2) (x Y : ℝ) {u : ℂ}
    (hu : xi (1 + 2 * u) ≠ 0) :
    inverseXiQuotient (covPulseNum g i x Y) u = pulseAmplitude g (-I * u) * covE i u x Y := by
  rw [inverseXiQuotient, covPulseNum, mul_div_assoc, covE_eq_div i hu]

section Data

variable (h : CompactPulse) (i : Fin 2) (x : ℝ) {Y : ℝ}

theorem analyticAt_covPulseNum (hY : 0 < Y) {u : ℂ} (hu : u.re ≤ 0) :
    AnalyticAt ℂ (covPulseNum h i x Y) u :=
  ((h.differentiable_amplitude.comp
    (by fun_prop : Differentiable ℂ fun v : ℂ => -I * v)).analyticAt u).mul
    (analyticAt_covNum i x hY hu)

/-- **The contour data of the rotated gradient of a pulse.** -/
theorem contourData_cov (hY : 0 < Y) {A : ℝ} (hA : 1 ≤ A) : ContourData A (covPulseNum h i x Y) := by
  have hAnn : 0 ≤ A := by linarith
  have hrapid := h.rapidAmplitude
  have hYm := mem_window_self hY
  obtain ⟨C₀, M₀, hC₀, hline⟩ := exists_eisenstein_jets_line_le_poly hY
  obtain ⟨C₁, T₁, M₁, hC₁, hleft⟩ := exists_jets_left_line hY hA
  obtain ⟨C₂, M₂, k₀, hC₂, hgood⟩ := exists_jets_goodHeight (A := A) (c := 0) hY hAnn le_rfl
  obtain ⟨Ca₀, hCa₀, ha₀⟩ := hrapid.exists_rotated_le 0 M₀
  obtain ⟨Ca₁, hCa₁, ha₁⟩ := hrapid.exists_rotated_le A M₁
  obtain ⟨Ca₂, hCa₂, ha₂⟩ := hrapid.exists_rotated_le A M₂
  have hbound : ∀ {u : ℂ} {M : ℕ} {B Ca K : ℝ}, xi (1 + 2 * u) ≠ 0 → |u.re| ≤ B →
      (∀ v : ℂ, |v.re| ≤ B → ‖pulseAmplitude h (-I * v)‖ * (1 + |v.im|) ^ M ≤
        Ca * ((1 + |v.im|) ^ 2)⁻¹) →
      ‖covE i u x Y‖ ≤ K * (1 + |u.im|) ^ M → 0 ≤ K →
      ‖inverseXiQuotient (covPulseNum h i x Y) u‖ ≤ K * Ca * ((1 + |u.im|) ^ 2)⁻¹ := by
    intro u M B Ca K hne hu hCa hE hK
    rw [inverseXiQuotient_covPulseNum h i x Y hne, norm_mul]
    calc ‖pulseAmplitude h (-I * u)‖ * ‖covE i u x Y‖
        ≤ ‖pulseAmplitude h (-I * u)‖ * (K * (1 + |u.im|) ^ M) :=
          mul_le_mul_of_nonneg_left hE (norm_nonneg _)
      _ = K * (‖pulseAmplitude h (-I * u)‖ * (1 + |u.im|) ^ M) := by ring
      _ ≤ K * (Ca * ((1 + |u.im|) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (hCa u hu) hK
      _ = _ := by ring
  refine ⟨fun u _ h2 => analyticAt_covPulseNum h i x hY h2, ?_, ?_, ?_⟩
  · have hcont : Continuous fun y : ℝ => inverseXiQuotient (covPulseNum h i x Y) ((y : ℂ) * I) := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      have han : AnalyticAt ℂ (inverseXiQuotient (covPulseNum h i x Y)) ((y : ℂ) * I) :=
        (analyticAt_covPulseNum h i x hY (by simp)).div (differentiable_xi_shift.analyticAt _)
          (xi_line_ne_zero y)
      exact ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) * I) han.continuousAt (by fun_prop)
    refine integrable_of_continuous_of_inv_sq_tail hcont (R := 0) (C := C₀ * Ca₀) fun y _ => ?_
    have him : ((y : ℂ) * I).im = y := by simp
    have hb := hbound (u := (y : ℂ) * I) (B := 0) (xi_line_ne_zero y) (by simp) ha₀ (by
      rw [him]
      obtain ⟨a0, a1, a2, a3, a4⟩ := hline y x Y hYm
      exact norm_covE_le ⟨a0, a1, a2, a3, a4⟩ i) hC₀
    rwa [him] at hb
  · have hre : ∀ y : ℝ, (((-A : ℝ) : ℂ) + (y : ℂ) * I).re = -A := fun y => by simp
    have him : ∀ y : ℝ, (((-A : ℝ) : ℂ) + (y : ℂ) * I).im = y := fun y => by simp
    have hne : ∀ y : ℝ, xi (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)) ≠ 0 := fun y =>
      xi_ne_zero_of_re_le (by rw [hre]; linarith)
    have hcont : Continuous fun y : ℝ =>
        inverseXiQuotient (covPulseNum h i x Y) (((-A : ℝ) : ℂ) + (y : ℂ) * I) := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      have han : AnalyticAt ℂ (inverseXiQuotient (covPulseNum h i x Y))
          (((-A : ℝ) : ℂ) + (y : ℂ) * I) :=
        (analyticAt_covPulseNum h i x hY (by rw [hre]; linarith)).div
          (differentiable_xi_shift.analyticAt _) (hne y)
      exact ContinuousAt.comp (f := fun y : ℝ => ((-A : ℝ) : ℂ) + (y : ℂ) * I) han.continuousAt
        (by fun_prop)
    refine integrable_of_continuous_of_inv_sq_tail hcont (R := T₁) (C := C₁ * Ca₁) fun y hy => ?_
    have hb := hbound (u := ((-A : ℝ) : ℂ) + (y : ℂ) * I) (B := A) (hne y)
      (by rw [hre, abs_neg, abs_of_nonneg hAnn]) ha₁ (by
        rw [him]
        exact norm_covE_le (hleft y x Y hy hYm) i) hC₁
    rwa [him] at hb
  · have hLat : Tendsto (fun k => goodHeight k / 2) atTop atTop :=
      tendsto_goodHeight.atTop_div_const (by norm_num)
    refine ⟨fun k => C₂ * Ca₂ * ((1 + goodHeight k / 2) ^ 2)⁻¹, ?_, ?_⟩
    · have h1 : Tendsto (fun k => 1 + goodHeight k / 2) atTop atTop :=
        tendsto_atTop_add_const_left _ _ hLat
      have h2 : Tendsto (fun k => (1 + goodHeight k / 2) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h1
      simpa using (tendsto_inv_atTop_zero.comp h2).const_mul (C₂ * Ca₂)
    · filter_upwards [eventually_ge_atTop k₀, hLat.eventually_ge_atTop 1] with k hk hLk u h1 h2 him
      have hne : xi (1 + 2 * u) ≠ 0 := by
        refine xi_ne_zero_of_abs_im_goodHeight k ?_
        have h3 : (1 + 2 * u).im = 2 * u.im := by simp
        rw [h3, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), him]
        ring
      have hg := hgood k hk u x Y h1 h2 him (by rw [him]; exact hLk) hYm
      have hb := hbound (u := u) (B := A) hne (abs_le.mpr ⟨h1, h2.trans hAnn⟩) ha₂
        (norm_covE_le hg i) hC₂
      rwa [him] at hb

end Data

/-- The spectral packet of the rotated gradient. -/
def covPacket (g : ℝ → ℂ) (i : Fin 2) (τ x Y : ℝ) : ℂ :=
  ∫ ξ : ℝ, pulseAmplitude g (ξ : ℂ) * covE i ((ξ : ℂ) * I) x Y * Complex.exp (I * (ξ : ℂ) * (τ : ℂ))

theorem contourField_cov (g : ℝ → ℂ) (i : Fin 2) (τ x Y : ℝ) :
    contourField (covPulseNum g i x Y) τ = covPacket g i τ x Y := by
  rw [contourField, covPacket]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [inverseXiQuotient, timeNumerator, covPulseNum, ← covE_eq_div i (xi_line_ne_zero y)]
  have harg : -I * ((y : ℂ) * I) = y := by linear_combination (-(y : ℂ)) * I_sq
  have he : Complex.exp ((y : ℂ) * I * (τ : ℂ)) = Complex.exp (I * (y : ℂ) * (τ : ℂ)) := by
    congr 1
    ring
  rw [harg, he]
  ring

/-- **The ringdown of the rotated gradient of a pulse.** -/
theorem cov_ringdown (g : CompactPulse) (i : Fin 2) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∃ Rem : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖Rem τ‖ ≤ C * Real.exp (-A * τ)) ∧
      ∀ τ₀ : ℝ, 0 ≤ τ₀ → TendstoUniformlyOn (fun k τ => contourPartial (covPulseNum g i x Y) τ k)
        (fun τ => covPacket g i τ x Y - Rem τ) atTop (Ici (-τ₀)) := by
  obtain ⟨Rem, hRem, hlim⟩ := contour_expansion fun A hA => contourData_cov g i x hY hA
  refine ⟨Rem, hRem, fun τ₀ hτ₀ => ?_⟩
  have := hlim τ₀ hτ₀
  simp_rw [contourField_cov] at this
  exact this

/-! ### The packet of the gradient -/

theorem continuous_line_div {N : ℂ → ℂ} (hN : ∀ ξ : ℝ, AnalyticAt ℂ N ((ξ : ℂ) * I)) :
    Continuous fun ξ : ℝ => N ((ξ : ℂ) * I) / xi (1 + 2 * ((ξ : ℂ) * I)) := by
  refine continuous_iff_continuousAt.mpr fun ξ => ?_
  have han : AnalyticAt ℂ (fun u => N u / xi (1 + 2 * u)) ((ξ : ℂ) * I) :=
    (hN ξ).div (differentiable_xi_shift.analyticAt _) (xi_line_ne_zero ξ)
  exact ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) * I) han.continuousAt (by fun_prop)

theorem continuous_covE_line (i : Fin 2) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Continuous fun ξ : ℝ => covE i ((ξ : ℂ) * I) x Y := by
  have h := continuous_line_div (N := fun v => covNum i v x Y)
    (fun ξ => analyticAt_covNum i x hY (by simp))
  refine h.congr fun ξ => covE_eq_div i (xi_line_ne_zero ξ) x Y

theorem continuous_normalized_line (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Continuous fun ξ : ℝ => normalizedEisenstein ((ξ : ℂ) * I) x Y := by
  have h := continuous_line_div (N := fun v => eisensteinNumerator v x Y)
    (fun ξ => analyticAt_eisensteinNumerator x hY (by simp))
  refine h.congr fun ξ => (normalizedEisenstein_eq_numerator_div (xi_line_ne_zero ξ) x Y).symm

section Packet

variable (g : CompactPulse) (τ : ℝ)

theorem continuous_amplitude_real : Continuous fun ξ : ℝ => pulseAmplitude g (ξ : ℂ) :=
  g.differentiable_amplitude.continuous.comp Complex.continuous_ofReal

theorem continuous_phase : Continuous fun ξ : ℝ => Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := by
  fun_prop

/-- The derivative in the height of the packet. -/
theorem hasDerivAt_pulsePacket_y (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q => pulsePacket g τ x q) (covPacket g 0 τ x Y) Y := by
  obtain ⟨C, M, hC, hE⟩ := exists_eisenstein_jets_line_le_poly hY
  obtain ⟨Ca, hCa, ha⟩ := g.rapidAmplitude.exists_mul_poly_le 0 M
  have hs : Ioo (Y / 2) (2 * Y) ∈ 𝓝 Y := Ioo_mem_nhds (by linarith) (by linarith)
  have hb0 : Integrable fun ξ : ℝ => C * Ca * ((1 + |ξ|) ^ 2)⁻¹ :=
    integrable_inv_one_add_abs_sq.const_mul _
  have hbn : ∀ (K : ℂ) (ξ : ℝ), ‖K‖ ≤ C * (1 + |ξ|) ^ M →
      ‖pulseAmplitude g (ξ : ℂ) * K * Complex.exp (I * (ξ : ℂ) * (τ : ℂ))‖ ≤
        C * Ca * ((1 + |ξ|) ^ 2)⁻¹ := fun K ξ hK => by
    rw [norm_mul, norm_mul, norm_exp_I_mul, mul_one]
    have h1 := ha (ξ : ℂ) (by simp)
    simp only [Complex.ofReal_re] at h1
    calc ‖pulseAmplitude g (ξ : ℂ)‖ * ‖K‖ ≤ ‖pulseAmplitude g (ξ : ℂ)‖ * (C * (1 + |ξ|) ^ M) :=
          mul_le_mul_of_nonneg_left hK (norm_nonneg _)
      _ = C * (‖pulseAmplitude g (ξ : ℂ)‖ * (1 + |ξ|) ^ M) := by ring
      _ ≤ C * (Ca * ((1 + |ξ|) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 hC
      _ = _ := by ring
  have hmeasF : ∀ q : ℝ, 0 < q → Continuous fun ξ : ℝ => pulseAmplitude g (ξ : ℂ) *
      normalizedEisenstein ((ξ : ℂ) * I) x q * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := fun q hq =>
    ((continuous_amplitude_real g).mul (continuous_normalized_line x hq)).mul (continuous_phase τ)
  have hmeasF' : Continuous fun ξ : ℝ => pulseAmplitude g (ξ : ℂ) *
      covE 0 ((ξ : ℂ) * I) x Y * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) :=
    ((continuous_amplitude_real g).mul (continuous_covE_line 0 x hY)).mul (continuous_phase τ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (q : ℝ) (ξ : ℝ) => pulseAmplitude g (ξ : ℂ) * normalizedEisenstein ((ξ : ℂ) * I) x q *
      Complex.exp (I * (ξ : ℂ) * (τ : ℂ)))
    (F' := fun (q : ℝ) (ξ : ℝ) => pulseAmplitude g (ξ : ℂ) * covE 0 ((ξ : ℂ) * I) x q *
      Complex.exp (I * (ξ : ℂ) * (τ : ℂ)))
    (x₀ := Y) (s := Ioo (Y / 2) (2 * Y)) (bound := fun ξ => C * Ca * ((1 + |ξ|) ^ 2)⁻¹) hs
    (by
      filter_upwards [lt_mem_nhds hY] with q hq
      exact (hmeasF q hq).aestronglyMeasurable)
    (hb0.mono' (hmeasF Y hY).aestronglyMeasurable
      (Eventually.of_forall fun ξ => hbn _ ξ (hE ξ x Y (mem_window_self hY)).1))
    hmeasF'.aestronglyMeasurable
    (Eventually.of_forall fun ξ q hq => hbn _ ξ (by
      simpa [covE] using (hE ξ x q (Ioo_subset_Icc_self hq)).2.2.2.1))
    hb0
    (Eventually.of_forall fun ξ q hq => by
      have hq0 : 0 < q := by linarith [hq.1]
      have h1 := hasDerivAt_eisenstein_y ((ξ : ℂ) * I) x hq0
      have h2 := (h1.const_mul (pulseAmplitude g (ξ : ℂ))).mul_const
        (Complex.exp (I * (ξ : ℂ) * (τ : ℂ)))
      simpa [covE] using h2)
  exact key.2

/-- The derivative along the horocycle of the packet. -/
theorem hasDerivAt_pulsePacket_x (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q => pulsePacket g τ q Y) (-covPacket g 1 τ x Y) x := by
  obtain ⟨C, M, hC, hE⟩ := exists_eisenstein_jets_line_le_poly hY
  obtain ⟨Ca, hCa, ha⟩ := g.rapidAmplitude.exists_mul_poly_le 0 M
  have hb0 : Integrable fun ξ : ℝ => C * Ca * ((1 + |ξ|) ^ 2)⁻¹ :=
    integrable_inv_one_add_abs_sq.const_mul _
  have hbn : ∀ (K : ℂ) (ξ : ℝ), ‖K‖ ≤ C * (1 + |ξ|) ^ M →
      ‖pulseAmplitude g (ξ : ℂ) * K * Complex.exp (I * (ξ : ℂ) * (τ : ℂ))‖ ≤
        C * Ca * ((1 + |ξ|) ^ 2)⁻¹ := fun K ξ hK => by
    rw [norm_mul, norm_mul, norm_exp_I_mul, mul_one]
    have h1 := ha (ξ : ℂ) (by simp)
    simp only [Complex.ofReal_re] at h1
    calc ‖pulseAmplitude g (ξ : ℂ)‖ * ‖K‖ ≤ ‖pulseAmplitude g (ξ : ℂ)‖ * (C * (1 + |ξ|) ^ M) :=
          mul_le_mul_of_nonneg_left hK (norm_nonneg _)
      _ = C * (‖pulseAmplitude g (ξ : ℂ)‖ * (1 + |ξ|) ^ M) := by ring
      _ ≤ C * (Ca * ((1 + |ξ|) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 hC
      _ = _ := by ring
  have hmeasF : ∀ q : ℝ, Continuous fun ξ : ℝ => pulseAmplitude g (ξ : ℂ) *
      normalizedEisenstein ((ξ : ℂ) * I) q Y * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := fun q =>
    ((continuous_amplitude_real g).mul (continuous_normalized_line q hY)).mul (continuous_phase τ)
  have hc1 : Continuous fun ξ : ℝ => eisensteinX ((ξ : ℂ) * I) x Y := by
    have := (continuous_covE_line 1 x hY).neg
    refine this.congr fun ξ => ?_
    simp [covE]
  have hmeasF' : Continuous fun ξ : ℝ => pulseAmplitude g (ξ : ℂ) *
      eisensteinX ((ξ : ℂ) * I) x Y * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) :=
    ((continuous_amplitude_real g).mul hc1).mul (continuous_phase τ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (q : ℝ) (ξ : ℝ) => pulseAmplitude g (ξ : ℂ) * normalizedEisenstein ((ξ : ℂ) * I) q Y *
      Complex.exp (I * (ξ : ℂ) * (τ : ℂ)))
    (F' := fun (q : ℝ) (ξ : ℝ) => pulseAmplitude g (ξ : ℂ) * eisensteinX ((ξ : ℂ) * I) q Y *
      Complex.exp (I * (ξ : ℂ) * (τ : ℂ)))
    (x₀ := x) (s := univ) (bound := fun ξ => C * Ca * ((1 + |ξ|) ^ 2)⁻¹) univ_mem
    (Eventually.of_forall fun q => (hmeasF q).aestronglyMeasurable)
    (hb0.mono' (hmeasF x).aestronglyMeasurable
      (Eventually.of_forall fun ξ => hbn _ ξ (hE ξ x Y (mem_window_self hY)).1))
    hmeasF'.aestronglyMeasurable
    (Eventually.of_forall fun ξ q _ => hbn _ ξ (hE ξ q Y (mem_window_self hY)).2.1)
    hb0
    (Eventually.of_forall fun ξ q _ =>
      ((hasDerivAt_eisenstein_x ((ξ : ℂ) * I) q hY).const_mul (pulseAmplitude g (ξ : ℂ))).mul_const
        (Complex.exp (I * (ξ : ℂ) * (τ : ℂ))))
  have hval : (∫ ξ : ℝ, pulseAmplitude g (ξ : ℂ) * eisensteinX ((ξ : ℂ) * I) x Y *
      Complex.exp (I * (ξ : ℂ) * (τ : ℂ))) = -covPacket g 1 τ x Y := by
    rw [covPacket, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp [covE]
  rw [← hval]
  exact key.2

/-- **The covector of the image field is the packet of the gradient.** -/
theorem imageCov_eq_covPacket (i : Fin 2) {x : Fin 4 → ℝ} (hy : 0 < x 3) :
    imageCov g i τ x = covPacket g i τ (x 2) (x 3) := by
  fin_cases i
  · have h1 := imageCov_zero g τ hy
    have h2 := (hasDerivAt_pulsePacket_y g τ (x 2) hy).add_const (meanCoefficient g * Complex.exp ((τ : ℂ) / 2))
    have hev : (fun q => imageField g τ (x 2) q) =ᶠ[𝓝 (x 3)] fun q =>
        pulsePacket g τ (x 2) q + meanCoefficient g * Complex.exp ((τ : ℂ) / 2) := by
      filter_upwards [lt_mem_nhds hy] with q hq
      exact imageField_eq_packet g τ (x 2) hq
    exact h1.unique (h2.congr_of_eventuallyEq hev)
  · have h1 := imageCov_one g τ hy
    have h2 := (hasDerivAt_pulsePacket_x g τ (x 2) hy).add_const (meanCoefficient g * Complex.exp ((τ : ℂ) / 2))
    have hev : (fun q => imageField g τ q (x 3)) =
        fun q => pulsePacket g τ q (x 3) + meanCoefficient g * Complex.exp ((τ : ℂ) / 2) :=
      funext fun q => imageField_eq_packet g τ q hy
    rw [hev] at h1
    exact neg_injective (h1.unique h2)

end Packet

/-! ### The linear combinations of a pulse and its derivative -/

/-- The pulse `c h + h'`. -/
def pulseLin (c : ℂ) (h : CompactPulse) : CompactPulse where
  toFun S := c * h S + h.D S
  smooth := (contDiff_const.mul h.smooth).add h.D.smooth
  compact := (h.compact.mul_left (f := fun _ => c)).add h.D.compact

theorem pulseLin_D_apply (c : ℂ) (h : CompactPulse) (S : ℝ) :
    (pulseLin c h).D S = c * h.D S + h.D.D S :=
  (((h.hasDerivAt S).const_mul c).add (h.D.hasDerivAt S)).deriv

theorem imageCov_pulseLin (c : ℂ) (h : CompactPulse) (i : Fin 2) (τ : ℝ) {x : Fin 4 → ℝ} (hy : 0 < x 3) :
    imageCov (pulseLin c h) i τ x = c * imageCov h i τ x + imageCov h.D i τ x := by
  obtain ⟨S, hS⟩ := exists_finset_point h τ hy
  have hrow : ∀ s : ℝ, pulseF1 (pulseLin c h) (pulseLin c h).D τ s =
      c * pulseF1 h h.D τ s + pulseF1 h.D h.D.D τ s := fun s => by
    simp only [pulseF1]
    rw [pulseLin_D_apply]
    change _ * (_ * (c * h (τ + Real.log s) + h.D (τ + Real.log s)) + _) = _
    ring
  rw [imageCov, imageCov, imageCov, tsum_eq_sum (s := S) fun p hp => by
      rw [hrow, (hS p hp).1, (hS p hp).2]
      simp,
    tsum_eq_sum (s := S) fun p hp => by rw [(hS p hp).1, mul_zero],
    tsum_eq_sum (s := S) fun p hp => by rw [(hS p hp).2, mul_zero]]
  simp only [hrow, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    ring
  
theorem pulseAmplitude_pulseLin (c : ℂ) (h : CompactPulse) (w : ℂ) :
    pulseAmplitude (pulseLin c h) w = (c + I * w) * pulseAmplitude h w := by
  have hsplit : (∫ S : ℝ, (pulseLin c h) S * Complex.exp (-(I * w * (S : ℂ)))) =
      c * (∫ S : ℝ, h S * Complex.exp (-(I * w * (S : ℂ)))) +
        ∫ S : ℝ, h.D S * Complex.exp (-(I * w * (S : ℂ))) := by
    rw [← integral_const_mul, ← integral_add ((h.integrable_mul_cexp w).const_mul c)
      (h.D.integrable_mul_cexp w)]
    refine integral_congr_ae (Eventually.of_forall fun S => ?_)
    change (c * h S + h.D S) * _ = _
    ring
  have hD := h.amplitude_D w
  rw [pulseAmplitude] at hD ⊢
  rw [hsplit, mul_add, hD]
  simp only [pulseAmplitude]
  ring

/-! ### The ringdown of the metric -/

/-- The coefficient `F - ½` of the temporal block. -/
def cT (r : ℝ) : ℂ := (r : ℂ) * (r : ℂ) + (-1) - 1 / 2

/-- A point of the exterior. -/
def chart4 (t r x y : ℝ) : Fin 4 → ℝ := ![t, r, x, y]

theorem imageT_eq (h : CompactPulse) (i : Fin 2) (t r x : ℝ) {y : ℝ} (hy : 0 < y) :
    imageT h.profile i (chart4 t r x y) =
      Complex.exp (-(1 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) *
        covPacket (pulseLin (cT r) h) i (t + radialPhase r) x y := by
  have hy' : 0 < chart4 t r x y 3 := hy
  have h1 := imageT_profile h i hy'
  have h2 := imageCov_pulseLin (cT r) h i (hyperTime (chart4 t r x y)) hy'
  have h3 := imageCov_eq_covPacket (pulseLin (cT r) h) (hyperTime (chart4 t r x y)) i hy'
  have hF : rowF (chart4 t r x y) - 1 / 2 = cT r := rfl
  rw [h1, hF, ← h2, h3]
  rfl

theorem imageR_eq (h : CompactPulse) (i : Fin 2) (t r x : ℝ) {y : ℝ} (hy : 0 < y) :
    imageR h.profile i (chart4 t r x y) =
      (r : ℂ) * ((r : ℂ) * (r : ℂ) + (-1))⁻¹ * Complex.exp (-(1 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) *
        covPacket (pulseLin (-(1 / 2)) h) i (t + radialPhase r) x y := by
  have hy' : 0 < chart4 t r x y 3 := hy
  have h1 := imageR_profile h i hy'
  have h2 := imageCov_pulseLin (-(1 / 2)) h i (hyperTime (chart4 t r x y)) hy'
  have h3 := imageCov_eq_covPacket (pulseLin (-(1 / 2)) h) (hyperTime (chart4 t r x y)) i hy'
  have h4 : imageCov h.D i (hyperTime (chart4 t r x y)) (chart4 t r x y) -
      (1 / 2 : ℂ) * imageCov h i (hyperTime (chart4 t r x y)) (chart4 t r x y) =
      imageCov (pulseLin (-(1 / 2)) h) i (hyperTime (chart4 t r x y)) (chart4 t r x y) := by
    rw [h2]
    ring
  rw [h1, h4, h3]
  rfl

/-- **The ringdown of the temporal block of the metric.** -/
theorem imageT_ringdown (h : CompactPulse) (i : Fin 2) (r x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∃ Rem : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖Rem τ‖ ≤ C * Real.exp (-A * τ)) ∧
      ∀ t : ℝ, Tendsto (fun k => Complex.exp (-(1 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) *
          contourPartial (covPulseNum (pulseLin (cT r) h) i x y) (t + radialPhase r) k) atTop
        (𝓝 (imageT h.profile i (chart4 t r x y) -
          Complex.exp (-(1 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) * Rem (t + radialPhase r))) := by
  obtain ⟨Rem, hRem, hlim⟩ := cov_ringdown (pulseLin (cT r) h) i x hy
  refine ⟨Rem, hRem, fun t => ?_⟩
  set τ := t + radialPhase r with hτ
  have hat := (hlim |τ| (abs_nonneg τ)).tendsto_at (neg_abs_le τ : τ ∈ Ici (-|τ|))
  have h2 := hat.const_mul (Complex.exp (-(1 / 2 : ℂ) * (τ : ℂ)))
  rw [mul_sub, ← imageT_eq h i t r x hy] at h2
  exact h2

/-- **The ringdown of the radial block of the metric.** -/
theorem imageR_ringdown (h : CompactPulse) (i : Fin 2) (r x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∃ Rem : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖Rem τ‖ ≤ C * Real.exp (-A * τ)) ∧
      ∀ t : ℝ, Tendsto (fun k => (r : ℂ) * ((r : ℂ) * (r : ℂ) + (-1))⁻¹ *
          Complex.exp (-(1 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) *
          contourPartial (covPulseNum (pulseLin (-(1 / 2)) h) i x y) (t + radialPhase r) k) atTop
        (𝓝 (imageR h.profile i (chart4 t r x y) - (r : ℂ) * ((r : ℂ) * (r : ℂ) + (-1))⁻¹ *
          Complex.exp (-(1 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) * Rem (t + radialPhase r))) := by
  obtain ⟨Rem, hRem, hlim⟩ := cov_ringdown (pulseLin (-(1 / 2)) h) i x hy
  refine ⟨Rem, hRem, fun t => ?_⟩
  set τ := t + radialPhase r with hτ
  have hat := (hlim |τ| (abs_nonneg τ)).tendsto_at (neg_abs_le τ : τ ∈ Ici (-|τ|))
  have h2 := hat.const_mul ((r : ℂ) * ((r : ℂ) * (r : ℂ) + (-1))⁻¹ * Complex.exp (-(1 / 2 : ℂ) * (τ : ℂ)))
  rw [mul_sub, ← imageR_eq h i t r x hy] at h2
  exact h2

/-! ### The modes of the metric -/

/-- The amplitude of `c h + h'` at a zero. -/
theorem pulseAmplitude_pulseLin_rotated (c : ℂ) (h : CompactPulse) (p : ℂ) :
    pulseAmplitude (pulseLin c h) (-I * p) = (c + p) * pulseAmplitude h (-I * p) := by
  rw [pulseAmplitude_pulseLin]
  congr 1
  have : I * (-I * p) = p := by linear_combination (-p) * I_sq
  rw [this]

/-- **The modes of the temporal block.** -/
theorem imageT_mode (h : CompactPulse) (i : Fin 2) (r x : ℝ) {y : ℝ} (hy : 0 < y) {p : ℂ}
    (hp : xi (1 + 2 * p) = 0) :
    ∃ (n : ℕ) (e : ℕ → ℂ),
      analyticOrderAt (fun u : ℂ => xi (1 + 2 * u)) p = ((n + 1 : ℕ) : ℕ∞) ∧
      (e 0 = 0 ↔ cT r + p = 0 ∨ pulseAmplitude h (-I * p) = 0 ∨ covNum i p x y = 0) ∧
      ∀ τ : ℝ, laurentCoeff (inverseXiQuotient (timeNumerator (covPulseNum (pulseLin (cT r) h) i x y) τ))
          p (-1) = Complex.exp (p * (τ : ℂ)) * ∑ j ∈ Finset.range (n + 1),
            e j * (τ : ℂ) ^ (n - j) / ((n - j).factorial : ℂ) := by
  obtain ⟨n, e, h1, h2, h3⟩ := exists_contourMode
    (analyticAt_covPulseNum (pulseLin (cT r) h) i x hy (re_neg_of_xi_shift_eq_zero hp).le) hp
  refine ⟨n, e, h1, ?_, h3⟩
  rw [h2, covPulseNum, pulseAmplitude_pulseLin_rotated, mul_eq_zero, mul_eq_zero, or_assoc]

/-- **The modes of the radial block.** -/
theorem imageR_mode (h : CompactPulse) (i : Fin 2) (x : ℝ) {y : ℝ} (hy : 0 < y) {p : ℂ}
    (hp : xi (1 + 2 * p) = 0) :
    ∃ (n : ℕ) (e : ℕ → ℂ),
      analyticOrderAt (fun u : ℂ => xi (1 + 2 * u)) p = ((n + 1 : ℕ) : ℕ∞) ∧
      (e 0 = 0 ↔ pulseAmplitude h (-I * p) = 0 ∨ covNum i p x y = 0) ∧
      ∀ τ : ℝ, laurentCoeff (inverseXiQuotient
          (timeNumerator (covPulseNum (pulseLin (-(1 / 2)) h) i x y) τ))
          p (-1) = Complex.exp (p * (τ : ℂ)) * ∑ j ∈ Finset.range (n + 1),
            e j * (τ : ℂ) ^ (n - j) / ((n - j).factorial : ℂ) := by
  obtain ⟨n, e, h1, h2, h3⟩ := exists_contourMode
    (analyticAt_covPulseNum (pulseLin (-(1 / 2)) h) i x hy (re_neg_of_xi_shift_eq_zero hp).le) hp
  refine ⟨n, e, h1, ?_, h3⟩
  have hne : -(1 / 2 : ℂ) + p ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    have hre := re_neg_of_xi_shift_eq_zero hp
    simp at this
    linarith
  rw [h2, covPulseNum, pulseAmplitude_pulseLin_rotated, mul_eq_zero, mul_eq_zero, or_assoc,
    or_iff_right hne]

/-- **Each zero is excited in the metric**: there is a pulse and a point of the horizon where the top coefficient of the
radial block of the metric does not vanish. -/
theorem exists_metric_excitation {p : ℂ} (hp : xi (1 + 2 * p) = 0) :
    ∃ (h : CompactPulse) (i : Fin 2) (x y : ℝ), 0 < y ∧
      pulseAmplitude h (-I * p) ≠ 0 ∧ covNum i p x y ≠ 0 := by
  obtain ⟨z, hz, k, hk⟩ := exists_gradCovector_ne_zero hp
  refine ⟨excitingPulse p, k, z 0, z 1, hz, pulseAmplitude_excitingPulse_ne_zero p, ?_⟩
  fin_cases k
  · have h0 : gradCovector (numeratorField p) 0 z = numY p (z 0) (z 1) :=
      coordDeriv_one_numerator p hz
    have h1 : gradCovector (numeratorField p) 0 z ≠ 0 := hk
    rw [h0] at h1
    simpa [covNum] using h1
  · have h0 : gradCovector (numeratorField p) 1 z = -numX p (z 0) (z 1) := by
      change -coordDeriv 0 (numeratorField p) z = _
      rw [coordDeriv_zero_numerator p hz]
    have h1 : gradCovector (numeratorField p) 1 z ≠ 0 := hk
    rw [h0] at h1
    simpa [covNum] using h1

end GaloisForLFunctions.BlackHoleRingdown

end

import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointConfinement
import GaloisForLFunctions.RHTower.XiCosineShiftAlmostEveryHeight
import GaloisForLFunctions.RHTower.PhotonicLosslessHeatFlowFiniteDefect
import GaloisForLFunctions.HTGeometry.AnalyticRootFactor
import GaloisForLFunctions.HTGeometry.LocallyUniformZeroCountTransfer

/-!
# RH is the absence of exceptional points of the cosine producer

Let `A_h(z) = (Ξ(z + ih) + Ξ(z − ih))/2` be the cosine producer (`cosProducer`).

**Theorem** (`riemannHypothesis_iff_cosProducer_no_exceptionalPoint`). RH holds iff for every
`0 < h < ½`, every real zero of `A_h` is simple: the lossless producer has no exceptional point
(no collision of real resonances).

`⇒` is exceptional-point confinement (`deriv_cosineShiftXi_ne_zero_of_rh`).

`⇐`, by contradiction. Let `w` be a non-real zero of `Ξ`.
1. By Hurwitz, `A_{h₀}` has a non-real zero near `w` for some small `h₀ > 0`.
2. The heights carrying a non-real zero of some `A_h`, `h ≥ h₀`, have small measure
   (`eventually_volume_cosineShift_nonrealHeight_le`). Pick such a defect-free height `R` beyond
   that zero; by evenness `−R` is defect-free too. So for `h ≥ h₀` no defect crosses the vertical
   sides of the box `|Re z| ≤ R`.
3. The finitely many zeros of `Ξ` below height `R + 1` have depth `< ½`. Hence there is
   `h_top < ½` such that for `h > h_top`, `A_h` has no defect in the box (defect disks).
4. Let `h*` be the supremum of the depths `h ≥ h₀` with a defect in the box. Take defects at depths
   `h_n → h*` and a limit point `z*`.
   * If `z*` were non-real, it would lie strictly inside the box, and by Hurwitz the defect would
     persist past `h*`.
   * So `z*` is real, and it is the limit of the conjugate pairs `z_n, z̄_n`. Hence `z*` is a
     multiple zero of `A_{h*}`, with `0 < h* < ½`: an exceptional point.

So every failure of RH forces a collision of two real resonances of the producer at some depth
`0 < h < ½`, located (by confinement) inside the trace of a zero deeper than that depth.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The cosine producer `cos(hD)Ξ`. -/
def cosProducer (h : ℝ) (z : ℂ) : ℂ := (XiC (z + h * I) + XiC (z - h * I)) / 2

theorem differentiable_XiC : Differentiable ℂ XiC := by
  rw [← DeBruijn.cosTransform_riemannKernel_eq_XiC]
  exact DeBruijn.riemannKernel_superExp.differentiable

theorem differentiable_cosProducer (h : ℝ) : Differentiable ℂ (cosProducer h) := by
  unfold cosProducer
  have := differentiable_XiC
  fun_prop

theorem continuous_cosProducer_uncurry :
    Continuous (fun p : ℝ × ℂ => cosProducer p.1 p.2) := by
  unfold cosProducer
  have := differentiable_XiC.continuous
  fun_prop

theorem cosProducer_neg (h : ℝ) (z : ℂ) : cosProducer h (-z) = cosProducer h z := by
  unfold cosProducer
  have e1 : -z + h * I = -(z - h * I) := by ring
  have e2 : -z - h * I = -(z + h * I) := by ring
  rw [e1, e2, DeBruijn.XiC_neg', DeBruijn.XiC_neg', add_comm]

theorem cosProducer_conj (h : ℝ) (z : ℂ) :
    cosProducer h ((starRingEnd ℂ) z) = (starRingEnd ℂ) (cosProducer h z) := by
  unfold cosProducer
  have e1 : (starRingEnd ℂ) z + h * I = (starRingEnd ℂ) (z - h * I) := by
    rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have e2 : (starRingEnd ℂ) z - h * I = (starRingEnd ℂ) (z + h * I) := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [e1, e2, DeBruijn.XiC_conj', DeBruijn.XiC_conj']
  simp only [map_div₀, map_add, map_ofNat]
  ring

theorem cosProducer_eq_cosTransform (h : ℝ) :
    cosProducer h = DeBruijn.cosTransform (fun x => riemannKernelReal x * Real.cosh (h * x)) :=
  (funext (DeBruijn.cosTransform_riemannKernel_mul_cosh h)).symm

theorem analyticOrderAt_cosProducer_ne_top (h : ℝ) (z : ℂ) :
    analyticOrderAt (cosProducer h) z ≠ ⊤ := by
  have hg := DeBruijn.riemannKernel_mul_cosh_superExp h
  rw [cosProducer_eq_cosTransform]
  exact DeBruijn.analyticOrderAt_ne_top_of_ne_zero
    (hg.differentiable.differentiableOn.analyticOnNhd isOpen_univ) hg.cosTransform_zero_ne z

theorem analyticOrderAt_XiC_ne_top (z : ℂ) : analyticOrderAt XiC z ≠ ⊤ := by
  have hg := DeBruijn.riemannKernel_superExp
  rw [← DeBruijn.cosTransform_riemannKernel_eq_XiC]
  exact DeBruijn.analyticOrderAt_ne_top_of_ne_zero
    (hg.differentiable.differentiableOn.analyticOnNhd isOpen_univ) hg.cosTransform_zero_ne z

theorem abs_im_le_half_of_cosProducer_eq_zero {h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz : cosProducer h z = 0) : |z.im| ≤ 1 / 2 := by
  have h1 := DeBruijn.cosineShift_zeros_im_sq_le hh hz
  have h2 : z.im ^ 2 ≤ (1 / 2) ^ 2 := h1.trans (max_le (by nlinarith) (by norm_num))
  have := sq_le_sq.mp h2
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this

/-! ## Local zero counts of an entire function -/

theorem one_le_zeroMult_of_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfin : ∀ z, analyticOrderAt f z ≠ ⊤) {z : ℂ} (hz : f z = 0) : 1 ≤ zeroMult f z := by
  have han : AnalyticAt ℂ f z := hf.analyticAt z
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hfin z)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (han.analyticOrderAt_eq_zero.mp (by rw [← hn]; rfl)) hz
  unfold zeroMult
  rw [← hn, ENat.toNat_coe]
  omega

/-- **Isolating discs.** -/
theorem exists_radius_zeroSumBall_eq_zeroMult {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfin : ∀ z, analyticOrderAt f z ≠ ⊤) (z₀ : ℂ) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ →
      (∀ w ∈ sphere z₀ r, f w ≠ 0) ∧ zeroSumBall f z₀ r = (zeroMult f z₀ : ℂ) := by
  classical
  have han : AnalyticAt ℂ f z₀ := hf.analyticAt z₀
  obtain ⟨ρ, hρ, hiso⟩ : ∃ ρ > 0, ∀ w ∈ ball z₀ ρ, w ≠ z₀ → f w ≠ 0 := by
    rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) (hfin z₀)
    · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
      obtain ⟨ρ, hρ, hball⟩ := h
      exact ⟨ρ, hρ, fun w hw hne => hball (mem_ball.mp hw) hne⟩
  refine ⟨ρ / 2, by positivity, fun r hr hrρ => ?_⟩
  have hsph : ∀ w ∈ sphere z₀ r, f w ≠ 0 := by
    intro w hw
    have hwr : dist w z₀ = r := mem_sphere.mp hw
    refine hiso w (mem_ball.mpr (by linarith)) ?_
    intro hwz
    rw [hwz, dist_self] at hwr
    linarith
  refine ⟨hsph, ?_⟩
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall hr (by linarith : r < 2 * r)
    isOpen_univ (subset_univ _) hf.differentiableOn hsph
  rw [hsum]
  have hZsub : Z ⊆ {z₀} := by
    intro w hw
    have hwb := hZball w hw
    have hw0 := (hZzero w hwb).mpr hw
    by_contra hne
    exact hiso w (mem_ball.mpr ((mem_ball.mp hwb).trans (by linarith)))
      (by simpa using hne) hw0
  by_cases hz : f z₀ = 0
  · have hZ : Z = {z₀} := Finset.Subset.antisymm hZsub (Finset.singleton_subset_iff.mpr
      ((hZzero z₀ (mem_ball_self hr)).mp hz))
    rw [hZ, Finset.sum_singleton]
  · have hZ : Z = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
      have := Finset.mem_singleton.mp (hZsub hw)
      subst this
      exact hz ((hZzero w (hZball w hw)).mpr hw)
    have hm : zeroMult f z₀ = 0 := by
      unfold zeroMult
      rw [(han.analyticOrderAt_eq_zero).mpr hz]
      rfl
    rw [hZ, Finset.sum_empty, hm]
    simp

/-- A zero with nonzero derivative has multiplicity one. -/
theorem zeroMult_eq_one_of_deriv_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z : ℂ}
    (hz : f z = 0) (hd : deriv f z ≠ 0) : zeroMult f z = 1 := by
  have han : AnalyticAt ℂ f z := hf.analyticAt z
  have hord : analyticOrderAt f z = (1 : ℕ) := by
    rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han]
    refine ⟨fun k hk => ?_, ?_⟩
    · have : k = 0 := by omega
      subst this
      simpa using hz
    · simpa using hd
  unfold zeroMult
  rw [hord]
  rfl

/-- **Zero persistence (Hurwitz).** If `F_a → f` locally uniformly and `z₀` is a zero of `f`, then
for every small `r > 0`, eventually `F_a` has a zero in `ball z₀ r`. -/
theorem eventually_exists_zero_mem_ball {α : Type*} {p : Filter α} {F : α → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ a, Differentiable ℂ (F a)) (hf : Differentiable ℂ f)
    (hfin : ∀ z, analyticOrderAt f z ≠ ⊤) (hconv : TendstoLocallyUniformly F f p) {z₀ : ℂ}
    (hz₀ : f z₀ = 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ a in p, ∃ z ∈ ball z₀ r, F a z = 0 := by
  classical
  obtain ⟨r₀, hr₀, hiso⟩ := exists_radius_zeroSumBall_eq_zeroMult hf hfin z₀
  set s := min r r₀ with hs
  have hs0 : 0 < s := lt_min hr hr₀
  obtain ⟨hsph, hcount⟩ := hiso s hs0 (min_le_right _ _)
  have hm := one_le_zeroMult_of_eq_zero hf hfin hz₀
  filter_upwards [eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hF hf hconv hs0
    (by linarith : s < 2 * s) hsph,
    LeeYangCount.eventually_ne_zero_on_sphere hf.continuous hconv hsph] with a ha hasph
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall hs0 (by linarith : s < 2 * s)
    isOpen_univ (subset_univ _) (hF a).differentiableOn hasph
  by_contra hno
  push Not at hno
  have hZ : Z = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
    have hwb := hZball w hw
    exact hno w (mem_ball.mpr ((mem_ball.mp hwb).trans_le (min_le_left _ _)))
      ((hZzero w hwb).mpr hw)
  rw [ha, hcount, hZ, Finset.sum_empty] at hsum
  have : (zeroMult f z₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : zeroMult f z₀ ≠ 0)
  exact this hsum

/-! ## Continuity in the depth -/

/-- `A_h → A_{h₀}` locally uniformly as `h → h₀`. -/
theorem tendstoLocallyUniformly_cosProducer (h₀ : ℝ) :
    TendstoLocallyUniformly (fun h => cosProducer h) (cosProducer h₀) (𝓝 h₀) := by
  have hXc : Continuous XiC := differentiable_XiC.continuous
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set ρ : ℝ := |h₀| + 1 with hρ
  have hK' : IsCompact (cthickening ρ K) := hK.cthickening
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp
    (hK'.uniformContinuousOn_of_continuous hXc.continuousOn) ε hε
  have hev : ∀ᶠ h in 𝓝 h₀, |h - h₀| < min δ 1 := by
    have := Metric.ball_mem_nhds h₀ (lt_min hδ one_pos)
    filter_upwards [this] with h hh
    rwa [mem_ball, Real.dist_eq] at hh
  filter_upwards [hev] with h hh z hz
  have hh1 : |h - h₀| < 1 := hh.trans_le (min_le_right _ _)
  have hhδ : |h - h₀| < δ := hh.trans_le (min_le_left _ _)
  have hmem : ∀ c : ℝ, |c| ≤ ρ → ∀ s : ℂ, s = z + c * I ∨ s = z - c * I → s ∈ cthickening ρ K := by
    intro c hc s hs
    refine Metric.mem_cthickening_of_dist_le _ z ρ K hz ?_
    rcases hs with rfl | rfl
    · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]; exact hc
    · rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]; exact hc
  have hc0 : |h₀| ≤ ρ := by rw [hρ]; linarith
  have hc1 : |h| ≤ ρ := by
    have := abs_sub_abs_le_abs_sub h h₀
    rw [hρ]; linarith
  have d1 : dist (z + h₀ * I) (z + h * I) = |h - h₀| := by
    rw [dist_eq_norm, show z + (h₀ : ℂ) * I - (z + h * I) = ((h₀ - h : ℝ) : ℂ) * I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have d2 : dist (z - h₀ * I) (z - h * I) = |h - h₀| := by
    rw [dist_eq_norm, show z - (h₀ : ℂ) * I - (z - h * I) = ((h - h₀ : ℝ) : ℂ) * I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have e1 := hδu _ (hmem h₀ hc0 _ (Or.inl rfl)) _ (hmem h hc1 _ (Or.inl rfl)) (by rw [d1]; exact hhδ)
  have e2 := hδu _ (hmem h₀ hc0 _ (Or.inr rfl)) _ (hmem h hc1 _ (Or.inr rfl)) (by rw [d2]; exact hhδ)
  unfold cosProducer
  rw [dist_eq_norm] at e1 e2 ⊢
  have : (XiC (z + h₀ * I) + XiC (z - h₀ * I)) / 2 - (XiC (z + h * I) + XiC (z - h * I)) / 2 =
      ((XiC (z + h₀ * I) - XiC (z + h * I)) + (XiC (z - h₀ * I) - XiC (z - h * I))) / 2 := by ring
  rw [this, norm_div, Complex.norm_two]
  have := norm_add_le (XiC (z + h₀ * I) - XiC (z + h * I)) (XiC (z - h₀ * I) - XiC (z - h * I))
  linarith

/-- A finite set of zeros of `Ξ` has a uniform depth bound below `½`. -/
theorem exists_depth_bound_of_finite {E : Set ℂ} (hE : E.Finite) (hzero : ∀ w ∈ E, XiC w = 0) :
    ∃ m : ℝ, m < 1 / 2 ∧ 0 ≤ m ∧ ∀ w ∈ E, |w.im| ≤ m := by
  classical
  have hlt : ∀ w ∈ E, |w.im| < 1 / 2 := by
    intro w hw
    have hxi : xi (1 / 2 + w * I) = 0 := by rw [← hzero w hw, XiC]
    obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hxi
    have hre : (1 / 2 + w * I).re = 1 / 2 - w.im := by simp; ring
    rw [hre] at h0 h1
    rw [abs_lt]; constructor <;> linarith
  rcases hE.toFinset.eq_empty_or_nonempty with he | hne
  · refine ⟨0, by norm_num, le_rfl, fun w hw => ?_⟩
    have : w ∈ hE.toFinset := hE.mem_toFinset.mpr hw
    rw [he] at this
    exact absurd this (Finset.notMem_empty _)
  · obtain ⟨w₀, hw₀, hmax⟩ := hE.toFinset.exists_max_image (fun w => |w.im|) hne
    refine ⟨|w₀.im|, hlt w₀ (hE.mem_toFinset.mp hw₀), abs_nonneg _, fun w hw => ?_⟩
    exact hmax w (hE.mem_toFinset.mpr hw)

/-! ## The criterion -/

/-- **No exceptional points ⇒ RH.** If for every `0 < h < ½` every real zero of `cos(hD)Ξ` is
simple, then RH holds. -/
theorem riemannHypothesis_of_cosProducer_no_exceptionalPoint
    (hno : ∀ h : ℝ, 0 < h → h < 1 / 2 → ∀ x : ℝ, cosProducer h x = 0 →
      deriv (cosProducer h) x ≠ 0) : RiemannHypothesis := by
  classical
  by_contra hRH
  -- a non-real zero of `Ξ`
  obtain ⟨w, hw, hwim⟩ : ∃ w, XiC w = 0 ∧ w.im ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hRH
    refine DeBruijn.riemannHypothesis_iff_riemannHeat_zero_real.mpr fun z hz => ?_
    rw [riemannHeat_zero_eq_XiC] at hz
    exact hall z hz
  -- a non-real zero of `A_{h₀}` for a small `h₀`
  have hconv0 : TendstoLocallyUniformly (fun (n : ℕ) => cosProducer (1 / ((n : ℝ) + 1))) XiC
      atTop := tendstoLocallyUniformly_cosineShift_XiC
  have hr : 0 < |w.im| / 2 := by have := abs_pos.mpr hwim; positivity
  obtain ⟨n, ⟨z₀, hz₀b, hz₀⟩, hn2⟩ := ((eventually_exists_zero_mem_ball
    (fun n => differentiable_cosProducer _) differentiable_XiC analyticOrderAt_XiC_ne_top hconv0 hw
    hr).and (eventually_ge_atTop 2)).exists
  set h₀ : ℝ := 1 / ((n : ℝ) + 1) with hh₀def
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hh₀ : 0 < h₀ := by positivity
  have hh₀half : h₀ < 1 / 2 := by
    rw [hh₀def, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hz₀im : z₀.im ≠ 0 := by
    intro h0
    have hd := mem_ball.mp hz₀b
    have him : |z₀.im - w.im| ≤ dist z₀ w := by
      rw [dist_eq_norm]; have := Complex.abs_im_le_norm (z₀ - w); simpa using this
    rw [h0, zero_sub, abs_neg] at him
    linarith
  -- a defect-free height `R`
  obtain ⟨U, ⟨T₁, hT₁, T₂, hT₂, hS⟩, hUbig⟩ :=
    ((eventually_volume_cosineShift_nonrealHeight_le hh₀ (by norm_num : (0 : ℝ) < 1 / 4)).and
      (eventually_ge_atTop (100 + 4 * |z₀.re|))).exists
  obtain ⟨R, hR, hRS⟩ : ∃ R ∈ Icc (T₁ + 1) (T₂ - 1), R ∉ {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
      ∃ h' : ℝ, h₀ ≤ h' ∧ ∃ z : ℂ, z.re = x ∧ z.im ≠ 0 ∧
        (XiC (z + h' * I) + XiC (z - h' * I)) / 2 = 0} := by
    by_contra hall
    push Not at hall
    have hsub : Icc (T₁ + 1) (T₂ - 1) ⊆ {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
        ∃ h' : ℝ, h₀ ≤ h' ∧ ∃ z : ℂ, z.re = x ∧ z.im ≠ 0 ∧
          (XiC (z + h' * I) + XiC (z - h' * I)) / 2 = 0} := fun x hx => hall x hx
    have hle := (measure_mono hsub).trans hS
    rw [Real.volume_Icc] at hle
    have hT : 20 ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1, abs_nonneg z₀.re]
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
    linarith
  have hRbig : |z₀.re| + 1 < R := by linarith [hR.1, hT₁.1, abs_nonneg z₀.re]
  have hRpos : 0 < R := by linarith [abs_nonneg z₀.re]
  have hRfree : ∀ h' : ℝ, h₀ ≤ h' → ∀ z : ℂ, z.im ≠ 0 → cosProducer h' z = 0 → |z.re| ≠ R := by
    intro h' hh' z hz h0 habs
    rcases abs_eq hRpos.le |>.mp habs with hre | hre
    · exact hRS ⟨hR, h', hh', z, hre, hz, h0⟩
    · refine hRS ⟨hR, h', hh', -z, by rw [Complex.neg_re, hre, neg_neg], by simpa using hz, ?_⟩
      have := cosProducer_neg h' z
      unfold cosProducer at this
      rw [this]; exact h0
  -- a depth bound below height `R + 1`
  have hEfin : {w' ∈ closedBall (0 : ℂ) (R + 2) | XiC w' = 0}.Finite :=
    finite_zeros_closedBall (fun z _ => differentiable_XiC.analyticAt z)
      (fun z _ h => analyticOrderAt_XiC_ne_top z (analyticOrderAt_eq_top.mpr h))
  obtain ⟨m, hmhalf, hm0, hmE⟩ := exists_depth_bound_of_finite hEfin (fun w' hw' => hw'.2)
  set htop : ℝ := max h₀ m with hhtop
  have htophalf : htop < 1 / 2 := max_lt hh₀half hmhalf
  have hnodef : ∀ h : ℝ, htop < h → ∀ z : ℂ, |z.re| ≤ R → cosProducer h z = 0 → z.im = 0 := by
    intro h hh z hzR h0
    by_contra hz
    have hhpos : 0 < h := lt_of_le_of_lt (le_trans hh₀.le (le_max_left _ _)) hh
    obtain ⟨w', hw', hdisk⟩ := DeBruijn.cosineShift_nonreal_zero_mem_defectDisk hhpos hz h0
    have hw'sq : w'.im ^ 2 ≤ 1 / 4 :=
      DeBruijn.riemannKernel_zeros_im_sq_le w'
        (by rw [DeBruijn.cosTransform_riemannKernel_eq_XiC]; exact hw')
    have hzsq : 0 < z.im ^ 2 := by positivity
    have hclose : |w'.re - z.re| ≤ 1 / 2 := by
      have := sq_le_sq.mp (show (w'.re - z.re) ^ 2 ≤ (1 / 2) ^ 2 by nlinarith)
      rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    have hw'im : |w'.im| ≤ 1 / 2 := by
      have := sq_le_sq.mp (show w'.im ^ 2 ≤ (1 / 2) ^ 2 by linarith)
      rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    have hw'E : w' ∈ {w' ∈ closedBall (0 : ℂ) (R + 2) | XiC w' = 0} := by
      refine ⟨?_, hw'⟩
      rw [mem_closedBall, dist_zero_right]
      have := Complex.norm_le_abs_re_add_abs_im w'
      have := abs_sub_abs_le_abs_sub w'.re z.re
      linarith
    have h1 := hmE w' hw'E
    have hdeep : h < |w'.im| := by
      have h2 : h ^ 2 < w'.im ^ 2 := by nlinarith [sq_nonneg (w'.re - z.re)]
      have := sq_lt_sq.mp h2
      rwa [abs_of_pos hhpos] at this
    have : m ≤ htop := le_max_right _ _
    linarith
  -- the supremum of the defective depths
  set SF : Set ℝ := {h : ℝ | h₀ ≤ h ∧ ∃ z : ℂ, |z.re| ≤ R ∧ z.im ≠ 0 ∧ cosProducer h z = 0}
    with hSFdef
  have hh₀SF : h₀ ∈ SF := ⟨le_rfl, z₀, by linarith, hz₀im, hz₀⟩
  have hbdd : BddAbove SF := by
    refine ⟨htop, fun h hh => ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨-, z, hzR, hz, h0⟩ := hh
    exact hz (hnodef h hlt z hzR h0)
  set hstar := sSup SF with hstardef
  have hstar_ge : h₀ ≤ hstar := le_csSup hbdd hh₀SF
  have hstar_le : hstar ≤ htop := csSup_le ⟨h₀, hh₀SF⟩ fun h hh => by
    by_contra hlt
    push Not at hlt
    obtain ⟨-, z, hzR, hz, h0⟩ := hh
    exact hz (hnodef h hlt z hzR h0)
  have hstarpos : 0 < hstar := lt_of_lt_of_le hh₀ hstar_ge
  have hstarhalf : hstar < 1 / 2 := lt_of_le_of_lt hstar_le htophalf
  obtain ⟨u, -, hu, huSF⟩ := exists_seq_tendsto_sSup ⟨h₀, hh₀SF⟩ hbdd
  choose zs hzsR hzsim hzs0 using fun k => (huSF k).2
  have hupos : ∀ k, 0 < u k := fun k => lt_of_lt_of_le hh₀ (huSF k).1
  have hzsK : ∀ k, zs k ∈ closedBall (0 : ℂ) (R + 1) := by
    intro k
    rw [mem_closedBall, dist_zero_right]
    have := Complex.norm_le_abs_re_add_abs_im (zs k)
    have := abs_im_le_half_of_cosProducer_eq_zero (hupos k) (hzs0 k)
    linarith [hzsR k]
  obtain ⟨zstar, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) (R + 1)).tendsto_subseq hzsK
  have huφ : Tendsto (u ∘ φ) atTop (𝓝 hstar) := hu.comp hφ.tendsto_atTop
  have hzstar0 : cosProducer hstar zstar = 0 := by
    have hpair : Tendsto (fun k => (u (φ k), zs (φ k))) atTop (𝓝 (hstar, zstar)) :=
      huφ.prodMk_nhds hlim
    have h1 := (continuous_cosProducer_uncurry.tendsto (hstar, zstar)).comp hpair
    have h2 : (fun k => cosProducer (u (φ k)) (zs (φ k))) = fun _ => (0 : ℂ) := by
      funext k; exact hzs0 (φ k)
    have h3 : Tendsto (fun k => cosProducer (u (φ k)) (zs (φ k))) atTop
        (𝓝 (cosProducer hstar zstar)) := h1
    rw [h2] at h3
    exact (tendsto_nhds_unique h3 tendsto_const_nhds)
  have hzstarR : |zstar.re| ≤ R := by
    have hc : Tendsto (fun k => |(zs (φ k)).re|) atTop (𝓝 |zstar.re|) :=
      ((Complex.continuous_re.tendsto zstar).comp hlim).abs
    exact le_of_tendsto hc (Eventually.of_forall fun k => hzsR (φ k))
  by_cases hzim : zstar.im = 0
  · -- the limit is real: a collision
    obtain ⟨x, hx⟩ : ∃ x : ℝ, zstar = (x : ℂ) :=
      ⟨zstar.re, Complex.ext (by simp) (by simp [hzim])⟩
    subst hx
    have hd := hno hstar hstarpos hstarhalf x hzstar0
    have hm1 := zeroMult_eq_one_of_deriv_ne_zero (differentiable_cosProducer hstar) hzstar0 hd
    obtain ⟨r₀, hr₀, hiso⟩ := exists_radius_zeroSumBall_eq_zeroMult
      (differentiable_cosProducer hstar) (analyticOrderAt_cosProducer_ne_top hstar) (x : ℂ)
    obtain ⟨hsph, hcount⟩ := hiso r₀ hr₀ le_rfl
    rw [hm1] at hcount
    have hconv := tendstoLocallyUniformly_cosProducer hstar
    have hevc := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
      (fun h => differentiable_cosProducer h) (differentiable_cosProducer hstar) hconv hr₀
      (by linarith : r₀ < 2 * r₀) hsph
    have hevs := LeeYangCount.eventually_ne_zero_on_sphere
      (differentiable_cosProducer hstar).continuous hconv hsph
    have hball : ∀ᶠ k in atTop, zs (φ k) ∈ ball (x : ℂ) r₀ :=
      hlim.eventually (Metric.ball_mem_nhds (x : ℂ) hr₀)
    obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := ((huφ.eventually (hevc.and hevs)).and hball).exists
    set h := u (φ k)
    set z := zs (φ k)
    have hzc0 : cosProducer h ((starRingEnd ℂ) z) = 0 := by
      rw [cosProducer_conj, hzs0 (φ k), map_zero]
    have hzcb : (starRingEnd ℂ) z ∈ ball (x : ℂ) r₀ := by
      rw [mem_ball] at hk3 ⊢
      rw [dist_eq_norm] at hk3 ⊢
      have e : (starRingEnd ℂ) z - x = (starRingEnd ℂ) (z - x) := by
        rw [map_sub, Complex.conj_ofReal]
      rw [e, Complex.norm_conj]; exact hk3
    have hne : z ≠ (starRingEnd ℂ) z := by
      intro he
      have := congrArg Complex.im he
      rw [Complex.conj_im] at this
      exact hzsim (φ k) (by linarith)
    obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall hr₀ (by linarith : r₀ < 2 * r₀)
      isOpen_univ (subset_univ _) (differentiable_cosProducer h).differentiableOn hk2
    have hzZ : z ∈ Z := (hZzero z hk3).mp (hzs0 (φ k))
    have hzcZ : (starRingEnd ℂ) z ∈ Z := (hZzero _ hzcb).mp hzc0
    have hpairsub : ({z, (starRingEnd ℂ) z} : Finset ℂ) ⊆ Z := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hzZ
      · rw [Finset.mem_singleton.mp hy]; exact hzcZ
    have hge : 2 ≤ ∑ ρ ∈ Z, zeroMult (cosProducer h) ρ := by
      calc 2 = ∑ ρ ∈ ({z, (starRingEnd ℂ) z} : Finset ℂ), 1 := by
            rw [Finset.sum_const, Finset.card_pair hne]; rfl
        _ ≤ ∑ ρ ∈ ({z, (starRingEnd ℂ) z} : Finset ℂ), zeroMult (cosProducer h) ρ := by
            refine Finset.sum_le_sum fun ρ hρ => ?_
            refine one_le_zeroMult_of_eq_zero (differentiable_cosProducer h)
              (analyticOrderAt_cosProducer_ne_top h) ?_
            rcases Finset.mem_insert.mp hρ with rfl | hρ
            · exact hzs0 (φ k)
            · rw [Finset.mem_singleton.mp hρ]; exact hzc0
        _ ≤ ∑ ρ ∈ Z, zeroMult (cosProducer h) ρ :=
            Finset.sum_le_sum_of_subset_of_nonneg hpairsub fun _ _ _ => Nat.zero_le _
    have hk1' : zeroSumBall (cosProducer h) (x : ℂ) r₀ = ((1 : ℕ) : ℂ) := hk1.trans hcount
    rw [hk1'] at hsum
    have : ∑ ρ ∈ Z, zeroMult (cosProducer h) ρ = 1 := by exact_mod_cast hsum.symm
    omega
  · -- the limit is non-real: the defect persists past `hstar`
    have hzR' : |zstar.re| < R := by
      rcases lt_or_eq_of_le hzstarR with h | h
      · exact h
      · exact absurd h (hRfree hstar hstar_ge zstar hzim hzstar0)
    set ρr : ℝ := min (|zstar.im|) (R - |zstar.re|) with hρr
    have hρr0 : 0 < ρr := lt_min (abs_pos.mpr hzim) (by linarith)
    have hev := eventually_exists_zero_mem_ball (fun h => differentiable_cosProducer h)
      (differentiable_cosProducer hstar) (analyticOrderAt_cosProducer_ne_top hstar)
      (tendstoLocallyUniformly_cosProducer hstar) hzstar0 hρr0
    obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨z, hzb, hz0⟩ := hδev (y := hstar + δ / 2)
      (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
    have hd : dist z zstar < ρr := mem_ball.mp hzb
    have hzim' : z.im ≠ 0 := by
      intro h0
      have : |z.im - zstar.im| ≤ dist z zstar := by
        rw [dist_eq_norm]; have := Complex.abs_im_le_norm (z - zstar); simpa using this
      rw [h0, zero_sub, abs_neg] at this
      linarith [min_le_left (|zstar.im|) (R - |zstar.re|)]
    have hzre' : |z.re| ≤ R := by
      have : |z.re - zstar.re| ≤ dist z zstar := by
        rw [dist_eq_norm]; have := Complex.abs_re_le_norm (z - zstar); simpa using this
      have := abs_sub_abs_le_abs_sub z.re zstar.re
      linarith [min_le_right (|zstar.im|) (R - |zstar.re|)]
    have hmem : hstar + δ / 2 ∈ SF := ⟨by linarith, z, hzre', hzim', hz0⟩
    have := le_csSup hbdd hmem
    linarith

/-- **RH ⇔ the cosine producer has no exceptional points.** RH holds iff for every `0 < h < ½`
every real zero of `cos(hD)Ξ` is simple. -/
theorem riemannHypothesis_iff_cosProducer_no_exceptionalPoint :
    RiemannHypothesis ↔ ∀ h : ℝ, 0 < h → h < 1 / 2 → ∀ x : ℝ, cosProducer h x = 0 →
      deriv (cosProducer h) x ≠ 0 :=
  ⟨fun hRH _ hh _ _ hx => deriv_cosineShiftXi_ne_zero_of_rh hRH hh hx,
    riemannHypothesis_of_cosProducer_no_exceptionalPoint⟩

end

end RHTower

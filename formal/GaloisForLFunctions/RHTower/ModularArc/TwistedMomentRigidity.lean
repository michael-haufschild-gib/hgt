import GaloisForLFunctions.RHTower.TwistedArcMinimumPrincipleProof

/-!
# Nonnegative twisted Whittaker sums on the modular arc

A finite twisted Whittaker sum nonnegative on the half arc vanishes there.
Clamped Legendre kernels retain a fixed positive fraction of an interior
kernel, linear in the distance to the corner. Positive weighted arc mass
would therefore contradict the stream function's corner derivative sign.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

private theorem legendreDensity_half_comparison {c s : ℝ}
    (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hs : s ∈ Icc (0 : ℝ) (1 / 2)) :
    (1 - 2 * c) * legendreKernelDensity (1 / 2) (1 / 4) s ≤
      legendreKernelDensity (1 / 2) c s := by
  have hd : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have ht : 0 ≤ 1 - 2 * c := by linarith
  unfold legendreKernelDensity legendreMeanWeight
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hd]
  by_cases hsc : s ≤ c <;> by_cases hsq : s ≤ 1 / 4
  · rw [min_eq_left hsc, min_eq_left hsq]
    have hnonneg := mul_nonneg hs.1 (sq_nonneg (1 - 2 * c))
    apply (mul_le_mul_iff_left₀ hc).mp
    field_simp
    nlinarith only [hnonneg]
  · rw [min_eq_left hsc, min_eq_right (le_of_not_ge hsq)]
    have hb : 0 ≤ s * (1 + 2 * c) - c := by
      have hprod := mul_nonneg (show 0 ≤ s - 1 / 4 by linarith)
        (show 0 ≤ 1 + 2 * c by linarith)
      nlinarith only [hprod, hc2]
    have hnonneg := mul_nonneg ht hb
    apply (mul_le_mul_iff_left₀ hc).mp
    field_simp
    nlinarith only [hnonneg]
  · rw [min_eq_right (le_of_not_ge hsc), min_eq_left hsq, div_self hc.ne']
    have hnonneg := mul_nonneg hc.le hs.1
    nlinarith only [hsq, hnonneg]
  · rw [min_eq_right (le_of_not_ge hsc), min_eq_right (le_of_not_ge hsq),
      div_self hc.ne']
    have hnonneg := mul_nonneg hc.le (show 0 ≤ 1 - 2 * s by linarith [hs.2])
    nlinarith only [hnonneg]

/-- A fixed interior clamped kernel survives up to the corner with linear weight. -/
theorem legendreKernel_half_comparison {c u : ℝ}
    (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hu : u ∈ Icc (0 : ℝ) (1 / 2)) :
    (1 - 2 * c) * legendreKernel (1 / 2) (1 / 4) u ≤
      legendreKernel (1 / 2) c u := by
  have hsub : uIcc u (1 / 2 : ℝ) ⊆ uIcc 0 (1 / 2 : ℝ) := by
    rw [uIcc_of_le hu.2, uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc hu.1 le_rfl
  unfold legendreKernel
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hu.2
    (((continuousOn_legendreKernelDensity (c := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)).mono hsub).intervalIntegrable.const_mul _)
    (((continuousOn_legendreKernelDensity (c := c)
      (by norm_num) (by norm_num)).mono hsub).intervalIntegrable) ?_
  intro s hs
  exact legendreDensity_half_comparison hc hc2 ⟨hu.1.trans hs.1, hs.2⟩

private theorem no_strict_linear_stream_flux {N : ℕ} (a : Fin N → ℝ)
    {κ : ℝ} (hκ : 0 < κ)
    (hflux : ∀ x : ℝ, 0 < x → x < 1 / 2 →
      arcStreamFlux a x < 2 * arcStreamFlux a (1 / 2) * x)
    (hgap : ∀ c ∈ Ioo (1 / 4 : ℝ) (1 / 2),
      κ * (1 / 2 - c) ≤ 2 * arcStreamFlux a (1 / 2) - arcStreamFlux a c / c) : False := by
  set G := arcStreamFlux a with hGdef
  have habs : ∀ x : ℝ, 0 < x → x < 1 / 2 → |x| < 1 := fun x hx hx2 => by
    rw [abs_of_pos hx]
    linarith
  rcases le_or_gt (G (1 / 2)) 0 with hG | hG
  · -- `G(½) ≤ 0`: the stream function is nonnegative
    have hψ : ∀ x y, 0 ≤ x → x ≤ 1 / 2 → 1 ≤ y → 0 ≤ whStream a x y := by
      intro x y hx hx2 hy
      refine le_of_halfDomainStreamMinimum (Zx := whStreamX a) (Zxx := whStreamXX a)
        (Zy := whStreamY a) (Zyy := whStreamYY a)
        (fun x y _ => hasDerivAt_whStream_x a x y) (fun x y _ => hasDerivAt_whStreamX_x a x y)
        (fun x y hy => hasDerivAt_whStream_y a x hy) (fun x y hy => hasDerivAt_whStreamY_y a x hy)
        (fun x y _ => whStream_pde a x y) (continuousOn_whStream a)
        (fun y _ => (whStream_zero a y).ge) (fun y _ => (whStream_half a y).ge) ?_ ?_
        hx hx2 (by linarith) (by nlinarith)
      · intro ε hε
        obtain ⟨Y, hY⟩ := exists_abs_whStream_le a hε
        exact ⟨Y, fun x y _ _ hy => by have := hY x y hy; rw [abs_le] at this; linarith⟩
      · intro x hx hx2
        have hy := modularArcHeight_pos_of_abs_lt (habs x hx hx2)
        refine ⟨G x, by nlinarith [hflux x hx hx2], ?_⟩
        have h := hasDerivAt_whStream_ray a x hy
        rw [whStream_ray_eq_flux a (habs x hx hx2)] at h
        exact h
    have hall := eq_zero_of_whStream_nonneg a hψ
    have h0 := hflux (1 / 4) (by norm_num) (by norm_num)
    simp only [hGdef, arcStreamFlux, hall, zero_mul, Finset.sum_const_zero, mul_zero,
      lt_self_iff_false] at h0
  · -- `G(½) > 0`: the corner
    set l := 2 * G (1 / 2) with hl
    have hl0 : 0 < l := by rw [hl]; linarith
    have hlin : ∀ x : ℝ, HasDerivAt (fun s : ℝ => l * s) l x := fun x => by
      simpa using (hasDerivAt_id x).const_mul l
    have hZ : ∀ x y, 0 ≤ x → x ≤ 1 / 2 → 0 ≤ y → 1 ≤ x ^ 2 + y ^ 2 →
        -G (1 / 2) ≤ whStream a x y - l * x := by
      intro x y hx hx2 hy0 hr
      refine le_of_halfDomainStreamMinimum (Z := fun x y => whStream a x y - l * x)
        (Zx := fun x y => whStreamX a x y - l) (Zxx := whStreamXX a) (Zy := whStreamY a)
        (Zyy := whStreamYY a)
        (fun x y _ => (hasDerivAt_whStream_x a x y).sub (hlin x))
        (fun x y _ => (hasDerivAt_whStreamX_x a x y).sub_const l)
        (fun x y hy => (hasDerivAt_whStream_y a x hy).sub_const _)
        (fun x y hy => hasDerivAt_whStreamY_y a x hy)
        (fun x y _ => whStream_pde a x y)
        ((continuousOn_whStream a).sub (by fun_prop)) ?_ ?_ ?_ ?_ hx hx2 hy0 hr
      · intro y _; simp only [whStream_zero]; linarith
      · intro y _; simp only [whStream_half]; rw [hl]; linarith
      · intro ε hε
        obtain ⟨Y, hY⟩ := exists_abs_whStream_le a hε
        refine ⟨Y, fun x y hx hx2 hy => ?_⟩
        have := hY x y hy
        rw [abs_le] at this
        have : l * x ≤ l * (1 / 2) := mul_le_mul_of_nonneg_left hx2 hl0.le
        rw [hl] at this ⊢
        linarith
      · intro x hx hx2
        have hy := modularArcHeight_pos_of_abs_lt (habs x hx hx2)
        refine ⟨G x - l * x, by rw [hl]; linarith [hflux x hx hx2], ?_⟩
        have h := hasDerivAt_whStream_ray a x hy
        rw [whStream_ray_eq_flux a (habs x hx hx2)] at h
        have hr : HasDerivAt (fun t : ℝ => l * ((1 + t) * x)) (l * x) 0 := by
          simpa using (((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const x).const_mul l
        exact h.sub hr
    -- the wall: `∂_x Z(½, y) ≤ 0` above the corner
    have hy₀ := modularArcHeight_half_pos
    have hy₀2 := modularArcHeight_half_sq
    have hwall : ∀ y, modularArcHeight (1 / 2) < y → whStreamX a (1 / 2) y - l ≤ 0 := by
      intro y hy
      have hy0 : 0 < y := hy₀.trans hy
      have hd : HasDerivAt (fun s => whStream a s y - l * s) (whStreamX a (1 / 2) y - l) (1 / 2) :=
        (hasDerivAt_whStream_x a (1 / 2) y).sub (hlin _)
      refine hasDerivAt_nonpos_of_left_ge hd ?_
      have hy2 : 3 / 4 < y ^ 2 := by nlinarith
      have hev1 : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), 1 < s ^ 2 + y ^ 2 :=
        continuousAt_const.eventually_lt
          (by fun_prop : Continuous fun s : ℝ => s ^ 2 + y ^ 2).continuousAt
          (by nlinarith)
      have hev2 : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), 0 < s := lt_mem_nhds (by norm_num)
      filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin]
        with s hs1 hs2 (hs3 : s < 1 / 2)
      have := hZ s y hs2.le hs3.le hy0.le hs1.le
      simp only [whStream_half]
      rw [hl] at this ⊢
      linarith
    have hφ0 : whStreamX a (1 / 2) (modularArcHeight (1 / 2)) - l = 0 := by
      rw [whStreamX_half_eq, hl, hGdef]; ring
    have hXY : whStreamXY a (1 / 2) (modularArcHeight (1 / 2)) ≤ 0 := by
      refine hasDerivAt_nonpos_of_right_le
        ((hasDerivAt_whStreamX_y a (1 / 2) hy₀).sub_const l) ?_
      filter_upwards [self_mem_nhdsWithin] with y (hy : modularArcHeight (1 / 2) < y)
      rw [hφ0]
      exact hwall y hy
    -- the certificate makes `G(c)/c` increase strictly into `½`
    have hH : HasDerivAt (fun c => G c / c)
        ((arcStreamFluxSlope a * (1 / 2) - G (1 / 2) * 1) / (1 / 2) ^ 2) (1 / 2) :=
      (hasDerivAt_arcStreamFlux_half a).div (hasDerivAt_id _) (by norm_num)
    have hκbound : κ ≤ (arcStreamFluxSlope a * (1 / 2) - G (1 / 2) * 1) / (1 / 2) ^ 2 := by
      refine le_hasDerivAt_of_left hH ?_
      filter_upwards [Ioo_mem_nhdsLT (show (1 / 4 : ℝ) < 1 / 2 by norm_num)] with c hc
      have h := hgap c hc
      have he : G (1 / 2) / (1 / 2) = 2 * G (1 / 2) := by ring
      rw [he]
      exact h
    have hpos' : 0 < arcStreamFluxSlope a - 2 * G (1 / 2) := by
      have : (arcStreamFluxSlope a * (1 / 2) - G (1 / 2) * 1) / (1 / 2) ^ 2 =
          2 * (arcStreamFluxSlope a - 2 * G (1 / 2)) := by ring
      rw [this] at hκbound
      linarith only [hκbound, hκ]
    have hXY' := whStreamXY_half_eq a
    rw [← hGdef] at hXY'
    have : 0 < 2 * modularArcHeight (1 / 2) * (arcStreamFluxSlope a - 2 * G (1 / 2)) := by
      positivity
    linarith

/-- A finite sum of twisted moments, evaluated on the clamped arc parameter. -/
def twistedArcMomentSum {N : ℕ} (a : Fin N → ℝ) (u : ℝ) : ℝ :=
  ∑ i, a i * twArcMoment i (arcClamp u)

private theorem continuous_twistedArcMomentSum {N : ℕ} (a : Fin N → ℝ) :
    Continuous (twistedArcMomentSum a) :=
  continuous_finsetSum _ fun i _ => (continuous_twArcMoment_arcClamp i).const_mul _

private theorem integral_twistedArcMomentSum_kernel {N : ℕ} (a : Fin N → ℝ)
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    (∫ u in (0 : ℝ)..(1 / 2), twistedArcMomentSum a u *
      (legendreKernel (1 / 2) c u / Real.sqrt (modularArcHeight u))) =
        4 * (2 * arcStreamFlux a (1 / 2) - arcStreamFlux a c / c) := by
  have hint : ∀ i : Fin N, IntervalIntegrable (fun u =>
      twArcMoment i (arcClamp u) *
        (legendreKernel (1 / 2) c u / Real.sqrt (modularArcHeight u))) volume 0 (1 / 2) :=
    fun i => ((continuous_twArcMoment_arcClamp i).continuousOn.mul
      continuousOn_legendreArcWeight).intervalIntegrable
  simp only [twistedArcMomentSum, Finset.sum_mul]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_finsetSum fun i _ => (hint i).const_mul (a i)]
  simp_rw [intervalIntegral.integral_const_mul,
    integral_twArcMoment_mul_legendreKernel _ hc hc2]
  simp only [arcStreamFlux, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [streamFreq]; ring

private theorem integral_twistedArcMomentSum_kernel_eq_zero {N : ℕ} (a : Fin N → ℝ)
    (hF : ∀ u ∈ Icc (0 : ℝ) (1 / 2), 0 ≤ twistedArcMomentSum a u) :
    (∫ u in (0 : ℝ)..(1 / 2), twistedArcMomentSum a u *
      (legendreKernel (1 / 2) (1 / 4) u / Real.sqrt (modularArcHeight u))) = 0 := by
  let F := twistedArcMomentSum a
  let w : ℝ → ℝ → ℝ := fun c u =>
    legendreKernel (1 / 2) c u / Real.sqrt (modularArcHeight u)
  let I := ∫ u in (0 : ℝ)..(1 / 2), F u * w (1 / 4) u
  have hwc (c : ℝ) : ContinuousOn (w c) (uIcc 0 (1 / 2)) :=
    continuousOn_legendreArcWeight
  have hFc : Continuous F := continuous_twistedArcMomentSum a
  have hI0 : 0 ≤ I := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact mul_nonneg (hF u hu) (div_nonneg
      (legendreKernel_nonneg (by norm_num) (by norm_num) (by norm_num) hu.1 hu.2)
      (Real.sqrt_nonneg _))
  by_contra hne
  have hI : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hne)
  have hcert (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
      I / 2 * (1 / 2 - c) ≤ 2 * arcStreamFlux a (1 / 2) - arcStreamFlux a c / c := by
    have hcompare : (1 - 2 * c) * I ≤ ∫ u in (0 : ℝ)..(1 / 2), F u * w c u := by
      calc
        _ = ∫ u in (0 : ℝ)..(1 / 2), F u * ((1 - 2 * c) * w (1 / 4) u) := by
          rw [show I = ∫ u in (0 : ℝ)..(1 / 2), F u * w (1 / 4) u from rfl,
            ← intervalIntegral.integral_const_mul]
          congr 1
          funext u
          ring
        _ ≤ _ := by
          refine intervalIntegral.integral_mono_on (by norm_num)
            ((hFc.continuousOn.mul ((hwc (1 / 4)).const_mul _)).intervalIntegrable)
            ((hFc.continuousOn.mul (hwc c)).intervalIntegrable) ?_
          intro u hu
          apply mul_le_mul_of_nonneg_left _ (hF u hu)
          dsimp only [w]
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right (legendreKernel_half_comparison hc hc2 hu)
            (Real.sqrt_nonneg _)
    have hid := integral_twistedArcMomentSum_kernel a hc hc2
    change (∫ u in (0 : ℝ)..(1 / 2), F u * w c u) = _ at hid
    rw [hid] at hcompare
    linarith only [hcompare]
  have hflux (x : ℝ) (hx : 0 < x) (hx2 : x < 1 / 2) :
      arcStreamFlux a x < 2 * arcStreamFlux a (1 / 2) * x := by
    have h := hcert x hx hx2.le
    have hpositive : 0 < I / 2 * (1 / 2 - x) :=
      mul_pos (by positivity) (by linarith)
    have hdiv : arcStreamFlux a x / x < 2 * arcStreamFlux a (1 / 2) := by
      linarith only [h, hpositive]
    exact (div_lt_iff₀ hx).mp hdiv
  exact no_strict_linear_stream_flux a (show 0 < I / 2 by positivity) hflux
    (fun c hc => hcert c (by linarith [hc.1]) hc.2.le)

private theorem legendreKernel_quarter_pos {u : ℝ} (hu : u ∈ Ico (0 : ℝ) (1 / 2)) :
    0 < legendreKernel (1 / 2) (1 / 4) u := by
  have hsub : uIcc u (1 / 2 : ℝ) ⊆ uIcc 0 (1 / 2 : ℝ) := by
    rw [uIcc_of_le hu.2.le, uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc hu.1 le_rfl
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (((continuousOn_legendreKernelDensity (c := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)).mono hsub).intervalIntegrable) _ hu.2
  intro s hs
  have hs0 : 0 < s := hu.1.trans_lt hs.1
  have hd : 0 < 1 - s ^ 2 := by nlinarith [hs.2]
  unfold legendreKernelDensity legendreMeanWeight
  apply div_pos _ hd
  by_cases hsq : s ≤ 1 / 4
  · rw [min_eq_left hsq]
    linarith only [hs0]
  · rw [min_eq_right (le_of_not_ge hsq)]
    linarith only [hs.2]

/-- A finite twisted Whittaker sum cannot have one sign on the half arc unless it vanishes. -/
theorem twistedArcMomentSum_eq_zero_of_nonneg {N : ℕ} (a : Fin N → ℝ)
    (hF : ∀ u ∈ Icc (0 : ℝ) (1 / 2), 0 ≤ twistedArcMomentSum a u) :
    ∀ u ∈ Icc (0 : ℝ) (1 / 2), twistedArcMomentSum a u = 0 := by
  have hFc := continuous_twistedArcMomentSum a
  have hwc : ContinuousOn (fun u => twistedArcMomentSum a u *
      (legendreKernel (1 / 2) (1 / 4) u / Real.sqrt (modularArcHeight u)))
      (Icc (0 : ℝ) (1 / 2)) := by
    rw [← uIcc_of_le (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    exact hFc.continuousOn.mul continuousOn_legendreArcWeight
  have hint0 := integral_twistedArcMomentSum_kernel_eq_zero a hF
  have hzero : Ioo (0 : ℝ) (1 / 2) ⊆ {u | twistedArcMomentSum a u = 0} := by
    intro u hu
    by_contra hne
    have hpos : 0 < twistedArcMomentSum a u := lt_of_le_of_ne
      (hF u ⟨hu.1.le, hu.2.le⟩) (Ne.symm hne)
    have hy : 0 < Real.sqrt (modularArcHeight u) :=
      Real.sqrt_pos.mpr (modularArcHeight_pos ⟨by linarith [hu.1], hu.2.le⟩)
    have hintpos := intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1 / 2)
      hwc (fun x hx => mul_nonneg (hF x ⟨hx.1.le, hx.2⟩)
        (div_nonneg (legendreKernel_nonneg (by norm_num) (by norm_num) (by norm_num)
          hx.1.le hx.2) (Real.sqrt_nonneg _)))
      ⟨u, ⟨hu.1.le, hu.2.le⟩, mul_pos hpos
        (div_pos (legendreKernel_quarter_pos ⟨hu.1.le, hu.2⟩) hy)⟩
    rw [hint0] at hintpos
    exact (lt_irrefl (0 : ℝ)) hintpos
  have hclosed : IsClosed {u | twistedArcMomentSum a u = 0} :=
    isClosed_eq hFc continuous_const
  have hclosure := closure_minimal hzero hclosed
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2)] at hclosure
  exact hclosure

end RHTower

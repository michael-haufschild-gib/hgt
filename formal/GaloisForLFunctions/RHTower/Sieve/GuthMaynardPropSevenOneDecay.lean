import GaloisForLFunctions.RHTower.Sieve.GuthMaynardCubicTermIntegral
import GaloisForLFunctions.RHTower.ChenGuptaLiSchwartzFourier

/-!
# Uniform non-stationary phase for the inner integral of (7.4)

`J(v, ξ) = ∫ e(−ξu) w₂(u, v) du` with `w₂(u, v) = u² w(u)² w(uv₁)² w(uv₂)²` (Guth–Maynard (7.4)).
The amplitude `w₂` is a smooth compactly supported function of `(u, v) ∈ ℝ³`, so all its
derivatives are bounded; the `u`-derivatives of every slice `u ↦ w₂(u, v)` are derivatives of `w₂`
along the affine line `u ↦ (u, v)` and obey the same bounds, and every slice is supported in
`[1, 2]`. Repeated integration by parts (`cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget`)
then gives `|ξ|^j |J(v, ξ)| ≤ K_j` uniformly in `v ∈ ℝ²`: the non-stationary phase input of
Proposition 7.1 (the case `j = 0` is the trivial bound `|J| ≪ 1`).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

/-- The slice `u ↦ w₂(u, v)` of the amplitude of (7.4). -/
def cubicAmplitudeSlice (w : CGLSmoothBump) (v : ℝ × ℝ) (u : ℝ) : ℂ :=
  cubicAmplitude w (u, v)

theorem contDiff_cubicAmplitudeSlice (w : CGLSmoothBump) (v : ℝ × ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cubicAmplitudeSlice w v) :=
  (contDiff_cubicAmplitude w).comp (contDiff_id.prodMk contDiff_const)

theorem cubicAmplitudeSlice_eq_zero (w : CGLSmoothBump) (v : ℝ × ℝ) {u : ℝ}
    (hu : u ∉ Icc (1 : ℝ) 2) : cubicAmplitudeSlice w v u = 0 :=
  cubicAmplitude_eq_zero w fun hp => hu hp.1

theorem hasCompactSupport_cubicAmplitudeSlice (w : CGLSmoothBump) (v : ℝ × ℝ) :
    HasCompactSupport (cubicAmplitudeSlice w v) :=
  HasCompactSupport.intro isCompact_Icc fun _ hu => cubicAmplitudeSlice_eq_zero w v hu

/-- The derivatives of all slices are bounded uniformly in `v`: they are derivatives of the
compactly supported `w₂` along the lines `u ↦ (u, v)`. -/
theorem exists_norm_iteratedFDeriv_cubicAmplitudeSlice_le (w : CGLSmoothBump) (i : ℕ) :
    ∃ C, ∀ v u, ‖iteratedFDeriv ℝ i (cubicAmplitudeSlice w v) u‖ ≤ C := by
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support
    ((contDiff_cubicAmplitude w).continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top))
    ((hasCompactSupport_cubicAmplitude w).iteratedFDeriv i)
  refine ⟨C, fun v u => ?_⟩
  have hshift : ContDiff ℝ (↑(⊤ : ℕ∞)) fun z : ℝ × ℝ × ℝ => cubicAmplitude w (z + (0, v)) :=
    (contDiff_cubicAmplitude w).comp (contDiff_id.add contDiff_const)
  have hslice : cubicAmplitudeSlice w v =
      (fun z : ℝ × ℝ × ℝ => cubicAmplitude w (z + (0, v))) ∘
        ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ) := by
    funext x; simp [cubicAmplitudeSlice]
  have hprod : ∏ _k : Fin i, ‖ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ =>
      ContinuousLinearMap.norm_inl_le_one ℝ ℝ (ℝ × ℝ)
  rw [hslice, ContinuousLinearMap.iteratedFDeriv_comp_right _ hshift u
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [iteratedFDeriv_comp_add_right]
  calc ‖iteratedFDeriv ℝ i (cubicAmplitude w) (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ) u + (0, v))‖ *
        ∏ _k : Fin i, ‖ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)‖ ≤ C * 1 :=
        mul_le_mul (hC _) hprod (by positivity) ((norm_nonneg _).trans (hC 0))
    _ = C := mul_one C

/-- A derivative of a slice vanishes off `[1, 2]`, so its `L¹` norm is at most its sup norm. -/
theorem integral_norm_iteratedFDeriv_cubicAmplitudeSlice_le (w : CGLSmoothBump) (v : ℝ × ℝ)
    (i : ℕ) {C : ℝ} (hC : ∀ u, ‖iteratedFDeriv ℝ i (cubicAmplitudeSlice w v) u‖ ≤ C) :
    ∫ u, ‖iteratedFDeriv ℝ i (cubicAmplitudeSlice w v) u‖ ≤ C := by
  have hsupp : ∀ u ∉ Icc (1 : ℝ) 2, iteratedFDeriv ℝ i (cubicAmplitudeSlice w v) u = 0 := by
    intro u hu
    have hts : tsupport (cubicAmplitudeSlice w v) ⊆ Icc (1 : ℝ) 2 :=
      closure_minimal (fun x hx => by
        by_contra hx'
        exact hx (cubicAmplitudeSlice_eq_zero w v hx')) isClosed_Icc
    exact Function.notMem_support.mp fun h => hu (hts (support_iteratedFDeriv_subset i h))
  calc ∫ u, ‖iteratedFDeriv ℝ i (cubicAmplitudeSlice w v) u‖
      ≤ ∫ u, (Icc (1 : ℝ) 2).indicator (fun _ => C) u := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          ((integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc)
          (ae_of_all _ fun u => ?_)
        by_cases hu : u ∈ Icc (1 : ℝ) 2
        · simp only [indicator_of_mem hu]; exact hC u
        · simp [indicator_of_notMem hu, hsupp u hu]
    _ = C := by
        rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc]
        norm_num

/-- **Uniform non-stationary phase.** For every `j` there is `K_j` with
`|ξ|^j |J(v, ξ)| ≤ K_j` for all `v ∈ ℝ²` and `ξ ∈ ℝ`. -/
theorem exists_pow_mul_norm_cubicPhaseIntegral_le (w : CGLSmoothBump) (j : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ (v : ℝ × ℝ) (ξ : ℝ), |ξ| ^ j * ‖cubicPhaseIntegral w v ξ‖ ≤ K := by
  choose C hC using exists_norm_iteratedFDeriv_cubicAmplitudeSlice_le w
  have hC0 : ∀ i, 0 ≤ C i := fun i => (norm_nonneg _).trans (hC i 0 0)
  refine ⟨2 ^ j * ∑ p ∈ Finset.range 1 ×ˢ Finset.range (j + 1), C p.2,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ => hC0 p.2), fun v ξ => ?_⟩
  set g : SchwartzMap ℝ ℂ := (hasCompactSupport_cubicAmplitudeSlice w v).toSchwartzMap
    (contDiff_cubicAmplitudeSlice w v) with hg
  have hgf : (g : ℝ → ℂ) = cubicAmplitudeSlice w v := rfl
  have h := cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget g j ξ
  rw [hgf] at h
  refine h.trans ?_
  unfold cglSchwartzFourierDecayBudget
  gcongr with p hp
  have hp1 : p.1 = 0 := by
    have := (Finset.mem_product.mp hp).1
    simpa using this
  rw [hp1]
  simp only [pow_zero, one_mul]
  rw [hgf]
  exact integral_norm_iteratedFDeriv_cubicAmplitudeSlice_le w v p.2 (hC p.2 v)

end

end RHTower.GuthMaynard

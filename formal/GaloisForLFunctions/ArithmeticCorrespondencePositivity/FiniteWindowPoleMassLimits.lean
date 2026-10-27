import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelMassDetectsThePoleOrder

/-!
# Gluing local pole masses on finite windows

A uniformly bounded complementary region vanishes under every positive
power of the boundary distance. Disjoint local atom laws therefore determine
the normalized integral over a finite window.
-/

open Set Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Uniform boundedness on a finite-measure set kills every positive scale. -/
theorem tendsto_scaled_setIntegral_of_bounded {f : ℝ → ℝ → ℝ} {E : Set ℝ}
    {k : ℕ} {C η : ℝ} (hk : 0 < k) (hη : 0 < η)
    (hE : volume E < ⊤)
    (hb : ∀ e ∈ Ioo 0 η, ∀ y ∈ E, ‖f e y‖ ≤ C) :
    Tendsto (fun e : ℝ => e ^ k * ∫ y in E, f e y) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun e : ℝ => e ^ k) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun e : ℝ => e ^ k) := by fun_prop
    simpa only [zero_pow hk.ne'] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := hp.mul_const (C * volume.real E)
  rw [zero_mul] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT hη] with e he
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos he.1 k)]
  exact mul_le_mul_of_nonneg_left
    (norm_setIntegral_le_of_norm_le_const hE (hb e he)) (pow_nonneg he.1.le k)

/-- Finite disjoint local limits and a vanishing complement give the whole-window limit. -/
theorem tendsto_scaled_integral_of_finite_windows {ι : Type*} (Z : Finset ι)
    {E : Set ℝ} {W : ι → Set ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ → ℝ} {L : ι → ℝ}
    (hW : ∀ i ∈ Z, MeasurableSet (W i))
    (hdisj : (Z : Set ι).Pairwise (Function.onFun Disjoint W))
    (hsub : (⋃ i ∈ Z, W i) ⊆ E)
    (hint : ∀ᶠ e : ℝ in 𝓝[>] 0, IntegrableOn (f e) E)
    (hlocal : ∀ i ∈ Z,
      Tendsto (fun e => p e * ∫ y in W i, f e y) (𝓝[>] 0) (𝓝 (L i)))
    (hrest : Tendsto (fun e => p e * ∫ y in E \ (⋃ i ∈ Z, W i), f e y)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun e => p e * ∫ y in E, f e y) (𝓝[>] 0) (𝓝 (∑ i ∈ Z, L i)) := by
  have hsum := tendsto_finsetSum Z hlocal
  have hlim := hrest.add hsum
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [hint] with e he
  have hU : MeasurableSet (⋃ i ∈ Z, W i) := Finset.measurableSet_biUnion Z hW
  have hsplit := setIntegral_sdiff hU he hsub
  have hunion := integral_biUnion_finset Z hW hdisj
    (fun i hi => he.mono_set (fun y hy => hsub (mem_iUnion₂.mpr ⟨i, hi, hy⟩)))
  rw [← Finset.mul_sum, ← hunion, hsplit]
  ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

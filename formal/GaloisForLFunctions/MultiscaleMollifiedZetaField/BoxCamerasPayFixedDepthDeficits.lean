import GaloisForLFunctions.MultiscaleMollifiedZetaField.BoxCameraGeometricLoss

/-!
# Box cameras pay a fixed positive cluster depth deficit

The exterior cost is eventually less than half the finite Turán signal,
uniformly in height, whenever logarithmic height and camera lags grow
linearly in convolution order and the two geometric decay rates beat
the fixed depth deficit. Every eligible cluster is then visible or has a
deep exterior companion; no exterior-mass bound is assumed.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open SquareRootThreshold (zetaZeroWidth)

theorem eventually_box_cluster_visible_or_deep_companion
    {A h r g d a b η L : ℝ} (hA : 0 < A) (hh : 0 < h) (hr : 0 < r)
    (hg : 0 < g) (hd : 0 ≤ d) (hL : 0 ≤ L) (hη : 0 < η)
    (hgapRate : Real.exp (η * b) < h * g) (hdepthRate : η * b < d * a)
    {M N : ℕ} (hN : 1 ≤ N) :
    ∀ᶠ n : ℕ in atTop, ∀ ℓ t : ℝ, 0 < ℓ →
      boxCameraRadius A h n r ≤ ((M : ℝ) + 1) * ℓ →
      a * ((n : ℝ) + 1) ≤ ((M : ℝ) + 1) * ℓ - boxCameraRadius A h n r →
      ((M : ℝ) + N) * ℓ + boxCameraRadius A h n r ≤ b * ((n : ℝ) + 1) →
      Real.log (|t| + 4) ≤ L * ((n : ℝ) + 1) →
      ∀ s : Finset zetaZeroConfig.carrier, s.card ≤ N →
      (∀ ρ ∈ s, |(ρ : ℂ).im - t| * boxCameraRadius A h n r ≤ 1 / 10) →
      ∀ ρ ∈ s, zetaZeroWidth - η ≤ (ρ : ℂ).re - 1 / 2 →
      (∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧
        (A / 2) * turanConstant N M *
          Real.exp (-(η * (((M : ℝ) + N) * ℓ + boxCameraRadius A h n r))) ≤
          ‖widthCenteredBoxZeroField A h n r ((ν : ℝ) * ℓ) t‖) ∨
      ∃ q : zetaZeroConfig.carrier, q ∉ s ∧
        zetaZeroWidth - d ≤ (q : ℂ).re - 1 / 2 ∧ |(q : ℂ).im - t| < g := by
  have hκ := turanConstant_pos hN M
  have hK : 0 < A * turanConstant N M / 2 := by positivity
  have ht := tendsto_boxRelativeExteriorMajorant (A := A) (L := L) hh hg hgapRate hdepthRate
  filter_upwards [ht.eventually (gt_mem_nhds hK)]
    with n hn ℓ t hℓ hy hlag hspan hheight s hcard hsector ρ hρ hnear
  have hbnd := boxExteriorBound_mul_exp_le hA.le hh hr hg hd hL n hlag hheight
    (b := b) (η := η)
  have hraw : boxExteriorBound A h n r g d (((M : ℝ) + 1) * ℓ) t ≤
      (A * turanConstant N M / 2) / Real.exp (η * b * ((n : ℝ) + 1)) :=
    (le_div_iff₀ (Real.exp_pos _)).mpr (hbnd.trans hn.le)
  have hsmall : boxExteriorBound A h n r g d (((M : ℝ) + 1) * ℓ) t ≤
      (A * turanConstant N M / 2) * Real.exp (-(η * b * ((n : ℝ) + 1))) := by
    simpa only [div_eq_mul_inv, ← Real.exp_neg] using hraw
  have hnoise : boxExteriorBound A h n r g d (((M : ℝ) + 1) * ℓ) t ≤
      (A * turanConstant N M / 2) *
        Real.exp (-(η * (((M : ℝ) + N) * ℓ + boxCameraRadius A h n r))) := by
    apply hsmall.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hspan hη.le
    nlinarith only [hm]
  rcases widthCenteredBox_cluster_visible_or_deep_companion hA hh hr n hℓ hη.le hg hd hN
      hy hcard hsector hρ hnear with hvisible | hcompanion
  · obtain ⟨ν, hν1, hνN, hv⟩ := hvisible
    refine Or.inl ⟨ν, hν1, hνN, ?_⟩
    nlinarith only [hv, hnoise]
  · exact Or.inr hcompanion

/-- A concrete lag schedule admits a fixed positive deficit for every
`h g>1`. The logarithmic height allowance is uniform over all clusters. -/
theorem exists_fixed_deficit_box_cluster_visible_or_deep_companion
    {A h r g d L : ℝ} (hA : 0 < A) (hh : 0 < h) (hr : 0 < r)
    (hg : 0 < g) (hd : 0 < d) (hL : 0 ≤ L) (hgap : 1 < h * g)
    {N : ℕ} (hN : 1 ≤ N) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      Real.log (|t| + 4) ≤ L * ((n : ℝ) + 1) →
      ∀ s : Finset zetaZeroConfig.carrier, s.card ≤ N →
      (∀ ρ ∈ s, |(ρ : ℂ).im - t| * boxCameraRadius A h n r ≤ 1 / 10) →
      ∀ ρ ∈ s, zetaZeroWidth - η ≤ (ρ : ℂ).re - 1 / 2 →
      (∃ ν : ℕ, 1 ≤ ν ∧ ν ≤ N ∧
        (A / 2) * turanConstant N 0 *
          Real.exp (-(η * (((N : ℝ) * (h + 2) + h + 1) * ((n : ℝ) + 1)))) ≤
          ‖widthCenteredBoxZeroField A h n r ((ν : ℝ) * ((h + 2) * ((n : ℝ) + 1))) t‖) ∨
      ∃ q : zetaZeroConfig.carrier, q ∉ s ∧
        zetaZeroWidth - d ≤ (q : ℂ).re - 1 / 2 ∧ |(q : ℂ).im - t| < g := by
  let b := (N : ℝ) * (h + 2) + h + 1
  have hb : 0 < b := by dsimp only [b]; positivity
  obtain ⟨η, hη, hηgap, hηdepth⟩ :=
    exists_positive_box_depth_deficit (b := b) hgap hd zero_lt_one hb
  refine ⟨η, hη, ?_⟩
  have hmain := eventually_box_cluster_visible_or_deep_companion
    hA hh hr hg hd.le hL hη hηgap hηdepth (M := 0) hN
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (A + r)
  filter_upwards [hmain, eventually_ge_atTop n₀]
    with n hn hnlarge t ht s hcard hsec ρ hρ hnear
  have hx : 0 < (n : ℝ) + 1 := by positivity
  have hc : A + r ≤ (n : ℝ) + 1 := by
    have hnreal : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlarge
    linarith only [hn₀, hnreal]
  have hδ : boxCameraRadius A h n r ≤ (h + 1) * ((n : ℝ) + 1) := by
    simp only [boxCameraRadius, Nat.cast_add, Nat.cast_one]
    nlinarith only [hc]
  have hlag : 1 * ((n : ℝ) + 1) ≤
      ((0 : ℝ) + 1) * ((h + 2) * ((n : ℝ) + 1)) - boxCameraRadius A h n r := by
    nlinarith only [hδ]
  have hy : boxCameraRadius A h n r ≤
      ((0 : ℝ) + 1) * ((h + 2) * ((n : ℝ) + 1)) := by
    linarith only [hlag, hx]
  have hspan : ((0 : ℝ) + N) * ((h + 2) * ((n : ℝ) + 1)) +
      boxCameraRadius A h n r ≤ b * ((n : ℝ) + 1) := by
    dsimp only [b]
    nlinarith only [hδ]
  rcases hn ((h + 2) * ((n : ℝ) + 1)) t (by positivity) hy hlag hspan ht
      s hcard hsec ρ hρ hnear with hvisible | hcompanion
  · obtain ⟨ν, hν1, hνN, hv⟩ := hvisible
    refine Or.inl ⟨ν, by simpa only [Nat.zero_add] using hν1,
      by simpa only [Nat.zero_add] using hνN, ?_⟩
    have hκ := turanConstant_pos hN 0
    apply le_trans _ hv
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hspan hη.le
    change -(η * (b * ((n : ℝ) + 1))) ≤ _
    nlinarith only [hm]
  · exact Or.inr hcompanion

end GaloisForLFunctions.MultiscaleMollifiedZetaField

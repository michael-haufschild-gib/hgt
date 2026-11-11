import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDepthCenteredCameraPaysItsExteriorMass
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTuranCameraSeesBoundedClusters

/-!
# Near-top clusters in the width-centered camera

Width centering removes exponential growth from the exterior zeros. A
cluster containing a zero within `η` of the top still has a Turán signal
at least `κ(N,M) exp(-η((M+N)h+δ))` times half the profile mass.
The explicit exterior estimate therefore replaces an assumed noise bound
by an ordinate-gap condition.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open SquareRootThreshold (zetaZeroWidth)

/-- The actual zero field of the width-centered camera. -/
def widthCenteredZeroField (v : ℝ → ℝ) (δ y t : ℝ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
    paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf ρ - t)

/-- A bounded cluster near the top retains a uniform Turán signal after
centering, independently of internal separation. -/
theorem exists_nu_widthCentered_cluster_signal
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u)
    {δ h t η : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hη : 0 ≤ η)
    {M N : ℕ} (hN : 1 ≤ N) {s : Finset zetaZeroConfig.carrier}
    (hcard : s.card ≤ N)
    (hsec : ∀ ρ ∈ s, |(ρ : ℂ).im - t| * δ ≤ 1 / 10)
    {ρ : zetaZeroConfig.carrier} (hρ : ρ ∈ s)
    (hnear : zetaZeroWidth - η ≤ (ρ : ℂ).re - 1 / 2) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧
      1 / 2 * (∫ u, v u) * turanConstant N M *
        Real.exp (-(η * (((M : ℝ) + N) * h + δ))) ≤
      ‖∑ q ∈ s, (zetaZeroConfig.mult q : ℂ) *
        paperFT (depthCenteredCamera v zetaZeroWidth δ ((ν : ℝ) * h)) (gammaOf q - t)‖ := by
  classical
  have hs : s.Nonempty := ⟨ρ, hρ⟩
  obtain ⟨q₀, hq₀, hmax⟩ := Finset.exists_max_image s (fun q => (q : ℂ).re) hs
  let r := fun q : zetaZeroConfig.carrier => (q : ℂ) - (zetaZeroWidth : ℂ)
  let w := fun q : zetaZeroConfig.carrier => (zetaZeroConfig.mult q : ℂ) *
    paperFT (cplx v) ((gammaOf (r q) - t) * δ)
  let z := fun q : zetaZeroConfig.carrier => cexp (I * (gammaOf (r q) - t) * h)
  let b := (q₀ : ℂ).re - 1 / 2 - zetaZeroWidth
  let Z := Real.exp (b * h)
  let B := 1 / 2 * Real.exp (-(η * δ)) * (∫ u, v u)
  have hZ : 0 < Z := Real.exp_pos _
  have hB : 0 < B := by dsimp only [B]; positivity
  have hb0 : b ≤ 0 := by
    have hh := (le_abs_self ((q₀ : ℂ).re - 1 / 2)).trans
      (SquareRootThreshold.abs_re_sub_half_le_zetaZeroWidth q₀.2)
    dsimp only [b]
    linarith only [hh]
  have hbη : -η ≤ b := by
    have hm := hmax ρ hρ
    dsimp only [b]
    linarith only [hnear, hm]
  have hnorm (q : zetaZeroConfig.carrier) :
      ‖z q‖ = Real.exp (((q : ℂ).re - 1 / 2 - zetaZeroWidth) * h) := by
    dsimp only [z]
    rw [norm_node_eq]
    simp only [r, Complex.sub_re, Complex.ofReal_re]
    congr 1
    ring
  have hqnorm : ‖z q₀‖ = Z := hnorm q₀
  have hrew (q : zetaZeroConfig.carrier) (hq : q ∈ s) :
      1 / 2 * Real.exp (-(|(gammaOf (r q) - t).im| * δ)) * (∫ u, v u) ≤ (w q).re := by
    have hsector : |(gammaOf (r q) - t).re| * δ ≤ 1 / 10 := by
      rw [gammaOf_sub_re]
      simpa only [r, Complex.sub_im, Complex.ofReal_im, sub_zero] using hsec q hq
    have hf := re_paperFT_profile_ge hv hsupp hv0 hδ hsector
    have hm : (1 : ℝ) ≤ zetaZeroConfig.mult q := by
      exact_mod_cast zetaZeroConfig.one_le_mult q q.2
    have he : (w q).re = (zetaZeroConfig.mult q : ℝ) *
        (paperFT (cplx v) ((gammaOf (r q) - t) * δ)).re := by
      simp only [w, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    rw [he]
    have h0 : 0 ≤ 1 / 2 * Real.exp (-(|(gammaOf (r q) - t).im| * δ)) *
        (∫ u, v u) := by positivity
    exact hf.trans (le_mul_of_one_le_left (h0.trans hf) hm)
  have hrew0 (q : zetaZeroConfig.carrier) (hq : q ∈ s) : 0 ≤ (w q).re := by
    have h0 : 0 ≤ 1 / 2 * Real.exp (-(|(gammaOf (r q) - t).im| * δ)) *
        (∫ u, v u) := by positivity
    exact h0.trans (hrew q hq)
  have hBq : B ≤ (w q₀).re := by
    have him : |(gammaOf (r q₀) - t).im| = -b := by
      rw [gammaOf_sub_im, abs_neg]
      change |(q₀ : ℂ).re - zetaZeroWidth - 1 / 2| = -b
      rw [show (q₀ : ℂ).re - zetaZeroWidth - 1 / 2 = b by dsimp only [b]; ring,
        abs_of_nonpos hb0]
    have hh := hrew q₀ hq₀
    rw [him] at hh
    apply le_trans _ hh
    dsimp only [B]
    apply mul_le_mul_of_nonneg_right _ hI.le
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    nlinarith only [hbη, hδ]
  have htop : ∀ u : ℝ, 1 - 1 / ((M : ℝ) + 2 * s.card + 2) ≤ u → u ≤ 1 →
      B ≤ ‖∑ q ∈ s.filter (fun q => u * Z ≤ ‖z q‖), w q‖ := by
    intro u _ hu
    have hmem : q₀ ∈ s.filter (fun q => u * Z ≤ ‖z q‖) := by
      refine Finset.mem_filter.mpr ⟨hq₀, ?_⟩
      rw [hqnorm]
      exact mul_le_of_le_one_left hZ.le hu
    calc
      B ≤ (w q₀).re := hBq
      _ ≤ ∑ q ∈ s.filter (fun q => u * Z ≤ ‖z q‖), (w q).re :=
        Finset.single_le_sum (fun q hq => hrew0 q (Finset.mem_filter.mp hq).1) hmem
      _ = (∑ q ∈ s.filter (fun q => u * Z ≤ ‖z q‖), w q).re := (Complex.re_sum _ _).symm
      _ ≤ _ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  obtain ⟨ν, hν1, hν2, hν⟩ := HTGeometry.exists_norm_weightedPowerSum_ge_scaled s z w hZ
    ⟨q₀, hq₀, hqnorm.ge⟩ M hB htop
  have hνN : ν ≤ M + N := by omega
  have hκ : B * Z ^ ν * turanConstant N M ≤ ‖∑ q ∈ s, w q * z q ^ ν‖ := by
    have hle := turanConstant_le (Finset.card_pos.mpr hs) hcard M
    have he : B * Z ^ ν / (2 * (Real.exp 1 * s.card *
        (6 * ((s.card : ℝ) + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card)) =
        B * Z ^ ν * turanConstant s.card M := by
      rw [turanConstant, mul_one_div]
    rw [he] at hν
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans hν
  have hamp : Real.exp (-(η * (((M : ℝ) + N) * h + δ))) ≤
      Real.exp (-(η * δ)) * Z ^ ν := by
    dsimp only [Z]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn0 : 0 ≤ (ν : ℝ) * h := by positivity
    have hnN : (ν : ℝ) * h ≤ ((M : ℝ) + N) * h := by
      apply mul_le_mul_of_nonneg_right _ hh.le
      exact_mod_cast hνN
    have h1 := mul_le_mul_of_nonneg_right hbη hn0
    have h2 := mul_le_mul_of_nonpos_left hnN (neg_nonpos.mpr hη)
    nlinarith only [h1, h2]
  have hsignal : 1 / 2 * (∫ u, v u) * turanConstant N M *
      Real.exp (-(η * (((M : ℝ) + N) * h + δ))) ≤ ‖∑ q ∈ s, w q * z q ^ ν‖ := by
    apply le_trans _ hκ
    have hh := mul_le_mul_of_nonneg_left hamp
      (show 0 ≤ 1 / 2 * (∫ u, v u) * turanConstant N M by
        have := turanConstant_pos hN M; positivity)
    dsimp only [B]
    convert hh using 1 <;> ring
  refine ⟨ν, hν1, hνN, ?_⟩
  have he : (∑ q ∈ s, (zetaZeroConfig.mult q : ℂ) *
      paperFT (depthCenteredCamera v zetaZeroWidth δ ((ν : ℝ) * h)) (gammaOf q - t)) =
      ∑ q ∈ s, w q * z q ^ ν := by
    apply Finset.sum_congr rfl
    intro q _
    rw [paperFT_depthCenteredCamera, term_eq_weight_mul_node_pow hδ]
  rw [he]
  exact hsignal

/-- The complete near-top field has the Turán signal minus an explicitly
paid exterior term. No exterior-mass hypothesis is required. -/
theorem exists_nu_widthCenteredZeroField_ge
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u)
    {δ h t η g : ℝ} (hδ : 1 ≤ δ) (hh : 0 < h) (hη : 0 ≤ η) (hg : 0 < g)
    {M N : ℕ} (hN : 1 ≤ N)
    (hy : δ ≤ ((M : ℝ) + 1) * h)
    {s : Finset zetaZeroConfig.carrier} (hcard : s.card ≤ N)
    (hsec : ∀ ρ ∈ s, |(ρ : ℂ).im - t| * δ ≤ 1 / 10)
    {ρ : zetaZeroConfig.carrier} (hρ : ρ ∈ s)
    (hnear : zetaZeroWidth - η ≤ (ρ : ℂ).re - 1 / 2)
    (hgap : ∀ q : zetaZeroConfig.carrier, q ∉ s → g ≤ |(q : ℂ).im - t|) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧
      1 / 2 * (∫ u, v u) * turanConstant N M *
        Real.exp (-(η * (((M : ℝ) + N) * h + δ))) -
          profileMass v * ((1 + g ^ 2) / (δ ^ 2 * g ^ 2)) * lorentzMass t ≤
        ‖widthCenteredZeroField v δ ((ν : ℝ) * h) t‖ := by
  have hδ0 : 0 < δ := one_pos.trans_le hδ
  obtain ⟨ν, hν1, hνN, hsignal⟩ :=
    exists_nu_widthCentered_cluster_signal hv hsupp hv0 hI hδ0 hh hη hN hcard hsec hρ hnear
  have hyν : δ ≤ (ν : ℝ) * h := by
    apply hy.trans
    apply mul_le_mul_of_nonneg_right _ hh.le
    exact_mod_cast hν1
  have hs := summable_widthCenteredCamera hv hsupp hδ hyν (t := t)
  have htail := norm_tsum_sub_sum_le hs s (c :=
      profileMass v * ((1 + g ^ 2) / (δ ^ 2 * g ^ 2)) * lorentzMass t) (fun F hF => by
    have h := sum_widthCenteredCamera_exterior_le hv hsupp hδ0 hyν hg F
      (fun q hq => hgap q (fun hqs => Finset.disjoint_left.mp hF hq hqs))
    simpa only [norm_mul, Complex.norm_natCast] using h)
  refine ⟨ν, hν1, hνN, ?_⟩
  have htri := norm_sub_norm_le
    (∑ q ∈ s, (zetaZeroConfig.mult q : ℂ) *
      paperFT (depthCenteredCamera v zetaZeroWidth δ ((ν : ℝ) * h)) (gammaOf q - t))
    (widthCenteredZeroField v δ ((ν : ℝ) * h) t)
  rw [norm_sub_rev] at htri
  change ‖widthCenteredZeroField v δ ((ν : ℝ) * h) t - _‖ ≤ _ at htail
  linarith only [hsignal, htail, htri]

/-- The exterior noise is explicit when only comparably deep zeros have an
ordinate gap. All shallower zeros are included in the exponential term. -/
theorem exists_nu_widthCenteredZeroField_ge_of_deep_gap
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u)
    {δ h t η g d : ℝ} (hδ : 1 ≤ δ) (hh : 0 < h) (hη : 0 ≤ η)
    (hg : 0 < g) (hd : 0 ≤ d) {M N : ℕ} (hN : 1 ≤ N)
    (hy : δ ≤ ((M : ℝ) + 1) * h)
    {s : Finset zetaZeroConfig.carrier} (hcard : s.card ≤ N)
    (hsec : ∀ ρ ∈ s, |(ρ : ℂ).im - t| * δ ≤ 1 / 10)
    {ρ : zetaZeroConfig.carrier} (hρ : ρ ∈ s)
    (hnear : zetaZeroWidth - η ≤ (ρ : ℂ).re - 1 / 2)
    (hgap : ∀ q : zetaZeroConfig.carrier, q ∉ s →
      zetaZeroWidth - d ≤ (q : ℂ).re - 1 / 2 → g ≤ |(q : ℂ).im - t|) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧
      1 / 2 * (∫ u, v u) * turanConstant N M *
        Real.exp (-(η * (((M : ℝ) + N) * h + δ))) -
          profileMass v * (((1 + g ^ 2) / (δ ^ 2 * g ^ 2)) +
            Real.exp (-(d * (((M : ℝ) + 1) * h - δ)))) * lorentzMass t ≤
        ‖widthCenteredZeroField v δ ((ν : ℝ) * h) t‖ := by
  have hδ0 : 0 < δ := one_pos.trans_le hδ
  obtain ⟨ν, hν1, hνN, hsignal⟩ :=
    exists_nu_widthCentered_cluster_signal hv hsupp hv0 hI hδ0 hh hη hN hcard hsec hρ hnear
  have hlow : ((M : ℝ) + 1) * h ≤ (ν : ℝ) * h := by
    apply mul_le_mul_of_nonneg_right _ hh.le
    exact_mod_cast hν1
  have hyν : δ ≤ (ν : ℝ) * h := hy.trans hlow
  have hs := summable_widthCenteredCamera hv hsupp hδ hyν (t := t)
  have hmass0 : 0 ≤ lorentzMass t := by
    simpa only [Finset.sum_empty] using sum_mult_unit_le_lorentzMass t ∅ (by simp)
  have htail := norm_tsum_sub_sum_le hs s (c :=
      profileMass v * (((1 + g ^ 2) / (δ ^ 2 * g ^ 2)) +
        Real.exp (-(d * (((M : ℝ) + 1) * h - δ)))) * lorentzMass t) (fun F hF => by
    have h := sum_widthCenteredCamera_exterior_le_deep_gap hv hsupp hδ hyν hg hd F
      (fun q hq hdeep => hgap q (fun hqs => Finset.disjoint_left.mp hF hq hqs) hdeep)
    simp only [norm_mul, Complex.norm_natCast]
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ hmass0
    apply mul_le_mul_of_nonneg_left _ (profileMass_nonneg v)
    apply add_le_add le_rfl
    apply Real.exp_le_exp.mpr
    nlinarith only [hlow, hd])
  refine ⟨ν, hν1, hνN, ?_⟩
  have htri := norm_sub_norm_le
    (∑ q ∈ s, (zetaZeroConfig.mult q : ℂ) *
      paperFT (depthCenteredCamera v zetaZeroWidth δ ((ν : ℝ) * h)) (gammaOf q - t))
    (widthCenteredZeroField v δ ((ν : ℝ) * h) t)
  rw [norm_sub_rev] at htri
  change ‖widthCenteredZeroField v δ ((ν : ℝ) * h) t - _‖ ≤ _ at htail
  linarith only [hsignal, htail, htri]

end GaloisForLFunctions.MultiscaleMollifiedZetaField

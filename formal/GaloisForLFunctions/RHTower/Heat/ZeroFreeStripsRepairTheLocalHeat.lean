import GaloisForLFunctions.RHTower.Heat.TheLocalHeatThreshold
import GaloisForLFunctions.SquareRootThreshold.AStripGivesLittlewoodWindows
import GaloisForLFunctions.RHTower.EvenLandauPairTest
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion

/-!
# Zero-free strips repair the local heat

**Repair** (`exists_localHeatThreshold_mul_log_le_of_strip`).  If every zero of height `≥ T₀` lies
within `d` of the critical line, `ℓ ≥ 1`, `ℓd ≤ 1` and `d e^{2ℓd} s(ℓ) C ≤ E/4`, then
`λ_t log t ≤ K/ℓ` at all large `t` with `Ξ(t) ≠ 0`, `K = 2048 D²A²/E`.  The Littlewood count under
the strip (`Littlewood.exists_strip_window_count_bound`) puts `≥ E log t/(8ℓA²)` zeros in
`(t − D/ℓ, t + D/ℓ]`; they lie within `R = D/ℓ + d ≤ 2D/ℓ` of `t`
(`N_le_card_xiSliceGaussianRadiusHead`), and the depth–count bound `λ_t ≤ 64R²/N(t, R)` applies.

**Equivalence** (`eventually_localHeat_le_iff_zeros_tend_to_the_line`).  `λ_t log t → 0` iff for
every `d > 0` all high zeros lie within `d` of the line.  Repair with `ℓ → ∞`, `d → 0` gives one
direction, extended to the heights with `Ξ(t) = 0` by lower semicontinuity of `λ_t`, since the real
zeros of `Ξ` are isolated (`localHeatThreshold_mul_log_le_of_punctured`).  Detection,
`(β − ½)²/200 ≤ λ_γ log γ`, gives the other.
-/

open Complex Filter Topology
open scoped ComplexConjugate
open Zeta23

namespace RHTower.DeBruijn

noncomputable section

private theorem spectral_re (q : XiZeroCopy) : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint]

private theorem spectral_im (q : XiZeroCopy) :
    (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
  simp [xiSpectralPoint]

/-- **Window zeros lie in the radius head.**  Under a strip of depth `d` above `T₀`, every zero
with `t − h < Im ρ ≤ t + h` lies within `h + d` of `t`, so `N(t − h, t + h)` is at most the number
of zero copies in the radius-`(h + d)` head. -/
theorem N_le_card_xiSliceGaussianRadiusHead {d T₀ t h : ℝ} (hS : Littlewood.ZeroFreeStrip d T₀)
    (hT₀ : T₀ ≤ t - h) (ht : 0 ≤ t - h) :
    (zetaZeroConfig.N (t - h) (t + h) : ℝ) ≤ (xiSliceGaussianRadiusHead t (h + d)).card := by
  classical
  have hfin : (zetaZeroConfig.window (t - h) (t + h)).Finite := zetaZeroConfig.finite_window _ _
  set g : ℂ → ℝ := fun z => if ‖(z - 1 / 2) * (-I) - (t : ℂ)‖ ≤ h + d then 1 else 0 with hg
  have hgq : ∀ q : XiZeroCopy,
      g (q.1 : ℂ) = if q ∈ xiSliceGaussianRadiusHead t (h + d) then 1 else 0 := by
    intro q; simp only [hg, mem_xiSliceGaussianRadiusHead, xiSpectralPoint]
  have hsum : Summable fun q : XiZeroCopy => g (q.1 : ℂ) := by
    refine summable_of_ne_finset_zero (s := xiSliceGaussianRadiusHead t (h + d)) (fun q hq => ?_)
    rw [hgq, if_neg hq]
  have htsum : ∑' q : XiZeroCopy, g (q.1 : ℂ) = (xiSliceGaussianRadiusHead t (h + d)).card := by
    rw [tsum_eq_sum (s := xiSliceGaussianRadiusHead t (h + d)) (fun q hq => by rw [hgq, if_neg hq]),
      Finset.sum_congr rfl (fun q hq => by rw [hgq, if_pos hq])]
    simp
  have hle := GaloisForLFunctions.SquareRootThreshold.sum_mult_le_tsum_copies g
    (fun q => by simp only [hg]; split_ifs <;> norm_num) hsum hfin.toFinset
    (fun ρ hρ => by obtain ⟨hc, -⟩ := (Set.Finite.mem_toFinset hfin).mp hρ; exact hc)
  rw [htsum] at hle
  refine le_trans (le_of_eq ?_) hle
  unfold ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  obtain ⟨hc, him1, him2⟩ := (Set.Finite.mem_toFinset hfin).mp hρ
  have hd : |ρ.re - 1 / 2| ≤ d := hS ρ hc (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hnorm : ‖(ρ - 1 / 2) * (-I) - (t : ℂ)‖ ≤ h + d := by
    have e : (ρ - 1 / 2) * (-I) - (t : ℂ) =
        ((ρ.im - t : ℝ) : ℂ) + ((-(ρ.re - 1 / 2) : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg]
    have : |ρ.im - t| ≤ h := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  simp only [hg, if_pos hnorm, mul_one]

/-- The repair constant `K = 2048 D²A²/E`. -/
def heatRepairConst : ℝ :=
  2048 * Littlewood.windowD ^ 2 * Littlewood.bumpMass ^ 2 / Littlewood.energy 0

theorem stripConst_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) : 0 ≤ Littlewood.stripConst ℓ := by
  have h0 := Littlewood.errConst_nonneg hℓ 0
  have h1 := Littlewood.errConst_nonneg hℓ 1
  unfold Littlewood.stripConst
  positivity

/-- **A zero-free strip repairs the heat at rate `1/ℓ`.**  There is `C > 0` such that if every zero
of height `≥ T₀` lies within `d` of the critical line, `1 ≤ ℓ`, `ℓd ≤ 1` and
`d e^{2ℓd} s(ℓ) C ≤ E/4`, then `λ_t log t ≤ K/ℓ` at all large heights with `Ξ(t) ≠ 0`. -/
theorem exists_localHeatThreshold_mul_log_le_of_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ d T₀ : ℝ, 1 ≤ ℓ → 0 ≤ d → ℓ * d ≤ 1 →
      d * Real.exp (2 * ℓ * d) * Littlewood.stripConst ℓ * C ≤ Littlewood.energy 0 / 4 →
      Littlewood.ZeroFreeStrip d T₀ →
      ∀ᶠ t : ℝ in atTop, XiC t ≠ 0 → localHeatThreshold t * Real.log t ≤ heatRepairConst / ℓ := by
  obtain ⟨C, hC0, hW⟩ := Littlewood.exists_strip_window_count_bound
  refine ⟨C, hC0, fun ℓ d T₀ hℓ hd hℓd hsmall hS => ?_⟩
  obtain ⟨M, hM⟩ := hW ℓ d T₀ hℓ hd hS
  have hℓ0 : 0 < ℓ := by linarith
  set D := Littlewood.windowD with hDdef
  set A := Littlewood.bumpMass
  set E := Littlewood.energy 0 with hE
  have hE0 : 0 < E := Littlewood.energy_zero_pos
  have hD1 : 1 ≤ D := Littlewood.one_le_windowD
  have hDℓ : 0 < D / ℓ := div_pos (by linarith) hℓ0
  have hdD : d ≤ D / ℓ := by rw [le_div_iff₀ hℓ0]; nlinarith
  have hlog : ∀ᶠ t : ℝ in atTop, 8 * M ≤ E * Real.log t := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (8 * M / E)] with t ht
    rw [div_le_iff₀ hE0] at ht; linarith
  filter_upwards [hM, hlog, eventually_ge_atTop (|T₀| + D / ℓ + 2)] with t hWt hlt ht hXi
  have hT₀ := le_abs_self T₀
  have hL : 0 < Real.log t := Real.log_pos (by linarith [abs_nonneg T₀])
  set L := Real.log t
  set N : ℝ := (zetaZeroConfig.N (t - D / ℓ) (t + D / ℓ) : ℝ)
  set R := D / ℓ + d with hR
  -- `ℓA²N ≥ E log t/8`
  have hcount : E * L ≤ 8 * (ℓ * A ^ 2 * N) := by
    have := mul_le_mul_of_nonneg_right hsmall hL.le
    linarith
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNpos : 0 < N := by
    by_contra h
    have h0 : N = 0 := le_antisymm (not_lt.mp h) hN0
    rw [h0, mul_zero, mul_zero] at hcount
    nlinarith
  have hhead := N_le_card_xiSliceGaussianRadiusHead (d := d) (t := t) hS (h := D / ℓ) (by linarith)
    (by linarith [abs_nonneg T₀])
  have hcard : 0 < (xiSliceGaussianRadiusHead t R).card := by
    have : (0 : ℝ) < (xiSliceGaussianRadiusHead t R).card := lt_of_lt_of_le hNpos hhead
    exact_mod_cast this
  have hdepth : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re - t| < 1 / 2 →
      (xiSpectralPoint q).im ^ 2 ≤ d ^ 2 := by
    intro q hq
    rw [spectral_re] at hq
    rw [spectral_im, neg_sq, ← sq_abs]
    have hγ : T₀ ≤ |(q.1 : ℂ).im| := by
      have := (abs_lt.mp hq).1
      rw [abs_of_nonneg (by linarith [abs_nonneg T₀])]
      linarith
    exact pow_le_pow_left₀ (abs_nonneg _) (hS _ (xiZeroCopy_mem_carrier q) hγ) 2
  have hδR : 2 * d ^ 2 ≤ R ^ 2 := by rw [hR]; nlinarith
  have hlam := localHeatThreshold_le_of_depth_count hXi (by positivity) hδR hdepth hcard
  have hlamN : localHeatThreshold t ≤ 64 * R ^ 2 / N :=
    hlam.trans (div_le_div_of_nonneg_left (by positivity) hNpos hhead)
  have hRℓ : R * ℓ ≤ 2 * D := by
    rw [hR, add_mul, div_mul_cancel₀ _ hℓ0.ne']; nlinarith
  have hRℓ2 : (R * ℓ) ^ 2 ≤ 4 * D ^ 2 := by
    have : 0 ≤ R * ℓ := by positivity
    nlinarith
  have hkey : 64 * R ^ 2 * L / N ≤ heatRepairConst / ℓ := by
    unfold heatRepairConst
    rw [div_div, div_le_div_iff₀ hNpos (by positivity)]
    calc 64 * R ^ 2 * L * (E * ℓ) = 64 * R ^ 2 * ℓ * (E * L) := by ring
      _ ≤ 64 * R ^ 2 * ℓ * (8 * (ℓ * A ^ 2 * N)) :=
          mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = 512 * (R * ℓ) ^ 2 * (A ^ 2 * N) := by ring
      _ ≤ 512 * (4 * D ^ 2) * (A ^ 2 * N) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRℓ2 (by norm_num))
            (by positivity)
      _ = 2048 * D ^ 2 * A ^ 2 * N := by ring
  calc localHeatThreshold t * L ≤ 64 * R ^ 2 / N * L := mul_le_mul_of_nonneg_right hlamN hL.le
    _ = 64 * R ^ 2 * L / N := by ring
    _ ≤ heatRepairConst / ℓ := hkey

/-- **Upper bounds pass to the zeros of `Ξ`.**  If `λ_s log s ≤ ε` on a punctured neighbourhood of
`t > 1`, then `λ_t log t ≤ ε`: `λ` is lower semicontinuous and `ε/log s` is continuous at `t`. -/
theorem localHeatThreshold_mul_log_le_of_punctured {t ε : ℝ} (ht : 1 < t)
    (h : ∀ᶠ s in 𝓝[≠] t, localHeatThreshold s * Real.log s ≤ ε) :
    localHeatThreshold t * Real.log t ≤ ε := by
  have hL : 0 < Real.log t := Real.log_pos ht
  by_contra hlt
  push Not at hlt
  have hlt' : ε / Real.log t < localHeatThreshold t := by rw [div_lt_iff₀ hL]; linarith
  set y := (localHeatThreshold t + ε / Real.log t) / 2 with hy
  have hy1 : y < localHeatThreshold t := by rw [hy]; linarith
  have hy2 : ε / Real.log t < y := by rw [hy]; linarith
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log (by linarith)
  have h1 : ∀ᶠ s in 𝓝[≠] t, y < localHeatThreshold s :=
    nhdsWithin_le_nhds (lowerSemicontinuous_localHeatThreshold t y hy1)
  have h2 : ∀ᶠ s in 𝓝[≠] t, ε / Real.log s < y :=
    nhdsWithin_le_nhds ((continuousAt_const.div hlog hL.ne').eventually (gt_mem_nhds hy2))
  have h3 : ∀ᶠ s in 𝓝[≠] t, 0 < Real.log s :=
    nhdsWithin_le_nhds (hlog.eventually (lt_mem_nhds hL))
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := (h.and (h1.and (h2.and h3))).exists
  have : localHeatThreshold s ≤ ε / Real.log s := by rw [le_div_iff₀ hs4]; exact hs1
  linarith

/-- A bound at the large heights with `Ξ(t) ≠ 0` holds at all large heights. -/
theorem localHeatThreshold_mul_log_le_of_forall_ne_zero {ε t₀ : ℝ}
    (h : ∀ t, t₀ ≤ t → XiC t ≠ 0 → localHeatThreshold t * Real.log t ≤ ε) :
    ∀ t, max t₀ 1 < t → localHeatThreshold t * Real.log t ≤ ε := by
  intro t ht
  refine localHeatThreshold_mul_log_le_of_punctured (lt_of_le_of_lt (le_max_right _ _) ht) ?_
  have hmap : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] t) (𝓝[≠] (t : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun s hs => fun h => hs (Complex.ofReal_injective h))
  have hXi : ∀ᶠ s : ℝ in 𝓝[≠] t, XiC (s : ℂ) ≠ 0 :=
    hmap.eventually (eventually_XiC_ne_zero_punctured _)
  have hge : ∀ᶠ s : ℝ in 𝓝[≠] t, t₀ ≤ s :=
    nhdsWithin_le_nhds ((lt_mem_nhds (lt_of_le_of_lt (le_max_left _ _) ht)).mono fun s hs => hs.le)
  filter_upwards [hXi, hge] with s hs1 hs2 using h s hs2 hs1

/-- **Zeros tending to the line repair the heat.**  If for every `d > 0` all high zeros lie within
`d` of the critical line, then `λ_t log t ≤ ε` at all large heights, for every `ε > 0`. -/
theorem eventually_localHeatThreshold_mul_log_le_of_strips
    (h : ∀ d > 0, ∃ T₀, Littlewood.ZeroFreeStrip d T₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, localHeatThreshold t * Real.log t ≤ ε := by
  obtain ⟨C, hC0, hrep⟩ := exists_localHeatThreshold_mul_log_le_of_strip
  set ℓ := max 1 (heatRepairConst / ε) with hℓ
  have hℓ1 : 1 ≤ ℓ := le_max_left _ _
  have hℓ0 : 0 < ℓ := by linarith
  have hK : heatRepairConst / ℓ ≤ ε := by
    rw [div_le_iff₀ hℓ0]
    calc heatRepairConst = heatRepairConst / ε * ε := by field_simp
      _ ≤ ℓ * ε := mul_le_mul_of_nonneg_right (le_max_right _ _) hε.le
      _ = ε * ℓ := mul_comm _ _
  set s := Littlewood.stripConst ℓ
  have hs : 0 ≤ s := stripConst_nonneg hℓ0
  have hE0 := Littlewood.energy_zero_pos
  set d := min (1 / ℓ) (Littlewood.energy 0 / (4 * (Real.exp 2 * s * C + 1))) with hd
  have hd0 : 0 < d := lt_min (by positivity) (by positivity)
  have hℓd : ℓ * d ≤ 1 := by
    calc ℓ * d ≤ ℓ * (1 / ℓ) := mul_le_mul_of_nonneg_left (min_le_left _ _) hℓ0.le
      _ = 1 := by field_simp
  have hsmall : d * Real.exp (2 * ℓ * d) * s * C ≤ Littlewood.energy 0 / 4 := by
    have he : Real.exp (2 * ℓ * d) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
    have h1 : Real.exp (2 * ℓ * d) * s * C ≤ Real.exp 2 * s * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hs) hC0.le
    have h2 := mul_le_mul_of_nonneg_left h1 hd0.le
    have hd2 : d ≤ Littlewood.energy 0 / (4 * (Real.exp 2 * s * C + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at hd2
    nlinarith
  obtain ⟨T₀, hS⟩ := h d hd0
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (hrep ℓ d T₀ hℓ1 hd0.le hℓd hsmall hS)
  have hall := localHeatThreshold_mul_log_le_of_forall_ne_zero (fun t ht hXi => ht₀ t ht hXi)
  exact eventually_atTop.mpr ⟨max t₀ 1 + 1, fun t ht => (hall t (by linarith)).trans hK⟩

/-- **Detection gives the strips.**  If `λ_t log t ≤ ε` at all large heights for every `ε > 0`,
then for every `d > 0` all high zeros lie within `d` of the critical line. -/
theorem strips_of_eventually_localHeatThreshold_mul_log_le
    (h : ∀ ε > 0, ∀ᶠ t : ℝ in atTop, localHeatThreshold t * Real.log t ≤ ε) :
    ∀ d > 0, ∃ T₀, Littlewood.ZeroFreeStrip d T₀ := by
  intro d hd
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (h (d ^ 2 / 200) (by positivity))
  refine ⟨max t₀ (Real.exp 1600), fun ρ hρ hT => ?_⟩
  -- the representative in the upper right quarter: same depth, height `|Im ρ|`
  have hrep : ∃ σ ∈ zetaZeroConfig.carrier, σ.re - 1 / 2 = |ρ.re - 1 / 2| ∧ σ.im = |ρ.im| := by
    have hc := conj_mem_zetaZeroConfig hρ
    rcases le_total (1 / 2) ρ.re with hr | hr <;> rcases le_total 0 ρ.im with hi | hi
    · exact ⟨ρ, hρ, by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ.re - 1 / 2)],
        by rw [abs_of_nonneg hi]⟩
    · exact ⟨conj ρ, hc, by rw [Complex.conj_re, abs_of_nonneg
        (by linarith : (0 : ℝ) ≤ ρ.re - 1 / 2)], by rw [Complex.conj_im, abs_of_nonpos hi]⟩
    · refine ⟨1 - conj ρ, one_sub_mem_zetaZeroConfig hc, ?_, ?_⟩
      · rw [Complex.sub_re, Complex.one_re, Complex.conj_re,
          abs_of_nonpos (by linarith : ρ.re - 1 / 2 ≤ 0)]; ring
      · rw [Complex.sub_im, Complex.one_im, Complex.conj_im, abs_of_nonneg hi]; ring
    · refine ⟨1 - ρ, one_sub_mem_zetaZeroConfig hρ, ?_, ?_⟩
      · rw [Complex.sub_re, Complex.one_re, abs_of_nonpos (by linarith : ρ.re - 1 / 2 ≤ 0)]; ring
      · rw [Complex.sub_im, Complex.one_im, abs_of_nonpos hi]; ring
  obtain ⟨σ, hσ, hσre, hσim⟩ := hrep
  rw [← hσre]
  rcases le_or_gt (σ.re - 1 / 2) 0 with h0 | hpos
  · linarith
  have hxi := (CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
    hσ).1
  have hγ : max t₀ (Real.exp 1600) ≤ σ.im := hσim ▸ hT
  have hγe : Real.exp 1600 ≤ σ.im := le_trans (le_max_right _ _) hγ
  have hL : 0 < Real.log σ.im := Real.log_pos (lt_of_lt_of_le
    (by have := Real.add_one_le_exp (1600 : ℝ); linarith) hγe)
  have hdet := le_localHeatThreshold_of_offLine_zero hxi (by linarith) hγe
  rw [div_le_iff₀ hL] at hdet
  have hup := ht₀ σ.im (le_trans (le_max_left _ _) hγ)
  have hsq : (σ.re - 1 / 2) ^ 2 ≤ d ^ 2 := by linarith
  nlinarith

/-- **The heat pincer closes iff the zeros tend to the line.**  `λ_t log t ≤ ε` at all large
heights for every `ε > 0` iff, for every `d > 0`, all high zeros lie within `d` of the critical
line. -/
theorem eventually_localHeat_le_iff_zeros_tend_to_the_line :
    (∀ ε > 0, ∀ᶠ t : ℝ in atTop, localHeatThreshold t * Real.log t ≤ ε) ↔
      ∀ d > 0, ∃ T₀, Littlewood.ZeroFreeStrip d T₀ :=
  ⟨strips_of_eventually_localHeatThreshold_mul_log_le,
    fun h _ hε => eventually_localHeatThreshold_mul_log_le_of_strips h hε⟩

end

end RHTower.DeBruijn

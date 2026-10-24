import GaloisForLFunctions.BiScaleUncertainty.WeilLagCriticalDeficitEndpointAndLimitLaw
import GaloisForLFunctions.BiScaleUncertainty.FiniteSpectralEnvelopeRealization
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSeventeenThirtiethsUnconditional
import GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley
import GaloisForLFunctions.RHTower.ZetaZeroDensityHypothesisFiveSixths
import GaloisForLFunctions.RHTower.XiZeroFoldedHeightCount
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel

/-!
# Zero-Density Filtered Critical Prime Deficit and the Ingham–Guth–Maynard `4/3` Linear Deficit Law

While the unfiltered incoming prime deficit `ccmPrimeDeficitIncoming T` is governed by the worst
single zero (`zetaZeroWidth`, with best unconditional pointwise saving at the Vinogradov–Korobov
sub-linear exponent `T^{3/5 - ε}`), cosine modulation at high frequency `γ ∈ [Γ, 2Γ]` localizes the
reciprocal-square spectral sum `spectralDeficitSum t = Σ_q e^{t(ρ_q - 1/2)} / ρ_q²` to ordinates
`|Im ρ_q| ≍ Γ`, replacing single-zero supremum control by unconditional zero-density counts
`N(σ, Γ)`.

This module establishes the zero-density filtering machinery and proves polynomial frequency-average
cancellation of `ccmPrimeDeficitIncoming` up to logarithmic aperture `A ≤ α log Γ` for every
`α < 2/3` (strictly containing both Huxley's `5/12` and Guth–Maynard's `13/30`):

1. **Hybrid Ingham–Guth–Maynard–DH Zero-Density Exponent and the Global `4/3` Linear Deficit Law (§1)**
   (`igmDensityExponent`, `igmDensityExponent_le_thirty_thirteenths`,
   `igmDensityExponent_le_one_sub_four_thirds`,
   `exists_zeroHeightBox_ncard_le_one_sub_four_thirds_uniform`):
   A naive application of `N(σ, T) ≪ T^{(30/13)(1-σ)}` alone exceeds `T^1` on `σ ∈ (1/2, 17/30)`.
   Combining Ingham's `3(1 - σ)/(2 - σ)` on `[1/2, 7/10]`, Guth–Maynard's `(30/13)(1 - σ)` on
   `(7/10, 5/6)`, and the Density Hypothesis `2(1 - σ)` on `[5/6, 1]` yields the global linear
   deficit inequality
   `igmDensityExponent σ ≤ 1 - (4 / 3) * (σ - 1 / 2)` across **all** `σ ∈ [1/2, 1]`.
   Discretizing `[1/2 + θ, 7/10]` by a finite antitone grid (`zeroHeightBox_ncard_antitone`) and
   joining it with the uniform `30/13` bound on `[7/10, 1]` produces a uniform zero-density estimate
   `#(zeroHeightBox σ T) ≤ D (1 + log T)^B T^{1 - (4/3 - δ)(σ - 1/2)}` across `σ ∈ [1/2 + θ, 1]`.

2. **Folded Dyadic-Shell Exponential Sums up to Aperture `A ≤ α log T`, `α < 2/3` (§2)**
   (`exp_foldedRe_le_sum_slabs`, `sum_exp_foldedRe_le_zeroHeightBox`,
   `exists_sum_exp_foldedRe_deep_decay_up_to_two_thirds_log`,
   `exists_sum_exp_foldedRe_le_subpower_up_to_two_thirds_log`,
   `exists_sum_exp_foldedRe_threeShells_le_subpower`):
   Using the 4-fold reflection/conjugation symmetry of `XiZeroCopy` (`ncard_foldedHeightBox_le`) and
   slab slicing `slabAbscissa M m = 1/2 + m/(2M)`, for every `α ∈ [0, 2/3)`:
   * Deep off-line zeros (`foldedRe q ≥ 1/2 + θ`) satisfy strict polynomial per-unit-height decay
     `(1 / T) Σ e^{2A(foldedRe q - 1/2)} ≤ C T^{-(4/3 - 2α)θ / 8}` for all `0 ≤ A ≤ α log T`.
   * Full dyadic shells (`T/2 ≤ |Im ρ_q| ≤ 4T`) satisfy the sub-power bound
     `(1 / T) Σ e^{2A(foldedRe q - 1/2)} ≤ C_{α,η} T^η` for every `η > 0` and all `0 ≤ A ≤ α log T`.

3. **Polynomial Decay of Cosine-Filtered `spectralDeficitSum` and `ccmPrimeDeficitIncoming` (§3–§4)**
   (`inv_one_add_sq_remote_le`, `norm_integral_exp_strip_mul_le`,
   `exists_frequencyAverage_abs_cosineFiltered_spectralDeficitSum_le`,
   `exists_frequencyAverage_abs_cosineFiltered_ccmPrimeDeficitIncoming_le`):
   For any `C²_c` test window `ψ` supported in `[0, 2A]` with `0 ≤ A ≤ α log Γ` (`α < 2/3`),
   two integrations by parts localize each zero mode to `(1 + (γ_q ∓ γ)²)^{-1}`, remote ordinates
   `|γ_q| ∉ [Γ/2, 4Γ]` decay as `O(Γ^{α - 2})` via `summable_inv_norm_sq_xiZeroCopy`, local shells
   gain `‖ρ_q‖^{-2} ≤ 4 Γ^{-2}` against the `O(Γ^{1 + 1/6})` zero-density sum, and the archimedean
   explicit-formula error `|ccmPrimeDeficitIncoming t - Re(spectralDeficitSum t)| ≤ C₀(1+t)e^{-t/2}`
   has `L²(ℝ)` cosine-correlation `O(1)` by Plancherel. Consequently,
   `(1 / Γ) ∫_Γ^{2Γ} |∫_0^{2A} ccmPrimeDeficitIncoming t * ψ t * cos(γ t) dt| dγ ≤ C_α Γ^{-1/2} N(ψ)`,
   decaying polynomially to `0` as `Γ → ∞` where unfiltered bounds grow exponentially in `A`.
-/

open MeasureTheory Set Filter Topology Complex Finset
open scoped BigOperators Real ENNReal NNReal

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open _root_.RHTower _root_.Zeta23

noncomputable section
set_option autoImplicit false

/-! ## §1. Hybrid Ingham–Guth–Maynard–DH Exponent and the Global `4/3` Linear Deficit Law -/

/-- The hybrid unconditional zero-density exponent combining Ingham's `3(1 - σ)/(2 - σ)` on
`[1/2, 7/10]`, Guth–Maynard's `(30/13)(1 - σ)` on `(7/10, 5/6)`, and the Density Hypothesis
`2(1 - σ)` on `[5/6, 1]`. -/
def igmDensityExponent (σ : ℝ) : ℝ :=
  if σ ≤ 7 / 10 then 3 * (1 - σ) / (2 - σ)
  else if σ < 5 / 6 then (30 / 13) * (1 - σ)
  else 2 * (1 - σ)

theorem igmDensityExponent_nonneg {σ : ℝ} (hσ1 : σ ≤ 1) :
    0 ≤ igmDensityExponent σ := by
  unfold igmDensityExponent
  split_ifs with h1 h2
  · exact div_nonneg (by linarith) (by linarith)
  · linarith
  · linarith

/-- Across `[1/2, 1]`, the hybrid exponent never exceeds Guth–Maynard's `(30/13)(1 - σ)`. -/
theorem igmDensityExponent_le_thirty_thirteenths {σ : ℝ} (_hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    igmDensityExponent σ ≤ (30 / 13) * (1 - σ) := by
  unfold igmDensityExponent
  split_ifs with h1 h2
  · rw [div_le_iff₀ (by linarith : 0 < 2 - σ)]
    nlinarith
  · exact le_rfl
  · nlinarith

/-- Strict linear margin on `[7/10, 1]`: `(30/13)(1 - σ) + 8/195 ≤ 1 - (4/3)(σ - 1/2)`. -/
theorem thirty_thirteenths_le_one_sub_four_thirds_sub_gap {σ : ℝ} (hσ : 7 / 10 ≤ σ) :
    (30 / 13) * (1 - σ) + 8 / 195 ≤ 1 - (4 / 3) * (σ - 1 / 2) := by
  linarith

/-- Ingham linear deficit on `[1/2, 3/4]`: `3(1 - σ)/(2 - σ) ≤ 1 - (4/3)(σ - 1/2)`. -/
theorem ingham_div_le_one_sub_four_thirds {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 3 / 4) :
    3 * (1 - σ) / (2 - σ) ≤ 1 - (4 / 3) * (σ - 1 / 2) := by
  rw [div_le_iff₀ (by linarith : 0 < 2 - σ)]
  nlinarith

/-- **Global `4/3` Linear Deficit Law (`igmDensityExponent_le_one_sub_four_thirds`):**
Across the entire half-strip `σ ∈ [1/2, 1]`, the combined Ingham–Guth–Maynard–DH exponent satisfies
`igmDensityExponent σ ≤ 1 - (4 / 3) * (σ - 1 / 2)`, with equality at `σ = 1/2`. -/
theorem igmDensityExponent_le_one_sub_four_thirds {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (_hσ1 : σ ≤ 1) :
    igmDensityExponent σ ≤ 1 - (4 / 3) * (σ - 1 / 2) := by
  unfold igmDensityExponent
  split_ifs with h1 h2
  · exact ingham_div_le_one_sub_four_thirds hσ0 (by linarith)
  · have := thirty_thirteenths_le_one_sub_four_thirds_sub_gap (not_le.mp h1).le
    linarith
  · nlinarith

/-- Pointwise off-line zero-density bound on `(1/2, 7/10]` with linear deficit `1 - (4/3)(σ - 1/2) + ε`. -/
private theorem exists_zeroHeightBox_ncard_le_ingham_linear {σ ε : ℝ}
    (hσ0 : 1 / 2 < σ) (hσ1 : σ ≤ 7 / 10) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ((zeroHeightBox σ T).ncard : ℝ) ≤
        D * (1 + Real.log T) ^ B * T ^ (1 - (4 / 3) * (σ - 1 / 2) + ε) := by
  obtain ⟨D, hD, B, T₀, hT₀, hbox⟩ :=
    exists_zeroHeightBox_ncard_le_ingham_huxley hσ0 (by linarith) hε0 hε1
  refine ⟨D, hD, B, T₀, hT₀, fun T hT => (hbox T hT).trans ?_⟩
  have hT1 : 1 ≤ T := hT₀.trans hT
  have hA : inghamHuxleyExponent σ = 3 / (2 - σ) := by
    unfold inghamHuxleyExponent
    rw [if_pos (by linarith)]
  have hexp : (inghamHuxleyExponent σ + ε) * (1 - σ) ≤ 1 - (4 / 3) * (σ - 1 / 2) + ε := by
    rw [hA]
    have hlin := ingham_div_le_one_sub_four_thirds hσ0.le (by linarith)
    have heq : 3 / (2 - σ) * (1 - σ) = 3 * (1 - σ) / (2 - σ) := by ring
    have hεsub : ε * (1 - σ) ≤ ε := mul_le_of_le_one_right hε0.le (by linarith)
    linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 hexp)
    (mul_nonneg hD (pow_nonneg (by linarith [Real.log_nonneg hT1]) _))

/-- **Uniform Strip Zero-Density Theorem (`exists_zeroHeightBox_ncard_le_one_sub_four_thirds_uniform`):**
For every abscissa margin `0 < θ ≤ 1/2` and slope slack `0 < δ < 4/3`, there exist `D ≥ 0`,
`B : ℕ`, and `T₀ ≥ 1` such that for all `T ≥ T₀` and **all** `σ ∈ [1/2 + θ, 1]`,
`#(zeroHeightBox σ T) ≤ D (1 + log T)^B T^{1 - (4/3 - δ)(σ - 1/2)}`. -/
theorem exists_zeroHeightBox_ncard_le_one_sub_four_thirds_uniform
    {θ δ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) (hδ0 : 0 < δ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 + θ ≤ σ → σ ≤ 1 →
        ((zeroHeightBox σ T).ncard : ℝ) ≤
          D * (1 + Real.log T) ^ B * T ^ (1 - (4 / 3 - δ) * (σ - 1 / 2)) := by
  -- High-abscissa branch `[7/10, 1]` via uniform Guth–Maynard `30/13`
  obtain ⟨D_gm, hD_gm, B_gm, T_gm, hT_gm, hgm⟩ :=
    exists_zeroHeightBox_ncard_le_thirtyThirteenths (ε := 8 / 195) (by norm_num) (by norm_num)
  by_cases hhigh : 7 / 10 ≤ 1 / 2 + θ
  · refine ⟨D_gm, hD_gm, B_gm, T_gm, hT_gm, fun T hT σ hσ0 hσ1 => (hgm T hT σ (by linarith) hσ1).trans ?_⟩
    have hT1 : 1 ≤ T := hT_gm.trans hT
    have hgap := thirty_thirteenths_le_one_sub_four_thirds_sub_gap (hhigh.trans hσ0)
    have hexp : (30 / 13 + 8 / 195) * (1 - σ) ≤ 1 - (4 / 3 - δ) * (σ - 1 / 2) := by
      have h1 : (8 / 195 : ℝ) * (1 - σ) ≤ 8 / 195 := by nlinarith
      have h2 : 0 ≤ δ * (σ - 1 / 2) := mul_nonneg hδ0.le (by linarith)
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 hexp)
      (mul_nonneg hD_gm (pow_nonneg (by linarith [Real.log_nonneg hT1]) _))
  · push Not at hhigh
    -- Finite grid on `[1/2 + θ, 7/10]` with step `h` and slack `ε₂`
    set ε₂ : ℝ := min 1 (δ * θ / 2)
    have hε₂0 : 0 < ε₂ := lt_min zero_lt_one (by positivity)
    have hε₂1 : ε₂ ≤ 1 := min_le_left _ _
    have hε₂_le : ε₂ ≤ δ * θ / 2 := min_le_right _ _
    set h : ℝ := δ * θ / 4
    have hh0 : 0 < h := by positivity
    set σ_grid : ℕ → ℝ := fun k => min (1 / 2 + θ + (k : ℝ) * h) (7 / 10)
    have hgrid : ∀ k : ℕ, 1 / 2 < σ_grid k ∧ σ_grid k ≤ 7 / 10 := fun k =>
      ⟨lt_of_lt_of_le (by linarith) (le_min (le_add_of_nonneg_right (by positivity)) hhigh.le),
       min_le_right _ _⟩
    choose Dk hDk Bk Tk hTk1 hTk using fun k : ℕ =>
      exists_zeroHeightBox_ncard_le_ingham_linear (hgrid k).1 (hgrid k).2 hε₂0 hε₂1
    set K : ℕ := ⌈(7 / 10 - (1 / 2 + θ)) / h⌉₊
    set D_tot : ℝ := D_gm + ∑ k ∈ Finset.range (K + 1), Dk k
    set B_tot : ℕ := B_gm + ∑ k ∈ Finset.range (K + 1), Bk k
    set T_tot : ℝ := max T_gm (1 + ∑ k ∈ Finset.range (K + 1), |Tk k|)
    have hD_tot : 0 ≤ D_tot := add_nonneg hD_gm (Finset.sum_nonneg fun k _ => hDk k)
    have hT_tot : 1 ≤ T_tot := hT_gm.trans (le_max_left _ _)
    refine ⟨D_tot, hD_tot, B_tot, T_tot, hT_tot, fun T hT σ hσ0 hσ1 => ?_⟩
    have hT1 : 1 ≤ T := hT_tot.trans hT
    have hl1 : 1 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
    have hl0 : 0 ≤ 1 + Real.log T := by linarith
    by_cases hσ7 : 7 / 10 ≤ σ
    · have h1 := hgm T ((le_max_left _ _).trans hT) σ (by linarith) hσ1
      have hgap := thirty_thirteenths_le_one_sub_four_thirds_sub_gap hσ7
      have hexp : (30 / 13 + 8 / 195) * (1 - σ) ≤ 1 - (4 / 3 - δ) * (σ - 1 / 2) := by
        have : (8 / 195 : ℝ) * (1 - σ) ≤ 8 / 195 := by nlinarith
        have : 0 ≤ δ * (σ - 1 / 2) := mul_nonneg hδ0.le (by linarith)
        nlinarith
      have hD_le : D_gm ≤ D_tot := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hDk k)
      have hB_le : (1 + Real.log T) ^ B_gm ≤ (1 + Real.log T) ^ B_tot :=
        pow_le_pow_right₀ hl1 (Nat.le_add_right _ _)
      have hT_le := Real.rpow_le_rpow_of_exponent_le hT1 hexp
      exact h1.trans (mul_le_mul (mul_le_mul hD_le hB_le (pow_nonneg hl0 _) hD_tot)
        hT_le (Real.rpow_nonneg (by linarith) _) (mul_nonneg hD_tot (pow_nonneg hl0 _)))
    · push Not at hσ7
      set k : ℕ := ⌊(σ - (1 / 2 + θ)) / h⌋₊
      have hq0 : 0 ≤ (σ - (1 / 2 + θ)) / h := div_nonneg (by linarith) hh0.le
      have hkle : (k : ℝ) * h ≤ σ - (1 / 2 + θ) := (le_div_iff₀ hh0).mp (Nat.floor_le hq0)
      have hkgt : σ - (1 / 2 + θ) < ((k : ℝ) + 1) * h := (div_lt_iff₀ hh0).mp (Nat.lt_floor_add_one _)
      have hkK : k ∈ Finset.range (K + 1) := by
        rw [Finset.mem_range, Nat.lt_succ_iff]
        exact (Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh0.le)).trans
          (Nat.floor_le_ceil _)
      have hgk : σ_grid k = 1 / 2 + θ + (k : ℝ) * h := min_eq_left (by linarith)
      have hTk_le : Tk k ≤ T := by
        have hsum_le : |Tk k| ≤ ∑ j ∈ Finset.range (K + 1), |Tk j| :=
          Finset.single_le_sum (f := fun j => |Tk j|) (fun _ _ => abs_nonneg _) hkK
        have hmax := (le_max_right T_gm (1 + ∑ j ∈ Finset.range (K + 1), |Tk j|)).trans hT
        linarith [le_abs_self (Tk k)]
      have hanti : ((zeroHeightBox σ T).ncard : ℝ) ≤ ((zeroHeightBox (σ_grid k) T).ncard : ℝ) :=
        zeroHeightBox_ncard_antitone (by rw [hgk]; linarith)
      have hk_bound := hTk k T hTk_le
      have hexp : 1 - (4 / 3) * (σ_grid k - 1 / 2) + ε₂ ≤ 1 - (4 / 3 - δ) * (σ - 1 / 2) := by
        rw [hgk]
        have hstep : σ - (1 / 2 + θ + (k : ℝ) * h) ≤ h := by linarith
        have h43 : (4 / 3 : ℝ) * h = δ * θ / 3 := by dsimp [h]; ring
        have hθ_le : δ * θ ≤ δ * (σ - 1 / 2) := mul_le_mul_of_nonneg_left (by linarith) hδ0.le
        linarith
      have hD_le : Dk k ≤ D_tot := by
        have := Finset.single_le_sum (f := Dk) (fun j _ => hDk j) hkK
        linarith [hD_gm]
      have hB_le : (1 + Real.log T) ^ Bk k ≤ (1 + Real.log T) ^ B_tot := by
        refine pow_le_pow_right₀ hl1 ?_
        have := Finset.single_le_sum (f := Bk) (fun j _ => Nat.zero_le (Bk j)) hkK
        omega
      have hT_le := Real.rpow_le_rpow_of_exponent_le hT1 hexp
      exact hanti.trans (hk_bound.trans (mul_le_mul
        (mul_le_mul hD_le hB_le (pow_nonneg hl0 _) hD_tot)
        hT_le (Real.rpow_nonneg (by linarith) _) (mul_nonneg hD_tot (pow_nonneg hl0 _))))

/-! ## §2. Folded Dyadic-Shell Exponential Sums up to Aperture `A ≤ α log T` (`α < 2/3`) -/

/-- Slab upper bound for `exp(2A(y - 1/2))` across `M` slabs `slabAbscissa M m = 1/2 + m/(2M)`. -/
theorem exp_foldedRe_le_sum_slabs {A : ℝ} (hA : 0 ≤ A) {M : ℕ} (hM : 0 < M)
    {y : ℝ} (hy1 : 1 / 2 ≤ y) (hy2 : y < 1) :
    Real.exp (2 * A * (y - 1 / 2)) ≤
      ∑ m ∈ range M,
        if slabAbscissa M m ≤ y then Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) else 0 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set j := ⌊(y - 1 / 2) * (2 * M)⌋₊
  have hnn : 0 ≤ (y - 1 / 2) * (2 * M) := mul_nonneg (by linarith) (by positivity)
  have hjle : (j : ℝ) ≤ (y - 1 / 2) * (2 * M) := Nat.floor_le hnn
  have hjlt : (y - 1 / 2) * (2 * M) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjM : j < M := by
    have : (j : ℝ) < M := by nlinarith
    exact_mod_cast this
  have hlow : slabAbscissa M j ≤ y := by
    rw [slabAbscissa]
    have : (j : ℝ) / (2 * M) ≤ y - 1 / 2 := (div_le_iff₀ (by positivity)).mpr hjle
    linarith
  have hup : y ≤ slabAbscissa M (j + 1) := by
    rw [slabAbscissa]
    push_cast
    have : y - 1 / 2 ≤ ((j : ℝ) + 1) / (2 * M) := (le_div_iff₀ (by positivity)).mpr hjlt.le
    linarith
  have hterm : Real.exp (2 * A * (y - 1 / 2)) ≤
      Real.exp (2 * A * (slabAbscissa M (j + 1) - 1 / 2)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  set f : ℕ → ℝ := fun m =>
    if slabAbscissa M m ≤ y then Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) else 0
  have hfj : f j = Real.exp (2 * A * (slabAbscissa M (j + 1) - 1 / 2)) := if_pos hlow
  have hf0 : ∀ m ∈ Finset.range M, 0 ≤ f m := fun m _ => by
    dsimp [f]; split_ifs; exacts [(Real.exp_pos _).le, le_rfl]
  exact (hterm.trans_eq hfj.symm).trans (Finset.single_le_sum hf0 (Finset.mem_range.mpr hjM))

/-- **Folded Layer-Cake Bound for `exp(2A(foldedRe q - 1/2))` (`sum_exp_foldedRe_le_zeroHeightBox`):**
Any finite set `G` of zero copies in the folded dyadic shell `T ≤ |Im ρ_q| ≤ 2T` is bounded by
four times the `M`-slab sum over `zeroHeightBox (slabAbscissa M m) T`. -/
theorem sum_exp_foldedRe_le_zeroHeightBox {A : ℝ} (hA : 0 ≤ A) {M : ℕ} (hM : 0 < M) {T : ℝ}
    (G : Finset XiZeroCopy) (hG : ∀ q ∈ G, T ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * T) :
    ∑ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
      4 * ∑ m ∈ range M,
        Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) *
          ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ) := by
  classical
  have hpt : ∀ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
      ∑ m ∈ range M,
        if slabAbscissa M m ≤ foldedRe q then
          Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) else 0 :=
    fun q _ => exp_foldedRe_le_sum_slabs hA hM (half_le_foldedRe q) (foldedRe_lt_one q)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hxp : 0 ≤ Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) := (Real.exp_pos _).le
  have hsub : ((G.filter fun q => slabAbscissa M m ≤ foldedRe q : Finset XiZeroCopy) :
      Set XiZeroCopy) ⊆ foldedHeightBox (slabAbscissa M m) T := by
    intro q hq
    rw [Finset.coe_filter] at hq
    exact ⟨hq.2, hG q hq.1⟩
  have h1 := Set.ncard_le_ncard hsub (foldedHeightBox_finite _ _)
  rw [Set.ncard_coe_finset] at h1
  have h2 := ncard_foldedHeightBox_le (slabAbscissa M m) T
  have hcard : ((G.filter fun q => slabAbscissa M m ≤ foldedRe q).card : ℝ) ≤
      4 * ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ) := by
    exact_mod_cast h1.trans h2
  nlinarith

/-- Global `O(T log T)` bound on `zeroHeightBox (1/2) T` in clean `(1 + log T) * T` form for `T ≥ 4`. -/
theorem exists_zeroHeightBox_half_le_mul_log :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ {T : ℝ}, 4 ≤ T → ∀ {σ : ℝ}, 1 / 2 ≤ σ →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ Cg * (1 + Real.log T) * T := by
  obtain ⟨C, hC, hglob⟩ := exists_ncard_zeroHeightBox_le_global
  refine ⟨9 * C, by positivity, fun {T} hT4 {σ} hσ => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog25 : Real.log (2 * T + 5) ≤ 3 * (1 + Real.log T) := by
    have h := Real.log_le_log (by linarith) (show 2 * T + 5 ≤ 4 * T by linarith)
    rw [Real.log_mul (by norm_num) hT0.ne'] at h
    have h4 : Real.log 4 ≤ 2 := by
      have h2 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_lt_d9]
    linarith [Real.log_nonneg hT1]
  calc ((zeroHeightBox σ T).ncard : ℝ) ≤ C * (2 * T + 4) * Real.log (2 * T + 5) := hglob hσ hT1
    _ ≤ C * (3 * T) * (3 * (1 + Real.log T)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC.le) hlog25
          (Real.log_nonneg (by linarith)) (by positivity)
    _ = 9 * C * (1 + Real.log T) * T := by ring

/-- Polylogarithmic absorption `(1 + log T)^B ≤ C_{B,ε} T^ε` for `T ≥ 1` and `ε > 0`. -/
theorem exists_one_add_log_pow_le_rpow (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℝ, 1 ≤ T → (1 + Real.log T) ^ B ≤ K * T ^ ε := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · refine ⟨1, le_rfl, fun T hT => ?_⟩
    rw [pow_zero, one_mul]
    exact Real.one_le_rpow hT hε.le
  · have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    set η : ℝ := ε / B
    have hη : 0 < η := div_pos hε hB0
    have hη_inv : 0 < 1 / η := div_pos zero_lt_one hη
    set c : ℝ := 1 + 1 / η
    have hc : 1 ≤ c := by dsimp [c]; linarith
    refine ⟨c ^ B, one_le_pow₀ hc, fun T hT => ?_⟩
    have hT0 : 0 < T := by linarith
    have h1 : 1 + Real.log T ≤ c * T ^ η := by
      have hexp := Real.add_one_le_exp (η * Real.log T)
      have hrew : Real.exp (η * Real.log T) = T ^ η := by
        rw [Real.rpow_def_of_pos hT0, mul_comm]
      rw [hrew] at hexp
      have h1_le : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
      have hmul := mul_le_mul_of_nonneg_left hexp hη_inv.le
      have hsimp : 1 / η * (η * Real.log T + 1) = Real.log T + 1 / η := by
        have hne : η ≠ 0 := hη.ne'
        field_simp
      rw [hsimp] at hmul
      dsimp [c]
      linarith
    calc (1 + Real.log T) ^ B ≤ (c * T ^ η) ^ B :=
          pow_le_pow_left₀ (by linarith [Real.log_nonneg hT]) h1 B
      _ = c ^ B * (T ^ η) ^ B := mul_pow c (T ^ η) B
      _ = c ^ B * T ^ ε := by
          rw [← Real.rpow_natCast (T ^ η), ← Real.rpow_mul hT0.le]
          congr 2
          dsimp [η]
          exact div_mul_cancel₀ ε hB0.ne'

/-- **Deep Off-Line Polynomial Decay up to `A ≤ α log T`, `α < 2/3`
(`exists_sum_exp_foldedRe_deep_decay_up_to_two_thirds_log`):**
For every `0 ≤ α < 2/3` and every depth threshold `0 < θ < 1/2`, there exist `C ≥ 0` and `T₀ ≥ 4`
such that for all `T ≥ T₀`, all `0 ≤ A ≤ α log T`, and every finite set `G` of zero copies in
`T ≤ |Im ρ_q| ≤ 2T` with `foldedRe q ≥ 1/2 + θ`,
`(1 / T) * Σ_{q ∈ G} e^{2A(foldedRe q - 1/2)} ≤ C * T^{-(4/3 - 2α)θ / 8}`. -/
theorem exists_sum_exp_foldedRe_deep_decay_up_to_two_thirds_log
    {α θ : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ A : ℝ, 0 ≤ A → A ≤ α * Real.log T →
        ∀ G : Finset XiZeroCopy,
          (∀ q ∈ G, 1 / 2 + θ ≤ foldedRe q ∧ T ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * T) →
          (1 / T) * (∑ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2))) ≤
            C * T ^ (-((4 / 3 - 2 * α) * θ / 8)) := by
  set γ₀ : ℝ := (4 / 3 - 2 * α) * θ / 8
  have hγ₀ : 0 < γ₀ := by dsimp [γ₀]; nlinarith
  set δ : ℝ := (4 / 3 - 2 * α) / 4
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  -- Choose slab resolution `M` so `1/(2M) ≤ θ/2` and `(2α + 2)(1/(2M)) ≤ γ₀`
  set M : ℕ := max (⌈1 / θ⌉₊ + 1) (⌈(2 * α + 2) / γ₀⌉₊ + 1)
  have hM : 0 < M := lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hstep_θ : 1 / (2 * (M : ℝ)) ≤ θ / 2 := by
    have h1 : (1 / θ : ℝ) ≤ M := (Nat.le_ceil _).trans (by
      have : ⌈1 / θ⌉₊ ≤ M := (Nat.le_succ _).trans (le_max_left _ _)
      exact_mod_cast this)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := (div_le_iff₀ hθ0).mp h1
    linarith
  have hstep_γ : (2 * α + 2) * (1 / (2 * (M : ℝ))) ≤ γ₀ := by
    have h1 : ((2 * α + 2) / γ₀ : ℝ) ≤ M := (Nat.le_ceil _).trans (by
      have : ⌈(2 * α + 2) / γ₀⌉₊ ≤ M := (Nat.le_succ _).trans (le_max_right _ _)
      exact_mod_cast this)
    have h2 := (div_le_iff₀ hγ₀).mp h1
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨D, hD, B, T₁, hT₁, huni⟩ :=
    exists_zeroHeightBox_ncard_le_one_sub_four_thirds_uniform
      (θ := θ / 2) (δ := δ) (by positivity) (by linarith) hδ0
  obtain ⟨K_log, hK1, hK_log⟩ := exists_one_add_log_pow_le_rpow B hγ₀
  refine ⟨4 * M * D * K_log, by positivity, max 4 T₁, le_max_left _ _,
    fun T hT A hA0 hA G hG => ?_⟩
  have hT4 : 4 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hT_ge1 : 1 ≤ T := by linarith
  have hT_T₁ : T₁ ≤ T := (le_max_right _ _).trans hT
  -- Every `q ∈ G` falls into its floor slab `j < M` with `slabAbscissa M j ≥ 1/2 + θ/2`
  classical
  have hpt : ∀ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
      ∑ m ∈ Finset.range M,
        if slabAbscissa M m ≤ foldedRe q ∧ 1 / 2 + θ / 2 ≤ slabAbscissa M m then
          Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) else 0 := by
    intro q hq
    set y := foldedRe q
    have hyθ : 1 / 2 + θ ≤ y := (hG q hq).1
    have hy2 : y < 1 := foldedRe_lt_one q
    set j := ⌊(y - 1 / 2) * (2 * M)⌋₊
    have hnn : 0 ≤ (y - 1 / 2) * (2 * M) := mul_nonneg (by linarith) (by positivity)
    have hjle : (j : ℝ) ≤ (y - 1 / 2) * (2 * M) := Nat.floor_le hnn
    have hjlt : (y - 1 / 2) * (2 * M) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hjM : j < M := by
      have : (j : ℝ) < M := by nlinarith
      exact_mod_cast this
    have hlow : slabAbscissa M j ≤ y := by
      rw [slabAbscissa]
      have : (j : ℝ) / (2 * M) ≤ y - 1 / 2 := (div_le_iff₀ (by positivity)).mpr hjle
      linarith
    have hup : y ≤ slabAbscissa M (j + 1) := by
      rw [slabAbscissa]; push_cast
      have : y - 1 / 2 ≤ ((j : ℝ) + 1) / (2 * M) := (le_div_iff₀ (by positivity)).mpr hjlt.le
      linarith
    have hdiff : slabAbscissa M (j + 1) - slabAbscissa M j = 1 / (2 * (M : ℝ)) := by
      unfold slabAbscissa; push_cast; ring
    have hjθ : 1 / 2 + θ / 2 ≤ slabAbscissa M j := by linarith
    have hterm : Real.exp (2 * A * (y - 1 / 2)) ≤
        Real.exp (2 * A * (slabAbscissa M (j + 1) - 1 / 2)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    set f : ℕ → ℝ := fun m =>
      if slabAbscissa M m ≤ y ∧ 1 / 2 + θ / 2 ≤ slabAbscissa M m then
        Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) else 0
    have hfj : f j = Real.exp (2 * A * (slabAbscissa M (j + 1) - 1 / 2)) := if_pos ⟨hlow, hjθ⟩
    have hf0 : ∀ m ∈ Finset.range M, 0 ≤ f m := fun m _ => by
      dsimp [f]; split_ifs; exacts [(Real.exp_pos _).le, le_rfl]
    exact (hterm.trans_eq hfj.symm).trans (Finset.single_le_sum hf0 (Finset.mem_range.mpr hjM))
  have hsum1 : ∑ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
      4 * ∑ m ∈ Finset.range M,
        if 1 / 2 + θ / 2 ≤ slabAbscissa M m then
          Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) *
            ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ)
        else 0 := by
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    by_cases hmθ : 1 / 2 + θ / 2 ≤ slabAbscissa M m
    · rw [if_pos hmθ]
      have hsimp : (∑ x ∈ G, if slabAbscissa M m ≤ foldedRe x ∧ 1 / 2 + θ / 2 ≤ slabAbscissa M m then
          Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) else 0) =
          ∑ x ∈ G, if slabAbscissa M m ≤ foldedRe x then
            Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) else 0 :=
        Finset.sum_congr rfl fun x _ => by
          by_cases hx : slabAbscissa M m ≤ foldedRe x
          · rw [if_pos ⟨hx, hmθ⟩, if_pos hx]
          · rw [if_neg (fun h => hx h.1), if_neg hx]
      rw [hsimp, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hsub : ((G.filter fun q => slabAbscissa M m ≤ foldedRe q : Finset XiZeroCopy) :
          Set XiZeroCopy) ⊆ foldedHeightBox (slabAbscissa M m) T := by
        intro q hq
        rw [Finset.coe_filter] at hq
        exact ⟨hq.2, (hG q hq.1).2⟩
      have h1 := Set.ncard_le_ncard hsub (foldedHeightBox_finite _ _)
      rw [Set.ncard_coe_finset] at h1
      have hcard : ((G.filter fun q => slabAbscissa M m ≤ foldedRe q).card : ℝ) ≤
          4 * ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ) := by
        exact_mod_cast h1.trans (ncard_foldedHeightBox_le (slabAbscissa M m) T)
      have hxp : 0 ≤ Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) := (Real.exp_pos _).le
      nlinarith
    · rw [if_neg hmθ, mul_zero]
      exact le_of_eq (Finset.sum_eq_zero fun x _ => if_neg (fun h => hmθ h.2))
  have hslab_bound : ∀ m ∈ Finset.range M,
      (if 1 / 2 + θ / 2 ≤ slabAbscissa M m then
        Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) *
          ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ)
      else 0) ≤ D * K_log * T ^ (1 - γ₀) := by
    intro m hm
    split_ifs with hmθ
    · have hm_lt : m < M := Finset.mem_range.mp hm
      have hm1 : slabAbscissa M m ≤ 1 := by
        unfold slabAbscissa
        have : (m : ℝ) ≤ M := by exact_mod_cast hm_lt.le
        have : (m : ℝ) / (2 * M) ≤ 1 / 2 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith)
        linarith
      have hbox := huni T hT_T₁ (slabAbscissa M m) hmθ hm1
      have hdiff : slabAbscissa M (m + 1) - 1 / 2 =
          (slabAbscissa M m - 1 / 2) + 1 / (2 * (M : ℝ)) := by
        unfold slabAbscissa; push_cast; ring
      have hsub_nonneg : 0 ≤ slabAbscissa M (m + 1) - 1 / 2 := by
        rw [hdiff]; linarith [show 0 < 1 / (2 * (M : ℝ)) by positivity]
      have hexpA : Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) ≤
          T ^ (2 * α * (slabAbscissa M (m + 1) - 1 / 2)) := by
        have hle : 2 * A * (slabAbscissa M (m + 1) - 1 / 2) ≤
            2 * α * (slabAbscissa M (m + 1) - 1 / 2) * Real.log T := by
          have := mul_le_mul_of_nonneg_right hA hsub_nonneg
          linarith
        calc Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2))
            ≤ Real.exp (2 * α * (slabAbscissa M (m + 1) - 1 / 2) * Real.log T) :=
              Real.exp_le_exp.mpr hle
          _ = T ^ (2 * α * (slabAbscissa M (m + 1) - 1 / 2)) := by
              rw [Real.rpow_def_of_pos hT0, mul_comm]
      have hlogB := hK_log T hT_ge1
      have htot_exp : 2 * α * (slabAbscissa M (m + 1) - 1 / 2) + γ₀ +
          (1 - (4 / 3 - δ) * (slabAbscissa M m - 1 / 2)) ≤ 1 - γ₀ := by
        rw [hdiff]
        have hs : θ / 2 ≤ slabAbscissa M m - 1 / 2 := by linarith
        have hslope : (4 / 3 - δ - 2 * α) * (slabAbscissa M m - 1 / 2) ≥ 3 * γ₀ := by
          have hcoef : 4 / 3 - δ - 2 * α = 3 * (4 / 3 - 2 * α) / 4 := by dsimp [δ]; ring
          rw [hcoef]
          have hnn_c : 0 ≤ 3 * (4 / 3 - 2 * α) / 4 := by linarith
          have hmul_s := mul_le_mul_of_nonneg_left hs hnn_c
          dsimp [γ₀]
          linarith
        have hstep_a : 2 * α * (1 / (2 * (M : ℝ))) ≤ γ₀ := by
          have : 0 ≤ 1 / (2 * (M : ℝ)) := by positivity
          nlinarith [hstep_γ]
        linarith
      calc Real.exp (2 * A * (slabAbscissa M (m + 1) - 1 / 2)) *
              ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ)
          ≤ T ^ (2 * α * (slabAbscissa M (m + 1) - 1 / 2)) *
              (D * (K_log * T ^ γ₀) * T ^ (1 - (4 / 3 - δ) * (slabAbscissa M m - 1 / 2))) := by
            refine mul_le_mul hexpA (hbox.trans ?_) (Nat.cast_nonneg _)
              (Real.rpow_nonneg hT0.le _)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlogB hD) (Real.rpow_nonneg hT0.le _)
        _ = D * K_log * (T ^ (2 * α * (slabAbscissa M (m + 1) - 1 / 2)) *
              T ^ γ₀ * T ^ (1 - (4 / 3 - δ) * (slabAbscissa M m - 1 / 2))) := by ring
        _ = D * K_log * T ^ (2 * α * (slabAbscissa M (m + 1) - 1 / 2) + γ₀ +
              (1 - (4 / 3 - δ) * (slabAbscissa M m - 1 / 2))) := by
            rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
        _ ≤ D * K_log * T ^ (1 - γ₀) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT_ge1 htot_exp)
              (by positivity)
    · positivity
  have hsum2 : ∑ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
      4 * M * D * K_log * T ^ (1 - γ₀) := by
    refine hsum1.trans ?_
    have := Finset.sum_le_sum hslab_bound
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    nlinarith
  calc (1 / T) * (∑ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2)))
      ≤ (1 / T) * (4 * M * D * K_log * T ^ (1 - γ₀)) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = 4 * M * D * K_log * (T ^ (-1 : ℝ) * T ^ (1 - γ₀)) := by
        rw [Real.rpow_neg_one]; ring
    _ = 4 * M * D * K_log * T ^ (-γ₀) := by
        rw [← Real.rpow_add hT0]; ring_nf

/-- **Full Folded Shell Sub-Power Bound up to `A ≤ α log T`, `α < 2/3`
(`exists_sum_exp_foldedRe_le_subpower_up_to_two_thirds_log`):**
For every `0 ≤ α < 2/3` and every `η > 0`, there exist `C ≥ 0` and `T₀ ≥ 4` such that for all
`T ≥ T₀`, all `0 ≤ A ≤ α log T`, and every finite set `G` of zero copies in `T ≤ |Im ρ_q| ≤ 2T`,
`(1 / T) * Σ_{q ∈ G} e^{2A(foldedRe q - 1/2)} ≤ C * T^η`. -/
theorem exists_sum_exp_foldedRe_le_subpower_up_to_two_thirds_log
    {α η : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ A : ℝ, 0 ≤ A → A ≤ α * Real.log T →
        ∀ G : Finset XiZeroCopy,
          (∀ q ∈ G, T ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * T) →
          (1 / T) * (∑ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2))) ≤ C * T ^ η := by
  set θ : ℝ := min (1 / 4) (η / (4 * (α + 1)))
  have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hθ_η : 2 * α * θ ≤ η / 2 := by
    have hle : θ ≤ η / (4 * (α + 1)) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 * α)
    have hdiv : 2 * α * (η / (4 * (α + 1))) ≤ η / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  obtain ⟨C_deep, hC_deep, T_deep, hT_deep, hdeep⟩ :=
    exists_sum_exp_foldedRe_deep_decay_up_to_two_thirds_log hα0 hα hθ0 hθ1
  obtain ⟨Cg, hCg, hglob⟩ := exists_zeroHeightBox_half_le_mul_log
  obtain ⟨K_log, hK1, hK_log⟩ := exists_one_add_log_pow_le_rpow 1 (by positivity : 0 < η / 2)
  refine ⟨4 * Cg * K_log + C_deep, by positivity, T_deep, hT_deep,
    fun T hT A hA0 hA G hG => ?_⟩
  classical
  have hT4 : 4 ≤ T := hT_deep.trans hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  set G_near := G.filter (fun q => foldedRe q < 1 / 2 + θ)
  set G_deep := G.filter (fun q => 1 / 2 + θ ≤ foldedRe q)
  have hsplit : ∑ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2)) =
      (∑ q ∈ G_near, Real.exp (2 * A * (foldedRe q - 1 / 2))) +
        ∑ q ∈ G_deep, Real.exp (2 * A * (foldedRe q - 1 / 2)) := by
    dsimp [G_near, G_deep]
    rw [← Finset.sum_filter_add_sum_filter_not G (fun q => foldedRe q < 1 / 2 + θ)]
    congr 2
    ext q
    simp [not_lt]
  -- Shallow part `G_near`
  have hnear_card : (G_near.card : ℝ) ≤ 4 * Cg * (1 + Real.log T) * T := by
    have hsub : (G_near : Set XiZeroCopy) ⊆ foldedHeightBox (1 / 2) T := by
      intro q hq
      rw [Finset.coe_filter] at hq
      exact ⟨half_le_foldedRe q, hG q hq.1⟩
    have h1 := Set.ncard_le_ncard hsub (foldedHeightBox_finite _ _)
    rw [Set.ncard_coe_finset] at h1
    have h2 : (G_near.card : ℝ) ≤ 4 * ((zeroHeightBox (1 / 2) T).ncard : ℝ) := by
      exact_mod_cast h1.trans (ncard_foldedHeightBox_le (1 / 2) T)
    have h3 := hglob hT4 (le_rfl : (1 / 2 : ℝ) ≤ 1 / 2)
    nlinarith
  have hnear_pt : ∀ q ∈ G_near, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤ T ^ (η / 2) := by
    intro q hq
    have hq_lt : foldedRe q < 1 / 2 + θ := (Finset.mem_filter.mp hq).2
    have hq_ge : 1 / 2 ≤ foldedRe q := half_le_foldedRe q
    have hexp1 : 2 * A * (foldedRe q - 1 / 2) ≤ (η / 2) * Real.log T := by
      have h1 : 2 * A * (foldedRe q - 1 / 2) ≤ 2 * (α * Real.log T) * θ := by
        have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
        nlinarith
      have h2 : 2 * (α * Real.log T) * θ = (2 * α * θ) * Real.log T := by ring
      have h3 := mul_le_mul_of_nonneg_right hθ_η (Real.log_nonneg hT1)
      linarith
    calc Real.exp (2 * A * (foldedRe q - 1 / 2))
        ≤ Real.exp ((η / 2) * Real.log T) := Real.exp_le_exp.mpr hexp1
      _ = T ^ (η / 2) := by rw [Real.rpow_def_of_pos hT0, mul_comm]
  have hnear_sum : (1 / T) * ∑ q ∈ G_near, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
      4 * Cg * K_log * T ^ η := by
    have hs1 : ∑ q ∈ G_near, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
        (G_near.card : ℝ) * T ^ (η / 2) := by
      refine (Finset.sum_le_sum hnear_pt).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have hlog1 : 1 + Real.log T ≤ K_log * T ^ (η / 2) := by
      simpa only [pow_one] using hK_log T hT1
    calc (1 / T) * ∑ q ∈ G_near, Real.exp (2 * A * (foldedRe q - 1 / 2))
        ≤ (1 / T) * ((4 * Cg * (1 + Real.log T) * T) * T ^ (η / 2)) :=
          mul_le_mul_of_nonneg_left
            (hs1.trans (mul_le_mul_of_nonneg_right hnear_card (Real.rpow_nonneg hT0.le _)))
            (by positivity)
      _ = 4 * Cg * (1 + Real.log T) * T ^ (η / 2) := by field_simp
      _ ≤ 4 * Cg * (K_log * T ^ (η / 2)) * T ^ (η / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog1 (by positivity))
            (Real.rpow_nonneg hT0.le _)
      _ = 4 * Cg * K_log * (T ^ (η / 2) * T ^ (η / 2)) := by ring
      _ = 4 * Cg * K_log * T ^ η := by rw [← Real.rpow_add hT0]; ring_nf
  -- Deep part `G_deep`
  have hdeep_sum : (1 / T) * ∑ q ∈ G_deep, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
      C_deep * T ^ η := by
    have hd := hdeep T hT A hA0 hA G_deep fun q hq => by
      rw [Finset.mem_filter] at hq
      exact ⟨hq.2, hG q hq.1⟩
    refine hd.trans (mul_le_mul_of_nonneg_left ?_ hC_deep)
    refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
    have : 0 < (4 / 3 - 2 * α) * θ / 8 := div_pos (mul_pos (by linarith) hθ0) (by norm_num)
    linarith
  rw [hsplit, mul_add, add_mul]
  exact add_le_add hnear_sum hdeep_sum

/-- **Three-Shell Sub-Power Bound across `Γ/2 ≤ |Im ρ_q| ≤ 4Γ`
(`exists_sum_exp_foldedRe_threeShells_le_subpower`):**
Covers `[Γ/2, Γ] ∪ [Γ, 2Γ] ∪ [2Γ, 4Γ]` simultaneously for any `0 ≤ A ≤ α log Γ` (`α < 2/3`). -/
theorem exists_sum_exp_foldedRe_threeShells_le_subpower
    {α η : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Γ₀ : ℝ, 8 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ A : ℝ, 0 ≤ A → A ≤ α * Real.log Γ →
        ∀ G : Finset XiZeroCopy,
          (∀ q ∈ G, Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ) →
          (1 / Γ) * (∑ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2))) ≤ C * Γ ^ η := by
  set α' : ℝ := (α + 2 / 3) / 2
  have hα'0 : 0 ≤ α' := by dsimp [α']; linarith
  have hα'_lt : α' < 2 / 3 := by dsimp [α']; linarith
  have hα_lt_α' : α < α' := by dsimp [α']; linarith
  obtain ⟨C₁, hC₁, T₀, hT₀, hshell⟩ :=
    exists_sum_exp_foldedRe_le_subpower_up_to_two_thirds_log hα'0 hα'_lt hη
  -- For `Γ ≥ Γ₀`, `α * log Γ ≤ α' * log(Γ / 2)`
  set Γ₁ : ℝ := Real.exp (α' * Real.log 2 / (α' - α))
  refine ⟨4 * C₁ * (2 : ℝ) ^ η, by positivity, max 8 (max (2 * T₀) Γ₁), le_max_left _ _,
    fun Γ hΓ A hA0 hA G hG => ?_⟩
  have hΓ8 : 8 ≤ Γ := (le_max_left _ _).trans hΓ
  have hΓ0 : 0 < Γ := by linarith
  have hΓ_T₀ : 2 * T₀ ≤ Γ := ((le_max_left _ _).trans (le_max_right _ _)).trans hΓ
  have hΓ_Γ₁ : Γ₁ ≤ Γ := ((le_max_right _ _).trans (le_max_right _ _)).trans hΓ
  have hA_half : A ≤ α' * Real.log (Γ / 2) := by
    have hlog_ge : α' * Real.log 2 / (α' - α) ≤ Real.log Γ := by
      have := Real.log_le_log (Real.exp_pos _) hΓ_Γ₁
      rwa [Real.log_exp] at this
    have hdiff_pos : 0 < α' - α := by linarith
    have hmul := (div_le_iff₀ hdiff_pos).mp hlog_ge
    have hlog_div : Real.log (Γ / 2) = Real.log Γ - Real.log 2 :=
      Real.log_div hΓ0.ne' (by norm_num)
    rw [hlog_div]
    nlinarith
  have hA_one : A ≤ α' * Real.log Γ := by
    have hlog0 : 0 ≤ Real.log Γ := Real.log_nonneg (by linarith)
    nlinarith
  have hA_two : A ≤ α' * Real.log (2 * Γ) := by
    have : Real.log Γ ≤ Real.log (2 * Γ) := Real.log_le_log hΓ0 (by linarith)
    linarith [mul_le_mul_of_nonneg_left this hα'0]
  classical
  set G₁ := G.filter (fun q => |(q.1 : ℂ).im| ≤ Γ)
  set G₂ := G.filter (fun q => Γ < |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * Γ)
  set G₃ := G.filter (fun q => 2 * Γ < |(q.1 : ℂ).im|)
  have hcover : ∑ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
      (∑ q ∈ G₁, Real.exp (2 * A * (foldedRe q - 1 / 2))) +
      (∑ q ∈ G₂, Real.exp (2 * A * (foldedRe q - 1 / 2))) +
      (∑ q ∈ G₃, Real.exp (2 * A * (foldedRe q - 1 / 2))) := by
    have hpt : ∀ q ∈ G, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
        (if |(q.1 : ℂ).im| ≤ Γ then Real.exp (2 * A * (foldedRe q - 1 / 2)) else 0) +
        (if Γ < |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * Γ then
          Real.exp (2 * A * (foldedRe q - 1 / 2)) else 0) +
        (if 2 * Γ < |(q.1 : ℂ).im| then Real.exp (2 * A * (foldedRe q - 1 / 2)) else 0) := by
      intro q _
      by_cases h1 : |(q.1 : ℂ).im| ≤ Γ
      · rw [if_pos h1, if_neg (fun h => not_lt_of_ge h1 h.1),
          if_neg (by linarith : ¬(2 * Γ < |(q.1 : ℂ).im|))]; ring_nf; exact le_rfl
      · push Not at h1
        by_cases h2 : |(q.1 : ℂ).im| ≤ 2 * Γ
        · rw [if_neg (not_le.mpr h1), if_pos ⟨h1, h2⟩, if_neg (not_lt.mpr h2)]; ring_nf; exact le_rfl
        · push Not at h2
          rw [if_neg (not_le.mpr h1), if_neg (fun h => not_le.mpr h2 h.2), if_pos h2]
          ring_nf; exact le_rfl
    refine (Finset.sum_le_sum hpt).trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.sum_filter]
    exact le_rfl
  have hb1 : (1 / Γ) * ∑ q ∈ G₁, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤ C₁ * Γ ^ η := by
    have h := hshell (Γ / 2) (by linarith) A hA0 hA_half G₁ fun q hq => by
      rw [Finset.mem_filter] at hq
      exact ⟨(hG q hq.1).1, by linarith [hq.2]⟩
    have hpow : (Γ / 2) ^ η ≤ Γ ^ η := Real.rpow_le_rpow (by positivity) (by linarith) hη.le
    have hmul : (1 / Γ) * ∑ q ∈ G₁, Real.exp (2 * A * (foldedRe q - 1 / 2)) =
        (1 / 2) * ((1 / (Γ / 2)) * ∑ q ∈ G₁, Real.exp (2 * A * (foldedRe q - 1 / 2))) := by ring
    rw [hmul]
    calc (1 / 2) * ((1 / (Γ / 2)) * ∑ q ∈ G₁, Real.exp (2 * A * (foldedRe q - 1 / 2)))
        ≤ 1 * (C₁ * (Γ / 2) ^ η) := mul_le_mul (by norm_num) h (by positivity) zero_le_one
      _ ≤ C₁ * Γ ^ η := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow hC₁
  have hb2 : (1 / Γ) * ∑ q ∈ G₂, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤ C₁ * Γ ^ η :=
    hshell Γ (by linarith) A hA0 hA_one G₂ fun q hq => by
      rw [Finset.mem_filter] at hq
      exact ⟨hq.2.1.le, hq.2.2⟩
  have hb3 : (1 / Γ) * ∑ q ∈ G₃, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
      2 * C₁ * (2 : ℝ) ^ η * Γ ^ η := by
    have h := hshell (2 * Γ) (by linarith) A hA0 hA_two G₃ fun q hq => by
      rw [Finset.mem_filter] at hq
      exact ⟨hq.2.le, by linarith [(hG q hq.1).2]⟩
    have hmul : (1 / Γ) * ∑ q ∈ G₃, Real.exp (2 * A * (foldedRe q - 1 / 2)) =
        2 * ((1 / (2 * Γ)) * ∑ q ∈ G₃, Real.exp (2 * A * (foldedRe q - 1 / 2))) := by ring
    rw [Real.mul_rpow (by norm_num) hΓ0.le] at h
    rw [hmul]
    nlinarith
  have h2pow : 1 ≤ (2 : ℝ) ^ η := Real.one_le_rpow (by norm_num) hη.le
  have h1le : C₁ * Γ ^ η ≤ C₁ * (2 : ℝ) ^ η * Γ ^ η := by
    have : 0 ≤ C₁ * Γ ^ η := by positivity
    nlinarith
  have hcov_mul := mul_le_mul_of_nonneg_left hcover (by positivity : 0 ≤ 1 / Γ)
  rw [mul_add, mul_add] at hcov_mul
  linarith

/-! ## §3. Remote-Ordinate Decay and Two-Integration-by-Parts Strip Localization -/

/-- Remote-ordinate Lorentzian decay: for `γ ∈ [Γ, 2Γ]` (`Γ ≥ 1`) and `|t| < Γ/2` or `|t| > 4Γ`,
`1 / (1 + (t - γ)²) ≤ 4 / Γ²` and `1 / (1 + (t - γ)²)² ≤ (16 / Γ²) / (1 + t²)`. -/
theorem inv_one_add_sq_remote_le {Γ γ t : ℝ} (hΓ : 1 ≤ Γ)
    (hγ1 : Γ ≤ γ) (hγ2 : γ ≤ 2 * Γ) (ht : |t| < Γ / 2 ∨ 4 * Γ < |t|) :
    1 / (1 + (t - γ) ^ 2) ≤ 4 / Γ ^ 2 ∧
      1 / (1 + (t - γ) ^ 2) ^ 2 ≤ (16 / Γ ^ 2) * (1 / (1 + t ^ 2)) := by
  rcases ht with hlow | hhigh
  · have hdiff : Γ / 2 ≤ γ - t := by
      have := le_abs_self t
      linarith
    have hsq : Γ ^ 2 / 4 ≤ (t - γ) ^ 2 := by
      have : (Γ / 2) ^ 2 ≤ (γ - t) ^ 2 := pow_le_pow_left₀ (by positivity) hdiff 2
      linarith [show (t - γ) ^ 2 = (γ - t) ^ 2 by ring]
    have h1 : 1 / (1 + (t - γ) ^ 2) ≤ 4 / Γ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have h2 : 1 + t ^ 2 ≤ 4 * (1 + (t - γ) ^ 2) := by
      have ht_sq : t ^ 2 ≤ Γ ^ 2 / 4 := by
        have := pow_le_pow_left₀ (abs_nonneg t) hlow.le 2
        rw [sq_abs] at this
        linarith
      linarith [sq_nonneg (t - γ)]
    refine ⟨h1, ?_⟩
    calc 1 / (1 + (t - γ) ^ 2) ^ 2
        = (1 / (1 + (t - γ) ^ 2)) * (1 / (1 + (t - γ) ^ 2)) := by simp [sq]
      _ ≤ (4 / Γ ^ 2) * (4 / (1 + t ^ 2)) := by
          refine mul_le_mul h1 ?_ (by positivity) (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
      _ = (16 / Γ ^ 2) * (1 / (1 + t ^ 2)) := by ring
  · have hsq_half : (|t| / 2) ^ 2 ≤ (t - γ) ^ 2 := by
      have h1 : |t| - |γ| ≤ |t - γ| := abs_sub_abs_le_abs_sub t γ
      have hγ_abs : |γ| = γ := abs_of_pos (by linarith)
      have h2 : |t| / 2 ≤ |t - γ| := by linarith
      have h3 := pow_le_pow_left₀ (by positivity) h2 2
      rwa [sq_abs] at h3
    have htsq : t ^ 2 / 4 ≤ (t - γ) ^ 2 := by
      rw [div_pow, sq_abs] at hsq_half
      linarith
    have hΓsq : 4 * Γ ^ 2 ≤ (t - γ) ^ 2 := by
      have : (4 * Γ) ^ 2 ≤ t ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hhigh.le 2
        rwa [sq_abs] at this
      linarith
    have h1 : 1 / (1 + (t - γ) ^ 2) ≤ 4 / Γ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : 1 / (1 + (t - γ) ^ 2) ≤ 4 / (1 + t ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    refine ⟨h1, ?_⟩
    calc 1 / (1 + (t - γ) ^ 2) ^ 2
        = (1 / (1 + (t - γ) ^ 2)) * (1 / (1 + (t - γ) ^ 2)) := by simp [sq]
      _ ≤ (4 / Γ ^ 2) * (4 / (1 + t ^ 2)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (16 / Γ ^ 2) * (1 / (1 + t ^ 2)) := by ring

/-- Symmetric version of `inv_one_add_sq_remote_le` for `t + γ = -((-t) - γ)`. -/
theorem inv_one_add_sq_remote_add_le {Γ γ t : ℝ} (hΓ : 1 ≤ Γ)
    (hγ1 : Γ ≤ γ) (hγ2 : γ ≤ 2 * Γ) (ht : |t| < Γ / 2 ∨ 4 * Γ < |t|) :
    1 / (1 + (t + γ) ^ 2) ≤ 4 / Γ ^ 2 ∧
      1 / (1 + (t + γ) ^ 2) ^ 2 ≤ (16 / Γ ^ 2) * (1 / (1 + t ^ 2)) := by
  have ht' : |-t| < Γ / 2 ∨ 4 * Γ < |-t| := by simpa only [abs_neg] using ht
  have h := inv_one_add_sq_remote_le hΓ hγ1 hγ2 ht'
  have heq : (-t - γ) ^ 2 = (t + γ) ^ 2 := by ring
  have htsq : (-t) ^ 2 = t ^ 2 := by ring
  rwa [heq, htsq] at h

/-- Integral of `1 / (1 + (t ∓ γ)²)` over any interval `[a, b]` is at most `π`. -/
theorem integral_Icc_inv_one_add_sq_sub_le_pi (a b t : ℝ) :
    (∫ γ in Icc a b, 1 / (1 + (t - γ) ^ 2)) ≤ Real.pi := by
  have heq : (fun γ : ℝ => 1 / (1 + (t - γ) ^ 2)) = fun γ : ℝ => (1 + (γ - t) ^ 2)⁻¹ := by
    funext γ; simp only [one_div]; congr 2; ring
  have hint : Integrable fun γ : ℝ => (1 + (γ - t) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_sub_right t
  rw [heq]
  calc (∫ γ in Icc a b, (1 + (γ - t) ^ 2)⁻¹)
      ≤ ∫ γ : ℝ, (1 + (γ - t) ^ 2)⁻¹ :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => by positivity)
    _ = ∫ u : ℝ, (1 + u ^ 2)⁻¹ :=
        integral_sub_right_eq_self (fun u : ℝ => (1 + u ^ 2)⁻¹) t
    _ = Real.pi := integral_univ_inv_one_add_sq

theorem integral_Icc_inv_one_add_sq_add_le_pi (a b t : ℝ) :
    (∫ γ in Icc a b, 1 / (1 + (t + γ) ^ 2)) ≤ Real.pi := by
  have heq : (fun γ : ℝ => 1 / (1 + (t + γ) ^ 2)) = fun γ : ℝ => 1 / (1 + ((-t) - γ) ^ 2) := by
    funext γ; congr 2; ring
  rw [heq]
  exact integral_Icc_inv_one_add_sq_sub_le_pi a b (-t)

private theorem lt_zero_or_gt_of_not_mem_Icc {t b : ℝ} (ht : ¬(0 ≤ t ∧ t ≤ b)) :
    t < 0 ∨ b < t := by
  rcases lt_or_ge t 0 with h | h
  · exact Or.inl h
  · exact Or.inr (lt_of_not_ge fun hb => ht ⟨h, hb⟩)

/-- **Two-Integration-by-Parts Strip Bound (`norm_integral_exp_strip_mul_le`):**
For any `ψ ∈ C²_c(ℝ)` supported in `[0, 2A]` (`0 ≤ A`) and any `w ∈ ℂ` with `0 ≤ w.re ≤ δ` or
`|w.re| ≤ δ` (`0 ≤ δ`),
`‖∫ t, ψ t * e^{w t}‖ ≤ e^{2A δ} * ((∫ |ψ|) + ∫ |ψ''|) / (1 + w.im²)`. -/
theorem norm_integral_exp_strip_mul_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hsupp : ∀ t : ℝ, t < 0 ∨ 2 * A < t → ψ t = 0)
    {w : ℂ} (hw : |w.re| ≤ δ) :
    ‖∫ t : ℝ, (ψ t : ℂ) * Complex.exp (w * (t : ℂ))‖ ≤
      Real.exp (2 * A * δ) * ((∫ t, |ψ t|) + ∫ t, |deriv (deriv ψ) t|) / (1 + w.im ^ 2) := by
  set g : ℝ → ℂ := fun t => (ψ t : ℂ)
  have hg : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp hψ
  have hgc : HasCompactSupport g := hψc.comp_left Complex.ofReal_zero
  set z : ℂ := -Complex.I * w
  have hiz : ∀ t : ℝ, Complex.I * z * (t : ℂ) = w * (t : ℂ) := fun t => by
    dsimp [z]; ring_nf; rw [Complex.I_sq]; ring
  have hft : (∫ t : ℝ, g t * Complex.exp (w * (t : ℂ))) = paperFT g z := by
    unfold paperFT
    exact integral_congr_ae (Eventually.of_forall fun t => by dsimp only; rw [hiz t])
  -- Bound `‖paperFT g z‖` on `[0, 2A]` directly so `e^{2A δ}` is sharp (rather than `e^{2A |t|}`)
  have h1 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) ψ from hψ)
  have h2 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv ψ) from h1.2.2)
  have hψ''_cont : Continuous (deriv (deriv ψ)) := h2.2.2.continuous
  have hsupp'' : ∀ t : ℝ, t < 0 ∨ 2 * A < t → deriv (deriv ψ) t = 0 := by
    intro t ht
    rcases ht with ht0 | htA
    · have heq : ψ =ᶠ[𝓝 t] 0 := Filter.eventually_of_mem (Iio_mem_nhds ht0) fun s hs => hsupp s (Or.inl hs)
      exact ((heq.deriv).deriv).eq_of_nhds.trans (by simp)
    · have heq : ψ =ᶠ[𝓝 t] 0 := Filter.eventually_of_mem (Ioi_mem_nhds htA) fun s hs => hsupp s (Or.inr hs)
      exact ((heq.deriv).deriv).eq_of_nhds.trans (by simp)
  have hexp_on_supp : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * A → ‖Complex.exp (Complex.I * z * (t : ℂ))‖ ≤ Real.exp (2 * A * δ) := by
    intro t ht0 ht2A
    rw [hiz t, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (w * (t : ℂ)).re = w.re * t := by simp [Complex.mul_re]
    rw [hre]
    calc w.re * t ≤ |w.re| * t := mul_le_mul_of_nonneg_right (le_abs_self _) ht0
      _ ≤ δ * (2 * A) := mul_le_mul hw ht2A ht0 hδ
      _ = 2 * A * δ := by ring
  have he0 : ‖paperFT g z‖ ≤ Real.exp (2 * A * δ) * ∫ t, |ψ t| := by
    unfold paperFT
    have hint : Integrable fun t : ℝ => |ψ t| := hψ.continuous.abs.integrable_of_hasCompactSupport hψc.abs
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases ht : 0 ≤ t ∧ t ≤ 2 * A
    · have := mul_le_mul_of_nonneg_left (hexp_on_supp t ht.1 ht.2) (abs_nonneg (ψ t))
      linarith
    · have h0 : ψ t = 0 := hsupp t (lt_zero_or_gt_of_not_mem_Icc ht)
      rw [h0]; simp
  have hg''_eq : deriv (deriv g) = fun t => ((deriv (deriv ψ) t : ℝ) : ℂ) := by
    have hd1 : deriv g = fun t => ((deriv ψ t : ℝ) : ℂ) := by
      funext t
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        (h1.1 t).hasDerivAt).hasDerivAt.deriv
    rw [hd1]
    funext t
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (h2.1 t).hasDerivAt).hasDerivAt.deriv
  have he2 : ‖paperFT (deriv (deriv g)) z‖ ≤ Real.exp (2 * A * δ) * ∫ t, |deriv (deriv ψ) t| := by
    unfold paperFT
    have hint : Integrable fun t : ℝ => |deriv (deriv ψ) t| :=
      hψ''_cont.abs.integrable_of_hasCompactSupport hψc.deriv.deriv.abs
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun t => ?_)
    rw [hg''_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases ht : 0 ≤ t ∧ t ≤ 2 * A
    · have := mul_le_mul_of_nonneg_left (hexp_on_supp t ht.1 ht.2) (abs_nonneg (deriv (deriv ψ) t))
      linarith
    · have h0 : deriv (deriv ψ) t = 0 := hsupp'' t (lt_zero_or_gt_of_not_mem_Icc ht)
      rw [h0]; simp
  rw [EvenSector.paperFT_deriv_deriv_of_compact hg hgc z, norm_mul, norm_neg, norm_pow] at he2
  have hzim : z.re = w.im := by simp [z, Complex.mul_re]
  have hz_sq : w.im ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← hzim, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  rw [hft, le_div_iff₀ (by positivity)]
  calc ‖paperFT g z‖ * (1 + w.im ^ 2)
      ≤ ‖paperFT g z‖ * (1 + ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = ‖paperFT g z‖ + ‖z‖ ^ 2 * ‖paperFT g z‖ := by ring
    _ ≤ Real.exp (2 * A * δ) * (∫ t, |ψ t|) +
          Real.exp (2 * A * δ) * ∫ t, |deriv (deriv ψ) t| := add_le_add he0 he2
    _ = Real.exp (2 * A * δ) * ((∫ t, |ψ t|) + ∫ t, |deriv (deriv ψ) t|) := by ring

/-! ## §4. Polynomial Power-Saving Decay of Cosine-Filtered `spectralDeficitSum` and `ccmPrimeDeficitIncoming` -/

/-- Norm of the `C²_c` test window entering the cosine-filtered prime-deficit bound. -/
def deficitWindowNorm (ψ : ℝ → ℝ) : ℝ :=
  (⨆ t : ℝ, |ψ t|) + (∫ t, |ψ t|) + ∫ t, |deriv (deriv ψ) t|

theorem deficitWindowNorm_nonneg {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    0 ≤ deficitWindowNorm ψ := by
  unfold deficitWindowNorm
  have hb : BddAbove (Set.range fun t : ℝ => |ψ t|) :=
    hψ.continuous.abs.bddAbove_range_of_hasCompactSupport hψc.abs
  have h0 : 0 ≤ ⨆ t : ℝ, |ψ t| := le_ciSup_of_le hb 0 (abs_nonneg _)
  have h1 : 0 ≤ ∫ t, |ψ t| := integral_nonneg fun _ => abs_nonneg _
  have h2 : 0 ≤ ∫ t, |deriv (deriv ψ) t| := integral_nonneg fun _ => abs_nonneg _
  linarith

/-- Folded real-part distance from the critical line: `foldedRe q - 1/2 = |Re ρ_q - 1/2|`. -/
theorem foldedRe_sub_half_eq_abs (q : XiZeroCopy) :
    foldedRe q - 1 / 2 = |(q.1 : ℂ).re - 1 / 2| := by
  unfold foldedRe
  rcases le_total (1 / 2) (q.1 : ℂ).re with h | h
  · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith)]
  · rw [max_eq_right (by linarith), abs_of_nonpos (by linarith)]; ring

private theorem integral_tsum_of_summable_integral_norm
    {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Countable ι] {μ : Measure α} {F : ι → α → E}
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i => ∫ x, ‖F i x‖ ∂μ) :
    ∫ x, ∑' i, F i x ∂μ = ∑' i, ∫ x, F i x ∂μ := by
  apply MeasureTheory.integral_tsum
  · exact fun i => (hF_int i).aestronglyMeasurable
  · have hi (i : ι) :
        (∫⁻ x, ‖F i x‖ₑ ∂μ) = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
      dsimp only [enorm]
      rw [lintegral_coe_eq_integral _ (hF_int i).norm, ENNReal.coe_nnreal_eq,
        coe_nnnorm, Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F i x))]
      simp only [coe_nnnorm]
    rw [funext hi]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2
      (NNReal.summable_coe.1 hF_sum.abs)

/-- Continuity of the cosine transform `γ ↦ ∫ t, g t * cos(γ t)` for continuous compactly supported `g`. -/
theorem continuous_cosine_pairing {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous fun γ : ℝ => ∫ t : ℝ, g t * Real.cos (γ * t) := by
  set h : ℝ → ℂ := fun t => (g t : ℂ)
  have hh_cont : Continuous h := Complex.continuous_ofReal.comp hg
  have hh_comp : HasCompactSupport h := hgc.comp_left Complex.ofReal_zero
  have hh1 : Integrable h := hh_cont.integrable_of_hasCompactSupport hh_comp
  have hre_eq : (fun γ : ℝ => ∫ t : ℝ, g t * Real.cos (γ * t)) = fun γ : ℝ => (paperFT h γ).re := by
    funext γ
    unfold paperFT
    have hint_c : Integrable fun t : ℝ => h t * Complex.exp (Complex.I * (γ : ℂ) * (t : ℂ)) :=
      (hh_cont.mul (by fun_prop)).integrable_of_hasCompactSupport hh_comp.mul_right
    have hre := Complex.reCLM.integral_comp_comm hint_c
    simp only [Complex.reCLM_apply] at hre
    rw [← hre]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only [Function.comp_apply, h]
    simp [Complex.mul_re, Complex.exp_re, Complex.mul_im]
  rw [hre_eq]
  have hfun : (fun γ : ℝ => (paperFT h γ).re) =
      fun γ => (FourierTransform.fourier h (γ / (-(2 * Real.pi)))).re := by
    funext γ; rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
  rw [hfun]
  exact Complex.continuous_re.comp
    ((GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hh1).comp
      (continuous_id.div_const _))

/-- Plancherel `L²` bound on any interval `[a, b]` for the cosine transform of a continuous
compactly supported profile `g : ℝ → ℝ` (requiring no `C²` smoothness on `g`). -/
theorem integral_Icc_sq_cosine_pairing_le {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (a b : ℝ) :
    (∫ γ in Icc a b, (∫ t : ℝ, g t * Real.cos (γ * t)) ^ 2) ≤
      2 * Real.pi * ∫ t : ℝ, g t ^ 2 := by
  set h : ℝ → ℂ := fun t => (g t : ℂ)
  have hh_cont : Continuous h := Complex.continuous_ofReal.comp hg
  have hh_comp : HasCompactSupport h := hgc.comp_left Complex.ofReal_zero
  have hh1 : Integrable h := hh_cont.integrable_of_hasCompactSupport hh_comp
  have hh2 : MemLp h 2 := by
    rw [memLp_two_iff_integrable_sq_norm hh_cont.aestronglyMeasurable]
    exact (hh_cont.norm.pow 2).integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))
  have hint_ft : Integrable fun γ : ℝ => ‖paperFT h γ‖ ^ 2 := by
    have hfun : (fun γ : ℝ => ‖paperFT h γ‖ ^ 2) =
        fun γ => (fun ξ : ℝ => ‖FourierTransform.fourier h ξ‖ ^ 2) (γ / (-(2 * Real.pi))) := by
      funext γ; rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
    rw [hfun]
    exact (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hh1 hh2).comp_div
      (by linarith [Real.pi_pos])
  have hre_eq : ∀ γ : ℝ, (∫ t : ℝ, g t * Real.cos (γ * t)) = (paperFT h γ).re := fun γ => by
    unfold paperFT
    have hint_c : Integrable fun t : ℝ => h t * Complex.exp (Complex.I * (γ : ℂ) * (t : ℂ)) :=
      (hh_cont.mul (by fun_prop)).integrable_of_hasCompactSupport hh_comp.mul_right
    have hre := Complex.reCLM.integral_comp_comm hint_c
    simp only [Complex.reCLM_apply] at hre
    rw [← hre]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only [Function.comp_apply, h]
    simp [Complex.mul_re, Complex.exp_re, Complex.mul_im]
  have hpt : ∀ γ : ℝ, (∫ t : ℝ, g t * Real.cos (γ * t)) ^ 2 ≤ ‖paperFT h γ‖ ^ 2 := fun γ => by
    rw [hre_eq γ]
    have habs := Complex.abs_re_le_norm (paperFT h γ)
    nlinarith [sq_abs (paperFT h γ).re, abs_nonneg (paperFT h γ).re, norm_nonneg (paperFT h γ)]
  have hint_lhs : IntegrableOn (fun γ : ℝ => (∫ t : ℝ, g t * Real.cos (γ * t)) ^ 2) (Icc a b) :=
    ((continuous_cosine_pairing hg hgc).pow 2).integrableOn_Icc
  calc (∫ γ in Icc a b, (∫ t : ℝ, g t * Real.cos (γ * t)) ^ 2)
      ≤ ∫ γ in Icc a b, ‖paperFT h γ‖ ^ 2 :=
        setIntegral_mono_on hint_lhs hint_ft.integrableOn measurableSet_Icc fun γ _ => hpt γ
    _ ≤ ∫ γ : ℝ, ‖paperFT h γ‖ ^ 2 :=
        setIntegral_le_integral hint_ft (Eventually.of_forall fun _ => sq_nonneg _)
    _ = 2 * Real.pi * ∫ t : ℝ, ‖h t‖ ^ 2 :=
        RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hh1 hh2
    _ = 2 * Real.pi * ∫ t : ℝ, g t ^ 2 := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp [h, sq_abs]

/-- `O(Γ^{-1/2})` frequency-average decay of the cosine transform of a continuous compactly
supported profile `g` whose `L²` norm is bounded by `K * M²`. -/
theorem frequencyAverage_abs_cosine_pairing_le {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {Γ M K : ℝ} (hΓ : 1 ≤ Γ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hg0 : M = 0 → ∀ t : ℝ, g t = 0)
    (hL2 : (∫ t : ℝ, g t ^ 2) ≤ K * M ^ 2) :
    (1 / Γ) * (∫ γ in Icc Γ (2 * Γ), |∫ t : ℝ, g t * Real.cos (γ * t)|) ≤
      (1 / 2 + Real.pi * K) * M * Γ ^ (-(1 / 2 : ℝ)) := by
  have hΓ0 : 0 < Γ := by linarith
  rcases eq_or_lt_of_le hM with rfl | hM_pos
  · have hzero : ∀ γ : ℝ, |∫ t : ℝ, g t * Real.cos (γ * t)| = 0 := fun γ => by
      simp [hg0 rfl]
    simp [hzero]
  · set Y : ℝ → ℝ := fun γ => ∫ t : ℝ, g t * Real.cos (γ * t)
    have hY_cont : Continuous Y := continuous_cosine_pairing hg hgc
    set c : ℝ := M * Γ ^ (-(1 / 2 : ℝ))
    have hc : 0 < c := mul_pos hM_pos (Real.rpow_pos_of_pos hΓ0 _)
    have hamgm : ∀ γ : ℝ, |Y γ| ≤ c / 2 + (Y γ) ^ 2 / (2 * c) := fun γ => by
      have h1 : 2 * c * |Y γ| ≤ c ^ 2 + (Y γ) ^ 2 := by
        nlinarith [sq_nonneg (|Y γ| - c), sq_abs (Y γ)]
      calc |Y γ| = (2 * c * |Y γ|) / (2 * c) := by field_simp [hc.ne']
        _ ≤ (c ^ 2 + (Y γ) ^ 2) / (2 * c) :=
            div_le_div_of_nonneg_right h1 (by positivity)
        _ = c / 2 + (Y γ) ^ 2 / (2 * c) := by field_simp [hc.ne']
    have hint1 : IntegrableOn (fun γ : ℝ => |Y γ|) (Icc Γ (2 * Γ)) :=
      hY_cont.abs.integrableOn_Icc
    have hint_sq : IntegrableOn (fun γ : ℝ => (Y γ) ^ 2 / (2 * c)) (Icc Γ (2 * Γ)) :=
      (hY_cont.mul hY_cont).integrableOn_Icc.div_const (2 * c) |>.congr_fun
        (fun γ _ => by simp [sq]) measurableSet_Icc
    have hint2 : IntegrableOn (fun γ : ℝ => c / 2 + (Y γ) ^ 2 / (2 * c)) (Icc Γ (2 * Γ)) :=
      continuous_const.integrableOn_Icc.add hint_sq
    have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Icc fun γ _ => hamgm γ
    rw [integral_add continuous_const.integrableOn_Icc hint_sq,
      setIntegral_const, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * Γ - Γ),
      show 2 * Γ - Γ = Γ by ring, smul_eq_mul, integral_div] at hmono
    have hplanch : (∫ γ in Icc Γ (2 * Γ), (Y γ) ^ 2) ≤ 2 * Real.pi * (K * M ^ 2) :=
      (integral_Icc_sq_cosine_pairing_le hg hgc Γ (2 * Γ)).trans
        (mul_le_mul_of_nonneg_left hL2 (by positivity))
    have hdiv_planch : (∫ γ in Icc Γ (2 * Γ), (Y γ) ^ 2) / (2 * c) ≤
        Real.pi * K * M ^ 2 / c := by
      calc (∫ γ in Icc Γ (2 * Γ), (Y γ) ^ 2) / (2 * c)
          ≤ (2 * Real.pi * (K * M ^ 2)) / (2 * c) :=
            div_le_div_of_nonneg_right hplanch (by positivity)
        _ = Real.pi * K * M ^ 2 / c := by field_simp
    have htot := (mul_le_mul_of_nonneg_left (hmono.trans (add_le_add_left hdiv_planch _))
      (by positivity : 0 ≤ 1 / Γ))
    have hsimp : (1 / Γ) * (Γ * (c / 2) + Real.pi * K * M ^ 2 / c) =
        (1 / 2 + Real.pi * K) * M * Γ ^ (-(1 / 2 : ℝ)) := by
      dsimp [c]
      have hr : Γ * Γ ^ (-(1 / 2 : ℝ)) * Γ ^ (-(1 / 2 : ℝ)) = 1 := by
        have h1 : Γ ^ (-(1 / 2 : ℝ)) * Γ ^ (-(1 / 2 : ℝ)) = Γ ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hΓ0]; norm_num
        rw [mul_assoc, h1, Real.rpow_neg_one, mul_inv_cancel₀ hΓ0.ne']
      have hne1 : Γ ≠ 0 := hΓ0.ne'
      have hne2 : M ≠ 0 := hM_pos.ne'
      have hne3 : Γ ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hΓ0 _).ne'
      field_simp
      linear_combination Real.pi * K * M * (1 - hr)
    exact htot.trans_eq hsimp

/-- **Polynomial Power-Saving Decay of Cosine-Filtered `spectralDeficitSum`
(`exists_frequencyAverage_abs_cosineFiltered_spectralDeficitSum_le`):**
For every aperture slope `0 ≤ α < 2/3` (strictly exceeding Huxley `5/12` and Guth–Maynard `13/30`),
there exist `C ≥ 0` and `Γ₀ ≥ 8` such that for all `Γ ≥ Γ₀`, all `0 ≤ A ≤ α log Γ`, and every
`ψ ∈ C²_c(ℝ)` supported in `[0, 2A]`,
`(1 / Γ) ∫_Γ^{2Γ} |∫_0^{2A} Re(spectralDeficitSum t) * ψ t * cos(γ t) dt| dγ ≤ C * Γ^{-4/3} * deficitWindowNorm ψ`. -/
theorem exists_frequencyAverage_abs_cosineFiltered_spectralDeficitSum_le
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Γ₀ : ℝ, 8 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ A : ℝ, 0 ≤ A → A ≤ α * Real.log Γ →
        ∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
          (∀ t : ℝ, t < 0 ∨ 2 * A < t → ψ t = 0) →
          (1 / Γ) * (∫ γ in Icc Γ (2 * Γ),
            |∫ t : ℝ, (spectralDeficitSum t).re * ψ t * Real.cos (γ * t)|) ≤
            C * Γ ^ (-(4 / 3 : ℝ)) * deficitWindowNorm ψ := by
  obtain ⟨C_loc, hC_loc, Γ₀, hΓ₀, hloc_bound⟩ :=
    exists_sum_exp_foldedRe_threeShells_le_subpower hα0 hα (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨4 * Real.pi * C_loc + 4 * reciprocalSquareWeightTotal,
    by positivity [reciprocalSquareWeightTotal_nonneg], Γ₀, hΓ₀,
    fun Γ hΓ A hA0 hA ψ hψ hψc hsupp => ?_⟩
  have hΓ8 : 8 ≤ Γ := hΓ₀.trans hΓ
  have hΓ1 : 1 ≤ Γ := by linarith
  have hΓ0 : 0 < Γ := by linarith
  set W₁ : ℝ := (∫ t, |ψ t|) + ∫ t, |deriv (deriv ψ) t|
  have hW₁_nonneg : 0 ≤ W₁ :=
    add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have hW₁_le : W₁ ≤ deficitWindowNorm ψ := by
    unfold deficitWindowNorm W₁
    have hb : BddAbove (Set.range fun t : ℝ => |ψ t|) :=
      hψ.continuous.abs.bddAbove_range_of_hasCompactSupport hψc.abs
    have h0 : 0 ≤ ⨆ t : ℝ, |ψ t| := le_ciSup_of_le hb 0 (abs_nonneg _)
    linarith
  -- Majorant per zero copy `q` and frequency `γ`
  set bq : XiZeroCopy → ℝ → ℝ := fun q γ =>
    (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)) * W₁ *
      ((1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) + 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) / 2)
  have hbq_nonneg : ∀ q γ, 0 ≤ bq q γ := fun q γ => by
    dsimp [bq]; positivity
  have hexp_le_A : ∀ q : XiZeroCopy, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤ Real.exp A :=
    fun q => Real.exp_le_exp.mpr (by
      have := (foldedRe_lt_one q).le
      nlinarith [half_le_foldedRe q])
  have hbq_dom : ∀ q γ, bq q γ ≤ (Real.exp A * W₁) * (1 / ‖(q.1 : ℂ)‖ ^ 2) := fun q γ => by
    dsimp [bq]
    have hl : (1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) + 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) / 2 ≤ 1 := by
      have h1 : 1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) ≤ 1 :=
        div_le_one_of_le₀ (by linarith [sq_nonneg ((q.1 : ℂ).im + γ)]) (by positivity)
      have h2 : 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2) ≤ 1 :=
        div_le_one_of_le₀ (by linarith [sq_nonneg ((q.1 : ℂ).im - γ)]) (by positivity)
      linarith
    calc (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)) * W₁ *
          ((1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) + 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) / 2)
        ≤ (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp A * W₁ * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hexp_le_A q) (by positivity)) hW₁_nonneg)
            hl (by positivity) (by positivity)
      _ = (Real.exp A * W₁) * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by ring
  have hbq_sum : ∀ γ, Summable (fun q => bq q γ) := fun γ =>
    Summable.of_nonneg_of_le (fun q => hbq_nonneg q γ) (fun q => hbq_dom q γ)
      (summable_inv_norm_sq_xiZeroCopy.mul_left _)
  -- Pointwise bound on `|∫ t, (spectralDeficitSum t).re * ψ t * cos(γ t)|` for every `γ : ℝ`
  have hpt_γ : ∀ γ : ℝ,
      |∫ t : ℝ, (spectralDeficitSum t).re * ψ t * Real.cos (γ * t)| ≤ ∑' q, bq q γ := by
    intro γ
    set w : ℝ → ℝ := fun t => ψ t * Real.cos (γ * t)
    have hw_cont : Continuous w := hψ.continuous.mul (by fun_prop)
    have hw_comp : HasCompactSupport w := hψc.mul_right
    have hint_prod : Integrable fun t : ℝ => spectralDeficitSum t * (w t : ℂ) :=
      (continuous_spectralDeficitSum.mul
        (Complex.continuous_ofReal.comp hw_cont)).integrable_of_hasCompactSupport
          ((hw_comp.comp_left Complex.ofReal_zero).mul_left)
    have hre_pull : (∫ t : ℝ, (spectralDeficitSum t).re * ψ t * Real.cos (γ * t)) =
        (∫ t : ℝ, spectralDeficitSum t * (w t : ℂ)).re := by
      have hre := Complex.reCLM.integral_comp_comm hint_prod
      simp only [Complex.reCLM_apply] at hre
      rw [← hre]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp only [Function.comp_apply]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      dsimp only [w]
      ring
    rw [hre_pull]
    refine (Complex.abs_re_le_norm _).trans ?_
    set fq : XiZeroCopy → ℝ → ℂ := fun q t =>
      (1 / (q.1 : ℂ) ^ 2) * Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2)) * (w t : ℂ)
    have hfq_int : ∀ q, Integrable (fq q) := fun q =>
      ((continuous_const.mul (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const))).mul
          (Complex.continuous_ofReal.comp hw_cont)).integrable_of_hasCompactSupport
            ((hw_comp.comp_left Complex.ofReal_zero).mul_left)
    have hfq_norm_le : ∀ q t, ‖fq q t‖ ≤ (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp A * |ψ t| := fun q t => by
      dsimp [fq, w]
      rw [norm_mul, norm_mul, norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_mul]
      by_cases ht : 0 ≤ t ∧ t ≤ 2 * A
      · have hexp : ‖Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ ≤ Real.exp A := by
          rw [Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          have hre : ((t : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = t * ((q.1 : ℂ).re - 1 / 2) := by
            simp [Complex.mul_re]
          rw [hre]
          have hb : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 :=
            abs_le.mpr ⟨by linarith [xiZeroCopy_re_pos q], by linarith [xiZeroCopy_re_lt_one q]⟩
          calc t * ((q.1 : ℂ).re - 1 / 2) ≤ t * |(q.1 : ℂ).re - 1 / 2| :=
                mul_le_mul_of_nonneg_left (le_abs_self _) ht.1
            _ ≤ (2 * A) * (1 / 2) := mul_le_mul ht.2 hb (abs_nonneg _) (by linarith)
            _ = A := by ring
        have hcos : |Real.cos (γ * t)| ≤ 1 := Real.abs_cos_le_one _
        calc (1 / ‖(q.1 : ℂ)‖ ^ 2) * ‖Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ *
              (|ψ t| * |Real.cos (γ * t)|)
            ≤ (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp A * (|ψ t| * 1) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hexp (by positivity))
                (mul_le_mul_of_nonneg_left hcos (abs_nonneg _)) (by positivity) (by positivity)
          _ = (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp A * |ψ t| := by ring
      · have h0 : ψ t = 0 := hsupp t (lt_zero_or_gt_of_not_mem_Icc ht)
        rw [h0]; simp
    have hint_absψ : Integrable fun t : ℝ => |ψ t| :=
      hψ.continuous.abs.integrable_of_hasCompactSupport hψc.abs
    have hfq_sum_norm : Summable fun q => ∫ t : ℝ, ‖fq q t‖ := by
      refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun t => norm_nonneg _)
        (fun q => ?_) (summable_inv_norm_sq_xiZeroCopy.mul_right (Real.exp A * ∫ t, |ψ t|))
      calc (∫ t : ℝ, ‖fq q t‖)
          ≤ ∫ t : ℝ, (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp A * |ψ t| :=
            integral_mono (hfq_int q).norm (hint_absψ.const_mul _) (hfq_norm_le q)
        _ = (1 / ‖(q.1 : ℂ)‖ ^ 2) * (Real.exp A * ∫ t, |ψ t|) := by
            rw [integral_const_mul, mul_assoc]
    have hexpand : (∫ t : ℝ, spectralDeficitSum t * (w t : ℂ)) = ∑' q, ∫ t : ℝ, fq q t := by
      have htsum_mul : ∀ t : ℝ, spectralDeficitSum t * (w t : ℂ) = ∑' q, fq q t := fun t => by
        unfold spectralDeficitSum fq
        exact (tsum_mul_right).symm
      simp_rw [htsum_mul]
      exact integral_tsum_of_summable_integral_norm hfq_int hfq_sum_norm
    have hfq_term_le : ∀ q, ‖∫ t : ℝ, fq q t‖ ≤ bq q γ := fun q => by
      set wp : ℂ := ((q.1 : ℂ) - 1 / 2) + Complex.I * (γ : ℂ)
      set wm : ℂ := ((q.1 : ℂ) - 1 / 2) - Complex.I * (γ : ℂ)
      have hint_p : Integrable fun t : ℝ => (ψ t : ℂ) * Complex.exp (wp * (t : ℂ)) :=
        ((Complex.continuous_ofReal.comp hψ.continuous).mul (by fun_prop)).integrable_of_hasCompactSupport
          ((hψc.comp_left Complex.ofReal_zero).mul_right)
      have hint_m : Integrable fun t : ℝ => (ψ t : ℂ) * Complex.exp (wm * (t : ℂ)) :=
        ((Complex.continuous_ofReal.comp hψ.continuous).mul (by fun_prop)).integrable_of_hasCompactSupport
          ((hψc.comp_left Complex.ofReal_zero).mul_right)
      have hsplit_q : (∫ t : ℝ, fq q t) =
          (1 / (2 * (q.1 : ℂ) ^ 2)) *
            ((∫ t : ℝ, (ψ t : ℂ) * Complex.exp (wp * (t : ℂ))) +
              ∫ t : ℝ, (ψ t : ℂ) * Complex.exp (wm * (t : ℂ))) := by
        rw [← integral_add hint_p hint_m, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        dsimp [fq, w]
        rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
        have hp : (t : ℂ) * ((q.1 : ℂ) - 1 / 2) + ((γ * t : ℝ) : ℂ) * Complex.I = wp * (t : ℂ) := by
          dsimp [wp]; push_cast; ring
        have hm : (t : ℂ) * ((q.1 : ℂ) - 1 / 2) + -(((γ * t : ℝ) : ℂ) * Complex.I) = wm * (t : ℂ) := by
          dsimp [wm]; push_cast; ring
        rw [← hp, ← hm, Complex.exp_add, Complex.exp_add]
        ring
      have hδq : 0 ≤ foldedRe q - 1 / 2 := sub_nonneg.mpr (half_le_foldedRe q)
      have hbp := norm_integral_exp_strip_mul_le hψ hψc hA0 hδq hsupp (w := wp)
        (by rw [foldedRe_sub_half_eq_abs]; simp [wp]; norm_num)
      have hbm := norm_integral_exp_strip_mul_le hψ hψc hA0 hδq hsupp (w := wm)
        (by rw [foldedRe_sub_half_eq_abs]; simp [wm]; norm_num)
      have him_p : wp.im = (q.1 : ℂ).im + γ := by simp [wp]
      have him_m : wm.im = (q.1 : ℂ).im - γ := by simp [wm]
      rw [him_p] at hbp
      rw [him_m] at hbm
      rw [hsplit_q, norm_mul, norm_div, norm_one, norm_mul, Complex.norm_ofNat, norm_pow]
      have htri := (norm_add_le _ _).trans (add_le_add hbp hbm)
      calc (1 / (2 * ‖(q.1 : ℂ)‖ ^ 2)) *
            ‖(∫ t : ℝ, (ψ t : ℂ) * Complex.exp (wp * (t : ℂ))) +
              ∫ t : ℝ, (ψ t : ℂ) * Complex.exp (wm * (t : ℂ))‖
          ≤ (1 / (2 * ‖(q.1 : ℂ)‖ ^ 2)) *
              (Real.exp (2 * A * (foldedRe q - 1 / 2)) * W₁ / (1 + ((q.1 : ℂ).im + γ) ^ 2) +
                Real.exp (2 * A * (foldedRe q - 1 / 2)) * W₁ / (1 + ((q.1 : ℂ).im - γ) ^ 2)) :=
            mul_le_mul_of_nonneg_left htri (by positivity)
        _ = bq q γ := by dsimp [bq, W₁]; ring
    have hfq_sum_term : Summable fun q => ‖∫ t : ℝ, fq q t‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hfq_term_le (hbq_sum γ)
    rw [hexpand]
    exact (norm_tsum_le_tsum_norm hfq_sum_term).trans
      (hfq_sum_term.tsum_le_tsum hfq_term_le (hbq_sum γ))
  -- Integrate `hpt_γ` over `γ ∈ Icc Γ (2 * Γ)` and exchange `∫` with `∑'`
  have hint_lhs : IntegrableOn
      (fun γ : ℝ => |∫ t : ℝ, (spectralDeficitSum t).re * ψ t * Real.cos (γ * t)|)
      (Icc Γ (2 * Γ)) :=
    (continuous_cosine_pairing
      ((Complex.continuous_re.comp continuous_spectralDeficitSum).mul hψ.continuous)
      hψc.mul_left).abs.integrableOn_Icc
  have hbq_cont : ∀ q, Continuous (bq q) := fun q => by
    dsimp [bq]
    refine continuous_const.mul (( ?_ ).div_const 2)
    exact (continuous_const.div (by fun_prop) (fun _ => by positivity)).add
      (continuous_const.div (by fun_prop) (fun _ => by positivity))
  have htsum_cont : Continuous (fun γ : ℝ => ∑' q, bq q γ) :=
    continuous_tsum hbq_cont (summable_inv_norm_sq_xiZeroCopy.mul_left (Real.exp A * W₁))
      fun q γ => by rw [Real.norm_of_nonneg (hbq_nonneg q γ)]; exact hbq_dom q γ
  have hmono_int := setIntegral_mono_on hint_lhs htsum_cont.integrableOn_Icc
    measurableSet_Icc fun γ _ => hpt_γ γ
  have hbq_int_norm_sum : Summable fun q => ∫ γ in Icc Γ (2 * Γ), ‖bq q γ‖ := by
    refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _)
      (fun q => ?_)
      (summable_inv_norm_sq_xiZeroCopy.mul_left (Γ * (Real.exp A * W₁)))
    calc (∫ γ in Icc Γ (2 * Γ), ‖bq q γ‖)
        ≤ ∫ _γ in Icc Γ (2 * Γ), (Real.exp A * W₁) * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
          refine setIntegral_mono_on (hbq_cont q).norm.integrableOn_Icc
            continuous_const.integrableOn_Icc measurableSet_Icc fun γ _ => ?_
          rw [Real.norm_of_nonneg (hbq_nonneg q γ)]
          exact hbq_dom q γ
      _ = Γ * (Real.exp A * W₁) * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
          rw [setIntegral_const, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * Γ - Γ),
            show 2 * Γ - Γ = Γ by ring, smul_eq_mul]
          ring
  have hswap_γ : (∫ γ in Icc Γ (2 * Γ), ∑' q, bq q γ) =
      ∑' q, ∫ γ in Icc Γ (2 * Γ), bq q γ :=
    integral_tsum_of_summable_integral_norm (fun q => (hbq_cont q).integrableOn_Icc)
      hbq_int_norm_sum
  -- Split `XiZeroCopy` into local shell `Γ/2 ≤ |Im ρ_q| ≤ 4Γ` and remote complement
  classical
  have hS_fin : ({q : XiZeroCopy | Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ}).Finite :=
    (finite_xiOrdinateWindow (4 * Γ) 0).subset fun q hq => by
      rw [mem_xiOrdinateWindow_iff, sub_zero]; exact hq.2
  set G_loc : Finset XiZeroCopy := hS_fin.toFinset
  have hmem_Gloc : ∀ q : XiZeroCopy,
      q ∈ G_loc ↔ Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ :=
    fun q => hS_fin.mem_toFinset
  set u_loc : XiZeroCopy → ℝ := fun q =>
    if q ∈ G_loc then (4 / Γ ^ 2) * Real.pi * W₁ * Real.exp (2 * A * (foldedRe q - 1 / 2)) else 0
  set u_rem : XiZeroCopy → ℝ := fun q =>
    (4 / Γ) * (Γ ^ α) * W₁ * (1 / ‖(q.1 : ℂ)‖ ^ 2)
  have hq_bound : ∀ q : XiZeroCopy,
      (∫ γ in Icc Γ (2 * Γ), bq q γ) ≤ u_loc q + u_rem q := fun q => by
    by_cases hq : q ∈ G_loc
    · have hq_shell := (hmem_Gloc q).mp hq
      have hnorm_sq : Γ ^ 2 / 4 ≤ ‖(q.1 : ℂ)‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        have him : (Γ / 2) ^ 2 ≤ (q.1 : ℂ).im ^ 2 := by
          have := pow_le_pow_left₀ (by positivity) hq_shell.1 2
          rwa [sq_abs] at this
        nlinarith [sq_nonneg (q.1 : ℂ).re]
      have hinv_norm : 1 / ‖(q.1 : ℂ)‖ ^ 2 ≤ 4 / Γ ^ 2 := by
        have hpos_q : 0 < ‖(q.1 : ℂ)‖ ^ 2 := lt_of_lt_of_le (by positivity) hnorm_sq
        rw [div_le_div_iff₀ hpos_q (by positivity)]
        linarith
      have hint_lor : (∫ γ in Icc Γ (2 * Γ),
          (1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) + 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) / 2) ≤ Real.pi := by
        have hi1 : IntegrableOn (fun γ : ℝ => 1 / (1 + ((q.1 : ℂ).im + γ) ^ 2)) (Icc Γ (2 * Γ)) :=
          (continuous_const.div (by fun_prop) (fun _ => by positivity)).integrableOn_Icc
        have hi2 : IntegrableOn (fun γ : ℝ => 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) (Icc Γ (2 * Γ)) :=
          (continuous_const.div (by fun_prop) (fun _ => by positivity)).integrableOn_Icc
        rw [integral_div, integral_add hi1 hi2]
        linarith [integral_Icc_inv_one_add_sq_add_le_pi Γ (2 * Γ) (q.1 : ℂ).im,
          integral_Icc_inv_one_add_sq_sub_le_pi Γ (2 * Γ) (q.1 : ℂ).im]
      have hbq_eq : (∫ γ in Icc Γ (2 * Γ), bq q γ) =
          (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)) * W₁ *
            ∫ γ in Icc Γ (2 * Γ),
              (1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) + 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) / 2 := by
        dsimp [bq]
        exact integral_const_mul _ _
      have hu_rem_0 : 0 ≤ u_rem q := by dsimp [u_rem]; positivity
      dsimp [u_loc]
      rw [if_pos hq, hbq_eq]
      have hprod : (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)) * W₁ *
            (∫ γ in Icc Γ (2 * Γ),
              (1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) + 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) / 2) ≤
          (4 / Γ ^ 2) * Real.pi * W₁ * Real.exp (2 * A * (foldedRe q - 1 / 2)) := by
        calc (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)) * W₁ *
              (∫ γ in Icc Γ (2 * Γ),
                (1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) + 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) / 2)
            ≤ (4 / Γ ^ 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)) * W₁ * Real.pi := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hinv_norm (Real.exp_pos _).le) hW₁_nonneg)
                hint_lor (integral_nonneg fun _ => by positivity) (by positivity)
          _ = (4 / Γ ^ 2) * Real.pi * W₁ * Real.exp (2 * A * (foldedRe q - 1 / 2)) := by ring
      linarith
    · have hq_rem : |(q.1 : ℂ).im| < Γ / 2 ∨ 4 * Γ < |(q.1 : ℂ).im| := by
        rw [hmem_Gloc, not_and_or] at hq
        rcases hq with h1 | h2
        · exact Or.inl (not_le.mp h1)
        · exact Or.inr (not_le.mp h2)
      have hexpA_Γ : Real.exp A ≤ Γ ^ α := by
        calc Real.exp A ≤ Real.exp (α * Real.log Γ) := Real.exp_le_exp.mpr hA
          _ = Γ ^ α := by rw [Real.rpow_def_of_pos hΓ0, mul_comm]
      have hrem_pt : ∀ γ ∈ Icc Γ (2 * Γ),
          bq q γ ≤ (4 / Γ ^ 2) * (Γ ^ α) * W₁ * (1 / ‖(q.1 : ℂ)‖ ^ 2) := fun γ hγ => by
        have hsub := (inv_one_add_sq_remote_le hΓ1 hγ.1 hγ.2 hq_rem).1
        have hadd := (inv_one_add_sq_remote_add_le hΓ1 hγ.1 hγ.2 hq_rem).1
        have hlor : (1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) + 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) / 2 ≤
            4 / Γ ^ 2 := by linarith
        dsimp [bq]
        calc (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)) * W₁ *
              ((1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) + 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) / 2)
            ≤ (1 / ‖(q.1 : ℂ)‖ ^ 2) * (Γ ^ α) * W₁ * (4 / Γ ^ 2) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left ((hexp_le_A q).trans hexpA_Γ) (by positivity))
                hW₁_nonneg) hlor (by positivity) (by positivity)
          _ = (4 / Γ ^ 2) * (Γ ^ α) * W₁ * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by ring
      have hint_rem : (∫ γ in Icc Γ (2 * Γ), bq q γ) ≤ u_rem q := by
        calc (∫ γ in Icc Γ (2 * Γ), bq q γ)
            ≤ ∫ _γ in Icc Γ (2 * Γ), (4 / Γ ^ 2) * (Γ ^ α) * W₁ * (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
              setIntegral_mono_on (hbq_cont q).integrableOn_Icc
                continuous_const.integrableOn_Icc measurableSet_Icc hrem_pt
          _ = Γ * ((4 / Γ ^ 2) * (Γ ^ α) * W₁ * (1 / ‖(q.1 : ℂ)‖ ^ 2)) := by
              rw [setIntegral_const, Measure.real, Real.volume_Icc,
                ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * Γ - Γ),
                show 2 * Γ - Γ = Γ by ring, smul_eq_mul]
          _ = u_rem q := by dsimp [u_rem]; field_simp
      dsimp [u_loc]
      rw [if_neg hq, zero_add]
      exact hint_rem
  have hu_loc_sum : Summable u_loc :=
    summable_of_ne_finset_zero (s := G_loc) fun q hq => if_neg hq
  have hu_rem_sum : Summable u_rem :=
    summable_inv_norm_sq_xiZeroCopy.mul_left ((4 / Γ) * (Γ ^ α) * W₁)
  have hbq_int_sum : Summable fun q => ∫ γ in Icc Γ (2 * Γ), bq q γ :=
    Summable.of_nonneg_of_le (fun q => integral_nonneg fun γ => hbq_nonneg q γ)
      hq_bound (hu_loc_sum.add hu_rem_sum)
  have htsum_le : (∑' q, ∫ γ in Icc Γ (2 * Γ), bq q γ) ≤ (∑' q, u_loc q) + ∑' q, u_rem q :=
    (hbq_int_sum.tsum_le_tsum hq_bound (hu_loc_sum.add hu_rem_sum)).trans_eq
      (hu_loc_sum.tsum_add hu_rem_sum)
  have htsum_loc_eq : (∑' q, u_loc q) =
      (4 / Γ ^ 2) * Real.pi * W₁ * ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)) := by
    rw [tsum_eq_sum (s := G_loc) (fun q hq => if_neg hq), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    dsimp [u_loc]; rw [if_pos hq]
  have htsum_rem_eq : (∑' q, u_rem q) =
      (4 / Γ) * (Γ ^ α) * W₁ * reciprocalSquareWeightTotal := by
    unfold reciprocalSquareWeightTotal
    dsimp only [u_rem]
    exact tsum_mul_left
  -- Bound the local shell sum via `hloc_bound`
  have hGloc_bound : (1 / Γ) * (∑' q, u_loc q) ≤
      4 * Real.pi * C_loc * Γ ^ (-(4 / 3 : ℝ)) * W₁ := by
    have hshell := hloc_bound Γ hΓ A hA0 hA G_loc fun q hq => (hmem_Gloc q).mp hq
    rw [htsum_loc_eq]
    have h1 : (1 / Γ) * ((4 / Γ ^ 2) * Real.pi * W₁ *
        ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2))) =
        4 * Real.pi * W₁ * (1 / Γ ^ 2) *
          ((1 / Γ) * ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2))) := by ring
    rw [h1]
    have h2 : 4 * Real.pi * W₁ * (1 / Γ ^ 2) *
          ((1 / Γ) * ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2))) ≤
        4 * Real.pi * W₁ * (1 / Γ ^ 2) * (C_loc * Γ ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hshell (by positivity)
    have hrpow : (1 / Γ ^ 2) * Γ ^ (1 / 2 : ℝ) = Γ ^ (-(3 / 2 : ℝ)) := by
      have hsq : (1 / Γ ^ 2 : ℝ) = Γ ^ (-2 : ℝ) := by
        rw [one_div, ← Real.rpow_natCast Γ 2, ← Real.rpow_neg hΓ0.le]; norm_num
      rw [hsq, ← Real.rpow_add hΓ0]; norm_num
    have h32_43 : Γ ^ (-(3 / 2 : ℝ)) ≤ Γ ^ (-(4 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num)
    calc 4 * Real.pi * W₁ * (1 / Γ ^ 2) *
          ((1 / Γ) * ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)))
        ≤ 4 * Real.pi * W₁ * (1 / Γ ^ 2) * (C_loc * Γ ^ (1 / 2 : ℝ)) := h2
      _ = 4 * Real.pi * C_loc * ((1 / Γ ^ 2) * Γ ^ (1 / 2 : ℝ)) * W₁ := by ring
      _ = 4 * Real.pi * C_loc * Γ ^ (-(3 / 2 : ℝ)) * W₁ := by rw [hrpow]
      _ ≤ 4 * Real.pi * C_loc * Γ ^ (-(4 / 3 : ℝ)) * W₁ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h32_43 (by positivity)) hW₁_nonneg
  -- Bound the remote sum
  have hrem_bound : (1 / Γ) * (∑' q, u_rem q) ≤
      4 * reciprocalSquareWeightTotal * Γ ^ (-(4 / 3 : ℝ)) * W₁ := by
    rw [htsum_rem_eq]
    have hrpow : (1 / Γ) * (4 / Γ) * Γ ^ α = 4 * Γ ^ (α - 2) := by
      have h1 : (1 / Γ) * (4 / Γ) = 4 * Γ ^ (-2 : ℝ) := by
        have hsq : (Γ ^ 2)⁻¹ = Γ ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast Γ 2, ← Real.rpow_neg hΓ0.le]; norm_num
        calc (1 / Γ) * (4 / Γ) = 4 * (Γ ^ 2)⁻¹ := by ring
          _ = 4 * Γ ^ (-2 : ℝ) := by rw [hsq]
      rw [h1, mul_assoc, ← Real.rpow_add hΓ0]
      congr 2; ring
    have hexp_le : Γ ^ (α - 2) ≤ Γ ^ (-(4 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hΓ1 (by linarith)
    calc (1 / Γ) * ((4 / Γ) * Γ ^ α * W₁ * reciprocalSquareWeightTotal)
        = reciprocalSquareWeightTotal * ((1 / Γ) * (4 / Γ) * Γ ^ α) * W₁ := by ring
      _ = 4 * reciprocalSquareWeightTotal * Γ ^ (α - 2) * W₁ := by rw [hrpow]; ring
      _ ≤ 4 * reciprocalSquareWeightTotal * Γ ^ (-(4 / 3 : ℝ)) * W₁ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp_le
              (by positivity [reciprocalSquareWeightTotal_nonneg])) hW₁_nonneg
  calc (1 / Γ) * (∫ γ in Icc Γ (2 * Γ),
        |∫ t : ℝ, (spectralDeficitSum t).re * ψ t * Real.cos (γ * t)|)
      ≤ (1 / Γ) * ((∑' q, u_loc q) + ∑' q, u_rem q) :=
        mul_le_mul_of_nonneg_left ((hmono_int.trans_eq hswap_γ).trans htsum_le) (by positivity)
    _ = (1 / Γ) * (∑' q, u_loc q) + (1 / Γ) * ∑' q, u_rem q := by ring
    _ ≤ 4 * Real.pi * C_loc * Γ ^ (-(4 / 3 : ℝ)) * W₁ +
          4 * reciprocalSquareWeightTotal * Γ ^ (-(4 / 3 : ℝ)) * W₁ :=
        add_le_add hGloc_bound hrem_bound
    _ = (4 * Real.pi * C_loc + 4 * reciprocalSquareWeightTotal) * Γ ^ (-(4 / 3 : ℝ)) * W₁ := by ring
    _ ≤ (4 * Real.pi * C_loc + 4 * reciprocalSquareWeightTotal) * Γ ^ (-(4 / 3 : ℝ)) *
          deficitWindowNorm ψ :=
        mul_le_mul_of_nonneg_left hW₁_le
          (by positivity [reciprocalSquareWeightTotal_nonneg])

/-- **Unconditional Polynomial Decay of Cosine-Filtered `ccmPrimeDeficitIncoming`
(`exists_frequencyAverage_abs_cosineFiltered_ccmPrimeDeficitIncoming_le`):**
For every aperture slope `0 ≤ α < 2/3` (covering both Huxley `5/12` and Guth–Maynard `13/30`),
there exist `C ≥ 0` and `Γ₀ ≥ 8` such that for all `Γ ≥ Γ₀`, all `0 ≤ A ≤ α log Γ`, and every
`ψ ∈ C²_c(ℝ)` supported in `[0, 2A]`,
`(1 / Γ) ∫_Γ^{2Γ} |∫_0^{2A} ccmPrimeDeficitIncoming t * ψ t * cos(γ t) dt| dγ ≤ C * Γ^{-1/2} * deficitWindowNorm ψ`. -/
theorem exists_frequencyAverage_abs_cosineFiltered_ccmPrimeDeficitIncoming_le
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Γ₀ : ℝ, 8 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ A : ℝ, 0 ≤ A → A ≤ α * Real.log Γ →
        ∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
          (∀ t : ℝ, t < 0 ∨ 2 * A < t → ψ t = 0) →
          (1 / Γ) * (∫ γ in Icc Γ (2 * Γ),
            |∫ t : ℝ, ccmPrimeDeficitIncoming t * ψ t * Real.cos (γ * t)|) ≤
            C * Γ ^ (-(1 / 2 : ℝ)) * deficitWindowNorm ψ := by
  obtain ⟨C₀, hC₀, harch_err⟩ := exists_abs_ccmPrimeDeficitIncoming_sub_spectralDeficitSum_le
  obtain ⟨C_spec, hC_spec, Γ₀, hΓ₀, hspec⟩ :=
    exists_frequencyAverage_abs_cosineFiltered_spectralDeficitSum_le hα0 hα
  set C_arch : ℝ := 1 / 2 + Real.pi * (32 * C₀ ^ 2)
  refine ⟨C_arch + C_spec, by dsimp [C_arch]; positivity, Γ₀, hΓ₀,
    fun Γ hΓ A hA0 hA ψ hψ hψc hsupp => ?_⟩
  have hΓ8 : 8 ≤ Γ := hΓ₀.trans hΓ
  have hΓ1 : 1 ≤ Γ := by linarith
  have hΓ0 : 0 < Γ := by linarith
  set g_err : ℝ → ℝ := fun t => (ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re) * ψ t
  set g_spec : ℝ → ℝ := fun t => (spectralDeficitSum t).re * ψ t
  have hg_err_cont : Continuous g_err :=
    (continuous_ccmPrimeDeficitIncoming.sub
      (Complex.continuous_re.comp continuous_spectralDeficitSum)).mul hψ.continuous
  have hg_err_comp : HasCompactSupport g_err := hψc.mul_left
  have hg_spec_cont : Continuous g_spec :=
    (Complex.continuous_re.comp continuous_spectralDeficitSum).mul hψ.continuous
  have hg_spec_comp : HasCompactSupport g_spec := hψc.mul_left
  -- Bound `∫ t, g_err t ^ 2 ≤ 32 * C₀ ^ 2 * M ^ 2` where `M = ⨆ t, |ψ t|`
  set M : ℝ := ⨆ t : ℝ, |ψ t|
  have hb : BddAbove (Set.range fun t : ℝ => |ψ t|) :=
    hψ.continuous.abs.bddAbove_range_of_hasCompactSupport hψc.abs
  have hM0 : 0 ≤ M := le_ciSup_of_le hb 0 (abs_nonneg _)
  have hψ_le_M : ∀ t : ℝ, |ψ t| ≤ M := fun t => le_ciSup hb t
  have hM_le_norm : M ≤ deficitWindowNorm ψ := by
    unfold deficitWindowNorm M
    have h1 : 0 ≤ ∫ t, |ψ t| := integral_nonneg fun _ => abs_nonneg _
    have h2 : 0 ≤ ∫ t, |deriv (deriv ψ) t| := integral_nonneg fun _ => abs_nonneg _
    linarith
  have hg_err_zero : M = 0 → ∀ t : ℝ, g_err t = 0 := fun hM_eq t => by
    have hψ0 : ψ t = 0 := abs_eq_zero.mp (le_antisymm ((hψ_le_M t).trans_eq hM_eq) (abs_nonneg _))
    simp [g_err, hψ0]
  have hg_err_L2 : (∫ t : ℝ, g_err t ^ 2) ≤ (32 * C₀ ^ 2) * M ^ 2 := by
    have hvan : ∀ t : ℝ, t ∉ Icc 0 (2 * A) → g_err t ^ 2 = 0 := fun t ht => by
      have h0 : ψ t = 0 := hsupp t (lt_zero_or_gt_of_not_mem_Icc (by rwa [Set.mem_Icc] at ht))
      dsimp only [g_err]; rw [h0]; ring
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan]
    have hpt_sq : ∀ t ∈ Icc (0 : ℝ) (2 * A),
        g_err t ^ 2 ≤ 16 * C₀ ^ 2 * M ^ 2 * Real.exp (-t / 2) := fun t ht => by
      have h1t : 1 + t ≤ 4 * Real.exp (t / 4) := by
        linarith [Real.add_one_le_exp (t / 4)]
      have herr_t : |ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re| ≤
          4 * C₀ * Real.exp (-t / 4) := by
        calc |ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re|
            ≤ C₀ * (1 + t) * Real.exp (-t / 2) := harch_err t ht.1
          _ ≤ C₀ * (4 * Real.exp (t / 4)) * Real.exp (-t / 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1t hC₀.le) (Real.exp_pos _).le
          _ = 4 * C₀ * (Real.exp (t / 4) * Real.exp (-t / 2)) := by ring
          _ = 4 * C₀ * Real.exp (-t / 4) := by
              rw [← Real.exp_add]; congr 2; ring
      have habs_g : |g_err t| ≤ 4 * C₀ * M * Real.exp (-t / 4) := by
        dsimp [g_err]
        rw [abs_mul]
        calc |ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re| * |ψ t|
            ≤ (4 * C₀ * Real.exp (-t / 4)) * M :=
              mul_le_mul herr_t (hψ_le_M t) (abs_nonneg _) (by positivity)
          _ = 4 * C₀ * M * Real.exp (-t / 4) := by ring
      have hsq := pow_le_pow_left₀ (abs_nonneg (g_err t)) habs_g 2
      rw [sq_abs] at hsq
      refine hsq.trans_eq ?_
      have hexp2 : Real.exp (-t / 4) ^ 2 = Real.exp (-t / 2) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      calc (4 * C₀ * M * Real.exp (-t / 4)) ^ 2
          = 16 * C₀ ^ 2 * M ^ 2 * Real.exp (-t / 4) ^ 2 := by ring
        _ = 16 * C₀ ^ 2 * M ^ 2 * Real.exp (-t / 2) := by rw [hexp2]
    have hint_exp : (∫ t in Icc (0 : ℝ) (2 * A), Real.exp (-t / 2)) ≤ 2 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * A)]
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => -2 * Real.exp (-t / 2))
        (f' := fun t : ℝ => Real.exp (-t / 2))
        (fun t _ => by
          have hd : HasDerivAt (fun s : ℝ => -s / 2) (-1 / 2) t := by
            simpa using ((hasDerivAt_id t).neg).div_const 2
          have h := (hd.exp).const_mul (-2)
          simpa only [show -2 * (Real.exp (-t / 2) * (-1 / 2)) = Real.exp (-t / 2) by ring] using h)
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t / 2)).intervalIntegrable 0 (2 * A))
      rw [hftc]
      simp only [neg_zero, zero_div, Real.exp_zero, mul_one]
      linarith [Real.exp_pos (-(2 * A) / 2)]
    calc (∫ t in Icc (0 : ℝ) (2 * A), g_err t ^ 2)
        ≤ ∫ t in Icc (0 : ℝ) (2 * A), 16 * C₀ ^ 2 * M ^ 2 * Real.exp (-t / 2) :=
          setIntegral_mono_on (hg_err_cont.pow 2).integrableOn_Icc
            ((by fun_prop : Continuous fun t : ℝ => 16 * C₀ ^ 2 * M ^ 2 * Real.exp (-t / 2)).integrableOn_Icc)
            measurableSet_Icc hpt_sq
      _ = 16 * C₀ ^ 2 * M ^ 2 * ∫ t in Icc (0 : ℝ) (2 * A), Real.exp (-t / 2) :=
          integral_const_mul _ _
      _ ≤ 16 * C₀ ^ 2 * M ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left hint_exp (by positivity)
      _ = (32 * C₀ ^ 2) * M ^ 2 := by ring
  have herr_avg := frequencyAverage_abs_cosine_pairing_le hg_err_cont hg_err_comp
    hΓ1 hM0 (by positivity : 0 ≤ 32 * C₀ ^ 2) hg_err_zero hg_err_L2
  have herr_avg' : (1 / Γ) * (∫ γ in Icc Γ (2 * Γ), |∫ t : ℝ, g_err t * Real.cos (γ * t)|) ≤
      C_arch * Γ ^ (-(1 / 2 : ℝ)) * deficitWindowNorm ψ := by
    refine herr_avg.trans ?_
    dsimp [C_arch]
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hM_le_norm (by positivity : 0 ≤ 1 / 2 + Real.pi * (32 * C₀ ^ 2)))
      (Real.rpow_nonneg hΓ0.le (-(1 / 2 : ℝ)))
    linarith
  have hspec_avg := hspec Γ hΓ A hA0 hA ψ hψ hψc hsupp
  have hspec_avg' : (1 / Γ) * (∫ γ in Icc Γ (2 * Γ), |∫ t : ℝ, g_spec t * Real.cos (γ * t)|) ≤
      C_spec * Γ ^ (-(1 / 2 : ℝ)) * deficitWindowNorm ψ := by
    refine hspec_avg.trans ?_
    have hrpow : Γ ^ (-(4 / 3 : ℝ)) ≤ Γ ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow hC_spec)
      (deficitWindowNorm_nonneg hψ hψc)
  -- Combine `g_err + g_spec` via triangle inequality
  have htri_pt : ∀ γ : ℝ,
      |∫ t : ℝ, ccmPrimeDeficitIncoming t * ψ t * Real.cos (γ * t)| ≤
        |∫ t : ℝ, g_err t * Real.cos (γ * t)| + |∫ t : ℝ, g_spec t * Real.cos (γ * t)| := fun γ => by
    have hi1 : Integrable fun t : ℝ => g_err t * Real.cos (γ * t) :=
      (hg_err_cont.mul (by fun_prop)).integrable_of_hasCompactSupport hg_err_comp.mul_right
    have hi2 : Integrable fun t : ℝ => g_spec t * Real.cos (γ * t) :=
      (hg_spec_cont.mul (by fun_prop)).integrable_of_hasCompactSupport hg_spec_comp.mul_right
    have heq : (∫ t : ℝ, ccmPrimeDeficitIncoming t * ψ t * Real.cos (γ * t)) =
        (∫ t : ℝ, g_err t * Real.cos (γ * t)) + ∫ t : ℝ, g_spec t * Real.cos (γ * t) := by
      rw [← integral_add hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp [g_err, g_spec]; ring
    rw [heq]
    exact abs_add_le _ _
  have hint_tot : IntegrableOn
      (fun γ : ℝ => |∫ t : ℝ, ccmPrimeDeficitIncoming t * ψ t * Real.cos (γ * t)|)
      (Icc Γ (2 * Γ)) :=
    (continuous_cosine_pairing (continuous_ccmPrimeDeficitIncoming.mul hψ.continuous)
      hψc.mul_left).abs.integrableOn_Icc
  have hint_e : IntegrableOn (fun γ : ℝ => |∫ t : ℝ, g_err t * Real.cos (γ * t)|) (Icc Γ (2 * Γ)) :=
    (continuous_cosine_pairing hg_err_cont hg_err_comp).abs.integrableOn_Icc
  have hint_s : IntegrableOn (fun γ : ℝ => |∫ t : ℝ, g_spec t * Real.cos (γ * t)|) (Icc Γ (2 * Γ)) :=
    (continuous_cosine_pairing hg_spec_cont hg_spec_comp).abs.integrableOn_Icc
  have hmono_tot := setIntegral_mono_on hint_tot (hint_e.add hint_s)
    measurableSet_Icc fun γ _ => htri_pt γ
  dsimp only [Pi.add_apply] at hmono_tot
  rw [integral_add hint_e hint_s] at hmono_tot
  have hmul_tot := mul_le_mul_of_nonneg_left hmono_tot (by positivity : 0 ≤ 1 / Γ)
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

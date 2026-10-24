import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TuransInequalityWithoutBoundedOnLineDensity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfAnIsolatedPair
import GaloisForLFunctions.RHTower.XiLogDerivLineOneWindowLower

/-!
# The Doubly-Logarithmic Visibility Law, On-Line Mass Barrier, and Excluded Depth over `ℚ`

In `TuransInequalityWithoutBoundedOnLineDensity`, the local off-line hypothesis
`OffLineCopiesLocallyBounded M` (which bounds only zeros with `Re ρ ≠ ½` in unit height windows and
places no bound on on-line zeros) eliminated the `log γ₀` factor from the Turán / Fejér cubic
potential tail (`offLineTwinPotential M r = 6 M (1/r³ + 3)`), made the unmodulated (`c = 0`)
visibility lags `recordLagOffLine` and `oneParamLagOffLine` completely height-free, and reduced the
modulated (`c = γ₀`) near-top visibility lag to `nearTopLagOffLine M w W_on (Re z₀)` and
`nearTopLogLogLagOffLine M w γ₀ (Re z₀)`.

This module completes the resolution of the visibility-aperture problem over `ℚ`:

1. **Exact two-sided logarithmic law for on-line mass `onLineEvenMass w c` and `2 Re S(0)` (§1)**
   (`norm_paperFT_scaledBump_real_ge_of_mul_abs_le`, `sum_mult_mul_le_onLineEvenMass`,
   `sum_mult_offLine_radius_le_of_offLineCopiesLocallyBounded`,
   `onLineEvenMass_ge_xiZeroCount_window_sub_of_offLineCopiesLocallyBounded`,
   `exists_onLineEvenMass_two_sided_log_of_offLineCopiesLocallyBounded`):
   Why does `onLineEvenMass w γ₀ = Θ_w(log γ₀)` remain under `OffLineCopiesLocallyBounded M`?
   By the Riemann–von Mangoldt bounded-window theorem `exists_xiZeroCount_window_ge_log`, there exist
   `h > 0` and `T₁ ≥ 4` such that every window `(c - h, c + h]` (`c ≥ T₁`) contains at least
   `log c` zeros of `ξ` with multiplicity. Under `OffLineCopiesLocallyBounded M`, at most
   `(2 ⌈h⌉₊ + 1) M` of those multiplicities are off-line (`Re ρ ≠ ½`), so at least
   `log c - (2 ⌈h⌉₊ + 1) M` are on-line (`Re ρ = ½`). Because every on-line zero in `[c - h, c + h]`
   has `‖h_w(γ - c)‖ ≥ 2 w ∫ weilBump` for `w h ≤ 1/8` and on-line coefficients never cancel,
   `onLineEvenMass w c` obeys the unconditional two-sided logarithmic law
   `c_w log c ≤ onLineEvenMass w c ≤ C_w (C_ξ + log(|c| + 4))`, and `2 Re S(0)` lies within
   `± 24 M² (e^{w/2} B_w)²` of `onLineEvenMass w c`.

2. **Exact two-sided order of the off-line visibility lags (§2)**
   (`log_noise_le_explicitOrder`, `recordOrderOffLine_two_sided`, `recordLagOffLine_two_sided`,
   `nearTopOrderOffLine_two_sided`, `nearTopLagOffLine_two_sided`,
   `nearTopLogLogLagOffLine_two_sided`):
   Using `explicitOrder_le`, `le_explicitOrder`, and the noise-logarithm lower bound
   `log M_noise / log 2 ≤ explicitOrder M_noise c P`, we establish explicit two-sided bounds for the
   entire off-line visibility hierarchy. Without `OffLineCopiesLocallyBounded M`, the companion count
   `P = ⌈80 log(180 Γ)⌉ ≍ log γ₀` made `2 P² log(P + 1) / log 2 ≍ (log γ₀)² log log γ₀` the
   dominant term in `explicitOrder`. Under `OffLineCopiesLocallyBounded M`, `P = M` is constant, so
   the height dependence shifts entirely to `log(nearTopNoiseOffLine M w W_on) / log 2`, giving
   `nearTopLagOffLine M w W_on δ₀ = Θ_{M,w}((1 + log⁺ W_on) / δ₀)` and
   `nearTopLogLogLagOffLine M w γ₀ δ₀ = Θ_{M,w}((1 + log log(|γ₀| + 4)) / δ₀)` from both sides.

3. **Intrinsic optimality of the doubly-logarithmic aperture: the on-line mass barrier and the
   all-test Hodge-defect threshold (§3)**
   (`onLineLagStructure`, `offLineLagStructure`,
   `two_re_lagStructure_eq_onLine_add_offLine`,
   `re_W_twoBump_modScaledBump_ge_onLineEvenMass_sub`,
   `re_W_twoBump_modScaledBump_nonneg_of_lag_le_log_ratio`,
   `rvmLocalDensity`, `hodgeDefectAt_isolatedPair_rvmDensity_eq_zero`,
   `hodgeDefectAt_isolatedPair_rvmDensity_eq_one`):
   We prove that the doubly-logarithmic scale `Θ((log log γ₀) / δ₀)` is not an artifact of the
   Turán power method, by establishing two complementary lower barriers:
   - *Difference-test barrier*: For any lag `v ≥ 0`,
     `Re W(twoBump b v (-1)) ≥ (onLineEvenMass w c - onLineLagStructure w c v) - offLineEvenMass w c · (e^{δ₀ v} + 1)`.
     Whenever the on-line cosine phases are `θ`-decoherent (`onLineLagStructure w c v ≤ (1 - θ) onLineEvenMass w c`),
     `Re W < 0` is impossible for `v ≤ (1/δ₀) log(θ · onLineEvenMass w c / offLineEvenMass w c - 1) = Ω_{w,M}((log log c) / δ₀)`.
   - *All-test Hodge-defect threshold*: In `isolatedPairConfig L δ₀ γ₀` at the Riemann–von Mangoldt
     local on-line density `L = (1/2π) log(γ₀/2π)`, `hodgeDefectAt = 0` for all `C²_c([-a, a])` tests
     when `0 < a ≤ (1/(2δ₀)) log(4 δ₀ L)` and `hodgeDefectAt = 1` when
     `(1/(2δ₀)) log(8 δ₀ L) ≤ a ≤ L/2`. Thus `a = Θ((log log γ₀) / δ₀)` is the exact visibility
     threshold across all compactly supported `C²` test functions.

4. **Modulated contact-aperture bridge and excluded-depth laws under `OffLineCopiesLocallyBounded M` (§4)**
   (`tsupport_twoBump_modScaledBump_subset_any`,
   `ccmRestrictedWeilGroundEnergy_neg_of_re_W_twoBump_modScaledBump_neg`,
   `zetaContactAperture_le_of_near_top_loglog_of_offLineCopiesLocallyBounded`,
   `recordExcludedDepthOffLine`, `nearTopExcludedDepthOffLine`, `nearTopLogLogExcludedDepthOffLine`,
   `recordLagOffLine_le_iff_le_recordExcludedDepthOffLine`,
   `nearTopLagOffLine_le_iff_le_nearTopExcludedDepthOffLine`,
   `nearTopLogLogLagOffLine_le_iff_le_nearTopLogLogExcludedDepthOffLine`,
   `re_lt_nearTopExcludedDepthOffLine_of_pos_on_Icc`,
   `re_lt_nearTopLogLogExcludedDepthOffLine_of_pos_on_Icc`,
   `re_lt_nearTopLogLogExcludedDepthOffLine_of_lt_contactAperture`):
   Extending the Rayleigh ground-energy bridge to arbitrary modulation centers `c ∈ ℝ` bounds
   `zetaContactAperture ≤ V / 2 + w` at the doubly-logarithmic lag
   `V ≥ nearTopLogLogLagOffLine M w z₀.im z₀.re`. Because `recordOrderOffLine M w a` and
   `nearTopOrderOffLine M w W_on` are independent of the depth parameter `σ` / `δ₀`,
   `recordLagOffLine` and `nearTopLagOffLine` are exact affine functions of `1 / δ₀`, yielding closed-form
   excluded-depth equivalences `Lag ≤ V ↔ ExcludedDepth ≤ δ₀` and certifying that positivity on
   `[0, V]` (or `V/2 + w < zetaContactAperture`) excludes every `1/V`-near-top zero of depth
   `≥ nearTopLogLogExcludedDepthOffLine M w γ₀ V = O_{w,M}((1 + log log γ₀) / V)`, improving
   `nearTopExcludedDepth` by `(log γ₀)²`.
-/

open Complex MeasureTheory Real Set Filter Topology Finset Matrix
open scoped Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.SquareRootThreshold
  GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Exact two-sided logarithmic law for on-line mass `onLineEvenMass w c` and `2 Re S(0)` -/

/-- Elementary lower bound `1 / 2 ≤ cos(1 / 8)`. -/
theorem half_le_cos_one_eighth : (1 / 2 : ℝ) ≤ Real.cos (1 / 8) := by
  have h1 : (0 : ℝ) ≤ 1 / 8 := by norm_num
  have h2 : (1 / 8 : ℝ) ≤ Real.pi / 3 := by linarith [Real.pi_gt_three]
  have hcos : Real.cos (Real.pi / 3) ≤ Real.cos (1 / 8) :=
    Real.cos_le_cos_of_nonneg_of_le_pi h1 (by linarith [Real.pi_pos]) h2
  rwa [Real.cos_pi_div_three] at hcos

/-- **Real-axis lower bound for `paperFT (scaledBump w)`.** Whenever `w > 0` and `w |s| ≤ 1/8`,
`2 w ∫ weilBump ≤ 4 w cos(1/8) ∫ weilBump ≤ ‖paperFT (scaledBump w) s‖`. -/
theorem norm_paperFT_scaledBump_real_ge_of_mul_abs_le {w : ℝ} (hw : 0 < w) {s : ℝ}
    (hs : w * |s| ≤ 1 / 8) :
    2 * w * (∫ u, weilBump u) ≤ ‖paperFT (scaledBump w) (s : ℂ)‖ := by
  rw [paperFT_scaledBump hw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 4 * w)]
  have hs' : |4 * w * s| ≤ 1 / 2 := by
    rw [show 4 * w * s = 4 * (w * s) by ring, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hw]
    linarith
  have h := norm_paperFT_weilBumpC_real_ge hs'
  rw [show (((4 * w : ℝ) : ℂ) * (s : ℂ)) = ((4 * w * s : ℝ) : ℂ) by push_cast; ring]
  have hint : 0 ≤ ∫ u, weilBump u := integral_nonneg fun u => weilBump.nonneg
  have hcos := half_le_cos_one_eighth
  calc 2 * w * (∫ u, weilBump u)
      = 4 * w * ((1 / 2) * (∫ u, weilBump u)) := by ring
    _ ≤ 4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u)) := by gcongr
    _ ≤ 4 * w * ‖paperFT weilBumpC ((4 * w * s : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_left h (by positivity)

/-- **Pointwise lower bound for an on-line modulated coefficient near the modulation center.**
For every on-line zero `ρ ∈ Z.carrier` (`Re ρ = ½`) within `w |Im ρ - c| ≤ 1/8` of the modulation
center `c`, the exponent `z = ρ - ½` (`Re z = 0`) has
`mult(ρ) · (2 w ∫ weilBump)² ≤ ‖evenCoeff Z (modScaledBump w c) (ρ - ½)‖`. -/
theorem norm_evenCoeff_modScaledBump_onLine_ge (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) (c : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hre : ρ.re = 1 / 2) (him : w * |ρ.im - c| ≤ 1 / 8) :
    (Z.mult ρ : ℝ) * (2 * w * (∫ u, weilBump u)) ^ 2 ≤
      ‖evenCoeff Z (modScaledBump w c) (ρ - 1 / 2)‖ := by
  set z : ℂ := ρ - 1 / 2 with hzdef
  have hzre : z.re = 0 := by simp [hzdef, hre]
  have hzim : z.im = ρ.im := by simp [hzdef]
  have hzmem : (1 / 2 + z) ∈ Z.carrier := by
    have e : 1 / 2 + z = ρ := by rw [hzdef]; ring
    rwa [e]
  have hlag1 : lagCoeff Z (modScaledBump w c) z =
      (((Z.mult ρ : ℝ) * ‖paperFT (scaledBump w) ((ρ.im - c : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    have e : 1 / 2 + z = ρ := by rw [hzdef]; ring
    rw [lagCoeff_modScaledBump Z hw c hzmem, e]
    have harg : -(I * z) - (c : ℂ) = ((ρ.im - c : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hzre, hzim]
    rw [harg, paperFT_scaledBump_ofReal_sq_eq_norm_sq]
    push_cast; ring
  have hlag2 : ∃ r₂ : ℝ, 0 ≤ r₂ ∧ lagCoeff Z (modScaledBump w c) (conj z) = (r₂ : ℂ) := by
    by_cases hc : (1 / 2 + conj z) ∈ Z.carrier
    · refine ⟨(Z.mult (1 / 2 + conj z) : ℝ) *
        ‖paperFT (scaledBump w) (((conj z).im - c : ℝ) : ℂ)‖ ^ 2, by positivity, ?_⟩
      rw [lagCoeff_modScaledBump Z hw c hc]
      have harg : -(I * conj z) - (c : ℂ) = (((conj z).im - c : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hzre]
      rw [harg, paperFT_scaledBump_ofReal_sq_eq_norm_sq]
      push_cast; ring
    · exact ⟨0, le_rfl, by rw [lagCoeff, Set.indicator_of_notMem hc, Complex.ofReal_zero]⟩
  obtain ⟨r₂, hr₂0, hr₂⟩ := hlag2
  have hev : evenCoeff Z (modScaledBump w c) z =
      (((Z.mult ρ : ℝ) * ‖paperFT (scaledBump w) ((ρ.im - c : ℝ) : ℂ)‖ ^ 2 + r₂ : ℝ) : ℂ) := by
    rw [evenCoeff, hlag1, hr₂, Complex.conj_ofReal, Complex.ofReal_add]
  have hnorm : ‖evenCoeff Z (modScaledBump w c) z‖ =
      (Z.mult ρ : ℝ) * ‖paperFT (scaledBump w) ((ρ.im - c : ℝ) : ℂ)‖ ^ 2 + r₂ := by
    rw [hev, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hft := norm_paperFT_scaledBump_real_ge_of_mul_abs_le hw him
  have hint : 0 ≤ 2 * w * (∫ u, weilBump u) := by
    have : 0 ≤ ∫ u, weilBump u := integral_nonneg fun u => weilBump.nonneg
    positivity
  have hsq : (2 * w * (∫ u, weilBump u)) ^ 2 ≤
      ‖paperFT (scaledBump w) ((ρ.im - c : ℝ) : ℂ)‖ ^ 2 :=
    pow_le_pow_left₀ hint hft 2
  have hm := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (Z.mult ρ))
  linarith [hnorm, hr₂0, hm]

/-- **Finite-window on-line multiplicity lower bound for `onLineEvenMass`.** For any finite set `S`
of on-line zeros of `ζ` (`Re ρ = ½`) in `[c - R, c + R]` with `w R ≤ 1/8`,
`(2 w ∫ weilBump)² ∑_{ρ ∈ S} mult(ρ) ≤ onLineEvenMass w c`. -/
theorem sum_mult_mul_le_onLineEvenMass {w c R : ℝ} (hw : 0 < w) (hwR : w * R ≤ 1 / 8)
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier ∧ ρ.re = 1 / 2 ∧ |ρ.im - c| ≤ R) :
    (2 * w * (∫ u, weilBump u)) ^ 2 * (∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ)) ≤
      onLineEvenMass w c := by
  classical
  set b := modScaledBump w c with hb
  set D := evenCoeff zetaZeroConfig b with hD
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c)
  have hs_on : Summable (fun z : ℂ => if z.re = 0 then ‖D z‖ else 0) :=
    hsD.of_nonneg_of_le (fun z => by split_ifs <;> positivity)
      (fun z => by split_ifs <;> [exact le_rfl; exact norm_nonneg _])
  have hinj : Function.Injective (fun ρ : ℂ => ρ - 1 / 2) := fun x y h => by
    simpa [sub_eq_iff_eq_add] using h
  set T : Finset ℂ := S.image (fun ρ : ℂ => ρ - 1 / 2) with hT
  have hsum_le : ∑ z ∈ T, (if z.re = 0 then ‖D z‖ else 0) ≤ onLineEvenMass w c :=
    hs_on.sum_le_tsum T (fun z _ => by split_ifs <;> positivity)
  have hT_eq : ∑ z ∈ T, (if z.re = 0 then ‖D z‖ else 0) =
      ∑ ρ ∈ S, (if (ρ - 1 / 2).re = 0 then ‖D (ρ - 1 / 2)‖ else 0) := by
    rw [hT, Finset.sum_image fun x _ y _ h => hinj h]
  have hterm : ∀ ρ ∈ S,
      (zetaZeroConfig.mult ρ : ℝ) * (2 * w * (∫ u, weilBump u)) ^ 2 ≤
        (if (ρ - 1 / 2).re = 0 then ‖D (ρ - 1 / 2)‖ else 0) := by
    intro ρ hρ
    obtain ⟨hmem, hre, him⟩ := hS ρ hρ
    have hzre : (ρ - 1 / 2).re = 0 := by simp [hre]
    rw [if_pos hzre]
    exact norm_evenCoeff_modScaledBump_onLine_ge zetaZeroConfig hw c hmem hre
      ((mul_le_mul_of_nonneg_left him hw.le).trans hwR)
  calc (2 * w * (∫ u, weilBump u)) ^ 2 * (∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ))
      = ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * (2 * w * (∫ u, weilBump u)) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ρ _ => mul_comm _ _
    _ ≤ ∑ ρ ∈ S, (if (ρ - 1 / 2).re = 0 then ‖D (ρ - 1 / 2)‖ else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ z ∈ T, (if z.re = 0 then ‖D z‖ else 0) := hT_eq.symm
    _ ≤ onLineEvenMass w c := hsum_le

/-- **Off-line multiplicity bound in a radius-`R` height window.** Under
`OffLineCopiesLocallyBounded M`, any finite set `S` of off-line zeros of `ζ` (`Re ρ ≠ ½`) in
`[c - R, c + R]` has total multiplicity `∑_{ρ ∈ S} mult(ρ) ≤ (2 ⌈R⌉₊ + 1) M`,
completely independent of the window center `c`. -/
theorem sum_mult_offLine_radius_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) (c R : ℝ) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier ∧ ρ.re ≠ 1 / 2 ∧ |ρ.im - c| ≤ R) :
    ∑ ρ ∈ S, zetaZeroConfig.mult ρ ≤ (2 * ⌈R⌉₊ + 1) * M := by
  classical
  set N : ℕ := ⌈R⌉₊ with hN
  set j : ℂ → ℤ := fun ρ => ⌊ρ.im - c⌋ with hj
  set J : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hJ
  have hmaps : ∀ ρ ∈ S, j ρ ∈ J := by
    intro ρ hρ
    have him := (hS ρ hρ).2.2
    rw [abs_le] at him
    have hRN : R ≤ (N : ℝ) := Nat.le_ceil R
    rw [hJ, Finset.mem_Icc, hj]
    refine ⟨?_, ?_⟩
    · exact Int.le_floor.mpr (by push_cast; linarith)
    · exact Int.floor_le_iff.mpr (by push_cast; linarith)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ k ∈ J, ∑ ρ ∈ S with j ρ = k, zetaZeroConfig.mult ρ ≤ M := by
    intro k _
    refine sum_mult_offLine_window_le_of_offLineCopiesLocallyBounded hM (c + k)
      (S.filter fun ρ => j ρ = k) fun ρ hρ => ?_
    rw [Finset.mem_filter] at hρ
    obtain ⟨hρS, hjk⟩ := hρ
    obtain ⟨hmem, hne, -⟩ := hS ρ hρS
    have h1 := Int.floor_le (ρ.im - c)
    have h2 := Int.lt_floor_add_one (ρ.im - c)
    rw [hj] at hjk; simp only at hjk; rw [hjk] at h1 h2
    refine ⟨hmem, hne, ?_⟩
    rw [abs_le]
    constructor <;> linarith
  have hcard : J.card = 2 * N + 1 := by
    rw [hJ, Int.card_Icc]
    omega
  calc ∑ k ∈ J, ∑ ρ ∈ S with j ρ = k, zetaZeroConfig.mult ρ
      ≤ ∑ _k ∈ J, M := Finset.sum_le_sum hfib
    _ = J.card * M := by rw [Finset.sum_const, smul_eq_mul]
    _ = (2 * N + 1) * M := by rw [hcard]

/-- **Lower bound for `onLineEvenMass` from the `ξ`-zero counting function.** Under
`OffLineCopiesLocallyBounded M`, for every `0 < R ≤ c` and every `w > 0` with `w R ≤ 1/8`, the
window `(c - R, c + R]` contributes at least
`(2 w ∫ weilBump)² · (xiZeroCount(c + R) - xiZeroCount(c - R) - (2 ⌈R⌉₊ + 1) M)`
to `onLineEvenMass w c`. -/
theorem onLineEvenMass_ge_xiZeroCount_window_sub_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w c R : ℝ} (hw : 0 < w) (hR : 0 < R) (hRc : R ≤ c)
    (hwR : w * R ≤ 1 / 8) :
    (2 * w * (∫ u, weilBump u)) ^ 2 *
        ((RHTower.xiZeroCount (c + R) : ℝ) - (RHTower.xiZeroCount (c - R) : ℝ) -
          ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) * M) ≤
      onLineEvenMass w c := by
  classical
  have h0 : 0 ≤ c - R := by linarith
  have hle : c - R ≤ c + R := by linarith
  set W₀ : Finset XiDivisorSupport := RHTower.xiSupportsWindow (c - R) (c + R) with hW₀
  set emb : XiDivisorSupport → ℂ := fun d => (RHTower.xiDivisorZetaCarrierEquiv d : ℂ) with hemb
  have hinj : Function.Injective emb := fun x y h => by
    apply RHTower.xiDivisorZetaCarrierEquiv.injective
    exact Subtype.ext h
  set W : Finset ℂ := W₀.image emb with hW
  have hW_mem : ∀ ρ ∈ W, ρ ∈ zetaZeroConfig.carrier ∧ |ρ.im - c| ≤ R := by
    intro ρ hρ
    rw [hW, Finset.mem_image] at hρ
    obtain ⟨d, hd, rfl⟩ := hρ
    have hd_win := (RHTower.mem_xiSupportsWindow h0).mp hd
    have hval : (emb d : ℂ) = (d : ℂ) := rfl
    refine ⟨(RHTower.xiDivisorZetaCarrierEquiv d).2, ?_⟩
    rw [hval, abs_le]
    constructor <;> linarith [hd_win.1, hd_win.2]
  have hW_sum : ∑ ρ ∈ W, (zetaZeroConfig.mult ρ : ℝ) =
      (RHTower.xiZeroCount (c + R) : ℝ) - (RHTower.xiZeroCount (c - R) : ℝ) := by
    rw [hW, Finset.sum_image fun x _ y _ h => hinj h]
    rw [← RHTower.sum_mult_xiSupportsWindow h0 hle]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hm := RHTower.xiDivisorZetaCarrierEquiv_multiplicity d
    unfold RHTower.xiSupportMultiplicity
    exact_mod_cast hm.symm
  set W_on : Finset ℂ := W.filter (fun ρ => ρ.re = 1 / 2) with hW_on
  set W_off : Finset ℂ := W.filter (fun ρ => ρ.re ≠ 1 / 2) with hW_off
  have hsplit : ∑ ρ ∈ W, (zetaZeroConfig.mult ρ : ℝ) =
      (∑ ρ ∈ W_on, (zetaZeroConfig.mult ρ : ℝ)) + (∑ ρ ∈ W_off, (zetaZeroConfig.mult ρ : ℝ)) := by
    rw [hW_on, hW_off, Finset.sum_filter_add_sum_filter_not]
  have hoff_nat : ∑ ρ ∈ W_off, zetaZeroConfig.mult ρ ≤ (2 * ⌈R⌉₊ + 1) * M :=
    sum_mult_offLine_radius_le_of_offLineCopiesLocallyBounded hM c R W_off fun ρ hρ => by
      rw [hW_off, Finset.mem_filter] at hρ
      exact ⟨(hW_mem ρ hρ.1).1, hρ.2, (hW_mem ρ hρ.1).2⟩
  have hoff : ∑ ρ ∈ W_off, (zetaZeroConfig.mult ρ : ℝ) ≤ ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) * M := by
    exact_mod_cast hoff_nat
  have hon_ge : (RHTower.xiZeroCount (c + R) : ℝ) - (RHTower.xiZeroCount (c - R) : ℝ) -
      ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) * M ≤ ∑ ρ ∈ W_on, (zetaZeroConfig.mult ρ : ℝ) := by
    linarith [hW_sum, hsplit, hoff]
  have hon_mass : (2 * w * (∫ u, weilBump u)) ^ 2 * (∑ ρ ∈ W_on, (zetaZeroConfig.mult ρ : ℝ)) ≤
      onLineEvenMass w c :=
    sum_mult_mul_le_onLineEvenMass hw hwR W_on fun ρ hρ => by
      rw [hW_on, Finset.mem_filter] at hρ
      exact ⟨(hW_mem ρ hρ.1).1, hρ.2, (hW_mem ρ hρ.1).2⟩
  exact (mul_le_mul_of_nonneg_left hon_ge (sq_nonneg _)).trans hon_mass

/-- **Exact two-sided logarithmic law for `onLineEvenMass w c` and `2 Re S(0)` under
`OffLineCopiesLocallyBounded M`.**
There exist an absolute window width `h > 0` and height threshold `T₁ ≥ 4` (from the Riemann–von
Mangoldt formula `exists_xiZeroCount_window_ge_log`) such that for every `M : ℕ` with
`OffLineCopiesLocallyBounded M`, every `0 < w` with `w h ≤ 1/8`, and every
`c ≥ max T₁ (exp (2 (2 ⌈h⌉₊ + 1) M))`:
1. `((2 w ∫ weilBump)² / 2) log c ≤ onLineEvenMass w c ≤ 16 (e^{w/2} B_w)² (C_ξ + log(|c| + 4))`;
2. `|2 Re S(0) - onLineEvenMass w c| ≤ 24 M² (e^{w/2} B_w)²`.

This proves that `onLineEvenMass w c` and `2 Re S(0)` grow as `Θ_w(log c)` unconditionally under
`OffLineCopiesLocallyBounded M`, because on-line zeros in `[c - h, c + h]` have Riemann–von Mangoldt
count `≥ log c - (2 ⌈h⌉₊ + 1) M` and never cancel. -/
theorem exists_onLineEvenMass_two_sided_log_of_offLineCopiesLocallyBounded :
    ∃ h : ℝ, 0 < h ∧ ∃ T₁ : ℝ, 4 ≤ T₁ ∧
      ∀ {M : ℕ}, OffLineCopiesLocallyBounded M →
        ∀ {w c : ℝ}, 0 < w → w * h ≤ 1 / 8 →
          max T₁ (Real.exp (2 * ((2 * ⌈h⌉₊ + 1 : ℕ) : ℝ) * M)) ≤ c →
          (2 * w * (∫ u, weilBump u)) ^ 2 / 2 * Real.log c ≤ onLineEvenMass w c ∧
            onLineEvenMass w c ≤
              16 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
                (xiLineTwoLogDerivConstant + Real.log (|c| + 4)) ∧
            |2 * (lagStructure zetaZeroConfig (modScaledBump w c) 0).re - onLineEvenMass w c| ≤
              24 * (M : ℝ) ^ 2 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := by
  obtain ⟨h, hh, T₁, hT₁4, hwin⟩ := RHTower.exists_xiZeroCount_window_ge_log
  refine ⟨h, hh, max T₁ h, le_trans hT₁4 (le_max_left _ _), ?_⟩
  intro M hM w c hw hwh hc
  have hc_max1 : max T₁ h ≤ c := (le_max_left _ _).trans hc
  have hcT₁ : T₁ ≤ c := (le_max_left _ _).trans hc_max1
  have hch : h ≤ c := (le_max_right _ _).trans hc_max1
  have hcexp : Real.exp (2 * ((2 * ⌈h⌉₊ + 1 : ℕ) : ℝ) * M) ≤ c := (le_max_right _ _).trans hc
  have hlog_ge : 2 * ((2 * ⌈h⌉₊ + 1 : ℕ) : ℝ) * M ≤ Real.log c := by
    have := Real.log_le_log (Real.exp_pos _) hcexp
    rwa [Real.log_exp] at this
  have hxi := hwin c hcT₁
  have hdiff : Real.log c / 2 ≤
      (RHTower.xiZeroCount (c + h) : ℝ) - (RHTower.xiZeroCount (c - h) : ℝ) -
        ((2 * ⌈h⌉₊ + 1 : ℕ) : ℝ) * M := by
    linarith
  have hlow := onLineEvenMass_ge_xiZeroCount_window_sub_of_offLineCopiesLocallyBounded
    hM hw hh hch hwh
  refine ⟨?_, onLineEvenMass_le_log hw c, ?_⟩
  · calc (2 * w * (∫ u, weilBump u)) ^ 2 / 2 * Real.log c
        = (2 * w * (∫ u, weilBump u)) ^ 2 * (Real.log c / 2) := by ring
      _ ≤ (2 * w * (∫ u, weilBump u)) ^ 2 *
            ((RHTower.xiZeroCount (c + h) : ℝ) - (RHTower.xiZeroCount (c - h) : ℝ) -
              ((2 * ⌈h⌉₊ + 1 : ℕ) : ℝ) * M) :=
          mul_le_mul_of_nonneg_left hdiff (sq_nonneg _)
      _ ≤ onLineEvenMass w c := hlow
  · have h2re := two_re_lagStructure_zero_eq_onLineEvenMass_add_offLine hw c
    set D := evenCoeff zetaZeroConfig (modScaledBump w c)
    have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig
      (contDiff_modScaledBump_two w c) (modScaledBump_support hw c)
    have hs_off_re : Summable (fun z : ℂ => if z.re = 0 then 0 else (D z).re) :=
      hsD.of_norm_bounded (fun z => by
        split_ifs
        · rw [norm_zero]; exact norm_nonneg _
        · rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
    have hs_off : Summable (fun z : ℂ => if z.re = 0 then 0 else ‖D z‖) :=
      hsD.of_nonneg_of_le (fun z => by split_ifs <;> positivity)
        (fun z => by split_ifs <;> [exact norm_nonneg _; exact le_rfl])
    have heq : 2 * (lagStructure zetaZeroConfig (modScaledBump w c) 0).re - onLineEvenMass w c =
        ∑' z : ℂ, if z.re = 0 then 0 else (D z).re := by linarith [h2re]
    rw [heq]
    calc |∑' z : ℂ, if z.re = 0 then 0 else (D z).re|
        = ‖∑' z : ℂ, if z.re = 0 then (0 : ℝ) else (D z).re‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' z : ℂ, ‖if z.re = 0 then (0 : ℝ) else (D z).re‖ :=
          norm_tsum_le_tsum_norm hs_off_re.norm
      _ ≤ ∑' z : ℂ, if z.re = 0 then 0 else ‖D z‖ := by
          refine Summable.tsum_le_tsum (fun z => ?_) hs_off_re.norm hs_off
          split_ifs
          · simp
          · rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      _ = offLineEvenMass w c := rfl
      _ ≤ 24 * (M : ℝ) ^ 2 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 :=
          offLineEvenMass_le_of_offLineCopiesLocallyBounded hM hw c

/-! ### 2. Exact two-sided order of `recordOrderOffLine`, `recordLagOffLine`, `nearTopOrderOffLine`,
`nearTopLagOffLine`, and `nearTopLogLogLagOffLine` -/

/-- **Noise-logarithm lower bound for `explicitOrder`.** For any noise scale `M_noise > 0` and
coherence parameter `0 < c ≤ 1`,
`log M_noise / log 2 ≤ explicitOrder M_noise c P`.
When `P = M` is held constant (as under `OffLineCopiesLocallyBounded M`), this noise logarithm is
the dominant term of `explicitOrder M_noise c M`. -/
theorem log_noise_le_explicitOrder {M_noise c : ℝ} (hM : 0 < M_noise) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (P : ℕ) :
    Real.log M_noise / Real.log 2 ≤ (explicitOrder M_noise c P : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hG : 1 ≤ explicitGap c P := by
    unfold explicitGap
    rw [one_le_div hc0]
    have : (1 : ℝ) ≤ ((P : ℝ) + 1) ^ 2 :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) P])
    linarith
  have hG0 : 0 < explicitGap c P := lt_of_lt_of_le zero_lt_one hG
  have hq0 : 0 < explicitRatio c P := by unfold explicitRatio; positivity
  have hq1 : explicitRatio c P ≤ 1 := by
    unfold explicitRatio
    rw [div_le_one (by positivity)]
    have h1 : (1 : ℝ) ≤ 2 * ((P : ℝ) + 1) := by linarith [Nat.cast_nonneg (α := ℝ) P]
    have h2 : (1 : ℝ) ≤ explicitGap c P ^ P := one_le_pow₀ hG
    nlinarith
  have hqp0 : 0 < explicitRatio c P ^ P := pow_pos hq0 P
  have hqp1 : explicitRatio c P ^ P ≤ 1 := pow_le_one₀ hq0.le hq1
  have hA1 : 1 ≤ (160 * π ^ 2 / 3) ^ P :=
    one_le_pow₀ (by nlinarith [Real.pi_gt_three])
  have hF1 : (1 : ℝ) ≤ ((2 * P).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hnum : M_noise ≤ 4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) * M_noise := by
    have : (1 : ℝ) ≤ 4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) := by nlinarith
    nlinarith
  have harg : M_noise ≤ 4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) * M_noise /
      explicitRatio c P ^ P :=
    hnum.trans (le_div_self (by positivity) hqp0 hqp1)
  have hlog : Real.log M_noise / Real.log 2 ≤ Real.logb 2
      (4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) * M_noise / explicitRatio c P ^ P) := by
    rw [Real.logb]
    exact div_le_div_of_nonneg_right (Real.log_le_log hM harg) hl2.le
  unfold explicitOrder
  push_cast
  have hceil := Nat.le_ceil (Real.logb 2
    (4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) * M_noise / explicitRatio c P ^ P))
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  linarith

/-- For `a > 0`, `1 ≤ recordNoiseOffLine M w a`. -/
theorem one_le_recordNoiseOffLine (M : ℕ) (w : ℝ) {a : ℝ} (ha : 0 < a) :
    1 ≤ recordNoiseOffLine M w a := by
  unfold recordNoiseOffLine
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have he : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
  have h1 : 0 ≤ 4 * (32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log 4)) / ((Real.exp 1 - 1) * a) := by positivity
  linarith [Nat.cast_nonneg (α := ℝ) M]

/-- Positivity and unit bound `0 < recordCoherenceOffLine M ≤ 1`. -/
theorem recordCoherenceOffLine_pos_le_one (M : ℕ) :
    0 < recordCoherenceOffLine M ∧ recordCoherenceOffLine M ≤ 1 := by
  unfold recordCoherenceOffLine explicitCoherence
  refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
  have : (0 : ℝ) ≤ 10 * ((M : ℝ) + 1) * (25 / 16 * M) := by positivity
  linarith

/-- **Two-sided bounds on `recordOrderOffLine M w a`.** For `a > 0`, the unmodulated off-line Fejér
order `recordOrderOffLine M w a` satisfies both `2 M² log(M + 1) / log 2 ≤ recordOrderOffLine M w a`
and `log(recordNoiseOffLine M w a) / log 2 ≤ recordOrderOffLine M w a`, and is bounded above by
`M + 2 + explicitOrderLog (recordNoiseOffLine M w a) (recordCoherenceOffLine M) M / log 2`. -/
theorem recordOrderOffLine_two_sided (M : ℕ) (w : ℝ) {a : ℝ} (ha : 0 < a) :
    2 * (M : ℝ) ^ 2 * Real.log (M + 1) / Real.log 2 ≤ (recordOrderOffLine M w a : ℝ) ∧
      Real.log (recordNoiseOffLine M w a) / Real.log 2 ≤ (recordOrderOffLine M w a : ℝ) ∧
      (recordOrderOffLine M w a : ℝ) ≤ M + 2 +
        explicitOrderLog (recordNoiseOffLine M w a) (recordCoherenceOffLine M) M / Real.log 2 := by
  obtain ⟨hc0, hc1⟩ := recordCoherenceOffLine_pos_le_one M
  have hN := one_le_recordNoiseOffLine M w ha
  unfold recordOrderOffLine
  exact ⟨le_explicitOrder hN hc0 hc1 M,
    log_noise_le_explicitOrder (lt_of_lt_of_le zero_lt_one hN) hc0 hc1 M,
    explicitOrder_le hN hc0 hc1 M⟩

/-- **Two-sided law for `recordLagOffLine M w a σ`.** Under `OffLineCopiesLocallyBounded M`, for
`a > 0` and `σ > 0`, `recordLagOffLine M w a σ` is sandwiched between explicit multiples of
`log(recordNoiseOffLine M w a) / σ + 1 / √a` and
`explicitOrderLog(recordNoiseOffLine M w a, recordCoherenceOffLine M, M) / σ + 1 / √a`, with zero
dependence on the height of any zero. -/
theorem recordLagOffLine_two_sided (M : ℕ) (w : ℝ) {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    4 / σ * (13 * π * (Real.log (recordNoiseOffLine M w a) / Real.log 2) + 4) +
        w + 8 * w * Real.exp (w / 2) * bumpMass w / recordScaleOffLine M a ≤
      recordLagOffLine M w a σ ∧
    recordLagOffLine M w a σ ≤
      4 / σ * (13 * π * (M + 2 +
        explicitOrderLog (recordNoiseOffLine M w a) (recordCoherenceOffLine M) M / Real.log 2) + 4) +
        w + 8 * w * Real.exp (w / 2) * bumpMass w / recordScaleOffLine M a := by
  obtain ⟨_, hlo, hhi⟩ := recordOrderOffLine_two_sided M w ha
  unfold recordLagOffLine
  constructor <;> gcongr

/-- For `w > 0` and `W_on ≥ 0`, `1 ≤ nearTopNoiseOffLine M w W_on`. -/
theorem one_le_nearTopNoiseOffLine (M : ℕ) {w W_on : ℝ} (hw : 0 < w) (hW : 0 ≤ W_on) :
    1 ≤ nearTopNoiseOffLine M w W_on := by
  unfold nearTopNoiseOffLine
  have ha0 : 0 < centerAmplitude w ^ 2 / (2 * Real.exp 1) := by
    have := centerAmplitude_pos hw; positivity
  have he : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
  have h1 : 0 ≤ 4 * (2 * W_on + 48 * (M : ℝ) ^ 2 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2) /
      ((Real.exp 1 - 1) * (centerAmplitude w ^ 2 / (2 * Real.exp 1))) := by positivity
  linarith [Nat.cast_nonneg (α := ℝ) M]

/-- For `w > 0`, `nearTopNoiseOffLine M w W_on` dominates
`16 e · W_on / ((e - 1) a_w²) + 1`. -/
theorem div_centerAmplitude_sq_le_nearTopNoiseOffLine (M : ℕ) {w : ℝ} (hw : 0 < w)
    (W_on : ℝ) :
    16 * Real.exp 1 * W_on / ((Real.exp 1 - 1) * centerAmplitude w ^ 2) + 1 ≤
      nearTopNoiseOffLine M w W_on := by
  unfold nearTopNoiseOffLine
  have ha0 : 0 < centerAmplitude w ^ 2 := sq_pos_of_pos (centerAmplitude_pos hw)
  have he : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
  have hK : 0 ≤ 48 * (M : ℝ) ^ 2 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := by positivity
  have h1 : 16 * Real.exp 1 * W_on / ((Real.exp 1 - 1) * centerAmplitude w ^ 2) =
      4 * (2 * W_on) / ((Real.exp 1 - 1) * (centerAmplitude w ^ 2 / (2 * Real.exp 1))) := by
    field_simp; ring
  have h2 : 4 * (2 * W_on) / ((Real.exp 1 - 1) * (centerAmplitude w ^ 2 / (2 * Real.exp 1))) ≤
      4 * (2 * W_on + 48 * (M : ℝ) ^ 2 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2) /
        ((Real.exp 1 - 1) * (centerAmplitude w ^ 2 / (2 * Real.exp 1))) := by
    gcongr; linarith
  linarith [Nat.cast_nonneg (α := ℝ) M]

/-- Positivity and unit bound `0 < nearTopCoherenceOffLine M w ≤ 1` for `w > 0`. -/
theorem nearTopCoherenceOffLine_pos_le_one (M : ℕ) {w : ℝ} (hw : 0 < w) :
    0 < nearTopCoherenceOffLine M w ∧ nearTopCoherenceOffLine M w ≤ 1 := by
  have ha0 : 0 < centerAmplitude w ^ 2 / (2 * Real.exp 1) := by
    have := centerAmplitude_pos hw; positivity
  unfold nearTopCoherenceOffLine explicitCoherence
  refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
  have : 0 ≤ 10 * ((M : ℝ) + 1) * (2 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2) := by
    positivity
  linarith

/-- **Two-sided bounds on `nearTopOrderOffLine M w W_on`: `Θ_{M,w}(1 + log⁺ W_on)`.** -/
theorem nearTopOrderOffLine_two_sided (M : ℕ) {w W_on : ℝ} (hw : 0 < w) (hW : 0 ≤ W_on) :
    Real.log (nearTopNoiseOffLine M w W_on) / Real.log 2 ≤ (nearTopOrderOffLine M w W_on : ℝ) ∧
      (nearTopOrderOffLine M w W_on : ℝ) ≤ M + 2 +
        explicitOrderLog (nearTopNoiseOffLine M w W_on) (nearTopCoherenceOffLine M w) M /
          Real.log 2 := by
  obtain ⟨hc0, hc1⟩ := nearTopCoherenceOffLine_pos_le_one M hw
  have hN := one_le_nearTopNoiseOffLine M hw hW
  unfold nearTopOrderOffLine
  exact ⟨log_noise_le_explicitOrder (lt_of_lt_of_le zero_lt_one hN) hc0 hc1 M,
    explicitOrder_le hN hc0 hc1 M⟩

/-- **Two-sided law for `nearTopLagOffLine M w W_on δ₀`: `Θ_{M,w}((1 + log⁺ W_on) / δ₀)`.**
For `w > 0`, `W_on ≥ 0`, and `δ₀ > 0`, `nearTopLagOffLine M w W_on δ₀` is bounded both below and
above by explicit affine functions of `log(nearTopNoiseOffLine M w W_on) / δ₀` (note that
`explicitOrderLog` depends on `W_on` exclusively through `Real.log (nearTopNoiseOffLine M w W_on)`). -/
theorem nearTopLagOffLine_two_sided (M : ℕ) {w W_on δ₀ : ℝ} (hw : 0 < w) (hW : 0 ≤ W_on)
    (hδ₀ : 0 < δ₀) :
    8 / δ₀ * (13 * π * (Real.log (nearTopNoiseOffLine M w W_on) / Real.log 2) + 4 +
        |Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)|) +
        w + 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScaleOffLine M w ≤
      nearTopLagOffLine M w W_on δ₀ ∧
    nearTopLagOffLine M w W_on δ₀ ≤
      8 / δ₀ * (13 * π * (M + 2 +
        explicitOrderLog (nearTopNoiseOffLine M w W_on) (nearTopCoherenceOffLine M w) M /
          Real.log 2) + 4 +
        |Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)|) +
        w + 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScaleOffLine M w := by
  obtain ⟨hlo, hhi⟩ := nearTopOrderOffLine_two_sided M hw hW
  unfold nearTopLagOffLine
  constructor <;> gcongr

/-- **Two-sided doubly-logarithmic law for `nearTopLogLogLagOffLine M w γ₀ δ₀`:
`Θ_{M,w}((1 + log log(|γ₀| + 4)) / δ₀)`.** -/
theorem nearTopLogLogLagOffLine_two_sided (M : ℕ) {w γ₀ δ₀ : ℝ} (hw : 0 < w) (hδ₀ : 0 < δ₀) :
    let W_log := 16 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log (|γ₀| + 4))
    8 / δ₀ * (13 * π * (Real.log (nearTopNoiseOffLine M w W_log) / Real.log 2) + 4 +
        |Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)|) +
        w + 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScaleOffLine M w ≤
      nearTopLogLogLagOffLine M w γ₀ δ₀ ∧
    nearTopLogLogLagOffLine M w γ₀ δ₀ ≤
      8 / δ₀ * (13 * π * (M + 2 +
        explicitOrderLog (nearTopNoiseOffLine M w W_log) (nearTopCoherenceOffLine M w) M /
          Real.log 2) + 4 +
        |Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)|) +
        w + 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScaleOffLine M w := by
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hlog : 0 ≤ Real.log (|γ₀| + 4) := Real.log_nonneg (by linarith [abs_nonneg γ₀])
  have hW : 0 ≤ 16 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log (|γ₀| + 4)) := by positivity
  unfold nearTopLogLogLagOffLine
  exact nearTopLagOffLine_two_sided M hw hW hδ₀

/-! ### 3. Intrinsic optimality of the doubly-logarithmic aperture: the on-line mass barrier
and the all-test Hodge-defect threshold -/

/-- The on-line cosine lag sum `∑_{Re z = 0} ‖evenCoeff ζ (modScaledBump w c) z‖ cos(Im z · v)`
at lag `v ∈ ℝ`. -/
def onLineLagStructure (w c v : ℝ) : ℝ :=
  ∑' z : ℂ, if z.re = 0 then
    ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ * Real.cos (z.im * v) else 0

/-- The off-line lag sum `∑_{Re z ≠ 0} Re (evenCoeff ζ (modScaledBump w c) z · e^{z v})` at lag `v`. -/
def offLineLagStructure (w c v : ℝ) : ℝ :=
  ∑' z : ℂ, if z.re = 0 then 0 else
    (evenCoeff zetaZeroConfig (modScaledBump w c) z * Complex.exp (z * (v : ℂ))).re

/-- **Exact on-line/off-line decomposition of `2 Re S(v)` at any lag `v`.** Because every on-line
exponent `z = i γ` (`Re z = 0`) has real nonnegative coefficient `D_c(z) = ‖D_c(z)‖` and
`Re(e^{i γ v}) = cos(γ v)`, `2 Re S(v) = onLineLagStructure w c v + offLineLagStructure w c v`. -/
theorem two_re_lagStructure_eq_onLine_add_offLine {w : ℝ} (hw : 0 < w) (c v : ℝ) :
    2 * (lagStructure zetaZeroConfig (modScaledBump w c) v).re =
      onLineLagStructure w c v + offLineLagStructure w c v := by
  classical
  set b := modScaledBump w c with hb
  set D := evenCoeff zetaZeroConfig b with hD
  have hv := two_re_lagStructure_eq zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c) v
  have hs_re : Summable (fun z : ℂ => (D z * Complex.exp (z * (v : ℂ))).re) :=
    (Complex.hasSum_re hv.1.hasSum).summable
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c)
  have hs_on : Summable (fun z : ℂ => if z.re = 0 then ‖D z‖ * Real.cos (z.im * v) else 0) :=
    hsD.of_norm_bounded (fun z => by
      split_ifs
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
      · rw [norm_zero]; exact norm_nonneg _)
  have hs_off : Summable (fun z : ℂ => if z.re = 0 then 0 else
      (D z * Complex.exp (z * (v : ℂ))).re) :=
    hs_re.norm.of_norm_bounded (fun z => by
      split_ifs
      · rw [norm_zero]; exact norm_nonneg _
      · exact le_rfl)
  have hterm : ∀ z : ℂ, (D z * Complex.exp (z * (v : ℂ))).re =
      (if z.re = 0 then ‖D z‖ * Real.cos (z.im * v) else 0) +
        (if z.re = 0 then 0 else (D z * Complex.exp (z * (v : ℂ))).re) := by
    intro z
    by_cases hz : z.re = 0
    · rw [if_pos hz, if_pos hz, add_zero]
      have hd_eq : D z = ((‖D z‖ : ℝ) : ℂ) := by
        rw [hD, hb]
        exact evenCoeff_modScaledBump_onLine_eq_norm zetaZeroConfig hw c hz
      have hexp : z * (v : ℂ) = ((z.im * v : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp [hz]
      calc (D z * Complex.exp (z * (v : ℂ))).re
          = (((‖D z‖ : ℝ) : ℂ) * Complex.exp (((z.im * v : ℝ) : ℂ) * I)).re := by
            congr 1; rw [hexp]; exact congrArg (· * _) hd_eq
        _ = ‖D z‖ * Real.cos (z.im * v) := by
            rw [Complex.re_ofReal_mul, Complex.exp_mul_I, Complex.add_re,
              Complex.cos_ofReal_re, Complex.mul_I_re, Complex.sin_ofReal_im, neg_zero, add_zero]
    · rw [if_neg hz, if_neg hz, zero_add]
  have hre_eq : 2 * (lagStructure zetaZeroConfig b v).re =
      ∑' z : ℂ, (D z * Complex.exp (z * (v : ℂ))).re := by
    have h1 := congrArg Complex.re hv.2
    rw [Complex.ofReal_re, Complex.re_tsum hv.1] at h1
    exact h1
  calc 2 * (lagStructure zetaZeroConfig b v).re
      = ∑' z : ℂ, (D z * Complex.exp (z * (v : ℂ))).re := hre_eq
    _ = ∑' z : ℂ, ((if z.re = 0 then ‖D z‖ * Real.cos (z.im * v) else 0) +
          (if z.re = 0 then 0 else (D z * Complex.exp (z * (v : ℂ))).re)) :=
        tsum_congr hterm
    _ = onLineLagStructure w c v + offLineLagStructure w c v :=
        Summable.tsum_add hs_on hs_off

/-- **Bound on `|offLineLagStructure w c v|` under a zero-width bound `δ₀`.** If every off-line zero
of `ζ` has depth `|Re ρ - ½| ≤ δ₀`, then for every `v ≥ 0`,
`|offLineLagStructure w c v| ≤ offLineEvenMass w c · e^{δ₀ v}`. -/
theorem abs_offLineLagStructure_le_of_depth_le {w c v δ₀ : ℝ} (hw : 0 < w) (hv : 0 ≤ v)
    (hdepth : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ δ₀) :
    |offLineLagStructure w c v| ≤ offLineEvenMass w c * Real.exp (δ₀ * v) := by
  classical
  set b := modScaledBump w c with hb
  set D := evenCoeff zetaZeroConfig b with hD
  have hv_eq := two_re_lagStructure_eq zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c) v
  have hs_re : Summable (fun z : ℂ => (D z * Complex.exp (z * (v : ℂ))).re) :=
    (Complex.hasSum_re hv_eq.1.hasSum).summable
  have hs_off : Summable (fun z : ℂ => if z.re = 0 then 0 else
      (D z * Complex.exp (z * (v : ℂ))).re) :=
    hs_re.norm.of_norm_bounded (fun z => by
      split_ifs
      · rw [norm_zero]; exact norm_nonneg _
      · exact le_rfl)
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c)
  have hs_mass : Summable (fun z : ℂ => if z.re = 0 then 0 else ‖D z‖) :=
    hsD.of_nonneg_of_le (fun z => by split_ifs <;> positivity)
      (fun z => by split_ifs <;> [exact norm_nonneg _; exact le_rfl])
  have hle : ∀ z : ℂ, ‖if z.re = 0 then (0 : ℝ) else (D z * Complex.exp (z * (v : ℂ))).re‖ ≤
      (if z.re = 0 then 0 else ‖D z‖) * Real.exp (δ₀ * v) := by
    intro z
    by_cases hz : z.re = 0
    · simp [hz]
    · rw [if_neg hz, if_neg hz, Real.norm_eq_abs]
      by_cases hDz : D z = 0
      · simp [hDz]
      · have hmem := add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hDz
        have hd := hdepth (1 / 2 + z) hmem
        have hre : (1 / 2 + z).re - 1 / 2 = z.re := by simp
        rw [hre] at hd
        have hexp : Real.exp (z.re * v) ≤ Real.exp (δ₀ * v) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hd) hv)
        calc |(D z * Complex.exp (z * (v : ℂ))).re|
            ≤ ‖D z * Complex.exp (z * (v : ℂ))‖ := Complex.abs_re_le_norm _
          _ = ‖D z‖ * Real.exp (z.re * v) := by
              rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
                Complex.ofReal_im, mul_zero, sub_zero]
          _ ≤ ‖D z‖ * Real.exp (δ₀ * v) := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
  calc |offLineLagStructure w c v|
      = ‖∑' z : ℂ, if z.re = 0 then (0 : ℝ) else (D z * Complex.exp (z * (v : ℂ))).re‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' z : ℂ, ‖if z.re = 0 then (0 : ℝ) else (D z * Complex.exp (z * (v : ℂ))).re‖ :=
        norm_tsum_le_tsum_norm hs_off.norm
    _ ≤ ∑' z : ℂ, (if z.re = 0 then 0 else ‖D z‖) * Real.exp (δ₀ * v) :=
        Summable.tsum_le_tsum hle hs_off.norm (hs_mass.mul_right _)
    _ = offLineEvenMass w c * Real.exp (δ₀ * v) := tsum_mul_right

/-- Exact identity `Re W(twoBump b v (-1)) = 2 Re S(0) - 2 Re S(v)` for a tempered configuration. -/
theorem re_W_twoBump_neg_one_eq (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re =
      2 * (lagStructure Z b 0).re - 2 * (lagStructure Z b v).re := by
  have hX : lagStructure Z b v + conj (lagStructure Z b (-v)) = 2 * lagStructure Z b v := by
    rw [conj_lagStructure_neg Z hZ hb hbs v]; ring
  rw [re_W_unit_twoBump Z hZ hb hbs v (by simp), hX]
  simp only [neg_mul, one_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero]
  ring

/-- **On-line mass lower bound for the Weil difference test `twoBump (modScaledBump w c) v (-1)`.**
If all zeros of `ζ` have depth `|Re ρ - ½| ≤ δ₀`, then for every lag `v ≥ 0`,
`Re W(twoBump (modScaledBump w c) v (-1)) ≥ (onLineEvenMass w c - onLineLagStructure w c v) - offLineEvenMass w c · (e^{δ₀ v} + 1)`.
In particular, the positive on-line contribution `onLineEvenMass w c - onLineLagStructure w c v`
must be overcome by the exponentially growing off-line term `offLineEvenMass w c · (e^{δ₀ v} + 1)`
before the difference test can become negative. -/
theorem re_W_twoBump_modScaledBump_ge_onLineEvenMass_sub (c : ℝ) {w v δ₀ : ℝ} (hw : 0 < w)
    (hv : 0 ≤ v)
    (hdepth : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ δ₀) :
    (onLineEvenMass w c - onLineLagStructure w c v) -
        offLineEvenMass w c * (Real.exp (δ₀ * v) + 1) ≤
      (zetaZeroConfig.W (twoBump (modScaledBump w c) v (-1))
        (twoBump (modScaledBump w c) v (-1))).re := by
  have hW := re_W_twoBump_neg_one_eq zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c) v
  have h0 := two_re_lagStructure_eq_onLine_add_offLine hw c 0
  have hv_eq := two_re_lagStructure_eq_onLine_add_offLine hw c v
  have hon0 : onLineLagStructure w c 0 = onLineEvenMass w c := by
    unfold onLineLagStructure onLineEvenMass
    refine tsum_congr fun z => ?_
    split_ifs <;> simp
  rw [hon0] at h0
  have hoff0 := abs_offLineLagStructure_le_of_depth_le (c := c) hw (le_refl 0) hdepth
  simp only [mul_zero, Real.exp_zero, mul_one] at hoff0
  have hoffv := abs_offLineLagStructure_le_of_depth_le (c := c) hw hv hdepth
  linarith [hW, h0, hv_eq, (abs_le.mp hoff0).1, (abs_le.mp hoffv).2]

/-- **Phase-incoherence lag barrier (`Ω((log log c) / δ₀)` lower bound for difference tests).**
Suppose all zeros of `ζ` have depth `|Re ρ - ½| ≤ δ₀` (`δ₀ > 0`), and at lag `v ≥ 0` the on-line
cosine sum is `θ`-decoherent (`onLineLagStructure w c v ≤ (1 - θ) · onLineEvenMass w c` with
`0 < θ ≤ 1`). If `0 < offLineEvenMass w c` and
`v ≤ (1 / δ₀) · log(θ · onLineEvenMass w c / offLineEvenMass w c - 1)`, then
`0 ≤ Re W(twoBump (modScaledBump w c) v (-1))`: no negative Weil value can occur at lag `v`.
Under `OffLineCopiesLocallyBounded M` (`offLineEvenMass w c ≤ 24 M² K₀`) and the Riemann–von
Mangoldt lower bound `onLineEvenMass w c ≥ c_w log c` of §1, this barrier scale is
`(1 / δ₀) log(θ c_w log c / (24 M² K₀) - 1) = Ω_{w,M}((log log c) / δ₀)`. -/
theorem re_W_twoBump_modScaledBump_nonneg_of_lag_le_log_ratio {w c v δ₀ θ : ℝ} (hw : 0 < w)
    (hv : 0 ≤ v) (hδ₀ : 0 < δ₀)
    (hdepth : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ δ₀)
    (hdec : onLineLagStructure w c v ≤ (1 - θ) * onLineEvenMass w c)
    (hoff_pos : 0 < offLineEvenMass w c)
    (hratio : 1 < θ * onLineEvenMass w c / offLineEvenMass w c)
    (hv_le : v ≤ (1 / δ₀) * Real.log (θ * onLineEvenMass w c / offLineEvenMass w c - 1)) :
    0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w c) v (-1))
      (twoBump (modScaledBump w c) v (-1))).re := by
  have hlow := re_W_twoBump_modScaledBump_ge_onLineEvenMass_sub c hw hv hdepth
  have h1 : θ * onLineEvenMass w c ≤ onLineEvenMass w c - onLineLagStructure w c v := by linarith
  have h2 : δ₀ * v ≤ Real.log (θ * onLineEvenMass w c / offLineEvenMass w c - 1) := by
    have := mul_le_mul_of_nonneg_left hv_le hδ₀.le
    rwa [← mul_assoc, mul_one_div_cancel hδ₀.ne', one_mul] at this
  have h3 : Real.exp (δ₀ * v) ≤ θ * onLineEvenMass w c / offLineEvenMass w c - 1 := by
    rw [← Real.exp_log (by linarith : 0 < θ * onLineEvenMass w c / offLineEvenMass w c - 1)]
    exact Real.exp_le_exp.mpr h2
  have h4 : offLineEvenMass w c * (Real.exp (δ₀ * v) + 1) ≤ θ * onLineEvenMass w c := by
    have := mul_le_mul_of_nonneg_left (by linarith : Real.exp (δ₀ * v) + 1 ≤
      θ * onLineEvenMass w c / offLineEvenMass w c) hoff_pos.le
    rwa [mul_div_cancel₀ _ hoff_pos.ne'] at this
  linarith

/-- The Riemann–von Mangoldt local on-line zero density `L(γ₀) = (1 / 2π) log(γ₀ / 2π)` at height `γ₀`. -/
def rvmLocalDensity (γ₀ : ℝ) : ℝ :=
  (1 / (2 * π)) * Real.log (γ₀ / (2 * π))

/-- For `2π < γ₀`, `0 < rvmLocalDensity γ₀`. -/
theorem rvmLocalDensity_pos {γ₀ : ℝ} (hγ₀ : 2 * π < γ₀) : 0 < rvmLocalDensity γ₀ := by
  unfold rvmLocalDensity
  have h1 : 1 < γ₀ / (2 * π) := (one_lt_div (by positivity)).mpr hγ₀
  have h2 : 0 < Real.log (γ₀ / (2 * π)) := Real.log_pos h1
  positivity

/-- **All-test Hodge-defect invisibility below the doubly-logarithmic aperture.** In
`isolatedPairConfig (rvmLocalDensity_pos hγ₀) hδ₀ hδ₀1 γ₀` (an isolated off-line pair at depth `δ₀`
and height `γ₀` in an on-line background of Riemann–von Mangoldt local density
`L = (1/2π) log(γ₀/2π)`), every `C²` test supported in `[-a, a]` has nonnegative Weil form
(`hodgeDefectAt = 0`) for all `0 < a ≤ rvmLocalDensity γ₀ / 2` with
`a ≤ (1 / (2 δ₀)) log(4 δ₀ · rvmLocalDensity γ₀) = Θ((log log γ₀) / δ₀)`. -/
theorem hodgeDefectAt_isolatedPair_rvmDensity_eq_zero {γ₀ δ₀ a : ℝ} (hγ₀ : 2 * π < γ₀)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1 / 2) (ha : 0 < a) (haL : a ≤ rvmLocalDensity γ₀ / 2)
    (ha_le : a ≤ (1 / (2 * δ₀)) * Real.log (4 * δ₀ * rvmLocalDensity γ₀)) :
    hodgeDefectAt (isolatedPairConfig (rvmLocalDensity_pos hγ₀) hδ₀ hδ₀1 γ₀) a = 0 := by
  rw [hodgeDefectAt_isolatedPair (rvmLocalDensity_pos hγ₀) hδ₀ hδ₀1 γ₀ ha haL, if_pos]
  have hL0 := rvmLocalDensity_pos hγ₀
  have h1 : 2 * δ₀ * a ≤ Real.log (4 * δ₀ * rvmLocalDensity γ₀) := by
    have := mul_le_mul_of_nonneg_left ha_le (by positivity : 0 ≤ 2 * δ₀)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity : 2 * δ₀ ≠ 0), one_mul] at this
  have h2 : Real.exp (2 * δ₀ * a) ≤ 4 * δ₀ * rvmLocalDensity γ₀ := by
    rw [← Real.exp_log (by positivity : 0 < 4 * δ₀ * rvmLocalDensity γ₀)]
    exact Real.exp_le_exp.mpr h1
  have hsinh : Real.sinh (2 * δ₀ * a) ≤ 2 * δ₀ * rvmLocalDensity γ₀ := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (-(2 * δ₀ * a))
    linarith
  have hdiv : Real.sinh (2 * δ₀ * a) / δ₀ ≤ 2 * rvmLocalDensity γ₀ := by
    rw [div_le_iff₀ hδ₀]
    linarith
  linarith

/-- **All-test Hodge-defect visibility above the doubly-logarithmic aperture.** In
`isolatedPairConfig (rvmLocalDensity_pos hγ₀) hδ₀ hδ₀1 γ₀`, the Hodge defect equals `1` at every
degree `a` in the range
`(1 / (2 δ₀)) log(6 δ₀ · rvmLocalDensity γ₀ + 1) < a ≤ rvmLocalDensity γ₀ / 2`.
Together with `hodgeDefectAt_isolatedPair_rvmDensity_eq_zero`, this proves that the
doubly-logarithmic scale `Θ((log log γ₀) / δ₀)` is the exact visibility threshold across all
compactly supported `C²` test functions when the local on-line density is `Θ(log γ₀)`. -/
theorem hodgeDefectAt_isolatedPair_rvmDensity_eq_one {γ₀ δ₀ a : ℝ} (hγ₀ : 2 * π < γ₀)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1 / 2)
    (ha_lo : (1 / (2 * δ₀)) * Real.log (6 * δ₀ * rvmLocalDensity γ₀ + 1) < a)
    (ha_hi : a ≤ rvmLocalDensity γ₀ / 2) :
    hodgeDefectAt (isolatedPairConfig (rvmLocalDensity_pos hγ₀) hδ₀ hδ₀1 γ₀) a = 1 := by
  have hL0 := rvmLocalDensity_pos hγ₀
  have hlog0 : 0 < Real.log (6 * δ₀ * rvmLocalDensity γ₀ + 1) :=
    Real.log_pos (by linarith [mul_pos hδ₀ hL0])
  have ha : 0 < a := lt_trans (by positivity) ha_lo
  rw [hodgeDefectAt_isolatedPair (rvmLocalDensity_pos hγ₀) hδ₀ hδ₀1 γ₀ ha ha_hi, if_neg]
  intro hle
  have h1 : Real.log (6 * δ₀ * rvmLocalDensity γ₀ + 1) < 2 * δ₀ * a := by
    have := mul_lt_mul_of_pos_left ha_lo (by positivity : 0 < 2 * δ₀)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity : 2 * δ₀ ≠ 0), one_mul] at this
  have h2 : 6 * δ₀ * rvmLocalDensity γ₀ + 1 < Real.exp (2 * δ₀ * a) := by
    rw [← Real.exp_log (by positivity : 0 < 6 * δ₀ * rvmLocalDensity γ₀ + 1)]
    exact Real.exp_lt_exp.mpr h1
  have hexp_neg : Real.exp (-(2 * δ₀ * a)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hsinh : 3 * δ₀ * rvmLocalDensity γ₀ < Real.sinh (2 * δ₀ * a) := by
    rw [Real.sinh_eq]
    linarith
  have hdiv : 3 * rvmLocalDensity γ₀ < Real.sinh (2 * δ₀ * a) / δ₀ := by
    rw [lt_div_iff₀ hδ₀]
    linarith
  linarith

/-! ### 4. Modulated contact-aperture bridge and excluded-depth laws under `OffLineCopiesLocallyBounded M` -/

/-- Support inclusion for the difference test `twoBump (modScaledBump w c) v (-1)` at an arbitrary
modulation center `c ∈ ℝ`: `tsupport ⊆ [-(v/2 + w), v/2 + w]`. -/
theorem tsupport_twoBump_modScaledBump_subset_any (c : ℝ) {w v : ℝ} (hw : 0 < w) (hv0 : 0 ≤ v) :
    tsupport (twoBump (modScaledBump w c) v (-1)) ⊆ Icc (-(v / 2 + w)) (v / 2 + w) := by
  have hbs := modScaledBump_support hw c
  refine closure_minimal (fun t ht => ?_) isClosed_Icc
  have ht' : twoBump (modScaledBump w c) v (-1) t ≠ 0 := ht
  rw [twoBump_apply] at ht'
  by_cases h1 : modScaledBump w c (t + v / 2) = 0
  · have h2 : modScaledBump w c (t - v / 2) ≠ 0 := fun h => ht' (by rw [h1, h]; ring)
    obtain ⟨h3, h4⟩ := abs_le.mp (hbs _ h2)
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨h3, h4⟩ := abs_le.mp (hbs _ h1)
    exact ⟨by linarith, by linarith⟩

/-- **Rayleigh ground-energy bridge for modulated difference tests.** At any modulation center
`c ∈ ℝ`, a negative Weil value `Re W_ζ(twoBump (modScaledBump w c) v (-1)) < 0` (`w > 0`, `v ≥ 0`)
forces `ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, _⟩ < 0`. -/
theorem ccmRestrictedWeilGroundEnergy_neg_of_re_W_twoBump_modScaledBump_neg (c : ℝ) {w v : ℝ}
    (hw : 0 < w) (hv : 0 ≤ v)
    (hneg : (zetaZeroConfig.W (twoBump (modScaledBump w c) v (-1))
      (twoBump (modScaledBump w c) v (-1))).re < 0) :
    ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by positivity⟩ < 0 := by
  have h := ccmRestrictedWeilGroundEnergy_mul_integral_norm_sq_le_re_W
    (A := ⟨v / 2 + w, by positivity⟩)
    (contDiff_top_bumpTest (contDiff_top_modScaledBump w c) v ![1, -1])
    (tsupport_twoBump_modScaledBump_subset_any c hw hv)
  refine lt_of_not_ge fun hcon => ?_
  have hI : 0 ≤ ∫ t, ‖twoBump (modScaledBump w c) v (-1) t‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  exact absurd (lt_of_le_of_lt h hneg) (not_lt.mpr (mul_nonneg hcon hI))

/-- **Doubly-logarithmic contact-aperture upper bound under `OffLineCopiesLocallyBounded M`.**
Any `1/V`-near-top zero `½ + z₀` right of the line above `nearTopHeightOffLine M w` with
`V ≥ nearTopLogLogLagOffLine M w z₀.im z₀.re` forces `ccmRestrictedWeilGroundEnergy A < 0` for all
`A ≥ V / 2 + w`, and hence `zetaContactAperture ≤ V / 2 + w`. -/
theorem zetaContactAperture_le_of_near_top_loglog_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeightOffLine M w ≤ z₀.im)
    {V : ℝ} (hV : nearTopLogLogLagOffLine M w z₀.im z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    zetaContactAperture ≤ V / 2 + w := by
  refine csSup_le groundEnergyNonnegApertures_nonempty fun A hA => ?_
  obtain ⟨hA0, hμ⟩ := hA
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv, hneg⟩ :=
    zeta_near_top_visible_at_loglog_lag_of_offLineCopiesLocallyBounded hM hw hz₀ hre₀ hTw hV htop
  have h1 := ccmRestrictedWeilGroundEnergy_neg_of_re_W_twoBump_modScaledBump_neg z₀.im hw hv.1 hneg
  have h2 := ccmRestrictedWeilGroundEnergy_antitone (a := ⟨v / 2 + w, by have := hv.1; positivity⟩)
    (b := ⟨A, hA0⟩) (show v / 2 + w ≤ A by linarith [hv.2])
  exact absurd hμ (not_le.mpr (lt_of_le_of_lt h2 h1))

/-- The height-free depth numerator `4 (13 π k_off(M, w, a) + 4)` of `recordLagOffLine M w a σ`.
Because `recordOrderOffLine M w a` is independent of `σ`, `recordLagOffLine` is an exact affine
function of `1 / σ`. -/
def recordLagNumeratorOffLine (M : ℕ) (w a : ℝ) : ℝ :=
  4 * (13 * π * recordOrderOffLine M w a + 4)

/-- The height-free phase-coherence drift `w + 8 w e^{w/2} J_w / recordScaleOffLine M a` of
`recordLagOffLine`. -/
def recordCoherenceDriftOffLine (M : ℕ) (w a : ℝ) : ℝ :=
  w + 8 * w * Real.exp (w / 2) * bumpMass w / recordScaleOffLine M a

/-- Exact affine-in-`1/σ` decomposition of `recordLagOffLine`. -/
theorem recordLagOffLine_eq_div_add_drift (M : ℕ) (w a σ : ℝ) :
    recordLagOffLine M w a σ =
      recordLagNumeratorOffLine M w a / σ + recordCoherenceDriftOffLine M w a := by
  unfold recordLagOffLine recordLagNumeratorOffLine recordCoherenceDriftOffLine
  ring

/-- The height-free excluded depth `recordExcludedDepthOffLine M w a V` at lag budget
`V > recordCoherenceDriftOffLine M w a`. -/
def recordExcludedDepthOffLine (M : ℕ) (w a V : ℝ) : ℝ :=
  recordLagNumeratorOffLine M w a / (V - recordCoherenceDriftOffLine M w a)

/-- Exact inversion `recordLagOffLine M w a σ ≤ V ↔ recordExcludedDepthOffLine M w a V ≤ σ`
whenever `recordCoherenceDriftOffLine M w a < V` and `0 < σ`. -/
theorem recordLagOffLine_le_iff_le_recordExcludedDepthOffLine (M : ℕ) (w a : ℝ) {σ V : ℝ}
    (hσ : 0 < σ) (hV : recordCoherenceDriftOffLine M w a < V) :
    recordLagOffLine M w a σ ≤ V ↔ recordExcludedDepthOffLine M w a V ≤ σ := by
  rw [recordLagOffLine_eq_div_add_drift, recordExcludedDepthOffLine, ← le_sub_iff_add_le,
    div_le_iff₀ hσ, div_le_iff₀ (sub_pos.mpr hV), mul_comm]

/-- The depth numerator of `nearTopLagOffLine M w W_on δ₀`:
`8 (13 π nearTopOrderOffLine M w W_on + 4 + |log(4 M (e^{w/2} B_w)² / a_w²)|)`.
Because `nearTopOrderOffLine M w W_on` does not depend on `δ₀`, `nearTopLagOffLine` is an exact
affine function of `1 / δ₀`. -/
def nearTopLagNumeratorOffLine (M : ℕ) (w W_on : ℝ) : ℝ :=
  8 * (13 * π * nearTopOrderOffLine M w W_on + 4 +
    |Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)|)

/-- The height-free phase-coherence drift `w + 8 w e^{w/2} J_w / nearTopScaleOffLine M w` of
`nearTopLagOffLine` and `nearTopLogLogLagOffLine`. -/
def nearTopCoherenceDriftOffLine (M : ℕ) (w : ℝ) : ℝ :=
  w + 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScaleOffLine M w

/-- Exact affine-in-`1/δ₀` decomposition of `nearTopLagOffLine`. -/
theorem nearTopLagOffLine_eq_div_add_drift (M : ℕ) (w W_on δ₀ : ℝ) :
    nearTopLagOffLine M w W_on δ₀ =
      nearTopLagNumeratorOffLine M w W_on / δ₀ + nearTopCoherenceDriftOffLine M w := by
  unfold nearTopLagOffLine nearTopLagNumeratorOffLine nearTopCoherenceDriftOffLine
  ring

/-- Positivity of `nearTopLagNumeratorOffLine M w W_on`. -/
theorem nearTopLagNumeratorOffLine_pos (M : ℕ) (w W_on : ℝ) :
    0 < nearTopLagNumeratorOffLine M w W_on := by
  unfold nearTopLagNumeratorOffLine
  have h1 : (0 : ℝ) ≤ 13 * π * nearTopOrderOffLine M w W_on := by positivity
  have h2 : (0 : ℝ) ≤ |Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
      centerAmplitude w ^ 2)| := abs_nonneg _
  linarith

/-- **The off-line near-top excluded depth `nearTopExcludedDepthOffLine M w W_on V`** at lag budget
`V > nearTopCoherenceDriftOffLine M w`. Because `nearTopLagNumeratorOffLine M w W_on` is independent
of `δ₀`, this is the exact closed-form inverse of `δ₀ ↦ nearTopLagOffLine M w W_on δ₀`. -/
def nearTopExcludedDepthOffLine (M : ℕ) (w W_on V : ℝ) : ℝ :=
  nearTopLagNumeratorOffLine M w W_on / (V - nearTopCoherenceDriftOffLine M w)

/-- **The doubly-logarithmic near-top excluded depth `nearTopLogLogExcludedDepthOffLine M w γ₀ V`**
at height `γ₀` and lag budget `V > nearTopCoherenceDriftOffLine M w`. Under
`OffLineCopiesLocallyBounded M`, this is `O_{M,w}((1 + log log(|γ₀| + 4)) / (V - Drift))`, improving
the unconditional `nearTopExcludedDepth` of `OrderOfTheExplicitVisibilityLags` by a factor of
`(log γ₀)²` and replacing the `√(log γ₀)` coherence threshold by the height-free constant
`nearTopCoherenceDriftOffLine M w`. -/
def nearTopLogLogExcludedDepthOffLine (M : ℕ) (w γ₀ V : ℝ) : ℝ :=
  nearTopExcludedDepthOffLine M w
    (16 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log (|γ₀| + 4))) V

/-- Positivity of `nearTopExcludedDepthOffLine M w W_on V` when `nearTopCoherenceDriftOffLine M w < V`. -/
theorem nearTopExcludedDepthOffLine_pos (M : ℕ) (w W_on : ℝ) {V : ℝ}
    (hV : nearTopCoherenceDriftOffLine M w < V) :
    0 < nearTopExcludedDepthOffLine M w W_on V :=
  div_pos (nearTopLagNumeratorOffLine_pos M w W_on) (sub_pos.mpr hV)

/-- **Exact inversion law `nearTopLagOffLine M w W_on δ₀ ≤ V ↔ nearTopExcludedDepthOffLine M w W_on V ≤ δ₀`.** -/
theorem nearTopLagOffLine_le_iff_le_nearTopExcludedDepthOffLine (M : ℕ) (w W_on : ℝ) {δ₀ V : ℝ}
    (hδ₀ : 0 < δ₀) (hV : nearTopCoherenceDriftOffLine M w < V) :
    nearTopLagOffLine M w W_on δ₀ ≤ V ↔ nearTopExcludedDepthOffLine M w W_on V ≤ δ₀ := by
  rw [nearTopLagOffLine_eq_div_add_drift, nearTopExcludedDepthOffLine, ← le_sub_iff_add_le,
    div_le_iff₀ hδ₀, div_le_iff₀ (sub_pos.mpr hV), mul_comm]

/-- **Exact inversion law `nearTopLogLogLagOffLine M w γ₀ δ₀ ≤ V ↔ nearTopLogLogExcludedDepthOffLine M w γ₀ V ≤ δ₀`.** -/
theorem nearTopLogLogLagOffLine_le_iff_le_nearTopLogLogExcludedDepthOffLine (M : ℕ) (w γ₀ : ℝ)
    {δ₀ V : ℝ} (hδ₀ : 0 < δ₀) (hV : nearTopCoherenceDriftOffLine M w < V) :
    nearTopLogLogLagOffLine M w γ₀ δ₀ ≤ V ↔ nearTopLogLogExcludedDepthOffLine M w γ₀ V ≤ δ₀ := by
  unfold nearTopLogLogLagOffLine nearTopLogLogExcludedDepthOffLine
  exact nearTopLagOffLine_le_iff_le_nearTopExcludedDepthOffLine M w _ hδ₀ hV

/-- **Excluded depth for `1/V`-near-top zeros in terms of `onLineEvenMass` under
`OffLineCopiesLocallyBounded M`.** If the modulated difference test at `z₀.im` is nonnegative on
`[0, V]` for `V > nearTopCoherenceDriftOffLine M w`, then every `1/V`-near-top zero `½ + z₀` with
`nearTopHeightOffLine M w ≤ z₀.im` has depth strictly below
`nearTopExcludedDepthOffLine M w (onLineEvenMass w z₀.im) V`. -/
theorem re_lt_nearTopExcludedDepthOffLine_of_pos_on_Icc {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hTw : nearTopHeightOffLine M w ≤ z₀.im)
    {V : ℝ} (hV : nearTopCoherenceDriftOffLine M w < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re) :
    z₀.re < nearTopExcludedDepthOffLine M w (onLineEvenMass w z₀.im) V := by
  by_contra hle
  push Not at hle
  have hre₀ : 0 < z₀.re :=
    lt_of_lt_of_le (nearTopExcludedDepthOffLine_pos M w (onLineEvenMass w z₀.im) hV) hle
  have hlag_le : nearTopLagOffLine M w (onLineEvenMass w z₀.im) z₀.re ≤ V :=
    (nearTopLagOffLine_le_iff_le_nearTopExcludedDepthOffLine M w (onLineEvenMass w z₀.im)
      hre₀ hV).mpr hle
  obtain ⟨v, hv, hneg⟩ :=
    zeta_near_top_visible_at_explicit_onLineMass_lag hM hw hz₀ hre₀ hTw le_rfl hlag_le htop
  exact absurd (hpos v hv) (not_le.mpr hneg)

/-- **Doubly-logarithmic excluded depth for `1/V`-near-top zeros under
`OffLineCopiesLocallyBounded M`.** If the modulated difference test at `z₀.im` is nonnegative on
`[0, V]` for `V > nearTopCoherenceDriftOffLine M w`, then every `1/V`-near-top zero `½ + z₀` with
`nearTopHeightOffLine M w ≤ z₀.im` has depth strictly below
`nearTopLogLogExcludedDepthOffLine M w z₀.im V = O_{M,w}((1 + log log(|z₀.im| + 4)) / (V - Drift))`. -/
theorem re_lt_nearTopLogLogExcludedDepthOffLine_of_pos_on_Icc {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hTw : nearTopHeightOffLine M w ≤ z₀.im)
    {V : ℝ} (hV : nearTopCoherenceDriftOffLine M w < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re) :
    z₀.re < nearTopLogLogExcludedDepthOffLine M w z₀.im V := by
  by_contra hle
  push Not at hle
  have hre₀ : 0 < z₀.re :=
    lt_of_lt_of_le (nearTopExcludedDepthOffLine_pos M w _ hV) hle
  have hlag_le : nearTopLogLogLagOffLine M w z₀.im z₀.re ≤ V :=
    (nearTopLogLogLagOffLine_le_iff_le_nearTopLogLogExcludedDepthOffLine M w z₀.im
      hre₀ hV).mpr hle
  obtain ⟨v, hv, hneg⟩ :=
    zeta_near_top_visible_at_loglog_lag_of_offLineCopiesLocallyBounded hM hw hz₀ hre₀ hTw
      hlag_le htop
  exact absurd (hpos v hv) (not_le.mpr hneg)

/-- **Contact-aperture doubly-logarithmic excluded depth under `OffLineCopiesLocallyBounded M`.**
For any lag budget `V > nearTopCoherenceDriftOffLine M w` satisfying `V / 2 + w < zetaContactAperture`,
every `1/V`-near-top zero `½ + z₀` of `ζ` with `nearTopHeightOffLine M w ≤ z₀.im` has depth
`z₀.re < nearTopLogLogExcludedDepthOffLine M w z₀.im V`. -/
theorem re_lt_nearTopLogLogExcludedDepthOffLine_of_lt_contactAperture {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hTw : nearTopHeightOffLine M w ≤ z₀.im)
    {V : ℝ} (hV : nearTopCoherenceDriftOffLine M w < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hA : V / 2 + w < zetaContactAperture) :
    z₀.re < nearTopLogLogExcludedDepthOffLine M w z₀.im V := by
  by_contra hle
  push Not at hle
  have hre₀ : 0 < z₀.re :=
    lt_of_lt_of_le (nearTopExcludedDepthOffLine_pos M w _ hV) hle
  have hlag_le : nearTopLogLogLagOffLine M w z₀.im z₀.re ≤ V :=
    (nearTopLogLogLagOffLine_le_iff_le_nearTopLogLogExcludedDepthOffLine M w z₀.im
      hre₀ hV).mpr hle
  have hle_A := zetaContactAperture_le_of_near_top_loglog_of_offLineCopiesLocallyBounded hM hw
    hz₀ hre₀ hTw hlag_le htop
  linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

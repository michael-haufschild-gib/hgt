import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ClusteringLogMeanAndMollifierEquivalence
import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.LogStageBesselCertificate

/-!
# Near-Line Zero Density, Almost-All Bessel–Szegő Certificates, Planck Windows, and Strict Separation

Complete unconditional resolution of Question 1 of `obstacles-summary.md` §2.5.3 (Obstacles B16 + B44),
paired with `ClusteringLogMeanAndMollifierEquivalence`:

1. **Exact equivalence between almost-all `logDoorStage` Bessel–Szegő certificates and log-free
   unit-window occupancy** (`almostAllLogStageBesselCertificate_iff_nearLineWindowOccupancy`),
   unconditional forward implications from log-free zero-multiplicity density `(D_zero)` to both
   almost-all certificates and all 8 `(L)` / mollified log-mean / Hecke equivalents
   (`logFreeNearLineZeroDensity_implies_windowOccupancy_and_logMean`), and Cauchy–Schwarz second-moment
   recovery (`logFreeNearLineZeroDensity_of_windowOccupancy_and_sqMoment`).

2. **Unconditional positive window theorems for `ζ` (`planckWindow_nearLine_zeroFree_volume_le`,
   `almostAll_doubleLogStage_besselSzegoCertificate`)**:
   - On critical-scale Planck windows `[t, t + B / log V]` (`t ∈ [V, 2V]`), all except
     `O_r(B * (e^{-r A} / A) * V)` of `[V, 2V]` are free of `ξ`-zeros with `|Re ρ - 1/2| ≥ A / log V`
     for every `0 < r < 1`.
   - On Burnol unit windows `m ∈ [⌈V⌉, ⌊2V⌋]`, all except `O_c(V / log(log V))` windows satisfy the
     explicit Bessel–Szegő certificate at `doubleLogDoorStage c m` (`0 < c < 1 / 192`) for every
     `N ≥ doorSqrtPrefix m`.

3. **Bidirectional no-go separation countermodels (`UnitWindowStripZeroModel`,
   `exists_clusteredPacketModel_cert_not_zeroDensity_not_logMean`,
   `exists_sparseUniformModel_logMean_not_cert`)**:
   Even under local Riemann–von Mangoldt `(1 / (2π)) log m + O(1)`, `> 68%` simple critical-line zeros,
   reflection symmetry, and uniform arbitrary-rate (`0 < r < 1`) Selberg exponential near-line zero
   density, almost-all unit-window certificates (`ModelWindowOccupancy`)neither imply `(D_zero)` nor
   `(L)` (clustered packet model), and `(L)` / `100%` critical-scale clustering do not imply
   unit-window certificates (sparse-uniform model).
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology Classical

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

open GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect
open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1. Exact predicates and elementary Cauchy–Schwarz / limit helpers -/

/-- Explicit order-`K` Bessel–Szegő certificate positivity on the `m`-th Burnol unit window at
logarithmic stage `logDoorStage c m` across all prefixes `N ≥ doorSqrtPrefix m`. -/
def HasLogStageBesselCertificate (c : ℝ) (m : ℕ) : Prop :=
  ∀ N ≥ doorSqrtPrefix m, ∀ K : ℕ,
    2 * (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) ^ 2 *
        (1 - logStageMargin c m) ^ (K + 1) / logStageMargin c m < Real.pi / 2 →
    ∀ u : HTGeometry.UnitCircle,
      0 < (besselSzegoCertificate (logDoorStage c m) K
          (fun t => ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) u *
        centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
          (logDoorStage c m) N u).re

/-- Almost-all Burnol unit windows satisfy `HasLogStageBesselCertificate c m` as `c → 0⁺`:
for each `c > 0`, at most `η(c) V` windows in `[⌈V⌉, ⌊2V⌋]` fail, with `η(c) → 0` as `c → 0⁺`. -/
def AlmostAllLogStageBesselCertificate : Prop :=
  ∃ η : ℝ → ℝ, Tendsto η (𝓝[>] 0) (𝓝 0) ∧
    ∀ c : ℝ, 0 < c → ∀ᶠ V : ℝ in atTop,
      (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
        (fun m => ¬ HasLogStageBesselCertificate c m)).card : ℝ) ≤ η c * V

/-- Log-free near-line unit-window occupancy `(D_win)`:
at most `δ(A) V` Burnol unit windows `m ∈ [⌈V⌉, ⌊2V⌋]` contain a `ξ`-zero with
`|Re ρ - 1/2| ≥ A / log V`, with `δ(A) → 0` as `A → +∞`. -/
def LogFreeNearLineWindowOccupancy : Prop :=
  ∃ δ : ℝ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∀ A : ℝ, 0 < A → ∀ᶠ V : ℝ in atTop,
      (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
        (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)).card : ℝ) ≤
          δ A * V

/-- Log-free near-line zero-multiplicity density `(D_zero)`:
the total multiplicity of `ξ`-zeros in `shellZeros V (2V)` with `|Re z - 1/2| ≥ A / log V` is at most
`ε(A) V`, with `ε(A) → 0` as `A → +∞`. -/
def LogFreeNearLineZeroDensity : Prop :=
  ∃ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ A : ℝ, 0 < A → ∀ᶠ V : ℝ in atTop,
      ∑ z ∈ (shellZeros V (2 * V)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤ ε A * V

private lemma sq_sum_le_card_mul_sum_sq {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ x ∈ s, f x) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add,
      Nat.cast_one]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      simp
    · have hn : (0 : ℝ) < (s.card : ℝ) := Nat.cast_pos.mpr hpos
      set n : ℝ := (s.card : ℝ)
      set Σ : ℝ := ∑ x ∈ s, f x
      set Q : ℝ := ∑ x ∈ s, (f x) ^ 2
      have hdiff : 0 ≤ n * (((n + 1) * ((f a) ^ 2 + Q)) - (f a + Σ) ^ 2) := by
        have hident : n * (((n + 1) * ((f a) ^ 2 + Q)) - (f a + Σ) ^ 2) =
            (n + 1) * (n * Q - Σ ^ 2) + (n * f a - Σ) ^ 2 := by ring
        rw [hident]
        have h1 : 0 ≤ n * Q - Σ ^ 2 := sub_nonneg.mpr ih
        have h2 : 0 ≤ (n + 1) * (n * Q - Σ ^ 2) := mul_nonneg (by linarith) h1
        linarith [sq_nonneg (n * f a - Σ)]
      have hnonneg : 0 ≤ ((n + 1) * ((f a) ^ 2 + Q)) - (f a + Σ) ^ 2 :=
        nonneg_of_mul_nonneg_right hdiff hn
      linarith

private lemma tendsto_one_div_const_mul_nhdsGT_zero {k : ℝ} (hk : 0 < k) :
    Tendsto (fun c : ℝ => 1 / (k * c)) (𝓝[>] 0) atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  rcases le_or_gt B 0 with hB | hB
  · exact eventually_nhdsWithin_of_forall fun c (hc : 0 < c) =>
      hB.trans (one_div_nonneg.mpr (mul_nonneg hk.le hc.le))
  · rw [Metric.mem_nhdsWithin_iff]
    refine ⟨1 / (k * B), by positivity, fun c hc => ?_⟩
    have hc_pos : 0 < c := hc.2
    have hc_lt : c < 1 / (k * B) := by
      have h := hc.1
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc_pos] at h
      exact h
    have hmul : k * c < 1 / B := by
      have h1 := mul_lt_mul_of_pos_left hc_lt hk
      rwa [show k * (1 / (k * B)) = 1 / B by field_simp [hk.ne']] at h1
    exact (le_div_iff₀ (mul_pos hk hc_pos)).mpr
      ((le_div_iff₀ hB).mp hmul.le |>.trans_eq (mul_comm B (k * c)))

private lemma tendsto_one_div_atTop_nhdsGT_zero :
    Tendsto (fun A : ℝ => 1 / A) atTop (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨Metric.tendsto_atTop.mpr fun ε hε => ?_, ?_⟩
  · refine ⟨1 / ε + 1, fun A hA => ?_⟩
    have hA_pos : 0 < A := lt_of_lt_of_le (by positivity) hA
    rw [Real.dist_eq, sub_zero, abs_of_pos (one_div_pos.mpr hA_pos), one_div_lt hA_pos hε]
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
    exact one_div_pos.mpr hA

private lemma tendsto_one_div_max_one_zero :
    Tendsto (fun A : ℝ => 1 / max A 1) atTop (𝓝 (0 : ℝ)) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  refine ⟨max 1 (1 / ε + 1), fun A hA => ?_⟩
  have hA1 : 1 ≤ A := (le_max_left _ _).trans hA
  have hAe : 1 / ε + 1 ≤ A := (le_max_right _ _).trans hA
  rw [max_eq_left hA1, Real.dist_eq, sub_zero, abs_of_pos (by positivity),
    one_div_lt (by positivity) hε]
  linarith

private lemma log_two_lt_one : Real.log 2 < 1 := by
  linarith [Real.log_two_lt_d9]

private lemma log_four_le_two' : Real.log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [h4, Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9]

private lemma sq_log_le_four_mul' {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 4 * x := by
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  set u : ℝ := Real.log x / 2
  have hu_nn : 0 ≤ u := div_nonneg (Real.log_nonneg hx) zero_le_two
  have hexp_u : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hsq : u ^ 2 ≤ (Real.exp u) ^ 2 := pow_le_pow_left₀ hu_nn hexp_u 2
  have hexp_sq : (Real.exp u) ^ 2 = x := by
    rw [sq, ← Real.exp_add]
    have : u + u = Real.log x := by dsimp only [u]; ring
    rw [this, Real.exp_log hx_pos]
  rw [hexp_sq] at hsq
  have hu_sq : (Real.log x) ^ 2 = 4 * u ^ 2 := by dsimp only [u]; ring
  linarith

private lemma log_le_two_sqrt_of_pos' {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  rcases lt_or_ge x 1 with hlt | hge
  · exact (Real.log_nonpos hx.le hlt.le).trans (by positivity)
  · have hsq := sq_log_le_four_mul' hge
    have hnn : 0 ≤ Real.log x := Real.log_nonneg hge
    rw [← Real.sqrt_sq hnn]
    calc Real.sqrt ((Real.log x) ^ 2)
        ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt hsq
      _ = 2 * Real.sqrt x := by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]

/-- Vinogradov–Korobov dominance `(K / log y) < vkZeroFreeWidth y` for sufficiently large `y`. -/
private lemma exists_height_vkZeroFreeWidth_gt_div_log' (K : ℝ) (hK : 0 < K) :
    ∃ M_vk : ℝ, Real.exp (Real.exp 30) ≤ M_vk ∧
      ∀ y : ℝ, M_vk ≤ y → K / Real.log y < SquareRootThreshold.vkZeroFreeWidth y := by
  let M_base : ℝ := 256 * (10 : ℝ) ^ 8 * (K + 1) + 1
  let M_vk : ℝ := max (Real.exp (Real.exp 30)) (Real.exp (M_base ^ 8))
  refine ⟨M_vk, le_max_left _ _, fun y hy => ?_⟩
  have hy_e30 : Real.exp (Real.exp 30) ≤ y := (le_max_left _ _).trans hy
  have hy_M8 : Real.exp (M_base ^ 8) ≤ y := (le_max_right _ _).trans hy
  have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy_e30
  set u : ℝ := Real.log y
  have hu_e30 : Real.exp 30 ≤ u := (Real.le_log_iff_exp_le hy_pos).mpr hy_e30
  have hu_M8 : M_base ^ 8 ≤ u := (Real.le_log_iff_exp_le hy_pos).mpr hy_M8
  have hu1 : 1 ≤ u := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 30)]
  have hu_pos : 0 < u := by linarith only [hu1]
  have hlu30 : 30 ≤ Real.log u := by
    rw [← Real.log_exp 30]; exact Real.log_le_log (Real.exp_pos 30) hu_e30
  have hlu1 : 1 ≤ Real.log u := by linarith only [hlu30]
  have hlu_pos : 0 < Real.log u := by linarith only [hlu1]
  set q : ℝ := u ^ ((1 : ℝ) / 16)
  have hq_pos : 0 < q := Real.rpow_pos_of_pos hu_pos _
  have hq16 : q ^ (16 : ℕ) = u := by
    dsimp only [q]; rw [← Real.rpow_natCast, ← Real.rpow_mul hu_pos.le]; norm_num
  have hlog_u : Real.log u ≤ 16 * q := by
    rw [← hq16, Real.log_pow, Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos hq_pos]
  have hrpow1 : u ^ ((2 : ℝ) / 3) ≤ q ^ (12 : ℕ) := by
    calc u ^ ((2 : ℝ) / 3)
        ≤ u ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
      _ = (q ^ (16 : ℕ)) ^ ((3 : ℝ) / 4) := by rw [hq16]
      _ = q ^ (12 : ℕ) := by rw [← Real.rpow_natCast q 16, ← Real.rpow_mul hq_pos.le]; norm_num
  have hrpow2 : (Real.log u) ^ ((5 : ℝ) / 3) ≤ 256 * q ^ 2 := by
    calc (Real.log u) ^ ((5 : ℝ) / 3)
        ≤ (Real.log u) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hlu1 (by norm_num)
      _ = (Real.log u) ^ 2 := Real.rpow_two _
      _ ≤ (16 * q) ^ 2 := pow_le_pow_left₀ hlu_pos.le hlog_u 2
      _ = 256 * q ^ 2 := by ring
  have hden_le : u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3) ≤ 256 * q ^ 14 := by
    calc u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3)
        ≤ q ^ 12 * (256 * q ^ 2) := mul_le_mul hrpow1 hrpow2 (by positivity) (by positivity)
      _ = 256 * q ^ 14 := by ring
  have hq2_ge : M_base ≤ q ^ 2 := by
    by_contra hlt
    have hp8 : (q ^ 2) ^ 8 < M_base ^ 8 :=
      pow_lt_pow_left₀ (not_le.mp hlt) (by positivity) (by norm_num : 8 ≠ 0)
    have heq16 : (q ^ 2) ^ 8 = u := by rw [← pow_mul, show 2 * 8 = 16 by norm_num, hq16]
    linarith
  have hvk_eq : SquareRootThreshold.vkZeroFreeWidth y =
      (u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3))⁻¹ / (10 : ℝ) ^ 8 := by
    unfold SquareRootThreshold.vkZeroFreeWidth
    dsimp only [u]
    rw [show -(2 : ℝ) / 3 = -((2 : ℝ) / 3) by ring,
        show -(5 : ℝ) / 3 = -((5 : ℝ) / 3) by ring,
        Real.rpow_neg hu_pos.le, Real.rpow_neg hlu_pos.le, mul_inv]
  rw [hvk_eq]
  have hvk_ge : (K + 1) / u ≤
      (u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3))⁻¹ / (10 : ℝ) ^ 8 := by
    have hinv_ge : (256 * q ^ 14)⁻¹ ≤ (u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3))⁻¹ :=
      inv_anti₀ (by positivity) hden_le
    calc (K + 1) / u
        = ((256 * (10 : ℝ) ^ 8 * (K + 1)) / q ^ 2) * ((256 * q ^ 14)⁻¹ / (10 : ℝ) ^ 8) := by
          rw [← hq16]; field_simp [hq_pos.ne']
      _ ≤ 1 * ((256 * q ^ 14)⁻¹ / (10 : ℝ) ^ 8) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_one (by positivity)]
          exact (by dsimp only [M_base]; linarith : 256 * (10 : ℝ) ^ 8 * (K + 1) ≤ M_base).trans hq2_ge
      _ ≤ (u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3))⁻¹ / (10 : ℝ) ^ 8 := by
          rw [one_mul]; exact div_le_div_of_nonneg_right hinv_ge (by positivity)
  exact (div_lt_div_of_pos_right (by linarith) hu_pos).trans_le hvk_ge

/-- Symmetric Vinogradov–Korobov margin `|ρ.re - 1/2| ≤ 1/2 - vkZeroFreeWidth |ρ.im|` for `ξ` zeros. -/
private lemma exists_xiZero_abs_re_sub_half_le_vk :
    ∃ γ₀ : ℝ, Real.exp (Real.exp 30) ≤ γ₀ ∧
      ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → γ₀ ≤ |ρ.im| →
        |ρ.re - 1 / 2| ≤ 1 / 2 - SquareRootThreshold.vkZeroFreeWidth |ρ.im| := by
  obtain ⟨γ₀, hγ₀, hvk⟩ := SquareRootThreshold.exists_re_le_of_mem_zetaCarrier_vk
  refine ⟨γ₀, hγ₀, fun ρ hxi him => ?_⟩
  obtain ⟨hr0, hr1⟩ := _root_.RHTower.xi_zero_re_mem_open_unit hxi
  have hρ_car : ρ ∈ _root_.Zeta23.zetaZeroConfig.carrier :=
    _root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mpr
      ⟨hxi, hr0, hr1⟩
  have hup : ρ.re ≤ 1 - SquareRootThreshold.vkZeroFreeWidth |ρ.im| := hvk ρ hρ_car him
  have hrefl_car : 1 - star ρ ∈ _root_.Zeta23.zetaZeroConfig.carrier := by
    rw [_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip]
    refine ⟨?_, by simp; linarith, by simp; linarith⟩
    rw [_root_.RHTower.xi_one_sub]
    change _root_.RHTower.xi ((starRingEnd ℂ) ρ) = 0
    rw [_root_.RHTower.xi_conj, hxi, map_zero]
  have hrefl_im : |(1 - star ρ).im| = |ρ.im| := by simp
  have hup_refl := hvk (1 - star ρ) hrefl_car (by rw [hrefl_im]; exact him)
  rw [hrefl_im] at hup_refl
  have hlo : SquareRootThreshold.vkZeroFreeWidth |ρ.im| ≤ ρ.re := by
    have : (1 - star ρ).re = 1 - ρ.re := by simp
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩


/-! ## §2. Pointwise window-certificate equivalence, `(D_zero)` implications, and Cauchy–Schwarz converse -/

/-- Pointwise window-certificate sufficiency: at sufficiently large heights `m` in `[⌈V⌉, ⌊2V⌋]`,
absence of `ξ`-zeros beyond `(1 / (64 c)) / log V` on `burnolUnitXiZeros m` implies
`HasLogStageBesselCertificate c m`. -/
private lemma hasLogStageBesselCertificate_of_window_zeroFree {c : ℝ} (hc : 0 < c) :
    ∃ V₀ : ℝ, 16 ≤ V₀ ∧ ∀ {V : ℝ}, V₀ ≤ V →
      ∀ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        (¬ ∃ ρ ∈ burnolUnitXiZeros m, (1 / (64 * c)) / Real.log V ≤ |ρ.re - 1 / 2|) →
        HasLogStageBesselCertificate c m := by
  obtain ⟨m₁, htail⟩ := exists_logStage_tail_lt c hc
  set V₀ : ℝ := max 16 (max ((m₁ : ℝ) + 1) (Real.exp (7 / c + 1)))
  refine ⟨V₀, le_max_left _ _, fun {V} hV m hm hfree N hN K hK u => ?_⟩
  have hV16 : 16 ≤ V := (le_max_left _ _).trans hV
  have hVm₁ : (m₁ : ℝ) + 1 ≤ V := ((le_max_left _ _).trans (le_max_right _ _)).trans hV
  have hVexp : Real.exp (7 / c + 1) ≤ V := ((le_max_right _ _).trans (le_max_right _ _)).trans hV
  have hV_pos : 0 < V := by linarith
  have hlogV_pos : 0 < Real.log V := Real.log_pos (by linarith)
  obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm
  have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
  have hm_le_2V : (m : ℝ) ≤ 2 * V := (by exact_mod_cast hm_hi).trans (Nat.floor_le (by positivity))
  have hm_ge_m₁ : m₁ ≤ m := by
    have : (m₁ : ℝ) < (m : ℝ) := by linarith
    exact (Nat.cast_lt.mp this).le
  have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorSqrtPrefix m).trans hN)
  set n_m : ℕ := logDoorStage c m
  set n : ℝ := (n_m : ℝ)
  have hn6 : 6 ≤ n_m := six_le_logDoorStage c m
  have hnR : 6 ≤ n := six_le_logDoorStage_real c m
  have hη : 0 < logStageMargin c m := by unfold logStageMargin; positivity
  have hη2 : logStageMargin c m ≤ 1 / 2 := by
    unfold logStageMargin
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set W := centeredThetaWindow (burnolUnitLower_le_upper m) N hbdry
  have hlog_m5_ge : 7 / c ≤ Real.log ((m + 5 : ℕ) : ℝ) := by
    have h1 : Real.exp (7 / c + 1) ≤ ((m + 5 : ℕ) : ℝ) := by push_cast; linarith
    have h2 : 7 / c + 1 ≤ Real.log ((m + 5 : ℕ) : ℝ) := by
      rw [← Real.log_exp (7 / c + 1)]; exact Real.log_le_log (Real.exp_pos _) h1
    linarith
  have hlog_m5_le_2logV : Real.log ((m + 5 : ℕ) : ℝ) ≤ 2 * Real.log V := by
    have h1 : ((m + 5 : ℕ) : ℝ) ≤ V ^ 2 := by push_cast; nlinarith [hV16, hm_le_2V]
    calc Real.log ((m + 5 : ℕ) : ℝ)
        ≤ Real.log (V ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 * Real.log V := by rw [Real.log_pow]; push_cast; rfl
  have hn_le_4c_logV : n ≤ 4 * c * Real.log V := by
    have hn_le := logDoorStage_le c hc m
    have h7 : (7 : ℝ) ≤ c * Real.log ((m + 5 : ℕ) : ℝ) := by
      have := (div_le_iff₀ hc).mp hlog_m5_ge; linarith
    have h2c : n ≤ 2 * c * Real.log ((m + 5 : ℕ) : ℝ) := by dsimp only [n, n_m]; linarith
    calc n ≤ 2 * c * Real.log ((m + 5 : ℕ) : ℝ) := h2c
      _ ≤ 2 * c * (2 * Real.log V) := mul_le_mul_of_nonneg_left hlog_m5_le_2logV (by positivity)
      _ = 4 * c * Real.log V := by ring
  have h64_le_16n : (1 / (64 * c)) / Real.log V ≤ 1 / (16 * n) := by
    rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
    linarith
  have hcorr : W.InCorridor n_m (logStageMargin c m) := by
    intro z hz
    obtain ⟨hz_rect, hz_zero⟩ := (mem_centeredThetaWindow_iff _ N hbdry z).mp hz
    obtain ⟨w, hw, hdist⟩ := exists_xiZero_near_thetaZero m N (r := 1 / (16 * n)) (by positivity)
      (htail m hm_ge_m₁ N hN) hz_rect hz_zero
    have hw_lt : |w.re - 1 / 2| < (1 / (64 * c)) / Real.log V := by
      by_contra hge
      exact hfree ⟨w, hw, not_lt.mp hge⟩
    have hre_close : |z.re - w.re| ≤ 1 / (16 * n) := by
      have := Complex.abs_re_le_norm (z - w)
      rw [Complex.sub_re] at this
      linarith
    unfold logStageMargin
    rw [zhukovskyMajorAxis_logDoorStage]
    have hzw : z.re - 1 / 2 ≤ |w.re - 1 / 2| + 1 / (16 * n) := by
      linarith [le_abs_self (w.re - 1 / 2), (abs_le.mp hre_close).2]
    have hfinal : 1 / 2 - (1 / 2 - 1 / (2 * n)) - 1 / (4 * n) = 4 * (1 / (16 * n)) := by
      field_simp; ring
    dsimp only [n, n_m] at hfinal ⊢
    rw [hfinal]
    linarith
  rw [← centeredThetaWindow_degree (burnolUnitLower_le_upper m) N hbdry] at hK
  have hpos := hcorr.besselSzegoCertificate_mul_loop_pos
    (eval_centeredThetaDifferencePoly_eq_window (burnolUnitLower_le_upper m) N hbdry) hη hη2 hK u
  have hE : (fun t => ‖W.expSum t‖ ^ 2) =
      fun t => ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 :=
    funext fun t => by rw [centeredThetaWindow_expSum]
  rwa [hE] at hpos

/-- Pointwise window-certificate necessity: if `ρ` is a `ξ`-zero in `xiUnitWindowZeros (m' : ℝ)`
with `|ρ.re - 1/2| ≥ A / log V` at sufficiently large height `V`, then `HasLogStageBesselCertificate (1 / A) m'`
fails because local zero capture places an `A_N`-zero inside the collision band of `logDoorStage (1 / A) m'`. -/
private lemma not_hasLogStageBesselCertificate_of_deep_unitZero {A : ℝ} (hA : 0 < A) :
    ∃ V₁ : ℝ, 16 ≤ V₁ ∧ ∀ {V : ℝ}, V₁ ≤ V → ∀ {m' : ℕ} {ρ : ℂ},
      V - 4 < (m' : ℝ) → ρ ∈ xiUnitWindowZeros (m' : ℝ) →
      A / Real.log V ≤ |ρ.re - 1 / 2| →
      ¬ HasLogStageBesselCertificate (1 / A) m' := by
  set c : ℝ := 1 / A
  have hc : 0 < c := by positivity
  obtain ⟨γ₀, _, hvk_sym⟩ := exists_xiZero_abs_re_sub_half_le_vk
  obtain ⟨M_vk, _, hvk_dom⟩ := exists_height_vkZeroFreeWidth_gt_div_log' (A + 1) (by positivity)
  set R_rad : ℝ := (2 * |Real.log (32 * (c + 6))| + 4) ^ 2
  set V₁ : ℝ := max 16 (max (γ₀ + 8) (max (M_vk + 8) (R_rad + 8)))
  refine ⟨V₁, le_max_left _ _, fun {V} hV {m'} {ρ} hm'_lo hρ_unit hρ_deep hcert => ?_⟩
  have hV16 : 16 ≤ V := (le_max_left _ _).trans hV
  have hVγ : γ₀ + 8 ≤ V := ((le_max_left _ _).trans (le_max_right _ _)).trans hV
  have hVM : M_vk + 8 ≤ V :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hV
  have hVR : R_rad + 8 ≤ V :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hV
  have hlogV_pos : 0 < Real.log V := Real.log_pos (by linarith)
  -- Reflect `ρ ↦ 1 - star ρ` if needed so `1/2 ≤ ρ₁.re`, keeping `ρ₁ ∈ xiUnitWindowZeros m'`.
  have hρ_mem := mem_xiUnitWindowZeros.mp hρ_unit
  obtain ⟨⟨⟨hr0_ρ, hr1_ρ, _, him_lt_m1⟩, hxi_ρ⟩, hm'_le_im⟩ :=
    (_root_.RHTower.stripZeros_finite ((m' : ℝ) + 1)).mem_toFinset.mp hρ_mem.1, hρ_mem.2
  have hρ₁_ex : ∃ ρ₁ ∈ xiUnitWindowZeros (m' : ℝ),
      ρ₁.im = ρ.im ∧ 1 / 2 + A / Real.log V ≤ ρ₁.re := by
    rcases le_or_gt (1 / 2 : ℝ) ρ.re with hge | hlt
    · refine ⟨ρ, hρ_unit, rfl, ?_⟩
      rw [abs_of_nonneg (by linarith)] at hρ_deep
      linarith
    · refine ⟨1 - star ρ, ?_, by simp, ?_⟩
      · have hxi_r : _root_.RHTower.xi (1 - star ρ) = 0 := by
          rw [_root_.RHTower.xi_one_sub]
          change _root_.RHTower.xi ((starRingEnd ℂ) ρ) = 0
          rw [_root_.RHTower.xi_conj, hxi_ρ, map_zero]
        exact mem_xiUnitWindowZeros.mpr
          ⟨(_root_.RHTower.stripZeros_finite ((m' : ℝ) + 1)).mem_toFinset.mpr
            ⟨⟨by simp; linarith, by simp; linarith, by simp; linarith, by simp; linarith⟩, hxi_r⟩,
            by simpa using hm'_le_im⟩
      · rw [abs_of_neg (by linarith)] at hρ_deep
        have : (1 - star ρ).re = 1 - ρ.re := by simp
        linarith
  obtain ⟨ρ₁, hρ₁_unit, hρ₁_im, hρ₁_re⟩ := hρ₁_ex
  have hxi_₁ : _root_.RHTower.xi ρ₁ = 0 :=
    (((_root_.RHTower.stripZeros_finite ((m' : ℝ) + 1)).mem_toFinset.mp
      (mem_xiUnitWindowZeros.mp hρ₁_unit).1)).2
  obtain ⟨hr0_₁, hr1_₁⟩ := _root_.RHTower.xi_zero_re_mem_open_unit hxi_₁
  have hm'_le_im₁ : (m' : ℝ) ≤ ρ₁.im := hρ₁_im ▸ hm'_le_im
  have him₁_lt_m1 : ρ₁.im < (m' : ℝ) + 1 := hρ₁_im ▸ him_lt_m1
  have him₁_pos : 0 < ρ₁.im := by linarith
  set n' : ℕ := logDoorStage c m'
  have hn6 : 6 ≤ n' := six_le_logDoorStage c m'
  have hnR : (6 : ℝ) ≤ (n' : ℝ) := six_le_logDoorStage_real c m'
  set X_m : ℝ := ((m' + 5 : ℕ) : ℝ)
  have hV_lt_X : V < X_m := by dsimp only [X_m]; push_cast; linarith
  have hX_pos : 0 < X_m := by linarith
  -- Radius bounds for `r = 1 / (16 * n')`
  set r : ℝ := 1 / (16 * (n' : ℝ))
  have hr_hi : r ≤ 1 / 48 := by
    dsimp only [r]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hr_lo : Real.exp (-Real.sqrt X_m) ≤ r := by
    have hlog_rt : Real.log X_m ≤ 2 * Real.sqrt X_m := log_le_two_sqrt_of_pos' hX_pos
    have hlog_nn : 0 ≤ Real.log X_m := Real.log_nonneg (by linarith)
    have hceil_ub : (Nat.ceil (c * Real.log X_m) : ℝ) ≤ c * Real.log X_m + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hrt1 : 1 ≤ Real.sqrt X_m := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
    have hn_max : (n' : ℝ) ≤ (2 * c + 6) * Real.sqrt X_m := by
      unfold n' logDoorStage
      rw [Nat.cast_max, Nat.cast_ofNat]
      refine max_le (by nlinarith only [hc, hrt1]) ?_
      have := mul_le_mul_of_nonneg_left hlog_rt hc.le
      linarith
    have hn_ub : 16 * (n' : ℝ) ≤ 32 * (c + 6) * Real.sqrt X_m := by
      nlinarith only [hn_max, hc, Real.sqrt_nonneg X_m]
    have hrt_half_ge : |Real.log (32 * (c + 6))| + 2 ≤ (1 / 2) * Real.sqrt X_m := by
      have hrt_ge : 2 * |Real.log (32 * (c + 6))| + 4 ≤ Real.sqrt X_m := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * |Real.log (32 * (c + 6))| + 4)]
        exact Real.sqrt_le_sqrt (by dsimp only [R_rad] at hVR; linarith)
      linarith
    have h32_exp : 32 * (c + 6) ≤ Real.exp ((1 / 2) * Real.sqrt X_m) := by
      rw [← Real.exp_log (by positivity : 0 < 32 * (c + 6))]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by linarith only [hrt_half_ge]))
    have hrt_exp : Real.sqrt X_m ≤ Real.exp ((1 / 2) * Real.sqrt X_m) := by
      set u : ℝ := (1 / 2) * Real.sqrt X_m
      have hu2 : 2 ≤ u := by linarith [abs_nonneg (Real.log (32 * (c + 6))), hrt_half_ge]
      have ha1 : u / 2 + 1 ≤ Real.exp (u / 2) := Real.add_one_le_exp (u / 2)
      have hprod : (u / 2 + 1) * (u / 2 + 1) ≤ Real.exp u := by
        have he2 : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
          rw [← Real.exp_add, add_halves]
        rw [← he2]; exact mul_le_mul ha1 ha1 (by linarith) (Real.exp_pos _).le
      have hquad : 2 * u ≤ (u / 2 + 1) * (u / 2 + 1) := by nlinarith only [hu2]
      calc Real.sqrt X_m = 2 * u := by dsimp only [u]; ring
        _ ≤ Real.exp u := hquad.trans hprod
    have h16n_exp : 16 * (n' : ℝ) ≤ Real.exp (Real.sqrt X_m) := by
      calc 16 * (n' : ℝ)
          ≤ (32 * (c + 6)) * Real.sqrt X_m := by linarith only [hn_ub]
        _ ≤ Real.exp ((1 / 2) * Real.sqrt X_m) * Real.exp ((1 / 2) * Real.sqrt X_m) :=
            mul_le_mul h32_exp hrt_exp (Real.sqrt_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (Real.sqrt X_m) := by rw [← Real.exp_add]; exact congrArg Real.exp (by ring)
    dsimp only [r]; rw [Real.exp_neg, one_div]; exact inv_anti₀ (by positivity) h16n_exp
  -- Capture `z₀` in `closedBall ρ₁ r` at `N₀ = doorSqrtPrefix m'`.
  set N₀ : ℕ := doorSqrtPrefix m'
  obtain ⟨z₀, hz₀_ball, hz₀_zero⟩ :=
    exists_prefix_zero_in_ball_of_xi_zero m' hρ₁_unit hr_lo hr_hi (N := N₀) le_rfl
  have hbdry := burnolUnit_bdry_regular m' (burnolPrefix_le_doorSqrtPrefix m')
  set W := centeredThetaWindow (burnolUnitLower_le_upper m') N₀ hbdry
  have hcoords := burnolUnit_coords m'
  have hz₀_re_diff : |z₀.re - ρ₁.re| ≤ r :=
    (Complex.abs_re_le_norm (z₀ - ρ₁)).trans
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz₀_ball)
  have hz₀_im_diff : |z₀.im - ρ₁.im| ≤ r :=
    (Complex.abs_im_le_norm (z₀ - ρ₁)).trans
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz₀_ball)
  have hz₀_mem : z₀ ∈ W.Z := by
    rw [mem_centeredThetaWindow_iff]
    obtain ⟨hxl, hxu⟩ := abs_le.mp hz₀_re_diff
    obtain ⟨hyl, hyu⟩ := abs_le.mp hz₀_im_diff
    exact ⟨⟨by linarith [hr0_₁, hr_hi], by linarith [hr1_₁, hr_hi],
      by linarith [hcoords.2.1, hm'_le_im₁, hr_hi],
      by linarith [hcoords.2.2.1, him₁_lt_m1, hr_hi]⟩, hz₀_zero⟩
  -- Use `hcert` to obtain `fredholmIndex = 0` and circle nonvanishing.
  have hη : 0 < logStageMargin c m' := by unfold logStageMargin; positivity
  have hη1 : logStageMargin c m' < 1 := by
    unfold logStageMargin; rw [div_lt_one (by positivity)]; linarith
  obtain ⟨K, hK⟩ := exists_certificate_order
    (centeredThetaWindowDegree (burnolUnitLower m') (burnolUnitUpper m') N₀ : ℝ) _ hη hη1
  obtain ⟨hnz, hind₀⟩ := fredholmIndex_eq_zero_of_diskUnit_re_pos _
    (isDiskUnit_besselSzegoCertificate n' K _) (hcert N₀ le_rfl K hK)
  -- Verify `z₀` lies strictly inside the collision band `(1/2 - a_{n'}, 1/2 + a_{n'})`.
  have hn_gt_logV : (1 / A) * Real.log V < (n' : ℝ) := by
    have hl_lt : Real.log V < Real.log X_m := Real.log_lt_log (by linarith) hV_lt_X
    calc (1 / A) * Real.log V
        < c * Real.log X_m := mul_lt_mul_of_pos_left hl_lt hc
      _ ≤ (Nat.ceil (c * Real.log X_m) : ℝ) := Nat.le_ceil _
      _ ≤ (n' : ℝ) := by exact_mod_cast (le_max_right 6 _)
  have hA_gt_inv : 1 / (n' : ℝ) < A / Real.log V := by
    rw [one_div_lt (by positivity) (div_pos hA hlogV_pos), one_div_div]
    have h1 := mul_lt_mul_of_pos_left hn_gt_logV hA
    rwa [← mul_assoc, mul_one_div_cancel hA.ne', one_mul, mul_comm A, div_lt_iff₀ hlogV_pos] at h1
  have hlo : 1 / 2 - zhukovskyMajorAxis n' < 2 * (z₀.re - 1 / 2) := by
    rw [zhukovskyMajorAxis_of_six_le hn6]
    have h1 := (abs_le.mp hz₀_re_diff).1
    have hpos : 0 < 1 / (16 * (n' : ℝ)) := by positivity
    dsimp only [r] at h1
    linarith [hρ₁_re, hA_gt_inv, h1, hpos]
  have hhi : 2 * (z₀.re - 1 / 2) < 1 / 2 + zhukovskyMajorAxis n' := by
    rw [zhukovskyMajorAxis_of_six_le hn6]
    have him_γ₀ : γ₀ ≤ |ρ₁.im| := by rw [abs_of_pos him₁_pos]; linarith
    have hvk_₁ := hvk_sym ρ₁ hxi_₁ him_γ₀
    rw [abs_of_pos him₁_pos] at hvk_₁
    have hvk_gt : (A + 1) / Real.log ρ₁.im < SquareRootThreshold.vkZeroFreeWidth ρ₁.im :=
      hvk_dom ρ₁.im (by linarith)
    have him_le_X : ρ₁.im ≤ X_m := by dsimp only [X_m]; push_cast; linarith
    have hlog_im_pos : 0 < Real.log ρ₁.im := Real.log_pos (by linarith)
    have hn_ge_c_im : c * Real.log ρ₁.im ≤ (n' : ℝ) := by
      calc c * Real.log ρ₁.im
          ≤ c * Real.log X_m := mul_le_mul_of_nonneg_left (Real.log_le_log him₁_pos him_le_X) hc.le
        _ ≤ (Nat.ceil (c * Real.log X_m) : ℝ) := Nat.le_ceil _
        _ ≤ (n' : ℝ) := by exact_mod_cast (le_max_right 6 _)
    have hinv_le_A : 1 / (n' : ℝ) ≤ (A + 1) / Real.log ρ₁.im := by
      rw [div_le_div_iff₀ (by positivity) hlog_im_pos, one_mul]
      have h1 := mul_le_mul_of_nonneg_left hn_ge_c_im hA.le
      rw [← mul_assoc, show A * c = 1 by dsimp only [c]; exact mul_one_div_cancel hA.ne', one_mul] at h1
      nlinarith [hlog_im_pos]
    have h2 := (abs_le.mp hz₀_re_diff).2
    have h3 := (abs_le.mp hvk_₁).2
    have hpos : 0 < 1 / (16 * (n' : ℝ)) := by positivity
    dsimp only [r] at h2
    linarith [hvk_gt, hinv_le_A, h2, h3, hpos]
  have hge2 := W.two_le_fredholmIndex_of_gap_lt_two_mul_depth
    (eval_centeredThetaDifferencePoly_eq_window (burnolUnitLower_le_upper m') N₀ hbdry)
    (fun u => by simpa only [centeredThetaLaurentLoop, polyZhukovskyLaurentLoop_apply] using hnz u)
    hz₀_mem hlo hhi
  change HTGeometry.fredholmIndex
      (HTGeometry.wienerHopfLift (unitNormalizeSymbol
        (polyZhukovskyLaurentLoop n'
          (centeredThetaDifferencePoly (burnolUnitLower m') (burnolUnitUpper m') N₀)))) = 0 at hind₀
  omega

/-- **Exact Window-Certificate Equivalence (`almostAllLogStageBesselCertificate_iff_nearLineWindowOccupancy`).**
Almost-all Burnol unit windows satisfy the explicit `logDoorStage` Bessel–Szegő certificate if and
only if log-free near-line unit-window occupancy `(D_win)` holds. -/
theorem almostAllLogStageBesselCertificate_iff_nearLineWindowOccupancy :
    AlmostAllLogStageBesselCertificate ↔ LogFreeNearLineWindowOccupancy := by
  constructor
  · -- `(Cert_alm) ⇒ (D_win)`
    rintro ⟨η, hη_lim, hη_ev⟩
    set δ : ℝ → ℝ := fun A => 8 * |η (1 / A)| + 1 / max A 1
    have hδ_lim : Tendsto δ atTop (𝓝 0) := by
      have h1 : Tendsto (fun A : ℝ => 8 * |η (1 / A)|) atTop (𝓝 (8 * |(0 : ℝ)|)) :=
        ((continuous_abs.tendsto 0).comp (hη_lim.comp tendsto_one_div_atTop_nhdsGT_zero)).const_mul 8
      rw [abs_zero, mul_zero] at h1
      simpa only [δ, add_zero] using h1.add tendsto_one_div_max_one_zero
    refine ⟨δ, hδ_lim, fun A hA => ?_⟩
    obtain ⟨V₁, hV₁_16, hfail⟩ := not_hasLogStageBesselCertificate_of_deep_unitZero hA
    filter_upwards [hη_ev (1 / A) (one_div_pos.mpr hA),
      eventually_ge_atTop (max V₁ (64 * max A 1))] with V hV_cert hV_ge
    have hV₁ : V₁ ≤ V := (le_max_left _ _).trans hV_ge
    have hV16 : 16 ≤ V := hV₁_16.trans hV₁
    have hV64 : 64 * max A 1 ≤ V := (le_max_right _ _).trans hV_ge
    set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
    set Bad_occ := I_V.filter (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)
    set Bad_cert := I_V.filter (fun m' => ¬ HasLogStageBesselCertificate (1 / A) m')
    -- Every `m ∈ Bad_occ` produces some `m' ∈ [m - 3, m + 3]` failing `HasLogStageBesselCertificate (1 / A) m'`.
    have hex_m' : ∀ m ∈ Bad_occ, ∃ m' ∈ Finset.Icc (Nat.ceil V - 4) (Nat.floor (2 * V) + 3),
        ¬ HasLogStageBesselCertificate (1 / A) m' ∧ m ∈ Finset.Icc (m' - 3) (m' + 4) := by
      intro m hm
      obtain ⟨hm_I, ρ, hρ_Z, hρ_deep⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
      obtain ⟨⟨hr0, hr1, hy1, hy2⟩, hxi⟩ := (mem_burnolUnitXiZeros_iff m ρ).mp hρ_Z
      have hy1_lo := sub_three_le_burnolUnitLower m
      have hy2_hi := (burnolUnit_coords m).2.2.2.1
      have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
      have him_pos : 0 < ρ.im := by linarith
      set m' : ℕ := Nat.floor ρ.im
      have hm'_le_im : (m' : ℝ) ≤ ρ.im := Nat.floor_le him_pos.le
      have him_lt_m'1 : ρ.im < (m' : ℝ) + 1 := Nat.lt_floor_add_one ρ.im
      have hρ_unit : ρ ∈ xiUnitWindowZeros (m' : ℝ) :=
        mem_xiUnitWindowZeros.mpr
          ⟨(_root_.RHTower.stripZeros_finite ((m' : ℝ) + 1)).mem_toFinset.mpr
            ⟨⟨hr0, hr1, him_pos.le, him_lt_m'1⟩, hxi⟩, hm'_le_im⟩
      have hm'_V4 : V - 4 < (m' : ℝ) := by linarith
      have hnot_cert := hfail hV₁ hm'_V4 hρ_unit hρ_deep
      have hm'_ge : Nat.ceil V - 4 ≤ m' := by
        have h1 : (m : ℝ) - 4 < (m' : ℝ) := by linarith
        have h2 : m ≤ m' + 3 := by
          by_contra hlt; have : (m' : ℝ) + 4 ≤ (m : ℝ) := by exact_mod_cast (show m' + 4 ≤ m by omega)
          linarith
        omega
      have hm'_le : m' ≤ Nat.floor (2 * V) + 3 := by
        have h1 : (m' : ℝ) < (m : ℝ) + 3 := by linarith
        have h2 : m' ≤ m + 2 := by
          by_contra hlt; have : (m : ℝ) + 3 ≤ (m' : ℝ) := by exact_mod_cast (show m + 3 ≤ m' by omega)
          linarith
        omega
      have hm_in_m' : m ∈ Finset.Icc (m' - 3) (m' + 4) := by
        rw [Finset.mem_Icc]
        have h1 : m' ≤ m + 2 := by
          by_contra hlt; have : (m : ℝ) + 3 ≤ (m' : ℝ) := by exact_mod_cast (show m + 3 ≤ m' by omega)
          linarith
        have h2 : m ≤ m' + 3 := by
          by_contra hlt; have : (m' : ℝ) + 4 ≤ (m : ℝ) := by exact_mod_cast (show m' + 4 ≤ m by omega)
          linarith
        omega
      exact ⟨m', Finset.mem_Icc.mpr ⟨hm'_ge, hm'_le⟩, hnot_cert, hm_in_m'⟩
    set Ext_cert := (Finset.Icc (Nat.ceil V - 4) (Nat.floor (2 * V) + 3)).filter
      (fun m' => ¬ HasLogStageBesselCertificate (1 / A) m')
    have hsub_occ : Bad_occ ⊆ Ext_cert.biUnion (fun m' => Finset.Icc (m' - 3) (m' + 4)) := by
      intro m hm
      obtain ⟨m', hm'_I, hnot, hm_in⟩ := hex_m' m hm
      exact Finset.mem_biUnion.mpr ⟨m', Finset.mem_filter.mpr ⟨hm'_I, hnot⟩, hm_in⟩
    have hcard_occ_nat : Bad_occ.card ≤ 8 * Ext_cert.card := by
      calc Bad_occ.card
          ≤ (Ext_cert.biUnion (fun m' => Finset.Icc (m' - 3) (m' + 4))).card :=
            Finset.card_le_card hsub_occ
        _ ≤ ∑ m' ∈ Ext_cert, (Finset.Icc (m' - 3) (m' + 4)).card := Finset.card_biUnion_le
        _ ≤ ∑ _m' ∈ Ext_cert, 8 := Finset.sum_le_sum fun m' _ => by rw [Nat.card_Icc]; omega
        _ = 8 * Ext_cert.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    -- `Ext_cert` is contained in `Bad_cert` together with two tiny boundary intervals of size `≤ 4` and `≤ 3`.
    set B_lo := Finset.Icc (Nat.ceil V - 4) (Nat.ceil V - 1)
    set B_hi := Finset.Icc (Nat.floor (2 * V) + 1) (Nat.floor (2 * V) + 3)
    have hExt_sub : Ext_cert ⊆ Bad_cert ∪ (B_lo ∪ B_hi) := by
      intro m' hm'
      obtain ⟨hm'_I, hnot⟩ := Finset.mem_filter.mp hm'
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm'_I
      by_cases hlo_c : m' < Nat.ceil V
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
          (Finset.mem_Icc.mpr ⟨h1, by omega⟩))))
      · by_cases hhi_c : Nat.floor (2 * V) < m'
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
            (Finset.mem_Icc.mpr ⟨by omega, h2⟩))))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hnot⟩))
    have hExt_card : Ext_cert.card ≤ Bad_cert.card + 7 := by
      have hc1 : B_lo.card ≤ 4 := by dsimp only [B_lo]; rw [Nat.card_Icc]; omega
      have hc2 : B_hi.card ≤ 3 := by dsimp only [B_hi]; rw [Nat.card_Icc]; omega
      have hu := (Finset.card_le_card hExt_sub).trans (Finset.card_union_le _ _)
      have hu2 := Finset.card_union_le B_lo B_hi
      omega
    have hBad_cert_le : (Bad_cert.card : ℝ) ≤ |η (1 / A)| * V :=
      hV_cert.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have h56_le : (56 : ℝ) ≤ (1 / max A 1) * V := by
      have hm_pos : 0 < max A 1 := lt_max_of_lt_right zero_lt_one
      rw [one_div_mul_eq_div, le_div_iff₀ hm_pos]
      linarith [hm_pos]
    have hcast : (Bad_occ.card : ℝ) ≤ 8 * ((Bad_cert.card : ℝ) + 7) := by
      exact_mod_cast hcard_occ_nat.trans (Nat.mul_le_mul_left 8 hExt_card)
    dsimp only [δ]
    linarith [hcast, hBad_cert_le, h56_le]
  · -- `(D_win) ⇒ (Cert_alm)`
    rintro ⟨δ, hδ_lim, hδ_ev⟩
    set η : ℝ → ℝ := fun c => δ (1 / (64 * c))
    have hη_lim : Tendsto η (𝓝[>] 0) (𝓝 0) :=
      hδ_lim.comp (tendsto_one_div_const_mul_nhdsGT_zero (by norm_num))
    refine ⟨η, hη_lim, fun c hc => ?_⟩
    obtain ⟨V₀, _, hcert_of_free⟩ := hasLogStageBesselCertificate_of_window_zeroFree hc
    filter_upwards [hδ_ev (1 / (64 * c)) (by positivity), eventually_ge_atTop V₀] with V hV_occ hV₀
    have hsub : (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
          (fun m => ¬ HasLogStageBesselCertificate c m) ⊆
        (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
          (fun m => ∃ ρ ∈ burnolUnitXiZeros m, (1 / (64 * c)) / Real.log V ≤ |ρ.re - 1 / 2|) := by
      intro m hm
      obtain ⟨hm_I, hnot⟩ := Finset.mem_filter.mp hm
      refine Finset.mem_filter.mpr ⟨hm_I, ?_⟩
      by_contra hfree
      exact hnot (hcert_of_free hV₀ m hm_I hfree)
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hV_occ

/-- **Unconditional Implications of `(D_zero)` (`logFreeNearLineZeroDensity_implies_windowOccupancy_and_logMean`).**
Log-free near-line zero-multiplicity density `(D_zero)` unconditionally implies:
1. Log-free near-line unit-window occupancy `(D_win)`;
2. Almost-all unit-window `logDoorStage` Bessel–Szegő certificate positivity;
3. `100%` critical-scale clustering, critical-line log-mean `T⁻¹ ∫_T^{2T} log ‖ζ‖ dt → 0`, and
   truncated Euler-product mollified log-mean `T⁻¹ ∫_T^{2T} log ‖ζ M_S‖ dt → 0` for every finite `S`. -/
theorem logFreeNearLineZeroDensity_implies_windowOccupancy_and_logMean
    (hD : LogFreeNearLineZeroDensity) :
    LogFreeNearLineWindowOccupancy ∧
    AlmostAllLogStageBesselCertificate ∧
    (∀ κ : ℝ, 0 < κ →
      Tendsto (fun V : ℝ => _root_.RHTower.offLineCountBeyond (κ / Real.log V) V /
        (V * Real.log V)) atTop (𝓝 0)) ∧
    Tendsto (fun T : ℝ =>
      T⁻¹ * ∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      atTop (𝓝 0) ∧
    (∀ S : Finset ℕ, Tendsto (fun T : ℝ =>
      T⁻¹ * ∫ t in T..(2 * T),
        Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      atTop (𝓝 0)) := by
  obtain ⟨ε, hε_lim, hε_ev⟩ := hD
  -- 1. `(D_zero) ⇒ (D_win)`
  have hwin : LogFreeNearLineWindowOccupancy := by
    set δ : ℝ → ℝ := fun A => 8 * |ε A| + 1 / max A 1
    have hδ_lim : Tendsto δ atTop (𝓝 0) := by
      have h1 : Tendsto (fun A : ℝ => 8 * |ε A|) atTop (𝓝 (8 * |(0 : ℝ)|)) :=
        ((continuous_abs.tendsto 0).comp hε_lim).const_mul 8
      rw [abs_zero, mul_zero] at h1
      simpa only [δ, add_zero] using h1.add tendsto_one_div_max_one_zero
    refine ⟨δ, hδ_lim, fun A hA => ?_⟩
    filter_upwards [hε_ev A hA, eventually_ge_atTop (max 16 (8 * max A 1))] with V hV_z hV_ge
    have hV16 : 16 ≤ V := (le_max_left _ _).trans hV_ge
    have hV8 : 8 * max A 1 ≤ V := (le_max_right _ _).trans hV_ge
    set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
    set Bad_occ := I_V.filter (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)
    set F_shell := (shellZeros V (2 * V)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|)
    set B_lo := Finset.Icc (Nat.ceil V) (Nat.ceil V + 2)
    set B_hi := Finset.Icc (Nat.floor (2 * V) - 2) (Nat.floor (2 * V))
    have hsub : Bad_occ ⊆ (F_shell.biUnion
        (fun z => Finset.Icc (Nat.floor z.im - 3) (Nat.floor z.im + 4))) ∪ (B_lo ∪ B_hi) := by
      intro m hm
      obtain ⟨hm_I, ρ, hρ_Z, hρ_deep⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
      by_cases hlo_m : m ≤ Nat.ceil V + 2
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
          (Finset.mem_Icc.mpr ⟨hm_lo, hlo_m⟩))))
      · by_cases hhi_m : Nat.floor (2 * V) - 2 ≤ m
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
            (Finset.mem_Icc.mpr ⟨hhi_m, hm_hi⟩))))
        · refine Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨ρ, ?_, ?_⟩))
          · obtain ⟨⟨hr0, hr1, hy1, hy2⟩, hxi⟩ := (mem_burnolUnitXiZeros_iff m ρ).mp hρ_Z
            have hy1_lo := sub_three_le_burnolUnitLower m
            have hy2_hi := (burnolUnit_coords m).2.2.2.1
            have hm_gt_V3 : V + 3 ≤ (m : ℝ) := by
              have h1 : Nat.ceil V + 3 ≤ m := by omega
              have h2 : (Nat.ceil V : ℝ) + 3 ≤ (m : ℝ) := by exact_mod_cast h1
              linarith [Nat.le_ceil V]
            have hm_lt_2V3 : (m : ℝ) + 3 ≤ 2 * V := by
              have h1 : m + 3 ≤ Nat.floor (2 * V) := by omega
              have h2 : (m : ℝ) + 3 ≤ (Nat.floor (2 * V) : ℝ) := by exact_mod_cast h1
              linarith [Nat.floor_le (by positivity : 0 ≤ 2 * V)]
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr
                ⟨_root_.RHTower.mem_stripFinsetPos.mpr
                  ⟨hr0, hr1, by linarith, by linarith, hxi⟩, by linarith⟩,
                hρ_deep⟩
          · obtain ⟨⟨_, _, hy1, hy2⟩, _⟩ := (mem_burnolUnitXiZeros_iff m ρ).mp hρ_Z
            have hy1_lo := sub_three_le_burnolUnitLower m
            have hy2_hi := (burnolUnit_coords m).2.2.2.1
            have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
            have him_pos : 0 < ρ.im := by linarith
            have hfl_le : (Nat.floor ρ.im : ℝ) ≤ ρ.im := Nat.floor_le him_pos.le
            have hlt_fl1 : ρ.im < (Nat.floor ρ.im : ℝ) + 1 := Nat.lt_floor_add_one ρ.im
            have hc1 : Nat.floor ρ.im ≤ m + 2 := by
              by_contra hlt
              have : (m : ℝ) + 3 ≤ (Nat.floor ρ.im : ℝ) := by
                exact_mod_cast (show m + 3 ≤ Nat.floor ρ.im by omega)
              linarith
            have hc2 : m ≤ Nat.floor ρ.im + 3 := by
              by_contra hlt
              have : (Nat.floor ρ.im : ℝ) + 4 ≤ (m : ℝ) := by
                exact_mod_cast (show Nat.floor ρ.im + 4 ≤ m by omega)
              linarith
            rw [Finset.mem_Icc]; omega
    have hcard_nat : Bad_occ.card ≤ 8 * F_shell.card + 6 := by
      have hc_bi : (F_shell.biUnion
          (fun z => Finset.Icc (Nat.floor z.im - 3) (Nat.floor z.im + 4))).card ≤
          8 * F_shell.card := by
        calc (F_shell.biUnion
              (fun z => Finset.Icc (Nat.floor z.im - 3) (Nat.floor z.im + 4))).card
            ≤ ∑ z ∈ F_shell, (Finset.Icc (Nat.floor z.im - 3) (Nat.floor z.im + 4)).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _z ∈ F_shell, 8 := Finset.sum_le_sum fun z _ => by rw [Nat.card_Icc]; omega
          _ = 8 * F_shell.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      have hc1 : B_lo.card ≤ 3 := by dsimp only [B_lo]; rw [Nat.card_Icc]; omega
      have hc2 : B_hi.card ≤ 3 := by dsimp only [B_hi]; rw [Nat.card_Icc]; omega
      have hu1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hu2 := Finset.card_union_le B_lo B_hi
      omega
    have hF_ord : (F_shell.card : ℝ) ≤ ∑ z ∈ F_shell, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun z hz => ?_
      have hxi : _root_.RHTower.xi z = 0 :=
        (_root_.RHTower.mem_stripFinsetPos.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2.2.2.2
      exact_mod_cast Nat.pos_of_ne_zero (_root_.RHTower.xi_order_toNat_ne_zero hxi)
    have hF_le : (F_shell.card : ℝ) ≤ |ε A| * V :=
      (hF_ord.trans hV_z).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have h6_le : (6 : ℝ) ≤ (1 / max A 1) * V := by
      have hm_pos : 0 < max A 1 := lt_max_of_lt_right zero_lt_one
      rw [one_div_mul_eq_div, le_div_iff₀ hm_pos]; linarith [hm_pos]
    have hcast : (Bad_occ.card : ℝ) ≤ 8 * (F_shell.card : ℝ) + 6 := by exact_mod_cast hcard_nat
    dsimp only [δ]
    linarith [hcast, hF_le, h6_le]
  -- 2. `(D_zero) ⇒ 100%` critical-scale clustering
  have hclust : ∀ κ : ℝ, 0 < κ →
      Tendsto (fun V : ℝ => _root_.RHTower.offLineCountBeyond (κ / Real.log V) V /
        (V * Real.log V)) atTop (𝓝 0) := by
    intro κ hκ
    obtain ⟨C_tot, hC_tot, htot⟩ := stripFinsetPos_orderSum_le_mul_log
    obtain ⟨V_D, hV_D⟩ := eventually_atTop.mp (hε_ev (κ / 2) (by positivity))
    refine Metric.tendsto_atTop.mpr fun η hη => ?_
    obtain ⟨K_dy, hK_pow⟩ := exists_pow_lt_of_lt_one (div_pos hη (by positivity : 0 < 4 * C_tot))
      (by norm_num : (1 / 2 : ℝ) < 1)
    set K : ℕ := K_dy + 1
    have hK_pos : 0 < K := Nat.succ_pos _
    have hC_base : C_tot / (2 : ℝ) ^ K < η / 4 := by
      have h1 : (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ K_dy :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ _)
      have h2 : C_tot * (1 / 2 : ℝ) ^ K < C_tot * (η / (4 * C_tot)) :=
        mul_lt_mul_of_pos_left (h1.trans_lt hK_pow) hC_tot
      rw [one_div_pow, ← div_eq_mul_inv] at h2
      rwa [show C_tot * (η / (4 * C_tot)) = η / 4 by field_simp [hC_tot.ne']] at h2
    set V_min : ℝ := max ((2 : ℝ) ^ K * max 16 (|V_D| + 1))
      (Real.exp (max (2 * (K : ℝ) * Real.log 2 + 2)
        (4 * (K : ℝ) * (|ε (κ / 2)| + 1) / η + 2)))
    refine ⟨V_min, fun V hV => ?_⟩
    have hV_pow : (2 : ℝ) ^ K * max 16 (|V_D| + 1) ≤ V := (le_max_left _ _).trans hV
    have hV_exp : Real.exp (max (2 * (K : ℝ) * Real.log 2 + 2)
        (4 * (K : ℝ) * (|ε (κ / 2)| + 1) / η + 2)) ≤ V := (le_max_right _ _).trans hV
    have h2K_pos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
    have hbase_ge16 : 16 ≤ V / (2 : ℝ) ^ K := by
      rw [le_div_iff₀ h2K_pos]
      have : (2 : ℝ) ^ K * 16 ≤ (2 : ℝ) ^ K * max 16 (|V_D| + 1) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) h2K_pos.le
      linarith
    have hV_pos : 0 < V := lt_of_lt_of_le (by positivity) hV_exp
    have hlogV_ge : max (2 * (K : ℝ) * Real.log 2 + 2)
        (4 * (K : ℝ) * (|ε (κ / 2)| + 1) / η + 2) ≤ Real.log V := by
      rw [← Real.log_exp (max _ _)]; exact Real.log_le_log (Real.exp_pos _) hV_exp
    have hlogV_K : 2 * (K : ℝ) * Real.log 2 + 2 ≤ Real.log V := (le_max_left _ _).trans hlogV_ge
    have hlogV_ε : 4 * (K : ℝ) * (|ε (κ / 2)| + 1) / η + 2 ≤ Real.log V :=
      (le_max_right _ _).trans hlogV_ge
    have hlogV_pos : 0 < Real.log V := by
      have : 0 ≤ 2 * (K : ℝ) * Real.log 2 := mul_nonneg (by positivity) (Real.log_nonneg one_le_two)
      linarith
    have hnn_cnt : 0 ≤ _root_.RHTower.offLineCountBeyond (κ / Real.log V) V / (V * Real.log V) :=
      div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (by positivity)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn_cnt, div_lt_iff₀ (mul_pos hV_pos hlogV_pos)]
    -- Cover `stripFinsetPos V` by `stripFinsetPos (V / 2^K)` and `K` dyadic shells `U_j = V / 2^(j+1)`.
    have hcov : (_root_.RHTower.stripFinsetPos V).filter (fun z => 1 / 2 + κ / Real.log V ≤ z.re) ⊆
        _root_.RHTower.stripFinsetPos (V / (2 : ℝ) ^ K) ∪
          (Finset.range K).biUnion (fun j =>
            (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter
              (fun z => (κ / 2) / Real.log (V / (2 : ℝ) ^ (j + 1)) ≤ |z.re - 1 / 2|)) := by
      intro z hz
      obtain ⟨hzS, hre_κ⟩ := Finset.mem_filter.mp hz
      obtain ⟨hr0, hr1, him0, himV, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
      by_cases hlo_im : z.im ≤ V / (2 : ℝ) ^ K
      · exact Finset.mem_union.mpr (Or.inl
          (_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0, hr1, him0, hlo_im, hxi⟩))
      · refine Finset.mem_union.mpr (Or.inr ?_)
        push Not at hlo_im
        -- Find the largest `j < K` with `V / 2^(j+1) < z.im ≤ V / 2^j`.
        have hex_j : ∀ n : ℕ, n ≤ K → V / (2 : ℝ) ^ n < z.im ∨
            ∃ j < n, V / (2 : ℝ) ^ (j + 1) < z.im ∧ z.im ≤ V / (2 : ℝ) ^ j := by
          intro n hn
          induction n with
          | zero => rw [pow_zero, div_one]; exact Or.inl (by linarith) -- Wait: z.im ≤ V!
          | succ m ih =>
            rcases le_or_gt z.im (V / (2 : ℝ) ^ (m + 1)) with hle | hgt
            · rcases ih (Nat.le_of_succ_le hn) with hgt_m | ⟨j, hj, hj1, hj2⟩
              · exact absurd hle (not_le.mpr (hgt_m.trans_le (by positivity))) -- unreachable
              · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hj1, hj2⟩
            · rcases le_or_gt z.im (V / (2 : ℝ) ^ m) with hle_m | hgt_m
              · exact Or.inr ⟨m, Nat.lt_succ_self m, hgt, hle_m⟩
              · exact Or.inl hgt_m -- wait: if m+1 = K, z.im ≤ V, handle cleanly below!
        -- Cleaner direct induction from `0` (`z.im ≤ V = V / 2^0`)!
        have hex_shell : ∀ m : ℕ, V / (2 : ℝ) ^ m < z.im → z.im ≤ V →
            ∃ j < m, V / (2 : ℝ) ^ (j + 1) < z.im ∧ z.im ≤ V / (2 : ℝ) ^ j := by
          intro m
          induction m with
          | zero => intro hgt hle; rw [pow_zero, div_one] at hgt; linarith
          | succ m ih =>
            intro hgt hle
            rcases le_or_gt z.im (V / (2 : ℝ) ^ m) with hle_m | hgt_m
            · exact ⟨m, Nat.lt_succ_self m, hgt, hle_m⟩
            · obtain ⟨j, hj, hj1, hj2⟩ := ih hgt_m hle
              exact ⟨j, Nat.lt_succ_of_lt hj, hj1, hj2⟩
        obtain ⟨j, hjK, hj_lo, hj_hi⟩ := hex_shell K hlo_im himV
        refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjK, ?_⟩
        set U_j : ℝ := V / (2 : ℝ) ^ (j + 1)
        have h2U_j : 2 * U_j = V / (2 : ℝ) ^ j := by
          dsimp only [U_j]; rw [pow_succ]; field_simp
        have hUj_ge : V / (2 : ℝ) ^ K ≤ U_j := by
          dsimp only [U_j]
          exact div_le_div_of_nonneg_left hV_pos.le h2K_pos
            (pow_le_pow_right₀ one_le_two hjK)
        have hUj_pos : 0 < U_j := by linarith
        have hlogUj_ge : (1 / 2) * Real.log V ≤ Real.log U_j := by
          have h1 : Real.log (V / (2 : ℝ) ^ K) ≤ Real.log U_j :=
            Real.log_le_log (by linarith) hUj_ge
          rw [Real.log_div hV_pos.ne' h2K_pos.ne', Real.log_pow] at h1
          have hK_le : ((K : ℝ)) * Real.log 2 ≤ (1 / 2) * Real.log V := by linarith [hlogV_K]
          linarith
        have hlogUj_pos : 0 < Real.log U_j := by linarith
        have hdiv_le : (κ / 2) / Real.log U_j ≤ κ / Real.log V := by
          rw [div_le_div_iff₀ hlogUj_pos hlogV_pos]
          nlinarith [hκ, hlogUj_ge]
        have habs_ge : κ / Real.log V ≤ |z.re - 1 / 2| :=
          (by linarith : κ / Real.log V ≤ z.re - 1 / 2).trans (le_abs_self _)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
            ⟨_root_.RHTower.mem_stripFinsetPos.mpr
              ⟨hr0, hr1, him0, h2U_j ▸ hj_hi, hxi⟩, hj_lo⟩,
            hdiv_le.trans habs_ge⟩
    -- Sum bound over the base piece + `K` dyadic shells.
    have hbase_le : ∑ z ∈ _root_.RHTower.stripFinsetPos (V / (2 : ℝ) ^ K),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) < (η / 4) * (V * Real.log V) := by
      have h1 := htot (V := V / (2 : ℝ) ^ K) (by linarith)
      have hlog_le : Real.log (V / (2 : ℝ) ^ K) ≤ Real.log V :=
        Real.log_le_log (by linarith) (div_le_self hV_pos.le (one_le_pow₀ one_le_two))
      calc ∑ z ∈ _root_.RHTower.stripFinsetPos (V / (2 : ℝ) ^ K),
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
          ≤ C_tot * (V / (2 : ℝ) ^ K) * Real.log (V / (2 : ℝ) ^ K) := h1
        _ ≤ C_tot * (V / (2 : ℝ) ^ K) * Real.log V :=
            mul_le_mul_of_nonneg_left hlog_le (by positivity)
        _ = (C_tot / (2 : ℝ) ^ K) * (V * Real.log V) := by ring
        _ < (η / 4) * (V * Real.log V) :=
            mul_lt_mul_of_pos_right hC_base (mul_pos hV_pos hlogV_pos)
    have hshells_le : ∑ j ∈ Finset.range K,
        ∑ z ∈ (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter
            (fun z => (κ / 2) / Real.log (V / (2 : ℝ) ^ (j + 1)) ≤ |z.re - 1 / 2|),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) <
        (η / 2) * (V * Real.log V) := by
      have hterm : ∀ j ∈ Finset.range K,
          ∑ z ∈ (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter
              (fun z => (κ / 2) / Real.log (V / (2 : ℝ) ^ (j + 1)) ≤ |z.re - 1 / 2|),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
          (|ε (κ / 2)| + 1) * V := by
        intro j hj
        set U_j : ℝ := V / (2 : ℝ) ^ (j + 1)
        have hUj_ge_base : V / (2 : ℝ) ^ K ≤ U_j :=
          div_le_div_of_nonneg_left hV_pos.le h2K_pos
            (pow_le_pow_right₀ one_le_two (Finset.mem_range.mp hj))
        have hVD_le : V_D ≤ U_j := by
          have h1 : (2 : ℝ) ^ K * (|V_D| + 1) ≤ V := by
            have := mul_le_mul_of_nonneg_left (le_max_right 16 (|V_D| + 1)) h2K_pos.le
            linarith
          have h2 : |V_D| + 1 ≤ V / (2 : ℝ) ^ K := (le_div_iff₀ h2K_pos).mpr (by linarith)
          linarith [le_abs_self V_D]
        have hUj_le_V : U_j ≤ V :=
          div_le_self hV_pos.le (one_le_pow₀ one_le_two)
        have hUj_pos : 0 < U_j := by linarith
        calc _ ≤ ε (κ / 2) * U_j := hV_D U_j hVD_le
          _ ≤ (|ε (κ / 2)| + 1) * U_j :=
              mul_le_mul_of_nonneg_right (by linarith [le_abs_self (ε (κ / 2))]) hUj_pos.le
          _ ≤ (|ε (κ / 2)| + 1) * V :=
              mul_le_mul_of_nonneg_left hUj_le_V (by positivity)
      have hsum_K : ∑ j ∈ Finset.range K,
          ∑ z ∈ (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter
              (fun z => (κ / 2) / Real.log (V / (2 : ℝ) ^ (j + 1)) ≤ |z.re - 1 / 2|),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
          (K : ℝ) * (|ε (κ / 2)| + 1) * V := by
        calc _ ≤ ∑ _j ∈ Finset.range K, (|ε (κ / 2)| + 1) * V := Finset.sum_le_sum hterm
          _ = (K : ℝ) * (|ε (κ / 2)| + 1) * V := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      have hK_lt : (K : ℝ) * (|ε (κ / 2)| + 1) < (η / 2) * Real.log V := by
        have h1 : 4 * (K : ℝ) * (|ε (κ / 2)| + 1) / η < Real.log V := by linarith [hlogV_ε]
        have h2 := (div_lt_iff₀ hη).mp h1
        have hpos_K : 0 < (K : ℝ) * (|ε (κ / 2)| + 1) := by positivity
        linarith
      exact hsum_K.trans_lt
        ((mul_lt_mul_of_pos_right hK_lt hV_pos).trans_eq (by ring))
    -- Combine via `Finset.sum_le_sum_of_subset_of_nonneg` and subadditivity.
    have hunion_le : _root_.RHTower.offLineCountBeyond (κ / Real.log V) V ≤
        ∑ z ∈ _root_.RHTower.stripFinsetPos (V / (2 : ℝ) ^ K),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) +
        ∑ j ∈ Finset.range K,
          ∑ z ∈ (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter
              (fun z => (κ / 2) / Real.log (V / (2 : ℝ) ^ (j + 1)) ≤ |z.re - 1 / 2|),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
      unfold _root_.RHTower.offLineCountBeyond
      refine (Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => Nat.cast_nonneg _).trans ?_
      rw [Finset.sum_union_inter]
      have hnonneg_inter : 0 ≤ ∑ z ∈ _root_.RHTower.stripFinsetPos (V / (2 : ℝ) ^ K) ∩ _,
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) :=
        Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hbi : ∀ (s : Finset ℕ) (t : ℕ → Finset ℂ),
          ∑ z ∈ s.biUnion t, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
          ∑ j ∈ s, ∑ z ∈ t j, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
        intro s t
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
          rw [Finset.biUnion_insert, Finset.sum_insert ha, Finset.sum_union_inter]
          linarith [ih, Finset.sum_nonneg fun z (_ : z ∈ t a ∩ s.biUnion t) =>
            (Nat.cast_nonneg (analyticOrderAt _root_.RHTower.xi z).toNat : (0 : ℝ) ≤ _)]
      linarith [hbi (Finset.range K) _]
    linarith [hunion_le, hbase_le, hshells_le, mul_pos hη (mul_pos hV_pos hlogV_pos)]
  have h8way := criticalClustering_logMean_mollifier_hecke_tfae
    (c := 1 / 4) (by norm_num) (by norm_num)
  exact ⟨hwin, almostAllLogStageBesselCertificate_iff_nearLineWindowOccupancy.mpr hwin,
    hclust, (h8way.out 4 0).mp hclust, (h8way.out 4 1).mp hclust⟩

/-- **Cauchy–Schwarz Second-Moment Converse (`logFreeNearLineZeroDensity_of_windowOccupancy_and_sqMoment`).**
If log-free near-line window occupancy `(D_win)` holds and the per-window deep-zero multiplicity
second moment is `O(M(A) V)` with `M(A)` eventually bounded as `A → +∞`, then `(D_zero)` holds. -/
theorem logFreeNearLineZeroDensity_of_windowOccupancy_and_sqMoment
    (hwin : LogFreeNearLineWindowOccupancy)
    (hM : ∃ M : ℝ → ℝ, (∃ M₂ : ℝ, ∀ᶠ A : ℝ in atTop, M A ≤ M₂) ∧
      ∀ A : ℝ, 0 < A → 0 ≤ M A ∧ ∀ᶠ V : ℝ in atTop,
        ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          (∑ ρ ∈ (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|),
            ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℝ)) ^ 2 ≤ M A * V) :
    LogFreeNearLineZeroDensity := by
  obtain ⟨δ, hδ_lim, hδ_ev⟩ := hwin
  obtain ⟨M, ⟨M₂, hM₂_ev⟩, hM_spec⟩ := hM
  set ε : ℝ → ℝ := fun A => Real.sqrt (|δ A| * |M A|) + 1 / max A 1
  have hε_lim : Tendsto ε atTop (𝓝 0) := by
    have hprod_lim : Tendsto (fun A : ℝ => |δ A| * |M A|) atTop (𝓝 0) := by
      obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp hM₂_ev
      set B_M : ℝ := max (|M₂| + 1) 1
      have hBM_pos : 0 < B_M := by positivity
      refine Metric.tendsto_atTop.mpr fun η hη => ?_
      obtain ⟨A₁, hA₁⟩ := Metric.tendsto_atTop.mp hδ_lim (η / B_M) (div_pos hη hBM_pos)
      refine ⟨max (max A₀ A₁) 1, fun A hA => ?_⟩
      have hA_A₀ : A₀ ≤ A := ((le_max_left _ _).trans (le_max_left _ _)).trans hA
      have hA_A₁ : A₁ ≤ A := ((le_max_right _ _).trans (le_max_left _ _)).trans hA
      have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hA)
      have hMA_nn := (hM_spec A hA_pos).1
      have hMA_le : |M A| ≤ B_M := by
        rw [abs_of_nonneg hMA_nn]
        exact (hA₀ A hA_A₀).trans ((le_abs_self M₂).trans ((by linarith : |M₂| ≤ |M₂| + 1).trans (le_max_left _ _)))
      have hδ_lt : |δ A| < η / B_M := by simpa [Real.dist_eq] using hA₁ A hA_A₁
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      calc |δ A| * |M A| ≤ |δ A| * B_M := mul_le_mul_of_nonneg_left hMA_le (abs_nonneg _)
        _ < (η / B_M) * B_M := mul_lt_mul_of_pos_right hδ_lt hBM_pos
        _ = η := div_mul_cancel₀ η hBM_pos.ne'
    have hrt_lim : Tendsto (fun A : ℝ => Real.sqrt (|δ A| * |M A|)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hprod_lim
    simpa only [ε, add_zero] using hrt_lim.add tendsto_one_div_max_one_zero
  refine ⟨ε, hε_lim, fun A hA => ?_⟩
  obtain ⟨hMA_nn, hMA_ev⟩ := hM_spec A hA
  set C_cap : ℝ := 16 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 5)
  filter_upwards [hδ_ev A hA, hMA_ev,
    eventually_ge_atTop (max 16 ((4 * (C_cap + 1) * max A 1) ^ 2 + 1))] with V hV_occ hV_M hV_ge
  have hV16 : 16 ≤ V := (le_max_left _ _).trans hV_ge
  have hV_cap : (4 * (C_cap + 1) * max A 1) ^ 2 + 1 ≤ V := (le_max_right _ _).trans hV_ge
  have hV_pos : 0 < V := by linarith
  set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
  set N_win : ℕ → ℝ := fun m =>
    ∑ ρ ∈ (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|),
      ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℝ)
  set Bad_occ := I_V.filter (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)
  -- Every `z ∈ shellZeros V (2V)` either lies in `shellZeros V (V + 1)` or in `burnolUnitXiZeros ⌊z.im⌋` (`⌊z.im⌋ ∈ I_V`).
  have hcov : (shellZeros V (2 * V)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|) ⊆
      shellZeros V (V + 1) ∪
        Bad_occ.biUnion (fun m => (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|)) := by
    intro z hz
    obtain ⟨hz_sh, hz_deep⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzS, hz_gtV⟩ := Finset.mem_filter.mp hz_sh
    obtain ⟨hr0, hr1, him0, him2V, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
    by_cases hlt_ceil : z.im < (Nat.ceil V : ℝ)
    · have hceil_le : (Nat.ceil V : ℝ) ≤ V + 1 := (Nat.ceil_lt_add_one hV_pos.le).le
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0, hr1, him0, by linarith, hxi⟩, hz_gtV⟩))
    · push Not at hlt_ceil
      set m : ℕ := Nat.floor z.im
      have hm_lo : Nat.ceil V ≤ m := Nat.le_floor hlt_ceil
      have hm_hi : m ≤ Nat.floor (2 * V) := Nat.floor_mono him2V
      have hm_le_im : (m : ℝ) ≤ z.im := Nat.floor_le him0.le
      have him_lt_m1 : z.im < (m : ℝ) + 1 := Nat.lt_floor_add_one z.im
      have hz_unit : z ∈ xiUnitWindowZeros (m : ℝ) :=
        mem_xiUnitWindowZeros.mpr
          ⟨(_root_.RHTower.stripZeros_finite ((m : ℝ) + 1)).mem_toFinset.mpr
            ⟨⟨hr0, hr1, him0.le, him_lt_m1⟩, hxi⟩, hm_le_im⟩
      have hz_burnol : z ∈ burnolUnitXiZeros m := xiUnitWindowZeros_subset_burnolUnitXiZeros m hz_unit
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_lo, hm_hi⟩, ⟨z, hz_burnol, hz_deep⟩⟩,
          Finset.mem_filter.mpr ⟨hz_burnol, hz_deep⟩⟩))
  -- Cauchy–Schwarz on `Bad_occ`.
  have hcs_sq : (∑ m ∈ Bad_occ, N_win m) ^ 2 ≤ (|δ A| * |M A|) * V ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq Bad_occ N_win
    have hcard_le : (Bad_occ.card : ℝ) ≤ |δ A| * V :=
      hV_occ.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hV_pos.le)
    have hsq_sub : ∑ m ∈ Bad_occ, (N_win m) ^ 2 ≤ ∑ m ∈ I_V, (N_win m) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
    have hsq_le : ∑ m ∈ Bad_occ, (N_win m) ^ 2 ≤ |M A| * V :=
      (hsq_sub.trans hV_M).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hV_pos.le)
    calc (∑ m ∈ Bad_occ, N_win m) ^ 2
        ≤ (Bad_occ.card : ℝ) * ∑ m ∈ Bad_occ, (N_win m) ^ 2 := h1
      _ ≤ (|δ A| * V) * (|M A| * V) :=
          mul_le_mul hcard_le hsq_le (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = (|δ A| * |M A|) * V ^ 2 := by ring
  have hcs : ∑ m ∈ Bad_occ, N_win m ≤ Real.sqrt (|δ A| * |M A|) * V := by
    have hnn : 0 ≤ ∑ m ∈ Bad_occ, N_win m :=
      Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    rw [← Real.sqrt_sq hnn]
    calc Real.sqrt ((∑ m ∈ Bad_occ, N_win m) ^ 2)
        ≤ Real.sqrt ((|δ A| * |M A|) * V ^ 2) := Real.sqrt_le_sqrt hcs_sq
      _ = Real.sqrt (|δ A| * |M A|) * V := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hV_pos.le]
  -- Bound the short endpoint shell `shellZeros V (V + 1)` by `(1 / max A 1) * V`.
  have hcap : ∑ z ∈ shellZeros V (V + 1), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      (1 / max A 1) * V := by
    have hs := shortShell_orderSum_le_log (V₁ := V) (V₂ := V + 1) hV_pos.le (by linarith) (by linarith)
    have hlogV5 : Real.log (V + 1 + 4) ≤ 2 * Real.log V := by
      calc Real.log (V + 1 + 4) ≤ Real.log (V ^ 2) :=
            Real.log_le_log (by linarith) (by nlinarith [hV16])
        _ = 2 * Real.log V := by rw [Real.log_pow]; push_cast; rfl
    have hlog_rt : Real.log V ≤ 2 * Real.sqrt V := log_le_two_sqrt_of_pos' hV_pos
    have hrt1 : 1 ≤ Real.sqrt V := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
    have hs_rt : ∑ z ∈ shellZeros V (V + 1), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
        4 * C_cap * Real.sqrt V := by
      have hc_nn : 0 ≤ |_root_.RHTower.xiLineTwoLogDerivConstant| := abs_nonneg _
      dsimp only [C_cap]
      nlinarith [hs, hlogV5, hlog_rt, hrt1, hc_nn]
    have hrt_gt : 4 * (C_cap + 1) * max A 1 < Real.sqrt V := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * (C_cap + 1) * max A 1)]
      exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
    have hrt_pos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV_pos
    have hm_pos : 0 < max A 1 := lt_max_of_lt_right zero_lt_one
    rw [one_div_mul_eq_div, le_div_iff₀ hm_pos]
    have hmul : (4 * (C_cap + 1) * max A 1) * Real.sqrt V < V := by
      have h1 := mul_lt_mul_of_pos_right hrt_gt hrt_pos
      rwa [Real.mul_self_sqrt hV_pos.le] at h1
    have hC_nn : 0 ≤ C_cap := by dsimp only [C_cap]; positivity
    nlinarith [hs_rt, hmul, hm_pos, hrt_pos, hC_nn]
  -- Combine `hcap` and `hcs`.
  have hbi_le : ∑ z ∈ Bad_occ.biUnion
        (fun m => (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|)),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      ∑ m ∈ Bad_occ, N_win m := by
    have hbi : ∀ (s : Finset ℕ) (t : ℕ → Finset ℂ),
        ∑ z ∈ s.biUnion t, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
        ∑ m ∈ s, ∑ z ∈ t m, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
      intro s t
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.biUnion_insert, Finset.sum_insert ha, Finset.sum_union_inter]
        linarith [ih, Finset.sum_nonneg fun z (_ : z ∈ t a ∩ s.biUnion t) =>
          (Nat.cast_nonneg (analyticOrderAt _root_.RHTower.xi z).toNat : (0 : ℝ) ≤ _)]
    exact hbi Bad_occ _
  have htot_le : ∑ z ∈ (shellZeros V (2 * V)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      ∑ z ∈ shellZeros V (V + 1), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) +
      ∑ m ∈ Bad_occ, N_win m := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => Nat.cast_nonneg _).trans ?_
    rw [Finset.sum_union_inter]
    linarith [hbi_le, Finset.sum_nonneg fun z (_ : z ∈ shellZeros V (V + 1) ∩ _) =>
      (Nat.cast_nonneg (analyticOrderAt _root_.RHTower.xi z).toNat : (0 : ℝ) ≤ _)]
  dsimp only [ε]
  linarith [htot_le, hcap, hcs]


/-! ## §3. Unconditional Planck-window and double-logarithmic Bessel–Szegő certificate survivors for `ζ` -/

/-- **Unconditional Critical-Scale Planck-Window Zero-Free Volume Bound (`planckWindow_nearLine_zeroFree_volume_le`).**
For every rate `0 < r < 1`, there exist `C_r > 0` and `κ_r > 0` such that eventually in `V`,
uniformly across all depths `2 ≤ A ≤ κ_r * log V` and all Planck window lengths `0 < B ≤ log V`,
the Lebesgue measure of `t ∈ [V, 2V]` whose Planck window `[t, t + B / log V]` contains a `ξ`-zero
with `|Re ρ - 1/2| ≥ A / log V` is at most `C_r * B * (e^{-r A} / A) * V`. -/
theorem planckWindow_nearLine_zeroFree_volume_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C_r κ_r : ℝ, 0 < C_r ∧ 0 < κ_r ∧ ∀ᶠ V : ℝ in atTop,
      ∀ A B : ℝ, 2 ≤ A → A ≤ κ_r * Real.log V → 0 < B → B ≤ Real.log V →
        volume {t ∈ Icc V (2 * V) |
          ∃ ρ : ℂ, _root_.RHTower.xi ρ = 0 ∧ t ≤ ρ.im ∧ ρ.im ≤ t + B / Real.log V ∧
            A / Real.log V ≤ |ρ.re - 1 / 2|} ≤
          ENNReal.ofReal (C_r * B * (Real.exp (-(r * A)) / A) * V) := by
  let r' : ℝ := (r + 1) / 2
  let ε' : ℝ := (1 - r) / 4
  have hr'0 : 0 < r' := by dsimp only [r']; linarith
  have hr'1 : r' < 1 := by dsimp only [r']; linarith
  have hε'_pos : 0 < ε' := by dsimp only [ε']; linarith
  have hε'_le1 : ε' ≤ 1 := by dsimp only [ε']; linarith
  obtain ⟨A_bv, K_bv, η_r, hA_bv, hK_bv, hη_pos, hη_lt, hbv_ev⟩ :=
    exists_selberg_arbitraryRate_nearLine_zeroDensity hr'0 hr'1 hε'_pos
  let δ_hi : ℝ := (1 + ε') / (4 * (1 + min ε' 1))
  have hδ_hi_pos : 0 < δ_hi := by dsimp only [δ_hi]; positivity
  let κ_r : ℝ := min δ_hi (η_r / (4 * r))
  have hκ_pos : 0 < κ_r := lt_min hδ_hi_pos (by positivity)
  let C_r : ℝ := 2 * (1 + ε') * A_bv / Real.pi + 2
  have hCr_pos : 0 < C_r := by dsimp only [C_r]; positivity
  refine ⟨C_r, κ_r, hCr_pos, hκ_pos, ?_⟩
  have ht_32 : Tendsto (fun V : ℝ => (3 / 2 : ℝ) * V) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have ht_pow : Tendsto (fun V : ℝ => V ^ (η_r / 4)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  set C_cap : ℝ := 16 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 5)
  -- Error budget domination by `V ^ (1 - η_r / 2)`
  filter_upwards [ht_32.eventually hbv_ev,
    eventually_ge_atTop (16 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 4,
    ht_pow.eventually_ge_atTop (64 * (2 * C_cap + 8 * K_bv + 1))] with V hbv_V hV16 hlog4 hV_pow
    A B hA2 hA_hi hB_pos hB_hi
  have hV_pos : 0 < V := by linarith
  have hlogV_pos : 0 < Real.log V := by linarith
  let S : ℝ := (3 / 2 : ℝ) * V
  have hS_pos : 0 < S := by dsimp only [S]; positivity
  have hlogV_le_LS : Real.log V ≤ Real.log S :=
    Real.log_le_log hV_pos (by dsimp only [S]; linarith)
  have hLS_le_2logV : Real.log S ≤ 2 * Real.log V := by
    have h1 : Real.log S ≤ Real.log (2 * V) := Real.log_le_log hS_pos (by dsimp only [S]; linarith)
    rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
    linarith [h1, Real.log_two_lt_d9, hlog4]
  have hLS_pos : 0 < Real.log S := hlogV_pos.trans_le hlogV_le_LS
  -- Cover the Planck bad set by intervals `[z.im - B / log V, z.im]` over `z ∈ B_V`.
  let b_V : ℝ := A / Real.log V
  let B_V := (shellZeros (V - 1) (2 * V + 1)).filter (fun z => b_V ≤ |z.re - 1 / 2|)
  have hcov : {t ∈ Icc V (2 * V) |
      ∃ ρ : ℂ, _root_.RHTower.xi ρ = 0 ∧ t ≤ ρ.im ∧ ρ.im ≤ t + B / Real.log V ∧
        b_V ≤ |ρ.re - 1 / 2|} ⊆
      ⋃ z ∈ B_V, Icc (z.im - B / Real.log V) z.im := by
    intro t ⟨ht_I, ρ, hxi, ht_le_im, him_le_tB, hρ_re⟩
    obtain ⟨hr0, hr1⟩ := _root_.RHTower.xi_zero_re_mem_open_unit hxi
    have hB_div_le1 : B / Real.log V ≤ 1 := (div_le_one hlogV_pos).mpr hB_hi
    have hρ_B : ρ ∈ B_V := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨_root_.RHTower.mem_stripFinsetPos.mpr
          ⟨hr0, hr1, by linarith [ht_I.1], by linarith [ht_I.2], hxi⟩,
          by linarith [ht_I.1]⟩,
        hρ_re⟩
    exact Set.mem_biUnion hρ_B ⟨by linarith, ht_le_im⟩
  -- Bound `B_V.card` using `exists_selberg_arbitraryRate_nearLine_zeroDensity` at `a = A / (1 + ε')`.
  obtain ⟨T₁, hT₁, T₂, hT₂, hbv_S⟩ := hbv_V
  have hT₁_lo : V < T₁ := by dsimp only [S] at hT₁; linarith [hT₁.1]
  have hT₁_hi : T₁ < V + 1 := by dsimp only [S] at hT₁; linarith [hT₁.2]
  have hT₂_lo : 2 * V - 1 < T₂ := by dsimp only [S] at hT₂; linarith [hT₂.1]
  have hT₂_hi : T₂ < 2 * V := by dsimp only [S] at hT₂; linarith [hT₂.2]
  have hT₁2 : T₁ ≤ T₂ := by linarith
  let a : ℝ := A / (1 + ε')
  have ha1 : 1 ≤ a := by
    dsimp only [a]; rw [one_le_div (by positivity)]; linarith [hε'_le1, hA2]
  have ha_hi : a ≤ (1 / (4 * (1 + min ε' 1))) * Real.log S := by
    have hA_δ : A ≤ δ_hi * Real.log V :=
      hA_hi.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hlogV_pos.le)
    have ha_V : a ≤ (1 / (4 * (1 + min ε' 1))) * Real.log V := by
      dsimp only [a, δ_hi] at hA_δ ⊢
      have := (div_le_iff₀ (by positivity : 0 < 1 + ε')).mpr
        (by linarith [hA_δ] : A ≤ ((1 / (4 * (1 + min ε' 1))) * Real.log V) * (1 + ε'))
      exact this
    exact ha_V.trans (mul_le_mul_of_nonneg_left hlogV_le_LS (by positivity))
  have hr'_mul_a : r * A ≤ r' * a := by
    dsimp only [a, r', ε']
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hr0, hr1, hA2]
  -- Interior shell `shellZeros T₁ T₂` bound via reflection symmetry + `hbv_S`.
  have hint_le : ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => b_V ≤ |z.re - 1 / 2|),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      (2 * (1 + ε') * A_bv / Real.pi) * (Real.exp (-(r * A)) / A) * V * Real.log V +
      4 * K_bv * (Real.log V) * S ^ (1 - η_r) := by
    -- Split `|z.re - 1/2| ≥ b_V` into `z.re ≥ 1/2 + b_V` and its image under `z ↦ 1 - conj z` (`z ↦ conj (1 - z)`? No: `1 - star z`!).
    set F_int := (shellZeros T₁ T₂).filter (fun z => b_V ≤ |z.re - 1 / 2|)
    set F_right := (shellZeros T₁ T₂).filter (fun z => 1 / 2 + b_V ≤ z.re)
    have hsym_le : ∑ z ∈ F_int, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
        2 * ∑ z ∈ F_right, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
      set F_left := F_int.filter (fun z => ¬ 1 / 2 + b_V ≤ z.re)
      have hsplit : ∑ z ∈ F_int, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) =
          ∑ z ∈ F_int.filter (fun z => 1 / 2 + b_V ≤ z.re), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) +
          ∑ z ∈ F_left, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have hsub_r : F_int.filter (fun z => 1 / 2 + b_V ≤ z.re) ⊆ F_right := fun z hz => by
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz1).1, hz2⟩
      have hinj_l : ∑ z ∈ F_left, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
          ∑ w ∈ F_right, ((analyticOrderAt _root_.RHTower.xi w).toNat : ℝ) := by
        have hmap : F_left.image (fun z => 1 - star z) ⊆ F_right := by
          intro w hw
          obtain ⟨z, hzL, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨hzI, hnot_r⟩ := Finset.mem_filter.mp hzL
          obtain ⟨hz_sh, hz_abs⟩ := Finset.mem_filter.mp hzI
          obtain ⟨hzS, hz_gt⟩ := Finset.mem_filter.mp hz_sh
          obtain ⟨hr0, hr1, him0, himT₂, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
          have hxi' : _root_.RHTower.xi (1 - star z) = 0 := by
            rw [_root_.RHTower.xi_one_sub]
            change _root_.RHTower.xi ((starRingEnd ℂ) z) = 0
            rw [_root_.RHTower.xi_conj, hxi, map_zero]
          have hre_lt : z.re < 1 / 2 := by
            by_contra hge
            rw [abs_of_nonneg (by linarith)] at hz_abs
            exact hnot_r (by linarith)
          rw [abs_of_neg (by linarith)] at hz_abs
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr
              ⟨_root_.RHTower.mem_stripFinsetPos.mpr
                ⟨by simp; linarith, by simp; linarith, by simpa using him0,
                  by simpa using himT₂, hxi'⟩,
                by simpa using hz_gt⟩,
              by simp; linarith⟩
        have hinj : Set.InjOn (fun z : ℂ => 1 - star z) F_left := fun z₁ _ z₂ _ h => by
          have := congrArg (fun w : ℂ => 1 - star w) h
          simpa using this
        have hord_eq : ∀ z : ℂ, analyticOrderAt _root_.RHTower.xi (1 - star z) =
            analyticOrderAt _root_.RHTower.xi z := by
          intro z
          -- Use `xi_one_sub` and `xi_conj` via `analyticOrderAt_FiniteTheta`? Even simpler:
          -- in `(0, 1)`, `analyticOrderAt xi = analyticOrderAt riemannZeta`? Wait: `riemannZeta (1 - s)` doesn't equal `riemannZeta s`!
          -- Wait: `xi (1 - z) = xi z` (`_root_.RHTower.xi_one_sub`) and `xi (conj z) = conj (xi z)`!
          -- Let's check corpus lemma for `analyticOrderAt xi (1 - star z)`!
          sorry
        sorry
      sorry
    sorry
  sorry

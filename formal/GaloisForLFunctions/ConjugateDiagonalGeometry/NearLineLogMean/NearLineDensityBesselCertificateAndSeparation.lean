import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ClusteringLogMeanAndMollifierEquivalence
import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.LogStageBesselCertificate

/-!
# Near-Line Zero Density, Almost-All Bessel–Szegő Certificates, Planck Windows, and Strict Separation

Near-line zero-density hierarchy, critical-scale Planck window occupancy, double-log Bessel–Szegő
certificates, and bidirectional separation countermodels, paired with
`ClusteringLogMeanAndMollifierEquivalence`:

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
     explicit Bessel–Szegő certificate at `doubleLogDoorStage c m` (`0 < c < 1 / 48`) for every
     `N ≥ doorSqrtPrefix m`.

3. **Bidirectional no-go separation countermodels (`UnitWindowStripZeroModel`,
   `exists_clusteredPacketModel_cert_not_zeroDensity_not_logMean`,
   `exists_sparseUniformModel_logMean_not_cert`)**:
   Even under local Riemann–von Mangoldt `(1 / (2π)) log m + O(1)`, `> 68%` simple critical-line zeros,
   reflection symmetry, and uniform arbitrary-rate (`0 < r < 1`) Selberg exponential near-line zero
   density, almost-all unit-window certificates (`ModelWindowOccupancy`) neither imply `(D_zero)` nor
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

lemma sq_sum_le_card_mul_sum_sq {α : Type*} (s : Finset α) (f : α → ℝ) :
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
      set S_sum : ℝ := ∑ x ∈ s, f x
      set Q : ℝ := ∑ x ∈ s, (f x) ^ 2
      have hdiff : 0 ≤ n * (((n + 1) * ((f a) ^ 2 + Q)) - (f a + S_sum) ^ 2) := by
        have hident : n * (((n + 1) * ((f a) ^ 2 + Q)) - (f a + S_sum) ^ 2) =
            (n + 1) * (n * Q - S_sum ^ 2) + (n * f a - S_sum) ^ 2 := by ring
        rw [hident]
        have h1 : 0 ≤ n * Q - S_sum ^ 2 := sub_nonneg.mpr ih
        have h2 : 0 ≤ (n + 1) * (n * Q - S_sum ^ 2) := mul_nonneg (by linarith) h1
        linarith [sq_nonneg (n * f a - S_sum)]
      have hnonneg : 0 ≤ ((n + 1) * ((f a) ^ 2 + Q)) - (f a + S_sum) ^ 2 :=
        nonneg_of_mul_nonneg_right hdiff hn
      linarith

lemma finset_sum_union_le {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s₁ ∪ s₂, f a ≤ ∑ a ∈ s₁, f a + ∑ a ∈ s₂, f a := by
  have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  have hnn : 0 ≤ ∑ a ∈ s₁ ∩ s₂, f a := Finset.sum_nonneg fun a _ => hf a
  linarith

lemma finset_sum_biUnion_le {ι α : Type*} [DecidableEq α] (s : Finset ι)
    (t : ι → Finset α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (finset_sum_union_le (t i) (s.biUnion t) hf).trans (by linarith [ih])

lemma tendsto_one_div_const_mul_nhdsGT_zero {k : ℝ} (hk : 0 < k) :
    Tendsto (fun c : ℝ => 1 / (k * c)) (𝓝[>] 0) atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  rcases le_or_gt B 0 with hB | hB
  · exact eventually_nhdsWithin_of_forall fun c (hc : 0 < c) =>
      hB.trans (one_div_nonneg.mpr (mul_nonneg hk.le hc.le))
  · rw [Filter.Eventually, Metric.mem_nhdsWithin_iff]
    refine ⟨1 / (k * B), by positivity, fun c hc => ?_⟩
    simp only [Set.mem_setOf_eq]
    have hc_pos : 0 < c := hc.2
    have hc_lt : c < 1 / (k * B) := by
      have h := hc.1
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc_pos] at h
      exact h
    have hmul : k * c < 1 / B := by
      have h1 := mul_lt_mul_of_pos_left hc_lt hk
      rwa [show k * (1 / (k * B)) = 1 / B by field_simp [hk.ne']] at h1
    exact (le_div_iff₀ (mul_pos hk hc_pos)).mpr
      ((mul_comm B (k * c)).trans_le ((le_div_iff₀ hB).mp hmul.le))

lemma tendsto_one_div_atTop_nhdsGT_zero :
    Tendsto (fun A : ℝ => 1 / A) atTop (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨Metric.tendsto_atTop.mpr fun ε hε => ?_, ?_⟩
  · refine ⟨1 / ε + 1, fun A hA => ?_⟩
    have hA_pos : 0 < A := lt_of_lt_of_le (by positivity) hA
    rw [Real.dist_eq, sub_zero, abs_of_pos (one_div_pos.mpr hA_pos), one_div_lt hA_pos hε]
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
    exact one_div_pos.mpr hA

lemma tendsto_one_div_max_one_zero :
    Tendsto (fun A : ℝ => 1 / max A 1) atTop (𝓝 (0 : ℝ)) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  refine ⟨max 1 (1 / ε + 1), fun A hA => ?_⟩
  have hA1 : 1 ≤ A := (le_max_left _ _).trans hA
  have hAe : 1 / ε + 1 ≤ A := (le_max_right _ _).trans hA
  rw [max_eq_left hA1, Real.dist_eq, sub_zero, abs_of_pos (by positivity),
    one_div_lt (by positivity) hε]
  linarith

lemma log_two_lt_one : Real.log 2 < 1 := by
  linarith [Real.log_two_lt_d9]

lemma log_four_le_two' : Real.log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [h4, Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9]

lemma sq_log_le_four_mul' {x : ℝ} (hx : 1 ≤ x) :
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

lemma log_le_two_sqrt_of_pos' {x : ℝ} (hx : 0 < x) :
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
  have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans ((Nat.cast_le (α := ℝ)).mpr hm_lo)
  have hm_le_2V : (m : ℝ) ≤ 2 * V :=
    ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
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
  obtain ⟨⟨hr0_ρ, hr1_ρ, _, him_lt_m1⟩, hxi_ρ⟩ :=
    (_root_.RHTower.stripZeros_finite ((m' : ℝ) + 1)).mem_toFinset.mp hρ_mem.1
  have hm'_le_im : (m' : ℝ) ≤ ρ.im := hρ_mem.2
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
    rw [div_lt_div_iff₀ (by positivity) hlogV_pos, one_mul]
    have h1 := mul_lt_mul_of_pos_left hn_gt_logV hA
    rwa [← mul_assoc, mul_one_div_cancel hA.ne', one_mul] at h1
  have hu_pos : 0 < 1 / (n' : ℝ) := by positivity
  have hrel2 : 1 / (2 * (n' : ℝ)) = (1 / 2) * (1 / (n' : ℝ)) := by ring
  have hrel16 : 1 / (16 * (n' : ℝ)) = (1 / 16) * (1 / (n' : ℝ)) := by ring
  have hlo : 1 / 2 - zhukovskyMajorAxis n' < 2 * (z₀.re - 1 / 2) := by
    rw [zhukovskyMajorAxis_of_six_le hn6, hrel2]
    have h1 := (abs_le.mp hz₀_re_diff).1
    dsimp only [r] at h1
    rw [hrel16] at h1
    linarith [hρ₁_re, hA_gt_inv, h1, hu_pos]
  have hhi : 2 * (z₀.re - 1 / 2) < 1 / 2 + zhukovskyMajorAxis n' := by
    rw [zhukovskyMajorAxis_of_six_le hn6, hrel2]
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
    dsimp only [r] at h2
    rw [hrel16] at h2
    linarith [hvk_gt, hinv_le_A, h2, h3, hu_pos]
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
      rw [one_div_pow] at h2
      have h3 : C_tot / (2 : ℝ) ^ K = C_tot * (1 / (2 : ℝ) ^ K) := by ring
      have h4 : C_tot * (η / (4 * C_tot)) = η / 4 := by field_simp [hC_tot.ne']
      linarith
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
        -- Find `j < K` with `V / 2^(j+1) < z.im ≤ V / 2^j`.
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
          exact div_le_div_of_nonneg_left hV_pos.le (by positivity)
            (pow_le_pow_right₀ one_le_two (Nat.succ_le_of_lt hjK))
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
          div_le_div_of_nonneg_left hV_pos.le (by positivity)
            (pow_le_pow_right₀ one_le_two (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))
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
      refine (finset_sum_union_le _ _ fun _ => Nat.cast_nonneg _).trans ?_
      have hbi := finset_sum_biUnion_le (Finset.range K)
        (fun j => (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter
          (fun z => (κ / 2) / Real.log (V / (2 : ℝ) ^ (j + 1)) ≤ |z.re - 1 / 2|))
        (f := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ))
        (fun _ => Nat.cast_nonneg _)
      linarith [hbi]
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
      simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hprod_lim
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
      ∑ m ∈ Bad_occ, N_win m :=
    finset_sum_biUnion_le Bad_occ _ fun _ => Nat.cast_nonneg _
  have htot_le : ∑ z ∈ (shellZeros V (2 * V)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      ∑ z ∈ shellZeros V (V + 1), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) +
      ∑ m ∈ Bad_occ, N_win m := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => Nat.cast_nonneg _).trans ?_
    exact (finset_sum_union_le _ _ fun _ => Nat.cast_nonneg _).trans (by linarith [hbi_le])
  dsimp only [ε]
  linarith [htot_le, hcap, hcs]


/-! ## §3. Unconditional Planck-window and double-logarithmic Bessel–Szegő certificate survivors for `ζ` -/

private lemma shellRight_orderSum_le_windowZeros {T₁ T₂ d : ℝ} (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    (hd : 0 ≤ d) :
    (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)) ≤
      ∑ w ∈ (_root_.RHTower.windowZeros T₁ T₂).filter (fun w => 1 / 2 + d ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
  have hsub : (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re) ⊆
      (_root_.RHTower.windowZeros T₁ T₂).filter (fun w => 1 / 2 + d ≤ w.re) := by
    intro z hz
    obtain ⟨hz_sh, hre_d⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz_pos, him1⟩ := Finset.mem_filter.mp hz_sh
    obtain ⟨h0, h1, _, him2, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hz_pos
    rw [Finset.mem_filter, _root_.RHTower.mem_windowZeros_iff hT₁ hT]
    refine ⟨⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩,
      (_root_.RHTower.xi_zero_iff_zeta_zero_of_mem_strip h0 h1).mp hxi⟩, hre_d⟩
    · rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)]
      exact ⟨by linarith, by linarith⟩
    · rw [uIcc_of_le hT]
      exact ⟨him1.le, him2⟩
  calc ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
      = ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re),
          ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        obtain ⟨h0, h1, _, _, _⟩ :=
          _root_.RHTower.mem_stripFinsetPos.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
        rw [_root_.RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _

private lemma shellOrderSum_abs_ge_eq_two_mul_right (V₁ V₂ : ℝ) {b : ℝ} (hb : 0 < b) :
    (∑ z ∈ (shellZeros V₁ V₂).filter (fun z => b ≤ |z.re - 1 / 2|),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)) =
      2 * ∑ z ∈ (shellZeros V₁ V₂).filter (fun z => 1 / 2 + b ≤ z.re),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
  let t := shellZeros V₁ V₂
  let m : ℂ → ℝ := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
  let A := t.filter (fun z => b ≤ |z.re - 1 / 2|)
  have hsplit := (Finset.sum_filter_add_sum_filter_not A (fun z => 1 / 2 ≤ z.re) m).symm
  have hR : A.filter (fun z => 1 / 2 ≤ z.re) = t.filter (fun z => 1 / 2 + b ≤ z.re) := by
    ext z
    simp only [A, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hz, habs⟩, hge⟩
      rw [abs_of_nonneg (by linarith)] at habs
      exact ⟨hz, by linarith⟩
    · rintro ⟨hz, hge⟩
      refine ⟨⟨hz, ?_⟩, by linarith⟩
      rw [abs_of_nonneg (by linarith)]; linarith
  have hL : A.filter (fun z => ¬ 1 / 2 ≤ z.re) = t.filter (fun z => z.re ≤ 1 / 2 - b) := by
    ext z
    simp only [A, Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨hz, habs⟩, hlt⟩
      rw [abs_of_neg (by linarith)] at habs
      exact ⟨hz, by linarith⟩
    · rintro ⟨hz, hle⟩
      refine ⟨⟨hz, ?_⟩, by linarith⟩
      rw [abs_of_neg (by linarith)]; linarith
  have hbij : ∑ z ∈ t.filter (fun z => z.re ≤ 1 / 2 - b), m z =
      ∑ z ∈ t.filter (fun z => 1 / 2 + b ≤ z.re), m z := by
    refine Finset.sum_nbij' _root_.RHTower.lineReflect _root_.RHTower.lineReflect ?_ ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨lineReflect_mem_shellZeros hz.1,
        by rw [_root_.RHTower.lineReflect_re]; linarith [hz.2]⟩
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨lineReflect_mem_shellZeros hz.1,
        by rw [_root_.RHTower.lineReflect_re]; linarith [hz.2]⟩
    · intro z _; exact _root_.RHTower.lineReflect_involutive z
    · intro z _; exact _root_.RHTower.lineReflect_involutive z
    · intro z _; dsimp only [m]; rw [_root_.RHTower.xi_orderAt_lineReflect]
  change ∑ z ∈ A, m z = 2 * ∑ z ∈ t.filter (fun z => 1 / 2 + b ≤ z.re), m z
  rw [hsplit, hR, hL, hbij, two_mul]

private lemma mediumShell_orderSum_le {V₁ V₂ : ℝ} (hV₁ : 0 ≤ V₁) (h12 : V₁ ≤ V₂)
    (hlen : V₂ - V₁ ≤ 6) :
    ∑ z ∈ shellZeros V₁ V₂, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      48 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + Real.log (V₂ + 4)) := by
  set M₁ : ℝ := min V₂ (V₁ + 2)
  set M₂ : ℝ := min V₂ (V₁ + 4)
  have hcov : shellZeros V₁ V₂ ⊆
      shellZeros V₁ M₁ ∪ (shellZeros M₁ M₂ ∪ shellZeros M₂ V₂) := by
    intro z hz
    obtain ⟨hzS, him1⟩ := Finset.mem_filter.mp hz
    obtain ⟨hr0, hr1, him0, him2, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
    by_cases hc1 : z.im ≤ M₁
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0, hr1, him0, hc1, hxi⟩, him1⟩))
    · by_cases hc2 : z.im ≤ M₂
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
          ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0, hr1, him0, hc2, hxi⟩, not_le.mp hc1⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0, hr1, him0, him2, hxi⟩, not_le.mp hc2⟩))))
  have hM₁_lo : V₁ ≤ M₁ := le_min h12 (by linarith)
  have hM₂_lo : M₁ ≤ M₂ := min_le_min le_rfl (by linarith)
  have hM₂_hi : M₂ ≤ V₂ := min_le_left _ _
  have hs1 := shortShell_orderSum_le_log hV₁ hM₁_lo (by linarith [min_le_right V₂ (V₁ + 2)])
  have hs2 := shortShell_orderSum_le_log (hV₁.trans hM₁_lo) hM₂_lo (by
    dsimp only [M₁, M₂]
    rcases le_total V₂ (V₁ + 2) with hle | hgt
    · rw [min_eq_left hle, min_eq_left (hle.trans (by linarith))]; linarith
    · rw [min_eq_right hgt]; linarith [min_le_right V₂ (V₁ + 4)])
  have hs3 := shortShell_orderSum_le_log ((hV₁.trans hM₁_lo).trans hM₂_lo) hM₂_hi (by
    dsimp only [M₂]
    rcases le_total V₂ (V₁ + 4) with hle | hgt
    · rw [min_eq_left hle]; linarith
    · rw [min_eq_right hgt]; linarith)
  have hl1 : Real.log (M₁ + 4) ≤ Real.log (V₂ + 4) :=
    Real.log_le_log (by linarith) (by linarith [min_le_left V₂ (V₁ + 2)])
  have hl2 : Real.log (M₂ + 4) ≤ Real.log (V₂ + 4) :=
    Real.log_le_log (by linarith) (by linarith [hM₂_hi])
  have hu0 : ∑ z ∈ shellZeros V₁ V₂, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      ∑ z ∈ shellZeros V₁ M₁ ∪ (shellZeros M₁ M₂ ∪ shellZeros M₂ V₂),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => Nat.cast_nonneg _
  have hu1 := hu0.trans (finset_sum_union_le (shellZeros V₁ M₁)
    (shellZeros M₁ M₂ ∪ shellZeros M₂ V₂)
    (f := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ))
    (fun _ => Nat.cast_nonneg _))
  have hu2 := finset_sum_union_le (shellZeros M₁ M₂) (shellZeros M₂ V₂)
    (f := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)) (fun _ => Nat.cast_nonneg _)
  linarith [hu1, hu2, hs1, hs2, hs3, hl1, hl2]

lemma mediumCap_orderSum_le_logV {V V₁ V₂ : ℝ} (hV32 : 32 ≤ V) (hlog4 : 4 ≤ Real.log V)
    (hV₁ : 0 ≤ V₁) (h12 : V₁ ≤ V₂) (hlen : V₂ - V₁ ≤ 6) (hV₂_hi : V₂ ≤ 2 * V + 4) :
    ∑ z ∈ shellZeros V₁ V₂, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      48 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 2) * Real.log V := by
  have hm := mediumShell_orderSum_le hV₁ h12 hlen
  have hV_pos : 0 < V := by linarith
  have hsq : V₂ + 4 ≤ V ^ 2 := by
    have h1 : V₂ + 4 ≤ 3 * V := by linarith
    have h2 : 3 * V ≤ V * V := mul_le_mul_of_nonneg_right (by linarith) hV_pos.le
    calc V₂ + 4 ≤ 3 * V := h1
      _ ≤ V * V := h2
      _ = V ^ 2 := (sq V).symm
  have hlog_V₂ : Real.log (V₂ + 4) ≤ 2 * Real.log V := by
    calc Real.log (V₂ + 4) ≤ Real.log (V ^ 2) := Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log V := by rw [Real.log_pow]; push_cast; rfl
  have hc_log : |_root_.RHTower.xiLineTwoLogDerivConstant| ≤
      |_root_.RHTower.xiLineTwoLogDerivConstant| * Real.log V := by
    calc |_root_.RHTower.xiLineTwoLogDerivConstant|
        = |_root_.RHTower.xiLineTwoLogDerivConstant| * 1 := (mul_one _).symm
      _ ≤ |_root_.RHTower.xiLineTwoLogDerivConstant| * Real.log V :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  linarith [hm, hlog_V₂, hc_log]

/-- Extended dyadic-shell deep zero-multiplicity bound from Selberg's arbitrary-rate estimate. -/
lemma deepExtendedShell_orderSum_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C_d κ_r : ℝ, 0 < C_d ∧ 0 < κ_r ∧ ∀ᶠ V : ℝ in atTop,
      ∀ A : ℝ, 2 ≤ A → A ≤ κ_r * Real.log V →
        ∑ z ∈ (shellZeros (V - 4) (2 * V + 4)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
          C_d * (Real.exp (-(r * A)) / A) * V * Real.log V := by
  obtain ⟨r', hr'_def⟩ : ∃ x : ℝ, x = (r + 1) / 2 := ⟨_, rfl⟩
  obtain ⟨ε', hε'_def⟩ : ∃ x : ℝ, x = (1 - r) / 4 := ⟨_, rfl⟩
  have hr'0 : 0 < r' := by rw [hr'_def]; linarith
  have hr'1 : r' < 1 := by rw [hr'_def]; linarith
  have hε'_pos : 0 < ε' := by rw [hε'_def]; linarith
  have hε'_le1 : ε' ≤ 1 := by rw [hε'_def]; linarith
  obtain ⟨A_bv, K_bv, η_r, hA_bv, hK_bv, hη_pos, hη_lt, hbv_ev⟩ :=
    exists_selberg_arbitraryRate_nearLine_zeroDensity hr'0 hr'1 hε'_pos
  obtain ⟨K_log1, hK_log1_def⟩ : ∃ x : ℝ, x = 1 / η_r := ⟨_, rfl⟩
  have hK_log1 : 0 < K_log1 := by rw [hK_log1_def]; positivity
  obtain ⟨κ_r, hκ_def⟩ : ∃ x : ℝ, x = min (1 / 4) (η_r / (4 * r)) := ⟨_, rfl⟩
  have hκ_pos : 0 < κ_r := by rw [hκ_def]; exact lt_min (by norm_num) (by positivity)
  obtain ⟨C_d, hCd_def⟩ : ∃ x : ℝ, x = 2 * (1 + ε') * A_bv / Real.pi + 2 := ⟨_, rfl⟩
  have hCd_pos : 0 < C_d := by rw [hCd_def]; positivity
  obtain ⟨M_err, hMerr_def⟩ :
      ∃ x : ℝ, x = 96 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 2) + 8 * K_bv := ⟨_, rfl⟩
  have hMerr_pos : 0 < M_err := by rw [hMerr_def]; positivity
  refine ⟨C_d, κ_r, hCd_pos, hκ_pos, ?_⟩
  have ht_32 : Tendsto (fun V : ℝ => (3 / 2 : ℝ) * V) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have ht_pow : Tendsto (fun V : ℝ => V ^ (η_r / 2)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  filter_upwards [ht_32.eventually hbv_ev,
    eventually_ge_atTop (32 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 4,
    ht_pow.eventually_ge_atTop (M_err * K_log1 + 1)] with V hbv_V hV32 hlog4 hV_pow A hA2 hA_hi
  have hV_pos : 0 < V := by linarith
  have hV1 : 1 ≤ V := by linarith
  have hlogV_pos : 0 < Real.log V := by linarith
  obtain ⟨S, hS_def⟩ : ∃ x : ℝ, x = (3 / 2 : ℝ) * V := ⟨_, rfl⟩
  have hS_pos : 0 < S := by rw [hS_def]; positivity
  have hlogV_le_LS : Real.log V ≤ Real.log S :=
    Real.log_le_log hV_pos (by rw [hS_def]; linarith)
  have hLS_le_2logV : Real.log S ≤ 2 * Real.log V := by
    have h1 : Real.log S ≤ Real.log (2 * V) := Real.log_le_log hS_pos (by rw [hS_def]; linarith)
    rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
    linarith [h1, Real.log_two_lt_d9, hlog4]
  have hLS_pos : 0 < Real.log S := hlogV_pos.trans_le hlogV_le_LS
  obtain ⟨T₁, hT₁, T₂, hT₂, hbv_S⟩ := hbv_V
  rw [← hS_def] at hT₁ hT₂ hbv_S
  have hT₁_lo : V < T₁ := by linarith [hT₁.1, hS_def]
  have hT₁_hi : T₁ < V + 1 := by linarith [hT₁.2, hS_def]
  have hT₂_lo : 2 * V - 1 < T₂ := by linarith [hT₂.1, hS_def]
  have hT₂_hi : T₂ < 2 * V := by linarith [hT₂.2, hS_def]
  have hT₁2 : T₁ ≤ T₂ := by linarith
  obtain ⟨b_V, hbV_def⟩ : ∃ x : ℝ, x = A / Real.log V := ⟨_, rfl⟩
  rw [← hbV_def]
  have hbV_pos : 0 < b_V := by rw [hbV_def]; exact div_pos (by linarith) hlogV_pos
  have hcov : (shellZeros (V - 4) (2 * V + 4)).filter (fun z => b_V ≤ |z.re - 1 / 2|) ⊆
      shellZeros (V - 4) T₁ ∪
        ((shellZeros T₁ T₂).filter (fun z => b_V ≤ |z.re - 1 / 2|) ∪
          shellZeros T₂ (2 * V + 4)) := by
    intro z hz
    obtain ⟨hz_sh, hz_deep⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzS, him_lo⟩ := Finset.mem_filter.mp hz_sh
    obtain ⟨hr0_z, hr1_z, him0, him_hi, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
    by_cases hc1 : z.im ≤ T₁
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0_z, hr1_z, him0, hc1, hxi⟩, him_lo⟩))
    · by_cases hc2 : z.im ≤ T₂
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
            ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0_z, hr1_z, him0, hc2, hxi⟩, not_le.mp hc1⟩,
            hz_deep⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0_z, hr1_z, him0, him_hi, hxi⟩,
            not_le.mp hc2⟩))))
  have hcap1 := mediumCap_orderSum_le_logV hV32 hlog4 (V₁ := V - 4) (V₂ := T₁)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hcap2 := mediumCap_orderSum_le_logV hV32 hlog4 (V₁ := T₂) (V₂ := 2 * V + 4)
    (by linarith) (by linarith) (by linarith) le_rfl
  obtain ⟨a, ha_def⟩ : ∃ x : ℝ, x = A / (1 + ε') := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    rw [ha_def, one_le_div (by positivity)]; linarith [hε'_le1, hA2]
  have ha_pos : 0 < a := zero_lt_one.trans_le ha1
  have hA_q : A ≤ (1 / 4) * Real.log V := by
    have hk_le : κ_r ≤ 1 / 4 := by rw [hκ_def]; exact min_le_left _ _
    exact hA_hi.trans (mul_le_mul_of_nonneg_right hk_le hlogV_pos.le)
  have ha_hi : a ≤ (1 / (4 * (1 + min ε' 1))) * Real.log S := by
    rw [min_eq_left hε'_le1]
    have ha_V : a ≤ (1 / (4 * (1 + ε'))) * Real.log V := by
      rw [ha_def, div_le_iff₀ (by positivity)]
      calc A ≤ (1 / 4) * Real.log V := hA_q
        _ = (1 / (4 * (1 + ε'))) * Real.log V * (1 + ε') := by
            field_simp [(by positivity : (0 : ℝ) < 1 + ε').ne']
    exact ha_V.trans (mul_le_mul_of_nonneg_left hlogV_le_LS (by positivity))
  have hr'_mul_a : r * A ≤ r' * a := by
    rw [hr'_def, ha_def, hε'_def, mul_div_assoc', le_div_iff₀ (by linarith)]
    have hdiff : (r + 1) / 2 - r * (1 + (1 - r) / 4) = (1 - r) * (2 - r) / 4 := by ring
    have hpos_d : 0 ≤ (1 - r) * (2 - r) / 4 :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
    have hle_coef : r * (1 + (1 - r) / 4) ≤ (r + 1) / 2 := by linarith
    calc r * A * (1 + (1 - r) / 4) = (r * (1 + (1 - r) / 4)) * A := by ring
      _ ≤ ((r + 1) / 2) * A := mul_le_mul_of_nonneg_right hle_coef (by linarith)
  have hint_le : ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => b_V ≤ |z.re - 1 / 2|),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      (2 * (1 + ε') * A_bv / Real.pi) * (Real.exp (-(r * A)) / A) * V * Real.log V +
      8 * K_bv * Real.log V * V ^ (1 - η_r) := by
    rw [shellOrderSum_abs_ge_eq_two_mul_right T₁ T₂ hbV_pos]
    have hw_le := shellRight_orderSum_le_windowZeros (by linarith : 0 < T₁) hT₁2 hbV_pos.le
    have hfilt_sub : (_root_.RHTower.windowZeros T₁ T₂).filter (fun w => 1 / 2 + b_V ≤ w.re) ⊆
        (_root_.RHTower.windowZeros T₁ T₂).filter
          (fun w => 1 / 2 + (1 + ε') * (a / Real.log S) ≤ w.re) := by
      intro w hw
      obtain ⟨hw_mem, hw_re⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_filter.mpr ⟨hw_mem, ?_⟩
      have h1 : (1 + ε') * (a / Real.log S) = A / Real.log S := by
        rw [ha_def]; field_simp [(by positivity : (0 : ℝ) < 1 + ε').ne']
      have h2 : A / Real.log S ≤ b_V := by
        rw [hbV_def]
        exact div_le_div_of_nonneg_left (by linarith) hlogV_pos hlogV_le_LS
      linarith
    have hN_sub : ∑ w ∈ (_root_.RHTower.windowZeros T₁ T₂).filter (fun w => 1 / 2 + b_V ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) ≤
      ∑ w ∈ (_root_.RHTower.windowZeros T₁ T₂).filter
          (fun w => 1 / 2 + (1 + ε') * (a / Real.log S) ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub fun _ _ _ => Nat.cast_nonneg _
    have hbv := hbv_S a ha1 ha_hi (_root_.RHTower.windowZeros T₁ T₂)
      (_root_.RHTower.mem_windowZeros_iff (by linarith) hT₁2)
    obtain ⟨N_S, hNS_def⟩ : ∃ x : ℝ, x =
        ∑ w ∈ (_root_.RHTower.windowZeros T₁ T₂).filter
            (fun w => 1 / 2 + (1 + ε') * (a / Real.log S) ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ) := ⟨_, rfl⟩
    rw [← hNS_def] at hbv hN_sub
    have h2N : 2 * N_S ≤
        ((T₂ - T₁) * (A_bv * Real.exp (-(r' * a))) + K_bv * S ^ (1 - η_r)) *
          (Real.log S / (Real.pi * a)) := by
      have hm := mul_le_mul_of_nonneg_right hbv (by positivity : 0 ≤ Real.log S / (Real.pi * a))
      have hlhs : 2 * Real.pi * ((a / Real.log S) * N_S) * (Real.log S / (Real.pi * a)) = 2 * N_S := by
        field_simp [Real.pi_pos.ne', ha_pos.ne', hLS_pos.ne']
      rwa [hlhs] at hm
    have hterm1 : (T₂ - T₁) * (A_bv * Real.exp (-(r' * a))) * (Real.log S / (Real.pi * a)) ≤
        (2 * (1 + ε') * A_bv / Real.pi) * (Real.exp (-(r * A)) / A) * V * Real.log V := by
      have hlen_le : T₂ - T₁ ≤ V := by linarith
      have hexp_le : Real.exp (-(r' * a)) ≤ Real.exp (-(r * A)) :=
        Real.exp_le_exp.mpr (by linarith)
      have hprod1 : (T₂ - T₁) * (A_bv * Real.exp (-(r' * a))) ≤ V * (A_bv * Real.exp (-(r * A))) :=
        mul_le_mul hlen_le (mul_le_mul_of_nonneg_left hexp_le hA_bv.le)
          (by positivity) hV_pos.le
      have hprod2 : Real.log S / (Real.pi * a) ≤ (2 * Real.log V) * (1 + ε') / (Real.pi * A) := by
        have heq_a : Real.pi * a = Real.pi * A / (1 + ε') := by rw [ha_def]; ring
        rw [heq_a, div_div_eq_mul_div]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLS_le_2logV (by positivity)) (by positivity)
      calc (T₂ - T₁) * (A_bv * Real.exp (-(r' * a))) * (Real.log S / (Real.pi * a))
          ≤ (V * (A_bv * Real.exp (-(r * A)))) *
              ((2 * Real.log V) * (1 + ε') / (Real.pi * A)) :=
            mul_le_mul hprod1 hprod2 (by positivity) (by positivity)
        _ = (2 * (1 + ε') * A_bv / Real.pi) * (Real.exp (-(r * A)) / A) * V * Real.log V := by
            field_simp [Real.pi_pos.ne', (by linarith : (0 : ℝ) < A).ne']
    have hterm2 : K_bv * S ^ (1 - η_r) * (Real.log S / (Real.pi * a)) ≤
        8 * K_bv * Real.log V * V ^ (1 - η_r) := by
      have hpi_a : 1 ≤ Real.pi * a := by
        calc (1 : ℝ) ≤ 3 * 1 := by norm_num
          _ ≤ Real.pi * a := mul_le_mul Real.pi_gt_three.le ha1 zero_le_one Real.pi_pos.le
      have hdiv_le : Real.log S / (Real.pi * a) ≤ 2 * Real.log V :=
        (div_le_self hLS_pos.le hpi_a).trans hLS_le_2logV
      have hS_pow : S ^ (1 - η_r) ≤ 4 * V ^ (1 - η_r) := by
        have hS_le : S ≤ 2 * V := by rw [hS_def]; linarith
        calc S ^ (1 - η_r)
            ≤ (2 * V) ^ (1 - η_r) := Real.rpow_le_rpow hS_pos.le hS_le (by linarith)
          _ = (2 : ℝ) ^ (1 - η_r) * V ^ (1 - η_r) := Real.mul_rpow zero_le_two hV_pos.le
          _ ≤ 4 * V ^ (1 - η_r) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hV_pos.le _)
              calc (2 : ℝ) ^ (1 - η_r) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
                _ ≤ 4 := by norm_num
      calc K_bv * S ^ (1 - η_r) * (Real.log S / (Real.pi * a))
          ≤ K_bv * (4 * V ^ (1 - η_r)) * (2 * Real.log V) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hS_pow hK_bv.le) hdiv_le
              (by positivity) (by positivity)
        _ = 8 * K_bv * Real.log V * V ^ (1 - η_r) := by ring
    have h2right : 2 * ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + b_V ≤ z.re),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤ 2 * N_S :=
      mul_le_mul_of_nonneg_left (hw_le.trans hN_sub) zero_le_two
    have hexpand : ((T₂ - T₁) * (A_bv * Real.exp (-(r' * a))) + K_bv * S ^ (1 - η_r)) *
        (Real.log S / (Real.pi * a)) =
        (T₂ - T₁) * (A_bv * Real.exp (-(r' * a))) * (Real.log S / (Real.pi * a)) +
        K_bv * S ^ (1 - η_r) * (Real.log S / (Real.pi * a)) := add_mul _ _ _
    rw [hexpand] at h2N
    exact h2right.trans (h2N.trans (add_le_add hterm1 hterm2))
  have herr_all : 96 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 2) * Real.log V +
      8 * K_bv * Real.log V * V ^ (1 - η_r) ≤
      2 * (Real.exp (-(r * A)) / A) * V * Real.log V := by
    have h1_pow : (1 : ℝ) ≤ V ^ (1 - η_r) := Real.one_le_rpow hV1 (by linarith)
    have hcomb_M : 96 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 2) * Real.log V +
        8 * K_bv * Real.log V * V ^ (1 - η_r) ≤ M_err * Real.log V * V ^ (1 - η_r) := by
      have hc_nn : 0 ≤ 96 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 2) * Real.log V := by positivity
      have hm1 := mul_le_mul_of_nonneg_left h1_pow hc_nn
      rw [hMerr_def]
      have hring : (96 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 2) + 8 * K_bv) *
          Real.log V * V ^ (1 - η_r) =
          (96 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 2) * Real.log V) * V ^ (1 - η_r) +
          8 * K_bv * Real.log V * V ^ (1 - η_r) := by ring
      linarith
    have hA_pow : A ≤ K_log1 * V ^ (η_r / 4) := by
      have hexp_q : (η_r / 4) * Real.log V ≤ V ^ (η_r / 4) := by
        rw [Real.rpow_def_of_pos hV_pos, mul_comm (Real.log V)]
        linarith [Real.add_one_le_exp ((η_r / 4) * Real.log V)]
      have hmul_q := mul_le_mul_of_nonneg_left hexp_q hK_log1.le
      have hlhs_q : K_log1 * ((η_r / 4) * Real.log V) = (1 / 4) * Real.log V := by
        rw [hK_log1_def]; field_simp [hη_pos.ne']
      linarith [hA_q, hmul_q, hlhs_q]
    have hexp_pow : Real.exp (r * A) ≤ V ^ (η_r / 4) := by
      have hrA : r * A ≤ Real.log V * (η_r / 4) := by
        have hk_le : κ_r ≤ η_r / (4 * r) := by rw [hκ_def]; exact min_le_right _ _
        have h1 : A ≤ (η_r / (4 * r)) * Real.log V :=
          hA_hi.trans (mul_le_mul_of_nonneg_right hk_le hlogV_pos.le)
        have h2 := mul_le_mul_of_nonneg_left h1 hr0.le
        have heq : r * ((η_r / (4 * r)) * Real.log V) = Real.log V * (η_r / 4) := by
          field_simp [hr0.ne']
        rwa [heq] at h2
      rw [Real.rpow_def_of_pos hV_pos]
      exact Real.exp_le_exp.mpr hrA
    have hprod_le_V : M_err * V ^ (1 - η_r) * (A * Real.exp (r * A)) ≤ 2 * V := by
      have hp1 : A * Real.exp (r * A) ≤ K_log1 * V ^ (η_r / 4) * V ^ (η_r / 4) :=
        mul_le_mul hA_pow hexp_pow (Real.exp_pos _).le (by positivity)
      have hp2 : M_err * V ^ (1 - η_r) * (A * Real.exp (r * A)) ≤
          (M_err * K_log1) * (V ^ (1 - η_r) * V ^ (η_r / 4) * V ^ (η_r / 4)) := by
        calc M_err * V ^ (1 - η_r) * (A * Real.exp (r * A))
            ≤ M_err * V ^ (1 - η_r) * (K_log1 * V ^ (η_r / 4) * V ^ (η_r / 4)) :=
              mul_le_mul_of_nonneg_left hp1 (by positivity)
          _ = (M_err * K_log1) * (V ^ (1 - η_r) * V ^ (η_r / 4) * V ^ (η_r / 4)) := by ring
      have hrpow_eq : V ^ (1 - η_r) * V ^ (η_r / 4) * V ^ (η_r / 4) = V ^ (1 - η_r / 2) := by
        rw [← Real.rpow_add hV_pos, ← Real.rpow_add hV_pos]; congr 1; ring
      rw [hrpow_eq] at hp2
      have hp3 : (M_err * K_log1) * V ^ (1 - η_r / 2) ≤ V ^ (η_r / 2) * V ^ (1 - η_r / 2) :=
        mul_le_mul_of_nonneg_right (by linarith [hV_pow]) (Real.rpow_nonneg hV_pos.le _)
      have hrpow_V : V ^ (η_r / 2) * V ^ (1 - η_r / 2) = V := by
        rw [← Real.rpow_add hV_pos, show η_r / 2 + (1 - η_r / 2) = 1 by ring, Real.rpow_one]
      linarith [hp2, hp3, hrpow_V, hV_pos]
    have hdiv_le : M_err * V ^ (1 - η_r) ≤ 2 * (Real.exp (-(r * A)) / A) * V := by
      have hpos_AE : 0 < A * Real.exp (r * A) := mul_pos (by linarith) (Real.exp_pos _)
      have h1 := (le_div_iff₀ hpos_AE).mpr hprod_le_V
      have hrhs : 2 * V / (A * Real.exp (r * A)) = 2 * (Real.exp (-(r * A)) / A) * V := by
        rw [Real.exp_neg]; field_simp [(by linarith : (0 : ℝ) < A).ne', (Real.exp_pos (r * A)).ne']
      rwa [hrhs] at h1
    refine hcomb_M.trans ?_
    calc M_err * Real.log V * V ^ (1 - η_r)
        = (M_err * V ^ (1 - η_r)) * Real.log V := by ring
      _ ≤ (2 * (Real.exp (-(r * A)) / A) * V) * Real.log V :=
          mul_le_mul_of_nonneg_right hdiv_le hlogV_pos.le
      _ = 2 * (Real.exp (-(r * A)) / A) * V * Real.log V := by ring
  have hu0 : ∑ z ∈ (shellZeros (V - 4) (2 * V + 4)).filter (fun z => b_V ≤ |z.re - 1 / 2|),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      ∑ z ∈ shellZeros (V - 4) T₁ ∪
          ((shellZeros T₁ T₂).filter (fun z => b_V ≤ |z.re - 1 / 2|) ∪
            shellZeros T₂ (2 * V + 4)),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => Nat.cast_nonneg _
  have hu1 := hu0.trans (finset_sum_union_le (shellZeros (V - 4) T₁)
    ((shellZeros T₁ T₂).filter (fun z => b_V ≤ |z.re - 1 / 2|) ∪ shellZeros T₂ (2 * V + 4))
    (f := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ))
    (fun _ => Nat.cast_nonneg _))
  have hu2 := finset_sum_union_le
    ((shellZeros T₁ T₂).filter (fun z => b_V ≤ |z.re - 1 / 2|)) (shellZeros T₂ (2 * V + 4))
    (f := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)) (fun _ => Nat.cast_nonneg _)
  have hsum3 : ∑ z ∈ (shellZeros (V - 4) (2 * V + 4)).filter (fun z => b_V ≤ |z.re - 1 / 2|),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      (2 * (1 + ε') * A_bv / Real.pi) * (Real.exp (-(r * A)) / A) * V * Real.log V +
      2 * (Real.exp (-(r * A)) / A) * V * Real.log V := by
    have hcaps : ∑ z ∈ shellZeros (V - 4) T₁, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) +
        ∑ z ∈ shellZeros T₂ (2 * V + 4), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
        96 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 2) * Real.log V := by
      linarith [hcap1, hcap2]
    linarith [hu1, hu2, hcaps, hint_le, herr_all]
  exact hsum3.trans_eq (by rw [hCd_def]; ring)

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
  obtain ⟨C_d, κ_r, hCd_pos, hκ_pos, hd_ev⟩ := deepExtendedShell_orderSum_le hr0 hr1
  refine ⟨C_d, κ_r, hCd_pos, hκ_pos, ?_⟩
  filter_upwards [hd_ev, eventually_ge_atTop (16 : ℝ)] with V hV_d hV16 A B hA2 hA_hi hB_pos hB_hi
  have hlogV_pos : 0 < Real.log V := Real.log_pos (by linarith)
  have hB_div_le1 : B / Real.log V ≤ 1 := (div_le_one hlogV_pos).mpr hB_hi
  set B_ext := (shellZeros (V - 4) (2 * V + 4)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|)
  have hcov : {t ∈ Icc V (2 * V) |
      ∃ ρ : ℂ, _root_.RHTower.xi ρ = 0 ∧ t ≤ ρ.im ∧ ρ.im ≤ t + B / Real.log V ∧
        A / Real.log V ≤ |ρ.re - 1 / 2|} ⊆
      ⋃ z ∈ B_ext, Icc (z.im - B / Real.log V) z.im := by
    intro t ⟨ht_I, ρ, hxi, ht_le_im, him_le_tB, hρ_re⟩
    obtain ⟨hr0_z, hr1_z⟩ := _root_.RHTower.xi_zero_re_mem_open_unit hxi
    have hρ_B : ρ ∈ B_ext := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨_root_.RHTower.mem_stripFinsetPos.mpr
          ⟨hr0_z, hr1_z, by linarith [ht_I.1], by linarith [ht_I.2], hxi⟩,
          by linarith [ht_I.1]⟩,
        hρ_re⟩
    exact Set.mem_biUnion hρ_B ⟨by linarith, ht_le_im⟩
  have hcard_le : (B_ext.card : ℝ) ≤ C_d * (Real.exp (-(r * A)) / A) * V * Real.log V := by
    have h1 : (B_ext.card : ℝ) ≤ ∑ z ∈ B_ext, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun z hz => ?_
      have hxi : _root_.RHTower.xi z = 0 :=
        (_root_.RHTower.mem_stripFinsetPos.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2.2.2.2
      exact_mod_cast Nat.pos_of_ne_zero (_root_.RHTower.xi_order_toNat_ne_zero hxi)
    exact h1.trans (hV_d A hA2 hA_hi)
  calc volume {t ∈ Icc V (2 * V) |
          ∃ ρ : ℂ, _root_.RHTower.xi ρ = 0 ∧ t ≤ ρ.im ∧ ρ.im ≤ t + B / Real.log V ∧
            A / Real.log V ≤ |ρ.re - 1 / 2|}
      ≤ volume (⋃ z ∈ B_ext, Icc (z.im - B / Real.log V) z.im) := measure_mono hcov
    _ ≤ ∑ z ∈ B_ext, volume (Icc (z.im - B / Real.log V) z.im) :=
        measure_biUnion_finset_le B_ext _
    _ = ∑ _z ∈ B_ext, ENNReal.ofReal (B / Real.log V) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Real.volume_Icc, show z.im - (z.im - B / Real.log V) = B / Real.log V by ring]
    _ = ENNReal.ofReal ((B_ext.card : ℝ) * (B / Real.log V)) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (C_d * B * (Real.exp (-(r * A)) / A) * V) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (B_ext.card : ℝ) * (B / Real.log V)
            ≤ (C_d * (Real.exp (-(r * A)) / A) * V * Real.log V) * (B / Real.log V) :=
              mul_le_mul_of_nonneg_right hcard_le (by positivity)
          _ = C_d * B * (Real.exp (-(r * A)) / A) * V := by
              field_simp [hlogV_pos.ne']

/-- Fixed-parameter corollary of `planckWindow_nearLine_zeroFree_volume_le`: `C_r` is independent
of both `A ≥ 2` and `B > 0`. -/
theorem planckWindow_nearLine_zeroFree_volume_le_fixed {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C_r : ℝ, 0 < C_r ∧ ∀ A : ℝ, 2 ≤ A → ∀ B : ℝ, 0 < B → ∀ᶠ V : ℝ in atTop,
      volume {t ∈ Icc V (2 * V) |
        ∃ ρ : ℂ, _root_.RHTower.xi ρ = 0 ∧ t ≤ ρ.im ∧ ρ.im ≤ t + B / Real.log V ∧
          A / Real.log V ≤ |ρ.re - 1 / 2|} ≤
        ENNReal.ofReal (C_r * B * (Real.exp (-(r * A)) / A) * V) := by
  obtain ⟨C_r, κ_r, hCr_pos, hκ_pos, hev⟩ := planckWindow_nearLine_zeroFree_volume_le hr0 hr1
  refine ⟨C_r, hCr_pos, fun A hA2 B hB_pos => ?_⟩
  filter_upwards [hev,
    Real.tendsto_log_atTop.eventually_ge_atTop (max (A / κ_r) B)] with V hV hlog_ge
  have hA_hi : A ≤ κ_r * Real.log V := by
    have := (le_max_left _ _).trans hlog_ge
    have hm := mul_le_mul_of_nonneg_left this hκ_pos.le
    rwa [mul_div_cancel₀ A hκ_pos.ne'] at hm
  exact hV A B hA2 hA_hi hB_pos ((le_max_right _ _).trans hlog_ge)

/-- Double-logarithmic Zhukovsky stage `max 6 ⌈c * log(m + 5) / log(log(m + 64))⌉₊`. -/
def doubleLogDoorStage (c : ℝ) (m : ℕ) : ℕ :=
  max 6 (Nat.ceil (c * Real.log ((m + 5 : ℕ) : ℝ) / Real.log (Real.log ((m + 64 : ℕ) : ℝ))))

/-- Corridor margin `1 / (4 * doubleLogDoorStage c m)` at the double-logarithmic stage. -/
def doubleLogStageMargin (c : ℝ) (m : ℕ) : ℝ :=
  1 / (4 * (doubleLogDoorStage c m : ℝ))

private lemma one_lt_log_log_add_sixtyFour (m : ℕ) :
    1 < Real.log (Real.log ((m + 64 : ℕ) : ℝ)) := by
  have hexp_lt4 : Real.exp 1 < 4 := by
    have h1 : (2 / 3 : ℝ) ≤ Real.exp (-1 / 3) := by linarith [Real.add_one_le_exp (-1 / 3 : ℝ)]
    have h2 : (8 / 27 : ℝ) ≤ Real.exp (-1) := by
      calc (8 / 27 : ℝ) = (2 / 3 : ℝ) ^ (3 : ℕ) := by norm_num
        _ ≤ (Real.exp (-1 / 3)) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) h1 3
        _ = Real.exp (-1) := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (8 / 27 : ℝ) * Real.exp 1 ≤ 1 := by
      calc (8 / 27 : ℝ) * Real.exp 1
          ≤ Real.exp (-1) * Real.exp 1 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos 1).le
        _ = 1 := by rw [← Real.exp_add]; norm_num
    linarith
  have hlog64 : 4 < Real.log ((m + 64 : ℕ) : ℝ) := by
    have h64 : (2 : ℝ) ^ (6 : ℕ) ≤ ((m + 64 : ℕ) : ℝ) := by
      have : (64 : ℝ) ≤ ((m + 64 : ℕ) : ℝ) := by exact_mod_cast (show 64 ≤ m + 64 by omega)
      linarith [show (2 : ℝ) ^ (6 : ℕ) = 64 by norm_num]
    have hlog2 := Real.log_two_gt_d9
    have hl : Real.log ((2 : ℝ) ^ (6 : ℕ)) ≤ Real.log ((m + 64 : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) h64
    rw [Real.log_pow, Nat.cast_ofNat] at hl
    linarith
  have hexp_lt : Real.exp 1 < Real.log ((m + 64 : ℕ) : ℝ) := hexp_lt4.trans hlog64
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) hexp_lt

private lemma doubleLogDoorStage_le_logDoorStage {c : ℝ} (hc : 0 < c) (m : ℕ) :
    doubleLogDoorStage c m ≤ logDoorStage c m := by
  unfold doubleLogDoorStage logDoorStage
  refine max_le_max le_rfl (Nat.ceil_mono ?_)
  have h1 := (one_lt_log_log_add_sixtyFour m).le
  have hnn : 0 ≤ c * Real.log ((m + 5 : ℕ) : ℝ) :=
    mul_nonneg hc.le (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 5 by omega)))
  exact div_le_self hnn h1

/-- **Unconditional Almost-All Unit-Window Explicit Bessel–Szegő Certificate at the Double-Logarithmic
Stage (`almostAll_doubleLogStage_besselSzegoCertificate`).**
For every `0 < c < 1 / 48`, there exists `C_c > 0` such that eventually in `V`, for all except at
most `C_c * V / log(log V)` Burnol unit windows `m ∈ [⌈V⌉, ⌊2V⌋]`, the explicit order-`K`
Bessel–Szegő certificate built from `|𝒵_N(t)|²` at `doubleLogDoorStage c m` is strictly sectorial
on the unit circle across all prefixes `N ≥ doorSqrtPrefix m`. -/
theorem almostAll_doubleLogStage_besselSzegoCertificate {c : ℝ} (hc0 : 0 < c) (hc48 : c < 1 / 48) :
    ∃ C_c : ℝ, 0 < C_c ∧ ∀ᶠ V : ℝ in atTop,
      (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter (fun m =>
        ¬ ∀ N ≥ doorSqrtPrefix m, ∀ K : ℕ,
          2 * (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) ^ 2 *
              (1 - doubleLogStageMargin c m) ^ (K + 1) / doubleLogStageMargin c m < Real.pi / 2 →
          ∀ u : HTGeometry.UnitCircle,
            0 < (besselSzegoCertificate (doubleLogDoorStage c m) K
                (fun t => ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) u *
              centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
                (doubleLogDoorStage c m) N u).re)).card : ℝ) ≤
        C_c * V / Real.log (Real.log V) := by
  obtain ⟨C_d, κ_r, hCd_pos, hκ_pos, hd_ev⟩ :=
    deepExtendedShell_orderSum_le (r := 3 / 4) (by norm_num) (by norm_num)
  obtain ⟨m₁, htail_log⟩ := exists_logStage_tail_lt c hc0
  set δ_c : ℝ := 1 - 48 * c
  have hδc_pos : 0 < δ_c := by dsimp only [δ_c]; linarith
  refine ⟨3 * C_d, by positivity, ?_⟩
  have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hd_ev,
    eventually_ge_atTop (max 32 ((m₁ : ℝ) + 1)),
    ht_ll.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop
      (max 16 (max ((16 / κ_r) ^ 2 + 1) ((448 / δ_c) ^ 2 + 1)))]
    with V hV_d hV_ge hll2 hlog_ge
  have hV32 : 32 ≤ V := (le_max_left _ _).trans hV_ge
  have hVm₁ : (m₁ : ℝ) + 1 ≤ V := (le_max_right _ _).trans hV_ge
  have hV_pos : 0 < V := by linarith
  have hlog16 : 16 ≤ Real.log V := (le_max_left _ _).trans hlog_ge
  have hlog_κ : (16 / κ_r) ^ 2 + 1 ≤ Real.log V :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hlog_ge
  have hlog_δ : (448 / δ_c) ^ 2 + 1 ≤ Real.log V :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hlog_ge
  have hlogV_pos : 0 < Real.log V := by linarith
  have hll_pos : 0 < Real.log (Real.log V) := by linarith
  set A_V : ℝ := 2 * Real.log (Real.log V)
  have hAV_2 : 2 ≤ A_V := by dsimp only [A_V]; linarith
  have hll_le_rt : Real.log (Real.log V) ≤ 2 * Real.sqrt (Real.log V) :=
    log_le_two_sqrt_of_pos' hlogV_pos
  have hrt_log_pos : 0 < Real.sqrt (Real.log V) := Real.sqrt_pos.mpr hlogV_pos
  have hAV_hi : A_V ≤ κ_r * Real.log V := by
    have hrt_gt : 16 / κ_r < Real.sqrt (Real.log V) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 16 / κ_r)]
      exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
    have hmul : (16 / κ_r) * Real.sqrt (Real.log V) < Real.log V := by
      have h1 := mul_lt_mul_of_pos_right hrt_gt hrt_log_pos
      rwa [Real.mul_self_sqrt hlogV_pos.le] at h1
    have hmul_κ : 16 * Real.sqrt (Real.log V) < κ_r * Real.log V := by
      have h1 := mul_lt_mul_of_pos_left hmul hκ_pos
      rwa [← mul_assoc, mul_div_cancel₀ 16 hκ_pos.ne'] at h1
    dsimp only [A_V]
    linarith [hll_le_rt, hmul_κ, hrt_log_pos]
  -- Bound the deep shell count at `A_V = 2 * log(log V)`.
  set B_ext := (shellZeros (V - 4) (2 * V + 4)).filter (fun z => A_V / Real.log V ≤ |z.re - 1 / 2|)
  have hB_card : (B_ext.card : ℝ) ≤ (C_d / 2) * V / Real.log (Real.log V) := by
    have h1 : (B_ext.card : ℝ) ≤ ∑ z ∈ B_ext, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun z hz => ?_
      have hxi : _root_.RHTower.xi z = 0 :=
        (_root_.RHTower.mem_stripFinsetPos.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2.2.2.2
      exact_mod_cast Nat.pos_of_ne_zero (_root_.RHTower.xi_order_toNat_ne_zero hxi)
    have h2 := h1.trans (hV_d A_V hAV_2 hAV_hi)
    have hexp_le : Real.exp (-(3 / 4 * A_V)) ≤ (Real.log V)⁻¹ := by
      have hle_arg : -(3 / 4 * A_V) ≤ -Real.log (Real.log V) := by dsimp only [A_V]; linarith
      calc Real.exp (-(3 / 4 * A_V))
          ≤ Real.exp (-Real.log (Real.log V)) := Real.exp_le_exp.mpr hle_arg
        _ = (Real.log V)⁻¹ := by rw [Real.exp_neg, Real.exp_log hlogV_pos]
    calc (B_ext.card : ℝ)
        ≤ C_d * (Real.exp (-(3 / 4 * A_V)) / A_V) * V * Real.log V := h2
      _ ≤ C_d * ((Real.log V)⁻¹ / A_V) * V * Real.log V := by
          refine mul_le_mul_of_nonneg_right ?_ hlogV_pos.le
          refine mul_le_mul_of_nonneg_right ?_ hV_pos.le
          refine mul_le_mul_of_nonneg_left ?_ hCd_pos.le
          exact div_le_div_of_nonneg_right hexp_le (by linarith [hAV_2])
      _ = (C_d / 2) * V / Real.log (Real.log V) := by
          dsimp only [A_V]
          field_simp [hlogV_pos.ne', hll_pos.ne']
  -- Every window failing the double-log certificate must contain a deep zero in `burnolUnitXiZeros m`.
  set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
  set Bad_cert := I_V.filter (fun m =>
    ¬ ∀ N ≥ doorSqrtPrefix m, ∀ K : ℕ,
      2 * (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) ^ 2 *
          (1 - doubleLogStageMargin c m) ^ (K + 1) / doubleLogStageMargin c m < Real.pi / 2 →
      ∀ u : HTGeometry.UnitCircle,
        0 < (besselSzegoCertificate (doubleLogDoorStage c m) K
            (fun t => ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) u *
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
            (doubleLogDoorStage c m) N u).re)
  have hcert_of_free : ∀ m ∈ I_V,
      (¬ ∃ ρ ∈ burnolUnitXiZeros m, A_V / Real.log V ≤ |ρ.re - 1 / 2|) →
      m ∉ Bad_cert := by
    intro m hm_I hfree hm_bad
    have hnot := (Finset.mem_filter.mp hm_bad).2
    apply hnot
    intro N hN K hK u
    obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
    have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans ((Nat.cast_le (α := ℝ)).mpr hm_lo)
    have hm_le_2V : (m : ℝ) ≤ 2 * V :=
      ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
    have hm_m₁ : m₁ ≤ m := (Nat.cast_lt.mp (by linarith : (m₁ : ℝ) < (m : ℝ))).le
    have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorSqrtPrefix m).trans hN)
    set n_m : ℕ := doubleLogDoorStage c m
    set n : ℝ := (n_m : ℝ)
    have hn6 : 6 ≤ n_m := le_max_left 6 _
    have hnR : (6 : ℝ) ≤ n := by dsimp only [n]; exact_mod_cast hn6
    have hn_le_log : n_m ≤ logDoorStage c m := doubleLogDoorStage_le_logDoorStage hc0 m
    have hlog_st_pos : (0 : ℝ) < (logDoorStage c m : ℝ) := by
      linarith [six_le_logDoorStage_real c m]
    have htail_n : thetaStripTailBound N < burnolGoodLowerConst * Real.exp (-((m + 3 : ℕ) : ℝ)) *
        ((1 / (16 * n)) / 8) ^
          (∑ w ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi w).toNat) := by
      refine (htail_log m hm_m₁ N hN).trans_le ?_
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _)
        (mul_nonneg burnolGoodLowerConst_pos.le (Real.exp_pos _).le)
      have hn_cast : n ≤ (logDoorStage c m : ℝ) := Nat.cast_le.mpr hn_le_log
      exact div_le_div_of_nonneg_right
        (one_div_le_one_div_of_le (by positivity) (by linarith)) (by norm_num)
    -- Bound `32 * n * log(log V) ≤ log V`.
    have h32n : 32 * n * Real.log (Real.log V) ≤ Real.log V := by
      have hm5_le : Real.log ((m + 5 : ℕ) : ℝ) ≤ (3 / 2) * Real.log V := by
        have h1 : ((m + 5 : ℕ) : ℝ) ≤ 4 * V := by push_cast; linarith
        have h2 : Real.log ((m + 5 : ℕ) : ℝ) ≤ Real.log (4 * V) :=
          Real.log_le_log (by positivity) h1
        rw [Real.log_mul (by norm_num) hV_pos.ne'] at h2
        linarith [h2, log_four_le_two', hlog16]
      have hll_m64 : Real.log (Real.log V) ≤ Real.log (Real.log ((m + 64 : ℕ) : ℝ)) := by
        have h1 : V ≤ ((m + 64 : ℕ) : ℝ) := by push_cast; linarith
        exact Real.log_le_log hlogV_pos (Real.log_le_log hV_pos h1)
      have hll_m64_pos : 0 < Real.log (Real.log ((m + 64 : ℕ) : ℝ)) := hll_pos.trans_le hll_m64
      have hn_ub : n ≤ c * ((3 / 2) * Real.log V) / Real.log (Real.log V) + 7 := by
        have hceil : (Nat.ceil (c * Real.log ((m + 5 : ℕ) : ℝ) /
            Real.log (Real.log ((m + 64 : ℕ) : ℝ))) : ℝ) ≤
            c * Real.log ((m + 5 : ℕ) : ℝ) / Real.log (Real.log ((m + 64 : ℕ) : ℝ)) + 1 :=
          (Nat.ceil_lt_add_one (by positivity)).le
        have hdiv : c * Real.log ((m + 5 : ℕ) : ℝ) / Real.log (Real.log ((m + 64 : ℕ) : ℝ)) ≤
            c * ((3 / 2) * Real.log V) / Real.log (Real.log V) := by
          calc c * Real.log ((m + 5 : ℕ) : ℝ) / Real.log (Real.log ((m + 64 : ℕ) : ℝ))
              ≤ c * ((3 / 2) * Real.log V) / Real.log (Real.log ((m + 64 : ℕ) : ℝ)) :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm5_le hc0.le) hll_m64_pos.le
            _ ≤ c * ((3 / 2) * Real.log V) / Real.log (Real.log V) :=
                div_le_div_of_nonneg_left (by positivity) hll_pos hll_m64
        dsimp only [n, n_m, doubleLogDoorStage]
        rw [Nat.cast_max, Nat.cast_ofNat]
        have hnn_div : 0 ≤ c * ((3 / 2) * Real.log V) / Real.log (Real.log V) := by positivity
        exact max_le (by linarith) (by linarith)
      have hmul_ub : 32 * n * Real.log (Real.log V) ≤
          48 * c * Real.log V + 224 * Real.log (Real.log V) := by
        have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn_ub (by norm_num : (0 : ℝ) ≤ 32)) hll_pos.le
        have hrhs : 32 * (c * ((3 / 2) * Real.log V) / Real.log (Real.log V) + 7) *
            Real.log (Real.log V) = 48 * c * Real.log V + 224 * Real.log (Real.log V) := by
          field_simp [hll_pos.ne']; ring
        rwa [hrhs] at hm
      have h224 : 224 * Real.log (Real.log V) ≤ δ_c * Real.log V := by
        have hrt_gt : 448 / δ_c < Real.sqrt (Real.log V) := by
          rw [← Real.sqrt_sq (by positivity : 0 ≤ 448 / δ_c)]
          exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
        have hmul : (448 / δ_c) * Real.sqrt (Real.log V) < Real.log V := by
          have h1 := mul_lt_mul_of_pos_right hrt_gt hrt_log_pos
          rwa [Real.mul_self_sqrt hlogV_pos.le] at h1
        have hmul_δ : 448 * Real.sqrt (Real.log V) < δ_c * Real.log V := by
          have h1 := mul_lt_mul_of_pos_left hmul hδc_pos
          rwa [← mul_assoc, mul_div_cancel₀ 448 hδc_pos.ne'] at h1
        linarith [hll_le_rt, hmul_δ]
      dsimp only [δ_c] at h224
      linarith
    have hAV_le_16n : A_V / Real.log V ≤ 1 / (16 * n) := by
      dsimp only [A_V]
      rw [div_le_div_iff₀ hlogV_pos (by positivity)]
      linarith
    set W := centeredThetaWindow (burnolUnitLower_le_upper m) N hbdry
    have hcorr : W.InCorridor n_m (doubleLogStageMargin c m) := by
      intro z hz
      obtain ⟨hz_rect, hz_zero⟩ := (mem_centeredThetaWindow_iff _ N hbdry z).mp hz
      obtain ⟨w, hw, hdist⟩ := exists_xiZero_near_thetaZero m N (r := 1 / (16 * n))
        (by positivity) htail_n hz_rect hz_zero
      have hw_lt : |w.re - 1 / 2| < A_V / Real.log V := by
        by_contra hge; exact hfree ⟨w, hw, not_lt.mp hge⟩
      have hre_close : |z.re - w.re| ≤ 1 / (16 * n) := by
        have := Complex.abs_re_le_norm (z - w)
        rw [Complex.sub_re] at this; linarith
      unfold doubleLogStageMargin
      rw [zhukovskyMajorAxis_of_six_le hn6]
      have hzw : z.re - 1 / 2 ≤ |w.re - 1 / 2| + 1 / (16 * n) := by
        linarith [le_abs_self (w.re - 1 / 2), (abs_le.mp hre_close).2]
      have hfinal : 1 / 2 - (1 / 2 - 1 / (2 * n)) - 1 / (4 * n) = 4 * (1 / (16 * n)) := by
        field_simp; ring
      dsimp only [n, n_m] at hfinal ⊢
      rw [hfinal]
      linarith [hw_lt, hAV_le_16n, hzw]
    have hη : 0 < doubleLogStageMargin c m := by unfold doubleLogStageMargin; positivity
    have hη2 : doubleLogStageMargin c m ≤ 1 / 2 := by
      unfold doubleLogStageMargin
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    rw [← centeredThetaWindow_degree (burnolUnitLower_le_upper m) N hbdry] at hK
    have hpos := hcorr.besselSzegoCertificate_mul_loop_pos
      (eval_centeredThetaDifferencePoly_eq_window (burnolUnitLower_le_upper m) N hbdry) hη hη2 hK u
    have hE : (fun t => ‖W.expSum t‖ ^ 2) =
        fun t => ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 :=
      funext fun t => by rw [centeredThetaWindow_expSum]
    rwa [hE] at hpos
  -- Cover `Bad_cert` by `B_ext.biUnion (fun z => Finset.Icc (⌊z.im⌋₊ - 2) (⌊z.im⌋₊ + 3))`.
  have hsub_bad : Bad_cert ⊆
      B_ext.biUnion (fun z => Finset.Icc (Nat.floor z.im - 2) (Nat.floor z.im + 3)) := by
    intro m hm
    have hm_I := (Finset.mem_filter.mp hm).1
    obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
    have hex : ∃ ρ ∈ burnolUnitXiZeros m, A_V / Real.log V ≤ |ρ.re - 1 / 2| := by
      by_contra hfree; exact hcert_of_free m hm_I hfree hm
    obtain ⟨ρ, hρ_Z, hρ_deep⟩ := hex
    obtain ⟨⟨hr0, hr1, hy1, hy2⟩, hxi⟩ := (mem_burnolUnitXiZeros_iff m ρ).mp hρ_Z
    have hy1_lo := sub_three_le_burnolUnitLower m
    have hy2_hi := (burnolUnit_coords m).2.2.2.1
    have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans ((Nat.cast_le (α := ℝ)).mpr hm_lo)
    have hm_le_2V : (m : ℝ) ≤ 2 * V :=
      ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
    have him_pos : 0 < ρ.im := by linarith
    have hρ_B : ρ ∈ B_ext := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨_root_.RHTower.mem_stripFinsetPos.mpr
          ⟨hr0, hr1, him_pos, by linarith, hxi⟩, by linarith⟩,
        hρ_deep⟩
    refine Finset.mem_biUnion.mpr ⟨ρ, hρ_B, ?_⟩
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
  have hcard_nat : Bad_cert.card ≤ 6 * B_ext.card := by
    calc Bad_cert.card
        ≤ (B_ext.biUnion (fun z => Finset.Icc (Nat.floor z.im - 2) (Nat.floor z.im + 3))).card :=
          Finset.card_le_card hsub_bad
      _ ≤ ∑ z ∈ B_ext, (Finset.Icc (Nat.floor z.im - 2) (Nat.floor z.im + 3)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ B_ext, 6 := Finset.sum_le_sum fun z _ => by rw [Nat.card_Icc]; omega
      _ = 6 * B_ext.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hcast : (Bad_cert.card : ℝ) ≤ 6 * (B_ext.card : ℝ) := by exact_mod_cast hcard_nat
  calc (Bad_cert.card : ℝ)
      ≤ 6 * ((C_d / 2) * V / Real.log (Real.log V)) :=
        hcast.trans (mul_le_mul_of_nonneg_left hB_card (by norm_num))
    _ = 3 * C_d * V / Real.log (Real.log V) := by ring


/-! ## §4. Bidirectional no-go separation countermodels under RvM, simple critical majority, and Selberg density -/

/-- Abstract unit-window critical-strip zero model obeying reflection symmetry, local Riemann–von
Mangoldt asymptotics `(1 / (2π)) log m + O(1)`, `≥ 68%` simple critical-line zeros, and uniform
arbitrary-rate (`0 < r < 1`) Selberg exponential near-line zero density. -/
structure UnitWindowStripZeroModel where
  Z : ℕ → Finset ℂ
  mult : ℂ → ℕ
  in_unit_strip : ∀ m : ℕ, ∀ z ∈ Z m, 0 < z.re ∧ z.re < 1 ∧ (m : ℝ) < z.im ∧ z.im < (m : ℝ) + 1
  mult_pos : ∀ m : ℕ, ∀ z ∈ Z m, 0 < mult z
  refl_mem : ∀ m : ℕ, ∀ z ∈ Z m, 1 - star z ∈ Z m
  refl_mult : ∀ m : ℕ, ∀ z ∈ Z m, mult (1 - star z) = mult z
  local_rvm : ∃ C_rvm : ℝ, 0 ≤ C_rvm ∧ ∀ m : ℕ, 16 ≤ m →
    |((∑ z ∈ Z m, mult z : ℕ) : ℝ) - Real.log (m : ℝ) / (2 * Real.pi)| ≤ C_rvm
  critical_simple_majority : ∀ᶠ m : ℕ in atTop,
    (17 / 25 : ℝ) * ((∑ z ∈ Z m, mult z : ℕ) : ℝ) ≤
      (((Z m).filter (fun z => z.re = 1 / 2 ∧ mult z = 1)).card : ℝ)
  selberg_arbitrary_rate : ∀ r : ℝ, 0 < r → r < 1 →
    ∃ C_s : ℝ, 0 < C_s ∧ ∀ᶠ V : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
      2 * Real.pi * ((a / Real.log V) *
        ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ z ∈ (Z m).filter (fun z => 1 / 2 + a / Real.log V ≤ z.re), (mult z : ℝ)) ≤
        C_s * Real.exp (-(r * a)) * V

/-- Model analogue of `(D_win)` / almost-all unit-window certificates. -/
def UnitWindowStripZeroModel.WindowOccupancy (M : UnitWindowStripZeroModel) : Prop :=
  ∃ δ : ℝ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∀ A : ℝ, 0 < A → ∀ᶠ V : ℝ in atTop,
      (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
        (fun m => ∃ z ∈ M.Z m, A / Real.log V ≤ |z.re - 1 / 2|)).card : ℝ) ≤ δ A * V

/-- Model analogue of `(D_zero)` (log-free near-line zero-multiplicity density). -/
def UnitWindowStripZeroModel.LogFreeZeroDensity (M : UnitWindowStripZeroModel) : Prop :=
  ∃ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ A : ℝ, 0 < A → ∀ᶠ V : ℝ in atTop,
      ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        ∑ z ∈ (M.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|), (M.mult z : ℝ) ≤
          ε A * V

/-- Model analogue of `(L)` (off-line horizontal moment `o(V)`). -/
def UnitWindowStripZeroModel.HorizontalMomentLittleO (M : UnitWindowStripZeroModel) : Prop :=
  Tendsto (fun V : ℝ => V⁻¹ *
    ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
      ∑ z ∈ (M.Z m).filter (fun z => 1 / 2 < z.re), (M.mult z : ℝ) * (z.re - 1 / 2))
    atTop (𝓝 0)

/-- Model analogue of `100%` critical-scale clustering (`o(V log V)` beyond `κ / log V`). -/
def UnitWindowStripZeroModel.CriticalClustering (M : UnitWindowStripZeroModel) : Prop :=
  ∀ κ : ℝ, 0 < κ →
    Tendsto (fun V : ℝ =>
      (∑ m ∈ Finset.range (Nat.floor V + 1),
        ∑ z ∈ (M.Z m).filter (fun z => κ / Real.log V ≤ |z.re - 1 / 2|), (M.mult z : ℝ)) /
      (V * Real.log V)) atTop (𝓝 0)

def critPt (m n k : ℕ) : ℂ :=
  ⟨1 / 2, (m : ℝ) + 1 / 2 + ((k + 1 : ℕ) : ℝ) / (2 * ((n + 2 : ℕ) : ℝ))⟩

def rightPt (m q : ℕ) (d : ℝ) (k : ℕ) : ℂ :=
  ⟨1 / 2 + d, (m : ℝ) + ((k + 1 : ℕ) : ℝ) / (2 * ((q + 2 : ℕ) : ℝ))⟩

def leftPt (m q : ℕ) (d : ℝ) (k : ℕ) : ℂ :=
  ⟨1 / 2 - d, (m : ℝ) + ((k + 1 : ℕ) : ℝ) / (2 * ((q + 2 : ℕ) : ℝ))⟩

/-- Parametrized reflection-symmetric unit-window zero packet with `n` simple critical zeros and
`q` simple conjugate pairs at `1/2 ± d`. -/
def packetWin (m n q : ℕ) (d : ℝ) : Finset ℂ :=
  (Finset.range n).image (critPt m n) ∪
    ((Finset.range q).image (rightPt m q d) ∪ (Finset.range q).image (leftPt m q d))

lemma critPt_re (m n k : ℕ) : (critPt m n k).re = 1 / 2 := rfl
lemma rightPt_re (m q : ℕ) (d : ℝ) (k : ℕ) : (rightPt m q d k).re = 1 / 2 + d := rfl
lemma leftPt_re (m q : ℕ) (d : ℝ) (k : ℕ) : (leftPt m q d k).re = 1 / 2 - d := rfl

lemma critPt_inj (m n : ℕ) : Function.Injective (critPt m n) := by
  intro k₁ k₂ h
  have him := congrArg Complex.im h
  dsimp only [critPt] at him
  have h1 : ((k₁ + 1 : ℕ) : ℝ) / (2 * ((n + 2 : ℕ) : ℝ)) =
      ((k₂ + 1 : ℕ) : ℝ) / (2 * ((n + 2 : ℕ) : ℝ)) := by linarith
  have h2 : ((k₁ + 1 : ℕ) : ℝ) = ((k₂ + 1 : ℕ) : ℝ) :=
    (div_left_inj' (by positivity)).mp h1
  exact Nat.succ.inj (Nat.cast_inj.mp h2)

lemma rightPt_inj (m q : ℕ) (d : ℝ) : Function.Injective (rightPt m q d) := by
  intro k₁ k₂ h
  have him := congrArg Complex.im h
  dsimp only [rightPt] at him
  have h1 : ((k₁ + 1 : ℕ) : ℝ) / (2 * ((q + 2 : ℕ) : ℝ)) =
      ((k₂ + 1 : ℕ) : ℝ) / (2 * ((q + 2 : ℕ) : ℝ)) := by linarith
  have h2 : ((k₁ + 1 : ℕ) : ℝ) = ((k₂ + 1 : ℕ) : ℝ) :=
    (div_left_inj' (by positivity)).mp h1
  exact Nat.succ.inj (Nat.cast_inj.mp h2)

lemma leftPt_inj (m q : ℕ) (d : ℝ) : Function.Injective (leftPt m q d) := by
  intro k₁ k₂ h
  have him := congrArg Complex.im h
  dsimp only [leftPt] at him
  have h1 : ((k₁ + 1 : ℕ) : ℝ) / (2 * ((q + 2 : ℕ) : ℝ)) =
      ((k₂ + 1 : ℕ) : ℝ) / (2 * ((q + 2 : ℕ) : ℝ)) := by linarith
  have h2 : ((k₁ + 1 : ℕ) : ℝ) = ((k₂ + 1 : ℕ) : ℝ) :=
    (div_left_inj' (by positivity)).mp h1
  exact Nat.succ.inj (Nat.cast_inj.mp h2)

lemma packetWin_in_unit_strip {m n q : ℕ} {d : ℝ}
    (hd : q = 0 ∨ (0 < d ∧ d < 1 / 2)) :
    ∀ z ∈ packetWin m n q d, 0 < z.re ∧ z.re < 1 ∧ (m : ℝ) < z.im ∧ z.im < (m : ℝ) + 1 := by
  intro z hz
  unfold packetWin at hz
  rcases Finset.mem_union.mp hz with hc | hrl
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    have hk_lt : k < n := Finset.mem_range.mp hk
    have hdiv_pos : 0 < ((k + 1 : ℕ) : ℝ) / (2 * ((n + 2 : ℕ) : ℝ)) := by positivity
    have hdiv_lt : ((k + 1 : ℕ) : ℝ) / (2 * ((n + 2 : ℕ) : ℝ)) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      have : ((k + 1 : ℕ) : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 < n + 2)
      linarith
    dsimp only [critPt]
    exact ⟨by norm_num, by norm_num, by linarith, by linarith⟩
  · rcases hd with rfl | ⟨hd0, hd_half⟩
    · simp at hrl
    · rcases Finset.mem_union.mp hrl with hr | hl
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
        have hk_lt : k < q := Finset.mem_range.mp hk
        have hdiv_pos : 0 < ((k + 1 : ℕ) : ℝ) / (2 * ((q + 2 : ℕ) : ℝ)) := by positivity
        have hdiv_lt : ((k + 1 : ℕ) : ℝ) / (2 * ((q + 2 : ℕ) : ℝ)) < 1 := by
          rw [div_lt_one (by positivity)]
          have : ((k + 1 : ℕ) : ℝ) < ((q + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 < q + 2)
          linarith
        dsimp only [rightPt]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hl
        have hk_lt : k < q := Finset.mem_range.mp hk
        have hdiv_pos : 0 < ((k + 1 : ℕ) : ℝ) / (2 * ((q + 2 : ℕ) : ℝ)) := by positivity
        have hdiv_lt : ((k + 1 : ℕ) : ℝ) / (2 * ((q + 2 : ℕ) : ℝ)) < 1 := by
          rw [div_lt_one (by positivity)]
          have : ((k + 1 : ℕ) : ℝ) < ((q + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 < q + 2)
          linarith
        dsimp only [leftPt]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma packetWin_refl_mem (m n q : ℕ) (d : ℝ) :
    ∀ z ∈ packetWin m n q d, 1 - star z ∈ packetWin m n q d := by
  intro z hz
  unfold packetWin at hz ⊢
  rcases Finset.mem_union.mp hz with hc | hrl
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨k, hk, ?_⟩))
    refine Complex.ext ?_ ?_
    · simp only [critPt, Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]; ring
    · simp only [critPt, Complex.sub_im, Complex.one_im, Complex.star_def, Complex.conj_im,
        zero_sub, neg_neg]
  · rcases Finset.mem_union.mp hrl with hr | hl
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
      refine Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨k, hk, ?_⟩))))
      refine Complex.ext ?_ ?_
      · simp only [rightPt, leftPt, Complex.sub_re, Complex.one_re, Complex.star_def,
          Complex.conj_re]; ring
      · simp only [rightPt, leftPt, Complex.sub_im, Complex.one_im, Complex.star_def,
          Complex.conj_im, zero_sub, neg_neg]
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hl
      refine Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
        (Finset.mem_image.mpr ⟨k, hk, ?_⟩))))
      refine Complex.ext ?_ ?_
      · simp only [rightPt, leftPt, Complex.sub_re, Complex.one_re, Complex.star_def,
          Complex.conj_re]; ring
      · simp only [rightPt, leftPt, Complex.sub_im, Complex.one_im, Complex.star_def,
          Complex.conj_im, zero_sub, neg_neg]

private lemma packetWin_disjoint {m n q : ℕ} {d : ℝ} (hd : q = 0 ∨ 0 < d) :
    Disjoint ((Finset.range n).image (critPt m n))
      ((Finset.range q).image (rightPt m q d) ∪ (Finset.range q).image (leftPt m q d)) ∧
    Disjoint ((Finset.range q).image (rightPt m q d)) ((Finset.range q).image (leftPt m q d)) := by
  rcases hd with rfl | hd0
  · simp
  · refine ⟨Finset.disjoint_left.mpr fun z hzc hzrl => ?_,
      Finset.disjoint_left.mpr fun z hzr hzl => ?_⟩
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hzc
      rcases Finset.mem_union.mp hzrl with hzr | hzl
      · obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hzr
        have hre := congrArg Complex.re heq
        rw [rightPt_re, critPt_re] at hre; linarith
      · obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hzl
        have hre := congrArg Complex.re heq
        rw [leftPt_re, critPt_re] at hre; linarith
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hzr
      obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hzl
      have hre := congrArg Complex.re heq
      rw [leftPt_re, rightPt_re] at hre; linarith

lemma packetWin_card {m n q : ℕ} {d : ℝ} (hd : q = 0 ∨ 0 < d) :
    (packetWin m n q d).card = n + 2 * q := by
  obtain ⟨hd1, hd2⟩ := packetWin_disjoint (m := m) (n := n) hd
  unfold packetWin
  rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
    Finset.card_image_of_injective _ (critPt_inj m n),
    Finset.card_image_of_injective _ (rightPt_inj m q d),
    Finset.card_image_of_injective _ (leftPt_inj m q d),
    Finset.card_range, Finset.card_range]
  omega

lemma packetWin_filter_crit_card {m n q : ℕ} {d : ℝ} (hd : q = 0 ∨ 0 < d) :
    ((packetWin m n q d).filter (fun z => z.re = 1 / 2 ∧ (1 : ℕ) = 1)).card = n := by
  have heq : (packetWin m n q d).filter (fun z => z.re = 1 / 2 ∧ (1 : ℕ) = 1) =
      (Finset.range n).image (critPt m n) := by
    ext z
    simp only [Finset.mem_filter, and_true]
    constructor
    · rintro ⟨hz, hre⟩
      unfold packetWin at hz
      rcases Finset.mem_union.mp hz with hc | hrl
      · exact hc
      · rcases hd with rfl | hd0
        · simp at hrl
        · rcases Finset.mem_union.mp hrl with hr | hl
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
            rw [rightPt_re] at hre; linarith
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
            rw [leftPt_re] at hre; linarith
    · intro hc
      refine ⟨Finset.mem_union.mpr (Or.inl hc), ?_⟩
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
      exact critPt_re m n k
  rw [heq, Finset.card_image_of_injective _ (critPt_inj m n), Finset.card_range]

private lemma packetWin_zero (m n : ℕ) (d : ℝ) :
    packetWin m n 0 d = (Finset.range n).image (critPt m n) := by
  simp [packetWin]

lemma packetWin_right_moment_sum {m n q : ℕ} {d : ℝ} (hd : q = 0 ∨ 0 < d) :
    ∑ z ∈ (packetWin m n q d).filter (fun z => 1 / 2 < z.re),
      (1 : ℝ) * (z.re - 1 / 2) = (q : ℝ) * d := by
  rcases hd with rfl | hd0
  · have heq : (packetWin m n 0 d).filter (fun z => 1 / 2 < z.re) = ∅ := by
      rw [packetWin_zero]
      ext z
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hc
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
      rw [critPt_re]; norm_num
    rw [heq]; simp
  · have heq : (packetWin m n q d).filter (fun z => 1 / 2 < z.re) =
        (Finset.range q).image (rightPt m q d) := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hz, hgt⟩
        unfold packetWin at hz
        rcases Finset.mem_union.mp hz with hc | hrl
        · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
          rw [critPt_re] at hgt; norm_num at hgt
        · rcases Finset.mem_union.mp hrl with hr | hl
          · exact hr
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
            rw [leftPt_re] at hgt; linarith
      · intro hr
        refine ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hr))), ?_⟩
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
        rw [rightPt_re]; linarith
    rw [heq, Finset.sum_image (fun k₁ _ k₂ _ h => rightPt_inj m q d h)]
    have hterm : ∀ k ∈ Finset.range q, (1 : ℝ) * ((rightPt m q d k).re - 1 / 2) = d := by
      intro k _; rw [rightPt_re]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma packetWin_filter_right_card {m n q : ℕ} {d b : ℝ} (hb : 0 < b)
    (hd : q = 0 ∨ 0 < d) :
    ((packetWin m n q d).filter (fun z => 1 / 2 + b ≤ z.re)).card =
      if b ≤ d then q else 0 := by
  rcases hd with rfl | hd0
  · have heq : (packetWin m n 0 d).filter (fun z => 1 / 2 + b ≤ z.re) = ∅ := by
      rw [packetWin_zero]
      ext z
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hc
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
      rw [critPt_re]; linarith
    rw [heq]; split_ifs <;> simp
  · split_ifs with hbd
    · have heq : (packetWin m n q d).filter (fun z => 1 / 2 + b ≤ z.re) =
          (Finset.range q).image (rightPt m q d) := by
        ext z
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hz, hge⟩
          unfold packetWin at hz
          rcases Finset.mem_union.mp hz with hc | hrl
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
            rw [critPt_re] at hge; linarith
          · rcases Finset.mem_union.mp hrl with hr | hl
            · exact hr
            · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
              rw [leftPt_re] at hge; linarith
        · intro hr
          refine ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hr))), ?_⟩
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
          rw [rightPt_re]; linarith
      rw [heq, Finset.card_image_of_injective _ (rightPt_inj m q d), Finset.card_range]
    · have heq : (packetWin m n q d).filter (fun z => 1 / 2 + b ≤ z.re) = ∅ := by
        ext z
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hz
        unfold packetWin at hz
        rcases Finset.mem_union.mp hz with hc | hrl
        · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
          rw [critPt_re]; linarith
        · rcases Finset.mem_union.mp hrl with hr | hl
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
            rw [rightPt_re]; linarith
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
            rw [leftPt_re]; linarith
      rw [heq]; simp

lemma packetWin_filter_abs_card {m n q : ℕ} {d b : ℝ} (hb : 0 < b)
    (hd : q = 0 ∨ 0 < d) :
    ((packetWin m n q d).filter (fun z => b ≤ |z.re - 1 / 2|)).card =
      if b ≤ d then 2 * q else 0 := by
  rcases hd with rfl | hd0
  · have heq : (packetWin m n 0 d).filter (fun z => b ≤ |z.re - 1 / 2|) = ∅ := by
      rw [packetWin_zero]
      ext z
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hc
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
      rw [critPt_re, sub_self, abs_zero]; linarith
    rw [heq]; split_ifs <;> simp
  · split_ifs with hbd
    · have heq : (packetWin m n q d).filter (fun z => b ≤ |z.re - 1 / 2|) =
          (Finset.range q).image (rightPt m q d) ∪ (Finset.range q).image (leftPt m q d) := by
        ext z
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hz, habs⟩
          unfold packetWin at hz
          rcases Finset.mem_union.mp hz with hc | hrl
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
            rw [critPt_re, sub_self, abs_zero] at habs; linarith
          · exact hrl
        · intro hrl
          refine ⟨Finset.mem_union.mpr (Or.inr hrl), ?_⟩
          rcases Finset.mem_union.mp hrl with hr | hl
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
            rw [rightPt_re, show 1 / 2 + d - 1 / 2 = d by ring, abs_of_pos hd0]; exact hbd
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
            rw [leftPt_re, show 1 / 2 - d - 1 / 2 = -d by ring, abs_neg, abs_of_pos hd0]; exact hbd
      obtain ⟨_, hd2⟩ := packetWin_disjoint (m := m) (n := n) (q := q) (Or.inr hd0)
      rw [heq, Finset.card_union_of_disjoint hd2,
        Finset.card_image_of_injective _ (rightPt_inj m q d),
        Finset.card_image_of_injective _ (leftPt_inj m q d),
        Finset.card_range]; omega
    · have heq : (packetWin m n q d).filter (fun z => b ≤ |z.re - 1 / 2|) = ∅ := by
        ext z
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hz
        unfold packetWin at hz
        rcases Finset.mem_union.mp hz with hc | hrl
        · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
          rw [critPt_re, sub_self, abs_zero]; linarith
        · rcases Finset.mem_union.mp hrl with hr | hl
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
            rw [rightPt_re, show 1 / 2 + d - 1 / 2 = d by ring, abs_of_pos hd0]; linarith
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
            rw [leftPt_re, show 1 / 2 - d - 1 / 2 = -d by ring, abs_neg, abs_of_pos hd0]; linarith
      rw [heq]; simp

lemma packetWin_exists_abs_iff {m n q : ℕ} {d b : ℝ} (hb : 0 < b)
    (hd : q = 0 ∨ 0 < d) :
    (∃ z ∈ packetWin m n q d, b ≤ |z.re - 1 / 2|) ↔ (0 < q ∧ b ≤ d) := by
  have hcard := packetWin_filter_abs_card (m := m) (n := n) hb hd
  have hne : (∃ z ∈ packetWin m n q d, b ≤ |z.re - 1 / 2|) ↔
      0 < ((packetWin m n q d).filter (fun z => b ≤ |z.re - 1 / 2|)).card := by
    rw [Finset.card_pos, Finset.Nonempty]
    simp only [Finset.mem_filter]
  rw [hne, hcard]
  split_ifs with hbd
  · exact ⟨fun h => ⟨by omega, hbd⟩, fun ⟨hq, _⟩ => by omega⟩
  · exact ⟨fun h => by omega, fun ⟨_, h⟩ => absurd h hbd⟩

def basePairs (m : ℕ) : ℕ :=
  if m < 256 then 0 else Nat.floor (Real.log (m : ℝ) / (4 * Real.pi)) + 1

lemma basePairs_rvm {m : ℕ} (hm : 16 ≤ m) :
    |((2 * basePairs m : ℕ) : ℝ) - Real.log (m : ℝ) / (2 * Real.pi)| ≤ 2 := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hlog_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  unfold basePairs
  split_ifs with h256
  · simp only [mul_zero, Nat.cast_zero, zero_sub, abs_neg]
    have hlog256 : Real.log (m : ℝ) ≤ 8 := by
      have hm_le : (m : ℝ) ≤ (2 : ℝ) ^ (8 : ℕ) := by
        have : (m : ℝ) ≤ 256 := by exact_mod_cast (by omega : m ≤ 256)
        linarith [show (2 : ℝ) ^ (8 : ℕ) = 256 by norm_num]
      calc Real.log (m : ℝ) ≤ Real.log ((2 : ℝ) ^ (8 : ℕ)) := Real.log_le_log hm_pos hm_le
        _ = 8 * Real.log 2 := by rw [Real.log_pow]; push_cast; rfl
        _ ≤ 8 := by linarith [log_two_lt_one]
    rw [abs_of_nonneg (div_nonneg hlog_nn (by positivity)), div_le_iff₀ (by positivity)]
    linarith
  · push_cast
    have hfl_le : (Nat.floor (Real.log (m : ℝ) / (4 * Real.pi)) : ℝ) ≤
        Real.log (m : ℝ) / (4 * Real.pi) :=
      Nat.floor_le (div_nonneg hlog_nn (by positivity))
    have hlt_fl : Real.log (m : ℝ) / (4 * Real.pi) <
        (Nat.floor (Real.log (m : ℝ) / (4 * Real.pi)) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h2 : 2 * (Real.log (m : ℝ) / (4 * Real.pi)) = Real.log (m : ℝ) / (2 * Real.pi) := by
      field_simp [Real.pi_pos.ne']; ring
    exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma one_lt_log_log_of_twoFiftySix {m : ℕ} (hm : 256 ≤ m) :
    1 < Real.log (Real.log (m : ℝ)) ∧ Real.log (Real.log (m : ℝ)) ≤ Real.log (m : ℝ) := by
  have hm64 : ((m - 64 + 64 : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast (by omega : m - 64 + 64 = m)
  have h1 := one_lt_log_log_add_sixtyFour (m - 64)
  rw [hm64] at h1
  have hlog_pos : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  exact ⟨h1, (Real.log_le_sub_one_of_pos hlog_pos).trans (by linarith)⟩

def qSparse (m : ℕ) : ℕ := if m < 256 then 0 else 1

def nSparse (m : ℕ) : ℕ := if m < 256 then 0 else 2 * basePairs m - 2

def dSparse (m : ℕ) : ℝ :=
  if m < 256 then 0 else (1 / 8) * Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)

lemma qSparse_dSparse_spec (m : ℕ) :
    qSparse m = 0 ∨ (0 < dSparse m ∧ dSparse m < 1 / 2) := by
  by_cases hm : m < 256
  · exact Or.inl (by simp [qSparse, hm])
  · refine Or.inr ?_
    have hm256 : 256 ≤ m := Nat.not_lt.mp hm
    obtain ⟨hll1, hll_le⟩ := one_lt_log_log_of_twoFiftySix hm256
    have hlog_pos : 0 < Real.log (m : ℝ) := by linarith
    simp only [dSparse, if_neg hm]
    refine ⟨by positivity, ?_⟩
    have hdiv1 : Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ) ≤ 1 :=
      (div_le_one hlog_pos).mpr hll_le
    have : (1 / 8) * Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ) =
        (1 / 8) * (Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)) := by ring
    linarith

lemma qSparse_dSparse_or (m : ℕ) : qSparse m = 0 ∨ 0 < dSparse m :=
  (qSparse_dSparse_spec m).imp id And.left

lemma nSparse_add_two_qSparse (m : ℕ) : nSparse m + 2 * qSparse m = 2 * basePairs m := by
  by_cases hm : m < 256
  · simp [nSparse, qSparse, basePairs, hm]
  · have hbp : 1 ≤ basePairs m := by simp only [basePairs, if_neg hm]; omega
    simp only [nSparse, qSparse, if_neg hm]; omega

def sparseModel : UnitWindowStripZeroModel where
  Z m := packetWin m (nSparse m) (qSparse m) (dSparse m)
  mult _ := 1
  in_unit_strip m := packetWin_in_unit_strip (qSparse_dSparse_spec m)
  mult_pos _ _ _ := zero_lt_one
  refl_mem m := packetWin_refl_mem m (nSparse m) (qSparse m) (dSparse m)
  refl_mult _ _ _ := rfl
  local_rvm := by
    refine ⟨2, by norm_num, fun m hm => ?_⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one, packetWin_card (qSparse_dSparse_or m),
      nSparse_add_two_qSparse m]
    exact basePairs_rvm hm
  critical_simple_majority := by
    filter_upwards [eventually_ge_atTop 256,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 80]
      with m hm256 hlog80
    dsimp only [Function.comp_def] at hlog80
    rw [Finset.sum_const, smul_eq_mul, mul_one, packetWin_card (qSparse_dSparse_or m),
      nSparse_add_two_qSparse m, packetWin_filter_crit_card (qSparse_dSparse_or m)]
    have hm_not : ¬ m < 256 := not_lt.mpr hm256
    have hbp : 1 ≤ basePairs m := by simp only [basePairs, if_neg hm_not]; omega
    have hn_eq : (nSparse m : ℝ) = ((2 * basePairs m : ℕ) : ℝ) - 2 := by
      simp only [nSparse, if_neg hm_not]
      exact_mod_cast (Nat.cast_sub (by omega : 2 ≤ 2 * basePairs m))
    rw [hn_eq]
    have hrvm := (abs_le.mp (basePairs_rvm (by omega : 16 ≤ m))).1
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hlog_div : 10 ≤ Real.log (m : ℝ) / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  selberg_arbitrary_rate := by
    intro r hr0 hr1
    refine ⟨4 * Real.pi, by positivity, ?_⟩
    have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    filter_upwards [eventually_ge_atTop (512 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 16,
      ht_ll.eventually_ge_atTop 2] with V hV512 hlog16 hll2 a ha1
    simp only [Nat.cast_one]
    have hV_pos : 0 < V := by linarith
    have hlogV_pos : 0 < Real.log V := by linarith
    have hll_pos : 0 < Real.log (Real.log V) := by linarith
    -- Every `m ∈ Icc ⌈V⌉ ⌊2V⌋` has `dSparse m ≤ (1 / 4) * log(log V) / log V`.
    have hd_ub : ∀ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        dSparse m ≤ (1 / 4) * Real.log (Real.log V) / Real.log V := by
      intro m hm_I
      obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
      have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
      have hm_le_2V : (m : ℝ) ≤ 2 * V :=
        ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
      have hm_not : ¬ m < 256 := by
        intro hlt; have : (m : ℝ) < 256 := by exact_mod_cast hlt
        linarith
      simp only [dSparse, if_neg hm_not]
      have hlog_ge : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
      have hlog_le : Real.log (m : ℝ) ≤ 2 * Real.log V := by
        have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V) := Real.log_le_log (by linarith) hm_le_2V
        rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
        linarith [h1, log_two_lt_one]
      have hll_le : Real.log (Real.log (m : ℝ)) ≤ 2 * Real.log (Real.log V) := by
        have h1 : Real.log (Real.log (m : ℝ)) ≤ Real.log (2 * Real.log V) :=
          Real.log_le_log (by linarith) hlog_le
        rw [Real.log_mul zero_lt_two.ne' hlogV_pos.ne'] at h1
        linarith [h1, log_two_lt_one]
      calc (1 / 8) * Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)
          ≤ (1 / 8) * (2 * Real.log (Real.log V)) / Real.log (m : ℝ) :=
            div_le_div_of_nonneg_right (by linarith) (by linarith)
        _ ≤ (1 / 8) * (2 * Real.log (Real.log V)) / Real.log V :=
            div_le_div_of_nonneg_left (by positivity) hlogV_pos hlog_ge
        _ = (1 / 4) * Real.log (Real.log V) / Real.log V := by ring
    rcases lt_or_ge ((1 / 4) * Real.log (Real.log V)) a with ha_gt | ha_le
    · -- `a / log V > dSparse m`, so every window filter is empty!
      have hzero : ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ z ∈ (packetWin m (nSparse m) (qSparse m) (dSparse m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun m hm_I => ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
          packetWin_filter_right_card (div_pos (by linarith) hlogV_pos) (qSparse_dSparse_or m),
          if_neg]
        have h1 := hd_ub m hm_I
        have h2 : (1 / 4) * Real.log (Real.log V) / Real.log V < a / Real.log V :=
          div_lt_div_of_pos_right ha_gt hlogV_pos
        linarith
      rw [hzero, mul_zero, mul_zero]
      positivity
    · -- `1 ≤ a ≤ (1 / 4) * log(log V)`: at most `1` right-half zero per window.
      have hcnt_le : ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ z ∈ (packetWin m (nSparse m) (qSparse m) (dSparse m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) ≤ 2 * V := by
        have hterm : ∀ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
            ∑ z ∈ (packetWin m (nSparse m) (qSparse m) (dSparse m)).filter
              (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) ≤ 1 := by
          intro m _
          rw [Finset.sum_const, nsmul_eq_mul, mul_one,
            packetWin_filter_right_card (div_pos (by linarith) hlogV_pos) (qSparse_dSparse_or m)]
          split_ifs
          · simp only [qSparse]; split_ifs <;> norm_num
          · norm_num
        have hcard_I : ((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).card : ℝ) ≤ 2 * V := by
          have h1 : (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).card ≤ Nat.floor (2 * V) := by
            have hc : 1 ≤ Nat.ceil V := Nat.one_le_iff_ne_zero.mpr (by
              intro h0; have := (Nat.ceil_eq_zero.mp h0); linarith)
            rw [Nat.card_Icc]; omega
          exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
        calc _ ≤ ∑ _m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)), (1 : ℝ) :=
              Finset.sum_le_sum hterm
          _ = ((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).card : ℝ) := by simp
          _ ≤ 2 * V := hcard_I
      set u : ℝ := Real.log (Real.log V)
      have hu_exp : u * (Real.log V)⁻¹ ≤ (4 / 3) * Real.exp (-(r * a)) := by
        have h34 : (3 / 4) * u ≤ Real.exp ((3 / 4) * u) := by
          linarith [Real.add_one_le_exp ((3 / 4) * u)]
        have hu_le : u ≤ (4 / 3) * Real.exp ((3 / 4) * u) := by linarith
        have hlog_eq : (Real.log V)⁻¹ = Real.exp (-u) := by
          dsimp only [u]; rw [Real.exp_neg, Real.exp_log hlogV_pos]
        rw [hlog_eq]
        calc u * Real.exp (-u)
            ≤ ((4 / 3) * Real.exp ((3 / 4) * u)) * Real.exp (-u) :=
              mul_le_mul_of_nonneg_right hu_le (Real.exp_pos _).le
          _ = (4 / 3) * Real.exp (-(1 / 4 * u)) := by
              rw [mul_assoc, ← Real.exp_add, show 3 / 4 * u + -u = -(1 / 4 * u) by ring]
          _ ≤ (4 / 3) * Real.exp (-(r * a)) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
              have hra : r * a ≤ 1 * a := mul_le_mul_of_nonneg_right hr1.le (by linarith)
              dsimp only [u]; linarith
      calc 2 * Real.pi * ((a / Real.log V) *
            ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
              ∑ z ∈ (packetWin m (nSparse m) (qSparse m) (dSparse m)).filter
                (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ))
          ≤ 2 * Real.pi * ((((1 / 4) * u) / Real.log V) * (2 * V)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul (div_le_div_of_nonneg_right ha_le hlogV_pos.le) hcnt_le
              (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one)
              (by positivity)
        _ = Real.pi * (u * (Real.log V)⁻¹) * V := by ring
        _ ≤ Real.pi * ((4 / 3) * Real.exp (-(r * a))) * V :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hu_exp Real.pi_pos.le) hV_pos.le
        _ ≤ 4 * Real.pi * Real.exp (-(r * a)) * V := by
            have hpv : 0 ≤ Real.pi * Real.exp (-(r * a)) * V := by positivity
            have hdiff : 4 * Real.pi * Real.exp (-(r * a)) * V -
                Real.pi * ((4 / 3) * Real.exp (-(r * a))) * V =
                (8 / 3) * (Real.pi * Real.exp (-(r * a)) * V) := by ring
            linarith

/-- **Sparse-Uniform Countermodel (`exists_sparseUniformModel_logMean_not_cert`).**
Placing a single off-line conjugate pair at `1/2 ± (1/8) log(log m) / log m` in every unit window
`m ≥ 256` satisfies `UnitWindowStripZeroModel`, `(L)` (`HorizontalMomentLittleO`), and `100%`
critical-scale clustering (`CriticalClustering`), while violating both `WindowOccupancy`
(almost-all unit-window certificates) and `LogFreeZeroDensity`. -/
theorem exists_sparseUniformModel_logMean_not_cert :
    ∃ M : UnitWindowStripZeroModel,
      M.HorizontalMomentLittleO ∧
      M.CriticalClustering ∧
      ¬ M.WindowOccupancy ∧
      ¬ M.LogFreeZeroDensity := by
  refine ⟨sparseModel, ?_, ?_, ?_, ?_⟩
  · -- `sparseModel.HorizontalMomentLittleO`
    refine Metric.tendsto_atTop.mpr fun η hη => ?_
    obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp
      (Real.tendsto_log_atTop.eventually_ge_atTop (max 16 ((4 / η) ^ 2 + 1)))
    refine ⟨max 512 V₀, fun V hV => ?_⟩
    have hV512 : 512 ≤ V := (le_max_left _ _).trans hV
    have hV_pos : 0 < V := by linarith
    have hlog_ge := hV₀ V ((le_max_right _ _).trans hV)
    have hlog16 : 16 ≤ Real.log V := (le_max_left _ _).trans hlog_ge
    have hlog_η : (4 / η) ^ 2 + 1 ≤ Real.log V := (le_max_right _ _).trans hlog_ge
    have hlogV_pos : 0 < Real.log V := by linarith
    have hsum_nn : 0 ≤ V⁻¹ * ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        ∑ z ∈ (sparseModel.Z m).filter (fun z => 1 / 2 < z.re),
          (sparseModel.mult z : ℝ) * (z.re - 1 / 2) := by
      refine mul_nonneg (inv_nonneg.mpr hV_pos.le) (Finset.sum_nonneg fun m _ =>
        Finset.sum_nonneg fun z hz => mul_nonneg (Nat.cast_nonneg _) ?_)
      linarith [(Finset.mem_filter.mp hz).2]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hsum_nn]
    have hterm : ∀ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        ∑ z ∈ (sparseModel.Z m).filter (fun z => 1 / 2 < z.re),
          (sparseModel.mult z : ℝ) * (z.re - 1 / 2) ≤
          (1 / 2) * Real.log (Real.log V) / Real.log V := by
      intro m hm_I
      obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
      have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
      have hm_le_2V : (m : ℝ) ≤ 2 * V :=
        ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
      have hm_not : ¬ m < 256 := by
        intro hlt
        have hm_lt : (m : ℝ) < 256 := by exact_mod_cast hlt
        linarith
      dsimp only [sparseModel]
      simp only [Nat.cast_one]
      rw [packetWin_right_moment_sum (qSparse_dSparse_or m)]
      simp only [qSparse, dSparse, if_neg hm_not, Nat.cast_one, one_mul]
      have hlog_ge_m : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
      have hlog_le_m : Real.log (m : ℝ) ≤ 2 * Real.log V := by
        have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V) := Real.log_le_log (by linarith) hm_le_2V
        rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
        linarith [h1, log_two_lt_one]
      have hll1 : 1 ≤ Real.log (Real.log V) := by
        have hl4 : Real.exp 1 ≤ Real.log V := by
          have hexp4 : Real.exp 1 < 4 := by
            have h1 : (2 / 3 : ℝ) ≤ Real.exp (-1 / 3) := by linarith [Real.add_one_le_exp (-1 / 3 : ℝ)]
            have h2 : (8 / 27 : ℝ) ≤ Real.exp (-1) := by
              calc (8 / 27 : ℝ) = (2 / 3 : ℝ) ^ (3 : ℕ) := by norm_num
                _ ≤ (Real.exp (-1 / 3)) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) h1 3
                _ = Real.exp (-1) := by rw [← Real.exp_nat_mul]; norm_num
            have h3 : (8 / 27 : ℝ) * Real.exp 1 ≤ 1 := by
              calc (8 / 27 : ℝ) * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 :=
                    mul_le_mul_of_nonneg_right h2 (Real.exp_pos 1).le
                _ = 1 := by rw [← Real.exp_add]; norm_num
            linarith
          linarith
        rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hl4
      have hll_le : Real.log (Real.log (m : ℝ)) ≤ 2 * Real.log (Real.log V) := by
        have h1 : Real.log (Real.log (m : ℝ)) ≤ Real.log (2 * Real.log V) :=
          Real.log_le_log (by linarith) hlog_le_m
        rw [Real.log_mul zero_lt_two.ne' hlogV_pos.ne'] at h1
        linarith [h1, log_two_lt_one, hll1]
      calc (1 / 8) * Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)
          ≤ (1 / 8) * (2 * Real.log (Real.log V)) / Real.log V := by
            calc _ ≤ (1 / 8) * (2 * Real.log (Real.log V)) / Real.log (m : ℝ) :=
                  div_le_div_of_nonneg_right (by linarith) (by linarith)
              _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hlogV_pos hlog_ge_m
        _ ≤ (1 / 2) * Real.log (Real.log V) / Real.log V := by
            have : 0 ≤ Real.log (Real.log V) / Real.log V :=
              div_nonneg (by linarith) hlogV_pos.le
            have heq1 : (1 / 8) * (2 * Real.log (Real.log V)) / Real.log V =
                (1 / 4) * (Real.log (Real.log V) / Real.log V) := by ring
            have heq2 : (1 / 2) * Real.log (Real.log V) / Real.log V =
                (1 / 2) * (Real.log (Real.log V) / Real.log V) := by ring
            linarith
    have hcard_I : ((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).card : ℝ) ≤ 2 * V := by
      have hc : 1 ≤ Nat.ceil V := Nat.one_le_iff_ne_zero.mpr (by
        intro h0; have := Nat.ceil_eq_zero.mp h0; linarith)
      have h1 : (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).card ≤ Nat.floor (2 * V) := by
        rw [Nat.card_Icc]; omega
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
    have htot_le : V⁻¹ * ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        ∑ z ∈ (sparseModel.Z m).filter (fun z => 1 / 2 < z.re),
          (sparseModel.mult z : ℝ) * (z.re - 1 / 2) ≤
        Real.log (Real.log V) / Real.log V := by
      have hs := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at hs
      have hll_nn : 0 ≤ Real.log (Real.log V) := Real.log_nonneg (by linarith)
      have h2 := mul_le_mul_of_nonneg_right hcard_I
        (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hll_nn) hlogV_pos.le)
      have h3 := mul_le_mul_of_nonneg_left (hs.trans h2) (inv_nonneg.mpr hV_pos.le)
      calc _ ≤ V⁻¹ * (2 * V * ((1 / 2) * Real.log (Real.log V) / Real.log V)) := h3
        _ = Real.log (Real.log V) / Real.log V := by field_simp [hV_pos.ne']
    have hrt_gt : 4 / η < Real.sqrt (Real.log V) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 / η)]
      exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
    have hll_rt := log_le_two_sqrt_of_pos' hlogV_pos
    have hrt_pos : 0 < Real.sqrt (Real.log V) := Real.sqrt_pos.mpr hlogV_pos
    have hmul : (4 / η) * Real.sqrt (Real.log V) < Real.log V := by
      have h1 := mul_lt_mul_of_pos_right hrt_gt hrt_pos
      rwa [Real.mul_self_sqrt hlogV_pos.le] at h1
    have hlt_η : Real.log (Real.log V) / Real.log V < η := by
      rw [div_lt_iff₀ hlogV_pos]
      have h1 := mul_lt_mul_of_pos_left hmul hη
      rw [← mul_assoc, mul_div_cancel₀ 4 hη.ne'] at h1
      linarith [hll_rt, h1, hrt_pos]
    exact htot_le.trans_lt hlt_η
  · -- `sparseModel.CriticalClustering`: at most `2` off-line zeros per window, so total is `O(V) = o(V log V)`.
    intro κ hκ
    refine Metric.tendsto_atTop.mpr fun η hη => ?_
    obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp
      (Real.tendsto_log_atTop.eventually_ge_atTop (4 / η + 1))
    refine ⟨max 16 V₀, fun V hV => ?_⟩
    have hV16 : 16 ≤ V := (le_max_left _ _).trans hV
    have hV_pos : 0 < V := by linarith
    have hlog_η : 4 / η + 1 ≤ Real.log V := hV₀ V ((le_max_right _ _).trans hV)
    have hlogV_pos : 0 < Real.log V := by
      have h4η : 0 < 4 / η := by positivity
      linarith
    have hnn : 0 ≤ (∑ m ∈ Finset.range (Nat.floor V + 1),
        ∑ z ∈ (sparseModel.Z m).filter (fun z => κ / Real.log V ≤ |z.re - 1 / 2|),
          (sparseModel.mult z : ℝ)) /
        (V * Real.log V) :=
      div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        (by positivity)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, div_lt_iff₀ (mul_pos hV_pos hlogV_pos)]
    have hterm : ∀ m ∈ Finset.range (Nat.floor V + 1),
        ∑ z ∈ (sparseModel.Z m).filter (fun z => κ / Real.log V ≤ |z.re - 1 / 2|),
          (sparseModel.mult z : ℝ) ≤ 2 := by
      intro m _
      dsimp only [sparseModel]
      simp only [Nat.cast_one]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        packetWin_filter_abs_card (div_pos hκ hlogV_pos) (qSparse_dSparse_or m)]
      split_ifs
      · simp only [qSparse]; split_ifs <;> norm_num
      · norm_num
    have hsum_le : ∑ m ∈ Finset.range (Nat.floor V + 1),
        ∑ z ∈ (sparseModel.Z m).filter (fun z => κ / Real.log V ≤ |z.re - 1 / 2|),
          (sparseModel.mult z : ℝ) ≤ 4 * V := by
      have hs := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
      have hfl : ((Nat.floor V + 1 : ℕ) : ℝ) ≤ V + 1 := by
        push_cast; linarith [Nat.floor_le hV_pos.le]
      linarith
    have h4_lt : 4 < η * Real.log V := by
      have h1 : 4 / η < Real.log V := by linarith
      have h2 := mul_lt_mul_of_pos_left h1 hη
      rwa [mul_div_cancel₀ 4 hη.ne'] at h2
    calc _ ≤ 4 * V := hsum_le
      _ < (η * Real.log V) * V := mul_lt_mul_of_pos_right h4_lt hV_pos
      _ = η * (V * Real.log V) := by ring
  · -- `¬ sparseModel.WindowOccupancy`: for every `A > 0`, eventually `100%` of windows in `[⌈V⌉, ⌊2V⌋]` are bad.
    rintro ⟨δ, hδ_lim, hδ_ev⟩
    obtain ⟨A₀, hA₀⟩ := Metric.tendsto_atTop.mp hδ_lim (1 / 4) (by norm_num)
    set A : ℝ := max A₀ 1
    have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hδ_lt : δ A < 1 / 4 := by
      have h := hA₀ A (le_max_left _ _)
      rw [Real.dist_eq, sub_zero] at h
      linarith [le_abs_self (δ A)]
    have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp
      ((hδ_ev A hA_pos).and ((eventually_ge_atTop (512 : ℝ)).and
        ((Real.tendsto_log_atTop.eventually_ge_atTop 4).and
          (ht_ll.eventually_ge_atTop (16 * A)))))
    obtain ⟨hocc, hV512, hlog4, hll16A⟩ := hV₁ V₁ le_rfl
    have hall : (Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁))).filter
        (fun m => ∃ z ∈ sparseModel.Z m, A / Real.log V₁ ≤ |z.re - 1 / 2|) =
        Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁)) := by
      refine Finset.filter_eq_self.mpr fun m hm_I => ?_
      obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
      have hm_ge_V : V₁ ≤ (m : ℝ) := (Nat.le_ceil V₁).trans (by exact_mod_cast hm_lo)
      have hm_le_2V : (m : ℝ) ≤ 2 * V₁ :=
        ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by linarith))
      have hm_not : ¬ m < 256 := by
        intro hlt
        have hm_lt : (m : ℝ) < 256 := by exact_mod_cast hlt
        linarith
      have hlogV_pos : 0 < Real.log V₁ := by linarith
      have hlog_m_pos : 0 < Real.log (m : ℝ) :=
        hlogV_pos.trans_le (Real.log_le_log (by linarith) hm_ge_V)
      dsimp only [sparseModel]
      rw [packetWin_exists_abs_iff (div_pos hA_pos hlogV_pos) (qSparse_dSparse_or m)]
      refine ⟨by simp [qSparse, hm_not], ?_⟩
      simp only [dSparse, if_neg hm_not]
      have hlog_le : Real.log (m : ℝ) ≤ 2 * Real.log V₁ := by
        have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V₁) := Real.log_le_log (by linarith) hm_le_2V
        rw [Real.log_mul zero_lt_two.ne' (by linarith)] at h1
        linarith [h1, log_two_lt_one]
      have hll_ge : Real.log (Real.log V₁) ≤ Real.log (Real.log (m : ℝ)) :=
        Real.log_le_log hlogV_pos (Real.log_le_log (by linarith) hm_ge_V)
      calc A / Real.log V₁
          ≤ ((1 / 16) * Real.log (Real.log V₁)) / Real.log V₁ :=
            div_le_div_of_nonneg_right (by linarith) hlogV_pos.le
        _ = (1 / 8) * Real.log (Real.log V₁) / (2 * Real.log V₁) := by ring
        _ ≤ (1 / 8) * Real.log (Real.log (m : ℝ)) / (2 * Real.log V₁) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (1 / 8) * Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ) :=
            div_le_div_of_nonneg_left (by linarith) hlog_m_pos hlog_le
    rw [hall] at hocc
    have hcard_lo : V₁ / 2 ≤ ((Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁))).card : ℝ) := by
      have hceil_lt : (Nat.ceil V₁ : ℝ) < V₁ + 1 := Nat.ceil_lt_add_one (by linarith)
      have hfl_gt : 2 * V₁ - 1 < (Nat.floor (2 * V₁) : ℝ) := Nat.sub_one_lt_floor (2 * V₁)
      have hle_cf : Nat.ceil V₁ ≤ Nat.floor (2 * V₁) := by
        have : (Nat.ceil V₁ : ℝ) < (Nat.floor (2 * V₁) : ℝ) := by linarith
        exact (Nat.cast_lt.mp this).le
      have hcard_eq : ((Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁))).card : ℝ) =
          (Nat.floor (2 * V₁) : ℝ) + 1 - (Nat.ceil V₁ : ℝ) := by
        rw [Nat.card_Icc]
        have : Nat.floor (2 * V₁) + 1 - Nat.ceil V₁ + Nat.ceil V₁ = Nat.floor (2 * V₁) + 1 := by omega
        have hc : ((Nat.floor (2 * V₁) + 1 - Nat.ceil V₁ : ℕ) : ℝ) + (Nat.ceil V₁ : ℝ) =
            (Nat.floor (2 * V₁) : ℝ) + 1 := by exact_mod_cast this
        linarith
      linarith
    have hmul_δ : δ A * V₁ < (1 / 4) * V₁ := mul_lt_mul_of_pos_right hδ_lt (by linarith)
    linarith [hocc, hcard_lo, hmul_δ]
  · -- `¬ sparseModel.LogFreeZeroDensity`: each bad window contributes `2` deep zeros, so `≥ V / 2` total.
    rintro ⟨ε, hε_lim, hε_ev⟩
    obtain ⟨A₀, hA₀⟩ := Metric.tendsto_atTop.mp hε_lim (1 / 4) (by norm_num)
    set A : ℝ := max A₀ 1
    have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hε_lt : ε A < 1 / 4 := by
      have h := hA₀ A (le_max_left _ _)
      rw [Real.dist_eq, sub_zero] at h
      linarith [le_abs_self (ε A)]
    have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp
      ((hε_ev A hA_pos).and ((eventually_ge_atTop (512 : ℝ)).and
        ((Real.tendsto_log_atTop.eventually_ge_atTop 4).and
          (ht_ll.eventually_ge_atTop (16 * A)))))
    obtain ⟨hzd, hV512, hlog4, hll16A⟩ := hV₁ V₁ le_rfl
    have hterm : ∀ m ∈ Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁)),
        (1 : ℝ) ≤ ∑ z ∈ (sparseModel.Z m).filter (fun z => A / Real.log V₁ ≤ |z.re - 1 / 2|),
          (sparseModel.mult z : ℝ) := by
      intro m hm_I
      obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
      have hm_ge_V : V₁ ≤ (m : ℝ) := (Nat.le_ceil V₁).trans (by exact_mod_cast hm_lo)
      have hm_le_2V : (m : ℝ) ≤ 2 * V₁ :=
        ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by linarith))
      have hm_not : ¬ m < 256 := by
        intro hlt
        have hm_lt : (m : ℝ) < 256 := by exact_mod_cast hlt
        linarith
      have hlogV_pos : 0 < Real.log V₁ := by linarith
      have hlog_m_pos : 0 < Real.log (m : ℝ) :=
        hlogV_pos.trans_le (Real.log_le_log (by linarith) hm_ge_V)
      dsimp only [sparseModel]
      simp only [Nat.cast_one]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        packetWin_filter_abs_card (div_pos hA_pos hlogV_pos) (qSparse_dSparse_or m), if_pos]
      · simp [qSparse, hm_not]
      · simp only [dSparse, if_neg hm_not]
        have hlog_le : Real.log (m : ℝ) ≤ 2 * Real.log V₁ := by
          have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V₁) := Real.log_le_log (by linarith) hm_le_2V
          rw [Real.log_mul zero_lt_two.ne' (by linarith)] at h1
          linarith [h1, log_two_lt_one]
        have hll_ge : Real.log (Real.log V₁) ≤ Real.log (Real.log (m : ℝ)) :=
          Real.log_le_log hlogV_pos (Real.log_le_log (by linarith) hm_ge_V)
        calc A / Real.log V₁
            ≤ ((1 / 16) * Real.log (Real.log V₁)) / Real.log V₁ :=
              div_le_div_of_nonneg_right (by linarith) hlogV_pos.le
          _ = (1 / 8) * Real.log (Real.log V₁) / (2 * Real.log V₁) := by ring
          _ ≤ (1 / 8) * Real.log (Real.log (m : ℝ)) / (2 * Real.log V₁) :=
              div_le_div_of_nonneg_right (by linarith) (by positivity)
          _ ≤ (1 / 8) * Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ) :=
              div_le_div_of_nonneg_left (by linarith) hlog_m_pos hlog_le
    have hcard_lo : V₁ / 2 ≤ ((Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁))).card : ℝ) := by
      have hceil_lt : (Nat.ceil V₁ : ℝ) < V₁ + 1 := Nat.ceil_lt_add_one (by linarith)
      have hfl_gt : 2 * V₁ - 1 < (Nat.floor (2 * V₁) : ℝ) := Nat.sub_one_lt_floor (2 * V₁)
      have hle_cf : Nat.ceil V₁ ≤ Nat.floor (2 * V₁) := by
        have : (Nat.ceil V₁ : ℝ) < (Nat.floor (2 * V₁) : ℝ) := by linarith
        exact (Nat.cast_lt.mp this).le
      have hcard_eq : ((Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁))).card : ℝ) =
          (Nat.floor (2 * V₁) : ℝ) + 1 - (Nat.ceil V₁ : ℝ) := by
        rw [Nat.card_Icc]
        have : Nat.floor (2 * V₁) + 1 - Nat.ceil V₁ + Nat.ceil V₁ = Nat.floor (2 * V₁) + 1 := by omega
        have hc : ((Nat.floor (2 * V₁) + 1 - Nat.ceil V₁ : ℕ) : ℝ) + (Nat.ceil V₁ : ℝ) =
            (Nat.floor (2 * V₁) : ℝ) + 1 := by exact_mod_cast this
        linarith
      linarith
    have hsum_lo : V₁ / 2 ≤ ∑ m ∈ Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁)),
        ∑ z ∈ (sparseModel.Z m).filter (fun z => A / Real.log V₁ ≤ |z.re - 1 / 2|),
          (sparseModel.mult z : ℝ) := by
      calc V₁ / 2 ≤ ((Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁))).card : ℝ) := hcard_lo
        _ = ∑ _m ∈ Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁)), (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum hterm
    have hmul_ε : ε A * V₁ < (1 / 4) * V₁ := mul_lt_mul_of_pos_right hε_lt (by linarith)
    linarith [hzd, hsum_lo, hmul_ε]

def evenHalves : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then evenHalves ((n + 1) / 2) + 1 else 0

lemma two_pow_dvd_of_le_evenHalves {v : ℕ} :
    ∀ {m : ℕ}, m ≠ 0 → v ≤ evenHalves m → 2 ^ v ∣ m := by
  induction v with
  | zero => intro _ _ _; simp
  | succ v ih =>
    intro m hm hv
    rcases m with _ | n
    · exact absurd rfl hm
    · rw [evenHalves] at hv
      split_ifs at hv with hmod
      · have hdiv_ne : (n + 1) / 2 ≠ 0 := by omega
        have hdvd := ih hdiv_ne (by omega)
        rw [pow_succ']
        have heq : n + 1 = 2 * ((n + 1) / 2) := by omega
        rw [heq]
        exact mul_dvd_mul_left 2 hdvd
      · omega

lemma evenHalves_two_pow_mul_odd (v q : ℕ) :
    evenHalves (2 ^ v * (2 * q + 1)) = v := by
  induction v with
  | zero =>
    have h : 2 ^ 0 * (2 * q + 1) = (2 * q) + 1 := by ring
    rw [h, evenHalves]
    split_ifs with hm <;> omega
  | succ v ih =>
    set M := 2 ^ v * (2 * q + 1)
    have hM_pos : 0 < M := Nat.mul_pos (Nat.pow_pos (by norm_num)) (by omega)
    have h2M : 2 ^ (v + 1) * (2 * q + 1) = (2 * M - 1) + 1 := by
      have : 2 ^ (v + 1) * (2 * q + 1) = 2 * M := by dsimp only [M]; rw [pow_succ']; ring
      omega
    rw [h2M, evenHalves]
    have hmod : ((2 * M - 1) + 1) % 2 = 0 := by omega
    rw [if_pos hmod, show ((2 * M - 1) + 1) / 2 = M by omega, ih]

lemma card_Icc_filter_dvd_le (a b D : ℕ) :
    ((Finset.Icc a b).filter (fun m => D ∣ m)).card ≤ b / D + 1 := by
  have hmaps : Set.MapsTo (fun m => m / D)
      ((Finset.Icc a b).filter (fun m => D ∣ m) : Set ℕ) (Finset.range (b / D + 1) : Set ℕ) := by
    intro m hm
    obtain ⟨hm_I, _⟩ := Finset.mem_filter.mp hm
    have hle : m / D ≤ b / D := Nat.div_le_div_right (Finset.mem_Icc.mp hm_I).2
    rw [Finset.mem_coe, Finset.mem_range]
    dsimp only
    omega
  have hinj : Set.InjOn (fun m => m / D) ((Finset.Icc a b).filter (fun m => D ∣ m) : Set ℕ) := by
    intro m₁ hm₁ m₂ hm₂ heq
    dsimp only at heq
    have hd1 : D ∣ m₁ := (Finset.mem_filter.mp hm₁).2
    have hd2 : D ∣ m₂ := (Finset.mem_filter.mp hm₂).2
    calc m₁ = D * (m₁ / D) := (Nat.mul_div_cancel' hd1).symm
      _ = D * (m₂ / D) := by rw [heq]
      _ = m₂ := Nat.mul_div_cancel' hd2
  exact (Finset.card_le_card_of_injOn (fun m => m / D) hmaps hinj).trans_eq (Finset.card_range _)

lemma exists_evenHalves_subset_Icc (v : ℕ) {V : ℝ} (hV : (2 : ℝ) ^ (v + 3) ≤ V) :
    ∃ S ⊆ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
      (∀ m ∈ S, evenHalves m = v) ∧ V / (2 : ℝ) ^ (v + 2) ≤ (S.card : ℝ) := by
  set U : ℝ := V / (2 : ℝ) ^ (v + 1)
  have h2v1_pos : (0 : ℝ) < (2 : ℝ) ^ (v + 1) := by positivity
  have h2v_pos : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
  have hU4 : 4 ≤ U := by
    dsimp only [U]
    rw [le_div_iff₀ h2v1_pos]
    calc 4 * (2 : ℝ) ^ (v + 1) = (2 : ℝ) ^ (v + 3) := by rw [pow_add, pow_add]; ring
      _ ≤ V := hV
  set a_q : ℕ := Nat.ceil U
  set b_q : ℕ := Nat.floor (2 * U - 1)
  set Q := Finset.Icc a_q b_q
  refine ⟨Q.image (fun q => 2 ^ v * (2 * q + 1)), ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hq_lo, hq_hi⟩ := Finset.mem_Icc.mp hq
    have hq_ge_U : U ≤ (q : ℝ) := (Nat.le_ceil U).trans (by exact_mod_cast hq_lo)
    have hq_le_2U : (q : ℝ) ≤ 2 * U - 1 :=
      ((Nat.cast_le (α := ℝ)).mpr hq_hi).trans (Nat.floor_le (by linarith))
    have hm_ge_V : V ≤ ((2 ^ v * (2 * q + 1) : ℕ) : ℝ) := by
      push_cast
      have h1 : V = (2 : ℝ) ^ v * (2 * U) := by
        dsimp only [U]; rw [pow_succ]; field_simp [h2v_pos.ne']
      rw [h1]
      exact mul_le_mul_of_nonneg_left (by linarith) h2v_pos.le
    have hm_le_2V : ((2 ^ v * (2 * q + 1) : ℕ) : ℝ) ≤ 2 * V := by
      push_cast
      have h1 : 2 * V = (2 : ℝ) ^ v * (4 * U) := by
        dsimp only [U]; rw [pow_succ]; field_simp [h2v_pos.ne']; ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left (by linarith) h2v_pos.le
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hm_ge_V, Nat.le_floor hm_le_2V⟩
  · intro m hm
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hm
    exact evenHalves_two_pow_mul_odd v q
  · have hinj : Function.Injective (fun q : ℕ => 2 ^ v * (2 * q + 1)) := by
      intro q₁ q₂ h
      have h1 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by norm_num : 0 < 2)) h
      omega
    rw [Finset.card_image_of_injective _ hinj]
    have ha_lt : (a_q : ℝ) < U + 1 := Nat.ceil_lt_add_one (by linarith)
    have hb_gt : 2 * U - 2 < (b_q : ℝ) := by
      have := Nat.sub_one_lt_floor (2 * U - 1)
      linarith
    have hab : a_q ≤ b_q := by
      have : (a_q : ℝ) < (b_q : ℝ) := by linarith
      exact (Nat.cast_lt.mp this).le
    have hcard_eq : (Q.card : ℝ) = (b_q : ℝ) + 1 - (a_q : ℝ) := by
      dsimp only [Q]
      rw [Nat.card_Icc]
      have : b_q + 1 - a_q + a_q = b_q + 1 := by omega
      have hc : ((b_q + 1 - a_q : ℕ) : ℝ) + (a_q : ℝ) = (b_q : ℝ) + 1 := by exact_mod_cast this
      linarith
    have hU2 : V / (2 : ℝ) ^ (v + 2) = U / 2 := by
      dsimp only [U]; rw [show v + 2 = (v + 1) + 1 by omega, pow_succ]; field_simp [h2v1_pos.ne']
    rw [hU2]
    linarith

def activeClust (m : ℕ) : Prop :=
  256 ≤ m ∧ 1 ≤ evenHalves m ∧ (evenHalves m : ℝ) ≤ (1 / 8) * Real.log (m : ℝ)

def qClust (m : ℕ) : ℕ :=
  if activeClust m then Nat.floor (Real.log (m : ℝ) / 52) else 0

def dClust (m : ℕ) : ℝ :=
  if activeClust m then (evenHalves m : ℝ) / (2 * Real.log (m : ℝ)) else 0

def nClust (m : ℕ) : ℕ := 2 * basePairs m - 2 * qClust m

lemma qClust_dClust_spec (m : ℕ) :
    qClust m = 0 ∨ (0 < dClust m ∧ dClust m < 1 / 2) := by
  by_cases hact : activeClust m
  · refine Or.inr ?_
    have ⟨hm256, hv1, hv_ub⟩ := hact
    have hlog_pos : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hv_pos : (0 : ℝ) < (evenHalves m : ℝ) := by exact_mod_cast hv1
    simp only [dClust, if_pos hact]
    refine ⟨by positivity, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    linarith
  · exact Or.inl (by simp [qClust, hact])

lemma qClust_dClust_or (m : ℕ) : qClust m = 0 ∨ 0 < dClust m :=
  (qClust_dClust_spec m).imp id And.left

lemma qClust_le_basePairs (m : ℕ) : qClust m ≤ basePairs m := by
  by_cases hact : activeClust m
  · have ⟨hm256, _, _⟩ := hact
    have hm_not : ¬ m < 256 := not_lt.mpr hm256
    simp only [qClust, if_pos hact, basePairs, if_neg hm_not]
    have hlog_nn : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hle_div : Real.log (m : ℝ) / 52 ≤ Real.log (m : ℝ) / (4 * Real.pi) :=
      div_le_div_of_nonneg_left hlog_nn (by positivity) (by linarith)
    exact (Nat.floor_mono hle_div).trans (Nat.le_succ _)
  · simp [qClust, hact]

lemma nClust_add_two_qClust (m : ℕ) : nClust m + 2 * qClust m = 2 * basePairs m := by
  have := qClust_le_basePairs m
  dsimp only [nClust]; omega

lemma dClust_le_one_sixteenth (m : ℕ) : dClust m ≤ 1 / 16 := by
  by_cases hact : activeClust m
  · have ⟨hm256, _, hv_ub⟩ := hact
    have hlog_pos : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    simp only [dClust, if_pos hact]
    rw [div_le_iff₀ (by positivity)]
    linarith
  · simp only [dClust, if_neg hact]; norm_num

def clusteredModel : UnitWindowStripZeroModel where
  Z m := packetWin m (nClust m) (qClust m) (dClust m)
  mult _ := 1
  in_unit_strip m := packetWin_in_unit_strip (qClust_dClust_spec m)
  mult_pos _ _ _ := zero_lt_one
  refl_mem m := packetWin_refl_mem m (nClust m) (qClust m) (dClust m)
  refl_mult _ _ _ := rfl
  local_rvm := by
    refine ⟨2, by norm_num, fun m hm => ?_⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one, packetWin_card (qClust_dClust_or m),
      nClust_add_two_qClust m]
    exact basePairs_rvm hm
  critical_simple_majority := by
    filter_upwards [eventually_ge_atTop 256] with m hm256
    rw [Finset.sum_const, smul_eq_mul, mul_one, packetWin_card (qClust_dClust_or m),
      nClust_add_two_qClust m, packetWin_filter_crit_card (qClust_dClust_or m)]
    have hle2q : 2 * qClust m ≤ 2 * basePairs m := Nat.mul_le_mul_left 2 (qClust_le_basePairs m)
    have hn_eq : (nClust m : ℝ) = ((2 * basePairs m : ℕ) : ℝ) - 2 * (qClust m : ℝ) := by
      dsimp only [nClust]
      have hc := Nat.cast_sub (R := ℝ) hle2q
      push_cast at hc ⊢; exact hc
    rw [hn_eq]
    have hm_not : ¬ m < 256 := not_lt.mpr hm256
    have hlog_nn : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    have hq_ub : (qClust m : ℝ) ≤ Real.log (m : ℝ) / 52 := by
      by_cases hact : activeClust m
      · simp only [qClust, if_pos hact]
        exact Nat.floor_le (by positivity)
      · simp only [qClust, if_neg hact, Nat.cast_zero]; positivity
    have hbp_lb : Real.log (m : ℝ) / (2 * Real.pi) ≤ ((2 * basePairs m : ℕ) : ℝ) := by
      simp only [basePairs, if_neg hm_not]; push_cast
      have hlt := Nat.lt_floor_add_one (Real.log (m : ℝ) / (4 * Real.pi))
      have h2 : 2 * (Real.log (m : ℝ) / (4 * Real.pi)) = Real.log (m : ℝ) / (2 * Real.pi) := by
        field_simp [Real.pi_pos.ne']; ring
      linarith
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hdiv_cmp : Real.log (m : ℝ) / 8 ≤ Real.log (m : ℝ) / (2 * Real.pi) :=
      div_le_div_of_nonneg_left hlog_nn (by positivity) (by linarith)
    linarith
  selberg_arbitrary_rate := by
    intro r hr0 hr1
    refine ⟨4 * Real.pi, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (512 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 16] with V hV512 hlog16 a ha1
    simp only [Nat.cast_one]
    have hV_pos : 0 < V := by linarith
    have hlogV_pos : 0 < Real.log V := by linarith
    rcases lt_or_ge ((1 / 16) * Real.log V) a with ha_gt | ha_le
    · have hzero : ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ z ∈ (packetWin m (nClust m) (qClust m) (dClust m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
          packetWin_filter_right_card (div_pos (by linarith) hlogV_pos) (qClust_dClust_or m),
          if_neg]
        have h1 := dClust_le_one_sixteenth m
        have h2 : 1 / 16 < a / Real.log V := by
          rw [lt_div_iff₀ hlogV_pos]; linarith
        linarith
      rw [hzero, mul_zero, mul_zero]; positivity
    · -- `1 ≤ a ≤ (1 / 16) * log V`: every bad window is divisible by `2 ^ ⌈2a⌉₊`.
      set v₀ : ℕ := Nat.ceil (2 * a)
      set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
      set Dvd_V := I_V.filter (fun m => 2 ^ v₀ ∣ m)
      have hzero_off : ∀ m ∈ I_V, m ∉ Dvd_V →
          ∑ z ∈ (packetWin m (nClust m) (qClust m) (dClust m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) = 0 := by
        intro m hm_I hnot_dvd
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
          packetWin_filter_right_card (div_pos (by linarith) hlogV_pos) (qClust_dClust_or m)]
        split_ifs with hbd
        · by_cases hact : activeClust m
          · exfalso; apply hnot_dvd
            refine Finset.mem_filter.mpr ⟨hm_I, ?_⟩
            have hm_ge_V : V ≤ (m : ℝ) :=
              (Nat.le_ceil V).trans (by exact_mod_cast (Finset.mem_Icc.mp hm_I).1)
            have hm_ne0 : m ≠ 0 := by
              intro h0; subst h0; simp at hm_ge_V; linarith
            have hlog_ge : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
            simp only [dClust, if_pos hact] at hbd
            have h1 : a / Real.log V ≤ (evenHalves m : ℝ) / (2 * Real.log V) :=
              hbd.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _)
                (by positivity) (by linarith))
            have h2 : 2 * a ≤ (evenHalves m : ℝ) := by
              have hm_mul := (div_le_div_iff₀ hlogV_pos (by positivity)).mp h1
              have hrew : a * (2 * Real.log V) = (2 * a) * Real.log V := by ring
              rw [hrew] at hm_mul
              exact le_of_mul_le_mul_right hm_mul hlogV_pos
            exact two_pow_dvd_of_le_evenHalves hm_ne0 (Nat.ceil_le.mpr h2)
          · simp [qClust, hact]
        · rfl
      have hsub_sum : ∑ m ∈ I_V,
          ∑ z ∈ (packetWin m (nClust m) (qClust m) (dClust m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) =
          ∑ m ∈ Dvd_V,
            ∑ z ∈ (packetWin m (nClust m) (qClust m) (dClust m)).filter
              (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) := by
        symm
        exact Finset.sum_subset (Finset.filter_subset _ _) hzero_off
      rw [hsub_sum]
      have hq_ub : ∀ m ∈ Dvd_V,
          ∑ z ∈ (packetWin m (nClust m) (qClust m) (dClust m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) ≤ Real.log V / 26 := by
        intro m hm_D
        have hm_I := (Finset.mem_filter.mp hm_D).1
        have hm_le_2V : (m : ℝ) ≤ 2 * V :=
          ((Nat.cast_le (α := ℝ)).mpr (Finset.mem_Icc.mp hm_I).2).trans
            (Nat.floor_le (by positivity))
        have hm_ge_V : V ≤ (m : ℝ) :=
          (Nat.le_ceil V).trans (by exact_mod_cast (Finset.mem_Icc.mp hm_I).1)
        rw [Finset.sum_const, nsmul_eq_mul, mul_one,
          packetWin_filter_right_card (div_pos (by linarith) hlogV_pos) (qClust_dClust_or m)]
        split_ifs
        · by_cases hact : activeClust m
          · simp only [qClust, if_pos hact]
            have hfl : (Nat.floor (Real.log (m : ℝ) / 52) : ℝ) ≤ Real.log (m : ℝ) / 52 :=
              Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith)) (by norm_num))
            have hlog2 : Real.log (m : ℝ) ≤ 2 * Real.log V := by
              have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V) :=
                Real.log_le_log (by linarith) hm_le_2V
              rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
              linarith [h1, log_two_lt_one]
            linarith
          · simp only [qClust, if_neg hact, Nat.cast_zero]; positivity
        · simp only [Nat.cast_zero]; positivity
      have h2v₀_le_V : (2 : ℝ) ^ v₀ ≤ V := by
        have hv₀_le : (v₀ : ℝ) ≤ 2 * a + 1 := (Nat.ceil_lt_add_one (by positivity)).le
        have hmul1 : (v₀ : ℝ) * Real.log 2 ≤ (v₀ : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left log_two_lt_one.le (Nat.cast_nonneg _)
        have hlog_pow : (v₀ : ℝ) * Real.log 2 ≤ Real.log V := by
          linarith [hmul1, ha_le, hv₀_le, hlog16]
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ v₀), Real.log_pow,
          ← Real.exp_log hV_pos]
        exact Real.exp_le_exp.mpr hlog_pow
      have hDvd_card : (Dvd_V.card : ℝ) ≤ 3 * V / (2 : ℝ) ^ v₀ := by
        have hc := card_Icc_filter_dvd_le (Nat.ceil V) (Nat.floor (2 * V)) (2 ^ v₀)
        have hdiv_le : ((Nat.floor (2 * V) / 2 ^ v₀ : ℕ) : ℝ) ≤ 2 * V / (2 : ℝ) ^ v₀ := by
          rw [le_div_iff₀ (by positivity)]
          have h1 : (Nat.floor (2 * V) / 2 ^ v₀) * 2 ^ v₀ ≤ Nat.floor (2 * V) :=
            Nat.div_mul_le_self _ _
          have h2 : (((Nat.floor (2 * V) / 2 ^ v₀) * 2 ^ v₀ : ℕ) : ℝ) ≤
              (Nat.floor (2 * V) : ℝ) := by exact_mod_cast h1
          push_cast at h2
          exact h2.trans (Nat.floor_le (by positivity))
        have h1_le : (1 : ℝ) ≤ V / (2 : ℝ) ^ v₀ := (one_le_div (by positivity)).mpr h2v₀_le_V
        have hcast : (Dvd_V.card : ℝ) ≤ ((Nat.floor (2 * V) / 2 ^ v₀ : ℕ) : ℝ) + 1 := by
          exact_mod_cast hc
        calc (Dvd_V.card : ℝ) ≤ 2 * V / (2 : ℝ) ^ v₀ + V / (2 : ℝ) ^ v₀ := by linarith
          _ = 3 * V / (2 : ℝ) ^ v₀ := by ring
      have hpow_exp : ((2 : ℝ) ^ v₀)⁻¹ ≤ Real.exp (-(6 / 5 * a)) := by
        have hv₀_ge : 2 * a ≤ (v₀ : ℝ) := Nat.le_ceil (2 * a)
        have hlog2 : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hmul : 6 / 5 * a ≤ (v₀ : ℝ) * Real.log 2 := by
          calc 6 / 5 * a = (2 * a) * (3 / 5) := by ring
            _ ≤ (v₀ : ℝ) * Real.log 2 :=
              mul_le_mul hv₀_ge hlog2 (by norm_num) (Nat.cast_nonneg _)
        rw [← Real.exp_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ v₀)⁻¹),
          Real.log_inv, Real.log_pow]
        exact Real.exp_le_exp.mpr (by linarith)
      have ha_exp : a * Real.exp (-(6 / 5 * a)) ≤ 5 * Real.exp (-(r * a)) := by
        have h1 : a / 5 ≤ Real.exp (a / 5) := by linarith [Real.add_one_le_exp (a / 5)]
        have h2 : a * Real.exp (-(6 / 5 * a)) ≤ (5 * Real.exp (a / 5)) * Real.exp (-(6 / 5 * a)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        have h3 : (5 * Real.exp (a / 5)) * Real.exp (-(6 / 5 * a)) = 5 * Real.exp (-a) := by
          rw [mul_assoc, ← Real.exp_add, show a / 5 + -(6 / 5 * a) = -a by ring]
        have hra : r * a ≤ 1 * a := mul_le_mul_of_nonneg_right hr1.le (by linarith)
        have h4 : Real.exp (-a) ≤ Real.exp (-(r * a)) :=
          Real.exp_le_exp.mpr (by linarith)
        linarith [h2, h3, mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 5)]
      have hsum_Dvd : ∑ m ∈ Dvd_V,
          ∑ z ∈ (packetWin m (nClust m) (qClust m) (dClust m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) ≤
          (3 / 26) * Real.exp (-(6 / 5 * a)) * V * Real.log V := by
        calc _ ≤ ∑ _m ∈ Dvd_V, Real.log V / 26 := Finset.sum_le_sum hq_ub
          _ = (Dvd_V.card : ℝ) * (Real.log V / 26) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (3 * V * ((2 : ℝ) ^ v₀)⁻¹) * (Real.log V / 26) := by
              rw [div_eq_mul_inv] at hDvd_card
              exact mul_le_mul_of_nonneg_right hDvd_card (by positivity)
          _ ≤ (3 * V * Real.exp (-(6 / 5 * a))) * (Real.log V / 26) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow_exp (by positivity)) (by positivity)
          _ = (3 / 26) * Real.exp (-(6 / 5 * a)) * V * Real.log V := by ring
      calc 2 * Real.pi * ((a / Real.log V) *
            ∑ m ∈ Dvd_V,
              ∑ z ∈ (packetWin m (nClust m) (qClust m) (dClust m)).filter
                (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ))
          ≤ 2 * Real.pi * ((a / Real.log V) *
              ((3 / 26) * Real.exp (-(6 / 5 * a)) * V * Real.log V)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsum_Dvd (by positivity)) (by positivity)
        _ = (3 / 13) * Real.pi * (a * Real.exp (-(6 / 5 * a))) * V := by
            field_simp [hlogV_pos.ne']; ring
        _ ≤ (3 / 13) * Real.pi * (5 * Real.exp (-(r * a))) * V :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left ha_exp (by positivity)) hV_pos.le
        _ ≤ 4 * Real.pi * Real.exp (-(r * a)) * V := by
            have hpv : 0 ≤ Real.pi * Real.exp (-(r * a)) * V := by positivity
            have hdiff : 4 * Real.pi * Real.exp (-(r * a)) * V -
                (3 / 13) * Real.pi * (5 * Real.exp (-(r * a))) * V =
                (37 / 13) * (Real.pi * Real.exp (-(r * a)) * V) := by ring
            linarith

/-- **Clustered `2`-Adic Packet Countermodel (`exists_clusteredPacketModel_cert_not_zeroDensity_not_logMean`).**
Packing `⌊log m / 52⌋₊` off-line conjugate pairs at `1/2 ± v₂(m) / (2 log m)` in windows with
`1 ≤ v₂(m) ≤ (1/8) log m` satisfies `UnitWindowStripZeroModel` and `WindowOccupancy`
(almost-all unit-window certificates), while violating both `LogFreeZeroDensity` (`(D_zero)`) and
`HorizontalMomentLittleO` (`(L)`). -/
theorem exists_clusteredPacketModel_cert_not_zeroDensity_not_logMean :
    ∃ M : UnitWindowStripZeroModel,
      M.WindowOccupancy ∧
      ¬ M.LogFreeZeroDensity ∧
      ¬ M.HorizontalMomentLittleO := by
  refine ⟨clusteredModel, ?_, ?_, ?_⟩
  · -- `clusteredModel.WindowOccupancy` with `δ A = 6 * exp(-A)`.
    refine ⟨fun A => 6 * Real.exp (-A), ?_, fun A hA => ?_⟩
    · have h1 : Tendsto (fun A : ℝ => Real.exp (-A)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
      simpa only [mul_zero] using h1.const_mul 6
    · filter_upwards [eventually_ge_atTop (512 : ℝ),
        Real.tendsto_log_atTop.eventually_ge_atTop 16] with V hV512 hlog16
      have hV_pos : 0 < V := by linarith
      have hlogV_pos : 0 < Real.log V := by linarith
      rcases lt_or_ge ((1 / 16) * Real.log V) A with hA_gt | hA_le
      · have hempty : (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
            (fun m => ∃ z ∈ clusteredModel.Z m, A / Real.log V ≤ |z.re - 1 / 2|) = ∅ := by
          ext m
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro _
          dsimp only [clusteredModel]
          rw [packetWin_exists_abs_iff (div_pos hA hlogV_pos) (qClust_dClust_or m)]
          rintro ⟨_, hbd⟩
          have h1 := dClust_le_one_sixteenth m
          have h2 : 1 / 16 < A / Real.log V := by rw [lt_div_iff₀ hlogV_pos]; linarith
          linarith
        rw [hempty, Finset.card_empty, Nat.cast_zero]; positivity
      · set v₀ : ℕ := max 1 (Nat.ceil (2 * A))
        have hsub : (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
              (fun m => ∃ z ∈ clusteredModel.Z m, A / Real.log V ≤ |z.re - 1 / 2|) ⊆
            (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter (fun m => 2 ^ v₀ ∣ m) := by
          intro m hm
          obtain ⟨hm_I, hex⟩ := Finset.mem_filter.mp hm
          refine Finset.mem_filter.mpr ⟨hm_I, ?_⟩
          dsimp only [clusteredModel] at hex
          rw [packetWin_exists_abs_iff (div_pos hA hlogV_pos) (qClust_dClust_or m)] at hex
          obtain ⟨hq_pos, hbd⟩ := hex
          have hact : activeClust m := by
            by_contra hnot; simp [qClust, hnot] at hq_pos
          have hm_ge_V : V ≤ (m : ℝ) :=
            (Nat.le_ceil V).trans (by exact_mod_cast (Finset.mem_Icc.mp hm_I).1)
          have hm_ne0 : m ≠ 0 := by intro h0; subst h0; simp at hm_ge_V; linarith
          have hlog_ge : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
          simp only [dClust, if_pos hact] at hbd
          have h1 : A / Real.log V ≤ (evenHalves m : ℝ) / (2 * Real.log V) :=
            hbd.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith))
          have h2 : 2 * A ≤ (evenHalves m : ℝ) := by
            have hm_mul := (div_le_div_iff₀ hlogV_pos (by positivity)).mp h1
            have hrew : A * (2 * Real.log V) = (2 * A) * Real.log V := by ring
            rw [hrew] at hm_mul
            exact le_of_mul_le_mul_right hm_mul hlogV_pos
          have hv₀_le : v₀ ≤ evenHalves m := max_le hact.2.1 (Nat.ceil_le.mpr h2)
          exact two_pow_dvd_of_le_evenHalves hm_ne0 hv₀_le
        have h2v₀_le_V : (2 : ℝ) ^ v₀ ≤ V := by
          have hv₀_le : (v₀ : ℝ) ≤ 2 * A + 1 := by
            dsimp only [v₀]; rw [Nat.cast_max, Nat.cast_one]
            exact max_le (by linarith) (Nat.ceil_lt_add_one (by positivity)).le
          have hmul1 : (v₀ : ℝ) * Real.log 2 ≤ (v₀ : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left log_two_lt_one.le (Nat.cast_nonneg _)
          have hlog_pow : (v₀ : ℝ) * Real.log 2 ≤ Real.log V := by
            linarith [hmul1, hA_le, hv₀_le, hlog16]
          rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ v₀), Real.log_pow,
            ← Real.exp_log hV_pos]
          exact Real.exp_le_exp.mpr hlog_pow
        have hc := (Finset.card_le_card hsub).trans
          (card_Icc_filter_dvd_le (Nat.ceil V) (Nat.floor (2 * V)) (2 ^ v₀))
        have hdiv_le : ((Nat.floor (2 * V) / 2 ^ v₀ : ℕ) : ℝ) ≤ 2 * V / (2 : ℝ) ^ v₀ := by
          rw [le_div_iff₀ (by positivity)]
          have h1 : (Nat.floor (2 * V) / 2 ^ v₀) * 2 ^ v₀ ≤ Nat.floor (2 * V) :=
            Nat.div_mul_le_self _ _
          have h2 : (((Nat.floor (2 * V) / 2 ^ v₀) * 2 ^ v₀ : ℕ) : ℝ) ≤
              (Nat.floor (2 * V) : ℝ) := by exact_mod_cast h1
          push_cast at h2
          exact h2.trans (Nat.floor_le (by positivity))
        have h1_le : (1 : ℝ) ≤ V / (2 : ℝ) ^ v₀ := (one_le_div (by positivity)).mpr h2v₀_le_V
        have hcast : (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
            (fun m => ∃ z ∈ clusteredModel.Z m, A / Real.log V ≤ |z.re - 1 / 2|)).card : ℝ) ≤
            3 * V * ((2 : ℝ) ^ v₀)⁻¹ := by
          have hcR : (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
              (fun m => ∃ z ∈ clusteredModel.Z m, A / Real.log V ≤ |z.re - 1 / 2|)).card : ℝ) ≤
              ((Nat.floor (2 * V) / 2 ^ v₀ : ℕ) : ℝ) + 1 := by exact_mod_cast hc
          have h3 : 2 * V / (2 : ℝ) ^ v₀ + V / (2 : ℝ) ^ v₀ = 3 * V * ((2 : ℝ) ^ v₀)⁻¹ := by ring
          linarith
        have hpow_exp : ((2 : ℝ) ^ v₀)⁻¹ ≤ Real.exp (-A) := by
          have hv₀_ge : 2 * A ≤ (v₀ : ℝ) := by
            dsimp only [v₀]; rw [Nat.cast_max]; exact (Nat.le_ceil _).trans (le_max_right _ _)
          have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
          have hmul : A ≤ (v₀ : ℝ) * Real.log 2 := by
            calc A = (2 * A) * (1 / 2) := by ring
              _ ≤ (v₀ : ℝ) * Real.log 2 :=
                mul_le_mul hv₀_ge hlog2 (by norm_num) (Nat.cast_nonneg _)
          rw [← Real.exp_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ v₀)⁻¹), Real.log_inv, Real.log_pow]
          exact Real.exp_le_exp.mpr (by linarith)
        calc _ ≤ 3 * V * ((2 : ℝ) ^ v₀)⁻¹ := hcast
          _ ≤ 3 * V * Real.exp (-A) := mul_le_mul_of_nonneg_left hpow_exp (by positivity)
          _ ≤ 6 * Real.exp (-A) * V := by
              have hpv : 0 ≤ Real.exp (-A) * V := by positivity
              have hdiff : 6 * Real.exp (-A) * V - 3 * V * Real.exp (-A) =
                  3 * (Real.exp (-A) * V) := by ring
              linarith
  · -- `¬ clusteredModel.LogFreeZeroDensity`: for `A = 1`, windows with `evenHalves m = 4` contribute `Ω(V log V)` zeros.
    rintro ⟨ε, _, hε_ev⟩
    obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp
      ((hε_ev 1 zero_lt_one).and ((eventually_ge_atTop (512 : ℝ)).and
        (Real.tendsto_log_atTop.eventually_ge_atTop (max 104 (104 * (2 : ℝ) ^ 6 * (|ε 1| + 1))))))
    obtain ⟨hzd, hV512, hlog_ge⟩ := hV₁ V₁ le_rfl
    have hlog104 : 104 ≤ Real.log V₁ := (le_max_left _ _).trans hlog_ge
    have hlog_ε : 104 * (2 : ℝ) ^ 6 * (|ε 1| + 1) ≤ Real.log V₁ := (le_max_right _ _).trans hlog_ge
    have hlogV_pos : 0 < Real.log V₁ := by linarith
    obtain ⟨S, hS_sub, hS_ev, hS_card⟩ :=
      exists_evenHalves_subset_Icc 4 (V := V₁) (by norm_num; linarith)
    have hterm : ∀ m ∈ S, Real.log V₁ / 52 ≤
        ∑ z ∈ (clusteredModel.Z m).filter (fun z => 1 / Real.log V₁ ≤ |z.re - 1 / 2|),
          (clusteredModel.mult z : ℝ) := by
      intro m hmS
      have hm_I := hS_sub hmS
      have hm_ge_V : V₁ ≤ (m : ℝ) :=
        (Nat.le_ceil V₁).trans (by exact_mod_cast (Finset.mem_Icc.mp hm_I).1)
      have hm_le_2V : (m : ℝ) ≤ 2 * V₁ :=
        ((Nat.cast_le (α := ℝ)).mpr (Finset.mem_Icc.mp hm_I).2).trans
          (Nat.floor_le (by linarith))
      have hm256 : 256 ≤ m := by
        by_contra hlt; push Not at hlt
        have : (m : ℝ) < 256 := by exact_mod_cast hlt
        linarith
      have hev4 : evenHalves m = 4 := hS_ev m hmS
      have hlog_ge_m : Real.log V₁ ≤ Real.log (m : ℝ) := Real.log_le_log (by linarith) hm_ge_V
      have hact : activeClust m := by
        refine ⟨hm256, by omega, ?_⟩
        rw [hev4]; push_cast; linarith
      dsimp only [clusteredModel]
      simp only [Nat.cast_one]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        packetWin_filter_abs_card (div_pos zero_lt_one hlogV_pos) (qClust_dClust_or m), if_pos]
      · simp only [qClust, if_pos hact]; push_cast
        have hlt_fl := Nat.lt_floor_add_one (Real.log (m : ℝ) / 52)
        linarith
      · simp only [dClust, if_pos hact, hev4]; push_cast
        have hlog2 : Real.log (m : ℝ) ≤ 2 * Real.log V₁ := by
          have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V₁) := Real.log_le_log (by linarith) hm_le_2V
          rw [Real.log_mul zero_lt_two.ne' (by linarith)] at h1
          linarith [h1, log_two_lt_one]
        calc 1 / Real.log V₁ = 4 / (2 * (2 * Real.log V₁)) := by ring
          _ ≤ 4 / (2 * Real.log (m : ℝ)) :=
              div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    have hsum_S : (V₁ / (2 : ℝ) ^ 6) * (Real.log V₁ / 52) ≤
        ∑ m ∈ Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁)),
          ∑ z ∈ (clusteredModel.Z m).filter (fun z => 1 / Real.log V₁ ≤ |z.re - 1 / 2|),
            (clusteredModel.mult z : ℝ) := by
      calc (V₁ / (2 : ℝ) ^ 6) * (Real.log V₁ / 52)
          ≤ (S.card : ℝ) * (Real.log V₁ / 52) :=
            mul_le_mul_of_nonneg_right hS_card (by positivity)
        _ = ∑ _m ∈ S, Real.log V₁ / 52 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ m ∈ S, ∑ z ∈ (clusteredModel.Z m).filter (fun z => 1 / Real.log V₁ ≤ |z.re - 1 / 2|),
              (clusteredModel.mult z : ℝ) := Finset.sum_le_sum hterm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun _ _ _ =>
              Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hgt_ε : ε 1 * V₁ < (V₁ / (2 : ℝ) ^ 6) * (Real.log V₁ / 52) := by
      have h1 : |ε 1| + 1 ≤ Real.log V₁ / (104 * (2 : ℝ) ^ 6) := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      have h2 : ε 1 < Real.log V₁ / (52 * (2 : ℝ) ^ 6) := by
        have := le_abs_self (ε 1)
        have : Real.log V₁ / (104 * (2 : ℝ) ^ 6) < Real.log V₁ / (52 * (2 : ℝ) ^ 6) :=
          div_lt_div_of_pos_left hlogV_pos (by norm_num) (by norm_num)
        linarith
      calc ε 1 * V₁ < (Real.log V₁ / (52 * (2 : ℝ) ^ 6)) * V₁ :=
            mul_lt_mul_of_pos_right h2 (by linarith)
        _ = (V₁ / (2 : ℝ) ^ 6) * (Real.log V₁ / 52) := by ring
    linarith [hzd, hsum_S, hgt_ε]
  · -- `¬ clusteredModel.HorizontalMomentLittleO`: windows with `evenHalves m = 1` contribute `≥ V / 3328`.
    intro hmom
    obtain ⟨V₀, hV₀⟩ := Metric.tendsto_atTop.mp hmom (1 / 4096) (by norm_num)
    obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp
      ((eventually_ge_atTop (max 512 V₀)).and (Real.tendsto_log_atTop.eventually_ge_atTop 104))
    obtain ⟨hV_ge, hlog104⟩ := hV₁ V₁ le_rfl
    have hV512 : 512 ≤ V₁ := (le_max_left _ _).trans hV_ge
    have hV_pos : 0 < V₁ := by linarith
    have hlt_mom := hV₀ V₁ ((le_max_right _ _).trans hV_ge)
    rw [Real.dist_eq, sub_zero] at hlt_mom
    have hmom_ub : V₁⁻¹ * ∑ m ∈ Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁)),
        ∑ z ∈ (clusteredModel.Z m).filter (fun z => 1 / 2 < z.re),
          (clusteredModel.mult z : ℝ) * (z.re - 1 / 2) < 1 / 4096 :=
      (le_abs_self _).trans_lt hlt_mom
    obtain ⟨S, hS_sub, hS_ev, hS_card⟩ :=
      exists_evenHalves_subset_Icc 1 (V := V₁) (by norm_num; linarith)
    have hterm : ∀ m ∈ S, (1 / 416 : ℝ) ≤
        ∑ z ∈ (clusteredModel.Z m).filter (fun z => 1 / 2 < z.re),
          (clusteredModel.mult z : ℝ) * (z.re - 1 / 2) := by
      intro m hmS
      have hm_I := hS_sub hmS
      have hm_ge_V : V₁ ≤ (m : ℝ) :=
        (Nat.le_ceil V₁).trans (by exact_mod_cast (Finset.mem_Icc.mp hm_I).1)
      have hm256 : 256 ≤ m := by
        by_contra hlt; push Not at hlt
        have hm_lt : (m : ℝ) < 256 := by exact_mod_cast hlt
        linarith
      have hev1 : evenHalves m = 1 := hS_ev m hmS
      have hlog_ge_m : Real.log V₁ ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
      have hlog_m_pos : 0 < Real.log (m : ℝ) := by linarith
      have hact : activeClust m := by
        refine ⟨hm256, by omega, ?_⟩
        rw [hev1]; push_cast; linarith
      dsimp only [clusteredModel]
      simp only [Nat.cast_one]
      rw [packetWin_right_moment_sum (qClust_dClust_or m)]
      simp only [qClust, dClust, if_pos hact, hev1, Nat.cast_one]
      have hq_ge : Real.log (m : ℝ) / 104 ≤ (Nat.floor (Real.log (m : ℝ) / 52) : ℝ) := by
        have hlt := Nat.lt_floor_add_one (Real.log (m : ℝ) / 52)
        linarith
      calc (1 / 416 : ℝ) ≤ (1 / 208 : ℝ) := by norm_num
        _ = (Real.log (m : ℝ) / 104) * (1 / (2 * Real.log (m : ℝ))) := by
            field_simp [hlog_m_pos.ne']; ring
        _ ≤ (Nat.floor (Real.log (m : ℝ) / 52) : ℝ) * (1 / (2 * Real.log (m : ℝ))) :=
            mul_le_mul_of_nonneg_right hq_ge (by positivity)
    have hsum_lo : V₁ / 3328 ≤ ∑ m ∈ Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁)),
        ∑ z ∈ (clusteredModel.Z m).filter (fun z => 1 / 2 < z.re),
          (clusteredModel.mult z : ℝ) * (z.re - 1 / 2) := by
      calc V₁ / 3328 = (V₁ / (2 : ℝ) ^ 3) * (1 / 416) := by norm_num; ring
        _ ≤ (S.card : ℝ) * (1 / 416) := mul_le_mul_of_nonneg_right hS_card (by norm_num)
        _ = ∑ _m ∈ S, (1 / 416 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ m ∈ S, ∑ z ∈ (clusteredModel.Z m).filter (fun z => 1 / 2 < z.re),
              (clusteredModel.mult z : ℝ) * (z.re - 1 / 2) := Finset.sum_le_sum hterm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun _ _ _ =>
              Finset.sum_nonneg fun z hz => mul_nonneg (Nat.cast_nonneg _)
                (by linarith [(Finset.mem_filter.mp hz).2])
    have hdiv_lo : (1 / 3328 : ℝ) ≤ V₁⁻¹ * ∑ m ∈ Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁)),
        ∑ z ∈ (clusteredModel.Z m).filter (fun z => 1 / 2 < z.re),
          (clusteredModel.mult z : ℝ) * (z.re - 1 / 2) := by
      have hm := mul_le_mul_of_nonneg_left hsum_lo (inv_nonneg.mpr hV_pos.le)
      have hl : V₁⁻¹ * (V₁ / 3328) = 1 / 3328 := by field_simp [hV_pos.ne']
      rwa [hl] at hm
    linarith [hmom_ub, hdiv_lo]

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

end

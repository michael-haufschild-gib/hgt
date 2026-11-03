import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.NearLineDensityBesselCertificateAndSeparation

/-!
# Short-Shell Per-Window Second Moment, Giant-Cluster Equivalence, and Planck-to-Unit Bridge

Unconditional short-shell × Selberg per-window moment bounds, exact sharpness countermodels,
giant-cluster characterization of `(D_win) ↔ (D_zero)`, Planck-window `logDoorStage` Bessel–Szegő
certificates, mesoscopic window occupancy, and the vertical Planck-shadow bridge to unit-window
occupancy:

1. **Short-shell × Selberg per-window `L^p` / `L^2` bounds and double-logarithmic `o(V)` law**
   (`burnolDeepOrderSum_le_logV`, `perWindow_deepOrderSum_rpow_le_selberg`,
   `perWindow_deepOrderSum_sq_le_selberg`, `perWindow_deepOrderSum_sq_doubleLog_le`):
   Covering `burnolUnitXiZeros m` with `mediumCap_orderSum_le_logV` (three applications of
   `shortShell_orderSum_le_log`) bounds each window's deep multiplicity by `C_sh * log V`, giving
   `∑_m N_m(A, V)^2 ≤ 8 C_sh C_d (e^{-r A} / A) V (log V)^2` across `2 ≤ A ≤ κ_r log V`, which
   collapses identically to `O_r(e^{-r u} V / log(log V)) = o(V)` at `A_V = (2 / r) log(log V) + u`.

2. **Sharpness countermodels and exact giant-cluster characterization of `(D_win) ↔ (D_zero)`**
   (`clusteredModel_sqMoment_lower_bound`,
   `exists_logSpacingModel_zeroDensity_not_linearSqMoment`,
   `logFreeNearLineZeroDensity_iff_windowOccupancy_and_clusterTail`,
   `logFreeNearLineZeroDensity_of_windowOccupancy_and_growingSqMoment`):
   `clusteredModel` proves the `(log V)^2` factor is unimprovable at every fixed `A > 0` even under
   `WindowOccupancy`; `logSpacingModel` satisfies `(D_zero)`, `(D_win)`, `(L)`, and
   `CriticalClustering` while still having `∑_m N_m(A, V)^2 ≥ c_A V log V`; and `(D_zero)` is
   unconditionally equivalent to `(D_win)` plus vanishing giant-cluster multiplicity tails.

3. **Planck-to-unit push: uniform Planck obstruction, Planck `logDoorStage` certificates,
   mesoscopic windows, and vertical Planck-shadow `IFF` bridge**
   (`sparseModel_uniformPlanckVolume_not_windowOccupancy`,
   `almostAll_planckWindow_logStage_besselSzegoCertificate`,
   `mesoscopicWindow_nearLine_zeroFree_volume_le`,
   `unitWindow_planckShadow_sum_le`,
   `logFreeNearLineWindowOccupancy_iff_thinPlanckShadow`):
   `sparseModel` satisfies the full uniform Planck-window volume bound across `0 < B ≤ log V` yet
   violates unit `WindowOccupancy`; unconditionally for `ζ`, true `logDoorStage` Bessel–Szegő
   certificates hold on `(1 - η(c)) V` of Planck windows with `η(c) → 0` as `c → 0⁺`, zero-free
   occupancy extends to mesoscopic windows `min(1, e^{r A / 2} / log V)` with `δ(A) → 0`, and the
   local Planck-shadow sum is `O_r(B (e^{-r A} / A) V)` without `log V` loss, isolating vertically
   thin off-line projections as the exact `IFF` gap to unit-window `(D_win)`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology Classical

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

open GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect
open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1. Short-shell × Selberg per-window `L^p` / `L^2` bounds and double-logarithmic `o(V)` law -/

/-- Deep `ξ`-zero multiplicity on the `m`-th Burnol unit window beyond `A / log V`. -/
def burnolDeepOrderSum (m : ℕ) (A V : ℝ) : ℝ :=
  ∑ ρ ∈ (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|),
    ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℝ)

/-- Explicit short-shell per-window multiplicity constant `48 * (|xiLineTwoLogDerivConstant| + 2)`. -/
def shortShellCapConst : ℝ :=
  48 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 2)

theorem shortShellCapConst_pos : 0 < shortShellCapConst := by
  unfold shortShellCapConst; positivity

theorem burnolDeepOrderSum_nonneg (m : ℕ) (A V : ℝ) : 0 ≤ burnolDeepOrderSum m A V :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- Pointwise per-window bound `N_m(A, V) ≤ shortShellCapConst * log V` from `shortShell_orderSum_le_log`. -/
theorem burnolDeepOrderSum_le_logV {V : ℝ} (hV32 : 32 ≤ V) (hlog4 : 4 ≤ Real.log V)
    {m : ℕ} (hm : m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))) (A : ℝ) :
    burnolDeepOrderSum m A V ≤ shortShellCapConst * Real.log V := by
  obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm
  have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
  have hm_le_2V : (m : ℝ) ≤ 2 * V :=
    ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by linarith))
  have hsub : (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|) ⊆
      shellZeros ((m : ℝ) - 3) ((m : ℝ) + 3) := by
    intro ρ hρ
    obtain ⟨hρ_Z, _⟩ := Finset.mem_filter.mp hρ
    obtain ⟨⟨hr0, hr1, hy1, hy2⟩, hxi⟩ := (mem_burnolUnitXiZeros_iff m ρ).mp hρ_Z
    have hy1_lo := sub_three_le_burnolUnitLower m
    have hy2_hi := (burnolUnit_coords m).2.2.2.1
    exact Finset.mem_filter.mpr
      ⟨_root_.RHTower.mem_stripFinsetPos.mpr
        ⟨hr0, hr1, by linarith, by linarith, hxi⟩, by linarith⟩
  have hcap := mediumCap_orderSum_le_logV (V := V) (V₁ := (m : ℝ) - 3) (V₂ := (m : ℝ) + 3)
    hV32 hlog4 (by linarith) (by linarith) (by linarith) (by linarith)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _).trans hcap

/-- Eight-fold Burnol unit-window overlap bound against the extended dyadic shell `(V - 4, 2V + 4]`. -/
lemma sum_burnolDeepOrderSum_le_eight_mul_extendedShell {V A : ℝ} (hV16 : 16 ≤ V) :
    ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)), burnolDeepOrderSum m A V ≤
      8 * ∑ z ∈ (shellZeros (V - 4) (2 * V + 4)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
  set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
  set B_ext := (shellZeros (V - 4) (2 * V + 4)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|)
  set f : ℂ → ℝ := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
  have hfilter_eq : ∀ m ∈ I_V,
      (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|) =
        B_ext.filter (fun z => z ∈ burnolUnitXiZeros m) := by
    intro m hm
    obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm
    have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
    have hm_le_2V : (m : ℝ) ≤ 2 * V :=
      ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by linarith))
    ext z
    simp only [B_ext, Finset.mem_filter]
    constructor
    · rintro ⟨hz_Z, hz_deep⟩
      obtain ⟨⟨hr0, hr1, hy1, hy2⟩, hxi⟩ := (mem_burnolUnitXiZeros_iff m z).mp hz_Z
      have hy1_lo := sub_three_le_burnolUnitLower m
      have hy2_hi := (burnolUnit_coords m).2.2.2.1
      exact ⟨⟨Finset.mem_filter.mpr ⟨_root_.RHTower.mem_stripFinsetPos.mpr
        ⟨hr0, hr1, by linarith, by linarith, hxi⟩, by linarith⟩, hz_deep⟩, hz_Z⟩
    · rintro ⟨⟨_, hz_deep⟩, hz_Z⟩
      exact ⟨hz_Z, hz_deep⟩
  have hcard_m : ∀ z ∈ B_ext, ((I_V.filter (fun m => z ∈ burnolUnitXiZeros m)).card : ℝ) ≤ 8 := by
    intro z _
    have hsub : I_V.filter (fun m => z ∈ burnolUnitXiZeros m) ⊆
        Finset.Icc (Nat.floor z.im - 3) (Nat.floor z.im + 4) := by
      intro m hm
      obtain ⟨hm_I, hz_Z⟩ := Finset.mem_filter.mp hm
      have hm_ge_V : V ≤ (m : ℝ) :=
        (Nat.le_ceil V).trans (by exact_mod_cast (Finset.mem_Icc.mp hm_I).1)
      obtain ⟨⟨_, _, hy1, hy2⟩, _⟩ := (mem_burnolUnitXiZeros_iff m z).mp hz_Z
      have hy1_lo := sub_three_le_burnolUnitLower m
      have hy2_hi := (burnolUnit_coords m).2.2.2.1
      have him_pos : 0 < z.im := by linarith
      have hfl_le : (Nat.floor z.im : ℝ) ≤ z.im := Nat.floor_le him_pos.le
      have hlt_fl : z.im < (Nat.floor z.im : ℝ) + 1 := Nat.lt_floor_add_one z.im
      have hc1 : Nat.floor z.im ≤ m + 3 := by
        have h : (Nat.floor z.im : ℝ) < ((m + 3 : ℕ) : ℝ) := by push_cast; linarith
        exact (Nat.cast_lt.mp h).le
      have hc2 : m ≤ Nat.floor z.im + 4 := by
        have h : (m : ℝ) < ((Nat.floor z.im + 4 : ℕ) : ℝ) := by push_cast; linarith
        exact (Nat.cast_lt.mp h).le
      rw [Finset.mem_Icc]; omega
    have hle8 : (Finset.Icc (Nat.floor z.im - 3) (Nat.floor z.im + 4)).card ≤ 8 := by
      rw [Nat.card_Icc]; omega
    exact_mod_cast (Finset.card_le_card hsub).trans hle8
  calc ∑ m ∈ I_V, burnolDeepOrderSum m A V
      = ∑ m ∈ I_V, ∑ z ∈ B_ext.filter (fun z => z ∈ burnolUnitXiZeros m), f z := by
        refine Finset.sum_congr rfl fun m hm => ?_
        unfold burnolDeepOrderSum
        rw [hfilter_eq m hm]
    _ = ∑ m ∈ I_V, ∑ z ∈ B_ext, if z ∈ burnolUnitXiZeros m then f z else 0 := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_filter _ _
    _ = ∑ z ∈ B_ext, ∑ m ∈ I_V, if z ∈ burnolUnitXiZeros m then f z else 0 := Finset.sum_comm
    _ = ∑ z ∈ B_ext, ((I_V.filter (fun m => z ∈ burnolUnitXiZeros m)).card : ℝ) * f z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ B_ext, 8 * f z :=
        Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (hcard_m z hz) (Nat.cast_nonneg _)
    _ = 8 * ∑ z ∈ B_ext, f z := (Finset.mul_sum _ _ _).symm

/-- **Unconditional Short-Shell × Selberg Per-Window `L^p` Moment Bound (`perWindow_deepOrderSum_rpow_le_selberg`).**
For every rate `0 < r < 1`, there exist `C_d > 0` and `κ_r > 0` such that eventually in `V`,
uniformly across all depths `2 ≤ A ≤ κ_r * log V` and all exponents `1 ≤ p`,
`∑_{m = ⌈V⌉}^{⌊2V⌋} N_m(A, V)^p ≤ 8 * shortShellCapConst^(p - 1) * C_d * (e^{-r A} / A) * V * (log V)^p`. -/
theorem perWindow_deepOrderSum_rpow_le_selberg {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C_d κ_r : ℝ, 0 < C_d ∧ 0 < κ_r ∧ ∀ᶠ V : ℝ in atTop,
      ∀ A p : ℝ, 2 ≤ A → A ≤ κ_r * Real.log V → 1 ≤ p →
        ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          (burnolDeepOrderSum m A V) ^ p ≤
          8 * shortShellCapConst ^ (p - 1) * C_d * (Real.exp (-(r * A)) / A) * V *
            (Real.log V) ^ p := by
  obtain ⟨C_d, κ_r, hCd_pos, hκ_pos, hd_ev⟩ := deepExtendedShell_orderSum_le hr0 hr1
  refine ⟨C_d, κ_r, hCd_pos, hκ_pos, ?_⟩
  filter_upwards [hd_ev, eventually_ge_atTop (32 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 4] with V hV_d hV32 hlog4 A p hA2 hA_hi hp1
  have hlogV_pos : 0 < Real.log V := by linarith
  have hM_pos : 0 < shortShellCapConst * Real.log V :=
    mul_pos shortShellCapConst_pos hlogV_pos
  have hterm : ∀ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
      (burnolDeepOrderSum m A V) ^ p ≤
        (shortShellCapConst * Real.log V) ^ (p - 1) * burnolDeepOrderSum m A V := by
    intro m hm
    have hx_nn := burnolDeepOrderSum_nonneg m A V
    have hx_le := burnolDeepOrderSum_le_logV hV32 hlog4 hm A
    rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
    · rw [← hx0, Real.zero_rpow (by linarith), mul_zero]
    · have hp_eq : (burnolDeepOrderSum m A V) ^ p =
          (burnolDeepOrderSum m A V) ^ (p - 1) * burnolDeepOrderSum m A V := by
        conv_lhs => rw [show p = (p - 1) + 1 by ring, Real.rpow_add hx_pos, Real.rpow_one]
      rw [hp_eq]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hx_pos.le hx_le (by linarith)) hx_pos.le
  have hsum1 : ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)), burnolDeepOrderSum m A V ≤
      8 * (C_d * (Real.exp (-(r * A)) / A) * V * Real.log V) :=
    (sum_burnolDeepOrderSum_le_eight_mul_extendedShell (by linarith)).trans
      (mul_le_mul_of_nonneg_left (hV_d A hA2 hA_hi) (by norm_num))
  have hrpow_mul : (shortShellCapConst * Real.log V) ^ (p - 1) * Real.log V =
      shortShellCapConst ^ (p - 1) * (Real.log V) ^ p := by
    rw [Real.mul_rpow shortShellCapConst_pos.le hlogV_pos.le, mul_assoc]
    congr 1
    conv_rhs => rw [show p = (p - 1) + 1 by ring, Real.rpow_add hlogV_pos, Real.rpow_one]
  calc ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)), (burnolDeepOrderSum m A V) ^ p
      ≤ ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          (shortShellCapConst * Real.log V) ^ (p - 1) * burnolDeepOrderSum m A V :=
        Finset.sum_le_sum hterm
    _ = (shortShellCapConst * Real.log V) ^ (p - 1) *
          ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)), burnolDeepOrderSum m A V :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (shortShellCapConst * Real.log V) ^ (p - 1) *
          (8 * (C_d * (Real.exp (-(r * A)) / A) * V * Real.log V)) :=
        mul_le_mul_of_nonneg_left hsum1 (Real.rpow_nonneg hM_pos.le _)
    _ = 8 * C_d * (Real.exp (-(r * A)) / A) * V *
          ((shortShellCapConst * Real.log V) ^ (p - 1) * Real.log V) := by ring
    _ = 8 * shortShellCapConst ^ (p - 1) * C_d * (Real.exp (-(r * A)) / A) * V *
          (Real.log V) ^ p := by rw [hrpow_mul]; ring

/-- **Unconditional Short-Shell × Selberg Per-Window Second Moment Bound (`perWindow_deepOrderSum_sq_le_selberg`).** -/
theorem perWindow_deepOrderSum_sq_le_selberg {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C_d κ_r : ℝ, 0 < C_d ∧ 0 < κ_r ∧ ∀ᶠ V : ℝ in atTop,
      ∀ A : ℝ, 2 ≤ A → A ≤ κ_r * Real.log V →
        ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          (burnolDeepOrderSum m A V) ^ 2 ≤
          8 * shortShellCapConst * C_d * (Real.exp (-(r * A)) / A) * V *
            (Real.log V) ^ 2 := by
  obtain ⟨C_d, κ_r, hCd_pos, hκ_pos, hev⟩ := perWindow_deepOrderSum_rpow_le_selberg hr0 hr1
  refine ⟨C_d, κ_r, hCd_pos, hκ_pos, ?_⟩
  filter_upwards [hev] with V hV A hA2 hA_hi
  have h := hV A 2 hA2 hA_hi (by norm_num)
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two] using h

/-- **Unconditional Sub-Linear (`o(V)`) Per-Window Second Moment at the Double-Logarithmic Threshold
(`perWindow_deepOrderSum_sq_doubleLog_le`).**
At `A_V(r, u) = (2 / r) * log(log V) + u` (`0 < r < 1`, `0 ≤ u ≤ (κ_r / 2) * log V`), Selberg's
exponential `e^{-r A_V} = (log V)^{-2} e^{-r u}` identically cancels `(log V)^2`, giving
`∑_m N_m(A_V, V)^2 ≤ 4 * r * shortShellCapConst * C_d * e^{-r u} * V / log(log V) = o(V)`. -/
theorem perWindow_deepOrderSum_sq_doubleLog_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C_d κ_r : ℝ, 0 < C_d ∧ 0 < κ_r ∧ ∀ᶠ V : ℝ in atTop,
      ∀ u : ℝ, 0 ≤ u → u ≤ (κ_r / 2) * Real.log V →
        ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          (burnolDeepOrderSum m ((2 / r) * Real.log (Real.log V) + u) V) ^ 2 ≤
          4 * r * shortShellCapConst * C_d * Real.exp (-(r * u)) * V /
            Real.log (Real.log V) := by
  obtain ⟨C_d, κ_r, hCd_pos, hκ_pos, hsq_ev⟩ := perWindow_deepOrderSum_sq_le_selberg hr0 hr1
  refine ⟨C_d, κ_r, hCd_pos, hκ_pos, ?_⟩
  have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hsq_ev, eventually_ge_atTop (32 : ℝ),
    ht_ll.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop ((8 / (r * κ_r)) ^ 2 + 16)]
    with V hV_sq hV32 hll2 hlog_ge u hu0 hu_hi
  set L : ℝ := Real.log V
  have hL16 : 16 ≤ L := by dsimp only [L]; linarith [sq_nonneg (8 / (r * κ_r))]
  have hL_pos : 0 < L := by linarith
  have hll_pos : 0 < Real.log L := by linarith
  set A_V : ℝ := (2 / r) * Real.log L + u
  have h2r_gt2 : 2 < (2 / r) * Real.log L := by
    have h2r : 2 < 2 / r := by rw [lt_div_iff₀ hr0]; linarith
    nlinarith [hll2, h2r]
  have hAV_2 : 2 ≤ A_V := by dsimp only [A_V]; linarith
  have hAV_hi : A_V ≤ κ_r * L := by
    have hll_rt : Real.log L ≤ 2 * Real.sqrt L := log_le_two_sqrt_of_pos' hL_pos
    have hrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
    have hrt_gt : 8 / (r * κ_r) < Real.sqrt L := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 8 / (r * κ_r))]
      exact Real.sqrt_lt_sqrt (by positivity) (by dsimp only [L] at hL16 ⊢; linarith)
    have hmul1 := mul_lt_mul_of_pos_right hrt_gt hrt_pos
    rw [Real.mul_self_sqrt hL_pos.le] at hmul1
    have hmul2 := mul_lt_mul_of_pos_left hmul1 (mul_pos hr0 hκ_pos)
    rw [← mul_assoc, mul_div_cancel₀ 8 (mul_pos hr0 hκ_pos).ne'] at hmul2
    have h2r_le : (2 / r) * Real.log L ≤ (κ_r / 2) * L := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hr0]
      have h1 : 2 * Real.log L ≤ 4 * Real.sqrt L := by linarith only [hll_rt]
      have h2 : (κ_r / 2) * L * r = (1 / 2) * ((r * κ_r) * L) := by ring
      linarith only [h1, h2, hmul2]
    dsimp only [A_V]; linarith only [h2r_le, hu_hi]
  have hmain := hV_sq A_V hAV_2 hAV_hi
  have hexp_eq : Real.exp (-(r * A_V)) * L ^ 2 = Real.exp (-(r * u)) := by
    have hrA : -(r * A_V) = -(2 * Real.log L) + -(r * u) := by
      dsimp only [A_V]; field_simp [hr0.ne']; ring
    have hexp2L : Real.exp (-(2 * Real.log L)) * L ^ 2 = 1 := by
      rw [Real.exp_neg, show 2 * Real.log L = Real.log (L ^ (2 : ℕ)) by
        rw [Real.log_pow]; push_cast; rfl,
        Real.exp_log (pow_pos hL_pos 2), inv_mul_cancel₀ (pow_ne_zero 2 hL_pos.ne')]
    rw [hrA, Real.exp_add]
    calc (Real.exp (-(2 * Real.log L)) * Real.exp (-(r * u))) * L ^ 2
        = (Real.exp (-(2 * Real.log L)) * L ^ 2) * Real.exp (-(r * u)) := by ring
      _ = Real.exp (-(r * u)) := by rw [hexp2L, one_mul]
  have hdiv_le : 1 / A_V ≤ r / (2 * Real.log L) := by
    have hge : (2 / r) * Real.log L ≤ A_V := by dsimp only [A_V]; linarith
    have h1 := one_div_le_one_div_of_le (by positivity) hge
    rwa [show 1 / ((2 / r) * Real.log L) = r / (2 * Real.log L) by field_simp [hr0.ne', hll_pos.ne']] at h1
  calc ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)), (burnolDeepOrderSum m A_V V) ^ 2
      ≤ 8 * shortShellCapConst * C_d * (Real.exp (-(r * A_V)) / A_V) * V * L ^ 2 := hmain
    _ = 8 * shortShellCapConst * C_d * V * (Real.exp (-(r * A_V)) * L ^ 2) * (1 / A_V) := by ring
    _ = 8 * shortShellCapConst * C_d * V * Real.exp (-(r * u)) * (1 / A_V) := by rw [hexp_eq]
    _ ≤ 8 * shortShellCapConst * C_d * V * Real.exp (-(r * u)) * (r / (2 * Real.log L)) := by
        refine mul_le_mul_of_nonneg_left hdiv_le ?_
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          shortShellCapConst_pos.le) hCd_pos.le) (by linarith)) (Real.exp_pos _).le
    _ = 4 * r * shortShellCapConst * C_d * Real.exp (-(r * u)) * V / Real.log L := by
        field_simp [hll_pos.ne']; ring


/-! ## §2. Sharpness countermodels and giant-cluster `IFF` characterization of `(D_win) ↔ (D_zero)` -/

/-- **Fixed-`A` `(log V)^2` Sharpness Theorem (`clusteredModel_sqMoment_lower_bound`).**
`clusteredModel` satisfies `UnitWindowStripZeroModel` and `WindowOccupancy`, yet for every `A > 0`
its per-window deep-zero second moment grows at least as `c_A * V * (log V)^2`, proving that the
`(log V)^2` factor in `perWindow_deepOrderSum_sq_le_selberg` cannot be improved at any fixed `A`
from local RvM, simple critical majority, arbitrary-rate Selberg density, and `WindowOccupancy`. -/
theorem clusteredModel_sqMoment_lower_bound :
    clusteredModel.WindowOccupancy ∧
    ∀ A : ℝ, 0 < A → ∀ᶠ V : ℝ in atTop,
      (1 / (2704 * (2 : ℝ) ^ (Nat.ceil (4 * A) + 6))) * V * (Real.log V) ^ 2 ≤
        ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          (∑ z ∈ (clusteredModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
            (clusteredModel.mult z : ℝ)) ^ 2 := by
  have hocc : clusteredModel.WindowOccupancy := by
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
          have hact : activeClust m := by by_contra hnot; simp [qClust, hnot] at hq_pos
          have hm_ge_V : V ≤ (m : ℝ) :=
            (Nat.le_ceil V).trans (by exact_mod_cast (Finset.mem_Icc.mp hm_I).1)
          have hm_ne0 : m ≠ 0 := by intro h0; subst h0; simp at hm_ge_V; linarith
          have hlog_ge : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
          simp only [dClust, if_pos hact] at hbd
          have h1 : A / Real.log V ≤ (evenHalves m : ℝ) / (2 * Real.log V) :=
            hbd.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith))
          have h2 : 2 * A ≤ (evenHalves m : ℝ) := by
            have hm_mul := (div_le_div_iff₀ hlogV_pos (by positivity)).mp h1
            rw [show A * (2 * Real.log V) = (2 * A) * Real.log V by ring] at hm_mul
            exact le_of_mul_le_mul_right hm_mul hlogV_pos
          exact two_pow_dvd_of_le_evenHalves hm_ne0 (max_le hact.2.1 (Nat.ceil_le.mpr h2))
        have h2v₀_le_V : (2 : ℝ) ^ v₀ ≤ V := by
          have hv₀_le : (v₀ : ℝ) ≤ 2 * A + 1 := by
            dsimp only [v₀]; rw [Nat.cast_max, Nat.cast_one]
            exact max_le (by linarith) (Nat.ceil_lt_add_one (by positivity)).le
          have hmul1 : (v₀ : ℝ) * Real.log 2 ≤ (v₀ : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left log_two_lt_one.le (Nat.cast_nonneg _)
          have hlog_pow : (v₀ : ℝ) * Real.log 2 ≤ Real.log V := by linarith
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
        have hcR : (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
            (fun m => ∃ z ∈ clusteredModel.Z m, A / Real.log V ≤ |z.re - 1 / 2|)).card : ℝ) ≤
            ((Nat.floor (2 * V) / 2 ^ v₀ : ℕ) : ℝ) + 1 := by exact_mod_cast hc
        have hpow_exp : ((2 : ℝ) ^ v₀)⁻¹ ≤ Real.exp (-A) := by
          have hv₀_ge : 2 * A ≤ (v₀ : ℝ) := by
            dsimp only [v₀]; rw [Nat.cast_max]; exact (Nat.le_ceil _).trans (le_max_right _ _)
          have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
          have hmul : A ≤ (v₀ : ℝ) * Real.log 2 := by
            calc A = (2 * A) * (1 / 2) := by ring
              _ ≤ (v₀ : ℝ) * Real.log 2 := mul_le_mul hv₀_ge hlog2 (by norm_num) (Nat.cast_nonneg _)
          rw [← Real.exp_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ v₀)⁻¹), Real.log_inv, Real.log_pow]
          exact Real.exp_le_exp.mpr (by linarith)
        have h3V : (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
            (fun m => ∃ z ∈ clusteredModel.Z m, A / Real.log V ≤ |z.re - 1 / 2|)).card : ℝ) ≤
            3 * V * ((2 : ℝ) ^ v₀)⁻¹ := by
          have hrew : 2 * V / (2 : ℝ) ^ v₀ + V / (2 : ℝ) ^ v₀ = 3 * V * ((2 : ℝ) ^ v₀)⁻¹ := by ring
          linarith
        calc _ ≤ 3 * V * Real.exp (-A) :=
              h3V.trans (mul_le_mul_of_nonneg_left hpow_exp (by positivity))
          _ ≤ 6 * Real.exp (-A) * V := by
              have hpv : 0 ≤ Real.exp (-A) * V := by positivity
              linarith
  refine ⟨hocc, fun A hA => ?_⟩
  set v_A : ℕ := Nat.ceil (4 * A) + 4
  filter_upwards [eventually_ge_atTop (max 512 ((2 : ℝ) ^ (v_A + 3))),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 104 (8 * (v_A : ℝ)))] with V hV_ge hlog_ge
  have hV512 : 512 ≤ V := (le_max_left _ _).trans hV_ge
  have hVv : (2 : ℝ) ^ (v_A + 3) ≤ V := (le_max_right _ _).trans hV_ge
  have hlog104 : 104 ≤ Real.log V := (le_max_left _ _).trans hlog_ge
  have hlog_v : 8 * (v_A : ℝ) ≤ Real.log V := (le_max_right _ _).trans hlog_ge
  have hlogV_pos : 0 < Real.log V := by linarith
  obtain ⟨S, hS_sub, hS_ev, hS_card⟩ := exists_evenHalves_subset_Icc v_A hVv
  have hterm : ∀ m ∈ S, (Real.log V / 52) ^ 2 ≤
      (∑ z ∈ (clusteredModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
        (clusteredModel.mult z : ℝ)) ^ 2 := by
    intro m hmS
    have hm_I := hS_sub hmS
    obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
    have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
    have hm_le_2V : (m : ℝ) ≤ 2 * V :=
      ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by linarith))
    have hm256 : 256 ≤ m := by
      by_contra hlt; have : (m : ℝ) < 256 := by exact_mod_cast (not_le.mp hlt)
      linarith
    have hev : evenHalves m = v_A := hS_ev m hmS
    have hlog_ge_m : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log (by linarith) hm_ge_V
    have hact : activeClust m := ⟨hm256, by rw [hev]; dsimp only [v_A]; omega,
      by rw [hev]; linarith⟩
    have hcnt : Real.log V / 52 ≤
        ∑ z ∈ (clusteredModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
          (clusteredModel.mult z : ℝ) := by
      dsimp only [clusteredModel]
      simp only [Nat.cast_one]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        packetWin_filter_abs_card (div_pos hA hlogV_pos) (qClust_dClust_or m), if_pos]
      · simp only [qClust, if_pos hact]; push_cast
        linarith [Nat.lt_floor_add_one (Real.log (m : ℝ) / 52)]
      · simp only [dClust, if_pos hact, hev]
        have hlog2 : Real.log (m : ℝ) ≤ 2 * Real.log V := by
          have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V) := Real.log_le_log (by linarith) hm_le_2V
          rw [Real.log_mul zero_lt_two.ne' (by linarith)] at h1
          linarith [h1, log_two_lt_one]
        have hv4A : 4 * A ≤ (v_A : ℝ) := by
          dsimp only [v_A]; push_cast; linarith [Nat.le_ceil (4 * A)]
        calc A / Real.log V = (4 * A) / (4 * Real.log V) := by ring
          _ ≤ (v_A : ℝ) / (4 * Real.log V) := div_le_div_of_nonneg_right hv4A (by positivity)
          _ ≤ (v_A : ℝ) / (2 * Real.log (m : ℝ)) :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) (by linarith)
    exact pow_le_pow_left₀ (by positivity) hcnt 2
  have hv_pow : (2 : ℝ) ^ (v_A + 2) = (2 : ℝ) ^ (Nat.ceil (4 * A) + 6) := by
    dsimp only [v_A]
  calc (1 / (2704 * (2 : ℝ) ^ (Nat.ceil (4 * A) + 6))) * V * (Real.log V) ^ 2
      = (V / (2 : ℝ) ^ (v_A + 2)) * (Real.log V / 52) ^ 2 := by rw [hv_pow]; ring
    _ ≤ (S.card : ℝ) * (Real.log V / 52) ^ 2 :=
        mul_le_mul_of_nonneg_right hS_card (sq_nonneg _)
    _ = ∑ _m ∈ S, (Real.log V / 52) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ S, (∑ z ∈ (clusteredModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
          (clusteredModel.mult z : ℝ)) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun _ _ _ => sq_nonneg _

/-- Elementary binary bit-length `⌊log₂ k⌋ + 1` for `k ≥ 1`, `0` at `0`. -/
private def natBitLen : ℕ → ℕ
  | 0 => 0
  | n + 1 => natBitLen ((n + 1) / 2) + 1

private lemma natBitLen_bounds :
    ∀ k : ℕ, 1 ≤ k → k < 2 ^ natBitLen k ∧ 2 ^ natBitLen k ≤ 2 * k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk1
    rcases eq_or_lt_of_le hk1 with rfl | hk2
    · rw [show (1 : ℕ) = 0 + 1 by rfl, natBitLen, show (0 + 1) / 2 = 0 by norm_num, natBitLen]
      norm_num
    · have hk_succ : k = (k - 1) + 1 := by omega
      have hdiv_ge : 1 ≤ k / 2 := by omega
      have hdiv_lt : k / 2 < k := Nat.div_lt_self (by omega) one_lt_two
      obtain ⟨h1, h2⟩ := ih (k / 2) hdiv_lt hdiv_ge
      have hlen : natBitLen k = natBitLen (k / 2) + 1 := by
        conv_lhs => rw [hk_succ, natBitLen]
        rw [← hk_succ]
      rw [hlen, pow_succ']
      exact ⟨by omega, by omega⟩

private lemma natBitLen_mono : ∀ b a : ℕ, a ≤ b → natBitLen a ≤ natBitLen b := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a hab
    rcases Nat.eq_zero_or_pos a with rfl | ha_pos
    · simp [natBitLen]
    · have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hab
      have ha_eq : natBitLen a = natBitLen (a / 2) + 1 := by
        conv_lhs => rw [show a = (a - 1) + 1 by omega, natBitLen]
        rw [show (a - 1) + 1 = a by omega]
      have hb_eq : natBitLen b = natBitLen (b / 2) + 1 := by
        conv_lhs => rw [show b = (b - 1) + 1 by omega, natBitLen]
        rw [show (b - 1) + 1 = b by omega]
      rw [ha_eq, hb_eq]
      exact Nat.add_le_add_right
        (ih (b / 2) (Nat.div_lt_self hb_pos one_lt_two) (a / 2) (Nat.div_le_div_right hab)) 1

private lemma natBitLen_two_mul {k : ℕ} (hk : 1 ≤ k) : natBitLen (2 * k) = natBitLen k + 1 := by
  conv_lhs => rw [show 2 * k = (2 * k - 1) + 1 by omega, natBitLen]
  rw [show ((2 * k - 1) + 1) / 2 = k by omega]

private def logTwoShift (m : ℕ) : ℕ :=
  natBitLen (Nat.floor (Real.log (m : ℝ)) + 1)

private def activeLogSp (m : ℕ) : Prop :=
  256 ≤ m ∧ logTwoShift m + 1 ≤ evenHalves m ∧
    ((evenHalves m - logTwoShift m : ℕ) : ℝ) ≤ (1 / 8) * Real.log (m : ℝ)

private def qLogSp (m : ℕ) : ℕ :=
  if activeLogSp m then Nat.floor (Real.log (m : ℝ) / 52) else 0

private def dLogSp (m : ℕ) : ℝ :=
  if activeLogSp m then ((evenHalves m - logTwoShift m : ℕ) : ℝ) / (2 * Real.log (m : ℝ)) else 0

private def nLogSp (m : ℕ) : ℕ := 2 * basePairs m - 2 * qLogSp m

private lemma qLogSp_dLogSp_spec (m : ℕ) :
    qLogSp m = 0 ∨ (0 < dLogSp m ∧ dLogSp m < 1 / 2) := by
  by_cases hact : activeLogSp m
  · refine Or.inr ?_
    simp only [dLogSp, if_pos hact]
    obtain ⟨hm256, hv_ge, hv_ub⟩ := hact
    have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hv_pos : (0 : ℝ) < ((evenHalves m - logTwoShift m : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < evenHalves m - logTwoShift m by omega)
    exact ⟨by positivity, (div_lt_iff₀ (by positivity)).mpr (by linarith)⟩
  · exact Or.inl (by simp [qLogSp, hact])

private lemma qLogSp_dLogSp_or (m : ℕ) : qLogSp m = 0 ∨ 0 < dLogSp m :=
  (qLogSp_dLogSp_spec m).imp id And.left

private lemma qLogSp_le_basePairs (m : ℕ) : qLogSp m ≤ basePairs m := by
  by_cases hact : activeLogSp m
  · have hm_not : ¬ m < 256 := not_lt.mpr hact.1
    simp only [qLogSp, if_pos hact, basePairs, if_neg hm_not]
    have hlog_nn : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    exact (Nat.floor_mono (div_le_div_of_nonneg_left hlog_nn (by positivity) (by linarith))).trans
      (Nat.le_succ _)
  · simp [qLogSp, hact]

private lemma nLogSp_add_two_qLogSp (m : ℕ) : nLogSp m + 2 * qLogSp m = 2 * basePairs m := by
  have := qLogSp_le_basePairs m; dsimp only [nLogSp]; omega

private lemma dLogSp_le_one_sixteenth (m : ℕ) : dLogSp m ≤ 1 / 16 := by
  by_cases hact : activeLogSp m
  · simp only [dLogSp, if_pos hact]
    obtain ⟨hm256, _, hv_ub⟩ := hact
    have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  · simp only [dLogSp, if_neg hact]; norm_num

private lemma logTwoShift_dyadic_bounds {V : ℝ} (hV16 : 16 ≤ V) {m : ℕ}
    (hm_ge : V ≤ (m : ℝ)) (hm_le : (m : ℝ) ≤ 2 * V) :
    let r_V := natBitLen (Nat.floor (Real.log V) + 1)
    Real.log V ≤ (2 : ℝ) ^ r_V ∧ (2 : ℝ) ^ r_V ≤ 4 * Real.log V ∧
      r_V ≤ logTwoShift m ∧ logTwoShift m ≤ r_V + 1 := by
  intro r_V
  have hV_pos : 0 < V := by linarith
  have hlogV_ge2 : 2 ≤ Real.log V := by
    have h16 : (2 : ℝ) ^ (4 : ℕ) ≤ V := by norm_num; linarith
    have hl := Real.log_le_log (by norm_num) h16
    rw [Real.log_pow, Nat.cast_ofNat] at hl
    linarith [Real.log_two_gt_d9]
  set k_V : ℕ := Nat.floor (Real.log V) + 1
  obtain ⟨hk_lt, hk_ub⟩ := natBitLen_bounds k_V (by omega)
  have h2r_ge : Real.log V ≤ (2 : ℝ) ^ r_V := by
    have h1 : Real.log V < (k_V : ℝ) := by
      dsimp only [k_V]; push_cast; exact Nat.lt_floor_add_one _
    have h2 : (k_V : ℝ) ≤ (2 : ℝ) ^ r_V := by exact_mod_cast hk_lt.le
    exact h1.le.trans h2
  have h2r_le : (2 : ℝ) ^ r_V ≤ 4 * Real.log V := by
    have h1 : (2 : ℝ) ^ r_V ≤ 2 * (k_V : ℝ) := by exact_mod_cast hk_ub
    have h2 : (k_V : ℝ) ≤ Real.log V + 1 := by
      dsimp only [k_V]; push_cast
      linarith [Nat.floor_le (by linarith : 0 ≤ Real.log V)]
    linarith
  have hlog_ge : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge
  have hlog_lt : Real.log (m : ℝ) < Real.log V + 1 := by
    have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V) := Real.log_le_log (by linarith) hm_le
    rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
    linarith [h1, log_two_lt_one]
  set k_m : ℕ := Nat.floor (Real.log (m : ℝ)) + 1
  have hk_mono : k_V ≤ k_m := Nat.add_le_add_right (Nat.floor_mono hlog_ge) 1
  have hkm_le2 : k_m ≤ 2 * k_V := by
    have hfl : Nat.floor (Real.log (m : ℝ)) ≤ Nat.floor (Real.log V) + 1 := by
      have hlt2 : Real.log (m : ℝ) < ((Nat.floor (Real.log V) + 2 : ℕ) : ℝ) := by
        push_cast; linarith [Nat.lt_floor_add_one (Real.log V)]
      have hfl_le : (Nat.floor (Real.log (m : ℝ)) : ℝ) <
          ((Nat.floor (Real.log V) + 2 : ℕ) : ℝ) :=
        (Nat.floor_le (by linarith)).trans_lt hlt2
      have hn := Nat.cast_lt.mp hfl_le
      omega
    dsimp only [k_m, k_V]; omega
  refine ⟨h2r_ge, h2r_le, natBitLen_mono k_m k_V hk_mono, ?_⟩
  calc logTwoShift m = natBitLen k_m := rfl
    _ ≤ natBitLen (2 * k_V) := natBitLen_mono (2 * k_V) k_m hkm_le2
    _ = r_V + 1 := natBitLen_two_mul (by omega)

private def logSpacingModel : UnitWindowStripZeroModel where
  Z m := packetWin m (nLogSp m) (qLogSp m) (dLogSp m)
  mult _ := 1
  in_unit_strip m := packetWin_in_unit_strip (qLogSp_dLogSp_spec m)
  mult_pos _ _ _ := zero_lt_one
  refl_mem m := packetWin_refl_mem m (nLogSp m) (qLogSp m) (dLogSp m)
  refl_mult _ _ _ := rfl
  local_rvm := by
    refine ⟨2, by norm_num, fun m hm => ?_⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one, packetWin_card (qLogSp_dLogSp_or m),
      nLogSp_add_two_qLogSp m]
    exact basePairs_rvm hm
  critical_simple_majority := by
    filter_upwards [eventually_ge_atTop 256] with m hm256
    rw [Finset.sum_const, smul_eq_mul, mul_one, packetWin_card (qLogSp_dLogSp_or m),
      nLogSp_add_two_qLogSp m, packetWin_filter_crit_card (qLogSp_dLogSp_or m)]
    have hle2q : 2 * qLogSp m ≤ 2 * basePairs m := Nat.mul_le_mul_left 2 (qLogSp_le_basePairs m)
    have hn_eq : (nLogSp m : ℝ) = ((2 * basePairs m : ℕ) : ℝ) - 2 * (qLogSp m : ℝ) := by
      dsimp only [nLogSp]
      have hc := Nat.cast_sub (R := ℝ) hle2q
      push_cast at hc ⊢; exact hc
    rw [hn_eq]
    have hm_not : ¬ m < 256 := not_lt.mpr hm256
    have hlog_nn : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    have hq_ub : (qLogSp m : ℝ) ≤ Real.log (m : ℝ) / 52 := by
      by_cases hact : activeLogSp m
      · simp only [qLogSp, if_pos hact]; exact Nat.floor_le (by positivity)
      · simp only [qLogSp, if_neg hact, Nat.cast_zero]; positivity
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
      Real.tendsto_log_atTop.eventually_ge_atTop 32] with V hV512 hlog32 a ha1
    simp only [Nat.cast_one]
    have hV_pos : 0 < V := by linarith
    have hlogV_pos : 0 < Real.log V := by linarith
    rcases lt_or_ge ((1 / 16) * Real.log V) a with ha_gt | ha_le
    · have hzero : ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ z ∈ (packetWin m (nLogSp m) (qLogSp m) (dLogSp m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
          packetWin_filter_right_card (div_pos (by linarith) hlogV_pos) (qLogSp_dLogSp_or m),
          if_neg]
        have h1 := dLogSp_le_one_sixteenth m
        have h2 : 1 / 16 < a / Real.log V := by rw [lt_div_iff₀ hlogV_pos]; linarith
        linarith
      rw [hzero, mul_zero, mul_zero]; positivity
    · set r_V : ℕ := natBitLen (Nat.floor (Real.log V) + 1)
      set v₀ : ℕ := r_V + Nat.ceil (2 * a)
      set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
      set Dvd_V := I_V.filter (fun m => 2 ^ v₀ ∣ m)
      have hzero_off : ∀ m ∈ I_V, m ∉ Dvd_V →
          ∑ z ∈ (packetWin m (nLogSp m) (qLogSp m) (dLogSp m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) = 0 := by
        intro m hm_I hnot_dvd
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
          packetWin_filter_right_card (div_pos (by linarith) hlogV_pos) (qLogSp_dLogSp_or m)]
        split_ifs with hbd
        · by_cases hact : activeLogSp m
          · exfalso; apply hnot_dvd
            refine Finset.mem_filter.mpr ⟨hm_I, ?_⟩
            obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
            have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
            have hm_le_2V : (m : ℝ) ≤ 2 * V :=
              ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
            have hm_ne0 : m ≠ 0 := by intro h0; subst h0; simp at hm_ge_V; linarith
            obtain ⟨_, _, hr_lo, _⟩ := logTwoShift_dyadic_bounds (by linarith) hm_ge_V hm_le_2V
            have hlog_ge : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
            simp only [dLogSp, if_pos hact] at hbd
            have h1 : a / Real.log V ≤
                ((evenHalves m - logTwoShift m : ℕ) : ℝ) / (2 * Real.log V) :=
              hbd.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith))
            have h2 : 2 * a ≤ ((evenHalves m - logTwoShift m : ℕ) : ℝ) := by
              have hm_mul := (div_le_div_iff₀ hlogV_pos (by positivity)).mp h1
              rw [show a * (2 * Real.log V) = (2 * a) * Real.log V by ring] at hm_mul
              exact le_of_mul_le_mul_right hm_mul hlogV_pos
            have hceil_le : Nat.ceil (2 * a) ≤ evenHalves m - logTwoShift m := Nat.ceil_le.mpr h2
            have hv₀_le : v₀ ≤ evenHalves m := by
              have := hact.2.1; dsimp only [v₀]; omega
            exact two_pow_dvd_of_le_evenHalves hm_ne0 hv₀_le
          · simp [qLogSp, hact]
        · rfl
      rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero_off]
      have hq_ub : ∀ m ∈ Dvd_V,
          ∑ z ∈ (packetWin m (nLogSp m) (qLogSp m) (dLogSp m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) ≤ Real.log V / 26 := by
        intro m hm_D
        have hm_I := (Finset.mem_filter.mp hm_D).1
        have hm_le_2V : (m : ℝ) ≤ 2 * V :=
          ((Nat.cast_le (α := ℝ)).mpr (Finset.mem_Icc.mp hm_I).2).trans
            (Nat.floor_le (by positivity))
        have hm_ge_V : V ≤ (m : ℝ) :=
          (Nat.le_ceil V).trans (by exact_mod_cast (Finset.mem_Icc.mp hm_I).1)
        rw [Finset.sum_const, nsmul_eq_mul, mul_one,
          packetWin_filter_right_card (div_pos (by linarith) hlogV_pos) (qLogSp_dLogSp_or m)]
        split_ifs
        · by_cases hact : activeLogSp m
          · simp only [qLogSp, if_pos hact]
            have hfl : (Nat.floor (Real.log (m : ℝ) / 52) : ℝ) ≤ Real.log (m : ℝ) / 52 :=
              Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith)) (by norm_num))
            have hlog2 : Real.log (m : ℝ) ≤ 2 * Real.log V := by
              have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V) :=
                Real.log_le_log (by linarith) hm_le_2V
              rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
              linarith [h1, log_two_lt_one]
            linarith
          · simp only [qLogSp, if_neg hact, Nat.cast_zero]; positivity
        · simp only [Nat.cast_zero]; positivity
      have hrV_bounds := logTwoShift_dyadic_bounds (by linarith : 16 ≤ V)
        (Nat.le_ceil V) ((Nat.ceil_lt_add_one hV_pos.le).le.trans (by linarith))
      have h2rV_le : (2 : ℝ) ^ r_V ≤ 4 * Real.log V := hrV_bounds.2.1
      have h2v₀_le_V : (2 : ℝ) ^ v₀ ≤ V := by
        have h2a_le : (2 : ℝ) ^ Nat.ceil (2 * a) ≤ Real.exp ((1 / 8) * Real.log V + 1) := by
          have hv_le : (Nat.ceil (2 * a) : ℝ) ≤ 2 * a + 1 :=
            (Nat.ceil_lt_add_one (by positivity)).le
          have hlog_p : (Nat.ceil (2 * a) : ℝ) * Real.log 2 ≤ (1 / 8) * Real.log V + 1 := by
            have hm1 : (Nat.ceil (2 * a) : ℝ) * Real.log 2 ≤ (Nat.ceil (2 * a) : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left log_two_lt_one.le (Nat.cast_nonneg _)
            linarith
          rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.ceil (2 * a)), Real.log_pow]
          exact Real.exp_le_exp.mpr hlog_p
        have h4log_le : 4 * Real.log V ≤ Real.exp ((1 / 2) * Real.log V) := by
          have h4e : 4 * Real.log V ≤ Real.exp ((3 / 8) * Real.log V) * Real.exp ((1 / 8) * Real.log V) := by
            have h1 : (3 / 8) * Real.log V ≤ Real.exp ((3 / 8) * Real.log V) := by
              linarith [Real.add_one_le_exp ((3 / 8) * Real.log V)]
            have h2 : (32 / 3 : ℝ) ≤ Real.exp ((1 / 8) * Real.log V) := by
              have hl4 : (4 : ℝ) ≤ (1 / 8) * Real.log V := by linarith
              have he4 : (12 : ℝ) ≤ Real.exp 4 := by
                have h2_ge : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
                calc (12 : ℝ) ≤ (2 : ℝ) ^ (4 : ℕ) := by norm_num
                  _ ≤ (Real.exp 1) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) h2_ge 4
                  _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
              exact (by norm_num : (32 / 3 : ℝ) ≤ 12).trans (he4.trans (Real.exp_le_exp.mpr hl4))
            have hprod := mul_le_mul h1 h2 (by norm_num) (Real.exp_pos _).le
            linarith
          exact h4e.trans_eq (by rw [← Real.exp_add]; congr 1; ring)
        calc (2 : ℝ) ^ v₀ = (2 : ℝ) ^ r_V * (2 : ℝ) ^ Nat.ceil (2 * a) := by
              dsimp only [v₀]; rw [pow_add]
          _ ≤ Real.exp ((1 / 2) * Real.log V) * Real.exp ((1 / 8) * Real.log V + 1) :=
              mul_le_mul (h2rV_le.trans h4log_le) h2a_le (by positivity) (Real.exp_pos _).le
          _ = Real.exp ((5 / 8) * Real.log V + 1) := by rw [← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (Real.log V) := Real.exp_le_exp.mpr (by linarith)
          _ = V := Real.exp_log hV_pos
      have hc := card_Icc_filter_dvd_le (Nat.ceil V) (Nat.floor (2 * V)) (2 ^ v₀)
      have hdiv_le : ((Nat.floor (2 * V) / 2 ^ v₀ : ℕ) : ℝ) ≤ 2 * V / (2 : ℝ) ^ v₀ := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : (Nat.floor (2 * V) / 2 ^ v₀) * 2 ^ v₀ ≤ Nat.floor (2 * V) := Nat.div_mul_le_self _ _
        have h2 : (((Nat.floor (2 * V) / 2 ^ v₀) * 2 ^ v₀ : ℕ) : ℝ) ≤
            (Nat.floor (2 * V) : ℝ) := by exact_mod_cast h1
        push_cast at h2; exact h2.trans (Nat.floor_le (by positivity))
      have h1_le : (1 : ℝ) ≤ V / (2 : ℝ) ^ v₀ := (one_le_div (by positivity)).mpr h2v₀_le_V
      have hcR : (Dvd_V.card : ℝ) ≤ ((Nat.floor (2 * V) / 2 ^ v₀ : ℕ) : ℝ) + 1 := by exact_mod_cast hc
      have hDvd_card : (Dvd_V.card : ℝ) ≤ 3 * V * ((2 : ℝ) ^ v₀)⁻¹ := by
        have hrew : 2 * V / (2 : ℝ) ^ v₀ + V / (2 : ℝ) ^ v₀ = 3 * V * ((2 : ℝ) ^ v₀)⁻¹ := by ring
        linarith
      have hpow_le : ((2 : ℝ) ^ v₀)⁻¹ ≤ Real.exp (-(6 / 5 * a)) := by
        have hv_ge : 2 * a ≤ (v₀ : ℝ) := by
          dsimp only [v₀]; push_cast
          exact (Nat.le_ceil (2 * a)).trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
        have hlog2 : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hmul : 6 / 5 * a ≤ (v₀ : ℝ) * Real.log 2 := by
          calc 6 / 5 * a = (2 * a) * (3 / 5) := by ring
            _ ≤ (v₀ : ℝ) * Real.log 2 := mul_le_mul hv_ge hlog2 (by norm_num) (Nat.cast_nonneg _)
        rw [← Real.exp_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ v₀)⁻¹), Real.log_inv, Real.log_pow]
        exact Real.exp_le_exp.mpr (by linarith)
      have ha_exp : a * Real.exp (-(6 / 5 * a)) ≤ 5 * Real.exp (-(r * a)) := by
        have h1 : a / 5 ≤ Real.exp (a / 5) := by linarith [Real.add_one_le_exp (a / 5)]
        have h2 : a * Real.exp (-(6 / 5 * a)) ≤ (5 * Real.exp (a / 5)) * Real.exp (-(6 / 5 * a)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        have h3 : (5 * Real.exp (a / 5)) * Real.exp (-(6 / 5 * a)) = 5 * Real.exp (-a) := by
          rw [mul_assoc, ← Real.exp_add, show a / 5 + -(6 / 5 * a) = -a by ring]
        have hra : r * a ≤ 1 * a := mul_le_mul_of_nonneg_right hr1.le (by linarith)
        have h4 : Real.exp (-a) ≤ Real.exp (-(r * a)) := Real.exp_le_exp.mpr (by linarith)
        linarith [h2, h3, mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 5)]
      have hsum_Dvd : ∑ m ∈ Dvd_V,
          ∑ z ∈ (packetWin m (nLogSp m) (qLogSp m) (dLogSp m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) ≤
          (3 / 26) * Real.exp (-(6 / 5 * a)) * V * Real.log V := by
        calc _ ≤ ∑ _m ∈ Dvd_V, Real.log V / 26 := Finset.sum_le_sum hq_ub
          _ = (Dvd_V.card : ℝ) * (Real.log V / 26) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (3 * V * Real.exp (-(6 / 5 * a))) * (Real.log V / 26) :=
              mul_le_mul_of_nonneg_right
                (hDvd_card.trans (mul_le_mul_of_nonneg_left hpow_le (by positivity))) (by positivity)
          _ = (3 / 26) * Real.exp (-(6 / 5 * a)) * V * Real.log V := by ring
      calc 2 * Real.pi * ((a / Real.log V) *
            ∑ m ∈ Dvd_V,
              ∑ z ∈ (packetWin m (nLogSp m) (qLogSp m) (dLogSp m)).filter
                (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ))
          ≤ 2 * Real.pi * ((a / Real.log V) *
              ((3 / 26) * Real.exp (-(6 / 5 * a)) * V * Real.log V)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_Dvd (by positivity)) (by positivity)
        _ = (3 / 13) * Real.pi * (a * Real.exp (-(6 / 5 * a))) * V := by
            field_simp [hlogV_pos.ne']; ring
        _ ≤ (3 / 13) * Real.pi * (5 * Real.exp (-(r * a))) * V :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha_exp (by positivity)) hV_pos.le
        _ ≤ 4 * Real.pi * Real.exp (-(r * a)) * V := by
            have hpv : 0 ≤ Real.pi * Real.exp (-(r * a)) * V := by positivity
            linarith

private lemma shift_diff_bounds {r s c : ℕ} (hlo : r ≤ s) (hhi : s ≤ r + 1) (hc : 1 ≤ c) :
    s + 1 ≤ r + 1 + c ∧ r + 1 + c - s ≤ c + 1 ∧ c ≤ r + 1 + c - s := by
  omega

private lemma logSpacingModel_logFreeZeroDensity : logSpacingModel.LogFreeZeroDensity := by
  refine ⟨fun A => Real.exp (-A) + 1 / max A 1, ?_, fun A hA => ?_⟩
  · have h1 : Tendsto (fun A : ℝ => Real.exp (-A)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa only [add_zero] using h1.add tendsto_one_div_max_one_zero
  · filter_upwards [eventually_ge_atTop (max 512 ((4 * max A 1) ^ 2 + 16)),
      Real.tendsto_log_atTop.eventually_ge_atTop 32] with V hV_ge hlog32
    have hV512 : 512 ≤ V := (le_max_left _ _).trans hV_ge
    have hVA_sq : (4 * max A 1) ^ 2 + 16 ≤ V := (le_max_right _ _).trans hV_ge
    have hV_pos : 0 < V := by linarith only [hV512]
    have hlogV_pos : 0 < Real.log V := by linarith only [hlog32]
    rcases lt_or_ge ((1 / 16) * Real.log V) A with hA_gt | hA_le
    · have hzero : ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ z ∈ (logSpacingModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
            (logSpacingModel.mult z : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun m _ => ?_
        dsimp only [logSpacingModel]; simp only [Nat.cast_one]
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
          packetWin_filter_abs_card (div_pos hA hlogV_pos) (qLogSp_dLogSp_or m), if_neg]
        have h1 := dLogSp_le_one_sixteenth m
        have h2 : 1 / 16 < A / Real.log V := by rw [lt_div_iff₀ hlogV_pos]; linarith only [hA_gt]
        exact not_le.mpr (h1.trans_lt h2)
      rw [hzero]; positivity
    · set r_V : ℕ := natBitLen (Nat.floor (Real.log V) + 1)
      set k_A : ℕ := max 1 (Nat.ceil (2 * A))
      set v₀ : ℕ := r_V + k_A
      set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
      set Dvd_V := I_V.filter (fun m => 2 ^ v₀ ∣ m)
      have hzero_off : ∀ m ∈ I_V, m ∉ Dvd_V →
          ∑ z ∈ (logSpacingModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
            (logSpacingModel.mult z : ℝ) = 0 := by
        intro m hm_I hnot_dvd
        dsimp only [logSpacingModel]; simp only [Nat.cast_one]
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
          packetWin_filter_abs_card (div_pos hA hlogV_pos) (qLogSp_dLogSp_or m)]
        split_ifs with hbd
        · by_cases hact : activeLogSp m
          · exfalso; apply hnot_dvd
            refine Finset.mem_filter.mpr ⟨hm_I, ?_⟩
            obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
            have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
            have hm_le_2V : (m : ℝ) ≤ 2 * V :=
              ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
            have hm_ne0 : m ≠ 0 := by intro h0; subst h0; simp at hm_ge_V; linarith only [hV512, hm_ge_V]
            obtain ⟨_, _, hr_lo, _⟩ := logTwoShift_dyadic_bounds (by linarith only [hV512]) hm_ge_V hm_le_2V
            have hlog_ge : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
            simp only [dLogSp, if_pos hact] at hbd
            have h1 : A / Real.log V ≤
                ((evenHalves m - logTwoShift m : ℕ) : ℝ) / (2 * Real.log V) :=
              hbd.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
                (by linarith only [hlog_ge]))
            have h2 : 2 * A ≤ ((evenHalves m - logTwoShift m : ℕ) : ℝ) := by
              have hm_mul := (div_le_div_iff₀ hlogV_pos (by positivity)).mp h1
              rw [show A * (2 * Real.log V) = (2 * A) * Real.log V by ring] at hm_mul
              exact le_of_mul_le_mul_right hm_mul hlogV_pos
            have hkA_le : k_A ≤ evenHalves m - logTwoShift m :=
              max_le (by have := hact.2.1; omega) (Nat.ceil_le.mpr h2)
            exact two_pow_dvd_of_le_evenHalves hm_ne0 (by dsimp only [v₀]; omega)
          · simp [qLogSp, hact]
        · rfl
      rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero_off]
      have hq_ub : ∀ m ∈ Dvd_V,
          ∑ z ∈ (logSpacingModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
            (logSpacingModel.mult z : ℝ) ≤ Real.log V / 13 := by
        intro m hm_D
        have hm_I := (Finset.mem_filter.mp hm_D).1
        have hm_le_2V : (m : ℝ) ≤ 2 * V :=
          ((Nat.cast_le (α := ℝ)).mpr (Finset.mem_Icc.mp hm_I).2).trans
            (Nat.floor_le (by positivity))
        have hm_ge_V : V ≤ (m : ℝ) :=
          (Nat.le_ceil V).trans (by exact_mod_cast (Finset.mem_Icc.mp hm_I).1)
        dsimp only [logSpacingModel]; simp only [Nat.cast_one]
        rw [Finset.sum_const, nsmul_eq_mul, mul_one,
          packetWin_filter_abs_card (div_pos hA hlogV_pos) (qLogSp_dLogSp_or m)]
        split_ifs
        · by_cases hact : activeLogSp m
          · simp only [qLogSp, if_pos hact]; push_cast
            have hfl : (Nat.floor (Real.log (m : ℝ) / 52) : ℝ) ≤ Real.log (m : ℝ) / 52 :=
              Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith only [hV512, hm_ge_V])) (by norm_num))
            have hlog2 : Real.log (m : ℝ) ≤ 2 * Real.log V := by
              have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V) :=
                Real.log_le_log (by linarith only [hV512, hm_ge_V]) hm_le_2V
              rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
              linarith only [h1, log_two_lt_one, hlog32]
            linarith only [hfl, hlog2]
          · simp only [qLogSp, if_neg hact, mul_zero, Nat.cast_zero]; positivity
        · simp only [Nat.cast_zero]; positivity
      have hrV_ge : Real.log V ≤ (2 : ℝ) ^ r_V :=
        (logTwoShift_dyadic_bounds (by linarith only [hV512] : 16 ≤ V)
          (Nat.le_ceil V) ((Nat.ceil_lt_add_one hV_pos.le).le.trans (by linarith only [hV512]))).1
      set q₀ : ℕ := Nat.floor (2 * V) / 2 ^ v₀
      have hc : Dvd_V.card ≤ q₀ + 1 :=
        card_Icc_filter_dvd_le (Nat.ceil V) (Nat.floor (2 * V)) (2 ^ v₀)
      have hdiv_le : (q₀ : ℝ) ≤ 2 * V / (2 : ℝ) ^ v₀ := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : q₀ * 2 ^ v₀ ≤ Nat.floor (2 * V) := Nat.div_mul_le_self _ _
        have h2 : ((q₀ * 2 ^ v₀ : ℕ) : ℝ) ≤ (Nat.floor (2 * V) : ℝ) := Nat.cast_le.mpr h1
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h2
        exact h2.trans (Nat.floor_le (by positivity))
      have hcR : (Dvd_V.card : ℝ) ≤ 2 * V / (2 : ℝ) ^ v₀ + 1 := by
        have hc1 : (Dvd_V.card : ℝ) ≤ (q₀ : ℝ) + 1 := by exact_mod_cast hc
        exact hc1.trans (add_le_add_left hdiv_le 1)
      have hpow_exp : ((2 : ℝ) ^ k_A)⁻¹ ≤ Real.exp (-A) := by
        have hk_ge : 2 * A ≤ (k_A : ℝ) := by
          dsimp only [k_A]; rw [Nat.cast_max]; exact (Nat.le_ceil _).trans (le_max_right _ _)
        have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hmul : A ≤ (k_A : ℝ) * Real.log 2 := by
          calc A = (2 * A) * (1 / 2) := by ring
            _ ≤ (k_A : ℝ) * Real.log 2 := mul_le_mul hk_ge hlog2 (by norm_num) (Nat.cast_nonneg _)
        rw [← Real.exp_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ k_A)⁻¹), Real.log_inv, Real.log_pow]
        exact Real.exp_le_exp.mpr (by linarith only [hmul])
      have hterm1 : (2 * V / (2 : ℝ) ^ v₀) * (Real.log V / 13) ≤ Real.exp (-A) * V := by
        have hv_split : (2 : ℝ) ^ v₀ = (2 : ℝ) ^ r_V * (2 : ℝ) ^ k_A := by
          dsimp only [v₀]; rw [pow_add]
        rw [hv_split]
        have hlog_div : Real.log V / (2 : ℝ) ^ r_V ≤ 1 := (div_le_one (by positivity)).mpr hrV_ge
        calc (2 * V / ((2 : ℝ) ^ r_V * (2 : ℝ) ^ k_A)) * (Real.log V / 13)
            = (2 / 13) * V * ((2 : ℝ) ^ k_A)⁻¹ * (Real.log V / (2 : ℝ) ^ r_V) := by ring
          _ ≤ (2 / 13) * V * ((2 : ℝ) ^ k_A)⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left hlog_div (by positivity)
          _ ≤ (2 / 13) * V * Real.exp (-A) * 1 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow_exp (by positivity)) zero_le_one
          _ ≤ Real.exp (-A) * V := by
              have hpv : 0 ≤ Real.exp (-A) * V := by positivity
              linarith only [hpv]
      have hterm2 : Real.log V / 13 ≤ (1 / max A 1) * V := by
        have hrt : Real.log V ≤ 2 * Real.sqrt V := log_le_two_sqrt_of_pos' hV_pos
        have hrt_gt : 4 * max A 1 < Real.sqrt V := by
          rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * max A 1)]
          exact Real.sqrt_lt_sqrt (by positivity) (by linarith only [hVA_sq])
        have hrt_pos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV_pos
        have hm_pos : 0 < max A 1 := lt_max_of_lt_right zero_lt_one
        rw [one_div_mul_eq_div, le_div_iff₀ hm_pos]
        have hmul := mul_lt_mul_of_pos_right hrt_gt hrt_pos
        rw [Real.mul_self_sqrt hV_pos.le] at hmul
        calc Real.log V / 13 * max A 1
            ≤ (2 * Real.sqrt V) / 13 * max A 1 :=
              mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hrt (by norm_num)) hm_pos.le
          _ ≤ (4 * max A 1) * Real.sqrt V := by
              have hp : 0 ≤ max A 1 * Real.sqrt V := by positivity
              linarith only [hp]
          _ ≤ V := hmul.le
      calc ∑ m ∈ Dvd_V, ∑ z ∈ (logSpacingModel.Z m).filter
              (fun z => A / Real.log V ≤ |z.re - 1 / 2|), (logSpacingModel.mult z : ℝ)
          ≤ ∑ _m ∈ Dvd_V, Real.log V / 13 := Finset.sum_le_sum hq_ub
        _ = (Dvd_V.card : ℝ) * (Real.log V / 13) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * V / (2 : ℝ) ^ v₀ + 1) * (Real.log V / 13) :=
            mul_le_mul_of_nonneg_right hcR (by positivity)
        _ = (2 * V / (2 : ℝ) ^ v₀) * (Real.log V / 13) + Real.log V / 13 := by ring
        _ ≤ Real.exp (-A) * V + (1 / max A 1) * V := add_le_add hterm1 hterm2
        _ = (Real.exp (-A) + 1 / max A 1) * V := by ring

private lemma logSpacingModel_horizontalMomentLittleO : logSpacingModel.HorizontalMomentLittleO := by
  refine Metric.tendsto_atTop.mpr fun η hη => ?_
  obtain ⟨K, hK_pow⟩ := exists_pow_lt_of_lt_one (div_pos hη (by norm_num : (0 : ℝ) < 4))
    (by norm_num : (1 / 2 : ℝ) < 1)
  set C_K : ℝ := ((K + 1 : ℕ) : ℝ)
  have hCK_pos : 0 < C_K := by positivity
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (max 32 (4 * C_K / η + 1)))
  refine ⟨max 512 (max V₀ (max (4 * C_K / η + 1) ((16 / η) ^ 2 + 1))), fun V hV => ?_⟩
  have hV512 : 512 ≤ V := (le_max_left _ _).trans hV
  have hV_V₀ : V₀ ≤ V := ((le_max_left _ _).trans (le_max_right _ _)).trans hV
  have hV_CK : 4 * C_K / η + 1 ≤ V :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hV
  have hV_ηsq : (16 / η) ^ 2 + 1 ≤ V :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hV
  have hV_pos : 0 < V := by linarith only [hV512]
  have hlog_ge := hV₀ V hV_V₀
  have hlog32 : 32 ≤ Real.log V := (le_max_left _ _).trans hlog_ge
  have hlog_CK : 4 * C_K / η + 1 ≤ Real.log V := (le_max_right _ _).trans hlog_ge
  have hlogV_pos : 0 < Real.log V := by linarith only [hlog32]
  set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
  set f : ℕ → ℝ := fun m =>
    ∑ z ∈ (logSpacingModel.Z m).filter (fun z => 1 / 2 < z.re),
      (logSpacingModel.mult z : ℝ) * (z.re - 1 / 2)
  have hf_nn : ∀ m, 0 ≤ f m := fun m =>
    Finset.sum_nonneg fun z hz => mul_nonneg (Nat.cast_nonneg _)
      (sub_nonneg.mpr (Finset.mem_filter.mp hz).2.le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hV_pos.le)
    (Finset.sum_nonneg fun m _ => hf_nn m))]
  set r_V : ℕ := natBitLen (Nat.floor (Real.log V) + 1)
  have hrV_ge : Real.log V ≤ (2 : ℝ) ^ r_V :=
    (logTwoShift_dyadic_bounds (by linarith only [hV512] : 16 ≤ V)
      (Nat.le_ceil V) ((Nat.ceil_lt_add_one hV_pos.le).le.trans (by linarith only [hV512]))).1
  set D₁ := I_V.filter (fun m => 2 ^ (r_V + 1) ∣ m)
  set D₂ := I_V.filter (fun m => 2 ^ (r_V + K + 1) ∣ m)
  have hf_le : ∀ m ∈ I_V, f m ≤
      (if m ∈ D₁ then C_K else 0) + (if m ∈ D₂ then Real.log V else 0) := by
    intro m hm_I
    obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
    have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
    have hm_le_2V : (m : ℝ) ≤ 2 * V :=
      ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
    have hm_ne0 : m ≠ 0 := by intro h0; subst h0; simp at hm_ge_V; linarith only [hV512, hm_ge_V]
    obtain ⟨_, _, hr_lo, _⟩ := logTwoShift_dyadic_bounds (by linarith only [hV512]) hm_ge_V hm_le_2V
    have hlog_ge_m : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
    have hlog_le_2 : Real.log (m : ℝ) ≤ 2 * Real.log V := by
      have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V) :=
        Real.log_le_log (by linarith only [hV512, hm_ge_V]) hm_le_2V
      rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
      linarith only [h1, log_two_lt_one, hlog32]
    have hf_eq : f m = (qLogSp m : ℝ) * dLogSp m := by
      dsimp only [f, logSpacingModel]; simp only [Nat.cast_one]
      exact packetWin_right_moment_sum (qLogSp_dLogSp_or m)
    rw [hf_eq]
    by_cases hact : activeLogSp m
    · have hd_nn : 0 ≤ dLogSp m := by
        simp only [dLogSp, if_pos hact]
        exact div_nonneg (Nat.cast_nonneg _)
          (mul_nonneg zero_le_two (Real.log_nonneg (by linarith only [hV512, hm_ge_V])))
      have hq_le : (qLogSp m : ℝ) ≤ Real.log V / 26 := by
        simp only [qLogSp, if_pos hact]
        have hfl : (Nat.floor (Real.log (m : ℝ) / 52) : ℝ) ≤ Real.log (m : ℝ) / 52 :=
          Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith only [hV512, hm_ge_V])) (by norm_num))
        linarith only [hfl, hlog_le_2]
      have hm_D₁ : m ∈ D₁ := Finset.mem_filter.mpr
        ⟨hm_I, two_pow_dvd_of_le_evenHalves hm_ne0 (by have := hact.2.1; omega)⟩
      by_cases hK_le : evenHalves m - logTwoShift m ≤ K
      · have hd_le : dLogSp m ≤ C_K / (2 * Real.log V) := by
          simp only [dLogSp, if_pos hact]
          calc ((evenHalves m - logTwoShift m : ℕ) : ℝ) / (2 * Real.log (m : ℝ))
              ≤ C_K / (2 * Real.log (m : ℝ)) := by
                refine div_le_div_of_nonneg_right ?_ (by linarith only [hlog32, hlog_ge_m])
                dsimp only [C_K]; exact_mod_cast (hK_le.trans (Nat.le_succ K))
            _ ≤ C_K / (2 * Real.log V) :=
                div_le_div_of_nonneg_left hCK_pos.le (by positivity) (by linarith only [hlog_ge_m])
        have hprod : (qLogSp m : ℝ) * dLogSp m ≤ C_K := by
          calc (qLogSp m : ℝ) * dLogSp m
              ≤ (Real.log V / 26) * (C_K / (2 * Real.log V)) :=
                mul_le_mul hq_le hd_le hd_nn (by positivity)
            _ = C_K / 52 := by field_simp [hlogV_pos.ne']; ring
            _ ≤ C_K := by linarith only [hCK_pos]
        have hnn2 : 0 ≤ (if m ∈ D₂ then Real.log V else 0) := by
          split_ifs <;> linarith only [hlogV_pos]
        rw [if_pos hm_D₁]; linarith only [hprod, hnn2]
      · have hm_D₂ : m ∈ D₂ := Finset.mem_filter.mpr
          ⟨hm_I, two_pow_dvd_of_le_evenHalves hm_ne0 (by omega)⟩
        have hd_le := dLogSp_le_one_sixteenth m
        have hprod : (qLogSp m : ℝ) * dLogSp m ≤ Real.log V := by
          calc (qLogSp m : ℝ) * dLogSp m
              ≤ (Real.log V / 26) * (1 / 16) :=
                mul_le_mul hq_le hd_le hd_nn (by positivity)
            _ ≤ Real.log V := by linarith only [hlogV_pos]
        rw [if_pos hm_D₁, if_pos hm_D₂]; linarith only [hprod, hCK_pos]
    · simp only [qLogSp, if_neg hact, Nat.cast_zero, zero_mul]
      positivity
  set q₁ : ℕ := Nat.floor (2 * V) / 2 ^ (r_V + 1)
  have hD₁_card : (D₁.card : ℝ) ≤ V / Real.log V + 1 := by
    have hc : D₁.card ≤ q₁ + 1 :=
      card_Icc_filter_dvd_le (Nat.ceil V) (Nat.floor (2 * V)) (2 ^ (r_V + 1))
    have hdiv : (q₁ : ℝ) ≤ V / Real.log V := by
      rw [le_div_iff₀ hlogV_pos]
      have h1 : q₁ * 2 ^ (r_V + 1) ≤ Nat.floor (2 * V) := Nat.div_mul_le_self _ _
      have hcast : ((q₁ * 2 ^ (r_V + 1) : ℕ) : ℝ) = (q₁ : ℝ) * ((2 : ℝ) ^ r_V * 2) := by
        rw [Nat.cast_mul, Nat.cast_pow, pow_succ, Nat.cast_ofNat]
      have h2 : (q₁ : ℝ) * ((2 : ℝ) ^ r_V * 2) ≤ 2 * V :=
        hcast ▸ ((Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity)))
      have h3 : (q₁ : ℝ) * (Real.log V * 2) ≤ (q₁ : ℝ) * ((2 : ℝ) ^ r_V * 2) :=
        mul_le_mul_of_nonneg_left (by linarith only [hrV_ge]) (Nat.cast_nonneg q₁)
      linarith only [h2, h3]
    have hc1 : (D₁.card : ℝ) ≤ (q₁ : ℝ) + 1 := by exact_mod_cast hc
    exact hc1.trans (add_le_add_left hdiv 1)
  set q₂ : ℕ := Nat.floor (2 * V) / 2 ^ (r_V + K + 1)
  have hD₂_card : (D₂.card : ℝ) ≤ (1 / 2 : ℝ) ^ K * (V / Real.log V) + 1 := by
    have hc : D₂.card ≤ q₂ + 1 :=
      card_Icc_filter_dvd_le (Nat.ceil V) (Nat.floor (2 * V)) (2 ^ (r_V + K + 1))
    have hdiv : (q₂ : ℝ) ≤ (1 / 2 : ℝ) ^ K * (V / Real.log V) := by
      have hden_pos : (0 : ℝ) < (2 : ℝ) ^ K * Real.log V := by positivity
      rw [one_div_pow, show 1 / (2 : ℝ) ^ K * (V / Real.log V) =
        V / ((2 : ℝ) ^ K * Real.log V) by ring, le_div_iff₀ hden_pos]
      have h1 : q₂ * 2 ^ (r_V + K + 1) ≤ Nat.floor (2 * V) := Nat.div_mul_le_self _ _
      have hcast : ((q₂ * 2 ^ (r_V + K + 1) : ℕ) : ℝ) =
          (q₂ : ℝ) * ((2 : ℝ) ^ r_V * (2 : ℝ) ^ K * 2) := by
        rw [Nat.cast_mul, Nat.cast_pow, pow_add, pow_add, pow_one, Nat.cast_ofNat]
      have h2 : (q₂ : ℝ) * ((2 : ℝ) ^ r_V * (2 : ℝ) ^ K * 2) ≤ 2 * V :=
        hcast ▸ ((Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity)))
      have hle_p : 2 * ((2 : ℝ) ^ K * Real.log V) ≤ (2 : ℝ) ^ r_V * (2 : ℝ) ^ K * 2 := by
        have hm := mul_le_mul_of_nonneg_right hrV_ge (by positivity : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ K)
        linarith only [hm]
      have h3 := mul_le_mul_of_nonneg_left hle_p (Nat.cast_nonneg q₂)
      linarith only [h2, h3]
    have hc1 : (D₂.card : ℝ) ≤ (q₂ : ℝ) + 1 := by exact_mod_cast hc
    exact hc1.trans (add_le_add_left hdiv 1)
  have hsum_le : ∑ m ∈ I_V, f m ≤ C_K * (V / Real.log V + 1) +
      ((1 / 2 : ℝ) ^ K * V + Real.log V) := by
    have hs := Finset.sum_le_sum hf_le
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
      Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul] at hs
    have h1 : (D₁.card : ℝ) * C_K ≤ C_K * (V / Real.log V + 1) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hD₁_card hCK_pos.le
    have h2 : (D₂.card : ℝ) * Real.log V ≤ (1 / 2 : ℝ) ^ K * V + Real.log V := by
      have hm := mul_le_mul_of_nonneg_right hD₂_card hlogV_pos.le
      have hr : ((1 / 2 : ℝ) ^ K * (V / Real.log V) + 1) * Real.log V =
          (1 / 2 : ℝ) ^ K * V + Real.log V := by field_simp [hlogV_pos.ne']
      rwa [hr] at hm
    exact hs.trans (add_le_add h1 h2)
  have hb1 : C_K / Real.log V < η / 4 := by
    rw [div_lt_iff₀ hlogV_pos]
    have h1 : 4 * C_K / η < Real.log V := lt_of_lt_of_le (lt_add_one _) hlog_CK
    have h2 := (div_lt_iff₀ hη).mp h1
    linarith only [h2]
  have hb2 : C_K / V < η / 4 := by
    rw [div_lt_iff₀ hV_pos]
    have h1 : 4 * C_K / η < V := lt_of_lt_of_le (lt_add_one _) hV_CK
    have h2 := (div_lt_iff₀ hη).mp h1
    linarith only [h2]
  have hb3 : Real.log V / V < η / 4 := by
    rw [div_lt_iff₀ hV_pos]
    have hrt := log_le_two_sqrt_of_pos' hV_pos
    have hrt_gt : 16 / η < Real.sqrt V := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 16 / η)]
      exact Real.sqrt_lt_sqrt (by positivity) (lt_of_lt_of_le (lt_add_one _) hV_ηsq)
    have hrt_pos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV_pos
    have hm := mul_lt_mul_of_pos_right hrt_gt hrt_pos
    rw [Real.mul_self_sqrt hV_pos.le] at hm
    have hm2 := mul_lt_mul_of_pos_left hm hη
    rw [← mul_assoc, mul_div_cancel₀ 16 hη.ne'] at hm2
    linarith only [hrt, hm2, hrt_pos]
  calc V⁻¹ * ∑ m ∈ I_V, f m
      ≤ V⁻¹ * (C_K * (V / Real.log V + 1) + ((1 / 2 : ℝ) ^ K * V + Real.log V)) :=
        mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hV_pos.le)
    _ = C_K / Real.log V + C_K / V + (1 / 2 : ℝ) ^ K + Real.log V / V := by
        field_simp [hV_pos.ne', hlogV_pos.ne']; ring
    _ < η / 4 + η / 4 + η / 4 + η / 4 :=
        add_lt_add (add_lt_add (add_lt_add hb1 hb2) hK_pow) hb3
    _ = η := by ring

private lemma logSpacingModel_criticalClustering : logSpacingModel.CriticalClustering := by
  intro κ hκ
  refine Metric.tendsto_atTop.mpr fun η hη => ?_
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (max 16 (4 / η + 1)))
  refine ⟨max 512 (max V₀ ((16 / η) ^ 2 + 1)), fun V hV => ?_⟩
  have hV512 : 512 ≤ V := (le_max_left _ _).trans hV
  have hV_V₀ : V₀ ≤ V := ((le_max_left _ _).trans (le_max_right _ _)).trans hV
  have hV_ηsq : (16 / η) ^ 2 + 1 ≤ V :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hV
  have hV_pos : 0 < V := by linarith only [hV512]
  have hlog_ge := hV₀ V hV_V₀
  have hlog16 : 16 ≤ Real.log V := (le_max_left _ _).trans hlog_ge
  have hlog_η : 4 / η + 1 ≤ Real.log V := (le_max_right _ _).trans hlog_ge
  have hlogV_pos : 0 < Real.log V := by linarith only [hlog16]
  set g : ℕ → ℝ := fun m =>
    ∑ z ∈ (logSpacingModel.Z m).filter (fun z => κ / Real.log V ≤ |z.re - 1 / 2|),
      (logSpacingModel.mult z : ℝ)
  have hg_nn : ∀ m, 0 ≤ g m := fun _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Finset.sum_nonneg fun m _ => hg_nn m)
    (by positivity)), div_lt_iff₀ (mul_pos hV_pos hlogV_pos)]
  have hg_ub : ∀ m ∈ Finset.range (Nat.floor V + 1), g m ≤ Real.log V := by
    intro m hm_r
    have hm_le_V : (m : ℝ) ≤ V :=
      ((Nat.cast_le (α := ℝ)).mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm_r))).trans
        (Nat.floor_le hV_pos.le)
    dsimp only [g, logSpacingModel]; simp only [Nat.cast_one]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      packetWin_filter_abs_card (div_pos hκ hlogV_pos) (qLogSp_dLogSp_or m)]
    split_ifs
    · by_cases hact : activeLogSp m
      · simp only [qLogSp, if_pos hact]; push_cast
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by have := hact.1; omega)
        have hfl : (Nat.floor (Real.log (m : ℝ) / 52) : ℝ) ≤ Real.log (m : ℝ) / 52 :=
          Nat.floor_le (div_nonneg (Real.log_nonneg hm1) (by norm_num))
        have hlm : Real.log (m : ℝ) ≤ Real.log V := Real.log_le_log (by linarith only [hm1]) hm_le_V
        linarith only [hfl, hlm, hlog16]
      · simp only [qLogSp, if_neg hact, mul_zero, Nat.cast_zero]; linarith only [hlogV_pos]
    · simp only [Nat.cast_zero]; linarith only [hlogV_pos]
  set U : ℕ := Nat.ceil (Real.sqrt V)
  set k_U : ℕ := Nat.floor ((1 / 2) * Real.log V) + 1
  set r_U : ℕ := natBitLen k_U
  have h2rU : Real.log V ≤ (2 : ℝ) ^ (r_U + 1) := by
    obtain ⟨hk_lt, _⟩ := natBitLen_bounds k_U (by omega)
    have h1 : (1 / 2) * Real.log V < (k_U : ℝ) := by
      dsimp only [k_U]; push_cast; exact Nat.lt_floor_add_one _
    have h2 : (k_U : ℝ) ≤ (2 : ℝ) ^ r_U := by exact_mod_cast hk_lt.le
    rw [pow_succ]; linarith only [h1, h2]
  set High_Dvd := (Finset.Icc U (Nat.floor V)).filter (fun m => 2 ^ (r_U + 1) ∣ m)
  have hcov : (Finset.range (Nat.floor V + 1)).filter (fun m => g m ≠ 0) ⊆
      Finset.range U ∪ High_Dvd := by
    intro m hm_f
    obtain ⟨hm_r, hg_ne⟩ := Finset.mem_filter.mp hm_f
    have hm_le_fl : m ≤ Nat.floor V := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm_r)
    by_cases hm_lt : m < U
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hm_lt))
    · refine Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨not_lt.mp hm_lt, hm_le_fl⟩, ?_⟩))
      have hact : activeLogSp m := by
        by_contra hnot
        apply hg_ne
        dsimp only [g, logSpacingModel]; simp only [Nat.cast_one]
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
          packetWin_filter_abs_card (div_pos hκ hlogV_pos) (qLogSp_dLogSp_or m)]
        split_ifs <;> simp [qLogSp, hnot]
      have hm_ge_rt : Real.sqrt V ≤ (m : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast not_lt.mp hm_lt)
      have hlog_m_ge : (1 / 2) * Real.log V ≤ Real.log (m : ℝ) := by
        have h1 := Real.log_le_log (Real.sqrt_pos.mpr hV_pos) hm_ge_rt
        rw [Real.log_sqrt hV_pos.le] at h1
        linarith only [h1]
      have hk_le : k_U ≤ Nat.floor (Real.log (m : ℝ)) + 1 :=
        Nat.add_le_add_right (Nat.floor_mono hlog_m_ge) 1
      have hr_le : r_U ≤ logTwoShift m := natBitLen_mono _ _ hk_le
      have hm_ne0 : m ≠ 0 := by have := hact.1; omega
      exact two_pow_dvd_of_le_evenHalves hm_ne0 (by have := hact.2.1; omega)
  have hsum_cov : ∑ m ∈ Finset.range (Nat.floor V + 1), g m ≤
      ((U : ℝ) + (High_Dvd.card : ℝ)) * Real.log V := by
    have hs0 : ∑ m ∈ Finset.range (Nat.floor V + 1), g m =
        ∑ m ∈ (Finset.range (Nat.floor V + 1)).filter (fun m => g m ≠ 0), g m :=
      (Finset.sum_subset (Finset.filter_subset _ _) fun m hm hnot => by
        simp only [Finset.mem_filter, hm, true_and, not_not] at hnot; exact hnot).symm
    rw [hs0]
    have hs1 : ∑ m ∈ (Finset.range (Nat.floor V + 1)).filter (fun m => g m ≠ 0), g m ≤
        ∑ _m ∈ (Finset.range (Nat.floor V + 1)).filter (fun m => g m ≠ 0), Real.log V :=
      Finset.sum_le_sum fun m hm => hg_ub m (Finset.mem_filter.mp hm).1
    rw [Finset.sum_const, nsmul_eq_mul] at hs1
    have hc_le : ((Finset.range (Nat.floor V + 1)).filter (fun m => g m ≠ 0)).card ≤
        U + High_Dvd.card := by
      calc _ ≤ (Finset.range U ∪ High_Dvd).card := Finset.card_le_card hcov
        _ ≤ (Finset.range U).card + High_Dvd.card := Finset.card_union_le _ _
        _ = U + High_Dvd.card := by rw [Finset.card_range]
    exact hs1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc_le) hlogV_pos.le)
  set q_H : ℕ := Nat.floor V / 2 ^ (r_U + 1)
  have hHigh_card : (High_Dvd.card : ℝ) ≤ V / Real.log V + 1 := by
    have hc : High_Dvd.card ≤ q_H + 1 := card_Icc_filter_dvd_le U (Nat.floor V) (2 ^ (r_U + 1))
    have hdiv : (q_H : ℝ) ≤ V / Real.log V := by
      rw [le_div_iff₀ hlogV_pos]
      have h1 : q_H * 2 ^ (r_U + 1) ≤ Nat.floor V := Nat.div_mul_le_self _ _
      have hcast : ((q_H * 2 ^ (r_U + 1) : ℕ) : ℝ) = (q_H : ℝ) * (2 : ℝ) ^ (r_U + 1) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      have h2 : (q_H : ℝ) * (2 : ℝ) ^ (r_U + 1) ≤ V :=
        hcast ▸ ((Nat.cast_le.mpr h1).trans (Nat.floor_le hV_pos.le))
      have h3 := mul_le_mul_of_nonneg_left h2rU (Nat.cast_nonneg q_H)
      linarith only [h2, h3]
    have hc1 : (High_Dvd.card : ℝ) ≤ (q_H : ℝ) + 1 := by exact_mod_cast hc
    exact hc1.trans (add_le_add_left hdiv 1)
  have hU_le : (U : ℝ) ≤ Real.sqrt V + 1 := (Nat.ceil_lt_add_one (Real.sqrt_nonneg V)).le
  have htot_ub : ((U : ℝ) + (High_Dvd.card : ℝ)) * Real.log V ≤
      (Real.sqrt V + 2) * Real.log V + V := by
    have h1 : (U : ℝ) + (High_Dvd.card : ℝ) ≤ Real.sqrt V + 2 + V / Real.log V :=
      (add_le_add hU_le hHigh_card).trans_eq (by ring)
    calc ((U : ℝ) + (High_Dvd.card : ℝ)) * Real.log V
        ≤ (Real.sqrt V + 2 + V / Real.log V) * Real.log V :=
          mul_le_mul_of_nonneg_right h1 hlogV_pos.le
      _ = (Real.sqrt V + 2) * Real.log V + V := by field_simp [hlogV_pos.ne']
  have hrt_lt : Real.sqrt V + 2 < (η / 2) * V := by
    have hrt1 : 1 ≤ Real.sqrt V := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith only [hV512])
    have hrt_gt : 16 / η < Real.sqrt V := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 16 / η)]
      exact Real.sqrt_lt_sqrt (by positivity) (lt_of_lt_of_le (lt_add_one _) hV_ηsq)
    have hrt_pos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV_pos
    have hm := mul_lt_mul_of_pos_right hrt_gt hrt_pos
    rw [Real.mul_self_sqrt hV_pos.le] at hm
    have hm2 := mul_lt_mul_of_pos_left hm hη
    rw [← mul_assoc, mul_div_cancel₀ 16 hη.ne'] at hm2
    linarith only [hrt1, hm2]
  have hV_lt : V < (η / 2) * (V * Real.log V) := by
    have h1 : 4 / η < Real.log V := lt_of_lt_of_le (lt_add_one _) hlog_η
    have h2 := (div_lt_iff₀ hη).mp h1
    nlinarith only [hV_pos, h2]
  have hprod_rt : (Real.sqrt V + 2) * Real.log V < (η / 2) * (V * Real.log V) := by
    calc (Real.sqrt V + 2) * Real.log V
        < ((η / 2) * V) * Real.log V := mul_lt_mul_of_pos_right hrt_lt hlogV_pos
      _ = (η / 2) * (V * Real.log V) := by ring
  linarith only [hsum_cov, htot_ub, hprod_rt, hV_lt]

private lemma logSpacingModel_sqMoment_lower_bound (A : ℝ) (hA : 0 < A) :
    ∀ᶠ V : ℝ in atTop,
      (1 / (21632 * (2 : ℝ) ^ (Nat.ceil (4 * A) + 4))) * V * Real.log V ≤
        ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          (∑ z ∈ (logSpacingModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
            (logSpacingModel.mult z : ℝ)) ^ 2 := by
  set c_A : ℕ := Nat.ceil (4 * A)
  have hcA_pos : 1 ≤ c_A := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  filter_upwards [eventually_ge_atTop (max 512 ((64 * (2 : ℝ) ^ (c_A + 4)) ^ 2 + 1)),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 104 (8 * ((c_A + 1 : ℕ) : ℝ)))]
    with V hV_ge hlog_ge
  have hV512 : 512 ≤ V := (le_max_left _ _).trans hV_ge
  have hV_pow : (64 * (2 : ℝ) ^ (c_A + 4)) ^ 2 + 1 ≤ V := (le_max_right _ _).trans hV_ge
  have hV_pos : 0 < V := by linarith only [hV512]
  have hlog104 : 104 ≤ Real.log V := (le_max_left _ _).trans hlog_ge
  have hlog_cA : 8 * ((c_A + 1 : ℕ) : ℝ) ≤ Real.log V := (le_max_right _ _).trans hlog_ge
  have hlogV_pos : 0 < Real.log V := by linarith only [hlog104]
  set r_V : ℕ := natBitLen (Nat.floor (Real.log V) + 1)
  have hrV_le : (2 : ℝ) ^ r_V ≤ 4 * Real.log V :=
    (logTwoShift_dyadic_bounds (by linarith only [hV512] : 16 ≤ V)
      (Nat.le_ceil V) ((Nat.ceil_lt_add_one hV_pos.le).le.trans (by linarith only [hV512]))).2.1
  set v_star : ℕ := r_V + 1 + c_A
  have hv_V : (2 : ℝ) ^ (v_star + 3) ≤ V := by
    have hp : (2 : ℝ) ^ (v_star + 3) = (2 : ℝ) ^ r_V * (2 : ℝ) ^ (c_A + 4) := by
      rw [show v_star + 3 = r_V + (c_A + 4) by dsimp only [v_star]; omega, pow_add]
    have hrt := log_le_two_sqrt_of_pos' hV_pos
    have hrt_gt : 64 * (2 : ℝ) ^ (c_A + 4) < Real.sqrt V := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 64 * (2 : ℝ) ^ (c_A + 4))]
      exact Real.sqrt_lt_sqrt (by positivity) (lt_of_lt_of_le (lt_add_one _) hV_pow)
    have hrt_pos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV_pos
    have hm := mul_lt_mul_of_pos_right hrt_gt hrt_pos
    rw [Real.mul_self_sqrt hV_pos.le] at hm
    rw [hp]
    calc (2 : ℝ) ^ r_V * (2 : ℝ) ^ (c_A + 4)
        ≤ (4 * Real.log V) * (2 : ℝ) ^ (c_A + 4) :=
          mul_le_mul_of_nonneg_right hrV_le (by positivity)
      _ ≤ (8 * Real.sqrt V) * (2 : ℝ) ^ (c_A + 4) :=
          mul_le_mul_of_nonneg_right (by linarith only [hrt]) (by positivity)
      _ ≤ (64 * (2 : ℝ) ^ (c_A + 4)) * Real.sqrt V := by
          have hp2 : (0 : ℝ) < (2 : ℝ) ^ (c_A + 4) * Real.sqrt V := by positivity
          linarith only [hp2]
      _ ≤ V := hm.le
  obtain ⟨S, hS_sub, hS_ev, hS_card⟩ := exists_evenHalves_subset_Icc v_star hv_V
  have hterm : ∀ m ∈ S, (Real.log V / 52) ^ 2 ≤
      (∑ z ∈ (logSpacingModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
        (logSpacingModel.mult z : ℝ)) ^ 2 := by
    intro m hmS
    have hm_I := hS_sub hmS
    obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
    have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
    have hm_le_2V : (m : ℝ) ≤ 2 * V :=
      ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
    have hm256 : 256 ≤ m := by
      by_contra hlt; have hm_lt : (m : ℝ) < 256 := by exact_mod_cast (not_le.mp hlt)
      linarith only [hV512, hm_ge_V, hm_lt]
    obtain ⟨_, _, hr_lo, hr_hi⟩ :=
      logTwoShift_dyadic_bounds (by linarith only [hV512]) hm_ge_V hm_le_2V
    have hev : evenHalves m = r_V + 1 + c_A := hS_ev m hmS
    have hlog_ge_m : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
    obtain ⟨hge_s, hdiff_ub, hdiff_lb⟩ := shift_diff_bounds hr_lo hr_hi hcA_pos
    have hsub_ub : ((evenHalves m - logTwoShift m : ℕ) : ℝ) ≤ ((c_A + 1 : ℕ) : ℝ) := by
      rw [hev]; exact Nat.cast_le.mpr hdiff_ub
    have hsub_lb : (c_A : ℝ) ≤ ((evenHalves m - logTwoShift m : ℕ) : ℝ) := by
      rw [hev]; exact Nat.cast_le.mpr hdiff_lb
    have hact : activeLogSp m :=
      ⟨hm256, hev ▸ hge_s, by linarith only [hsub_ub, hlog_cA, hlog_ge_m]⟩
    have hcnt : Real.log V / 52 ≤
        ∑ z ∈ (logSpacingModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
          (logSpacingModel.mult z : ℝ) := by
      dsimp only [logSpacingModel]; simp only [Nat.cast_one]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        packetWin_filter_abs_card (div_pos hA hlogV_pos) (qLogSp_dLogSp_or m), if_pos]
      · simp only [qLogSp, if_pos hact]; push_cast
        have hlt := Nat.lt_floor_add_one (Real.log (m : ℝ) / 52)
        linarith only [hlt, hlog_ge_m, hlog104]
      · simp only [dLogSp, if_pos hact]
        have hlog2 : Real.log (m : ℝ) ≤ 2 * Real.log V := by
          have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V) :=
            Real.log_le_log (by linarith only [hV512, hm_ge_V]) hm_le_2V
          rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
          linarith only [h1, log_two_lt_one, hlog104]
        have hc4A : 4 * A ≤ (c_A : ℝ) := Nat.le_ceil (4 * A)
        calc A / Real.log V = (4 * A) / (4 * Real.log V) := by ring
          _ ≤ ((evenHalves m - logTwoShift m : ℕ) : ℝ) / (4 * Real.log V) :=
              div_le_div_of_nonneg_right (hc4A.trans hsub_lb) (by positivity)
          _ ≤ ((evenHalves m - logTwoShift m : ℕ) : ℝ) / (2 * Real.log (m : ℝ)) :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _)
                (by linarith only [hlog104, hlog_ge_m]) (by linarith only [hlog2])
    exact pow_le_pow_left₀ (by positivity) hcnt 2
  have hpow_ub : (2 : ℝ) ^ (v_star + 2) ≤ 8 * (2 : ℝ) ^ (c_A + 4) * Real.log V := by
    have hp : (2 : ℝ) ^ (v_star + 2) = (2 : ℝ) ^ r_V * (2 : ℝ) ^ (c_A + 3) := by
      rw [show v_star + 2 = r_V + (c_A + 3) by dsimp only [v_star]; omega, pow_add]
    have hp2 : (2 : ℝ) ^ (c_A + 4) = 2 * (2 : ℝ) ^ (c_A + 3) := by rw [pow_succ']
    rw [hp, hp2]
    have hm := mul_le_mul_of_nonneg_right hrV_le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (c_A + 3))
    have hp3 : 0 ≤ (2 : ℝ) ^ (c_A + 3) * Real.log V := by positivity
    linarith only [hm, hp3]
  have hcard_lb : V / (8 * (2 : ℝ) ^ (c_A + 4) * Real.log V) ≤ (S.card : ℝ) :=
    (div_le_div_of_nonneg_left hV_pos.le (by positivity) hpow_ub).trans hS_card
  calc (1 / (21632 * (2 : ℝ) ^ (c_A + 4))) * V * Real.log V
      = (V / (8 * (2 : ℝ) ^ (c_A + 4) * Real.log V)) * (Real.log V / 52) ^ 2 := by
          field_simp [hlogV_pos.ne', (by positivity : (0 : ℝ) < (2 : ℝ) ^ (c_A + 4)).ne']; ring
    _ ≤ (S.card : ℝ) * (Real.log V / 52) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard_lb (sq_nonneg _)
    _ = ∑ _m ∈ S, (Real.log V / 52) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ S, (∑ z ∈ (logSpacingModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
          (logSpacingModel.mult z : ℝ)) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun _ _ _ => sq_nonneg _

/-- **Super-Linear Second Moment Under `(D_zero)` (`exists_logSpacingModel_zeroDensity_not_linearSqMoment`).**
There exists a `UnitWindowStripZeroModel` satisfying `LogFreeZeroDensity`, `WindowOccupancy`,
`HorizontalMomentLittleO`, and `CriticalClustering` whose per-window deep-zero second moment grows
at least as `c_A * V * log V` for every `A > 0` (proving `∑_m N_m^2 = O_A(V)` is strictly stronger
than `(D_zero)`). -/
theorem exists_logSpacingModel_zeroDensity_not_linearSqMoment :
    ∃ M : UnitWindowStripZeroModel,
      M.LogFreeZeroDensity ∧
      M.WindowOccupancy ∧
      M.HorizontalMomentLittleO ∧
      M.CriticalClustering ∧
      ∀ A : ℝ, 0 < A → ∀ᶠ V : ℝ in atTop,
        (1 / (21632 * (2 : ℝ) ^ (Nat.ceil (4 * A) + 4))) * V * Real.log V ≤
          ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
            (∑ z ∈ (M.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
              (M.mult z : ℝ)) ^ 2 := by
  have hzd := logSpacingModel_logFreeZeroDensity
  refine ⟨logSpacingModel, hzd, ?_, logSpacingModel_horizontalMomentLittleO,
    logSpacingModel_criticalClustering, logSpacingModel_sqMoment_lower_bound⟩
  obtain ⟨ε, hε_lim, hε_ev⟩ := hzd
  refine ⟨ε, hε_lim, fun A hA => ?_⟩
  filter_upwards [hε_ev A hA] with V hV
  set Bad := (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
    (fun m => ∃ z ∈ logSpacingModel.Z m, A / Real.log V ≤ |z.re - 1 / 2|)
  have h1 : ∀ m ∈ Bad, (1 : ℝ) ≤
      ∑ z ∈ (logSpacingModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
        (logSpacingModel.mult z : ℝ) := by
    intro m hm
    obtain ⟨_, z₀, hz₀_Z, hz₀_re⟩ := Finset.mem_filter.mp hm
    have hz₀_f : z₀ ∈ (logSpacingModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|) :=
      Finset.mem_filter.mpr ⟨hz₀_Z, hz₀_re⟩
    have hpos : (1 : ℝ) ≤ (logSpacingModel.mult z₀ : ℝ) := by simp [logSpacingModel]
    exact hpos.trans (Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) hz₀_f)
  calc (Bad.card : ℝ) = ∑ _m ∈ Bad, (1 : ℝ) := by simp
    _ ≤ ∑ m ∈ Bad, ∑ z ∈ (logSpacingModel.Z m).filter
          (fun z => A / Real.log V ≤ |z.re - 1 / 2|), (logSpacingModel.mult z : ℝ) :=
        Finset.sum_le_sum h1
    _ ≤ ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ z ∈ (logSpacingModel.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
            (logSpacingModel.mult z : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
          Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    _ ≤ ε A * V := hV

/-- **Exact Giant-Cluster Characterization of `(D_win) ↔ (D_zero)`
(`logFreeNearLineZeroDensity_iff_windowOccupancy_and_clusterTail`).**
`LogFreeNearLineZeroDensity` holds if and only if unit-window occupancy holds at rate `δ(A) → 0`
together with a multiplicity cutoff `K(A) ≥ 0` satisfying `K(A) |δ(A)| → 0` and vanishing
giant-cluster multiplicity tail `∑_{N_m > K(A)} N_m(A, V) ≤ τ(A) V`, `τ(A) → 0`. -/
theorem logFreeNearLineZeroDensity_iff_windowOccupancy_and_clusterTail :
    LogFreeNearLineZeroDensity ↔
    ∃ δ K τ : ℝ → ℝ,
      Tendsto δ atTop (𝓝 0) ∧
      Tendsto (fun A => K A * |δ A|) atTop (𝓝 0) ∧
      Tendsto τ atTop (𝓝 0) ∧
      ∀ A : ℝ, 0 < A → 0 ≤ K A ∧
        (∀ᶠ V : ℝ in atTop,
          (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
            (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)).card : ℝ) ≤
            δ A * V) ∧
        (∀ᶠ V : ℝ in atTop,
          ∑ m ∈ (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
              (fun m => K A < burnolDeepOrderSum m A V),
            burnolDeepOrderSum m A V ≤ τ A * V) := by
  constructor
  · intro hD
    obtain ⟨δ, hδ_lim, hδ_ev⟩ := (logFreeNearLineZeroDensity_implies_windowOccupancy_and_logMean hD).1
    obtain ⟨ε, hε_lim, hε_ev⟩ := hD
    set τ : ℝ → ℝ := fun A => 8 * |ε A| + 1 / max A 1
    have hτ_lim : Tendsto τ atTop (𝓝 0) := by
      have h1 : Tendsto (fun A : ℝ => 8 * |ε A|) atTop (𝓝 (8 * |(0 : ℝ)|)) :=
        ((continuous_abs.tendsto 0).comp hε_lim).const_mul 8
      rw [abs_zero, mul_zero] at h1
      simpa only [τ, add_zero] using h1.add tendsto_one_div_max_one_zero
    refine ⟨δ, fun _ => 0, τ, hδ_lim, by simp, hτ_lim, fun A hA => ⟨le_rfl, hδ_ev A hA, ?_⟩⟩
    filter_upwards [hε_ev A hA,
      eventually_ge_atTop (max 32 ((32 * (shortShellCapConst + 1) * max A 1) ^ 2 + 1)),
      Real.tendsto_log_atTop.eventually_ge_atTop 4] with V hV_z hV_ge hlog4
    have hV32 : 32 ≤ V := (le_max_left _ _).trans hV_ge
    have hV_cap : (32 * (shortShellCapConst + 1) * max A 1) ^ 2 + 1 ≤ V :=
      (le_max_right _ _).trans hV_ge
    have hV_pos : 0 < V := by linarith
    set B_ext := (shellZeros (V - 4) (2 * V + 4)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|)
    have hcov_ext : B_ext ⊆ shellZeros (V - 4) V ∪
        ((shellZeros V (2 * V)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|) ∪
          shellZeros (2 * V) (2 * V + 4)) := by
      intro z hz
      obtain ⟨hz_sh, hz_re⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzS, him_lo⟩ := Finset.mem_filter.mp hz_sh
      obtain ⟨hr0, hr1, him0, him_hi, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
      by_cases hc1 : z.im ≤ V
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
          ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0, hr1, him0, hc1, hxi⟩, him_lo⟩))
      · by_cases hc2 : z.im ≤ 2 * V
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr
              ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0, hr1, him0, hc2, hxi⟩, not_le.mp hc1⟩,
              hz_re⟩))))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0, hr1, him0, him_hi, hxi⟩, not_le.mp hc2⟩))))
    have hcap1 := mediumCap_orderSum_le_logV hV32 hlog4 (V₁ := V - 4) (V₂ := V)
      (by linarith) (by linarith) (by linarith) (by linarith)
    have hcap2 := mediumCap_orderSum_le_logV hV32 hlog4 (V₁ := 2 * V) (V₂ := 2 * V + 4)
      (by linarith) (by linarith) (by linarith) le_rfl
    have hext_le : ∑ z ∈ B_ext, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
        |ε A| * V + 2 * shortShellCapConst * Real.log V := by
      have hu0 := Finset.sum_le_sum_of_subset_of_nonneg hcov_ext
        (f := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ))
        (fun _ _ _ => Nat.cast_nonneg _)
      have hu1 := hu0.trans (finset_sum_union_le _ _ fun _ => Nat.cast_nonneg _)
      have hu2 := finset_sum_union_le
        ((shellZeros V (2 * V)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|))
        (shellZeros (2 * V) (2 * V + 4))
        (f := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ))
        (fun _ => Nat.cast_nonneg _)
      have hz_abs := hV_z.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hV_pos.le)
      unfold shortShellCapConst
      linarith [hu1, hu2, hcap1, hcap2, hz_abs]
    have h16_cap : 16 * shortShellCapConst * Real.log V ≤ (1 / max A 1) * V := by
      have hc_pos := shortShellCapConst_pos
      have hm_pos : 0 < max A 1 := lt_max_of_lt_right zero_lt_one
      have hrt := log_le_two_sqrt_of_pos' hV_pos
      have hrt_gt : 32 * (shortShellCapConst + 1) * max A 1 < Real.sqrt V := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 32 * (shortShellCapConst + 1) * max A 1)]
        exact Real.sqrt_lt_sqrt (by positivity) (lt_of_lt_of_le (lt_add_one _) hV_cap)
      have hrt_pos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV_pos
      rw [one_div_mul_eq_div, le_div_iff₀ hm_pos]
      have hm := mul_lt_mul_of_pos_right hrt_gt hrt_pos
      rw [Real.mul_self_sqrt hV_pos.le] at hm
      have h1 : 16 * shortShellCapConst * Real.log V ≤
          32 * (shortShellCapConst + 1) * Real.sqrt V := by
        calc 16 * shortShellCapConst * Real.log V
            ≤ 16 * (shortShellCapConst + 1) * (2 * Real.sqrt V) :=
              mul_le_mul (by linarith only [hc_pos]) hrt
                (Real.log_nonneg (by linarith only [hV32])) (by linarith only [hc_pos])
          _ = 32 * (shortShellCapConst + 1) * Real.sqrt V := by ring
      calc 16 * shortShellCapConst * Real.log V * max A 1
          ≤ (32 * (shortShellCapConst + 1) * Real.sqrt V) * max A 1 :=
            mul_le_mul_of_nonneg_right h1 hm_pos.le
        _ = 32 * (shortShellCapConst + 1) * max A 1 * Real.sqrt V := by ring
        _ ≤ V := hm.le
    calc ∑ m ∈ (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
            (fun m => 0 < burnolDeepOrderSum m A V), burnolDeepOrderSum m A V
        ≤ ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)), burnolDeepOrderSum m A V :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => burnolDeepOrderSum_nonneg m A V
      _ ≤ 8 * ∑ z ∈ B_ext, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) :=
          sum_burnolDeepOrderSum_le_eight_mul_extendedShell (by linarith only [hV32])
      _ ≤ 8 * (|ε A| * V + 2 * shortShellCapConst * Real.log V) :=
          mul_le_mul_of_nonneg_left hext_le (by norm_num)
      _ = 8 * |ε A| * V + 16 * shortShellCapConst * Real.log V := by ring
      _ ≤ 8 * |ε A| * V + (1 / max A 1) * V := add_le_add le_rfl h16_cap
      _ = τ A * V := by dsimp only [τ]; ring
  · rintro ⟨δ, K, τ, hδ_lim, hKδ_lim, hτ_lim, hspec⟩
    set ε : ℝ → ℝ := fun A => K A * |δ A| + |τ A| + 1 / max A 1
    have hε_lim : Tendsto ε atTop (𝓝 0) := by
      have h1 : Tendsto (fun A : ℝ => K A * |δ A| + |τ A|) atTop (𝓝 (0 + |(0 : ℝ)|)) :=
        hKδ_lim.add ((continuous_abs.tendsto 0).comp hτ_lim)
      rw [abs_zero, add_zero] at h1
      simpa only [ε, add_zero] using h1.add tendsto_one_div_max_one_zero
    refine ⟨ε, hε_lim, fun A hA => ?_⟩
    obtain ⟨hKA_nn, hocc_ev, htail_ev⟩ := hspec A hA
    filter_upwards [hocc_ev, htail_ev,
      eventually_ge_atTop (max 32 ((4 * (shortShellCapConst + 1) * max A 1) ^ 2 + 1)),
      Real.tendsto_log_atTop.eventually_ge_atTop 4] with V hV_occ hV_tail hV_ge hlog4
    have hV32 : 32 ≤ V := (le_max_left _ _).trans hV_ge
    have hV_cap : (4 * (shortShellCapConst + 1) * max A 1) ^ 2 + 1 ≤ V :=
      (le_max_right _ _).trans hV_ge
    have hV_pos : 0 < V := by linarith only [hV32]
    set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
    set Bad_occ := I_V.filter (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)
    have hcov : (shellZeros V (2 * V)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|) ⊆
        shellZeros V (V + 1) ∪
          Bad_occ.biUnion (fun m => (burnolUnitXiZeros m).filter
            (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|)) := by
      intro z hz
      obtain ⟨hz_sh, hz_deep⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzS, hz_gtV⟩ := Finset.mem_filter.mp hz_sh
      obtain ⟨hr0, hr1, him0, him2V, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
      by_cases hlt_ceil : z.im < (Nat.ceil V : ℝ)
      · have hceil_le : (Nat.ceil V : ℝ) ≤ V + 1 := (Nat.ceil_lt_add_one hV_pos.le).le
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
          ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨hr0, hr1, him0, by linarith only [hlt_ceil, hceil_le], hxi⟩,
            hz_gtV⟩))
      · push Not at hlt_ceil
        set m : ℕ := Nat.floor z.im
        have hm_lo : Nat.ceil V ≤ m := Nat.le_floor hlt_ceil
        have hm_hi : m ≤ Nat.floor (2 * V) := Nat.floor_mono him2V
        have hz_unit : z ∈ xiUnitWindowZeros (m : ℝ) :=
          mem_xiUnitWindowZeros.mpr
            ⟨(_root_.RHTower.stripZeros_finite ((m : ℝ) + 1)).mem_toFinset.mpr
              ⟨⟨hr0, hr1, him0.le, Nat.lt_floor_add_one z.im⟩, hxi⟩, Nat.floor_le him0.le⟩
        have hz_burnol : z ∈ burnolUnitXiZeros m := xiUnitWindowZeros_subset_burnolUnitXiZeros m hz_unit
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
          ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_lo, hm_hi⟩, ⟨z, hz_burnol, hz_deep⟩⟩,
            Finset.mem_filter.mpr ⟨hz_burnol, hz_deep⟩⟩))
    have hsplit := (Finset.sum_filter_add_sum_filter_not Bad_occ
      (fun m => K A < burnolDeepOrderSum m A V) (fun m => burnolDeepOrderSum m A V)).symm
    have hpart_hi : ∑ m ∈ Bad_occ.filter (fun m => K A < burnolDeepOrderSum m A V),
        burnolDeepOrderSum m A V ≤ |τ A| * V := by
      have hsub_hi : Bad_occ.filter (fun m => K A < burnolDeepOrderSum m A V) ⊆
          I_V.filter (fun m => K A < burnolDeepOrderSum m A V) := by
        intro m hm
        obtain ⟨hm_b, hgt⟩ := Finset.mem_filter.mp hm
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm_b).1, hgt⟩
      exact ((Finset.sum_le_sum_of_subset_of_nonneg hsub_hi
        fun m _ _ => burnolDeepOrderSum_nonneg m A V).trans hV_tail).trans
          (mul_le_mul_of_nonneg_right (le_abs_self _) hV_pos.le)
    have hpart_lo : ∑ m ∈ Bad_occ.filter (fun m => ¬ K A < burnolDeepOrderSum m A V),
        burnolDeepOrderSum m A V ≤ K A * |δ A| * V := by
      have hle_K : ∑ m ∈ Bad_occ.filter (fun m => ¬ K A < burnolDeepOrderSum m A V),
          burnolDeepOrderSum m A V ≤ (Bad_occ.card : ℝ) * K A := by
        calc _ ≤ ∑ _m ∈ Bad_occ.filter (fun m => ¬ K A < burnolDeepOrderSum m A V), K A :=
              Finset.sum_le_sum fun m hm => not_lt.mp (Finset.mem_filter.mp hm).2
          _ = ((Bad_occ.filter (fun m => ¬ K A < burnolDeepOrderSum m A V)).card : ℝ) * K A := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Bad_occ.card : ℝ) * K A :=
              mul_le_mul_of_nonneg_right
                (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))) hKA_nn
      have hcard_occ : (Bad_occ.card : ℝ) ≤ |δ A| * V :=
        hV_occ.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hV_pos.le)
      exact hle_K.trans ((mul_le_mul_of_nonneg_right hcard_occ hKA_nn).trans_eq (by ring))
    have hcap : ∑ z ∈ shellZeros V (V + 1), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
        (1 / max A 1) * V := by
      have hc_pos := shortShellCapConst_pos
      have hm_pos : 0 < max A 1 := lt_max_of_lt_right zero_lt_one
      have hs : ∑ z ∈ shellZeros V (V + 1), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
          shortShellCapConst * Real.log V :=
        mediumCap_orderSum_le_logV hV32 hlog4 (V₁ := V) (V₂ := V + 1)
          hV_pos.le (by linarith only [hV32]) (by linarith only [hV32]) (by linarith only [hV32])
      have hrt := log_le_two_sqrt_of_pos' hV_pos
      have hrt_gt : 4 * (shortShellCapConst + 1) * max A 1 < Real.sqrt V := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * (shortShellCapConst + 1) * max A 1)]
        exact Real.sqrt_lt_sqrt (by positivity) (lt_of_lt_of_le (lt_add_one _) hV_cap)
      have hrt_pos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV_pos
      rw [one_div_mul_eq_div, le_div_iff₀ hm_pos]
      have hm := mul_lt_mul_of_pos_right hrt_gt hrt_pos
      rw [Real.mul_self_sqrt hV_pos.le] at hm
      have h1 : shortShellCapConst * Real.log V ≤
          4 * (shortShellCapConst + 1) * Real.sqrt V := by
        calc shortShellCapConst * Real.log V
            ≤ 2 * (shortShellCapConst + 1) * (2 * Real.sqrt V) :=
              mul_le_mul (by linarith only [hc_pos]) hrt
                (Real.log_nonneg (by linarith only [hV32])) (by linarith only [hc_pos])
          _ = 4 * (shortShellCapConst + 1) * Real.sqrt V := by ring
      calc (∑ z ∈ shellZeros V (V + 1), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)) * max A 1
          ≤ (shortShellCapConst * Real.log V) * max A 1 := mul_le_mul_of_nonneg_right hs hm_pos.le
        _ ≤ (4 * (shortShellCapConst + 1) * Real.sqrt V) * max A 1 :=
            mul_le_mul_of_nonneg_right h1 hm_pos.le
        _ = 4 * (shortShellCapConst + 1) * max A 1 * Real.sqrt V := by ring
        _ ≤ V := hm.le
    have hbi := finset_sum_biUnion_le Bad_occ
      (fun m => (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|))
      (f := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ))
      (fun _ => Nat.cast_nonneg _)
    have htot : ∑ z ∈ (shellZeros V (2 * V)).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
        (∑ z ∈ shellZeros V (V + 1), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)) +
        ∑ z ∈ Bad_occ.biUnion
          (fun m => (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|)),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) :=
      (Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => Nat.cast_nonneg _).trans
        (finset_sum_union_le _ _ fun _ => Nat.cast_nonneg _)
    change ∑ m ∈ Bad_occ.biUnion _, _ ≤ ∑ m ∈ Bad_occ, burnolDeepOrderSum m A V at hbi
    dsimp only [ε]
    linarith only [htot, hbi, hsplit, hpart_hi, hpart_lo, hcap]

/-- **Growing Second-Moment Converse (`logFreeNearLineZeroDensity_of_windowOccupancy_and_growingSqMoment`).**
`LogFreeNearLineWindowOccupancy` at rate `δ(A) → 0` upgrades to `LogFreeNearLineZeroDensity`
even when `∑_m N_m(A, V)^2 ≤ M(A) V` has `M(A) → +∞`, provided `|δ(A)| * |M(A)| → 0`. -/
theorem logFreeNearLineZeroDensity_of_windowOccupancy_and_growingSqMoment
    {δ M : ℝ → ℝ}
    (hδ_lim : Tendsto δ atTop (𝓝 0))
    (hδ_ev : ∀ A : ℝ, 0 < A → ∀ᶠ V : ℝ in atTop,
      (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
        (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)).card : ℝ) ≤
          δ A * V)
    (hδM_lim : Tendsto (fun A => |δ A| * |M A|) atTop (𝓝 0))
    (hM_ev : ∀ A : ℝ, 0 < A → 0 ≤ M A ∧ ∀ᶠ V : ℝ in atTop,
      ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        (burnolDeepOrderSum m A V) ^ 2 ≤ M A * V) :
    LogFreeNearLineZeroDensity := by
  refine logFreeNearLineZeroDensity_iff_windowOccupancy_and_clusterTail.mpr
    ⟨δ, fun _ => 0, fun A => Real.sqrt (|δ A| * |M A|), hδ_lim, by simp, ?_, fun A hA => ?_⟩
  · simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hδM_lim
  · refine ⟨le_rfl, hδ_ev A hA, ?_⟩
    filter_upwards [hδ_ev A hA, (hM_ev A hA).2, eventually_ge_atTop (1 : ℝ)] with V hV_occ hV_M hV1
    have hV_pos : 0 < V := by linarith
    set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
    set Bad_occ := I_V.filter (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)
    have hsub : I_V.filter (fun m => 0 < burnolDeepOrderSum m A V) ⊆ Bad_occ := by
      intro m hm
      obtain ⟨hm_I, hpos⟩ := Finset.mem_filter.mp hm
      refine Finset.mem_filter.mpr ⟨hm_I, ?_⟩
      by_contra hfree
      have hempty : (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|) = ∅ := by
        ext ρ; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨h1, h2⟩; exact hfree ⟨ρ, h1, h2⟩
      unfold burnolDeepOrderSum at hpos
      rw [hempty, Finset.sum_empty] at hpos
      linarith
    have hcs_sq : (∑ m ∈ Bad_occ, burnolDeepOrderSum m A V) ^ 2 ≤ (|δ A| * |M A|) * V ^ 2 := by
      have h1 := sq_sum_le_card_mul_sum_sq Bad_occ (fun m => burnolDeepOrderSum m A V)
      have hc : (Bad_occ.card : ℝ) ≤ |δ A| * V :=
        hV_occ.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hV_pos.le)
      have hs : ∑ m ∈ Bad_occ, (burnolDeepOrderSum m A V) ^ 2 ≤ |M A| * V :=
        ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => sq_nonneg _).trans hV_M).trans
          (mul_le_mul_of_nonneg_right (le_abs_self _) hV_pos.le)
      calc _ ≤ (Bad_occ.card : ℝ) * ∑ m ∈ Bad_occ, (burnolDeepOrderSum m A V) ^ 2 := h1
        _ ≤ (|δ A| * V) * (|M A| * V) :=
            mul_le_mul hc hs (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = (|δ A| * |M A|) * V ^ 2 := by ring
    have hnn : 0 ≤ ∑ m ∈ Bad_occ, burnolDeepOrderSum m A V :=
      Finset.sum_nonneg fun m _ => burnolDeepOrderSum_nonneg m A V
    calc ∑ m ∈ I_V.filter (fun m => 0 < burnolDeepOrderSum m A V), burnolDeepOrderSum m A V
        ≤ ∑ m ∈ Bad_occ, burnolDeepOrderSum m A V :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => burnolDeepOrderSum_nonneg m A V
      _ = Real.sqrt ((∑ m ∈ Bad_occ, burnolDeepOrderSum m A V) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((|δ A| * |M A|) * V ^ 2) := Real.sqrt_le_sqrt hcs_sq
      _ = Real.sqrt (|δ A| * |M A|) * V := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hV_pos.le]

/-! ## §3. Planck-to-unit push: uniform Planck obstruction, Planck `logDoorStage` certificates,
mesoscopic windows, and vertical Planck-shadow `IFF` bridge -/

/-- Local rectangle-boundary edge exhaustion for `[z₁.re, z₂.re] × [z₁.im, z₂.im]`. -/
private lemma rectangleBoundaryPath_on_edges_local (z₁ z₂ : ℂ) (s : ℝ) :
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ s).re = z₁.re ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ s).re = z₂.re ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ s).im = z₁.im ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ s).im = z₂.im := by
  unfold _root_.RHTower.rectangleBoundaryPath _root_.RHTower.rectangleEdgePath
  set τ := Int.fract s
  split_ifs with h1 h2 h3
  · right; right; left; simp
  · right; left; simp
  · right; right; right; simp
  · left; simp

/-- Vertical-edge membership on a sub-rectangle `[x₁, x₂] × [t, y₂]` inside `[x₁, x₂] × [y₁, y_u]`
lifts boundary nonvanishing from the outer rectangle. -/
private lemma vertical_edge_ne_zero_of_outer_bdry {y₁ y_u : ℝ} (N : ℕ)
    (houter : ∀ s : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y_u) s) ≠ 0)
    {z : ℂ} (hre : z.re = -1 / 2 ∨ z.re = 3 / 2)
    (him_lo : y₁ < z.im) (him_hi : z.im < y_u) :
    _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
  have hdy : 0 < y_u - y₁ := by linarith
  have hll_im : (centeredWindowLowerLeft y₁).im = y₁ := by simp [centeredWindowLowerLeft]
  have hur_im : (centeredWindowUpperRight y_u).im = y_u := by simp [centeredWindowUpperRight]
  rcases hre with hleft | hright
  · set τ : ℝ := 3 / 4 + (y_u - z.im) / (4 * (y_u - y₁))
    have hτ_gt : 3 / 4 < τ := by
      dsimp only [τ]
      linarith [div_pos (sub_pos.mpr him_hi) (by positivity : 0 < 4 * (y_u - y₁))]
    have hτ_lt : τ < 1 := by
      dsimp only [τ]
      have h1 : (y_u - z.im) / (4 * (y_u - y₁)) < 1 / 4 := by
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    have hz_eq : _root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y_u) τ = z := by
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, hτ_lt⟩,
        _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (by linarith),
        if_neg (not_le.mpr hτ_gt)]
      apply Complex.ext
      · simp [centeredWindowLowerLeft, hleft]
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, hll_im, hur_im, mul_one, mul_zero, add_zero]
        dsimp only [τ]; field_simp [hdy.ne']; ring
    exact hz_eq ▸ houter τ
  · set τ : ℝ := 1 / 4 + (z.im - y₁) / (4 * (y_u - y₁))
    have hτ_gt : 1 / 4 < τ := by
      dsimp only [τ]
      linarith [div_pos (sub_pos.mpr him_lo) (by positivity : 0 < 4 * (y_u - y₁))]
    have hτ_le : τ ≤ 1 / 2 := by
      dsimp only [τ]
      have h1 : (z.im - y₁) / (4 * (y_u - y₁)) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    have hz_eq : _root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y_u) τ = z := by
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_neg (not_le.mpr hτ_gt), if_pos hτ_le]
      apply Complex.ext
      · simp [centeredWindowUpperRight, hright]
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, hll_im, hur_im, mul_one, mul_zero, add_zero]
        dsimp only [τ]; field_simp [hdy.ne']; ring
    exact hz_eq ▸ houter τ

/-- **Uniform Planck-Window Obstruction (`sparseModel_uniformPlanckVolume_not_windowOccupancy`).**
`sparseModel` satisfies the uniform Planck-window zero-free volume bound
`O(B * (e^{-r A} / A) * V)` across all `2 ≤ A`, `0 < B ≤ log V`, and `0 < r < 1`, yet violates
unit-window `WindowOccupancy` because `B = log V` incurs the exact `log V` covering loss. -/
theorem sparseModel_uniformPlanckVolume_not_windowOccupancy :
    ¬ sparseModel.WindowOccupancy ∧
    ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ V : ℝ in atTop,
      ∀ A B : ℝ, 2 ≤ A → 0 < B → B ≤ Real.log V →
        volume {t ∈ Icc V (2 * V) |
          ∃ m : ℕ, ∃ z ∈ sparseModel.Z m,
            t ≤ z.im ∧ z.im ≤ t + B / Real.log V ∧ A / Real.log V ≤ |z.re - 1 / 2|} ≤
          ENNReal.ofReal (8 * B * (Real.exp (-(r * A)) / A) * V) := by
  refine ⟨?_, fun r hr0 hr1 => ?_⟩
  · -- `¬ sparseModel.WindowOccupancy`: for `A = 1`, every window in `[⌈V⌉, ⌊2V⌋]` is occupied once `log(log V) ≥ 16`.
    rintro ⟨δ, hδ_lim, hδ_ev⟩
    obtain ⟨A₀, hA₀⟩ := Metric.tendsto_atTop.mp hδ_lim (1 / 4) (by norm_num)
    set A₁ : ℝ := max 1 (|A₀| + 1)
    have hA₁_pos : 0 < A₁ := by positivity
    have hδ_lt : δ A₁ < 1 / 4 := by
      have h := hA₀ A₁ (by dsimp only [A₁]; linarith [le_abs_self A₀, le_max_right 1 (|A₀| + 1)])
      rw [Real.dist_eq, sub_zero] at h
      exact (le_abs_self _).trans_lt h
    have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp
      ((hδ_ev A₁ hA₁_pos).and ((eventually_ge_atTop (512 : ℝ)).and
        ((Real.tendsto_log_atTop.eventually_ge_atTop 16).and
          (ht_ll.eventually_ge_atTop (16 * A₁)))))
    obtain ⟨hocc, hV512, hlog16, hll_ge⟩ := hV₁ V₁ le_rfl
    have hV_pos : 0 < V₁ := by linarith
    have hlogV_pos : 0 < Real.log V₁ := by linarith
    set I_V := Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁))
    have hall : I_V.filter (fun m => ∃ z ∈ sparseModel.Z m, A₁ / Real.log V₁ ≤ |z.re - 1 / 2|) = I_V := by
      refine Finset.filter_eq_self.mpr fun m hm_I => ?_
      obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_I
      have hm_ge_V : V₁ ≤ (m : ℝ) := (Nat.le_ceil V₁).trans (by exact_mod_cast hm_lo)
      have hm_le_2V : (m : ℝ) ≤ 2 * V₁ :=
        ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
      have hm_not : ¬ m < 256 := by
        intro hlt
        have hm256 : (m : ℝ) < 256 := Nat.cast_lt.mpr hlt
        linarith only [hV512, hm_ge_V, hm256]
      have hlog_ge : Real.log V₁ ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
      have hlog_le : Real.log (m : ℝ) ≤ 2 * Real.log V₁ := by
        have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V₁) :=
          Real.log_le_log (by linarith only [hV512, hm_ge_V]) hm_le_2V
        rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
        linarith only [h1, log_two_lt_one, hlog16]
      have hll_m : Real.log (Real.log V₁) ≤ Real.log (Real.log (m : ℝ)) :=
        Real.log_le_log hlogV_pos hlog_ge
      have hd_ge : A₁ / Real.log V₁ ≤ dSparse m := by
        simp only [dSparse, if_neg hm_not]
        calc A₁ / Real.log V₁
            ≤ ((1 / 16) * Real.log (Real.log V₁)) / Real.log V₁ :=
              div_le_div_of_nonneg_right (by linarith only [hll_ge]) hlogV_pos.le
          _ = (1 / 8) * Real.log (Real.log V₁) / (2 * Real.log V₁) := by ring
          _ ≤ (1 / 8) * Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ) := by
              calc _ ≤ (1 / 8) * Real.log (Real.log (m : ℝ)) / (2 * Real.log V₁) :=
                    div_le_div_of_nonneg_right (by linarith only [hll_m]) (by positivity)
                _ ≤ _ := div_le_div_of_nonneg_left
                    (by linarith only [hA₁_pos, hll_ge, hll_m])
                    (by linarith only [hlogV_pos, hlog_ge]) hlog_le
      have hcard_pos : 0 < ((sparseModel.Z m).filter
          (fun z => A₁ / Real.log V₁ ≤ |z.re - 1 / 2|)).card := by
        dsimp only [sparseModel]
        rw [packetWin_filter_abs_card (div_pos hA₁_pos hlogV_pos) (qSparse_dSparse_or m),
          if_pos hd_ge]
        simp [qSparse, hm_not]
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard_pos
      exact ⟨z, (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩
    rw [hall] at hocc
    have hcard_lo : V₁ / 2 ≤ (I_V.card : ℝ) := by
      have hc : (Nat.ceil V₁ : ℝ) < V₁ + 1 := Nat.ceil_lt_add_one hV_pos.le
      have hf : 2 * V₁ - 1 < (Nat.floor (2 * V₁) : ℝ) := Nat.sub_one_lt_floor (2 * V₁)
      have hle_cf : Nat.ceil V₁ ≤ Nat.floor (2 * V₁) := by
        by_contra hgt; push Not at hgt
        have : (Nat.floor (2 * V₁) : ℝ) + 1 ≤ (Nat.ceil V₁ : ℝ) := by exact_mod_cast hgt
        linarith
      have hcard_eq : I_V.card = Nat.floor (2 * V₁) + 1 - Nat.ceil V₁ := Nat.card_Icc _ _
      have hcast : (I_V.card : ℝ) = (Nat.floor (2 * V₁) : ℝ) + 1 - (Nat.ceil V₁ : ℝ) := by
        rw [hcard_eq, Nat.cast_sub (by omega)]; push_cast; ring
      linarith
    nlinarith [hocc, hcard_lo, hδ_lt, hV_pos]
  · -- Uniform Planck-window volume bound for `sparseModel`.
    have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    filter_upwards [eventually_ge_atTop (512 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 16,
      ht_ll.eventually_ge_atTop 4] with V hV512 hlog16 hll4 A B hA2 hB_pos hB_hi
    have hV_pos : 0 < V := by linarith
    have hlogV_pos : 0 < Real.log V := by linarith
    have hB_div_le1 : B / Real.log V ≤ 1 := (div_le_one hlogV_pos).mpr hB_hi
    set J_V := Finset.Icc (Nat.floor V) (Nat.floor (2 * V) + 1)
    -- Every `m ∈ J_V` has `dSparse m ≤ (1 / 2) * log(log V) / log V`.
    have hd_ub : ∀ m ∈ J_V, dSparse m ≤ (1 / 2) * Real.log (Real.log V) / Real.log V := by
      intro m hm_J
      obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm_J
      have hm_ge : V - 1 < (m : ℝ) :=
        (Nat.sub_one_lt_floor V).trans_le (by exact_mod_cast hm_lo)
      have hm_le : (m : ℝ) ≤ 2 * V + 1 := by
        have h1 : (m : ℝ) ≤ (Nat.floor (2 * V) : ℝ) + 1 := by exact_mod_cast hm_hi
        linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * V)]
      have hm_not : ¬ m < 256 := by
        intro hlt
        have hm256 : (m : ℝ) < 256 := Nat.cast_lt.mpr hlt
        linarith only [hV512, hm_ge, hm256]
      simp only [dSparse, if_neg hm_not]
      have hlog_lo : (1 / 2) * Real.log V ≤ Real.log (m : ℝ) := by
        have h1 : Real.log (V / 2) ≤ Real.log (m : ℝ) :=
          Real.log_le_log (by linarith only [hV512]) (by linarith only [hV512, hm_ge])
        rw [Real.log_div hV_pos.ne' zero_lt_two.ne'] at h1
        linarith only [h1, log_two_lt_one, hlog16]
      have hlog_hi : Real.log (m : ℝ) ≤ 2 * Real.log V := by
        have hsq : (m : ℝ) ≤ V ^ 2 := by nlinarith only [hV512, hm_le]
        calc Real.log (m : ℝ) ≤ Real.log (V ^ 2) :=
              Real.log_le_log (by linarith only [hV512, hm_ge]) hsq
          _ = 2 * Real.log V := by rw [Real.log_pow]; push_cast; rfl
      have hll_hi : Real.log (Real.log (m : ℝ)) ≤ 2 * Real.log (Real.log V) := by
        have h1 : Real.log (Real.log (m : ℝ)) ≤ Real.log (2 * Real.log V) :=
          Real.log_le_log (by linarith only [hlog16, hlog_lo]) hlog_hi
        rw [Real.log_mul zero_lt_two.ne' hlogV_pos.ne'] at h1
        linarith only [h1, log_two_lt_one, hll4]
      calc (1 / 8) * Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)
          ≤ (1 / 8) * (2 * Real.log (Real.log V)) / Real.log (m : ℝ) :=
            div_le_div_of_nonneg_right (by linarith only [hll_hi])
              (by linarith only [hlog16, hlog_lo])
        _ ≤ (1 / 8) * (2 * Real.log (Real.log V)) / ((1 / 2) * Real.log V) :=
            div_le_div_of_nonneg_left (by linarith only [hll4]) (by positivity) hlog_lo
        _ = (1 / 2) * Real.log (Real.log V) / Real.log V := by
            field_simp [hlogV_pos.ne']; ring
    rcases lt_or_ge ((1 / 2) * Real.log (Real.log V)) A with hA_gt | hA_le
    · -- Above `(1 / 2) * log(log V)`, the bad set is empty.
      have hempty : {t ∈ Icc V (2 * V) |
          ∃ m : ℕ, ∃ z ∈ sparseModel.Z m,
            t ≤ z.im ∧ z.im ≤ t + B / Real.log V ∧ A / Real.log V ≤ |z.re - 1 / 2|} = ∅ := by
        ext t; simp only [Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨ht_I, m, z, hz_Z, ht_im, him_tB, hz_re⟩
        obtain ⟨_, _, him_m0, him_m1⟩ := sparseModel.in_unit_strip m z hz_Z
        have hm_J : m ∈ J_V := by
          refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
          · by_contra hlt; push Not at hlt
            have h1 : (m : ℝ) + 1 ≤ (Nat.floor V : ℝ) := by exact_mod_cast hlt
            have hfl := Nat.floor_le hV_pos.le
            linarith only [h1, hfl, ht_I.1, ht_im, him_m1]
          · by_contra hgt; push Not at hgt
            have h1 : (Nat.floor (2 * V) : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hgt
            have hfl := Nat.lt_floor_add_one (2 * V)
            have him_hi : z.im ≤ 2 * V + 1 := him_tB.trans (add_le_add ht_I.2 hB_div_le1)
            linarith only [h1, hfl, him_m0, him_hi]
        have hcard0 : ((sparseModel.Z m).filter
            (fun w => A / Real.log V ≤ |w.re - 1 / 2|)).card = 0 := by
          dsimp only [sparseModel]
          rw [packetWin_filter_abs_card (div_pos (by linarith only [hA2]) hlogV_pos) (qSparse_dSparse_or m),
            if_neg]
          exact not_le.mpr ((hd_ub m hm_J).trans_lt (div_lt_div_of_pos_right hA_gt hlogV_pos))
        exact absurd (Finset.mem_filter.mpr ⟨hz_Z, hz_re⟩) (Finset.card_eq_zero.mp hcard0 ▸ Finset.notMem_empty z)
      rw [hempty, measure_empty]; exact zero_le
    · -- For `2 ≤ A ≤ (1 / 2) * log(log V)`, union-bound over `J_V` and use `A * e^{r A} ≤ log V`.
      set Z_bad := J_V.biUnion (fun m => (sparseModel.Z m).filter
        (fun z => A / Real.log V ≤ |z.re - 1 / 2|))
      have hcov : {t ∈ Icc V (2 * V) |
          ∃ m : ℕ, ∃ z ∈ sparseModel.Z m,
            t ≤ z.im ∧ z.im ≤ t + B / Real.log V ∧ A / Real.log V ≤ |z.re - 1 / 2|} ⊆
          ⋃ z ∈ Z_bad, Icc (z.im - B / Real.log V) z.im := by
        intro t ⟨ht_I, m, z, hz_Z, ht_im, him_tB, hz_re⟩
        obtain ⟨_, _, him_m0, him_m1⟩ := sparseModel.in_unit_strip m z hz_Z
        have hm_J : m ∈ J_V := by
          refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
          · by_contra hlt; push Not at hlt
            have h1 : (m : ℝ) + 1 ≤ (Nat.floor V : ℝ) := by exact_mod_cast hlt
            linarith [Nat.floor_le hV_pos.le, ht_I.1]
          · by_contra hgt; push Not at hgt
            have h1 : (Nat.floor (2 * V) : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hgt
            linarith [Nat.lt_floor_add_one (2 * V), ht_I.2]
        exact Set.mem_biUnion (Finset.mem_biUnion.mpr ⟨m, hm_J, Finset.mem_filter.mpr ⟨hz_Z, hz_re⟩⟩)
          ⟨by linarith, ht_im⟩
      have hZ_card : (Z_bad.card : ℝ) ≤ 8 * V := by
        have hbi : Z_bad.card ≤ ∑ m ∈ J_V, ((sparseModel.Z m).filter
            (fun z => A / Real.log V ≤ |z.re - 1 / 2|)).card := Finset.card_biUnion_le
        have hterm : ∀ m ∈ J_V, ((sparseModel.Z m).filter
            (fun z => A / Real.log V ≤ |z.re - 1 / 2|)).card ≤ 2 := by
          intro m _
          dsimp only [sparseModel]
          rw [packetWin_filter_abs_card (div_pos (by linarith) hlogV_pos) (qSparse_dSparse_or m)]
          split_ifs
          · simp only [qSparse]; split_ifs <;> omega
          · omega
        have hsum_le : Z_bad.card ≤ 2 * J_V.card := by
          calc Z_bad.card ≤ ∑ m ∈ J_V, ((sparseModel.Z m).filter
                (fun z => A / Real.log V ≤ |z.re - 1 / 2|)).card := hbi
            _ ≤ ∑ _m ∈ J_V, 2 := Finset.sum_le_sum hterm
            _ = 2 * J_V.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        have hJ_card : (J_V.card : ℝ) ≤ 4 * V := by
          have h1 : J_V.card ≤ Nat.floor (2 * V) + 2 := by rw [Nat.card_Icc]; omega
          have h2 : (J_V.card : ℝ) ≤ (Nat.floor (2 * V) : ℝ) + 2 := by exact_mod_cast h1
          linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * V)]
        have hsum_R : (Z_bad.card : ℝ) ≤ 2 * (J_V.card : ℝ) := by exact_mod_cast hsum_le
        linarith
      have hinv_log : (Real.log V)⁻¹ ≤ Real.exp (-(r * A)) / A := by
        set y : ℝ := (1 / 2) * Real.log (Real.log V)
        have hA_ey : A ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
        have hrA_ey : Real.exp (r * A) ≤ Real.exp y :=
          Real.exp_le_exp.mpr (by nlinarith [hr0, hr1, hA2, hA_le])
        have hprod_le : A * Real.exp (r * A) ≤ Real.log V := by
          calc A * Real.exp (r * A)
              ≤ Real.exp y * Real.exp y := mul_le_mul hA_ey hrA_ey (Real.exp_pos _).le (by positivity)
            _ = Real.exp (Real.log (Real.log V)) := by
                rw [← Real.exp_add]; congr 1; dsimp only [y]; ring
            _ = Real.log V := Real.exp_log hlogV_pos
        have hpos_AE : 0 < A * Real.exp (r * A) := mul_pos (by linarith) (Real.exp_pos _)
        calc (Real.log V)⁻¹ ≤ (A * Real.exp (r * A))⁻¹ := inv_anti₀ hpos_AE hprod_le
          _ = Real.exp (-(r * A)) / A := by
              rw [Real.exp_neg, mul_inv, div_eq_mul_inv, mul_comm]
      calc volume {t ∈ Icc V (2 * V) |
              ∃ m : ℕ, ∃ z ∈ sparseModel.Z m,
                t ≤ z.im ∧ z.im ≤ t + B / Real.log V ∧ A / Real.log V ≤ |z.re - 1 / 2|}
          ≤ volume (⋃ z ∈ Z_bad, Icc (z.im - B / Real.log V) z.im) := measure_mono hcov
        _ ≤ ∑ z ∈ Z_bad, volume (Icc (z.im - B / Real.log V) z.im) :=
            measure_biUnion_finset_le Z_bad _
        _ = ∑ _z ∈ Z_bad, ENNReal.ofReal (B / Real.log V) := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Real.volume_Icc, show z.im - (z.im - B / Real.log V) = B / Real.log V by ring]
        _ = ENNReal.ofReal ((Z_bad.card : ℝ) * (B / Real.log V)) := by
            rw [Finset.sum_const, nsmul_eq_mul,
              ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (8 * B * (Real.exp (-(r * A)) / A) * V) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc (Z_bad.card : ℝ) * (B / Real.log V)
                ≤ (8 * V) * (B * (Real.log V)⁻¹) := by
                  rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hZ_card (by positivity)
              _ ≤ (8 * V) * (B * (Real.exp (-(r * A)) / A)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hinv_log hB_pos.le) (by positivity)
              _ = 8 * B * (Real.exp (-(r * A)) / A) * V := by ring

/-- Explicit `logDoorStage` Bessel–Szegő certificate predicate on the Planck window
`[-1/2, 3/2] × [t, t + B / log V]` at integer prefix `N = doorSqrtPrefix ⌊t⌋₊`. -/
def HasPlanckLogStageBesselCertificate (B V c t : ℝ) : Prop :=
  let m := Nat.floor t
  let N := doorSqrtPrefix m
  let y₂ := t + B / Real.log V
  (∀ s : ℝ, _root_.RHTower.finiteThetaAmplitude N
    (_root_.RHTower.rectangleBoundaryPath
      (centeredWindowLowerLeft t) (centeredWindowUpperRight y₂) s) ≠ 0) ∧
  ∀ K : ℕ,
    2 * (centeredThetaWindowDegree t y₂ N : ℝ) ^ 2 *
        (1 - logStageMargin c m) ^ (K + 1) / logStageMargin c m < Real.pi / 2 →
    ∀ u : HTGeometry.UnitCircle,
      0 < (besselSzegoCertificate (logDoorStage c m) K
          (fun s => ‖centeredThetaExpSum t y₂ N s‖ ^ 2) u *
        centeredThetaLaurentLoop t y₂ (logDoorStage c m) N u).re

/-- **Unconditional Planck-Window Log-Stage Bessel–Szegő Certificate (`almostAll_planckWindow_logStage_besselSzegoCertificate`).**
For every `B > 0` and `0 < r < 1`, there exists `η(c) → 0` as `c → 0⁺` such that for every `c > 0`,
eventually in `V`, the Lebesgue measure of `t ∈ [V, 2V]` failing `HasPlanckLogStageBesselCertificate B V c t`
is at most `η(c) * V`. -/
theorem almostAll_planckWindow_logStage_besselSzegoCertificate
    {B r : ℝ} (hB : 0 < B) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ η : ℝ → ℝ, Tendsto η (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
      ∀ c : ℝ, 0 < c → ∀ᶠ V : ℝ in atTop,
        volume {t ∈ Icc V (2 * V) | ¬ HasPlanckLogStageBesselCertificate B V c t} ≤
          ENNReal.ofReal (η c * V) := by
  obtain ⟨C_d, κ_r, hCd_pos, hκ_pos, hd_ev⟩ := deepExtendedShell_orderSum_le hr0 hr1
  let η : ℝ → ℝ := fun c =>
    if 0 < c ∧ c < 1 / 128 then C_d * (8 + 64 * B * c) * Real.exp (-(r / (64 * c))) else 1
  refine ⟨η, ?_, fun c hc => ?_⟩
  · -- `η(c) → 0` as `c → 0⁺` via `e^{-x} ≤ 1 / x` on `(0, 1 / 128)`.
    refine Metric.tendsto_nhdsWithin_nhds.mpr fun ε hε => ?_
    set K_lip : ℝ := C_d * (8 + B) * (64 / r)
    have hK_pos : 0 < K_lip := by dsimp only [K_lip]; positivity
    refine ⟨min (1 / 128) (ε / (K_lip + 1)), lt_min (by norm_num) (by positivity), fun c hc_pos hc_dist => ?_⟩
    rw [Set.mem_Ioi] at hc_pos
    rw [Real.dist_eq, sub_zero, abs_of_pos hc_pos] at hc_dist
    have hc_128 : c < 1 / 128 := hc_dist.trans_le (min_le_left _ _)
    have hc_ε : c < ε / (K_lip + 1) := hc_dist.trans_le (min_le_right _ _)
    have hη_eq : η c = C_d * (8 + 64 * B * c) * Real.exp (-(r / (64 * c))) :=
      if_pos ⟨hc_pos, hc_128⟩
    rw [Real.dist_eq, sub_zero, hη_eq, abs_of_nonneg (by positivity)]
    have hexp_le : Real.exp (-(r / (64 * c))) ≤ (64 / r) * c := by
      have hx_pos : 0 < r / (64 * c) := by positivity
      have hx_exp : r / (64 * c) ≤ Real.exp (r / (64 * c)) :=
        by linarith [Real.add_one_le_exp (r / (64 * c))]
      rw [Real.exp_neg]
      calc (Real.exp (r / (64 * c)))⁻¹ ≤ (r / (64 * c))⁻¹ := inv_anti₀ hx_pos hx_exp
        _ = (64 / r) * c := by field_simp [hr0.ne', hc_pos.ne']
    have h8B : 8 + 64 * B * c ≤ 8 + B := by nlinarith [hB, hc_128]
    have hle_K : C_d * (8 + 64 * B * c) * Real.exp (-(r / (64 * c))) ≤ K_lip * c := by
      calc C_d * (8 + 64 * B * c) * Real.exp (-(r / (64 * c)))
          ≤ C_d * (8 + B) * ((64 / r) * c) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h8B hCd_pos.le) hexp_le
              (Real.exp_pos _).le (by positivity)
        _ = K_lip * c := by dsimp only [K_lip]; ring
    have hKc_lt : c * (K_lip + 1) < ε := (lt_div_iff₀ (by positivity)).mp hc_ε
    nlinarith only [hle_K, hKc_lt, hc_pos, hK_pos]
  · -- Fix `c > 0`.
    by_cases hc_small : c < 1 / 128
    · have hη_eq : η c = C_d * (8 + 64 * B * c) * Real.exp (-(r / (64 * c))) :=
        if_pos ⟨hc, hc_small⟩
      rw [hη_eq]
      set A_c : ℝ := 1 / (64 * c)
      have hAc_gt2 : 2 < A_c := by
        dsimp only [A_c]
        rw [lt_div_iff₀ (by positivity)]
        linarith only [hc_small]
      obtain ⟨m₁, htail⟩ := exists_logStage_tail_lt c hc
      filter_upwards [hd_ev,
        eventually_ge_atTop (max 32 ((m₁ + 2 : ℕ) : ℝ)),
        Real.tendsto_log_atTop.eventually_ge_atTop
          (max (max 16 B) (max (A_c / κ_r) (7 / c + 1)))] with V hV_d hV_lo hlog_lo
      have hV32 : 32 ≤ V := (le_max_left _ _).trans hV_lo
      have hVm₁ : ((m₁ + 2 : ℕ) : ℝ) ≤ V := (le_max_right _ _).trans hV_lo
      have hV_pos : 0 < V := by linarith only [hV32]
      have hlog16 : 16 ≤ Real.log V := ((le_max_left _ _).trans (le_max_left _ _)).trans hlog_lo
      have hlogB : B ≤ Real.log V := ((le_max_right _ _).trans (le_max_left _ _)).trans hlog_lo
      have hlogAc : A_c / κ_r ≤ Real.log V :=
        ((le_max_left _ _).trans (le_max_right _ _)).trans hlog_lo
      have hlog7c : 7 / c + 1 ≤ Real.log V :=
        ((le_max_right _ _).trans (le_max_right _ _)).trans hlog_lo
      have hlogV_pos : 0 < Real.log V := by linarith only [hlog16]
      have hAc_le_κ : A_c ≤ κ_r * Real.log V := by
        have hm := mul_le_mul_of_nonneg_left hlogAc hκ_pos.le
        rwa [mul_div_cancel₀ _ hκ_pos.ne'] at hm
      have hB_div_pos : 0 < B / Real.log V := div_pos hB hlogV_pos
      have hB_div_le1 : B / Real.log V ≤ 1 := (div_le_one hlogV_pos).mpr hlogB
      -- Finite exceptional height finset `Y_fin` where `finiteThetaAmplitude` hits horizontal edges.
      let W_burnol (k : ℕ) := centeredThetaWindow (burnolUnitLower_le_upper k) (doorSqrtPrefix k)
        (burnolUnit_bdry_regular k (burnolPrefix_le_doorSqrtPrefix k))
      let Y_fin : Finset ℝ := (Finset.Icc (Nat.floor V) (Nat.floor (2 * V))).biUnion
        (fun k => (W_burnol k).Z.image Complex.im ∪
          (W_burnol k).Z.image (fun z => z.im - B / Real.log V))
      set B_ext := (shellZeros (V - 4) (2 * V + 4)).filter
        (fun z => A_c / Real.log V ≤ |z.re - 1 / 2|)
      set δ_im : ℝ := 4 * A_c / Real.log V
      -- Every bad `t ∈ [V, 2V]` lies either in `Y_fin` or within `[w.im - (B + 4 A_c)/log V, w.im + 4 A_c/log V]` of `w ∈ B_ext`.
      have hcov : {t ∈ Icc V (2 * V) | ¬ HasPlanckLogStageBesselCertificate B V c t} ⊆
          (Y_fin : Set ℝ) ∪ ⋃ w ∈ B_ext, Icc (w.im - B / Real.log V - δ_im) (w.im + δ_im) := by
        intro t ⟨ht_I, hnot_cert⟩
        by_cases ht_Y : t ∈ (Y_fin : Set ℝ)
        · exact Or.inl ht_Y
        · refine Or.inr ?_
          set m : ℕ := Nat.floor t
          set N : ℕ := doorSqrtPrefix m
          set y₂ : ℝ := t + B / Real.log V
          have ht_le_y₂ : t ≤ y₂ := le_add_of_nonneg_right hB_div_pos.le
          have hm_le_t : (m : ℝ) ≤ t := Nat.floor_le (by linarith only [hV_pos, ht_I.1])
          have ht_lt_m1 : t < (m : ℝ) + 1 := Nat.lt_floor_add_one t
          have hm_mem : m ∈ Finset.Icc (Nat.floor V) (Nat.floor (2 * V)) :=
            Finset.mem_Icc.mpr ⟨Nat.floor_mono ht_I.1, Nat.floor_mono ht_I.2⟩
          have hm₁_le : m₁ ≤ m := by
            by_contra hlt; push Not at hlt
            have h1 : (m : ℝ) + 1 ≤ (m₁ : ℝ) := by exact_mod_cast hlt
            have h2 : (m₁ : ℝ) + 2 ≤ V := by exact_mod_cast hVm₁
            linarith only [h1, h2, ht_lt_m1, ht_I.1]
          have hcoords := burnolUnit_coords m
          have hy₁_lt_t : burnolUnitLower m < t := by linarith only [hcoords.2.1, hm_le_t]
          have hy₂_lt_u : y₂ < burnolUnitUpper m := by
            dsimp only [y₂]; linarith only [hcoords.2.2.1, ht_lt_m1, hB_div_le1]
          -- Step 1: `[t, y₂]` is boundary-regular since `t ∉ Y_fin`.
          have hbdry_t : ∀ s : ℝ, _root_.RHTower.finiteThetaAmplitude N
              (_root_.RHTower.rectangleBoundaryPath
                (centeredWindowLowerLeft t) (centeredWindowUpperRight y₂) s) ≠ 0 := by
            intro s hs0
            set z := _root_.RHTower.rectangleBoundaryPath
              (centeredWindowLowerLeft t) (centeredWindowUpperRight y₂) s
            have hll_re : (centeredWindowLowerLeft t).re = -1 / 2 := by simp [centeredWindowLowerLeft]
            have hll_im : (centeredWindowLowerLeft t).im = t := by simp [centeredWindowLowerLeft]
            have hur_re : (centeredWindowUpperRight y₂).re = 3 / 2 := by simp [centeredWindowUpperRight]
            have hur_im : (centeredWindowUpperRight y₂).im = y₂ := by simp [centeredWindowUpperRight]
            have hmem_rect := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
              (centeredWindowLowerLeft t) (centeredWindowUpperRight y₂)
              (by rw [hll_re, hur_re]; norm_num)
              (by rw [hll_im, hur_im]; exact ht_le_y₂) s
            rw [Complex.mem_reProdIm, hll_re, hll_im, hur_re, hur_im,
              uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 3 / 2), uIcc_of_le ht_le_y₂] at hmem_rect
            have hedges := rectangleBoundaryPath_on_edges_local
              (centeredWindowLowerLeft t) (centeredWindowUpperRight y₂) s
            rw [hll_re, hll_im, hur_re, hur_im] at hedges
            by_cases hre_v : z.re = -1 / 2 ∨ z.re = 3 / 2
            · exact vertical_edge_ne_zero_of_outer_bdry N
                (burnolUnit_bdry_regular m (burnolPrefix_le_doorSqrtPrefix m)) hre_v
                (hy₁_lt_t.trans_le hmem_rect.2.1) (hmem_rect.2.2.trans_lt hy₂_lt_u) hs0
            · push Not at hre_v
              have hz_re_lo : -1 / 2 < z.re := lt_of_le_of_ne hmem_rect.1.1 (Ne.symm hre_v.1)
              have hz_re_hi : z.re < 3 / 2 := lt_of_le_of_ne hmem_rect.1.2 hre_v.2
              have hz_W : z ∈ (W_burnol m).Z :=
                (mem_centeredThetaWindow_iff (burnolUnitLower_le_upper m) N _ z).mpr
                  ⟨⟨hz_re_lo, hz_re_hi, hy₁_lt_t.trans_le hmem_rect.2.1,
                    hmem_rect.2.2.trans_lt hy₂_lt_u⟩, hs0⟩
              have him_edge : z.im = t ∨ z.im = y₂ := by
                rcases hedges with h | h | h | h
                · exact absurd h hre_v.1
                · exact absurd h hre_v.2
                · exact Or.inl h
                · exact Or.inr h
              apply ht_Y
              rw [Finset.mem_coe]
              refine Finset.mem_biUnion.mpr ⟨m, hm_mem, ?_⟩
              rcases him_edge with h1 | h2
              · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨z, hz_W, h1⟩))
              · refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨z, hz_W, ?_⟩))
                dsimp only [y₂] at h2; linarith only [h2]
          -- Step 2: Failure of `HasPlanckLogStageBesselCertificate` forces failure of `InCorridor`.
          let W_P := centeredThetaWindow ht_le_y₂ N hbdry_t
          set n_m : ℕ := logDoorStage c m
          have hn6 : (6 : ℝ) ≤ (n_m : ℝ) := six_le_logDoorStage_real c m
          have hnot_corr : ¬ W_P.InCorridor n_m (logStageMargin c m) := by
            intro hcorr
            apply hnot_cert
            refine ⟨hbdry_t, fun K hK u => ?_⟩
            have hη_pos : 0 < logStageMargin c m := by unfold logStageMargin; positivity
            have hη_half : logStageMargin c m ≤ 1 / 2 := by
              unfold logStageMargin
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hn6]
            rw [← centeredThetaWindow_degree ht_le_y₂ N hbdry_t] at hK
            have hpos := hcorr.besselSzegoCertificate_mul_loop_pos
              (eval_centeredThetaDifferencePoly_eq_window ht_le_y₂ N hbdry_t)
              hη_pos hη_half hK u
            have hE : (fun s => ‖W_P.expSum s‖ ^ 2) = fun s => ‖centeredThetaExpSum t y₂ N s‖ ^ 2 := by
              funext s; rw [centeredThetaWindow_expSum]
            rwa [hE] at hpos
          -- Step 3: Extract `z ∈ W_P.Z` outside the corridor and transfer to `w ∈ burnolUnitXiZeros m`.
          unfold ReflectedWindow.InCorridor at hnot_corr
          push Not at hnot_corr
          obtain ⟨z, hz_P, hz_out⟩ := hnot_corr
          obtain ⟨⟨hz_r0, hz_r1, hz_im1, hz_im2⟩, hz_zero⟩ :=
            (mem_centeredThetaWindow_iff ht_le_y₂ N hbdry_t z).mp hz_P
          have hz_re_gt : 1 / (8 * (n_m : ℝ)) < z.re - 1 / 2 := by
            rw [zhukovskyMajorAxis_logDoorStage, logStageMargin] at hz_out
            have hrhs : 1 / 2 - (1 / 2 - 1 / (2 * (n_m : ℝ))) - 1 / (4 * (n_m : ℝ)) =
                2 * (1 / (8 * (n_m : ℝ))) := by
              field_simp [(by positivity : (0 : ℝ) < (n_m : ℝ)).ne']; ring
            dsimp only [n_m] at hrhs ⊢
            linarith only [hz_out, hrhs]
          obtain ⟨w, hw_unit, hzw_dist⟩ := exists_xiZero_near_thetaZero m N
            (r := 1 / (16 * (n_m : ℝ))) (by positivity) (htail m hm₁_le N le_rfl)
            ⟨hz_r0, hz_r1, hy₁_lt_t.trans hz_im1, hz_im2.trans hy₂_lt_u⟩ hz_zero
          -- Step 4: Bound `(n_m : ℝ)` and locate `w ∈ B_ext`.
          set X_m : ℝ := ((m + 5 : ℕ) : ℝ)
          have hV_lt_X : V < X_m := by
            have h1 : X_m = (m : ℝ) + 5 := by dsimp only [X_m]; push_cast; rfl
            linarith only [h1, ht_lt_m1, ht_I.1]
          have hX_le_sq : X_m ≤ V ^ 2 := by
            have hm_2V : (m : ℝ) ≤ 2 * V := hm_le_t.trans ht_I.2
            have h1 : X_m = (m : ℝ) + 5 := by dsimp only [X_m]; push_cast; rfl
            nlinarith only [h1, hm_2V, hV32]
          have hlogX_lo : Real.log V ≤ Real.log X_m := Real.log_le_log hV_pos hV_lt_X.le
          have hlogX_hi : Real.log X_m ≤ 2 * Real.log V := by
            calc Real.log X_m ≤ Real.log (V ^ 2) :=
                  Real.log_le_log (by linarith only [hV_pos, hV_lt_X]) hX_le_sq
              _ = 2 * Real.log V := by rw [Real.log_pow]; push_cast; rfl
          have hn_lo : c * Real.log V ≤ (n_m : ℝ) := by
            calc c * Real.log V ≤ c * Real.log X_m := mul_le_mul_of_nonneg_left hlogX_lo hc.le
              _ ≤ (Nat.ceil (c * Real.log X_m) : ℝ) := Nat.le_ceil _
              _ ≤ (n_m : ℝ) := by exact_mod_cast (le_max_right 6 _)
          have hn_hi : (n_m : ℝ) ≤ 3 * c * Real.log V := by
            have h1 := logDoorStage_le c hc m
            have h7 : 7 ≤ c * Real.log V := by
              have hm := mul_le_mul_of_nonneg_left hlog7c hc.le
              rw [mul_add, mul_div_cancel₀ 7 hc.ne', mul_one] at hm
              linarith only [hm, hc]
            dsimp only [n_m, X_m] at h1 hlogX_hi ⊢
            nlinarith only [hc, h1, hlogX_hi, h7]
          have hrad_le_δ : 1 / (16 * (n_m : ℝ)) ≤ δ_im := by
            dsimp only [δ_im, A_c]
            have hrhs : 4 * (1 / (64 * c)) / Real.log V = 1 / (16 * (c * Real.log V)) := by
              field_simp [hc.ne', hlogV_pos.ne']; ring
            rw [hrhs]
            exact one_div_le_one_div_of_le (by positivity) (by linarith only [hn_lo])
          have hre_diff : |z.re - w.re| ≤ 1 / (16 * (n_m : ℝ)) :=
            (Complex.abs_re_le_norm (z - w)).trans (by simpa only [Complex.sub_re] using hzw_dist)
          have him_diff : |z.im - w.im| ≤ 1 / (16 * (n_m : ℝ)) :=
            (Complex.abs_im_le_norm (z - w)).trans (by simpa only [Complex.sub_im] using hzw_dist)
          have hw_re_ge : A_c / Real.log V ≤ |w.re - 1 / 2| := by
            have hw_gt : 1 / (16 * (n_m : ℝ)) ≤ w.re - 1 / 2 := by
              have h1 := (abs_le.mp hre_diff).2
              have h2 : 1 / (8 * (n_m : ℝ)) - 1 / (16 * (n_m : ℝ)) = 1 / (16 * (n_m : ℝ)) := by ring
              linarith only [hz_re_gt, h1, h2]
            have hAc_le : A_c / Real.log V ≤ 1 / (16 * (n_m : ℝ)) := by
              dsimp only [A_c]
              rw [div_le_div_iff₀ hlogV_pos (by positivity), one_mul]
              calc 1 / (64 * c) * (16 * (n_m : ℝ))
                  ≤ 1 / (64 * c) * (16 * (3 * c * Real.log V)) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left hn_hi (by norm_num)) (by positivity)
                _ = (3 / 4) * Real.log V := by field_simp [hc.ne']; ring
                _ ≤ Real.log V := by linarith only [hlogV_pos]
            exact hAc_le.trans (hw_gt.trans (le_abs_self _))
          obtain ⟨⟨hw0, hw1, _, _⟩, hw_xi⟩ := (mem_burnolUnitXiZeros_iff m w).mp hw_unit
          have hδ_le_1 : δ_im ≤ 1 := by
            dsimp only [δ_im]
            rw [div_le_one hlogV_pos]
            dsimp only [A_c] at hlog7c ⊢
            have h4Ac : 4 * (1 / (64 * c)) ≤ 7 / c := by
              rw [show 4 * (1 / (64 * c)) = (1 / 16) * (1 / c) by ring,
                show 7 / c = 7 * (1 / c) by ring]
              exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            exact h4Ac.trans ((le_add_of_nonneg_right zero_le_one).trans hlog7c)
          have him_le1 : |z.im - w.im| ≤ 1 := him_diff.trans (hrad_le_δ.trans hδ_le_1)
          have hy₂_le_2V1 : y₂ ≤ 2 * V + 1 := add_le_add ht_I.2 hB_div_le1
          have hw_im_lo : V - 4 < w.im := by
            have hd2 := (abs_le.mp him_le1).2
            linarith only [hd2, ht_I.1, hz_im1]
          have hw_im_hi : w.im ≤ 2 * V + 4 := by
            have hd1 := (abs_le.mp him_le1).1
            linarith only [hd1, hy₂_le_2V1, hz_im2]
          have hw_B : w ∈ B_ext := Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr
              ⟨_root_.RHTower.mem_stripFinsetPos.mpr
                ⟨hw0, hw1, by linarith only [hV32, hw_im_lo], hw_im_hi, hw_xi⟩, hw_im_lo⟩,
              hw_re_ge⟩
          refine Set.mem_biUnion hw_B ⟨?_, ?_⟩
          · have hwz : w.im - z.im ≤ δ_im :=
              (le_abs_self _).trans ((abs_sub_comm _ _).trans_le (him_diff.trans hrad_le_δ))
            have hz_sub : z.im - B / Real.log V ≤ t := sub_le_iff_le_add.mpr hz_im2.le
            calc w.im - B / Real.log V - δ_im
                = (w.im - z.im - δ_im) + (z.im - B / Real.log V) := by ring
              _ ≤ 0 + t := add_le_add (sub_nonpos.mpr hwz) hz_sub
              _ = t := zero_add t
          · have hzw : z.im - w.im ≤ δ_im := (le_abs_self _).trans (him_diff.trans hrad_le_δ)
            calc t ≤ z.im := hz_im1.le
              _ = w.im + (z.im - w.im) := by ring
              _ ≤ w.im + δ_im := add_le_add_right hzw w.im
      -- Step 5: `volume Y_fin = 0` and sum interval lengths over `B_ext`.
      have hvol_Y : volume (Y_fin : Set ℝ) = 0 := by
        have hsub_s : (Y_fin : Set ℝ) ⊆ ⋃ x ∈ Y_fin, Icc x x := by
          intro x hx; rw [Finset.mem_coe] at hx
          exact Set.mem_biUnion hx ⟨le_rfl, le_rfl⟩
        refine le_antisymm ((measure_mono hsub_s).trans ?_) zero_le
        refine (measure_biUnion_finset_le Y_fin _).trans ?_
        simp
      have hcard_B : (B_ext.card : ℝ) ≤ C_d * (Real.exp (-(r * A_c)) / A_c) * V * Real.log V := by
        have h1 : (B_ext.card : ℝ) ≤ ∑ z ∈ B_ext, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum]
          refine Finset.sum_le_sum fun z hz => ?_
          have hxi : _root_.RHTower.xi z = 0 :=
            (_root_.RHTower.mem_stripFinsetPos.mp
              (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2.2.2.2
          exact_mod_cast Nat.pos_of_ne_zero (_root_.RHTower.xi_order_toNat_ne_zero hxi)
        exact h1.trans (hV_d A_c hAc_gt2.le hAc_le_κ)
      have hlen_pos : 0 ≤ (B + 8 * A_c) / Real.log V := by positivity
      calc volume {t ∈ Icc V (2 * V) | ¬ HasPlanckLogStageBesselCertificate B V c t}
          ≤ volume ((Y_fin : Set ℝ) ∪
              ⋃ w ∈ B_ext, Icc (w.im - B / Real.log V - δ_im) (w.im + δ_im)) :=
            measure_mono hcov
        _ ≤ volume (Y_fin : Set ℝ) +
              volume (⋃ w ∈ B_ext, Icc (w.im - B / Real.log V - δ_im) (w.im + δ_im)) :=
            measure_union_le _ _
        _ = volume (⋃ w ∈ B_ext, Icc (w.im - B / Real.log V - δ_im) (w.im + δ_im)) := by
            rw [hvol_Y, zero_add]
        _ ≤ ∑ w ∈ B_ext, volume (Icc (w.im - B / Real.log V - δ_im) (w.im + δ_im)) :=
            measure_biUnion_finset_le B_ext _
        _ = ∑ _w ∈ B_ext, ENNReal.ofReal ((B + 8 * A_c) / Real.log V) := by
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [Real.volume_Icc]
            congr 1
            dsimp only [δ_im]; field_simp [hlogV_pos.ne']; ring
        _ = ENNReal.ofReal ((B_ext.card : ℝ) * ((B + 8 * A_c) / Real.log V)) := by
            rw [Finset.sum_const, nsmul_eq_mul,
              ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (C_d * (8 + 64 * B * c) * Real.exp (-(r / (64 * c))) * V) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc (B_ext.card : ℝ) * ((B + 8 * A_c) / Real.log V)
                ≤ (C_d * (Real.exp (-(r * A_c)) / A_c) * V * Real.log V) *
                    ((B + 8 * A_c) / Real.log V) :=
                  mul_le_mul_of_nonneg_right hcard_B hlen_pos
              _ = C_d * (8 + 64 * B * c) * Real.exp (-(r / (64 * c))) * V := by
                  dsimp only [A_c]
                  field_simp [hc.ne', hlogV_pos.ne']
                  ring
    · -- For `c ≥ 1 / 128`, `η c = 1` and `volume [V, 2V] = V`.
      have hη1 : η c = 1 := if_neg (fun h => hc_small h.2)
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with V _hV0
      rw [hη1, one_mul]
      calc volume {t ∈ Icc V (2 * V) | ¬ HasPlanckLogStageBesselCertificate B V c t}
          ≤ volume (Icc V (2 * V)) := measure_mono fun _ ht => ht.1
        _ = ENNReal.ofReal V := by rw [Real.volume_Icc, show 2 * V - V = V by ring]

/-- **Mesoscopic Window Zero-Free Push (`mesoscopicWindow_nearLine_zeroFree_volume_le`).**
Pushing `planckWindow_nearLine_zeroFree_volume_le` to the exponentially expanding mesoscopic
window width `min(1, e^{r A / 2} / log V)` preserves a vanishing log-free exceptional measure
`δ_r(A) * V` with `δ_r(A) → 0` as `A → +∞`. -/
theorem mesoscopicWindow_nearLine_zeroFree_volume_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C_r κ_r : ℝ, 0 < C_r ∧ 0 < κ_r ∧
      Tendsto (fun A : ℝ => C_r * (Real.exp (-(r * max A 2 / 2)) / max A 2)) atTop (nhds 0) ∧
      ∀ᶠ V : ℝ in atTop, ∀ A : ℝ, 2 ≤ A → A ≤ κ_r * Real.log V →
        volume {t ∈ Icc V (2 * V) |
          ∃ ρ : ℂ, _root_.RHTower.xi ρ = 0 ∧
            t ≤ ρ.im ∧ ρ.im ≤ t + min 1 (Real.exp (r * A / 2) / Real.log V) ∧
            A / Real.log V ≤ |ρ.re - 1 / 2|} ≤
          ENNReal.ofReal (C_r * (Real.exp (-(r * max A 2 / 2)) / max A 2) * V) := by
  obtain ⟨C_r, κ_r, hCr_pos, hκ_pos, hp_ev⟩ := planckWindow_nearLine_zeroFree_volume_le hr0 hr1
  refine ⟨C_r, κ_r, hCr_pos, hκ_pos, ?_, ?_⟩
  · -- `C_r * (e^{-r max(A, 2) / 2} / max(A, 2)) → 0` as `A → +∞`.
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    refine ⟨max 2 (C_r / ε + 1), fun A hA => ?_⟩
    have hA2 : 2 ≤ A := (le_max_left _ _).trans hA
    have hA_ε : C_r / ε + 1 ≤ A := (le_max_right _ _).trans hA
    rw [max_eq_left hA2, Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    have hexp1 : Real.exp (-(r * A / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hr0, hA2])
    have hle : C_r * (Real.exp (-(r * A / 2)) / A) ≤ C_r / A := by
      calc C_r * (Real.exp (-(r * A / 2)) / A) ≤ C_r * (1 / A) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hexp1 (by linarith only [hA2])) hCr_pos.le
        _ = C_r / A := by ring
    have hlt : C_r / A < ε := by
      rw [div_lt_iff₀ (by linarith only [hA2])]
      have hm := (div_lt_iff₀ hε).mp (lt_of_lt_of_le (lt_add_one _) hA_ε)
      linarith only [hm]
    exact hle.trans_lt hlt
  · filter_upwards [hp_ev, eventually_ge_atTop (16 : ℝ)] with V hVp hV16 A hA2 hA_hi
    have hV_pos : 0 < V := by linarith only [hV16]
    have hlogV_pos : 0 < Real.log V := Real.log_pos (by linarith only [hV16])
    set B : ℝ := min (Real.log V) (Real.exp (r * A / 2))
    have hB_pos : 0 < B := lt_min hlogV_pos (Real.exp_pos _)
    have hB_le_log : B ≤ Real.log V := min_le_left _ _
    have hB_le_exp : B ≤ Real.exp (r * A / 2) := min_le_right _ _
    have hmin_eq : min 1 (Real.exp (r * A / 2) / Real.log V) = B / Real.log V := by
      dsimp only [B]
      rcases le_total (Real.log V) (Real.exp (r * A / 2)) with hle | hge
      · rw [min_eq_left hle, div_self hlogV_pos.ne', min_eq_left ((one_le_div hlogV_pos).mpr hle)]
      · rw [min_eq_right hge, min_eq_right ((div_le_one hlogV_pos).mpr hge)]
    rw [hmin_eq, max_eq_left hA2]
    refine (hVp A B hA2 hA_hi hB_pos hB_le_log).trans (ENNReal.ofReal_le_ofReal ?_)
    calc C_r * B * (Real.exp (-(r * A)) / A) * V
        ≤ C_r * Real.exp (r * A / 2) * (Real.exp (-(r * A)) / A) * V :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hB_le_exp hCr_pos.le) (by positivity))
            hV_pos.le
      _ = C_r * (Real.exp (-(r * A / 2)) / A) * V := by
          have hexp_prod : Real.exp (r * A / 2) * Real.exp (-(r * A)) =
              Real.exp (-(r * A / 2)) := by
            rw [← Real.exp_add]; congr 1; ring
          calc C_r * Real.exp (r * A / 2) * (Real.exp (-(r * A)) / A) * V
              = C_r * ((Real.exp (r * A / 2) * Real.exp (-(r * A))) / A) * V := by ring
            _ = C_r * (Real.exp (-(r * A / 2)) / A) * V := by rw [hexp_prod]

/-- Local vertical Planck shadow of deep `ξ`-zeros inside the `m`-th Burnol unit window. -/
def planckShadowSet (m : ℕ) (A B V : ℝ) : Set ℝ :=
  ⋃ ρ ∈ (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|),
    Icc (ρ.im - B / Real.log V) ρ.im

/-- Real Lebesgue measure of the local vertical Planck shadow on the `m`-th Burnol unit window. -/
def planckShadow (m : ℕ) (A B V : ℝ) : ℝ :=
  (volume (planckShadowSet m A B V)).toReal

lemma planckShadow_nonneg (m : ℕ) (A B V : ℝ) : 0 ≤ planckShadow m A B V :=
  ENNReal.toReal_nonneg

lemma planckShadow_le_deepOrderSum_mul (m : ℕ) (A : ℝ) {B V : ℝ}
    (hB : 0 ≤ B) (hlogV : 0 < Real.log V) :
    planckShadow m A B V ≤ burnolDeepOrderSum m A V * (B / Real.log V) := by
  set F := (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|)
  have hvol_le : volume (planckShadowSet m A B V) ≤
      ENNReal.ofReal ((F.card : ℝ) * (B / Real.log V)) := by
    calc volume (planckShadowSet m A B V)
        ≤ ∑ ρ ∈ F, volume (Icc (ρ.im - B / Real.log V) ρ.im) := measure_biUnion_finset_le F _
      _ = ∑ _ρ ∈ F, ENNReal.ofReal (B / Real.log V) := by
          refine Finset.sum_congr rfl fun ρ _ => ?_
          rw [Real.volume_Icc, show ρ.im - (ρ.im - B / Real.log V) = B / Real.log V by ring]
      _ = ENNReal.ofReal ((F.card : ℝ) * (B / Real.log V)) := by
          rw [Finset.sum_const, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have htoReal : planckShadow m A B V ≤ (F.card : ℝ) * (B / Real.log V) := by
    unfold planckShadow
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol_le).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hcard_le : (F.card : ℝ) ≤ burnolDeepOrderSum m A V := by
    unfold burnolDeepOrderSum
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have hxi := ((mem_burnolUnitXiZeros_iff m ρ).mp (Finset.mem_filter.mp hρ).1).2
    exact_mod_cast Nat.pos_of_ne_zero (_root_.RHTower.xi_order_toNat_ne_zero hxi)
  exact htoReal.trans (mul_le_mul_of_nonneg_right hcard_le (by positivity))

/-- `planckShadow m A B V` is strictly positive iff `burnolUnitXiZeros m` has a zero beyond `A / log V`. -/
theorem planckShadow_pos_iff (m : ℕ) (A : ℝ) {B V : ℝ} (hB : 0 < B) (hlogV : 0 < Real.log V) :
    0 < planckShadow m A B V ↔
      ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2| := by
  set F := (burnolUnitXiZeros m).filter (fun ρ => A / Real.log V ≤ |ρ.re - 1 / 2|)
  constructor
  · intro hpos
    by_contra hnone
    have hempty : F = ∅ := by
      ext ρ; simp only [F, Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2⟩; exact hnone ⟨ρ, h1, h2⟩
    have hset : planckShadowSet m A B V = ∅ := by
      unfold planckShadowSet; change (⋃ ρ ∈ F, _) = ∅; simp [hempty]
    unfold planckShadow at hpos
    rw [hset, measure_empty, ENNReal.toReal_zero] at hpos
    exact lt_irrefl 0 hpos
  · rintro ⟨ρ₀, hρ₀_Z, hρ₀_re⟩
    have hρ₀_F : ρ₀ ∈ F := Finset.mem_filter.mpr ⟨hρ₀_Z, hρ₀_re⟩
    have hvol_fin : volume (planckShadowSet m A B V) ≠ ⊤ := by
      have hvol_le : volume (planckShadowSet m A B V) ≤
          ENNReal.ofReal ((F.card : ℝ) * (B / Real.log V)) := by
        calc volume (planckShadowSet m A B V)
            ≤ ∑ ρ ∈ F, volume (Icc (ρ.im - B / Real.log V) ρ.im) := measure_biUnion_finset_le F _
          _ = ∑ _ρ ∈ F, ENNReal.ofReal (B / Real.log V) := by
              refine Finset.sum_congr rfl fun ρ _ => ?_
              rw [Real.volume_Icc, show ρ.im - (ρ.im - B / Real.log V) = B / Real.log V by ring]
          _ = ENNReal.ofReal ((F.card : ℝ) * (B / Real.log V)) := by
              rw [Finset.sum_const, nsmul_eq_mul,
                ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol_le
    have hsub : Icc (ρ₀.im - B / Real.log V) ρ₀.im ⊆ planckShadowSet m A B V :=
      fun _ hx => Set.mem_biUnion hρ₀_F hx
    have hlo : B / Real.log V ≤ planckShadow m A B V := by
      unfold planckShadow
      calc B / Real.log V
          = (ENNReal.ofReal (B / Real.log V)).toReal :=
            (ENNReal.toReal_ofReal (by positivity)).symm
        _ = (volume (Icc (ρ₀.im - B / Real.log V) ρ₀.im)).toReal := by
            rw [Real.volume_Icc, show ρ₀.im - (ρ₀.im - B / Real.log V) = B / Real.log V by ring]
        _ ≤ (volume (planckShadowSet m A B V)).toReal :=
            ENNReal.toReal_mono hvol_fin (measure_mono hsub)
    exact (div_pos hB hlogV).trans_le hlo

/-- **Unconditional Unit-Window Planck-Shadow Sum (`unitWindow_planckShadow_sum_le`).**
Summing `planckShadow m A B V` across `m ∈ [⌈V⌉, ⌊2V⌋]` cancels `log V` identically via bounded
unit-window overlap, giving `≤ 8 * C_d * B * (e^{-r A} / A) * V` and bounding thick-shadow unit
windows (`planckShadow m A 1 V ≥ e^{-r A / 2}`) by `8 * C_d * (e^{-r A / 2} / A) * V`. -/
theorem unitWindow_planckShadow_sum_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C_d κ_r : ℝ, 0 < C_d ∧ 0 < κ_r ∧ ∀ᶠ V : ℝ in atTop,
      ∀ A B : ℝ, 2 ≤ A → A ≤ κ_r * Real.log V → 0 < B → B ≤ Real.log V →
        (∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)), planckShadow m A B V ≤
          8 * C_d * B * (Real.exp (-(r * A)) / A) * V) ∧
        (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
            (fun m => Real.exp (-(r * A / 2)) ≤ planckShadow m A 1 V)).card : ℝ) ≤
          8 * C_d * (Real.exp (-(r * A / 2)) / A) * V := by
  obtain ⟨C_d, κ_r, hCd_pos, hκ_pos, hd_ev⟩ := deepExtendedShell_orderSum_le hr0 hr1
  refine ⟨C_d, κ_r, hCd_pos, hκ_pos, ?_⟩
  filter_upwards [hd_ev, eventually_ge_atTop (16 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with V hV_d hV16 hlog2 A B hA2 hA_hi hB_pos hB_hi
  have hV_pos : 0 < V := by linarith only [hV16]
  have hlogV_pos : 0 < Real.log V := by linarith only [hlog2]
  set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
  have hsum_bound : ∀ B' : ℝ, 0 < B' →
      ∑ m ∈ I_V, planckShadow m A B' V ≤ 8 * C_d * B' * (Real.exp (-(r * A)) / A) * V := by
    intro B' hB'_pos
    have h1 : ∑ m ∈ I_V, planckShadow m A B' V ≤
        (∑ m ∈ I_V, burnolDeepOrderSum m A V) * (B' / Real.log V) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun m _ => planckShadow_le_deepOrderSum_mul m A hB'_pos.le hlogV_pos
    have h2 : ∑ m ∈ I_V, burnolDeepOrderSum m A V ≤
        8 * (C_d * (Real.exp (-(r * A)) / A) * V * Real.log V) :=
      (sum_burnolDeepOrderSum_le_eight_mul_extendedShell hV16).trans
        (mul_le_mul_of_nonneg_left (hV_d A hA2 hA_hi) (by norm_num))
    calc ∑ m ∈ I_V, planckShadow m A B' V
        ≤ (8 * (C_d * (Real.exp (-(r * A)) / A) * V * Real.log V)) * (B' / Real.log V) :=
          h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
      _ = 8 * C_d * B' * (Real.exp (-(r * A)) / A) * V := by
          field_simp [hlogV_pos.ne']
  refine ⟨hsum_bound B hB_pos, ?_⟩
  set Thick := I_V.filter (fun m => Real.exp (-(r * A / 2)) ≤ planckShadow m A 1 V)
  have h1_sum := hsum_bound 1 zero_lt_one
  have hmarkov : (Thick.card : ℝ) * Real.exp (-(r * A / 2)) ≤
      8 * C_d * 1 * (Real.exp (-(r * A)) / A) * V := by
    calc (Thick.card : ℝ) * Real.exp (-(r * A / 2))
        = ∑ _m ∈ Thick, Real.exp (-(r * A / 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Thick, planckShadow m A 1 V :=
          Finset.sum_le_sum fun m hm => (Finset.mem_filter.mp hm).2
      _ ≤ ∑ m ∈ I_V, planckShadow m A 1 V :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => planckShadow_nonneg m A 1 V
      _ ≤ 8 * C_d * 1 * (Real.exp (-(r * A)) / A) * V := h1_sum
  have hexp_pos : 0 < Real.exp (-(r * A / 2)) := Real.exp_pos _
  have hdiv := (le_div_iff₀ hexp_pos).mpr hmarkov
  refine hdiv.trans_eq ?_
  have hexp_eq : Real.exp (-(r * A)) / Real.exp (-(r * A / 2)) = Real.exp (-(r * A / 2)) := by
    rw [← Real.exp_sub]; congr 1; ring
  calc 8 * C_d * 1 * (Real.exp (-(r * A)) / A) * V / Real.exp (-(r * A / 2))
      = 8 * C_d * ((Real.exp (-(r * A)) / Real.exp (-(r * A / 2))) / A) * V := by ring
    _ = 8 * C_d * (Real.exp (-(r * A / 2)) / A) * V := by rw [hexp_eq]

/-- **Vertical Planck-Shadow Equivalence for Unit-Window Occupancy (`logFreeNearLineWindowOccupancy_iff_thinPlanckShadow`).**
Because thick-shadow windows (`planckShadow m A 1 V ≥ e^{-r A / 2}`) are unconditionally
`O_r((e^{-r A / 2} / A) V) = o_{A → ∞}(V)`, `LogFreeNearLineWindowOccupancy` holds if and only if
the count of unit windows with vertically thin non-empty Planck shadows
`0 < planckShadow m A 1 V < e^{-r A / 2}` is `o_{A → ∞}(V)`. -/
theorem logFreeNearLineWindowOccupancy_iff_thinPlanckShadow {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    LogFreeNearLineWindowOccupancy ↔
      ∃ η : ℝ → ℝ, Tendsto η atTop (nhds 0) ∧
        ∀ A : ℝ, 2 ≤ A → ∀ᶠ V : ℝ in atTop,
          (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
            (fun m => 0 < planckShadow m A 1 V ∧
              planckShadow m A 1 V < Real.exp (-(r * A / 2)))).card : ℝ) ≤ η A * V := by
  constructor
  · rintro ⟨δ, hδ_lim, hδ_ev⟩
    refine ⟨δ, hδ_lim, fun A hA2 => ?_⟩
    filter_upwards [hδ_ev A (by linarith only [hA2]), eventually_ge_atTop (16 : ℝ)] with V hV_occ hV16
    have hlogV_pos : 0 < Real.log V := Real.log_pos (by linarith only [hV16])
    set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
    have hsub : I_V.filter (fun m => 0 < planckShadow m A 1 V ∧
        planckShadow m A 1 V < Real.exp (-(r * A / 2))) ⊆
        I_V.filter (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|) := by
      intro m hm
      obtain ⟨hm_I, hpos, _⟩ := Finset.mem_filter.mp hm
      exact Finset.mem_filter.mpr ⟨hm_I, (planckShadow_pos_iff m A zero_lt_one hlogV_pos).mp hpos⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hV_occ
  · rintro ⟨η, hη_lim, hη_ev⟩
    obtain ⟨C_d, κ_r, hCd_pos, hκ_pos, hsh_ev⟩ := unitWindow_planckShadow_sum_le hr0 hr1
    let δ : ℝ → ℝ := fun A =>
      if 2 ≤ A then |η A| + 8 * C_d * (Real.exp (-(r * A / 2)) / A) else 3
    refine ⟨δ, ?_, fun A hA_pos => ?_⟩
    · -- `δ(A) → 0` as `A → +∞`.
      have h1 : Tendsto (fun A => |η A|) atTop (nhds 0) := by
        simpa using hη_lim.abs
      have h2 : Tendsto (fun A : ℝ => 8 * C_d * (Real.exp (-(r * A / 2)) / A)) atTop (nhds 0) := by
        refine Metric.tendsto_atTop.mpr fun ε hε => ?_
        refine ⟨max 2 (8 * C_d / ε + 1), fun A hA => ?_⟩
        have hA2 : 2 ≤ A := (le_max_left _ _).trans hA
        have hA_ε : 8 * C_d / ε + 1 ≤ A := (le_max_right _ _).trans hA
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
        have hexp1 : Real.exp (-(r * A / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hr0, hA2])
        have hle : 8 * C_d * (Real.exp (-(r * A / 2)) / A) ≤ 8 * C_d / A := by
          calc 8 * C_d * (Real.exp (-(r * A / 2)) / A) ≤ 8 * C_d * (1 / A) :=
                mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hexp1 (by linarith only [hA2]))
                  (by positivity)
            _ = 8 * C_d / A := by ring
        have hlt : 8 * C_d / A < ε := by
          rw [div_lt_iff₀ (by linarith only [hA2])]
          have hm := (div_lt_iff₀ hε).mp (lt_of_lt_of_le (lt_add_one _) hA_ε)
          linarith only [hm]
        exact hle.trans_lt hlt
      have hsum_lim : Tendsto (fun A => |η A| + 8 * C_d * (Real.exp (-(r * A / 2)) / A))
          atTop (nhds 0) := by simpa using h1.add h2
      refine hsum_lim.congr' ?_
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with A hA2
      exact (if_pos hA2).symm
    · by_cases hA2 : 2 ≤ A
      · have hδ_eq : δ A = |η A| + 8 * C_d * (Real.exp (-(r * A / 2)) / A) := if_pos hA2
        rw [hδ_eq]
        filter_upwards [hη_ev A hA2, hsh_ev, eventually_ge_atTop (16 : ℝ),
          Real.tendsto_log_atTop.eventually_ge_atTop (max 2 (A / κ_r))]
          with V hV_thin hV_sh hV16 hlog_lo
        have hV_pos : 0 < V := by linarith only [hV16]
        have hlog2 : 2 ≤ Real.log V := (le_max_left _ _).trans hlog_lo
        have hlogA : A / κ_r ≤ Real.log V := (le_max_right _ _).trans hlog_lo
        have hlogV_pos : 0 < Real.log V := by linarith only [hlog2]
        have hA_hi : A ≤ κ_r * Real.log V := by
          have hm := mul_le_mul_of_nonneg_left hlogA hκ_pos.le
          rwa [mul_div_cancel₀ _ hκ_pos.ne'] at hm
        have hthick := (hV_sh A 1 hA2 hA_hi zero_lt_one (by linarith only [hlog2])).2
        set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
        set Bad := I_V.filter (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)
        set Thin := I_V.filter (fun m => 0 < planckShadow m A 1 V ∧
          planckShadow m A 1 V < Real.exp (-(r * A / 2)))
        set Thick := I_V.filter (fun m => Real.exp (-(r * A / 2)) ≤ planckShadow m A 1 V)
        have hcov : Bad ⊆ Thin ∪ Thick := by
          intro m hm
          obtain ⟨hm_I, hex⟩ := Finset.mem_filter.mp hm
          have hpos := (planckShadow_pos_iff m A zero_lt_one hlogV_pos).mpr hex
          rcases lt_or_ge (planckShadow m A 1 V) (Real.exp (-(r * A / 2))) with hlt | hge
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hm_I, hpos, hlt⟩))
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hm_I, hge⟩))
        have hcard_le : (Bad.card : ℝ) ≤ (Thin.card : ℝ) + (Thick.card : ℝ) := by
          exact_mod_cast (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
        have hthin_abs : (Thin.card : ℝ) ≤ |η A| * V :=
          hV_thin.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hV_pos.le)
        calc (Bad.card : ℝ) ≤ (Thin.card : ℝ) + (Thick.card : ℝ) := hcard_le
          _ ≤ |η A| * V + 8 * C_d * (Real.exp (-(r * A / 2)) / A) * V :=
              add_le_add hthin_abs hthick
          _ = (|η A| + 8 * C_d * (Real.exp (-(r * A / 2)) / A)) * V := by ring
      · -- For `0 < A < 2`, `δ A = 3` and `#I_V ≤ 2 V ≤ 3 V`.
        have hδ_eq : δ A = 3 := if_neg hA2
        rw [hδ_eq]
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with V hV1
        set I_V := Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))
        have hc1 : 1 ≤ Nat.ceil V := Nat.one_le_iff_ne_zero.mpr (by
          intro h0; have := Nat.ceil_eq_zero.mp h0; linarith only [this, hV1])
        have hcard_I : (I_V.card : ℝ) ≤ 2 * V := by
          have h1 : I_V.card ≤ Nat.floor (2 * V) := by rw [Nat.card_Icc]; omega
          exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
        have hsub : (I_V.filter (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)).card ≤
            I_V.card := Finset.card_filter_le _ _
        have hsub_R : ((I_V.filter (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)).card : ℝ) ≤
            (I_V.card : ℝ) := by exact_mod_cast hsub
        linarith only [hsub_R, hcard_I, hV1]

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

end

section AxiomAudit
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
#print axioms burnolDeepOrderSum_le_logV
#print axioms perWindow_deepOrderSum_rpow_le_selberg
#print axioms perWindow_deepOrderSum_sq_le_selberg
#print axioms perWindow_deepOrderSum_sq_doubleLog_le
#print axioms clusteredModel_sqMoment_lower_bound
#print axioms exists_logSpacingModel_zeroDensity_not_linearSqMoment
#print axioms logFreeNearLineZeroDensity_iff_windowOccupancy_and_clusterTail
#print axioms logFreeNearLineZeroDensity_of_windowOccupancy_and_growingSqMoment
#print axioms sparseModel_uniformPlanckVolume_not_windowOccupancy
#print axioms almostAll_planckWindow_logStage_besselSzegoCertificate
#print axioms mesoscopicWindow_nearLine_zeroFree_volume_le
#print axioms planckShadow_pos_iff
#print axioms unitWindow_planckShadow_sum_le
#print axioms logFreeNearLineWindowOccupancy_iff_thinPlanckShadow
end AxiomAudit

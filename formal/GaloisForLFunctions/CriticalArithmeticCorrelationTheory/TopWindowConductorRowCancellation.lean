import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.FiniteConductorCollarReductionAndPolarDecoupling

/-!
# Top-Window Conductor Row Cancellation and Critical-Band Uniformity

For a fixed critical ratio `c⁸ ≍ log N` and a low conductor `2 ≤ m ≤ m₀`, the dual seventh-power
bound `topCollarDualSeventhMass M N r_m / E_m(c) = O(R² m⁻⁵)` does not decay at fixed `m`. This
module resolves `1 ≤ m ≤ m₀` on the top collar `Ioc M N` without assuming smooth test vectors:

1. **Compactness lift from critical curves to critical bands** (`eventually_uniform_critical_band_of_curve`)
   upgrades any curvewise property along `c_N⁸ / log N → R ∈ [R₀, R_max]` to hold uniformly across
   `R₀ log N ≤ c⁸ ≤ R_max log N`, yielding all-ratio low-packet coercivity
   (`eventually_uniform_low_packet_energy_ge`) and uniform signed polar approximation
   (`eventually_uniform_low_packet_signed_approx`).
2. **Truncated collar dual seventh-power bound** (`exists_truncated_dualSeventh_conductor_residual`)
   gains a factor `δ` on `Ioc M ⌊δ N⌋₊` (`0 ≤ δ ≤ 1`) for every `m ≥ 1`, using `(n / N)⁷ ≤ δ` on bulk
   `ℓ²` channels and `(Ioc M ⌊δ N⌋₊).card ≤ δ N` on the upward prime shells.
3. **Nonpolar top-window `ℓ²` row cancellation** (`eventually_uniform_nonpolar_topWindow_norm_sq`):
   for every `m ≥ 2` and `0 < δ < 1`, `(log N / c²) ∑_{n ∈ Ioc ⌊δ N⌋₊ N} (r_m)_n² → 0` uniformly on
   `R₀ log N ≤ c⁸ ≤ R_max log N`. Zero-mean Ramanujan periodicity cancels the near-Gamma, separated
   cross, harmonic-collar, and upward prime shells row by row, while the divisor-jet pole component
   `(Λ(m) / √φ(m)) nearPoleRow` cancels the center pole harmonic sum `lagHarmonic m N → -Λ(m)` up to
   `poleRowDefect` (`O(1 + log c) = o(c²)`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticElectrostatics
  ArithmeticHodgeTheoryOfDegenerations
  BezoutValuationIncidence
  CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis
  SuccessorShellArithmetic

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Section 1: Critical-Band Compactness Lift and All-Ratio Low-Packet Coercivity -/

/-- Extending a convergent subsequence along `s : ℕ → ℕ` (`StrictMono s`) by a convergent default
sequence preserves the `atTop` limit. -/
private theorem tendsto_extend_along_strictMono {s : ℕ → ℕ} (hs : StrictMono s)
    {a d : ℕ → ℝ} {R : ℝ} (ha : Tendsto a atTop (𝓝 R)) (hd : Tendsto d atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => if h : ∃ i : ℕ, s i = N then a h.choose else d N) atTop (𝓝 R) := by
  rw [Metric.tendsto_atTop] at ha hd ⊢
  intro ε hε
  obtain ⟨I₀, hI₀⟩ := ha ε hε
  obtain ⟨N₀, hN₀⟩ := hd ε hε
  refine ⟨max N₀ (s I₀), fun N hN => ?_⟩
  by_cases hex : ∃ i : ℕ, s i = N
  · rw [dif_pos hex]
    have hsi : s hex.choose = N := hex.choose_spec
    have hi : I₀ ≤ hex.choose := by
      by_contra hlt
      have hss : s hex.choose < s I₀ := hs (lt_of_not_ge hlt)
      have hge : s I₀ ≤ N := (le_max_right N₀ (s I₀)).trans hN
      omega
    exact hI₀ hex.choose hi
  · rw [dif_neg hex]
    exact hN₀ N ((le_max_left N₀ (s I₀)).trans hN)

/-- Default critical-curve sequence `(R * log N)^{1/8}` clamped below at `1`. -/
private theorem tendsto_default_critical_curve {R : ℝ} (hR : 0 < R) :
    Tendsto (fun N : ℕ => (max (1 : ℝ) ((R * Real.log (N : ℝ)) ^ (1 / 8 : ℝ))) ^ 8 /
        Real.log (N : ℝ)) atTop (𝓝 R) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun N : ℕ => R * Real.log (N : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hR hlog
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hlog.eventually_gt_atTop 0, hprod.eventually_ge_atTop 1] with N hL0 hRL1
  have h1 : (1 : ℝ) ≤ (R * Real.log (N : ℝ)) ^ (1 / 8 : ℝ) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow zero_le_one hRL1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
  rw [max_eq_right h1, ← Real.rpow_natCast _ 8,
    ← Real.rpow_mul (mul_nonneg hR.le hL0.le)]
  norm_num [Real.rpow_one]
  exact (mul_div_cancel_right₀ R hL0.ne').symm

/-- **Compactness lift from critical curves to critical bands.**
If `P N (c N)` holds eventually along every critical curve `1 ≤ c N` with `c N ^ 8 / log N → R`
for `R ∈ [R₀, R_max]` (`0 < R₀ ≤ R_max`), then `P N c` holds eventually in `N` uniformly across all
`1 ≤ c` with `R₀ * log N ≤ c ^ 8 ≤ R_max * log N`. -/
theorem eventually_uniform_critical_band_of_curve {P : ℕ → ℝ → Prop} {R₀ R_max : ℝ}
    (hR₀ : 0 < R₀) (_hR_le : R₀ ≤ R_max)
    (hcurve : ∀ R ∈ Set.Icc R₀ R_max, ∀ c : ℕ → ℝ, (∀ N, 1 ≤ c N) →
      Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R) →
      ∀ᶠ N : ℕ in atTop, P N (c N)) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      R₀ * Real.log (N : ℝ) ≤ c ^ 8 → c ^ 8 ≤ R_max * Real.log (N : ℝ) → P N c := by
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  have hfreq : ∃ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) ∧
      ∃ c : ℝ, 1 ≤ c ∧ R₀ * Real.log (N : ℝ) ≤ c ^ 8 ∧
        c ^ 8 ≤ R_max * Real.log (N : ℝ) ∧ ¬ P N c := by
    refine hnot.mp ?_
    filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with N hL1 hbad
    push Not at hbad
    exact ⟨hL1, hbad⟩
  obtain ⟨k, hk_mono, hk_bad⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose c_bad hc1 hlo hhi hfail using fun j => (hk_bad j).2
  have hmem : ∀ j : ℕ, c_bad j ^ 8 / Real.log (k j : ℝ) ∈ Set.Icc R₀ R_max := fun j => by
    have hL0 : 0 < Real.log (k j : ℝ) := zero_lt_one.trans_le (hk_bad j).1
    exact ⟨(le_div_iff₀ hL0).mpr (hlo j), (div_le_iff₀ hL0).mpr (hhi j)⟩
  obtain ⟨R, hR_mem, φ, hφ_mono, hφ_lim⟩ := isCompact_Icc.tendsto_subseq hmem
  have hR_pos : 0 < R := hR₀.trans_le hR_mem.1
  let s : ℕ → ℕ := k ∘ φ
  have hs_mono : StrictMono s := hk_mono.comp hφ_mono
  let d : ℕ → ℝ := fun N => max (1 : ℝ) ((R * Real.log (N : ℝ)) ^ (1 / 8 : ℝ))
  let c_ext : ℕ → ℝ := fun N => if h : ∃ i : ℕ, s i = N then c_bad (φ h.choose) else d N
  have hc_ext1 : ∀ N : ℕ, 1 ≤ c_ext N := fun N => by
    dsimp only [c_ext]
    split_ifs with hex
    · exact hc1 (φ hex.choose)
    · exact le_max_left _ _
  have hc_ext_val : ∀ i : ℕ, c_ext (s i) = c_bad (φ i) := fun i => by
    have hex : ∃ j : ℕ, s j = s i := ⟨i, rfl⟩
    dsimp only [c_ext]
    rw [dif_pos hex, hs_mono.injective hex.choose_spec]
  have hcrit : Tendsto (fun N : ℕ => c_ext N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R) := by
    have heq : (fun N : ℕ => c_ext N ^ 8 / Real.log (N : ℝ)) =
        fun N : ℕ => if h : ∃ i : ℕ, s i = N then
          c_bad (φ h.choose) ^ 8 / Real.log (s h.choose : ℝ)
        else d N ^ 8 / Real.log (N : ℝ) := by
      ext N; dsimp only [c_ext]; split_ifs with hex
      · rw [hex.choose_spec]
      · rfl
    rw [heq]
    exact tendsto_extend_along_strictMono hs_mono hφ_lim (tendsto_default_critical_curve hR_pos)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hcurve R hR_mem c_ext hc_ext1 hcrit)
  have hgood := hN₁ (s N₁) (hs_mono.id_le N₁)
  rw [hc_ext_val N₁] at hgood
  exact hfail (φ N₁) hgood

/-- **Uniform signed polar approximation on any positive critical band.**
Across `R₀ * log N ≤ c ^ 8 ≤ R_max * log N` (`0 < R₀ ≤ R_max`), `completeWeilMatrix` on the low
packet `Q₁ = ⌊(log N)^{13/32}⌋₊` equals `∑ E_m(c) b_m² + tiltedPolarFinitePart * (c / log N) * b₁²`
up to relative error `ε`. -/
theorem eventually_uniform_low_packet_signed_approx {R₀ R_max ε : ℝ}
    (hR₀ : 0 < R₀) (hR_le : R₀ ≤ R_max) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      R₀ * Real.log (N : ℝ) ≤ c ^ 8 → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
      ∀ b : ℕ → ℝ,
        let Q := ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊
        let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
        |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) y, y⟫ -
          (∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline c m * b m ^ 2) -
          tiltedPolarFinitePart * (c / Real.log (N : ℝ)) * b 1 ^ 2| ≤
          ε * ∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline c m * b m ^ 2 :=
  eventually_uniform_critical_band_of_curve hR₀ hR_le fun _R hR _c hc hcrit =>
    eventually_completeWeil_low_packet_signed_approx hc (hR₀.trans_le hR.1) hcrit hε

/-- **All-ratio low-packet coercivity up to any critical ceiling.**
For every `R_max`, eventually in `N` and uniformly across all `1 ≤ c` with `c ^ 8 ≤ R_max * log N`,
`completeWeilMatrix tiltedUnitSpline c N` retains at least one-quarter of the completed conductor
energy on the entire low packet `Q₁ = ⌊(log N)^{13/32}⌋₊` (including `m = 1`). -/
theorem eventually_uniform_low_packet_energy_ge (R_max : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
      ∀ b : ℕ → ℝ,
        let Q := ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊
        let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
        (1 / 4 : ℝ) * ∑ m ∈ Icc 1 Q,
          completedConductorEnergy tiltedUnitSpline c m * b m ^ 2 ≤
          ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) y, y⟫ := by
  obtain ⟨K₁, hK₁_pos, _, hlow_ev⟩ :=
    exists_critical_multiple_low_packet_and_collar_budget zero_lt_one
  set R₀ : ℝ := (2 * K₁) ^ 8
  have hR₀_pos : 0 < R₀ := by dsimp only [R₀]; positivity
  set R_hi : ℝ := max R₀ R_max
  have hband_ev := eventually_uniform_critical_band_of_curve hR₀_pos (le_max_left R₀ R_max)
    (P := fun N c => ∀ b : ℕ → ℝ,
      let Q := ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊
      let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
      (1 / 2 : ℝ) * ∑ m ∈ Icc 1 Q,
        completedConductorEnergy tiltedUnitSpline c m * b m ^ 2 ≤
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) y, y⟫)
    fun _R hR _c hc hcrit =>
      eventually_completeWeil_low_packet_energy_ge hc (hR₀_pos.trans_le hR.1) hcrit
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlow_ev, hband_ev, hlog.eventually_ge_atTop 1] with N hlow hband hL1
  intro c hc1 hc_max b Q y
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hS0 : 0 ≤ ∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline c m * b m ^ 2 :=
    sum_nonneg fun m hm =>
      mul_nonneg (completedConductorEnergy_tilted_pos hc0 (mem_Icc.mp hm).1).le (sq_nonneg _)
  by_cases hsmall : c ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ)
  · have hsf := (hlow c hc1 hsmall).1 b
    have hfloor_nn : 0 ≤ (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖y‖ ^ 2 :=
      mul_nonneg (div_nonneg tiltedSplineSpectralFloorConstant_pos.le (by positivity)) (sq_nonneg _)
    have hid := spectralFloorWeilMatrix_inner c y
    unfold completeWeilEnergy at hid
    linarith only [hsf, hid, hfloor_nn]
  · push Not at hsmall
    have hc8_lo : R₀ * Real.log (N : ℝ) ≤ c ^ 8 := by
      have hp := pow_le_pow_left₀ (by positivity) hsmall.le 8
      rw [mul_pow, ← Real.rpow_natCast (Real.log (N : ℝ) ^ (1 / 8 : ℝ)) 8,
        ← Real.rpow_mul hL0.le] at hp
      norm_num [Real.rpow_one] at hp
      exact hp
    have hc8_hi : c ^ 8 ≤ R_hi * Real.log (N : ℝ) :=
      hc_max.trans (mul_le_mul_of_nonneg_right (le_max_right R₀ R_max) hL0.le)
    have hhalf := hband c hc1 hc8_lo hc8_hi b
    linarith only [hhalf, hS0]

/-! ## Section 2: Truncated Collar Dual Seventh-Power Residual (`Ioc M ⌊δ N⌋₊`) -/

/-- Dual seventh-power mass on the truncated collar `Ioc M U`. -/
def truncatedCollarDualSeventhMass (M U N : ℕ) (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) : ℝ :=
  ∑ n ∈ Ioc M U, ((n : ℝ) / N) ^ 7 * primeHorizonExtension u n ^ 2

theorem truncatedCollarDualSeventhMass_nonneg (M U N : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    0 ≤ truncatedCollarDualSeventhMass M U N u :=
  sum_nonneg fun _ _ => mul_nonneg (by positivity) (sq_nonneg _)

theorem truncatedCollarDualSeventhMass_smul (M U N : ℕ) (a : ℝ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    truncatedCollarDualSeventhMass M U N (a • u) =
      a ^ 2 * truncatedCollarDualSeventhMass M U N u := by
  unfold truncatedCollarDualSeventhMass
  rw [mul_sum]
  refine sum_congr rfl fun n _ => ?_
  by_cases hnI : n ∈ Icc 1 N
  · let idx : PrimeHorizonIndex N := ⟨n, hnI⟩
    have h1 : primeHorizonExtension (a • u) n = a * primeHorizonExtension u n := by
      change primeHorizonExtension (a • u) idx.1 = a * primeHorizonExtension u idx.1
      rw [primeHorizonExtension_coe, primeHorizonExtension_coe]; rfl
    rw [h1]; ring
  · simp [primeHorizonExtension, hnI]

theorem truncatedCollarDualSeventhMass_neg (M U N : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    truncatedCollarDualSeventhMass M U N (-u) = truncatedCollarDualSeventhMass M U N u := by
  rw [show (-u) = (-1 : ℝ) • u by simp, truncatedCollarDualSeventhMass_smul]; ring

/-- On `Ioc M ⌊δ N⌋₊` (`0 ≤ δ ≤ 1`), `(n / N)⁷ ≤ δ`, so `truncatedCollarDualSeventhMass` gains a
factor `δ` over `‖u‖²`. -/
theorem truncatedCollarDualSeventhMass_le_mul_norm_sq {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (M N : ℕ) (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N u ≤ δ * ‖u‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN_pos
  · simp [truncatedCollarDualSeventhMass]; positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have hU_le : ⌊δ * (N : ℝ)⌋₊ ≤ N := by
    have : (⌊δ * (N : ℝ)⌋₊ : ℝ) ≤ N :=
      (Nat.floor_le (mul_nonneg hδ0 hN0.le)).trans
        ((mul_le_mul_of_nonneg_right hδ1 hN0.le).trans_eq (one_mul _))
    exact_mod_cast this
  have hsub : Ioc M ⌊δ * (N : ℝ)⌋₊ ⊆ Icc 1 N := fun n hn =>
    mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2.trans hU_le⟩
  have hδ7 : δ ^ 7 ≤ δ := by
    calc δ ^ 7 = δ * δ ^ 6 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hδ0 hδ1) hδ0
      _ = δ := mul_one _
  calc truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N u
      ≤ ∑ n ∈ Ioc M ⌊δ * (N : ℝ)⌋₊, δ * primeHorizonExtension u n ^ 2 := by
        refine sum_le_sum fun n hn => ?_
        have hn_fl : (n : ℝ) ≤ δ * N :=
          (by exact_mod_cast (mem_Ioc.mp hn).2 : (n : ℝ) ≤ ⌊δ * (N : ℝ)⌋₊).trans
            (Nat.floor_le (mul_nonneg hδ0 hN0.le))
        have hdiv : (n : ℝ) / N ≤ δ := (div_le_iff₀ hN0).mpr hn_fl
        have hw7 : ((n : ℝ) / N) ^ 7 ≤ δ := (pow_le_pow_left₀ (by positivity) hdiv 7).trans hδ7
        exact mul_le_mul_of_nonneg_right hw7 (sq_nonneg _)
    _ ≤ ∑ n ∈ Icc 1 N, δ * primeHorizonExtension u n ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => mul_nonneg hδ0 (sq_nonneg _)
    _ = δ * ‖u‖ ^ 2 := by
        rw [← mul_sum, EuclideanSpace.norm_sq_eq, ← sum_coe_sort (Icc 1 N)]
        congr 1
        refine sum_congr rfl fun n _ => ?_
        rw [Real.norm_eq_abs, sq_abs, primeHorizonExtension_coe]

private theorem truncatedCollarDualSeventhMass_add_le (M U N : ℕ)
    (u v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    truncatedCollarDualSeventhMass M U N (u + v) ≤
      2 * truncatedCollarDualSeventhMass M U N u + 2 * truncatedCollarDualSeventhMass M U N v := by
  unfold truncatedCollarDualSeventhMass
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  by_cases hnI : n ∈ Icc 1 N
  · let idx : PrimeHorizonIndex N := ⟨n, hnI⟩
    have h1 : primeHorizonExtension (u + v) n =
        primeHorizonExtension u n + primeHorizonExtension v n := by
      change primeHorizonExtension (u + v) idx.1 =
        primeHorizonExtension u idx.1 + primeHorizonExtension v idx.1
      rw [primeHorizonExtension_coe, primeHorizonExtension_coe, primeHorizonExtension_coe]; rfl
    rw [h1]
    have h2 : (primeHorizonExtension u n + primeHorizonExtension v n) ^ 2 ≤
        2 * primeHorizonExtension u n ^ 2 + 2 * primeHorizonExtension v n ^ 2 := by
      nlinarith only [sq_nonneg (primeHorizonExtension u n - primeHorizonExtension v n)]
    have hw : 0 ≤ ((n : ℝ) / N) ^ 7 := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left h2 hw]
  · simp [primeHorizonExtension, hnI]

private theorem truncatedCollarDualSeventhMass_seven_le (M U N : ℕ)
    (u₁ u₂ u₃ u₄ u₅ u₆ u₇ : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    truncatedCollarDualSeventhMass M U N (u₁ + u₂ + u₃ + u₄ + u₅ + u₆ + u₇) ≤
      16 * (truncatedCollarDualSeventhMass M U N u₁ +
        truncatedCollarDualSeventhMass M U N u₂ +
        truncatedCollarDualSeventhMass M U N u₃ +
        truncatedCollarDualSeventhMass M U N u₄ +
        truncatedCollarDualSeventhMass M U N u₅ +
        truncatedCollarDualSeventhMass M U N u₆ +
        truncatedCollarDualSeventhMass M U N u₇) := by
  have h1 := truncatedCollarDualSeventhMass_add_le M U N ((u₁ + u₂) + (u₃ + u₄)) ((u₅ + u₆) + u₇)
  have h2 := truncatedCollarDualSeventhMass_add_le M U N (u₁ + u₂) (u₃ + u₄)
  have h3 := truncatedCollarDualSeventhMass_add_le M U N u₁ u₂
  have h4 := truncatedCollarDualSeventhMass_add_le M U N u₃ u₄
  have h5 := truncatedCollarDualSeventhMass_add_le M U N (u₅ + u₆) u₇
  have h6 := truncatedCollarDualSeventhMass_add_le M U N u₅ u₆
  have n1 := truncatedCollarDualSeventhMass_nonneg M U N u₁
  have n2 := truncatedCollarDualSeventhMass_nonneg M U N u₂
  have n3 := truncatedCollarDualSeventhMass_nonneg M U N u₃
  have n4 := truncatedCollarDualSeventhMass_nonneg M U N u₄
  have n5 := truncatedCollarDualSeventhMass_nonneg M U N u₅
  have n6 := truncatedCollarDualSeventhMass_nonneg M U N u₆
  have n7 := truncatedCollarDualSeventhMass_nonneg M U N u₇
  have heq : u₁ + u₂ + u₃ + u₄ + u₅ + u₆ + u₇ = ((u₁ + u₂) + (u₃ + u₄)) + ((u₅ + u₆) + u₇) := by abel
  rw [heq]
  linarith only [h1, h2, h3, h4, h5, h6, n1, n2, n3, n4, n5, n6, n7]

private lemma truncatedCollar_upward_b_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {N M m : ℕ} {c δ : ℝ}
    (hN : 1 ≤ N) (hL1 : 1 ≤ Real.log (N : ℝ)) (hm : 0 < m)
    (hc1 : 1 ≤ c) (hcN : c ≤ N) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h2BM : 2 * linearPrimeStrip c ≤ M) :
    truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N
      (WithLp.toLp 2 (fun n : PrimeHorizonIndex N =>
        ((linearizedUpwardCoefficient φ c (linearPrimeStrip c) N m n.1 -
          reciprocalUpwardCoefficient φ c (linearPrimeStrip c) N m n.1) / Real.sqrt n.1) /
          Real.sqrt (Real.log N))) ≤
      δ * (16 * (Real.exp 1 + 2) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N) := by
  let d : ℝ := Real.exp 1 + 2
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  set B := linearPrimeStrip c
  have hB_le : (B : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
  have hB1 : (B : ℝ) + 1 ≤ d * c := by dsimp only [d]; linarith only [hB_le, hc1]
  have hU_le : ⌊δ * (N : ℝ)⌋₊ ≤ N := by
    have : (⌊δ * (N : ℝ)⌋₊ : ℝ) ≤ N :=
      (Nat.floor_le (mul_nonneg hδ0 hN0.le)).trans
        ((mul_le_mul_of_nonneg_right hδ1 hN0.le).trans_eq (one_mul _))
    exact_mod_cast this
  have hcard_U : ((Ioc M ⌊δ * (N : ℝ)⌋₊).card : ℝ) ≤ δ * N := by
    rw [Nat.card_Ioc]
    exact (Nat.cast_le.mpr (Nat.sub_le ⌊δ * (N : ℝ)⌋₊ M)).trans (Nat.floor_le (mul_nonneg hδ0 hN0.le))
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let u_b : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun n => b n.1 / Real.sqrt (Real.log N))
  let S_ex : ℕ → Finset ℕ := fun n =>
    (Icc 1 (N + B)).filter (fun k => N ≤ k * n + B ∧ k * n ≤ N + B)
  have hpt : ∀ n ∈ Ioc M ⌊δ * (N : ℝ)⌋₊,
      ((n : ℝ) / N) ^ 7 * primeHorizonExtension u_b n ^ 2 ≤
        16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N) := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hnN : n ≤ N := (mem_Ioc.mp hn).2.trans hU_le
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have hn2B : 2 * B < n := lt_of_le_of_lt h2BM (mem_Ioc.mp hn).1
    let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, hnN⟩⟩
    have hext : primeHorizonExtension u_b n = b n / Real.sqrt (Real.log N) :=
      primeHorizonExtension_coe u_b idx
    have hcard_one : (S_ex n).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun k₁ hk₁ k₂ hk₂ => ?_
      obtain ⟨_, h1lo, h1hi⟩ := mem_filter.mp hk₁
      obtain ⟨_, h2lo, h2hi⟩ := mem_filter.mp hk₂
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hstep : (k₁ + 1) * n ≤ k₂ * n := Nat.mul_le_mul_right n hlt
        nlinarith [hstep, hn2B, h1lo, h2hi]
      · have hstep : (k₂ + 1) * n ≤ k₁ * n := Nat.mul_le_mul_right n hgt
        nlinarith [hstep, hn2B, h2lo, h1hi]
    have hsum_k : (∑ k ∈ S_ex n, (Λ k : ℝ) / k) ≤ 1 := by
      calc (∑ k ∈ S_ex n, (Λ k : ℝ) / k) ≤ ∑ _k ∈ S_ex n, (1 : ℝ) := by
            refine sum_le_sum fun k hk => ?_
            have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hk).1).1
            rw [div_le_one hk0]
            linarith [ArithmeticFunction.vonMangoldt_le_log (n := k),
              Real.log_le_sub_one_of_pos hk0]
        _ = ((S_ex n).card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
        _ ≤ 1 := by exact_mod_cast hcard_one
    have hrow : |linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n| ≤
        4 * d * (m.totient : ℝ) * c := by
      let L_val := 4 * (B : ℝ) * (∫ u, φ u ^ 2) * m.totient
      have hpk : ∀ k ∈ Icc 1 (N + B),
          |∑ h ∈ Icc 1 B, (linearizedUpwardOffset φ c N m n k h -
              reciprocalUpwardOffset φ c N m n k h)| ≤
            if N ≤ k * n + B ∧ k * n ≤ N + B then L_val else 0 := by
        intro k hk
        have hT : 1 ≤ k * n := Nat.mul_pos (mem_Icc.mp hk).1 hn1
        by_cases hex : N ≤ k * n + B ∧ k * n ≤ N + B
        · rw [if_pos hex]
          have h := (abs_sum_le_sum_abs _ (Icc 1 B)).trans
            (sum_le_sum fun h _ => abs_linearizedUpwardOffset_sub_reciprocal_le hφ hsupp c N m n k h)
          rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at h
          exact h.trans_eq (by dsimp only [L_val]; ring)
        · rw [if_neg hex]
          have hz : (∑ h ∈ Icc 1 B, (linearizedUpwardOffset φ c N m n k h -
              reciprocalUpwardOffset φ c N m n k h)) = 0 := by
            refine sum_eq_zero fun h hh => ?_
            have hhB := (mem_Icc.mp hh).2
            by_cases hhT : h < k * n
            · rcases (show k * n + B < N ∨ N + B < k * n by omega) with hfar | hfar
              · simp only [linearizedUpwardOffset, reciprocalUpwardOffset,
                  if_pos (show k * n + h ≤ N by omega),
                  if_pos (show h < k * n ∧ k * n - h ≤ N from ⟨hhT, by omega⟩),
                  if_pos (show k * n ≤ N by omega),
                  ramanujanLagCoefficient_sub_eq_reflected hm hhT.le, sub_self]
              · simp only [linearizedUpwardOffset, reciprocalUpwardOffset,
                  if_neg (show ¬ k * n + h ≤ N by omega),
                  if_neg (show ¬ (h < k * n ∧ k * n - h ≤ N) by omega),
                  if_neg (show ¬ k * n ≤ N by omega), add_zero, sub_self]
            · have hT0 : (0 : ℝ) < (k * n : ℕ) := by exact_mod_cast hT
              have hzero := shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
                ((one_le_mul_of_one_le_of_one_le ((one_le_div hc0).mpr hcN)
                  ((one_le_div hT0).mpr (Nat.cast_le.mpr (by omega : k * n ≤ h)))).trans
                  (le_abs_self _))
              simp only [linearizedUpwardOffset, reciprocalUpwardOffset, hzero, mul_zero, sub_self]
          rw [hz, abs_zero]
      unfold linearizedUpwardCoefficient reciprocalUpwardCoefficient
      rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hM_int)]
      have h1 : 1 / (∫ u, φ u ^ 2) * |∑ k ∈ Icc 1 (N + B),
          ((Λ k : ℝ) / k * ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h -
            (Λ k : ℝ) / k * ∑ h ∈ Icc 1 B, reciprocalUpwardOffset φ c N m n k h)| ≤
          4 * (B : ℝ) * m.totient * ∑ k ∈ S_ex n, (Λ k : ℝ) / k := by
        calc _ ≤ 1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
              if N ≤ k * n + B ∧ k * n ≤ N + B then (Λ k : ℝ) / k * L_val else 0 := by
              refine mul_le_mul_of_nonneg_left
                ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)) (by positivity)
              rw [← mul_sub, ← sum_sub_distrib, abs_mul,
                abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))]
              have hp := hpk k hk
              split_ifs at hp ⊢
              · exact mul_le_mul_of_nonneg_left hp
                  (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
              · simpa only [mul_zero] using mul_le_mul_of_nonneg_left hp
                  (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
          _ = 4 * (B : ℝ) * m.totient * ∑ k ∈ S_ex n, (Λ k : ℝ) / k := by
              dsimp only [S_ex, L_val]; rw [← sum_filter, ← sum_mul]; field_simp [hM_int.ne']
      have hBd : (B : ℝ) ≤ d * c := by linarith only [hB1]
      calc _ ≤ 4 * (B : ℝ) * m.totient * 1 :=
            h1.trans (mul_le_mul_of_nonneg_left hsum_k (by positivity))
        _ ≤ 4 * (d * c) * m.totient * 1 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBd (by norm_num))
                (Nat.cast_nonneg _)) zero_le_one
        _ = 4 * d * (m.totient : ℝ) * c := by ring
    rw [hext, div_pow (b n), Real.sq_sqrt hL0.le]
    have hb2 : b n ^ 2 ≤ 16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / n := by
      dsimp only [b]
      rw [div_pow, Real.sq_sqrt hn0.le]
      refine div_le_div_of_nonneg_right ?_ hn0.le
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hrow 2
      rw [sq_abs] at hsq; exact hsq.trans_eq (by ring)
    have hw7 : ((n : ℝ) / N) ^ 7 ≤ (n : ℝ) / N := by
      have h6 : ((n : ℝ) / N) ^ 6 ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hN0).mpr hnNR)
      nlinarith only [h6, div_pos hn0 hN0,
        (by ring : ((n : ℝ) / N) ^ 7 = ((n : ℝ) / N) * ((n : ℝ) / N) ^ 6)]
    calc ((n : ℝ) / N) ^ 7 * (b n ^ 2 / Real.log N)
        ≤ ((n : ℝ) / N) * ((16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / n) / Real.log N) :=
          mul_le_mul hw7 (div_le_div_of_nonneg_right hb2 hL0.le) (by positivity) (by positivity)
      _ = 16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N) := by
          field_simp [hn0.ne', hN0.ne', hL0.ne']
  calc truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N u_b
      ≤ ((Ioc M ⌊δ * (N : ℝ)⌋₊).card : ℝ) *
          (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N)) := by
        unfold truncatedCollarDualSeventhMass
        exact (sum_le_sum hpt).trans_eq (by rw [sum_const, nsmul_eq_mul])
    _ ≤ (δ * N) * (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N)) :=
        mul_le_mul_of_nonneg_right hcard_U (by dsimp only [d]; positivity)
    _ = δ * (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N) := by
        field_simp [hN0.ne', hL0.ne']

private lemma truncatedCollar_upward_r_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {N M m : ℕ} {c δ : ℝ}
    (hN : 1 ≤ N) (hL1 : 1 ≤ Real.log (N : ℝ)) (hm : 0 < m)
    (hc1 : 1 ≤ c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N
      (WithLp.toLp 2 (fun n : PrimeHorizonIndex N =>
        ((reciprocalUpwardCoefficient φ c (linearPrimeStrip c) N m n.1 -
          ramanujanLagCoefficient m n.1 * shellCorrection φ c m) / Real.sqrt n.1) /
          Real.sqrt (Real.log N))) ≤
      δ * (16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  set B := linearPrimeStrip c
  have hB_ceil : ⌈c⌉₊ ≤ B := by
    apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_left (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)) hc0.le
    exact (by simpa only [mul_one] using h : c ≤ c * Real.exp 1).trans (Nat.le_ceil _)
  have hU_le : ⌊δ * (N : ℝ)⌋₊ ≤ N := by
    have : (⌊δ * (N : ℝ)⌋₊ : ℝ) ≤ N :=
      (Nat.floor_le (mul_nonneg hδ0 hN0.le)).trans
        ((mul_le_mul_of_nonneg_right hδ1 hN0.le).trans_eq (one_mul _))
    exact_mod_cast this
  have hcard_U : ((Ioc M ⌊δ * (N : ℝ)⌋₊).card : ℝ) ≤ δ * N := by
    rw [Nat.card_Ioc]
    exact (Nat.cast_le.mpr (Nat.sub_le ⌊δ * (N : ℝ)⌋₊ M)).trans (Nat.floor_le (mul_nonneg hδ0 hN0.le))
  let r : ℕ → ℝ := fun n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  let u_r : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun n => r n.1 / Real.sqrt (Real.log N))
  have hpt : ∀ n ∈ Ioc M ⌊δ * (N : ℝ)⌋₊,
      ((n : ℝ) / N) ^ 7 * primeHorizonExtension u_r n ^ 2 ≤
        16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N) := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hnN : n ≤ N := (mem_Ioc.mp hn).2.trans hU_le
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have hX1 : 1 ≤ (N : ℝ) / n := (one_le_div hn0).mpr hnNR
    let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, hnN⟩⟩
    rw [show primeHorizonExtension u_r n = r n / Real.sqrt (Real.log N) from
      primeHorizonExtension_coe u_r idx, div_pow (r n), Real.sq_sqrt hL0.le]
    have hr_num : |reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m| ≤
        4 * (Real.log 4 + 4) * (m.totient : ℝ) * c := by
      rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc0 hB_ceil N m n hn1]
      have hsc : shellCorrection φ c m =
          (shellCorrectionOfShift φ c m id +
            shellCorrectionOfShift φ c m (reflectedAffineShift m)) / 2 := by
        rw [shellCorrectionOfShift_reflected hm]
        change shellCorrection φ c m = (shellCorrection φ c m + shellCorrection φ c m) / 2
        ring
      have h1 := abs_affineShellCorrection_error_le_linear hm hφ hsupp hM_int n id hc0 hX1
      have h2 := abs_affineShellCorrection_error_le_linear hm hφ hsupp hM_int n
        (reflectedAffineShift m) hc0 hX1
      rw [hsc, show (affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) +
          affinePrimeShellCorrectionOfShift m n (reflectedAffineShift m) φ c ((N : ℝ) / n)) / 2 -
          ramanujanLagCoefficient m n *
            ((shellCorrectionOfShift φ c m id +
              shellCorrectionOfShift φ c m (reflectedAffineShift m)) / 2) =
          ((affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) -
            ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m id) +
          (affinePrimeShellCorrectionOfShift m n (reflectedAffineShift m) φ c ((N : ℝ) / n) -
            ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m (reflectedAffineShift m))) / 2 by ring,
        abs_div, show |(2 : ℝ)| = 2 by norm_num]
      have htri := abs_add_le
        (affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) -
          ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m id)
        (affinePrimeShellCorrectionOfShift m n (reflectedAffineShift m) φ c ((N : ℝ) / n) -
          ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m (reflectedAffineShift m))
      linarith only [htri, h1, h2]
    have hr2 : r n ^ 2 ≤ 16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / n := by
      dsimp only [r]
      rw [div_pow, Real.sq_sqrt hn0.le]
      refine div_le_div_of_nonneg_right ?_ hn0.le
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hr_num 2
      rw [sq_abs] at hsq; exact hsq.trans_eq (by ring)
    have hw7 : ((n : ℝ) / N) ^ 7 ≤ (n : ℝ) / N := by
      have h6 : ((n : ℝ) / N) ^ 6 ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hN0).mpr hnNR)
      nlinarith only [h6, div_pos hn0 hN0,
        (by ring : ((n : ℝ) / N) ^ 7 = ((n : ℝ) / N) * ((n : ℝ) / N) ^ 6)]
    calc ((n : ℝ) / N) ^ 7 * (r n ^ 2 / Real.log N)
        ≤ ((n : ℝ) / N) *
            ((16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / n) / Real.log N) :=
          mul_le_mul hw7 (div_le_div_of_nonneg_right hr2 hL0.le) (by positivity) (by positivity)
      _ = 16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N) := by
          field_simp [hn0.ne', hN0.ne', hL0.ne']
  calc truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N u_r
      ≤ ((Ioc M ⌊δ * (N : ℝ)⌋₊).card : ℝ) *
          (16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N)) := by
        unfold truncatedCollarDualSeventhMass
        exact (sum_le_sum hpt).trans_eq (by rw [sum_const, nsmul_eq_mul])
    _ ≤ (δ * N) *
          (16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N)) :=
        mul_le_mul_of_nonneg_right hcard_U (by positivity)
    _ = δ * (16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N) := by
        field_simp [hN0.ne', hL0.ne']

/-- Truncated collar dual seventh-power bound on Channel 8 (`upwardPrimeVector - shellCorrection`),
gaining a factor `δ` on `Ioc M ⌊δ N⌋₊`. -/
private theorem exists_truncated_upward_dual_seventh_log_free {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) :
    ∃ Cu7 : ℝ, 0 < Cu7 ∧
      ∀ {N M m : ℕ} {c δ : ℝ},
        1 ≤ N → 1 ≤ Real.log (N : ℝ) → 0 < m → 1 ≤ c →
        0 ≤ δ → δ ≤ 1 →
        4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ N →
        2 * linearPrimeStrip c ≤ M →
        truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N
          (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
            shellCorrection φ c m • normalizedRamanujanHorizonVector m N) ≤
          Cu7 * δ * (m : ℝ) ^ 2 *
            (c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_logarithmicUpward_uniform_conductor_harmonic_bound hφ hsupp hM_int
  let d : ℝ := Real.exp 1 + 2
  set K_c : ℝ := 4 * Ca * d ^ 6 + 64 * d ^ 2 + 64 * (Real.log 4 + 4) ^ 2
  refine ⟨K_c + 1, by dsimp only [K_c, d]; positivity, ?_⟩
  intro N M m c δ hN hL1 hm hc1 hδ0 hδ1 hlarge h2BM
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  set B := linearPrimeStrip c
  have hB_le : (B : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
  have hB1 : (B : ℝ) + 1 ≤ d * c := by dsimp only [d]; linarith only [hB_le, hc1]
  have hc_sq : c ≤ c ^ 2 := by nlinarith only [hc1]
  have hBN : B ≤ N := by
    have : (B : ℝ) ≤ N := by
      have h1 : (B : ℝ) ≤ d * c := by linarith only [hB1]
      have h2 : d * c ≤ 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 := by
        dsimp only [d]
        have he1 : 0 < Real.exp 1 := Real.exp_pos 1
        have he2 : 0 ≤ Real.exp 1 ^ 2 := sq_nonneg _
        have hce : c * Real.exp 1 ≤ c ^ 2 * Real.exp 1 :=
          mul_le_mul_of_nonneg_right hc_sq he1.le
        nlinarith only [hc1, hc_sq, he1, he2, hce]
      linarith only [h1, h2, hlarge]
    exact_mod_cast this
  have hwidth : c / N ≤ 1 / 2 := (div_le_iff₀ hN0).mpr (by
    have : 2 * c ≤ 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 := by
      have he1 : 0 < Real.exp 1 := Real.exp_pos 1
      have he2 : 0 ≤ Real.exp 1 ^ 2 := sq_nonneg _
      nlinarith only [hc1, hc_sq, he1, he2]
    linarith only [this, hlarge])
  have hcN : c ≤ N := by linarith only [(div_le_iff₀ hN0).mp hwidth, hc0]
  have hkernel : 2 * ((Real.exp 1 + 3) * c) * (B : ℝ) ≤ N := by
    have h1 : (B : ℝ) ≤ (Real.exp 1 + 3) * c := by linarith only [hB_le, hc1]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * ((Real.exp 1 + 3) * c))
    nlinarith only [h2, hlarge]
  rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, truncatedCollarDualSeventhMass_smul,
    inv_pow, Real.sq_sqrt htot_pos.le]
  let a : ℕ → ℝ := fun n =>
    (logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let r : ℕ → ℝ := fun n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  let u_a : EuclideanSpace ℝ (PrimeHorizonIndex N) := WithLp.toLp 2 (fun n => a n / Real.sqrt (Real.log N))
  let u_b : EuclideanSpace ℝ (PrimeHorizonIndex N) := WithLp.toLp 2 (fun n => b n / Real.sqrt (Real.log N))
  let u_r : EuclideanSpace ℝ (PrimeHorizonIndex N) := WithLp.toLp 2 (fun n => r n / Real.sqrt (Real.log N))
  have hsplit3 : normalizedUpwardPrimeResidual φ c N m = (u_a + u_b) + u_r := by
    ext n
    have hn : (n : ℕ) ∈ Icc 1 N := n.2
    have hsqrt : Real.sqrt (n : ℕ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < (n : ℕ))).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n / (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt (n : ℕ) :=
      (eq_div_iff hsqrt).mpr (by
        simpa only [mul_comm] using
          sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width hsupp hc0 hn
            (hwidth.trans (by norm_num)) m)
    change actualUpwardRowError φ c N m n / Real.sqrt (Real.log N) =
      (a n / Real.sqrt (Real.log N) + b n / Real.sqrt (Real.log N)) + r n / Real.sqrt (Real.log N)
    rw [actualUpwardRowError, hu]; dsimp only [a, b, r]; ring
  have hua : truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N u_a ≤
      δ * (Ca * d ^ 6 * (m.totient : ℝ) ^ 2 * c ^ 10 * (Real.log N / N) ^ 2) := by
    have h1 := truncatedCollarDualSeventhMass_le_mul_norm_sq hδ0 hδ1 M N u_a
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (B : ℝ) + 1) hB1 6
    have hb := (ha m N hN hL1 c hc1 (hwidth.trans (by norm_num)) B hBN hkernel).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ Ca * (m.totient : ℝ) ^ 2 * c ^ 4))
        (sq_nonneg _))
    have hua_sq : ‖u_a‖ ^ 2 = (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N := by
      rw [EuclideanSpace.norm_sq_eq]
      change (∑ n : PrimeHorizonIndex N, ‖a n / Real.sqrt (Real.log N)‖ ^ 2) = _
      simp only [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hL0.le]
      rw [← sum_div, ← sum_coe_sort (Icc 1 N)]
    exact h1.trans (mul_le_mul_of_nonneg_left (hua_sq.le.trans (hb.trans_eq (by ring))) hδ0)
  have hub : truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N u_b ≤
      δ * (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N) :=
    truncatedCollar_upward_b_le hφ hsupp hM_int hN hL1 hm hc1 hcN hδ0 hδ1 h2BM
  have hur : truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N u_r ≤
      δ * (16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N) :=
    truncatedCollar_upward_r_le hφ hsupp hM_int hN hL1 hm hc1 hδ0 hδ1
  rw [hsplit3]
  have htri1 := truncatedCollarDualSeventhMass_add_le M ⌊δ * (N : ℝ)⌋₊ N (u_a + u_b) u_r
  have htri2 := truncatedCollarDualSeventhMass_add_le M ⌊δ * (N : ℝ)⌋₊ N u_a u_b
  have nr := truncatedCollarDualSeventhMass_nonneg M ⌊δ * (N : ℝ)⌋₊ N u_r
  have hsum : truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N ((u_a + u_b) + u_r) ≤
      K_c * δ * (m.totient : ℝ) ^ 2 *
        (c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2) := by
    have hlin : truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N ((u_a + u_b) + u_r) ≤
        δ * (m.totient : ℝ) ^ 2 * ((4 * Ca * d ^ 6) * (c ^ 10 * (Real.log N / N) ^ 2) +
          (64 * d ^ 2 + 32 * (Real.log 4 + 4) ^ 2) * (c ^ 2 / Real.log N)) := by
      have hlin0 : truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N ((u_a + u_b) + u_r) ≤
          4 * (δ * (Ca * d ^ 6 * (m.totient : ℝ) ^ 2 * c ^ 10 * (Real.log N / N) ^ 2)) +
          4 * (δ * (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N)) +
          2 * (δ * (16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N)) := by
        linarith only [htri1, htri2, nr, hua, hub, hur]
      exact hlin0.trans_eq (by ring)
    have hc2_pos : 0 ≤ c ^ 2 / Real.log N := by positivity
    have hc10_pos : 0 ≤ c ^ 10 * (Real.log N / N) ^ 2 := by positivity
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    have hlog4 : 0 ≤ (Real.log 4 + 4) ^ 2 := sq_nonneg _
    have hCad : 0 ≤ Ca * d ^ 6 := by dsimp only [d]; positivity
    have hin : (4 * Ca * d ^ 6) * (c ^ 10 * (Real.log N / N) ^ 2) +
        (64 * d ^ 2 + 32 * (Real.log 4 + 4) ^ 2) * (c ^ 2 / Real.log N) ≤
        K_c * (c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2) := by
      dsimp only [K_c]; nlinarith only [hc2_pos, hc10_pos, hd2, hlog4, hCad]
    exact hlin.trans ((mul_le_mul_of_nonneg_left hin (by positivity)).trans_eq (by ring))
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have htot_m2 : (m.totient : ℝ) ≤ (m : ℝ) ^ 2 := htot_le.trans (by nlinarith only [hm1R])
  have hKc0 : 0 ≤ K_c := by dsimp only [K_c, d]; positivity
  calc (m.totient : ℝ)⁻¹ * truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N ((u_a + u_b) + u_r)
      ≤ (m.totient : ℝ)⁻¹ *
          (K_c * δ * (m.totient : ℝ) ^ 2 *
            (c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (K_c * δ * (m.totient : ℝ) *
          (c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2)) *
          ((m.totient : ℝ)⁻¹ * m.totient) := by ring
    _ = K_c * δ * (m.totient : ℝ) *
          (c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2) := by
        rw [inv_mul_cancel₀ htot_pos.ne', mul_one]
    _ ≤ (K_c + 1) * δ * (m : ℝ) ^ 2 *
          (c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_right (by linarith only) hδ0) htot_m2
            (Nat.cast_nonneg _) (by positivity)) (by positivity)

/-- **Truncated collar dual seventh-power residual bound (`Ioc M ⌊δ N⌋₊`).**
For every `m ≥ 1` and `0 ≤ δ ≤ 1`, restricting `conductorResidualVector c m N` to `Ioc M ⌊δ N⌋₊`
gains a linear factor `δ` over `exists_completeWeil_dualSeventh_conductor_residual_log_free`. -/
theorem exists_truncated_dualSeventh_conductor_residual :
    ∃ K_td7 : ℝ, 0 < K_td7 ∧
      ∀ {N M m : ℕ} {c δ : ℝ},
        0 < m → 1 ≤ c → 1 ≤ Real.log (N : ℝ) →
        0 ≤ δ → δ ≤ 1 →
        4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ N →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N → c ^ 4 ≤ N →
        2 * linearPrimeStrip c ≤ M →
        truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N (conductorResidualVector c m N) ≤
          K_td7 * δ * (m : ℝ) ^ 2 *
            (c ^ 2 / Real.log N + c ^ 3 * Real.log N / N + c ^ 10 * (Real.log N / N) ^ 2) := by
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_quad_bound
  obtain ⟨Cs, hCs, hs⟩ := exists_selfError_quad_bound hφ hsupp hM
  obtain ⟨Cx, hCx, hx⟩ := exists_separatedCrossError_bounds hφ hsupp hM
  obtain ⟨Cq, hCq, hq⟩ := exists_poleError_quadratic_conductor_bound hφ hsupp hM
  obtain ⟨Cngc, hCngc, hngc⟩ := exists_nearGammaDownward_add_nearCenter_log_free hφ hsupp hM
  obtain ⟨Cu7, hCu7, hu7⟩ := exists_truncated_upward_dual_seventh_log_free hφ hsupp hM
  let S₁ := |completeWeilPoleShift tiltedUnitSpline 1|
  let K_td7 := 16 * (4 * Cp + Cs + 87 * S₁ ^ 2 + Cx + Cq + Cngc + Cu7 + 1)
  refine ⟨K_td7, by dsimp only [K_td7, S₁]; positivity, ?_⟩
  intro N M m c δ hm hc1 hL1 hδ0 hδ1 hlarge hradN hc4N h2BM
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1R]
  have hc2N : c ^ 2 ≤ N := (pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 4)).trans hc4N
  have hcN : c ≤ N := (by nlinarith only [hc1] : c ≤ c ^ 2).trans hc2N
  have hN1 : 1 ≤ N := by exact_mod_cast hc1.trans hcN
  let R := c ^ 2 / Real.log N + c ^ 3 * Real.log N / N + c ^ 10 * (Real.log N / N) ^ 2
  have hr_c2 : c ^ 2 / Real.log N ≤ R := by
    dsimp only [R]
    have : 0 ≤ c ^ 3 * Real.log N / N + c ^ 10 * (Real.log N / N) ^ 2 := by positivity
    linarith only [this]
  have hr_sub : c ^ 10 * (Real.log N / N) ^ 2 ≤ R := le_add_of_nonneg_left (by positivity)
  have hr_ngc : c ^ 2 / Real.log N + c ^ 3 * Real.log N / N ≤ R :=
    le_add_of_nonneg_right (by positivity)
  have hr_u7 : c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2 ≤ R := by
    dsimp only [R]
    have hmid : 0 ≤ c ^ 3 * Real.log N / N := by positivity
    linarith only [hmid]
  let v_m := normalizedRamanujanHorizonVector m N
  let u₁ := Matrix.toEuclideanLin (fullPrimeMatrix N) v_m -
    (Real.log N - ramanujanAdjunctionEnergy m) • v_m
  let u₂ := completeWeilSelfError tiltedUnitSpline c N • v_m
  let u₃ := Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) v_m -
    (if m = 1 then completeWeilPoleShift tiltedUnitSpline c else 0) • v_m
  let u₄ := Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) v_m
  let u₅ := Matrix.toEuclideanLin (fullWeilPoleErrorMatrix tiltedUnitSpline c N) v_m
  let u₆₇ := (Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector tiltedUnitSpline c N m +
    nearCenterVector tiltedUnitSpline c N m
  let u₈ := upwardPrimeVector tiltedUnitSpline c N v_m - shellCorrection tiltedUnitSpline c m • v_m
  let U := ⌊δ * (N : ℝ)⌋₊
  have hd1 : truncatedCollarDualSeventhMass M U N (-u₁) ≤ 4 * Cp * δ * (m : ℝ) ^ 2 * R := by
    rw [truncatedCollarDualSeventhMass_neg]
    have hlog_sq := one_add_log_sq_le_four_mul hm1R
    have h1 : ‖u₁‖ ^ 2 ≤ 4 * Cp * (m : ℝ) ^ 2 * R := by
      have hm_c : (m : ℝ) * (1 + Real.log m) ^ 2 ≤ 4 * (m : ℝ) ^ 2 * c ^ 2 :=
        (mul_le_mul_of_nonneg_left hlog_sq (Nat.cast_nonneg m)).trans
          (by nlinarith only [one_le_pow₀ hc1 (n := 2), sq_nonneg (m : ℝ)])
      exact (hp m hm N).trans (((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm_c hCp.le)
        hL0.le).trans_eq (by ring)).trans (mul_le_mul_of_nonneg_left hr_c2 (by positivity)))
    exact (truncatedCollarDualSeventhMass_le_mul_norm_sq hδ0 hδ1 M N u₁).trans
      ((mul_le_mul_of_nonneg_left h1 hδ0).trans_eq (by ring))
  have hd2 : truncatedCollarDualSeventhMass M U N u₂ ≤ Cs * δ * (m : ℝ) ^ 2 * R := by
    have hc2_10 : c ^ 2 / (N : ℝ) ^ 2 ≤ c ^ 10 * (Real.log N / N) ^ 2 := by
      rw [div_pow, mul_div_assoc']
      exact div_le_div_of_nonneg_right
        ((pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 10)).trans
          (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1))) (sq_nonneg _)
    have h1 : ‖u₂‖ ^ 2 ≤ Cs * (m : ℝ) ^ 2 * R :=
      (hs m hm N hN1 hL1 c hc0 hcN).trans
        (((by ring : Cs * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2 = Cs * (m : ℝ) * (c ^ 2 / (N : ℝ) ^ 2)).le.trans
          (mul_le_mul (mul_le_mul_of_nonneg_left hm_sq hCs.le) hc2_10 (by positivity) (by positivity))).trans
          (mul_le_mul_of_nonneg_left hr_sub (by positivity)))
    exact (truncatedCollarDualSeventhMass_le_mul_norm_sq hδ0 hδ1 M N u₂).trans
      ((mul_le_mul_of_nonneg_left h1 hδ0).trans_eq (by ring))
  have hd3 : truncatedCollarDualSeventhMass M U N u₃ ≤ 87 * S₁ ^ 2 * δ * (m : ℝ) ^ 2 * R := by
    have hcen := fullWeilCenter_residual_uniform_conductor_bound hm
      (completeWeilPoleShift tiltedUnitSpline c) N
    have hshift : (completeWeilPoleShift tiltedUnitSpline c) ^ 2 = S₁ ^ 2 * c ^ 2 := by
      have h1 : completeWeilPoleShift tiltedUnitSpline c =
          completeWeilPoleShift tiltedUnitSpline 1 * c := by unfold completeWeilPoleShift; ring
      rw [h1, mul_pow, ← sq_abs]
    rw [hshift] at hcen
    have h1 : ‖u₃‖ ^ 2 ≤ 87 * S₁ ^ 2 * (m : ℝ) ^ 2 * R :=
      (hcen.trans_eq (by ring)).trans (mul_le_mul_of_nonneg_left hr_c2 (by dsimp only [S₁]; positivity))
    exact (truncatedCollarDualSeventhMass_le_mul_norm_sq hδ0 hδ1 M N u₃).trans
      ((mul_le_mul_of_nonneg_left h1 hδ0).trans_eq (by ring))
  have hd4 : truncatedCollarDualSeventhMass M U N (-u₄) ≤ Cx * δ * (m : ℝ) ^ 2 * R := by
    rw [truncatedCollarDualSeventhMass_neg]
    have h1 : ‖u₄‖ ^ 2 ≤ Cx * (m : ℝ) ^ 2 * R :=
      ((hx m hm c hc1 N hN1 hc2N).1.trans_eq (by ring)).trans
        ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_sq hCx.le) (by positivity)).trans
          (mul_le_mul_of_nonneg_left hr_c2 (by positivity)))
    exact (truncatedCollarDualSeventhMass_le_mul_norm_sq hδ0 hδ1 M N u₄).trans
      ((mul_le_mul_of_nonneg_left h1 hδ0).trans_eq (by ring))
  have hd5 : truncatedCollarDualSeventhMass M U N u₅ ≤ Cq * δ * (m : ℝ) ^ 2 * R := by
    have h1 : ‖u₅‖ ^ 2 ≤ Cq * (m : ℝ) ^ 2 * R :=
      ((hq m hm c hc1 N hN1 hL1 hcN).trans_eq (by ring)).trans
        ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_sq hCq) (by positivity)).trans
          (mul_le_mul_of_nonneg_left hr_sub (by positivity)))
    exact (truncatedCollarDualSeventhMass_le_mul_norm_sq hδ0 hδ1 M N u₅).trans
      ((mul_le_mul_of_nonneg_left h1 hδ0).trans_eq (by ring))
  have hd67 : truncatedCollarDualSeventhMass M U N u₆₇ ≤ Cngc * δ * (m : ℝ) ^ 2 * R :=
    (truncatedCollarDualSeventhMass_le_mul_norm_sq hδ0 hδ1 M N u₆₇).trans
      ((mul_le_mul_of_nonneg_left
        ((hngc hm hc1 hL1 hradN hc4N).1.trans (mul_le_mul_of_nonneg_left hr_ngc (by positivity)))
        hδ0).trans_eq (by ring))
  have hd8 : truncatedCollarDualSeventhMass M U N (-u₈) ≤ Cu7 * δ * (m : ℝ) ^ 2 * R := by
    rw [truncatedCollarDualSeventhMass_neg]
    exact (hu7 hN1 hL1 hm hc1 hδ0 hδ1 hlarge h2BM).trans
      (mul_le_mul_of_nonneg_left hr_u7 (by positivity))
  have hres_eq : conductorResidualVector c m N = (-u₁) + u₂ + u₃ + (-u₄) + u₅ + u₆₇ + (-u₈) := by
    unfold conductorResidualVector
    rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN1 hm]
    dsimp only [v_m, u₁, u₂, u₃, u₄, u₅, u₆₇, u₈]; abel
  rw [hres_eq]
  have h7 := truncatedCollarDualSeventhMass_seven_le M U N (-u₁) u₂ u₃ (-u₄) u₅ u₆₇ (-u₈)
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add hd1 hd2) hd3) hd4) hd5) hd67) hd8
  have hnn : 0 ≤ δ * (m : ℝ) ^ 2 * R := by dsimp only [R]; positivity
  calc _ ≤ 16 * ((4 * Cp + Cs + 87 * S₁ ^ 2 + Cx + Cq + Cngc + Cu7) * (δ * (m : ℝ) ^ 2 * R)) :=
        h7.trans (mul_le_mul_of_nonneg_left (hsum.trans_eq (by ring)) (by norm_num))
    _ ≤ K_td7 * δ * (m : ℝ) ^ 2 * R := by dsimp only [K_td7]; nlinarith only [hnn]

/-! ## Section 3: Nonpolar (`m ≥ 2`) Top-Window `ℓ²` Row Cancellation (`Ioc ⌊δ N⌋₊ N`) -/

/-- Squared `ℓ²` mass of a horizon vector on the top window `Ioc ⌊δ N⌋₊ N`. -/
def topWindowResidualMass (δ : ℝ) (N : ℕ) (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) : ℝ :=
  ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, primeHorizonExtension u n ^ 2

theorem topWindowResidualMass_nonneg (δ : ℝ) (N : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    0 ≤ topWindowResidualMass δ N u :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem topWindowResidualMass_le_norm_sq (δ : ℝ) (N : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topWindowResidualMass δ N u ≤ ‖u‖ ^ 2 := by
  have hsub : Ioc ⌊δ * (N : ℝ)⌋₊ N ⊆ Icc 1 N := fun n hn =>
    mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
  calc topWindowResidualMass δ N u
      ≤ ∑ n ∈ Icc 1 N, primeHorizonExtension u n ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ = ‖u‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, ← sum_coe_sort (Icc 1 N)]
        refine sum_congr rfl fun n _ => ?_
        rw [Real.norm_eq_abs, sq_abs, primeHorizonExtension_coe]

theorem topWindowResidualMass_add_le (δ : ℝ) (N : ℕ)
    (u v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topWindowResidualMass δ N (u + v) ≤
      2 * topWindowResidualMass δ N u + 2 * topWindowResidualMass δ N v := by
  unfold topWindowResidualMass
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n hn => ?_
  let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩⟩
  have h1 : primeHorizonExtension (u + v) n = primeHorizonExtension u n + primeHorizonExtension v n := by
    change primeHorizonExtension (u + v) idx.1 = primeHorizonExtension u idx.1 + primeHorizonExtension v idx.1
    rw [primeHorizonExtension_coe, primeHorizonExtension_coe, primeHorizonExtension_coe]; rfl
  rw [h1]
  nlinarith only [sq_nonneg (primeHorizonExtension u n - primeHorizonExtension v n)]

theorem topWindowResidualMass_neg (δ : ℝ) (N : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topWindowResidualMass δ N (-u) = topWindowResidualMass δ N u := by
  unfold topWindowResidualMass
  refine sum_congr rfl fun n hn => ?_
  let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩⟩
  have h1 : primeHorizonExtension (-u) n = -primeHorizonExtension u n := by
    change primeHorizonExtension (-u) idx.1 = -primeHorizonExtension u idx.1
    rw [primeHorizonExtension_coe, primeHorizonExtension_coe]; rfl
  rw [h1, neg_sq]

theorem topWindowResidualMass_smul (δ : ℝ) (N : ℕ) (a : ℝ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topWindowResidualMass δ N (a • u) = a ^ 2 * topWindowResidualMass δ N u := by
  unfold topWindowResidualMass
  rw [mul_sum]
  refine sum_congr rfl fun n hn => ?_
  let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩⟩
  have h1 : primeHorizonExtension (a • u) n = a * primeHorizonExtension u n := by
    change primeHorizonExtension (a • u) idx.1 = a * primeHorizonExtension u idx.1
    rw [primeHorizonExtension_coe, primeHorizonExtension_coe]; rfl
  rw [h1]; ring

private theorem topWindowResidualMass_five_le (δ : ℝ) (N : ℕ)
    (v₁ v₂ v₃ v₄ v₅ : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topWindowResidualMass δ N (v₁ + v₂ + v₃ + v₄ + v₅) ≤
      8 * (topWindowResidualMass δ N v₁ + topWindowResidualMass δ N v₂ +
        topWindowResidualMass δ N v₃ + topWindowResidualMass δ N v₄ +
        topWindowResidualMass δ N v₅) := by
  have h1 := topWindowResidualMass_add_le δ N (v₁ + v₂ + v₃ + v₄) v₅
  have h2 := topWindowResidualMass_add_le δ N (v₁ + v₂) (v₃ + v₄)
  have h3 := topWindowResidualMass_add_le δ N v₁ v₂
  have h4 := topWindowResidualMass_add_le δ N v₃ v₄
  have n5 := topWindowResidualMass_nonneg δ N v₅
  have heq : v₁ + v₂ + v₃ + v₄ = (v₁ + v₂) + (v₃ + v₄) := by abel
  rw [heq] at h1 ⊢
  linarith only [h1, h2, h3, h4, n5]

private lemma abs_mode_le_sqrt_conductor {m : ℕ} (hm0 : 0 < m) (j : ℕ) :
    |normalizedRamanujanMode m j| ≤ Real.sqrt m :=
  (SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm0 j).trans
    (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.totient_le m)))

/-- Filtering an integer interval `Ico a b` by an order-convex predicate yields a sub-interval. -/
private lemma filter_Ico_eq_Ico {P : ℕ → Prop} [DecidablePred P]
    (hconv : ∀ ⦃i j r : ℕ⦄, i ≤ j → j ≤ r → P i → P r → P j) (a b : ℕ) :
    ∃ L U : ℕ, L ≤ U ∧ (Ico a b).filter P = Ico L U := by
  let T := (Ico a b).filter P
  by_cases hT : T.Nonempty
  · refine ⟨T.min' hT, T.max' hT + 1, by have := T.min'_le _ (T.max'_mem hT); omega, ?_⟩
    ext j; simp only [T, mem_filter, mem_Ico]
    constructor
    · intro hj
      have hjT : j ∈ T := mem_filter.mpr ⟨mem_Ico.mpr hj.1, hj.2⟩
      exact ⟨T.min'_le j hjT, Nat.lt_succ_of_le (T.le_max' j hjT)⟩
    · intro ⟨hlo, hhi⟩
      have hhi' : j ≤ T.max' hT := Nat.le_of_lt_succ hhi
      obtain ⟨hminI, hPmin⟩ := mem_filter.mp (T.min'_mem hT)
      obtain ⟨hmaxI, hPmax⟩ := mem_filter.mp (T.max'_mem hT)
      exact ⟨⟨(mem_Ico.mp hminI).1.trans hlo, hhi'.trans_lt (mem_Ico.mp hmaxI).2⟩,
        hconv hlo hhi' hPmin hPmax⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    exact ⟨0, 0, le_rfl, hT.trans (Finset.Ico_eq_empty_of_le le_rfl).symm⟩

/-- Bounded-variation summation by parts against `normalizedRamanujanMode k` (`k ≥ 2`). -/
private lemma abs_sum_Ico_mode_bv_le {k : ℕ} (hk : 2 ≤ k) (w : ℕ → ℝ) (a b : ℕ) :
    |∑ j ∈ Ico a b, w j * normalizedRamanujanMode k j| ≤
      (k : ℝ) * ((if a < b then |w (b - 1)| else 0) +
        ∑ j ∈ Ico a (b - 1), |w j - w (j + 1)|) := by
  rcases le_or_gt b a with hba | hab
  · rw [Ico_eq_empty (not_lt.mpr hba), if_neg (not_lt.mpr hba),
      Ico_eq_empty (by omega), sum_empty, sum_empty, abs_zero, add_zero, mul_zero]
  · rw [if_pos hab]
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, b = a + m + 1 := ⟨b - a - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    let G : ℕ → ℝ := fun r => ∑ i ∈ Ico a r, normalizedRamanujanMode k i
    have hGa : G a = 0 := by simp [G]
    have hG_step : ∀ j : ℕ, a ≤ j → normalizedRamanujanMode k j = G (j + 1) - G j := fun j haj => by
      dsimp only [G]; rw [sum_Ico_succ_top haj]; ring
    have hab_id : ∀ n : ℕ, (∑ j ∈ Ico a (a + n + 1), w j * normalizedRamanujanMode k j) =
        w (a + n) * G (a + n + 1) + ∑ j ∈ Ico a (a + n), (w j - w (j + 1)) * G (j + 1) := by
      intro n
      induction n with
      | zero =>
        simp only [add_zero, Finset.Ico_self, sum_empty]
        have h1 : Ico a (a + 1) = {a} := by ext j; simp only [mem_Ico, mem_singleton]; omega
        rw [h1, sum_singleton, hG_step a le_rfl, hGa, sub_zero]
      | succ n ih =>
        rw [show a + (n + 1) + 1 = (a + n + 1) + 1 by omega, sum_Ico_succ_top (by omega), ih,
          hG_step (a + n + 1) (by omega), show a + (n + 1) = (a + n) + 1 by omega,
          sum_Ico_succ_top (by omega)]
        ring
    rw [hab_id m]
    have hG_le : ∀ r : ℕ, a ≤ r → |G r| ≤ k := fun r har =>
      CompletedArithmeticForms.abs_sum_Ico_normalizedRamanujanMode_le hk har
    have hb1 : |w (a + m) * G (a + m + 1)| ≤ |w (a + m)| * (k : ℝ) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hG_le _ (by omega)) (abs_nonneg _)
    have hb2 : |∑ j ∈ Ico a (a + m), (w j - w (j + 1)) * G (j + 1)| ≤
        (k : ℝ) * ∑ j ∈ Ico a (a + m), |w j - w (j + 1)| := by
      calc |∑ j ∈ Ico a (a + m), (w j - w (j + 1)) * G (j + 1)|
          ≤ ∑ j ∈ Ico a (a + m), |w j - w (j + 1)| * (k : ℝ) := by
            refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hG_le _ (by have := (mem_Ico.mp hj).1; omega)) (abs_nonneg _)
        _ = (k : ℝ) * ∑ j ∈ Ico a (a + m), |w j - w (j + 1)| := by
            rw [mul_sum]; refine sum_congr rfl fun _ _ => mul_comm _ _
    exact ((abs_add_le _ _).trans (add_le_add hb1 hb2)).trans_eq (by ring)

/-- Harmonic sum on the top window `Ioc ⌊δ N⌋₊ N` is bounded by `1 / δ`. -/
private lemma sum_topWindow_inv_le {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, 1 / (n : ℝ)) ≤ 1 / δ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, 1 / (n : ℝ))
      ≤ ∑ _n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, 1 / (δ * N) := by
        refine sum_le_sum fun n hn => ?_
        have hgt : δ * N < n := (Nat.lt_floor_add_one (δ * N)).trans_le
          (by exact_mod_cast (Nat.succ_le_of_lt (mem_Ioc.mp hn).1))
        exact one_div_le_one_div_of_le (mul_pos hδ hN0) hgt.le
    _ = ((Ioc ⌊δ * (N : ℝ)⌋₊ N).card : ℝ) * (1 / (δ * N)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (1 / (δ * N)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le N _
    _ = 1 / δ := by field_simp [hδ.ne', hN0.ne']

/-- Exact identity expressing the symmetrized `affinePrimeShellCorrectionOfShift` at `X = N / n`
as the Mertens-weighted sum of `upwardShellModel φ c N m ⌈c⌉₊ (k * n)`. -/
theorem affinePrimeShellCorrection_symm_eq_sum_upwardShellModel
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc0 : 0 < c) {N m n : ℕ} (_hm : 1 ≤ m) (hn : n ∈ Icc 1 N) :
    (affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) +
      affinePrimeShellCorrectionOfShift m n (reflectedAffineShift m) φ c ((N : ℝ) / n)) / 2 =
      ∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, ((Λ k : ℝ) / k) * upwardShellModel φ c N m ⌈c⌉₊ (k * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hc_pos : 1 ≤ ⌈c⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hc0).ne'
  have hext_sum : ∀ shift : ℕ → ℕ,
      (∑ h ∈ Ico 1 ⌈c⌉₊, affineRamanujanPrimeShell m n (shift h) φ c h ((N : ℝ) / n)) =
        ∑ h ∈ Icc 1 ⌈c⌉₊, affineRamanujanPrimeShell m n (shift h) φ c h ((N : ℝ) / n) := by
    intro shift
    have htop_zero : affineRamanujanPrimeShell m n (shift ⌈c⌉₊) φ c ⌈c⌉₊ ((N : ℝ) / n) = 0 := by
      unfold affineRamanujanPrimeShell
      refine sum_eq_zero fun k hk => ?_
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
      have hk_le : (k : ℝ) ≤ (N : ℝ) / n :=
        (Nat.cast_le.mpr (mem_Icc.mp hk).2).trans (Nat.floor_le (div_nonneg hN0.le hn0.le))
      have harg1 : 1 ≤ (⌈c⌉₊ : ℝ) * ((N : ℝ) / n) / (c * k) := by
        rw [show (⌈c⌉₊ : ℝ) * ((N : ℝ) / n) / (c * k) =
          ((⌈c⌉₊ : ℝ) / c) * (((N : ℝ) / n) / k) by ring]
        exact one_le_mul_of_one_le_of_one_le ((one_le_div hc0).mpr (Nat.le_ceil c))
          ((one_le_div hk0).mpr hk_le)
      rw [shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (harg1.trans (le_abs_self _)), mul_zero]
    rw [← Finset.Ico_insert_right hc_pos, sum_insert (by simp), htop_zero, zero_add]
  unfold affinePrimeShellCorrectionOfShift
  rw [hext_sum id, hext_sum (reflectedAffineShift m), ← mul_add, ← sum_add_distrib]
  unfold affineRamanujanPrimeShell upwardShellModel
  simp_rw [← sum_add_distrib]
  rw [sum_comm, mul_sum, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
  rw [mul_sum, mul_sum, sum_div]
  refine sum_congr rfl fun j _ => ?_
  have href : reflectedAffineShift m j = (m - 1) * j := by
    unfold reflectedAffineShift; exact (Nat.sub_one_mul m j).symm
  have harg : (j : ℝ) * ((N : ℝ) / n) / (c * k) = (j : ℝ) * N / (c * (k * n : ℕ)) := by
    push_cast; field_simp [hn0.ne', hc0.ne', hk0.ne']
  simp only [id_eq, href, harg]; ring

/-- Pointwise BV bound `O(k / √n)` on any gap-shell correlation `α w < |log j - log n| ≤ β w`
against `normalizedRamanujanMode k` (`k ≥ 2`) for a bounded Lipschitz profile `K` on `[α, β]`. -/
private theorem abs_gapWindow_lipschitz_mode_le {K : ℝ → ℝ} {α β AK LK : ℝ}
    (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hAK0 : 0 ≤ AK) (hLK0 : 0 ≤ LK)
    (hAK : ∀ s ∈ Set.Icc α β, |K s| ≤ AK)
    (hLK : ∀ x ∈ Set.Icc α β, ∀ y ∈ Set.Icc α β, |K x - K y| ≤ LK * |x - y|)
    {k N n : ℕ} (hk : 2 ≤ k) (hn : n ∈ Icc 1 N) {c : ℝ} (hc0 : 0 < c) (hβw : β * (c / N) ≤ 2) :
    |∑ j ∈ (Icc 1 N).filter (fun j => j ≠ n ∧
        α * (c / N) < |Real.log (j : ℝ) - Real.log n| ∧
        |Real.log (j : ℝ) - Real.log n| ≤ β * (c / N)),
      K (|Real.log (j : ℝ) - Real.log n| / (c / N)) *
        normalizedRamanujanMode k j / Real.sqrt j| ≤
      2 * (2 * Real.exp 1 * AK + 2 * β * Real.exp 5 * LK) * (k : ℝ) / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hβ0 : 0 ≤ β := hα0.trans hαβ
  let W := (Icc 1 N).filter (fun j => j ≠ n ∧
    α * (c / N) < |Real.log (j : ℝ) - Real.log n| ∧ |Real.log (j : ℝ) - Real.log n| ≤ β * (c / N))
  have hpt_sj : ∀ j ∈ W, 1 / Real.sqrt (j : ℝ) ≤ Real.exp 1 / Real.sqrt n := by
    intro j hj
    obtain ⟨hjI, _, _, hhi⟩ := mem_filter.mp hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
    have hlow : Real.log n - 2 ≤ Real.log j := by linarith only [(abs_le.mp hhi).1, hβw]
    have hexp : (n : ℝ) * Real.exp (-2) ≤ j := by
      rw [← Real.exp_log hn0, ← Real.exp_add, ← Real.exp_log hj0]
      exact Real.exp_le_exp.mpr (by linarith only [hlow])
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hj0) hsn, one_mul]
    calc Real.sqrt (n : ℝ) = Real.sqrt ((n : ℝ) * Real.exp (-2)) * Real.exp 1 := by
          have he2 : Real.exp (-2) = Real.exp (-1) ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
          rw [Real.sqrt_mul hn0.le, he2, Real.sqrt_sq (Real.exp_pos _).le,
            mul_assoc, ← Real.exp_add]
          norm_num
      _ ≤ Real.sqrt j * Real.exp 1 := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hexp) (Real.exp_pos 1).le
      _ = Real.exp 1 * Real.sqrt j := mul_comm _ _
  have hpt_arg : ∀ j ∈ W, |Real.log (j : ℝ) - Real.log n| / (c / N) ∈ Set.Icc α β := fun j hj => by
    obtain ⟨_, _, hlo, hhi⟩ := mem_filter.mp hj
    exact ⟨((le_div_iff₀ hw0).mpr hlo.le), (div_le_iff₀ hw0).mpr hhi⟩
  have hcard_W : (W.card : ℝ) ≤ 2 * β * Real.exp 2 * (c * n / N) := by
    let r := (n : ℝ) * (β * (c / N) * Real.exp 2)
    have hr0 : 0 ≤ r := by dsimp only [r]; positivity
    have hsub : W ⊆ (Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ r) := by
      intro j hj
      obtain ⟨hjI, hjn, _, hhi⟩ := mem_filter.mp hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
      have he : Real.exp (β * (c / N)) - 1 ≤ β * (c / N) * Real.exp 2 :=
        exp_sub_one_le_mul_exp.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hβw) (by positivity))
      exact mem_filter.mpr ⟨hjI, hjn, (abs_sub_le_of_abs_log_le hj0 hn0 hhi).trans
        (mul_le_mul_of_nonneg_left he hn0.le)⟩
    exact ((show (W.card : ℝ) ≤ _ by exact_mod_cast card_le_card hsub).trans
      (card_near_le (Icc 1 N) n hr0)).trans_eq (by dsimp only [r]; ring)
  let w_n : ℕ → ℝ := fun j => K (|Real.log (j : ℝ) - Real.log n| / (c / N)) / Real.sqrt j
  have hsub_bv : ∀ a b : ℕ, Ico a b ⊆ W →
      |∑ j ∈ Ico a b, w_n j * normalizedRamanujanMode k j| ≤
        (2 * Real.exp 1 * AK + 2 * β * Real.exp 5 * LK) * (k : ℝ) / Real.sqrt n := by
    intro a b hsub
    have hbv := abs_sum_Ico_mode_bv_le hk w_n a b
    have ht1 : (if a < b then |w_n (b - 1)| else 0) ≤ Real.exp 1 * AK / Real.sqrt n := by
      split_ifs with hab
      · have hbm : b - 1 ∈ W := hsub (mem_Ico.mpr ⟨by omega, by omega⟩)
        dsimp only [w_n]
        rw [div_eq_mul_one_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt ((b - 1 : ℕ) : ℝ))]
        exact (mul_le_mul (hAK _ (hpt_arg _ hbm)) (hpt_sj _ hbm) (by positivity) hAK0).trans_eq (by ring)
      · positivity
    have ht2 : (∑ j ∈ Ico a (b - 1), |w_n j - w_n (j + 1)|) ≤
        (Real.exp 1 * AK + 2 * β * Real.exp 5 * LK) / Real.sqrt n := by
      rcases le_or_gt (b - 1) a with hba' | hab'
      · rw [Ico_eq_empty (not_lt.mpr hba'), sum_empty]; positivity
      have hstep : ∀ j ∈ Ico a (b - 1), |w_n j - w_n (j + 1)| ≤
          (LK * Real.exp 2 * (N / (c * n))) * (Real.exp 1 / Real.sqrt n) +
            AK * (1 / Real.sqrt j - 1 / Real.sqrt (j + 1 : ℕ)) := by
        intro j hj
        obtain ⟨haj, _⟩ := mem_Ico.mp hj
        have hjm : j ∈ W := hsub (mem_Ico.mpr ⟨haj, by omega⟩)
        have hj1m : j + 1 ∈ W := hsub (mem_Ico.mpr ⟨by omega, by omega⟩)
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hjm).1).1
        have hj20 : (0 : ℝ) < (j + 1 : ℕ) := by positivity
        have hsj := hpt_sj j hjm
        have hinv_j : 1 / (j : ℝ) ≤ Real.exp 2 / n := by
          have hsq := pow_le_pow_left₀ (by positivity) hsj 2
          rwa [div_pow, div_pow, one_pow, Real.sq_sqrt hj0.le, Real.sq_sqrt hn0.le,
            show Real.exp 1 ^ 2 = Real.exp 2 by rw [sq, ← Real.exp_add]; norm_num] at hsq
        have hlog_step : |Real.log ((j + 1 : ℕ) : ℝ) - Real.log j| ≤ 1 / (j : ℝ) := by
          rw [← Real.log_div hj20.ne' hj0.ne',
            abs_of_nonneg (Real.log_nonneg ((one_le_div hj0).mpr (by exact_mod_cast Nat.le_succ j)))]
          have hl := Real.log_le_sub_one_of_pos (div_pos hj20 hj0)
          have hq : ((j + 1 : ℕ) : ℝ) / j - 1 = 1 / (j : ℝ) := by field_simp [hj0.ne']; push_cast; ring
          linarith only [hl, hq]
        have harg_diff : |(|Real.log (j : ℝ) - Real.log n| / (c / N) -
            |Real.log ((j + 1 : ℕ) : ℝ) - Real.log n| / (c / N))| ≤ Real.exp 2 * (N / (c * n)) := by
          rw [← sub_div, abs_div, abs_of_pos hw0]
          have hrev := abs_abs_sub_abs_le_abs_sub (Real.log (j : ℝ) - Real.log n)
            (Real.log ((j + 1 : ℕ) : ℝ) - Real.log n)
          rw [show (Real.log (j : ℝ) - Real.log n) - (Real.log ((j + 1 : ℕ) : ℝ) - Real.log n) =
            -(Real.log ((j + 1 : ℕ) : ℝ) - Real.log j) by ring, abs_neg] at hrev
          exact ((div_le_div_of_nonneg_right (hrev.trans hlog_step) hw0.le).trans
            (div_le_div_of_nonneg_right hinv_j hw0.le)).trans_eq (by field_simp [hn0.ne', hc0.ne', hN0.ne'])
        have hK_diff : |K (|Real.log (j : ℝ) - Real.log n| / (c / N)) -
            K (|Real.log ((j + 1 : ℕ) : ℝ) - Real.log n| / (c / N))| ≤
            LK * Real.exp 2 * (N / (c * n)) :=
          (hLK _ (hpt_arg j hjm) _ (hpt_arg (j + 1) hj1m)).trans
            ((mul_le_mul_of_nonneg_left harg_diff hLK0).trans_eq (by ring))
        have hs_mono : 0 ≤ 1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ) :=
          sub_nonneg.mpr (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hj0)
            (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ j)))
        have hsplit : w_n j - w_n (j + 1) =
            (K (|Real.log (j : ℝ) - Real.log n| / (c / N)) -
              K (|Real.log ((j + 1 : ℕ) : ℝ) - Real.log n| / (c / N))) * (1 / Real.sqrt j) +
            K (|Real.log ((j + 1 : ℕ) : ℝ) - Real.log n| / (c / N)) *
              (1 / Real.sqrt j - 1 / Real.sqrt (j + 1 : ℕ)) := by dsimp only [w_n]; ring
        rw [hsplit]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
          exact mul_le_mul hK_diff hsj (by positivity) (by positivity)
        · rw [abs_mul, abs_of_nonneg hs_mono]
          exact mul_le_mul_of_nonneg_right (hAK _ (hpt_arg (j + 1) hj1m)) hs_mono
      have htel : (∑ j ∈ Ico a (b - 1), (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ))) ≤
          Real.exp 1 / Real.sqrt n := by
        have htel_eq : ∀ r : ℕ, (∑ j ∈ Ico a (a + r),
            (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ))) =
            1 / Real.sqrt (a : ℝ) - 1 / Real.sqrt ((a + r : ℕ) : ℝ) := by
          intro r; induction r with
          | zero => simp
          | succ r ih => rw [show a + (r + 1) = (a + r) + 1 by omega, sum_Ico_succ_top (by omega), ih]; ring
        obtain ⟨r, hr⟩ : ∃ r : ℕ, b - 1 = a + r := ⟨b - 1 - a, by omega⟩
        rw [hr, htel_eq r]
        have ham : a ∈ W := hsub (mem_Ico.mpr ⟨le_rfl, by omega⟩)
        linarith only [hpt_sj a ham, (by positivity : 0 ≤ 1 / Real.sqrt ((a + r : ℕ) : ℝ))]
      have hcard_ico : ((Ico a (b - 1)).card : ℝ) ≤ 2 * β * Real.exp 2 * (c * n / N) := by
        have hsub' : Ico a (b - 1) ⊆ W := (Ico_subset_Ico_right (Nat.sub_le b 1)).trans hsub
        exact (Nat.cast_le.mpr (card_le_card hsub')).trans hcard_W
      have hexp5 : Real.exp 2 * Real.exp 2 * Real.exp 1 = Real.exp 5 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      calc (∑ j ∈ Ico a (b - 1), |w_n j - w_n (j + 1)|)
          ≤ ((Ico a (b - 1)).card : ℝ) * ((LK * Real.exp 2 * (N / (c * n))) * (Real.exp 1 / Real.sqrt n)) +
              AK * ∑ j ∈ Ico a (b - 1), (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) := by
            refine (sum_le_sum hstep).trans_eq ?_
            rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
        _ ≤ (2 * β * Real.exp 2 * (c * n / N)) *
              ((LK * Real.exp 2 * (N / (c * n))) * (Real.exp 1 / Real.sqrt n)) +
              AK * (Real.exp 1 / Real.sqrt n) :=
            add_le_add (mul_le_mul_of_nonneg_right hcard_ico (by positivity))
              (mul_le_mul_of_nonneg_left htel hAK0)
        _ = (Real.exp 1 * AK + 2 * β * Real.exp 5 * LK) / Real.sqrt n := by
            field_simp [hc0.ne', hn0.ne', hN0.ne', hsn.ne']; rw [← hexp5]; ring
    calc |∑ j ∈ Ico a b, w_n j * normalizedRamanujanMode k j|
        ≤ (k : ℝ) * (Real.exp 1 * AK / Real.sqrt n +
            (Real.exp 1 * AK + 2 * β * Real.exp 5 * LK) / Real.sqrt n) :=
          hbv.trans (mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (Nat.cast_nonneg k))
      _ = (2 * Real.exp 1 * AK + 2 * β * Real.exp 5 * LK) * (k : ℝ) / Real.sqrt n := by ring
  let P_lo : ℕ → Prop := fun j => 1 ≤ j ∧ α * (c / N) < Real.log n - Real.log j ∧
    Real.log n - Real.log j ≤ β * (c / N)
  let P_hi : ℕ → Prop := fun j => 1 ≤ j ∧ α * (c / N) < Real.log j - Real.log n ∧
    Real.log j - Real.log n ≤ β * (c / N)
  have hconv_lo : ∀ ⦃i j r : ℕ⦄, i ≤ j → j ≤ r → P_lo i → P_lo r → P_lo j := by
    intro i j r hij hjr hi hr
    have hj1 : 1 ≤ j := hi.1.trans hij
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    exact ⟨hj1, by linarith [hr.2.1, Real.log_le_log hj0 (Nat.cast_le.mpr hjr)],
      by linarith [hi.2.2, Real.log_le_log hi0 (Nat.cast_le.mpr hij)]⟩
  have hconv_hi : ∀ ⦃i j r : ℕ⦄, i ≤ j → j ≤ r → P_hi i → P_hi r → P_hi j := by
    intro i j r hij hjr hi hr
    have hj1 : 1 ≤ j := hi.1.trans hij
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    exact ⟨hj1, by linarith [hi.2.1, Real.log_le_log hi0 (Nat.cast_le.mpr hij)],
      by linarith [hr.2.2, Real.log_le_log hj0 (Nat.cast_le.mpr hjr)]⟩
  let S_lo := (Ico 1 n).filter P_lo
  let S_hi := (Ico (n + 1) (N + 1)).filter P_hi
  have hdisj : Disjoint S_lo S_hi := disjoint_left.mpr fun j h1 h2 => by
    have := (mem_Ico.mp (mem_filter.mp h1).1).2; have := (mem_Ico.mp (mem_filter.mp h2).1).1; omega
  have hsplit_W : W = S_lo ∪ S_hi := by
    ext j; simp only [W, S_lo, S_hi, P_lo, P_hi, mem_union, mem_filter, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨⟨hj1, hjN⟩, hjn, hlo, hhi⟩
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      rcases lt_or_gt_of_ne hjn with hlt | hgt
      · have hneg : Real.log (j : ℝ) - Real.log n < 0 :=
          sub_neg.mpr (Real.log_lt_log hj0 (by exact_mod_cast hlt))
        rw [abs_of_neg hneg, neg_sub] at hlo hhi
        exact Or.inl ⟨⟨hj1, hlt⟩, hj1, hlo, hhi⟩
      · have hpos : 0 < Real.log (j : ℝ) - Real.log n :=
          sub_pos.mpr (Real.log_lt_log hn0 (by exact_mod_cast hgt))
        rw [abs_of_pos hpos] at hlo hhi
        exact Or.inr ⟨⟨by omega, by omega⟩, hj1, hlo, hhi⟩
    · rintro (⟨⟨hj1, hlt⟩, _, hlo, hhi⟩ | ⟨⟨hgt, hjN⟩, hj1, hlo, hhi⟩)
      · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        have hneg : Real.log (j : ℝ) - Real.log n < 0 :=
          sub_neg.mpr (Real.log_lt_log hj0 (by exact_mod_cast hlt))
        refine ⟨⟨hj1, hlt.le.trans (mem_Icc.mp hn).2⟩, by omega, ?_, ?_⟩ <;>
          rwa [abs_of_neg hneg, neg_sub]
      · have hpos : 0 < Real.log (j : ℝ) - Real.log n :=
          sub_pos.mpr (Real.log_lt_log hn0 (by exact_mod_cast hgt))
        refine ⟨⟨hj1, by omega⟩, by omega, ?_, ?_⟩ <;> rwa [abs_of_pos hpos]
  obtain ⟨L₁, U₁, _, hlo_eq⟩ := filter_Ico_eq_Ico hconv_lo 1 n
  obtain ⟨L₂, U₂, _, hhi_eq⟩ := filter_Ico_eq_Ico hconv_hi (n + 1) (N + 1)
  have hsub1 : Ico L₁ U₁ ⊆ W := by rw [← hlo_eq, hsplit_W]; exact subset_union_left
  have hsub2 : Ico L₂ U₂ ⊆ W := by rw [← hhi_eq, hsplit_W]; exact subset_union_right
  have hrew : (∑ j ∈ W, K (|Real.log (j : ℝ) - Real.log n| / (c / N)) *
      normalizedRamanujanMode k j / Real.sqrt j) =
      (∑ j ∈ Ico L₁ U₁, w_n j * normalizedRamanujanMode k j) +
        ∑ j ∈ Ico L₂ U₂, w_n j * normalizedRamanujanMode k j := by
    have hpt : ∀ j : ℕ, K (|Real.log (j : ℝ) - Real.log n| / (c / N)) *
        normalizedRamanujanMode k j / Real.sqrt j = w_n j * normalizedRamanujanMode k j :=
      fun _ => by dsimp only [w_n]; ring
    simp_rw [hpt]; rw [hsplit_W, sum_union hdisj, ← hlo_eq, ← hhi_eq]
  change |∑ j ∈ W, _| ≤ _
  rw [hrew]
  exact ((abs_add_le _ _).trans (add_le_add (hsub_bv L₁ U₁ hsub1) (hsub_bv L₂ U₂ hsub2))).trans_eq
    (by ring)



/-- Logarithm-free `ℓ²` norm bound on the exterior downward boundary piece
`(√φ(m))⁻¹ • normalizedExteriorDownwardVector φ c N m` (`m ≥ 1`). -/
theorem exteriorDownward_norm_sq_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m N : ℕ} {c : ℝ}
    (hm : 0 < m) (hc1 : 1 ≤ c) (hL1 : 1 ≤ Real.log (N : ℝ))
    (hradN : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N) :
    ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
      ((Real.exp 1 + 2) * (5 * (Real.exp 1 + 1)) ^ 2) * (m : ℝ) * (c ^ 3 * Real.log N / N) := by
  let C_q : ℝ := (Real.exp 1 + 2) * (5 * (Real.exp 1 + 1)) ^ 2
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [h0]
    exact_mod_cast this.trans hradN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    have hcR : c ≤ linearNearRowRadius c := by
      unfold linearNearRowRadius
      have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      nlinarith only [hc0, he2]
    exact (div_le_one hN0).mpr (by nlinarith only [hcR, h0, hradN])
  have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hw1
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw0
  have hgc : HasCompactSupport (atomDilate φ (c / N)) := HasCompactSupport.intro isCompact_Icc hgsupp
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  have hB_le : (linearPrimeStrip c : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
  have hcut_ub : (exteriorPrimeCutoff c N : ℝ) ≤ 5 * (N : ℝ) := by
    have h1 : (exteriorPrimeCutoff c N : ℝ) ≤ (N : ℝ) + linearPrimeStrip c := by
      exact_mod_cast (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw1).2
    have he1 : Real.exp 1 ≤ 3 := by have h := Real.exp_one_lt_d9; linarith
    nlinarith only [h1, hB_le, hcN, he1, hc0]
  have hrow_reg : ∀ n : ℕ, |regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N m n| ≤
      5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N := fun n => by
    have hcard : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ linearPrimeStrip c := by
      have hbound := (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw1).2
      rw [Nat.card_Ioc]; exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ linearPrimeStrip c by omega)
    have hterm : ∀ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
        |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
          (bumpCorr (atomDilate φ (c / N)) (Real.log ℓ - Real.log n) /
            (∫ u, (atomDilate φ (c / N)) u ^ 2))| ≤
          5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
      intro ℓ hℓ
      obtain ⟨hNℓ, hℓ_hi⟩ := mem_Ioc.mp hℓ
      have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le N) hNℓ)
      have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
      have hℓ_5N : (ℓ : ℝ) ≤ 5 * (N : ℝ) :=
        (by exact_mod_cast hℓ_hi : (ℓ : ℝ) ≤ exteriorPrimeCutoff c N).trans hcut_ub
      have hlogℓ : Real.log ℓ ≤ 5 * Real.log N := by
        have hl := Real.log_le_log hℓ0 hℓ_5N
        rw [Real.log_mul (by norm_num) hN0.ne'] at hl
        have hl5 : Real.log 5 ≤ 4 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5); linarith
        linarith only [hl, hl5, hL1]
      have hcorr : |bumpCorr (atomDilate φ (c / N)) (Real.log ℓ - Real.log n) /
          (∫ u, (atomDilate φ (c / N)) u ^ 2)| ≤ 1 := by
        rw [abs_div, abs_of_pos hG, div_le_one hG]
        exact abs_bumpCorr_le hg.continuous hgc _
      have hjet : |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ| ≤
          5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
        rw [abs_div, abs_of_pos hsℓ]
        calc |horizonRamanujanMangoldt m N ℓ| / Real.sqrt ℓ
            ≤ ((m.totient : ℝ) * Real.log ℓ) / Real.sqrt ℓ :=
              div_le_div_of_nonneg_right (abs_horizonRamanujanMangoldt_le m N ℓ) hsℓ.le
          _ ≤ ((m.totient : ℝ) * (5 * Real.log N)) / Real.sqrt N :=
              (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogℓ (Nat.cast_nonneg _)) hsℓ.le).trans
                (div_le_div_of_nonneg_left (by positivity) hsN (Real.sqrt_le_sqrt (by exact_mod_cast hNℓ.le)))
          _ = 5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by ring
      rw [abs_mul]; simpa only [mul_one] using mul_le_mul hjet hcorr (abs_nonneg _) (by positivity)
    unfold regroupedExteriorDownwardPrimeRow
    exact ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)).trans
      (by rw [sum_const, nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq (by ring))
  let S := (Icc 1 N).filter (fun n => N - linearPrimeStrip c ≤ n)
  have hrestrict : (∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) =
      ∑ n ∈ S, regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N m n ^ 2 := by
    unfold actualExteriorDownwardRow
    rw [sum_congr rfl fun n hn => congrArg (· ^ 2) (downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m)]
    symm
    refine sum_subset (filter_subset _ _) fun n hn hnS => ?_
    have hout : n < N - linearPrimeStrip c := lt_of_not_ge fun h => hnS (mem_filter.mpr ⟨hn, h⟩)
    rw [regroupedExteriorDownwardPrimeRow_eq_zero_small_width hc0 hn hgsupp hw1 hout m, zero_pow (by decide)]
  have hcard_S : (S.card : ℝ) ≤ (Real.exp 1 + 2) * c := by
    have hcontain : S ⊆ Icc (N - linearPrimeStrip c) N := fun n hn =>
      mem_Icc.mpr ⟨(mem_filter.mp hn).2, (mem_Icc.mp (mem_filter.mp hn).1).2⟩
    have hnat : S.card ≤ linearPrimeStrip c + 1 := by
      have h := card_le_card hcontain; rw [Nat.card_Icc] at h; omega
    linarith only [(by exact_mod_cast hnat : (S.card : ℝ) ≤ (linearPrimeStrip c : ℝ) + 1), hB_le, hc1]
  have hsum_raw : (∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) ≤
      C_q * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.log N ^ 2 / N := by
    rw [hrestrict]
    have hcoef : 5 * (m.totient : ℝ) * linearPrimeStrip c ≤ 5 * (m.totient : ℝ) * ((Real.exp 1 + 1) * c) :=
      mul_le_mul_of_nonneg_left hB_le (by positivity)
    calc (∑ n ∈ S, regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N m n ^ 2)
        ≤ ∑ _n ∈ S, (5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N) ^ 2 :=
          sum_le_sum fun n _ => by have h := mul_self_le_mul_self (abs_nonneg _) (hrow_reg n); rwa [← sq, sq_abs, ← sq] at h
      _ ≤ ((Real.exp 1 + 2) * c) * ((5 * (m.totient : ℝ) * ((Real.exp 1 + 1) * c)) ^ 2 * Real.log N ^ 2 / N) := by
          rw [sum_const, nsmul_eq_mul, div_pow, mul_pow, Real.sq_sqrt hN0.le]
          exact mul_le_mul hcard_S (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcoef 2) (sq_nonneg _)) hN0.le)
            (by positivity) (by positivity)
      _ = C_q * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.log N ^ 2 / N := by dsimp only [C_q]; ring
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt htot_pos.le,
    normalizedExteriorDownwardVector_norm_sq]
  calc (m.totient : ℝ)⁻¹ * ((∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) / Real.log N)
      ≤ (m.totient : ℝ)⁻¹ * ((C_q * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.log N ^ 2 / N) / Real.log N) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum_raw hL0.le) (by positivity)
    _ = C_q * (m.totient : ℝ) * (c ^ 3 * Real.log N / N) := by field_simp [htot_pos.ne', hN0.ne', hL0.ne']
    _ ≤ C_q * (m : ℝ) * (c ^ 3 * Real.log N / N) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htot_le (by dsimp only [C_q]; positivity)) (by positivity)

/-- Subchannel 3a (`m ≥ 1`): Channels 1, 2, 5, and the exterior downward piece of Channel 6 vanish
in `(log N / c²) * topWindowResidualMass` along any critical curve. -/
theorem tendsto_topWindow_bulk_subchannels {m : ℕ} (hm : 1 ≤ m) (δ : ℝ)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (-(Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
            (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) +
          completeWeilSelfError tiltedUnitSpline (c N) N • normalizedRamanujanHorizonVector m N +
          Matrix.toEuclideanLin (fullWeilPoleErrorMatrix tiltedUnitSpline (c N) N)
            (normalizedRamanujanHorizonVector m N) -
          (Real.sqrt (m.totient : ℝ))⁻¹ •
            normalizedExteriorDownwardVector tiltedUnitSpline (c N) N m)) atTop (𝓝 0) := by
  have hm0 : 0 < m := by omega
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_quad_bound
  obtain ⟨Cs, hCs, hs⟩ := exists_selfError_quad_bound hφ hsupp hM
  obtain ⟨Cq, hCq, hq⟩ := exists_poleError_quadratic_conductor_bound hφ hsupp hM
  let C_ext : ℝ := (Real.exp 1 + 2) * (5 * (Real.exp 1 + 1)) ^ 2
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hinv_c2 : Tendsto (fun N : ℕ => 1 / c N ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hcinf)
  have hl1 := criticalCurve_pow_log_div_natCast hc hR hcrit 0 1
  simp only [pow_zero, one_mul, pow_one] at hl1
  have hl2 := criticalCurve_pow_log_div_natCast hc hR hcrit 8 3
  have hl3 := criticalCurve_pow_log_div_natCast hc hR hcrit 1 2
  simp only [pow_one] at hl3
  have hlim := (((hinv_c2.const_mul (4 * Cp * ((m : ℝ) * (1 + Real.log m) ^ 2))).add
      (hl1.const_mul (4 * Cs * m))).add (hl2.const_mul (4 * Cq * m))).add
      (hl3.const_mul (4 * C_ext * m))
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) ?_ hlim
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_below_overlap_pair_admissible hc hR hcrit, hlog] with N hadm hL1
  obtain ⟨_, _, hradN, hc4N⟩ := hadm 1 1 (by simpa using hc N) (by simpa using hc N)
  have hc1 := hc N
  have hc0 : 0 < c N := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hcN : c N ≤ N := (le_self_pow₀ hc1 (by norm_num : 4 ≠ 0)).trans hc4N
  have hN1 : 1 ≤ N := by exact_mod_cast hc1.trans hcN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN_sq : (N : ℝ) ≤ (N : ℝ) ^ 2 := le_self_pow₀ (by exact_mod_cast hN1) (by norm_num)
  let v_m := normalizedRamanujanHorizonVector m N
  let u₁ := Matrix.toEuclideanLin (fullPrimeMatrix N) v_m - (Real.log N - ramanujanAdjunctionEnergy m) • v_m
  let u₂ := completeWeilSelfError tiltedUnitSpline (c N) N • v_m
  let u₅ := Matrix.toEuclideanLin (fullWeilPoleErrorMatrix tiltedUnitSpline (c N) N) v_m
  let u_ext := (Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector tiltedUnitSpline (c N) N m
  have hnorm4 : ‖-u₁ + u₂ + u₅ - u_ext‖ ^ 2 ≤ 4 * (‖u₁‖ ^ 2 + ‖u₂‖ ^ 2 + ‖u₅‖ ^ 2 + ‖u_ext‖ ^ 2) := by
    have htri : ‖-u₁ + u₂ + u₅ - u_ext‖ ≤ ‖u₁‖ + ‖u₂‖ + ‖u₅‖ + ‖u_ext‖ := by
      rw [sub_eq_add_neg]
      have t1 := norm_add_le (-u₁ + u₂ + u₅) (-u_ext)
      have t2 := norm_add_le (-u₁ + u₂) u₅
      have t3 := norm_add_le (-u₁) u₂
      rw [norm_neg] at t1 t3
      linarith only [t1, t2, t3]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith only [hsq, sq_nonneg (‖u₁‖ - ‖u₂‖), sq_nonneg (‖u₁‖ - ‖u₅‖), sq_nonneg (‖u₁‖ - ‖u_ext‖),
      sq_nonneg (‖u₂‖ - ‖u₅‖), sq_nonneg (‖u₂‖ - ‖u_ext‖), sq_nonneg (‖u₅‖ - ‖u_ext‖)]
  have hb1 : (Real.log (N : ℝ) / c N ^ 2) * ‖u₁‖ ^ 2 ≤
      4 / 4 * (Cp * ((m : ℝ) * (1 + Real.log m) ^ 2) * (1 / c N ^ 2)) := by
    exact (mul_le_mul_of_nonneg_left (hp m hm0 N) (by positivity)).trans_eq (by field_simp [hL0.ne', hc0.ne'])
  have hb2 : (Real.log (N : ℝ) / c N ^ 2) * ‖u₂‖ ^ 2 ≤ Cs * (m : ℝ) * (Real.log N / N) := by
    calc (Real.log (N : ℝ) / c N ^ 2) * ‖u₂‖ ^ 2
        ≤ (Real.log (N : ℝ) / c N ^ 2) * (Cs * (m : ℝ) * c N ^ 2 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hs m hm0 N hN1 hL1 (c N) hc0 hcN) (by positivity)
      _ = Cs * (m : ℝ) * Real.log N / (N : ℝ) ^ 2 := by field_simp [hc0.ne']
      _ ≤ Cs * (m : ℝ) * (Real.log N / N) := by
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left hL0.le hN0 hN_sq) (by positivity)
  have hb5 : (Real.log (N : ℝ) / c N ^ 2) * ‖u₅‖ ^ 2 ≤ Cq * (m : ℝ) * (c N ^ 8 * Real.log N ^ 3 / N) := by
    calc (Real.log (N : ℝ) / c N ^ 2) * ‖u₅‖ ^ 2
        ≤ (Real.log (N : ℝ) / c N ^ 2) * (Cq * (m : ℝ) * c N ^ 10 * (Real.log N / N) ^ 2) :=
          mul_le_mul_of_nonneg_left (hq m hm0 (c N) hc1 N hN1 hL1 hcN) (by positivity)
      _ = Cq * (m : ℝ) * (c N ^ 8 * Real.log N ^ 3 / (N : ℝ) ^ 2) := by field_simp [hc0.ne']
      _ ≤ Cq * (m : ℝ) * (c N ^ 8 * Real.log N ^ 3 / N) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hN0 hN_sq) (by positivity)
  have hb_ext : (Real.log (N : ℝ) / c N ^ 2) * ‖u_ext‖ ^ 2 ≤ C_ext * (m : ℝ) * (c N * Real.log N ^ 2 / N) := by
    calc (Real.log (N : ℝ) / c N ^ 2) * ‖u_ext‖ ^ 2
        ≤ (Real.log (N : ℝ) / c N ^ 2) * (C_ext * (m : ℝ) * (c N ^ 3 * Real.log N / N)) :=
          mul_le_mul_of_nonneg_left (exteriorDownward_norm_sq_le hφ hsupp hM hm0 hc1 hL1 hradN) (by positivity)
      _ = C_ext * (m : ℝ) * (c N * Real.log N ^ 2 / N) := by field_simp [hc0.ne']
  calc (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N (-u₁ + u₂ + u₅ - u_ext)
      ≤ (Real.log (N : ℝ) / c N ^ 2) * (4 * (‖u₁‖ ^ 2 + ‖u₂‖ ^ 2 + ‖u₅‖ ^ 2 + ‖u_ext‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left ((topWindowResidualMass_le_norm_sq δ N _).trans hnorm4) (by positivity)
    _ = 4 * ((Real.log (N : ℝ) / c N ^ 2) * ‖u₁‖ ^ 2 + (Real.log (N : ℝ) / c N ^ 2) * ‖u₂‖ ^ 2 +
          (Real.log (N : ℝ) / c N ^ 2) * ‖u₅‖ ^ 2 + (Real.log (N : ℝ) / c N ^ 2) * ‖u_ext‖ ^ 2) := by ring
    _ ≤ _ := by linarith only [hb1, hb2, hb5, hb_ext]

private lemma nearRowIndices_eq_gapWindow {c : ℝ} {N n : ℕ} (hn : n ∈ Icc 1 N) :
    nearRowIndices c N n = (Icc 1 N).filter (fun j => j ≠ n ∧
      0 * (c / N) < |Real.log (j : ℝ) - Real.log n| ∧
      |Real.log (j : ℝ) - Real.log n| ≤ 2 * (c / N)) := by
  ext j; simp only [nearRowIndices, mem_filter, zero_mul, mul_div_assoc]
  refine ⟨fun ⟨hj, hne, hle⟩ => ⟨hj, hne, ?_, hle⟩, fun ⟨hj, hne, _, hle⟩ => ⟨hj, hne, hle⟩⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  refine abs_pos.mpr (sub_ne_zero.mpr ?_)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (Real.log_lt_log hj0 (by exact_mod_cast hlt)).ne
  · exact (Real.log_lt_log hn0 (by exact_mod_cast hgt)).ne'

/-- Nonpolar (`m ≥ 2`) near-Gamma row after removing the pole component `(Λ(m)/√φ(m)) * nearPoleRow`. -/
private def nearGammaNonpolarRemRow (φ : ℝ → ℝ) (c : ℝ) (N m n : ℕ) : ℝ :=
  (Real.sqrt (m.totient : ℝ))⁻¹ * nearGammaDownwardRow φ c N m n -
    (Λ m / Real.sqrt (m.totient : ℝ)) * nearPoleRow φ c N n

/-- Exact algebraic decomposition of `nearGammaNonpolarRemRow` at `m ≥ 2` into smooth gap-window
mode correlations (`k ≥ 2`) and `O(c / N)` pair remainders. -/
private lemma nearGammaNonpolarRemRow_eq {φ : ℝ → ℝ} {c : ℝ} (hc0 : 0 < c)
    {N m n : ℕ} (hm2 : 2 ≤ m) (hN0 : (0 : ℝ) < N) :
    nearGammaNonpolarRemRow φ c N m n =
      (∑ j ∈ nearRowIndices c N n,
          (nearKernel φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
            normalizedRamanujanMode m j / Real.sqrt j) +
      (∑ j ∈ nearRowIndices c N n,
          (nearArchimedeanRemainder φ (c / N) n j -
            nearKernel φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
            normalizedRamanujanMode m j / Real.sqrt j) +
      ((Real.log N - Real.log n - Real.log c) *
        nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n) +
      (∑ j ∈ nearRowIndices c N n,
          (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
            (Real.log n - Real.log j) * normalizedRamanujanMode m j / Real.sqrt j) +
      (∑ k ∈ m.divisors.erase 1, ramanujanJetConductorWeight m k *
          (Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) *
          nearGram φ c N (fun j => normalizedRamanujanMode k j / Real.sqrt j) n) := by
  have hm0 : 0 < m := by omega
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hstot_ne : Real.sqrt (m.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr htot_pos).ne'
  have hlog_eq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
  have h1_mem : (1 : ℕ) ∈ m.divisors := Nat.mem_divisors.mpr ⟨one_dvd m, hm0.ne'⟩
  have hw1 : ramanujanJetConductorWeight m 1 = Λ m := by
    simp [ramanujanJetConductorWeight, show (1 : ℕ) ≠ m by omega]
  have hjet_sum : (∑ j ∈ nearRowIndices c N n,
      (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
        (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ) / Real.sqrt j)) =
      (Λ m / Real.sqrt (m.totient : ℝ)) * nearPoleRow φ c N n +
      ∑ k ∈ m.divisors.erase 1, ramanujanJetConductorWeight m k *
        (Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) *
        nearGram φ c N (fun j => normalizedRamanujanMode k j / Real.sqrt j) n := by
    have hpt : ∀ j ∈ nearRowIndices c N n,
        (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
          (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ) / Real.sqrt j) =
        ∑ k ∈ m.divisors, ramanujanJetConductorWeight m k *
          (Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) *
          ((shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
            (normalizedRamanujanMode k j / Real.sqrt j)) := fun j _ => by
      rw [ramanujanLogDivisorJet_div_sqrt_eq hm0 j, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      unfold ramanujanPoleProfile; ring
    conv_lhs => rw [sum_congr rfl hpt, sum_comm, ← Finset.insert_erase h1_mem, sum_insert (Finset.notMem_erase 1 _)]
    congr 1
    · rw [hw1, Nat.totient_one, Nat.cast_one, Real.sqrt_one, ← mul_sum]
      unfold nearPoleRow nearGram
      have hmode1 : ∀ j : ℕ, normalizedRamanujanMode 1 j / Real.sqrt j = (Real.sqrt j)⁻¹ := fun j => by
        rw [normalizedRamanujanMode, TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient one_pos,
          ramanujanLagCoefficient_one, Nat.totient_one, Nat.cast_one, Real.sqrt_one]; ring
      simp_rw [hmode1]; ring
    · refine sum_congr rfl fun k _ => ?_
      rw [← mul_sum]; rfl
  unfold nearGammaNonpolarRemRow nearGammaDownwardRow
  have hmain : (Real.sqrt (m.totient : ℝ))⁻¹ *
      (∑ j ∈ nearRowIndices c N n, nearGammaDownwardCoefficient φ c N m n j / Real.sqrt j) =
      (∑ j ∈ nearRowIndices c N n,
          nearArchimedeanRemainder φ (c / N) n j * normalizedRamanujanMode m j / Real.sqrt j) +
      ((Real.log N - Real.log n - Real.log c) *
        nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n) +
      (∑ j ∈ nearRowIndices c N n,
          (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
            (Real.log n - Real.log j) * normalizedRamanujanMode m j / Real.sqrt j) +
      (∑ j ∈ nearRowIndices c N n,
          (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
            (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ) / Real.sqrt j)) := by
    unfold nearGram nearArchimedeanRemainder
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    dsimp only
    have hj1 := (mem_Icc.mp (mem_filter.mp hj).1).1
    rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m hj1,
      normalizedRamanujanMode, TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hm0,
      hlog_eq]
    field_simp [hstot_ne]; ring
  have hsplit_arch : (∑ j ∈ nearRowIndices c N n,
      nearArchimedeanRemainder φ (c / N) n j * normalizedRamanujanMode m j / Real.sqrt j) =
      (∑ j ∈ nearRowIndices c N n,
          (nearKernel φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
            normalizedRamanujanMode m j / Real.sqrt j) +
      (∑ j ∈ nearRowIndices c N n,
          (nearArchimedeanRemainder φ (c / N) n j -
            nearKernel φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
            normalizedRamanujanMode m j / Real.sqrt j) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun _ _ => by ring
  rw [hmain, hsplit_arch, hjet_sum]; ring

private lemma nearRowIndices_card_and_pointwise_local {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} {N n : ℕ}
    (hc0 : 0 < c) (hN0 : (0 : ℝ) < N) (hw1 : c / N ≤ 1) (hn : n ∈ Icc 1 N) :
    ((nearRowIndices c N n).card : ℝ) ≤ 2 * (n : ℝ) * (linearNearRowRadius c / N) ∧
    ∀ j ∈ nearRowIndices c N n,
      1 / Real.sqrt j ≤ Real.exp 1 / Real.sqrt n ∧
      |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| ≤ 1 := by
  have he_gap : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
    calc Real.exp (2 * c / N) - 1 ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
      _ ≤ 2 * c / N * Real.exp 2 := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by
            have h := mul_le_mul_of_nonneg_left hw1 zero_le_two
            simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
      _ = linearNearRowRadius c / N := by unfold linearNearRowRadius; ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hR0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have hrad0 : 0 ≤ (n : ℝ) * (linearNearRowRadius c / N) := by positivity
  have hcard_n : ((nearRowIndices c N n).card : ℝ) ≤ 2 * (n : ℝ) * (linearNearRowRadius c / N) := by
    have hsub : nearRowIndices c N n ⊆
        (Icc 1 N).filter (fun j : ℕ => j ≠ n ∧ |(j : ℝ) - n| ≤ (n : ℝ) * (linearNearRowRadius c / N)) := by
      intro j hj
      obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
      exact mem_filter.mpr ⟨hjN, hjn, (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans
        (mul_le_mul_of_nonneg_left he_gap hn0.le)⟩
    exact ((Nat.cast_le.mpr (card_le_card hsub)).trans (card_near_le (Icc 1 N) n hrad0)).trans_eq (by ring)
  refine ⟨hcard_n, fun j hj => ?_⟩
  obtain ⟨hjN, _, hlog⟩ := mem_filter.mp hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
  have hlow : Real.log n - 2 ≤ Real.log j := by
    have h2 : 2 * c / N ≤ 2 := by
      have h := mul_le_mul_of_nonneg_left hw1 zero_le_two
      simpa only [mul_div_assoc, mul_one] using h
    linarith only [(abs_le.mp hlog).1, h2]
  have hexp : (n : ℝ) * Real.exp (-2) ≤ j := by
    rw [← Real.exp_log hn0, ← Real.exp_add, ← Real.exp_log hj0]
    exact Real.exp_le_exp.mpr (by linarith only [hlow])
  have hsj : 1 / Real.sqrt (j : ℝ) ≤ Real.exp 1 / Real.sqrt n := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hj0) hsn, one_mul]
    calc Real.sqrt (n : ℝ) = Real.sqrt ((n : ℝ) * Real.exp (-2)) * Real.exp 1 := by
          have he2 : Real.exp (-2) = Real.exp (-1) ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
          rw [Real.sqrt_mul hn0.le, he2, Real.sqrt_sq (Real.exp_pos _).le, mul_assoc, ← Real.exp_add]
          norm_num
      _ ≤ Real.sqrt j * Real.exp 1 := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hexp) (Real.exp_pos 1).le
      _ = Real.exp 1 * Real.sqrt j := mul_comm _ _
  refine ⟨hsj, ?_⟩
  rw [abs_div, abs_of_pos hM, div_le_one hM]
  exact abs_shellAutocorr_le hφ hsupp _

private lemma nearGammaNonpolarRemRow_sq_le {m N n : ℕ} (hm2 : 2 ≤ m)
    {δ c AK LK : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc1 : 1 ≤ c)
    (hAK0 : 0 ≤ AK) (hLK0 : 0 ≤ LK)
    (hAK : ∀ ℓ ∈ Set.Icc 0 2, |nearKernel tiltedUnitSpline ℓ| ≤ AK)
    (hLK : ∀ x ∈ Set.Icc 0 2, ∀ y ∈ Set.Icc 0 2,
      |nearKernel tiltedUnitSpline x - nearKernel tiltedUnitSpline y| ≤ LK * |x - y|)
    {K_lip : NNReal} (hlip : LipschitzWith K_lip (shellAutocorr tiltedUnitSpline))
    (h8c : 8 * c ≤ N) (hn_top : n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N) :
    let M0 := ∫ u, tiltedUnitSpline u ^ 2
    let C_K := 2 * (2 * Real.exp 1 * (AK / M0) + 4 * Real.exp 5 * (LK / M0)) * m
    let C_G := 2 * (2 * Real.exp 1 * 1 + 4 * Real.exp 5 * ((K_lip : ℝ) / M0))
    let C_jet := ∑ k ∈ m.divisors.erase 1, ramanujanJetConductorWeight m k *
      (Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) * (C_G * k)
    let A_const := C_K + Real.log (1 / δ) * (C_G * m) + C_jet
    let B_const := C_G * m
    let D_const := 20 * Real.exp 3 * Real.sqrt m
    nearGammaNonpolarRemRow tiltedUnitSpline c N m n ^ 2 ≤
      (4 * A_const ^ 2 + 4 * B_const ^ 2 * Real.log c ^ 2) * (1 / (n : ℝ)) +
        2 * D_const ^ 2 * c ^ 2 * (c / N) ^ 2 * ((n : ℝ) / N ^ 2) := by
  intro M0 C_K C_G C_jet A_const B_const D_const
  have hm0 : 0 < m := by omega
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM : 0 < M0 := integral_tiltedUnitSpline_sq_pos
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by exact_mod_cast (by linarith only [hc1, h8c] : (1 : ℝ) ≤ N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw3 : c / N ≤ 1 / 3 := (div_le_iff₀ hN0).mpr (by linarith only [hc0, h8c])
  have hw1 : c / N ≤ 1 := hw3.trans (by norm_num)
  have hβw : 2 * (c / N) ≤ 2 := by linarith only [hw1]
  have hn : n ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn_top).1; omega, (mem_Ioc.mp hn_top).2⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hn_gt : δ * N < n := (Nat.lt_floor_add_one (δ * N)).trans_le
    (by exact_mod_cast (Nat.succ_le_of_lt (mem_Ioc.mp hn_top).1))
  obtain ⟨hcard_n, hpt_n⟩ := nearRowIndices_card_and_pointwise_local hφ hsupp hM hc0 hN0 hw1 hn
  have hnearGram_le : ∀ {k : ℕ}, 2 ≤ k →
      |nearGram tiltedUnitSpline c N (fun j => normalizedRamanujanMode k j / Real.sqrt j) n| ≤
        C_G * (k : ℝ) / Real.sqrt n := fun {k} hk => by
    unfold nearGram
    rw [nearRowIndices_eq_gapWindow hn]
    have hpt : ∀ j : ℕ, (shellAutocorr tiltedUnitSpline (|Real.log (j : ℝ) - Real.log n| / (c / N)) / M0) *
        (normalizedRamanujanMode k j / Real.sqrt j) =
        (shellAutocorr tiltedUnitSpline (|Real.log (j : ℝ) - Real.log n| / (c / N)) / M0) *
          normalizedRamanujanMode k j / Real.sqrt j := fun _ => by ring
    change |∑ j ∈ (_ : Finset ℕ), (shellAutocorr tiltedUnitSpline (|Real.log (j : ℝ) - Real.log n| / (c / N)) / M0) *
      (normalizedRamanujanMode k j / Real.sqrt j)| ≤ _
    simp_rw [hpt]
    exact (abs_gapWindow_lipschitz_mode_le (K := fun s => shellAutocorr tiltedUnitSpline s / M0)
      le_rfl (by norm_num : (0 : ℝ) ≤ 2) zero_le_one (div_nonneg (NNReal.coe_nonneg K_lip) hM.le)
      (fun s _ => by rw [abs_div, abs_of_pos hM, div_le_one hM]; exact abs_shellAutocorr_le hφ hsupp s)
      (fun x _ y _ => by
        rw [← sub_div, abs_div, abs_of_pos hM, div_le_iff₀ hM]
        have hd := hlip.dist_le_mul x y
        rw [Real.dist_eq, Real.dist_eq] at hd
        exact hd.trans_eq (by field_simp [hM.ne']))
      hk hn hc0 hβw).trans_eq (by dsimp only [C_G]; ring)
  rw [nearGammaNonpolarRemRow_eq hc0 hm2 hN0]
  have hb1 : |∑ j ∈ nearRowIndices c N n,
      (nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) / M0) *
        normalizedRamanujanMode m j / Real.sqrt j| ≤ C_K / Real.sqrt n := by
    rw [nearRowIndices_eq_gapWindow hn]
    exact (abs_gapWindow_lipschitz_mode_le (K := fun s => nearKernel tiltedUnitSpline s / M0)
      le_rfl (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hAK0 hM.le) (div_nonneg hLK0 hM.le)
      (fun s hs => by rw [abs_div, abs_of_pos hM]; exact div_le_div_of_nonneg_right (hAK s hs) hM.le)
      (fun x hx y hy => by
        rw [← sub_div, abs_div, abs_of_pos hM]
        exact (div_le_div_of_nonneg_right (hLK x hx y hy) hM.le).trans_eq (by ring))
      hm2 hn hc0 hβw).trans_eq (by dsimp only [C_K]; ring)
  have hb2 : |∑ j ∈ nearRowIndices c N n,
      (nearArchimedeanRemainder tiltedUnitSpline (c / N) n j -
        nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) / M0) *
        normalizedRamanujanMode m j / Real.sqrt j| ≤
      12 * Real.exp 3 * Real.sqrt m * (c ^ 2 * Real.sqrt n / N ^ 2) := by
    have hj_le : ∀ j ∈ nearRowIndices c N n,
        |(nearArchimedeanRemainder tiltedUnitSpline (c / N) n j -
          nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) / M0) *
          normalizedRamanujanMode m j / Real.sqrt j| ≤
        3 * (c / N) * Real.sqrt m * Real.exp 1 / Real.sqrt n := fun j hj => by
      have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
        simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
      have hrem := abs_nearArchimedeanRemainder_sub_le hφ hsupp hM hw0 hw3 hs
      obtain ⟨hsj, _⟩ := hpt_n j hj
      rw [div_eq_mul_one_div _ (Real.sqrt (j : ℝ)), abs_mul, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
      exact (mul_le_mul (mul_le_mul hrem (abs_mode_le_sqrt_conductor hm0 j) (abs_nonneg _) (by positivity))
        hsj (by positivity) (by positivity)).trans_eq (by ring)
    have hexp3 : Real.exp 2 * Real.exp 1 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
    calc _ ≤ ((nearRowIndices c N n).card : ℝ) * (3 * (c / N) * Real.sqrt m * Real.exp 1 / Real.sqrt n) := by
          rw [← nsmul_eq_mul, ← sum_const]; exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hj_le)
      _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) *
            (3 * (c / N) * Real.sqrt m * Real.exp 1 / Real.sqrt n) :=
          mul_le_mul_of_nonneg_right hcard_n (by positivity)
      _ = 12 * Real.exp 3 * Real.sqrt m * (c ^ 2 * Real.sqrt n / N ^ 2) := by
          unfold linearNearRowRadius; field_simp [hsn.ne', hN0.ne']
          rw [Real.sq_sqrt hn0.le, ← hexp3]; ring
  have hb3_log : |(Real.log N - Real.log n) *
      nearGram tiltedUnitSpline c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n| ≤
      Real.log (1 / δ) * (C_G * m) / Real.sqrt n := by
    have hnn : 0 ≤ Real.log (N : ℝ) - Real.log n :=
      sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast (mem_Icc.mp hn).2))
    have hub : Real.log (N : ℝ) - Real.log n ≤ Real.log (1 / δ) := by
      rw [← Real.log_div hN0.ne' hn0.ne']
      exact Real.log_le_log (div_pos hN0 hn0) ((div_le_div_iff₀ hn0 hδ0).mpr (by linarith only [hn_gt]))
    rw [abs_mul, abs_of_nonneg hnn]
    exact (mul_le_mul hub (hnearGram_le hm2) (abs_nonneg _)
      (Real.log_nonneg ((one_le_div hδ0).mpr hδ1.le))).trans_eq (by ring)
  have hb3_c : |-Real.log c *
      nearGram tiltedUnitSpline c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n| ≤
      Real.log c * B_const / Real.sqrt n := by
    rw [abs_mul, abs_neg, abs_of_nonneg (Real.log_nonneg hc1)]
    exact (mul_le_mul_of_nonneg_left (hnearGram_le hm2) (Real.log_nonneg hc1)).trans_eq
      (by dsimp only [B_const]; ring)
  have hb4 : |∑ j ∈ nearRowIndices c N n,
      (shellAutocorr tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) / M0) *
        (Real.log n - Real.log j) * normalizedRamanujanMode m j / Real.sqrt j| ≤
      8 * Real.exp 3 * Real.sqrt m * (c ^ 2 * Real.sqrt n / N ^ 2) := by
    have hj_le : ∀ j ∈ nearRowIndices c N n,
        |(shellAutocorr tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) / M0) *
          (Real.log n - Real.log j) * normalizedRamanujanMode m j / Real.sqrt j| ≤
        2 * (c / N) * Real.sqrt m * Real.exp 1 / Real.sqrt n := fun j hj => by
      obtain ⟨hsj, hq⟩ := hpt_n j hj
      have hs : |Real.log n - Real.log j| ≤ 2 * (c / N) := by
        rw [abs_sub_comm]; simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
      rw [div_eq_mul_one_div _ (Real.sqrt (j : ℝ)), abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
      exact (mul_le_mul (mul_le_mul (mul_le_mul hq hs (abs_nonneg _) zero_le_one)
        (abs_mode_le_sqrt_conductor hm0 j) (abs_nonneg _) (by positivity)) hsj
        (by positivity) (by positivity)).trans_eq (by ring)
    have hexp3 : Real.exp 2 * Real.exp 1 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
    calc _ ≤ ((nearRowIndices c N n).card : ℝ) * (2 * (c / N) * Real.sqrt m * Real.exp 1 / Real.sqrt n) := by
          rw [← nsmul_eq_mul, ← sum_const]; exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hj_le)
      _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) *
            (2 * (c / N) * Real.sqrt m * Real.exp 1 / Real.sqrt n) :=
          mul_le_mul_of_nonneg_right hcard_n (by positivity)
      _ = 8 * Real.exp 3 * Real.sqrt m * (c ^ 2 * Real.sqrt n / N ^ 2) := by
          unfold linearNearRowRadius; field_simp [hsn.ne', hN0.ne']
          rw [Real.sq_sqrt hn0.le, ← hexp3]; ring
  have hb5 : |∑ k ∈ m.divisors.erase 1, ramanujanJetConductorWeight m k *
      (Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) *
      nearGram tiltedUnitSpline c N (fun j => normalizedRamanujanMode k j / Real.sqrt j) n| ≤
      C_jet / Real.sqrt n := by
    calc _ ≤ ∑ k ∈ m.divisors.erase 1, |ramanujanJetConductorWeight m k *
          (Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) *
          nearGram tiltedUnitSpline c N (fun j => normalizedRamanujanMode k j / Real.sqrt j) n| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ m.divisors.erase 1, ramanujanJetConductorWeight m k *
          (Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) * (C_G * (k : ℝ) / Real.sqrt n) := by
          refine sum_le_sum fun k hk => ?_
          have hk_ne1 := (mem_erase.mp hk).1
          have hk_pos := Nat.pos_of_mem_divisors (mem_erase.mp hk).2
          have hk2 : 2 ≤ k := by omega
          rw [abs_mul, abs_of_nonneg (mul_nonneg (ramanujanJetConductorWeight_nonneg m k) (by positivity))]
          exact mul_le_mul_of_nonneg_left (hnearGram_le hk2)
            (mul_nonneg (ramanujanJetConductorWeight_nonneg m k) (by positivity))
      _ = C_jet / Real.sqrt n := by
          dsimp only [C_jet]; rw [sum_div]; refine sum_congr rfl fun _ _ => by ring
  set s₁ := ∑ j ∈ nearRowIndices c N n,
    (nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) / M0) *
      normalizedRamanujanMode m j / Real.sqrt j
  set s₂ := ∑ j ∈ nearRowIndices c N n,
    (nearArchimedeanRemainder tiltedUnitSpline (c / N) n j -
      nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) / M0) *
      normalizedRamanujanMode m j / Real.sqrt j
  set g_m := nearGram tiltedUnitSpline c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n
  set s₄ := ∑ j ∈ nearRowIndices c N n,
    (shellAutocorr tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) / M0) *
      (Real.log n - Real.log j) * normalizedRamanujanMode m j / Real.sqrt j
  set s₅ := ∑ k ∈ m.divisors.erase 1, ramanujanJetConductorWeight m k *
    (Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) *
    nearGram tiltedUnitSpline c N (fun j => normalizedRamanujanMode k j / Real.sqrt j) n
  set X_val := s₁ + (Real.log N - Real.log n) * g_m + s₅ + (-Real.log c * g_m)
  set Y_val := s₂ + s₄
  have hXY_eq : s₁ + s₂ + (Real.log N - Real.log n - Real.log c) * g_m + s₄ + s₅ = X_val + Y_val := by
    dsimp only [X_val, Y_val]; ring
  change (s₁ + s₂ + (Real.log N - Real.log n - Real.log c) * g_m + s₄ + s₅) ^ 2 ≤ _
  rw [hXY_eq]
  have hX_abs : |X_val| ≤ (A_const + B_const * Real.log c) / Real.sqrt n := by
    have t1 := abs_add_le (s₁ + (Real.log N - Real.log n) * g_m + s₅) (-Real.log c * g_m)
    have t2 := abs_add_le (s₁ + (Real.log N - Real.log n) * g_m) s₅
    have t3 := abs_add_le s₁ ((Real.log N - Real.log n) * g_m)
    have hlin : |X_val| ≤ C_K / Real.sqrt n + Real.log (1 / δ) * (C_G * m) / Real.sqrt n +
        C_jet / Real.sqrt n + Real.log c * B_const / Real.sqrt n := by
      dsimp only [X_val]; linarith only [t1, t2, t3, hb1, hb3_log, hb5, hb3_c]
    exact hlin.trans_eq (by dsimp only [A_const]; ring)
  have hY_abs : |Y_val| ≤ D_const * (c ^ 2 * Real.sqrt n / N ^ 2) := by
    have t1 := abs_add_le s₂ s₄
    dsimp only [Y_val, D_const]; linarith only [t1, hb2, hb4]
  have hA0 : 0 ≤ A_const := by
    have hlogδ : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ0).mpr hδ1.le)
    have hCjet0 : 0 ≤ C_jet := sum_nonneg fun k _ => mul_nonneg
      (mul_nonneg (ramanujanJetConductorWeight_nonneg m k) (by positivity))
      (by dsimp only [C_G]; positivity)
    dsimp only [A_const, C_K, C_G]; positivity
  have hB0 : 0 ≤ B_const := by dsimp only [B_const, C_G]; positivity
  have hX2 : X_val ^ 2 ≤ (2 * A_const ^ 2 + 2 * B_const ^ 2 * Real.log c ^ 2) * (1 / (n : ℝ)) := by
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hX_abs 2
    rw [sq_abs, div_pow, Real.sq_sqrt hn0.le] at hsq
    have hab : (A_const + B_const * Real.log c) ^ 2 ≤
        2 * A_const ^ 2 + 2 * B_const ^ 2 * Real.log c ^ 2 := by
      nlinarith only [sq_nonneg (A_const - B_const * Real.log c)]
    exact hsq.trans ((div_le_div_of_nonneg_right hab hn0.le).trans_eq (by ring))
  have hY2 : Y_val ^ 2 ≤ D_const ^ 2 * c ^ 2 * (c / N) ^ 2 * ((n : ℝ) / N ^ 2) := by
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hY_abs 2
    rw [sq_abs, mul_pow D_const, div_pow, mul_pow (c ^ 2) (Real.sqrt n), Real.sq_sqrt hn0.le] at hsq
    exact hsq.trans_eq (by ring)
  nlinarith only [sq_nonneg (X_val - Y_val), hX2, hY2]

/-- Subchannel 3b (`m ≥ 2`): The nonpolar near-Gamma remainder vector vanishes in
`(log N / c²) * topWindowResidualMass` along any critical curve. -/
private theorem tendsto_topWindow_nearGamma_nonpolar {m : ℕ} (hm2 : 2 ≤ m)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
          nearGammaNonpolarRemRow tiltedUnitSpline (c N) N m idx.1 / Real.sqrt (Real.log N))))
      atTop (𝓝 0) := by
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  obtain ⟨AK, LK, hLK0, hAK, hLK⟩ := exists_nearKernel_bounds hφ hsupp
  obtain ⟨K_lip, hlip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hAK0 : 0 ≤ AK := (abs_nonneg _).trans (hAK 0 ⟨le_rfl, by norm_num⟩)
  let M0 := ∫ u, tiltedUnitSpline u ^ 2
  let C_K := 2 * (2 * Real.exp 1 * (AK / M0) + 4 * Real.exp 5 * (LK / M0)) * m
  let C_G := 2 * (2 * Real.exp 1 * 1 + 4 * Real.exp 5 * ((K_lip : ℝ) / M0))
  let C_jet := ∑ k ∈ m.divisors.erase 1, ramanujanJetConductorWeight m k *
    (Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) * (C_G * k)
  let A_const := C_K + Real.log (1 / δ) * (C_G * m) + C_jet
  let B_const := C_G * m
  let D_const := 20 * Real.exp 3 * Real.sqrt m
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have h1 : Tendsto (fun N : ℕ => 1 / c N ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hcinf)
  have h2 : Tendsto (fun N : ℕ => (Real.log (c N) / c N) ^ 2) atTop (𝓝 0) := by
    have hlogc : Tendsto (fun N : ℕ => Real.log (c N) / c N) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq] using
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcinf
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hlogc.pow 2
  have h3 : Tendsto (fun N : ℕ => (c N / N) ^ 2) atTop (𝓝 0) := by
    have hcN := criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
    simp only [pow_one, pow_zero, mul_one] at hcN
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hcN.pow 2
  have hlim := ((h1.const_mul (4 * A_const ^ 2 / δ)).add (h2.const_mul (4 * B_const ^ 2 / δ))).add
    (h3.const_mul (2 * D_const ^ 2))
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) ?_ hlim
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_below_overlap_pair_admissible hc hR hcrit, hlog] with N hadm hL1
  obtain ⟨_, _, hradN, _⟩ := hadm 1 1 (by simpa using hc N) (by simpa using hc N)
  have hc1 := hc N
  have hc0 : 0 < c N := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have he2_ge4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h2e, hp]
  have h8c : 8 * c N ≤ N := by
    unfold linearNearRowRadius at hradN
    have hc_e2 : 4 * c N ≤ c N * Real.exp 2 := by
      have h := mul_le_mul_of_nonneg_left he2_ge4 hc0.le
      linarith only [h]
    have : 8 * c N ≤ (2 * c N * Real.exp 2 + 1) ^ 2 := by
      have hsq : 0 ≤ (c N * Real.exp 2) ^ 2 := sq_nonneg _
      nlinarith only [hc1, hc_e2, hsq]
    linarith only [this, hradN]
  have hN1 : 1 ≤ N := by exact_mod_cast (by linarith only [hc1, h8c] : (1 : ℝ) ≤ N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpt_row : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      nearGammaNonpolarRemRow tiltedUnitSpline (c N) N m n ^ 2 ≤
        (4 * A_const ^ 2 + 4 * B_const ^ 2 * Real.log (c N) ^ 2) * (1 / (n : ℝ)) +
          2 * D_const ^ 2 * c N ^ 2 * (c N / N) ^ 2 * ((n : ℝ) / N ^ 2) := fun n hn_top =>
    nearGammaNonpolarRemRow_sq_le hm2 hδ0 hδ1 hc1 hAK0 hLK0 hAK hLK hlip h8c hn_top
  have hmass_eq : (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
          nearGammaNonpolarRemRow tiltedUnitSpline (c N) N m idx.1 / Real.sqrt (Real.log N))) =
      (1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        nearGammaNonpolarRemRow tiltedUnitSpline (c N) N m n ^ 2 := by
    unfold topWindowResidualMass
    have hpt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        primeHorizonExtension (WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
          nearGammaNonpolarRemRow tiltedUnitSpline (c N) N m idx.1 / Real.sqrt (Real.log N))) n ^ 2 =
        nearGammaNonpolarRemRow tiltedUnitSpline (c N) N m n ^ 2 / Real.log N := fun n hn_top => by
      let idx : PrimeHorizonIndex N :=
        ⟨n, mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn_top).1; omega, (mem_Ioc.mp hn_top).2⟩⟩
      change primeHorizonExtension _ idx.1 ^ 2 = _
      rw [primeHorizonExtension_coe, div_pow, Real.sq_sqrt hL0.le]
    rw [sum_congr rfl hpt, ← sum_div]
    field_simp [hL0.ne', hc0.ne']
  rw [hmass_eq]
  have hsum_n : (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ) / N ^ 2) ≤ 1 := by
    calc (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ) / N ^ 2)
        ≤ ∑ _n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (N : ℝ) / N ^ 2 :=
          sum_le_sum fun n hn_top => div_le_div_of_nonneg_right
            (by exact_mod_cast (mem_Ioc.mp hn_top).2) (sq_nonneg _)
      _ = ((Ioc ⌊δ * (N : ℝ)⌋₊ N).card : ℝ) * ((N : ℝ) / N ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * ((N : ℝ) / N ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le N _
      _ = 1 := by field_simp [hN0.ne']
  calc (1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        nearGammaNonpolarRemRow tiltedUnitSpline (c N) N m n ^ 2
      ≤ (1 / c N ^ 2) * ((4 * A_const ^ 2 + 4 * B_const ^ 2 * Real.log (c N) ^ 2) *
            (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, 1 / (n : ℝ)) +
          2 * D_const ^ 2 * c N ^ 2 * (c N / N) ^ 2 *
            (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ) / N ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ((sum_le_sum hpt_row).trans_eq ?_) (by positivity)
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ (1 / c N ^ 2) * ((4 * A_const ^ 2 + 4 * B_const ^ 2 * Real.log (c N) ^ 2) * (1 / δ) +
          2 * D_const ^ 2 * c N ^ 2 * (c N / N) ^ 2 * 1) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left (sum_topWindow_inv_le hδ0 hN1) (by positivity))
          (mul_le_mul_of_nonneg_left hsum_n (by positivity))) (by positivity)
    _ = 4 * A_const ^ 2 / δ * (1 / c N ^ 2) +
          4 * B_const ^ 2 / δ * (Real.log (c N) / c N) ^ 2 +
          2 * D_const ^ 2 * (c N / N) ^ 2 := by field_simp [hc0.ne', hδ0.ne']


private lemma abs_sum_Ico_mode_mono_inc_le {k : ℕ} (hk : 2 ≤ k) {w : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    {a b : ℕ} (hbnd : ∀ j ∈ Ico a b, 0 ≤ w j ∧ w j ≤ M)
    (hinc : ∀ j ∈ Ico a (b - 1), w j ≤ w (j + 1)) :
    |∑ j ∈ Ico a b, w j * normalizedRamanujanMode k j| ≤ 2 * M * k := by
  have hbv := abs_sum_Ico_mode_bv_le hk w a b
  have ht1 : (if a < b then |w (b - 1)| else 0) ≤ M := by
    split_ifs with hab
    · have h := hbnd (b - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
      rw [abs_of_nonneg h.1]; exact h.2
    · exact hM
  have ht2 : (∑ j ∈ Ico a (b - 1), |w j - w (j + 1)|) ≤ M := by
    rcases le_or_gt (b - 1) a with hba | hab
    · rw [Ico_eq_empty (not_lt.mpr hba), sum_empty]; exact hM
    · have heq : (∑ j ∈ Ico a (b - 1), |w j - w (j + 1)|) =
          ∑ j ∈ Ico a (b - 1), (w (j + 1) - w j) := sum_congr rfl fun j hj => by
        rw [abs_of_nonpos (sub_nonpos.mpr (hinc j hj)), neg_sub]
      have htel : ∀ r : ℕ, (∑ j ∈ Ico a (a + r), (w (j + 1) - w j)) = w (a + r) - w a := fun r => by
        induction r with
        | zero => simp
        | succ r ih => rw [show a + (r + 1) = (a + r) + 1 by omega, sum_Ico_succ_top (by omega), ih]; ring
      obtain ⟨r, hr⟩ : ∃ r : ℕ, b - 1 = a + r := ⟨b - 1 - a, by omega⟩
      rw [heq, hr, htel r]
      have ha0 := (hbnd a (mem_Ico.mpr ⟨le_rfl, by omega⟩)).1
      have hbr := (hbnd (a + r) (mem_Ico.mpr ⟨by omega, by omega⟩)).2
      linarith only [ha0, hbr]
  exact hbv.trans ((mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (Nat.cast_nonneg k)).trans_eq (by ring))

private lemma abs_sum_Ico_mode_mono_dec_le {k : ℕ} (hk : 2 ≤ k) {w : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    {a b : ℕ} (hbnd : ∀ j ∈ Ico a b, 0 ≤ w j ∧ w j ≤ M)
    (hdec : ∀ j ∈ Ico a (b - 1), w (j + 1) ≤ w j) :
    |∑ j ∈ Ico a b, w j * normalizedRamanujanMode k j| ≤ 2 * M * k := by
  have hbv := abs_sum_Ico_mode_bv_le hk w a b
  have ht1 : (if a < b then |w (b - 1)| else 0) ≤ M := by
    split_ifs with hab
    · have h := hbnd (b - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
      rw [abs_of_nonneg h.1]; exact h.2
    · exact hM
  have ht2 : (∑ j ∈ Ico a (b - 1), |w j - w (j + 1)|) ≤ M := by
    rcases le_or_gt (b - 1) a with hba | hab
    · rw [Ico_eq_empty (not_lt.mpr hba), sum_empty]; exact hM
    · have heq : (∑ j ∈ Ico a (b - 1), |w j - w (j + 1)|) =
          ∑ j ∈ Ico a (b - 1), (w j - w (j + 1)) := sum_congr rfl fun j hj =>
        abs_of_nonneg (sub_nonneg.mpr (hdec j hj))
      have htel : ∀ r : ℕ, (∑ j ∈ Ico a (a + r), (w j - w (j + 1))) = w a - w (a + r) := fun r => by
        induction r with
        | zero => simp
        | succ r ih => rw [show a + (r + 1) = (a + r) + 1 by omega, sum_Ico_succ_top (by omega), ih]; ring
      obtain ⟨r, hr⟩ : ∃ r : ℕ, b - 1 = a + r := ⟨b - 1 - a, by omega⟩
      rw [heq, hr, htel r]
      have haM := (hbnd a (mem_Ico.mpr ⟨le_rfl, by omega⟩)).2
      have hbr0 := (hbnd (a + r) (mem_Ico.mpr ⟨by omega, by omega⟩)).1
      linarith only [haM, hbr0]
  exact hbv.trans ((mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (Nat.cast_nonneg k)).trans_eq (by ring))

/-- Far archimedean center row (`|log j - log n| > 2 c / N`) against `normalizedRamanujanMode m`
(`m ≥ 2`) is `O(m / √n)` uniformly in `c` and `N` once `2 * c ≤ N`. -/
private lemma abs_farCenter_mode_row_le {φ : ℝ → ℝ} {m N n : ℕ} (hm2 : 2 ≤ m)
    (hn : n ∈ Icc 1 N) {c : ℝ} (hc0 : 0 < c) (h2cN : 2 * c ≤ N) :
    |(completeWeilPoleShift φ c / N) *
      ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * c / N < |Real.log (j : ℝ) - Real.log (n : ℝ)|),
        archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j| ≤
      4 * |completeWeilPoleShift φ 1| * (m : ℝ) / Real.sqrt n := by
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hn1.trans (mem_Icc.mp hn).2
  let M_bnd : ℝ := (N : ℝ) / (c * n)
  have hM0 : 0 ≤ M_bnd := by dsimp only [M_bnd]; positivity
  have hinv_n_le : 1 / (n : ℝ) ≤ M_bnd := by
    dsimp only [M_bnd]
    rw [div_le_div_iff₀ hn0 (mul_pos hc0 hn0)]
    nlinarith only [h2cN, hc0, hn0]
  let F : Finset ℕ := (Icc 1 N).filter (fun j : ℕ => 2 * c / N < |Real.log (j : ℝ) - Real.log (n : ℝ)|)
  let P_lo : ℕ → Prop := fun j => 1 ≤ j ∧ 2 * c / N < Real.log n - Real.log j
  let P_hi : ℕ → Prop := fun j => 1 ≤ j ∧ 2 * c / N < Real.log j - Real.log n
  have hconv_lo : ∀ ⦃i j r : ℕ⦄, i ≤ j → j ≤ r → P_lo i → P_lo r → P_lo j := fun i j r hij hjr hi hr =>
    ⟨hi.1.trans hij, by
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (hi.1.trans hij)
      linarith [hr.2, Real.log_le_log hj0 (Nat.cast_le.mpr hjr)]⟩
  have hconv_hi : ∀ ⦃i j r : ℕ⦄, i ≤ j → j ≤ r → P_hi i → P_hi r → P_hi j := fun i j r hij _ hi _ =>
    ⟨hi.1.trans hij, by
      have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.1
      linarith [hi.2, Real.log_le_log hi0 (Nat.cast_le.mpr hij)]⟩
  let S_lo := (Ico 1 n).filter P_lo
  let S_hi := (Ico (n + 1) (N + 1)).filter P_hi
  have hdisj : Disjoint S_lo S_hi := disjoint_left.mpr fun j h1 h2 => by
    have := (mem_Ico.mp (mem_filter.mp h1).1).2; have := (mem_Ico.mp (mem_filter.mp h2).1).1; omega
  have hsplit_F : F = S_lo ∪ S_hi := by
    ext j; simp only [F, S_lo, S_hi, P_lo, P_hi, mem_union, mem_filter, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨⟨hj1, hjN⟩, hgt⟩
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hne : j ≠ n := by
        intro heq; subst heq; simp only [sub_self, abs_zero] at hgt
        linarith only [hgt, div_pos (mul_pos two_pos hc0) hN0]
      rcases lt_or_gt_of_ne hne with hlt | hgt'
      · rw [abs_of_neg (sub_neg.mpr (Real.log_lt_log hj0 (by exact_mod_cast hlt))), neg_sub] at hgt
        exact Or.inl ⟨⟨hj1, hlt⟩, hj1, hgt⟩
      · rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hn0 (by exact_mod_cast hgt')))] at hgt
        exact Or.inr ⟨⟨by omega, by omega⟩, hj1, hgt⟩
    · rintro (⟨⟨hj1, hlt⟩, _, hgt⟩ | ⟨⟨hgt', hjN⟩, hj1, hgt⟩)
      · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        refine ⟨⟨hj1, hlt.le.trans (mem_Icc.mp hn).2⟩, ?_⟩
        rwa [abs_of_neg (sub_neg.mpr (Real.log_lt_log hj0 (by exact_mod_cast hlt))), neg_sub]
      · refine ⟨⟨hj1, by omega⟩, ?_⟩
        rwa [abs_of_pos (sub_pos.mpr (Real.log_lt_log hn0 (by exact_mod_cast hgt')))]
  obtain ⟨L₁, U₁, _, hlo_eq⟩ := filter_Ico_eq_Ico hconv_lo 1 n
  obtain ⟨L₂, U₂, _, hhi_eq⟩ := filter_Ico_eq_Ico hconv_hi (n + 1) (N + 1)
  have hpt_F : ∀ j ∈ F, archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j =
      (Real.sqrt n / 2) * ((1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) * normalizedRamanujanMode m j) := by
    intro j hj
    obtain ⟨hjI, hgt⟩ := mem_filter.mp hj
    have hj1 := (mem_Icc.mp hjI).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hnj : n ≠ j := by
      intro heq; subst heq; simp only [sub_self, abs_zero] at hgt
      linarith only [hgt, div_pos (mul_pos two_pos hc0) hN0]
    have hker := archimedeanCenterKernel_div_sqrt_mul hn1 hj1 hnj
    have hrew : archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j =
        Real.sqrt n * (archimedeanCenterKernel n j / (Real.sqrt n * Real.sqrt j)) *
          normalizedRamanujanMode m j := by field_simp [hsn.ne', (Real.sqrt_pos.mpr hj0).ne']
    rw [hrew, hker]; ring
  have hlo_diff : |∑ j ∈ Ico L₁ U₁, (1 / ((n : ℝ) - j)) * normalizedRamanujanMode m j| ≤
      2 * M_bnd * m := by
    refine abs_sum_Ico_mode_mono_inc_le hm2 hM0 (fun j hj => ?_) (fun j hj => ?_)
    · rw [← hlo_eq] at hj
      obtain ⟨hjIco, hj1, hlog⟩ := mem_filter.mp hj
      have hlt : (j : ℝ) < n := by exact_mod_cast (mem_Ico.mp hjIco).2
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hgap : c * n / N ≤ (n : ℝ) - j := by
        by_cases h2j : 2 * (j : ℝ) ≤ n
        · have : c * n / N ≤ (n : ℝ) / 2 := (div_le_div_iff₀ hN0 two_pos).mpr (by nlinarith only [h2cN, hn0])
          linarith only [this, h2j]
        · push Not at h2j
          have hl := Real.log_le_sub_one_of_pos (div_pos hn0 hj0)
          rw [Real.log_div hn0.ne' hj0.ne'] at hl
          have hstep : 2 * c / N < ((n : ℝ) - j) / j := by
            have : (n : ℝ) / j - 1 = ((n : ℝ) - j) / j := by field_simp [hj0.ne']
            linarith only [hlog, hl, this]
          have hstep2 : ((n : ℝ) - j) / j ≤ 2 * ((n : ℝ) - j) / n := by
            rw [div_le_div_iff₀ hj0 hn0]; nlinarith only [h2j, hlt]
          have hfin := hstep.le.trans hstep2
          rw [div_le_div_iff₀ hN0 hn0] at hfin
          rw [div_le_iff₀ hN0]; nlinarith only [hfin]
      exact ⟨by positivity, (one_div_le_one_div_of_le (div_pos (mul_pos hc0 hn0) hN0) hgap).trans_eq
        (by dsimp only [M_bnd]; field_simp [hc0.ne', hn0.ne', hN0.ne'])⟩
    · obtain ⟨hjlo, hjhi⟩ := mem_Ico.mp hj
      have hj1_mem : j + 1 ∈ S_lo := by
        change j + 1 ∈ (Ico 1 n).filter P_lo
        rw [hlo_eq]; exact mem_Ico.mpr ⟨by omega, by omega⟩
      have hlt : ((j + 1 : ℕ) : ℝ) < n := by exact_mod_cast (mem_Ico.mp (mem_filter.mp hj1_mem).1).2
      exact one_div_le_one_div_of_le (by push_cast at hlt ⊢; linarith) (by push_cast; linarith)
  have hhi_diff : |∑ j ∈ Ico L₂ U₂, (1 / ((j : ℝ) - n)) * normalizedRamanujanMode m j| ≤
      2 * M_bnd * m := by
    refine abs_sum_Ico_mode_mono_dec_le hm2 hM0 (fun j hj => ?_) (fun j hj => ?_)
    · rw [← hhi_eq] at hj
      obtain ⟨hjIco, _, hlog⟩ := mem_filter.mp hj
      have hgt : (n : ℝ) < j := by exact_mod_cast (mem_Ico.mp hjIco).1
      have hj0 : (0 : ℝ) < j := hn0.trans hgt
      have hl := Real.log_le_sub_one_of_pos (div_pos hj0 hn0)
      rw [Real.log_div hj0.ne' hn0.ne'] at hl
      have hstep : 2 * c / N < ((j : ℝ) - n) / n := by
        have : (j : ℝ) / n - 1 = ((j : ℝ) - n) / n := by field_simp [hn0.ne']
        linarith only [hlog, hl, this]
      have hgap : c * n / N ≤ (j : ℝ) - n := by
        rw [div_lt_div_iff₀ hN0 hn0] at hstep
        rw [div_le_iff₀ hN0]; nlinarith only [hstep, hc0, hn0]
      exact ⟨by positivity, (one_div_le_one_div_of_le (div_pos (mul_pos hc0 hn0) hN0) hgap).trans_eq
        (by dsimp only [M_bnd]; field_simp [hc0.ne', hn0.ne', hN0.ne'])⟩
    · obtain ⟨hjlo, hjhi⟩ := mem_Ico.mp hj
      have hj_mem : j ∈ S_hi := by
        change j ∈ (Ico (n + 1) (N + 1)).filter P_hi
        rw [hhi_eq]; exact mem_Ico.mpr ⟨hjlo, by omega⟩
      have hgt : (n : ℝ) < j := by exact_mod_cast (mem_Ico.mp (mem_filter.mp hj_mem).1).1
      exact one_div_le_one_div_of_le (sub_pos.mpr hgt) (by push_cast; linarith)
  have hsum_part : ∀ a b : ℕ, |∑ j ∈ Ico a b, (1 / ((n : ℝ) + j)) * normalizedRamanujanMode m j| ≤
      2 * M_bnd * m := fun a b =>
    abs_sum_Ico_mode_mono_dec_le hm2 hM0
      (fun j _ => ⟨by positivity,
        (one_div_le_one_div_of_le hn0 (le_add_of_nonneg_right (Nat.cast_nonneg j))).trans hinv_n_le⟩)
      (fun j _ => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith))
  have hF_sum : |∑ j ∈ F, archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j| ≤
      (Real.sqrt n / 2) * (8 * M_bnd * m) := by
    rw [sum_congr rfl hpt_F, ← mul_sum, hsplit_F, sum_union hdisj]
    dsimp only [S_lo, S_hi]
    rw [hlo_eq, hhi_eq]
    have h1 : (∑ j ∈ Ico L₁ U₁, (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) * normalizedRamanujanMode m j) =
        (∑ j ∈ Ico L₁ U₁, (1 / ((n : ℝ) - j)) * normalizedRamanujanMode m j) +
        (∑ j ∈ Ico L₁ U₁, (1 / ((n : ℝ) + j)) * normalizedRamanujanMode m j) := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun j hj => ?_
      rw [← hlo_eq] at hj
      have hlt : (j : ℝ) < n := by exact_mod_cast (mem_Ico.mp (mem_filter.mp hj).1).2
      rw [abs_of_pos (sub_pos.mpr hlt)]; ring
    have h2 : (∑ j ∈ Ico L₂ U₂, (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) * normalizedRamanujanMode m j) =
        (∑ j ∈ Ico L₂ U₂, (1 / ((j : ℝ) - n)) * normalizedRamanujanMode m j) +
        (∑ j ∈ Ico L₂ U₂, (1 / ((n : ℝ) + j)) * normalizedRamanujanMode m j) := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun j hj => ?_
      rw [← hhi_eq] at hj
      have hgt : (n : ℝ) < j := by exact_mod_cast (mem_Ico.mp (mem_filter.mp hj).1).1
      rw [abs_of_neg (sub_neg.mpr hgt), neg_sub]; ring
    rw [h1, h2, abs_mul, abs_of_pos (by positivity : 0 < Real.sqrt (n : ℝ) / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    set s₁ := ∑ j ∈ Ico L₁ U₁, (1 / ((n : ℝ) - j)) * normalizedRamanujanMode m j
    set s₂ := ∑ j ∈ Ico L₁ U₁, (1 / ((n : ℝ) + j)) * normalizedRamanujanMode m j
    set s₃ := ∑ j ∈ Ico L₂ U₂, (1 / ((j : ℝ) - n)) * normalizedRamanujanMode m j
    set s₄ := ∑ j ∈ Ico L₂ U₂, (1 / ((n : ℝ) + j)) * normalizedRamanujanMode m j
    have t1 := abs_add_le (s₁ + s₂) (s₃ + s₄)
    have t2 := abs_add_le s₁ s₂
    have t3 := abs_add_le s₃ s₄
    linarith only [t1, t2, t3, hlo_diff, hhi_diff, hsum_part L₁ U₁, hsum_part L₂ U₂]
  have hshift : |completeWeilPoleShift φ c| = |completeWeilPoleShift φ 1| * c := by
    have : completeWeilPoleShift φ c = completeWeilPoleShift φ 1 * c := by unfold completeWeilPoleShift; ring
    rw [this, abs_mul, abs_of_pos hc0]
  rw [abs_mul, abs_div, hshift, abs_of_pos hN0]
  calc |completeWeilPoleShift φ 1| * c / N * |∑ j ∈ F, _|
      ≤ |completeWeilPoleShift φ 1| * c / N * ((Real.sqrt n / 2) * (8 * M_bnd * m)) :=
        mul_le_mul_of_nonneg_left hF_sum (by positivity)
    _ = 4 * |completeWeilPoleShift φ 1| * (m : ℝ) / Real.sqrt n := by
        dsimp only [M_bnd]; field_simp [hc0.ne', hn0.ne', hN0.ne', hsn.ne']
        rw [Real.sq_sqrt hn0.le]; ring

/-- Coordinate decomposition for Subchannel 3c (`m ≥ 2`): Channel 3 (`fullWeilCenterMatrix`) plus
`nearCenterVector` plus `(Λ(m)/√φ(m)) * nearPoleRow` splits into five decaying row pieces. -/
private lemma center_and_jetPole_coord_eq {m N : ℕ} (hm0 : 0 < m)
    {c : ℝ} (hc0 : 0 < c) (hN0 : (0 : ℝ) < N) (idx : PrimeHorizonIndex N) :
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N)
        (normalizedRamanujanHorizonVector m N) +
      nearCenterVector tiltedUnitSpline c N m +
      WithLp.toLp 2 (fun i : PrimeHorizonIndex N =>
        (Λ m / Real.sqrt (m.totient : ℝ)) *
          nearPoleRow tiltedUnitSpline c N i.1 / Real.sqrt (Real.log N))) idx =
    (((Λ m / Real.sqrt (m.totient : ℝ)) * poleRowDefect tiltedUnitSpline c N idx.1) +
      ((Λ m / Real.sqrt (m.totient : ℝ)) * atomPoleErrorCoefficient tiltedUnitSpline c N * Real.sqrt idx.1) +
      (completeWeilPoleShift tiltedUnitSpline c / (N * Real.sqrt (m.totient : ℝ)) *
        Real.sqrt idx.1 * (lagHarmonic m N + Λ m)) +
      (completeWeilPoleShift tiltedUnitSpline c / (N * Real.sqrt (m.totient : ℝ)) *
        (1 / Real.sqrt idx.1) * lagSum m N) -
      ((completeWeilPoleShift tiltedUnitSpline c / N) *
        ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * c / N < |Real.log (j : ℝ) - Real.log (idx.1 : ℝ)|),
          archimedeanCenterKernel idx.1 j * normalizedRamanujanMode m j / Real.sqrt j)) /
      Real.sqrt (Real.log N) := by
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hstot_ne : Real.sqrt (m.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr htot_pos).ne'
  have hn0 : (0 : ℝ) < idx.1 := by exact_mod_cast (mem_Icc.mp idx.2).1
  have hsn : Real.sqrt (idx.1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  let J_m := Λ m / Real.sqrt (m.totient : ℝ)
  have hcen_app : (Matrix.toEuclideanLin
      (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N)
      (normalizedRamanujanHorizonVector m N)) idx =
      (∑ j ∈ Icc 1 N, (completeWeilPoleShift tiltedUnitSpline c / N) *
        (arithmeticPoleKernel idx.1 j - archimedeanCenterKernel idx.1 j) *
        (normalizedRamanujanMode m j / Real.sqrt j)) / Real.sqrt (Real.log N) := by
    rw [normalizedRamanujanHorizonVector, map_smul]
    change (Real.sqrt (Real.log N))⁻¹ *
      ((Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N)
        (ramanujanHorizonVector m N)) idx) = _
    rw [div_eq_inv_mul]
    congr 1
    exact horizonKernelMatrix_apply_profile
      (fun n j => (completeWeilPoleShift tiltedUnitSpline c / N) *
        (arithmeticPoleKernel n j - archimedeanCenterKernel n j))
      (ramanujanPoleProfile m) N idx
  have hpole_sum : (∑ j ∈ Icc 1 N, (completeWeilPoleShift tiltedUnitSpline c / N) *
      arithmeticPoleKernel idx.1 j * (normalizedRamanujanMode m j / Real.sqrt j)) =
      completeWeilPoleShift tiltedUnitSpline c / (N * Real.sqrt (m.totient : ℝ)) *
        Real.sqrt idx.1 * lagHarmonic m N +
      completeWeilPoleShift tiltedUnitSpline c / (N * Real.sqrt (m.totient : ℝ)) *
        (1 / Real.sqrt idx.1) * lagSum m N := by
    unfold lagHarmonic lagSum
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    have hsj : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hj0).ne'
    unfold arithmeticPoleKernel
    rw [normalizedRamanujanMode,
      TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hm0]
    field_simp [hN0.ne', hstot_ne, hsn, hsj]
    rw [Real.sq_sqrt hj0.le]; ring
  have harch_split : (∑ j ∈ nearRowIndices c N idx.1,
      completeWeilPoleShift tiltedUnitSpline c / N * archimedeanCenterKernel idx.1 j *
        normalizedRamanujanMode m j / Real.sqrt j) -
      (∑ j ∈ Icc 1 N, (completeWeilPoleShift tiltedUnitSpline c / N) *
        archimedeanCenterKernel idx.1 j * (normalizedRamanujanMode m j / Real.sqrt j)) =
      -((completeWeilPoleShift tiltedUnitSpline c / N) *
        ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * c / N < |Real.log (j : ℝ) - Real.log (idx.1 : ℝ)|),
          archimedeanCenterKernel idx.1 j * normalizedRamanujanMode m j / Real.sqrt j) := by
    rw [nearRowIndices, sum_filter, mul_sum, sum_filter, ← sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases hjn : j = idx.1
    · subst hjn
      simp [archimedeanCenterKernel_self, not_lt_of_ge (by positivity : 0 ≤ 2 * c / (N : ℝ))]
    · by_cases hle : |Real.log (j : ℝ) - Real.log (idx.1 : ℝ)| ≤ 2 * c / N
      · rw [if_pos ⟨hjn, hle⟩, if_neg (not_lt.mpr hle)]; ring
      · rw [if_neg (fun h => hle h.2), if_pos (lt_of_not_ge hle)]; ring
  have hpole_def : J_m * nearPoleRow tiltedUnitSpline c N idx.1 =
      J_m * poleRowDefect tiltedUnitSpline c N idx.1 +
      J_m * atomPoleErrorCoefficient tiltedUnitSpline c N * Real.sqrt idx.1 +
      completeWeilPoleShift tiltedUnitSpline c / (N * Real.sqrt (m.totient : ℝ)) *
        Real.sqrt idx.1 * Λ m := by
    have hd : nearPoleRow tiltedUnitSpline c N idx.1 =
        poleRowDefect tiltedUnitSpline c N idx.1 +
          (atomPoleErrorCoefficient tiltedUnitSpline c N +
            completeWeilPoleShift tiltedUnitSpline c / N) * Real.sqrt idx.1 := by
      unfold poleRowDefect; rw [exactPoleCoefficient_eq]; ring
    rw [hd]; dsimp only [J_m]; field_simp [hN0.ne', hstot_ne]; ring
  change (Matrix.toEuclideanLin _ _) idx +
    (∑ j ∈ nearRowIndices c N idx.1, _) / Real.sqrt (Real.log N) +
    J_m * nearPoleRow tiltedUnitSpline c N idx.1 / Real.sqrt (Real.log N) = _
  rw [hcen_app, ← add_div, ← add_div]
  congr 1
  have hcen_sub : (∑ j ∈ Icc 1 N, (completeWeilPoleShift tiltedUnitSpline c / N) *
      (arithmeticPoleKernel idx.1 j - archimedeanCenterKernel idx.1 j) *
      (normalizedRamanujanMode m j / Real.sqrt j)) =
      (∑ j ∈ Icc 1 N, (completeWeilPoleShift tiltedUnitSpline c / N) *
        arithmeticPoleKernel idx.1 j * (normalizedRamanujanMode m j / Real.sqrt j)) -
      (∑ j ∈ Icc 1 N, (completeWeilPoleShift tiltedUnitSpline c / N) *
        archimedeanCenterKernel idx.1 j * (normalizedRamanujanMode m j / Real.sqrt j)) := by
    rw [← sum_sub_distrib]; refine sum_congr rfl fun _ _ => by ring
  rw [hcen_sub, hpole_sum, hpole_def]
  dsimp only [J_m]
  linarith only [harch_split]

/-- Subchannel 3c (`m ≥ 2`): Channel 3 (`fullWeilCenterMatrix`) plus `nearCenterVector` plus the
divisor-jet pole component `(Λ(m)/√φ(m)) * nearPoleRow` vanishes in
`(log N / c²) * topWindowResidualMass` along any critical curve. -/
private theorem tendsto_topWindow_center_and_jetPole_nonpolar {m : ℕ} (hm2 : 2 ≤ m)
    {δ : ℝ} (hδ0 : 0 < δ)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline (c N)) N)
            (normalizedRamanujanHorizonVector m N) +
          nearCenterVector tiltedUnitSpline (c N) N m +
          WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
            (Λ m / Real.sqrt (m.totient : ℝ)) *
              nearPoleRow tiltedUnitSpline (c N) N idx.1 / Real.sqrt (Real.log N))))
      atTop (𝓝 0) := by
  have hm0 : 0 < m := by omega
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_d, hCd0, hdef⟩ := exists_sum_poleRowDefect_sq_le hφ hsupp hM
  let S₁ := |completeWeilPoleShift tiltedUnitSpline 1|
  let C_pe := atomPoleMomentErrorConstant tiltedUnitSpline
  let L_bnd := (2 * (m : ℝ) + 1) * ∑ d ∈ m.divisors, (d : ℝ)
  let J_m := Λ m / Real.sqrt (m.totient : ℝ)
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have h1 : Tendsto (fun N : ℕ => (1 + Real.log (c N)) / c N ^ 2) atTop (𝓝 0) := by
    have ha : Tendsto (fun N : ℕ => 1 / c N ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hcinf)
    have hlog_div : Tendsto (fun N : ℕ => Real.log (c N) / c N) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq] using
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcinf
    have hb : Tendsto (fun N : ℕ => Real.log (c N) / c N * (1 / c N)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hlog_div.mul (tendsto_const_nhds.div_atTop hcinf)
    simpa only [add_zero] using (ha.add hb).congr (fun N => by ring)
  have h2 : Tendsto (fun N : ℕ => (c N / N) ^ 2) atTop (𝓝 0) := by
    have hcN := criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
    simp only [pow_one, pow_zero, mul_one] at hcN
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hcN.pow 2
  have h3 : Tendsto (fun N : ℕ => (lagHarmonic m N + Λ m) ^ 2) atTop (𝓝 0) := by
    have hl := (tendsto_lagHarmonic hm2).add_const (Λ m)
    rw [neg_add_cancel] at hl
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hl.pow 2
  have h4 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h5 : Tendsto (fun N : ℕ => 1 / c N ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hcinf)
  have hlim := ((((h1.const_mul (8 * J_m ^ 2 * C_d)).add
      (h2.const_mul (8 * J_m ^ 2 * C_pe ^ 2))).add
      (h3.const_mul (8 * S₁ ^ 2 / m.totient))).add
      (h4.const_mul (8 * S₁ ^ 2 * L_bnd ^ 2 / (δ * m.totient)))).add
      (h5.const_mul (128 * S₁ ^ 2 * (m : ℝ) ^ 2 / δ))
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) ?_ hlim
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_below_overlap_pair_admissible hc hR hcrit, hlog] with N hadm hL1
  obtain ⟨_, _, hradN, hc4N⟩ := hadm 1 1 (by simpa using hc N) (by simpa using hc N)
  have hc1 := hc N
  have hc0 : 0 < c N := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have he2_ge4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h2, hp]
  have h8c : 8 * c N ≤ N := by
    unfold linearNearRowRadius at hradN
    have hc_e2 : 4 * c N ≤ c N * Real.exp 2 := by
      have h := mul_le_mul_of_nonneg_left he2_ge4 hc0.le
      linarith only [h]
    have : 8 * c N ≤ (2 * c N * Real.exp 2 + 1) ^ 2 := by
      nlinarith only [hc1, hc_e2, sq_nonneg (c N * Real.exp 2)]
    linarith only [this, hradN]
  have hN1 : 1 ≤ N := by exact_mod_cast (by linarith only [hc1, h8c] : (1 : ℝ) ≤ N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN : c N ≤ N := by linarith only [hc0, h8c]
  have h2cN : 2 * c N ≤ N := by linarith only [hc0, h8c]
  have hshift_sq : completeWeilPoleShift tiltedUnitSpline (c N) ^ 2 = S₁ ^ 2 * c N ^ 2 := by
    have : completeWeilPoleShift tiltedUnitSpline (c N) =
        completeWeilPoleShift tiltedUnitSpline 1 * c N := by unfold completeWeilPoleShift; ring
    rw [this, mul_pow, ← sq_abs]
  let row_tot : ℕ → ℝ := fun n =>
    (J_m * poleRowDefect tiltedUnitSpline (c N) N n) +
    (J_m * atomPoleErrorCoefficient tiltedUnitSpline (c N) N * Real.sqrt n) +
    (completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
      Real.sqrt n * (lagHarmonic m N + Λ m)) +
    (completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
      (1 / Real.sqrt n) * lagSum m N) -
    ((completeWeilPoleShift tiltedUnitSpline (c N) / N) *
      ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * c N / N < |Real.log (j : ℝ) - Real.log (n : ℝ)|),
        archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j)
  have hcoord : ∀ idx : PrimeHorizonIndex N,
      (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline (c N)) N)
          (normalizedRamanujanHorizonVector m N) +
        nearCenterVector tiltedUnitSpline (c N) N m +
        WithLp.toLp 2 (fun i : PrimeHorizonIndex N =>
          J_m * nearPoleRow tiltedUnitSpline (c N) N i.1 / Real.sqrt (Real.log N))) idx =
      row_tot idx.1 / Real.sqrt (Real.log N) :=
    fun idx => center_and_jetPole_coord_eq hm0 hc0 hN0 idx
  have hmass_eq : (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline (c N)) N)
            (normalizedRamanujanHorizonVector m N) +
          nearCenterVector tiltedUnitSpline (c N) N m +
          WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
            J_m * nearPoleRow tiltedUnitSpline (c N) N idx.1 / Real.sqrt (Real.log N))) =
      (1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, row_tot n ^ 2 := by
    unfold topWindowResidualMass
    have hpt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        primeHorizonExtension _ n ^ 2 = row_tot n ^ 2 / Real.log N := fun n hn_top => by
      let idx : PrimeHorizonIndex N :=
        ⟨n, mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn_top).1; omega, (mem_Ioc.mp hn_top).2⟩⟩
      change primeHorizonExtension _ idx.1 ^ 2 = _
      rw [primeHorizonExtension_coe, hcoord idx, div_pow, Real.sq_sqrt hL0.le]
    rw [sum_congr rfl hpt, ← sum_div]; field_simp [hL0.ne', hc0.ne']
  rw [hmass_eq]
  have hsub_top : Ioc ⌊δ * (N : ℝ)⌋₊ N ⊆ Icc 1 N := fun n hn =>
    mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
  have h5sq : ∀ n : ℕ, row_tot n ^ 2 ≤
      8 * ((J_m * poleRowDefect tiltedUnitSpline (c N) N n) ^ 2 +
        (J_m * atomPoleErrorCoefficient tiltedUnitSpline (c N) N * Real.sqrt n) ^ 2 +
        (completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
          Real.sqrt n * (lagHarmonic m N + Λ m)) ^ 2 +
        (completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
          (1 / Real.sqrt n) * lagSum m N) ^ 2 +
        ((completeWeilPoleShift tiltedUnitSpline (c N) / N) *
          ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * c N / N < |Real.log (j : ℝ) - Real.log (n : ℝ)|),
            archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j) ^ 2) := fun n => by
    dsimp only [row_tot]
    set x₁ := J_m * poleRowDefect tiltedUnitSpline (c N) N n
    set x₂ := J_m * atomPoleErrorCoefficient tiltedUnitSpline (c N) N * Real.sqrt n
    set x₃ := completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
      Real.sqrt n * (lagHarmonic m N + Λ m)
    set x₄ := completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
      (1 / Real.sqrt n) * lagSum m N
    set x₅ := (completeWeilPoleShift tiltedUnitSpline (c N) / N) *
      ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * c N / N < |Real.log (j : ℝ) - Real.log (n : ℝ)|),
        archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j
    nlinarith only [sq_nonneg ((x₁ + x₂ + x₃ + x₄) + x₅), sq_nonneg ((x₁ + x₂) - (x₃ + x₄)),
      sq_nonneg (x₁ - x₂), sq_nonneg (x₃ - x₄), sq_nonneg x₅]
  have hs1 : (1 / c N ^ 2) * (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (J_m * poleRowDefect tiltedUnitSpline (c N) N n) ^ 2) ≤
      J_m ^ 2 * C_d * ((1 + Real.log (c N)) / c N ^ 2) := by
    have hsum : (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (J_m * poleRowDefect tiltedUnitSpline (c N) N n) ^ 2) ≤
        J_m ^ 2 * (C_d * (1 + Real.log (c N))) := by
      calc _ ≤ ∑ n ∈ Icc 1 N, J_m ^ 2 * poleRowDefect tiltedUnitSpline (c N) N n ^ 2 :=
            (sum_le_sum fun n _ => (mul_pow _ _ 2).le).trans
              (sum_le_sum_of_subset_of_nonneg hsub_top fun _ _ _ => by positivity)
        _ = J_m ^ 2 * ∑ n ∈ Icc 1 N, poleRowDefect tiltedUnitSpline (c N) N n ^ 2 := (mul_sum _ _ _).symm
        _ ≤ J_m ^ 2 * (C_d * (1 + Real.log (c N))) :=
            mul_le_mul_of_nonneg_left (hdef hc1 h8c hc4N) (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)
  have hsum_n_N2 : (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ)) ≤ (N : ℝ) ^ 2 := by
    calc (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ))
        ≤ ∑ _n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (N : ℝ) :=
          sum_le_sum fun n hn => by exact_mod_cast (mem_Ioc.mp hn).2
      _ = ((Ioc ⌊δ * (N : ℝ)⌋₊ N).card : ℝ) * N := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_right (by rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le N _) hN0.le
      _ = (N : ℝ) ^ 2 := (sq _).symm
  have hs2 : (1 / c N ^ 2) * (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (J_m * atomPoleErrorCoefficient tiltedUnitSpline (c N) N * Real.sqrt n) ^ 2) ≤
      J_m ^ 2 * C_pe ^ 2 * (c N / N) ^ 2 := by
    have hpe := abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM hc0 hN1 hcN
    have hpe2 : atomPoleErrorCoefficient tiltedUnitSpline (c N) N ^ 2 ≤ C_pe ^ 2 * (c N / N) ^ 4 := by
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hpe 2
      rw [sq_abs] at hsq; exact hsq.trans_eq (by ring)
    have hsum : (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        (J_m * atomPoleErrorCoefficient tiltedUnitSpline (c N) N * Real.sqrt n) ^ 2) ≤
        J_m ^ 2 * C_pe ^ 2 * (c N / N) ^ 4 * (N : ℝ) ^ 2 := by
      calc _ = J_m ^ 2 * atomPoleErrorCoefficient tiltedUnitSpline (c N) N ^ 2 *
              ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ) := by
            rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
            rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        _ ≤ (J_m ^ 2 * (C_pe ^ 2 * (c N / N) ^ 4)) * (N : ℝ) ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpe2 (sq_nonneg _)) hsum_n_N2
              (sum_nonneg fun _ _ => Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq
      (by field_simp [hc0.ne', hN0.ne'])
  have hs3 : (1 / c N ^ 2) * (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
        Real.sqrt n * (lagHarmonic m N + Λ m)) ^ 2) ≤
      S₁ ^ 2 / m.totient * (lagHarmonic m N + Λ m) ^ 2 := by
    have hsum : (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        (completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
          Real.sqrt n * (lagHarmonic m N + Λ m)) ^ 2) ≤
        S₁ ^ 2 * c N ^ 2 / m.totient * (lagHarmonic m N + Λ m) ^ 2 := by
      calc _ = (completeWeilPoleShift tiltedUnitSpline (c N) ^ 2 / ((N : ℝ) ^ 2 * m.totient) *
              (lagHarmonic m N + Λ m) ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ) := by
            rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
            rw [mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt htot_pos.le,
              Real.sq_sqrt (Nat.cast_nonneg n)]; ring
        _ ≤ (S₁ ^ 2 * c N ^ 2 / ((N : ℝ) ^ 2 * m.totient) * (lagHarmonic m N + Λ m) ^ 2) * (N : ℝ) ^ 2 := by
            rw [hshift_sq]
            exact mul_le_mul_of_nonneg_left hsum_n_N2 (by positivity)
        _ = S₁ ^ 2 * c N ^ 2 / m.totient * (lagHarmonic m N + Λ m) ^ 2 := by
            field_simp [hN0.ne', htot_pos.ne']
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by field_simp [hc0.ne', htot_pos.ne'])
  have hs4 : (1 / c N ^ 2) * (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
        (1 / Real.sqrt n) * lagSum m N) ^ 2) ≤
      S₁ ^ 2 * L_bnd ^ 2 / (δ * m.totient) * (1 / (N : ℝ)) := by
    have hlag := abs_lagSum_le hm2 N
    have hlag2 : lagSum m N ^ 2 ≤ L_bnd ^ 2 := by
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hlag 2
      rwa [sq_abs] at hsq
    have hN_sq : (N : ℝ) ≤ (N : ℝ) ^ 2 :=
      le_self_pow₀ (by exact_mod_cast hN1 : (1 : ℝ) ≤ N) (by norm_num)
    have hsum : (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        (completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
          (1 / Real.sqrt n) * lagSum m N) ^ 2) ≤
        S₁ ^ 2 * c N ^ 2 * L_bnd ^ 2 / (δ * m.totient) * (1 / (N : ℝ)) := by
      calc _ = (S₁ ^ 2 * c N ^ 2 / ((N : ℝ) ^ 2 * m.totient) * lagSum m N ^ 2) *
              ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, 1 / (n : ℝ) := by
            rw [← hshift_sq, mul_sum]; refine sum_congr rfl fun n _ => ?_
            rw [mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt htot_pos.le, div_pow, one_pow,
              Real.sq_sqrt (Nat.cast_nonneg n)]; ring
        _ ≤ (S₁ ^ 2 * c N ^ 2 / ((N : ℝ) ^ 2 * m.totient) * L_bnd ^ 2) * (1 / δ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hlag2 (by positivity))
              (sum_topWindow_inv_le hδ0 hN1) (sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = S₁ ^ 2 * c N ^ 2 * L_bnd ^ 2 / (δ * m.totient) * (1 / (N : ℝ) ^ 2) := by ring
        _ ≤ S₁ ^ 2 * c N ^ 2 * L_bnd ^ 2 / (δ * m.totient) * (1 / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hN0 hN_sq) (by positivity)
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq
      (by field_simp [hc0.ne', hδ0.ne', htot_pos.ne', hN0.ne'])
  have hs5 : (1 / c N ^ 2) * (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      ((completeWeilPoleShift tiltedUnitSpline (c N) / N) *
        ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * c N / N < |Real.log (j : ℝ) - Real.log (n : ℝ)|),
          archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j) ^ 2) ≤
      16 * S₁ ^ 2 * (m : ℝ) ^ 2 / δ * (1 / c N ^ 2) := by
    have hpt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        ((completeWeilPoleShift tiltedUnitSpline (c N) / N) *
          ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * c N / N < |Real.log (j : ℝ) - Real.log (n : ℝ)|),
            archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j) ^ 2 ≤
        16 * S₁ ^ 2 * (m : ℝ) ^ 2 * (1 / (n : ℝ)) := fun n hn_top => by
      have hn := hsub_top hn_top
      have hsq := pow_le_pow_left₀ (abs_nonneg _)
        (abs_farCenter_mode_row_le (φ := tiltedUnitSpline) hm2 hn hc0 h2cN) 2
      rw [sq_abs, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hsq
      exact hsq.trans_eq (by dsimp only [S₁]; ring)
    have hsum : (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        ((completeWeilPoleShift tiltedUnitSpline (c N) / N) *
          ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * c N / N < |Real.log (j : ℝ) - Real.log (n : ℝ)|),
            archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j) ^ 2) ≤
        16 * S₁ ^ 2 * (m : ℝ) ^ 2 / δ := by
      calc _ ≤ 16 * S₁ ^ 2 * (m : ℝ) ^ 2 * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, 1 / (n : ℝ) :=
            (sum_le_sum hpt).trans_eq (mul_sum _ _ _).symm
        _ ≤ 16 * S₁ ^ 2 * (m : ℝ) ^ 2 * (1 / δ) :=
            mul_le_mul_of_nonneg_left (sum_topWindow_inv_le hδ0 hN1) (by positivity)
        _ = 16 * S₁ ^ 2 * (m : ℝ) ^ 2 / δ := by ring
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)
  have htot_sum : (1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, row_tot n ^ 2 ≤
      8 * ((1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (J_m * poleRowDefect tiltedUnitSpline (c N) N n) ^ 2 +
        (1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
          (J_m * atomPoleErrorCoefficient tiltedUnitSpline (c N) N * Real.sqrt n) ^ 2 +
        (1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
          (completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
            Real.sqrt n * (lagHarmonic m N + Λ m)) ^ 2 +
        (1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
          (completeWeilPoleShift tiltedUnitSpline (c N) / (N * Real.sqrt (m.totient : ℝ)) *
            (1 / Real.sqrt n) * lagSum m N) ^ 2 +
        (1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
          ((completeWeilPoleShift tiltedUnitSpline (c N) / N) *
            ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * c N / N < |Real.log (j : ℝ) - Real.log (n : ℝ)|),
              archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j) ^ 2) := by
    have hs := sum_le_sum fun n (_ : n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N) => h5sq n
    rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib] at hs
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)
  exact htot_sum.trans (by
    have hlin := add_le_add (add_le_add (add_le_add (add_le_add hs1 hs2) hs3) hs4) hs5
    have hmul := mul_le_mul_of_nonneg_left hlin (by norm_num : (0 : ℝ) ≤ 8)
    exact hmul.trans_eq (by ring))

private lemma sum_Icc_inv_sq_le_two_div {d N : ℕ} (hd1 : 1 ≤ d) :
    (∑ k ∈ Icc d N, 1 / (k : ℝ) ^ 2) ≤ 2 / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  rcases lt_or_ge N d with hlt | hle
  · rw [Icc_eq_empty (not_le.mpr hlt), sum_empty]; positivity
  · have hsplit : Icc d N = insert d (Ico (d + 1) (N + 1)) := by
      ext k; simp only [mem_Icc, mem_insert, mem_Ico]; omega
    rw [hsplit, sum_insert (by simp)]
    have hfirst : 1 / (d : ℝ) ^ 2 ≤ 1 / (d : ℝ) :=
      one_div_le_one_div_of_le hd0 (le_self_pow₀ (by exact_mod_cast hd1 : (1 : ℝ) ≤ d) (by norm_num))
    have hstep : ∀ k ∈ Ico (d + 1) (N + 1),
        1 / (k : ℝ) ^ 2 ≤ 1 / ((k - 1 : ℕ) : ℝ) - 1 / ((k : ℕ) : ℝ) := by
      intro k hk
      have hk2 : 2 ≤ k := by have := (mem_Ico.mp hk).1; omega
      have hk1_pos : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
      have hk_pos : (0 : ℝ) < k := by positivity
      have heq : 1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) = 1 / (((k - 1 : ℕ) : ℝ) * k) := by
        rw [div_sub_div _ _ hk1_pos.ne' hk_pos.ne', one_mul, mul_one,
          Nat.cast_sub (by omega : 1 ≤ k)]
        ring
      rw [heq]
      refine one_div_le_one_div_of_le (mul_pos hk1_pos hk_pos) ?_
      rw [Nat.cast_sub (by omega : 1 ≤ k)]; nlinarith only [hk_pos]
    have htel : ∀ r : ℕ, (∑ k ∈ Ico (d + 1) (d + 1 + r),
        (1 / ((k - 1 : ℕ) : ℝ) - 1 / ((k : ℕ) : ℝ))) =
        1 / (d : ℝ) - 1 / ((d + r : ℕ) : ℝ) := fun r => by
      induction r with
      | zero => simp
      | succ r ih =>
        rw [show d + 1 + (r + 1) = (d + 1 + r) + 1 by omega, sum_Ico_succ_top (by omega), ih,
          show d + 1 + r - 1 = d + r by omega, show d + (r + 1) = d + 1 + r by omega]
        ring
    obtain ⟨r, hr⟩ : ∃ r : ℕ, N + 1 = d + 1 + r := ⟨N - d, by omega⟩
    have hrest : (∑ k ∈ Ico (d + 1) (N + 1), 1 / (k : ℝ) ^ 2) ≤ 1 / (d : ℝ) := by
      refine (sum_le_sum hstep).trans ?_
      rw [hr, htel r]
      linarith only [(by positivity : 0 ≤ 1 / ((d + r : ℕ) : ℝ))]
    linarith only [hfirst, hrest, (by ring : 1 / (d : ℝ) + 1 / (d : ℝ) = 2 / (d : ℝ))]

/-- Far-tail (`|log j - log n| > T * (c / N)`) row bound for `separatedCrossErrorMatrix` against
`normalizedRamanujanMode m` (`m ≥ 1`). -/
private lemma separatedCross_tail_row_le {m N n : ℕ} (hm0 : 0 < m)
    (hn : n ∈ Icc 1 N) {c T : ℝ} (hc0 : 0 < c) (_hcN : c ≤ N) (hT2 : 2 ≤ T) :
    |∑ j ∈ (Icc 1 N).filter (fun j : ℕ => T * (c / N) < |Real.log (j : ℝ) - Real.log (n : ℝ)|),
      atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j *
        (normalizedRamanujanMode m j / Real.sqrt j)| ≤
      (4 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) * Real.sqrt m) *
          (c ^ 2 / N) +
        64 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
          Real.sqrt m / T * (c * Real.sqrt n / N) := by
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  let K₀ : ℝ := 152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)
  let C_far : ℝ := 4 * K₀ * Real.sqrt m
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hN1 : 1 ≤ N := hn1.trans (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hT0 : 0 < T := zero_lt_two.trans_le hT2
  let F_T := (Icc 1 N).filter (fun j : ℕ => T * (c / N) < |Real.log (j : ℝ) - Real.log (n : ℝ)|)
  let S_near := F_T.filter (fun j : ℕ => n ≤ 2 * j ∧ j ≤ 2 * n)
  have hterm_pt : ∀ j ∈ F_T,
      |atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j *
        (normalizedRamanujanMode m j / Real.sqrt j)| ≤
      K₀ * (c / N) ^ 2 * Real.sqrt m *
        ((if j ∈ S_near then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4) := by
    intro j hjF
    obtain ⟨hj, hgapT⟩ := mem_filter.mp hjF
    have hgap2 : 2 * (c / N) < |Real.log (j : ℝ) - Real.log (n : ℝ)| :=
      (mul_le_mul_of_nonneg_right hT2 hw0.le).trans_lt hgapT
    have hj1 := (mem_Icc.mp hj).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
    have hne : n ≠ j := by intro h; subst h; simp at hgap2; linarith only [hgap2, hw0]
    have hd_pos : 0 < |(n : ℝ) - j| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
    have hentry := abs_separatedCrossError_le hφ hsupp hM hc0 hN1 hn hj
    rw [if_pos hgap2] at hentry
    have ha : |normalizedRamanujanMode m j / Real.sqrt j| ≤ Real.sqrt m / Real.sqrt j := by
      rw [abs_div, abs_of_pos hsj]; exact div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hm0 j) hsj.le
    have hprod := mul_le_mul hentry ha (abs_nonneg _) (by positivity)
    rw [← abs_mul] at hprod
    have hprod_eq : (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
        (c / N) ^ 2 * max (n : ℝ) j ^ 2 / |(n : ℝ) - j| ^ 2 * (Real.sqrt m / Real.sqrt j) =
        K₀ * (c / N) ^ 2 * Real.sqrt m * (max (n : ℝ) j ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2)) := by
      dsimp only [K₀]; ring
    refine (hprod.trans_eq hprod_eq).trans
      (mul_le_mul_of_nonneg_left ?_ (by dsimp only [K₀]; positivity))
    by_cases hnr : n ≤ 2 * j ∧ j ≤ 2 * n
    · rw [if_pos (mem_filter.mpr ⟨hjF, hnr⟩)]
      have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnr.1
      have hjnR : (j : ℝ) ≤ 2 * n := by exact_mod_cast hnr.2
      have hs_cmp : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (j : ℝ) := by
        by_contra h
        have hlt := lt_of_not_ge h
        have hp := mul_pos (sub_pos.mpr hlt) (by positivity : 0 < Real.sqrt (n : ℝ) + 2 * Real.sqrt (j : ℝ))
        nlinarith only [hp, Real.sq_sqrt hn0.le, Real.sq_sqrt hj0.le, hnjR, hj0]
      have hm2_le : (max (n : ℝ) j) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
        have hsq := mul_self_le_mul_self (hn0.le.trans (le_max_left _ _)) (max_le (by linarith only [hn0]) hjnR)
        nlinarith only [hsq]
      have hc1_bound : (max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2) ≤
          8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 := by
        rw [div_le_div_iff₀ (mul_pos hsj (sq_pos_of_pos hd_pos)) (sq_pos_of_pos hd_pos)]
        have hmx : (max (n : ℝ) j) ^ 2 * Real.sqrt n ≤ 8 * (n : ℝ) ^ 2 * Real.sqrt j := by
          calc (max (n : ℝ) j) ^ 2 * Real.sqrt n ≤ (4 * (n : ℝ) ^ 2) * (2 * Real.sqrt j) :=
                mul_le_mul hm2_le hs_cmp (Real.sqrt_nonneg _) (by positivity)
            _ = 8 * (n : ℝ) ^ 2 * Real.sqrt j := by ring
        have hsq_eq : 8 * (n : ℝ) * Real.sqrt n * (Real.sqrt j * |(n : ℝ) - j| ^ 2) =
            (8 * (n : ℝ) ^ 2 * Real.sqrt j / Real.sqrt n) * |(n : ℝ) - j| ^ 2 := by
          field_simp [hsn.ne']; rw [Real.sq_sqrt hn0.le]
        have hdiv : (max (n : ℝ) j) ^ 2 ≤ 8 * (n : ℝ) ^ 2 * Real.sqrt j / Real.sqrt n :=
          (le_div_iff₀ hsn).mpr hmx
        nlinarith only [mul_le_mul_of_nonneg_right hdiv (sq_nonneg |(n : ℝ) - j|), hsq_eq]
      linarith only [hc1_bound]
    · have hj_not : j ∉ S_near := fun h => hnr (mem_filter.mp h).2
      rw [if_neg hj_not, zero_add]
      have hhalf : max (n : ℝ) j ≤ 2 * |(n : ℝ) - j| := by
        rcases lt_or_ge n j with hlt | hge
        · have h2n : 2 * n < j := by omega
          rw [max_eq_right (by exact_mod_cast hlt.le),
            abs_of_neg (sub_neg.mpr (by exact_mod_cast hlt))]
          have : 2 * (n : ℝ) < j := by exact_mod_cast h2n
          linarith only [this]
        · have h2j : 2 * j < n := by omega
          rw [max_eq_left (by exact_mod_cast hge),
            abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hge))]
          have : 2 * (j : ℝ) < n := by exact_mod_cast h2j
          linarith only [this]
      have hsq := mul_self_le_mul_self (hn0.le.trans (le_max_left _ _)) hhalf
      have hsj1 : 1 ≤ Real.sqrt (j : ℝ) := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hj1 : (1 : ℝ) ≤ j)
      rw [div_le_iff₀ (mul_pos hsj (sq_pos_of_pos hd_pos))]
      nlinarith only [hsq, hsj1, sq_nonneg |(n : ℝ) - j|]
  let d_T : ℕ := max 1 ⌈(T / 2) * (c * n / N)⌉₊
  have hd1 : 1 ≤ d_T := le_max_left _ _
  have hd_ge : (T / 2) * (c * n / N) ≤ d_T :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
  have hdist_sum : (∑ j ∈ S_near, 1 / |(n : ℝ) - j| ^ 2) ≤ 8 * N / (T * c * n) := by
    have hmem_dist : ∀ j ∈ S_near, Nat.dist n j ∈ Icc d_T N := fun j hjS => by
      obtain ⟨hjF, hnr1, _⟩ := mem_filter.mp hjS
      obtain ⟨hjI, hgapT⟩ := mem_filter.mp hjF
      have hj1 := (mem_Icc.mp hjI).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hdist_le : Nat.dist n j ≤ N := by
        have := (mem_Icc.mp hn).2; have := (mem_Icc.mp hjI).2
        rcases le_total n j with h | h
        · rw [Nat.dist_eq_sub_of_le h]; omega
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]; omega
      have hgap_real : (T / 2) * (c * n / N) ≤ |(n : ℝ) - j| := by
        rcases lt_or_gt_of_ne (by
          intro h; subst h; simp at hgapT; linarith only [hgapT, mul_pos hT0 hw0] : j ≠ n) with hlt | hgt
        · rw [abs_of_neg (sub_neg.mpr (Real.log_lt_log hj0 (by exact_mod_cast hlt))), neg_sub] at hgapT
          have hl := Real.log_le_sub_one_of_pos (div_pos hn0 hj0)
          rw [Real.log_div hn0.ne' hj0.ne'] at hl
          have h1 : T * (c / N) < ((n : ℝ) - j) / j := by
            have : (n : ℝ) / j - 1 = ((n : ℝ) - j) / j := by field_simp [hj0.ne']
            linarith only [hgapT, hl, this]
          have h2 : ((n : ℝ) - j) / j ≤ 2 * ((n : ℝ) - j) / n := by
            rw [div_le_div_iff₀ hj0 hn0]
            have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnr1
            have hltR : (j : ℝ) < n := by exact_mod_cast hlt
            nlinarith only [hnjR, hltR]
          have h3 := h1.le.trans h2
          rw [abs_of_pos (sub_pos.mpr (by exact_mod_cast hlt))]
          rw [mul_div_assoc', div_le_div_iff₀ hN0 hn0] at h3
          rw [show (T / 2) * (c * n / N) = T * c * n / (2 * N) by ring, div_le_iff₀ (by positivity)]
          nlinarith only [h3]
        · rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hn0 (by exact_mod_cast hgt)))] at hgapT
          have hl := Real.log_le_sub_one_of_pos (div_pos hj0 hn0)
          rw [Real.log_div hj0.ne' hn0.ne'] at hl
          have h1 : T * (c / N) < ((j : ℝ) - n) / n := by
            have : (j : ℝ) / n - 1 = ((j : ℝ) - n) / n := by field_simp [hn0.ne']
            linarith only [hgapT, hl, this]
          rw [abs_of_neg (sub_neg.mpr (by exact_mod_cast hgt)), neg_sub]
          rw [mul_div_assoc', div_lt_div_iff₀ hN0 hn0] at h1
          rw [show (T / 2) * (c * n / N) = T * c * n / (2 * N) by ring, div_le_iff₀ (by positivity)]
          have hpos_tcn : 0 < T * c * (n : ℝ) := by positivity
          have hN_nn : (0 : ℝ) ≤ N := hN0.le
          nlinarith only [h1, hpos_tcn, hN_nn]
      have hcast_dist : ((Nat.dist n j : ℕ) : ℝ) = |(n : ℝ) - j| := by
        rcases le_total n j with h | h
        · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
            abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h)), neg_sub]
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
            abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
      have hd_le_dist : d_T ≤ Nat.dist n j := by
        refine max_le ?_ (Nat.ceil_le.mpr (hgap_real.trans_eq hcast_dist.symm))
        by_contra h0
        have hz : Nat.dist n j = 0 := by omega
        rw [hz, Nat.cast_zero] at hcast_dist
        have hpos : 0 < (T / 2) * (c * n / N) := by positivity
        linarith only [hpos, hgap_real, hcast_dist]
      exact mem_Icc.mpr ⟨hd_le_dist, hdist_le⟩
    let S_lo := S_near.filter (fun j : ℕ => j < n)
    let S_hi := S_near.filter (fun j : ℕ => n ≤ j)
    have hdisj_S : Disjoint S_lo S_hi := disjoint_left.mpr fun j h1 h2 =>
      (not_le_of_gt (mem_filter.mp h1).2) (mem_filter.mp h2).2
    have hunion_S : S_near = S_lo ∪ S_hi := by
      ext j; simp only [S_lo, S_hi, mem_union, mem_filter]
      exact ⟨fun h => (lt_or_ge j n).imp (⟨h, ·⟩) (⟨h, ·⟩), fun h => h.elim And.left And.left⟩
    have hhalf_sum : ∀ S_sub : Finset ℕ, S_sub ⊆ S_near →
        Set.InjOn (Nat.dist n) S_sub →
        (∑ j ∈ S_sub, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 / (d_T : ℝ) := by
      intro S_sub hsub hinj
      have heq : (∑ j ∈ S_sub, 1 / |(n : ℝ) - j| ^ 2) =
          ∑ k ∈ S_sub.image (Nat.dist n), 1 / (k : ℝ) ^ 2 := by
        rw [sum_image hinj]
        refine sum_congr rfl fun j _ => ?_
        have hcast : ((Nat.dist n j : ℕ) : ℝ) = |(n : ℝ) - j| := by
          rcases le_total n j with h | h
          · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
              abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h)), neg_sub]
          · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
              abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
        rw [hcast]
      rw [heq]
      exact (sum_le_sum_of_subset_of_nonneg
        (fun k hk => by obtain ⟨j, hj, rfl⟩ := mem_image.mp hk; exact hmem_dist j (hsub hj))
        fun _ _ _ => by positivity).trans (sum_Icc_inv_sq_le_two_div hd1)
    have hinj_lo : Set.InjOn (Nat.dist n) S_lo := fun j₁ hj₁ j₂ hj₂ heq => by
      have h1 := (mem_filter.mp hj₁).2
      have h2 := (mem_filter.mp hj₂).2
      rw [Nat.dist_comm n j₁, Nat.dist_eq_sub_of_le h1.le,
        Nat.dist_comm n j₂, Nat.dist_eq_sub_of_le h2.le] at heq
      omega
    have hinj_hi : Set.InjOn (Nat.dist n) S_hi := fun j₁ hj₁ j₂ hj₂ heq => by
      have h1 := (mem_filter.mp hj₁).2
      have h2 := (mem_filter.mp hj₂).2
      rw [Nat.dist_eq_sub_of_le h1, Nat.dist_eq_sub_of_le h2] at heq
      omega
    rw [hunion_S, sum_union hdisj_S]
    have h4d : 2 / (d_T : ℝ) + 2 / (d_T : ℝ) ≤ 8 * N / (T * c * n) := by
      have hpos : 0 < (T / 2) * (c * n / N) := by positivity
      have hinv := one_div_le_one_div_of_le hpos hd_ge
      calc 2 / (d_T : ℝ) + 2 / (d_T : ℝ) = 4 * (1 / (d_T : ℝ)) := by ring
        _ ≤ 4 * (1 / ((T / 2) * (c * n / N))) := mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = 8 * N / (T * c * n) := by field_simp [hT0.ne', hc0.ne', hn0.ne', hN0.ne']; ring
    exact (add_le_add (hhalf_sum S_lo (filter_subset _ _) hinj_lo)
      (hhalf_sum S_hi (filter_subset _ _) hinj_hi)).trans h4d
  have hcard_FT : (F_T.card : ℝ) ≤ N :=
    (Nat.cast_le.mpr (card_le_card (filter_subset _ (Icc 1 N)))).trans
      (by rw [Nat.card_Icc]; push_cast; linarith)
  calc _ ≤ ∑ j ∈ F_T, K₀ * (c / N) ^ 2 * Real.sqrt m *
        ((if j ∈ S_near then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm_pt)
    _ = K₀ * (c / N) ^ 2 * Real.sqrt m *
          ((8 * (n : ℝ) * Real.sqrt n * ∑ j ∈ S_near, 1 / |(n : ℝ) - j| ^ 2) + 4 * F_T.card) := by
        rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
        have hsf : (∑ j ∈ F_T, if j ∈ S_near then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) =
            8 * (n : ℝ) * Real.sqrt n * ∑ j ∈ S_near, 1 / |(n : ℝ) - j| ^ 2 := by
          have hf_eq : F_T.filter (· ∈ S_near) = S_near := by
            ext j; simp only [mem_filter]
            exact ⟨fun h => h.2, fun h => ⟨(mem_filter.mp h).1, h⟩⟩
          rw [← sum_filter, hf_eq, mul_sum]
          refine sum_congr rfl fun _ _ => by ring
        rw [hsf]; ring
    _ ≤ K₀ * (c / N) ^ 2 * Real.sqrt m *
          ((8 * (n : ℝ) * Real.sqrt n * (8 * N / (T * c * n))) + 4 * N) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hdist_sum (by positivity))
          (mul_le_mul_of_nonneg_left hcard_FT (by norm_num))) (by dsimp only [K₀]; positivity)
    _ = C_far * (c ^ 2 / N) + 64 * K₀ * Real.sqrt m / T * (c * Real.sqrt n / N) := by
        dsimp only [C_far]; field_simp [hT0.ne', hc0.ne', hn0.ne', hN0.ne']; ring

/-- Pointwise squared row bound for `separatedCrossErrorMatrix` on `Icc 1 N` (`m ≥ 2`). -/
private lemma separatedCross_row_sq_le {m N n : ℕ} (hm2 : 2 ≤ m)
    (hn : n ∈ Icc 1 N) {c T : ℝ} (hc0 : 0 < c) (hcN : c ≤ N)
    (hT2 : 2 ≤ T) (hTw : T * (c / N) ≤ 2) :
    (∑ j ∈ Icc 1 N, (if 2 * (c / N) < |Real.log (j : ℝ) - Real.log (n : ℝ)| then
        atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j else 0) *
        (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 ≤
      4 * (2 * (2 * Real.exp 1 * (farCrossLip tiltedUnitSpline / 2) +
          2 * T * Real.exp 5 * (farCrossLip tiltedUnitSpline / 4)) * m) ^ 2 * (1 / (n : ℝ)) +
      4 * (2 * T * Real.exp 3 *
          (5 / 2 * (∫ t, |bumpAutocorr tiltedUnitSpline t|) / (∫ u, tiltedUnitSpline u ^ 2)) *
          Real.sqrt m) ^ 2 * c ^ 2 * (c / N) ^ 2 * ((n : ℝ) / N ^ 2) +
      4 * (4 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
          Real.sqrt m) ^ 2 * (c ^ 4 / N ^ 2) +
      4 * (64 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2))) ^ 2 *
          (m : ℝ) / T ^ 2 * (c ^ 2 * (n : ℝ) / N ^ 2) := by
  have hm0 : 0 < m := by omega
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  let K₀ : ℝ := 152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)
  let C_ker_err : ℝ := 5 / 2 * (∫ t, |bumpAutocorr tiltedUnitSpline t|) / (∫ u, tiltedUnitSpline u ^ 2)
  let AK : ℝ := farCrossLip tiltedUnitSpline / 2
  let LK : ℝ := farCrossLip tiltedUnitSpline / 4
  have hAK0 : 0 ≤ AK := div_nonneg (farCrossLip_nonneg _) zero_le_two
  have hLK0 : 0 ≤ LK := div_nonneg (farCrossLip_nonneg _) (by norm_num)
  let C_sing : ℝ := 2 * (2 * Real.exp 1 * AK + 2 * T * Real.exp 5 * LK) * m
  let C_werr : ℝ := 2 * T * Real.exp 3 * C_ker_err * Real.sqrt m
  let C_far : ℝ := 4 * K₀ * Real.sqrt m
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hN1 : 1 ≤ N := hn1.trans (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc0 hN0
  let W_T := (Icc 1 N).filter (fun j : ℕ => j ≠ n ∧
    2 * (c / N) < |Real.log (j : ℝ) - Real.log (n : ℝ)| ∧
    |Real.log (j : ℝ) - Real.log (n : ℝ)| ≤ T * (c / N))
  let F_T := (Icc 1 N).filter (fun j : ℕ => T * (c / N) < |Real.log (j : ℝ) - Real.log (n : ℝ)|)
  have hdisj : Disjoint W_T F_T := disjoint_left.mpr fun j h1 h2 =>
    (not_lt_of_ge (mem_filter.mp h1).2.2.2) (mem_filter.mp h2).2
  have hrow_split : (∑ j ∈ Icc 1 N, (if 2 * (c / N) < |Real.log (j : ℝ) - Real.log (n : ℝ)| then
      atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j else 0) *
      (normalizedRamanujanMode m j / Real.sqrt j)) =
      (∑ j ∈ W_T, crossSingular tiltedUnitSpline (1 / (|Real.log (j : ℝ) - Real.log (n : ℝ)| / (c / N))) *
        normalizedRamanujanMode m j / Real.sqrt j) +
      (∑ j ∈ W_T, (atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j -
        crossSingular tiltedUnitSpline ((c / N) / |Real.log (j : ℝ) - Real.log (n : ℝ)|)) *
        (normalizedRamanujanMode m j / Real.sqrt j)) +
      (∑ j ∈ F_T, atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j *
        (normalizedRamanujanMode m j / Real.sqrt j)) := by
    have hunion : (Icc 1 N).filter (fun j : ℕ => 2 * (c / N) < |Real.log (j : ℝ) - Real.log (n : ℝ)|) =
        W_T ∪ F_T := by
      ext j; simp only [W_T, F_T, mem_union, mem_filter]
      constructor
      · rintro ⟨hjI, hgt⟩
        have hjn : j ≠ n := by
          intro heq; subst heq; simp only [sub_self, abs_zero] at hgt; linarith only [hgt, hw0]
        rcases le_or_gt |Real.log (j : ℝ) - Real.log (n : ℝ)| (T * (c / N)) with hle | hgtT
        · exact Or.inl ⟨hjI, hjn, hgt, hle⟩
        · exact Or.inr ⟨hjI, hgtT⟩
      · rintro (⟨hjI, _, hgt, _⟩ | ⟨hjI, hgtT⟩)
        · exact ⟨hjI, hgt⟩
        · exact ⟨hjI, (mul_le_mul_of_nonneg_right hT2 hw0.le).trans_lt hgtT⟩
    have h1 : (∑ j ∈ Icc 1 N, (if 2 * (c / N) < |Real.log (j : ℝ) - Real.log (n : ℝ)| then
        atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j else 0) *
        (normalizedRamanujanMode m j / Real.sqrt j)) =
        ∑ j ∈ W_T ∪ F_T,
          atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j *
            (normalizedRamanujanMode m j / Real.sqrt j) := by
      rw [← hunion, sum_filter]
      refine sum_congr rfl fun j _ => by split_ifs <;> ring
    rw [h1, sum_union hdisj]
    congr 1
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [one_div_div]; ring
  have hb_sing : |∑ j ∈ W_T,
      crossSingular tiltedUnitSpline (1 / (|Real.log (j : ℝ) - Real.log (n : ℝ)| / (c / N))) *
        normalizedRamanujanMode m j / Real.sqrt j| ≤ C_sing / Real.sqrt n :=
    abs_gapWindow_lipschitz_mode_le (K := fun s => crossSingular tiltedUnitSpline (1 / s))
      zero_le_two hT2 hAK0 hLK0
      (fun s hs => abs_crossSingular_inv_le hφ hsupp hM hs.1)
      (fun x hx y hy => abs_crossSingular_inv_sub_le hφ hsupp hM hx.1 hy.1)
      hm2 hn hc0 hTw
  have hb_werr : |∑ j ∈ W_T,
      (atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j -
        crossSingular tiltedUnitSpline ((c / N) / |Real.log (j : ℝ) - Real.log (n : ℝ)|)) *
        (normalizedRamanujanMode m j / Real.sqrt j)| ≤
      C_werr * (c ^ 2 * Real.sqrt n / N ^ 2) := by
    have hcard_WT : (W_T.card : ℝ) ≤ 2 * T * Real.exp 2 * (c * n / N) := by
      let r := (n : ℝ) * (T * (c / N) * Real.exp 2)
      have hr0 : 0 ≤ r := by dsimp only [r]; positivity
      have hsub : W_T ⊆ (Icc 1 N).filter (fun j : ℕ => j ≠ n ∧ |(j : ℝ) - n| ≤ r) := fun j hj => by
        obtain ⟨hjI, hjn, _, hhi⟩ := mem_filter.mp hj
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
        have he : Real.exp (T * (c / N)) - 1 ≤ T * (c / N) * Real.exp 2 :=
          exp_sub_one_le_mul_exp.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hTw) (by positivity))
        exact mem_filter.mpr ⟨hjI, hjn, (abs_sub_le_of_abs_log_le hj0 hn0 hhi).trans
          (mul_le_mul_of_nonneg_left he hn0.le)⟩
      exact ((show (W_T.card : ℝ) ≤ _ by exact_mod_cast card_le_card hsub).trans
        (card_near_le (Icc 1 N) n hr0)).trans_eq (by dsimp only [r]; ring)
    have hj_le : ∀ j ∈ W_T,
        |(atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j -
          crossSingular tiltedUnitSpline ((c / N) / |Real.log (j : ℝ) - Real.log (n : ℝ)|)) *
          (normalizedRamanujanMode m j / Real.sqrt j)| ≤
        C_ker_err * (c / N) * Real.sqrt m * Real.exp 1 / Real.sqrt n := fun j hj => by
      obtain ⟨hjI, hjn, hlo, hhi⟩ := mem_filter.mp hj
      have hj1 := (mem_Icc.mp hjI).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hws : c / N < |Real.log (j : ℝ) - Real.log (n : ℝ)| := by linarith only [hlo, hw0]
      have hker := abs_atomCrossErrorKernel_sub_crossSingular_le hφ hsupp hM
        hw0 hn1 hj1 (Ne.symm hjn) hws
      have hlow : Real.log n - 2 ≤ Real.log j := by linarith only [(abs_le.mp hhi).1, hTw]
      have hexp : (n : ℝ) * Real.exp (-2) ≤ j := by
        rw [← Real.exp_log hn0, ← Real.exp_add, ← Real.exp_log hj0]
        exact Real.exp_le_exp.mpr (by linarith only [hlow])
      have hsj : 1 / Real.sqrt (j : ℝ) ≤ Real.exp 1 / Real.sqrt n := by
        have he2 : Real.exp (-2) = Real.exp (-1) ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
        rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hj0) hsn, one_mul]
        calc Real.sqrt (n : ℝ) = Real.sqrt ((n : ℝ) * Real.exp (-2)) * Real.exp 1 := by
              rw [Real.sqrt_mul hn0.le, he2, Real.sqrt_sq (Real.exp_pos _).le,
                mul_assoc, ← Real.exp_add]
              norm_num
          _ ≤ Real.sqrt j * Real.exp 1 :=
              mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hexp) (Real.exp_pos 1).le
          _ = Real.exp 1 * Real.sqrt j := mul_comm _ _
      rw [div_eq_mul_one_div (normalizedRamanujanMode m j), abs_mul, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
      exact (mul_le_mul hker (mul_le_mul (abs_mode_le_sqrt_conductor hm0 j) hsj
        (by positivity) (Real.sqrt_nonneg _)) (by positivity) (by positivity)).trans_eq
        (by dsimp only [C_ker_err]; ring)
    have hexp3 : Real.exp 2 * Real.exp 1 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
    calc _ ≤ (W_T.card : ℝ) * (C_ker_err * (c / N) * Real.sqrt m * Real.exp 1 / Real.sqrt n) := by
          rw [← nsmul_eq_mul, ← sum_const]; exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hj_le)
      _ ≤ (2 * T * Real.exp 2 * (c * n / N)) *
            (C_ker_err * (c / N) * Real.sqrt m * Real.exp 1 / Real.sqrt n) :=
          mul_le_mul_of_nonneg_right hcard_WT (by dsimp only [C_ker_err]; positivity)
      _ = C_werr * (c ^ 2 * Real.sqrt n / N ^ 2) := by
          dsimp only [C_werr]; field_simp [hsn.ne', hN0.ne']
          rw [Real.sq_sqrt hn0.le, ← hexp3]; ring
  have hb_tail : |∑ j ∈ F_T, atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j *
      (normalizedRamanujanMode m j / Real.sqrt j)| ≤
      C_far * (c ^ 2 / N) + 64 * K₀ * Real.sqrt m / T * (c * Real.sqrt n / N) :=
    separatedCross_tail_row_le hm0 hn hc0 hcN hT2
  rw [hrow_split]
  set z₁ := ∑ j ∈ W_T, crossSingular tiltedUnitSpline (1 / (|Real.log (j : ℝ) - Real.log (n : ℝ)| / (c / N))) *
    normalizedRamanujanMode m j / Real.sqrt j
  set z₂ := ∑ j ∈ W_T, (atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j -
    crossSingular tiltedUnitSpline ((c / N) / |Real.log (j : ℝ) - Real.log (n : ℝ)|)) *
    (normalizedRamanujanMode m j / Real.sqrt j)
  set z₃ := ∑ j ∈ F_T, atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j *
    (normalizedRamanujanMode m j / Real.sqrt j)
  have htri : |z₁ + z₂ + z₃| ≤ C_sing / Real.sqrt n + C_werr * (c ^ 2 * Real.sqrt n / N ^ 2) +
      C_far * (c ^ 2 / N) + 64 * K₀ * Real.sqrt m / T * (c * Real.sqrt n / N) := by
    have t1 := abs_add_le (z₁ + z₂) z₃
    have t2 := abs_add_le z₁ z₂
    linarith only [t1, t2, hb_sing, hb_werr, hb_tail]
  have hsq := pow_le_pow_left₀ (abs_nonneg _) htri 2
  rw [sq_abs] at hsq
  set q₁ := C_sing / Real.sqrt n
  set q₂ := C_werr * (c ^ 2 * Real.sqrt n / N ^ 2)
  set q₃ := C_far * (c ^ 2 / N)
  set q₄ := 64 * K₀ * Real.sqrt m / T * (c * Real.sqrt n / N)
  have h4sq : (q₁ + q₂ + q₃ + q₄) ^ 2 ≤ 4 * q₁ ^ 2 + 4 * q₂ ^ 2 + 4 * q₃ ^ 2 + 4 * q₄ ^ 2 := by
    nlinarith only [sq_nonneg ((q₁ + q₂) - (q₃ + q₄)), sq_nonneg (q₁ - q₂), sq_nonneg (q₃ - q₄)]
  have hq1 : q₁ ^ 2 = C_sing ^ 2 * (1 / (n : ℝ)) := by
    dsimp only [q₁]; rw [div_pow, Real.sq_sqrt hn0.le]; ring
  have hq2 : q₂ ^ 2 = C_werr ^ 2 * c ^ 2 * (c / N) ^ 2 * ((n : ℝ) / N ^ 2) := by
    dsimp only [q₂]; rw [mul_pow C_werr, div_pow, mul_pow (c ^ 2) (Real.sqrt n), Real.sq_sqrt hn0.le]; ring
  have hq3 : q₃ ^ 2 = C_far ^ 2 * (c ^ 4 / N ^ 2) := by dsimp only [q₃]; ring
  have hq4 : q₄ ^ 2 = (64 * K₀) ^ 2 * (m : ℝ) / T ^ 2 * (c ^ 2 * (n : ℝ) / N ^ 2) := by
    dsimp only [q₄]
    rw [mul_pow _ (c * Real.sqrt n / N), div_pow _ T, mul_pow (64 * K₀) (Real.sqrt m),
      Real.sq_sqrt (Nat.cast_nonneg m), div_pow (c * Real.sqrt n) N,
      mul_pow c (Real.sqrt n), Real.sq_sqrt hn0.le]
  rw [hq1, hq2, hq3, hq4] at h4sq
  exact hsq.trans (h4sq.trans_eq (by dsimp only [C_sing, AK, LK, C_werr, C_ker_err, C_far, K₀]; ring))

/-- Subchannel 3d (`m ≥ 2`): Channel 4 (`separatedCrossErrorMatrix`) vanishes in
`(log N / c²) * topWindowResidualMass` along any critical curve. -/
private theorem tendsto_topWindow_separatedCross_nonpolar {m : ℕ} (hm2 : 2 ≤ m)
    {δ : ℝ} (hδ0 : 0 < δ)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N)))
      atTop (𝓝 0) := by
  let K₀ : ℝ := 152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)
  have hK₀0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  let C_ker_err : ℝ := 5 / 2 * (∫ t, |bumpAutocorr tiltedUnitSpline t|) / (∫ u, tiltedUnitSpline u ^ 2)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let T : ℝ := max 2 (256 * K₀ * Real.sqrt m / Real.sqrt ε + 1)
  have hT2 : 2 ≤ T := le_max_left _ _
  have hT0 : 0 < T := zero_lt_two.trans_le hT2
  have htail_small : 4 * (64 * K₀) ^ 2 * (m : ℝ) / T ^ 2 < ε / 2 := by
    have hT_gt : 256 * K₀ * Real.sqrt m / Real.sqrt ε < T :=
      (lt_add_one _).trans_le (le_max_right _ _)
    have hsq := pow_lt_pow_left₀ hT_gt (by positivity) (by decide : 2 ≠ 0)
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), Real.sq_sqrt hε.le] at hsq
    have hpos_T2 : 0 < T ^ 2 := sq_pos_of_pos hT0
    rw [div_lt_iff₀ hpos_T2]
    have hmul := (div_lt_iff₀ hε).mp hsq
    nlinarith only [hmul, hpos_T2, hε]
  let AK : ℝ := farCrossLip tiltedUnitSpline / 2
  let LK : ℝ := farCrossLip tiltedUnitSpline / 4
  let C_sing : ℝ := 2 * (2 * Real.exp 1 * AK + 2 * T * Real.exp 5 * LK) * m
  let C_werr : ℝ := 2 * T * Real.exp 3 * C_ker_err * Real.sqrt m
  let C_far : ℝ := 4 * K₀ * Real.sqrt m
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hcN_lim : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hrem_lim : Tendsto (fun N : ℕ =>
      4 * C_sing ^ 2 / δ * (1 / c N ^ 2) +
      4 * C_werr ^ 2 * (c N / N) ^ 2 +
      4 * C_far ^ 2 * (c N ^ 2 / (N : ℝ))) atTop (𝓝 0) := by
    have l1 : Tendsto (fun N : ℕ => 1 / c N ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hcinf)
    have l2 : Tendsto (fun N : ℕ => (c N / N) ^ 2) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0)] using hcN_lim.pow 2
    have l3 : Tendsto (fun N : ℕ => c N ^ 2 / (N : ℝ)) atTop (𝓝 0) := by
      simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 2 0
    have h := ((l1.const_mul (4 * C_sing ^ 2 / δ)).add (l2.const_mul (4 * C_werr ^ 2))).add
      (l3.const_mul (4 * C_far ^ 2))
    simpa only [mul_zero, add_zero] using h
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hTw_ev : ∀ᶠ N : ℕ in atTop, T * (c N / N) ≤ 2 := by
    have hlim_Tw : Tendsto (fun N : ℕ => T * (c N / N)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hcN_lim.const_mul T
    exact (hlim_Tw.eventually (gt_mem_nhds two_pos)).mono fun _ h => h.le
  have hrem_ev : ∀ᶠ N : ℕ in atTop,
      4 * C_sing ^ 2 / δ * (1 / c N ^ 2) + 4 * C_werr ^ 2 * (c N / N) ^ 2 +
        4 * C_far ^ 2 * (c N ^ 2 / (N : ℝ)) < ε / 2 :=
    hrem_lim.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (((eventually_below_overlap_pair_admissible hc hR hcrit).and hlog).and (hTw_ev.and hrem_ev))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨hadm, hL1⟩, hTw, hrem_lt⟩ := hN₀ N hN
  obtain ⟨_, _, _, hc4N⟩ := hadm 1 1 (by simpa using hc N) (by simpa using hc N)
  have hc1 := hc N
  have hc0 : 0 < c N := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hcN : c N ≤ N := (le_self_pow₀ hc1 (by norm_num : 4 ≠ 0)).trans hc4N
  have hN1 : 1 ≤ N := by exact_mod_cast hc1.trans hcN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  let row_x : ℕ → ℝ := fun n =>
    ∑ j ∈ Icc 1 N, (if 2 * (c N / N) < |Real.log (j : ℝ) - Real.log (n : ℝ)| then
      atomCrossErrorKernel (atomDilate tiltedUnitSpline (c N / N)) n j else 0) *
      (normalizedRamanujanMode m j / Real.sqrt j)
  have hmass_eq : (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N)) =
      (1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, row_x n ^ 2 := by
    unfold topWindowResidualMass
    have hpt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        primeHorizonExtension (Matrix.toEuclideanLin
          (separatedCrossErrorMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N)) n ^ 2 = row_x n ^ 2 / Real.log N := fun n hn_top => by
      let idx : PrimeHorizonIndex N :=
        ⟨n, mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn_top).1; omega, (mem_Ioc.mp hn_top).2⟩⟩
      have hcoord : (Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N)) idx = row_x idx.1 / Real.sqrt (Real.log N) := by
        rw [normalizedRamanujanHorizonVector, map_smul]
        change (Real.sqrt (Real.log N))⁻¹ *
          ((Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline (c N) N)
            (ramanujanHorizonVector m N)) idx) = _
        rw [div_eq_inv_mul]
        congr 1
        exact horizonKernelMatrix_apply_profile
          (fun k j => if 2 * (c N / N) < |Real.log (j : ℝ) - Real.log (k : ℝ)| then
            atomCrossErrorKernel (atomDilate tiltedUnitSpline (c N / N)) k j else 0)
          (ramanujanPoleProfile m) N idx
      change primeHorizonExtension _ idx.1 ^ 2 = _
      rw [primeHorizonExtension_coe, hcoord, div_pow, Real.sq_sqrt hL0.le]
    rw [sum_congr rfl hpt, ← sum_div]; field_simp [hL0.ne', hc0.ne']
  have hrow_sq : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, row_x n ^ 2 ≤
      4 * C_sing ^ 2 * (1 / (n : ℝ)) +
      4 * C_werr ^ 2 * c N ^ 2 * (c N / N) ^ 2 * ((n : ℝ) / N ^ 2) +
      4 * C_far ^ 2 * (c N ^ 4 / N ^ 2) +
      4 * (64 * K₀) ^ 2 * (m : ℝ) / T ^ 2 * (c N ^ 2 * (n : ℝ) / N ^ 2) := fun n hn_top => by
    have hn : n ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn_top).1; omega, (mem_Ioc.mp hn_top).2⟩
    exact separatedCross_row_sq_le hm2 hn hc0 hcN hT2 hTw
  have hsum_n : (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ) / N ^ 2) ≤ 1 := by
    calc (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ) / N ^ 2)
        ≤ ∑ _n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (N : ℝ) / N ^ 2 :=
          sum_le_sum fun n hn_top => div_le_div_of_nonneg_right
            (by exact_mod_cast (mem_Ioc.mp hn_top).2) (sq_nonneg _)
      _ = ((Ioc ⌊δ * (N : ℝ)⌋₊ N).card : ℝ) * ((N : ℝ) / N ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * ((N : ℝ) / N ^ 2) :=
          mul_le_mul_of_nonneg_right (by rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le N _) (by positivity)
      _ = 1 := by field_simp [hN0.ne']
  have hcard_N : ((Ioc ⌊δ * (N : ℝ)⌋₊ N).card : ℝ) ≤ N := by
    rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le N _
  have htot_le : (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N)) ≤
      (4 * C_sing ^ 2 / δ * (1 / c N ^ 2) + 4 * C_werr ^ 2 * (c N / N) ^ 2 +
        4 * C_far ^ 2 * (c N ^ 2 / (N : ℝ))) +
      4 * (64 * K₀) ^ 2 * (m : ℝ) / T ^ 2 := by
    rw [hmass_eq]
    calc (1 / c N ^ 2) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, row_x n ^ 2
        ≤ (1 / c N ^ 2) * (4 * C_sing ^ 2 * (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, 1 / (n : ℝ)) +
            4 * C_werr ^ 2 * c N ^ 2 * (c N / N) ^ 2 * (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ) / N ^ 2) +
            (Ioc ⌊δ * (N : ℝ)⌋₊ N).card * (4 * C_far ^ 2 * (c N ^ 4 / N ^ 2)) +
            4 * (64 * K₀) ^ 2 * (m : ℝ) / T ^ 2 * c N ^ 2 *
              (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, (n : ℝ) / N ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ((sum_le_sum hrow_sq).trans_eq ?_) (by positivity)
          rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, nsmul_eq_mul]
          congr 1
          rw [mul_sum]
          refine sum_congr rfl fun _ _ => by ring
      _ ≤ (1 / c N ^ 2) * (4 * C_sing ^ 2 * (1 / δ) +
            4 * C_werr ^ 2 * c N ^ 2 * (c N / N) ^ 2 * 1 +
            (N : ℝ) * (4 * C_far ^ 2 * (c N ^ 4 / N ^ 2)) +
            4 * (64 * K₀) ^ 2 * (m : ℝ) / T ^ 2 * c N ^ 2 * 1) :=
          mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left (sum_topWindow_inv_le hδ0 hN1) (by positivity))
            (mul_le_mul_of_nonneg_left hsum_n (by positivity)))
            (mul_le_mul_of_nonneg_right hcard_N (by positivity)))
            (mul_le_mul_of_nonneg_left hsum_n (by positivity))) (by positivity)
      _ = _ := by field_simp [hc0.ne', hδ0.ne', hN0.ne', hT0.ne']
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (mul_nonneg (div_nonneg hL0.le (sq_nonneg _)) (topWindowResidualMass_nonneg δ N _))]
  linarith only [htot_le, hrem_lt, htail_small]

/-- Top-window bound for the boundary-exception difference `linearizedUpwardCoefficient - reciprocalUpwardCoefficient`. -/
private lemma upward_reciprocal_topWindow_le {m N : ℕ} (hm : 1 ≤ m)
    {δ c : ℝ} (hδ0 : 0 < δ) (hc1 : 1 ≤ c) (hcN : c ≤ N)
    (hN1 : 1 ≤ N) (hL1 : 1 ≤ Real.log (N : ℝ))
    (hBN : linearPrimeStrip c ≤ N)
    (h2dN : 2 * ((Real.exp 1 + 2) * c) + 1 < δ * N) :
    (Real.log (N : ℝ) / c ^ 2) * (m.totient : ℝ)⁻¹ *
      topWindowResidualMass δ N
        (WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
          ((linearizedUpwardCoefficient tiltedUnitSpline c (linearPrimeStrip c) N m idx.1 -
            reciprocalUpwardCoefficient tiltedUnitSpline c (linearPrimeStrip c) N m idx.1) /
            Real.sqrt idx.1) / Real.sqrt (Real.log N))) ≤
      32 * (Real.exp 1 + 2) ^ 3 * (m.totient : ℝ) * ⌊2 / δ⌋₊ / δ * (c / N) := by
  have hm0 : 0 < m := by omega
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  let d : ℝ := Real.exp 1 + 2
  let K_k : ℕ := ⌊2 / δ⌋₊
  set B := linearPrimeStrip c
  have hB_le : (B : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
  have hB1 : (B : ℝ) + 1 ≤ d * c := by dsimp only [d]; linarith only [hB_le, hc1]
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient tiltedUnitSpline c B N m n -
      reciprocalUpwardCoefficient tiltedUnitSpline c B N m n) / Real.sqrt n
  let u_b : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun idx : PrimeHorizonIndex N => b idx.1 / Real.sqrt (Real.log N))
  let S_ex : ℕ → Finset ℕ := fun n =>
    (Icc 1 (N + B)).filter (fun k : ℕ => N ≤ k * n + B ∧ k * n ≤ N + B)
  let T_b := (Ioc ⌊δ * (N : ℝ)⌋₊ N).filter (fun n : ℕ => (S_ex n).Nonempty)
  have hcard_Tb : (T_b.card : ℝ) ≤ (K_k : ℝ) * (2 * d * c) := by
    let F_k : ℕ → Finset ℕ := fun k =>
      (Ioc ⌊δ * (N : ℝ)⌋₊ N).filter (fun n : ℕ => N ≤ k * n + B ∧ k * n ≤ N + B)
    have hsub_bi : T_b ⊆ (Icc 1 K_k).biUnion F_k := fun n hn => by
      obtain ⟨hn_top, k, hk⟩ := mem_filter.mp hn
      obtain ⟨hkI, hlo, hhi⟩ := mem_filter.mp hk
      have hn_gt : δ * N < n := (Nat.lt_floor_add_one (δ * N)).trans_le
        (by exact_mod_cast (Nat.succ_le_of_lt (mem_Ioc.mp hn_top).1))
      have hk_le : k ≤ K_k := Nat.le_floor <| (le_div_iff₀ hδ0).mpr <| by
        have h1 : (k : ℝ) * (δ * N) ≤ (k : ℝ) * n := mul_le_mul_of_nonneg_left hn_gt.le (Nat.cast_nonneg k)
        have h2 : (k : ℝ) * n ≤ 2 * N := by
          have : ((k * n : ℕ) : ℝ) ≤ N + B := by exact_mod_cast hhi
          have hBR : (B : ℝ) ≤ N := by exact_mod_cast hBN
          push_cast at this; linarith only [this, hBR]
        nlinarith only [h1, h2, hN0]
      exact mem_biUnion.mpr ⟨k, mem_Icc.mpr ⟨(mem_Icc.mp hkI).1, hk_le⟩, mem_filter.mpr ⟨hn_top, hlo, hhi⟩⟩
    have hcard_Fk : ∀ k ∈ Icc 1 K_k, (F_k k).card ≤ 2 * B + 1 := fun k hk => by
      have hk1 := (mem_Icc.mp hk).1
      by_cases hne : (F_k k).Nonempty
      · let n₀ := (F_k k).min' hne
        have hn₀_lo : N ≤ k * n₀ + B := (mem_filter.mp ((F_k k).min'_mem hne)).2.1
        have hsub_k : F_k k ⊆ Icc n₀ (n₀ + 2 * B) := fun n hn => by
          have hmin : n₀ ≤ n := (F_k k).min'_le n hn
          have hn_hi := (mem_filter.mp hn).2.2
          have hstep : k * (n - n₀) ≤ 2 * B := by
            have hmul_le : k * n₀ ≤ k * n := Nat.mul_le_mul_left k hmin
            rw [Nat.mul_sub_left_distrib]
            omega
          have hdiff : n - n₀ ≤ 2 * B := (Nat.le_mul_of_pos_left _ hk1).trans hstep
          exact mem_Icc.mpr ⟨hmin, by omega⟩
        exact (card_le_card hsub_k).trans (by rw [Nat.card_Icc]; omega)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne; rw [hne]; simp
    have hnat : T_b.card ≤ K_k * (2 * B + 1) :=
      (card_le_card hsub_bi).trans ((card_biUnion_le).trans
        ((sum_le_sum hcard_Fk).trans_eq (by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul])))
    have h2B1 : (2 * (B : ℝ) + 1) ≤ 2 * d * c := by linarith only [hB1]
    exact (by exact_mod_cast hnat : (T_b.card : ℝ) ≤ (K_k : ℝ) * (2 * (B : ℝ) + 1)).trans
      (mul_le_mul_of_nonneg_left h2B1 (Nat.cast_nonneg K_k))
  have hrow_Sex : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      |linearizedUpwardCoefficient tiltedUnitSpline c B N m n -
        reciprocalUpwardCoefficient tiltedUnitSpline c B N m n| ≤
      4 * (B : ℝ) * m.totient * ∑ k ∈ S_ex n, (Λ k : ℝ) / k := fun n hn_top => by
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn_top).1; omega
    let L_val := 4 * (B : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * m.totient
    have hpk : ∀ k ∈ Icc 1 (N + B),
        |∑ h ∈ Icc 1 B, (linearizedUpwardOffset tiltedUnitSpline c N m n k h -
            reciprocalUpwardOffset tiltedUnitSpline c N m n k h)| ≤
          if N ≤ k * n + B ∧ k * n ≤ N + B then L_val else 0 := by
      intro k hk
      have hT : 1 ≤ k * n := Nat.mul_pos (mem_Icc.mp hk).1 hn1
      by_cases hex : N ≤ k * n + B ∧ k * n ≤ N + B
      · rw [if_pos hex]
        have h := (abs_sum_le_sum_abs _ (Icc 1 B)).trans
          (sum_le_sum fun h _ => abs_linearizedUpwardOffset_sub_reciprocal_le hφ hsupp c N m n k h)
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at h
        exact h.trans_eq (by dsimp only [L_val]; ring)
      · rw [if_neg hex]
        have hz : (∑ h ∈ Icc 1 B, (linearizedUpwardOffset tiltedUnitSpline c N m n k h -
            reciprocalUpwardOffset tiltedUnitSpline c N m n k h)) = 0 := by
          refine sum_eq_zero fun h hh => ?_
          have hhB := (mem_Icc.mp hh).2
          by_cases hhT : h < k * n
          · rcases (show k * n + B < N ∨ N + B < k * n by omega) with hfar | hfar
            · simp only [linearizedUpwardOffset, reciprocalUpwardOffset,
                if_pos (show k * n + h ≤ N by omega),
                if_pos (show h < k * n ∧ k * n - h ≤ N from ⟨hhT, by omega⟩),
                if_pos (show k * n ≤ N by omega),
                ramanujanLagCoefficient_sub_eq_reflected hm hhT.le, sub_self]
            · simp only [linearizedUpwardOffset, reciprocalUpwardOffset,
                if_neg (show ¬ k * n + h ≤ N by omega),
                if_neg (show ¬ (h < k * n ∧ k * n - h ≤ N) by omega),
                if_neg (show ¬ k * n ≤ N by omega), add_zero, sub_self]
          · have hT0 : (0 : ℝ) < (k * n : ℕ) := by exact_mod_cast hT
            have hzero := shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
              ((one_le_mul_of_one_le_of_one_le ((one_le_div hc0).mpr hcN)
                ((one_le_div hT0).mpr (Nat.cast_le.mpr (by omega : k * n ≤ h)))).trans
                (le_abs_self _))
            simp only [linearizedUpwardOffset, reciprocalUpwardOffset, hzero, mul_zero, sub_self]
        rw [hz, abs_zero]
    unfold linearizedUpwardCoefficient reciprocalUpwardCoefficient
    rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hM)]
    calc _ ≤ 1 / (∫ u, tiltedUnitSpline u ^ 2) * ∑ k ∈ Icc 1 (N + B),
          if N ≤ k * n + B ∧ k * n ≤ N + B then (Λ k : ℝ) / k * L_val else 0 := by
          refine mul_le_mul_of_nonneg_left
            ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)) (by positivity)
          rw [← mul_sub, ← sum_sub_distrib, abs_mul,
            abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))]
          have hp := hpk k hk
          split_ifs at hp ⊢
          · exact mul_le_mul_of_nonneg_left hp
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
          · simpa only [mul_zero] using mul_le_mul_of_nonneg_left hp
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
      _ = 4 * (B : ℝ) * m.totient * ∑ k ∈ S_ex n, (Λ k : ℝ) / k := by
          dsimp only [S_ex, L_val]; rw [← sum_filter, ← sum_mul]; field_simp [hM.ne']
  have hrestrict : topWindowResidualMass δ N u_b =
      (∑ n ∈ T_b, b n ^ 2) / Real.log N := by
    unfold topWindowResidualMass
    have hpt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        primeHorizonExtension u_b n ^ 2 = b n ^ 2 / Real.log N := fun n hn_top => by
      let idx : PrimeHorizonIndex N :=
        ⟨n, mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn_top).1; omega, (mem_Ioc.mp hn_top).2⟩⟩
      change primeHorizonExtension u_b idx.1 ^ 2 = _
      rw [primeHorizonExtension_coe, div_pow, Real.sq_sqrt hL0.le]
    rw [sum_congr rfl hpt, ← sum_div]
    congr 1; symm
    refine sum_subset (filter_subset _ _) fun n hn_top hn_not => ?_
    have hempty : S_ex n = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun h =>
      hn_not (mem_filter.mpr ⟨hn_top, h⟩)
    have hb0 : b n = 0 := by
      have hr := hrow_Sex n hn_top
      rw [hempty, sum_empty, mul_zero, abs_nonpos_iff] at hr
      dsimp only [b]; rw [hr, zero_div]
    rw [hb0, zero_pow (by decide)]
  have hpt_Tb : ∀ n ∈ T_b, b n ^ 2 ≤ 16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / (δ * N) := by
    intro n hnT
    have hn_top := (mem_filter.mp hnT).1
    have hn_gt : δ * N < n := (Nat.lt_floor_add_one (δ * N)).trans_le
      (by exact_mod_cast (Nat.succ_le_of_lt (mem_Ioc.mp hn_top).1))
    have hn0 : (0 : ℝ) < n := (mul_pos hδ0 hN0).trans hn_gt
    have hn2B : 2 * B < n := by
      have hBR : 2 * (B : ℝ) + 1 ≤ 2 * (d * c) + 1 := by linarith only [hB1]
      have : 2 * (B : ℝ) + 1 < n := hBR.trans_lt (h2dN.trans hn_gt)
      exact_mod_cast (show 2 * B + 1 ≤ n by exact_mod_cast this.le)
    have hcard_one : (S_ex n).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun k₁ hk₁ k₂ hk₂ => ?_
      obtain ⟨_, h1lo, h1hi⟩ := mem_filter.mp hk₁
      obtain ⟨_, h2lo, h2hi⟩ := mem_filter.mp hk₂
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hstep : (k₁ + 1) * n ≤ k₂ * n := Nat.mul_le_mul_right n hlt
        nlinarith [hstep, hn2B, h1lo, h2hi]
      · have hstep : (k₂ + 1) * n ≤ k₁ * n := Nat.mul_le_mul_right n hgt
        nlinarith [hstep, hn2B, h2lo, h1hi]
    have hsum_k : (∑ k ∈ S_ex n, (Λ k : ℝ) / k) ≤ 1 := by
      calc (∑ k ∈ S_ex n, (Λ k : ℝ) / k) ≤ ∑ _k ∈ S_ex n, (1 : ℝ) := by
            refine sum_le_sum fun k hk => ?_
            have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hk).1).1
            rw [div_le_one hk0]
            linarith [ArithmeticFunction.vonMangoldt_le_log (n := k),
              Real.log_le_sub_one_of_pos hk0]
        _ = ((S_ex n).card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
        _ ≤ 1 := by exact_mod_cast hcard_one
    have hBd : (B : ℝ) ≤ d * c := by linarith only [hB1]
    have hnum : |linearizedUpwardCoefficient tiltedUnitSpline c B N m n -
        reciprocalUpwardCoefficient tiltedUnitSpline c B N m n| ≤
        4 * d * (m.totient : ℝ) * c :=
      (hrow_Sex n hn_top).trans ((mul_le_mul_of_nonneg_left hsum_k (by positivity)).trans
        (by nlinarith only [hBd, htot_pos]))
    have hnum2 : (linearizedUpwardCoefficient tiltedUnitSpline c B N m n -
        reciprocalUpwardCoefficient tiltedUnitSpline c B N m n) ^ 2 ≤
        16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 := by
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hnum 2
      rw [sq_abs] at hsq; exact hsq.trans_eq (by ring)
    dsimp only [b]
    rw [div_pow, Real.sq_sqrt hn0.le]
    exact (div_le_div_of_nonneg_right hnum2 hn0.le).trans
      (div_le_div_of_nonneg_left (by dsimp only [d]; positivity) (mul_pos hδ0 hN0) hn_gt.le)
  have hsum_Tb : (∑ n ∈ T_b, b n ^ 2) ≤
      32 * d ^ 3 * (m.totient : ℝ) ^ 2 * K_k / δ * (c ^ 3 / N) := by
    calc (∑ n ∈ T_b, b n ^ 2)
        ≤ (T_b.card : ℝ) * (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / (δ * N)) := by
          rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum hpt_Tb
      _ ≤ ((K_k : ℝ) * (2 * d * c)) * (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / (δ * N)) :=
          mul_le_mul_of_nonneg_right hcard_Tb (by dsimp only [d]; positivity)
      _ = 32 * d ^ 3 * (m.totient : ℝ) ^ 2 * K_k / δ * (c ^ 3 / N) := by
          field_simp [hδ0.ne', hN0.ne']; ring
  change (Real.log (N : ℝ) / c ^ 2) * (m.totient : ℝ)⁻¹ * topWindowResidualMass δ N u_b ≤ _
  rw [hrestrict]
  calc (Real.log (N : ℝ) / c ^ 2) * (m.totient : ℝ)⁻¹ * ((∑ n ∈ T_b, b n ^ 2) / Real.log N)
      ≤ (Real.log (N : ℝ) / c ^ 2) * (m.totient : ℝ)⁻¹ *
          ((32 * d ^ 3 * (m.totient : ℝ) ^ 2 * K_k / δ * (c ^ 3 / N)) / Real.log N) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum_Tb hL0.le) (by positivity)
    _ = 32 * d ^ 3 * (m.totient : ℝ) * K_k / δ * (c / N) := by
        field_simp [hc0.ne', htot_pos.ne', hL0.ne', hδ0.ne', hN0.ne']

/-- Upward linearization subchannels (`m ≥ 1`): replacing `upwardPrimeVector φ c N v_m` on
`Ioc ⌊δ N⌋₊ N` by `(√φ(m))⁻¹ • WithLp.toLp 2 (fun n => reciprocalUpwardCoefficient φ c (linearPrimeStrip c) N m n / √(n log N))`
has vanishing `(log N / c²)` top-window `ℓ²` mass along any critical curve. -/
theorem tendsto_topWindow_upward_linearization {m : ℕ} (hm : 1 ≤ m)
    {δ : ℝ} (hδ0 : 0 < δ)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (upwardPrimeVector tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector m N) -
          (Real.sqrt (m.totient : ℝ))⁻¹ • WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
            reciprocalUpwardCoefficient tiltedUnitSpline (c N) (linearPrimeStrip (c N)) N m idx.1 /
              (Real.sqrt idx.1 * Real.sqrt (Real.log N)))))
      atTop (𝓝 0) := by
  have hm0 : 0 < m := by omega
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  obtain ⟨Ca, hCa, ha⟩ := exists_logarithmicUpward_uniform_conductor_harmonic_bound hφ hsupp hM
  let d : ℝ := Real.exp 1 + 2
  let K_k : ℕ := ⌊2 / δ⌋₊
  have hl_ua := criticalCurve_pow_log_div_natCast hc hR hcrit 8 3
  have hl_ub := criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  simp only [pow_one, pow_zero, mul_one] at hl_ub
  have hlim := (hl_ua.const_mul (2 * Ca * d ^ 6 * m.totient)).add
    (hl_ub.const_mul (64 * d ^ 3 * m.totient * K_k / δ))
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) ?_ hlim
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hc2N_ev : ∀ᶠ N : ℕ in atTop, 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ N ∧
      2 * (d * c N) + 1 < δ * N := by
    have l1 := criticalCurve_pow_log_div_natCast hc hR hcrit 2 0
    simp only [pow_zero, mul_one] at l1
    have e1 := (l1.const_mul (4 * (Real.exp 1 + 3) ^ 2)).eventually (by
      rw [mul_zero]; exact gt_mem_nhds zero_lt_one)
    have e2 := ((hl_ub.const_mul (2 * d)).add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_natCast_atTop_atTop)).eventually (by
      rw [mul_zero, add_zero]; exact gt_mem_nhds hδ0)
    filter_upwards [e1, e2, eventually_ge_atTop 1] with N h1 h2 hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    refine ⟨(div_le_one hN0).mp (by linarith only [h1, (by field_simp [hN0.ne'] :
      4 * (Real.exp 1 + 3) ^ 2 * (c N ^ 2 / N) = 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 / N)]), ?_⟩
    have hrew : 2 * d * (c N / N) + 1 / (N : ℝ) = (2 * (d * c N) + 1) / N := by field_simp [hN0.ne']
    rw [hrew, div_lt_iff₀ hN0] at h2
    exact h2
  filter_upwards [hc2N_ev, hlog] with N ⟨hlarge, h2dN⟩ hL1
  have hc1 := hc N
  have hc0 : 0 < c N := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hc_sq : c N ≤ c N ^ 2 := by nlinarith only [hc1]
  have he1 : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : 0 ≤ Real.exp 1 ^ 2 := sq_nonneg _
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 := by
      nlinarith only [hc1, hc_sq, he1, he2, sq_nonneg (c N * Real.exp 1)]
    exact_mod_cast this.trans hlarge
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set B := linearPrimeStrip (c N)
  have hB_le : (B : ℝ) ≤ (Real.exp 1 + 1) * c N := linearPrimeStrip_le hc1
  have hB1 : (B : ℝ) + 1 ≤ d * c N := by dsimp only [d]; linarith only [hB_le, hc1]
  have hBN : B ≤ N := by
    have : (B : ℝ) ≤ N := by
      have hce : c N * Real.exp 1 ≤ c N ^ 2 * Real.exp 1 :=
        mul_le_mul_of_nonneg_right hc_sq he1.le
      have : d * c N ≤ 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 := by
        dsimp only [d]
        nlinarith only [hc1, hc_sq, he1, he2, hce]
      linarith only [hB1, this, hlarge]
    exact_mod_cast this
  have hwidth : c N / N ≤ 1 / 2 := (div_le_iff₀ hN0).mpr (by
    have : 2 * c N ≤ 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 := by
      nlinarith only [hc1, hc_sq, he1, he2]
    linarith only [this, hlarge])
  have hcN : c N ≤ N := by linarith only [(div_le_iff₀ hN0).mp hwidth, hc0]
  have hkernel : 2 * ((Real.exp 1 + 3) * c N) * (B : ℝ) ≤ N := by
    have h1 : (B : ℝ) ≤ (Real.exp 1 + 3) * c N := by linarith only [hB_le, hc1]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * ((Real.exp 1 + 3) * c N))
    nlinarith only [h2, hlarge]
  let a : ℕ → ℝ := fun n =>
    (logarithmicUpwardCoefficient tiltedUnitSpline (c N) B N m n -
      linearizedUpwardCoefficient tiltedUnitSpline (c N) B N m n) / Real.sqrt n
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient tiltedUnitSpline (c N) B N m n -
      reciprocalUpwardCoefficient tiltedUnitSpline (c N) B N m n) / Real.sqrt n
  let u_a : EuclideanSpace ℝ (PrimeHorizonIndex N) := WithLp.toLp 2 (fun n => a n / Real.sqrt (Real.log N))
  let u_b : EuclideanSpace ℝ (PrimeHorizonIndex N) := WithLp.toLp 2 (fun n => b n / Real.sqrt (Real.log N))
  have hvec_eq : upwardPrimeVector tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector m N) -
      (Real.sqrt (m.totient : ℝ))⁻¹ • WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
        reciprocalUpwardCoefficient tiltedUnitSpline (c N) B N m idx.1 /
          (Real.sqrt idx.1 * Real.sqrt (Real.log N))) =
      (Real.sqrt (m.totient : ℝ))⁻¹ • (u_a + u_b) := by
    have hup : upwardPrimeVector tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector m N) =
        shellCorrection tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N +
          (Real.sqrt (m.totient : ℝ))⁻¹ • normalizedUpwardPrimeResidual tiltedUnitSpline (c N) N m := by
      have h := upwardPrimeVector_ramanujan_residual_eq tiltedUnitSpline (c N) N hm0
      exact eq_add_of_sub_eq' h
    rw [hup]
    ext idx
    have hn : idx.1 ∈ Icc 1 N := idx.2
    have hsqrt : Real.sqrt (idx.1 : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < idx.1)).ne'
    have hu : upwardPrimeRow (atomDilate tiltedUnitSpline (c N / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) idx.1 /
          (∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) =
        logarithmicUpwardCoefficient tiltedUnitSpline (c N) B N m idx.1 / Real.sqrt idx.1 :=
      (eq_div_iff hsqrt).mpr (by
        simpa only [mul_comm] using
          sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width hsupp hc0 hn
            (hwidth.trans (by norm_num)) m)
    change shellCorrection tiltedUnitSpline (c N) m *
        ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m idx.1 / Real.sqrt idx.1)) +
      (Real.sqrt (m.totient : ℝ))⁻¹ *
        (actualUpwardRowError tiltedUnitSpline (c N) N m idx.1 / Real.sqrt (Real.log N)) -
      (Real.sqrt (m.totient : ℝ))⁻¹ *
        (reciprocalUpwardCoefficient tiltedUnitSpline (c N) B N m idx.1 /
          (Real.sqrt idx.1 * Real.sqrt (Real.log N))) =
      (Real.sqrt (m.totient : ℝ))⁻¹ * (a idx.1 / Real.sqrt (Real.log N) + b idx.1 / Real.sqrt (Real.log N))
    rw [actualUpwardRowError, hu, normalizedRamanujanMode,
      TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hm0]
    dsimp only [a, b]
    have hstot_ne : Real.sqrt (m.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr htot_pos).ne'
    field_simp [hstot_ne, hsqrt, (Real.sqrt_pos.mpr hL0).ne']; ring
  rw [hvec_eq, topWindowResidualMass_smul, inv_pow, Real.sq_sqrt htot_pos.le]
  have hua_le : (Real.log (N : ℝ) / c N ^ 2) * (m.totient : ℝ)⁻¹ * topWindowResidualMass δ N u_a ≤
      Ca * d ^ 6 * (m.totient : ℝ) * (c N ^ 8 * Real.log N ^ 3 / N) := by
    have hN_sq : (N : ℝ) ≤ (N : ℝ) ^ 2 :=
      le_self_pow₀ (by exact_mod_cast hN1 : (1 : ℝ) ≤ N) (by norm_num)
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (B : ℝ) + 1) hB1 6
    have hb := (ha m N hN1 hL1 (c N) hc1 (hwidth.trans (by norm_num)) B hBN hkernel).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ Ca * (m.totient : ℝ) ^ 2 * c N ^ 4))
        (sq_nonneg _))
    have hua_sq : ‖u_a‖ ^ 2 = (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N := by
      rw [EuclideanSpace.norm_sq_eq]
      change (∑ n : PrimeHorizonIndex N, ‖a n / Real.sqrt (Real.log N)‖ ^ 2) = _
      simp only [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hL0.le]
      rw [← sum_div, ← sum_coe_sort (Icc 1 N)]
    calc (Real.log (N : ℝ) / c N ^ 2) * (m.totient : ℝ)⁻¹ * topWindowResidualMass δ N u_a
        ≤ (Real.log (N : ℝ) / c N ^ 2) * (m.totient : ℝ)⁻¹ * ‖u_a‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (topWindowResidualMass_le_norm_sq δ N u_a) (by positivity)
      _ ≤ (Real.log (N : ℝ) / c N ^ 2) * (m.totient : ℝ)⁻¹ *
            (Ca * (m.totient : ℝ) ^ 2 * c N ^ 4 * (d * c N) ^ 6 * (Real.log N / N) ^ 2) :=
          mul_le_mul_of_nonneg_left (hua_sq.le.trans hb) (by positivity)
      _ = Ca * d ^ 6 * (m.totient : ℝ) * (c N ^ 8 * Real.log N ^ 3 / N ^ 2) := by
          field_simp [hc0.ne', htot_pos.ne', hN0.ne']
      _ ≤ Ca * d ^ 6 * (m.totient : ℝ) * (c N ^ 8 * Real.log N ^ 3 / N) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (by positivity) hN0 hN_sq)
            (by dsimp only [d]; positivity)
  have hub_le : (Real.log (N : ℝ) / c N ^ 2) * (m.totient : ℝ)⁻¹ * topWindowResidualMass δ N u_b ≤
      32 * d ^ 3 * (m.totient : ℝ) * K_k / δ * (c N / N) :=
    upward_reciprocal_topWindow_le hm hδ0 hc1 hcN hN1 hL1 hBN h2dN
  calc (Real.log (N : ℝ) / c N ^ 2) * ((m.totient : ℝ)⁻¹ * topWindowResidualMass δ N (u_a + u_b))
      = (Real.log (N : ℝ) / c N ^ 2) * (m.totient : ℝ)⁻¹ * topWindowResidualMass δ N (u_a + u_b) := by ring
    _ ≤ (Real.log (N : ℝ) / c N ^ 2) * (m.totient : ℝ)⁻¹ *
          (2 * topWindowResidualMass δ N u_a + 2 * topWindowResidualMass δ N u_b) :=
        mul_le_mul_of_nonneg_left (topWindowResidualMass_add_le δ N u_a u_b) (by positivity)
    _ = 2 * ((Real.log (N : ℝ) / c N ^ 2) * (m.totient : ℝ)⁻¹ * topWindowResidualMass δ N u_a) +
          2 * ((Real.log (N : ℝ) / c N ^ 2) * (m.totient : ℝ)⁻¹ * topWindowResidualMass δ N u_b) := by ring
    _ ≤ 2 * (Ca * d ^ 6 * (m.totient : ℝ) * (c N ^ 8 * Real.log N ^ 3 / N)) +
          2 * (32 * d ^ 3 * (m.totient : ℝ) * K_k / δ * (c N / N)) :=
        add_le_add (mul_le_mul_of_nonneg_left hua_le zero_le_two)
          (mul_le_mul_of_nonneg_left hub_le zero_le_two)
    _ = _ := by ring

/-- Subchannel 3e (`m ≥ 2`): Channel 8 (`upwardPrimeVector - shellCorrection • v_m`) vanishes in
`(log N / c²) * topWindowResidualMass` along any critical curve. -/
private theorem tendsto_topWindow_upward_nonpolar {m : ℕ} (hm2 : 2 ≤ m)
    {δ : ℝ} (hδ0 : 0 < δ)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (upwardPrimeVector tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector m N) -
          shellCorrection tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N))
      atTop (𝓝 0) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : 0 < m := by omega
  have hm_ne1 : m ≠ 1 := by omega
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  obtain ⟨K_lip, hlip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hGL : ∀ x y : ℝ, |shellAutocorr tiltedUnitSpline x - shellAutocorr tiltedUnitSpline y| ≤
      (K_lip : ℝ) * |x - y| := fun x y => by
    have hd := hlip.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at hd
  let C_mod : ℝ := 4 * m * m.totient * (1 + 2 * (K_lip : ℝ) / ((∫ u, tiltedUnitSpline u ^ 2) * δ))
  let C_rec : ℝ := (⌊1 / δ⌋₊ : ℝ) * C_mod
  have hlin := tendsto_topWindow_upward_linearization hm1 hδ0 hc hR hcrit
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hinv_c2 : Tendsto (fun N : ℕ => 1 / c N ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hcinf)
  have hsc_div : Tendsto (fun N : ℕ => (shellCorrection tiltedUnitSpline (c N) m / c N) ^ 2)
      atTop (𝓝 0) := by
    have h := (tendsto_shellCorrection_div_overlap hφ hsupp hM hm0).comp hcinf
    rw [if_neg hm_ne1] at h
    simpa only [Function.comp_def, zero_pow (by decide : 2 ≠ 0)] using h.pow 2
  have hlim := ((hlin.const_mul 4).add
    (hinv_c2.const_mul (4 * (m.totient : ℝ)⁻¹ * C_rec ^ 2 / δ))).add
    (hsc_div.const_mul (4 * m / δ))
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) ?_ hlim
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_below_overlap_pair_admissible hc hR hcrit, hlog] with N hadm hL1
  obtain ⟨_, _, _, hc4N⟩ := hadm 1 1 (by simpa using hc N) (by simpa using hc N)
  have hc1 := hc N
  have hc0 : 0 < c N := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hcN : c N ≤ N := (le_self_pow₀ hc1 (by norm_num : 4 ≠ 0)).trans hc4N
  have hN1 : 1 ≤ N := by exact_mod_cast hc1.trans hcN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set B := linearPrimeStrip (c N)
  have hB_ceil : ⌈c N⌉₊ ≤ B := by
    apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_left (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)) hc0.le
    exact (by simpa only [mul_one] using h : c N ≤ c N * Real.exp 1).trans (Nat.le_ceil _)
  let v_m := normalizedRamanujanHorizonVector m N
  let v_rec : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    (Real.sqrt (m.totient : ℝ))⁻¹ • WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
      reciprocalUpwardCoefficient tiltedUnitSpline (c N) B N m idx.1 /
        (Real.sqrt idx.1 * Real.sqrt (Real.log N)))
  let w₁ := upwardPrimeVector tiltedUnitSpline (c N) N v_m - v_rec
  let w₂ := v_rec
  let w₃ := -(shellCorrection tiltedUnitSpline (c N) m • v_m)
  have hsplit : upwardPrimeVector tiltedUnitSpline (c N) N v_m -
      shellCorrection tiltedUnitSpline (c N) m • v_m = (w₁ + w₂) + w₃ := by
    dsimp only [w₁, w₂, w₃]; abel
  have hrec_le : (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N v_rec ≤
      (m.totient : ℝ)⁻¹ * C_rec ^ 2 / δ * (1 / c N ^ 2) := by
    have hH1 : 1 ≤ ⌈c N⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hc0).ne'
    have hceil_le : (⌈c N⌉₊ : ℝ) ≤ 2 * c N := by
      have := (Nat.ceil_lt_add_one hc0.le).le; linarith only [this, hc1]
    have hpt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        primeHorizonExtension v_rec n ^ 2 ≤
          (m.totient : ℝ)⁻¹ * C_rec ^ 2 / Real.log N * (1 / (n : ℝ)) := fun n hn_top => by
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn_top).1; omega
      have hnN : n ≤ N := (mem_Ioc.mp hn_top).2
      have hnI : n ∈ Icc 1 N := mem_Icc.mpr ⟨hn1, hnN⟩
      have hn_gt : δ * N < n := (Nat.lt_floor_add_one (δ * N)).trans_le
        (by exact_mod_cast (Nat.succ_le_of_lt (mem_Ioc.mp hn_top).1))
      have hn0 : (0 : ℝ) < n := (mul_pos hδ0 hN0).trans hn_gt
      have hcoef : |reciprocalUpwardCoefficient tiltedUnitSpline (c N) B N m n| ≤ C_rec := by
        rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc0 hB_ceil N m n hn1,
          affinePrimeShellCorrection_symm_eq_sum_upwardShellModel hφ hsupp hc0 hm1 hnI]
        have hk_term : ∀ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊,
            |((Λ k : ℝ) / k) * upwardShellModel tiltedUnitSpline (c N) N m ⌈c N⌉₊ (k * n)| ≤
              ((Λ k : ℝ) / k) * C_mod := fun k hk => by
          have hk1 := (mem_Icc.mp hk).1
          have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
          have hkn_ge : δ * N ≤ (k * n : ℕ) := by
            have h1 : (1 : ℝ) * n ≤ (k : ℝ) * n :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hk1) hn0.le
            push_cast; linarith only [hn_gt, h1]
          have hcp_ge : δ * c N ≤ c N * (k * n : ℕ) / N := by
            rw [le_div_iff₀ hN0]
            have := mul_le_mul_of_nonneg_left hkn_ge hc0.le
            linarith only [this]
          have hrat : (K_lip : ℝ) * ⌈c N⌉₊ /
              ((∫ u, tiltedUnitSpline u ^ 2) * (c N * (k * n : ℕ) / N)) ≤
              2 * (K_lip : ℝ) / ((∫ u, tiltedUnitSpline u ^ 2) * δ) := by
            have hnum : (K_lip : ℝ) * ⌈c N⌉₊ ≤ (K_lip : ℝ) * (2 * c N) :=
              mul_le_mul_of_nonneg_left hceil_le (NNReal.coe_nonneg K_lip)
            have hden : (∫ u, tiltedUnitSpline u ^ 2) * (δ * c N) ≤
                (∫ u, tiltedUnitSpline u ^ 2) * (c N * (k * n : ℕ) / N) :=
              mul_le_mul_of_nonneg_left hcp_ge hM.le
            calc _ ≤ (K_lip : ℝ) * (2 * c N) / ((∫ u, tiltedUnitSpline u ^ 2) * (δ * c N)) :=
                  (div_le_div_of_nonneg_right hnum (by positivity)).trans
                    (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
              _ = 2 * (K_lip : ℝ) / ((∫ u, tiltedUnitSpline u ^ 2) * δ) := by
                  field_simp [hc0.ne', hM.ne', hδ0.ne']
          have hmod : |upwardShellModel tiltedUnitSpline (c N) N m ⌈c N⌉₊ (k * n)| ≤ C_mod := by
            refine (abs_upwardShellModel_nonpolar_le hφ hsupp hM hc0 (NNReal.coe_nonneg K_lip)
              hGL hN1 hH1 (Nat.mul_pos hk1 hn1) hm2).trans ?_
            dsimp only [C_mod]
            exact mul_le_mul_of_nonneg_left (by linarith only [hrat]) (by positivity)
          rw [abs_mul, abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hk0.le)]
          exact mul_le_mul_of_nonneg_left hmod
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hk0.le)
        have hfl_le : ⌊(N : ℝ) / n⌋₊ ≤ ⌊1 / δ⌋₊ :=
          Nat.floor_mono ((div_le_div_iff₀ hn0 hδ0).mpr (by linarith only [hn_gt]))
        have hsum_lam : (∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (Λ k : ℝ) / k) ≤ ⌊1 / δ⌋₊ := by
          calc (∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (Λ k : ℝ) / k)
              ≤ ∑ _k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (1 : ℝ) := by
                refine sum_le_sum fun k hk => ?_
                have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
                rw [div_le_one hk0]
                linarith [ArithmeticFunction.vonMangoldt_le_log (n := k),
                  Real.log_le_sub_one_of_pos hk0]
            _ = (⌊(N : ℝ) / n⌋₊ : ℝ) := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
            _ ≤ ⌊1 / δ⌋₊ := by exact_mod_cast hfl_le
        calc _ ≤ ∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, ((Λ k : ℝ) / k) * C_mod :=
              (abs_sum_le_sum_abs _ _).trans (sum_le_sum hk_term)
          _ = (∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (Λ k : ℝ) / k) * C_mod := (sum_mul _ _ _).symm
          _ ≤ (⌊1 / δ⌋₊ : ℝ) * C_mod :=
              mul_le_mul_of_nonneg_right hsum_lam (by dsimp only [C_mod]; positivity)
      let idx : PrimeHorizonIndex N := ⟨n, hnI⟩
      have hext : primeHorizonExtension v_rec n =
          (Real.sqrt (m.totient : ℝ))⁻¹ *
            (reciprocalUpwardCoefficient tiltedUnitSpline (c N) B N m n /
              (Real.sqrt n * Real.sqrt (Real.log N))) := by
        change primeHorizonExtension v_rec idx.1 = _
        rw [primeHorizonExtension_coe]; rfl
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hcoef 2
      rw [sq_abs] at hsq
      rw [hext, mul_pow, inv_pow, Real.sq_sqrt htot_pos.le, div_pow, mul_pow,
        Real.sq_sqrt hn0.le, Real.sq_sqrt hL0.le]
      calc (m.totient : ℝ)⁻¹ * (reciprocalUpwardCoefficient tiltedUnitSpline (c N) B N m n ^ 2 /
              (n * Real.log N))
          ≤ (m.totient : ℝ)⁻¹ * (C_rec ^ 2 / (n * Real.log N)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq (by positivity)) (by positivity)
        _ = (m.totient : ℝ)⁻¹ * C_rec ^ 2 / Real.log N * (1 / (n : ℝ)) := by ring
    have hmass : topWindowResidualMass δ N v_rec ≤ (m.totient : ℝ)⁻¹ * C_rec ^ 2 / (δ * Real.log N) := by
      unfold topWindowResidualMass
      calc _ ≤ ((m.totient : ℝ)⁻¹ * C_rec ^ 2 / Real.log N) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, 1 / (n : ℝ) :=
            (sum_le_sum hpt).trans_eq (mul_sum _ _ _).symm
        _ ≤ ((m.totient : ℝ)⁻¹ * C_rec ^ 2 / Real.log N) * (1 / δ) :=
            mul_le_mul_of_nonneg_left (sum_topWindow_inv_le hδ0 hN1) (by positivity)
        _ = (m.totient : ℝ)⁻¹ * C_rec ^ 2 / (δ * Real.log N) := by ring
    exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq
      (by field_simp [hc0.ne', hδ0.ne', hL0.ne'])
  have hsc_le : (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N w₃ ≤
      (m : ℝ) / δ * (shellCorrection tiltedUnitSpline (c N) m / c N) ^ 2 := by
    dsimp only [w₃]
    rw [topWindowResidualMass_neg, topWindowResidualMass_smul]
    have hvm_pt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        primeHorizonExtension v_m n ^ 2 ≤ (m : ℝ) / Real.log N * (1 / (n : ℝ)) := fun n hn_top => by
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn_top).1; omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, (mem_Ioc.mp hn_top).2⟩⟩
      have hext : primeHorizonExtension v_m n =
          normalizedRamanujanMode m n / Real.sqrt n / Real.sqrt (Real.log N) := by
        change primeHorizonExtension v_m idx.1 = _
        rw [primeHorizonExtension_coe]
        exact (div_eq_inv_mul _ _).symm
      have hmode2 : normalizedRamanujanMode m n ^ 2 ≤ m := by
        have hsq := pow_le_pow_left₀ (abs_nonneg _) (abs_mode_le_sqrt_conductor hm0 n) 2
        rwa [sq_abs, Real.sq_sqrt (Nat.cast_nonneg m)] at hsq
      rw [hext, div_pow, div_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hL0.le]
      calc normalizedRamanujanMode m n ^ 2 / n / Real.log N
          ≤ (m : ℝ) / n / Real.log N :=
            div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmode2 hn0.le) hL0.le
        _ = (m : ℝ) / Real.log N * (1 / (n : ℝ)) := by ring
    have hvm_mass : topWindowResidualMass δ N v_m ≤ (m : ℝ) / (δ * Real.log N) := by
      unfold topWindowResidualMass
      calc _ ≤ ((m : ℝ) / Real.log N) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, 1 / (n : ℝ) :=
            (sum_le_sum hvm_pt).trans_eq (mul_sum _ _ _).symm
        _ ≤ ((m : ℝ) / Real.log N) * (1 / δ) :=
            mul_le_mul_of_nonneg_left (sum_topWindow_inv_le hδ0 hN1) (by positivity)
        _ = (m : ℝ) / (δ * Real.log N) := by ring
    calc (Real.log (N : ℝ) / c N ^ 2) *
          (shellCorrection tiltedUnitSpline (c N) m ^ 2 * topWindowResidualMass δ N v_m)
        ≤ (Real.log (N : ℝ) / c N ^ 2) *
            (shellCorrection tiltedUnitSpline (c N) m ^ 2 * ((m : ℝ) / (δ * Real.log N))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvm_mass (sq_nonneg _)) (by positivity)
      _ = (m : ℝ) / δ * (shellCorrection tiltedUnitSpline (c N) m / c N) ^ 2 := by
          field_simp [hc0.ne', hδ0.ne', hL0.ne']
  rw [hsplit]
  have ht1 := topWindowResidualMass_add_le δ N (w₁ + w₂) w₃
  have ht2 := topWindowResidualMass_add_le δ N w₁ w₂
  have hn3 := topWindowResidualMass_nonneg δ N w₃
  have h4 : topWindowResidualMass δ N ((w₁ + w₂) + w₃) ≤
      4 * topWindowResidualMass δ N w₁ + 4 * topWindowResidualMass δ N w₂ +
        4 * topWindowResidualMass δ N w₃ := by linarith only [ht1, ht2, hn3]
  calc (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N ((w₁ + w₂) + w₃)
      ≤ (Real.log (N : ℝ) / c N ^ 2) *
          (4 * topWindowResidualMass δ N w₁ + 4 * topWindowResidualMass δ N w₂ +
            4 * topWindowResidualMass δ N w₃) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 4 * ((Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N w₁) +
          4 * ((Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N v_rec) +
          4 * ((Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N w₃) := by
        dsimp only [w₂]; ring
    _ ≤ 4 * ((Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N w₁) +
          4 * ((m.totient : ℝ)⁻¹ * C_rec ^ 2 / δ * (1 / c N ^ 2)) +
          4 * ((m : ℝ) / δ * (shellCorrection tiltedUnitSpline (c N) m / c N) ^ 2) :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hrec_le (by norm_num)))
          (mul_le_mul_of_nonneg_left hsc_le (by norm_num))
    _ = _ := by dsimp only [w₁, v_m, v_rec, B]; ring

/-- **Curvewise nonpolar top-window `ℓ²` row cancellation (`m ≥ 2`).**
Along every critical curve `c N ^ 8 / log N → R > 0`, for any `m ≥ 2` and `0 < δ < 1`,
`(log N / c N ^ 2) * topWindowResidualMass δ N (conductorResidualVector (c N) m N) → 0`. -/
theorem tendsto_nonpolar_topWindow_norm_sq {m : ℕ} (hm2 : 2 ≤ m)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N (conductorResidualVector (c N) m N)) atTop (𝓝 0) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : 0 < m := by omega
  have hm_ne1 : m ≠ 1 := by omega
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  have l1 := tendsto_topWindow_bulk_subchannels hm1 δ hc hR hcrit
  have l2 := tendsto_topWindow_nearGamma_nonpolar hm2 hδ0 hδ1 hc hR hcrit
  have l3 := tendsto_topWindow_center_and_jetPole_nonpolar hm2 hδ0 hc hR hcrit
  have l4 := tendsto_topWindow_separatedCross_nonpolar hm2 hδ0 hc hR hcrit
  have l5 := tendsto_topWindow_upward_nonpolar hm2 hδ0 hc hR hcrit
  have hlim := ((((l1.const_mul 8).add (l2.const_mul 8)).add (l3.const_mul 8)).add
    (l4.const_mul 8)).add (l5.const_mul 8)
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN1
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  let v_m := normalizedRamanujanHorizonVector m N
  let v_pole : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
      (Λ m / Real.sqrt (m.totient : ℝ)) * nearPoleRow tiltedUnitSpline (c N) N idx.1 /
        Real.sqrt (Real.log N))
  let v₁ := -(Matrix.toEuclideanLin (fullPrimeMatrix N) v_m -
      (Real.log N - ramanujanAdjunctionEnergy m) • v_m) +
    completeWeilSelfError tiltedUnitSpline (c N) N • v_m +
    Matrix.toEuclideanLin (fullWeilPoleErrorMatrix tiltedUnitSpline (c N) N) v_m -
    (Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector tiltedUnitSpline (c N) N m
  let v₂ : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
      nearGammaNonpolarRemRow tiltedUnitSpline (c N) N m idx.1 / Real.sqrt (Real.log N))
  let v₃ := Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline (c N)) N) v_m +
    nearCenterVector tiltedUnitSpline (c N) N m + v_pole
  let v₄ := -Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline (c N) N) v_m
  let v₅ := -(upwardPrimeVector tiltedUnitSpline (c N) N v_m -
    shellCorrection tiltedUnitSpline (c N) m • v_m)
  have hng_split : (Real.sqrt (m.totient : ℝ))⁻¹ •
      normalizedNearGammaDownwardVector tiltedUnitSpline (c N) N m = v₂ + v_pole := by
    ext idx
    change (Real.sqrt (m.totient : ℝ))⁻¹ *
      (nearGammaDownwardRow tiltedUnitSpline (c N) N m idx.1 / Real.sqrt (Real.log N)) =
      nearGammaNonpolarRemRow tiltedUnitSpline (c N) N m idx.1 / Real.sqrt (Real.log N) +
        (Λ m / Real.sqrt (m.totient : ℝ)) * nearPoleRow tiltedUnitSpline (c N) N idx.1 /
          Real.sqrt (Real.log N)
    unfold nearGammaNonpolarRemRow; ring
  have hdecomp : conductorResidualVector (c N) m N = v₁ + v₂ + v₃ + v₄ + v₅ := by
    unfold conductorResidualVector
    rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN1 hm0,
      if_neg hm_ne1, zero_smul, sub_zero,
      normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc0 N m,
      smul_sub, hng_split]
    dsimp only [v_m, v₁, v₃, v₄, v₅]
    abel
  rw [hdecomp]
  have h5 := topWindowResidualMass_five_le δ N v₁ v₂ v₃ v₄ v₅
  rw [show topWindowResidualMass δ N v₄ = topWindowResidualMass δ N
      (Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline (c N) N) v_m) from
      topWindowResidualMass_neg δ N _,
    show topWindowResidualMass δ N v₅ = topWindowResidualMass δ N
      (upwardPrimeVector tiltedUnitSpline (c N) N v_m -
        shellCorrection tiltedUnitSpline (c N) m • v_m) from
      topWindowResidualMass_neg δ N _] at h5
  exact (mul_le_mul_of_nonneg_left h5 (by positivity)).trans_eq (by ring)

/-- **Uniform nonpolar top-window `ℓ²` row cancellation across any positive critical band.**
For every `m ≥ 2`, `0 < δ < 1`, `0 < R₀ ≤ R_max`, and `η > 0`, eventually in `N` and uniformly
across all `1 ≤ c` with `R₀ * log N ≤ c ^ 8 ≤ R_max * log N`:
`(log N / c ^ 2) * topWindowResidualMass δ N (conductorResidualVector c m N) ≤ η`. -/
theorem eventually_uniform_nonpolar_topWindow_norm_sq {m : ℕ} (hm2 : 2 ≤ m)
    {δ R₀ R_max η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hR₀ : 0 < R₀) (hR_le : R₀ ≤ R_max) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      R₀ * Real.log (N : ℝ) ≤ c ^ 8 → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
      (Real.log (N : ℝ) / c ^ 2) *
        topWindowResidualMass δ N (conductorResidualVector c m N) ≤ η :=
  eventually_uniform_critical_band_of_curve hR₀ hR_le fun _R hR _c hc hcrit =>
    ((tendsto_nonpolar_topWindow_norm_sq hm2 hδ0 hδ1 hc (hR₀.trans_le hR.1) hcrit).eventually
      (gt_mem_nhds hη)).mono fun _ h => h.le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory


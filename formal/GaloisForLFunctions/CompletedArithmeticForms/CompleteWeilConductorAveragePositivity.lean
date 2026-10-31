import GaloisForLFunctions.CompletedArithmeticForms.CompleteWeilResidualLevelOfDistribution
import GaloisForLFunctions.ArithmeticIntersectionTheory.ThePositiveSquaresOfTheTorsionFormLiveBelowFourFifths

/-!
# Conductor-Average Positivity and Sublinear Negative Index of the Complete Weil Form

Unconditional consequences of the Bombieri–Vinogradov complete-Weil residual level of distribution
(`tendsto_completeWeil_residual_levelOfDistribution`) across all Ramanujan conductors
`1 ≤ m ≤ M = ⌊N^θ⌋₊` for every `0 < θ < 1 / 2` and every overlap schedule `c : ℕ → ℝ` with
`∀ᶠ N, 1 ≤ c N` and `c N ^ 2 / log N → 0` (covering the entire RH-complete regime
`c N = 2 (log N)^α`, `1 / 4 < α < 1 / 2`):

* **Diverging positive conductor average (`tendsto_completeWeil_conductorAverage_atTop`,
  `eventually_completeWeil_conductorAverage_pos`).** Every shell-completed conductor energy is
  nonnegative (`completedConductorEnergy_nonneg`), the top dyadic half `⌊M / 2⌋₊ < m ≤ M` carries
  completed energy `(θ / 2) log N` and norm square `‖v_m‖² ≥ 1 - 2θ`, and the residual Rayleigh
  sum is `o(M log N)`, forcing
  ```
  (1 / ⌊N^θ⌋₊) ∑_{m=1}^{⌊N^θ⌋₊} completeWeilEnergy φ (c N) N v_m → +∞.
  ```
* **Almost-all positive conductor census (`tendsto_nonpositive_conductor_fraction_zero`).** The
  proportion of conductors `1 ≤ m ≤ ⌊N^θ⌋₊` on which `completeWeilEnergy φ (c N) N v_m ≤ 0`
  tends to `0`.
* **Sublinear negative index on the conductor subspace
  (`tendsto_completeWeil_conductorSubspace_negIndex_div_zero`).** For any family of subspaces
  `U N ≤ conductorSubspace ⌊N^θ⌋₊ N` on which `completeWeilEnergy φ (c N) N` is nonpositive,
  `finrank ℝ (U N) / ⌊N^θ⌋₊ → 0`, i.e., `κ(W_{N, c_N}|_{V_M}) = o(M)`.
* **`tiltedUnitSpline` RH-complete specializations.** Direct specializations to
  `c N = 2 (log N)^α` (`0 < α < 1 / 2`).
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open ArithmeticIntersectionTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis

/-! ## Section 1: Conductor Rayleigh Decomposition and Subspace Frame Tools -/

/-- The complete-Weil residual vector on the `m`-th normalized Ramanujan horizon mode:
`W_{N, c} v_m - E_m(c) v_m`. -/
def completeWeilConductorResidual (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
    completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N

/-- Exact Rayleigh decomposition of `completeWeilEnergy` on a single conductor mode `v_m`. -/
theorem completeWeilEnergy_normalizedRamanujanHorizonVector_eq
    (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    completeWeilEnergy φ c N (normalizedRamanujanHorizonVector m N) =
      ⟪completeWeilConductorResidual φ c N m, normalizedRamanujanHorizonVector m N⟫ +
        completedConductorEnergy φ c m * ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  unfold completeWeilEnergy completeWeilConductorResidual
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- Individual norm-square lower bound `1 - 2θ ≤ ‖v_m‖²` for `1 ≤ m ≤ M ≤ N^θ`. -/
theorem normalizedRamanujanHorizonVector_norm_sq_ge
    {θ : ℝ} {m M N : ℕ} (hm : m ∈ Icc 1 M) (hN : 4 ≤ N) (hMN : (M : ℝ) ≤ (N : ℝ) ^ θ) :
    1 - 2 * θ ≤ ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hM1 : 1 ≤ M := (mem_Icc.mp hm).1.trans (mem_Icc.mp hm).2
  have h := ramanujanConductor_lower_riesz hM1 hN hMN (fun k => if k = m then 1 else 0)
  simpa only [ite_smul, one_smul, zero_smul, sum_ite_eq', if_pos hm, ite_pow, one_pow,
    zero_pow (by decide : 2 ≠ 0), mul_one] using h

/-- Bessel inequality along the ambient coercion of any finite `OrthonormalBasis` of `W`. -/
private theorem sum_sq_inner_orthonormalBasis_le
    {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι]
    {W : Submodule ℝ V} (b : OrthonormalBasis ι ℝ W) (x : V) :
    (∑ j : ι, ⟪x, (b j : V)⟫ ^ 2) ≤ ‖x‖ ^ 2 := by
  have hv : Orthonormal ℝ (fun j : ι => (b j : V)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← W.coe_inner, orthonormal_iff_ite.mp b.orthonormal i j]
  have hbessel := hv.sum_inner_products_le x (s := Finset.univ)
  refine le_trans (le_of_eq ?_) hbessel
  refine sum_congr rfl fun j _ => ?_
  rw [real_inner_comm x (b j : V), Real.norm_eq_abs, sq_abs]

/-- Uniform relative concentration of `completedConductorEnergy φ (c N) m` around `θ log N`
across every top conductor slice `Ioc ⌊δ * ⌊N^θ⌋₊⌋₊ ⌊N^θ⌋₊` (`0 < δ`, `0 < η`). -/
theorem eventually_abs_completedConductorEnergy_sub_theta_log_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    {c : ℕ → ℝ} (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (hc_lim : Tendsto (fun N => c N ^ 2 / Real.log N) atTop (𝓝 0))
    {δ η : ℝ} (hδ0 : 0 < δ) (hη0 : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ Ioc ⌊δ * (⌊(N : ℝ) ^ θ⌋₊ : ℝ)⌋₊ ⌊(N : ℝ) ^ θ⌋₊,
      |completedConductorEnergy φ (c N) m - θ * Real.log N| ≤ η * (θ * Real.log N) := by
  let K : ℕ := ⌈20 / η⌉₊ + 1
  have hK1 : 1 ≤ K := by dsimp only [K]; omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hK_eta : 2 / (K : ℝ) ≤ η / 10 := by
    have hceil : 20 / η < (K : ℝ) := by
      have hc := Nat.le_ceil (20 / η)
      dsimp only [K]
      push_cast
      linarith only [hc]
    rw [div_le_iff₀ hK0]
    rw [div_lt_iff₀ hη0] at hceil
    linarith only [hceil]
  let L₄ := 2 * (Real.log 4 + 4)
  have hL₄ : 0 < L₄ := by
    dsimp only [L₄]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  let B_tame := 2 * Real.log K + 2 * Real.log 4
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrpow : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ0).comp tendsto_natCast_atTop_atTop
  let L_min := max 1 (max ((5 / (η * θ)) * |Real.log (δ / 2)|)
    (max ((5 / (η * θ)) * |completeWeilSelfFinitePart φ 1|)
      ((10 / (η * θ)) * |B_tame|)))
  have hc_eps : 0 < min (η * θ / 5) (η * θ / (5 * L₄)) := by positivity
  filter_upwards [eventually_conductorCutoff_bounds hθ0 hθ, hc1,
    hc_lim.eventually (ge_mem_nhds hc_eps),
    hlog.eventually_ge_atTop L_min,
    hrpow.eventually_ge_atTop (4 / δ),
    eventually_ge_atTop 2] with N hcut hcN1 hcN_sm hLN hNθ_δ hN2
  obtain ⟨_, _, hfl_half, hfl_le, _⟩ := hcut
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN1 : 1 ≤ Real.log N := (le_max_left _ _).trans hLN
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hLN1
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN1
  have hc_le_c2 : c N ≤ c N ^ 2 := by nlinarith only [hcN1]
  let E₀ := θ * Real.log N
  have hE₀_pos : 0 < E₀ := mul_pos hθ0 hLN0
  -- Extract the log-growth thresholds from `L_min ≤ Real.log N`.
  have hLN_a : (5 / (η * θ)) * |Real.log (δ / 2)| ≤ Real.log N :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hLN
  have hLN_b : (5 / (η * θ)) * |completeWeilSelfFinitePart φ 1| ≤ Real.log N :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLN
  have hLN_c : (10 / (η * θ)) * |B_tame| ≤ Real.log N :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLN
  have hscale_5 : ∀ X : ℝ, (5 / (η * θ)) * X ≤ Real.log N → X ≤ (η / 5) * E₀ := by
    intro X hX
    have hmul := mul_le_mul_of_nonneg_left hX (show 0 ≤ (η * θ) / 5 by positivity)
    calc
      X = ((η * θ) / 5) * ((5 / (η * θ)) * X) := by field_simp [hη0.ne', hθ0.ne']
      _ ≤ ((η * θ) / 5) * Real.log N := hmul
      _ = (η / 5) * E₀ := by dsimp only [E₀]; ring
  have hscale_10 : ∀ X : ℝ, (10 / (η * θ)) * X ≤ Real.log N → X ≤ (η / 10) * E₀ := by
    intro X hX
    have hmul := mul_le_mul_of_nonneg_left hX (show 0 ≤ (η * θ) / 10 by positivity)
    calc
      X = ((η * θ) / 10) * ((10 / (η * θ)) * X) := by field_simp [hη0.ne', hθ0.ne']
      _ ≤ ((η * θ) / 10) * Real.log N := hmul
      _ = (η / 10) * E₀ := by dsimp only [E₀]; ring
  have h_piece_δ : |Real.log (δ / 2)| ≤ (η / 5) * E₀ := hscale_5 _ hLN_a
  have h_piece_self : |completeWeilSelfFinitePart φ 1| ≤ (η / 5) * E₀ := hscale_5 _ hLN_b
  have h_piece_Btame : |B_tame| ≤ (η / 10) * E₀ := hscale_10 _ hLN_c
  -- Overlap bounds on `|log (c N)|` and `L₄ * c N`.
  have hc2_div1 : c N ^ 2 / Real.log N ≤ η * θ / 5 := hcN_sm.trans (min_le_left _ _)
  have hc2_div2 : c N ^ 2 / Real.log N ≤ η * θ / (5 * L₄) := hcN_sm.trans (min_le_right _ _)
  have h_piece_logc : |Real.log (c N)| ≤ (η / 5) * E₀ := by
    have h0 : 0 ≤ Real.log (c N) := Real.log_nonneg hcN1
    have hle : Real.log (c N) ≤ c N ^ 2 :=
      ((Real.log_le_sub_one_of_pos hc0).trans (by linarith only [hc0])).trans hc_le_c2
    rw [abs_of_nonneg h0]
    have h1 := (div_le_iff₀ hLN0).mp hc2_div1
    dsimp only [E₀]
    linarith only [hle, h1]
  have h_piece_cL4 : L₄ * c N ≤ (η / 5) * E₀ := by
    have h1 := (div_le_iff₀ hLN0).mp hc2_div2
    have h2 := mul_le_mul_of_nonneg_left (hc_le_c2.trans h1) hL₄.le
    calc
      L₄ * c N ≤ L₄ * (η * θ / (5 * L₄) * Real.log N) := h2
      _ = (η / 5) * E₀ := by dsimp only [E₀]; field_simp [hL₄.ne']
  -- Now fix `m ∈ Ioc ⌊δ * M⌋₊ M`.
  intro m hm
  obtain ⟨hm_gt, hm_le⟩ := mem_Ioc.mp hm
  -- Show `2 ≤ ⌊δ * M⌋₊`, hence `3 ≤ m`, `0 < m`, and `m ≠ 1`.
  have hfl_ge2 : 2 ≤ ⌊δ * (⌊(N : ℝ) ^ θ⌋₊ : ℝ)⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    have h1 : 4 ≤ δ * (N : ℝ) ^ θ := by
      have := mul_le_mul_of_nonneg_left hNθ_δ hδ0.le
      have h4 : δ * (4 / δ) = 4 := by field_simp [hδ0.ne']
      linarith only [this, h4]
    have h2 : (δ * (N : ℝ) ^ θ) / 2 ≤ δ * (⌊(N : ℝ) ^ θ⌋₊ : ℝ) := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hfl_half hδ0.le
    linarith only [h1, h2]
  have hm0 : 0 < m := by omega
  have hm_ne1 : m ≠ 1 := by omega
  -- Exact decomposition of `completedConductorEnergy φ (c N) m - E₀` for `m ≠ 1`.
  have hdecomp : completedConductorEnergy φ (c N) m - E₀ =
      (Real.log m - E₀) + completeWeilSelfFinitePart φ 1 - Real.log (c N) +
        tameDifferent m - shellCorrection φ (c N) m := by
    rw [completedConductorEnergy_eq_sub_shellCorrection hc0 hm0, completeWeilAdjunctionEnergy,
      completeWeilSelfFinitePart_eq_at_one_sub_log φ hc0, ramanujanAdjunctionEnergy,
      if_neg hm_ne1]
    ring
  -- Bound `Real.log m - E₀`.
  have hm_ub : (m : ℝ) ≤ (N : ℝ) ^ θ :=
    (show (m : ℝ) ≤ ⌊(N : ℝ) ^ θ⌋₊ by exact_mod_cast hm_le).trans hfl_le
  have hlogm_le : Real.log m ≤ E₀ := by
    have h := Real.log_le_log (by exact_mod_cast hm0) hm_ub
    rwa [Real.log_rpow hN0] at h
  have hm_lb : (δ / 2) * (N : ℝ) ^ θ ≤ m := by
    have hgt : δ * (⌊(N : ℝ) ^ θ⌋₊ : ℝ) < m := Nat.lt_of_floor_lt hm_gt
    nlinarith only [hgt, hfl_half, hδ0]
  have hlogm_ge : -((η / 5) * E₀) ≤ Real.log m - E₀ := by
    have h := Real.log_le_log (by positivity) hm_lb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0] at h
    linarith only [h, neg_abs_le (Real.log (δ / 2)), h_piece_δ]
  have hlogm_le' : Real.log m - E₀ ≤ (η / 5) * E₀ :=
    (sub_nonpos.mpr hlogm_le).trans (by positivity)
  -- Bound `tameDifferent m` via prime-divisor splitting at `K`.
  have htame_nonneg : 0 ≤ tameDifferent m :=
    SelectiveMultiscaleArithmeticPositivity.tameDifferent_nonneg m
  have htame_le : tameDifferent m ≤ (η / 5) * E₀ := by
    have hsplit := tameDifferent_le_split hm0 hK1
    have htail : 2 * Real.log m / K ≤ (η / 10) * E₀ := by
      calc
        2 * Real.log m / K = (2 / (K : ℝ)) * Real.log m := by ring
        _ ≤ (2 / (K : ℝ)) * E₀ :=
          mul_le_mul_of_nonneg_left hlogm_le (by positivity)
        _ ≤ (η / 10) * E₀ := mul_le_mul_of_nonneg_right hK_eta hE₀_pos.le
    have hB : B_tame ≤ (η / 10) * E₀ := (le_abs_self B_tame).trans h_piece_Btame
    dsimp only [B_tame] at hB
    linarith only [hsplit, hB, htail]
  -- Bound `|shellCorrection φ (c N) m|`.
  have hshell : |shellCorrection φ (c N) m| ≤ (η / 5) * E₀ :=
    (abs_shellCorrection_le_linear hφ hsupp hM_int hm0 hc0).trans h_piece_cL4
  -- Combine all five terms.
  change |completedConductorEnergy φ (c N) m - E₀| ≤ η * E₀
  rw [hdecomp, abs_le]
  obtain ⟨hs1, hs2⟩ := abs_le.mp h_piece_self
  obtain ⟨hl1, hl2⟩ := abs_le.mp h_piece_logc
  obtain ⟨hsh1, hsh2⟩ := abs_le.mp hshell
  have h5eq : 5 * ((η / 5) * E₀) = η * E₀ := by ring
  have hηE_pos : 0 < (η / 5) * E₀ := by positivity
  exact ⟨by linarith only [hlogm_ge, hs1, hl2, htame_nonneg, hsh2, h5eq, hηE_pos],
    by linarith only [hlogm_le', hs2, hl1, htame_le, hsh1, h5eq]⟩

/-! ## Section 2: Unconditional Conductor-Average Positivity, Census, and Negative-Index Laws -/

/-- **Unconditional Conductor-Average Divergence at RH-Complete Overlap.**
For every `C²` profile `φ` supported in `[0, 1]` with `0 < ∫ φ²`, every Bombieri–Vinogradov
exponent `0 < θ < 1 / 2`, and every overlap schedule `c : ℕ → ℝ` with `∀ᶠ N, 1 ≤ c N` and
`c N ^ 2 / log N → 0`, the uniform conductor average of `completeWeilEnergy` across
`1 ≤ m ≤ ⌊N^θ⌋₊` diverges to `+∞`:
```
(1 / ⌊N^θ⌋₊) ∑_{m=1}^{⌊N^θ⌋₊} completeWeilEnergy φ (c N) N v_m → +∞.
```
-/
theorem tendsto_completeWeil_conductorAverage_atTop {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    {c : ℕ → ℝ} (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (hc_lim : Tendsto (fun N => c N ^ 2 / Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (1 / (⌊(N : ℝ) ^ θ⌋₊ : ℝ)) *
        ∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
          completeWeilEnergy φ (c N) N (normalizedRamanujanHorizonVector m N))
      atTop atTop := by
  let c₀ := (1 - 2 * θ) * θ / 8
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    have : 0 < 1 - 2 * θ := by linarith only [hθ]
    positivity
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmaj : Tendsto (fun N : ℕ => c₀ * Real.log (N : ℝ)) atTop atTop :=
    hlog.const_mul_atTop hc₀
  have hres := tendsto_completeWeil_residual_div_mul_log_sq_zero hφ hsupp hM_int hθ0 hθ hc1 hc_lim
  have heps : 0 < c₀ ^ 2 / 6 := by positivity
  refine tendsto_atTop_mono' atTop ?_ hmaj
  filter_upwards [eventually_conductorCutoff_bounds hθ0 hθ, hc1,
    eventually_completedConductorEnergy_ge_on_Ioc hφ hsupp hM_int hθ0 hθ hc1 hc_lim
      (by norm_num : (0 : ℝ) < 1 / 2),
    hres.eventually (ge_mem_nhds heps),
    eventually_ge_atTop 4] with N hcut hcN1 hE_top hres_sm hN4
  obtain ⟨hM2, hMN, _, hfl_le, hLN_exp⟩ := hcut
  let M := ⌊(N : ℝ) ^ θ⌋₊
  have hM1 : 1 ≤ M := by omega
  have hMR0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hLN0 : 0 < Real.log N := by linarith [Real.exp_pos 7]
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN1
  -- Split into residual Rayleigh sum plus diagonal conductor sum.
  have hsplit : (∑ m ∈ Icc 1 M,
      completeWeilEnergy φ (c N) N (normalizedRamanujanHorizonVector m N)) =
      (∑ m ∈ Icc 1 M,
        ⟪completeWeilConductorResidual φ (c N) N m, normalizedRamanujanHorizonVector m N⟫) +
      ∑ m ∈ Icc 1 M,
        completedConductorEnergy φ (c N) m * ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun m _ =>
      completeWeilEnergy_normalizedRamanujanHorizonVector_eq φ (c N) N m
  -- Lower bound the diagonal sum via `completedConductorEnergy_nonneg` and the top half.
  let S_top := Ioc ⌊(1 / 2 : ℝ) * (M : ℝ)⌋₊ M
  have hsub : S_top ⊆ Icc 1 M := fun m hm =>
    mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2⟩
  have hcard_top : (M : ℝ) / 2 ≤ S_top.card := by
    have hfl : (⌊(1 / 2 : ℝ) * (M : ℝ)⌋₊ : ℝ) ≤ (1 / 2 : ℝ) * (M : ℝ) :=
      Nat.floor_le (by positivity)
    have hle_M : ⌊(1 / 2 : ℝ) * (M : ℝ)⌋₊ ≤ M := by
      have hR : (⌊(1 / 2 : ℝ) * (M : ℝ)⌋₊ : ℝ) ≤ (M : ℝ) :=
        hfl.trans (by linarith [Nat.cast_nonneg (α := ℝ) M])
      exact_mod_cast hR
    dsimp only [S_top]
    rw [Nat.card_Ioc, Nat.cast_sub hle_M]
    linarith only [hfl]
  have hdiag_lb : 2 * c₀ * (M : ℝ) * Real.log N ≤
      ∑ m ∈ Icc 1 M,
        completedConductorEnergy φ (c N) m * ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have hnonneg : ∀ m ∈ Icc 1 M, m ∉ S_top →
        0 ≤ completedConductorEnergy φ (c N) m * ‖normalizedRamanujanHorizonVector m N‖ ^ 2 :=
      fun m hm _ => mul_nonneg (completedConductorEnergy_nonneg hφ hsupp hM_int hc0 (mem_Icc.mp hm).1)
        (sq_nonneg _)
    calc
      2 * c₀ * (M : ℝ) * Real.log N =
          ((M : ℝ) / 2) * (((θ / 2) * Real.log N) * (1 - 2 * θ)) := by
        dsimp only [c₀]; ring
      _ ≤ (S_top.card : ℝ) * (((θ / 2) * Real.log N) * (1 - 2 * θ)) :=
        mul_le_mul_of_nonneg_right hcard_top
          (mul_nonneg (by positivity) (by linarith only [hθ]))
      _ = ∑ _m ∈ S_top, ((θ / 2) * Real.log N) * (1 - 2 * θ) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ S_top,
            completedConductorEnergy φ (c N) m * ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := by
        refine sum_le_sum fun m hm => ?_
        exact mul_le_mul (hE_top m hm)
          (normalizedRamanujanHorizonVector_norm_sq_ge (hsub hm) hN4 hfl_le)
          (by linarith only [hθ]) ((mul_pos (half_pos hθ0) hLN0).le.trans (hE_top m hm))
      _ ≤ ∑ m ∈ Icc 1 M,
            completedConductorEnergy φ (c N) m * ‖normalizedRamanujanHorizonVector m N‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub hnonneg
  -- Bound the residual Rayleigh sum by `c₀ * M * log N` via Cauchy–Schwarz and `‖v_m‖² ≤ 6`.
  have hres_ub : -(c₀ * (M : ℝ) * Real.log N) ≤
      ∑ m ∈ Icc 1 M,
        ⟪completeWeilConductorResidual φ (c N) N m, normalizedRamanujanHorizonVector m N⟫ := by
    let S_neg := ∑ m ∈ Icc 1 M,
      (-⟪completeWeilConductorResidual φ (c N) N m, normalizedRamanujanHorizonVector m N⟫)
    suffices hS : S_neg ≤ c₀ * (M : ℝ) * Real.log N by
      dsimp only [S_neg] at hS
      rw [sum_neg_distrib] at hS
      linarith only [hS]
    by_cases hS0 : S_neg ≤ 0
    · exact hS0.trans (by positivity)
    · have hS_pos : 0 < S_neg := lt_of_not_ge hS0
      have hpt : ∀ m ∈ Icc 1 M,
          -⟪completeWeilConductorResidual φ (c N) N m, normalizedRamanujanHorizonVector m N⟫ ≤
            ‖completeWeilConductorResidual φ (c N) N m‖ *
              ‖normalizedRamanujanHorizonVector m N‖ := by
        intro m _
        calc
          -⟪completeWeilConductorResidual φ (c N) N m, normalizedRamanujanHorizonVector m N⟫ =
              ⟪-completeWeilConductorResidual φ (c N) N m, normalizedRamanujanHorizonVector m N⟫ :=
            (inner_neg_left _ _).symm
          _ ≤ ‖-completeWeilConductorResidual φ (c N) N m‖ *
                ‖normalizedRamanujanHorizonVector m N‖ := real_inner_le_norm _ _
          _ = ‖completeWeilConductorResidual φ (c N) N m‖ *
                ‖normalizedRamanujanHorizonVector m N‖ := by rw [norm_neg]
      have hS_le : S_neg ≤ ∑ m ∈ Icc 1 M,
          ‖completeWeilConductorResidual φ (c N) N m‖ *
            ‖normalizedRamanujanHorizonVector m N‖ := sum_le_sum hpt
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 M)
        (fun m => ‖completeWeilConductorResidual φ (c N) N m‖)
        (fun m => ‖normalizedRamanujanHorizonVector m N‖)
      have hv_sum : (∑ m ∈ Icc 1 M, ‖normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ 6 * (M : ℝ) := by
        calc
          _ ≤ ∑ _m ∈ Icc 1 M, (6 : ℝ) :=
            sum_le_sum fun m hm => normalizedRamanujanHorizonVector_norm_sq_le_six hm hMN hLN_exp
          _ = 6 * (M : ℝ) := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
      have hr_sum : (∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2) ≤
          (c₀ ^ 2 / 6) * ((M : ℝ) * (Real.log N) ^ 2) :=
        (div_le_iff₀ (by positivity)).mp hres_sm
      have hS_sq : S_neg ^ 2 ≤ (c₀ * (M : ℝ) * Real.log N) ^ 2 := by
        calc
          S_neg ^ 2 ≤ (∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ (c N) N m‖ *
              ‖normalizedRamanujanHorizonVector m N‖) ^ 2 :=
            pow_le_pow_left₀ hS_pos.le hS_le 2
          _ ≤ (∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2) *
                (∑ m ∈ Icc 1 M, ‖normalizedRamanujanHorizonVector m N‖ ^ 2) := hcs
          _ ≤ ((c₀ ^ 2 / 6) * ((M : ℝ) * (Real.log N) ^ 2)) * (6 * (M : ℝ)) :=
            mul_le_mul hr_sum hv_sum (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
          _ = (c₀ * (M : ℝ) * Real.log N) ^ 2 := by ring
      by_contra hgt
      have hlt : c₀ * (M : ℝ) * Real.log N < S_neg := lt_of_not_ge hgt
      have hB_pos : 0 < c₀ * (M : ℝ) * Real.log N := by positivity
      nlinarith only [hS_sq, hlt, hB_pos]
  -- Conclude `c₀ * log N ≤ (1 / M) * ∑_{m=1}^M completeWeilEnergy`.
  have htot : c₀ * (M : ℝ) * Real.log N ≤
      ∑ m ∈ Icc 1 M, completeWeilEnergy φ (c N) N (normalizedRamanujanHorizonVector m N) := by
    rw [hsplit]
    linarith only [hdiag_lb, hres_ub]
  calc
    c₀ * Real.log N = (1 / (M : ℝ)) * (c₀ * (M : ℝ) * Real.log N) := by
      field_simp [hMR0.ne']
    _ ≤ (1 / (M : ℝ)) *
          ∑ m ∈ Icc 1 M, completeWeilEnergy φ (c N) N (normalizedRamanujanHorizonVector m N) :=
      mul_le_mul_of_nonneg_left htot (by positivity)

/-- Eventual strict positivity of the conductor average of `completeWeilEnergy` at RH-complete
resolution (`0 < θ < 1 / 2`, `c N ^ 2 / log N → 0`). -/
theorem eventually_completeWeil_conductorAverage_pos {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    {c : ℕ → ℝ} (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (hc_lim : Tendsto (fun N => c N ^ 2 / Real.log N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop,
      0 < (1 / (⌊(N : ℝ) ^ θ⌋₊ : ℝ)) *
        ∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
          completeWeilEnergy φ (c N) N (normalizedRamanujanHorizonVector m N) :=
  (tendsto_completeWeil_conductorAverage_atTop hφ hsupp hM_int hθ0 hθ hc1 hc_lim).eventually_gt_atTop 0

/-- **Almost-All Conductor Positivity Census at RH-Complete Overlap.**
Under the hypotheses of Question Q3 (`0 < θ < 1 / 2`, `∀ᶠ N, 1 ≤ c N`, `c N ^ 2 / log N → 0`),
the fraction of conductors `1 ≤ m ≤ ⌊N^θ⌋₊` on which `completeWeilEnergy φ (c N) N v_m ≤ 0`
tends to `0`. -/
theorem tendsto_nonpositive_conductor_fraction_zero {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    {c : ℕ → ℝ} (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (hc_lim : Tendsto (fun N => c N ^ 2 / Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (((Icc 1 ⌊(N : ℝ) ^ θ⌋₊).filter (fun m =>
        completeWeilEnergy φ (c N) N (normalizedRamanujanHorizonVector m N) ≤ 0)).card : ℝ) /
      (⌊(N : ℝ) ^ θ⌋₊ : ℝ)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun N =>
      ha.trans_le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · intro b hb
    let δ := min (b / 2) (1 / 2)
    have hδ0 : 0 < δ := by dsimp only [δ]; positivity
    have hδ_b : δ ≤ b / 2 := min_le_left _ _
    let γ := (1 - 2 * θ) * θ / 2
    have hγ0 : 0 < γ := by
      dsimp only [γ]
      have : 0 < 1 - 2 * θ := by linarith only [hθ]
      positivity
    have hres := tendsto_completeWeil_residual_div_mul_log_sq_zero hφ hsupp hM_int hθ0 hθ hc1 hc_lim
    have heps : 0 < (b / 2) * (γ ^ 2 / 6) := by positivity
    filter_upwards [eventually_conductorCutoff_bounds hθ0 hθ,
      eventually_completedConductorEnergy_ge_on_Ioc hφ hsupp hM_int hθ0 hθ hc1 hc_lim hδ0,
      hres.eventually (gt_mem_nhds heps),
      eventually_ge_atTop 4] with N hcut hE_high hres_lt hN4
    obtain ⟨hM2, hMN, _, hfl_le, hLN_exp⟩ := hcut
    let M := ⌊(N : ℝ) ^ θ⌋₊
    have hM1 : 1 ≤ M := by omega
    have hMR0 : (0 : ℝ) < M := by exact_mod_cast hM1
    have hLN0 : 0 < Real.log N := by linarith [Real.exp_pos 7]
    let M_low := ⌊δ * (M : ℝ)⌋₊
    let bad := (Icc 1 M).filter (fun m =>
      completeWeilEnergy φ (c N) N (normalizedRamanujanHorizonVector m N) ≤ 0)
    let bad_low := bad.filter (· ≤ M_low)
    let bad_high := bad.filter (fun m => ¬ m ≤ M_low)
    have hcard_split : bad.card = bad_low.card + bad_high.card :=
      (Finset.card_filter_add_card_filter_not (s := bad) (· ≤ M_low)).symm
    -- Low conductors: `bad_low ⊆ Icc 1 M_low`, so `bad_low.card ≤ M_low ≤ δ * M`.
    have hlow_le : (bad_low.card : ℝ) ≤ (b / 2) * (M : ℝ) := by
      have hsub_low : bad_low ⊆ Icc 1 M_low := fun m hm => by
        obtain ⟨hm_bad, hm_le⟩ := mem_filter.mp hm
        exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hm_bad).1).1, hm_le⟩
      have hnat : bad_low.card ≤ M_low := by
        have h := Finset.card_le_card hsub_low
        rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
      have hfl : (M_low : ℝ) ≤ δ * (M : ℝ) := Nat.floor_le (by positivity)
      calc
        (bad_low.card : ℝ) ≤ (M_low : ℝ) := by exact_mod_cast hnat
        _ ≤ δ * (M : ℝ) := hfl
        _ ≤ (b / 2) * (M : ℝ) := mul_le_mul_of_nonneg_right hδ_b hMR0.le
    -- High bad conductors: each contributes `(γ log N)² ≤ 6 ‖r_m‖²`.
    have hhigh_lt : (bad_high.card : ℝ) < (b / 2) * (M : ℝ) := by
      have hsub_Ioc : bad_high ⊆ Ioc M_low M := fun m hm => by
        obtain ⟨hm_bad, hm_gt⟩ := mem_filter.mp hm
        exact mem_Ioc.mpr ⟨Nat.lt_of_not_ge hm_gt, (mem_Icc.mp (mem_filter.mp hm_bad).1).2⟩
      have hsub_Icc : bad_high ⊆ Icc 1 M := fun m hm =>
        (mem_filter.mp (mem_filter.mp hm).1).1
      have hpt : ∀ m ∈ bad_high,
          (γ * Real.log N) ^ 2 ≤ 6 * ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2 := by
        intro m hm
        have hm_Ioc := hsub_Ioc hm
        have hm_Icc := hsub_Icc hm
        have hm_neg : completeWeilEnergy φ (c N) N (normalizedRamanujanHorizonVector m N) ≤ 0 :=
          (mem_filter.mp (mem_filter.mp hm).1).2
        rw [completeWeilEnergy_normalizedRamanujanHorizonVector_eq] at hm_neg
        have hdiag_m : γ * Real.log N ≤
            completedConductorEnergy φ (c N) m *
              ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := by
          calc
            γ * Real.log N = ((θ / 2) * Real.log N) * (1 - 2 * θ) := by dsimp only [γ]; ring
            _ ≤ completedConductorEnergy φ (c N) m *
                  ‖normalizedRamanujanHorizonVector m N‖ ^ 2 :=
              mul_le_mul (hE_high m hm_Ioc)
                (normalizedRamanujanHorizonVector_norm_sq_ge hm_Icc hN4 hfl_le)
                (by linarith only [hθ]) ((mul_pos (half_pos hθ0) hLN0).le.trans (hE_high m hm_Ioc))
        have hinner_ge : γ * Real.log N ≤
            ‖completeWeilConductorResidual φ (c N) N m‖ *
              ‖normalizedRamanujanHorizonVector m N‖ := by
          have h1 : γ * Real.log N ≤
              -⟪completeWeilConductorResidual φ (c N) N m,
                normalizedRamanujanHorizonVector m N⟫ := by linarith only [hm_neg, hdiag_m]
          have h2 :
              -⟪completeWeilConductorResidual φ (c N) N m,
                normalizedRamanujanHorizonVector m N⟫ ≤
                ‖completeWeilConductorResidual φ (c N) N m‖ *
                  ‖normalizedRamanujanHorizonVector m N‖ := by
            rw [← inner_neg_left]
            exact (real_inner_le_norm _ _).trans_eq (by rw [norm_neg])
          exact h1.trans h2
        calc
          (γ * Real.log N) ^ 2 ≤
              (‖completeWeilConductorResidual φ (c N) N m‖ *
                ‖normalizedRamanujanHorizonVector m N‖) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hinner_ge 2
          _ = ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2 *
                ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := mul_pow _ _ 2
          _ ≤ ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2 * 6 :=
            mul_le_mul_of_nonneg_left
              (normalizedRamanujanHorizonVector_norm_sq_le_six hm_Icc hMN hLN_exp) (sq_nonneg _)
          _ = 6 * ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2 := mul_comm _ _
      have hsum_high : (bad_high.card : ℝ) * (γ * Real.log N) ^ 2 ≤
          6 * ∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2 := by
        calc
          (bad_high.card : ℝ) * (γ * Real.log N) ^ 2 =
              ∑ _m ∈ bad_high, (γ * Real.log N) ^ 2 := by rw [sum_const, nsmul_eq_mul]
          _ ≤ ∑ m ∈ bad_high, 6 * ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2 :=
            sum_le_sum hpt
          _ ≤ ∑ m ∈ Icc 1 M, 6 * ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2 :=
            sum_le_sum_of_subset_of_nonneg hsub_Icc fun _ _ _ => by positivity
          _ = 6 * ∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2 :=
            (mul_sum _ _ _).symm
      have hr_lt : (∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2) <
          ((b / 2) * (γ ^ 2 / 6)) * ((M : ℝ) * (Real.log N) ^ 2) :=
        (div_lt_iff₀ (by positivity)).mp hres_lt
      have hmul_lt : (bad_high.card : ℝ) * (γ * Real.log N) ^ 2 <
          ((b / 2) * (M : ℝ)) * (γ * Real.log N) ^ 2 := by
        calc
          (bad_high.card : ℝ) * (γ * Real.log N) ^ 2 ≤
              6 * ∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2 := hsum_high
          _ < 6 * (((b / 2) * (γ ^ 2 / 6)) * ((M : ℝ) * (Real.log N) ^ 2)) :=
            mul_lt_mul_of_pos_left hr_lt (by norm_num)
          _ = ((b / 2) * (M : ℝ)) * (γ * Real.log N) ^ 2 := by ring
      exact lt_of_mul_lt_mul_right hmul_lt (sq_nonneg _)
    -- Combine low and high bad conductor counts.
    rw [div_lt_iff₀ hMR0]
    have hcardR : (bad.card : ℝ) = (bad_low.card : ℝ) + (bad_high.card : ℝ) := by
      exact_mod_cast hcard_split
    linarith only [hcardR, hlow_le, hhigh_lt]

/-! ### High-conductor subspace and deterministic dimension bound -/

/-- The high-conductor subspace spanned by `normalizedRamanujanHorizonVector m N`
for `m ∈ Ioc M_low M`. -/
def highConductorSubspace (M_low M N : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)) :=
  Submodule.span ℝ
    (Set.range (fun m : ↥(Ioc M_low M) => normalizedRamanujanHorizonVector m.1 N))

theorem highConductorSubspace_le_conductorSubspace (M_low M N : ℕ) :
    highConductorSubspace M_low M N ≤ conductorSubspace M N := by
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  have hm : m.1 ∈ Icc 1 M :=
    mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp m.2).1, (mem_Ioc.mp m.2).2⟩
  exact ⟨⟨m.1, hm⟩, rfl⟩

theorem finrank_highConductorSubspace_eq {M_low M N : ℕ} (hN : 2 ≤ N)
    (h2log : 2 * Real.log M < Real.log N) :
    Module.finrank ℝ (highConductorSubspace M_low M N) = M - M_low := by
  have hS_sub : Ioc M_low M ⊆ Icc 1 M := fun m hm =>
    mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2⟩
  have hemb : Function.Injective (fun m : ↥(Ioc M_low M) => (⟨m.1, hS_sub m.2⟩ : ↥(Icc 1 M))) :=
    fun _ _ h => Subtype.ext (Subtype.ext_iff.mp h)
  have hli : LinearIndependent ℝ
      (fun m : ↥(Ioc M_low M) => normalizedRamanujanHorizonVector m.1 N) :=
    (linearIndependent_conductorBasisFamily hN h2log).comp _ hemb
  unfold highConductorSubspace
  rw [finrank_span_eq_card hli, Fintype.card_coe]
  exact Nat.card_Ioc M_low M

theorem mem_highConductorSubspace_exists_coeff {M_low M N : ℕ}
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu : u ∈ highConductorSubspace M_low M N) :
    ∃ a : ℕ → ℝ, (∀ m, m ∉ Ioc M_low M → a m = 0) ∧
      u = ∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N := by
  have hS_sub : Ioc M_low M ⊆ Icc 1 M := fun m hm =>
    mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2⟩
  unfold highConductorSubspace at hu
  rw [Submodule.mem_span_range_iff_exists_fun] at hu
  obtain ⟨c_fn, hc_eq⟩ := hu
  refine ⟨fun m => if hm : m ∈ Ioc M_low M then c_fn ⟨m, hm⟩ else 0,
    fun m hm => dif_neg hm, ?_⟩
  have h1 : (∑ x : ↥(Ioc M_low M), c_fn x • normalizedRamanujanHorizonVector x.1 N) =
      ∑ x : ↥(Ioc M_low M),
        (if hm : x.1 ∈ Ioc M_low M then c_fn ⟨x.1, hm⟩ else 0) •
          normalizedRamanujanHorizonVector x.1 N :=
    Finset.sum_congr rfl fun x _ => by simp only [dif_pos x.2]
  have h2 := Finset.sum_coe_sort (Ioc M_low M) (fun m =>
    (if hm : m ∈ Ioc M_low M then c_fn ⟨m, hm⟩ else 0) •
      normalizedRamanujanHorizonVector m N)
  have h3 : (∑ m ∈ Ioc M_low M,
      (if hm : m ∈ Ioc M_low M then c_fn ⟨m, hm⟩ else 0) •
        normalizedRamanujanHorizonVector m N) =
      ∑ m ∈ Icc 1 M,
        (if hm : m ∈ Ioc M_low M then c_fn ⟨m, hm⟩ else 0) •
          normalizedRamanujanHorizonVector m N :=
    Finset.sum_subset hS_sub fun m _ hm_not => by simp only [dif_neg hm_not, zero_smul]
  exact hc_eq.symm.trans (h1.trans (h2.trans h3))

theorem finrank_le_finrank_inf_highConductorSubspace_add
    {M_low M N : ℕ} (hN : 2 ≤ N) (h2log : 2 * Real.log M < Real.log N)
    (U : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (hU : U ≤ conductorSubspace M N) :
    Module.finrank ℝ U ≤
      Module.finrank ℝ ↥(U ⊓ highConductorSubspace M_low M N) + M_low := by
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq U (highConductorSubspace M_low M N)
  have hsup_le : Module.finrank ℝ ↥(U ⊔ highConductorSubspace M_low M N) ≤ M := by
    have hmono := Submodule.finrank_mono
      (sup_le hU (highConductorSubspace_le_conductorSubspace M_low M N))
    rwa [finrank_conductorSubspace_eq hN h2log] at hmono
  rw [finrank_highConductorSubspace_eq hN h2log] at hgrass
  omega

private theorem completeWeilMatrix_apply_sum_eq (φ : ℝ → ℝ) (c : ℝ) (N M : ℕ)
    (E₀ : ℝ) (a : ℕ → ℝ) :
    Matrix.toEuclideanLin (completeWeilMatrix φ c N)
        (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) =
      (∑ m ∈ Icc 1 M, a m • completeWeilConductorResidual φ c N m) +
        (∑ m ∈ Icc 1 M,
          (a m * (completedConductorEnergy φ c m - E₀)) •
            normalizedRamanujanHorizonVector m N) +
        E₀ • ∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N := by
  rw [map_sum, smul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_smul]
  unfold completeWeilConductorResidual
  module

private theorem highConductor_unit_vector_residual_pairing_ge
    {φ : ℝ → ℝ} {c θ E₀ : ℝ} {M_low M N : ℕ}
    (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hE₀_pos : 0 < E₀)
    (hM1 : 1 ≤ M) (hN4 : 4 ≤ N) (hfl_le : (M : ℝ) ≤ (N : ℝ) ^ θ)
    (hMN : M * M ≤ N) (hLN_exp : 4 * Real.exp 7 ≤ Real.log N)
    (hE_conc : ∀ m ∈ Ioc M_low M,
      |completedConductorEnergy φ c m - E₀| ≤ ((1 - 2 * θ) / 6) * E₀)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu_norm_sq : ‖u‖ ^ 2 = 1)
    (hu_neg : completeWeilEnergy φ c N u ≤ 0)
    {a : ℕ → ℝ} (ha_supp : ∀ m, m ∉ Ioc M_low M → a m = 0)
    (hu_eq : u = ∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) :
    (∑ m ∈ Icc 1 M, a m ^ 2 ≤ 1 / (1 - 2 * θ)) ∧
      E₀ / 2 ≤ ∑ m ∈ Icc 1 M, (-a m) * ⟪completeWeilConductorResidual φ c N m, u⟫ := by
  have h12θ : 0 < 1 - 2 * θ := by linarith only [hθ]
  have ha_riesz : (∑ m ∈ Icc 1 M, a m ^ 2) ≤ 1 / (1 - 2 * θ) := by
    have hlow := ramanujanConductor_lower_riesz hM1 hN4 hfl_le a
    rw [← hu_eq, hu_norm_sq] at hlow
    rwa [le_div_iff₀' h12θ]
  refine ⟨ha_riesz, ?_⟩
  have hu_norm : ‖u‖ = 1 := by
    have h0 := norm_nonneg u
    nlinarith only [hu_norm_sq, h0]
  have hW_vec : Matrix.toEuclideanLin (completeWeilMatrix φ c N) u =
      (∑ m ∈ Icc 1 M, a m • completeWeilConductorResidual φ c N m) +
        (∑ m ∈ Icc 1 M,
          (a m * (completedConductorEnergy φ c m - E₀)) •
            normalizedRamanujanHorizonVector m N) +
        E₀ • u := by
    have h := completeWeilMatrix_apply_sum_eq φ c N M E₀ a
    rwa [← hu_eq] at h
  generalize hw_def : (∑ m ∈ Icc 1 M,
      (a m * (completedConductorEnergy φ c m - E₀)) •
        normalizedRamanujanHorizonVector m N) = w_shift at hW_vec
  have hW_expand : completeWeilEnergy φ c N u =
      (∑ m ∈ Icc 1 M, a m * ⟪completeWeilConductorResidual φ c N m, u⟫) +
        ⟪w_shift, u⟫ + E₀ := by
    unfold completeWeilEnergy
    rw [hW_vec, inner_add_left, inner_add_left, sum_inner, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu_norm_sq, mul_one]
    congr 2
    exact sum_congr rfl fun m _ => real_inner_smul_left _ _ _
  have hw_sq : ‖w_shift‖ ^ 2 ≤ (E₀ / 2) ^ 2 := by
    rw [← hw_def]
    have hup := ramanujanConductor_upper_riesz hMN hLN_exp
      (fun m => a m * (completedConductorEnergy φ c m - E₀))
    have hcoef : ∀ m ∈ Icc 1 M,
        (a m * (completedConductorEnergy φ c m - E₀)) ^ 2 ≤
          a m ^ 2 * (((1 - 2 * θ) / 6) * E₀) ^ 2 := by
      intro m _
      by_cases hmS : m ∈ Ioc M_low M
      · rw [mul_pow, ← sq_abs (completedConductorEnergy φ c m - E₀)]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (hE_conc m hmS) 2) (sq_nonneg _)
      · rw [ha_supp m hmS]
        simp
    have heta_alg : 6 * (1 / (1 - 2 * θ)) * ((1 - 2 * θ) / 6) ^ 2 ≤ 1 / 4 := by
      have h1 : 6 * (1 / (1 - 2 * θ)) * ((1 - 2 * θ) / 6) ^ 2 = (1 - 2 * θ) / 6 := by
        field_simp [h12θ.ne']
      rw [h1]
      linarith only [hθ0]
    calc
      _ ≤ 6 * ∑ m ∈ Icc 1 M, (a m * (completedConductorEnergy φ c m - E₀)) ^ 2 := hup
      _ ≤ 6 * ∑ m ∈ Icc 1 M, a m ^ 2 * (((1 - 2 * θ) / 6) * E₀) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum hcoef) (by norm_num)
      _ = 6 * (∑ m ∈ Icc 1 M, a m ^ 2) * (((1 - 2 * θ) / 6) * E₀) ^ 2 := by
        rw [← sum_mul, mul_assoc]
      _ ≤ 6 * (1 / (1 - 2 * θ)) * (((1 - 2 * θ) / 6) * E₀) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ha_riesz (by norm_num)) (sq_nonneg _)
      _ = (6 * (1 / (1 - 2 * θ)) * ((1 - 2 * θ) / 6) ^ 2) * E₀ ^ 2 := by ring
      _ ≤ (1 / 4) * E₀ ^ 2 := mul_le_mul_of_nonneg_right heta_alg (sq_nonneg _)
      _ = (E₀ / 2) ^ 2 := by ring
  have hw_norm : ‖w_shift‖ ≤ E₀ / 2 := by
    by_contra hgt
    have hlt : E₀ / 2 < ‖w_shift‖ := lt_of_not_ge hgt
    nlinarith only [hw_sq, hlt, hE₀_pos]
  have hshift_ge : -(E₀ / 2) ≤ ⟪w_shift, u⟫ := by
    have h1 : -⟪w_shift, u⟫ ≤ ‖w_shift‖ * ‖u‖ := by
      rw [← inner_neg_left]
      exact (real_inner_le_norm _ _).trans_eq (by rw [norm_neg])
    rw [hu_norm, mul_one] at h1
    linarith only [h1, hw_norm]
  have hsum_neg : (∑ m ∈ Icc 1 M, (-a m) *
      ⟪completeWeilConductorResidual φ c N m, u⟫) =
      -(∑ m ∈ Icc 1 M, a m * ⟪completeWeilConductorResidual φ c N m, u⟫) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun m _ => neg_mul _ _
  rw [hsum_neg]
  linarith only [hu_neg, hW_expand, hshift_ge]

private theorem card_orthonormalBasis_nonpos_highConductor_le
    {ι : Type*} [Fintype ι]
    {φ : ℝ → ℝ} {c θ E₀ : ℝ} {M_low M N : ℕ}
    (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hE₀_pos : 0 < E₀)
    (hM1 : 1 ≤ M) (hN4 : 4 ≤ N) (hfl_le : (M : ℝ) ≤ (N : ℝ) ^ θ)
    (hMN : M * M ≤ N) (hLN_exp : 4 * Real.exp 7 ≤ Real.log N)
    (hE_conc : ∀ m ∈ Ioc M_low M,
      |completedConductorEnergy φ c m - E₀| ≤ ((1 - 2 * θ) / 6) * E₀)
    {W : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N))}
    (hW_high : W ≤ highConductorSubspace M_low M N)
    (hW_neg : ∀ u ∈ W, completeWeilEnergy φ c N u ≤ 0)
    (b : OrthonormalBasis ι ℝ W) :
    (Fintype.card ι : ℝ) * ((1 - 2 * θ) * E₀ ^ 2 / 4) ≤
      ∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ c N m‖ ^ 2 := by
  have h12θ : 0 < 1 - 2 * θ := by linarith only [hθ]
  have hex_coord : ∀ i : ι, ∃ a : ℕ → ℝ,
      (∀ m, m ∉ Ioc M_low M → a m = 0) ∧
      (b i : EuclideanSpace ℝ (PrimeHorizonIndex N)) =
        ∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N :=
    fun i => mem_highConductorSubspace_exists_coeff (hW_high (b i).2)
  obtain ⟨A, hA⟩ := Classical.axiomOfChoice hex_coord
  have hb_norm_sq : ∀ i : ι, ‖(b i : EuclideanSpace ℝ (PrimeHorizonIndex N))‖ ^ 2 = 1 := by
    intro i
    rw [← real_inner_self_eq_norm_sq, ← W.coe_inner,
      orthonormal_iff_ite.mp b.orthonormal i i, if_pos rfl]
  have hpair : ∀ i : ι,
      (∑ m ∈ Icc 1 M, A i m ^ 2 ≤ 1 / (1 - 2 * θ)) ∧
        E₀ / 2 ≤ ∑ m ∈ Icc 1 M,
          (-A i m) * ⟪completeWeilConductorResidual φ c N m,
            (b i : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫ :=
    fun i => highConductor_unit_vector_residual_pairing_ge hθ0 hθ hE₀_pos
      hM1 hN4 hfl_le hMN hLN_exp hE_conc (hb_norm_sq i)
      (hW_neg _ (b i).2) (hA i).1 (hA i).2
  generalize ht_def : (1 - 2 * θ) * E₀ / 2 = t
  have ht_pos : 0 < t := by rw [← ht_def]; positivity
  have hpt_young : ∀ i : ι,
      2 * t * (E₀ / 2) ≤
        t ^ 2 * (∑ m ∈ Icc 1 M, A i m ^ 2) +
          ∑ m ∈ Icc 1 M,
            ⟪completeWeilConductorResidual φ c N m,
              (b i : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫ ^ 2 := by
    intro i
    have h1 := mul_le_mul_of_nonneg_left (hpair i).2 (by positivity : 0 ≤ 2 * t)
    have h2 : 2 * t * (∑ m ∈ Icc 1 M,
        (-A i m) * ⟪completeWeilConductorResidual φ c N m,
          (b i : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫) ≤
        ∑ m ∈ Icc 1 M, (t ^ 2 * A i m ^ 2 +
          ⟪completeWeilConductorResidual φ c N m,
            (b i : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫ ^ 2) := by
      rw [mul_sum]
      refine sum_le_sum fun m _ => ?_
      have hsq := sq_nonneg
        (t * (-A i m) -
          ⟪completeWeilConductorResidual φ c N m,
            (b i : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫)
      nlinarith only [hsq]
    rw [sum_add_distrib, ← mul_sum] at h2
    exact h1.trans h2
  have hsum_young : (Fintype.card ι : ℝ) * (t * E₀) ≤
      t ^ 2 * ((Fintype.card ι : ℝ) * (1 / (1 - 2 * θ))) +
        ∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ c N m‖ ^ 2 := by
    have hlhs : (∑ _i : ι, 2 * t * (E₀ / 2)) = (Fintype.card ι : ℝ) * (t * E₀) := by
      rw [sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    have hrhs1 : (∑ i : ι, t ^ 2 * (∑ m ∈ Icc 1 M, A i m ^ 2)) ≤
        t ^ 2 * ((Fintype.card ι : ℝ) * (1 / (1 - 2 * θ))) := by
      rw [← mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg t)
      calc
        (∑ i : ι, ∑ m ∈ Icc 1 M, A i m ^ 2) ≤ ∑ _i : ι, 1 / (1 - 2 * θ) :=
          sum_le_sum fun i _ => (hpair i).1
        _ = (Fintype.card ι : ℝ) * (1 / (1 - 2 * θ)) := by
          rw [sum_const, Finset.card_univ, nsmul_eq_mul]
    have hrhs2 : (∑ i : ι, ∑ m ∈ Icc 1 M,
        ⟪completeWeilConductorResidual φ c N m,
          (b i : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫ ^ 2) ≤
        ∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ c N m‖ ^ 2 := by
      rw [Finset.sum_comm]
      exact sum_le_sum fun m _ =>
        sum_sq_inner_orthonormalBasis_le b (completeWeilConductorResidual φ c N m)
    have htot := sum_le_sum (s := (Finset.univ : Finset ι)) fun i _ => hpt_young i
    rw [hlhs, sum_add_distrib] at htot
    exact htot.trans (add_le_add hrhs1 hrhs2)
  have hcoef_eq : (Fintype.card ι : ℝ) * (t * E₀) -
      t ^ 2 * ((Fintype.card ι : ℝ) * (1 / (1 - 2 * θ))) =
      (Fintype.card ι : ℝ) * ((1 - 2 * θ) * E₀ ^ 2 / 4) := by
    rw [← ht_def]
    have hne : 1 - 2 * θ ≠ 0 := h12θ.ne'
    calc
      (Fintype.card ι : ℝ) * (((1 - 2 * θ) * E₀ / 2) * E₀) -
          ((1 - 2 * θ) * E₀ / 2) ^ 2 * ((Fintype.card ι : ℝ) * (1 / (1 - 2 * θ))) =
        (Fintype.card ι : ℝ) * ((1 - 2 * θ) * E₀ ^ 2 / 2 -
          ((1 - 2 * θ) * E₀ ^ 2 / 4) * ((1 - 2 * θ) / (1 - 2 * θ))) := by ring
      _ = (Fintype.card ι : ℝ) * ((1 - 2 * θ) * E₀ ^ 2 / 4) := by
        rw [div_self hne]; ring
  linarith only [hsum_young, hcoef_eq]

/-- Deterministic bound on the dimension of any nonpositive subspace of
`highConductorSubspace M_low M N` in terms of the collective complete-Weil residual energy. -/
theorem finrank_nonpos_highConductor_subspace_le
    {φ : ℝ → ℝ} {c θ : ℝ} {M_low M N : ℕ}
    (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (hM1 : 1 ≤ M) (hN4 : 4 ≤ N) (hfl_le : (M : ℝ) ≤ (N : ℝ) ^ θ)
    (hMN : M * M ≤ N) (hLN_exp : 4 * Real.exp 7 ≤ Real.log N)
    (hE_conc : ∀ m ∈ Ioc M_low M,
      |completedConductorEnergy φ c m - θ * Real.log N| ≤
        ((1 - 2 * θ) / 6) * (θ * Real.log N))
    (W : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (hW_high : W ≤ highConductorSubspace M_low M N)
    (hW_neg : ∀ u ∈ W, completeWeilEnergy φ c N u ≤ 0) :
    (Module.finrank ℝ W : ℝ) ≤
      (4 / ((1 - 2 * θ) * θ ^ 2)) *
        ((∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ c N m‖ ^ 2) / (Real.log N) ^ 2) := by
  have h12θ : 0 < 1 - 2 * θ := by linarith only [hθ]
  have hLN0 : 0 < Real.log N := by linarith [Real.exp_pos 7]
  have hcard := card_orthonormalBasis_nonpos_highConductor_le hθ0 hθ (mul_pos hθ0 hLN0)
    hM1 hN4 hfl_le hMN hLN_exp hE_conc hW_high hW_neg (stdOrthonormalBasis ℝ W)
  rw [Fintype.card_fin] at hcard
  generalize (∑ m ∈ Icc 1 M, ‖completeWeilConductorResidual φ c N m‖ ^ 2) = S at hcard ⊢
  have hden : 0 < (1 - 2 * θ) * (θ * Real.log N) ^ 2 / 4 := by positivity
  rw [← le_div_iff₀ hden] at hcard
  refine hcard.trans_eq ?_
  have hne1 : (1 - 2 * θ) * (θ * Real.log N) ^ 2 / 4 ≠ 0 := hden.ne'
  have hne2 : (1 - 2 * θ) * θ ^ 2 ≠ 0 := (mul_pos h12θ (sq_pos_of_pos hθ0)).ne'
  have hne3 : (Real.log N) ^ 2 ≠ 0 := (sq_pos_of_pos hLN0).ne'
  rw [div_eq_iff hne1]
  calc
    (4 / ((1 - 2 * θ) * θ ^ 2)) * (S / (Real.log N) ^ 2) *
        ((1 - 2 * θ) * (θ * Real.log N) ^ 2 / 4) =
      S * (((1 - 2 * θ) * θ ^ 2) / ((1 - 2 * θ) * θ ^ 2)) *
        ((Real.log N) ^ 2 / (Real.log N) ^ 2) := by ring
    _ = S := by rw [div_self hne2, div_self hne3, mul_one, mul_one]

/-- **Sublinear Negative Index on the Conductor Subspace (`κ(W_{N, c_N}|_{V_M}) = o(M)`).**
For every `C²` profile `φ` supported in `[0, 1]` with `0 < ∫ φ²`, every Bombieri–Vinogradov
exponent `0 < θ < 1 / 2`, every overlap schedule `c : ℕ → ℝ` with `∀ᶠ N, 1 ≤ c N` and
`c N ^ 2 / log N → 0`, and every sequence of subspaces `U N ≤ conductorSubspace ⌊N^θ⌋₊ N` on
which `completeWeilEnergy φ (c N) N` is nonpositive (`∀ u ∈ U N, completeWeilEnergy φ (c N) N u ≤ 0`),
```
finrank ℝ (U N) / ⌊N^θ⌋₊ → 0.
```
-/
theorem tendsto_completeWeil_conductorSubspace_negIndex_div_zero {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    {c : ℕ → ℝ} (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (hc_lim : Tendsto (fun N => c N ^ 2 / Real.log N) atTop (𝓝 0))
    (U : ∀ N : ℕ, Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (hU_sub : ∀ N, U N ≤ conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)
    (hU_neg : ∀ N, ∀ u ∈ U N, completeWeilEnergy φ (c N) N u ≤ 0) :
    Tendsto (fun N : ℕ => (Module.finrank ℝ (U N) : ℝ) / (⌊(N : ℝ) ^ θ⌋₊ : ℝ)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun N =>
      ha.trans_le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · intro b hb
    have h12θ : 0 < 1 - 2 * θ := by linarith only [hθ]
    have hδ0 : 0 < min (b / 2) (1 / 2) := by positivity
    have hη0 : 0 < (1 - 2 * θ) / 6 := by positivity
    have hK_dim0 : 0 < 4 / ((1 - 2 * θ) * θ ^ 2) := by positivity
    have hres := tendsto_completeWeil_residual_div_mul_log_sq_zero hφ hsupp hM_int hθ0 hθ hc1 hc_lim
    have heps : 0 < (b / 2) / (4 / ((1 - 2 * θ) * θ ^ 2)) := by positivity
    filter_upwards [eventually_conductorCutoff_bounds hθ0 hθ,
      eventually_abs_completedConductorEnergy_sub_theta_log_le hφ hsupp hM_int hθ0 hθ hc1 hc_lim
        hδ0 hη0,
      hres.eventually (gt_mem_nhds heps),
      eventually_ge_atTop 4] with N hcut hE_conc hres_lt hN4
    obtain ⟨hM2, hMN, _, hfl_le, hLN_exp⟩ := hcut
    have hM1 : 1 ≤ ⌊(N : ℝ) ^ θ⌋₊ := by omega
    have hMR0 : (0 : ℝ) < ⌊(N : ℝ) ^ θ⌋₊ := by exact_mod_cast hM1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hLN0 : 0 < Real.log N := by linarith [Real.exp_pos 7]
    have h2log : 2 * Real.log (⌊(N : ℝ) ^ θ⌋₊ : ℝ) < Real.log N := by
      have hlogM : Real.log (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤ θ * Real.log N := by
        have h := Real.log_le_log hMR0 hfl_le
        rwa [Real.log_rpow hN0] at h
      nlinarith only [hlogM, hθ, hLN0]
    have hrank_U := finrank_le_finrank_inf_highConductorSubspace_add
      (M_low := ⌊min (b / 2) (1 / 2) * (⌊(N : ℝ) ^ θ⌋₊ : ℝ)⌋₊)
      (by omega : 2 ≤ N) h2log (U N) (hU_sub N)
    have hd_bound := finrank_nonpos_highConductor_subspace_le hθ0 hθ hM1 hN4 hfl_le hMN hLN_exp
      hE_conc (U N ⊓ highConductorSubspace ⌊min (b / 2) (1 / 2) * (⌊(N : ℝ) ^ θ⌋₊ : ℝ)⌋₊
        ⌊(N : ℝ) ^ θ⌋₊ N)
      inf_le_right (fun u hu => hU_neg N u hu.1)
    generalize (Module.finrank ℝ
      ↥(U N ⊓ highConductorSubspace ⌊min (b / 2) (1 / 2) * (⌊(N : ℝ) ^ θ⌋₊ : ℝ)⌋₊
        ⌊(N : ℝ) ^ θ⌋₊ N)) = d at hrank_U hd_bound
    generalize (∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
      ‖completeWeilConductorResidual φ (c N) N m‖ ^ 2) = S at hd_bound hres_lt
    have hd_div_lt : (d : ℝ) / (⌊(N : ℝ) ^ θ⌋₊ : ℝ) < b / 2 := by
      have h1 : (4 / ((1 - 2 * θ) * θ ^ 2)) *
          (S / ((⌊(N : ℝ) ^ θ⌋₊ : ℝ) * (Real.log N) ^ 2)) < b / 2 := by
        have := mul_lt_mul_of_pos_left hres_lt hK_dim0
        rwa [mul_div_cancel₀ _ hK_dim0.ne'] at this
      calc
        (d : ℝ) / (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤
            ((4 / ((1 - 2 * θ) * θ ^ 2)) * (S / (Real.log N) ^ 2)) / (⌊(N : ℝ) ^ θ⌋₊ : ℝ) :=
          div_le_div_of_nonneg_right hd_bound hMR0.le
        _ = (4 / ((1 - 2 * θ) * θ ^ 2)) *
            (S / ((⌊(N : ℝ) ^ θ⌋₊ : ℝ) * (Real.log N) ^ 2)) := by
          rw [mul_div_assoc, div_div, mul_comm ((Real.log N) ^ 2) (⌊(N : ℝ) ^ θ⌋₊ : ℝ)]
        _ < b / 2 := h1
    have hlow_div_le :
        (⌊min (b / 2) (1 / 2) * (⌊(N : ℝ) ^ θ⌋₊ : ℝ)⌋₊ : ℝ) / (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤ b / 2 := by
      rw [div_le_iff₀ hMR0]
      exact (Nat.floor_le (by positivity)).trans
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hMR0.le)
    have hU_le : (Module.finrank ℝ (U N) : ℝ) / (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤
        (d : ℝ) / (⌊(N : ℝ) ^ θ⌋₊ : ℝ) +
          (⌊min (b / 2) (1 / 2) * (⌊(N : ℝ) ^ θ⌋₊ : ℝ)⌋₊ : ℝ) / (⌊(N : ℝ) ^ θ⌋₊ : ℝ) := by
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hMR0.le
      exact_mod_cast hrank_U
    linarith only [hU_le, hd_div_lt, hlow_div_le]

/-! ## Section 3: RH-Complete Specializations for `tiltedUnitSpline` -/

/-- **RH-Complete Conductor-Average Divergence (`tiltedUnitSpline`).**
Along every overlap schedule `c_N = 2 (log N)^α` (`0 < α < 1 / 2`, covering the entire
RH-complete window `1 / 4 < α < 1 / 2`) and every `0 < θ < 1 / 2`, the conductor average of
`completeWeilEnergy tiltedUnitSpline (2 * log N ^ α) N` over `1 ≤ m ≤ ⌊N^θ⌋₊` diverges to `+∞`. -/
theorem tendsto_tiltedUnitSpline_completeWeil_conductorAverage_atTop
    {α θ : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    Tendsto (fun N : ℕ =>
      (1 / (⌊(N : ℝ) ^ θ⌋₊ : ℝ)) *
        ∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
          completeWeilEnergy tiltedUnitSpline (2 * Real.log N ^ α) N
            (normalizedRamanujanHorizonVector m N))
      atTop atTop := by
  obtain ⟨hc1, hc_lim⟩ := logarithmic_rhComplete_overlap_facts hα0 hα
  exact tendsto_completeWeil_conductorAverage_atTop
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hθ0 hθ hc1 hc_lim

/-- **RH-Complete Conductor Census (`tiltedUnitSpline`).**
Along `c_N = 2 (log N)^α` (`0 < α < 1 / 2`) and `0 < θ < 1 / 2`, almost all conductors
`1 ≤ m ≤ ⌊N^θ⌋₊` have strictly positive `tiltedUnitSpline` complete-Weil energy. -/
theorem tendsto_tiltedUnitSpline_nonpositive_conductor_fraction_zero
    {α θ : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    Tendsto (fun N : ℕ =>
      (((Icc 1 ⌊(N : ℝ) ^ θ⌋₊).filter (fun m =>
        completeWeilEnergy tiltedUnitSpline (2 * Real.log N ^ α) N
          (normalizedRamanujanHorizonVector m N) ≤ 0)).card : ℝ) /
      (⌊(N : ℝ) ^ θ⌋₊ : ℝ)) atTop (𝓝 0) := by
  obtain ⟨hc1, hc_lim⟩ := logarithmic_rhComplete_overlap_facts hα0 hα
  exact tendsto_nonpositive_conductor_fraction_zero
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hθ0 hθ hc1 hc_lim

/-- **RH-Complete Sublinear Negative Index (`tiltedUnitSpline`).**
Along `c_N = 2 (log N)^α` (`0 < α < 1 / 2`) and `0 < θ < 1 / 2`, any family of subspaces
`U N ≤ conductorSubspace ⌊N^θ⌋₊ N` on which `completeWeilEnergy tiltedUnitSpline (2 * log N ^ α) N`
is nonpositive satisfies `finrank ℝ (U N) / ⌊N^θ⌋₊ → 0`, i.e., `κ(W_N|_{V_M}) = o(M)`. -/
theorem tendsto_tiltedUnitSpline_conductorSubspace_negIndex_div_zero
    {α θ : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2) (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (U : ∀ N : ℕ, Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (hU_sub : ∀ N, U N ≤ conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)
    (hU_neg : ∀ N, ∀ u ∈ U N,
      completeWeilEnergy tiltedUnitSpline (2 * Real.log N ^ α) N u ≤ 0) :
    Tendsto (fun N : ℕ => (Module.finrank ℝ (U N) : ℝ) / (⌊(N : ℝ) ^ θ⌋₊ : ℝ)) atTop (𝓝 0) := by
  obtain ⟨hc1, hc_lim⟩ := logarithmic_rhComplete_overlap_facts hα0 hα
  exact tendsto_completeWeil_conductorSubspace_negIndex_div_zero
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hθ0 hθ hc1 hc_lim U hU_sub hU_neg

#print axioms tendsto_completeWeil_conductorAverage_atTop
#print axioms eventually_completeWeil_conductorAverage_pos
#print axioms tendsto_nonpositive_conductor_fraction_zero
#print axioms tendsto_completeWeil_conductorSubspace_negIndex_div_zero
#print axioms tendsto_tiltedUnitSpline_completeWeil_conductorAverage_atTop
#print axioms tendsto_tiltedUnitSpline_nonpositive_conductor_fraction_zero
#print axioms tendsto_tiltedUnitSpline_conductorSubspace_negIndex_div_zero

end GaloisForLFunctions.CompletedArithmeticForms

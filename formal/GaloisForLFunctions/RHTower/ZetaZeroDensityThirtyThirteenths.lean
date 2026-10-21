import GaloisForLFunctions.RHTower.ZetaZeroDensityGuthMaynardBox

/-!
# The zero-density estimate with exponent `30/13`

Guth–Maynard (1.5): under the large values estimate `GuthMaynardLargeValuesBound`, for every
`0 < ε ≤ 1` there are `D, B, T₀` with

`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ D (1 + log T)^B T^{(30/13 + ε)(1 - σ)}`

for all `T ≥ T₀` and all `σ ∈ [1/2, 1]`, counting zeros with multiplicity
(`exists_zeroHeightBox_ncard_le_thirty_thirteenths`).

At a fixed `σ ∈ [1/2, 5/6]` the bound `T^{(30/13)(1-σ) + ε}` comes from

* the global count `O(T log T)` for `σ ≤ 17/30`, where `(30/13)(1 - σ) ≥ 1`;
* Ingham's `3/(2 - σ) ≤ 30/13` for `σ ≤ 7/10` and Huxley's `3/(3σ - 1) ≤ 30/13` for `σ > 8/10`
  (`exists_zeroHeightBox_ncard_le_ingham_huxley`);
* Guth–Maynard's `15(1 - σ)/(3 + 5σ) ≤ (30/13)(1 - σ)` on `[7/10, 8/10]`
  (`exists_zeroHeightBox_ncard_le_gm`).

A finite grid of step `θ` makes these uniform, because the box count is antitone in `σ`; the
grid costs `T^{(30/13)θ}`, absorbed since `1 - σ ≥ 1/6`.  On `[5/6, 1]` the density hypothesis
`exists_zeroHeightBox_ncard_le_density_hypothesis` is already uniform.
-/

set_option autoImplicit false

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve RHTower.GuthMaynard

/-- The box count is antitone in `σ`. -/
theorem zeroHeightBox_ncard_antitone {σ σ' T : ℝ} (hσ : σ ≤ σ') :
    ((zeroHeightBox σ' T).ncard : ℝ) ≤ (zeroHeightBox σ T).ncard := by
  have hsub : zeroHeightBox σ' T ⊆ zeroHeightBox σ T :=
    fun q hq => ⟨le_trans hσ hq.1, hq.2.1, hq.2.2⟩
  exact_mod_cast Set.ncard_le_ncard hsub (zeroHeightBox_finite σ T)

/-- **Uniformity from a finite grid.**  Let `f(σ, T)` be antitone in `σ`, `A ≥ 0`, and suppose
that at every `σ ∈ [σ₁, σ₂]` some `D, B, T₀` give `f(σ, T) ≤ D (1 + log T)^B T^{A(1-σ) + η}` for
`T ≥ T₀`.  Then for every `θ > 0` one choice of `D, B, T₀` gives
`f(σ, T) ≤ D (1 + log T)^B T^{A(1-σ) + η + Aθ}` for all `σ ∈ [σ₁, σ₂]` and `T ≥ T₀`. -/
theorem exists_uniform_of_antitone_of_forall {f : ℝ → ℝ → ℝ} {σ₁ σ₂ A η θ : ℝ}
    (hσ : σ₁ ≤ σ₂) (hA : 0 ≤ A) (hθ : 0 < θ)
    (hanti : ∀ T σ σ', σ ≤ σ' → f σ' T ≤ f σ T)
    (hfix : ∀ σ, σ₁ ≤ σ → σ ≤ σ₂ → ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      f σ T ≤ D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ) + η)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ σ, σ₁ ≤ σ → σ ≤ σ₂ →
      f σ T ≤ D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ) + η + A * θ) := by
  -- the grid points `g k = min (σ₁ + kθ) σ₂`, `k ≤ K`
  have hg : ∀ k : ℕ, σ₁ ≤ min (σ₁ + k * θ) σ₂ ∧ min (σ₁ + k * θ) σ₂ ≤ σ₂ :=
    fun k => ⟨le_min (le_add_of_nonneg_right (by positivity)) hσ, min_le_right _ _⟩
  choose D hD B T₁ hT₁ using fun k : ℕ => hfix _ (hg k).1 (hg k).2
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈(σ₂ - σ₁) / θ⌉₊ := ⟨_, rfl⟩
  have hS0 : 0 ≤ ∑ k ∈ range (K + 1), |T₁ k| := sum_nonneg fun k _ => abs_nonneg (T₁ k)
  refine ⟨∑ k ∈ range (K + 1), D k, sum_nonneg fun k _ => hD k, ∑ k ∈ range (K + 1), B k,
    1 + ∑ k ∈ range (K + 1), |T₁ k|, by linarith, ?_⟩
  intro T hT σ hσ1 hσ2
  have hT1 : 1 ≤ T := le_trans (by linarith) hT
  have hT0 : 0 < T := by linarith
  -- the grid point below `σ`
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌊(σ - σ₁) / θ⌋₊ := ⟨_, rfl⟩
  have hq0 : 0 ≤ (σ - σ₁) / θ := div_nonneg (by linarith) hθ.le
  have hkle : (k : ℝ) * θ ≤ σ - σ₁ := by
    rw [← le_div_iff₀ hθ, hkdef]
    exact Nat.floor_le hq0
  have hkgt : σ - σ₁ < (k + 1) * θ := by
    rw [← div_lt_iff₀ hθ, hkdef]
    exact Nat.lt_floor_add_one _
  have hkK : k ∈ range (K + 1) := by
    rw [mem_range, Nat.lt_succ_iff, hkdef, hK]
    exact le_trans (Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hθ.le))
      (Nat.floor_le_ceil _)
  have hgk : min (σ₁ + k * θ) σ₂ = σ₁ + k * θ := min_eq_left (by linarith)
  have hTk : T₁ k ≤ T :=
    le_trans (le_trans (le_abs_self _) (single_le_sum (fun j _ => abs_nonneg (T₁ j)) hkK))
      (by linarith)
  have h := hT₁ k T hTk
  rw [hgk] at h
  have hl1 : 1 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
  have hDk : D k ≤ ∑ j ∈ range (K + 1), D j := single_le_sum (fun j _ => hD j) hkK
  have hBk : (1 + Real.log T) ^ B k ≤ (1 + Real.log T) ^ (∑ j ∈ range (K + 1), B j) :=
    pow_le_pow_right₀ hl1 (single_le_sum (fun j _ => Nat.zero_le (B j)) hkK)
  have hexp : A * (1 - (σ₁ + k * θ)) + η ≤ A * (1 - σ) + η + A * θ := by
    have : A * (σ - (σ₁ + k * θ)) ≤ A * θ := mul_le_mul_of_nonneg_left (by linarith) hA
    linarith
  have hTe := Real.rpow_le_rpow_of_exponent_le hT1 hexp
  have hl0 : 0 ≤ 1 + Real.log T := by linarith
  calc f σ T ≤ f (σ₁ + k * θ) T := hanti T _ _ (by linarith)
    _ ≤ D k * (1 + Real.log T) ^ B k * T ^ (A * (1 - (σ₁ + k * θ)) + η) := h
    _ ≤ (∑ j ∈ range (K + 1), D j) * (1 + Real.log T) ^ (∑ j ∈ range (K + 1), B j) *
          T ^ (A * (1 - σ) + η + A * θ) :=
        mul_le_mul (mul_le_mul hDk hBk (pow_nonneg hl0 _) (le_trans (hD k) hDk)) hTe
          (Real.rpow_nonneg hT0.le _) (mul_nonneg (le_trans (hD k) hDk) (pow_nonneg hl0 _))

/-- The global count at a fixed `σ ≤ 17/30`: `O(T log T) ≤ O((1 + log T) T^{(30/13)(1-σ)})`. -/
theorem exists_zeroHeightBox_ncard_le_global_thirty_thirteenths :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {σ T : ℝ}, 1 / 2 ≤ σ → σ ≤ 17 / 30 → 4 ≤ T →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ 1 * T ^ ((30 / 13) * (1 - σ)) := by
  obtain ⟨Cg, hCg, hglob⟩ := exists_ncard_zeroHeightBox_le_global
  refine ⟨9 * Cg, by positivity, fun {σ T} hσ1 hσ2 hT4 => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlogT := Real.log_nonneg hT1
  have hlog25 : Real.log (2 * T + 5) ≤ 3 * (1 + Real.log T) := by
    have h := Real.log_le_log (by linarith) (show 2 * T + 5 ≤ 4 * T by linarith)
    rw [Real.log_mul (by norm_num) hT0.ne'] at h
    have h4 : Real.log 4 ≤ 2 := by
      have h2 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_lt_d9]
    linarith
  have hTpow : T ≤ T ^ ((30 / 13) * (1 - σ)) := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ ((30 / 13) * (1 - σ)) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (one_le_thirty_thirteenths_mul hσ2)
  calc ((zeroHeightBox σ T).ncard : ℝ) ≤ Cg * (2 * T + 4) * Real.log (2 * T + 5) := hglob hσ1 hT1
    _ ≤ Cg * (3 * T) * (3 * (1 + Real.log T)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCg.le) hlog25
          (Real.log_nonneg (by linarith)) (by positivity)
    _ = 9 * Cg * (1 + Real.log T) ^ 1 * T := by ring
    _ ≤ 9 * Cg * (1 + Real.log T) ^ 1 * T ^ ((30 / 13) * (1 - σ)) :=
        mul_le_mul_of_nonneg_left hTpow (mul_nonneg (by positivity) (pow_nonneg (by linarith) 1))

/-- **The exponent `30/13` at a fixed `σ ∈ [1/2, 5/6]`.**  Under the large values estimate,
for `0 < ε ≤ 1` there are `D, B, T₀` with
`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ D (1 + log T)^B T^{(30/13)(1-σ) + ε}` for `T ≥ T₀`. -/
theorem exists_zeroHeightBox_ncard_le_fixed_thirty_thirteenths (hGM : GuthMaynardLargeValuesBound)
    {σ ε : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 6) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D * (1 + Real.log T) ^ B * T ^ ((30 / 13) * (1 - σ) + ε) := by
  -- raising the exponent of `T` in `D (1 + log T)^B T^e`
  have hraise : ∀ {D T e e' : ℝ} {B : ℕ}, 0 ≤ D → 1 ≤ T → e ≤ e' →
      D * (1 + Real.log T) ^ B * T ^ e ≤ D * (1 + Real.log T) ^ B * T ^ e' :=
    fun hD hT he => mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT he)
      (mul_nonneg hD (pow_nonneg (by linarith [Real.log_nonneg hT]) _))
  by_cases hlow : σ ≤ 17 / 30
  · -- the global count
    obtain ⟨D, hD, hglob⟩ := exists_zeroHeightBox_ncard_le_global_thirty_thirteenths
    exact ⟨D, hD, 1, 4, fun T hT =>
      le_trans (hglob hσ0 hlow hT) (hraise hD (by linarith) (by linarith))⟩
  by_cases hmid : 7 / 10 ≤ σ ∧ σ ≤ 8 / 10
  · -- Guth–Maynard
    obtain ⟨D, hD, T₀, hT₀, hbox⟩ := exists_zeroHeightBox_ncard_le_gm hGM hmid.1 hmid.2 hε
    refine ⟨D, hD, 12, T₀, fun T hT => le_trans (hbox T hT) (hraise hD (le_trans hT₀ hT) ?_)⟩
    linarith [gmDensityExponent_le_thirty_thirteenths hmid.1 (by linarith)]
  · -- Ingham and Huxley
    have hσh : 1 / 2 < σ := by linarith
    obtain ⟨D, hD, B, T₀, hT₀, hbox⟩ :=
      exists_zeroHeightBox_ncard_le_ingham_huxley hσh (by linarith) hε hε1
    refine ⟨D, hD, B, T₀, fun T hT => le_trans (hbox T hT) (hraise hD (le_trans hT₀ hT) ?_)⟩
    have hA : inghamHuxleyExponent σ ≤ 30 / 13 := by
      unfold inghamHuxleyExponent
      rcases not_and_or.mp hmid with h | h
      · rw [if_pos (by linarith)]
        exact ingham_exponent_le_thirty_thirteenths (by linarith)
      · rw [if_neg (by linarith), if_pos hσ1]
        exact huxley_exponent_le_thirty_thirteenths (by linarith)
    have h1 : inghamHuxleyExponent σ * (1 - σ) ≤ (30 / 13) * (1 - σ) :=
      mul_le_mul_of_nonneg_right hA (by linarith)
    have h2 : ε * (1 - σ) ≤ ε := mul_le_of_le_one_right hε.le (by linarith)
    linarith

/-- **Guth–Maynard's zero-density estimate with exponent `30/13`.**  Under the large values
estimate, for every `0 < ε ≤ 1` there are `D ≥ 0`, `B` and `T₀ ≥ 1` such that for all `T ≥ T₀`
and all `σ ∈ [1/2, 1]`,
`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ D (1 + log T)^B T^{(30/13 + ε)(1 - σ)}`. -/
theorem exists_zeroHeightBox_ncard_le_thirty_thirteenths (hGM : GuthMaynardLargeValuesBound)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ →
      σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ ((30 / 13 + ε) * (1 - σ)) := by
  -- `[1/2, 5/6]`: the grid with step `θ = 13ε/360`
  obtain ⟨D₁, hD₁, B₁, T₁, hT₁, hlow⟩ := exists_uniform_of_antitone_of_forall
    (f := fun σ T => ((zeroHeightBox σ T).ncard : ℝ)) (σ₁ := 1 / 2) (σ₂ := 5 / 6)
    (A := 30 / 13) (η := ε / 12) (θ := 13 * ε / 360) (by norm_num) (by norm_num) (by positivity)
    (fun T σ σ' h => zeroHeightBox_ncard_antitone h)
    (fun σ h1 h2 => exists_zeroHeightBox_ncard_le_fixed_thirty_thirteenths hGM h1 h2
      (by positivity) (by linarith))
  -- `[5/6, 1]`: the density hypothesis
  obtain ⟨D₂, hD₂, T₂, hT₂, hhigh⟩ := exists_zeroHeightBox_ncard_le_density_hypothesis hε hε1
  refine ⟨D₁ + D₂, by positivity, B₁ + (dhLogExponent ε + 4), max T₁ T₂, le_trans hT₁
    (le_max_left _ _), fun T hT σ hσ0 hσ1 => ?_⟩
  have hT1 : 1 ≤ T := le_trans hT₁ (le_trans (le_max_left _ _) hT)
  have hl1 : 1 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
  have hTe : 0 ≤ T ^ ((30 / 13 + ε) * (1 - σ)) := Real.rpow_nonneg (by linarith) _
  -- enlarging the constant and the logarithmic power
  have hgrow : ∀ {D e : ℝ} {B : ℕ}, 0 ≤ D → D ≤ D₁ + D₂ → B ≤ B₁ + (dhLogExponent ε + 4) →
      e ≤ (30 / 13 + ε) * (1 - σ) → D * (1 + Real.log T) ^ B * T ^ e
        ≤ (D₁ + D₂) * (1 + Real.log T) ^ (B₁ + (dhLogExponent ε + 4)) *
          T ^ ((30 / 13 + ε) * (1 - σ)) :=
    fun hD hDD hB he => mul_le_mul (mul_le_mul hDD (pow_le_pow_right₀ hl1 hB)
      (pow_nonneg (by linarith) _) (by positivity)) (Real.rpow_le_rpow_of_exponent_le hT1 he)
      (Real.rpow_nonneg (by linarith) _) (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
  by_cases hσ56 : σ ≤ 5 / 6
  · refine le_trans (hlow T (le_trans (le_max_left _ _) hT) σ hσ0 hσ56)
      (hgrow hD₁ (by linarith) (by omega) ?_)
    have h6 : ε * (1 / 6) ≤ ε * (1 - σ) := mul_le_mul_of_nonneg_left (by linarith) hε.le
    linarith
  · refine le_trans (hhigh T (le_trans (le_max_right _ _) hT) σ (by linarith) hσ1)
      (hgrow hD₂ (by linarith) (by omega) ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)

end RHTower

end

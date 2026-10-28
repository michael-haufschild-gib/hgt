import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.AMarginNeedsHarmonicCorrelation
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo

/-!
# Full correlation keeps the margin

For a sign gauge `ω² = 1` the margin is read on `ζ`'s hyperplane `x ⟂ b`, `b_n = n^{−1/2}`, through
`P_N(ωx)`. With `y = ωx` this is the prime form on the hyperplane `y ⟂ ωb`. When `ω` agrees with
`1` on a set of full harmonic density, `ωb` is nearly `b`, and the sharp gap of `ζ` survives.

* **Pole splitting** (`poleCoord`, `poleResidual`, `atomicWeilForm_eq_poleSplit`): `y = αb + z`
  with `z ⟂ b`, and `P_N(y) = α²P_N(b) + P_N(z) + 2α Σ_n R_n b_n z_n`, with rows `R_n` within a
  constant `B` of `log N − γ` (RenormalizedArithmeticPotentialTheory).
* **The row cost** (`two_mul_poleCoord_mul_cross_le`): `2α Σ R_n b_n z_n ≤ α²H/t + tB²|z|²`.
* **The misalignment cost** (`sq_sum_mul_truncPole_le`): for `y ⟂ ωb`,
  `⟨y, b⟩² ≤ |y|² · 2(H_N − S_N)`, where `S_N = Σ ω(n)/n` and `H_N = Σ 1/n`.
* **Full correlation keeps the margin** (`hasHyperplaneGap_two_mul_log_two_of_correlation`): if
  `S_N/H_N → 1`, the gauge has hyperplane gap `2 log 2`. The sharp gap pays `z`, the ceiling pays
  `αb`, and `α²H ≤ |y|² · 2(1 − S_N/H_N) → 0` (`fullCorrelation_arith`).
* **Finite flips keep the margin** (`hasHyperplaneGap_two_mul_log_two_of_eventually_eq_one`): a
  sign gauge equal to `1` beyond some point has gap `2 log 2`.

With `AMarginNeedsHarmonicCorrelation` the margin is decided at both ends by the harmonic
correlation `S_N/H_N`: `2 log 2` when it tends to `1`, `0` when `S_N² = o(log N)`.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

/-- **Pole polarization**: `P_N(αb + z) = α²P_N(b) + P_N(z) + 2α Σ_n R_n b_n z_n`. -/
theorem atomicWeilForm_smul_truncPole_add (N : ℕ) (α : ℝ) (z : ℕ → ℝ) :
    atomicWeilForm N (fun n => α * truncPole N n + z n) =
      α ^ 2 * atomicWeilForm N (truncPole N) + atomicWeilForm N z +
        2 * α * ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * z n := by
  rcases eq_or_ne α 0 with rfl | hα
  · simp
  · have h := atomicWeilForm_truncPole_add N (fun n => α⁻¹ * z n)
    have e : (fun n => α * truncPole N n + z n) =
        fun n => α * (fun n => truncPole N n + α⁻¹ * z n) n := by
      funext n
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hα, one_mul]
    rw [e, atomicWeilForm_smul, h, atomicWeilForm_smul]
    have hs : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * (α⁻¹ * z n) =
        α⁻¹ * ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * z n := by
      rw [mul_sum]
      exact sum_congr rfl fun n _ => by ring
    rw [hs, inv_pow]
    field_simp

/-- The pole coordinate `α(y) = ⟨y, b⟩/H_N`. -/
def poleCoord (N : ℕ) (y : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Icc 1 N, y n * truncPole N n) / gaugeHarmonicSum (fun _ => 1) N

/-- The part of `y` orthogonal to the pole: `z = y − α(y) b`. -/
def poleResidual (N : ℕ) (y : ℕ → ℝ) (n : ℕ) : ℝ := y n - poleCoord N y * truncPole N n

section PoleSplit

variable {N : ℕ}

local notation "𝓗" => gaugeHarmonicSum (fun _ => 1) N

theorem poleCoord_mul (hN : 1 ≤ N) (y : ℕ → ℝ) :
    poleCoord N y * 𝓗 = ∑ n ∈ Icc 1 N, y n * truncPole N n :=
  div_mul_cancel₀ _ (gaugeHarmonicSum_one_pos hN).ne'

theorem sum_poleResidual_mul_truncPole (hN : 1 ≤ N) (y : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, poleResidual N y n * truncPole N n = 0 := by
  calc ∑ n ∈ Icc 1 N, poleResidual N y n * truncPole N n
      = ∑ n ∈ Icc 1 N, (y n * truncPole N n - poleCoord N y * truncPole N n ^ 2) :=
        sum_congr rfl fun n _ => by rw [poleResidual]; ring
    _ = ∑ n ∈ Icc 1 N, y n * truncPole N n - poleCoord N y * 𝓗 := by
        rw [sum_sub_distrib, ← mul_sum, sum_truncPole_sq]
    _ = 0 := by rw [poleCoord_mul hN, sub_self]

/-- The residual lies on the pole hyperplane. -/
theorem sum_poleResidual_div_sqrt (hN : 1 ≤ N) (y : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, poleResidual N y n / Real.sqrt n = 0 := by
  rw [← sum_poleResidual_mul_truncPole hN y]
  exact sum_congr rfl fun n hn => by rw [truncPole_eq hn, mul_one_div]

/-- Pythagoras: `|z|² = |y|² − α²H_N`. -/
theorem sum_poleResidual_sq (hN : 1 ≤ N) (y : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, poleResidual N y n ^ 2 = ∑ n ∈ Icc 1 N, y n ^ 2 - poleCoord N y ^ 2 * 𝓗 := by
  calc ∑ n ∈ Icc 1 N, poleResidual N y n ^ 2
      = ∑ n ∈ Icc 1 N, (y n ^ 2 - 2 * poleCoord N y * (y n * truncPole N n) +
          poleCoord N y ^ 2 * truncPole N n ^ 2) :=
        sum_congr rfl fun n _ => by rw [poleResidual]; ring
    _ = ∑ n ∈ Icc 1 N, y n ^ 2 - 2 * poleCoord N y * ∑ n ∈ Icc 1 N, y n * truncPole N n +
          poleCoord N y ^ 2 * 𝓗 := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_truncPole_sq]
    _ = ∑ n ∈ Icc 1 N, y n ^ 2 - poleCoord N y ^ 2 * 𝓗 := by
        rw [← poleCoord_mul hN y]; ring

/-- **Pole splitting**: `P_N(y) = α²P_N(b) + P_N(z) + 2α Σ_n R_n b_n z_n`. -/
theorem atomicWeilForm_eq_poleSplit (y : ℕ → ℝ) :
    atomicWeilForm N y = poleCoord N y ^ 2 * atomicWeilForm N (truncPole N) +
      atomicWeilForm N (poleResidual N y) + 2 * poleCoord N y *
        ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * poleResidual N y n := by
  have h := atomicWeilForm_smul_truncPole_add N (poleCoord N y) (poleResidual N y)
  have e : (fun n => poleCoord N y * truncPole N n + poleResidual N y n) = y :=
    funext fun n => by rw [poleResidual]; ring
  rwa [e] at h

/-- **The row cost**: since `z ⟂ b`, only the row deviations `R_n − (log N − γ)`, bounded by `B`,
couple `αb` to `z`; for every `t > 0` they cost at most `α²H/t + tB²|z|²`. -/
theorem two_mul_poleCoord_mul_cross_le (hN : 1 ≤ N) (y : ℕ → ℝ) {t : ℝ} (ht : 0 < t) :
    2 * poleCoord N y *
        ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * poleResidual N y n ≤
      poleCoord N y ^ 2 * 𝓗 / t +
        t * (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 * ∑ n ∈ Icc 1 N, poleResidual N y n ^ 2 := by
  have hzb := sum_poleResidual_mul_truncPole hN y
  have hsplit : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n *
        poleResidual N y n =
      ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n - (Real.log N - γ)) * truncPole N n *
        poleResidual N y n := by
    have : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * poleResidual N y n -
        ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n - (Real.log N - γ)) * truncPole N n *
          poleResidual N y n =
        (Real.log N - γ) * ∑ n ∈ Icc 1 N, poleResidual N y n * truncPole N n := by
      rw [← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    rw [hzb, mul_zero] at this
    linarith only [this]
  -- pointwise `2xy ≤ x²/t + ty²`
  have hpt : ∀ n ∈ Icc 1 N, 2 * poleCoord N y * ((mertensSum (N / n) + Real.log n -
      (Real.log N - γ)) * truncPole N n * poleResidual N y n) ≤
      poleCoord N y ^ 2 * truncPole N n ^ 2 / t +
        t * (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 * poleResidual N y n ^ 2 := by
    intro n hn
    have hR : |mertensSum (N / n) + Real.log n - (Real.log N - γ)| ≤
        Real.log 4 + 4 + Real.log 2 + γ := abs_row_sub_le hn
    have h1 : 2 * poleCoord N y * ((mertensSum (N / n) + Real.log n - (Real.log N - γ)) *
        truncPole N n * poleResidual N y n) ≤
        2 * (|poleCoord N y| * |truncPole N n|) *
          ((Real.log 4 + 4 + Real.log 2 + γ) * |poleResidual N y n|) := by
      calc _ ≤ |2 * poleCoord N y * ((mertensSum (N / n) + Real.log n - (Real.log N - γ)) *
            truncPole N n * poleResidual N y n)| := le_abs_self _
        _ = 2 * (|poleCoord N y| * |truncPole N n|) *
            (|mertensSum (N / n) + Real.log n - (Real.log N - γ)| * |poleResidual N y n|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]; ring
        _ ≤ _ := by gcongr
    have h2 := sq_nonneg (|poleCoord N y| * |truncPole N n| -
      t * ((Real.log 4 + 4 + Real.log 2 + γ) * |poleResidual N y n|))
    have e2 : (|poleCoord N y| * |truncPole N n| -
        t * ((Real.log 4 + 4 + Real.log 2 + γ) * |poleResidual N y n|)) ^ 2 =
        poleCoord N y ^ 2 * truncPole N n ^ 2 - 2 * (|poleCoord N y| * |truncPole N n|) *
          ((Real.log 4 + 4 + Real.log 2 + γ) * |poleResidual N y n|) * t +
          t * (t * (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 * poleResidual N y n ^ 2) := by
      calc _ = |poleCoord N y| ^ 2 * |truncPole N n| ^ 2 - 2 * (|poleCoord N y| *
            |truncPole N n|) * ((Real.log 4 + 4 + Real.log 2 + γ) * |poleResidual N y n|) * t +
            t * (t * (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 * |poleResidual N y n| ^ 2) := by ring
        _ = _ := by rw [sq_abs, sq_abs, sq_abs]
    rw [e2] at h2
    have h3 : 2 * (|poleCoord N y| * |truncPole N n|) *
        ((Real.log 4 + 4 + Real.log 2 + γ) * |poleResidual N y n|) * t ≤
        (poleCoord N y ^ 2 * truncPole N n ^ 2 / t +
          t * (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 * poleResidual N y n ^ 2) * t := by
      rw [add_mul (poleCoord N y ^ 2 * truncPole N n ^ 2 / t), div_mul_cancel₀ _ ht.ne']
      linarith only [h2]
    linarith only [h1, le_of_mul_le_mul_right h3 ht]
  rw [hsplit, mul_sum]
  calc _ ≤ ∑ n ∈ Icc 1 N, (poleCoord N y ^ 2 * truncPole N n ^ 2 / t +
        t * (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 * poleResidual N y n ^ 2) := sum_le_sum hpt
    _ = _ := by rw [sum_add_distrib, ← sum_div, ← mul_sum, ← mul_sum, sum_truncPole_sq]

end PoleSplit

/-- **The misalignment cost.** If `Σ y_n ω_n b_n = 0` with `ω² = 1`, then
`⟨y, b⟩² ≤ |y|² · 2(H_N − S_N)`. -/
theorem sq_sum_mul_truncPole_le {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1) (N : ℕ) {y : ℕ → ℝ}
    (hy : ∑ n ∈ Icc 1 N, y n * (ω n * truncPole N n) = 0) :
    (∑ n ∈ Icc 1 N, y n * truncPole N n) ^ 2 ≤
      (∑ n ∈ Icc 1 N, y n ^ 2) *
        (2 * (gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum ω N)) := by
  have e : ∑ n ∈ Icc 1 N, y n * truncPole N n =
      ∑ n ∈ Icc 1 N, y n * ((1 - ω n) * truncPole N n) := by
    rw [← sub_zero (∑ n ∈ Icc 1 N, y n * truncPole N n), ← hy, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  have hd : ∑ n ∈ Icc 1 N, ((1 - ω n) * truncPole N n) ^ 2 =
      2 * (gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum ω N) := by
    simp only [gaugeHarmonicSum]
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [mul_pow, truncPole_sq hn]
    have h1 : (1 - ω n) ^ 2 = 2 - 2 * ω n := by linear_combination hω n
    rw [h1]
    ring
  rw [e, ← hd]
  exact sum_mul_sq_le_sq_mul_sq _ _ _

/-- **The arithmetic of full correlation.** With `a = α²`, the pole splitting, the ceiling for the
pole, the sharp gap for the residual, the row cost and the misalignment `aH ≤ δY` give
`P(y) ≤ (L − γ − 2 log 2 + ε)Y`. -/
theorem fullCorrelation_arith {L g l2 ε ε₁ t B δ H Y a Pb Pz E PY : ℝ} (hε : 0 < ε)
    (hl2 : 0 < l2) (ht : 0 < t) (ha : 0 ≤ a) (hH : 0 < H) (hY : 0 ≤ Y)
    (hPY : PY = a * Pb + Pz + E) (hPb : Pb ≤ (L - g + ε₁) * H)
    (hPz : Pz ≤ (L - g - 2 * l2 + ε / 4) * (Y - a * H))
    (hE : E ≤ a * H / t + t * B ^ 2 * (Y - a * H)) (haH : a * H ≤ Y * δ)
    (htB : t * B ^ 2 ≤ ε / 4) (hcδ : (2 * l2 + 1 / t) * δ = ε / 4) (hε₁ : ε₁ ≤ ε / 4) :
    PY ≤ (L - g - 2 * l2 + ε) * Y := by
  have haH0 : 0 ≤ a * H := mul_nonneg ha hH.le
  have hB2 : 0 ≤ t * B ^ 2 := mul_nonneg ht.le (sq_nonneg B)
  have hc : 0 ≤ 2 * l2 + 1 / t := by have := one_div_pos.mpr ht; linarith only [hl2, this]
  have h1 : a * Pb ≤ a * ((L - g + ε₁) * H) := mul_le_mul_of_nonneg_left hPb ha
  have h2a : t * B ^ 2 * (Y - a * H) ≤ t * B ^ 2 * Y :=
    mul_le_mul_of_nonneg_left (by linarith only [haH0]) hB2
  have h2b : t * B ^ 2 * Y ≤ ε / 4 * Y := mul_le_mul_of_nonneg_right htB hY
  have h3 : (2 * l2 + 1 / t) * (a * H) ≤ ε / 4 * Y := by
    calc (2 * l2 + 1 / t) * (a * H) ≤ (2 * l2 + 1 / t) * (Y * δ) :=
          mul_le_mul_of_nonneg_left haH hc
      _ = ε / 4 * Y := by rw [← hcδ]; ring
  have h4 : (ε₁ - ε / 4) * (a * H) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith only [hε₁]) haH0
  have h5 : a * H / t = 1 / t * (a * H) := by ring
  have h6 : 0 ≤ ε / 4 * Y := mul_nonneg (by linarith only [hε]) hY
  linarith only [hPY, h1, hPz, hE, h2a, h2b, h3, h4, h5, h6]

/-- **Full correlation keeps the margin.** A sign gauge whose harmonic correlation with `ζ` tends
to `1`, `S_N/H_N → 1`, has hyperplane gap `2 log 2`. -/
theorem hasHyperplaneGap_two_mul_log_two_of_correlation {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hS : Tendsto (fun N : ℕ => gaugeHarmonicSum ω N / gaugeHarmonicSum (fun _ => 1) N) atTop
      (𝓝 1)) :
    HasHyperplaneGap ω (2 * Real.log 2) := by
  intro ε hε
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the weight of the row cost, and the admissible misalignment
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = ε / (4 * ((Real.log 4 + 4 + Real.log 2 + γ) ^ 2 + 1)) :=
    ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; positivity
  have htB : t * (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 ≤ ε / 4 := by
    have h1 : t * ((Real.log 4 + 4 + Real.log 2 + γ) ^ 2 + 1) = ε / 4 := by
      rw [ht_def]; field_simp
    have h2 := mul_le_mul_of_nonneg_left
      (show (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 ≤ (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 + 1
        by linarith only) ht.le
    linarith only [h1, h2]
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 2 * Real.log 2 + 1 / t := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; have := one_div_pos.mpr ht; linarith only [hl2, this]
  have hc0 := hc.ne'
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = ε / (4 * c) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδ_def]; positivity
  have hcδ : (2 * Real.log 2 + 1 / t) * δ = ε / 4 := by
    rw [← hc_def, hδ_def]; field_simp
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hS.eventually (Ioi_mem_nhds (show 1 - δ / 2 < 1 by linarith only [hδ])))
  obtain ⟨N₂, hN₂⟩ := eventually_atomicWeilForm_le_two_log_two (show 0 < ε / 4 by positivity)
  obtain ⟨ε₁, hε₁_def⟩ : ∃ ε₁ : ℝ, ε₁ = min (ε / 4) (1 / 2) := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁_def]; exact lt_min (by positivity) (by norm_num)
  have hε₁4 : ε₁ ≤ ε / 4 := by rw [hε₁_def]; exact min_le_left _ _
  have hε₁2 : ε₁ ≤ 1 / 2 := by rw [hε₁_def]; exact min_le_right _ _
  obtain ⟨N₃, hN₃⟩ := eventually_atomicWeilForm_add_poleDefect_le hε₁
  refine ⟨max N₁ (max N₂ (max N₃ 1)), fun N hN x hx => ?_⟩
  have hN1' : N₁ ≤ N := le_of_max_le_left hN
  have hN2' : N₂ ≤ N := (le_max_left _ _).trans (le_of_max_le_right hN)
  have hN3' : N₃ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_of_max_le_right hN)
  have hN1 : 1 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_of_max_le_right hN)
  have hH0 := gaugeHarmonicSum_one_pos hN1
  -- `y = ωx` has the mass of `x` and lies on the hyperplane `y ⟂ ωb`
  have hyy : ∑ n ∈ Icc 1 N, (ω n * x n) ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 :=
    sum_congr rfl fun n _ => by rw [mul_pow, sq (ω n), hω, one_mul]
  have hY : 0 ≤ ∑ n ∈ Icc 1 N, (ω n * x n) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hyω : ∑ n ∈ Icc 1 N, (ω n * x n) * (ω n * truncPole N n) = 0 := by
    rw [← hx]
    refine sum_congr rfl fun n hn => ?_
    rw [truncPole_eq hn]
    linear_combination (x n / Real.sqrt n) * hω n
  -- the misalignment: `α²H ≤ δ|y|²`
  have haH : poleCoord N (fun n => ω n * x n) ^ 2 * gaugeHarmonicSum (fun _ => 1) N ≤
      (∑ n ∈ Icc 1 N, (ω n * x n) ^ 2) * δ := by
    have hD : 2 * (gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum ω N) ≤
        δ * gaugeHarmonicSum (fun _ => 1) N := by
      have h : 1 - δ / 2 < gaugeHarmonicSum ω N / gaugeHarmonicSum (fun _ => 1) N := hN₁ N hN1'
      rw [lt_div_iff₀ hH0] at h
      linarith only [h]
    have hp := sq_sum_mul_truncPole_le hω N hyω
    rw [← poleCoord_mul hN1 (fun n => ω n * x n)] at hp
    have h2 : poleCoord N (fun n => ω n * x n) ^ 2 * gaugeHarmonicSum (fun _ => 1) N *
        gaugeHarmonicSum (fun _ => 1) N ≤
        (∑ n ∈ Icc 1 N, (ω n * x n) ^ 2) * δ * gaugeHarmonicSum (fun _ => 1) N := by
      calc _ = (poleCoord N (fun n => ω n * x n) * gaugeHarmonicSum (fun _ => 1) N) ^ 2 := by ring
        _ ≤ _ := hp
        _ ≤ (∑ n ∈ Icc 1 N, (ω n * x n) ^ 2) * (δ * gaugeHarmonicSum (fun _ => 1) N) :=
            mul_le_mul_of_nonneg_left hD hY
        _ = _ := by ring
    exact le_of_mul_le_mul_right h2 hH0
  -- the ceiling pays the pole, the sharp gap pays the residual
  have hPb : atomicWeilForm N (truncPole N) ≤
      (Real.log N - γ + ε₁) * gaugeHarmonicSum (fun _ => 1) N := by
    have h := hN₃ N hN3' (truncPole N)
    rw [sum_truncPole_sq] at h
    have := mul_nonneg (show (0 : ℝ) ≤ 1 - ε₁ by linarith only [hε₁2])
      (poleDefect_nonneg N (truncPole N))
    linarith only [h, this]
  have hPz := hN₂ N hN2' _ (sum_poleResidual_div_sqrt hN1 (fun n => ω n * x n))
  rw [sum_poleResidual_sq hN1] at hPz
  have hE := two_mul_poleCoord_mul_cross_le hN1 (fun n => ω n * x n) ht
  rw [sum_poleResidual_sq hN1] at hE
  rw [← hyy]
  exact fullCorrelation_arith hε hl2 ht (sq_nonneg _) hH0 hY
    (atomicWeilForm_eq_poleSplit _) hPb hPz hE haH htB hcδ hε₁4

/-- **Finite flips keep the margin**: a sign gauge equal to `1` from some point on has hyperplane
gap `2 log 2`. -/
theorem hasHyperplaneGap_two_mul_log_two_of_eventually_eq_one {ω : ℕ → ℝ}
    (hω : ∀ n, ω n * ω n = 1) {M : ℕ} (hM : ∀ n, M ≤ n → ω n = 1) :
    HasHyperplaneGap ω (2 * Real.log 2) := by
  refine hasHyperplaneGap_two_mul_log_two_of_correlation hω ?_
  have hHnn : ∀ N : ℕ, 0 ≤ gaugeHarmonicSum (fun _ => 1) N :=
    fun N => sum_nonneg fun _ _ => by positivity
  -- `H_N − S_N` is bounded by `C = 2 H_M`
  have hdiff : ∀ N : ℕ, |gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum ω N| ≤
      2 * gaugeHarmonicSum (fun _ => 1) M := by
    intro N
    have hle : ∀ n ∈ Icc 1 N, |(1 : ℝ) / n - ω n / n| ≤ if n ≤ M then 2 / (n : ℝ) else 0 := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      split_ifs with h
      · rw [← sub_div, abs_div, abs_of_pos hn0]
        refine div_le_div_of_nonneg_right ?_ hn0.le
        calc |1 - ω n| ≤ |(1 : ℝ)| + |ω n| := abs_sub _ _
          _ = 2 := by rw [abs_one, abs_eq_one_of_mul_self_eq_one (hω n)]; norm_num
      · rw [hM n (by omega), sub_self, abs_zero]
    simp only [gaugeHarmonicSum]
    calc |∑ n ∈ Icc 1 N, (1 : ℝ) / n - ∑ n ∈ Icc 1 N, ω n / n|
        = |∑ n ∈ Icc 1 N, ((1 : ℝ) / n - ω n / n)| := by rw [sum_sub_distrib]
      _ ≤ ∑ n ∈ Icc 1 N, |(1 : ℝ) / n - ω n / n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, (if n ≤ M then 2 / (n : ℝ) else 0) := sum_le_sum hle
      _ ≤ ∑ n ∈ Icc 1 M, 2 / (n : ℝ) := by
        rw [← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => by positivity)
        simp only [mem_filter, mem_Icc] at hn ⊢
        omega
      _ = 2 * ∑ n ∈ Icc 1 M, (1 : ℝ) / n := by
        rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
  -- `H_N → ∞`
  have hHtop : Tendsto (fun N : ℕ => gaugeHarmonicSum (fun _ => 1) N) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
    have h := log_add_one_le_harmonic N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simp only [gaugeHarmonicSum, Function.comp_apply, one_div]
    exact h
  -- `(H_N − S_N)/H_N → 0`
  have hq : Tendsto (fun N : ℕ => (gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum ω N) /
      gaugeHarmonicSum (fun _ => 1) N) atTop (𝓝 0) := by
    have hC : Tendsto (fun N : ℕ => 2 * gaugeHarmonicSum (fun _ => 1) M *
        (gaugeHarmonicSum (fun _ => 1) N)⁻¹) atTop (𝓝 0) := by
      simpa using hHtop.inv_tendsto_atTop.const_mul (2 * gaugeHarmonicSum (fun _ => 1) M)
    refine squeeze_zero_norm (fun N => ?_) hC
    rw [Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_nonneg (inv_nonneg.mpr (hHnn N))]
    exact mul_le_mul_of_nonneg_right (hdiff N) (inv_nonneg.mpr (hHnn N))
  -- `S_N/H_N = 1 − (H_N − S_N)/H_N` for `N ≥ 1`
  have hev : (fun N : ℕ => 1 - (gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum ω N) /
      gaugeHarmonicSum (fun _ => 1) N) =ᶠ[atTop]
      fun N : ℕ => gaugeHarmonicSum ω N / gaugeHarmonicSum (fun _ => 1) N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h0 := (gaugeHarmonicSum_one_pos hN).ne'
    rw [eq_div_iff h0, sub_mul, div_mul_cancel₀ _ h0]
    ring
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub hq
  rw [sub_zero] at h1
  exact h1.congr' hev

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsTwiceTheMertensLimit

/-!
# The finite part is the harmonic mean of the Mertens error

A gauge whose Mertens error converges, `A_ε(y) − κ log y → α`, has finite part `2α`
(`exists_abs_primeBilinear_gaugeTrunc_finitePart_le`). This file proves the exact converse on the
pole: the finite part exists if and only if the Mertens error has a harmonic mean.

* **The diagonal Gram** (`primeBilinear_gaugeTrunc_self_eq`):
  `⟨εu^{(M)}, P εu^{(M)}⟩ = 2 Σ_{m ≤ M} A_ε(⌊M/m⌋)/m`.
* **The logarithmic part is `o(H_M)`** (`exists_abs_sum_log_floor_sub_harmonicSq_le`):
  `2 Σ_{m ≤ M} log⌊M/m⌋/m = H_M² + o(H_M)`. This is read off `ζ`: its pole Gram is
  `H_M² − 2γ H_M + o(H_M)` (RP10) and its Mertens error converges to `−γ`.
* **The finite-part criterion** (`gaugePole_finitePart_iff`): for every sign gauge and `|κ| ≤ 1`,
  `⟨εu^{(M)}, P εu^{(M)}⟩ = κ H_M² + 2α H_M + o(H_M)` if and only if
  `Σ_{m ≤ M} E(⌊M/m⌋)/m = α H_M + o(H_M)`, `E = A_ε − κ log`.

So the finite part of a gauge on its pole is the harmonic mean of its Mertens error: convergence of
the error (RP30) is the Abelian sufficient condition, and the harmonic mean is necessary and
sufficient.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

variable {ε : ℕ → ℝ}

/-- **The diagonal Gram**: `⟨εu^{(M)}, P εu^{(M)}⟩ = 2 Σ_{m ≤ M} A_ε(⌊M/m⌋)/m`. -/
theorem primeBilinear_gaugeTrunc_self_eq (hε : IsSignGauge ε) (M : ℕ) :
    primeBilinear M (gaugeTrunc ε M) (gaugeTrunc ε M) =
      2 * ∑ m ∈ Icc 1 M, gaugeMertensSum ε (M / m) / m := by
  rw [primeBilinear_gaugeTrunc_eq_sum hε le_rfl le_rfl, mul_sum]
  exact sum_congr rfl fun m _ => by ring

/-- **The logarithmic part is `o(H_M)`**: for every `η > 0` there is `C` with
`|2 Σ_{m ≤ M} log⌊M/m⌋/m − H_M²| ≤ η H_M + C` for `M ≥ 1`. -/
theorem exists_abs_sum_log_floor_sub_harmonicSq_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M →
      |2 * ∑ m ∈ Icc 1 M, Real.log ((M / m : ℕ) : ℝ) / m - harmonicSum M ^ 2| ≤
        η * harmonicSum M + C := by
  obtain ⟨C₁, hC₁⟩ := exists_abs_primeBilinear_truncPole_finitePart_le (η := η / 2) (by positivity)
  have hD : Tendsto (fun y : ℕ => mertensSum y - Real.log y) atTop (𝓝 (-γ)) :=
    tendsto_mertensSum_sub_log
  obtain ⟨C₂, hC₂⟩ := exists_abs_sum_div_sub_le_of_tendsto hD (η := η / 4) (by positivity)
  refine ⟨|C₁| + 2 * |C₂|, fun M hM => ?_⟩
  have h1 := hC₁ M M M hM le_rfl le_rfl
  have h2 := hC₂ M M le_rfl
  -- `ζ`'s diagonal Gram splits into the logarithmic part and its Mertens error
  have hG : primeBilinear M (truncPole M) (truncPole M) =
      2 * ∑ m ∈ Icc 1 M, Real.log ((M / m : ℕ) : ℝ) / m +
        2 * ∑ m ∈ Icc 1 M, (mertensSum (M / m) - Real.log ((M / m : ℕ) : ℝ)) / m := by
    have h := primeBilinear_gaugeTrunc_self_eq euler_matching.1 M
    rw [gaugeTrunc_one] at h
    rw [h, ← mul_add, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun m _ => by rw [gaugeMertensSum_one]; ring
  rw [hG] at h1
  have hH0 := harmonicSum_nonneg M
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, le_abs_self C₁, le_abs_self C₂,
    neg_abs_le C₁, neg_abs_le C₂]

/-- **The finite-part criterion**: for every sign gauge and `|κ| ≤ 1`, the pole Grams satisfy
`|⟨εu^{(M)}, P εu^{(M)}⟩ − κ H_M² − 2α H_M| ≤ η H_M + C_η` for all `η > 0` if and only if the
harmonic mean of the Mertens error satisfies `|Σ_{m ≤ M} E(⌊M/m⌋)/m − α H_M| ≤ η H_M + C_η`. -/
theorem gaugePole_finitePart_iff (hε : IsSignGauge ε) {κ : ℝ} (hκ : |κ| ≤ 1) (α : ℝ) :
    (∀ η > 0, ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M →
      |primeBilinear M (gaugeTrunc ε M) (gaugeTrunc ε M) - κ * harmonicSum M ^ 2 -
          2 * α * harmonicSum M| ≤ η * harmonicSum M + C) ↔
    (∀ η > 0, ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M →
      |∑ m ∈ Icc 1 M, gaugeMertensError ε κ (M / m) / m - α * harmonicSum M| ≤
        η * harmonicSum M + C) := by
  -- `G − κH² − 2αH = 2(Σ E/m − αH) + κ(2 Σ log⌊M/m⌋/m − H²)`
  have hid : ∀ M : ℕ, primeBilinear M (gaugeTrunc ε M) (gaugeTrunc ε M) -
      κ * harmonicSum M ^ 2 - 2 * α * harmonicSum M =
      2 * (∑ m ∈ Icc 1 M, gaugeMertensError ε κ (M / m) / m - α * harmonicSum M) +
        κ * (2 * ∑ m ∈ Icc 1 M, Real.log ((M / m : ℕ) : ℝ) / m - harmonicSum M ^ 2) := by
    intro M
    rw [primeBilinear_gaugeTrunc_self_eq hε M]
    have : ∑ m ∈ Icc 1 M, gaugeMertensSum ε (M / m) / m =
        ∑ m ∈ Icc 1 M, gaugeMertensError ε κ (M / m) / m +
          κ * ∑ m ∈ Icc 1 M, Real.log ((M / m : ℕ) : ℝ) / m := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun m _ => by rw [gaugeMertensError]; ring
    rw [this]
    ring
  -- the logarithmic part, scaled by `|κ| ≤ 1`
  have hlog : ∀ η > 0, ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M →
      |κ * (2 * ∑ m ∈ Icc 1 M, Real.log ((M / m : ℕ) : ℝ) / m - harmonicSum M ^ 2)| ≤
        η * harmonicSum M + C := by
    intro η hη
    obtain ⟨C, hC⟩ := exists_abs_sum_log_floor_sub_harmonicSq_le hη
    refine ⟨|C|, fun M hM => ?_⟩
    rw [abs_mul]
    have h := hC M hM
    have hH := harmonicSum_nonneg M
    calc |κ| * |2 * ∑ m ∈ Icc 1 M, Real.log ((M / m : ℕ) : ℝ) / m - harmonicSum M ^ 2|
        ≤ 1 * (η * harmonicSum M + C) := mul_le_mul hκ h (abs_nonneg _) zero_le_one
      _ ≤ η * harmonicSum M + |C| := by linarith [le_abs_self C]
  constructor
  · intro hG η hη
    obtain ⟨C₁, hC₁⟩ := hG η hη
    obtain ⟨C₂, hC₂⟩ := hlog η hη
    refine ⟨(C₁ + C₂) / 2, fun M hM => ?_⟩
    have h1 := hC₁ M hM
    have h2 := hC₂ M hM
    rw [hid M] at h1
    have hH := harmonicSum_nonneg M
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, mul_nonneg hη.le hH]
  · intro hE η hη
    obtain ⟨C₁, hC₁⟩ := hE (η / 4) (by positivity)
    obtain ⟨C₂, hC₂⟩ := hlog (η / 2) (by positivity)
    refine ⟨2 * C₁ + C₂, fun M hM => ?_⟩
    have h1 := hC₁ M hM
    have h2 := hC₂ M hM
    rw [hid M]
    have hH := harmonicSum_nonneg M
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, mul_nonneg hη.le hH]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

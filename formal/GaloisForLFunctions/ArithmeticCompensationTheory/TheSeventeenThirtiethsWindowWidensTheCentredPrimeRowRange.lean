import GaloisForLFunctions.BezoutValuationIncidence.CentredPrimeRowPassesTheCoherentBlockObstruction
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSeventeenThirtiethsUnconditional

/-!
# The `17/30` short window widens the range of the centred prime row

The actual-row estimate of Bézout–Valuation Incidence
(`BezoutValuationIncidence.exists_abs_rowBilinear_centredPrimeRow_le`) bounds the cross-scale
remainder of the centred prime row `Λ(n) − 1` on a window at scale `Q` against any row on `(P, 2P]`
by `16ε` times the rank-two bound. Its only arithmetic input is the prime number theorem in short
intervals uniformly in the length, `|ψ(x + h) − ψ(x) − h| ≤ εh` for `x^α ≤ h ≤ x/2`, which it takes
from Huxley at `α > 7/12`. Its side conditions are `H ≍ Q^α`, `(H/2)(Σ_{k ≤ N} 1/k)² + 1/8 ≤ εP`
and `3P ≤ 2εQ`; with the horizon `N` polynomial in `Q` they hold for
`P^{1+δ} ≤ Q ≤ P^{1/α − δ}`, so Huxley gives the range `Q ≤ P^{12/7 − δ}`.

The corpus also owns the Guth–Maynard theorem `ψ(x + x^β) − ψ(x) ∼ x^β` for every `β > 17/30`
(`RHTower.tendsto_psi_short_window_div_seventeenThirtieths`), but only for the single length
`x^β`. This module connects the two.

* `eventually_abs_psi_window_sub_le_seventeenThirtieths`: the uniform-in-length version for every
  `α > 17/30`. Tile `[x, x + h]` by consecutive windows `[y, y + y^β]`, `17/30 < β < α`; the errors
  add up to `ε'h`, and the last partial window costs at most `(1 + ε')y^β = o(x^α)` because `ψ` is
  monotone.
* `exists_abs_rowBilinear_centredPrimeRow_le_seventeenThirtieths`: the actual-row estimate at every
  `α > 17/30`, with all side conditions kept.
* `exists_abs_rowBilinear_centredPrimeRow_le_of_range`: hence the sufficient unbalanced range
  `P^{1+δ} ≤ Q ≤ P^{30/17 − δ}` for horizons `N ≤ Q^C`, at the explicit block exponent
  `α = 17/30 + δ/4`.

This is an internal transfer, not a new prime theorem, and it does not touch the balanced regime
`Q ≍ P`.
-/

open Finset Filter Topology RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BezoutValuationIncidence
open ArithmeticFunction (vonMangoldt)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## Tiling a long window by short ones -/

/-- The tiling sequence `y₀ = x`, `y_{n+1} = y_n + y_n^β`. -/
def tileSeq (x β : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => tileSeq x β n + tileSeq x β n ^ β

theorem tileSeq_ge {x β : ℝ} (hx : 1 ≤ x) (hβ : 0 ≤ β) (n : ℕ) : x + n ≤ tileSeq x β n := by
  induction n with
  | zero => simp [tileSeq]
  | succ n ih =>
      have h1 : 1 ≤ tileSeq x β n := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have h2 := Real.one_le_rpow h1 hβ
      rw [tileSeq]
      push_cast
      linarith

/-- **Huxley's uniform window, at the Guth–Maynard exponent.** For `17/30 < α < 1` and `ε > 0`,
for all large `x` and every `x^α ≤ h ≤ x/2`: `|ψ(x + h) − ψ(x) − h| ≤ εh`. -/
theorem eventually_abs_psi_window_sub_le_seventeenThirtieths {α ε : ℝ} (hα : 17 / 30 < α)
    (hα1 : α < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ h : ℝ, x ^ α ≤ h → h ≤ x / 2 →
      |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤ ε * h := by
  set β := (17 / 30 + α) / 2 with hβdef
  have hβ : 17 / 30 < β := by rw [hβdef]; linarith
  have hβα : β < α := by rw [hβdef]; linarith
  have hβ0 : 0 < β := by linarith
  have hβ1 : β < 1 := by linarith
  -- the fixed-length window with error `ε/2`
  have hwin := (tendsto_psi_short_window_div_seventeenThirtieths hβ hβ1).eventually
    (Metric.ball_mem_nhds (1 : ℝ) (by positivity : (0 : ℝ) < ε / 2))
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hwin
  have hgap : Tendsto (fun x : ℝ => x ^ (α - β)) atTop atTop := tendsto_rpow_atTop (by linarith)
  filter_upwards [eventually_ge_atTop (max Y₀ 1), hgap.eventually_ge_atTop (4 / ε + 2)] with x hx hxg
  intro h hh1 hh2
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hxY : Y₀ ≤ x := (le_max_left _ _).trans hx
  have hxβ : 0 < x ^ β := Real.rpow_pos_of_pos hx0 β
  -- one tile: `|ψ(y + y^β) − ψ(y) − y^β| ≤ (ε/2) y^β` for `y ≥ x`
  have htile : ∀ y : ℝ, x ≤ y →
      |Chebyshev.psi (y + y ^ β) - Chebyshev.psi y - y ^ β| ≤ ε / 2 * y ^ β := by
    intro y hy
    have hy0 : 0 < y ^ β := Real.rpow_pos_of_pos (by linarith) β
    have h : |(Chebyshev.psi (y + y ^ β) - Chebyshev.psi y) / y ^ β - 1| < ε / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hY₀ y (hxY.trans hy)
    have heq : Chebyshev.psi (y + y ^ β) - Chebyshev.psi y - y ^ β =
        ((Chebyshev.psi (y + y ^ β) - Chebyshev.psi y) / y ^ β - 1) * y ^ β := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hy0]
    exact mul_le_mul_of_nonneg_right h.le hy0.le
  -- the tiles accumulate their errors
  have hacc : ∀ n : ℕ, x ≤ tileSeq x β n ∧
      |Chebyshev.psi (tileSeq x β n) - Chebyshev.psi x - (tileSeq x β n - x)| ≤
        ε / 2 * (tileSeq x β n - x) := by
    intro n
    induction n with
    | zero => simp [tileSeq]
    | succ n ih =>
        obtain ⟨hge, hle⟩ := ih
        have hpos : 0 < tileSeq x β n ^ β := Real.rpow_pos_of_pos (by linarith) β
        refine ⟨by rw [tileSeq]; linarith, ?_⟩
        have ht := htile _ hge
        rw [tileSeq]
        calc |Chebyshev.psi (tileSeq x β n + tileSeq x β n ^ β) - Chebyshev.psi x -
              (tileSeq x β n + tileSeq x β n ^ β - x)|
            = |(Chebyshev.psi (tileSeq x β n) - Chebyshev.psi x - (tileSeq x β n - x)) +
              (Chebyshev.psi (tileSeq x β n + tileSeq x β n ^ β) - Chebyshev.psi (tileSeq x β n) -
                tileSeq x β n ^ β)| := by ring_nf
          _ ≤ ε / 2 * (tileSeq x β n - x) + ε / 2 * tileSeq x β n ^ β :=
              (abs_add_le _ _).trans (add_le_add hle ht)
          _ = ε / 2 * (tileSeq x β n + tileSeq x β n ^ β - x) := by ring
  -- the last tile that starts inside `[x, x + h]`
  have hex : ∃ n, x + h < tileSeq x β (n + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt h
    refine ⟨n, lt_of_lt_of_le ?_ (tileSeq_ge hx1 hβ0.le (n + 1))⟩
    push_cast; linarith
  classical
  set N := Nat.find hex
  have hN : x + h < tileSeq x β (N + 1) := Nat.find_spec hex
  have hN' : tileSeq x β N ≤ x + h := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0]; simp only [tileSeq]; linarith [(Real.rpow_pos_of_pos hx0 α).le.trans hh1]
    · have := Nat.find_min hex (show N - 1 < N by omega)
      rw [show N - 1 + 1 = N by omega] at this
      exact not_lt.mp this
  obtain ⟨hge, hle⟩ := hacc N
  set y := tileSeq x β N
  have hyβ : 0 < y ^ β := Real.rpow_pos_of_pos (by linarith) β
  have hnext : tileSeq x β (N + 1) = y + y ^ β := rfl
  rw [hnext] at hN
  -- the remainder window `[y, x + h]` costs at most `(1 + ε/2) y^β`
  have hmono1 : Chebyshev.psi y ≤ Chebyshev.psi (x + h) := Chebyshev.psi_mono hN'
  have hmono2 : Chebyshev.psi (x + h) ≤ Chebyshev.psi (y + y ^ β) := Chebyshev.psi_mono hN.le
  have ht := (abs_le.mp (htile y hge)).2
  have hrest : |Chebyshev.psi (x + h) - Chebyshev.psi y - (x + h - y)| ≤ (1 + ε / 2) * y ^ β := by
    rw [abs_le]; constructor <;> nlinarith
  -- `y^β ≤ (3x/2)^β ≤ 2 x^β` and `(2 + ε) x^β ≤ (ε/2) x^α ≤ (ε/2) h`
  have hy32 : y ≤ 3 / 2 * x := by linarith
  have hyβle : y ^ β ≤ 2 * x ^ β := by
    calc y ^ β ≤ (3 / 2 * x) ^ β := Real.rpow_le_rpow (by linarith) hy32 hβ0.le
      _ = (3 / 2) ^ β * x ^ β := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 2 * x ^ β := by
          refine mul_le_mul_of_nonneg_right ?_ hxβ.le
          calc (3 / 2 : ℝ) ^ β ≤ (3 / 2) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1.le
            _ ≤ 2 := by norm_num
  have hsmall : (1 + ε / 2) * (2 * x ^ β) ≤ ε / 2 * h := by
    have hsplit : x ^ α = x ^ (α - β) * x ^ β := by
      rw [← Real.rpow_add hx0]; ring_nf
    have h1 : (4 / ε + 2) * x ^ β ≤ x ^ α := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_right hxg hxβ.le
    have h2 : (1 + ε / 2) * (2 * x ^ β) = ε / 2 * ((4 / ε + 2) * x ^ β) := by
      field_simp; ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left (h1.trans hh1) (by positivity)
  calc |Chebyshev.psi (x + h) - Chebyshev.psi x - h|
      = |(Chebyshev.psi y - Chebyshev.psi x - (y - x)) +
          (Chebyshev.psi (x + h) - Chebyshev.psi y - (x + h - y))| := by ring_nf
    _ ≤ ε / 2 * (y - x) + (1 + ε / 2) * y ^ β := (abs_add_le _ _).trans (add_le_add hle hrest)
    _ ≤ ε / 2 * h + ε / 2 * h := by
        have h1 : y - x ≤ h := by linarith
        have h2 : (1 + ε / 2) * y ^ β ≤ (1 + ε / 2) * (2 * x ^ β) :=
          mul_le_mul_of_nonneg_left hyβle (by positivity)
        nlinarith
    _ = ε * h := by ring

/-! ## The actual-row estimate at the `17/30` exponent -/

/-- **The centred prime row at every block exponent `α > 17/30`.** The statement of
`BezoutValuationIncidence.exists_abs_rowBilinear_centredPrimeRow_le` with Huxley's exponent `7/12`
replaced by the Guth–Maynard exponent `17/30`; every side condition is kept. -/
theorem exists_abs_rowBilinear_centredPrimeRow_le_seventeenThirtieths {α : ℝ} (hα : 17 / 30 < α)
    (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ Q₀ : ℕ, ∀ {N A H K P Q : ℕ} {c : ℕ → ℝ}, Q₀ ≤ Q → Q ≤ A → A + K * H ≤ 2 * Q →
      2 * Q ≤ N → 1 ≤ P → (2 * (Q : ℝ)) ^ α ≤ H → (H : ℝ) ≤ 4 * (Q : ℝ) ^ α →
      (∀ d, c d ≠ 0 → P < d ∧ d ≤ 2 * P) →
      (H : ℝ) * (∑ k ∈ Icc 1 N, 1 / (k : ℝ)) ^ 2 / 2 + 1 / 8 ≤ ε * P →
      3 * (P : ℝ) ≤ 2 * ε * Q →
      |rowBilinear N c (centredPrimeRow A H K) +
          rowMean N c * vonMangoldtReadout N (centredPrimeRow A H K) +
          rowBeta N c * finiteHarmonicSum N (centredPrimeRow A H K)| ≤
        16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1
    (eventually_abs_psi_window_sub_le_seventeenThirtieths hα hα1 hε)
  have hev : ∀ᶠ q : ℝ in atTop, 100 / ε ≤ q ^ (1 - α) ∧ 100 ≤ q ∧ X₀ + 1 ≤ q :=
    ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - α)).eventually_ge_atTop _).and
      ((eventually_ge_atTop _).and (eventually_ge_atTop _))
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨Q₀, ?_⟩
  intro N A H K P Q c hQ hA hAK hN hP hH1 hH2 hc hterm2 hterm3
  obtain ⟨hq1, hq100, hqX⟩ := hQ₀ Q hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ1 : 1 ≤ Q := by exact_mod_cast (show (1 : ℝ) ≤ Q by linarith)
  have hQα : (Q : ℝ) ^ α * (Q : ℝ) ^ (1 - α) = Q := by
    rw [← Real.rpow_add hQ0, show α + (1 - α) = (1 : ℝ) by ring, Real.rpow_one]
  have hQα0 : 0 < (Q : ℝ) ^ α := Real.rpow_pos_of_pos hQ0 α
  have h100 : 100 * (Q : ℝ) ^ α ≤ ε * Q := by
    rw [div_le_iff₀ hε] at hq1
    calc 100 * (Q : ℝ) ^ α ≤ (Q : ℝ) ^ (1 - α) * ε * (Q : ℝ) ^ α :=
          mul_le_mul_of_nonneg_right hq1 hQα0.le
      _ = ε * Q := by
          rw [mul_comm ((Q : ℝ) ^ (1 - α)) ε, mul_assoc, mul_comm ((Q : ℝ) ^ (1 - α)), hQα]
  have hHQ : 25 * (H : ℝ) ≤ ε * Q := by linarith
  have hHnat : 1 ≤ H := by
    have : (1 : ℝ) ≤ H := le_trans (Real.one_le_rpow (by linarith) (by linarith)) hH1
    exact_mod_cast this
  have hΔ := blockDiscrepancy_centredPrimeRow_le (A := A) (H := H) (K := K) (Q := Q) (ε := ε)
    fun m hm => abs_sum_block_le_of_window (by linarith) hε hε1 hX₀ hA hAK hHnat hq100 hqX hH1
      hHQ hm
  have hS₀ := mass_centredPrimeRow_ge (N := N) hQ1 hA hAK hN
  have hKH : 2 * ε * K * H / (Q : ℝ) ^ 2 ≤
      96 * ε * rowInverseSquareMass N (centredPrimeRow A H K) := by
    have h48 : (K : ℝ) * H / (48 * (Q : ℝ) ^ 2) = (K : ℝ) * H / (Q : ℝ) ^ 2 / 48 := by
      rw [div_div, mul_comm 48]
    rw [h48, div_le_iff₀ (by norm_num)] at hS₀
    have : 0 ≤ (K : ℝ) * H / (Q : ℝ) ^ 2 := by positivity
    calc 2 * ε * K * H / (Q : ℝ) ^ 2 = 2 * ε * ((K : ℝ) * H / (Q : ℝ) ^ 2) := by ring
      _ ≤ 2 * ε * (48 * rowInverseSquareMass N (centredPrimeRow A H K)) :=
          mul_le_mul_of_nonneg_left (by unfold rowInverseSquareMass; linarith) (by positivity)
      _ = 96 * ε * rowInverseSquareMass N (centredPrimeRow A H K) := by ring
  have hmain := abs_rowBilinear_add_mean_add_beta_le_block (N := N) (A := A) (H := H) (K := K)
    (c := c) (c' := centredPrimeRow A H K) (by omega) (by omega) fun n => centredPrimeRow_support
  have hS1 := mul_sum_abs_le_rowLinearWeight (N := N) hc
  have hS2 := sum_abs_mul_sq_le_rowLinearWeight (N := N) hc
  have hS3 := mul_sum_abs_div_cube_le_rowInverseSquareMass (N := N) (Q := Q)
    (c' := centredPrimeRow A H K) fun n hn => hA.trans (mem_Ico.mp (centredPrimeRow_support hn)).1
  refine assembly_le hε (rowInverseSquareMass_nonneg _ _) (rowLinearWeight_nonneg _ _)
    (sum_nonneg fun m _ => abs_nonneg _) (sum_nonneg fun d _ => abs_nonneg _)
    (sum_nonneg fun n _ => by positivity) ?_ (hΔ.trans hKH) hterm2 hS1 hS2 hS3 hterm3
  exact hmain

/-! ## The unbalanced range `P^{1+δ} ≤ Q ≤ P^{30/17 − δ}` -/

/-- The harmonic sum is at most `1 + log N`. -/
theorem sum_Icc_inv_le_one_add_log (N : ℕ) :
    ∑ k ∈ Icc 1 N, 1 / (k : ℝ) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- **The sufficient unbalanced range reaches `30/17`.** For `0 < δ ≤ 1`, `0 < ε ≤ 1` and `C ≥ 1`
there is `P₀` such that for `P ≥ P₀`, `P^{1+δ} ≤ Q ≤ P^{30/17 − δ}`, horizons `2Q ≤ N ≤ Q^C`,
windows `[A, A + KH) ⊆ [Q, 2Q]` and blocks of length `(2Q)^α ≤ H ≤ 4Q^α` with
`α = 17/30 + δ/4`, every row `c` on `(P, 2P]` satisfies the rank-two-quality estimate. -/
theorem exists_abs_rowBilinear_centredPrimeRow_le_of_range {δ ε C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 1 ≤ C) :
    ∃ P₀ : ℕ, ∀ {N A H K P Q : ℕ} {c : ℕ → ℝ}, P₀ ≤ P →
      (P : ℝ) ^ (1 + δ) ≤ Q → (Q : ℝ) ≤ (P : ℝ) ^ (30 / 17 - δ) →
      Q ≤ A → A + K * H ≤ 2 * Q → 2 * Q ≤ N → (N : ℝ) ≤ (Q : ℝ) ^ C →
      (2 * (Q : ℝ)) ^ (17 / 30 + δ / 4) ≤ H → (H : ℝ) ≤ 4 * (Q : ℝ) ^ (17 / 30 + δ / 4) →
      (∀ d, c d ≠ 0 → P < d ∧ d ≤ 2 * P) →
      |rowBilinear N c (centredPrimeRow A H K) +
          rowMean N c * vonMangoldtReadout N (centredPrimeRow A H K) +
          rowBeta N c * finiteHarmonicSum N (centredPrimeRow A H K)| ≤
        16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c := by
  set α := 17 / 30 + δ / 4 with hαdef
  have hα : 17 / 30 < α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  obtain ⟨Q₀, hQ₀⟩ := exists_abs_rowBilinear_centredPrimeRow_le_seventeenThirtieths hα hα1 hε hε1
  -- the exponent of `Q^α` in `P` is at most `1 − δ/8`
  have hexp : α * (30 / 17 - δ) ≤ 1 - δ / 8 := by rw [hαdef]; nlinarith
  -- the side conditions in `P` alone, for large `P`
  have hlogP : Tendsto (fun P : ℝ => (8 * P ^ (1 - δ / 8) * (1 + 2 * C * Real.log P) ^ 2 + 1 / 8) / P)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun P : ℝ => Real.log P ^ 2 / P ^ (δ / 8)) atTop (𝓝 0) := by
      simpa [Real.rpow_two] using
        (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by positivity : (0 : ℝ) < δ / 8)).tendsto_div_nhds_zero
    have h2 : Tendsto (fun P : ℝ => Real.log P / P ^ (δ / 8)) atTop (𝓝 0) := by
      simpa using (isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < δ / 8)).tendsto_div_nhds_zero
    have h3 : Tendsto (fun P : ℝ => (1 : ℝ) / P ^ (δ / 8)) atTop (𝓝 0) := by
      refine ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < δ / 8)).inv_tendsto_atTop).congr
        fun P => ?_
      simp [one_div]
    have h4 : Tendsto (fun P : ℝ => (1 / 8 : ℝ) / P) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hsum := ((h3.add ((h2.const_mul (4 * C)).add (h1.const_mul (4 * C ^ 2)))).const_mul 8).add h4
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with P hP
    have hsplit : P ^ (1 - δ / 8) = P / P ^ (δ / 8) := by
      rw [Real.rpow_sub hP, Real.rpow_one]
    rw [hsplit]
    field_simp
    ring
  have hev : ∀ᶠ P : ℝ in atTop,
      (8 * P ^ (1 - δ / 8) * (1 + 2 * C * Real.log P) ^ 2 + 1 / 8) / P ≤ ε ∧
        3 / (2 * ε) ≤ P ^ δ ∧ (Q₀ : ℝ) ≤ P ∧ 1 ≤ P :=
    (hlogP.eventually (eventually_le_nhds hε)).and
      (((tendsto_rpow_atTop hδ).eventually_ge_atTop _).and
        ((eventually_ge_atTop _).and (eventually_ge_atTop _)))
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨P₀, ?_⟩
  intro N A H K P Q c hP hQlo hQhi hA hAK hN hNC hH1 hH2 hc
  obtain ⟨hside, hPδ, hPQ₀, hP1⟩ := hP₀ P hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hQlo
  have hPQ : (P : ℝ) ≤ Q := by
    calc (P : ℝ) = P ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ P ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
      _ ≤ Q := hQlo
  have hQQ₀ : Q₀ ≤ Q := by exact_mod_cast hPQ₀.trans hPQ
  have hPnat : 1 ≤ P := by exact_mod_cast hP1
  refine hQ₀ hQQ₀ hA hAK hN hPnat hH1 hH2 hc ?_ ?_
  · -- `H h_N²/2 + 1/8 ≤ εP`
    have hQ1 : (1 : ℝ) ≤ Q := hP1.trans hPQ
    have hQα : (Q : ℝ) ^ α ≤ P ^ (1 - δ / 8) := by
      calc (Q : ℝ) ^ α ≤ ((P : ℝ) ^ (30 / 17 - δ)) ^ α :=
            Real.rpow_le_rpow hQ0.le hQhi (by linarith)
        _ = (P : ℝ) ^ (α * (30 / 17 - δ)) := by
            rw [← Real.rpow_mul hP0.le, mul_comm]
        _ ≤ (P : ℝ) ^ (1 - δ / 8) := Real.rpow_le_rpow_of_exponent_le hP1 hexp
    have hlogQ : Real.log Q ≤ 2 * Real.log P := by
      have hQ2 : (Q : ℝ) ≤ P ^ (2 : ℝ) :=
        hQhi.trans (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith))
      have := Real.log_le_log hQ0 hQ2
      rwa [Real.log_rpow hP0] at this
    have hlogN : Real.log N ≤ C * (2 * Real.log P) := by
      have hN0 : (0 : ℝ) < N := by
        have : (2 : ℝ) * Q ≤ N := by exact_mod_cast hN
        linarith
      have := Real.log_le_log hN0 hNC
      rw [Real.log_rpow hQ0] at this
      exact this.trans (mul_le_mul_of_nonneg_left hlogQ (by linarith))
    have hharm := sum_Icc_inv_le_one_add_log N
    have hharm0 : 0 ≤ ∑ k ∈ Icc 1 N, 1 / (k : ℝ) := sum_nonneg fun k _ => by positivity
    have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg hP1
    have hsq : (∑ k ∈ Icc 1 N, 1 / (k : ℝ)) ^ 2 ≤ (1 + 2 * C * Real.log P) ^ 2 :=
      pow_le_pow_left₀ hharm0 (by nlinarith) 2
    have hH : (H : ℝ) ≤ 4 * P ^ (1 - δ / 8) := hH2.trans (by linarith)
    have hside' := hside
    rw [div_le_iff₀ hP0] at hside'
    have hpow0 : 0 ≤ (P : ℝ) ^ (1 - δ / 8) := Real.rpow_nonneg hP0.le _
    calc (H : ℝ) * (∑ k ∈ Icc 1 N, 1 / (k : ℝ)) ^ 2 / 2 + 1 / 8
        ≤ 4 * P ^ (1 - δ / 8) * (1 + 2 * C * Real.log P) ^ 2 / 2 + 1 / 8 := by
          gcongr
      _ ≤ 8 * P ^ (1 - δ / 8) * (1 + 2 * C * Real.log P) ^ 2 + 1 / 8 := by
          nlinarith [sq_nonneg (1 + 2 * C * Real.log P)]
      _ ≤ ε * P := hside'
  · -- `3P ≤ 2εQ`
    have hQP : (P : ℝ) ^ (1 + δ) = P * P ^ δ := by
      rw [Real.rpow_add hP0, Real.rpow_one]
    rw [div_le_iff₀ (by positivity)] at hPδ
    nlinarith [hQlo, hQP]

end GaloisForLFunctions.ArithmeticCompensationTheory

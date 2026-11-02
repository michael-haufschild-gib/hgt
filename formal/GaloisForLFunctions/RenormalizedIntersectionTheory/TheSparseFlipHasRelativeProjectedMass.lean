import GaloisForLFunctions.RenormalizedIntersectionTheory.TheZeroDensityRoughMeanIsUniform
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheSparseFlipHasUniformHarmonicRatios
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheZeroDensityConductorSeriesConverges
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheMultiscaleProjectionBound

/-!
# Relative projected mass at zero prime density

Square-root comparison between harmonic horizons makes the smooth-fibre bound
relative to the actual signed mean. Subpower growth of the inverse Euler density
then gives a summable dyadic spectral tail, even when the Euler density is zero.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

private theorem roughHarmonicSum_eq_one_of_lt (P : Set ℕ) {Q Y : ℕ}
    (hY : 1 ≤ Y) (hYQ : Y < Q) :
    gaugeHarmonicSum (roughGauge Q (primeSetFlip P)) Y = 1 := by
  rw [← sum_roughInterval_eq_gaugeHarmonicSum]
  have hset : roughInterval Q Y = {1} := by
    ext n
    constructor
    · intro hn
      exact mem_singleton.mpr (eq_one_of_mem_roughInterval_of_le hn hYQ)
    · intro hn
      rw [mem_singleton.mp hn]
      exact one_mem_roughInterval Q hY
  rw [hset, sum_singleton, Nat.cast_one, div_one]
  exact signGauge_map_one (primeSetFlip_isSignGauge P)

/-- One square-root envelope controls every earlier rough horizon, including the
finite initial range and horizons below the roughness cutoff. -/
theorem exists_eventually_uniform_earlier_roughMean_bound (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      0 ≤ gaugeHarmonicSum (primeSetFlip P) N ∧
      ∀ Q Y : ℕ, 3 ≤ Q → 1 ≤ Y → Y ≤ N →
        |gaugeHarmonicSum (roughGauge Q (primeSetFlip P)) Y| ≤
          (A * gaugeHarmonicSum (primeSetFlip P) N /
            (Real.log Q * flipDensityBelow (primeSetFlip P) Q)) *
              (Real.log Y / Real.log N) ^ (1 / 2 : ℝ) + B := by
  obtain ⟨A, B, hA, hB, hrough⟩ := exists_eventually_uniform_zeroDensity_roughMean_bound P hP
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hrough
  obtain ⟨M₁, _, hearlier⟩ := exists_sparse_signedMean_uniform_earlier_bound P hP
    (show (0 : ℝ) < 1 / 2 by norm_num)
  let M := max M₀ M₁
  let B' := B + 1 + Real.log M
  have hB' : 0 < B' := by
    have hlog := Real.log_natCast_nonneg M
    dsimp only [B']
    linarith only [hB, hlog]
  refine ⟨6 * A, B', mul_pos (by norm_num) hA, hB', ?_⟩
  filter_upwards [(tendsto_sparse_signedMean_atTop P hP).eventually (eventually_ge_atTop 0),
    eventually_ge_atTop (3 : ℕ)] with N hSN hN
  refine ⟨hSN, fun Q Y hQ hY hYN => ?_⟩
  let d := Real.log Q * flipDensityBelow (primeSetFlip P) Q
  have hd : 0 < d := mul_pos (zero_lt_one.trans_le (one_le_log_of_three_le hQ))
    (flipDensityBelow_pos_le_one (abs_primeSetFlip_le P) Q).1
  have hmain : 0 ≤ (6 * A * gaugeHarmonicSum (primeSetFlip P) N / d) *
      (Real.log Y / Real.log N) ^ (1 / 2 : ℝ) := by positivity
  change |gaugeHarmonicSum (roughGauge Q (primeSetFlip P)) Y| ≤
    (6 * A * gaugeHarmonicSum (primeSetFlip P) N / d) *
      (Real.log Y / Real.log N) ^ (1 / 2 : ℝ) + B'
  by_cases hMY : M ≤ Y
  · by_cases hQY : Q ≤ Y
    · have hR := hM₀ Y ((le_max_left _ _).trans hMY) Q hQ hQY
      have hS := hearlier Y N ((le_max_right _ _).trans hMY) hYN
      norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hS
      have hBsmall : B ≤ B' := by
        have hlog := Real.log_natCast_nonneg M
        dsimp only [B']
        linarith only [hlog]
      refine hR.trans ?_
      apply add_le_add _ hBsmall
      calc
        A * (gaugeHarmonicSum (primeSetFlip P) Y / d) ≤
            A * ((6 * (Real.log Y / Real.log N) ^ (1 / 2 : ℝ) *
              gaugeHarmonicSum (primeSetFlip P) N) / d) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hS hd.le) hA.le
        _ = _ := by ring
    · rw [roughHarmonicSum_eq_one_of_lt P hY (lt_of_not_ge hQY), abs_one]
      have hlog := Real.log_natCast_nonneg M
      dsimp only [B']
      linarith only [hmain, hB, hlog]
  · have hsmall := abs_gaugeHarmonicSum_le (roughGauge Q (primeSetFlip P))
      (abs_roughGauge_le (abs_primeSetFlip_le P) Q) Y
    have hlog : Real.log Y ≤ Real.log M := Real.log_le_log
      (by exact_mod_cast hY) (by exact_mod_cast (lt_of_not_ge hMY).le)
    dsimp only [B']
    linarith only [hsmall, hlog, hmain, hB]

/-- The projected mass is controlled by the actual harmonic correlation and the
inverse finite Euler density, plus the ordinary smooth-sector logarithm. -/
theorem exists_eventually_projectedMass_le_eulerDensity (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ᶠ N : ℕ in atTop,
      ∀ Q : ℕ, 3 ≤ Q → Q ≤ N →
        ‖(smoothFibreSpace Q N).starProjection (gaugeVector N (primeSetFlip P))‖ ^ (2 : ℕ) ≤
          C * (gaugeHarmonicSum (primeSetFlip P) N ^ (2 : ℕ) / Real.log N) /
            flipDensityBelow (primeSetFlip P) Q ^ (2 : ℕ) + D * Real.log Q := by
  obtain ⟨A, B, hA, hB, hW⟩ := exists_eventually_uniform_earlier_roughMean_bound P hP
  obtain ⟨c₀, hc₀, hR⟩ := exists_roughHarmonic_ge
  obtain ⟨Ks, hKs, hsm⟩ := exists_sum_smoothSet_inv_le
  let F := (1 + 1 / c₀) * Ks
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨2 * A ^ (2 : ℕ) * F, 2 * B ^ (2 : ℕ) * F, by positivity, by positivity, ?_⟩
  filter_upwards [hW] with N hWN Q hQ hQN
  let ω := primeSetFlip P
  let S := gaugeHarmonicSum ω N
  let δ := flipDensityBelow ω Q
  let U := Real.log N / Real.log Q
  let D₀ := A * S / (Real.log Q * δ)
  let A₀ := D₀ / U ^ (1 / 2 : ℝ)
  have hS : 0 ≤ S := hWN.1
  have hq1 : 1 ≤ Real.log Q := one_le_log_of_three_le hQ
  have hq : 0 < Real.log Q := zero_lt_one.trans_le hq1
  have hlogs : Real.log Q ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q by omega)) (by exact_mod_cast hQN)
  have hNlog : 0 < Real.log N := hq.trans_le hlogs
  have hδ : 0 < δ := (flipDensityBelow_pos_le_one (abs_primeSetFlip_le P) Q).1
  have hU : 1 ≤ U := (le_div_iff₀ hq).mpr (by simpa only [one_mul] using hlogs)
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀, D₀]; positivity
  let K₀ := (2 * A₀ ^ (2 : ℕ) + 2 * B ^ (2 : ℕ)) * (1 + 1 / c₀)
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hfib : ∀ a ∈ smoothSet Q N,
      (∑ b ∈ roughInterval Q (N / a), ω (a * b) / b) ^ (2 : ℕ) /
        (a * roughHarmonic Q (N / a)) ≤ (1 / a) * K₀ := by
    intro a ha
    obtain ⟨ha1, haN, _⟩ := mem_smoothSet.mp ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    have hY1 : 1 ≤ N / a := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hY0 : (0 : ℝ) < (N / a : ℕ) := by exact_mod_cast hY1
    have hsum : ∑ b ∈ roughInterval Q (N / a), ω (a * b) / b =
        ω a * gaugeHarmonicSum (roughGauge Q ω) (N / a) := by
      rw [← sum_roughInterval_eq_gaugeHarmonicSum, mul_sum]
      refine sum_congr rfl fun b hb => ?_
      have hb1 := (mem_roughInterval.mp hb).1
      dsimp only [ω]
      rw [(primeSetFlip_isSignGauge P).mul (by omega : a ≠ 0) (by omega : b ≠ 0)]
      ring
    have hωsq : ω a ^ (2 : ℕ) = 1 := by rw [sq]; exact primeSetFlip_mul_self P a
    rw [hsum, mul_pow, hωsq, one_mul]
    let u := Real.log ((N / a : ℕ) : ℝ) / Real.log Q
    have hu : 0 ≤ u := div_nonneg (Real.log_natCast_nonneg _) hq.le
    have huU : u ≤ U := div_le_div_of_nonneg_right
      (Real.log_le_log hY0 (by exact_mod_cast Nat.div_le_self N a)) hq.le
    have hRu : c₀ * u ≤ roughHarmonic Q (N / a) := by
      refine le_trans ?_ (hR Q hQ (N / a))
      rw [mul_div_assoc']
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hc₀.le) hq.le
      exact Real.log_le_log hY0 (by linarith)
    have hbound := hWN.2 Q (N / a) hQ hY1 (Nat.div_le_self N a)
    have hratio : Real.log ((N / a : ℕ) : ℝ) / Real.log N = u / U := by
      dsimp only [u, U]
      field_simp [hq.ne', hNlog.ne']
    have hpower : D₀ * (Real.log ((N / a : ℕ) : ℝ) / Real.log N) ^ (1 / 2 : ℝ) =
        A₀ * u ^ (1 / 2 : ℝ) := by
      rw [hratio, Real.div_rpow hu hU0.le]
      dsimp only [A₀]
      ring
    change |gaugeHarmonicSum (roughGauge Q ω) (N / a)| ≤
      D₀ * (Real.log ((N / a : ℕ) : ℝ) / Real.log N) ^ (1 / 2 : ℝ) + B at hbound
    rw [hpower] at hbound
    have h := sq_div_le_of_rough_bound hA₀ hB.le hc₀ (β := 1 / 2) le_rfl hu huU hU
      hbound (one_le_roughHarmonic Q hY1) hRu
    norm_num only [show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num,
      Real.rpow_zero, mul_one] at h
    calc
      _ = (1 / (a : ℝ)) * (gaugeHarmonicSum (roughGauge Q ω) (N / a) ^ (2 : ℕ) /
          roughHarmonic Q (N / a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  have hM : ∀ v ∈ smoothFibreSpace Q N,
      ⟪gaugeVector N ω, v⟫ ^ (2 : ℕ) ≤ (K₀ * (Ks * Real.log Q)) * ‖v‖ ^ (2 : ℕ) := by
    intro v hv
    refine (inner_sq_le_of_mem_smoothFibreSpace ω hv).trans ?_
    rw [mul_comm _ (‖v‖ ^ (2 : ℕ))]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    refine (sum_le_sum hfib).trans ?_
    rw [← sum_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hsm Q hQ N) hK₀
  have hproj := norm_starProjection_sq_le (gaugeVector N ω) (by positivity) hM
  have hUhalf : (U ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = U := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    norm_num
  have hA₀sq : A₀ ^ (2 : ℕ) * Real.log Q =
      A ^ (2 : ℕ) * (S ^ (2 : ℕ) / Real.log N) / δ ^ (2 : ℕ) := by
    dsimp only [A₀]
    rw [div_pow, hUhalf]
    dsimp only [D₀, U]
    field_simp [hq.ne', hNlog.ne', hδ.ne']
  refine hproj.trans_eq ?_
  calc
    K₀ * (Ks * Real.log Q) =
        (2 * (A₀ ^ (2 : ℕ) * Real.log Q) + 2 * B ^ (2 : ℕ) * Real.log Q) * F := by
      dsimp only [K₀, F]
      ring
    _ = _ := by rw [hA₀sq]; ring

/-- Zero-density projected mass has a half-power logarithmic cost, small enough
for a geometrically summable spectral tail. -/
theorem exists_eventually_relative_projectedMass_le_sqrt_log (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ Q : ℕ, 3 ≤ Q → Q ≤ N →
        ‖(smoothFibreSpace Q N).starProjection (gaugeVector N (primeSetFlip P))‖ ^ (2 : ℕ) ≤
          K * (gaugeHarmonicSum (primeSetFlip P) N ^ (2 : ℕ) / Real.log N) *
            Real.log Q ^ (1 / 2 : ℝ) := by
  obtain ⟨C, D, hC, hD, hmass⟩ := exists_eventually_projectedMass_le_eulerDensity P hP
  obtain ⟨E, hE, hdensity⟩ := exists_inv_sq_flipDensityBelow_le_rpow_log P hP
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hgrowth := (tendsto_sparse_signedMean_div_log_rpow_atTop P hP
    (α := 3 / 4) (by norm_num)).eventually (eventually_ge_atTop 1)
  refine ⟨C * E + D, add_nonneg (mul_nonneg hC hE.le) hD, ?_⟩
  filter_upwards [hmass, hgrowth, eventually_ge_atTop (3 : ℕ)] with N hmassN hgN hN Q hQ hQN
  let R := gaugeHarmonicSum (primeSetFlip P) N ^ (2 : ℕ) / Real.log N
  have hlogN : 0 < Real.log N := zero_lt_one.trans_le (one_le_log_of_three_le hN)
  have hlogQ : 0 < Real.log Q := zero_lt_one.trans_le (one_le_log_of_three_le hQ)
  have hR : 0 ≤ R := div_nonneg (sq_nonneg _) hlogN.le
  have hS : Real.log N ^ (3 / 4 : ℝ) ≤ gaugeHarmonicSum (primeSetFlip P) N := by
    simpa only [one_mul] using (le_div_iff₀ (Real.rpow_pos_of_pos hlogN (3 / 4))).mp hgN
  have hSsq := pow_le_pow_left₀ (Real.rpow_nonneg hlogN.le (3 / 4)) hS 2
  have hpower : (Real.log N ^ (3 / 4 : ℝ)) ^ (2 : ℕ) =
      Real.log N ^ (1 / 2 : ℝ) * Real.log N := by
    calc
      _ = Real.log N ^ ((3 / 4 : ℝ) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hlogN.le]
        norm_num
      _ = Real.log N ^ ((1 / 2 : ℝ) + 1) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hlogN, Real.rpow_one]
  rw [hpower] at hSsq
  have hrootN : Real.log N ^ (1 / 2 : ℝ) ≤ R := (le_div_iff₀ hlogN).mpr hSsq
  have hlogs : Real.log Q ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q by omega)) (by exact_mod_cast hQN)
  have hrootQ := (Real.rpow_le_rpow hlogQ.le hlogs (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans hrootN
  have hQsq : Real.log Q ^ (1 / 2 : ℝ) * Real.log Q ^ (1 / 2 : ℝ) = Real.log Q := by
    rw [← Real.rpow_add hlogQ]
    norm_num
  have habsorb : Real.log Q ≤ R * Real.log Q ^ (1 / 2 : ℝ) := by
    calc
      Real.log Q = Real.log Q ^ (1 / 2 : ℝ) * Real.log Q ^ (1 / 2 : ℝ) := hQsq.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hrootQ (Real.rpow_nonneg hlogQ.le _)
  have hden := mul_le_mul_of_nonneg_left (hdensity Q hQ) (mul_nonneg hC hR)
  have hadd := mul_le_mul_of_nonneg_left habsorb hD
  refine (hmassN Q hQ hQN).trans ?_
  change C * R / flipDensityBelow (primeSetFlip P) Q ^ (2 : ℕ) + D * Real.log Q ≤ _
  have hbound : C * R * (1 / flipDensityBelow (primeSetFlip P) Q ^ (2 : ℕ)) +
      D * Real.log Q ≤ (C * E + D) * R * Real.log Q ^ (1 / 2 : ℝ) :=
    (add_le_add hden hadd).trans_eq (by ring)
  simpa only [mul_one_div] using hbound

end GaloisForLFunctions.RenormalizedIntersectionTheory


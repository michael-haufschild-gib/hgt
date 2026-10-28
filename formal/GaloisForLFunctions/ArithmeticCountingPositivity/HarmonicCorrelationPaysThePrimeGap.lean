import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.FullCorrelationKeepsTheMargin

/-!
# Harmonic correlation pays the prime gap

For a sign gauge `ω`, let `c_N = (Σ ω(n)/n)/(Σ 1/n)`. On the fixed pole
hyperplane, gauging retains at least `c_N²` of the harmonic variance. The sharp
multiplicative Poincaré inequality therefore pays a prime gap of
`(2 log 2)c_N²`, with an error uniform over all gauges. No limiting harmonic
density is required.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics

/-- Normalized harmonic correlation of a sign gauge with the pole. -/
def harmonicCorrelation (ω : ℕ → ℝ) (N : ℕ) : ℝ :=
  gaugeHarmonicSum ω N / gaugeHarmonicSum (fun _ => 1) N

/-- Harmonic variance is the squared Euclidean distance to the pole line. -/
theorem harmonicVar_poleGauge_poleResidual {N : ℕ} (_hN : 1 ≤ N) (y : ℕ → ℝ) :
    harmonicVar 0 N (poleGauge y) = ∑ n ∈ Icc 1 N, poleResidual N y n ^ 2 := by
  have hm : wMean (Icc 1 N) (fun n => 1 / (n : ℝ)) (poleGauge y) = poleCoord N y := by
    unfold wMean poleCoord gaugeHarmonicSum
    congr 1
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [poleGauge, truncPole_eq hn]
    have hs := (Real.sqrt_pos.mpr hn0).ne'
    dsimp only
    rw [show (1 : ℝ) / n = 1 / (Real.sqrt n * Real.sqrt n) by
      rw [Real.mul_self_sqrt hn0.le]]
    field_simp
  rw [harmonicVar, roughInterval_zero, wVar, hm]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hs := (Real.sqrt_pos.mpr hn0).ne'
  rw [poleGauge, poleResidual, truncPole_eq hn]
  have he : Real.sqrt n * y n - poleCoord N y =
      Real.sqrt n * (y n - poleCoord N y * (1 / Real.sqrt n)) := by
    field_simp
  rw [he, mul_pow, Real.sq_sqrt hn0.le]
  field_simp

/-- The projected gauge pole gives the exact squared-angle variance bound. -/
theorem harmonicCorrelation_sq_mul_mass_le_variance {ω : ℕ → ℝ}
    (hω : ∀ n, ω n * ω n = 1) {N : ℕ} (hN : 1 ≤ N) {x : ℕ → ℝ}
    (hx : ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0) :
    harmonicCorrelation ω N ^ 2 * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      harmonicVar 0 N (poleGauge (fun n => ω n * x n)) := by
  let H := gaugeHarmonicSum (fun _ => 1) N
  let S := gaugeHarmonicSum ω N
  let M := ∑ n ∈ Icc 1 N, x n ^ 2
  let T := ∑ n ∈ Icc 1 N, (ω n * x n) * truncPole N n
  have hH : 0 < H := gaugeHarmonicSum_one_pos hN
  have hxb : ∑ n ∈ Icc 1 N, x n * truncPole N n = 0 := by
    rw [← hx]
    exact sum_congr rfl fun n hn => by rw [truncPole_eq hn, mul_one_div]
  have hT : ∑ n ∈ Icc 1 N, x n * gaugeWitness ω N n = T := by
    have he : ∀ n, x n * gaugeWitness ω N n =
        (ω n * x n) * truncPole N n - (S / H) * (x n * truncPole N n) := by
      intro n
      dsimp [gaugeWitness, S, H]
      ring
    rw [sum_congr rfl (fun n _ => he n), sum_sub_distrib, ← mul_sum, hxb, mul_zero,
      sub_zero]
  have hc := sum_mul_sq_le_sq_mul_sq (Icc 1 N) x (gaugeWitness ω N)
  rw [hT, sum_gaugeWitness_sq hω hN] at hc
  change T ^ 2 ≤ M * (H - S ^ 2 / H) at hc
  have hmass : ∑ n ∈ Icc 1 N, (ω n * x n) ^ 2 = M :=
    sum_congr rfl fun n _ => by rw [mul_pow, sq (ω n), hω, one_mul]
  rw [harmonicVar_poleGauge_poleResidual hN, sum_poleResidual_sq hN, hmass]
  change (S / H) ^ 2 * M ≤ M - (T / H) ^ 2 * H
  have hd := (div_le_div_of_nonneg_right hc hH.le)
  have he₁ : (M * (H - S ^ 2 / H)) / H = M - (S / H) ^ 2 * M := by
    field_simp [hH.ne']
  have he₂ : T ^ 2 / H = (T / H) ^ 2 * H := by
    field_simp [hH.ne']
  rw [he₁, he₂] at hd
  linarith only [hd]

/-- A harmonic correlation is a cosine, so its square is at most one. -/
theorem harmonicCorrelation_sq_le_one {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    {N : ℕ} (hN : 1 ≤ N) : harmonicCorrelation ω N ^ 2 ≤ 1 := by
  have h := sum_gaugeWitness_sq (ω := ω) hω hN
  have hnn : 0 ≤ ∑ n ∈ Icc 1 N, gaugeWitness ω N n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  rw [h] at hnn
  have hH := gaugeHarmonicSum_one_pos hN
  have hs : gaugeHarmonicSum ω N ^ 2 / gaugeHarmonicSum (fun _ => 1) N ≤
      gaugeHarmonicSum (fun _ => 1) N := by linarith only [hnn]
  rw [div_le_iff₀ hH] at hs
  rw [harmonicCorrelation, div_pow, div_le_one (sq_pos_of_pos hH)]
  nlinarith only [hs]

/-- The projected gauge pole attains the squared-angle variance bound. This is
sharpness of the projection inequality, not an upper bound for the arithmetic gap. -/
theorem gaugeWitness_attains_variance_bound {ω : ℕ → ℝ}
    (hω : ∀ n, ω n * ω n = 1) {N : ℕ} (hN : 1 ≤ N) :
    harmonicVar 0 N (poleGauge (fun n => ω n * gaugeWitness ω N n)) =
      harmonicCorrelation ω N ^ 2 * ∑ n ∈ Icc 1 N, gaugeWitness ω N n ^ 2 := by
  let H := gaugeHarmonicSum (fun _ => 1) N
  let S := gaugeHarmonicSum ω N
  have hH : 0 < H := gaugeHarmonicSum_one_pos hN
  have hs : ∑ n ∈ Icc 1 N, ω n * truncPole N n ^ 2 = S := by
    exact sum_congr rfl fun n hn => by rw [truncPole_sq hn, mul_one_div]
  have hT : ∑ n ∈ Icc 1 N, (ω n * gaugeWitness ω N n) * truncPole N n =
      H - (S / H) * S := by
    have he : ∀ n, (ω n * gaugeWitness ω N n) * truncPole N n =
        truncPole N n ^ 2 - (S / H) * (ω n * truncPole N n ^ 2) := by
      intro n
      dsimp [gaugeWitness, S, H]
      linear_combination truncPole N n ^ 2 * hω n
    rw [sum_congr rfl (fun n _ => he n), sum_sub_distrib, ← mul_sum,
      sum_truncPole_sq, hs]
  have hmass : ∑ n ∈ Icc 1 N, (ω n * gaugeWitness ω N n) ^ 2 =
      ∑ n ∈ Icc 1 N, gaugeWitness ω N n ^ 2 :=
    sum_congr rfl fun n _ => by rw [mul_pow, sq (ω n), hω, one_mul]
  rw [harmonicVar_poleGauge_poleResidual hN, sum_poleResidual_sq hN, hmass,
    sum_gaugeWitness_sq hω hN, poleCoord, hT]
  change H - S ^ 2 / H - ((H - S / H * S) / H) ^ 2 * H =
    (S / H) ^ 2 * (H - S ^ 2 / H)
  field_simp [hH.ne']
  ring

/-- The prime-gap estimate is uniform over sign gauges, including gauges that vary with `N`. -/
theorem eventually_prime_gap_ge_squared_correlation {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ ω : ℕ → ℝ, (∀ n, ω n * ω n = 1) →
      ∀ x : ℕ → ℝ, (∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0) →
        atomicWeilForm N (fun n => ω n * x n) ≤
          (Real.log N - Real.eulerMascheroniConstant -
            2 * Real.log 2 * harmonicCorrelation ω N ^ 2 + ε) *
            ∑ n ∈ Icc 1 N, x n ^ 2 := by
  let g := 2 * Real.log 2
  have hg : 0 < g := mul_pos (by norm_num) (Real.log_pos one_lt_two)
  let δ := min (1 / 2 : ℝ) (min (g / 2) (ε / (g + 2)))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδg : δ ≤ g / 2 :=
    (min_le_right (1 / 2) _).trans (min_le_left (g / 2) _)
  have hδε : δ * (g + 2) ≤ ε := by
    have h := (min_le_right (g / 2) (ε / (g + 2))).trans' (min_le_right (1 / 2) _)
    exact (le_div_iff₀ (by positivity : 0 < g + 2)).mp h
  obtain ⟨N₁, hN₁⟩ := eventually_atomicWeilForm_add_poleDefect_le hδ
  obtain ⟨N₂, hN₂⟩ := eventually_mul_harmonicVar_le_poleDefect hδ
  refine ⟨max 1 (max N₁ N₂), fun N hN ω hω x hx => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN₁' : N₁ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN₂' : N₂ ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  let M := ∑ n ∈ Icc 1 N, x n ^ 2
  let c := harmonicCorrelation ω N ^ 2
  have hM : 0 ≤ M := sum_nonneg fun _ _ => sq_nonneg _
  have hc : 0 ≤ c := sq_nonneg _
  have hc1 : c ≤ 1 := harmonicCorrelation_sq_le_one hω hN1
  have hmass : ∑ n ∈ Icc 1 N, (ω n * x n) ^ 2 = M :=
    sum_congr rfl fun n _ => by rw [mul_pow, sq (ω n), hω, one_mul]
  have hp := hN₁ N hN₁' (fun n => ω n * x n)
  rw [hmass] at hp
  have hv := harmonicCorrelation_sq_mul_mass_le_variance hω hN1 hx
  have hD : (g - δ) * (c * M) ≤ poleDefect N (fun n => ω n * x n) :=
    (mul_le_mul_of_nonneg_left hv (by linarith only [hδg, hg])).trans
      (hN₂ N hN₂' (fun n => ω n * x n))
  have hpaid := mul_le_mul_of_nonneg_left hD
    (show 0 ≤ 1 - δ by linarith only [hδhalf])
  have hcoeff : g * c - (1 - δ) * ((g - δ) * c) + δ ≤ ε := by
    have hsmall := mul_le_mul_of_nonneg_left hc1
      (show 0 ≤ δ * (g + 1) by positivity)
    have hpos := mul_nonneg (sq_nonneg δ) hc
    nlinarith only [hsmall, hpos, hδε]
  have herr := mul_le_mul_of_nonneg_right hcoeff hM
  change atomicWeilForm N (fun n => ω n * x n) ≤
    (Real.log N - Real.eulerMascheroniConstant - g * c + ε) * M
  nlinarith only [hp, hpaid, herr]

end GaloisForLFunctions.ArithmeticCountingPositivity

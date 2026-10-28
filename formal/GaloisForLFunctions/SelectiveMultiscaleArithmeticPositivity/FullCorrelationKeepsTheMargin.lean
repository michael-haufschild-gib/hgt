import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheHyperplaneGapIsTheSelectiveMargin
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo

/-!
# Full correlation keeps the margin

For a sign gauge `ω² = 1` the margin is read on `ζ`'s hyperplane `x ⟂ b`, `b_n = n^{−1/2}`, through
`P_N(ωx)`. With `y = ωx` this is the prime form on the hyperplane `y ⟂ ωb`. When `ω` agrees with
`1` on a set of full harmonic density, `ωb` is nearly `b`, and the sharp gap of `ζ` survives.

* **Pole polarization** (`atomicWeilForm_smul_truncPole_add`):
  `P_N(αb + z) = α²P_N(b) + P_N(z) + 2α Σ_n R_n b_n z_n`, with rows `R_n` within a constant `B` of
  `log N − γ` (RenormalizedArithmeticPotentialTheory).
* **The misalignment cost** (`sq_sum_mul_truncPole_le`): for `y ⟂ ωb`, the pole coordinate obeys
  `(Σ y_n b_n)² ≤ |y|² · 2(H_N − S_N)`, where `H_N = Σ 1/n` and `S_N = Σ ω(n)/n`.
* **Full correlation keeps the margin** (`hasHyperplaneGap_two_mul_log_two_of_correlation`): if
  `S_N/H_N → 1`, the gauge has hyperplane gap `2 log 2`. Writing `y = αb + z` with `z ⟂ b`, the
  sharp gap pays `z`, the ceiling pays `αb`, the row deviations cost `α²H/t + tB²|z|²`, and
  `α²H ≤ |y|² · 2(1 − S_N/H_N) → 0`.
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

theorem truncPole_eq {N n : ℕ} (hn : n ∈ Icc 1 N) : truncPole N n = 1 / Real.sqrt n := by
  simp only [truncPole, if_pos (mem_Icc.mp hn).2, poleVector]

theorem truncPole_sq {N n : ℕ} (hn : n ∈ Icc 1 N) : truncPole N n ^ 2 = 1 / n := by
  rw [truncPole_eq hn, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- **The misalignment cost.** If `Σ y_n ω_n b_n = 0` with `ω² = 1`, then
`(Σ y_n b_n)² ≤ |y|² · 2(H_N − S_N)`. -/
theorem sq_sum_mul_truncPole_le {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1) (N : ℕ) {y : ℕ → ℝ}
    (hy : ∑ n ∈ Icc 1 N, y n * (ω n * truncPole N n) = 0) :
    (∑ n ∈ Icc 1 N, y n * truncPole N n) ^ 2 ≤
      (∑ n ∈ Icc 1 N, y n ^ 2) *
        (2 * (∑ n ∈ Icc 1 N, (1 : ℝ) / n - ∑ n ∈ Icc 1 N, ω n / n)) := by
  have e : ∑ n ∈ Icc 1 N, y n * truncPole N n =
      ∑ n ∈ Icc 1 N, y n * ((1 - ω n) * truncPole N n) := by
    rw [← sub_zero (∑ n ∈ Icc 1 N, y n * truncPole N n), ← hy, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  have hd : ∑ n ∈ Icc 1 N, ((1 - ω n) * truncPole N n) ^ 2 =
      2 * (∑ n ∈ Icc 1 N, (1 : ℝ) / n - ∑ n ∈ Icc 1 N, ω n / n) := by
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [mul_pow, truncPole_sq hn]
    have h1 : (1 - ω n) ^ 2 = 2 - 2 * ω n := by linear_combination hω n
    rw [h1]
    ring
  rw [e, ← hd]
  exact sum_mul_sq_le_sq_mul_sq _ _ _

/-- **Full correlation keeps the margin.** A sign gauge whose harmonic correlation with `ζ` tends
to `1`, `S_N/H_N → 1`, has hyperplane gap `2 log 2`. -/
theorem hasHyperplaneGap_two_mul_log_two_of_correlation {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hS : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ω n / n) / ∑ n ∈ Icc 1 N, (1 : ℝ) / n) atTop
      (𝓝 1)) :
    HasHyperplaneGap ω (2 * Real.log 2) := by
  intro ε hε
  set B := Real.log 4 + 4 + Real.log 2 + γ
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hB : 0 ≤ B := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the weight of the row-deviation estimate, and the admissible misalignment
  set t := ε / (4 * (B ^ 2 + 1))
  have ht : 0 < t := by positivity
  have htB1 : t * (B ^ 2 + 1) = ε / 4 := by simp only [t]; field_simp
  have htB : t * B ^ 2 ≤ ε / 4 := by
    rw [← htB1]; exact mul_le_mul_of_nonneg_left (by linarith) ht.le
  set c := 2 * Real.log 2 + 1 / t
  have hc : 0 < c := by positivity
  set δ := ε / (4 * c)
  have hδ : 0 < δ := by positivity
  have hcδ : c * δ = ε / 4 := by simp only [δ]; field_simp
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hS.eventually (Ioi_mem_nhds (show 1 - δ / 2 < 1 by linarith)))
  obtain ⟨N₂, hN₂⟩ := eventually_atomicWeilForm_le_two_log_two (show 0 < ε / 4 by positivity)
  set ε₁ := min (ε / 4) (1 / 2)
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by norm_num)
  have hε₁4 : ε₁ ≤ ε / 4 := min_le_left _ _
  have hε₁2 : ε₁ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨N₃, hN₃⟩ := eventually_atomicWeilForm_add_poleDefect_le hε₁
  refine ⟨max N₁ (max N₂ (max N₃ 1)), fun N hN x hx => ?_⟩
  have hN1' : N₁ ≤ N := le_of_max_le_left hN
  have hN2' : N₂ ≤ N := (le_max_left _ _).trans (le_of_max_le_right hN)
  have hN3' : N₃ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_of_max_le_right hN)
  have hN1 : 1 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_of_max_le_right hN)
  set H := ∑ n ∈ Icc 1 N, (1 : ℝ) / n
  set S := ∑ n ∈ Icc 1 N, ω n / n
  have hbsq : ∑ n ∈ Icc 1 N, truncPole N n ^ 2 = H := sum_congr rfl fun n hn => truncPole_sq hn
  have hH0 : 0 < H :=
    sum_pos (fun n hn => by have := (mem_Icc.mp hn).1; positivity) ⟨1, mem_Icc.mpr ⟨le_rfl, hN1⟩⟩
  -- `y = ωx` lies on the hyperplane `y ⟂ ωb`, with the mass of `x`
  set y : ℕ → ℝ := fun n => ω n * x n
  have hyy : ∑ n ∈ Icc 1 N, y n ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 :=
    sum_congr rfl fun n _ => by simp only [y]; rw [mul_pow, sq (ω n), hω, one_mul]
  set Y := ∑ n ∈ Icc 1 N, y n ^ 2
  have hY : 0 ≤ Y := sum_nonneg fun _ _ => sq_nonneg _
  have hyω : ∑ n ∈ Icc 1 N, y n * (ω n * truncPole N n) = 0 := by
    rw [← hx]
    refine sum_congr rfl fun n hn => ?_
    simp only [y]
    rw [truncPole_eq hn]
    linear_combination (x n / Real.sqrt n) * hω n
  -- split `y = αb + z` with `z ⟂ b`
  set p := ∑ n ∈ Icc 1 N, y n * truncPole N n
  set α := p / H
  have hpα : p = α * H := by simp only [α]; field_simp
  set z : ℕ → ℝ := fun n => y n - α * truncPole N n
  have hzb : ∑ n ∈ Icc 1 N, z n * truncPole N n = 0 := by
    calc ∑ n ∈ Icc 1 N, z n * truncPole N n
        = ∑ n ∈ Icc 1 N, (y n * truncPole N n - α * truncPole N n ^ 2) :=
          sum_congr rfl fun n _ => by simp only [z]; ring
      _ = p - α * H := by rw [sum_sub_distrib, ← mul_sum, hbsq]
      _ = 0 := by rw [hpα, sub_self]
  have hz : ∑ n ∈ Icc 1 N, z n / Real.sqrt n = 0 := by
    rw [← hzb]
    refine sum_congr rfl fun n hn => ?_
    rw [truncPole_eq hn, mul_one_div]
  have hzsq : ∑ n ∈ Icc 1 N, z n ^ 2 = Y - α ^ 2 * H := by
    calc ∑ n ∈ Icc 1 N, z n ^ 2
        = ∑ n ∈ Icc 1 N, (y n ^ 2 - 2 * α * (y n * truncPole N n) + α ^ 2 * truncPole N n ^ 2) :=
          sum_congr rfl fun n _ => by simp only [z]; ring
      _ = Y - 2 * α * p + α ^ 2 * H := by
          rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hbsq]
      _ = Y - α ^ 2 * H := by rw [hpα]; ring
  have hαH0 : 0 ≤ α ^ 2 * H := by positivity
  -- the misalignment: `α²H ≤ |y|² · 2(H − S)/H ≤ δ|y|²`
  have hp : p ^ 2 ≤ Y * (2 * (H - S)) := sq_sum_mul_truncPole_le hω N hyω
  have hαH : α ^ 2 * H ≤ Y * δ := by
    have h : 1 - δ / 2 < S / H := hN₁ N hN1'
    rw [lt_div_iff₀ hH0] at h
    have hD : 2 * (H - S) ≤ δ * H := by linarith
    have e : p ^ 2 = α ^ 2 * H * H := by rw [hpα]; ring
    have h2 : α ^ 2 * H * H ≤ Y * δ * H := by
      rw [← e]
      calc p ^ 2 ≤ Y * (2 * (H - S)) := hp
        _ ≤ Y * (δ * H) := mul_le_mul_of_nonneg_left hD hY
        _ = Y * δ * H := by ring
    exact le_of_mul_le_mul_right h2 hH0
  -- the pole polarization of `y = αb + z`
  have hyz : (fun n => α * truncPole N n + z n) = y := funext fun n => by simp only [z]; ring
  have hP := atomicWeilForm_smul_truncPole_add N α z
  rw [hyz] at hP
  -- the row deviations cost at most `α²H/t + tB²|z|²`
  have hE : 2 * α * ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * z n ≤
      α ^ 2 * H / t + t * B ^ 2 * ∑ n ∈ Icc 1 N, z n ^ 2 := by
    have hsplit : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * z n =
        ∑ n ∈ Icc 1 N,
          (mertensSum (N / n) + Real.log n - (Real.log N - γ)) * truncPole N n * z n := by
      have : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * z n -
          ∑ n ∈ Icc 1 N,
            (mertensSum (N / n) + Real.log n - (Real.log N - γ)) * truncPole N n * z n =
          (Real.log N - γ) * ∑ n ∈ Icc 1 N, z n * truncPole N n := by
        rw [← sum_sub_distrib, mul_sum]
        exact sum_congr rfl fun n _ => by ring
      rw [hzb, mul_zero] at this
      linarith
    have hpt : ∀ n ∈ Icc 1 N,
        2 * α * ((mertensSum (N / n) + Real.log n - (Real.log N - γ)) * truncPole N n * z n) ≤
          α ^ 2 * truncPole N n ^ 2 / t + t * B ^ 2 * z n ^ 2 := by
      intro n hn
      set r := mertensSum (N / n) + Real.log n - (Real.log N - γ)
      set a := truncPole N n
      have hRn : |r| ≤ B := abs_row_sub_le hn
      have h1 : 2 * α * (r * a * z n) ≤ 2 * (|α| * |a|) * (B * |z n|) := by
        calc 2 * α * (r * a * z n) ≤ |2 * α * (r * a * z n)| := le_abs_self _
          _ = 2 * (|α| * |a|) * (|r| * |z n|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]; ring
          _ ≤ 2 * (|α| * |a|) * (B * |z n|) := by gcongr
      have h2 := sq_nonneg (|α| * |a| - t * (B * |z n|))
      have e2 : (|α| * |a| - t * (B * |z n|)) ^ 2 =
          α ^ 2 * a ^ 2 - 2 * (|α| * |a|) * (B * |z n|) * t + t ^ 2 * B ^ 2 * z n ^ 2 := by
        calc (|α| * |a| - t * (B * |z n|)) ^ 2 = |α| ^ 2 * |a| ^ 2 -
              2 * (|α| * |a|) * (B * |z n|) * t + t ^ 2 * B ^ 2 * |z n| ^ 2 := by ring
          _ = _ := by rw [sq_abs, sq_abs, sq_abs]
      rw [e2] at h2
      have h3 : 2 * (|α| * |a|) * (B * |z n|) * t ≤
          (α ^ 2 * a ^ 2 / t + t * B ^ 2 * z n ^ 2) * t := by
        rw [add_mul (α ^ 2 * a ^ 2 / t), div_mul_cancel₀ _ ht.ne']
        linarith
      linarith [le_of_mul_le_mul_right h3 ht]
    rw [hsplit, mul_sum]
    calc ∑ n ∈ Icc 1 N,
          2 * α * ((mertensSum (N / n) + Real.log n - (Real.log N - γ)) * truncPole N n * z n)
        ≤ ∑ n ∈ Icc 1 N, (α ^ 2 * truncPole N n ^ 2 / t + t * B ^ 2 * z n ^ 2) :=
          sum_le_sum hpt
      _ = α ^ 2 * H / t + t * B ^ 2 * ∑ n ∈ Icc 1 N, z n ^ 2 := by
        rw [sum_add_distrib, ← sum_div, ← mul_sum, ← mul_sum, hbsq]
  -- the ceiling pays the pole part, the sharp gap pays `z`
  have hPb : atomicWeilForm N (truncPole N) ≤ (Real.log N - γ + ε₁) * H := by
    have h := hN₃ N hN3' (truncPole N)
    rw [hbsq] at h
    have := mul_nonneg (show (0 : ℝ) ≤ 1 - ε₁ by linarith) (poleDefect_nonneg N (truncPole N))
    linarith
  have hPz : atomicWeilForm N z ≤ (Real.log N - γ - 2 * Real.log 2 + ε / 4) * (Y - α ^ 2 * H) := by
    rw [← hzsq]; exact hN₂ N hN2' z hz
  have h1 : α ^ 2 * atomicWeilForm N (truncPole N) ≤ α ^ 2 * ((Real.log N - γ + ε₁) * H) :=
    mul_le_mul_of_nonneg_left hPb (sq_nonneg α)
  have hzY : ∑ n ∈ Icc 1 N, z n ^ 2 ≤ Y := by linarith
  have h2 : t * B ^ 2 * ∑ n ∈ Icc 1 N, z n ^ 2 ≤ ε / 4 * Y :=
    (mul_le_mul_of_nonneg_left hzY (by positivity)).trans (mul_le_mul_of_nonneg_right htB hY)
  have h3 : (2 * Real.log 2 + 1 / t) * (α ^ 2 * H) ≤ ε / 4 * Y := by
    calc (2 * Real.log 2 + 1 / t) * (α ^ 2 * H) ≤ c * (Y * δ) :=
          mul_le_mul_of_nonneg_left hαH hc.le
      _ = ε / 4 * Y := by rw [← hcδ]; ring
  have h4 : (ε₁ - ε / 4) * (α ^ 2 * H) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hαH0
  have h5 : α ^ 2 * H / t = 1 / t * (α ^ 2 * H) := by ring
  have h6 : 0 ≤ ε / 4 * Y := by positivity
  change atomicWeilForm N y ≤ _
  rw [hP, ← hyy]
  linarith

theorem abs_eq_one_of_mul_self_eq_one' {a : ℝ} (h : a * a = 1) : |a| = 1 := by
  have h2 : |a| * |a| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg a]

/-- **Finite flips keep the margin**: a sign gauge equal to `1` from some point on has hyperplane
gap `2 log 2`. -/
theorem hasHyperplaneGap_two_mul_log_two_of_eventually_eq_one {ω : ℕ → ℝ}
    (hω : ∀ n, ω n * ω n = 1) {M : ℕ} (hM : ∀ n, M ≤ n → ω n = 1) :
    HasHyperplaneGap ω (2 * Real.log 2) := by
  refine hasHyperplaneGap_two_mul_log_two_of_correlation hω ?_
  have hHnn : ∀ N : ℕ, 0 ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / n := fun N => sum_nonneg fun _ _ => by positivity
  -- `H_N − S_N` is bounded by `C = 2 Σ_{n ≤ M} 1/n`
  set C := 2 * ∑ n ∈ Icc 1 M, (1 : ℝ) / n
  have hdiff : ∀ N : ℕ, |∑ n ∈ Icc 1 N, (1 : ℝ) / n - ∑ n ∈ Icc 1 N, ω n / n| ≤ C := by
    intro N
    have hle : ∀ n ∈ Icc 1 N, |(1 : ℝ) / n - ω n / n| ≤ if n ≤ M then 2 / (n : ℝ) else 0 := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      split_ifs with h
      · rw [← sub_div, abs_div, abs_of_pos hn0]
        refine div_le_div_of_nonneg_right ?_ hn0.le
        calc |1 - ω n| ≤ |(1 : ℝ)| + |ω n| := abs_sub _ _
          _ = 2 := by rw [abs_one, abs_eq_one_of_mul_self_eq_one' (hω n)]; norm_num
      · rw [hM n (by omega), sub_self, abs_zero]
    calc |∑ n ∈ Icc 1 N, (1 : ℝ) / n - ∑ n ∈ Icc 1 N, ω n / n|
        = |∑ n ∈ Icc 1 N, ((1 : ℝ) / n - ω n / n)| := by rw [sum_sub_distrib]
      _ ≤ ∑ n ∈ Icc 1 N, |(1 : ℝ) / n - ω n / n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, (if n ≤ M then 2 / (n : ℝ) else 0) := sum_le_sum hle
      _ ≤ ∑ n ∈ Icc 1 M, 2 / (n : ℝ) := by
        rw [← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => by positivity)
        simp only [mem_filter, mem_Icc] at hn ⊢
        omega
      _ = C := by simp only [C, mul_sum]; exact sum_congr rfl fun n _ => by ring
  -- `H_N → ∞`
  have hHtop : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, (1 : ℝ) / n) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
    have h := log_add_one_le_harmonic N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simp only [Function.comp_apply, one_div]
    exact h
  -- `(H_N − S_N)/H_N → 0`
  have hq : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (1 : ℝ) / n - ∑ n ∈ Icc 1 N, ω n / n) /
      ∑ n ∈ Icc 1 N, (1 : ℝ) / n) atTop (𝓝 0) := by
    have hC : Tendsto (fun N : ℕ => C * (∑ n ∈ Icc 1 N, (1 : ℝ) / n)⁻¹) atTop (𝓝 0) := by
      simpa using hHtop.inv_tendsto_atTop.const_mul C
    refine squeeze_zero_norm (fun N => ?_) hC
    rw [Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_nonneg (inv_nonneg.mpr (hHnn N))]
    exact mul_le_mul_of_nonneg_right (hdiff N) (inv_nonneg.mpr (hHnn N))
  -- `S_N/H_N = 1 − (H_N − S_N)/H_N` for `N ≥ 1`
  have hev : (fun N : ℕ => 1 - (∑ n ∈ Icc 1 N, (1 : ℝ) / n - ∑ n ∈ Icc 1 N, ω n / n) /
      ∑ n ∈ Icc 1 N, (1 : ℝ) / n) =ᶠ[atTop]
      fun N : ℕ => (∑ n ∈ Icc 1 N, ω n / n) / ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h0 : ∑ n ∈ Icc 1 N, (1 : ℝ) / n ≠ 0 :=
      (sum_pos (fun n hn => by have := (mem_Icc.mp hn).1; positivity)
        ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩⟩).ne'
    rw [eq_div_iff h0, sub_mul, div_mul_cancel₀ _ h0]
    ring
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub hq
  rw [sub_zero] at h1
  exact h1.congr' hev

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

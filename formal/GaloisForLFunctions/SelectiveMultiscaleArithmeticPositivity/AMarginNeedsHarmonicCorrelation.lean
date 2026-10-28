import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheHyperplaneGapIsTheSelectiveMargin

/-!
# A margin needs harmonic correlation

The prime forms `P_N(x)` and `P_N(ωx)` of a sign gauge `ω² = 1` are unitarily equivalent; their
tops point along the pole `b_n = n^{−1/2}` and along `ω_n b_n`. The pole hyperplane cuts off the
first. It cuts off the second only as far as the two directions correlate, and that correlation
is the harmonic sum `S_N(ω) = Σ_{n ≤ N} ω(n)/n` (`gaugeHarmonicSum`) against `H_N = S_N(1)`.

* **The ceiling witness** (`gaugeWitness`, `eventually_exists_gauge_ceiling_witness`): the gauge's
  top projected onto the pole hyperplane, `x_n = (ω_n − S_N/H_N) b_n`, has mass `H_N − S_N²/H_N`
  and `P_N(ωx) ≥ P_N(b) − O(S_N² + 1)` (`atomicWeilForm_gaugeWitness_ge`), read off the
  ground-state identity polarized at the pole (RenormalizedArithmeticPotentialTheory). If
  `S_N² = o(log N)` it reaches the ceiling: `P_N(ωx) ≥ (log N − γ − ε)|x|²`.
* **No margin without correlation** (`not_hasHyperplaneGap_of_harmonicSum_small`): such a gauge has
  no positive hyperplane gap. Bounded harmonic sums suffice
  (`not_hasHyperplaneGap_of_abs_harmonicSum_le`), which recovers the Liouville twin.
* **Contrapositive** (`frequently_harmonicSum_sq_ge_of_hasHyperplaneGap`): a sign gauge with a
  positive margin has `S_N(ω)² ≥ c log N` for some `c > 0` and infinitely many `N`.

So the margin `2 log 2` of `ζ` (`S_N = H_N`) is carried by its correlation with the pole, and every
sign gauge that decorrelates from it faster than `√log N` is at the ceiling.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

theorem abs_eq_one_of_mul_self_eq_one {a : ℝ} (h : a * a = 1) : |a| = 1 := by
  have h2 : |a| * |a| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg a]

/-- The harmonic correlation `S_N(ω) = Σ_{n ≤ N} ω(n)/n` of a gauge with `ζ`; `S_N(1) = H_N`. -/
def gaugeHarmonicSum (ω : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, ω n / n

theorem truncPole_eq {N n : ℕ} (hn : n ∈ Icc 1 N) : truncPole N n = 1 / Real.sqrt n := by
  simp only [truncPole, if_pos (mem_Icc.mp hn).2, poleVector]

theorem truncPole_sq {N n : ℕ} (hn : n ∈ Icc 1 N) : truncPole N n ^ 2 = 1 / n := by
  rw [truncPole_eq hn, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The pole has mass `H_N`. -/
theorem sum_truncPole_sq (N : ℕ) :
    ∑ n ∈ Icc 1 N, truncPole N n ^ 2 = gaugeHarmonicSum (fun _ => 1) N :=
  sum_congr rfl fun n hn => truncPole_sq hn

theorem gaugeHarmonicSum_one_pos {N : ℕ} (hN : 1 ≤ N) : 0 < gaugeHarmonicSum (fun _ => 1) N :=
  sum_pos (fun n hn => by have := (mem_Icc.mp hn).1; positivity) ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩⟩

theorem log_le_gaugeHarmonicSum_one {N : ℕ} (hN : 1 ≤ N) :
    Real.log N ≤ gaugeHarmonicSum (fun _ => 1) N := by
  have h := log_add_one_le_harmonic N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast hN) (by linarith)
  simp only [gaugeHarmonicSum, one_div]
  linarith

section Witness

variable {ω : ℕ → ℝ} {N : ℕ}

local notation "𝓗" => gaugeHarmonicSum (fun _ => 1) N
local notation "𝓢" => gaugeHarmonicSum ω N

/-- The gauge's top `ω_n b_n` projected onto the pole hyperplane, in the coordinates of `ζ`:
`x_n = (ω_n − S_N/H_N) b_n`. -/
def gaugeWitness (ω : ℕ → ℝ) (N n : ℕ) : ℝ :=
  (ω n - gaugeHarmonicSum ω N / gaugeHarmonicSum (fun _ => 1) N) * truncPole N n

/-- The witness lies on the pole hyperplane. -/
theorem sum_gaugeWitness_div_sqrt (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, gaugeWitness ω N n / Real.sqrt n = 0 := by
  have hH := (gaugeHarmonicSum_one_pos hN).ne'
  have e : ∀ n ∈ Icc 1 N, gaugeWitness ω N n / Real.sqrt n = ω n / n - 𝓢 / 𝓗 * (1 / n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [gaugeWitness, truncPole_eq hn, mul_one_div, div_div, Real.mul_self_sqrt hn0.le]
    ring
  rw [sum_congr rfl e, sum_sub_distrib, ← mul_sum]
  change 𝓢 - 𝓢 / 𝓗 * 𝓗 = 0
  rw [div_mul_cancel₀ _ hH, sub_self]

/-- The witness has mass `H_N − S_N²/H_N`. -/
theorem sum_gaugeWitness_sq (hω : ∀ n, ω n * ω n = 1) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, gaugeWitness ω N n ^ 2 = 𝓗 - 𝓢 ^ 2 / 𝓗 := by
  have hH := (gaugeHarmonicSum_one_pos hN).ne'
  have e : ∀ n ∈ Icc 1 N, gaugeWitness ω N n ^ 2 =
      1 / n - 2 * (𝓢 / 𝓗) * (ω n / n) + (𝓢 / 𝓗) ^ 2 * (1 / n) := by
    intro n hn
    rw [gaugeWitness, mul_pow, truncPole_sq hn]
    have : (ω n - 𝓢 / 𝓗) ^ 2 = 1 - 2 * (𝓢 / 𝓗) * ω n + (𝓢 / 𝓗) ^ 2 := by
      linear_combination hω n
    rw [this]
    ring
  rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  change 𝓗 - 2 * (𝓢 / 𝓗) * 𝓢 + (𝓢 / 𝓗) ^ 2 * 𝓗 = 𝓗 - 𝓢 ^ 2 / 𝓗
  have hsH : 𝓢 / 𝓗 * 𝓗 = 𝓢 := div_mul_cancel₀ _ hH
  have hS2 : 𝓢 ^ 2 / 𝓗 = 𝓢 / 𝓗 * 𝓢 := by ring
  rw [hS2]
  linear_combination (𝓢 / 𝓗) * hsH

/-- The gauge of the witness is the pole minus `S_N/H_N` times the gauge's top. -/
theorem gauge_mul_gaugeWitness (hω : ∀ n, ω n * ω n = 1) :
    (fun n => ω n * gaugeWitness ω N n) =
      fun n => truncPole N n + -(𝓢 / 𝓗) * (ω n * truncPole N n) := by
  funext n
  rw [gaugeWitness]
  linear_combination truncPole N n * hω n

/-- **The prime form at the witness**: the projection costs `(S/H)²(log N + C₀)H` through the
bottom of the twisted top, and `2|S/H|((log N + γ)|S| + BH)` through the rows of the prime form. -/
theorem atomicWeilForm_gaugeWitness_ge (hω : ∀ n, ω n * ω n = 1) (hN : 1 ≤ N) :
    atomicWeilForm N (truncPole N) - (𝓢 / 𝓗) ^ 2 * ((Real.log N + (Real.log 4 + 4)) * 𝓗) -
        2 * (|𝓢 / 𝓗| * ((Real.log N + γ) * |𝓢| + (Real.log 4 + 4 + Real.log 2 + γ) * 𝓗)) ≤
      atomicWeilForm N (fun n => ω n * gaugeWitness ω N n) := by
  rw [gauge_mul_gaugeWitness hω, atomicWeilForm_truncPole_add]
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  -- the twisted top has mass `H` and the bottom of the prime form bounds it below
  have hlb2 : ∑ n ∈ Icc 1 N, (ω n * truncPole N n) ^ 2 = 𝓗 := by
    rw [← sum_truncPole_sq]
    exact sum_congr rfl fun n _ => by rw [mul_pow, show ω n ^ 2 = 1 by rw [sq, hω], one_mul]
  have hPu : -((𝓢 / 𝓗) ^ 2 * ((Real.log N + (Real.log 4 + 4)) * 𝓗)) ≤
      atomicWeilForm N (fun n => -(𝓢 / 𝓗) * (ω n * truncPole N n)) := by
    rw [atomicWeilForm_smul, neg_sq]
    have hbot := fixedPoint_bottom_ge (κ := -1) (by norm_num) N (fun n => ω n * truncPole N n)
    rw [hlb2] at hbot
    have e : ((-1 : ℝ) - 1 / -1) = 0 := by norm_num
    rw [e, zero_mul, zero_add] at hbot
    have h2 : -((Real.log N + (Real.log 4 + 4)) * 𝓗) ≤
        atomicWeilForm N (fun n => ω n * truncPole N n) := by linarith only [hbot]
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg (𝓢 / 𝓗))
    linarith only [this]
  -- the cross term: rows within `B` of `log N − γ`
  have hcross : |∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n *
      (-(𝓢 / 𝓗) * (ω n * truncPole N n))| ≤
      |𝓢 / 𝓗| * ((Real.log N + γ) * |𝓢| + (Real.log 4 + 4 + Real.log 2 + γ) * 𝓗) := by
    have e : ∀ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n *
        (-(𝓢 / 𝓗) * (ω n * truncPole N n)) =
        -(𝓢 / 𝓗) * ((Real.log N - γ) * (ω n / n) +
          (mertensSum (N / n) + Real.log n - (Real.log N - γ)) * (ω n * (1 / n))) := by
      intro n hn
      have : (mertensSum (N / n) + Real.log n) * truncPole N n *
          (-(𝓢 / 𝓗) * (ω n * truncPole N n)) =
          -(𝓢 / 𝓗) * ((mertensSum (N / n) + Real.log n) * ω n * truncPole N n ^ 2) := by ring
      rw [this, truncPole_sq hn]
      ring
    rw [sum_congr rfl e, ← mul_sum, abs_mul, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [sum_add_distrib, ← mul_sum]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      have : |Real.log N - γ| ≤ Real.log N + γ := by
        rw [abs_le]; constructor <;> linarith only [hL, hγ]
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    · refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [show (Real.log 4 + 4 + Real.log 2 + γ) * 𝓗 =
          ∑ n ∈ Icc 1 N, (Real.log 4 + 4 + Real.log 2 + γ) * (1 / (n : ℝ)) by
        simp only [gaugeHarmonicSum, mul_sum]]
      refine sum_le_sum fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [abs_mul, abs_mul, abs_eq_one_of_mul_self_eq_one (hω n), one_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
      exact mul_le_mul_of_nonneg_right (abs_row_sub_le hn) (by positivity)
  have hcr := (abs_le.mp hcross).1
  linarith only [hPu, hcr]

end Witness

/-- **The arithmetic of the ceiling witness.** If `S² ≤ ηL`, `η(4 + C₀ + 2γ) = ε/4` and
`B² ≤ εL/4`, the projection costs at most `εL/2 ≤ εH/2`, and the witness stays within `ε` of the
ceiling. -/
theorem ceilingWitness_arith {L g ε H S P C₀ B η : ℝ} (hg : 0 < g) (hε : 0 < ε) (hC₀ : 0 ≤ C₀)
    (hLH : L ≤ H) (hL3 : 3 ≤ L) (hLg : g + ε ≤ L) (hSL : S ^ 2 ≤ η * L)
    (hηκ : η * (4 + C₀ + 2 * g) = ε / 4) (hB2 : B ^ 2 ≤ ε / 4 * L)
    (hP : (L - g - ε / 2) * H ≤ P) :
    (L - g - ε) * (H - S ^ 2 / H) ≤
      P - (S / H) ^ 2 * ((L + C₀) * H) - 2 * (|S / H| * ((L + g) * |S| + B * H)) := by
  have hH : 0 < H := by linarith only [hLH, hL3]
  have hH1 : 1 ≤ H := by linarith only [hLH, hL3]
  have hS : S = S / H * H := (div_mul_cancel₀ S hH.ne').symm
  have hSabs : |S| = |S / H| * H := by
    conv_lhs => rw [hS]
    rw [abs_mul, abs_of_pos hH]
  -- the bottom cost `T₁ ≤ S²(1 + C₀)`
  have hT1 : (S / H) ^ 2 * ((L + C₀) * H) ≤ S ^ 2 * (1 + C₀) := by
    have a1 := mul_le_mul_of_nonneg_right hLH hH.le
    have a2 := mul_le_mul_of_nonneg_left hH1 (mul_nonneg hC₀ hH.le)
    have h1 : (L + C₀) * H ≤ H ^ 2 * (1 + C₀) := by linarith only [a1, a2]
    calc (S / H) ^ 2 * ((L + C₀) * H) ≤ (S / H) ^ 2 * (H ^ 2 * (1 + C₀)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = (S / H * H) ^ 2 * (1 + C₀) := by ring
      _ = S ^ 2 * (1 + C₀) := by rw [← hS]
  -- the row cost `T₂ ≤ S²(3 + 2γ) + B²`
  have hT2 : 2 * (|S / H| * ((L + g) * |S| + B * H)) ≤ S ^ 2 * (3 + 2 * g) + B ^ 2 := by
    have e : |S / H| * ((L + g) * |S| + B * H) = |S / H| ^ 2 * (H * (L + g)) + B * |S| := by
      rw [hSabs]; ring
    have a1 := mul_le_mul_of_nonneg_left hLH hH.le
    have a2 := mul_le_mul_of_nonneg_left hH1 (mul_nonneg hH.le hg.le)
    have h1 : H * (L + g) ≤ H ^ 2 * (1 + g) := by linarith only [a1, a2]
    have h2 : |S / H| ^ 2 * (H * (L + g)) ≤ S ^ 2 * (1 + g) := by
      calc |S / H| ^ 2 * (H * (L + g)) ≤ |S / H| ^ 2 * (H ^ 2 * (1 + g)) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = (|S / H| * H) ^ 2 * (1 + g) := by ring
        _ = S ^ 2 * (1 + g) := by rw [← hSabs, sq_abs]
    have h3 : 2 * (B * |S|) ≤ S ^ 2 + B ^ 2 := by
      have h := sq_nonneg (B - |S|)
      rw [sub_sq, sq_abs] at h
      linarith only [h]
    rw [e]
    linarith only [h2, h3]
  have hκS : S ^ 2 * (4 + C₀ + 2 * g) ≤ ε / 4 * L := by
    have h := mul_le_mul_of_nonneg_right hSL
      (show (0 : ℝ) ≤ 4 + C₀ + 2 * g by linarith only [hC₀, hg])
    have e : η * L * (4 + C₀ + 2 * g) = ε / 4 * L := by rw [mul_right_comm, hηκ]
    linarith only [h, e]
  have hSH : 0 ≤ S ^ 2 / H := div_nonneg (sq_nonneg S) hH.le
  have h3 : (L - g - ε) * (H - S ^ 2 / H) ≤ (L - g - ε) * H :=
    mul_le_mul_of_nonneg_left (by linarith only [hSH]) (by linarith only [hLg])
  have h4 : ε / 2 * L ≤ ε / 2 * H := mul_le_mul_of_nonneg_left hLH (by linarith only [hε])
  linarith only [h3, h4, hP, hT1, hT2, hκS, hB2]

/-- **The ceiling witness.** If `S_N(ω)²/log N → 0`, then for every `ε > 0`, eventually in `N`,
some nonzero `x` on the pole hyperplane has `P_N(ωx) ≥ (log N − γ − ε)|x|²`. -/
theorem eventually_exists_gauge_ceiling_witness {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hS : Tendsto (fun N : ℕ => gaugeHarmonicSum ω N ^ 2 / Real.log N) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧
      0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
      (Real.log N - γ - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ atomicWeilForm N (fun n => ω n * x n) := by
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hC₀ : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = 4 + (Real.log 4 + 4) + 2 * γ := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκ_def]; linarith
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = ε / (4 * κ) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; positivity
  have hηκ : η * (4 + (Real.log 4 + 4) + 2 * γ) = ε / 4 := by
    rw [← hκ_def, hη_def]; field_simp
  obtain ⟨N₂, hN₂⟩ := eventually_atomicWeilForm_truncPole_ge (show 0 < ε / 2 by positivity)
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp (hS.eventually (Iic_mem_nhds hη))
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop |>.eventually_ge_atTop
      (max (γ + ε) (max (4 * (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 / ε) (3 + η))))
  refine ⟨max N₂ (max N₃ N₄), fun N hN => ?_⟩
  have hN3 := hN₃ N ((le_max_left _ _).trans (le_of_max_le_right hN))
  simp only [Function.comp_apply] at hN3
  have hLγ : γ + ε ≤ Real.log N := (le_max_left _ _).trans hN3
  have hLB : 4 * (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 / ε ≤ Real.log N :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hN3
  have hL3 : 3 + η ≤ Real.log N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN3
  have hLpos : 0 < Real.log N := by linarith only [hL3, hη]
  have hN1 : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    rw [this, Nat.cast_zero, Real.log_zero] at hLpos
    exact lt_irrefl 0 hLpos
  have hSL : gaugeHarmonicSum ω N ^ 2 ≤ η * Real.log N := by
    have h := hN₄ N ((le_max_right _ _).trans (le_of_max_le_right hN))
    rwa [div_le_iff₀ hLpos] at h
  have hB2 : (Real.log 4 + 4 + Real.log 2 + γ) ^ 2 ≤ ε / 4 * Real.log N := by
    rw [div_le_iff₀ hε] at hLB
    linarith only [hLB]
  have hPb : (Real.log N - γ - ε / 2) * gaugeHarmonicSum (fun _ => 1) N ≤
      atomicWeilForm N (truncPole N) := by
    have h := hN₂ N (le_of_max_le_left hN)
    rwa [sum_truncPole_sq] at h
  have hHL := log_le_gaugeHarmonicSum_one hN1
  have hH0 := gaugeHarmonicSum_one_pos hN1
  refine ⟨gaugeWitness ω N, sum_gaugeWitness_div_sqrt hN1, ?_, ?_⟩
  · -- `S² ≤ ηL < L² ≤ H²`
    rw [sum_gaugeWitness_sq hω hN1]
    have h1 : η * Real.log N < Real.log N * Real.log N :=
      mul_lt_mul_of_pos_right (by linarith only [hL3]) hLpos
    have h2 := mul_le_mul hHL hHL hLpos.le hH0.le
    have h3 : gaugeHarmonicSum ω N ^ 2 / gaugeHarmonicSum (fun _ => 1) N <
        gaugeHarmonicSum (fun _ => 1) N := by
      rw [div_lt_iff₀ hH0]
      linarith only [hSL, h1, h2]
    linarith only [h3]
  · rw [sum_gaugeWitness_sq hω hN1]
    exact (ceilingWitness_arith hγ hε hC₀ hHL (by linarith only [hL3, hη]) hLγ hSL hηκ hB2
      hPb).trans (atomicWeilForm_gaugeWitness_ge hω hN1)

/-- **No margin without harmonic correlation**: a sign gauge with `S_N(ω)²/log N → 0` has no
positive hyperplane gap. -/
theorem not_hasHyperplaneGap_of_harmonicSum_small {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hS : Tendsto (fun N : ℕ => gaugeHarmonicSum ω N ^ 2 / Real.log N) atTop (𝓝 0))
    {g : ℝ} (hg : 0 < g) : ¬ HasHyperplaneGap ω g := by
  intro h
  obtain ⟨N₁, hN₁⟩ := h (g / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_exists_gauge_ceiling_witness hω hS (show 0 < g / 4 by positivity)
  obtain ⟨x, hx, hmass, hge⟩ := hN₂ (max N₁ N₂) (le_max_right _ _)
  have hle := hN₁ (max N₁ N₂) (le_max_left _ _) x hx
  have h2 := le_of_mul_le_mul_right (hge.trans hle) hmass
  linarith only [h2, hg]

/-- Bounded harmonic sums are `o(√log N)`. -/
theorem tendsto_harmonicSum_sq_div_log_of_abs_le {ω : ℕ → ℝ} {M : ℝ}
    (hM : ∀ N, |gaugeHarmonicSum ω N| ≤ M) :
    Tendsto (fun N : ℕ => gaugeHarmonicSum ω N ^ 2 / Real.log N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun N : ℕ => M ^ 2 / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun N => div_nonneg (sq_nonneg _) (Real.log_natCast_nonneg N)) (fun N => ?_)
  refine div_le_div_of_nonneg_right ?_ (Real.log_natCast_nonneg N)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hM N) 2

/-- A sign gauge with bounded harmonic sums has no positive hyperplane gap. -/
theorem not_hasHyperplaneGap_of_abs_harmonicSum_le {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1) {M : ℝ}
    (hM : ∀ N, |gaugeHarmonicSum ω N| ≤ M) {g : ℝ} (hg : 0 < g) : ¬ HasHyperplaneGap ω g :=
  not_hasHyperplaneGap_of_harmonicSum_small hω (tendsto_harmonicSum_sq_div_log_of_abs_le hM) hg

/-- The Liouville twin, recovered: `|Σ_{n ≤ N} λ(n)/n| ≤ 2`. -/
theorem not_liouville_hasHyperplaneGap' {g : ℝ} (hg : 0 < g) :
    ¬ HasHyperplaneGap liouvilleSign g :=
  not_hasHyperplaneGap_of_abs_harmonicSum_le liouvilleSign_mul_self abs_sum_liouvilleSign_div_le hg

/-- **A positive margin forces harmonic correlation**: if a sign gauge has a positive hyperplane
gap, then `S_N(ω)² ≥ c log N` for some `c > 0` and infinitely many `N`. -/
theorem frequently_harmonicSum_sq_ge_of_hasHyperplaneGap {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    {g : ℝ} (hg : 0 < g) (h : HasHyperplaneGap ω g) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ N : ℕ in atTop, c * Real.log N ≤ gaugeHarmonicSum ω N ^ 2 := by
  by_contra hne
  simp only [not_exists, not_and, not_frequently, not_le] at hne
  refine not_hasHyperplaneGap_of_harmonicSum_small hω ?_ hg h
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hne (δ / 2) (by positivity)).and
    (eventually_gt_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hlt, h1⟩ := hN₀ N hN
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast h1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (sq_nonneg _) hL.le), div_lt_iff₀ hL]
  linarith only [hlt, mul_pos hδ hL]

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PolarMatchingReadsTheDensityOfTheGauge

/-!
# Polar matching needs only the leading order

The matching law (`abs_gaugeForm_stepProfile_sub_le`) assumes `A_ε(y) = κ log y + O(1)` for all
`y`. This file identifies the remainder of the law exactly and shows what weaker inputs give.

Write `E(y) = A_ε(y) − κ log y` for the **Mertens error** of a sign gauge (`gaugeMertensError`).

* **The transfer law** (`abs_primeBilinear_gaugeTrunc_sub_transfer_le`): for every sign gauge,
  every `|κ| ≤ 1` and `1 ≤ M ≤ M' ≤ N`,
  `⟨εu^{(M)}, P εu^{(M')}⟩ = κ H_M H_{M'} + Σ_{m ≤ M} (E(⌊M'/m⌋) + E(⌊M/m⌋))/m + O(H_M)`, with
  `O(H_M)` at most `(2 log 2 + 4) H_M` and no hypothesis on `ε`: the horizon remainder is the
  harmonic convolution of the Mertens error.
* **The local law** (`abs_primeBilinear_gaugeTrunc_sub_le_local`): the Gram at cutoffs `≤ M'` sees
  `A_ε` only on `[1, M']`; `|E| ≤ g` there gives the bound `(2g + 2 log 2 + 4) H_M`.
* **The soft law** (`gaugeForm_stepProfile_soft`, `gaugeForm_stepProfile_of_tendsto`): if
  `A_ε(y)/log y → κ`, then for every `η > 0` there is `C_η` with
  `|P_N(εx) − κ ℓ(x)²| ≤ (η log N + C_η) Σ_{i,j} |c_i| |c_j| H_{min(M_i, M_j)}` on uniform step
  profiles. The polar divergence `κ ℓ²`, of order `(log N)²`, is read off the leading order of
  `A_ε` alone; the remainder is `o((log N)²)` instead of the mass.
* **The diagonal criterion** (`gaugePole_bounded_iff`): `⟨εu^{(M)}, P εu^{(M)}⟩ = κ H_M² + O(H_M)`
  for all `M` if and only if `Σ_{m ≤ M} E(⌊M/m⌋)/m = O(H_M)`.

So an error `o(log y)` keeps the law at leading order, and the mass-scale law holds exactly when the
Mertens error is bounded in logarithmic mean. The matching coefficient is the logarithmic density of
the gauge; boundedness of `E` is a statement about its finite part.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {ε : ℕ → ℝ}

/-- The **Mertens error** of a gauge against the coefficient `κ`: `E(y) = A_ε(y) − κ log y`. -/
def gaugeMertensError (ε : ℕ → ℝ) (κ : ℝ) (y : ℕ) : ℝ := gaugeMertensSum ε y - κ * Real.log y

/-- `|Σ_{m ≤ M} log⌊X/m⌋/m − (H_M log X − Σ_{m ≤ M} log m/m)| ≤ log 2 · H_M` for `M ≤ X`. -/
theorem abs_sum_log_div_div_sub_le {M X : ℕ} (hMX : M ≤ X) :
    |∑ m ∈ Icc 1 M, Real.log ((X / m : ℕ) : ℝ) / m -
        (harmonicSum M * Real.log X - ∑ m ∈ Icc 1 M, Real.log m / m)| ≤
      Real.log 2 * harmonicSum M := by
  have hexp : harmonicSum M * Real.log X - ∑ m ∈ Icc 1 M, Real.log m / m =
      ∑ m ∈ Icc 1 M, (Real.log X - Real.log m) / m := by
    rw [harmonicSum, sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [hexp, ← sum_sub_distrib, harmonicSum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmX := (mem_Icc.mp hm).2.trans hMX
  have h2 := log_div_add_log_le hm0 hmX
  have h3 := log_le_log_div_add_log hm0 hmX
  rw [← sub_div, abs_div, abs_of_pos hm', mul_one_div]
  refine div_le_div_of_nonneg_right ?_ hm'.le
  rw [abs_le]
  constructor <;> linarith

/-- **The transfer law**: for every sign gauge, `|κ| ≤ 1` and `1 ≤ M ≤ M' ≤ N`,
`|⟨εu^{(M)}, P εu^{(M')}⟩ − κ H_M H_{M'} − Σ_{m ≤ M} (E(⌊M'/m⌋) + E(⌊M/m⌋))/m| ≤
(2 log 2 + 4) H_M`. -/
theorem abs_primeBilinear_gaugeTrunc_sub_transfer_le (hε : IsSignGauge ε) {κ : ℝ}
    (hκ : |κ| ≤ 1) {M M' N : ℕ} (hM : 1 ≤ M) (hMM' : M ≤ M') (hM'N : M' ≤ N) :
    |primeBilinear N (gaugeTrunc ε M) (gaugeTrunc ε M') - κ * harmonicSum M * harmonicSum M' -
        ∑ m ∈ Icc 1 M, (gaugeMertensError ε κ (M' / m) + gaugeMertensError ε κ (M / m)) / m| ≤
      (2 * Real.log 2 + 4) * harmonicSum M := by
  rw [primeBilinear_gaugeTrunc_eq hε hMM' hM'N]
  -- the divisor part averages to the Mertens part
  have hsplit : ∑ m ∈ Icc 1 M, (gaugeMertensSum ε (M' / m) + gaugeDivisorSum ε m) / m =
      ∑ m ∈ Icc 1 M, (gaugeMertensSum ε (M' / m) + gaugeMertensSum ε (M / m)) / m := by
    simp_rw [add_div]
    rw [sum_add_distrib, sum_add_distrib, sum_gaugeDivisorSum_div]
  -- what is left after the errors is `κ Σ_m (log⌊M'/m⌋ + log⌊M/m⌋)/m`
  have hAE : ∑ m ∈ Icc 1 M, (gaugeMertensSum ε (M' / m) + gaugeMertensSum ε (M / m)) / m -
      ∑ m ∈ Icc 1 M, (gaugeMertensError ε κ (M' / m) + gaugeMertensError ε κ (M / m)) / m =
      κ * (∑ m ∈ Icc 1 M, Real.log ((M' / m : ℕ) : ℝ) / m +
        ∑ m ∈ Icc 1 M, Real.log ((M / m : ℕ) : ℝ) / m) := by
    rw [← sum_sub_distrib, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    simp only [gaugeMertensError]
    ring
  have hL1 := abs_sum_log_div_div_sub_le hMM'
  have hL2 := abs_sum_log_div_div_sub_le (le_refl M)
  set S := ∑ m ∈ Icc 1 M, Real.log m / m
  have hS1 := sum_log_div_le M
  have hS2 := sum_log_div_ge hM
  have hH1 := one_le_harmonicSum hM
  have hHle := harmonicSum_le M
  have hHge := log_le_harmonicSum M
  have hH'le := harmonicSum_le M'
  have hH'ge := log_le_harmonicSum M'
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hlogM1 : Real.log M ≤ Real.log (M + 1) :=
    Real.log_le_log (by exact_mod_cast hM) (by linarith)
  -- the main term `κ (H_M (log M + log M') − 2S)` is `κ H_M H_{M'}` up to `4 H_M`
  have hmain : |κ * (harmonicSum M * Real.log M' - S + (harmonicSum M * Real.log M - S)) -
      κ * harmonicSum M * harmonicSum M'| ≤ 4 * harmonicSum M := by
    have hsq1 : Real.log M ^ 2 ≤ harmonicSum M * Real.log M := by nlinarith
    have hsq2 : harmonicSum M * Real.log M ≤ Real.log M + Real.log (M + 1) ^ 2 := by
      nlinarith [pow_le_pow_left₀ hlogM hlogM1 2]
    have hinner : |harmonicSum M * Real.log M' - S + (harmonicSum M * Real.log M - S) -
        harmonicSum M * harmonicSum M'| ≤ 4 * harmonicSum M := by
      rw [abs_le]; constructor <;> nlinarith
    calc |κ * (harmonicSum M * Real.log M' - S + (harmonicSum M * Real.log M - S)) -
          κ * harmonicSum M * harmonicSum M'|
        = |κ| * |harmonicSum M * Real.log M' - S + (harmonicSum M * Real.log M - S) -
            harmonicSum M * harmonicSum M'| := by rw [← abs_mul]; ring_nf
      _ ≤ 1 * (4 * harmonicSum M) := mul_le_mul hκ hinner (abs_nonneg _) zero_le_one
      _ = 4 * harmonicSum M := one_mul _
  -- the floors cost `log 2` per term
  have hfloor : |κ * ((∑ m ∈ Icc 1 M, Real.log ((M' / m : ℕ) : ℝ) / m -
      (harmonicSum M * Real.log M' - S)) + (∑ m ∈ Icc 1 M, Real.log ((M / m : ℕ) : ℝ) / m -
      (harmonicSum M * Real.log M - S)))| ≤ 2 * Real.log 2 * harmonicSum M := by
    rw [abs_mul]
    calc |κ| * |(∑ m ∈ Icc 1 M, Real.log ((M' / m : ℕ) : ℝ) / m -
          (harmonicSum M * Real.log M' - S)) + (∑ m ∈ Icc 1 M, Real.log ((M / m : ℕ) : ℝ) / m -
          (harmonicSum M * Real.log M - S))|
        ≤ 1 * (Real.log 2 * harmonicSum M + Real.log 2 * harmonicSum M) :=
          mul_le_mul hκ ((abs_add_le _ _).trans (add_le_add hL1 hL2)) (abs_nonneg _) zero_le_one
      _ = 2 * Real.log 2 * harmonicSum M := by ring
  rw [hsplit]
  have hid : ∑ m ∈ Icc 1 M, (gaugeMertensSum ε (M' / m) + gaugeMertensSum ε (M / m)) / m -
      κ * harmonicSum M * harmonicSum M' -
      ∑ m ∈ Icc 1 M, (gaugeMertensError ε κ (M' / m) + gaugeMertensError ε κ (M / m)) / m =
      κ * ((∑ m ∈ Icc 1 M, Real.log ((M' / m : ℕ) : ℝ) / m -
        (harmonicSum M * Real.log M' - S)) + (∑ m ∈ Icc 1 M, Real.log ((M / m : ℕ) : ℝ) / m -
        (harmonicSum M * Real.log M - S))) +
      (κ * (harmonicSum M * Real.log M' - S + (harmonicSum M * Real.log M - S)) -
        κ * harmonicSum M * harmonicSum M') := by
    rw [sub_right_comm, hAE]
    ring
  rw [hid]
  calc _ ≤ 2 * Real.log 2 * harmonicSum M + 4 * harmonicSum M :=
        (abs_add_le _ _).trans (add_le_add hfloor hmain)
    _ = (2 * Real.log 2 + 4) * harmonicSum M := by ring

/-- If `|E(y)| ≤ g` for `1 ≤ y ≤ X`, then `|Σ_{m ≤ M} E(⌊X/m⌋)/m| ≤ g H_M` for `M ≤ X`. -/
theorem abs_sum_gaugeMertensError_div_le {κ g : ℝ} {M X : ℕ} (hMX : M ≤ X)
    (hE : ∀ y : ℕ, 1 ≤ y → y ≤ X → |gaugeMertensError ε κ y| ≤ g) :
    |∑ m ∈ Icc 1 M, gaugeMertensError ε κ (X / m) / m| ≤ g * harmonicSum M := by
  rw [harmonicSum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmX := (mem_Icc.mp hm).2.trans hMX
  rw [abs_div, abs_of_pos hm', mul_one_div]
  exact div_le_div_of_nonneg_right
    (hE _ ((Nat.le_div_iff_mul_le hm0).mpr (by omega)) (Nat.div_le_self X m)) hm'.le

/-- **The local matching law**: if `|A_ε(y) − κ log y| ≤ g` for `1 ≤ y ≤ M'`, then
`|⟨εu^{(M)}, P εu^{(M')}⟩ − κ H_M H_{M'}| ≤ (2g + 2 log 2 + 4) H_M` for `1 ≤ M ≤ M' ≤ N`. -/
theorem abs_primeBilinear_gaugeTrunc_sub_le_local (hε : IsSignGauge ε) {κ g : ℝ} (hκ : |κ| ≤ 1)
    {M M' N : ℕ} (hM : 1 ≤ M) (hMM' : M ≤ M') (hM'N : M' ≤ N)
    (hE : ∀ y : ℕ, 1 ≤ y → y ≤ M' → |gaugeMertensError ε κ y| ≤ g) :
    |primeBilinear N (gaugeTrunc ε M) (gaugeTrunc ε M') - κ * harmonicSum M * harmonicSum M'| ≤
      (2 * g + 2 * Real.log 2 + 4) * harmonicSum M := by
  have ht := abs_primeBilinear_gaugeTrunc_sub_transfer_le hε hκ hM hMM' hM'N
  have h1 := abs_sum_gaugeMertensError_div_le hMM' hE
  have h2 := abs_sum_gaugeMertensError_div_le (le_refl M) fun y hy hyM => hE y hy (hyM.trans hMM')
  have hsum : ∑ m ∈ Icc 1 M, (gaugeMertensError ε κ (M' / m) + gaugeMertensError ε κ (M / m)) / m =
      ∑ m ∈ Icc 1 M, gaugeMertensError ε κ (M' / m) / m +
        ∑ m ∈ Icc 1 M, gaugeMertensError ε κ (M / m) / m := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun m _ => add_div _ _ _
  rw [hsum] at ht
  rw [abs_le] at ht h1 h2 ⊢
  constructor <;> linarith [ht.1, ht.2, h1.1, h1.2, h2.1, h2.2]

/-- Pair bounds give the profile bound: if every pole Gram satisfies
`|⟨εu^{(M_i)}, P εu^{(M_j)}⟩ − κ H_{M_i} H_{M_j}| ≤ B H_{min(M_i, M_j)}`, then
`|P_N(εx) − κ ℓ(x)²| ≤ B Σ_{i,j} |c_i| |c_j| H_{min(M_i, M_j)}`. -/
theorem abs_gaugeForm_stepProfile_sub_le_of_pairs {κ B : ℝ} {k N : ℕ} (c : Fin k → ℝ)
    (M : Fin k → ℕ) (hM : ∀ i, M i ≤ N)
    (hpair : ∀ i j, |primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
      κ * harmonicSum (M i) * harmonicSum (M j)| ≤ B * harmonicSum (min (M i) (M j))) :
    |atomicWeilForm N (fun n => ε n * stepProfile c M n) -
        κ * polarFunctional N (stepProfile c M) ^ 2| ≤
      B * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) := by
  have hL : ∀ y, primeBilinear N (fun n => ε n * stepProfile c M n) y =
      ∑ i, c i * primeBilinear N (gaugeTrunc ε (M i)) y := by
    intro y
    have h := primeBilinear_sum_left N c (fun i => gaugeTrunc ε (M i)) y
    rw [← h]
    congr 1
    funext n
    rw [stepProfile, mul_sum]
    exact sum_congr rfl fun i _ => by rw [gaugeTrunc]; ring
  have hexp : atomicWeilForm N (fun n => ε n * stepProfile c M n) =
      ∑ i, ∑ j, c i * c j * primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) := by
    rw [atomicWeilForm_eq_primeBilinear, hL]
    refine sum_congr rfl fun i _ => ?_
    rw [primeBilinear_comm, hL, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [primeBilinear_comm]
    ring
  rw [hexp, polarFunctional_stepProfile c M hM, sq, sum_mul_sum, mul_sum, ← sum_sub_distrib]
  simp_rw [mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have hrw : c i * c j * primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
      κ * (c i * harmonicSum (M i) * (c j * harmonicSum (M j))) =
      (c i * c j) * (primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
        κ * harmonicSum (M i) * harmonicSum (M j)) := by ring
  rw [hrw, abs_mul, abs_mul]
  calc |c i| * |c j| * |primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
        κ * harmonicSum (M i) * harmonicSum (M j)|
      ≤ |c i| * |c j| * (B * harmonicSum (min (M i) (M j))) :=
        mul_le_mul_of_nonneg_left (hpair i j) (by positivity)
    _ = B * (|c i| * |c j| * harmonicSum (min (M i) (M j))) := by ring

/-- **The soft matching law**: if for every `η > 0` the Mertens error satisfies
`|A_ε(y) − κ log y| ≤ η log y + C_η`, then for every `η > 0` there is `C` with
`|P_N(εx) − κ ℓ(x)²| ≤ (η log N + C) Σ_{i,j} |c_i| |c_j| H_{min(M_i, M_j)}` on uniform profiles. -/
theorem gaugeForm_stepProfile_soft (hε : IsSignGauge ε) {κ : ℝ} (hκ : |κ| ≤ 1)
    (hA : ∀ η > 0, ∃ C : ℝ, ∀ y : ℕ, 1 ≤ y → |gaugeMertensError ε κ y| ≤ η * Real.log y + C) :
    ∀ η > 0, ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) →
      (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (fun n => ε n * stepProfile c M n) -
          κ * polarFunctional N (stepProfile c M) ^ 2| ≤
        (η * Real.log N + C) * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) := by
  intro η hη
  obtain ⟨C₀, hC₀⟩ := hA (η / 2) (by positivity)
  refine ⟨2 * C₀ + 2 * Real.log 2 + 4, fun {k N} c M hM hM1 => ?_⟩
  -- below the horizon the error is at most `(η/2) log N + C₀`
  have hE : ∀ y : ℕ, 1 ≤ y → y ≤ N → |gaugeMertensError ε κ y| ≤ η / 2 * Real.log N + C₀ :=
    fun y hy hyN => (hC₀ y hy).trans (by
      have := mul_le_mul_of_nonneg_left (Real.log_le_log (Nat.cast_pos.mpr hy)
        (by exact_mod_cast hyN : (y : ℝ) ≤ N)) (half_pos hη).le
      linarith)
  have hB : 2 * (η / 2 * Real.log N + C₀) + 2 * Real.log 2 + 4 =
      η * Real.log N + (2 * C₀ + 2 * Real.log 2 + 4) := by ring
  refine abs_gaugeForm_stepProfile_sub_le_of_pairs c M hM fun i j => ?_
  rcases le_total (M i) (M j) with h | h
  · rw [min_eq_left h, ← hB]
    exact abs_primeBilinear_gaugeTrunc_sub_le_local hε hκ (hM1 i) h (hM j)
      fun y hy hyM => hE y hy (hyM.trans (hM j))
  · rw [min_eq_right h, primeBilinear_comm, mul_assoc, mul_comm (harmonicSum (M i)), ← mul_assoc,
      ← hB]
    exact abs_primeBilinear_gaugeTrunc_sub_le_local hε hκ (hM1 j) h (hM i)
      fun y hy hyM => hE y hy (hyM.trans (hM i))

/-- `A_ε(y)/log y → κ` gives, for every `η > 0`, `|A_ε(y) − κ log y| ≤ η log y + C_η`. -/
theorem exists_abs_gaugeMertensError_le_of_tendsto {κ : ℝ}
    (h : Tendsto (fun y : ℕ => gaugeMertensSum ε y / Real.log y) atTop (𝓝 κ)) :
    ∀ η > 0, ∃ C : ℝ, ∀ y : ℕ, 1 ≤ y → |gaugeMertensError ε κ y| ≤ η * Real.log y + C := by
  intro η hη
  obtain ⟨Y, hY⟩ := Metric.tendsto_atTop.mp h η hη
  refine ⟨∑ z ∈ range (max Y 2), |gaugeMertensError ε κ z|, fun y _ => ?_⟩
  have hC : 0 ≤ ∑ z ∈ range (max Y 2), |gaugeMertensError ε κ z| :=
    sum_nonneg fun _ _ => abs_nonneg _
  have hlog : 0 ≤ Real.log y := Real.log_natCast_nonneg y
  by_cases hyY : max Y 2 ≤ y
  · -- beyond `Y` the error is `η`-small relative to `log y`
    have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast (le_max_right Y 2).trans hyY
    have hlpos : 0 < Real.log y := Real.log_pos (by linarith)
    have hd := hY y ((le_max_left Y 2).trans hyY)
    rw [Real.dist_eq] at hd
    have hL0 := hlpos.ne'
    have heq : gaugeMertensError ε κ y = (gaugeMertensSum ε y / Real.log y - κ) * Real.log y := by
      rw [gaugeMertensError]
      field_simp
    rw [heq, abs_mul, abs_of_pos hlpos]
    exact (mul_le_mul_of_nonneg_right hd.le hlpos.le).trans (le_add_of_nonneg_right hC)
  · -- below `Y` the finitely many errors are absorbed in the constant
    have hmem : y ∈ range (max Y 2) := mem_range.mpr (not_le.mp hyY)
    have := single_le_sum (f := fun z => |gaugeMertensError ε κ z|) (fun _ _ => abs_nonneg _) hmem
    nlinarith [mul_nonneg hη.le hlog]

/-- **The soft law from the density**: if `A_ε(y)/log y → κ` with `|κ| ≤ 1`, then for every `η > 0`
there is `C` with `|P_N(εx) − κ ℓ(x)²| ≤ (η log N + C) Σ_{i,j} |c_i| |c_j| H_{min(M_i, M_j)}`. -/
theorem gaugeForm_stepProfile_of_tendsto (hε : IsSignGauge ε) {κ : ℝ} (hκ : |κ| ≤ 1)
    (h : Tendsto (fun y : ℕ => gaugeMertensSum ε y / Real.log y) atTop (𝓝 κ)) :
    ∀ η > 0, ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) →
      (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (fun n => ε n * stepProfile c M n) -
          κ * polarFunctional N (stepProfile c M) ^ 2| ≤
        (η * Real.log N + C) * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) :=
  gaugeForm_stepProfile_soft hε hκ (exists_abs_gaugeMertensError_le_of_tendsto h)

/-- **The diagonal criterion**: `⟨εu^{(M)}, P εu^{(M)}⟩ = κ H_M² + O(H_M)` for all `M ≥ 1` if and only
if the harmonic convolution of the Mertens error is `O(H_M)`. -/
theorem gaugePole_bounded_iff (hε : IsSignGauge ε) {κ : ℝ} (hκ : |κ| ≤ 1) :
    (∃ K : ℝ, ∀ M : ℕ, 1 ≤ M →
      |primeBilinear M (gaugeTrunc ε M) (gaugeTrunc ε M) - κ * harmonicSum M ^ 2| ≤
        K * harmonicSum M) ↔
    (∃ K : ℝ, ∀ M : ℕ, 1 ≤ M →
      |∑ m ∈ Icc 1 M, gaugeMertensError ε κ (M / m) / m| ≤ K * harmonicSum M) := by
  -- on the diagonal the transfer law reads `G − κH² = 2 Σ E(⌊M/m⌋)/m + O(H)`
  have ht : ∀ M : ℕ, 1 ≤ M → |primeBilinear M (gaugeTrunc ε M) (gaugeTrunc ε M) -
      κ * harmonicSum M ^ 2 - 2 * ∑ m ∈ Icc 1 M, gaugeMertensError ε κ (M / m) / m| ≤
        (2 * Real.log 2 + 4) * harmonicSum M := by
    intro M hM
    have h := abs_primeBilinear_gaugeTrunc_sub_transfer_le hε hκ hM le_rfl le_rfl
    have hd : ∑ m ∈ Icc 1 M, (gaugeMertensError ε κ (M / m) + gaugeMertensError ε κ (M / m)) / m =
        2 * ∑ m ∈ Icc 1 M, gaugeMertensError ε κ (M / m) / m := by
      rw [mul_sum]
      exact sum_congr rfl fun m _ => by ring
    rwa [hd, mul_assoc, ← sq] at h
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨(K + 2 * Real.log 2 + 4) / 2, fun M hM => ?_⟩
    have h1 := ht M hM
    have h2 := hK M hM
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  · rintro ⟨K, hK⟩
    refine ⟨2 * K + 2 * Real.log 2 + 4, fun M hM => ?_⟩
    have h1 := ht M hM
    have h2 := hK M hM
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

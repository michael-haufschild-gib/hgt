import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PolarMatchingNeedsOnlyTheLeadingOrder
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant

/-!
# The finite part is twice the Mertens limit

For `ζ` the horizon form on uniform step profiles is `ℓ(x)² − 2γ|x|² + o(mass)`
(`exists_abs_atomicWeilForm_stepProfile_finitePart_le`), and `−γ` is the limit of the Mertens error
`A(y) − log y`. This file shows that this is the general rule for sign gauges.

* **The gauged pole Gram as a Mertens convolution** (`primeBilinear_gaugeTrunc_eq_sum`):
  `⟨εu^{(M)}, P εu^{(M')}⟩ = Σ_{m ≤ M} (A_ε(⌊M'/m⌋) + A_ε(⌊M/m⌋))/m`.
* **Convergent convolutions** (`exists_abs_sum_div_sub_le_of_tendsto`): if `D(y) → β`, then
  `Σ_{m ≤ M} D(⌊X/m⌋)/m = β H_M + o(H_M) + O(1)` uniformly in `X ≥ M`.
* **The finite-part law** (`exists_abs_primeBilinear_gaugeTrunc_finitePart_le`,
  `exists_abs_gaugeForm_stepProfile_finitePart_le`): if the Mertens error converges,
  `A_ε(y) − κ log y → α`, with `|κ| ≤ 1`, then
  `⟨εu^{(M)}, P εu^{(M')}⟩ = κ H_M H_{M'} + 2α H_M + o(H_M) + O(1)` for `M ≤ M'`, and on uniform step
  profiles `P_N(εx) = κ ℓ(x)² + 2α |x|² + o(mass)`. The comparison is with `ζ` itself: the gauge
  minus `κ` times the Euler gauge has a convergent Mertens sum, with limit `α + κγ`.

So the regulator, the matching coefficient and the finite part of a gauge are the three terms of
its Mertens expansion `A_ε(y) = κ log y + α + o(1)`: the divergence reads `κ`, the finite part
reads `2α`, and for `ζ` (`κ = 1`, `α = −γ`) this is RP10.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

variable {ε : ℕ → ℝ}

/-- **The gauged pole Gram is a Mertens convolution**: for `M ≤ M' ≤ N`,
`⟨εu^{(M)}, P εu^{(M')}⟩ = Σ_{m ≤ M} (A_ε(⌊M'/m⌋) + A_ε(⌊M/m⌋))/m`. -/
theorem primeBilinear_gaugeTrunc_eq_sum (hε : IsSignGauge ε) {M M' N : ℕ} (hMM' : M ≤ M')
    (hM'N : M' ≤ N) :
    primeBilinear N (gaugeTrunc ε M) (gaugeTrunc ε M') =
      ∑ m ∈ Icc 1 M, (gaugeMertensSum ε (M' / m) + gaugeMertensSum ε (M / m)) / m := by
  rw [primeBilinear_gaugeTrunc_eq hε hMM' hM'N]
  simp_rw [add_div]
  rw [sum_add_distrib, sum_add_distrib, sum_gaugeDivisorSum_div]

theorem gaugeTrunc_one (M : ℕ) : gaugeTrunc (fun _ => 1) M = truncPole M :=
  funext fun _ => one_mul _

theorem gaugeMertensSum_one (y : ℕ) : gaugeMertensSum (fun _ => 1) y = mertensSum y :=
  sum_congr rfl fun t _ => by rw [one_mul]

/-- **Convergent convolutions**: if `D(y) → β`, then for every `η > 0` there is `C` with
`|Σ_{m ≤ M} D(⌊X/m⌋)/m − β H_M| ≤ η H_M + C` for all `M ≤ X`. -/
theorem exists_abs_sum_div_sub_le_of_tendsto {D : ℕ → ℝ} {β : ℝ}
    (hD : Tendsto D atTop (𝓝 β)) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ M X : ℕ, M ≤ X →
      |∑ m ∈ Icc 1 M, D (X / m) / m - β * harmonicSum M| ≤ η * harmonicSum M + C := by
  obtain ⟨Y, hY⟩ := Metric.tendsto_atTop.mp hD η hη
  set B := ∑ y ∈ range Y, |D y - β| with hBdef
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B * Y, fun M X hMX => ?_⟩
  -- below `Y` the error is at most `B`, and those `m` have `1/m < Y/X`
  have hterm : ∀ m ∈ Icc 1 M, |D (X / m) / m - β * (1 / (m : ℝ))| ≤
      η * (1 / (m : ℝ)) + B * (if X / m < Y then 1 / (m : ℝ) else 0) := by
    intro m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
    rw [show D (X / m) / m - β * (1 / (m : ℝ)) = (D (X / m) - β) * (1 / (m : ℝ)) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
    by_cases hXY : X / m < Y
    · rw [if_pos hXY]
      have hle : |D (X / m) - β| ≤ B :=
        single_le_sum (f := fun y => |D y - β|) (fun _ _ => abs_nonneg _) (mem_range.mpr hXY)
      have := mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ 1 / m)
      have : 0 ≤ η * (1 / (m : ℝ)) := by positivity
      linarith
    · rw [if_neg hXY, mul_zero, add_zero]
      have hd := hY (X / m) (not_lt.mp hXY)
      rw [Real.dist_eq] at hd
      exact mul_le_mul_of_nonneg_right hd.le (by positivity)
  have hcount : ∑ m ∈ Icc 1 M, (if X / m < Y then 1 / (m : ℝ) else 0) ≤ Y := by
    rcases Nat.eq_zero_or_pos X with hX | hX
    · have : M = 0 := by omega
      subst this
      simp
    have hX' : (0 : ℝ) < X := by exact_mod_cast hX
    calc ∑ m ∈ Icc 1 M, (if X / m < Y then 1 / (m : ℝ) else 0)
        ≤ ∑ _m ∈ Icc 1 M, (Y : ℝ) / X := by
          refine sum_le_sum fun m hm => ?_
          have hm0 := (mem_Icc.mp hm).1
          have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
          split_ifs with h
          · -- `⌊X/m⌋ < Y` gives `X < Y m`
            have hlt : X < Y * m := (Nat.div_lt_iff_lt_mul hm0).mp h
            have : (X : ℝ) ≤ Y * m := by exact_mod_cast hlt.le
            rw [div_le_div_iff₀ hm' hX']
            linarith
          · positivity
      _ = M * ((Y : ℝ) / X) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ ≤ X * ((Y : ℝ) / X) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hMX) (by positivity)
      _ = Y := by field_simp
  have hsplit : ∑ m ∈ Icc 1 M, D (X / m) / m - β * harmonicSum M =
      ∑ m ∈ Icc 1 M, (D (X / m) / m - β * (1 / (m : ℝ))) := by
    rw [sum_sub_distrib, harmonicSum, mul_sum]
  rw [hsplit]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← harmonicSum]
  have := mul_le_mul_of_nonneg_left hcount hB0
  linarith

/-- **The finite-part law for a pole Gram**: if `A_ε(y) − κ log y → α` and `|κ| ≤ 1`, then for
every `η > 0` there is `C` with
`|⟨εu^{(M)}, P εu^{(M')}⟩ − κ H_M H_{M'} − 2α H_M| ≤ η H_M + C` for `1 ≤ M ≤ M' ≤ N`. -/
theorem exists_abs_primeBilinear_gaugeTrunc_finitePart_le (hε : IsSignGauge ε) {κ α : ℝ}
    (hκ : |κ| ≤ 1) (hE : Tendsto (gaugeMertensError ε κ) atTop (𝓝 α)) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ M M' N : ℕ, 1 ≤ M → M ≤ M' → M' ≤ N →
      |primeBilinear N (gaugeTrunc ε M) (gaugeTrunc ε M') -
          κ * harmonicSum M * harmonicSum M' - 2 * α * harmonicSum M| ≤
        η * harmonicSum M + C := by
  -- the gauge minus `κ` times the Euler gauge has the convergent Mertens sum `D`
  set D : ℕ → ℝ := fun y => gaugeMertensSum ε y - κ * mertensSum y with hDdef
  have hDlim : Tendsto D atTop (𝓝 (α + κ * γ)) := by
    have h := hE.sub (tendsto_mertensSum_sub_log.const_mul κ)
    refine (h.congr fun y => ?_).trans (by rw [mul_neg, sub_neg_eq_add])
    simp only [hDdef, gaugeMertensError]
    ring
  obtain ⟨C₁, hC₁⟩ := exists_abs_primeBilinear_truncPole_finitePart_le (η := η / 3) (by positivity)
  obtain ⟨C₂, hC₂⟩ := exists_abs_sum_div_sub_le_of_tendsto hDlim (η := η / 3) (by positivity)
  refine ⟨|C₁| + 2 * |C₂|, fun M M' N hM hMM' hM'N => ?_⟩
  have hζ := hC₁ M M' N hM hMM' hM'N
  have h1 := hC₂ M M' hMM'
  have h2 := hC₂ M M le_rfl
  -- `G_ε = κ G_ζ + Σ_m (D(⌊M'/m⌋) + D(⌊M/m⌋))/m`
  have hG : primeBilinear N (gaugeTrunc ε M) (gaugeTrunc ε M') =
      κ * primeBilinear N (truncPole M) (truncPole M') +
        (∑ m ∈ Icc 1 M, D (M' / m) / m + ∑ m ∈ Icc 1 M, D (M / m) / m) := by
    have he := primeBilinear_gaugeTrunc_eq_sum hε hMM' hM'N
    have h1' := primeBilinear_gaugeTrunc_eq_sum euler_matching.1 hMM' hM'N
    rw [gaugeTrunc_one, gaugeTrunc_one] at h1'
    simp only [gaugeMertensSum_one] at h1'
    rw [he, h1', mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    simp only [hDdef]
    ring
  have hH0 := harmonicSum_nonneg M
  have hκζ : |κ * (primeBilinear N (truncPole M) (truncPole M') - harmonicSum M * harmonicSum M' +
      2 * γ * harmonicSum M)| ≤ η / 3 * harmonicSum M + |C₁| := by
    rw [abs_mul]
    calc |κ| * |primeBilinear N (truncPole M) (truncPole M') - harmonicSum M * harmonicSum M' +
          2 * γ * harmonicSum M|
        ≤ 1 * (η / 3 * harmonicSum M + C₁) := mul_le_mul hκ hζ (abs_nonneg _) zero_le_one
      _ ≤ η / 3 * harmonicSum M + |C₁| := by linarith [le_abs_self C₁]
  have hid : primeBilinear N (gaugeTrunc ε M) (gaugeTrunc ε M') -
      κ * harmonicSum M * harmonicSum M' - 2 * α * harmonicSum M =
      κ * (primeBilinear N (truncPole M) (truncPole M') - harmonicSum M * harmonicSum M' +
        2 * γ * harmonicSum M) +
      (∑ m ∈ Icc 1 M, D (M' / m) / m - (α + κ * γ) * harmonicSum M) +
      (∑ m ∈ Icc 1 M, D (M / m) / m - (α + κ * γ) * harmonicSum M) := by
    rw [hG]
    ring
  rw [hid]
  have hC₂' : C₂ ≤ |C₂| := le_abs_self C₂
  calc _ ≤ |κ * (primeBilinear N (truncPole M) (truncPole M') - harmonicSum M * harmonicSum M' +
          2 * γ * harmonicSum M)| +
        |∑ m ∈ Icc 1 M, D (M' / m) / m - (α + κ * γ) * harmonicSum M| +
        |∑ m ∈ Icc 1 M, D (M / m) / m - (α + κ * γ) * harmonicSum M| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (η / 3 * harmonicSum M + |C₁|) + (η / 3 * harmonicSum M + C₂) +
          (η / 3 * harmonicSum M + C₂) := add_le_add (add_le_add hκζ h1) h2
    _ ≤ η * harmonicSum M + (|C₁| + 2 * |C₂|) := by linarith

/-- The gauged step profile expands over pairs of pole Grams. -/
theorem atomicWeilForm_gaugeStepProfile_eq {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ) :
    atomicWeilForm N (fun n => ε n * stepProfile c M n) =
      ∑ i, ∑ j, c i * c j * primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) := by
  have hL : ∀ y, primeBilinear N (fun n => ε n * stepProfile c M n) y =
      ∑ i, c i * primeBilinear N (gaugeTrunc ε (M i)) y := by
    intro y
    rw [← primeBilinear_sum_left N c (fun i => gaugeTrunc ε (M i)) y]
    congr 1
    funext n
    rw [stepProfile, mul_sum]
    exact sum_congr rfl fun i _ => by rw [gaugeTrunc]; ring
  rw [atomicWeilForm_eq_primeBilinear, hL]
  refine sum_congr rfl fun i _ => ?_
  rw [primeBilinear_comm, hL, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [primeBilinear_comm]
  ring

/-- **The finite-part law on uniform step profiles**: if `A_ε(y) − κ log y → α` with `|κ| ≤ 1`,
then for every `η > 0` there is `C` with
`|P_N(εx) − κ ℓ(x)² − 2α|x|²| ≤ Σ_{i,j} |c_i| |c_j| (η H_{min(M_i, M_j)} + C)`. -/
theorem exists_abs_gaugeForm_stepProfile_finitePart_le (hε : IsSignGauge ε) {κ α : ℝ}
    (hκ : |κ| ≤ 1) (hE : Tendsto (gaugeMertensError ε κ) atTop (𝓝 α)) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) → (∀ i, M i ≤ N) →
      |atomicWeilForm N (fun n => ε n * stepProfile c M n) -
          κ * polarFunctional N (stepProfile c M) ^ 2 -
          2 * α * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
        ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C) := by
  obtain ⟨C, hC⟩ := exists_abs_primeBilinear_gaugeTrunc_finitePart_le hε hκ hE hη
  refine ⟨C, fun {k N} c M hM1 hM => ?_⟩
  have hpair : ∀ i j, |primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
      κ * harmonicSum (M i) * harmonicSum (M j) - 2 * α * harmonicSum (min (M i) (M j))| ≤
        η * harmonicSum (min (M i) (M j)) + C := by
    intro i j
    rcases le_total (M i) (M j) with h | h
    · rw [min_eq_left h]
      exact hC _ _ _ (hM1 i) h (hM j)
    · rw [min_eq_right h, primeBilinear_comm, mul_assoc, mul_comm (harmonicSum (M i)),
        ← mul_assoc]
      exact hC _ _ _ (hM1 j) h (hM i)
  rw [atomicWeilForm_gaugeStepProfile_eq, polarFunctional_stepProfile c M hM,
    sum_stepProfile_sq c M hM, sq, sum_mul_sum, mul_sum, mul_sum, ← sum_sub_distrib,
    ← sum_sub_distrib]
  simp_rw [mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have hrw : c i * c j * primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
      κ * (c i * harmonicSum (M i) * (c j * harmonicSum (M j))) -
        2 * α * (c i * c j * harmonicSum (min (M i) (M j))) =
      (c i * c j) * (primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
        κ * harmonicSum (M i) * harmonicSum (M j) - 2 * α * harmonicSum (min (M i) (M j))) := by
    ring
  rw [hrw, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hpair i j) (by positivity)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

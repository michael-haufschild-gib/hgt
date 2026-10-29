import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerDecomposition
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePlateauShapeAndChargeHaveTheirIndicatorLimits
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanFinitePartIsMinusLogTwoPi
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAtomCrossMatrixIsCloseToItsCenterKernel
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleHyperplaneSeparatesTheFullWeilForms
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing

/-!
# Selectivity of fixed overlap ratios on the Liouville twin

For `ζ`, the complete Weil form is eventually positive definite on atomic families up to and strictly
above the touching ratio `c = 1` (`TransMetzlerPositivity`). For the Liouville sign twin `λ Λ`,
whose Dirichlet series `ζ(2s)/ζ(s)` lacks the simple pole at `s = 1` in its prime gauge, the prime
form reaches `log M - γ + o(1)` on the harmonic hyperplane `∑_{n ≤ M} x_n / √n = 0` where both pole
moments vanish identically.

This module establishes the sharp breakdown and narrow survival of the Liouville twin's complete
Weil form across fixed overlap ratios:

* **Finite Fejér–Abel lower bound on the archimedean center kernel**
  (`sum_archimedeanCenterKernel_ge`): in pole gauge `b_n = √n x_n`, the exact decomposition
  `archimedeanCenterKernel n j / (√n √j) = (1/2)(1/|n - j| + 1/(n + j))` combines with the uniform
  cosine partial-sum floor `∑_{d=1}^M cos(dθ)/d ≥ -4` and the positive Hankel moment kernel on
  `[0, 1]` to give `∑_{n, j ≤ M} x_n x_j archimedeanCenterKernel n j ≥ -(17/4) ∑_{n ≤ M} n x_n²`;
* **Breakdown above the Robin–Euler ratio** (`eventually_liouville_weilQuadTw_neg_of_gt_robinEuler`):
  for every `C²` profile `φ` supported in `[0, 1]` with `robinEulerThreshold φ < 1` and every fixed
  `c > robinEulerThreshold φ = exp(β(φ)/‖φ‖₂²)/(2π)` — including `c = 1` and `c > 1` via sub-horizon
  dilution `M_N = ⌊(c'/c) N⌋` — the Liouville twin's complete Weil form is eventually strictly
  negative on atomic families of width `w_N` whenever `w_N N → c`;
* **Trans-Metzler selectivity** (`eventually_liouville_weilQuadTw_neg_transMetzlerProfile`) and the
  indicator limit `e / (2π)` (`exists_plateau_liouville_weilQuadTw_neg_of_gt_exp_div_two_pi`),
  paired with narrow-width nonnegativity (`liouville_weilQuadTw_nonneg_of_le_fixedWidthRatio`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset RHTower
open scoped Real

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory SelectiveMultiscaleArithmeticPositivity
  ArithmeticLorentzianGeometry ArithmeticElectrostatics

/-! ### 1. The Robin–Euler overlap ratio -/

/-- The Robin–Euler overlap ratio `c_RE(φ) = exp(β(φ)/‖φ‖₂²) / (2π)` at which the Markov ground
energy on the harmonic hyperplane changes sign. -/
def robinEulerThreshold (φ : ℝ → ℝ) : ℝ :=
  Real.exp (bumpRobin φ 1 / ∫ u, φ u ^ 2) / (2 * Real.pi)

theorem robinEulerThreshold_pos (φ : ℝ → ℝ) : 0 < robinEulerThreshold φ := by
  unfold robinEulerThreshold
  positivity

/-- For `transMetzlerProfile = plateau (1 / 1000)`, the Robin–Euler ratio lies strictly below `1/2`. -/
theorem robinEulerThreshold_transMetzlerProfile_lt_half :
    robinEulerThreshold transMetzlerProfile < 1 / 2 :=
  transMetzlerProfile_robinEuler_lt_half

/-! ### 2. Finite Fejér–Abel and Hankel lower bound on the archimedean center kernel -/

private theorem abs_sin_nat_mul_le (d : ℕ) (α : ℝ) :
    |Real.sin ((d : ℝ) * α)| ≤ (d : ℝ) * |Real.sin α| := by
  induction d with
  | zero => simp
  | succ d ih =>
    push_cast
    rw [add_mul, one_mul, Real.sin_add]
    calc |Real.sin ((d : ℝ) * α) * Real.cos α + Real.cos ((d : ℝ) * α) * Real.sin α|
        ≤ |Real.sin ((d : ℝ) * α) * Real.cos α| + |Real.cos ((d : ℝ) * α) * Real.sin α| :=
          abs_add_le _ _
      _ = |Real.sin ((d : ℝ) * α)| * |Real.cos α| + |Real.cos ((d : ℝ) * α)| * |Real.sin α| := by
          rw [abs_mul, abs_mul]
      _ ≤ ((d : ℝ) * |Real.sin α|) * 1 + 1 * |Real.sin α| := by
          refine add_le_add
            (mul_le_mul ih (Real.abs_cos_le_one α) (abs_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _))
      _ = ((d : ℝ) + 1) * |Real.sin α| := by ring

private theorem cos_nonneg_of_mul_two_abs_sin_le_one {d : ℕ} {θ : ℝ}
    (h : (d : ℝ) * (2 * |Real.sin (θ / 2)|) ≤ 1) :
    0 ≤ Real.cos ((d : ℝ) * θ) := by
  have hsin : |Real.sin ((d : ℝ) * (θ / 2))| ≤ 1 / 2 := by
    have h1 := abs_sin_nat_mul_le d (θ / 2)
    linarith only [h, h1]
  have hsq : Real.sin ((d : ℝ) * (θ / 2)) ^ 2 ≤ 1 / 4 := by
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hsin 2
    rw [sq_abs] at h2
    linarith only [h2]
  have hcos : Real.cos ((d : ℝ) * θ) = 1 - 2 * Real.sin ((d : ℝ) * (θ / 2)) ^ 2 := by
    rw [show (d : ℝ) * θ = 2 * ((d : ℝ) * (θ / 2)) by ring, Real.cos_two_mul, Real.cos_sq']
    ring
  linarith only [hcos, hsq]

private theorem two_sin_mul_sum_cos_eq (k : ℕ) (θ : ℝ) :
    2 * Real.sin (θ / 2) * (∑ j ∈ Icc 1 k, Real.cos ((j : ℝ) * θ)) =
      Real.sin (((k : ℝ) + 1 / 2) * θ) - Real.sin (θ / 2) := by
  induction k with
  | zero =>
    simp only [Icc_eq_empty (by omega : ¬1 ≤ 0), sum_empty, mul_zero, Nat.cast_zero, zero_add]
    rw [show (1 / 2 : ℝ) * θ = θ / 2 by ring, sub_self]
  | succ k ih =>
    have hIcc : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext j; simp only [mem_Icc, mem_insert]; omega
    have hnot : k + 1 ∉ Icc 1 k := by simp only [mem_Icc]; omega
    rw [hIcc, sum_insert hnot, mul_add, ih]
    have h1 : ((k : ℝ) + 1 / 2) * θ = ((k : ℝ) + 1) * θ - θ / 2 := by ring
    have h2 : (((k + 1 : ℕ) : ℝ) + 1 / 2) * θ = ((k : ℝ) + 1) * θ + θ / 2 := by
      push_cast; ring
    have h3 : ((k + 1 : ℕ) : ℝ) * θ = ((k : ℝ) + 1) * θ := by push_cast; rfl
    rw [h1, h2, h3, Real.sin_sub, Real.sin_add]
    ring

private theorem two_abs_sin_mul_abs_sum_cos_le (k : ℕ) (θ : ℝ) :
    (2 * |Real.sin (θ / 2)|) * |∑ j ∈ Icc 1 k, Real.cos ((j : ℝ) * θ)| ≤ 2 := by
  have heq : (2 * |Real.sin (θ / 2)|) * |∑ j ∈ Icc 1 k, Real.cos ((j : ℝ) * θ)| =
      |2 * Real.sin (θ / 2) * ∑ j ∈ Icc 1 k, Real.cos ((j : ℝ) * θ)| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [heq, two_sin_mul_sum_cos_eq]
  calc |Real.sin (((k : ℝ) + 1 / 2) * θ) - Real.sin (θ / 2)|
      ≤ |Real.sin (((k : ℝ) + 1 / 2) * θ)| + |Real.sin (θ / 2)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
    _ = 2 := by norm_num

private theorem abel_sum_Icc (D : ℕ → ℝ) {a : ℕ} (ha : 1 ≤ a) (K : ℕ) :
    ∑ d ∈ Icc a (a + K), (D d - D (d - 1)) / (d : ℝ) =
      D (a + K) / ((a + K : ℕ) : ℝ) - D (a - 1) / (a : ℝ) +
        ∑ i ∈ range K, D (a + i) * (1 / ((a + i : ℕ) : ℝ) - 1 / ((a + i + 1 : ℕ) : ℝ)) := by
  induction K with
  | zero =>
    have hIcc : Icc a a = {a} := by ext j; simp only [mem_Icc, mem_singleton]; omega
    simp only [add_zero, hIcc, sum_singleton, range_zero, sum_empty]
    simp only [div_eq_mul_inv]
    ring
  | succ K ih =>
    have hIcc : Icc a (a + (K + 1)) = insert (a + K + 1) (Icc a (a + K)) := by
      ext j; simp only [mem_Icc, mem_insert]; omega
    have hnot : a + K + 1 ∉ Icc a (a + K) := by simp only [mem_Icc]; omega
    rw [hIcc, sum_insert hnot, ih, Finset.sum_range_succ,
      show a + (K + 1) = a + K + 1 by omega, show a + K + 1 - 1 = a + K by omega]
    simp only [div_eq_mul_inv]
    ring

private theorem sum_range_inv_telescope (a K : ℕ) :
    ∑ i ∈ range K, (1 / ((a + i : ℕ) : ℝ) - 1 / ((a + i + 1 : ℕ) : ℝ)) =
      1 / (a : ℝ) - 1 / ((a + K : ℕ) : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, show a + (K + 1) = a + K + 1 by omega]
    ring

/-- Uniform Fejér–Abel lower bound `-4 ≤ ∑_{d=1}^M cos(dθ)/d` for all `M : ℕ` and `θ : ℝ`. -/
theorem neg_four_le_sum_cos_div (M : ℕ) (θ : ℝ) :
    (-4 : ℝ) ≤ ∑ d ∈ Icc 1 M, Real.cos ((d : ℝ) * θ) / (d : ℝ) := by
  set δ : ℝ := 2 * |Real.sin (θ / 2)|
  have hδ0 : 0 ≤ δ := by positivity
  by_cases hMδ : (M : ℝ) * δ ≤ 1
  · have hnn : 0 ≤ ∑ d ∈ Icc 1 M, Real.cos ((d : ℝ) * θ) / (d : ℝ) := by
      refine sum_nonneg fun d hd => ?_
      have hd1 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      have hdM : (d : ℝ) ≤ M := by exact_mod_cast (mem_Icc.mp hd).2
      have hdδ : (d : ℝ) * δ ≤ 1 := (mul_le_mul_of_nonneg_right hdM hδ0).trans hMδ
      exact div_nonneg (cos_nonneg_of_mul_two_abs_sin_le_one hdδ) hd1.le
    linarith only [hnn]
  · replace hMδ := not_le.mp hMδ
    have hδ_pos : 0 < δ := by
      rcases hδ0.eq_or_lt with h0 | hpos
      · exfalso; rw [← h0, mul_zero] at hMδ; linarith only [hMδ]
      · exact hpos
    have h1δM : 1 / δ < (M : ℝ) := (div_lt_iff₀ hδ_pos).mpr (by linarith only [hMδ])
    set A : ℕ := ⌊1 / δ⌋₊
    have hA_le : (A : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
    have hAM_lt : A < M := by exact_mod_cast hA_le.trans_lt h1δM
    have hA1_le_M : A + 1 ≤ M := Nat.succ_le_of_lt hAM_lt
    have h1δ_lt : 1 / δ < ((A + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (1 / δ)
    have hδA1 : 1 < δ * ((A + 1 : ℕ) : ℝ) := by
      have h := (div_lt_iff₀ hδ_pos).mp h1δ_lt
      linarith only [h]
    have hsplit : Icc 1 M = Icc 1 A ∪ Icc (A + 1) M := by
      ext d; simp only [mem_union, mem_Icc]; omega
    have hdisj : Disjoint (Icc 1 A) (Icc (A + 1) M) := by
      rw [disjoint_left]
      intro d hd1 hd2
      simp only [mem_Icc] at hd1 hd2
      omega
    rw [hsplit, sum_union hdisj]
    have hhead : 0 ≤ ∑ d ∈ Icc 1 A, Real.cos ((d : ℝ) * θ) / (d : ℝ) := by
      refine sum_nonneg fun d hd => ?_
      have hd1 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      have hdA : (d : ℝ) ≤ A := by exact_mod_cast (mem_Icc.mp hd).2
      have hdδ : (d : ℝ) * δ ≤ 1 := by
        have h1 : (d : ℝ) ≤ 1 / δ := hdA.trans hA_le
        rwa [le_div_iff₀ hδ_pos] at h1
      exact div_nonneg (cos_nonneg_of_mul_two_abs_sin_le_one hdδ) hd1.le
    set D : ℕ → ℝ := fun k => ∑ j ∈ Icc 1 k, Real.cos ((j : ℝ) * θ)
    have hD_le : ∀ k, |D k| ≤ 2 / δ := fun k => by
      rw [le_div_iff₀ hδ_pos, mul_comm]
      exact two_abs_sin_mul_abs_sum_cos_le k θ
    have hD_step : ∀ {d : ℕ}, 1 ≤ d → Real.cos ((d : ℝ) * θ) = D d - D (d - 1) := by
      intro d hd
      obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
      have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext j; simp only [mem_Icc, mem_insert]; omega
      have hnot : m + 1 ∉ Icc 1 m := by simp only [mem_Icc]; omega
      simp only [D, hIcc, sum_insert hnot, Nat.add_sub_cancel]
      ring
    obtain ⟨K, hMK⟩ : ∃ K, M = A + 1 + K := ⟨M - (A + 1), by omega⟩
    have htail_eq : ∑ d ∈ Icc (A + 1) M, Real.cos ((d : ℝ) * θ) / (d : ℝ) =
        ∑ d ∈ Icc (A + 1) (A + 1 + K), (D d - D (d - 1)) / (d : ℝ) := by
      rw [hMK]
      refine sum_congr rfl fun d hd => ?_
      rw [hD_step (by have := (mem_Icc.mp hd).1; omega)]
    rw [htail_eq, abel_sum_Icc D (by omega : 1 ≤ A + 1) K, Nat.add_sub_cancel]
    have ha1_pos : (0 : ℝ) < ((A + 1 : ℕ) : ℝ) := by positivity
    have haK_pos : (0 : ℝ) < ((A + 1 + K : ℕ) : ℝ) := by positivity
    have hsum_abs : |∑ i ∈ range K,
          D (A + 1 + i) * (1 / ((A + 1 + i : ℕ) : ℝ) - 1 / ((A + 1 + i + 1 : ℕ) : ℝ))| ≤
        (2 / δ) * (1 / ((A + 1 : ℕ) : ℝ) - 1 / ((A + 1 + K : ℕ) : ℝ)) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ range K,
            |D (A + 1 + i) * (1 / ((A + 1 + i : ℕ) : ℝ) - 1 / ((A + 1 + i + 1 : ℕ) : ℝ))|
          ≤ ∑ i ∈ range K,
              (2 / δ) * (1 / ((A + 1 + i : ℕ) : ℝ) - 1 / ((A + 1 + i + 1 : ℕ) : ℝ)) := by
            refine sum_le_sum fun i _ => ?_
            have hpos_i : (0 : ℝ) < ((A + 1 + i : ℕ) : ℝ) := by positivity
            have hle_i : ((A + 1 + i : ℕ) : ℝ) ≤ ((A + 1 + i + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.le_succ _
            have hdiff_nn : 0 ≤ 1 / ((A + 1 + i : ℕ) : ℝ) - 1 / ((A + 1 + i + 1 : ℕ) : ℝ) :=
              sub_nonneg.mpr (one_div_le_one_div_of_le hpos_i hle_i)
            rw [abs_mul, abs_of_nonneg hdiff_nn]
            exact mul_le_mul_of_nonneg_right (hD_le _) hdiff_nn
        _ = (2 / δ) * (1 / ((A + 1 : ℕ) : ℝ) - 1 / ((A + 1 + K : ℕ) : ℝ)) := by
            rw [← mul_sum, sum_range_inv_telescope]
    have htot_abs : |D (A + 1 + K) / ((A + 1 + K : ℕ) : ℝ) - D A / ((A + 1 : ℕ) : ℝ) +
          ∑ i ∈ range K,
            D (A + 1 + i) * (1 / ((A + 1 + i : ℕ) : ℝ) - 1 / ((A + 1 + i + 1 : ℕ) : ℝ))| ≤ 4 := by
      have hb1 : |D (A + 1 + K) / ((A + 1 + K : ℕ) : ℝ)| ≤ (2 / δ) / ((A + 1 + K : ℕ) : ℝ) := by
        rw [abs_div, abs_of_pos haK_pos]
        exact div_le_div_of_nonneg_right (hD_le _) haK_pos.le
      have hb2 : |D A / ((A + 1 : ℕ) : ℝ)| ≤ (2 / δ) / ((A + 1 : ℕ) : ℝ) := by
        rw [abs_div, abs_of_pos ha1_pos]
        exact div_le_div_of_nonneg_right (hD_le _) ha1_pos.le
      have htri : |D (A + 1 + K) / ((A + 1 + K : ℕ) : ℝ) - D A / ((A + 1 : ℕ) : ℝ) +
            ∑ i ∈ range K, D (A + 1 + i) *
              (1 / ((A + 1 + i : ℕ) : ℝ) - 1 / ((A + 1 + i + 1 : ℕ) : ℝ))| ≤
          |D (A + 1 + K) / ((A + 1 + K : ℕ) : ℝ)| + |D A / ((A + 1 : ℕ) : ℝ)| +
            |∑ i ∈ range K, D (A + 1 + i) *
              (1 / ((A + 1 + i : ℕ) : ℝ) - 1 / ((A + 1 + i + 1 : ℕ) : ℝ))| := by
        have h1 := abs_add_le (D (A + 1 + K) / ((A + 1 + K : ℕ) : ℝ) - D A / ((A + 1 : ℕ) : ℝ))
          (∑ i ∈ range K, D (A + 1 + i) *
            (1 / ((A + 1 + i : ℕ) : ℝ) - 1 / ((A + 1 + i + 1 : ℕ) : ℝ)))
        have h2 := abs_sub (D (A + 1 + K) / ((A + 1 + K : ℕ) : ℝ)) (D A / ((A + 1 : ℕ) : ℝ))
        linarith only [h1, h2]
      have hsimp : (2 / δ) / ((A + 1 + K : ℕ) : ℝ) + (2 / δ) / ((A + 1 : ℕ) : ℝ) +
          (2 / δ) * (1 / ((A + 1 : ℕ) : ℝ) - 1 / ((A + 1 + K : ℕ) : ℝ)) =
          4 / (δ * ((A + 1 : ℕ) : ℝ)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      have hlt4 : 4 / (δ * ((A + 1 : ℕ) : ℝ)) ≤ 4 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [hδA1]
      linarith only [htri, hb1, hb2, hsum_abs, hsimp, hlt4]
    have hlow := neg_abs_le (D (A + 1 + K) / ((A + 1 + K : ℕ) : ℝ) - D A / ((A + 1 : ℕ) : ℝ) +
      ∑ i ∈ range K, D (A + 1 + i) * (1 / ((A + 1 + i : ℕ) : ℝ) - 1 / ((A + 1 + i + 1 : ℕ) : ℝ)))
    linarith only [hhead, htot_abs, hlow]

private theorem sin_nat_mul_pi (m : ℕ) : Real.sin ((m : ℝ) * Real.pi) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    rw [add_mul, one_mul, Real.sin_add, ih, Real.sin_pi]
    ring

private theorem integral_cos_nat_mul_two_pi (k : ℕ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * θ) =
      if k = 0 then 2 * Real.pi else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [if_neg hk.ne']
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hderiv : ∀ θ : ℝ,
        HasDerivAt (fun t : ℝ => Real.sin ((k : ℝ) * t) / (k : ℝ))
          (Real.cos ((k : ℝ) * θ)) θ := fun θ => by
      have h1 := ((Real.hasDerivAt_sin ((k : ℝ) * θ)).comp θ
        ((hasDerivAt_id θ).const_mul (k : ℝ))).div_const (k : ℝ)
      refine h1.congr_deriv ?_
      field_simp [hk0]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
      ((by fun_prop : Continuous fun θ : ℝ => Real.cos ((k : ℝ) * θ)).intervalIntegrable _ _)]
    have h2pi : (k : ℝ) * (2 * Real.pi) = ((2 * k : ℕ) : ℝ) * Real.pi := by push_cast; ring
    rw [h2pi, sin_nat_mul_pi, mul_zero, Real.sin_zero, zero_div, sub_self]

private theorem integral_cos_mul_cos_two_pi {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos ((d : ℝ) * θ) * Real.cos ((k : ℝ) * θ) =
      if d = k then Real.pi else 0 := by
  set m : ℕ := if k ≤ d then d - k else k - d
  have htrig : ∀ θ : ℝ, Real.cos ((d : ℝ) * θ) * Real.cos ((k : ℝ) * θ) =
      (1 / 2 : ℝ) * (Real.cos (((d + k : ℕ) : ℝ) * θ) + Real.cos ((m : ℝ) * θ)) := fun θ => by
    have hsum : ((d + k : ℕ) : ℝ) * θ = (d : ℝ) * θ + (k : ℝ) * θ := by push_cast; ring
    rw [hsum, Real.cos_add]
    by_cases hkd : k ≤ d
    · have hm : (m : ℝ) * θ = (d : ℝ) * θ - (k : ℝ) * θ := by
        simp only [m, if_pos hkd, Nat.cast_sub hkd]; ring
      rw [hm, Real.cos_sub]
      ring
    · have hdk : d ≤ k := le_of_not_ge hkd
      have hm : (m : ℝ) * θ = (k : ℝ) * θ - (d : ℝ) * θ := by
        simp only [m, if_neg hkd, Nat.cast_sub hdk]; ring
      rw [hm, Real.cos_sub]
      ring
  simp_rw [htrig]
  have hint1 : IntervalIntegrable (fun θ : ℝ => Real.cos (((d + k : ℕ) : ℝ) * θ))
      volume 0 (2 * Real.pi) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ : ℝ => Real.cos ((m : ℝ) * θ))
      volume 0 (2 * Real.pi) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hint1 hint2,
    integral_cos_nat_mul_two_pi, integral_cos_nat_mul_two_pi, if_neg (by omega : d + k ≠ 0),
    zero_add]
  by_cases hdk : d = k
  · subst hdk
    simp only [m, le_rfl, if_true, Nat.sub_self]
    ring
  · have hm0 : m ≠ 0 := by simp only [m]; split_ifs <;> omega
    rw [if_neg hm0, if_neg hdk, mul_zero]

private theorem sum_inv_abs_sub_ge (M : ℕ) (b : ℕ → ℝ) :
    -8 * (∑ n ∈ Icc 1 M, b n ^ 2) ≤
      ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / |(n : ℝ) - j| := by
  set W : ℝ → ℝ := fun θ => 4 + ∑ d ∈ Icc 1 M, Real.cos ((d : ℝ) * θ) / (d : ℝ)
  set P : ℝ → ℝ := fun θ =>
    (∑ n ∈ Icc 1 M, b n * Real.cos ((n : ℝ) * θ)) ^ 2 +
      (∑ n ∈ Icc 1 M, b n * Real.sin ((n : ℝ) * θ)) ^ 2
  have hWP_nn : ∀ θ : ℝ, 0 ≤ W θ * P θ := fun θ => by
    have hW : 0 ≤ W θ := by
      have := neg_four_le_sum_cos_div M θ
      dsimp only [W]
      linarith only [this]
    have hP : 0 ≤ P θ := add_nonneg (sq_nonneg _) (sq_nonneg _)
    exact mul_nonneg hW hP
  have hP_eq : ∀ θ : ℝ, P θ = ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
      b n * b j * Real.cos ((if j ≤ n then n - j else j - n : ℕ) * θ) := fun θ => by
    dsimp only [P]
    rw [sq, sum_mul, sq, sum_mul]
    simp_rw [mul_sum]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases hjn : j ≤ n
    · rw [if_pos hjn, Nat.cast_sub hjn, sub_mul, Real.cos_sub]
      ring
    · have hnj : n ≤ j := le_of_not_ge hjn
      rw [if_neg hjn, Nat.cast_sub hnj, sub_mul, Real.cos_sub]
      ring
  have hint_nonneg : 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), W θ * P θ :=
    intervalIntegral.integral_nonneg (by positivity) fun θ _ => hWP_nn θ
  have hpair_int : ∀ n ∈ Icc 1 M, ∀ j ∈ Icc 1 M,
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          W θ * Real.cos (((if j ≤ n then n - j else j - n : ℕ) : ℝ) * θ)) =
        if n = j then 8 * Real.pi else Real.pi / |(n : ℝ) - j| := by
    intro n hn j hj
    set k : ℕ := if j ≤ n then n - j else j - n
    have hrew : (fun θ : ℝ => W θ * Real.cos ((k : ℝ) * θ)) =
        fun θ => 4 * Real.cos ((k : ℝ) * θ) +
          ∑ d ∈ Icc 1 M, (1 / (d : ℝ)) * (Real.cos ((d : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) := by
      funext θ
      simp only [W, add_mul, sum_mul]
      congr 1
      exact sum_congr rfl fun d _ => by ring
    rw [hrew]
    have hi1 : IntervalIntegrable (fun θ : ℝ => 4 * Real.cos ((k : ℝ) * θ))
        volume 0 (2 * Real.pi) :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    have hi2 : ∀ d ∈ Icc 1 M, IntervalIntegrable
        (fun θ : ℝ => (1 / (d : ℝ)) * (Real.cos ((d : ℝ) * θ) * Real.cos ((k : ℝ) * θ)))
        volume 0 (2 * Real.pi) := fun d _ =>
      (by fun_prop : Continuous _).intervalIntegrable _ _
    have hi2_sum : IntervalIntegrable
        (fun θ : ℝ => ∑ d ∈ Icc 1 M,
          (1 / (d : ℝ)) * (Real.cos ((d : ℝ) * θ) * Real.cos ((k : ℝ) * θ)))
        volume 0 (2 * Real.pi) :=
      (continuous_finsetSum _ fun d _ => by fun_prop).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 hi2_sum,
      intervalIntegral.integral_const_mul, integral_cos_nat_mul_two_pi,
      intervalIntegral.integral_finsetSum hi2]
    by_cases hnj : n = j
    · subst hnj
      have hk0 : k = 0 := by simp [k]
      rw [if_pos rfl, hk0, if_pos rfl]
      have hsum0 : (∑ d ∈ Icc 1 M,
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (1 / (d : ℝ)) * (Real.cos ((d : ℝ) * θ) * Real.cos (((0 : ℕ) : ℝ) * θ))) = 0 := by
        refine sum_eq_zero fun d hd => ?_
        have hd1 := (mem_Icc.mp hd).1
        rw [intervalIntegral.integral_const_mul, integral_cos_mul_cos_two_pi hd1 0,
          if_neg (by omega), mul_zero]
      rw [hsum0]
      ring
    · have hk_pos : 1 ≤ k := by simp only [k]; split_ifs <;> omega
      have hkM : k ≤ M := by
        have hnM := (mem_Icc.mp hn).2
        have hjM := (mem_Icc.mp hj).2
        simp only [k]; split_ifs <;> omega
      have hk_mem : k ∈ Icc 1 M := mem_Icc.mpr ⟨hk_pos, hkM⟩
      have hk_abs : (k : ℝ) = |(n : ℝ) - j| := by
        by_cases hjn : j ≤ n
        · have hR : (j : ℝ) ≤ n := by exact_mod_cast hjn
          simp only [k, if_pos hjn, Nat.cast_sub hjn, abs_of_nonneg (sub_nonneg.mpr hR)]
        · have hR : (n : ℝ) ≤ j := by exact_mod_cast le_of_not_ge hjn
          simp only [k, if_neg hjn, Nat.cast_sub (le_of_not_ge hjn),
            abs_of_nonpos (sub_nonpos.mpr hR)]
          ring
      rw [if_neg hnj, if_neg (by omega : k ≠ 0), mul_zero, zero_add]
      have hsum_eval : ∀ d ∈ Icc 1 M,
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (1 / (d : ℝ)) * (Real.cos ((d : ℝ) * θ) * Real.cos ((k : ℝ) * θ))) =
            if d = k then Real.pi / (k : ℝ) else 0 := by
        intro d hd
        rw [intervalIntegral.integral_const_mul,
          integral_cos_mul_cos_two_pi (mem_Icc.mp hd).1 k]
        split_ifs with hdk
        · subst hdk; ring
        · ring
      rw [sum_congr rfl hsum_eval, sum_ite_eq' _ _ _, if_pos hk_mem, hk_abs]
  have hint_eval : (∫ θ in (0 : ℝ)..(2 * Real.pi), W θ * P θ) =
      8 * Real.pi * (∑ n ∈ Icc 1 M, b n ^ 2) +
        Real.pi * ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
          if n = j then 0 else b n * b j / |(n : ℝ) - j| := by
    have hexp : ∀ θ : ℝ, W θ * P θ =
        ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
          (b n * b j) * (W θ * Real.cos (((if j ≤ n then n - j else j - n : ℕ) : ℝ) * θ)) := by
      intro θ
      rw [hP_eq θ, mul_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    simp_rw [hexp]
    have hcontW : Continuous W := by
      unfold W
      exact continuous_const.add (continuous_finsetSum _ fun d _ => by fun_prop)
    have hcont_term : ∀ n j : ℕ, Continuous (fun θ : ℝ => (b n * b j) *
        (W θ * Real.cos (((if j ≤ n then n - j else j - n : ℕ) : ℝ) * θ))) :=
      fun _ _ => continuous_const.mul
        (hcontW.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    have hint_row : ∀ n ∈ Icc 1 M, ∀ j ∈ Icc 1 M, IntervalIntegrable
        (fun θ : ℝ => (b n * b j) *
          (W θ * Real.cos (((if j ≤ n then n - j else j - n : ℕ) : ℝ) * θ)))
        volume 0 (2 * Real.pi) := fun n _ j _ => (hcont_term n j).intervalIntegrable _ _
    have hint_outer : ∀ n ∈ Icc 1 M, IntervalIntegrable
        (fun θ : ℝ => ∑ j ∈ Icc 1 M, (b n * b j) *
          (W θ * Real.cos (((if j ≤ n then n - j else j - n : ℕ) : ℝ) * θ)))
        volume 0 (2 * Real.pi) := fun n _ =>
      (continuous_finsetSum _ fun j _ => hcont_term n j).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hint_outer]
    have hrow : ∀ n ∈ Icc 1 M,
        (∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ j ∈ Icc 1 M, (b n * b j) *
          (W θ * Real.cos (((if j ≤ n then n - j else j - n : ℕ) : ℝ) * θ))) =
        8 * Real.pi * b n ^ 2 +
          Real.pi * ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / |(n : ℝ) - j| := by
      intro n hn
      rw [intervalIntegral.integral_finsetSum fun j hj => hint_row n hn j hj]
      have hterm : ∀ j ∈ Icc 1 M,
          (∫ θ in (0 : ℝ)..(2 * Real.pi), (b n * b j) *
            (W θ * Real.cos (((if j ≤ n then n - j else j - n : ℕ) : ℝ) * θ))) =
          (if n = j then 8 * Real.pi * b n ^ 2 else 0) +
            Real.pi * (if n = j then 0 else b n * b j / |(n : ℝ) - j|) := by
        intro j hj
        rw [intervalIntegral.integral_const_mul, hpair_int n hn j hj]
        split_ifs with hnj
        · subst hnj; ring
        · ring
      rw [sum_congr rfl hterm, sum_add_distrib, sum_ite_eq, if_pos hn, mul_sum]
    rw [sum_congr rfl hrow, sum_add_distrib, ← mul_sum, ← mul_sum]
  rw [hint_eval] at hint_nonneg
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith only [hint_nonneg, hpi]

private theorem sum_inv_add_ge (M : ℕ) (b : ℕ → ℝ) :
    -(1 / 2 : ℝ) * (∑ n ∈ Icc 1 M, b n ^ 2) ≤
      ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / ((n : ℝ) + j) := by
  have hint_nn : 0 ≤ ∫ t in (0 : ℝ)..1, t * (∑ n ∈ Icc 1 M, b n * t ^ (n - 1)) ^ 2 := by
    refine intervalIntegral.integral_nonneg zero_le_one fun t ht => ?_
    exact mul_nonneg ht.1 (sq_nonneg _)
  have hint_eval : (∫ t in (0 : ℝ)..1, t * (∑ n ∈ Icc 1 M, b n * t ^ (n - 1)) ^ 2) =
      ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, b n * b j / ((n : ℝ) + j) := by
    have hexp : ∀ t : ℝ, t * (∑ n ∈ Icc 1 M, b n * t ^ (n - 1)) ^ 2 =
        ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, (b n * b j) * t ^ ((n - 1) + (j - 1) + 1) := fun t => by
      rw [sq, sum_mul, mul_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [pow_succ, pow_add]
      ring
    simp_rw [hexp]
    have hi : ∀ n ∈ Icc 1 M, ∀ j ∈ Icc 1 M,
        IntervalIntegrable (fun t : ℝ => (b n * b j) * t ^ ((n - 1) + (j - 1) + 1)) volume 0 1 :=
      fun _ _ _ _ => (by fun_prop : Continuous _).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum fun n _ =>
      (continuous_finsetSum _ fun j _ => by fun_prop).intervalIntegrable _ _]
    refine sum_congr rfl fun n hn => ?_
    rw [intervalIntegral.integral_finsetSum fun j hj => hi n hn j hj]
    refine sum_congr rfl fun j hj => ?_
    have hn1 := (mem_Icc.mp hn).1
    have hj1 := (mem_Icc.mp hj).1
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have hexp_eq : (n - 1) + (j - 1) + 1 + 1 = n + j := by omega
    have hden_eq : (((n - 1) + (j - 1) + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + j := by
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hn1, Nat.cast_sub hj1, Nat.cast_one]
      ring
    rw [hexp_eq, hden_eq, one_pow, zero_pow (by omega : n + j ≠ 0), sub_zero]
    ring
  rw [hint_eval] at hint_nn
  have hsplit : (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, b n * b j / ((n : ℝ) + j)) =
      (∑ n ∈ Icc 1 M, b n ^ 2 / (2 * (n : ℝ))) +
        ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / ((n : ℝ) + j) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [sum_eq_diag_add hn]
    congr 1
    ring
  have hdiag_le : (∑ n ∈ Icc 1 M, b n ^ 2 / (2 * (n : ℝ))) ≤
      (1 / 2 : ℝ) * ∑ n ∈ Icc 1 M, b n ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hdiv : 1 / (2 * (n : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith only [hn1])
    calc b n ^ 2 / (2 * (n : ℝ))
        = (1 / (2 * (n : ℝ))) * b n ^ 2 := by ring
      _ ≤ (1 / 2) * b n ^ 2 := mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)
  linarith only [hint_nn, hsplit, hdiag_le]

/-- **Pole-gauge lower bound on the archimedean center kernel**: for every `M : ℕ` and `x : ℕ → ℝ`,
`-(17 / 4) * ∑_{n ≤ M} n x_n² ≤ ∑_{n, j ≤ M} x_n x_j archimedeanCenterKernel n j`. -/
theorem sum_archimedeanCenterKernel_ge (M : ℕ) (x : ℕ → ℝ) :
    -(17 / 4 : ℝ) * (∑ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2) ≤
      ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j := by
  set b : ℕ → ℝ := fun n => Real.sqrt n * x n
  have hbsq : ∑ n ∈ Icc 1 M, b n ^ 2 = ∑ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt hn0]
  have hterm : ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j =
      (1 / 2 : ℝ) *
        ((∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / |(n : ℝ) - j|) +
          ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / ((n : ℝ) + j)) := by
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    by_cases hnj : n = j
    · subst hnj
      simp [archimedeanCenterKernel_self]
    · have hn1 := (mem_Icc.mp hn).1
      have hj1 := (mem_Icc.mp hj).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
      have hsj : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hj0).ne'
      have hdiv := archimedeanCenterKernel_div_sqrt_mul hn1 hj1 hnj
      rw [if_neg hnj, if_neg hnj]
      have hker : archimedeanCenterKernel n j =
          (Real.sqrt n * Real.sqrt j) *
            ((1 / 2 : ℝ) * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j))) := by
        rw [div_eq_iff (mul_ne_zero hsn hsj)] at hdiv
        linarith only [hdiv]
      rw [hker]
      dsimp only [b]
      ring
  have h1 := sum_inv_abs_sub_ge M b
  have h2 := sum_inv_add_ge M b
  rw [hterm, ← hbsq]
  linarith only [h1, h2]

/-! ### 3. Quadratic cross-error bound on bounded-pole vectors -/

private theorem sum_Icc_inv_sq_le_two (K : ℕ) :
    ∑ d ∈ Icc 1 K, 1 / (d : ℝ) ^ 2 ≤ 2 := by
  induction K with
  | zero => simp
  | succ K _ =>
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · norm_num
    · have hsplit : Icc 1 (K + 1) = insert 1 (Icc 2 (K + 1)) := by
        ext d; simp only [mem_Icc, mem_insert]; omega
      have hnot : (1 : ℕ) ∉ Icc 2 (K + 1) := by simp only [mem_Icc]; omega
      rw [hsplit, sum_insert hnot]
      have htel : ∑ d ∈ Icc 2 (K + 1), 1 / (d : ℝ) ^ 2 ≤
          ∑ i ∈ range K, (1 / ((1 + i : ℕ) : ℝ) - 1 / ((1 + i + 1 : ℕ) : ℝ)) := by
        have hbij : ∑ d ∈ Icc 2 (K + 1), 1 / (d : ℝ) ^ 2 =
            ∑ i ∈ range K, 1 / ((1 + i + 1 : ℕ) : ℝ) ^ 2 := by
          refine sum_nbij' (fun d => d - 2) (fun i => 1 + i + 1) ?_ ?_ ?_ ?_ ?_
          · intro d hd; simp only [mem_Icc] at hd; simp only [mem_range]; omega
          · intro i hi; simp only [mem_range] at hi; simp only [mem_Icc]; omega
          · intro d hd; simp only [mem_Icc] at hd; omega
          · intro i _; omega
          · intro d hd
            have hd2 : 1 + (d - 2) + 1 = d := by simp only [mem_Icc] at hd; omega
            rw [hd2]
        rw [hbij]
        refine sum_le_sum fun i _ => ?_
        set m : ℝ := ((1 + i : ℕ) : ℝ)
        have hm1 : (1 : ℝ) ≤ m := by
          dsimp only [m]; exact_mod_cast (by omega : 1 ≤ 1 + i)
        have hm0 : 0 < m := by linarith only [hm1]
        have hm1_pos : 0 < m + 1 := by linarith only [hm1]
        have hcast : ((1 + i + 1 : ℕ) : ℝ) = m + 1 := by dsimp only [m]; push_cast; ring
        rw [hcast]
        have hle : m * (m + 1) ≤ (m + 1) ^ 2 := by nlinarith only [hm0]
        calc 1 / (m + 1) ^ 2
            ≤ 1 / (m * (m + 1)) := one_div_le_one_div_of_le (mul_pos hm0 hm1_pos) hle
          _ = 1 / m - 1 / (m + 1) := by field_simp [hm0.ne', hm1_pos.ne']; ring
      rw [sum_range_inv_telescope 1 K] at htel
      have hpos : 0 ≤ 1 / ((1 + K : ℕ) : ℝ) := by positivity
      have h1 : (1 : ℝ) / (1 : ℕ) ^ 2 = 1 := by norm_num
      have h2 : (1 : ℝ) / (1 : ℕ) = 1 := by norm_num
      rw [h1]
      rw [h2] at htel
      linarith only [htel, hpos]

/-- On any vector with `n x_n² ≤ 4` on `Icc 1 M`, the off-diagonal cross-error majorant sums to
`O(M²)` with no logarithmic factor. -/
theorem sum_cross_error_bounded_pole_le {M : ℕ} {x : ℕ → ℝ}
    (hx : ∀ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ 4) :
    ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
        (if n = j then 0 else |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) ≤
      56 * (M : ℝ) ^ 2 := by
  have hx_abs : ∀ n ∈ Icc 1 M, |x n| ≤ 2 := fun n hn => by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have h4 := hx n hn
    have hsq : x n ^ 2 ≤ 2 ^ 2 := by nlinarith only [hn1, h4, sq_nonneg (x n)]
    have habs : |x n| ^ 2 ≤ 2 ^ 2 := by rwa [sq_abs]
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by norm_num) two_ne_zero).mp habs
  have hlt_term : ∀ j ∈ Icc 1 M, ∀ n ∈ Icc 1 (j - 1),
      |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 ≤
        16 + 6 * (j : ℝ) * (1 / ((j : ℝ) - n) ^ 2) := by
    intro j hj n hn
    have hjM := (mem_Icc.mp hj).2
    have hn1 := (mem_Icc.mp hn).1
    have hnj_lt : n < j := by
      have hj1 := (mem_Icc.mp hj).1
      have hnj1 := (mem_Icc.mp hn).2
      omega
    have hnM : n ∈ Icc 1 M := mem_Icc.mpr ⟨hn1, hnj_lt.le.trans hjM⟩
    have hnjR : (n : ℝ) < j := by exact_mod_cast hnj_lt
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    have hdiff_pos : 0 < (j : ℝ) - n := sub_pos.mpr hnjR
    have hmax : max (n : ℝ) j = j := max_eq_right hnjR.le
    have habs_sq : |(n : ℝ) - j| ^ 2 = ((j : ℝ) - n) ^ 2 := by
      rw [abs_sub_comm, sq_abs]
    rw [hmax, habs_sq]
    by_cases h2n : 2 * n < j
    · have h2nR : 2 * (n : ℝ) < j := by exact_mod_cast h2n
      have hhalf : (j : ℝ) / 2 ≤ (j : ℝ) - n := by linarith only [h2nR]
      have hsq_ge : (j : ℝ) ^ 2 / 4 ≤ ((j : ℝ) - n) ^ 2 := by
        have h := pow_le_pow_left₀ (by positivity) hhalf 2
        linarith only [h]
      have hquot : (j : ℝ) ^ 2 / ((j : ℝ) - n) ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (sq_pos_of_pos hdiff_pos)]
        linarith only [hsq_ge]
      have hprod : |x n| * |x j| ≤ 4 := by
        have h1 := hx_abs n hnM
        have h2 := hx_abs j hj
        nlinarith only [h1, h2, abs_nonneg (x n), abs_nonneg (x j)]
      have h16 : |x n| * |x j| * (j : ℝ) ^ 2 / ((j : ℝ) - n) ^ 2 ≤ 16 := by
        calc |x n| * |x j| * (j : ℝ) ^ 2 / ((j : ℝ) - n) ^ 2
            = (|x n| * |x j|) * ((j : ℝ) ^ 2 / ((j : ℝ) - n) ^ 2) := by ring
          _ ≤ 4 * 4 := mul_le_mul hprod hquot (by positivity) (by norm_num)
          _ = 16 := by norm_num
      have hpos_r : 0 ≤ 6 * (j : ℝ) * (1 / ((j : ℝ) - n) ^ 2) := by positivity
      linarith only [h16, hpos_r]
    · have hj2n : (j : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast not_lt.mp h2n
      have hxn := hx n hnM
      have hxj := hx j hj
      have hsq32 : (|x n| * |x j| * (j : ℝ)) ^ 2 ≤ 6 ^ 2 := by
        calc (|x n| * |x j| * (j : ℝ)) ^ 2
            = x n ^ 2 * x j ^ 2 * (j : ℝ) ^ 2 := by
              rw [mul_pow, mul_pow, sq_abs, sq_abs]
          _ ≤ x n ^ 2 * x j ^ 2 * ((2 * (n : ℝ)) * (j : ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
              nlinarith only [hj2n, hj0]
          _ = 2 * ((n : ℝ) * x n ^ 2) * ((j : ℝ) * x j ^ 2) := by ring
          _ ≤ 2 * 4 * 4 := by
              have hnx0 : 0 ≤ (n : ℝ) * x n ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
              have hjx0 : 0 ≤ (j : ℝ) * x j ^ 2 := mul_nonneg (Nat.cast_nonneg j) (sq_nonneg _)
              nlinarith only [hxn, hxj, hnx0, hjx0]
          _ ≤ 6 ^ 2 := by norm_num
      have h6 : |x n| * |x j| * (j : ℝ) ≤ 6 :=
        (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).mp hsq32
      have hterm6 : |x n| * |x j| * (j : ℝ) ^ 2 / ((j : ℝ) - n) ^ 2 ≤
          6 * (j : ℝ) * (1 / ((j : ℝ) - n) ^ 2) := by
        calc |x n| * |x j| * (j : ℝ) ^ 2 / ((j : ℝ) - n) ^ 2
            = (|x n| * |x j| * (j : ℝ)) * ((j : ℝ) * (1 / ((j : ℝ) - n) ^ 2)) := by ring
          _ ≤ 6 * ((j : ℝ) * (1 / ((j : ℝ) - n) ^ 2)) :=
              mul_le_mul_of_nonneg_right h6 (by positivity)
          _ = 6 * (j : ℝ) * (1 / ((j : ℝ) - n) ^ 2) := by ring
      linarith only [hterm6]
  have hupper_triangle :
      (∑ j ∈ Icc 1 M, ∑ n ∈ Icc 1 (j - 1),
          |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) ≤ 28 * (M : ℝ) ^ 2 := by
    have hrow : ∀ j ∈ Icc 1 M,
        (∑ n ∈ Icc 1 (j - 1), |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) ≤
          28 * (M : ℝ) := by
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hjM : (j : ℝ) ≤ M := by exact_mod_cast (mem_Icc.mp hj).2
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hbij : ∑ n ∈ Icc 1 (j - 1), 1 / ((j : ℝ) - n) ^ 2 =
          ∑ d ∈ Icc 1 (j - 1), 1 / (d : ℝ) ^ 2 := by
        refine sum_nbij' (fun n => j - n) (fun d => j - d) ?_ ?_ ?_ ?_ ?_
        · intro n hn; simp only [mem_Icc] at hn ⊢; omega
        · intro d hd; simp only [mem_Icc] at hd ⊢; omega
        · intro n hn; simp only [mem_Icc] at hn; omega
        · intro d hd; simp only [mem_Icc] at hd; omega
        · intro n hn
          have hle : n ≤ j := by simp only [mem_Icc] at hn; omega
          rw [Nat.cast_sub hle]
      have hcard : (∑ _n ∈ Icc 1 (j - 1), (16 : ℝ)) ≤ 16 * (j : ℝ) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hle : ((j - 1 + 1 - 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast (by omega : j - 1 + 1 - 1 ≤ j)
        nlinarith only [hle]
      calc ∑ n ∈ Icc 1 (j - 1), |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2
          ≤ ∑ n ∈ Icc 1 (j - 1), (16 + 6 * (j : ℝ) * (1 / ((j : ℝ) - n) ^ 2)) :=
            sum_le_sum fun n hn => hlt_term j hj n hn
        _ = (∑ _n ∈ Icc 1 (j - 1), (16 : ℝ)) +
            6 * (j : ℝ) * ∑ n ∈ Icc 1 (j - 1), 1 / ((j : ℝ) - n) ^ 2 := by
            rw [sum_add_distrib, ← mul_sum]
        _ ≤ 16 * (j : ℝ) + 6 * (j : ℝ) * 2 := by
            rw [hbij]
            exact add_le_add hcard
              (mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le_two (j - 1)) (by positivity))
        _ = 28 * (j : ℝ) := by ring
        _ ≤ 28 * (M : ℝ) := by linarith only [hjM]
    calc ∑ j ∈ Icc 1 M, ∑ n ∈ Icc 1 (j - 1),
          |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2
        ≤ ∑ _j ∈ Icc 1 M, 28 * (M : ℝ) := sum_le_sum hrow
      _ = 28 * (M : ℝ) ^ 2 := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel_right, nsmul_eq_mul]
          ring
  have hfull_eq : (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
      if n = j then 0 else |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) =
      2 * ∑ j ∈ Icc 1 M, ∑ n ∈ Icc 1 (j - 1),
        |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
    set F : ℕ → ℕ → ℝ := fun n j => |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2
    have hsym : ∀ n j, F n j = F j n := fun n j => by
      dsimp only [F]
      rw [mul_comm |x n| |x j|, max_comm, abs_sub_comm]
    have hsplit_pair : ∀ n ∈ Icc 1 M, ∀ j ∈ Icc 1 M,
        (if n = j then (0 : ℝ) else F n j) =
          (if n < j then F n j else 0) + (if j < n then F j n else 0) := by
      intro n _ j _
      rcases lt_trichotomy n j with hlt | rfl | hgt
      · rw [if_neg hlt.ne, if_pos hlt, if_neg (not_lt.mpr hlt.le), add_zero]
      · simp
      · rw [if_neg hgt.ne', if_neg (not_lt.mpr hgt.le), if_pos hgt, zero_add, hsym]
    have h1 : (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else F n j) =
        (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n < j then F n j else 0) +
          ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if j < n then F j n else 0 := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun n hn => by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun j hj => hsplit_pair n hn j hj
    have hswap : (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n < j then F n j else 0) =
        ∑ j ∈ Icc 1 M, ∑ n ∈ Icc 1 M, if n < j then F n j else 0 := sum_comm
    have hinner : ∀ j ∈ Icc 1 M,
        (∑ n ∈ Icc 1 M, if n < j then F n j else 0) = ∑ n ∈ Icc 1 (j - 1), F n j := by
      intro j hj
      have hjM := (mem_Icc.mp hj).2
      have hsub : Icc 1 (j - 1) ⊆ Icc 1 M := fun n hn => by
        simp only [mem_Icc] at hn ⊢; omega
      rw [← sum_subset hsub]
      · refine sum_congr rfl fun n hn => ?_
        have hj1 := (mem_Icc.mp hj).1
        have hlt : n < j := by simp only [mem_Icc] at hn; omega
        rw [if_pos hlt]
      · intro n hn hnot
        rw [if_neg]
        intro hlt
        exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, by omega⟩)
    rw [h1, hswap]
    have heq_tri : (∑ j ∈ Icc 1 M, ∑ n ∈ Icc 1 M, if n < j then F n j else 0) =
        ∑ j ∈ Icc 1 M, ∑ n ∈ Icc 1 (j - 1), F n j :=
      sum_congr rfl hinner
    rw [heq_tri]
    ring
  rw [hfull_eq]
  linarith only [hupper_triangle]

/-! ### 4. Bounded-pole hyperplane witness for the Liouville twin -/

/-- Projected Liouville pole witness on `Icc 1 M`: supported on `Icc 1 M`, orthogonal to the pole
`∑ x_n / √n = 0`, obeying `n x_n² ≤ 4` and `log M - 2 ≤ ∑ x_n²`, and attaining `log M - γ - ε` in
the Liouville twin's prime form. -/
theorem exists_bounded_hyperplane_liouville_witness {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ M, M₀ ≤ M →
      ∃ x : ℕ → ℝ,
        (∀ n, n ∉ Icc 1 M → x n = 0) ∧
        ∑ n ∈ Icc 1 M, x n / Real.sqrt n = 0 ∧
        (∀ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ 4) ∧
        Real.log M - 2 ≤ ∑ n ∈ Icc 1 M, x n ^ 2 ∧
        0 < ∑ n ∈ Icc 1 M, x n ^ 2 ∧
        (Real.log M - Real.eulerMascheroniConstant - ε) * ∑ n ∈ Icc 1 M, x n ^ 2 ≤
          atomicWeilForm M (fun n => liouvilleSign n * x n) := by
  let γ := Real.eulerMascheroniConstant
  obtain ⟨M₁, hM₁⟩ := eventually_atomicWeilForm_truncPole_ge (show 0 < ε / 2 by positivity)
  set C₀ := Real.log 4 + 4
  set B := Real.log 4 + 4 + Real.log 2 + γ
  have hC₀ : 0 ≤ C₀ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hB : 0 ≤ B := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  set K := 4 + 4 * C₀ + 8 + 8 * γ + 4 * B
  obtain ⟨M₂, hM₂⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max (γ + ε) (max (2 * K / ε) 3)))
  refine ⟨max 1 (max M₁ M₂), le_max_left _ _, fun M hM => ?_⟩
  have hM1_ge : 1 ≤ M := (le_max_left _ _).trans hM
  have hMM₁ : M₁ ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hMM₂ : M₂ ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hlog_ge := hM₂ M hMM₂
  simp only [Function.comp] at hlog_ge
  have hLγ : γ + ε ≤ Real.log M := (le_max_left _ _).trans hlog_ge
  have hLK : 2 * K / ε ≤ Real.log M := ((le_max_left _ _).trans (le_max_right _ _)).trans hlog_ge
  have hL3 : 3 ≤ Real.log M := ((le_max_right _ _).trans (le_max_right _ _)).trans hlog_ge
  set b := truncPole M
  set H := ∑ n ∈ Icc 1 M, (1 : ℝ) / n
  set S := ∑ n ∈ Icc 1 M, liouvilleSign n / n
  set L := Real.log M
  have hb_zero : ∀ n, n ∉ Icc 1 M → b n = 0 := fun n hn => by
    simp only [mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn0 | hnM
    · have : n = 0 := by omega
      subst this; simp [b, truncPole, poleVector]
    · simp [b, truncPole, if_neg (not_le.mpr hnM)]
  have hb2 : ∀ n ∈ Icc 1 M, b n ^ 2 = 1 / n := fun n hn => by
    simp only [b, truncPole, if_pos (mem_Icc.mp hn).2, poleVector_sq]
  have hbsq : ∑ n ∈ Icc 1 M, b n ^ 2 = H := sum_congr rfl hb2
  have hbs : ∀ n ∈ Icc 1 M, b n / Real.sqrt n = 1 / n := fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [b, truncPole, if_pos (mem_Icc.mp hn).2, poleVector]
    rw [div_div, Real.mul_self_sqrt hn0.le]
  have hHL : L ≤ H := by
    have h := log_add_one_le_harmonic M
    rw [RHTower.harmonic_eq_sum_Icc] at h
    push_cast at h
    have : L ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log (by exact_mod_cast hM1_ge) (by linarith)
    linarith
  have hH3 : 3 ≤ H := hL3.trans hHL
  have hH0 : 0 < H := by linarith only [hH3]
  have hS := abs_sum_liouvilleSign_div_le M
  have hS2 : S ^ 2 ≤ 4 := by
    rw [← sq_abs, show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact pow_le_pow_left₀ (abs_nonneg S) hS 2
  set s := S / H
  have hs : |s| ≤ 2 / H := by
    rw [abs_div, abs_of_pos hH0]
    exact div_le_div_of_nonneg_right hS hH0.le
  have hs_le_one : |s| ≤ 1 := by
    refine hs.trans ?_
    rw [div_le_one hH0]
    linarith only [hH3]
  set x : ℕ → ℝ := fun n => (liouvilleSign n - s) * b n
  have hx_supp : ∀ n, n ∉ Icc 1 M → x n = 0 := fun n hn => by
    simp only [x, hb_zero n hn, mul_zero]
  have horth : ∑ n ∈ Icc 1 M, x n / Real.sqrt n = 0 := by
    have hpt : ∀ n ∈ Icc 1 M, x n / Real.sqrt n = liouvilleSign n / n - s * (1 / n) :=
      fun n hn => by
        rw [show x n / Real.sqrt n = (liouvilleSign n - s) * (b n / Real.sqrt n) by
          simp only [x]; ring, hbs n hn]
        ring
    rw [sum_congr rfl hpt, sum_sub_distrib, ← mul_sum]
    show S - s * H = 0
    rw [div_mul_cancel₀ S hH0.ne', sub_self]
  have hnx_le : ∀ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ 4 := fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have habs : |liouvilleSign n - s| ≤ 2 := by
      calc |liouvilleSign n - s| ≤ |liouvilleSign n| + |s| := abs_sub _ _
        _ ≤ 1 + 1 := by rw [abs_liouvilleSign]; linarith only [hs_le_one]
        _ = 2 := by norm_num
    have hsq4 : (liouvilleSign n - s) ^ 2 ≤ 4 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs] at h
      linarith only [h]
    dsimp only [x]
    rw [mul_pow, hb2 n hn]
    have hcancel : (n : ℝ) * ((liouvilleSign n - s) ^ 2 * (1 / (n : ℝ))) =
        (liouvilleSign n - s) ^ 2 := by field_simp [hn0.ne']
    linarith only [hcancel, hsq4]
  have hxsq : ∑ n ∈ Icc 1 M, x n ^ 2 = H - S ^ 2 / H := by
    have hpt : ∀ n ∈ Icc 1 M, x n ^ 2 = 1 / n - 2 * s * (liouvilleSign n / n) + s ^ 2 * (1 / n) :=
      fun n hn => by
        have hl := liouvilleSign_mul_self n
        dsimp only [x]
        rw [mul_pow, hb2 n hn]
        have : (liouvilleSign n - s) ^ 2 = 1 - 2 * s * liouvilleSign n + s ^ 2 := by
          linear_combination hl
        rw [this]
        ring
    rw [sum_congr rfl hpt, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
    dsimp only [s]
    field_simp [hH0.ne']
    ring
  have hS2H_le : S ^ 2 / H ≤ 2 := by
    rw [div_le_iff₀ hH0]
    linarith only [hS2, hH3]
  have hx_ge_log : L - 2 ≤ ∑ n ∈ Icc 1 M, x n ^ 2 := by
    rw [hxsq]
    linarith only [hHL, hS2H_le]
  have hxpos : 0 < ∑ n ∈ Icc 1 M, x n ^ 2 := by
    linarith only [hx_ge_log, hL3]
  refine ⟨x, hx_supp, horth, hnx_le, hx_ge_log, hxpos, ?_⟩
  set u : ℕ → ℝ := fun n => -s * (liouvilleSign n * b n)
  have hlx : (fun n => liouvilleSign n * x n) = fun n => b n + u n := by
    funext n
    have hl := liouvilleSign_mul_self n
    dsimp only [x, u]
    linear_combination b n * hl
  rw [hlx, atomicWeilForm_truncPole_add M u]
  have hPb : (L - γ - ε / 2) * H ≤ atomicWeilForm M b := by
    have := hM₁ M hMM₁
    rwa [hbsq] at this
  have hlb2 : ∑ n ∈ Icc 1 M, (liouvilleSign n * b n) ^ 2 = H := by
    rw [← hbsq]
    exact sum_congr rfl fun n _ => by
      rw [mul_pow, show liouvilleSign n ^ 2 = 1 by rw [sq, liouvilleSign_mul_self], one_mul]
  have hPu : -(s ^ 2 * ((L + C₀) * H)) ≤ atomicWeilForm M u := by
    have hu : u = fun n => (-s) * (liouvilleSign n * b n) := rfl
    rw [hu, atomicWeilForm_smul, neg_sq]
    have hbot := fixedPoint_bottom_ge (κ := -1) (by norm_num) M (fun n => liouvilleSign n * b n)
    rw [hlb2] at hbot
    have e : ((-1 : ℝ) - 1 / -1) = 0 := by norm_num
    rw [e, zero_mul, zero_add] at hbot
    have h1 : -((L + C₀) * H) ≤ atomicWeilForm M (fun n => liouvilleSign n * b n) := by
      dsimp only [L, C₀] at hbot ⊢; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg s)
    linarith only [h2]
  have hcross : |∑ n ∈ Icc 1 M,
        (RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n) * b n * u n| ≤
      |s| * ((L + γ) * 2 + B * H) := by
    have e : ∀ n ∈ Icc 1 M,
        (RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n) * b n * u n =
        -s * ((L - γ) * (liouvilleSign n / n) +
          (RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n - (L - γ)) *
            (liouvilleSign n * (1 / n))) := by
      intro n hn
      dsimp only [u]
      have hbb : b n * b n = 1 / n := by rw [← sq, hb2 n hn]
      have hr : (RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n) *
          b n * (-s * (liouvilleSign n * b n)) =
          -s * ((RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n) *
            liouvilleSign n * (b n * b n)) := by ring
      rw [hr, hbb]
      ring
    rw [sum_congr rfl e, ← mul_sum, abs_mul, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
    rw [sum_add_distrib, ← mul_sum]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      have : |L - γ| ≤ L + γ := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul this hS (abs_nonneg _) (by linarith)
    · refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [show B * H = ∑ n ∈ Icc 1 M, B * (1 / (n : ℝ)) by rw [← mul_sum]]
      refine sum_le_sum fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [abs_mul, abs_mul, abs_liouvilleSign, one_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
      exact mul_le_mul_of_nonneg_right (abs_row_sub_le hn) (by positivity)
  have hs2 : s ^ 2 ≤ 4 / H ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right hS2 (by positivity)
  have hT1 : s ^ 2 * ((L + C₀) * H) ≤ 4 + 4 * C₀ := by
    calc s ^ 2 * ((L + C₀) * H) ≤ 4 / H ^ 2 * ((L + C₀) * H) :=
          mul_le_mul_of_nonneg_right hs2 (by positivity)
      _ = 4 * L / H + 4 * C₀ / H := by field_simp [hH0.ne']
      _ ≤ 4 + 4 * C₀ := by
          have h1 : 4 * L / H ≤ 4 := by rw [div_le_iff₀ hH0]; linarith
          have h2 : 4 * C₀ / H ≤ 4 * C₀ := div_le_self (by positivity) (by linarith)
          linarith
  have hT2 : 2 * (|s| * ((L + γ) * 2 + B * H)) ≤ 8 + 8 * γ + 4 * B := by
    calc 2 * (|s| * ((L + γ) * 2 + B * H)) ≤ 2 * (2 / H * ((L + γ) * 2 + B * H)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (by positivity)) (by norm_num)
      _ = 8 * L / H + 8 * γ / H + 4 * B := by field_simp [hH0.ne']; ring
      _ ≤ 8 + 8 * γ + 4 * B := by
          have h1 : 8 * L / H ≤ 8 := by rw [div_le_iff₀ hH0]; linarith
          have h2 : 8 * γ / H ≤ 8 * γ := div_le_self (by positivity) (by linarith)
          linarith
  have hεH : K ≤ ε / 2 * H := by
    have : 2 * K / ε ≤ H := hLK.trans hHL
    rw [div_le_iff₀ hε] at this
    linarith
  have hxH : ∑ n ∈ Icc 1 M, x n ^ 2 ≤ H := by
    rw [hxsq]
    have : 0 ≤ S ^ 2 / H := div_nonneg (sq_nonneg _) hH0.le
    linarith
  have hcoef : 0 ≤ L - γ - ε := by linarith
  have hcr := (abs_le.mp hcross).1
  calc (L - γ - ε) * ∑ n ∈ Icc 1 M, x n ^ 2 ≤ (L - γ - ε) * H :=
        mul_le_mul_of_nonneg_left hxH hcoef
    _ ≤ atomicWeilForm M b + atomicWeilForm M u +
        2 * ∑ n ∈ Icc 1 M,
          (RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n) * b n * u n := by
        linarith

/-! ### 5. Breakdown of the Liouville twin above the Robin–Euler ratio -/

private theorem integral_levyMixed_atom_self (g : ℝ → ℝ) (n : ℕ) :
    (∫ y in Set.Ioi 0, levyMixed (atom g n) (atom g n) y) = levyEnergy g := by
  unfold levyEnergy levyMixed atom
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  congr 1
  rw [← integral_sub_right_eq_self (fun u => (g u - g (u + y)) ^ 2) (Real.log n)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [sq, show u - Real.log n + y = u + y - Real.log n by ring]

private theorem atomicTest_eq_of_le {M N : ℕ} (hMN : M ≤ N) {x : ℕ → ℝ}
    (hx : ∀ n, n ∉ Icc 1 M → x n = 0) (g : ℝ → ℝ) :
    atomicTest N x g = atomicTest M x g := by
  funext u
  rw [atomicTest_eq_sum_atom, atomicTest_eq_sum_atom]
  refine (sum_subset (Icc_subset_Icc_right hMN) ?_).symm
  intro n _ hnM
  rw [hx n hnM, zero_mul]

/-- Pointwise upper bound on the Liouville twin's complete Weil form on a sub-horizon harmonic
hyperplane witness with `n x_n² ≤ 4`. -/
private theorem liouville_weilQuadTw_subhorizon_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : 0 < ∫ u, φ u ^ 2) {K_lip : ℝ}
    (hLip : ∀ u v, |φ u - φ v| ≤ K_lip * |u - v|)
    {M N : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N) {w c₀ : ℝ}
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hc0 : 0 ≤ c₀) (hc1 : c₀ < 1)
    (hw_c0 : w ≤ c₀ / (M : ℝ)) (hw_sp : w < atomSpacing M)
    {x : ℕ → ℝ} (hx_supp : ∀ n, n ∉ Icc 1 M → x n = 0)
    (horth : ∑ n ∈ Icc 1 M, x n / Real.sqrt n = 0)
    (hnx : ∀ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ 4)
    {ε : ℝ} (hprime : (Real.log M - Real.eulerMascheroniConstant - ε) *
        (∑ n ∈ Icc 1 M, x n ^ 2) ≤ atomicWeilForm M (fun n => liouvilleSign n * x n)) :
    weilQuadTw (fun n => liouvilleTwin n * ArithmeticFunction.vonMangoldt n)
        (atomicTest N x (atomDilate φ w)) ≤
      (∫ u, atomDilate φ w u ^ 2) *
        ((Real.log (1 / (2 * Real.pi * (w * M))) +
            bumpRobin φ 1 / (∫ u, φ u ^ 2) + ε + Real.exp (1 / 2) / 2 * w) *
          (∑ n ∈ Icc 1 M, x n ^ 2) +
          17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * (w * M) +
          56 * (38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c₀) ^ 2)) * (w * M) ^ 2) := by
  set g := atomDilate φ w
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hG : 0 < ∫ u, g u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hφ0
  rw [atomicTest_eq_of_le hMN hx_supp g]
  have hf := contDiff_atomicTest hgc2 M x
  have hfc := hasCompactSupport_atomicTest hgsupp M x
  rw [weilQuadTw_eq_twinMarkov_add_pole liouvilleTwin hf hfc,
    integral_atomicTest_mul_exp_neg_half hgc2.continuous hgsupp M x]
  simp only [horth, zero_mul, mul_zero, add_zero]
  rw [archForm_eq_levyEnergy hf hfc,
    integral_atomicTest_sq hgc2 hgc hgsupp hw_sp x,
    (twistedPrimeSum_atomicTest liouvilleTwin_mul liouvilleTwin_sign hgc2 hgc hgsupp hw_sp x).2,
    twistedAtomicWeilForm_liouvilleTwin M x]
  -- Self-energy and off-diagonal decomposition of `levyEnergy`
  have hlevy_eq : levyEnergy (atomicTest M x g) =
      (∑ n ∈ Icc 1 M, x n ^ 2) * levyEnergy g -
        (∫ u, g u ^ 2) *
          (((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) *
              (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j) +
            ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j) := by
    rw [levyEnergy_atomicTest_eq_sum hgc2 hgsupp M x]
    have hdiag_split :
        (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
            x n * x j * ∫ y in Set.Ioi 0, levyMixed (atom g n) (atom g j) y) =
          (∑ n ∈ Icc 1 M, x n ^ 2) * levyEnergy g +
            ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
              if n = j then 0
              else x n * x j * (-atomCrossTerm g |Real.log j - Real.log n|) := by
      rw [sum_mul, ← sum_add_distrib]
      refine sum_congr rfl fun n hn => ?_
      rw [sum_eq_diag_add hn, integral_levyMixed_atom_self]
      congr 1
      · ring
      · refine sum_congr rfl fun j hj => ?_
        split_ifs with hnj
        · rfl
        · have hgap := atomSpacing_le_abs_logGap hn hj hnj
          simp only [SpacingScaleHarmonicAnalysis.logGap] at hgap
          rw [integral_levyMixed_atom_of_lt_abs_log hgsupp
            (mem_Icc.mp hn).1 (mem_Icc.mp hj).1 hw0.le (hw_sp.trans_le hgap)]
    rw [hdiag_split]
    have hoff_eq :
        (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
            if n = j then 0 else x n * x j * (-atomCrossTerm g |Real.log j - Real.log n|)) =
          -(∫ u, g u ^ 2) *
            (((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) *
                (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j) +
              ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j) := by
      rw [mul_add, ← mul_assoc, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      by_cases hnj : n = j
      · subst hnj
        simp [archimedeanCenterKernel_self, atomCrossErrorKernel_self]
      · rw [if_neg hnj, atomCrossErrorKernel, if_neg hnj]
        field_simp [hG.ne']
        ring
    rw [hoff_eq]
    ring
  rw [hlevy_eq]
  -- Bound the four pieces
  have hself := abs_levyEnergy_atomDilate_sub_le hφ hφsupp hφ0 hw0 hw1 hLip
  have hself_up : levyEnergy g ≤
      (Real.log (1 / w) + profileRobin φ + Real.exp (1 / 2) / 2 * w) * ∫ u, g u ^ 2 := by
    have := (abs_le.mp hself).2
    dsimp only [g]
    linarith
  have hX_nn : 0 ≤ ∑ n ∈ Icc 1 M, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  have hdiag_up : 2 * gammaHardyPhaseRate 0 * ((∑ n ∈ Icc 1 M, x n ^ 2) * ∫ u, g u ^ 2) +
        (∑ n ∈ Icc 1 M, x n ^ 2) * levyEnergy g -
        (∫ u, g u ^ 2) * atomicWeilForm M (fun n => liouvilleSign n * x n) ≤
      (∫ u, g u ^ 2) *
        ((Real.log (1 / (2 * Real.pi * (w * M))) + bumpRobin φ 1 / (∫ u, φ u ^ 2) + ε +
            Real.exp (1 / 2) / 2 * w) * ∑ n ∈ Icc 1 M, x n ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hself_up hX_nn
    have h2 := mul_le_mul_of_nonneg_left hprime hG.le
    have hfp := finitePart_profileRobin_eq φ
    have hlog_eq : Real.log (1 / (2 * Real.pi * (w * M))) =
        Real.log (1 / w) - Real.log M - Real.log (2 * Real.pi) := by
      rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity),
        Real.log_mul hw0.ne' hM0.ne', one_div, Real.log_inv]
      ring
    calc 2 * gammaHardyPhaseRate 0 * ((∑ n ∈ Icc 1 M, x n ^ 2) * ∫ u, g u ^ 2) +
            (∑ n ∈ Icc 1 M, x n ^ 2) * levyEnergy g -
            (∫ u, g u ^ 2) * atomicWeilForm M (fun n => liouvilleSign n * x n)
        ≤ 2 * gammaHardyPhaseRate 0 * ((∑ n ∈ Icc 1 M, x n ^ 2) * ∫ u, g u ^ 2) +
            (∑ n ∈ Icc 1 M, x n ^ 2) *
              ((Real.log (1 / w) + profileRobin φ + Real.exp (1 / 2) / 2 * w) * ∫ u, g u ^ 2) -
            (∫ u, g u ^ 2) *
              ((Real.log M - Real.eulerMascheroniConstant - ε) * ∑ n ∈ Icc 1 M, x n ^ 2) := by
          linarith only [h1, h2]
      _ = (∫ u, g u ^ 2) *
            (((2 * gammaHardyPhaseRate 0 + profileRobin φ + Real.eulerMascheroniConstant) +
                Real.log (1 / w) - Real.log M + ε + Real.exp (1 / 2) / 2 * w) *
              ∑ n ∈ Icc 1 M, x n ^ 2) := by ring
      _ = (∫ u, g u ^ 2) *
            ((Real.log (1 / (2 * Real.pi * (w * M))) + bumpRobin φ 1 / (∫ u, φ u ^ 2) + ε +
                Real.exp (1 / 2) / 2 * w) * ∑ n ∈ Icc 1 M, x n ^ 2) := by
          rw [hfp, hlog_eq]
          ring
  -- Center kernel bound
  have hcenter_ge := sum_archimedeanCenterKernel_ge M x
  have hsum_nx : ∑ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ 4 * M := by
    calc ∑ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ ∑ _n ∈ Icc 1 M, (4 : ℝ) := sum_le_sum hnx
      _ = 4 * M := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel_right, nsmul_eq_mul]; ring
  have hint_g_eq : ∫ u, g u = w * ∫ u, φ u := by
    have h := MeasureTheory.Measure.integral_comp_div φ w
    simpa only [g, atomDilate, smul_eq_mul, abs_of_pos hw0] using h
  have hratio_g : (∫ u, g u) ^ 2 / (∫ u, g u ^ 2) = w * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) := by
    rw [hint_g_eq, integral_atomDilate_sq hw0]
    field_simp [hw0.ne', hφ0.ne']
  have hcenter_up : -(((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) *
        ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j) ≤
      17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * (w * M) := by
    have hq_nn : 0 ≤ (∫ u, g u) ^ 2 / ∫ u, g u ^ 2 := div_nonneg (sq_nonneg _) hG.le
    have h1 : -(∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j) ≤
        17 * (M : ℝ) := by linarith only [hcenter_ge, hsum_nx]
    calc -(((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) *
            ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j)
        = ((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) *
            (-(∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j)) := by ring
      _ ≤ ((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) * (17 * (M : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hq_nn
      _ = 17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * (w * M) := by rw [hratio_g]; ring
  -- Cross-error bound
  set K₀ : ℝ := 38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c₀) ^ 2)
  have hK0_nn : 0 ≤ K₀ := by
    dsimp only [K₀]; positivity
  have herr_up : -(∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j) ≤
      56 * K₀ * (w * M) ^ 2 := by
    have habs : |∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j| ≤
        K₀ * w ^ 2 *
          ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
            if n = j then 0 else |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [mul_sum]
      refine sum_le_sum fun n hn => ?_
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [mul_sum]
      refine sum_le_sum fun j hj => ?_
      by_cases hnj : n = j
      · subst hnj; simp [atomCrossErrorKernel_self]
      · rw [if_neg hnj, abs_mul, abs_mul]
        have hk := abs_atomCrossErrorKernel_atomDilate_le hφ hφsupp hφ0 hw0 hc0 hc1 hw_c0 hn hj
        calc |x n| * |x j| * |atomCrossErrorKernel g n j|
            ≤ |x n| * |x j| * (K₀ * w ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) :=
              mul_le_mul_of_nonneg_left hk (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = K₀ * w ^ 2 * (|x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) := by ring
    have hsum56 := sum_cross_error_bounded_pole_le hnx
    have htot : |∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j| ≤
        56 * K₀ * (w * M) ^ 2 := by
      calc |∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j|
          ≤ K₀ * w ^ 2 *
              ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
                if n = j then 0 else |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 :=
            habs
        _ ≤ K₀ * w ^ 2 * (56 * (M : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hsum56 (by positivity)
        _ = 56 * K₀ * (w * M) ^ 2 := by ring
    have hneg := neg_abs_le (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j)
    linarith only [htot, hneg]
  have hcomb := mul_le_mul_of_nonneg_left (add_le_add hcenter_up herr_up) hG.le
  linarith only [hdiag_up, hcomb]

/-- **Breakdown of the Liouville twin above the Robin–Euler ratio**: for any `C²` profile `φ`
supported in `[0, 1]` with `robinEulerThreshold φ < 1` and any fixed overlap ratio
`c > robinEulerThreshold φ` (including `c = 1` and `c > 1`), eventually in `N` the Liouville twin's
complete Weil form is strictly negative on some atomic test of width `w_N` whenever `w_N N → c`. -/
theorem eventually_liouville_weilQuadTw_neg_of_gt_robinEuler {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : 0 < ∫ u, φ u ^ 2) (hRE1 : robinEulerThreshold φ < 1)
    {c : ℝ} (hc : robinEulerThreshold φ < c)
    {w : ℕ → ℝ} (hw_pos : ∀ᶠ N in atTop, 0 < w N)
    (hw_lim : Tendsto (fun N : ℕ => w N * (N : ℝ)) atTop (𝓝 c)) :
    ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (fun n => liouvilleTwin n * ArithmeticFunction.vonMangoldt n)
        (atomicTest N x (atomDilate φ (w N))) < 0 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨K_lip, hC_lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by norm_num)
  have hLip : ∀ u v, |φ u - φ v| ≤ (K_lip : ℝ) * |u - v| := fun u v => by
    simpa [Real.dist_eq] using hC_lip.dist_le_mul u v
  have hRE_pos : 0 < robinEulerThreshold φ := robinEulerThreshold_pos φ
  have hc_pos : 0 < c := hRE_pos.trans hc
  -- Sub-horizon target overlap ratio `c' ∈ (robinEulerThreshold φ, 1)` with `c' ≤ c`
  set c' : ℝ := min c ((robinEulerThreshold φ + 1) / 2)
  have hc'_gt : robinEulerThreshold φ < c' := lt_min hc (by linarith only [hRE1])
  have hc'_lt1 : c' < 1 := (min_le_right _ _).trans_lt (by linarith only [hRE1])
  have hc'_pos : 0 < c' := hRE_pos.trans hc'_gt
  have hc'_le_c : c' ≤ c := min_le_left _ _
  set θ : ℝ := c' / c
  have hθ_pos : 0 < θ := div_pos hc'_pos hc_pos
  have hθ_le1 : θ ≤ 1 := (div_le_one hc_pos).mpr hc'_le_c
  set c₀ : ℝ := (c' + 1) / 2
  have hc₀_gt : c' < c₀ := by dsimp only [c₀]; linarith only [hc'_lt1]
  have hc₀_lt1 : c₀ < 1 := by dsimp only [c₀]; linarith only [hc'_lt1]
  have hc₀_nn : 0 ≤ c₀ := by linarith only [hc'_pos, hc₀_gt]
  -- Logarithmic margin `μ = log (c' / c_RE(φ)) > 0`
  set μ : ℝ := Real.log (c' / robinEulerThreshold φ)
  have hμ_pos : 0 < μ := Real.log_pos ((one_lt_div hRE_pos).mpr hc'_gt)
  obtain ⟨M₀, hM₀1, hwit⟩ := exists_bounded_hyperplane_liouville_witness (ε := μ / 4) (by positivity)
  -- Sub-horizon window `M N = ⌊θ * N⌋₊`
  set M : ℕ → ℕ := fun N => ⌊θ * (N : ℝ)⌋₊
  have hM_tendsto : Tendsto M atTop atTop := by
    refine tendsto_atTop.mpr fun B => ?_
    filter_upwards [eventually_ge_atTop (⌈((B : ℝ) + 1) / θ⌉₊)] with N hN
    have h1 : ((B : ℝ) + 1) / θ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    have h2 : (B : ℝ) ≤ θ * (N : ℝ) := by
      have := (div_le_iff₀ hθ_pos).mp h1
      linarith only [this]
    exact Nat.le_floor h2
  have hMN_ratio : Tendsto (fun N : ℕ => (M N : ℝ) / (N : ℝ)) atTop (𝓝 θ) := by
    have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hlow : Tendsto (fun N : ℕ => θ - 1 / (N : ℝ)) atTop (𝓝 θ) := by
      simpa using tendsto_const_nhds.sub h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have hfl : θ * (N : ℝ) - 1 ≤ (M N : ℝ) := (Nat.sub_one_lt_floor _).le
      rw [le_div_iff₀ hN0, sub_mul, div_mul_cancel₀ _ hN0.ne']
      exact hfl
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_iff₀ hN0]
      exact Nat.floor_le (by positivity)
  have hwM_lim : Tendsto (fun N : ℕ => w N * (M N : ℝ)) atTop (𝓝 c') := by
    have hprod := hw_lim.mul hMN_ratio
    have hcθ : c * θ = c' := mul_div_cancel₀ c' hc_pos.ne'
    rw [hcθ] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp [hN0]
  have hw_zero : Tendsto w atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hp := hw_lim.mul hinv
    rw [mul_zero] at hp
    refine hp.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp [hN0]
  -- Continuity of the leading coefficient as `w N * M N → c'` and `w N → 0`
  have hcoef_lim : Tendsto (fun N : ℕ =>
      Real.log (1 / (2 * Real.pi * (w N * (M N : ℝ)))) +
        bumpRobin φ 1 / (∫ u, φ u ^ 2) + μ / 4 + Real.exp (1 / 2) / 2 * w N)
      atTop (𝓝 (-(3 * μ / 4))) := by
    have hdenom : Tendsto (fun N : ℕ => 2 * Real.pi * (w N * (M N : ℝ))) atTop
        (𝓝 (2 * Real.pi * c')) := hwM_lim.const_mul (2 * Real.pi)
    have hinv_d : Tendsto (fun N : ℕ => 1 / (2 * Real.pi * (w N * (M N : ℝ)))) atTop
        (𝓝 (1 / (2 * Real.pi * c'))) :=
      tendsto_const_nhds.div hdenom (by positivity)
    have hlog_t := (Real.continuousAt_log (by positivity)).tendsto.comp hinv_d
    have htot := ((hlog_t.add_const (bumpRobin φ 1 / ∫ u, φ u ^ 2)).add_const (μ / 4)).add
      (hw_zero.const_mul (Real.exp (1 / 2) / 2))
    have hval : Real.log (1 / (2 * Real.pi * c')) + bumpRobin φ 1 / (∫ u, φ u ^ 2) +
        μ / 4 + Real.exp (1 / 2) / 2 * 0 = -(3 * μ / 4) := by
      have hRE_eq : Real.log (robinEulerThreshold φ) =
          bumpRobin φ 1 / (∫ u, φ u ^ 2) - Real.log (2 * Real.pi) := by
        unfold robinEulerThreshold
        rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp]
      have hlog1 : Real.log (1 / (2 * Real.pi * c')) =
          -Real.log (2 * Real.pi) - Real.log c' := by
        rw [one_div, Real.log_inv, Real.log_mul (by positivity) hc'_pos.ne']
        ring
      have hμ_eq : μ = Real.log c' - Real.log (robinEulerThreshold φ) :=
        Real.log_div hc'_pos.ne' hRE_pos.ne'
      linarith only [hRE_eq, hlog1, hμ_eq]
    rwa [hval] at htot
  -- Uniform bound `C_err` on the `O(1)` archimedean center + cross-error terms
  set K₀ : ℝ := 38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c₀) ^ 2)
  set C_err : ℝ := 17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * 1 + 56 * K₀ * 1 ^ 2
  have hlogM_atTop : Tendsto (fun N : ℕ => Real.log (M N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hM_tendsto)
  filter_upwards [hw_pos,
    hw_zero.eventually (gt_mem_nhds zero_lt_one),
    hM_tendsto.eventually_ge_atTop M₀,
    (tendsto_natCast_atTop_atTop.comp hM_tendsto).eventually_gt_atTop (c₀ / (1 - c₀)),
    hwM_lim.eventually (gt_mem_nhds hc₀_gt),
    hcoef_lim.eventually (gt_mem_nhds (show -(3 * μ / 4) < -(μ / 2) by linarith only [hμ_pos])),
    hlogM_atTop.eventually_gt_atTop (2 + 2 * (C_err + 1) / μ)]
    with N hw0 hw1 hMM₀ hM_sp hwM_c₀ hcoef_neg hlogM_big
  simp only [Function.comp] at hM_sp hlogM_big
  have hM1 : 1 ≤ M N := hM₀1.trans hMM₀
  have hM0 : (0 : ℝ) < M N := by exact_mod_cast hM1
  have hMN : M N ≤ N := by
    have hle : θ * (N : ℝ) ≤ (N : ℝ) := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith only [hθ_le1, hN0]
    exact Nat.floor_le_of_le hle
  have hw_c0 : w N ≤ c₀ / (M N : ℝ) := (le_div_iff₀ hM0).mpr hwM_c₀.le
  have hw_sp : w N < atomSpacing (M N) := by
    have hsp := (atomSpacing_bounds hM1).1
    have hlt : c₀ / (M N : ℝ) < 1 / ((M N : ℝ) + 1) := by
      rw [div_lt_div_iff₀ hM0 (by positivity)]
      have hsub_pos : 0 < 1 - c₀ := sub_pos.mpr hc₀_lt1
      have h1 := (div_lt_iff₀ hsub_pos).mp hM_sp
      nlinarith only [h1]
    exact (hw_c0.trans_lt hlt).trans_le hsp
  obtain ⟨x, hx_supp, horth, hnx, hx_log, hx_pos, hprime⟩ := hwit (M N) hMM₀
  refine ⟨x, ?_⟩
  have hup := liouville_weilQuadTw_subhorizon_le hφ hφsupp hφ0 hLip hM1 hMN hw0 hw1.le hc₀_nn
    hc₀_lt1 hw_c0 hw_sp hx_supp horth hnx hprime
  have hG_pos : 0 < ∫ u, atomDilate φ (w N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hφ0
  have hwM_le1 : w N * (M N : ℝ) ≤ 1 := hwM_c₀.le.trans hc₀_lt1.le
  have hwM_nn : 0 ≤ w N * (M N : ℝ) := by positivity
  have hK0_nn : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have herr_le : 17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * (w N * (M N : ℝ)) +
      56 * K₀ * (w N * (M N : ℝ)) ^ 2 ≤ C_err := by
    dsimp only [C_err]
    have hq_nn : 0 ≤ (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 := div_nonneg (sq_nonneg _) hφ0.le
    have hsq1 : (w N * (M N : ℝ)) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hwM_nn hwM_le1 2
    nlinarith only [hwM_le1, hq_nn, hK0_nn, hsq1]
  have hlead_le : (Real.log (1 / (2 * Real.pi * (w N * (M N : ℝ)))) +
        bumpRobin φ 1 / (∫ u, φ u ^ 2) + μ / 4 + Real.exp (1 / 2) / 2 * w N) *
      (∑ n ∈ Icc 1 (M N), x n ^ 2) ≤ -(μ / 2) * (Real.log (M N : ℝ) - 2) := by
    have h1 := mul_le_mul_of_nonneg_right hcoef_neg.le hx_pos.le
    have h2 : -(μ / 2) * (∑ n ∈ Icc 1 (M N), x n ^ 2) ≤ -(μ / 2) * (Real.log (M N : ℝ) - 2) := by
      nlinarith only [hμ_pos, hx_log]
    linarith only [h1, h2]
  have hbracket_neg :
      (Real.log (1 / (2 * Real.pi * (w N * (M N : ℝ)))) +
          bumpRobin φ 1 / (∫ u, φ u ^ 2) + μ / 4 + Real.exp (1 / 2) / 2 * w N) *
        (∑ n ∈ Icc 1 (M N), x n ^ 2) +
        17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * (w N * (M N : ℝ)) +
        56 * K₀ * (w N * (M N : ℝ)) ^ 2 < 0 := by
    have hbig : C_err + 1 < (μ / 2) * (Real.log (M N : ℝ) - 2) := by
      have h := (div_lt_iff₀ hμ_pos).mp (show 2 * (C_err + 1) / μ < Real.log (M N : ℝ) - 2 by
        linarith only [hlogM_big])
      linarith only [h]
    linarith only [hlead_le, herr_le, hbig]
  have hprod_neg := mul_neg_of_pos_of_neg hG_pos hbracket_neg
  exact hup.trans_lt hprod_neg

/-! ### 6. Corollaries: spacing multiples, `c / N` widths, `transMetzlerProfile`, and thin plateaus -/

private theorem tendsto_atomSpacing_mul_natCast :
    Tendsto (fun N : ℕ => atomSpacing N * (N : ℝ)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlow : Tendsto (fun N : ℕ => 1 - 1 / ((N : ℝ) + 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hb := (atomSpacing_bounds hN).1
    have h1 : 1 - 1 / ((N : ℝ) + 1) = (N : ℝ) / ((N : ℝ) + 1) := by field_simp; ring
    rw [h1]
    calc (N : ℝ) / ((N : ℝ) + 1) = (1 / ((N : ℝ) + 1)) * (N : ℝ) := by ring
      _ ≤ atomSpacing N * (N : ℝ) := mul_le_mul_of_nonneg_right hb hN0.le
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hb := (atomSpacing_bounds hN).2
    calc atomSpacing N * (N : ℝ) ≤ (1 / (N : ℝ)) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hb hN0.le
      _ = 1 := div_mul_cancel₀ 1 hN0.ne'

/-- At exact spacing multiples `w_N = c * atomSpacing N` as well as `w_N = c / N`, the Liouville
twin fails eventual nonnegativity for `transMetzlerProfile` at **every** fixed `c ≥ 1 / 2` —
including the touching ratio `c = 1` and the trans-Metzler ratio `cZero = 1 + 10⁻¹⁸ > 1` where
`ζ`'s complete Weil matrix is eventually positive definite. -/
theorem eventually_liouville_weilQuadTw_neg_transMetzlerProfile {c : ℝ} (hc : 1 / 2 ≤ c) :
    (∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (fun n => liouvilleTwin n * ArithmeticFunction.vonMangoldt n)
        (atomicTest N x (atomDilate transMetzlerProfile (c * atomSpacing N))) < 0) ∧
    (∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (fun n => liouvilleTwin n * ArithmeticFunction.vonMangoldt n)
        (atomicTest N x (atomDilate transMetzlerProfile (c / N))) < 0) := by
  have hRE_lt : robinEulerThreshold transMetzlerProfile < c :=
    robinEulerThreshold_transMetzlerProfile_lt_half.trans_le hc
  have hRE1 : robinEulerThreshold transMetzlerProfile < 1 :=
    robinEulerThreshold_transMetzlerProfile_lt_half.trans (by norm_num)
  have hc_pos : 0 < c := by linarith only [hc]
  constructor
  · refine eventually_liouville_weilQuadTw_neg_of_gt_robinEuler
      contDiff_transMetzlerProfile (fun u hu => transMetzlerProfile_eq_zero hu)
      integral_transMetzlerProfile_sq_pos hRE1 hRE_lt ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact mul_pos hc_pos (atomSpacing_pos hN)
    · have h := tendsto_atomSpacing_mul_natCast.const_mul c
      rw [mul_one] at h
      exact h.congr fun N => by ring
  · refine eventually_liouville_weilQuadTw_neg_of_gt_robinEuler
      contDiff_transMetzlerProfile (fun u hu => transMetzlerProfile_eq_zero hu)
      integral_transMetzlerProfile_sq_pos hRE1 hRE_lt ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      exact div_pos hc_pos hN0
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      exact (div_mul_cancel₀ c hN0).symm

/-- As `η → 0⁺`, `robinEulerThreshold (plateau η) → e / (2π) ≈ 0.4326 < 1`, so for every fixed
`c > e / (2π)` there is a smooth full-support plateau profile on `[0, 1]` whose Liouville twin
complete Weil form is eventually negative at overlap ratio `c`. -/
theorem exists_plateau_liouville_weilQuadTw_neg_of_gt_exp_div_two_pi {c : ℝ}
    (hc : Real.exp 1 / (2 * Real.pi) < c) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
        weilQuadTw (fun n => liouvilleTwin n * ArithmeticFunction.vonMangoldt n)
          (atomicTest N x (atomDilate (SpacingScaleHarmonicAnalysis.plateau η) (c / N))) < 0 := by
  have he_lt_2pi : Real.exp 1 / (2 * Real.pi) < 1 := by
    rw [div_lt_one (by positivity)]
    have he1 := Real.exp_one_lt_d9
    have hpi := Real.pi_gt_three
    linarith only [he1, hpi]
  have hlim : Tendsto (fun η : ℝ => robinEulerThreshold (SpacingScaleHarmonicAnalysis.plateau η))
      (𝓝[>] 0) (𝓝 (Real.exp 1 / (2 * Real.pi))) := by
    unfold robinEulerThreshold
    exact (Real.continuous_exp.continuousAt.tendsto.comp
      tendsto_normalized_bumpRobin_plateau).div_const (2 * Real.pi)
  have hev1 : ∀ᶠ η : ℝ in 𝓝[>] 0,
      robinEulerThreshold (SpacingScaleHarmonicAnalysis.plateau η) < min c 1 :=
    hlim.eventually (gt_mem_nhds (lt_min hc he_lt_2pi))
  have hev2 : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 / 2 :=
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hev3 : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  obtain ⟨η, hRE_min, hη2, hη0⟩ := (hev1.and (hev2.and hev3)).exists
  have hRE_c : robinEulerThreshold (SpacingScaleHarmonicAnalysis.plateau η) < c :=
    hRE_min.trans_le (min_le_left _ _)
  have hRE_1 : robinEulerThreshold (SpacingScaleHarmonicAnalysis.plateau η) < 1 :=
    hRE_min.trans_le (min_le_right _ _)
  have hc_pos : 0 < c := (by positivity : 0 < Real.exp 1 / (2 * Real.pi)).trans hc
  have hsq_pos : 0 < ∫ u, SpacingScaleHarmonicAnalysis.plateau η u ^ 2 :=
    lt_of_lt_of_le (by linarith only [hη2]) (integral_plateau_sq_ge hη0 hη2.le)
  refine ⟨η, hη0, hη2, eventually_liouville_weilQuadTw_neg_of_gt_robinEuler
    ((contDiff_plateau η).of_le (by norm_num)) (fun u hu => plateau_eq_zero hη0 hu)
    hsq_pos hRE_1 hRE_c ?_ ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact div_pos hc_pos hN0
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    exact (div_mul_cancel₀ c hN0).symm

/-- **Narrow-width survival of the Liouville twin**: at every fixed fraction `0 < c ≤ fixedWidthRatio`
of `atomSpacing N`, the Liouville twin's complete Weil form is nonnegative on all atomic tests for
every `N ≥ 1`. -/
theorem liouville_weilQuadTw_nonneg_of_le_fixedWidthRatio {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc0 : 0 < c) (hc : c ≤ fixedWidthRatio)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    0 ≤ weilQuadTw (fun n => liouvilleTwin n * ArithmeticFunction.vonMangoldt n)
      (atomicTest N x (atomDilate φ (c * atomSpacing N))) := by
  have hw0 : 0 < c * atomSpacing N := mul_pos hc0 (atomSpacing_pos hN)
  have hw : c * atomSpacing N ≤ fixedWidthRatio * atomSpacing N :=
    mul_le_mul_of_nonneg_right hc (atomSpacing_pos hN).le
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  rw [weilQuadTw_eq_twinMarkov_add_pole liouvilleTwin (contDiff_atomicTest hg N x)
    (hasCompactSupport_atomicTest hgsupp N x)]
  exact twin_markov_add_pole_nonneg liouvilleTwin_mul liouvilleTwin_sign hg hgc hgsupp hN hw0 hw x

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.sum_archimedeanCenterKernel_ge
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_liouville_weilQuadTw_neg_of_gt_robinEuler
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_liouville_weilQuadTw_neg_transMetzlerProfile
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.exists_plateau_liouville_weilQuadTw_neg_of_gt_exp_div_two_pi
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.liouville_weilQuadTw_nonneg_of_le_fixedWidthRatio

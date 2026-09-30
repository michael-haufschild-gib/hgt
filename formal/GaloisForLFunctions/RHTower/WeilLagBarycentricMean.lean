import GaloisForLFunctions.RHTower.WeilLagQuadraticInterpolation
import Mathlib.Analysis.Convex.Jensen

/-!
# Signed barycentric means of the integer Weil lag

Finite probability means retain the signed lag values and control their integer
barycenter with an explicit variance loss. A fixed geometric mean schedule with
uniform variance budget is RH-complete for bounded upper normalized means.
The actual mean ceiling remains an open arithmetic producer target.
-/

open Real Set
open scoped BigOperators

namespace RHTower

noncomputable section

private def lagCorrectedExtension (N : ℕ) (r x : ℝ) : ℝ :=
  x * (1 + eulerMascheroniConstant) - Real.log (2 * π) +
    (x ^ 2 / (2 * r) - x * Real.log x) +
    trivialZeroSeriesReal x + lagArithmeticRamp N x

private theorem convexOn_lagCorrectedExtension (N : ℕ) {r : ℝ} (hr : 2 ≤ r) :
    ConvexOn ℝ (Ici r) (lagCorrectedExtension N r) := by
  refine ⟨convex_Ici r, ?_⟩
  intro a ha b hb u v hu hv huv
  simp only [mem_Ici, smul_eq_mul] at ha hb ⊢
  have hr0 : 0 < r := by linarith
  have hlog := mul_log_chord_defect_le_of_lower_bound hr0 ha hb hu hv huv
    (rfl : u * a + v * b = u * a + v * b)
  have hS := trivialZeroSeriesReal_chord (by linarith : 1 ≤ a)
    (by linarith : 1 ≤ b) hu hv huv
  have hR := lagArithmeticRamp_chord N hu hv huv (a := a) (b := b)
  have hvar : u * a ^ 2 + v * b ^ 2 - (u * a + v * b) ^ 2 =
      u * v * (b - a) ^ 2 := by
    have hv' : v = 1 - u := by linarith
    rw [hv']
    ring
  rw [← hvar] at hlog
  have hconst : u * Real.log (2 * π) + v * Real.log (2 * π) = Real.log (2 * π) := by
    calc _ = (u + v) * Real.log (2 * π) := by ring
      _ = _ := by rw [huv, one_mul]
  dsimp [lagCorrectedExtension]
  linear_combination hlog + hS + hR + hconst

private theorem lagCorrectedExtension_nat {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    (r : ℝ) :
    lagCorrectedExtension N r n = Real.sqrt n * integerLag n + (n : ℝ) ^ 2 / (2 * r) := by
  dsimp [lagCorrectedExtension]
  rw [integerLag_eq hn, lagArithmeticRamp_nat hnN]
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  simp only [one_div]
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  ring

/-- Actual finite signed lag means bound their integer barycenter with a variance cost. -/
theorem sqrt_integerLag_le_finite_mean_add_variance {s : Finset ℕ} {w : ℕ → ℝ}
    {r : ℝ} {k : ℕ} (hr : 2 ≤ r) (hw : ∀ n ∈ s, 0 ≤ w n)
    (hprob : ∑ n ∈ s, w n = 1) (hn : ∀ n ∈ s, r ≤ (n : ℝ))
    (hmean : (k : ℝ) = ∑ n ∈ s, w n * n) :
    Real.sqrt k * integerLag k ≤
      (∑ n ∈ s, w n * (Real.sqrt n * integerLag n)) +
        (∑ n ∈ s, w n * ((n : ℝ) - k) ^ 2) / (2 * r) := by
  classical
  let N := s.sup id
  have hnN : ∀ n ∈ s, n ≤ N := by
    intro n h
    exact Finset.le_sup (f := id) h
  have hkR : r ≤ (k : ℝ) := by
    rw [hmean]
    calc r = ∑ n ∈ s, w n * r := by rw [← Finset.sum_mul, hprob, one_mul]
      _ ≤ ∑ n ∈ s, w n * n := Finset.sum_le_sum fun n h =>
        mul_le_mul_of_nonneg_left (hn n h) (hw n h)
  have hk : 2 ≤ k := by exact_mod_cast hr.trans hkR
  have hkN : k ≤ N := by
    have h : (k : ℝ) ≤ N := by
      rw [hmean]
      calc _ ≤ ∑ n ∈ s, w n * (N : ℝ) := Finset.sum_le_sum fun n h =>
          mul_le_mul_of_nonneg_left (by exact_mod_cast hnN n h) (hw n h)
        _ = N := by rw [← Finset.sum_mul, hprob, one_mul]
    exact_mod_cast h
  have hJ := (convexOn_lagCorrectedExtension N hr).map_sum_le hw hprob hn
  simp only [smul_eq_mul] at hJ
  rw [← hmean, lagCorrectedExtension_nat hk hkN] at hJ
  have hnodes : (∑ n ∈ s, w n * lagCorrectedExtension N r n) =
      (∑ n ∈ s, w n * (Real.sqrt n * integerLag n)) +
        (∑ n ∈ s, w n * (n : ℝ) ^ 2) / (2 * r) := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n h
    have hn2 : 2 ≤ n := by exact_mod_cast hr.trans (hn n h)
    rw [lagCorrectedExtension_nat hn2 (hnN n h)]
    ring
  rw [hnodes] at hJ
  have hvar : (∑ n ∈ s, w n * ((n : ℝ) - k) ^ 2) =
      (∑ n ∈ s, w n * (n : ℝ) ^ 2) - (k : ℝ) ^ 2 := by
    calc _ = ∑ n ∈ s, (w n * (n : ℝ) ^ 2 - 2 * k * (w n * n) + w n * (k : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro n _
          ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul, ← hmean, hprob]
        ring
  rw [hvar]
  linear_combination hJ

private theorem sqrt_finite_mean_le {s : Finset ℕ} {w : ℕ → ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hw : ∀ n ∈ s, 0 ≤ w n) (hprob : ∑ n ∈ s, w n = 1)
    (hmean : (k : ℝ) = ∑ n ∈ s, w n * n) :
    (∑ n ∈ s, w n * Real.sqrt n) ≤ Real.sqrt k := by
  have hsq : (∑ n ∈ s, w n * (Real.sqrt n - Real.sqrt k) ^ 2) =
      2 * k - 2 * Real.sqrt k * (∑ n ∈ s, w n * Real.sqrt n) := by
    calc
      _ = ∑ n ∈ s, (w n * (n : ℝ) -
          2 * Real.sqrt k * (w n * Real.sqrt n) + w n * (k : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n _
        calc _ = w n * ((Real.sqrt n) ^ 2 -
            2 * Real.sqrt k * Real.sqrt n + (Real.sqrt k) ^ 2) := by ring
          _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (Nat.cast_nonneg k)]; ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul, ← hmean, hprob]
        ring
  have hnonneg : 0 ≤ ∑ n ∈ s, w n * (Real.sqrt n - Real.sqrt k) ^ 2 :=
    Finset.sum_nonneg fun n h => mul_nonneg (hw n h) (sq_nonneg _)
  have hkS : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by positivity)
  apply (mul_le_mul_iff_right₀ hkS).mp
  nlinarith only [hsq, hnonneg, Real.sq_sqrt (Nat.cast_nonneg k)]

/-- The literal signed scaled lag mean, normalized at its integer barycenter. -/
def normalizedBarycentricLagMean (s : Finset ℕ) (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ n ∈ s, w n * (Real.sqrt n * integerLag n)) / Real.sqrt k

/-- A geometric probability schedule with a uniform natural-scale variance budget. -/
def BarycentricLagMeanScheme (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (r : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 2 ≤ k →
    2 ≤ r k ∧ (∀ n ∈ s k, 0 ≤ w k n) ∧ (∑ n ∈ s k, w k n = 1) ∧
      (∀ n ∈ s k, r k ≤ (n : ℝ)) ∧ ((k : ℝ) = ∑ n ∈ s k, w k n * n) ∧
        (∑ n ∈ s k, w k n * ((n : ℝ) - k) ^ 2) ≤ C * r k * Real.sqrt k

/-- A bounded upper signed mean on such a schedule bounds every actual integer lag. -/
theorem integerLag_bddAbove_of_barycentricMeanScheme
    {s : ℕ → Finset ℕ} {w : ℕ → ℕ → ℝ} {r : ℕ → ℝ}
    (hS : BarycentricLagMeanScheme s w r) {M : ℝ}
    (hM : ∀ k : ℕ, 2 ≤ k → normalizedBarycentricLagMean (s k) (w k) k ≤ M) :
    ∃ B : ℝ, ∀ k : ℕ, 2 ≤ k → integerLag k ≤ B := by
  obtain ⟨C, hC, hscheme⟩ := hS
  refine ⟨M + C / 2, ?_⟩
  intro k hk
  obtain ⟨hr, hw, hprob, hn, hmean, hvar⟩ := hscheme k hk
  have hJ := sqrt_integerLag_le_finite_mean_add_variance hr hw hprob hn hmean
  have hkS : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hmeanM : (∑ n ∈ s k, w k n * (Real.sqrt n * integerLag n)) ≤ M * Real.sqrt k :=
    (div_le_iff₀ hkS).mp (hM k hk)
  have hvarC : (∑ n ∈ s k, w k n * ((n : ℝ) - k) ^ 2) / (2 * r k) ≤
      C / 2 * Real.sqrt k := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * r k)]
    nlinarith only [hvar]
  apply (mul_le_mul_iff_right₀ hkS).mp
  calc _ ≤ _ := hJ
    _ ≤ M * Real.sqrt k + C / 2 * Real.sqrt k := add_le_add hmeanM hvarC
    _ = Real.sqrt k * (M + C / 2) := by ring

/-- Every variance-controlled signed mean schedule has the exact upper-bound RH boundary. -/
theorem barycentricLagMeanScheme_characterization :
    ∀ (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (r : ℕ → ℝ),
      (BarycentricLagMeanScheme s w r ∧
        ∃ M : ℝ, ∀ k : ℕ, 2 ≤ k → normalizedBarycentricLagMean (s k) (w k) k ≤ M) ↔
          (BarycentricLagMeanScheme s w r ∧ RiemannHypothesis) := by
  intro s w r
  constructor
  · rintro ⟨hS, M, hM⟩
    exact ⟨hS, riemannHypothesis_iff_integerLag_bddAbove.mpr
      (integerLag_bddAbove_of_barycentricMeanScheme hS hM)⟩
  · rintro ⟨hS, hRH⟩
    refine ⟨hS, max poleSharpConstant 0, ?_⟩
    intro k hk
    obtain ⟨C, _, hscheme⟩ := hS
    obtain ⟨_, hw, hprob, _, hmean, _⟩ := hscheme k hk
    have hB : 0 ≤ max poleSharpConstant 0 := le_max_right _ _
    have hlag : ∀ n : ℕ, integerLag n ≤ max poleSharpConstant 0 := fun n =>
      ((le_abs_self _).trans (abs_integerLag_le_of_riemannHypothesis hRH n)).trans (le_max_left _ _)
    have hkS : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by positivity)
    apply (div_le_iff₀ hkS).mpr
    calc _ ≤ ∑ n ∈ s k, w k n * (Real.sqrt n * max poleSharpConstant 0) :=
        Finset.sum_le_sum fun n h => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hlag n) (Real.sqrt_nonneg _)) (hw n h)
      _ = max poleSharpConstant 0 * (∑ n ∈ s k, w k n * Real.sqrt n) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ max poleSharpConstant 0 * Real.sqrt k :=
        mul_le_mul_of_nonneg_left (sqrt_finite_mean_le hk hw hprob hmean) hB

end
end RHTower

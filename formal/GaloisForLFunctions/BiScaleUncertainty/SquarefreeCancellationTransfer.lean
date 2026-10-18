import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic
import GaloisForLFunctions.RHTower.Sieve.SquarefreeCount
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate
import GaloisForLFunctions.RHTower.DeningerAbelSummation

/-!
# Transfer of actual Möbius cancellation to squarefree discrepancy

Finite Abel summation retains both signed tails in the squarefree divisor
identity. A linear Mertens bound beyond a cutoff gives a quantitative error
bound with a freely chosen cutoff; inverse-log cancellation can then improve
the square-root error without changing the arithmetic source.
-/

noncomputable section
open Finset Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace RHTower.SquarefreeDiscrepancy

private theorem sum_Ioc_eq_prefix_sub (f : ℕ → ℝ) {D R : ℕ} (hDR : D ≤ R) :
    (∑ n ∈ Ioc D R, f n) =
      (∑ n ∈ range (R + 1), f n) - ∑ n ∈ range (D + 1), f n := by
  have he : Ioc D R = Ico (D + 1) (R + 1) := by ext n; simp
  rw [he, sum_Ico_eq_sub _ (by omega : D + 1 ≤ R + 1)]

private theorem mobius_abel_tail (w : ℕ → ℝ) {D R : ℕ} (hDR : D ≤ R) :
    (∑ n ∈ Ioc D R, (μ n : ℝ) * w n) =
      Sieve.mertensM R * w R - Sieve.mertensM D * w D +
        ∑ n ∈ Ico D R, Sieve.mertensM n * (w n - w (n + 1)) := by
  rw [sum_Ioc_eq_prefix_sub _ hDR,
    deningerAbelSummation _ _ R, deningerAbelSummation _ _ D,
    sum_Ico_eq_sub _ hDR]
  simp only [deningerPartialSum, Sieve.mertensM]
  ring

private theorem weighted_telescoping (w : ℕ → ℝ) {D R : ℕ} (hDR : D ≤ R) :
    (R : ℝ) * w R + (D : ℝ) * w D +
        (∑ n ∈ Ico D R, (n : ℝ) * (w n - w (n + 1))) =
      2 * D * w D + ∑ n ∈ Ioc D R, w n := by
  induction R, hDR using Nat.le_induction with
  | base => simp; ring
  | succ R hDR ih =>
      have he : Ioc D (R + 1) = insert (R + 1) (Ioc D R) := by
        ext n
        simp only [mem_Ioc, mem_insert]
        omega
      rw [sum_Ico_succ_top hDR, he, sum_insert (by simp)]
      push_cast
      nlinarith [ih]

/-- Signed Möbius tails against a decreasing nonnegative weight. Both Abel
boundary terms are retained. -/
theorem abs_mobius_weighted_tail_le {D R : ℕ} (hDR : D ≤ R)
    {δ : ℝ}
    (hM : ∀ n : ℕ, D ≤ n → |Sieve.mertensM n| ≤ δ * n)
    (w : ℕ → ℝ) (hw0 : ∀ n, D ≤ n → 0 ≤ w n)
    (hw : ∀ n, D ≤ n → w (n + 1) ≤ w n) :
    |∑ n ∈ Ioc D R, (μ n : ℝ) * w n| ≤
      δ * (2 * D * w D + ∑ n ∈ Ioc D R, w n) := by
  have hboundary (n : ℕ) (hn : D ≤ n) :
      |Sieve.mertensM n * w n| ≤ δ * n * w n := by
    rw [abs_mul, abs_of_nonneg (hw0 n hn)]
    exact mul_le_mul_of_nonneg_right (hM n hn) (hw0 n hn)
  have hsum : |∑ n ∈ Ico D R, Sieve.mertensM n * (w n - w (n + 1))| ≤
      δ * ∑ n ∈ Ico D R, (n : ℝ) * (w n - w (n + 1)) := by
    calc
      _ ≤ ∑ n ∈ Ico D R, |Sieve.mertensM n * (w n - w (n + 1))| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Ico D R, δ * ((n : ℝ) * (w n - w (n + 1))) := by
        apply sum_le_sum
        intro n hn
        have hdiff := sub_nonneg.mpr (hw n (mem_Ico.mp hn).1)
        rw [abs_mul, abs_of_nonneg hdiff]
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_right (hM n (mem_Ico.mp hn).1) hdiff
      _ = _ := (mul_sum _ _ _).symm
  rw [mobius_abel_tail w hDR]
  calc
    _ ≤ |Sieve.mertensM R * w R - Sieve.mertensM D * w D| +
        |∑ n ∈ Ico D R, Sieve.mertensM n * (w n - w (n + 1))| := abs_add_le _ _
    _ ≤ (|Sieve.mertensM R * w R| + |Sieve.mertensM D * w D|) +
        |∑ n ∈ Ico D R, Sieve.mertensM n * (w n - w (n + 1))| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (δ * R * w R + δ * D * w D) +
        δ * ∑ n ∈ Ico D R, (n : ℝ) * (w n - w (n + 1)) :=
      add_le_add (add_le_add (hboundary R hDR) (hboundary D le_rfl)) hsum
    _ = δ * ((R : ℝ) * w R + (D : ℝ) * w D +
        ∑ n ∈ Ico D R, (n : ℝ) * (w n - w (n + 1))) := by ring
    _ = _ := by rw [weighted_telescoping w hDR]

/-- The complete signed reciprocal-square tail inherits the Mertens saving. -/
theorem abs_mobius_density_tail_le {D : ℕ} (hD : 1 ≤ D)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ n : ℕ, D ≤ n → |Sieve.mertensM n| ≤ δ * n) :
    |(∑ n ∈ Icc 1 D, (μ n : ℝ) / (n : ℝ)^2) - Sieve.squarefreeDensity| ≤
      3 * δ / D := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hfinite (R : ℕ) (hDR : D ≤ R) :
      |∑ n ∈ Ioc D R, (μ n : ℝ) / (n : ℝ)^2| ≤ 3 * δ / D := by
    have hb := abs_mobius_weighted_tail_le hDR hM
      (fun n => 1 / (n : ℝ)^2) (fun n hn => by positivity) (by
        intro n hn
        apply div_le_div_of_nonneg_left (by norm_num) (by
          have : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hD hn)
          positivity)
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast
        nlinarith)
    have htail : ∑ n ∈ Ioc D R, 1 / (n : ℝ)^2 ≤ 1 / (D : ℝ) := by
      have he : Ioc D R = Icc (D + 1) R := by
        ext n; simp only [mem_Ioc, mem_Icc]; omega
      rw [he]
      exact sum_inv_sq_tail_le hD R
    simp only [mul_one_div] at hb
    calc
      _ ≤ δ * (2 * D * (1 / (D : ℝ)^2) + ∑ n ∈ Ioc D R, 1 / (n : ℝ)^2) := by
        simpa only [mul_one_div] using hb
      _ ≤ δ * (2 * D * (1 / (D : ℝ)^2) + 1 / (D : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) hδ
      _ = _ := by field_simp; ring
  have hlim := Sieve.summable_moebius_div_sq.hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  have hprefix : (∑ n ∈ range (D + 1), (μ n : ℝ) / (n : ℝ)^2) =
      ∑ n ∈ Icc 1 D, (μ n : ℝ) / (n : ℝ)^2 := by
    have he : range (D + 1) = insert 0 (Icc 1 D) := by
      ext n; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [he, sum_insert (by simp)]
    simp
  have hbound : ∀ᶠ R : ℕ in atTop,
      |(∑ n ∈ range (R + 1), (μ n : ℝ) / (n : ℝ)^2) -
        ∑ n ∈ Icc 1 D, (μ n : ℝ) / (n : ℝ)^2| ≤ 3 * δ / D := by
    filter_upwards [eventually_ge_atTop D] with R hR
    rw [← hprefix, ← sum_Ioc_eq_prefix_sub _ hR]
    exact hfinite R hR
  have ht := le_of_tendsto ((hlim.sub_const
    (∑ n ∈ Icc 1 D, (μ n : ℝ) / (n : ℝ)^2)).abs) hbound
  simpa only [Sieve.squarefreeDensity, abs_sub_comm] using ht

private theorem prefix_eq_Icc (f : ℕ → ℝ) (hf : f 0 = 0) (R : ℕ) :
    (∑ n ∈ range (R + 1), f n) = ∑ n ∈ Icc 1 R, f n := by
  have he : range (R + 1) = insert 0 (Icc 1 R) := by
    ext n; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [he, sum_insert (by simp), hf, zero_add]

/-- The exact squarefree source benefits from cancellation in both tails.
The freely chosen truncation need not be the square root of the cutoff. -/
theorem abs_squarefree_count_sub_le_of_mertens {N D : ℕ} (hD : 1 ≤ D)
    (hDN : D ≤ N) {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ n : ℕ, D ≤ n → |Sieve.mertensM n| ≤ δ * n) :
    |(∑ n ∈ Icc 1 N, (μ n : ℝ)^2) - Sieve.squarefreeDensity * N| ≤
      D + 6 * δ * N / D := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  let w : ℕ → ℝ := fun n => ((N / (n * n) : ℕ) : ℝ)
  have hwle (n : ℕ) : w n ≤ (N : ℝ) / (n : ℝ)^2 := by
    simpa [w, pow_two] using (Nat.cast_div_le (m := N) (n := n * n) (α := ℝ))
  have hmono (n : ℕ) (hn : D ≤ n) : w (n + 1) ≤ w n := by
    dsimp [w]
    exact_mod_cast Nat.div_le_div_left (by nlinarith : n * n ≤ (n + 1) * (n + 1))
      (by nlinarith [hD, hn] : 0 < n * n)
  have htail : |∑ n ∈ Ioc D N, (μ n : ℝ) * w n| ≤ 3 * δ * N / D := by
    have hb := abs_mobius_weighted_tail_le hDN hM w
      (fun n _ => Nat.cast_nonneg _) hmono
    have hsum : ∑ n ∈ Ioc D N, w n ≤ (N : ℝ) / D := by
      calc
        _ ≤ ∑ n ∈ Ioc D N, (N : ℝ) / (n : ℝ)^2 :=
          sum_le_sum fun n _ => hwle n
        _ = (N : ℝ) * ∑ n ∈ Ioc D N, 1 / (n : ℝ)^2 := by
          rw [mul_sum]; apply sum_congr rfl; intro n hn; ring
        _ ≤ (N : ℝ) * (1 / (D : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
          have he : Ioc D N = Icc (D + 1) N := by
            ext n; simp only [mem_Ioc, mem_Icc]; omega
          rw [he]
          exact sum_inv_sq_tail_le hD N
        _ = _ := by ring
    calc
      _ ≤ δ * (2 * D * w D + ∑ n ∈ Ioc D N, w n) := hb
      _ ≤ δ * (2 * D * ((N : ℝ) / (D : ℝ)^2) + (N : ℝ) / D) := by
        apply mul_le_mul_of_nonneg_left _ hδ
        exact add_le_add (mul_le_mul_of_nonneg_left (hwle D) (by positivity)) hsum
      _ = _ := by field_simp; ring
  have hhead : |∑ n ∈ Icc 1 D, (μ n : ℝ) * (w n - (N : ℝ) / (n : ℝ)^2)| ≤ D := by
    calc
      _ ≤ ∑ n ∈ Icc 1 D, |(μ n : ℝ) * (w n - (N : ℝ) / (n : ℝ)^2)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Icc 1 D, (1 : ℝ) := by
        apply sum_le_sum
        intro n hn
        have hn1 := (mem_Icc.mp hn).1
        have hnn : 1 ≤ n * n := by nlinarith
        have hfrac := natDiv_frac_mem (N := N) hnn
        have hfrac' : |w n - (N : ℝ) / (n : ℝ)^2| ≤ 1 := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hwle n))]
          simpa [w, pow_two] using hfrac.2.le
        have hmu : |(μ n : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul hmu hfrac' (abs_nonneg _) zero_le_one
      _ = _ := by simp
  have hdensity : |(N : ℝ) * ((∑ n ∈ Icc 1 D, (μ n : ℝ) / (n : ℝ)^2) -
      Sieve.squarefreeDensity)| ≤ 3 * δ * N / D := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    calc
      _ ≤ (N : ℝ) * (3 * δ / D) :=
        mul_le_mul_of_nonneg_left (abs_mobius_density_tail_le hD hδ hM)
          (Nat.cast_nonneg N)
      _ = _ := by ring
  have hcount : (∑ n ∈ Icc 1 N, (μ n : ℝ)^2) =
      ∑ n ∈ Icc 1 N, (μ n : ℝ) * w n := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (sum_moebius_sq_Icc N)
    push_cast at h
    exact h
  have hsplit : (∑ n ∈ Icc 1 N, (μ n : ℝ)^2) - Sieve.squarefreeDensity * N =
      (∑ n ∈ Icc 1 D, (μ n : ℝ) * (w n - (N : ℝ) / (n : ℝ)^2)) +
      (∑ n ∈ Ioc D N, (μ n : ℝ) * w n) +
      (N : ℝ) * ((∑ n ∈ Icc 1 D, (μ n : ℝ) / (n : ℝ)^2) - Sieve.squarefreeDensity) := by
    rw [hcount, sum_Ioc_eq_prefix_sub _ hDN,
      prefix_eq_Icc _ (by simp) N, prefix_eq_Icc _ (by simp) D,
      mul_sub, mul_sum]
    have he : (∑ n ∈ Icc 1 D, (μ n : ℝ) * (w n - (N : ℝ) / (n : ℝ)^2)) =
        (∑ n ∈ Icc 1 D, (μ n : ℝ) * w n) -
        ∑ n ∈ Icc 1 D, (N : ℝ) * ((μ n : ℝ) / (n : ℝ)^2) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro n hn
      ring
    rw [he]
    ring
  rw [hsplit]
  have htri := abs_add_le
    ((∑ n ∈ Icc 1 D, (μ n : ℝ) * (w n - (N : ℝ) / (n : ℝ)^2)) +
      (∑ n ∈ Ioc D N, (μ n : ℝ) * w n))
    ((N : ℝ) * ((∑ n ∈ Icc 1 D, (μ n : ℝ) / (n : ℝ)^2) - Sieve.squarefreeDensity))
  have htri' := abs_add_le
    (∑ n ∈ Icc 1 D, (μ n : ℝ) * (w n - (N : ℝ) / (n : ℝ)^2))
    (∑ n ∈ Ioc D N, (μ n : ℝ) * w n)
  calc
    _ ≤ _ := htri
    _ ≤ _ := add_le_add htri' le_rfl
    _ ≤ ((D : ℝ) + 3 * δ * N / D) + 3 * δ * N / D :=
      add_le_add (add_le_add hhead htail) hdensity
    _ = _ := by ring

end RHTower.SquarefreeDiscrepancy

import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmFreeCriticalConductorResiduals
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheLinearMomentRemovesTheOverlapLogarithm
import GaloisForLFunctions.HTGeometry.FiniteHorizonLayerCake

/-!
# The logarithmic row is an integral of horizons

Keeping atom width fixed makes every smaller horizon a truncation of the
same arithmetic kernel. The logarithmic distance to the larger index is
an exact weighted sum of those truncated forms.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedIntersectionTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  CompletedArithmeticForms SpacingScaleHarmonicAnalysis SignedArithmeticHodgeTheory

/-- A near-pair coefficient with physical atom width fixed independently of the horizon. -/
def fixedWidthNearPair (φ : ℝ → ℝ) (w : ℝ) (m l n j : ℕ) : ℝ :=
  if j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * w then
    ramanujanPoleProfile m n * ramanujanPoleProfile l j *
      (shellAutocorr φ (|Real.log j - Real.log n| / w) / ∫ u, φ u ^ 2)
  else 0

/-- The raw, logarithmically unnormalized near-Gram form at fixed physical width. -/
def fixedWidthNearGram (φ : ℝ → ℝ) (w : ℝ) (N m l : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, fixedWidthNearPair φ w m l n j

/-- Removing horizon normalization leaves precisely the fixed-width kernel. -/
theorem log_mul_nearGramModeBilin_eq_fixedWidth (φ : ℝ → ℝ) (c : ℝ)
    {N : ℕ} (hL : 0 < Real.log N) (m l : ℕ) :
    Real.log N * nearGramModeBilin φ c N m l = fixedWidthNearGram φ (c / N) N m l := by
  have hcancel : Real.log N * ((Real.sqrt (Real.log N))⁻¹ *
      (Real.sqrt (Real.log N))⁻¹) = 1 := by
    rw [← mul_inv, ← sq, Real.sq_sqrt hL.le, mul_inv_cancel₀ hL.ne']
  unfold nearGramModeBilin fixedWidthNearGram
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [primeHorizonExtension_normalizedRamanujan hn, nearGram, nearRowIndices, sum_filter,
    mul_sum, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [primeHorizonExtension_normalizedRamanujan hj]
  unfold fixedWidthNearPair
  rw [show 2 * c / (N : ℝ) = 2 * (c / N) by ring]
  split_ifs
  · calc
      _ = (Real.log N * ((Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹)) *
          (ramanujanPoleProfile m n * ramanujanPoleProfile l j *
            (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2)) := by ring
      _ = _ := by rw [hcancel, one_mul]
  · ring

/-- Changing the horizon changes overlap by the same ratio and preserves physical width. -/
theorem fixedWidthNearGram_eq_subhorizon (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    {T : ℕ} (hT : 2 ≤ T) (m l : ℕ) :
    fixedWidthNearGram φ (c / N) T m l =
      Real.log T * nearGramModeBilin φ (c * T / N) T m l := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  rw [log_mul_nearGramModeBilin_eq_fixedWidth φ _
    (Real.log_pos (by exact_mod_cast (show 1 < T by omega)))]
  congr 1
  symm
  calc
    c * (T : ℝ) / N / T = (c / N) * (T / T) := by ring
    _ = c / N := by rw [div_self hT0.ne', mul_one]

/-- Exact logarithmic layer identity for the actual arithmetic near-pair kernel. -/
theorem fixedWidthNearPair_log_max_eq (φ : ℝ → ℝ) (w : ℝ) (N m l : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      fixedWidthNearPair φ w m l n j * (Real.log N - Real.log (max n j))) =
      ∑ T ∈ Ico 1 N, fixedWidthNearGram φ w T m l *
        (Real.log ((T : ℝ) + 1) - Real.log T) :=
  HTGeometry.sum_pair_log_max_eq_horizon_layers (fixedWidthNearPair φ w m l) N

/-- Replacing the receiving index by the later index costs only the atom width. -/
theorem abs_fixedWidthNearPair_log_row_sub_max_le (φ : ℝ → ℝ)
    {w : ℝ} (hw : 0 ≤ w) (N m l : ℕ) :
    |(∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        fixedWidthNearPair φ w m l n j * (Real.log N - Real.log j)) -
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        fixedWidthNearPair φ w m l n j * (Real.log N - Real.log (max n j)))| ≤
      2 * w * ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, |fixedWidthNearPair φ w m l n j| := by
  rw [← sum_sub_distrib, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  rw [← sum_sub_distrib, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro j hj
  have hdiff : fixedWidthNearPair φ w m l n j * (Real.log N - Real.log j) -
      fixedWidthNearPair φ w m l n j * (Real.log N - Real.log (max n j)) =
      fixedWidthNearPair φ w m l n j * (Real.log (max n j) - Real.log j) := by ring
  rw [hdiff, abs_mul]
  by_cases hnear : j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * w
  · have hgap : |Real.log (max n j) - Real.log j| ≤ 2 * w := by
      by_cases hnj : n ≤ j
      · rw [max_eq_right (show (n : ℝ) ≤ j by exact_mod_cast hnj), sub_self, abs_zero]
        positivity
      · rw [max_eq_left (show (j : ℝ) ≤ n by exact_mod_cast (le_of_not_ge hnj)), abs_sub_comm]
        exact hnear.2
    simpa only [mul_comm (2 * w)] using
      mul_le_mul_of_nonneg_left hgap (abs_nonneg (fixedWidthNearPair φ w m l n j))
  · simp only [fixedWidthNearPair, if_neg hnear, abs_zero, zero_mul, mul_zero, le_refl]

private theorem near_pair_abs_product_le_squares (c : ℝ) (N : ℕ) (f g : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, |f n * g j|) ≤
      ∑ n ∈ Icc 1 N, ((nearRowIndices c N n).card : ℝ) * (f n ^ 2 + g n ^ 2) := by
  have hswap : (∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, g j ^ 2) =
      ∑ n ∈ Icc 1 N, ∑ _j ∈ nearRowIndices c N n, g n ^ 2 := by
    simp only [nearRowIndices, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun n _ => sum_congr rfl fun j _ => ?_
    simp only [ne_comm, abs_sub_comm]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, (f n ^ 2 + g j ^ 2) := by
      refine sum_le_sum fun n _ => sum_le_sum fun j _ => ?_
      rw [abs_mul]
      nlinarith only [sq_nonneg (|f n| - |g j|), sq_abs (f n), sq_abs (g j),
        mul_nonneg (abs_nonneg (f n)) (abs_nonneg (g j))]
    _ = _ := by
      simp only [sum_add_distrib]
      rw [hswap]
      simp only [sum_const, nsmul_eq_mul]
      rw [← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring

private theorem poleProfile_sq_le_totient_div {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ramanujanPoleProfile m n ^ 2 ≤ (m.totient : ℝ) / n := by
  have h := abs_normalizedRamanujanMode_le_sqrt_totient hm n
  have hsq := mul_le_mul h h (abs_nonneg _) (Real.sqrt_nonneg _)
  rw [← sq, sq_abs, ← sq, Real.sq_sqrt (Nat.cast_nonneg m.totient)] at hsq
  rw [ramanujanPoleProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right hsq (Nat.cast_nonneg n)

/-- A fixed conductor pair has raw near-pair mass linear in overlap, on every horizon. -/
theorem sum_abs_fixedWidthNearPair_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N m l : ℕ} (hN : 1 ≤ N)
    (hm : 0 < m) (hl : 0 < l) (hw : c / N ≤ 1) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, |fixedWidthNearPair φ (c / N) m l n j|) ≤
      2 * linearNearRowRadius c * ((m.totient : ℝ) + l.totient) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hrad : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have hsum : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      |fixedWidthNearPair φ (c / N) m l n j|) =
      ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n,
        |ramanujanPoleProfile m n * ramanujanPoleProfile l j| *
          |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2| := by
    apply sum_congr rfl
    intro n _
    rw [nearRowIndices, sum_filter]
    apply sum_congr rfl
    intro j _
    unfold fixedWidthNearPair
    rw [show 2 * c / (N : ℝ) = 2 * (c / N) by ring]
    split_ifs <;> simp only [abs_mul, abs_zero]
  rw [hsum]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n,
        |ramanujanPoleProfile m n * ramanujanPoleProfile l j| := by
      refine sum_le_sum fun n _ => sum_le_sum fun j _ => ?_
      apply mul_le_of_le_one_right (abs_nonneg _)
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      exact abs_shellAutocorr_le hφ hsupp _
    _ ≤ ∑ n ∈ Icc 1 N, ((nearRowIndices c N n).card : ℝ) *
        (ramanujanPoleProfile m n ^ 2 + ramanujanPoleProfile l n ^ 2) :=
      near_pair_abs_product_le_squares c N _ _
    _ ≤ ∑ _n ∈ Icc 1 N,
        2 * linearNearRowRadius c / N * ((m.totient : ℝ) + l.totient) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hs : ramanujanPoleProfile m n ^ 2 + ramanujanPoleProfile l n ^ 2 ≤
          ((m.totient : ℝ) + l.totient) / n := by
        rw [add_div]
        exact add_le_add (poleProfile_sq_le_totient_div hm n) (poleProfile_sq_le_totient_div hl n)
      calc
        _ ≤ (2 * linearNearRowRadius c * ((n : ℝ) / N)) *
            (((m.totient : ℝ) + l.totient) / n) :=
          mul_le_mul (card_nearRowIndices_le_relative_radius hc hn hw) hs
            (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
        _ = _ := by field_simp [hn0.ne', hN0.ne']
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      field_simp [hN0.ne']

/-- The entire truncated near-Gram obeys the same linear mass bound. -/
theorem abs_fixedWidthNearGram_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N m l : ℕ} (hN : 1 ≤ N)
    (hm : 0 < m) (hl : 0 < l) (hw : c / N ≤ 1) :
    |fixedWidthNearGram φ (c / N) N m l| ≤
      2 * linearNearRowRadius c * ((m.totient : ℝ) + l.totient) := by
  apply (abs_sum_le_sum_abs _ _).trans
  exact (sum_le_sum fun n _ => abs_sum_le_sum_abs _ _).trans
    (sum_abs_fixedWidthNearPair_le hφ hsupp hM hc hN hm hl hw)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.fixedWidthNearPair_log_max_eq
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_abs_fixedWidthNearPair_le

import GaloisForLFunctions.RHTower.WeilWorkDeficitRepairCost
import GaloisForLFunctions.RHTower.WeilWorkExposingRayTailAsymptotic
import GaloisForLFunctions.RHTower.WeilFullConeNearNullPositiveDefinite
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Full arithmetic repair budgets of short coherent Riemann packets

The existing sharp theta envelope gives every exponential rate below π for
shifts in [-log 2, 0]. The bound includes the actual isolated-atom repair cost
and is uniform in physical truncation. No cancellation construction is assumed.
Paper proof: WP06 PROOF.md, C3t+.
-/

open MeasureTheory Filter Topology Set Real Zeta23
noncomputable section
namespace RHTower.WeilWorkDeficitBudget
open WeilExcess WeilOneSided WeilWorkPBAP

/-- A finite real coherent packet on the prescribed short interval. -/
structure ShortPacket where
  size : ℕ
  coeff : Fin size → ℝ
  shift : Fin size → Icc (-Real.log 2) 0

/-- Squared coefficient variation, the cost used in C3+. -/
def ShortPacket.cost (P : ShortPacket) : ℝ := (∑ i, |P.coeff i|) ^ 2

private theorem cost_nonneg (P : ShortPacket) : 0 ≤ P.cost := sq_nonneg _

/-- The exact finite quadratic autocorrelation expansion. -/
def ShortPacket.correlation (P : ShortPacket) (K : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ i, ∑ j, P.coeff i * P.coeff j * K (y + P.shift j - P.shift i)

/-- The existing compact test with this packet's coefficients and shifts. -/
def ShortPacket.test (P : ShortPacket) (L : ℝ) : WeilTestFn :=
  ⟨shiftComb Finset.univ P.coeff (fun i => P.shift i) L,
    contDiff_shiftComb _ _ _ _, hasCompactSupport_shiftComb _ _ _ _⟩

/-- Natural indexing of all logarithmic atoms, beginning at 2. -/
def logIndex (n : ℕ) : LogIndex := ⟨n + 2, by omega⟩

/-- Limiting logarithmic defect of the untruncated coherent packet. -/
def ShortPacket.coefficient (P : ShortPacket) (n : ℕ) : ℝ :=
  (P.correlation riemannAutocorr (log (n + 2)) +
    P.correlation riemannAutocorr (-log (n + 2))) / sqrt (n + 2)

/-- Both the von Mangoldt contribution and the actual positive repair cost. -/
def weight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt (n + 2) + atomCost (logIndex n)

private theorem weight_nonneg (n : ℕ) : 0 ≤ weight n :=
  add_nonneg ArithmeticFunction.vonMangoldt_nonneg (atomCost_nonneg _)

/-- The packet uses precisely the existing logarithmic defect. -/
theorem logValue_test (P : ShortPacket) (L : ℝ) (n : ℕ) :
    logValue (P.test L).1 (n + 2) =
      (P.correlation (truncatedRiemannAutocorr L) (log (n + 2)) +
        P.correlation (truncatedRiemannAutocorr L) (-log (n + 2))) / sqrt (n + 2) := by
  simp only [logValue, ShortPacket.test, weilTest_shiftComb, Complex.add_re,
    Complex.ofReal_re, ShortPacket.correlation, Nat.cast_add, Nat.cast_ofNat]

private theorem correlation_bound (P : ShortPacket) (K : ℝ → ℝ) (y B : ℝ)
    (hK : ∀ i j, |K (y + P.shift j - P.shift i)| ≤ B) :
    |P.correlation K y| ≤ P.cost * B := by
  classical
  calc
    _ ≤ ∑ i, ∑ j, |P.coeff i| * |P.coeff j| * |K (y + P.shift j - P.shift i)| := by
      unfold ShortPacket.correlation
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun j => P.coeff i * P.coeff j * K (y + P.shift j - P.shift i)) Finset.univ
    _ ≤ ∑ i, ∑ j, |P.coeff i| * |P.coeff j| * B := by
      gcongr with i _ j _
      exact hK i j
    _ = P.cost * B := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, ShortPacket.cost, sq]

private theorem exp_shift_ge (P : ShortPacket) (i j : Fin P.size) (n : ℕ)
    {y : ℝ} (hy : |y| = log (n + 2)) :
    (n + 2 : ℝ) / 2 ≤ exp |y + P.shift j - P.shift i| := by
  have hi := (P.shift i).property
  have hj := (P.shift j).property
  have hd : |(P.shift j : ℝ) - P.shift i| ≤ log 2 := by
    rw [abs_le]; constructor <;> linarith
  have htri : |y| ≤ |y + P.shift j - P.shift i| + |(P.shift j : ℝ) - P.shift i| := by
    convert abs_sub (y + (P.shift j : ℝ) - P.shift i) ((P.shift j : ℝ) - P.shift i) using 1
    congr 1; ring
  have he := exp_le_exp.mpr (show log (n + 2) - log 2 ≤ |y + P.shift j - P.shift i| by
    rw [hy] at htri; linarith)
  rwa [exp_sub, exp_log (by positivity), exp_log (by norm_num : (0 : ℝ) < 2)] at he

private theorem correlation_exponential (P : ShortPacket) (K : ℝ → ℝ)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hK : ∀ y, |K y| ≤ C * exp (-(2 * c * exp |y|))) (n : ℕ)
    {y : ℝ} (hy : |y| = log (n + 2)) :
    |P.correlation K y| ≤ P.cost * (C * exp (-(c * (n + 2)))) := by
  apply correlation_bound
  intro i j
  refine (hK _).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply exp_le_exp.mpr
  have := exp_shift_ge P i j n hy
  nlinarith

private theorem coefficient_exponential (P : ShortPacket) (K : ℝ → ℝ)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hK : ∀ y, |K y| ≤ C * exp (-(2 * c * exp |y|))) (n : ℕ) :
    |(P.correlation K (log (n + 2)) + P.correlation K (-log (n + 2))) /
      sqrt (n + 2)| ≤ 2 * C * P.cost * exp (-(c * (n + 2))) / sqrt (n + 2) := by
  have hl : 0 ≤ log (n + 2 : ℝ) := Real.log_nonneg (by positivity)
  rw [abs_div, abs_of_nonneg (sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
  have h1 := correlation_exponential P K hc hC hK n (abs_of_nonneg hl)
  have h2 := correlation_exponential P K hc hC hK n (by rw [abs_neg, abs_of_nonneg hl])
  have h := abs_add_le (P.correlation K (log (n + 2))) (P.correlation K (-log (n + 2)))
  linarith

private theorem weight_bound : ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
    weight n ≤ D * (n + 3) * sqrt (n + 2) := by
  obtain ⟨C, hC, hbound⟩ := atomCost_le_polynomial
  refine ⟨C + 1, by positivity, fun n => ?_⟩
  have hA := hbound (logIndex n)
  have hL := ArithmeticFunction.vonMangoldt_le_log (n + 2)
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n + 2 by positivity)
  have hs : 1 ≤ sqrt (n + 2 : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; positivity)
  have hm : (n + 2 : ℝ) ≤ (n + 3) * sqrt (n + 2) := by nlinarith
  dsimp [logIndex] at hA
  simp only [Nat.cast_add, Nat.cast_ofNat] at hA hL
  dsimp [weight]
  nlinarith

/-- A uniform full repair-weight bound for every packet and every cutoff. -/
theorem weighted_coefficient_polynomial_exponential {c : ℝ} (hc : 0 < c) (hcπ : c < π) :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : ShortPacket) (n : ℕ),
      weight n * |P.coefficient n| ≤ B * P.cost * (n + 3) * exp (-(c * (n + 2))) ∧
      ∀ L : ℝ, weight n * |logValue (P.test L).1 (n + 2)| ≤
        B * P.cost * (n + 3) * exp (-(c * (n + 2))) := by
  obtain ⟨C, hC, hK⟩ := ExposingRayTail.autocorr_upper hc hcπ
  obtain ⟨D, hD, hD_bound⟩ := weight_bound
  have hfull : ∀ y, |riemannAutocorr y| ≤ C * exp (-(2 * c * exp |y|)) := by
    intro y
    rw [abs_of_nonneg (riemannAutocorr_nonneg y)]
    exact hK y
  have htrunc : ∀ L y, |truncatedRiemannAutocorr L y| ≤ C * exp (-(2*c*exp |y|)) := by
    intro L y
    have hpos : 0 ≤ truncatedRiemannAutocorr L y := by
      exact integral_nonneg fun t => mul_nonneg (truncatedRiemannKernelReal_nonneg L t)
        (truncatedRiemannKernelReal_nonneg L _)
    rw [abs_of_nonneg hpos]
    exact (truncatedRiemannAutocorr_le_riemannAutocorr L y).trans (hK y)
  refine ⟨2*C*D, by positivity, fun P n => ?_⟩
  have hs : 0 < sqrt (n + 2 : ℝ) := sqrt_pos.mpr (by positivity)
  have hfinish (a : ℝ) (ha : |a| ≤ 2*C*P.cost*exp (-(c*(n+2)))/sqrt (n+2)) :
      weight n * |a| ≤ 2*C*D*P.cost*(n+3)*exp (-(c*(n+2))) := by
    calc
      _ ≤ (D*(n+3)*sqrt (n+2)) * (2*C*P.cost*exp (-(c*(n+2)))/sqrt (n+2)) :=
        mul_le_mul (hD_bound n) ha (abs_nonneg _) (by positivity)
      _ = _ := by field_simp; ring
  constructor
  · exact hfinish _ (coefficient_exponential P riemannAutocorr hc hC hfull n)
  · intro L
    rw [logValue_test]
    exact hfinish _ (coefficient_exponential P _ hc hC (htrunc L) n)

end RHTower.WeilWorkDeficitBudget

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
  obtain ⟨hi0, hi1⟩ := (P.shift i).property
  obtain ⟨hj0, hj1⟩ := (P.shift j).property
  have hd : |(P.shift j : ℝ) - P.shift i| ≤ log 2 := by
    rw [abs_le]; constructor <;> linarith
  have htri : |y| ≤ |y + P.shift j - P.shift i| + |(P.shift j : ℝ) - P.shift i| := by
    calc
      |y| = |(y + (P.shift j : ℝ) - P.shift i) - ((P.shift j : ℝ) - P.shift i)| := by
        congr 1; ring
      _ ≤ _ := abs_sub _ _
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
  have hl : 0 ≤ log (n + 2 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
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
  have hL := ArithmeticFunction.vonMangoldt_le_log (n := n + 2)
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n + 2 by positivity)
  have hs : 1 ≤ sqrt (n + 2 : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; nlinarith)
  have hm : (n + 2 : ℝ) ≤ (n + 3) * sqrt (n + 2) := by nlinarith
  dsimp [logIndex] at hA
  simp only [Nat.cast_add, Nat.cast_ofNat] at hA hL
  dsimp [weight, logIndex]
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
      _ = _ := by field_simp
  constructor
  · exact hfinish _ (coefficient_exponential P riemannAutocorr hc hC hfull n)
  · intro L
    rw [logValue_test]
    exact hfinish _ (coefficient_exponential P _ hc hC (htrunc L) n)

/-- Every rate below π controls the entire actual weighted defect, uniformly in truncation. -/
theorem weighted_coefficient_exponential {r : ℝ} (hr : 0 < r) (hrπ : r < π) :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : ShortPacket) (n : ℕ),
      weight n * |P.coefficient n| ≤ B * P.cost * exp (-(r * (n + 2))) ∧
      ∀ L : ℝ, weight n * |logValue (P.test L).1 (n + 2)| ≤
        B * P.cost * exp (-(r * (n + 2))) := by
  let c := (r + π) / 2
  have hrc : r < c := by dsimp [c]; linarith
  have hcπ : c < π := by dsimp [c]; linarith
  obtain ⟨B, hB, hbound⟩ := weighted_coefficient_polynomial_exponential (lt_trans hr hrc) hcπ
  let d := c - r
  have hd : 0 < d := sub_pos.mpr hrc
  refine ⟨B * (1 + 1 / d), by positivity, fun P n => ?_⟩
  have hpoly : (n + 3 : ℝ) ≤ (1 + 1 / d) * exp (d * (n + 2)) := by
    have he := Real.add_one_le_exp (d * (n + 2))
    have h1 : 1 ≤ exp (d * (n + 2)) := Real.one_le_exp (by positivity)
    have h2 : (n + 2 : ℝ) ≤ exp (d * (n + 2)) / d := by
      apply (le_div_iff₀ hd).mpr; nlinarith
    calc
      (n + 3 : ℝ) = (n + 2) + 1 := by ring
      _ ≤ exp (d * (n + 2)) / d + exp (d * (n + 2)) := add_le_add h2 h1
      _ = _ := by ring
  have hP := cost_nonneg P
  have hfinish (a : ℝ) (ha : a ≤ B*P.cost*(n+3)*exp (-(c*(n+2)))) :
      a ≤ B*(1+1/d)*P.cost*exp (-(r*(n+2))) := by
    calc
      a ≤ B*P.cost*(n+3)*exp (-(c*(n+2))) := ha
      _ ≤ B*P.cost*((1+1/d)*exp (d*(n+2)))*exp (-(c*(n+2))) := by
        gcongr
      _ = B*(1+1/d)*P.cost*(exp (d*(n+2))*exp (-(c*(n+2)))) := by ring
      _ = _ := by rw [← exp_add]; congr 2; dsimp [d]; ring
  exact ⟨hfinish _ (hbound P n).1, fun L => hfinish _ ((hbound P n).2 L)⟩

private theorem summable_envelope {r : ℝ} (hr : 0 < r) (B : ℝ) (P : ShortPacket) :
    Summable fun n : ℕ => B * P.cost * exp (-(r*(n+2))) := by
  have h := (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hr)).mul_left
    (B * P.cost * exp (-(2*r)))
  refine h.congr fun n => ?_
  rw [mul_assoc, ← exp_add]
  congr 2
  ring

/-- Full weighted untruncated defect is summable for every actual short packet. -/
theorem summable_weighted_coefficient (P : ShortPacket) :
    Summable fun n : ℕ => weight n * |P.coefficient n| := by
  obtain ⟨B, _, hB⟩ := weighted_coefficient_exponential (r := 1) zero_lt_one
    (by linarith [Real.pi_gt_three])
  refine (summable_envelope zero_lt_one B P).of_nonneg_of_le
    (fun n => mul_nonneg (weight_nonneg n) (abs_nonneg _)) fun n => (hB P n).1

/-- Every physical cutoff has a summable full weighted budget, with no index discarded. -/
theorem summable_weighted_logValue (P : ShortPacket) (L : ℝ) :
    Summable fun n : ℕ => weight n * |logValue (P.test L).1 (n + 2)| := by
  obtain ⟨B, _, hB⟩ := weighted_coefficient_exponential (r := 1) zero_lt_one
    (by linarith [Real.pi_gt_three])
  refine (summable_envelope zero_lt_one B P).of_nonneg_of_le
    (fun n => mul_nonneg (weight_nonneg n) (abs_nonneg _)) fun n => (hB P n).2 L

/-- Pointwise convergence of the existing compact logarithmic defect. -/
theorem tendsto_logValue (P : ShortPacket) (n : ℕ) :
    Tendsto (fun L : ℝ => logValue (P.test L).1 (n + 2)) atTop (𝓝 (P.coefficient n)) := by
  simp only [logValue_test, ShortPacket.coefficient]
  have hcorr (y : ℝ) : Tendsto (fun L => P.correlation (truncatedRiemannAutocorr L) y)
      atTop (𝓝 (P.correlation riemannAutocorr y)) := by
    unfold ShortPacket.correlation
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      (tendsto_truncatedRiemannAutocorr _).const_mul _
  exact ((hcorr _).add (hcorr _)).div_const _

/-- Weighted ℓ¹ convergence pays every new integer activated by the growing cutoff. -/
theorem tendsto_weighted_defect_difference (P : ShortPacket) :
    Tendsto (fun L : ℝ => ∑' n : ℕ,
      weight n * |logValue (P.test L).1 (n + 2) - P.coefficient n|) atTop (𝓝 0) := by
  obtain ⟨B, _, hB⟩ := weighted_coefficient_exponential (r := 1) zero_lt_one
    (by linarith [Real.pi_gt_three])
  have hs := (summable_envelope zero_lt_one B P).mul_left 2
  have hlim (n : ℕ) : Tendsto (fun L : ℝ =>
      weight n * |logValue (P.test L).1 (n+2) - P.coefficient n|) atTop (𝓝 0) := by
    simpa using (((tendsto_logValue P n).sub (tendsto_const_nhds (x := P.coefficient n))).abs.const_mul (weight n))
  have h := tendsto_tsum_of_dominated_convergence hs hlim
    (Eventually.of_forall fun L n => ?_)
  · simpa using h
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg n) (abs_nonneg _))]
  have htri := mul_le_mul_of_nonneg_left
    (abs_sub (logValue (P.test L).1 (n+2)) (P.coefficient n)) (weight_nonneg n)
  have h1 := (hB P n).1
  have h2 := (hB P n).2 L
  nlinarith

/-- The complete weighted absolute repair budget converges under physical truncation. -/
theorem tendsto_weighted_budget (P : ShortPacket) :
    Tendsto (fun L : ℝ => ∑' n : ℕ, weight n * |logValue (P.test L).1 (n+2)|)
      atTop (𝓝 (∑' n : ℕ, weight n * |P.coefficient n|)) := by
  obtain ⟨B, _, hB⟩ := weighted_coefficient_exponential (r := 1) zero_lt_one
    (by linarith [Real.pi_gt_three])
  refine tendsto_tsum_of_dominated_convergence (summable_envelope zero_lt_one B P)
    (fun n => (tendsto_logValue P n).abs.const_mul (weight n))
    (Eventually.of_forall fun L n => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg n) (abs_nonneg _))]
  exact (hB P n).2 L

/-- Every arithmetic tail has the same subcritical exponential rate, uniformly in cutoff. -/
theorem weighted_tail_exponential {r : ℝ} (hr : 0 < r) (hrπ : r < π) :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : ShortPacket) (N : ℕ),
      (∑' k : ℕ, weight (N+k) * |P.coefficient (N+k)|) ≤
        B * P.cost * exp (-(r*(N+2))) ∧
      ∀ L : ℝ, (∑' k : ℕ, weight (N+k) * |logValue (P.test L).1 (N+k+2)|) ≤
        B * P.cost * exp (-(r*(N+2))) := by
  obtain ⟨C, hC, hCbound⟩ := weighted_coefficient_exponential hr hrπ
  have hq : exp (-r) < 1 := exp_lt_one_iff.mpr (neg_neg_of_pos hr)
  have hq0 : 0 ≤ exp (-r) := (exp_pos _).le
  refine ⟨C / (1-exp (-r)), by positivity, fun P N => ?_⟩
  have hP := cost_nonneg P
  have hfinish (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
      (hb : ∀ n, a n ≤ C*P.cost*exp (-(r*(n+2)))) :
      (∑' k : ℕ, a (N+k)) ≤ (C/(1-exp (-r)))*P.cost*exp (-(r*(N+2))) := by
    let D := C*P.cost*exp (-(r*(N+2)))
    have hterm (k : ℕ) : a (N+k) ≤ D * exp (-r)^k := by
      refine (hb (N+k)).trans_eq ?_
      dsimp [D]
      rw [← exp_nat_mul]
      have he : exp (-(r * ((N+k : ℕ) + 2 : ℝ))) =
          exp (-(r * (N+2))) * exp ((k : ℝ) * -r) := by
        rw [← exp_add]
        congr 1
        push_cast
        ring
      rw [he]
      ring
    have hs := (summable_geometric_of_lt_one hq0 hq).mul_left D
    have hsA : Summable fun k : ℕ => a (N+k) :=
      hs.of_nonneg_of_le (fun k => ha (N+k)) hterm
    have h := hsA.tsum_le_tsum hterm hs
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq] at h
    refine h.trans_eq ?_
    dsimp [D]
    ring
  exact ⟨hfinish _ (fun n => mul_nonneg (weight_nonneg n) (abs_nonneg _))
      (fun n => (hCbound P n).1), fun L =>
    hfinish _ (fun n => mul_nonneg (weight_nonneg n) (abs_nonneg _))
      (fun n => (hCbound P n).2 L)⟩

end RHTower.WeilWorkDeficitBudget

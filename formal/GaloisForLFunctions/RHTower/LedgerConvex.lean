/-
Doc 37 §2 (tasks #142/#143): the convexity-pairing algebra behind Lemma G.

The corrected ledger leaves gain terms and loss terms with paired increments and
paired weights.  This file isolates the reusable algebraic core: if the gain
increment dominates the loss increment and the gain weight dominates the loss
weight, then the weighted pair contributes nonnegatively.  The analytic work of
doc 37 is to prove those two domination hypotheses for the coth/csch kernels;
this module is the finite algebra they feed.
-/
import GaloisForLFunctions.RHTower.LedgerIdentity

namespace RHTower

open Finset

section WeightedPair

variable {incB incA wB wA : ℝ}

/-- Algebraic decomposition behind the convexity-pairing gain/loss comparison. -/
theorem weighted_pair_decomp :
    incB * wB - incA * wA = (incB - incA) * wA + incB * (wB - wA) := by
  ring

/-- If the left increment and the left weight dominate, the weighted gain dominates the
weighted loss. -/
theorem weighted_pair_nonneg (hinc : incA ≤ incB) (hincA : 0 ≤ incA)
    (hw : wA ≤ wB) (hwA : 0 ≤ wA) :
    0 ≤ incB * wB - incA * wA := by
  rw [weighted_pair_decomp]
  have hincB : 0 ≤ incB := le_trans hincA hinc
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hinc) hwA)
    (mul_nonneg hincB (sub_nonneg.mpr hw))

/-- The paired gain is at least the increment surplus times the smaller weight. -/
theorem weighted_pair_lower_bound (hincB : 0 ≤ incB) (hw : wA ≤ wB) :
    (incB - incA) * wA ≤ incB * wB - incA * wA := by
  rw [weighted_pair_decomp]
  exact le_add_of_nonneg_right (mul_nonneg hincB (sub_nonneg.mpr hw))

/-- Finite-sum form of `weighted_pair_nonneg`, used for the near-range part of the
corrected ledger pairing. -/
theorem sum_weighted_pair_nonneg {ι : Type*} (s : Finset ι)
    (incB incA wB wA : ι → ℝ)
    (hinc : ∀ x ∈ s, incA x ≤ incB x)
    (hincA : ∀ x ∈ s, 0 ≤ incA x)
    (hw : ∀ x ∈ s, wA x ≤ wB x)
    (hwA : ∀ x ∈ s, 0 ≤ wA x) :
    0 ≤ ∑ x ∈ s, (incB x * wB x - incA x * wA x) := by
  exact sum_nonneg fun x hx =>
    weighted_pair_nonneg (hinc x hx) (hincA x hx) (hw x hx) (hwA x hx)

/-- Finite-sum form of `weighted_pair_lower_bound`. -/
theorem sum_weighted_pair_lower_bound {ι : Type*} (s : Finset ι)
    (incB incA wB wA : ι → ℝ)
    (hincB : ∀ x ∈ s, 0 ≤ incB x)
    (hw : ∀ x ∈ s, wA x ≤ wB x) :
    (∑ x ∈ s, ((incB x - incA x) * wA x)) ≤
      ∑ x ∈ s, (incB x * wB x - incA x * wA x) := by
  apply sum_le_sum
  intro x hx
  exact weighted_pair_lower_bound (hincB x hx) (hw x hx)

/-- If the increment on the gain side dominates, any reversal can only come from the
weight defect. -/
theorem weighted_pair_reversal_le (hinc : incA ≤ incB) (hwB : 0 ≤ wB) :
    incA * wA - incB * wB ≤ incA * (wA - wB) := by
  calc
    incA * wA - incB * wB = incA * (wA - wB) - (incB - incA) * wB := by ring
    _ ≤ incA * (wA - wB) := by
      exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hinc) hwB)

/-- A numerical form of `weighted_pair_reversal_le`: bound the increment and the
weight defect separately. -/
theorem weighted_pair_reversal_bound (hinc : incA ≤ incB) (hincA : 0 ≤ incA)
    (hwB : 0 ≤ wB) (hweight : wA - wB ≤ eps) (heps : 0 ≤ eps) (hincBound : incA ≤ L) :
    incA * wA - incB * wB ≤ L * eps := by
  have h0 : incA * wA - incB * wB ≤ incA * (wA - wB) :=
    weighted_pair_reversal_le hinc hwB
  have h1 : incA * (wA - wB) ≤ incA * eps :=
    mul_le_mul_of_nonneg_left hweight hincA
  have h2 : incA * eps ≤ L * eps :=
    mul_le_mul_of_nonneg_right hincBound heps
  exact le_trans h0 (le_trans h1 h2)

/-- If the loss weight is no larger than the gain weight, the reversed pair is nonpositive. -/
theorem weighted_pair_reversal_nonpos (hinc : incA ≤ incB) (hincA : 0 ≤ incA)
    (hwB : 0 ≤ wB) (hw : wA ≤ wB) :
    incA * wA - incB * wB ≤ 0 := by
  have h0 : incA * wA - incB * wB ≤ incA * (wA - wB) :=
    weighted_pair_reversal_le hinc hwB
  have h1 : incA * (wA - wB) ≤ 0 := by
    have hw' : wA - wB ≤ 0 := sub_nonpos.mpr hw
    simpa using mul_nonpos_of_nonneg_of_nonpos hincA hw'
  exact le_trans h0 h1

/-- Finite-sum reversal bound with per-index increment and weight-defect bounds. -/
theorem sum_weighted_pair_reversal_bound {ι : Type*} (s : Finset ι)
    (incB incA wB wA E L : ι → ℝ)
    (hinc : ∀ x ∈ s, incA x ≤ incB x)
    (hincA : ∀ x ∈ s, 0 ≤ incA x)
    (hwB : ∀ x ∈ s, 0 ≤ wB x)
    (hweight : ∀ x ∈ s, wA x - wB x ≤ E x)
    (hE : ∀ x ∈ s, 0 ≤ E x)
    (hincBound : ∀ x ∈ s, incA x ≤ L x) :
    (∑ x ∈ s, (incA x * wA x - incB x * wB x)) ≤ ∑ x ∈ s, L x * E x := by
  apply sum_le_sum
  intro x hx
  exact weighted_pair_reversal_bound (hinc x hx) (hincA x hx) (hwB x hx)
    (hweight x hx) (hE x hx) (hincBound x hx)

/-- Positive-part consequence of `weighted_pair_reversal_bound`. -/
theorem weighted_pair_reversal_posPart_bound (hinc : incA ≤ incB) (hincA : 0 ≤ incA)
    (hwB : 0 ≤ wB) (hweight : wA - wB ≤ eps) (heps : 0 ≤ eps) (hincBound : incA ≤ L)
    (hL : 0 ≤ L) :
    max (incA * wA - incB * wB) 0 ≤ L * eps := by
  apply max_le
  · exact weighted_pair_reversal_bound hinc hincA hwB hweight heps hincBound
  · exact mul_nonneg hL heps

/-- Positive-part consequence when the loss weight is no larger than the gain weight. -/
theorem weighted_pair_reversal_posPart_eq_zero (hinc : incA ≤ incB) (hincA : 0 ≤ incA)
    (hwB : 0 ≤ wB) (hw : wA ≤ wB) :
    max (incA * wA - incB * wB) 0 = 0 := by
  apply le_antisymm
  · exact max_le (weighted_pair_reversal_nonpos hinc hincA hwB hw) le_rfl
  · exact le_max_right _ _

/-- Finite-sum positive-part reversal bound, matching the `(loss-gain)⁺` term in
doc 37 Lemma H. -/
theorem sum_weighted_pair_reversal_posPart_bound {ι : Type*} (s : Finset ι)
    (incB incA wB wA E L : ι → ℝ)
    (hinc : ∀ x ∈ s, incA x ≤ incB x)
    (hincA : ∀ x ∈ s, 0 ≤ incA x)
    (hwB : ∀ x ∈ s, 0 ≤ wB x)
    (hweight : ∀ x ∈ s, wA x - wB x ≤ E x)
    (hE : ∀ x ∈ s, 0 ≤ E x)
    (hincBound : ∀ x ∈ s, incA x ≤ L x)
    (hL : ∀ x ∈ s, 0 ≤ L x) :
    (∑ x ∈ s, max (incA x * wA x - incB x * wB x) 0) ≤ ∑ x ∈ s, L x * E x := by
  apply sum_le_sum
  intro x hx
  exact weighted_pair_reversal_posPart_bound (hinc x hx) (hincA x hx) (hwB x hx)
    (hweight x hx) (hE x hx) (hincBound x hx) (hL x hx)

/-- Finite-sum form of `weighted_pair_reversal_nonpos`. -/
theorem sum_weighted_pair_reversal_nonpos {ι : Type*} (s : Finset ι)
    (incB incA wB wA : ι → ℝ)
    (hinc : ∀ x ∈ s, incA x ≤ incB x)
    (hincA : ∀ x ∈ s, 0 ≤ incA x)
    (hwB : ∀ x ∈ s, 0 ≤ wB x)
    (hw : ∀ x ∈ s, wA x ≤ wB x) :
    (∑ x ∈ s, (incA x * wA x - incB x * wB x)) ≤ 0 := by
  calc
    (∑ x ∈ s, (incA x * wA x - incB x * wB x)) ≤ ∑ _x ∈ s, (0 : ℝ) := by
      apply sum_le_sum
      intro x hx
      exact weighted_pair_reversal_nonpos (hinc x hx) (hincA x hx) (hwB x hx) (hw x hx)
    _ = 0 := by simp

end WeightedPair

/-- Doc 37 numerical boundary: `C₀ ≤ 1/10` gives the non-strict remainder bound. -/
theorem two_hundred_mul_sq_le_two_of_le_one_tenth {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (h : C₀ ≤ (1 : ℝ) / 10) : 200 * C₀ ^ 2 ≤ 2 := by
  nlinarith [sq_nonneg (C₀ - (1 : ℝ) / 10)]

/-- Strict positivity margin for Theorem B″: to get `200*C₀^2 < 2`, use `C₀ < 1/10`. -/
theorem two_hundred_mul_sq_lt_two_of_lt_one_tenth {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (h : C₀ < (1 : ℝ) / 10) : 200 * C₀ ^ 2 < 2 := by
  nlinarith [sq_nonneg (C₀ - (1 : ℝ) / 10)]

/-- The same strict margin in the form consumed by a ledger lower bound `2 - 200*C₀^2`. -/
theorem sub_two_hundred_mul_sq_pos_of_lt_one_tenth {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (h : C₀ < (1 : ℝ) / 10) : 0 < 2 - 200 * C₀ ^ 2 := by
  linarith [two_hundred_mul_sq_lt_two_of_lt_one_tenth hC₀ h]

/-- The stronger numerical threshold used by doc 37 Theorem S′:
`C₀ ≤ 1/15` leaves at least unit march margin. -/
theorem sub_two_hundred_mul_sq_ge_one_of_le_one_fifteenth {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (h : C₀ ≤ (1 : ℝ) / 15) : 1 ≤ 2 - 200 * C₀ ^ 2 := by
  nlinarith [sq_nonneg (C₀ - (1 : ℝ) / 15)]

/-- Constant fold in doc 37 Lemma H's near range: `N` terms, each bounded by
`43*C₀^2*δ`, and `N*δ ≤ 4` give total `≤ 172*C₀^2`. -/
theorem lemmaH_nearRange_const_bound {C₀ δ : ℝ} {N : ℕ}
    (hN : (N : ℝ) * δ ≤ 4) :
    (∑ _k ∈ range N, 43 * C₀ ^ 2 * δ) ≤ 172 * C₀ ^ 2 := by
  rw [sum_const, card_range, nsmul_eq_mul]
  have hC : 0 ≤ 43 * C₀ ^ 2 := by positivity
  calc
    (N : ℝ) * (43 * C₀ ^ 2 * δ) = (43 * C₀ ^ 2) * ((N : ℝ) * δ) := by ring
    _ ≤ (43 * C₀ ^ 2) * 4 := mul_le_mul_of_nonneg_left hN hC
    _ = 172 * C₀ ^ 2 := by ring

/-- Finite-sum version of the near-range constant fold. -/
theorem lemmaH_nearRange_sum_bound {ι : Type*} (s : Finset ι) {C₀ δ : ℝ}
    (hcard : (s.card : ℝ) * δ ≤ 4) (a : ι → ℝ)
    (ha : ∀ x ∈ s, a x ≤ 43 * C₀ ^ 2 * δ) :
    (∑ x ∈ s, a x) ≤ 172 * C₀ ^ 2 := by
  calc
    (∑ x ∈ s, a x) ≤ ∑ _x ∈ s, 43 * C₀ ^ 2 * δ := by
      exact sum_le_sum ha
    _ = (s.card : ℝ) * (43 * C₀ ^ 2 * δ) := by
      rw [sum_const, nsmul_eq_mul]
    _ = (43 * C₀ ^ 2) * ((s.card : ℝ) * δ) := by ring
    _ ≤ (43 * C₀ ^ 2) * 4 := by
      exact mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = 172 * C₀ ^ 2 := by ring

/-- Doc 37 Lemma H final fold: the near-range `172*C₀^2` bound plus a `28*C₀^2`
tail bound gives the advertised `200*C₀^2`. -/
theorem lemmaH_total_bound_of_near_and_tail {C₀ near tail : ℝ}
    (hnear : near ≤ 172 * C₀ ^ 2) (htail : tail ≤ 28 * C₀ ^ 2) :
    near + tail ≤ 200 * C₀ ^ 2 := by
  linarith

/-- A direct form: if a near sum is bounded termwise by `43*C₀^2*δ` with
cardinality scale `card*δ ≤ 4`, and the remaining tail is bounded by `28*C₀^2`,
the whole reversal budget is bounded by `200*C₀^2`. -/
theorem lemmaH_sum_add_tail_bound {ι : Type*} (s : Finset ι) {C₀ δ tail : ℝ}
    (hcard : (s.card : ℝ) * δ ≤ 4) (a : ι → ℝ)
    (ha : ∀ x ∈ s, a x ≤ 43 * C₀ ^ 2 * δ) (htail : tail ≤ 28 * C₀ ^ 2) :
    (∑ x ∈ s, a x) + tail ≤ 200 * C₀ ^ 2 := by
  exact lemmaH_total_bound_of_near_and_tail (lemmaH_nearRange_sum_bound s hcard a ha) htail

/-- Corrected doc 37 Theorem B″ arithmetic: two far-field extras, nonnegative paired
near-range contribution, and a `200*C₀^2` reversal budget give the ledger lower bound. -/
theorem corrected_march_lower_bound {C₀ extra paired reversal ΔG : ℝ}
    (hextra : 2 ≤ extra) (hpaired : 0 ≤ paired)
    (hreversal : reversal ≤ 200 * C₀ ^ 2)
    (hΔ : ΔG = extra + paired - reversal) :
    2 - 200 * C₀ ^ 2 ≤ ΔG := by
  rw [hΔ]
  linarith

/-- Strict corrected march positivity in the theorem range `C₀ < 1/10`. -/
theorem corrected_march_positive_of_C₀_lt_one_tenth {C₀ extra paired reversal ΔG : ℝ}
    (hC₀ : 0 ≤ C₀) (hCsmall : C₀ < (1 : ℝ) / 10)
    (hextra : 2 ≤ extra) (hpaired : 0 ≤ paired)
    (hreversal : reversal ≤ 200 * C₀ ^ 2)
    (hΔ : ΔG = extra + paired - reversal) :
    0 < ΔG := by
  have hlow : 2 - 200 * C₀ ^ 2 ≤ ΔG :=
    corrected_march_lower_bound hextra hpaired hreversal hΔ
  exact lt_of_lt_of_le (sub_two_hundred_mul_sq_pos_of_lt_one_tenth hC₀ hCsmall) hlow

/-- Corrected march margin in the `C₀ ≤ 1/15` range consumed by Theorem S′. -/
theorem corrected_march_ge_one_of_C₀_le_one_fifteenth {C₀ extra paired reversal ΔG : ℝ}
    (hC₀ : 0 ≤ C₀) (hCsmall : C₀ ≤ (1 : ℝ) / 15)
    (hextra : 2 ≤ extra) (hpaired : 0 ≤ paired)
    (hreversal : reversal ≤ 200 * C₀ ^ 2)
    (hΔ : ΔG = extra + paired - reversal) :
    1 ≤ ΔG := by
  have hlow : 2 - 200 * C₀ ^ 2 ≤ ΔG :=
    corrected_march_lower_bound hextra hpaired hreversal hΔ
  exact le_trans (sub_two_hundred_mul_sq_ge_one_of_le_one_fifteenth hC₀ hCsmall) hlow

/-- Per-carrier protocol shell: a direct finite evaluation margin `γᵢ` implies the
corrected march step, independent of the crude `200*C₀^2` theorem range. -/
theorem corrected_march_positive_of_direct_eval {extra paired reversal ΔG γᵢ : ℝ}
    (hγᵢ : 0 < γᵢ) (heval : γᵢ ≤ extra + paired - reversal)
    (hΔ : ΔG = extra + paired - reversal) :
    0 < ΔG := by
  rw [hΔ]
  exact lt_of_lt_of_le hγᵢ heval

/-- Per-carrier protocol shell in the unit-margin form consumed by Theorem S′. -/
theorem corrected_march_ge_one_of_direct_eval {extra paired reversal ΔG γᵢ : ℝ}
    (hγᵢ : 1 ≤ γᵢ) (heval : γᵢ ≤ extra + paired - reversal)
    (hΔ : ΔG = extra + paired - reversal) :
    1 ≤ ΔG := by
  rw [hΔ]
  exact le_trans hγᵢ heval

/-- Direct finite-sum form of corrected doc 37 Theorem B″: Lemma H's near-range and
tail fold supplies the reversal budget consumed by the march assembly. -/
theorem corrected_march_positive_of_sum_tail {ι : Type*} (s : Finset ι)
    {C₀ δ extra paired tail ΔG : ℝ} (a : ι → ℝ)
    (hC₀ : 0 ≤ C₀) (hCsmall : C₀ < (1 : ℝ) / 10)
    (hextra : 2 ≤ extra) (hpaired : 0 ≤ paired)
    (hcard : (s.card : ℝ) * δ ≤ 4)
    (ha : ∀ x ∈ s, a x ≤ 43 * C₀ ^ 2 * δ)
    (htail : tail ≤ 28 * C₀ ^ 2)
    (hΔ : ΔG = extra + paired - ((∑ x ∈ s, a x) + tail)) :
    0 < ΔG := by
  have hrev : (∑ x ∈ s, a x) + tail ≤ 200 * C₀ ^ 2 :=
    lemmaH_sum_add_tail_bound s hcard a ha htail
  exact corrected_march_positive_of_C₀_lt_one_tenth hC₀ hCsmall hextra hpaired hrev hΔ

/-- Direct finite-sum form with the stronger `C₀ ≤ 1/15` unit march margin. -/
theorem corrected_march_ge_one_of_sum_tail {ι : Type*} (s : Finset ι)
    {C₀ δ extra paired tail ΔG : ℝ} (a : ι → ℝ)
    (hC₀ : 0 ≤ C₀) (hCsmall : C₀ ≤ (1 : ℝ) / 15)
    (hextra : 2 ≤ extra) (hpaired : 0 ≤ paired)
    (hcard : (s.card : ℝ) * δ ≤ 4)
    (ha : ∀ x ∈ s, a x ≤ 43 * C₀ ^ 2 * δ)
    (htail : tail ≤ 28 * C₀ ^ 2)
    (hΔ : ΔG = extra + paired - ((∑ x ∈ s, a x) + tail)) :
    1 ≤ ΔG := by
  have hrev : (∑ x ∈ s, a x) + tail ≤ 200 * C₀ ^ 2 :=
    lemmaH_sum_add_tail_bound s hcard a ha htail
  exact corrected_march_ge_one_of_C₀_le_one_fifteenth hC₀ hCsmall hextra hpaired hrev hΔ

/-- Doc 37 §4 increment arithmetic: `ΔG ≥ 1` and `W̄ ≤ 40/δ²` imply
`ΔG/(2W̄) ≥ δ²/80`. -/
theorem corrected_march_increment_lower_bound {ΔG W inc δ : ℝ}
    (hδ : 0 < δ) (hWpos : 0 < W) (hΔG : 1 ≤ ΔG)
    (hW : W ≤ 40 / δ ^ 2) (hinc : inc = ΔG / (2 * W)) :
    δ ^ 2 / 80 ≤ inc := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hWbound : W * δ ^ 2 ≤ 40 := by
    rwa [le_div_iff₀ hδsq] at hW
  rw [hinc]
  rw [le_div_iff₀ (by positivity : 0 < 2 * W)]
  nlinarith [hΔG, hWbound, hδsq]

/-- Doc 37 §4 deep-band arithmetic:
`(δ²/80)*(1.4*27/δ³)` beats the tip error when `M²δ ≥ 36`. -/
theorem corrected_deep_regime_margin_pos {δ M : ℝ}
    (hδ : 0 < δ) (hM : 36 ≤ M ^ 2 * δ) :
    0 < (δ ^ 2 / 80) * (((189 : ℝ) / 5) / δ ^ 3) - 16 / (M ^ 2 * δ ^ 2) := by
  have hMδpos : 0 < M ^ 2 * δ := lt_of_lt_of_le (by norm_num) hM
  have hdenpos : 0 < M ^ 2 * δ ^ 2 := by nlinarith [hMδpos, hδ]
  have hmain : (δ ^ 2 / 80) * (((189 : ℝ) / 5) / δ ^ 3) = 189 / (400 * δ) := by
    field_simp [hδ.ne']
    ring
  have htail : 16 / (M ^ 2 * δ ^ 2) ≤ 4 / (9 * δ) := by
    rw [div_le_iff₀ hdenpos]
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ (by positivity : 0 < 9 * δ)]
    nlinarith [hM, hδ]
  calc
    0 < 101 / (3600 * δ) := by positivity
    _ = 189 / (400 * δ) - 4 / (9 * δ) := by
      field_simp [hδ.ne']
      ring
    _ ≤ (δ ^ 2 / 80) * (((189 : ℝ) / 5) / δ ^ 3) - 16 / (M ^ 2 * δ ^ 2) := by
      rw [hmain]
      linarith

/-- Doc 37 §4 endpoint-band arithmetic:
`(δ²/80)*(5/(12δ²))` beats the tip error when `M²δ² ≥ 56²`. -/
theorem corrected_endpoint_regime_margin_pos {δ M : ℝ}
    (hδ : 0 < δ) (hM : 3136 ≤ M ^ 2 * δ ^ 2) :
    0 < (δ ^ 2 / 80) * ((5 : ℝ) / (12 * δ ^ 2)) - 16 / (M ^ 2 * δ ^ 2) := by
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hdenpos : 0 < M ^ 2 * δ ^ 2 := lt_of_lt_of_le (by norm_num) hM
  have hmain : (δ ^ 2 / 80) * ((5 : ℝ) / (12 * δ ^ 2)) = 1 / 192 := by
    field_simp [hδ2.ne']
    ring
  have htail : 16 / (M ^ 2 * δ ^ 2) ≤ 1 / 196 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [hM]
  calc
    0 < (1 : ℝ) / 192 - 1 / 196 := by norm_num
    _ ≤ (δ ^ 2 / 80) * ((5 : ℝ) / (12 * δ ^ 2)) - 16 / (M ^ 2 * δ ^ 2) := by
      rw [hmain]
      linarith

/-- Deep-band assembly shell for doc 37 Theorem S′.  The response and tip-error
estimates remain explicit hypotheses; this theorem is only the finite arithmetic. -/
theorem corrected_deep_regime_assembly_pos {δ M inc response error ΔS : ℝ}
    (hδ : 0 < δ) (hM : 36 ≤ M ^ 2 * δ)
    (hinc : δ ^ 2 / 80 ≤ inc)
    (hresponse : ((189 : ℝ) / 5) / δ ^ 3 ≤ response)
    (herror : error ≤ 16 / (M ^ 2 * δ ^ 2))
    (hΔS : ΔS = inc * response - error) :
    0 < ΔS := by
  have hbase : 0 < (δ ^ 2 / 80) * (((189 : ℝ) / 5) / δ ^ 3) -
      16 / (M ^ 2 * δ ^ 2) := corrected_deep_regime_margin_pos hδ hM
  have hinc_nonneg : 0 ≤ inc := le_trans (by positivity) hinc
  have hresp_base_nonneg : 0 ≤ ((189 : ℝ) / 5) / δ ^ 3 := by positivity
  have hprod : (δ ^ 2 / 80) * (((189 : ℝ) / 5) / δ ^ 3) ≤ inc * response := by
    exact mul_le_mul hinc hresponse hresp_base_nonneg hinc_nonneg
  rw [hΔS]
  linarith

/-- Endpoint-band assembly shell for doc 37 Theorem S′. -/
theorem corrected_endpoint_regime_assembly_pos {δ M inc response error ΔS : ℝ}
    (hδ : 0 < δ) (hM : 3136 ≤ M ^ 2 * δ ^ 2)
    (hinc : δ ^ 2 / 80 ≤ inc)
    (hresponse : (5 : ℝ) / (12 * δ ^ 2) ≤ response)
    (herror : error ≤ 16 / (M ^ 2 * δ ^ 2))
    (hΔS : ΔS = inc * response - error) :
    0 < ΔS := by
  have hbase : 0 < (δ ^ 2 / 80) * ((5 : ℝ) / (12 * δ ^ 2)) -
      16 / (M ^ 2 * δ ^ 2) := corrected_endpoint_regime_margin_pos hδ hM
  have hinc_nonneg : 0 ≤ inc := le_trans (by positivity) hinc
  have hresp_base_nonneg : 0 ≤ (5 : ℝ) / (12 * δ ^ 2) := by positivity
  have hprod : (δ ^ 2 / 80) * ((5 : ℝ) / (12 * δ ^ 2)) ≤ inc * response := by
    exact mul_le_mul hinc hresponse hresp_base_nonneg hinc_nonneg
  rw [hΔS]
  linarith

end RHTower

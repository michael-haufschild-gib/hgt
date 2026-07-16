import GaloisForLFunctions.HTGeometry.DiscreteMomentHankel
import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# A geometric Källén--Lehmann spectrum

For parameters `0 < a,b < 1`, the positive atomic mass-squared law

`(1-a) * sum_k a^k delta_(b^k)`

has moments

`m_n = (1-a) / (1-a*b^n)`.

This module proves the exact atomic realization, the static self-similarity constraint on the
formal response, strict positivity of every finite moment Hankel determinant, and escape from every
fixed finite spectral width.  These are unconditional positive-spectral facts.  The separate paper
argument that the analytic response is hypertranscendental uses the published general
`q`-difference theorem of Adamczewski--Dreyfus--Hardouin and is intentionally not claimed here.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Weight of the `k`-th geometric Källén--Lehmann atom. -/
def geometricKallenLehmannWeight (a : ℝ) (k : ℕ) : ℝ :=
  (1 - a) * a ^ k

/-- Mass-squared node of the `k`-th geometric Källén--Lehmann atom. -/
def geometricKallenLehmannNode (b : ℝ) (k : ℕ) : ℝ :=
  b ^ k

/-- Closed form of the `n`-th moment of the geometric positive spectrum. -/
def geometricKallenLehmannMoment (a b : ℝ) (n : ℕ) : ℝ :=
  (1 - a) / (1 - a * b ^ n)

/-- The geometric spectral weights are nonnegative. -/
theorem geometricKallenLehmannWeight_nonneg
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (k : ℕ) :
    0 ≤ geometricKallenLehmannWeight a k := by
  exact mul_nonneg (sub_nonneg.mpr ha₁) (pow_nonneg ha₀ k)

/-- Interior parameters make every geometric spectral weight strictly positive. -/
theorem geometricKallenLehmannWeight_pos
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) (k : ℕ) :
    0 < geometricKallenLehmannWeight a k := by
  exact mul_pos (sub_pos.mpr ha₁) (pow_pos ha₀ k)

/-- The moment denominator stays positive throughout the physical parameter square. -/
theorem geometricKallenLehmannMoment_denominator_pos
    {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (n : ℕ) :
    0 < 1 - a * b ^ n := by
  have hbn₀ : 0 ≤ b ^ n := pow_nonneg hb₀ n
  have hbn₁ : b ^ n ≤ 1 := pow_le_one₀ hb₀ hb₁
  nlinarith

/-- Every moment of the geometric positive spectrum is strictly positive. -/
theorem geometricKallenLehmannMoment_pos
    {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (n : ℕ) :
    0 < geometricKallenLehmannMoment a b n := by
  exact div_pos (sub_pos.mpr ha₁)
    (geometricKallenLehmannMoment_denominator_pos ha₀ ha₁ hb₀ hb₁ n)

/-- Coefficientwise form of the fixed self-similarity constraint. -/
theorem geometricKallenLehmannMoment_constraint
    {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (n : ℕ) :
    (1 - a * b ^ n) * geometricKallenLehmannMoment a b n = 1 - a := by
  rw [geometricKallenLehmannMoment]
  field_simp [ne_of_gt
    (geometricKallenLehmannMoment_denominator_pos ha₀ ha₁ hb₀ hb₁ n)]

/-- Every absolute moment of the geometric atomic presentation is summable. -/
theorem summable_geometricKallenLehmannWeight_mul_node_abs_pow
    {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (n : ℕ) :
    Summable (fun k : ℕ ↦
      geometricKallenLehmannWeight a k *
        |geometricKallenLehmannNode b k| ^ n) := by
  have hbn₀ : 0 ≤ b ^ n := pow_nonneg hb₀ n
  have hbn₁ : b ^ n ≤ 1 := pow_le_one₀ hb₀ hb₁
  have hab₀ : 0 ≤ a * b ^ n := mul_nonneg ha₀ hbn₀
  have hab₁ : a * b ^ n < 1 := by nlinarith
  have hs := (summable_geometric_of_lt_one hab₀ hab₁).mul_left (1 - a)
  convert hs using 1
  funext k
  have hpow : (b ^ k) ^ n = (b ^ n) ^ k := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [geometricKallenLehmannWeight, geometricKallenLehmannNode,
    abs_of_nonneg (pow_nonneg hb₀ k), hpow, mul_pow]
  ring

/-- The closed moment formula is exactly the positive atomic moment sum. -/
theorem geometricKallenLehmannMoment_eq_tsum
    {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (n : ℕ) :
    geometricKallenLehmannMoment a b n =
      ∑' k : ℕ,
        geometricKallenLehmannWeight a k *
          geometricKallenLehmannNode b k ^ n := by
  have hbn₀ : 0 ≤ b ^ n := pow_nonneg hb₀ n
  have hbn₁ : b ^ n ≤ 1 := pow_le_one₀ hb₀ hb₁
  have hab₀ : 0 ≤ a * b ^ n := mul_nonneg ha₀ hbn₀
  have hab₁ : a * b ^ n < 1 := by nlinarith
  have hs := (hasSum_geometric_of_lt_one hab₀ hab₁).mul_left (1 - a)
  calc
    geometricKallenLehmannMoment a b n =
        (1 - a) * (1 - a * b ^ n)⁻¹ := by
          simp [geometricKallenLehmannMoment, div_eq_mul_inv]
    _ = ∑' k : ℕ, (1 - a) * (a * b ^ n) ^ k := hs.tsum_eq.symm
    _ = ∑' k : ℕ,
        geometricKallenLehmannWeight a k *
          geometricKallenLehmannNode b k ^ n := by
      apply tsum_congr
      intro k
      have hpow : (b ^ n) ^ k = (b ^ k) ^ n := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [geometricKallenLehmannWeight, geometricKallenLehmannNode, mul_pow, hpow]
      ring

/-- Distinct geometric nodes and positive weights escape every finite spectral palette. -/
theorem geometricKallenLehmann_infiniteSupport
    {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (F : Finset ℝ) :
    ∃ k : ℕ,
      geometricKallenLehmannNode b k ∉ F ∧
        0 < geometricKallenLehmannWeight a k := by
  have hinj : Function.Injective (fun k : ℕ ↦ b ^ k) :=
    (pow_right_strictAnti₀ hb₀ hb₁).injective
  have hrange : (Set.range fun k : ℕ ↦ b ^ k).Infinite :=
    Set.infinite_range_of_injective hinj
  have hex : ∃ k : ℕ, b ^ k ∉ F := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hsub : Set.range (fun k : ℕ ↦ b ^ k) ⊆ (↑F : Set ℝ) := by
      rintro _ ⟨k, rfl⟩
      exact h k
    exact hrange (F.finite_toSet.subset hsub)
  obtain ⟨k, hk⟩ := hex
  exact ⟨k, hk, geometricKallenLehmannWeight_pos ha₀ ha₁ k⟩

/-- Every finite Hankel determinant of the geometric Källén--Lehmann moments is positive. -/
theorem det_momentHankelMatrix_geometricKallenLehmannMoment_pos
    {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (n : ℕ) :
    0 < (momentHankelMatrix (geometricKallenLehmannMoment a b) n).det := by
  have hraw := det_discreteMomentHankel_pos
    (geometricKallenLehmannWeight a)
    (geometricKallenLehmannNode b)
    (fun k ↦ geometricKallenLehmannWeight_nonneg ha₀.le ha₁.le k)
    (fun k ↦ summable_geometricKallenLehmannWeight_mul_node_abs_pow
      ha₀.le ha₁ hb₀.le hb₁.le k)
    (geometricKallenLehmann_infiniteSupport ha₀ ha₁ hb₀ hb₁)
    n
  simpa only [← geometricKallenLehmannMoment_eq_tsum
    ha₀.le ha₁ hb₀.le hb₁.le] using hraw

/-- The geometric positive spectrum cannot be approximated locally with one fixed finite spectral
width. -/
theorem geometricKallenLehmannMoment_not_fixedSpectralWidthLocalClosure
    {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (d : ℕ) :
    ¬ FixedSpectralWidthLocalClosure d (geometricKallenLehmannMoment a b) := by
  apply not_fixedSpectralWidthLocalClosure_of_det_ne_zero
  exact ne_of_gt
    (det_momentHankelMatrix_geometricKallenLehmannMoment_pos
      ha₀ ha₁ hb₀ hb₁ (d + 1))

/-- Formal mass-resolvent response of the geometric Källén--Lehmann spectrum. -/
def geometricKallenLehmannResponse (a b : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (geometricKallenLehmannMoment a b)

@[simp]
theorem geometricKallenLehmannResponse_coeff (a b : ℝ) (n : ℕ) :
    PowerSeries.coeff n (geometricKallenLehmannResponse a b) =
      geometricKallenLehmannMoment a b n := by
  simp [geometricKallenLehmannResponse]

/-- **Static geometric spectral constraint.**  Removing the leading mass atom and rescaling the
remaining spectrum by `b` reproduces the response with weight `a`. -/
theorem geometricKallenLehmannResponse_selfSimilarity
    {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    geometricKallenLehmannResponse a b =
      (1 - a) • (PowerSeries.invOneSubPow ℝ 1).val +
        a • PowerSeries.rescale b (geometricKallenLehmannResponse a b) := by
  ext n
  simp only [geometricKallenLehmannResponse_coeff, map_add, PowerSeries.coeff_smul,
    PowerSeries.coeff_rescale]
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp only [PowerSeries.coeff_mk, Nat.zero_add, Nat.choose_zero_right, smul_eq_mul,
    Nat.cast_one]
  have h := geometricKallenLehmannMoment_constraint ha₀ ha₁ hb₀ hb₁ n
  linear_combination h

/-- **Constraint uniqueness.**  The positive geometric response is the only formal response with
the normalized one-atom boundary term and the prescribed geometric rescaling law.  Thus the
self-similarity identity determines the entire response coefficientwise; it is not merely a law
verified by a preselected series. -/
theorem geometricKallenLehmannResponse_unique
    {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (R : PowerSeries ℝ)
    (hR : R =
      (1 - a) • (PowerSeries.invOneSubPow ℝ 1).val +
        a • PowerSeries.rescale b R) :
    R = geometricKallenLehmannResponse a b := by
  ext n
  have hcoeff := congrArg (PowerSeries.coeff n) hR
  simp only [map_add, PowerSeries.coeff_smul,
    PowerSeries.coeff_rescale] at hcoeff
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose] at hcoeff
  simp only [PowerSeries.coeff_mk, Nat.zero_add, Nat.choose_zero_right,
    smul_eq_mul, Nat.cast_one] at hcoeff
  rw [geometricKallenLehmannResponse_coeff,
    geometricKallenLehmannMoment]
  have hden := geometricKallenLehmannMoment_denominator_pos
    ha₀ ha₁ hb₀ hb₁ n
  field_simp [ne_of_gt hden]
  linear_combination hcoeff

end

end HTGeometry

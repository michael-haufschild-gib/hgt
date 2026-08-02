import Mathlib

/-!
# Coprime product-sign extraction for Route E

This file isolates two exact finite laws used by the all-interval coprime Möbius product-sign
argument.

* A packet whose signs are literally `±1` has each sign mass at least half its total mass minus
  half the absolute signed imbalance.  Deleting an arbitrary bad set costs at most its full mass.
* Uniformly splitting a squarefree product over every Boolean factorization label preserves one
  unit of unsigned capacity, but any product-level signed coefficient is preserved as well.  Thus
  the collision-perfect full Boolean normalization cannot manufacture Möbius cancellation.

Both statements are unconditional finite theorems.  No analytic density or cancellation
hypothesis is present.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Total mass of a finite weighted packet. -/
def finiteProductPairTotalMass
    {α : Type*} (s : Finset α) (weight : α → ℝ) : ℝ :=
  ∑ a ∈ s, weight a

/-- Mass of the positive-sign part of a finite packet. -/
def finiteProductPairPositiveMass
    {α : Type*} (s : Finset α) (weight sign : α → ℝ) : ℝ :=
  ∑ a ∈ s.filter (fun a => sign a = 1), weight a

/-- Mass of the negative-sign part of a finite packet. -/
def finiteProductPairNegativeMass
    {α : Type*} (s : Finset α) (weight sign : α → ℝ) : ℝ :=
  ∑ a ∈ s.filter (fun a => sign a = -1), weight a

/-- Signed mass of a finite product-pair packet. -/
def finiteProductPairSignedMass
    {α : Type*} (s : Finset α) (weight sign : α → ℝ) : ℝ :=
  ∑ a ∈ s, sign a * weight a

/-- Total weight of an arbitrary bad part of a finite packet. -/
def finiteProductPairBadMass
    {α : Type*} (s : Finset α) (weight : α → ℝ) (bad : α → Prop)
    [DecidablePred bad] : ℝ :=
  ∑ a ∈ s.filter bad, weight a

/-- Positive-sign mass remaining after deletion of the bad part. -/
def finiteProductPairGoodPositiveMass
    {α : Type*} (s : Finset α) (weight sign : α → ℝ)
    (bad : α → Prop) [DecidablePred bad] : ℝ :=
  ∑ a ∈ s.filter (fun a => sign a = 1 ∧ ¬ bad a), weight a

/-- Negative-sign mass remaining after deletion of the bad part. -/
def finiteProductPairGoodNegativeMass
    {α : Type*} (s : Finset α) (weight sign : α → ℝ)
    (bad : α → Prop) [DecidablePred bad] : ℝ :=
  ∑ a ∈ s.filter (fun a => sign a = -1 ∧ ¬ bad a), weight a

theorem finiteProductPairTotalMass_eq_positive_add_negative
    {α : Type*} [DecidableEq α] (s : Finset α) (weight sign : α → ℝ)
    (hsign : ∀ a ∈ s, sign a = 1 ∨ sign a = -1) :
    finiteProductPairTotalMass s weight =
      finiteProductPairPositiveMass s weight sign +
        finiteProductPairNegativeMass s weight sign := by
  rw [finiteProductPairTotalMass, finiteProductPairPositiveMass,
    finiteProductPairNegativeMass, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rcases hsign a ha with hp | hn
  · norm_num [hp]
  · norm_num [hn]

theorem finiteProductPairSignedMass_eq_positive_sub_negative
    {α : Type*} [DecidableEq α] (s : Finset α) (weight sign : α → ℝ)
    (hsign : ∀ a ∈ s, sign a = 1 ∨ sign a = -1) :
    finiteProductPairSignedMass s weight sign =
      finiteProductPairPositiveMass s weight sign -
        finiteProductPairNegativeMass s weight sign := by
  rw [finiteProductPairSignedMass, finiteProductPairPositiveMass,
    finiteProductPairNegativeMass, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rcases hsign a ha with hp | hn
  · norm_num [hp]
  · norm_num [hn]

private theorem positiveMass_sub_badMass_le_goodPositiveMass
    {α : Type*} [DecidableEq α] (s : Finset α) (weight sign : α → ℝ)
    (bad : α → Prop) [DecidablePred bad]
    (hweight : ∀ a ∈ s, 0 ≤ weight a) :
    finiteProductPairPositiveMass s weight sign -
        finiteProductPairBadMass s weight bad ≤
      finiteProductPairGoodPositiveMass s weight sign bad := by
  rw [finiteProductPairPositiveMass, finiteProductPairBadMass,
    finiteProductPairGoodPositiveMass, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hp : sign a = 1
  · by_cases hb : bad a
    · simp [hp, hb]
    · simp [hp, hb]
  · by_cases hb : bad a
    · simp [hp, hb, hweight a ha]
    · simp [hp, hb]

private theorem negativeMass_sub_badMass_le_goodNegativeMass
    {α : Type*} [DecidableEq α] (s : Finset α) (weight sign : α → ℝ)
    (bad : α → Prop) [DecidablePred bad]
    (hweight : ∀ a ∈ s, 0 ≤ weight a) :
    finiteProductPairNegativeMass s weight sign -
        finiteProductPairBadMass s weight bad ≤
      finiteProductPairGoodNegativeMass s weight sign bad := by
  rw [finiteProductPairNegativeMass, finiteProductPairBadMass,
    finiteProductPairGoodNegativeMass, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hn : sign a = -1
  · by_cases hb : bad a
    · simp [hn, hb]
    · simp [hn, hb]
  · by_cases hb : bad a
    · simp [hn, hb, hweight a ha]
    · simp [hn, hb]

private theorem halfTotal_sub_halfAbsImbalance_le_both
    {positive negative : ℝ} :
    (positive + negative - |positive - negative|) / 2 ≤ positive ∧
      (positive + negative - |positive - negative|) / 2 ≤ negative := by
  rcases le_total positive negative with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    constructor <;> linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    constructor <;> linarith

/-- **Both-sign extraction after arbitrary bad-pair deletion.**

For nonnegative weights and literal `±1` signs, each surviving sign mass is at least

`(total mass - |signed mass|) / 2 - bad mass`.

In the analytic application, total mass comes from the `μ²` bilinear sum, signed mass from the
`μ` bilinear sum, and the bad mass is the noncoprime-pair union bound. -/
theorem finiteProductPair_bothSignMass_after_bad_lower
    {α : Type*} [DecidableEq α] (s : Finset α) (weight sign : α → ℝ)
    (bad : α → Prop) [DecidablePred bad]
    (hweight : ∀ a ∈ s, 0 ≤ weight a)
    (hsign : ∀ a ∈ s, sign a = 1 ∨ sign a = -1) :
    (finiteProductPairTotalMass s weight -
          |finiteProductPairSignedMass s weight sign|) / 2 -
        finiteProductPairBadMass s weight bad ≤
          finiteProductPairGoodPositiveMass s weight sign bad ∧
      (finiteProductPairTotalMass s weight -
          |finiteProductPairSignedMass s weight sign|) / 2 -
        finiteProductPairBadMass s weight bad ≤
          finiteProductPairGoodNegativeMass s weight sign bad := by
  rw [finiteProductPairTotalMass_eq_positive_add_negative s weight sign hsign,
    finiteProductPairSignedMass_eq_positive_sub_negative s weight sign hsign]
  have hhalf := halfTotal_sub_halfAbsImbalance_le_both
    (positive := finiteProductPairPositiveMass s weight sign)
    (negative := finiteProductPairNegativeMass s weight sign)
  constructor
  · exact le_trans (sub_le_sub_right hhalf.1 _)
      (positiveMass_sub_badMass_le_goodPositiveMass s weight sign bad hweight)
  · exact le_trans (sub_le_sub_right hhalf.2 _)
      (negativeMass_sub_badMass_le_goodNegativeMass s weight sign bad hweight)

/-- Uniformly splitting one unit of capacity over every Boolean factorization label preserves
exactly one unit. -/
theorem sum_uniform_booleanFactorizationCapacity_eq_one
    {α : Type*} [DecidableEq α] (primeSupport : Finset α) :
    ∑ _factorSupport ∈ primeSupport.powerset,
        (1 : ℝ) / 2 ^ primeSupport.card = 1 := by
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hpow : (2 : ℝ) ^ primeSupport.card ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- The same full Boolean normalization preserves any product-level signed coefficient.  Applied
to a squarefree target coefficient `c = μ(n)`, this is the collision-normalization diagonal:
perfect load control pushes the original Möbius coefficient forward unchanged. -/
theorem sum_uniform_booleanFactorization_signedPushforward
    {α : Type*} [DecidableEq α] (primeSupport : Finset α) (c : ℝ) :
    ∑ _factorSupport ∈ primeSupport.powerset,
        c / 2 ^ primeSupport.card = c := by
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hpow : (2 : ℝ) ^ primeSupport.card ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

end

end RHTower

import GaloisForLFunctions.RHTower.GaussianIntegerLogConcavity

/-! # Divisibility correlations in the literal Gaussian integer measure

Reindexing actual multiples identifies their masses with dilations of the same
Gaussian series. Its logarithmic four-point law then signs coprime correlations.
-/

open Set

namespace RHTower.GaussianDivisibility

noncomputable section
set_option autoImplicit false

/-- The Gaussian weight on positive integers, extended by zero at zero. -/
def positiveGaussianWeight (σ y : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ (-σ) * Real.exp (-y * (n : ℝ) ^ 2)

theorem tsum_positiveGaussianWeight (σ y : ℝ) :
    (∑' n : ℕ, positiveGaussianWeight σ y n) = integerGaussianMass σ y := by
  have hi : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b hab
    omega
  have hs : Function.support (positiveGaussianWeight σ y) ⊆
      Set.range (fun n : ℕ => n + 1) := by
    intro n hn
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      exact hn (by simp only [positiveGaussianWeight, if_pos rfl])
    exact ⟨n - 1, by omega⟩
  have h := hi.tsum_eq hs
  have heq : (fun n : ℕ => positiveGaussianWeight σ y (n + 1)) =
      fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-σ)) *
        Real.exp (-y * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    funext n
    exact if_neg (Nat.succ_ne_zero n)
  rw [heq] at h
  exact h.symm

private theorem tsum_if_dvd {d : ℕ} (hd : 0 < d) (f : ℕ → ℝ) :
    (∑' n : ℕ, if d ∣ n then f n else 0) = ∑' k : ℕ, f (d * k) := by
  have hi : Function.Injective (fun k : ℕ => d * k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  have hs : Function.support (fun n : ℕ => if d ∣ n then f n else 0) ⊆
      Set.range (fun k : ℕ => d * k) := by
    intro n hn
    have hdn : d ∣ n := by
      by_contra hnot
      exact hn (if_neg hnot)
    rcases hdn with ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  calc
    _ = ∑' k : ℕ, if d ∣ d * k then f (d * k) else 0 := (hi.tsum_eq hs).symm
    _ = _ := tsum_congr (fun k => if_pos ⟨k, rfl⟩)

theorem positiveGaussianWeight_mul (σ y : ℝ) {d : ℕ} (hd : 0 < d) (n : ℕ) :
    positiveGaussianWeight σ y (d * n) =
      (d : ℝ) ^ (-σ) * positiveGaussianWeight σ ((d : ℝ) ^ 2 * y) n := by
  by_cases hn : n = 0
  · subst n
    simp only [mul_zero, positiveGaussianWeight, if_pos rfl]
  · simp only [positiveGaussianWeight, if_neg hn,
      if_neg (Nat.mul_ne_zero hd.ne' hn), Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg n)]
    rw [show -y * ((d : ℝ) * (n : ℝ)) ^ 2 =
      -((d : ℝ) ^ 2 * y) * (n : ℝ) ^ 2 by ring]
    ring

/-- The mass of the actual set of multiples of `d`. -/
def divisibilityMass (σ y : ℝ) (d : ℕ) : ℝ :=
  ∑' n : ℕ, if d ∣ n then positiveGaussianWeight σ y n else 0

theorem divisibilityMass_eq_scaled_mass (σ y : ℝ) {d : ℕ} (hd : 0 < d) :
    divisibilityMass σ y d =
      (d : ℝ) ^ (-σ) * integerGaussianMass σ ((d : ℝ) ^ 2 * y) := by
  rw [divisibilityMass, tsum_if_dvd hd]
  simp_rw [positiveGaussianWeight_mul σ y hd]
  rw [tsum_mul_left, tsum_positiveGaussianWeight]

/-- The probability of the divisibility event under the one common integer law. -/
def divisibilityProbability (σ y : ℝ) (d : ℕ) : ℝ :=
  divisibilityMass σ y d / integerGaussianMass σ y

theorem divisibilityProbability_eq_tsum (σ y : ℝ) (d : ℕ) :
    divisibilityProbability σ y d = ∑' n : ℕ,
      if d ∣ n then (integerGaussianMass σ y)⁻¹ * positiveGaussianWeight σ y n else 0 := by
  calc
    _ = (integerGaussianMass σ y)⁻¹ *
        ∑' n : ℕ, if d ∣ n then positiveGaussianWeight σ y n else 0 := by
      unfold divisibilityProbability divisibilityMass
      rw [div_eq_mul_inv, mul_comm]
    _ = ∑' n : ℕ, (integerGaussianMass σ y)⁻¹ *
        (if d ∣ n then positiveGaussianWeight σ y n else 0) := tsum_mul_left.symm
    _ = _ := by
      apply tsum_congr
      intro n
      by_cases hn : d ∣ n <;> simp only [hn, if_true, if_false, mul_zero]

/-- The intersection mass is kept as its literal integer indicator sum. -/
def divisibilityIntersectionMass (σ y : ℝ) (a b : ℕ) : ℝ :=
  ∑' n : ℕ, if a ∣ n ∧ b ∣ n then positiveGaussianWeight σ y n else 0

theorem divisibilityIntersectionMass_eq {a b : ℕ} (hab : a.Coprime b) (σ y : ℝ) :
    divisibilityIntersectionMass σ y a b = divisibilityMass σ y (a * b) := by
  apply tsum_congr
  intro n
  have heq : (a ∣ n ∧ b ∣ n) ↔ a * b ∣ n := by
    constructor
    · intro h
      exact hab.mul_dvd_of_dvd_of_dvd h.1 h.2
    · intro h
      exact ⟨dvd_trans ⟨b, rfl⟩ h, dvd_trans ⟨a, Nat.mul_comm b a⟩ h⟩
  rw [heq]

theorem divisibilityMass_nonneg (σ y : ℝ) (d : ℕ) :
    0 ≤ divisibilityMass σ y d := by
  apply tsum_nonneg
  intro n
  split_ifs
  · unfold positiveGaussianWeight
    split_ifs <;> positivity
  · exact le_rfl

/-- The normalized weights sum to one on the original positive integers. -/
theorem tsum_normalized_positiveGaussianWeight {σ y : ℝ} (hσ : 0 ≤ σ) (hy : 0 < y) :
    (∑' n : ℕ, (integerGaussianMass σ y)⁻¹ * positiveGaussianWeight σ y n) = 1 := by
  rw [tsum_mul_left, tsum_positiveGaussianWeight,
    inv_mul_cancel₀ (integerGaussianMass_pos hσ hy).ne']

/-- The literal divisibility masses obey a product inequality with one shared
normalizing mass. No coprimality is needed for this product-modulus statement. -/
theorem divisibilityMass_mul_modulus_le {σ y : ℝ} (hσ : 0 ≤ σ) (hy : 0 < y)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    divisibilityMass σ y (a * b) * integerGaussianMass σ y ≤
      divisibilityMass σ y a * divisibilityMass σ y b := by
  have h := integerGaussianMass_scale_submultiplicative hσ hy
    (show (1 : ℝ) ≤ (a : ℝ) by exact_mod_cast ha)
    (show (1 : ℝ) ≤ (b : ℝ) by exact_mod_cast hb)
  rw [divisibilityMass_eq_scaled_mass σ y (Nat.mul_pos ha hb),
    divisibilityMass_eq_scaled_mass σ y ha,
    divisibilityMass_eq_scaled_mass σ y hb, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b), mul_pow]
  calc
    _ = ((a : ℝ) ^ (-σ) * (b : ℝ) ^ (-σ)) *
        (integerGaussianMass σ y *
          integerGaussianMass σ ((a : ℝ) ^ 2 * (b : ℝ) ^ 2 * y)) := by ring
    _ ≤ ((a : ℝ) ^ (-σ) * (b : ℝ) ^ (-σ)) *
        (integerGaussianMass σ ((a : ℝ) ^ 2 * y) *
          integerGaussianMass σ ((b : ℝ) ^ 2 * y)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem divisibilityProbability_nonneg (σ y : ℝ) (d : ℕ) :
    0 ≤ divisibilityProbability σ y d := by
  apply div_nonneg (divisibilityMass_nonneg σ y d)
  apply tsum_nonneg
  intro n
  positivity

/-- The covariance is defined by the actual intersection of integer events. -/
def divisibilityCovariance (σ y : ℝ) (a b : ℕ) : ℝ :=
  divisibilityIntersectionMass σ y a b / integerGaussianMass σ y -
    divisibilityProbability σ y a * divisibilityProbability σ y b

private theorem normalized_mass_difference (A B C Z : ℝ) (hZ : Z ≠ 0) :
    C / Z - (A / Z) * (B / Z) = Z⁻¹ ^ 2 * (C * Z - A * B) := by
  field_simp [hZ]
  ring

theorem divisibilityProbability_mul_modulus_le {σ y : ℝ} (hσ : 0 ≤ σ) (hy : 0 < y)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    divisibilityProbability σ y (a * b) ≤
      divisibilityProbability σ y a * divisibilityProbability σ y b := by
  apply sub_nonpos.mp
  unfold divisibilityProbability
  rw [normalized_mass_difference _ _ _ _ (integerGaussianMass_pos hσ hy).ne']
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    (sub_nonpos.mpr (divisibilityMass_mul_modulus_le hσ hy ha hb))

/-- Coprime divisibility indicators have nonpositive covariance under every
nonnegatively power-weighted Gaussian integer probability measure. -/
theorem divisibilityCovariance_nonpos {σ y : ℝ} (hσ : 0 ≤ σ) (hy : 0 < y)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    divisibilityCovariance σ y a b ≤ 0 := by
  rw [divisibilityCovariance, divisibilityIntersectionMass_eq hab]
  exact sub_nonpos.mpr (divisibilityProbability_mul_modulus_le hσ hy ha hb)

theorem divisibilityProbability_one {σ y : ℝ} (hσ : 0 ≤ σ) (hy : 0 < y) :
    divisibilityProbability σ y 1 = 1 := by
  rw [divisibilityProbability, divisibilityMass_eq_scaled_mass σ y (by omega : 0 < 1)]
  simp only [Nat.cast_one, Real.one_rpow, one_pow, one_mul]
  exact div_self (integerGaussianMass_pos hσ hy).ne'

/-- The product-modulus inequality holds simultaneously for every finite family. -/
theorem divisibilityProbability_finset_prod_le {ι : Type*} {σ y : ℝ}
    (hσ : 0 ≤ σ) (hy : 0 < y) (S : Finset ι) (d : ι → ℕ)
    (hd : ∀ i ∈ S, 0 < d i) :
    divisibilityProbability σ y (∏ i ∈ S, d i) ≤
      ∏ i ∈ S, divisibilityProbability σ y (d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, divisibilityProbability_one hσ hy, le_refl]
  | @insert i S hi ih =>
      have hdi : 0 < d i := hd i (Finset.mem_insert_self _ _)
      have hdS : ∀ j ∈ S, 0 < d j := fun j hj => hd j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact (divisibilityProbability_mul_modulus_le hσ hy hdi
        (Finset.prod_pos hdS)).trans
        (mul_le_mul_of_nonneg_left (ih hdS) (divisibilityProbability_nonneg σ y (d i)))

end

end RHTower.GaussianDivisibility

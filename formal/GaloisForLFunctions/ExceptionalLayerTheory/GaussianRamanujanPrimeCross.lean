import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherMomentTypeIPole
import GaloisForLFunctions.RHTower.PMRamanujanCutoffPrimeBalance
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The prime cross form on a moving Gaussian window

An even cofactor mask is invariant under every odd prime. After Gaussian
localization, its prime cross form has positive scaled limit: the atom at
twice the prime survives, while the complementary Ramanujan mass escapes.
The error is uniform over every positive Gaussian moment order.
-/

open Complex Finset Filter Topology RHTower
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Squared critical Gaussian moment relative to its value at the physical scale. -/
def gaussianRelativeMomentEnergy (r Q n : ℕ) : ℝ :=
  ((n : ℝ) / Q) ^ (4 * r - 1) * Real.exp (4 * (1 - ((n : ℝ) / Q) ^ 2))

private theorem relativeEnergy_nonneg (r Q n : ℕ) :
    0 ≤ gaussianRelativeMomentEnergy r Q n := by
  unfold gaussianRelativeMomentEnergy
  positivity

private theorem relativeEnergy_self (r : ℕ) {Q : ℕ} (hQ : 0 < Q) :
    gaussianRelativeMomentEnergy r Q Q = 1 := by
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  simp only [gaussianRelativeMomentEnergy, div_self hQ0, one_pow, sub_self,
    mul_zero, Real.exp_zero, mul_one]

private theorem relativeEnergy_le (r : ℕ) (hr : r ≠ 0) {Q n : ℕ}
    (hQ : 0 < Q) (hn : n ≤ Q) :
    gaussianRelativeMomentEnergy r Q n ≤ Real.exp 4 * ((n : ℝ) / Q) ^ 3 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hx0 : 0 ≤ (n : ℝ) / Q := by positivity
  have hx1 : (n : ℝ) / Q ≤ 1 := (div_le_one hQ0).mpr (by exact_mod_cast hn)
  have hk : 3 ≤ 4 * r - 1 := by omega
  have hp : ((n : ℝ) / Q) ^ (4 * r - 1) ≤ ((n : ℝ) / Q) ^ 3 := by
    rw [show 4 * r - 1 = 3 + (4 * r - 1 - 3) by omega, pow_add]
    exact mul_le_of_le_one_right (pow_nonneg hx0 _) (pow_le_one₀ hx0 hx1)
  have he : Real.exp (4 * (1 - ((n : ℝ) / Q) ^ 2)) ≤ Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    nlinarith only [sq_nonneg ((n : ℝ) / Q)]
  exact (mul_le_mul hp he (Real.exp_pos _).le (pow_nonneg hx0 _)).trans_eq (mul_comm _ _)

private def ramanujanCubicHead (η : ℝ) (Q : ℕ) : ℝ :=
  ∑ n ∈ range (Q + 1), ‖pmPowerDampedRamanujanWeight η n‖ * ((n : ℝ) / Q) ^ 3

private theorem tendsto_ramanujanCubicHead {η : ℝ} (hη : 0 < η) :
    Tendsto (ramanujanCubicHead η) atTop (𝓝 0) := by
  let f (Q n : ℕ) : ℝ := if n ≤ Q then
    ‖pmPowerDampedRamanujanWeight η n‖ * ((n : ℝ) / Q) ^ 3 else 0
  have hpoint (n : ℕ) : Tendsto (fun Q => f Q n) atTop (𝓝 0) := by
    have hd : Tendsto (fun Q : ℕ => (n : ℝ) / (Q : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hh := (hd.pow 3).const_mul ‖pmPowerDampedRamanujanWeight η n‖
    simp only [zero_pow (by omega : (3 : ℕ) ≠ 0), mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop n] with Q hQ
    simp only [f, if_pos hQ]
  have hbound : ∀ᶠ Q : ℕ in atTop, ∀ n, ‖f Q n‖ ≤ ‖pmPowerDampedRamanujanWeight η n‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with Q hQ n
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    by_cases hn : n ≤ Q
    · have hx0 : 0 ≤ (n : ℝ) / Q := by positivity
      have hx1 : (n : ℝ) / Q ≤ 1 := (div_le_one hQ0).mpr (by exact_mod_cast hn)
      rw [f, if_pos hn, Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hx0 hx1)
    · simp only [f, if_neg hn, norm_zero, norm_nonneg]
  have hh := tendsto_tsum_of_dominated_convergence
    (hasSum_norm_pmPowerDampedRamanujanWeight hη).summable hpoint hbound
  simp only [tsum_zero] at hh
  have heq (Q : ℕ) : (∑' n, f Q n) = ramanujanCubicHead η Q := by
    rw [tsum_eq_sum (s := range (Q + 1)) (fun n hn => by
      have hnQ : ¬n ≤ Q := by simpa only [mem_range, Nat.lt_succ_iff] using hn
      simp only [f, if_neg hnQ])]
    exact sum_congr rfl fun n hn => by
      simp only [f, if_pos (Nat.lt_succ_iff.mp (mem_range.mp hn))]
  simpa only [heq] using hh

/-- The even-mask prime cross form, scaled by the reciprocal prime mass. -/
def gaussianEvenPrimeCross (η : ℝ) (r p : ℕ) : ℝ :=
  ((p : ℝ) ^ (1 + η) - 1) * pmRamanujanCutoffMean η (2 * p)
    (fun n => pmRamanujanPrimeFeature η p n *
      (if 2 ∣ n then gaussianRelativeMomentEnergy r (2 * p) n else 0))

private theorem primeDifference_even_gaussian {η : ℝ}
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (r : ℕ) :
    pmRamanujanPrimeCutoffDifference η p (2 * p)
      (fun n => if 2 ∣ n then gaussianRelativeMomentEnergy r (2 * p) n else 0) =
      ‖pmPowerDampedRamanujanWeight η 2‖ -
        ∑ n ∈ range (2 * p + 1), if p ∣ n then 0 else
          ‖pmPowerDampedRamanujanWeight η n‖ *
            (if 2 ∣ n then gaussianRelativeMomentEnergy r (2 * p) n else 0) := by
  let H := fun n => if 2 ∣ n then gaussianRelativeMomentEnergy r (2 * p) n else 0
  have hp1 : ¬p ∣ 1 := by simpa only [Nat.dvd_one] using hp.ne_one
  have hp2 : ¬p ∣ 2 := by
    intro h
    have hh := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  have h2p : ¬2 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
  have hQ : 2 * p / p = 2 := Nat.mul_div_cancel 2 hp.pos
  have hHp : H (p * 1) = 0 := by simp only [H, mul_one, if_neg h2p]
  have hH2p : H (p * 2) = 1 := by
    rw [show p * 2 = 2 * p by omega]
    simp only [H, dvd_mul_right, if_true, relativeEnergy_self r (by omega : 0 < 2 * p)]
  have hpos : (∑ n ∈ range (2 + 1), if p ∣ n then 0 else
      ‖pmPowerDampedRamanujanWeight η n‖ * H (p * n)) =
      ‖pmPowerDampedRamanujanWeight η 2‖ := by
    simp only [sum_range_succ, sum_range_zero, dvd_zero, if_true,
      hp1, hp2, if_false, hHp, hH2p, mul_zero, mul_one, zero_add]
  have hsub : range (2 + 1) ⊆ range (2 * p + 1) := range_mono (by omega)
  have hband := sum_sdiff_eq_sub hsub
    (f := fun n => if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight η n‖ * H n)
  have hterm (n : ℕ) :
      (if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight η n‖ * (H (p*n) - H n)) =
      (if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight η n‖ * H (p*n)) -
      (if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight η n‖ * H n) := by
    split_ifs <;> ring
  change pmRamanujanPrimeCutoffDifference η p (2 * p) H = _
  rw [pmRamanujanPrimeCutoffDifference, pmRamanujanPrimeBoundary, hQ,
    sum_congr rfl (fun n _ => hterm n), sum_sub_distrib, hpos, hband]
  ring

/-- The signed form is a surviving even prime atom minus a nonnegative mass. -/
theorem gaussianEvenPrimeCross_eq_atom_sub {η : ℝ} (hη : 0 < η)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (r : ℕ) :
    gaussianEvenPrimeCross η r p = ‖pmPowerDampedRamanujanWeight η 2‖ -
      ∑ n ∈ range (2 * p + 1), if p ∣ n then 0 else
        ‖pmPowerDampedRamanujanWeight η n‖ *
          (if 2 ∣ n then gaussianRelativeMomentEnergy r (2 * p) n else 0) := by
  have hD : (p : ℝ) ^ (1 + η) - 1 ≠ 0 := ne_of_gt
    (lt_trans (by norm_num) (pmPowerDampedRamanujan_prime_denominator_one_lt hη hp))
  rw [gaussianEvenPrimeCross, pmRamanujanPrimeFeature_cutoff_mean hη hp,
    primeDifference_even_gaussian hp hp3]
  field_simp [hD]

private theorem cross_error_le {η : ℝ} (hη : 0 < η)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (r : ℕ) (hr : r ≠ 0) :
    |gaussianEvenPrimeCross η r p - ‖pmPowerDampedRamanujanWeight η 2‖| ≤
      Real.exp 4 * ramanujanCubicHead η (2 * p) := by
  rw [gaussianEvenPrimeCross_eq_atom_sub hη hp hp3]
  have hnonneg : 0 ≤ ∑ n ∈ range (2 * p + 1), if p ∣ n then 0 else
      ‖pmPowerDampedRamanujanWeight η n‖ *
        (if 2 ∣ n then gaussianRelativeMomentEnergy r (2 * p) n else 0) := by
    apply sum_nonneg
    intro n hn
    have hg := relativeEnergy_nonneg r (2 * p) n
    split_ifs <;> positivity
  rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hnonneg]
  rw [ramanujanCubicHead, mul_sum]
  apply sum_le_sum
  intro n hn
  have hnQ : n ≤ 2 * p := Nat.lt_succ_iff.mp (mem_range.mp hn)
  have hb := relativeEnergy_le r hr (by omega : 0 < 2 * p) hnQ
  split_ifs
  · positivity
  · nlinarith only [mul_le_mul_of_nonneg_left hb (norm_nonneg (pmPowerDampedRamanujanWeight η n))]
  · positivity

/-- The exact scaled limit is positive, uniformly over every positive moment order. -/
theorem eventually_gaussianEvenPrimeCross_near_atom {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᶠ p : ℕ in atTop, p.Prime → ∀ r : ℕ, r ≠ 0 →
      |gaussianEvenPrimeCross η r p - ‖pmPowerDampedRamanujanWeight η 2‖| < δ := by
  have hh := ((tendsto_ramanujanCubicHead hη).const_mul (Real.exp 4)).eventually_lt_const hδ
  simp only [mul_zero] at hh
  obtain ⟨N, hN⟩ := eventually_atTop.mp hh
  filter_upwards [eventually_ge_atTop (max N 3)] with p hp hpprime r hr
  exact (cross_error_le hη hpprime (by omega) r hr).trans_lt (hN (2 * p) (by omega))

private theorem weight_two_pos {η : ℝ} (hη : 0 < η) :
    0 < ‖pmPowerDampedRamanujanWeight η 2‖ := by
  have h1 : 0 < ‖pmPowerDampedRamanujanWeight η 1‖ := by
    rw [pmPowerDampedRamanujanWeight_one hη]
    exact (pmPowerDampedDivisorDensity_re_pos hη).trans_le (Complex.re_le_norm _)
  have he := norm_pmPowerDampedRamanujanWeight_prime_mul hη Nat.prime_two 1
  have hnot : ¬2 ∣ (1 : ℕ) := by norm_num
  simp only [mul_one, if_neg hnot] at he
  rw [he]
  exact div_pos h1 (lt_trans (by norm_num)
    (pmPowerDampedRamanujan_prime_denominator_one_lt hη Nat.prime_two))

/-- Gaussian localization makes the even-mask prime cross form strictly positive. -/
theorem eventually_gaussianEvenPrimeCross_pos {η : ℝ} (hη : 0 < η) :
    ∀ᶠ p : ℕ in atTop, p.Prime → ∀ r : ℕ, r ≠ 0 → 0 < gaussianEvenPrimeCross η r p := by
  have hw := weight_two_pos hη
  filter_upwards [eventually_gaussianEvenPrimeCross_near_atom hη (half_pos hw)] with p hp hprime r hr
  have hh := (abs_lt.mp (hp hprime r hr)).1
  linarith only [hh, hw]

#print axioms gaussianEvenPrimeCross_eq_atom_sub
#print axioms eventually_gaussianEvenPrimeCross_near_atom
#print axioms eventually_gaussianEvenPrimeCross_pos
end GaloisForLFunctions.ExceptionalLayerTheory

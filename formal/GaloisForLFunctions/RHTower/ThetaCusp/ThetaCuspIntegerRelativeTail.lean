import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFiniteShellSeamCancellation

/-!
# Relative Gaussian tails for finite theta shells

First-atom domination retains a Gaussian factor in the integer cutoff.
Summing the remaining positive weights bounds the omitted shells relative
to the completed source. Even reflection gives the same bound on the line.
-/

open Real MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- A summable integer weight retaining one Gaussian factor for a cutoff error. -/
def thetaCuspIntegerTailWeight (m : ℕ) : ℝ :=
  (2 * Real.exp Real.pi) * ((m : ℝ) ^ 4 * Real.exp (-(Real.pi - 1) * (m : ℝ) ^ 2))

def thetaCuspIntegerTailConstant : ℝ := ∑' m : ℕ, thetaCuspIntegerTailWeight m

lemma thetaCuspIntegerTailWeight_nonneg (m : ℕ) : 0 ≤ thetaCuspIntegerTailWeight m := by
  unfold thetaCuspIntegerTailWeight
  positivity

lemma summable_thetaCuspIntegerTailWeight : Summable thetaCuspIntegerTailWeight :=
  (summable_pow_mul_exp_neg_nat_sq 4 (by linarith only [Real.pi_gt_three] : 0 < Real.pi - 1)).mul_left _

lemma thetaCuspIntegerTailConstant_nonneg : 0 ≤ thetaCuspIntegerTailConstant :=
  tsum_nonneg thetaCuspIntegerTailWeight_nonneg

lemma thetaCuspSourceAtomDominationWeight_le_integerTail {N m : ℕ} (hNm : N ≤ m) :
    thetaCuspSourceAtomDominationWeight m ≤
      Real.exp (-((N : ℝ) ^ 2)) * thetaCuspIntegerTailWeight m := by
  have hNmR : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hNm
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) N) hNmR 2
  have he : Real.exp (-Real.pi * ((m : ℝ) ^ 2 - 1)) ≤
      Real.exp (-((N : ℝ) ^ 2)) * Real.exp Real.pi *
        Real.exp (-(Real.pi - 1) * (m : ℝ) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hs]
  unfold thetaCuspSourceAtomDominationWeight thetaCuspIntegerTailWeight
  calc
    2 * (m : ℝ) ^ 4 * Real.exp (-Real.pi * ((m : ℝ) ^ 2 - 1)) ≤
        2 * (m : ℝ) ^ 4 * (Real.exp (-((N : ℝ) ^ 2)) * Real.exp Real.pi *
          Real.exp (-(Real.pi - 1) * (m : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

lemma thetaCuspSourceTerm_nonneg_on_halfLine {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    0 ≤ thetaCuspSourceTerm x m := by
  rcases hx.eq_or_lt with hx | hx
  · subst x
    rcases m with _ | m
    · simp only [thetaCuspSourceTerm, Nat.cast_zero, zero_mul, thetaCuspSeed,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        mul_zero, sub_self, le_refl]
    · exact (thetaCuspSourceTerm_zero_pos (Nat.succ_pos m)).le
  · exact thetaCuspSourceTerm_nonneg_of_pos hx m

lemma thetaCuspSourceTerm_one_le_full {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x :=
  (summable_thetaCuspSourceTerm x).le_tsum 1
    (fun m _ => thetaCuspSourceTerm_nonneg_on_halfLine hx m)

/-- The omitted integer shells are relatively small everywhere on the positive half-line. -/
theorem thetaCuspFiniteShellPrefix_relative_tail (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspFullSource x - thetaCuspFiniteShellPrefix N x ∧
    thetaCuspFullSource x - thetaCuspFiniteShellPrefix N x ≤
      thetaCuspIntegerTailConstant * Real.exp (-((N : ℝ) ^ 2)) * thetaCuspFullSource x := by
  have hs := summable_thetaCuspSourceTerm x
  have ht : Summable (fun k : ℕ => thetaCuspSourceTerm x (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr hs
  have hw : Summable (fun k : ℕ => thetaCuspIntegerTailWeight (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr summable_thetaCuspIntegerTailWeight
  have hsplit : thetaCuspFullSource x - thetaCuspFiniteShellPrefix N x =
      ∑' k : ℕ, thetaCuspSourceTerm x (k + (N + 1)) := by
    rw [thetaCuspFullSource, thetaCuspFiniteShellPrefix, ← hs.sum_add_tsum_nat_add (N + 1)]
    ring
  have hwsum : (∑' k : ℕ, thetaCuspIntegerTailWeight (k + (N + 1))) ≤
      thetaCuspIntegerTailConstant := by
    have h := summable_thetaCuspIntegerTailWeight.sum_add_tsum_nat_add (N + 1)
    have hhead : 0 ≤ ∑ m ∈ Finset.range (N + 1), thetaCuspIntegerTailWeight m :=
      Finset.sum_nonneg fun m _ => thetaCuspIntegerTailWeight_nonneg m
    change _ ≤ ∑' m : ℕ, thetaCuspIntegerTailWeight m
    linarith only [h, hhead]
  have hfirst : 0 ≤ thetaCuspSourceTerm x 1 := thetaCuspSourceTerm_nonneg_on_halfLine hx 1
  rw [hsplit]
  refine ⟨tsum_nonneg (fun k => thetaCuspSourceTerm_nonneg_on_halfLine hx _), ?_⟩
  calc
    (∑' k : ℕ, thetaCuspSourceTerm x (k + (N + 1))) ≤
        ∑' k : ℕ, (Real.exp (-((N : ℝ) ^ 2)) *
          thetaCuspIntegerTailWeight (k + (N + 1))) * thetaCuspSourceTerm x 1 := by
      apply ht.tsum_le_tsum _ ((hw.mul_left _).mul_right _)
      intro k
      exact (thetaCuspSourceTerm_le_first (by omega) hx).trans
        (mul_le_mul_of_nonneg_right (thetaCuspSourceAtomDominationWeight_le_integerTail (by omega)) hfirst)
    _ = (Real.exp (-((N : ℝ) ^ 2)) *
        (∑' k : ℕ, thetaCuspIntegerTailWeight (k + (N + 1)))) * thetaCuspSourceTerm x 1 := by
      rw [tsum_mul_right, tsum_mul_left]
    _ ≤ (Real.exp (-((N : ℝ) ^ 2)) * thetaCuspIntegerTailConstant) *
        thetaCuspSourceTerm x 1 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hwsum (Real.exp_pos _).le) hfirst
    _ ≤ (Real.exp (-((N : ℝ) ^ 2)) * thetaCuspIntegerTailConstant) * thetaCuspFullSource x :=
      mul_le_mul_of_nonneg_left (thetaCuspSourceTerm_one_le_full hx)
        (mul_nonneg (Real.exp_pos _).le thetaCuspIntegerTailConstant_nonneg)
    _ = _ := by ring

/-- Reflection of the finite positive half-line source. -/
def reflectedFiniteThetaSource (N : ℕ) (x : ℝ) : ℝ := thetaCuspFiniteShellPrefix N |x|

lemma thetaCuspFullSource_abs (x : ℝ) : thetaCuspFullSource |x| = thetaCuspFullSource x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, thetaCuspFullSource_neg]

/-- The reflected finite source has a global Gaussian relative error. -/
theorem reflectedFiniteThetaSource_relative_tail (N : ℕ) (x : ℝ) :
    0 ≤ thetaCuspFullSource x - reflectedFiniteThetaSource N x ∧
    |thetaCuspFullSource x - reflectedFiniteThetaSource N x| ≤
      thetaCuspIntegerTailConstant * Real.exp (-((N : ℝ) ^ 2)) * thetaCuspFullSource x := by
  have h := thetaCuspFiniteShellPrefix_relative_tail N (abs_nonneg x)
  rw [thetaCuspFullSource_abs] at h
  exact ⟨h.1, (abs_of_nonneg h.1).trans_le h.2⟩

end RHTower

#print axioms RHTower.reflectedFiniteThetaSource_relative_tail

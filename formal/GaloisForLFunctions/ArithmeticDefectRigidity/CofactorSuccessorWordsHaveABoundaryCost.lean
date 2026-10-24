import GaloisForLFunctions.ArithmeticDefectRigidity.FixedSuccessorsDisappearFromEscapingProfiles
import GaloisForLFunctions.ArithmeticDefectRigidity.TheForcingHasFinitePronicMass

/-!
# Boundary cost of finite cofactor-successor words

A word of successor translations and positive integer floor dilations has a multiplicative
denominator and an additive boundary cost. Its action on a cell lies between the pure dilation
and that dilation plus the boundary cost. Applied to the actual receiver, the word therefore
differs from its pure dilation by at most that cost in pronic norm.

Every fixed word loses its successor information on an escaping normalized receiver. The
quantitative estimate also prices moving words; it does not assert disappearance when their
boundary costs grow on the receiver-energy scale.

The forcing's finite pronic L1 mass also pays the signed boundary work uniformly. Thus fixed
word boundaries disappear even in the full forcing pairing on the escaping branch.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A finite word of translations and positive cofactor dilations, acting on integer cells. -/
inductive CellWord where
  | identity
  | successor (k : ℕ) (w : CellWord)
  | cofactor (j : ℕ+) (w : CellWord)

namespace CellWord

def apply : CellWord → ℕ → ℕ
  | .identity, n => n
  | .successor k w, n => w.apply n + k
  | .cofactor j w, n => w.apply n / j

def denominator : CellWord → ℕ
  | .identity => 1
  | .successor _ w => w.denominator
  | .cofactor j w => w.denominator * j

/-- Total translation length; cofactor division cannot increase this boundary budget. -/
def boundaryCost : CellWord → ℕ
  | .identity => 0
  | .successor k w => w.boundaryCost + k
  | .cofactor _ w => w.boundaryCost

theorem denominator_pos (w : CellWord) : 0 < w.denominator := by
  induction w with
  | identity => exact Nat.zero_lt_one
  | successor k w ih => exact ih
  | cofactor j w ih => exact Nat.mul_pos ih j.property

private theorem div_add_le (n b : ℕ) (j : ℕ+) :
    (n + b) / j ≤ n / j + b := by
  have hr := Nat.mod_lt n j.property
  have hid := Nat.div_add_mod n (j : ℕ)
  have hj : 1 ≤ (j : ℕ) := j.property
  have hb : b ≤ (j : ℕ) * b := by nlinarith
  have hlt : n + b < (n / j + b + 1) * j := by nlinarith
  have hd := (Nat.div_lt_iff_lt_mul j.property).mpr hlt
  omega

/-- The word acts within its boundary budget of the pure multiplicative dilation. -/
theorem apply_bounds (w : CellWord) (n : ℕ) :
    n / w.denominator ≤ w.apply n ∧
      w.apply n ≤ n / w.denominator + w.boundaryCost := by
  induction w with
  | identity => simp only [denominator, apply, boundaryCost, Nat.div_one, Nat.add_zero, le_refl,
      and_self]
  | successor k w ih =>
    simp only [denominator, apply, boundaryCost]
    constructor <;> omega
  | cofactor j w ih =>
    simp only [denominator, apply, boundaryCost]
    constructor
    · rw [← Nat.div_div_eq_div_mul]
      exact Nat.div_le_div_right ih.1
    · calc w.apply n / j ≤ (n / w.denominator + w.boundaryCost) / j :=
          Nat.div_le_div_right ih.2
        _ ≤ (n / w.denominator) / j + w.boundaryCost := div_add_le _ _ j
        _ = _ := by rw [Nat.div_div_eq_div_mul]

end CellWord

/-- The actual receiver distinguishes a word from pure dilation by at most its boundary cost. -/
theorem abs_receiver_word_sub_dilation_le (ε : SubcriticalDamping) (w : CellWord) (n : ℕ) :
    |pmPowerDampedCenteredDivisorPrefix ε (w.apply n) -
      pmPowerDampedCenteredDivisorPrefix ε (n / w.denominator)| ≤ (w.boundaryCost : ℝ) := by
  obtain ⟨hl, hu⟩ := w.apply_bounds n
  have heq : n / w.denominator + (w.apply n - n / w.denominator) = w.apply n :=
    Nat.add_sub_of_le hl
  have h := abs_receiver_shift_sub_le ε (n / w.denominator)
    (w.apply n - n / w.denominator)
  rw [heq] at h
  exact h.trans (by exact_mod_cast (show w.apply n - n / w.denominator ≤ w.boundaryCost by omega))

def wordDisplacementEnergy (ε : ℝ) (w : CellWord) (T : ℕ) : ℝ :=
  pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix ε (w.apply n) -
    pmPowerDampedCenteredDivisorPrefix ε (n / w.denominator)) ^ 2

theorem wordDisplacementEnergy_nonneg (ε : ℝ) (w : CellWord) (T : ℕ) :
    0 ≤ wordDisplacementEnergy ε w T := sq_nonneg _

/-- A finite word has a uniform quadratic energy cost relative to its pure dilation. -/
theorem wordDisplacementEnergy_le (ε : SubcriticalDamping) (w : CellWord) (T : ℕ) :
    wordDisplacementEnergy ε w T ≤ (w.boundaryCost : ℝ) ^ 2 := by
  have hsq : ∀ n : ℕ,
      (pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (w.apply n) -
        pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (n / w.denominator)) ^ 2 ≤
          (w.boundaryCost : ℝ) ^ 2 := by
    intro n
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_receiver_word_sub_dilation_le ε w n) 2
  have hone : pronicNorm T (fun _ => 1) ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (pronicNorm_nonneg T (fun _ => 1)) (pronicNorm_one_le T) 2
  calc wordDisplacementEnergy ε w T
      = ∑ n ∈ Icc 1 T, (pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (w.apply n) -
          pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (n / w.denominator)) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) := pronicNorm_sq _ _
    _ ≤ ∑ n ∈ Icc 1 T, (w.boundaryCost : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      sum_le_sum fun n _ => div_le_div_of_nonneg_right (hsq n) (by positivity)
    _ = (w.boundaryCost : ℝ) ^ 2 * pronicNorm T (fun _ => 1) ^ 2 := by
      rw [pronicNorm_sq, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ (w.boundaryCost : ℝ) ^ 2 := by nlinarith [sq_nonneg (w.boundaryCost : ℝ)]

/-- On the escaping branch, all fixed words reduce to pure multiplicative dilations. -/
theorem admits_or_fixed_words_collapse (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ w : CellWord,
      Tendsto (fun T => wordDisplacementEnergy ε w T / dampedMobiusEnergy ε T)
        atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun w => squeeze_zero
      (fun T => div_nonneg (wordDisplacementEnergy_nonneg ε w T)
        (dampedMobiusEnergy_nonneg ε T))
      (fun T => div_le_div_of_nonneg_right (wordDisplacementEnergy_le ε w T)
        (dampedMobiusEnergy_nonneg ε T)) ?_
    exact tendsto_const_nhds.div_atTop hE

/-- The signed work of a word's boundary displacement against the complete forcing. -/
def wordForcingWork (ε : ℝ) (w : CellWord) (T : ℕ) : ℝ :=
  pronicPairing T
    (fun n => pmPowerDampedCenteredDivisorPrefix ε (w.apply n) -
      pmPowerDampedCenteredDivisorPrefix ε (n / w.denominator))
    (inversionDefect ε)

/-- Cauchy--Schwarz prices boundary work using the complete forcing energy. -/
theorem wordForcingWork_sq_le (ε : SubcriticalDamping) (w : CellWord) (T : ℕ) :
    wordForcingWork ε w T ^ 2 ≤ (w.boundaryCost : ℝ) ^ 2 * forcingEnergy ε T := by
  let v : ℕ → ℝ := fun n => pmPowerDampedCenteredDivisorPrefix ε (w.apply n) -
    pmPowerDampedCenteredDivisorPrefix ε (n / w.denominator)
  have hp := sum_mul_div_le_pronicNorm T v (inversionDefect ε)
  change wordForcingWork ε w T ≤ pronicNorm T v * pronicNorm T (inversionDefect ε) at hp
  have hn := sum_mul_div_le_pronicNorm T v (fun n => -inversionDefect ε n)
  rw [pronicNorm_neg] at hn
  have heq : (∑ n ∈ Icc 1 T, v n * -inversionDefect ε n /
      ((n : ℝ) * ((n : ℝ) + 1))) = -wordForcingWork ε w T := by
    simp only [wordForcingWork, pronicPairing, v, mul_neg, neg_div, sum_neg_distrib]
  rw [heq] at hn
  have habs : |wordForcingWork ε w T| ≤
      pronicNorm T v * pronicNorm T (inversionDefect ε) := abs_le.mpr ⟨by linarith, hp⟩
  have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs, mul_pow] at hsq
  change wordForcingWork ε w T ^ 2 ≤
    wordDisplacementEnergy ε w T * forcingEnergy ε T at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_right (wordDisplacementEnergy_le ε w T)
    (forcingEnergy_nonneg ε T))

/-- The generic L2 work estimate retains the second energy ratio `F/E²`. -/
theorem normalized_wordForcingWork_sq_le (ε : SubcriticalDamping) (w : CellWord) (T : ℕ) :
    (wordForcingWork ε w T / dampedMobiusEnergy ε T) ^ 2 ≤
      (w.boundaryCost : ℝ) ^ 2 * (forcingEnergy ε T / dampedMobiusEnergy ε T ^ 2) := by
  rw [div_pow]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (wordForcingWork_sq_le ε w T)
    (sq_nonneg (dampedMobiusEnergy ε T))

/-- Finite pronic forcing mass improves the generic L2 estimate to an absolute work bound. -/
theorem abs_wordForcingWork_le (ε : SubcriticalDamping) (w : CellWord) (T : ℕ) :
    |wordForcingWork ε w T| ≤ (w.boundaryCost : ℝ) * forcingMassLimit ε := by
  unfold wordForcingWork pronicPairing
  calc _ ≤ ∑ n ∈ Icc 1 T,
        |(pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (w.apply n) -
          pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (n / w.denominator)) *
          inversionDefect ε n / ((n : ℝ) * ((n : ℝ) + 1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 T,
        (w.boundaryCost : ℝ) * inversionDefect ε n / ((n : ℝ) * ((n : ℝ) + 1)) := by
      refine sum_le_sum fun n _ => ?_
      rw [abs_div, abs_mul, abs_of_nonneg (inversionDefect_nonneg ε.property.1 n),
        abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) by positivity)]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (abs_receiver_word_sub_dilation_le ε w n)
          (inversionDefect_nonneg ε.property.1 n)) (by positivity)
    _ = (w.boundaryCost : ℝ) * forcingPronicMass ε T := by
      rw [forcingPronicMass, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ (w.boundaryCost : ℝ) * forcingMassLimit ε :=
      mul_le_mul_of_nonneg_left (forcingPronicMass_le_limit ε T) (Nat.cast_nonneg _)

/-- The actual source pays moving-word work linearly in the boundary length. -/
theorem normalized_abs_wordForcingWork_le (ε : SubcriticalDamping) (w : CellWord) (T : ℕ) :
    |wordForcingWork ε w T| / dampedMobiusEnergy ε T ≤
      (w.boundaryCost : ℝ) * forcingMassLimit ε / dampedMobiusEnergy ε T :=
  div_le_div_of_nonneg_right (abs_wordForcingWork_le ε w T) (dampedMobiusEnergy_nonneg ε T)

/-- Fixed word boundaries disappear in the complete forcing pairing whenever energy escapes. -/
theorem admits_or_fixed_word_forcing_work_disappears (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ w : CellWord,
      Tendsto (fun T => |wordForcingWork ε w T| / dampedMobiusEnergy ε T) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun w => squeeze_zero
      (fun T => div_nonneg (abs_nonneg _) (dampedMobiusEnergy_nonneg ε T))
      (normalized_abs_wordForcingWork_le ε w) ?_
    exact tendsto_const_nhds.div_atTop hE

end GaloisForLFunctions.ArithmeticDefectRigidity

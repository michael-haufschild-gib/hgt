import GaloisForLFunctions.RHTower.DivisorSourceResidueOrientation

/-!
# A core-uniform lower margin for the oriented divisor residue

The physical pair residue does not merely retain its parity-determined sign under finite prime
processing.  Its oriented magnitude is bounded below by a fixed positive source moment times the
literal product of the factors `sqrt p - 1`.  Thus the residue margin itself does not collapse as
the core grows; any failure to iterate the even-core pair reserve must arise from quantitative
threshold or finite-cutoff transport, not from a vanishing Mellin-residue coefficient.
-/

noncomputable section
open Complex Filter Set Topology MeasureTheory Finset
namespace RHTower

/-- Every nonempty finite prime core has a parity-oriented Mellin pair-residue margin bounded
below by the complete positive source moment and its explicit growing prime product. -/
theorem divisorCoreMellinPairResidue_uniform_margin (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, p.Prime) :
    (divisorSourceEntire (-(1 / 2))).re *
        Real.exp (-2 * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ)) *
        (∫ x in Ioi (0 : ℝ), divisorContinuousUnitHead x / x ^ 3) *
        (∏ p ∈ P, (Real.sqrt p - 1 : ℝ)) ≤
      (-1 : ℝ) ^ (P.card + 1) * (divisorCoreMellinPairResidue P).re := by
  have hfactor : 0 ≤ (divisorSourceEntire (-(1 / 2))).re *
      (∏ p ∈ P, (Real.sqrt p - 1 : ℝ)) := by
    apply mul_nonneg divisorSourceEntire_negative_half_pos.le
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hprime p hp).one_lt
    have hs : Real.sqrt (1 : ℝ) < Real.sqrt p :=
      Real.sqrt_lt_sqrt (by norm_num) hp1
    exact sub_nonneg.mpr (by simpa only [Real.sqrt_one] using hs.le)
  have hmoment := integral_mobiusDivisorContinuousHead_moment_uniform_lower P hprime
  have he : (∏ p ∈ P, (1 - Real.sqrt p : ℝ)) =
      (-1 : ℝ) ^ P.card * ∏ p ∈ P, (Real.sqrt p - 1 : ℝ) := by
    calc
      _ = ∏ p ∈ P, (-1 : ℝ) * (Real.sqrt p - 1) := by
        apply Finset.prod_congr rfl
        intro p _
        ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hmul := mul_le_mul_of_nonneg_left hmoment hfactor
  have hs : ((-1 : ℝ) ^ P.card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm P.card 2, pow_mul]
    norm_num
  have hresidue :
      (-1 : ℝ) ^ (P.card + 1) * (divisorCoreMellinPairResidue P).re =
        ((divisorSourceEntire (-(1 / 2))).re *
          (∏ p ∈ P, (Real.sqrt p - 1 : ℝ))) *
          ∫ x in Ioi (0 : ℝ), mobiusDivisorContinuousHead P x / x ^ 3 := by
    rw [divisorCoreMellinPairResidue_eq_signed_moment P hP hprime,
      divisorCoreMellinEuler_zero P hprime]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, neg_div]
    rw [he, pow_succ]
    calc
      _ = ((-1 : ℝ) ^ P.card) ^ 2 *
          (((divisorSourceEntire (-(1 / 2))).re *
            (∏ p ∈ P, (Real.sqrt p - 1 : ℝ))) *
            ∫ x in Ioi (0 : ℝ), mobiusDivisorContinuousHead P x / x ^ 3) := by ring
      _ = _ := by rw [hs, one_mul]
  rw [hresidue]
  calc
    _ = ((divisorSourceEntire (-(1 / 2))).re *
        (∏ p ∈ P, (Real.sqrt p - 1 : ℝ))) *
        (Real.exp (-2 * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ)) *
          ∫ x in Ioi (0 : ℝ), divisorContinuousUnitHead x / x ^ 3) := by ring
    _ ≤ _ := hmul

end RHTower

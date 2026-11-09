import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape
import GaloisForLFunctions.RHTower.ThetaTranslationMeasureGauge
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeFluxSplit
import GaloisForLFunctions.RHTower.Sieve.EulerExpansion

/-!
# A relative theta neighborhood preserves all finite prime deletions

First-atom domination and the exact integer shift identity bound every finite
prime-deletion operator by the same relative norm constant. The first atom
survives every deletion, giving a fixed positive radius around the theta source.
-/

noncomputable section
set_option autoImplicit false

open Real Set RHTower

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Uniform domination of the full source by its first atom. -/
def thetaFirstAtomConstant : ℝ := 1 + thetaCuspHigherAtomDominationWeight

theorem thetaFirstAtomConstant_pos : 0 < thetaFirstAtomConstant := by
  have h := thetaCuspHigherAtomDominationWeight_nonneg
  unfold thetaFirstAtomConstant
  linarith only [h]

theorem thetaCuspFullSource_le_first_uniform {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullSource x ≤ thetaFirstAtomConstant * thetaCuspSourceTerm x 1 := by
  have h := thetaCuspFullSource_sub_first_le hx
  unfold thetaFirstAtomConstant
  linarith only [h]

/-- Prime subsets contribute distinct integer atoms, so their absolute operator bound
is independent of the number and sizes of the deleted primes. -/
theorem abs_thetaPrimeDeletion_le_relative {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x, 0 ≤ x → |g x| ≤ C * thetaCuspFullSource x)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {x : ℝ} (hx : 0 ≤ x) :
    |thetaPrimeDeletion S g x| ≤ C * thetaFirstAtomConstant * thetaCuspFullSource x := by
  classical
  have hterm (T : Finset ℕ) (hT : T ∈ S.powerset) :
      |(-1 : ℝ) ^ T.card * (((∏ p ∈ T, p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        g (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ)))| ≤
        (C * thetaFirstAtomConstant) * thetaCuspSourceTerm x (∏ p ∈ T, p) := by
    let d : ℕ := ∏ p ∈ T, p
    have hd : 0 < d := Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hy : 0 ≤ x + Real.log (d : ℝ) := add_nonneg hx (Real.log_nonneg hd1)
    have hp : 0 ≤ (d : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg d) _
    have hshift : (d : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (x + Real.log d) ≤
        thetaFirstAtomConstant * thetaCuspSourceTerm x d := by
      calc
        _ ≤ (d : ℝ) ^ (-(1 / 2 : ℝ)) *
            (thetaFirstAtomConstant * thetaCuspSourceTerm (x + Real.log d) 1) :=
          mul_le_mul_of_nonneg_left (thetaCuspFullSource_le_first_uniform hy) hp
        _ = thetaFirstAtomConstant * ((d : ℝ) ^ (-(1 / 2 : ℝ)) *
            thetaCuspSourceTerm (x + Real.log d) 1) := by ring
        _ = _ := by rw [invSqrt_mul_thetaCuspSourceTerm_shift hd, Nat.mul_one]
    change |(-1 : ℝ) ^ T.card * ((d : ℝ) ^ (-(1 / 2 : ℝ)) * g (x + Real.log d))| ≤ _
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hp]
    calc
      _ ≤ (d : ℝ) ^ (-(1 / 2 : ℝ)) * (C * thetaCuspFullSource (x + Real.log d)) :=
        mul_le_mul_of_nonneg_left (hg _ hy) hp
      _ = C * ((d : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (x + Real.log d)) := by ring
      _ ≤ C * (thetaFirstAtomConstant * thetaCuspSourceTerm x d) :=
        mul_le_mul_of_nonneg_left hshift hC
      _ = _ := by ring
  have hsum : (∑ T ∈ S.powerset, thetaCuspSourceTerm x (∏ p ∈ T, p)) ≤
      thetaCuspFullSource x := by
    calc
      _ = ∑ n ∈ S.powerset.image (fun T => ∏ p ∈ T, p), thetaCuspSourceTerm x n := by
        rw [Finset.sum_image (Sieve.prod_injOn_powerset hS)]
      _ ≤ _ := (summable_thetaCuspSourceTerm x).sum_le_tsum _
        (fun n _ => thetaCuspSourceTerm_nonneg_of_nonneg hx n)
  calc
    _ ≤ ∑ T ∈ S.powerset, (C * thetaFirstAtomConstant) *
        thetaCuspSourceTerm x (∏ p ∈ T, p) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = (C * thetaFirstAtomConstant) *
        (∑ T ∈ S.powerset, thetaCuspSourceTerm x (∏ p ∈ T, p)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (mul_nonneg hC thetaFirstAtomConstant_pos.le)

/-- A fixed radius works simultaneously for every finite set of primes. -/
def thetaDeletionRelativeRadius : ℝ := 1 / (2 * thetaFirstAtomConstant ^ 2)

theorem thetaDeletionRelativeRadius_pos : 0 < thetaDeletionRelativeRadius := by
  have h := thetaFirstAtomConstant_pos
  unfold thetaDeletionRelativeRadius
  positivity

/-- Every source in the relative theta ball retains half the first atom after every deletion. -/
theorem thetaPrimeDeletion_lower_of_relative_ball {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → |f x - thetaCuspFullSource x| ≤
      thetaDeletionRelativeRadius * thetaCuspFullSource x)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x 1 / 2 ≤ thetaPrimeDeletion S f x := by
  have h := abs_thetaPrimeDeletion_le_relative thetaDeletionRelativeRadius_pos.le hf S hS hx
  rw [thetaPrimeDeletion_sub] at h
  have hb := mul_le_mul_of_nonneg_left (thetaCuspFullSource_le_first_uniform hx)
    (mul_nonneg thetaDeletionRelativeRadius_pos.le thetaFirstAtomConstant_pos.le)
  have he : thetaDeletionRelativeRadius * thetaFirstAtomConstant *
      (thetaFirstAtomConstant * thetaCuspSourceTerm x 1) = thetaCuspSourceTerm x 1 / 2 := by
    unfold thetaDeletionRelativeRadius
    field_simp [thetaFirstAtomConstant_pos.ne']
  rw [he] at hb
  have hlow := (thetaCuspSourceTerm_one_le_thetaPrimeDeletion S hS hx).1
  have hab := (abs_le.mp (h.trans hb)).1
  linarith only [hlow, hab]

theorem thetaPrimeDeletion_pos_of_relative_ball {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → |f x - thetaCuspFullSource x| ≤
      thetaDeletionRelativeRadius * thetaCuspFullSource x)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaPrimeDeletion S f x :=
  (half_pos (thetaCuspSourceTerm_one_pos_of_nonneg hx)).trans_le
    (thetaPrimeDeletion_lower_of_relative_ball hf S hS hx)

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.thetaPrimeDeletion_lower_of_relative_ball

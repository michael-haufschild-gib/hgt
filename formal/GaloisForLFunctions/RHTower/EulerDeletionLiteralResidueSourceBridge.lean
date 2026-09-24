import GaloisForLFunctions.RHTower.EulerDeletionLiteralResidueSpectralSupport
import GaloisForLFunctions.RHTower.EulerDeletionMobiusPeriodCovariance

/-!
# The spectral signal is the literal centered residue source

The factorial-clock complex source used in the Fourier support theorem is
identified pointwise with the existing real residue combination minus its
exact complete-period mean. No physical weight or sign is changed.
-/

noncomputable section
open Finset

namespace RHTower.DeletionPeriodCovariance

theorem centeredSourcePeriod_apply_eq_complex_centered_residue
    (N : ℕ) (a : ℕ → ℝ) (x : ZMod N.factorial) :
    RHTower.Sieve.centeredSourcePeriod N.factorial N a x =
      ((residueCombination (Finset.Icc 1 N) a x.val -
        periodMean (Finset.Icc 1 N) a : ℝ) : ℂ) := by
  let S := Finset.Icc 1 N
  have hterm (d : ℕ) (hd : d ∈ S) :
      ((a d : ℝ) : ℂ) * RHTower.Sieve.liftedNormalizedResidue N.factorial d x =
      ((a d * ((x.val % d : ℕ) : ℝ) / (d : ℝ) -
        a d * ((d : ℝ) - 1) / (2 * (d : ℝ)) : ℝ) : ℂ) := by
    have hdC : (d : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
    unfold RHTower.Sieve.liftedNormalizedResidue
    push_cast
    field_simp
  calc
    RHTower.Sieve.centeredSourcePeriod N.factorial N a x =
        ∑ d ∈ S, ((a d * ((x.val % d : ℕ) : ℝ) / (d : ℝ) -
          a d * ((d : ℝ) - 1) / (2 * (d : ℝ)) : ℝ) : ℂ) := by
      unfold RHTower.Sieve.centeredSourcePeriod
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl hterm
    _ = ((∑ d ∈ S, (a d * ((x.val % d : ℕ) : ℝ) / (d : ℝ) -
          a d * ((d : ℝ) - 1) / (2 * (d : ℝ))) : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = ((residueCombination S a x.val - periodMean S a : ℝ) : ℂ) := by
      rw [residueCombination, periodMean, Finset.sum_sub_distrib]

end RHTower.DeletionPeriodCovariance

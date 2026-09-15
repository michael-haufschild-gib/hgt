import GaloisForLFunctions.RHTower.EulerDeletionRamarePhysical
import GaloisForLFunctions.RHTower.BaezDuarteGramDiscrete
import GaloisForLFunctions.RHTower.BaezDuarteMobiusPrefixApproximation

/-!
# Exact signed physical energy for Euler-deletion Ramaré packets

The literal Euler-deletion source has a finite, exact Báez--Duarte Gram
energy.  The Ramaré source identity transfers that energy to the complete
signed physical packet field, retaining every rough, dilation, and harmonic
cross term.  Thus a cofinal energy estimate for EDQ has one unambiguous
target; no unweighted-period substitute is used here.
-/

noncomputable section

open Finset MeasureTheory Set
open scoped ArithmeticFunction.Moebius

namespace RHTower.DeletionRamarePhysical

/-- The exact finite Gram energy of the literal Möbius source. -/
def sourceGramEnergy (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
    ((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ) *
      bdGram (1 / (n : ℝ)) (1 / (m : ℝ))

/-- The squared physical source norm is precisely its complete finite signed
Gram form. -/
theorem integral_source_sq_eq_sourceGramEnergy (M : ℕ) :
    (∫ u in Ioi (1 : ℝ), source M u ^ 2) = sourceGramEnergy M := by
  classical
  have habs : ∀ n ∈ Finset.Icc 1 M, |1 / (n : ℝ)| ≤ 1 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega) hn1)
    rw [abs_of_pos (by positivity), div_le_one hn0]
    exact_mod_cast hn1
  have hterm : ∀ n ∈ Finset.Icc 1 M, ∀ m ∈ Finset.Icc 1 M,
      IntegrableOn (fun u : ℝ =>
        ((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ) *
          (bdGenReal (1 / (n : ℝ)) u * bdGenReal (1 / (m : ℝ)) u)) (Ioi 1) := by
    intro n hn m hm
    exact (integrableOn_bdGenReal_mul (habs n hn) (habs m hm)).const_mul _
  unfold source sourceGramEnergy
  simp_rw [pow_two, Finset.sum_mul_sum]
  have hnormalize :
      (fun u : ℝ => ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
        ((μ n : ℤ) : ℝ) * bdGenReal (1 / (n : ℝ)) u *
          (((μ m : ℤ) : ℝ) * bdGenReal (1 / (m : ℝ)) u)) =
      (fun u : ℝ => ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
        ((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ) *
          (bdGenReal (1 / (n : ℝ)) u * bdGenReal (1 / (m : ℝ)) u)) := by
    funext u
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hnormalize]
  rw [integral_finsetSum _ (fun n hn => integrable_finsetSum _ (hterm n hn))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_finsetSum _ (hterm n hn)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_const_mul, bdGram]

/-- The complete signed Ramaré physical packet field has exactly the literal
Möbius Gram energy.  In particular, this equality retains all prime--prime,
prime--rough, and harmonic-correction cross terms. -/
theorem integral_packetField_sq_eq_sourceGramEnergy {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) :
    (∫ u in Ioi (1 : ℝ), (rough P M u - ∑ p ∈ P, packet P M p u) ^ 2) =
      sourceGramEnergy M := by
  calc
    _ = ∫ u in Ioi (1 : ℝ), source M u ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change (rough P M u - ∑ p ∈ P, packet P M p u) ^ 2 = source M u ^ 2
      rw [source_eq_rough_sub_sum_packet hPprime M u]
    _ = _ := integral_source_sq_eq_sourceGramEnergy M

/-- The literal physical Gram form is the squared norm of the existing
modular Möbius approximant.  Hence the complete Ramaré packet field retains
the same signed off-diagonal arithmetic covariance as the original carrier. -/
theorem sourceGramEnergy_eq_modular_norm_sq (M : ℕ) :
    sourceGramEnergy M = ‖bdMobiusModularApproximantVec M‖ ^ 2 := by
  rw [bdMobiusModularApproximantVec_eq_generatorCombination,
    bdMobiusGeneratorCombination, ← bdGram_quadraticForm_eq_norm_sq]
  simp only [neg_mul_neg]
  rfl

/-- The complete physical Ramaré packet energy is exactly the modular Möbius
carrier energy, with every signed cross term retained. -/
theorem integral_packetField_sq_eq_modular_norm_sq {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) :
    (∫ u in Ioi (1 : ℝ), (rough P M u - ∑ p ∈ P, packet P M p u) ^ 2) =
      ‖bdMobiusModularApproximantVec M‖ ^ 2 := by
  rw [integral_packetField_sq_eq_sourceGramEnergy hPprime M,
    sourceGramEnergy_eq_modular_norm_sq]

end RHTower.DeletionRamarePhysical

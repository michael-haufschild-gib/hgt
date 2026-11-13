import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarSourceIsContinuousInTheWeightedNorm
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit

/-!
# Complete exponential prime rows on the half-line

The forward row stops at the terminal support and is bounded by Chebyshev's
function. The backward row is a convergent von Mangoldt Dirichlet series.
Both bounds hold uniformly over arbitrary finite prime-index sets.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

private theorem barrier_atom_nonneg (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

theorem exponentialBarrier_prime_forward_coefficient {n : ℕ} (hn : 2 ≤ n) (β : ℝ) :
    vonMangoldtAtom n * Real.exp (β * Real.log (n : ℝ)) =
      (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp ((β - 1 / 2) * Real.log (n : ℝ)) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [vonMangoldtAtom, if_pos hn, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0,
    div_eq_mul_inv, mul_assoc, ← Real.exp_neg, ← Real.exp_add]
  congr 2
  ring

theorem exponentialBarrier_prime_backward_coefficient {n : ℕ} (hn : 2 ≤ n) (β : ℝ) :
    vonMangoldtAtom n * Real.exp (-(β * Real.log (n : ℝ))) =
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (β + 1 / 2) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [vonMangoldtAtom, if_pos hn, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0]
  simp only [div_eq_mul_inv, ← Real.exp_neg]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The backward exponential prime row has finite total mass for every rate above one half. -/
theorem summable_exponentialBarrier_prime_backward {β : ℝ} (hβ : 1 / 2 < β) :
    Summable (fun n : ℕ => vonMangoldtAtom n * Real.exp (-(β * Real.log (n : ℝ)))) := by
  have hs := summable_vonMangoldt_div_rpow (show 1 < β + 1 / 2 by linarith only [hβ])
  apply hs.congr
  intro n
  by_cases hn : 2 ≤ n
  · exact (exponentialBarrier_prime_backward_coefficient hn β).symm
  · have h01 : n = 0 ∨ n = 1 := by omega
    rcases h01 with rfl | rfl <;> simp [vonMangoldtAtom]

/-- Total mass of the backward prime row after division by the exponential barrier. -/
def halfLineExponentialPrimeTail (β : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(β * Real.log (n : ℝ)))

theorem halfLineExponentialPrimeTail_nonneg (β : ℝ) : 0 ≤ halfLineExponentialPrimeTail β :=
  tsum_nonneg fun n => mul_nonneg (barrier_atom_nonneg n) (Real.exp_pos _).le

theorem sum_exponentialBarrier_prime_backward_le {β : ℝ} (hβ : 1 / 2 < β) (s : Finset ℕ) :
    (∑ n ∈ s, vonMangoldtAtom n * Real.exp (-(β * Real.log (n : ℝ)))) ≤
      halfLineExponentialPrimeTail β :=
  (summable_exponentialBarrier_prime_backward hβ).sum_le_tsum s
    (fun n _ => mul_nonneg (barrier_atom_nonneg n) (Real.exp_pos _).le)

private theorem sum_weighted_log_cutoff_le_psi {p : ℝ} (hp : 0 ≤ p)
    (s : Finset ℕ) (x : ℝ) :
    (∑ n ∈ s.filter (fun n : ℕ => 2 ≤ n ∧ Real.log (n : ℝ) < x),
      (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp (p * Real.log (n : ℝ))) ≤
      Real.exp (p * x) * Chebyshev.psi (Real.exp x) := by
  classical
  let S : Finset ℕ := s.filter (fun n : ℕ => 2 ≤ n ∧ Real.log (n : ℝ) < x)
  have hsubset : S ⊆ Finset.Ioc 0 ⌊Real.exp x⌋₊ := by
    intro n hn
    have hn' := (Finset.mem_filter.mp hn).2
    have hn2 : 2 ≤ n := hn'.1
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    exact Finset.mem_Ioc.mpr ⟨by omega,
      Nat.le_floor (((Real.log_lt_iff_lt_exp hn0).mp hn'.2).le)⟩
  calc
    _ ≤ ∑ n ∈ S, Real.exp (p * x) * (ArithmeticFunction.vonMangoldt n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := (Finset.mem_filter.mp hn).2
      exact (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn'.2.le hp))
        ArithmeticFunction.vonMangoldt_nonneg).trans_eq (mul_comm _ _)
    _ = Real.exp (p * x) * ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) :=
      (Finset.mul_sum S _ _).symm
    _ ≤ Real.exp (p * x) *
        ∑ n ∈ Finset.Ioc 0 ⌊Real.exp x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = _ := rfl

/-- The support-restricted growing row has exponential order `β+1/2`, uniformly in the cutoff. -/
theorem sum_exponentialBarrier_prime_forward_le {β : ℝ} (hβ : 1 / 2 ≤ β)
    (s : Finset ℕ) (u : ℝ) :
    (∑ n ∈ s, if u < -Real.log (n : ℝ) then
      vonMangoldtAtom n * Real.exp (β * Real.log (n : ℝ)) else 0) ≤
      6 * Real.exp (-((β + 1 / 2) * u)) := by
  classical
  have he : (∑ n ∈ s, if u < -Real.log (n : ℝ) then
      vonMangoldtAtom n * Real.exp (β * Real.log (n : ℝ)) else 0) =
      ∑ n ∈ s.filter (fun n : ℕ => 2 ≤ n ∧ Real.log (n : ℝ) < -u),
        (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp ((β - 1 / 2) * Real.log (n : ℝ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : 2 ≤ n
    · by_cases hu : u < -Real.log (n : ℝ)
      · have hl : Real.log (n : ℝ) < -u := by linarith only [hu]
        rw [if_pos hu, if_pos ⟨hn, hl⟩]
        exact exponentialBarrier_prime_forward_coefficient hn β
      · have hl : ¬ Real.log (n : ℝ) < -u := by linarith only [hu]
        rw [if_neg hu, if_neg (fun h => hl h.2)]
    · simp only [hn, false_and, if_false, vonMangoldtAtom, if_neg hn, zero_mul,
        ite_self]
  rw [he]
  have hrow := sum_weighted_log_cutoff_le_psi (sub_nonneg.mpr hβ) s (-u)
  have hpsi := mul_le_mul_of_nonneg_left (exp_mul_chebyshevPsi_le_six u).2
    (Real.exp_pos (-((β + 1 / 2) * u))).le
  have hexp : Real.exp ((β - 1 / 2) * (-u)) * Chebyshev.psi (Real.exp (-u)) =
      Real.exp (-((β + 1 / 2) * u)) * (Real.exp u * Chebyshev.psi (Real.exp (-u))) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  exact hrow.trans ((le_of_eq hexp).trans (hpsi.trans_eq (mul_comm _ _)))

#print axioms summable_exponentialBarrier_prime_backward
#print axioms sum_exponentialBarrier_prime_forward_le
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

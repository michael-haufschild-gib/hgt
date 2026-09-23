import GaloisForLFunctions.RHTower.XiPoissonVerticalType
import GaloisForLFunctions.RHTower.XiHeatShellMinimum

/-!
# Poisson shells of the Xi divisor

A Poisson shell is a level set of the height `Re (xiPoissonPoint q) = |g|`.  Shells are finite,
because the squared coordinate's shell `(xiSpectralPoint q ^ (2 : ℕ)).re <= R ^ (2 : ℕ)` already is and the
critical strip makes the two comparable:

`(xiSpectralPoint q ^ (2 : ℕ)).re = g ^ (2 : ℕ) - delta ^ (2 : ℕ) <= g ^ (2 : ℕ) = (Re (xiPoissonPoint q)) ^ (2 : ℕ)`.

Finiteness gives a lowest shell, which is where the peeling induction of the vertical criterion
starts.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A Poisson shell of the Xi divisor is finite. -/
theorem finite_xiPoissonShell (R : ℝ) :
    {q : XiZeroCopy | (xiPoissonPoint q).re ≤ R}.Finite := by
  refine Set.Finite.subset (finite_xiHeatShell (R ^ (2 : ℕ))) ?_
  intro q hq
  simp only [Set.mem_setOf_eq] at hq ⊢
  have hnn : 0 ≤ (xiPoissonPoint q).re := xiPoissonPoint_re_nonneg q
  have hsq : (xiSpectralPoint q ^ (2 : ℕ)).re =
      (xiSpectralPoint q).re * (xiSpectralPoint q).re -
        (xiSpectralPoint q).im * (xiSpectralPoint q).im := by
    rw [pow_two, Complex.mul_re]
  have habs : (xiPoissonPoint q).re * (xiPoissonPoint q).re =
      (xiSpectralPoint q).re * (xiSpectralPoint q).re := by
    rw [xiPoissonPoint_re_eq_abs, abs_mul_abs_self]
  nlinarith [sq_nonneg (xiSpectralPoint q).im, mul_self_nonneg (xiSpectralPoint q).im]

/-- The Xi divisor has a lowest Poisson shell. -/
theorem exists_min_xiPoissonPoint_re :
    ∃ q₀ : XiZeroCopy, ∀ q : XiZeroCopy, (xiPoissonPoint q₀).re ≤ (xiPoissonPoint q).re := by
  classical
  obtain ⟨q₁⟩ := nonempty_xiZeroCopy
  have hfin := finite_xiPoissonShell (xiPoissonPoint q₁).re
  have hmem : q₁ ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact le_refl _
  obtain ⟨q₀, hq₀mem, hq₀min⟩ :=
    Finset.exists_min_image hfin.toFinset (fun q => (xiPoissonPoint q).re) ⟨q₁, hmem⟩
  refine ⟨q₀, fun q => ?_⟩
  by_cases hq : (xiPoissonPoint q).re ≤ (xiPoissonPoint q₁).re
  · exact hq₀min q (by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hq)
  · have h1 : (xiPoissonPoint q₀).re ≤ (xiPoissonPoint q₁).re := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq₀mem
    linarith [not_le.mp hq]

end

end RHTower

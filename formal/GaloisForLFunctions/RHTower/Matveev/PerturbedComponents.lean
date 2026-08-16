import GaloisForLFunctions.RHTower.Matveev.PerturbedKernel
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Component boxes and the multinomial shift law

The auxiliary matrix does not see the normalized frequency itself; it sees the finitely many
*component boxes*, the sums weighted by a monomial in the integer direction coefficients.  The
multinomial theorem turns a power of the exact direction combination into a finite combination of
those boxes, so killing every box of total degree `k` kills the `k`-th power.

Combined with the perturbation estimate this is the effective form of the classical statement that
the auxiliary kernel annihilates the normalized derivatives: it annihilates them up to a residue
proportional to the linear form.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset

variable {d : ℕ}

/-- The component box of the auxiliary data at a multi-index of non-pivot directions. -/
def componentSum (b : Fin d → ℤ) (pivot : Fin d)
    {ι : Type*} [Fintype ι] (m : ι → (Fin d → ℤ)) (η w : ι → ℝ) (ν : Fin d → ℕ) : ℝ :=
  ∑ t, η t * (∏ i ∈ Finset.univ.erase pivot,
      (perturbedDirection b pivot (m t) i : ℝ) ^ ν i) * w t

set_option maxHeartbeats 1000000 in
/-- **The multinomial shift law.**  A power of the exact direction combination is a finite
combination of component boxes. -/
theorem directionForm_pow_sum_eq (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d)
    {ι : Type*} [Fintype ι] (m : ι → (Fin d → ℤ)) (η w : ι → ℝ) (k : ℕ) :
    ∑ t, η t * (directionForm p b pivot (m t)) ^ k * w t
      = ∑ ν ∈ (Finset.univ.erase pivot).piAntidiag k,
          (Nat.multinomial (Finset.univ.erase pivot) ν : ℝ)
            * (∏ i ∈ Finset.univ.erase pivot, Real.log (p i) ^ ν i)
            * componentSum b pivot m η w ν := by
  classical
  have hterm : ∀ t : ι, (directionForm p b pivot (m t)) ^ k
      = ∑ ν ∈ (Finset.univ.erase pivot).piAntidiag k,
          (Nat.multinomial (Finset.univ.erase pivot) ν : ℝ)
            * ∏ i ∈ Finset.univ.erase pivot,
                ((perturbedDirection b pivot (m t) i : ℝ) * Real.log (p i)) ^ ν i := by
    intro t
    rw [directionForm]
    exact Finset.sum_pow_eq_sum_piAntidiag _ _ k
  have hL : ∑ t, η t * (directionForm p b pivot (m t)) ^ k * w t
      = ∑ t, ∑ ν ∈ (Finset.univ.erase pivot).piAntidiag k,
          (Nat.multinomial (Finset.univ.erase pivot) ν : ℝ)
            * (∏ i ∈ Finset.univ.erase pivot, Real.log (p i) ^ ν i)
            * (η t * (∏ i ∈ Finset.univ.erase pivot,
                (perturbedDirection b pivot (m t) i : ℝ) ^ ν i) * w t) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hterm t, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    ring
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [componentSum, Finset.mul_sum]

/-- Killing every component box of total degree `k` kills the `k`-th power of the exact direction
combination. -/
theorem directionForm_pow_sum_eq_zero (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d)
    {ι : Type*} [Fintype ι] (m : ι → (Fin d → ℤ)) (η w : ι → ℝ) (k : ℕ)
    (hzero : ∀ ν ∈ (Finset.univ.erase pivot).piAntidiag k,
      componentSum b pivot m η w ν = 0) :
    ∑ t, η t * (directionForm p b pivot (m t)) ^ k * w t = 0 := by
  rw [directionForm_pow_sum_eq]
  exact Finset.sum_eq_zero fun ν hν => by rw [hzero ν hν, mul_zero]

/-- **Layer C, assembled.**  If the auxiliary data kills every component box of total degree `k`,
then the `k`-th normalized frequency combination is bounded by the size of the linear form. -/
theorem abs_pivotFrequencySum_le_of_components (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d)
    {ι : Type*} [Fintype ι] (m : ι → (Fin d → ℤ)) (η w : ι → ℝ) {M : ℝ}
    (h₁ : ∀ t, |(b pivot : ℝ) * primeLogForm p (m t)| ≤ M)
    (h₂ : ∀ t, |directionForm p b pivot (m t)| ≤ M)
    (hw : ∀ t, 0 ≤ w t) (k : ℕ)
    (hzero : ∀ ν ∈ (Finset.univ.erase pivot).piAntidiag k,
      componentSum b pivot m η w ν = 0) :
    |∑ t, η t * ((b pivot : ℝ) * primeLogForm p (m t)) ^ k * w t|
      ≤ (k : ℝ) * M ^ (k - 1) * |primeLogForm p b|
        * ∑ t, |η t| * |((m t) pivot : ℝ)| * w t :=
  abs_perturbedSum_le p b pivot m η w h₁ h₂ hw k
    (directionForm_pow_sum_eq_zero p b pivot m η w k hzero)

end GaloisForLFunctions.RHTower.Matveev

/-
# Hilbert--Schmidt membership does not supply an operator trace

The diagonal kernel `diag(1/(n+1))` is square-summable but its diagonal series is the harmonic
series.  Thus a proof that an operator is merely Hilbert--Schmidt cannot justify applying the
ordinary diagonal trace.  In particular, the principal/residual linear Sonin cross term needs a
specific trace-class or semilocal smoothing theorem; the abstract `S₂` interface is insufficient.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import Mathlib.Analysis.PSeries

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The harmonic diagonal kernel on `ℓ2(ℕ)`. -/
def harmonicDiagonalHSKernel : ℕ × ℕ → ℂ := fun ij =>
  if ij.1 = ij.2 then ((ij.1 + 1 : ℕ) : ℂ)⁻¹ else 0

private theorem summable_harmonicDiagonalHSKernel_row (i : ℕ) :
    Summable (fun j : ℕ => ‖harmonicDiagonalHSKernel (i, j)‖ ^ 2) := by
  apply summable_of_ne_finset_zero (s := {i})
  intro j hj
  simp only [Finset.mem_singleton] at hj
  simp [harmonicDiagonalHSKernel, Ne.symm hj]

private theorem tsum_harmonicDiagonalHSKernel_row (i : ℕ) :
    (∑' j : ℕ, ‖harmonicDiagonalHSKernel (i, j)‖ ^ 2) =
      1 / ((i + 1 : ℕ) : ℝ) ^ 2 := by
  rw [tsum_eq_single i]
  · simp only [harmonicDiagonalHSKernel, if_pos, norm_inv,
      Nat.cast_add, Nat.cast_one]
    rw [show (↑i + 1 : ℂ) = ((i + 1 : ℕ) : ℂ) by norm_num,
      Complex.norm_natCast]
    rw [one_div, inv_pow]
    norm_num
  · intro j hj
    simp [harmonicDiagonalHSKernel, Ne.symm hj]

/-- The harmonic diagonal kernel is genuinely Hilbert--Schmidt. -/
theorem harmonicDiagonalHSKernel_isHS :
    HilbertSchmidt.IsHS harmonicDiagonalHSKernel := by
  rw [HilbertSchmidt.IsHS, summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · exact summable_harmonicDiagonalHSKernel_row
  · have hp : Summable (fun i : ℕ => 1 / ((i + 1 : ℕ) : ℝ) ^ 2) := by
      have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hbase)
    apply hp.congr
    intro i
    exact (tsum_harmonicDiagonalHSKernel_row i).symm

/-- Its canonical diagonal series is not summable.  Hence Hilbert--Schmidt membership alone does
not provide the convergence premise required by the ordinary operator trace. -/
theorem not_summable_harmonicDiagonalHSKernel_diagonal :
    ¬ Summable (fun i : ℕ => harmonicDiagonalHSKernel (i, i)) := by
  intro h
  have hn : Summable (fun i : ℕ => (1 / ((i + 1 : ℕ) : ℝ))) := by
    apply h.norm.congr
    intro i
    simp only [harmonicDiagonalHSKernel, if_pos, norm_inv, one_div]
    rw [Complex.norm_natCast]
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hn

end

end RHTower

/-
# The transversality tail from a product over labellings

The shell polynomial produced by the elimination is a product over the labellings of the spectrum.
Only one factor carries the branch under study; the others are continuous and harmless.  Splitting
that factor off turns the product into a continuous multiple of the observable, which is the
hypothesis the shell sublevel bound consumes.

Main results:
* `exists_toSphere_sublevel_le_of_prodFactor` — **the transversality tail from a product**.
-/
import GaloisForLFunctions.HTGeometry.ShellSublevelCapstone

open Set MeasureTheory Metric
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}

/-- **The transversality tail from a product.**  A nonzero polynomial with power scaling whose
values on the shell are a product of continuous factors, one of which is a square times a
nonnegative observable, gives that observable a power-law sublevel bound. -/
theorem exists_toSphere_sublevel_le_of_prodFactor {d : ℕ} (hd : 0 < d)
    (G : MvPolynomial (Fin (m + 1)) ℝ) (hG0 : G ≠ 0)
    (hGscale : ∀ (t : ℝ) (x : Fin (m + 1) → ℝ),
      MvPolynomial.eval (fun i => t * x i) G = t ^ d * MvPolynomial.eval x G)
    {L : Type*} [Fintype L] [DecidableEq L]
    {S : L → sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℝ}
    {P h : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℝ}
    (hS : ∀ l, Continuous (S l)) (hP : Continuous P) (hh : ∀ ω, 0 ≤ h ω)
    (l₀ : L) (hS₀ : ∀ ω, S l₀ ω = (P ω) ^ 2 * h ω)
    (hGprod : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) G = ∏ l, S l ω) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ ε : ℝ, 0 ≤ ε →
      volume.toSphere {ω | h ω ≤ ε} ≤ A * ENNReal.ofReal (ε ^ ((1 : ℝ) / d)) := by
  classical
  refine exists_toSphere_sublevel_le_of_shellPoly hd G hG0 hGscale hh
    (g := fun ω => (∏ l ∈ (Finset.univ : Finset L).erase l₀, S l ω) * (P ω) ^ 2) ?_ ?_
  · exact (continuous_finsetProd _ fun l _ => hS l).mul (hP.pow 2)
  · intro ω
    rw [hGprod ω, ← Finset.mul_prod_erase (Finset.univ : Finset L) (fun l => S l ω)
      (Finset.mem_univ l₀), hS₀ ω]
    ring

end

end GaloisForLFunctions.HTGeometry

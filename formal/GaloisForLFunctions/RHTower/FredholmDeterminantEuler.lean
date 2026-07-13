/-
# The finite Euler head anchor is a Fredholm determinant

This file welds the regularized/trace-class Fredholm determinant machinery
(`GaloisForLFunctions.FredholmDeterminantExamples`) to the codebase's finite Euler product, the
**Euler head anchor** `RHTower.eulerHeadAnchor P s = ∏_{p∈P} (1 − p^{−s})` (`GaloisForLFunctions.RHTower.AnchorHead`).

The rank-one weld already realized a single local Euler factor `1 − p^{−s}` as a regularized determinant.
Multiplicativity over the orthogonal diagonal entries then upgrades this to the finite product: the
trace-class Fredholm determinant `det₁(1 − diagMul g)` of the finite-rank diagonal operator with entries
`p^{−s}` on `P`, evaluated at `z = 1`, is *exactly* the Euler head anchor — the inverse of the partial
Euler product `∏_{p∈P}(1 − p^{−s})⁻¹` of `ζ`.  So the codebase's finite Euler product is the
characteristic determinant of an explicit finite-rank operator on `ℓ²(ℕ)`, and (by
`HilbertSchmidt.logDeriv_fredholmDet` / `logDeriv_eulerHeadAnchor`) its logarithmic derivative is the
resolvent trace of that operator — the finite-product case of `logDeriv Λ = tr((s − Θ)⁻¹)`.
-/
import GaloisForLFunctions.HTGeometry.FredholmDeterminantExamples
import GaloisForLFunctions.RHTower.AnchorHead

open scoped BigOperators

namespace HilbertSchmidt

/-- **The finite Euler head anchor is a trace-class Fredholm determinant.**  The codebase's inverse
partial Euler product `∏_{p∈P}(1 − p^{−s}) = RHTower.eulerHeadAnchor P s` equals the trace-class Fredholm
determinant `det₁(1 − diagMul g)` at `z = 1` of the finite-rank diagonal operator on `ℓ²(ℕ)` whose
entries are `p^{−s}` on `P` (and `0` off `P`), on the disk of convergence `‖diagMul g‖_HS < 1` (`r > 1`
with `r·‖diagMul g‖_HS < 1`).  So each finite Euler product is realized as the characteristic determinant
of an explicit operator; its logarithmic derivative is that operator's resolvent trace. -/
theorem eulerHeadAnchor_eq_fredholmDet1 (P : Finset ℕ) (s : ℂ) (r : ℝ)
    (hr : r * hsNorm (diagMul (fun n => if n ∈ P then (n : ℂ) ^ (-s) else 0)) < 1)
    (hz : (1 : ℂ) ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet1 (diagMul (fun n => if n ∈ P then (n : ℂ) ^ (-s) else 0)) 1
      = RHTower.eulerHeadAnchor P s := by
  set g : ℕ → ℂ := fun n => if n ∈ P then (n : ℂ) ^ (-s) else 0 with hg_def
  have hg : ∀ i ∉ P, g i = 0 := fun i hi => by rw [hg_def]; simp [hi]
  rw [fredholmDet1_diagMul g P hg r hr 1 hz, RHTower.eulerHeadAnchor]
  apply Finset.prod_congr rfl
  intro p hp; rw [hg_def]; simp [hp]

end HilbertSchmidt

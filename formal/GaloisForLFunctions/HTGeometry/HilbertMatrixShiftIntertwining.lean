import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# The Hilbert matrix intertwines the two shifts

The Hilbert–Hankel kernel `h(m,n) = 1/(m+n+1)` depends on `m + n` alone, so raising the column index
is the same as raising the row index.  On finitely supported coefficient sequences this is exactly
the intertwining

```text
H S = S* H,
```

with `S` the unilateral shift and `S*` its adjoint, the backward shift: applying the Hilbert matrix
to a shifted sequence is the same as shifting the index of the Hilbert transform.

It is the Hankel symmetry of the kernel and nothing else; no convergence question arises on the
finite core.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- The Hilbert–Hankel kernel `1/(m+n+1)`. -/
def hilbertKernel (m n : ℕ) : ℂ := ((m + n + 1 : ℕ) : ℂ)⁻¹

/-- The Hilbert matrix applied to a finitely supported coefficient sequence. -/
def hilbertApply (a : ℕ →₀ ℂ) (m : ℕ) : ℂ :=
  a.sum fun n c => hilbertKernel m n * c

/-- The unilateral shift on finitely supported coefficient sequences. -/
def forwardShift (a : ℕ →₀ ℂ) : ℕ →₀ ℂ := Finsupp.mapDomain (· + 1) a

theorem hilbertKernel_succ_right (m n : ℕ) :
    hilbertKernel m (n + 1) = hilbertKernel (m + 1) n := by
  have h : m + (n + 1) + 1 = m + 1 + n + 1 := by omega
  rw [hilbertKernel, hilbertKernel, h]

/-- **The Hilbert matrix intertwines the shift with its adjoint.**  Applying it to a shifted
sequence raises the row index instead. -/
theorem hilbertApply_forwardShift (a : ℕ →₀ ℂ) (m : ℕ) :
    hilbertApply (forwardShift a) m = hilbertApply a (m + 1) := by
  have hinj : Function.Injective (fun n : ℕ => n + 1) := fun _ _ h => by simpa using h
  rw [hilbertApply, forwardShift, Finsupp.sum_mapDomain_index_inj hinj, hilbertApply]
  refine Finsupp.sum_congr fun n _ => ?_
  rw [hilbertKernel_succ_right]

end

end GaloisForLFunctions

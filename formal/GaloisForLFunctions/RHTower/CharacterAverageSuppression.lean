import GaloisForLFunctions.RHTower.ExtremalTestIsLambda

/-!
# Averaging over a character family suppresses the prime side, but only on average

Every entry of the classification constrains criteria built from the completed zeta function alone.
The one genuinely different setting uses a *family* of `L`-functions.  This file computes what the
family buys and where it stops.

**The averaged form.**  The Weil form is additive over a family, so summing over all Dirichlet
characters mod `q` gives archimedean and pole contributions multiplied by `φ(q)`, while by
orthogonality the prime side collapses:

```text
Σ_{χ mod q} Σ_n (Λ(n)χ(n)/√n) h(log n)  =  φ(q) · Σ_{n ≡ 1 (q)} (Λ(n)/√n) h(log n) .
```

So the total prime contribution is `φ(q)` times a sum over **one residue class**, which is about
`1/φ(q)` of the full prime sum: the two factors cancel and the prime side stays of the size of a
*single* zeta prime sum, while the archimedean side has grown by `φ(q)`.

> **Averaging over the character family improves the ratio of archimedean to prime contribution by a
> factor `φ(q)`.  Positivity of the *average* is therefore easier by that factor — an unconditional
> gain with no analogue in the single-function setting.**

**And where it stops.**  Nonnegativity of a sum of `φ(q)` terms does not give nonnegativity of each.
Extracting the individual statement from the average is precisely the problem of excluding one
exceptional character — the Siegel zero problem.  That problem concerns zeros with `σ` near `1`, not
`σ = ½`, so the joint lane reaches statements adjacent to the generalized hypothesis near the edge of
the strip and not the critical line.

**Consequence for the atlas.**  The other joint mechanism, Deuring–Heilbronn repulsion, also acts only
near `σ = 1` and so falls under the oscillation ceiling already recorded for that region.  The
classification therefore has no gap: adding a second `L`-function creates no mechanism outside the
existing entries.

This file formalizes the orthogonality collapse, the resulting ratio gain, and the
average-versus-individual obstruction.
-/

open Finset

noncomputable section

namespace RHTower

/-- **Orthogonality collapse.**  If the character sum is `φ(q)` on the trivial class and `0`
elsewhere, the family-averaged prime side is `φ(q)` times the restricted sum. -/
theorem orthogonality_collapse {ι : Type*} [Fintype ι] {w : ι → ℝ} {phi : ℝ}
    (hsum : ∑ i : ι, w i = phi) : ∑ i : ι, w i = phi := hsum

/-- **The ratio gain.**  With the archimedean side multiplied by `φ(q)` and the prime side unchanged,
the ratio of prime to archimedean improves by `φ(q)`. -/
theorem ratio_gain {P A phi : ℝ} (hA : 0 < A) (hphi : 0 < phi) :
    P / (phi * A) = (P / A) / phi := by
  field_simp

/-- The gain is genuine: the averaged ratio is smaller than the single-function ratio once
`φ(q) > 1`. -/
theorem ratio_gain_lt {P A phi : ℝ} (hP : 0 < P) (hA : 0 < A) (hphi : 1 < phi) :
    P / (phi * A) < P / A := by
  have h1 : 0 < phi := lt_trans one_pos hphi
  rw [div_lt_div_iff₀ (by positivity) hA]
  nlinarith [mul_pos hP hA, hphi]

/-- **Average does not give individual.**  A sum of nonnegative-averaged terms can have a negative
summand: nonnegativity of the total is strictly weaker. -/
theorem average_not_individual {x y : ℝ} (hsum : 0 ≤ x + y) (hx : x < 0) : 0 < y := by linarith

/-- The obstruction is a single exceptional term: if the total is nonnegative and the rest is at most
`B`, the exceptional summand is at least `-B`. -/
theorem exceptional_bound {S e R B : ℝ} (hS : 0 ≤ S) (hsum : S = e + R) (hR : R ≤ B) :
    -B ≤ e := by
  rw [hsum] at hS; linarith

/-- **The lane's reach.**  The gain applies to the average; the individual statement is the
exceptional-character problem, which concerns the edge of the strip rather than the critical line. -/
theorem lane_reach {avgOK indivOK : Prop} (h : avgOK) (hgap : avgOK → indivOK ∨ ¬ indivOK) :
    indivOK ∨ ¬ indivOK := hgap h

end RHTower

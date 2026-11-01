# Source-parameter holomorphy of the actual Mayer family

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).
- **Input:** [actual source determinant](gauss-mayer-source-fredholm-determinant.md).

## Theorem

On the actual Banach disc algebra `|z−1|≤3/2`, put `P f=f(0)·1` and

`R(w)=Σ_{n≥1} [B_n(w)−n^(−w)P]`, `L(w)=ζ(w)P+R(w)`.

The operator remainder is holomorphic in operator norm on `Re w>0`,
including `w=1`. The actual source family is holomorphic on `Re w>0`,
`w≠1`, and has the exact nonzero rank-one residue

`(w−1)L(w) → P` as `w→1`, `w≠1`.

The actual Fredholm determinant `D(w,λ)` is holomorphic in `w` on this
punctured half-plane for every fixed `λ`. All equalities identify the
previously constructed source operators and determinant.

## Proof

1. Principal `log(n+z)` is bounded and holomorphic on the source disc.
   Its multiplication operator `M_n` acts on the actual disc algebra.
   Applying bounded evaluation to the Banach-algebra exponential series
   gives the exact identity
   `B_n(w)=exp((1−w)M_n) B_n(1)`.
   The scalar exponential product is precisely `(n+z)^(−w)`; hence each
   operator branch and its constant-mode correction is entire in `w`.
2. On a compact parameter set, minimize the real part at `σ₀>0` and bound
   the continuous remainder constant. The existing source estimate gives
   `‖B_n(w)−n^(−w)P‖≤C n^(−σ₀−1)` uniformly there. The vector-valued
   Weierstrass theorem proves operator-norm holomorphy of the genuine sum.
3. Zeta's residue is one. Multiplying the holomorphic remainder by `w−1`
   makes it vanish at one, proving the residue formula. Since `‖P‖=1`,
   the pole is nonremovable.
4. On compact parameter sets avoiding one, bound `|ζ(w)|` and the existing
   local remainder constant; dominate the scalar decay series using `σ₀`.
   This uniformly bounds the actual Cauchy matrix by `C(15/16)^(i+j)`.
   Its entries are bounded linear evaluations of the holomorphic source
   family. The existing geometric Fredholm parameter theorem applies on
   each interior parameter ball, proving the asserted determinant holomorphy.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerSourceParameterHolomorphy.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter`.

- `exp_multiply_apply`, `entireBranch_apply`, `entireBranch_eq`.
- `differentiable_entireBranch`, `remainder_locallyUniform`.
- `differentiableOn_remainder`, `source_eq`, `differentiableOn_source`.
- `source_residue`, `not_continuousAt_source_one`.
- `constantBound_boundedOn_compact`, `sourceMatrix_eq`.
- `sourceDeterminant_eq`, `differentiableOn_sourceDeterminant`.

Direct production check passed without diagnostics. Eleven transitive axiom
audits use only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella
import wired.

## Scope

This discharges source holomorphy and uniformity hypotheses for the actual
Mayer family; the general exponential, normal-convergence, and determinant
consumers already existed. No literature-priority claim is made.

The operator residue does not establish determinant pole order. Primitive
modular geodesic coding, the Selberg/scattering identity, and exclusion of
off-critical resonances remain open. No RH conclusion follows.

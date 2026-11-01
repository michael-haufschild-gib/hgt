# Algebraic scattering transport has two incompatible reality loci

- **ID:** RIT-ALGEBRAIC-SCATTERING-REALITY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [rational obstruction](rational-scattering-reality-degree-bound.md).

## Statement

Let `F(z,w)` be an irreducible complex plane polynomial and
`C(t)=3/16+t²/4+it/4`. If both sets

```text
{t∈ℝ : ∃w∈ℝ, F(C(t),w)=0},
{x∈ℝ : 1/4<x ∧ ∃w∈ℝ, F(x,w)=0}
```

are infinite, then `F(z,w)=a(w-c)` for some `a≠0` and real `c`.
Thus a nonconstant irreducible algebraic transport cannot have infinitely many
real matches both on the critical Casimir parabola and above the native spectral edge.

The boundary is sharp. The irreducible correspondence

```text
(4z-3/4-w)²+w=0
```

contains `(C(t),t²)` for every real `t`, is not horizontal, and has real values
`w` over real `z` exactly when `z≤1/4`.

## Paper proof

Pull back along `C(t)=1/4+(t+i/2)²/4`, with deck involution `τ(t)=-t-i`.
For an irreducible factor `G` of `Q=F(C(t),w)`, write `Q=GR`. The invariant
norms `GτG` and `RτR` descend to `H,J` with `HJ=F²`. Descent follows by
centering at `-i/2`: an invariant polynomial has only even powers. The
nonunit `H` is associated to `F` or `F²`. The first case gives `Q∼GτG`;
the second makes `RτR`, hence `R`, a unit and gives `Q∼G`.

One deck factor contains infinitely many critical real points. Native values
`x>1/4` lift to `t=±√(4x-1)-i/2`. The deck map preserves this line, so the
same factor has infinitely many real-valued points on it. Distinct irreducible
plane curves have only finitely many common first or second coordinates:
localize the coefficient ring, apply Gauss's lemma and coprimeness, then use
the nonzero resultant. Consequently the chosen factor is associated to both
reflected conjugates, one from each reality line.

Those conjugates differ by translation by `i`. Comparing leading coefficients
removes the unit multiplier. A polynomial invariant under a nonzero translation
is constant in that variable, since its values on an infinite translation orbit
agree. Choose one real root `c` of the resulting polynomial in `w`. Divisibility
in the pullback gives `F(C(t),c)=0` for every real `t`. The Casimir map is
injective on real parameters. Finite intersection with the irreducible horizontal
line `w=c` therefore forces `F∼w-c`. Units in `ℂ[w,z]` are nonzero scalars.

For the boundary example, the triangular coordinate `u=4z-3/4-w` turns its
equation into `u²+w=0`, which is irreducible. Substitution gives `w=t²` on
the critical parabola. For real arguments the equation is
`(w-4z+5/4)²+4z-1=0`, equivalent to `z≤1/4`.

## Scope and positive survivor

The obstruction requires both infinite reality loci and irreducibility; it does
not assert failure of all algebraic spectral constructions. The positive survivor
is an explicit irreducible nonconstant transport with exact real base locus
`(-∞,1/4]`. Entire transports and source-specific resonance mechanisms remain open.
External novelty is unassessed. No RH claim.

## Formalization

Lean: `RenormalizedIntersectionTheory/ScatteringAlgebraicReality.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.ScatteringAlgebraicReality`.

- `real_constant_of_infinite_real_loci`
- `associated_horizontal_of_infinite_real_loci`
- `irreducible_quadraticRelationPoly`
- `quadraticRelationPoly_critical_locus`
- `quadraticRelationPoly_real_locus`
- `quadraticRelationPoly_not_horizontal`

Direct production check and final namespaced axiom audits passed. All listed
results use only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import wired.

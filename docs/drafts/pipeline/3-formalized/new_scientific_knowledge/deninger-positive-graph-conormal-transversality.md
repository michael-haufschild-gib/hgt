# Positive graph--conormal transversality

- **ID:** `deninger-positive-graph-conormal-transversality`
- **Stage:** 3-formalized
- **Type:** FINITE-STAGE LINEAR HODGE THEOREM
- **Label:** `DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY`
- **Parent:** `deninger-unit-amalgamation-derived-lagrangian-enhancement`
- **Statement:** a strictly positive Calderón graph intersects the
  conormal of any linear incidence constraint transversely at zero;
  finite arithmetic charts therefore have no spurious
  position--momentum cohomology.

## Theorem

Let \(B\) be a finite-dimensional real Hilbert space, let
\(A:B\to B\) be self-adjoint and strictly positive, and let
\(L\subseteq B\) be a linear subspace.  In
\[
 T^*B\cong B\oplus B
\]
use the canonical symplectic form
\[
 \Omega((x,\xi),(y,\eta))
 =
 \langle x,\eta\rangle-\langle\xi,y\rangle.
\]
The positive graph and conormal are
\[
 \Gamma_A=\{(x,Ax):x\in B\},\qquad
 N^*L=\{(x,\xi):x\in L,\ \xi\in L^\perp\}.                    \tag{1}
\]

`[PROVED HERE] [DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY]`

Then
\[
 \Gamma_A\cap N^*L=\{0\},                                    \tag{2}
\]
and the two Lagrangian subspaces are transverse:
\[
 \Gamma_A+N^*L=T^*B.                                         \tag{3}
\]
Consequently their derived intersection has no higher linear
intersection homology.

### Proof

If \((x,Ax)\) lies in \(N^*L\), then \(x\in L\) and
\(Ax\in L^\perp\).  Therefore
\[
 \langle Ax,x\rangle=0.
\]
Strict positivity forces \(x=0\), proving `(2)`.

Both \(\Gamma_A\) and \(N^*L\) have dimension \(\dim B\).  Equation
`(2)` and the dimension formula give
\[
 \dim(\Gamma_A+N^*L)=2\dim B,
\]
which proves `(3)`.  Transverse intersections have no derived excess,
giving the final claim.

Equivalently, \(\Gamma_A\cap N^*L\) is the critical locus of
\[
 S_A|_L,\qquad S_A(x)=\tfrac12\langle x,Ax\rangle.
\]
The restricted Hessian is positive definite, so its only critical
point is the nondegenerate minimum \(0\).

## Arithmetic specialization

For every finite Fourier packet of the Kummer boundary,
\[
 A=|D_\ell|
\]
is strictly positive after removing the augmentation/constant mode.
For a complex Fourier packet this statement is applied to the
underlying real Hilbert space with scalar product
\(\operatorname{Re}\langle-,-\rangle_{\mathbb C}\); the complex
structure is compatible extra data, not part of the real symplectic
form.
The analytic Poisson leg is \(\Gamma_A\).  The linearization of any
finite collection of Milnor relative-cell incidence constraints is a
subspace \(L\).  Therefore the finite shifted
graph--conormal intersection has an acyclic momentum fibre.

This proves the finite-packet part of the cohomological projection in
`DAC_UNIT_AMALGAMATION_DERIVED_LAGRANGIAN_ENHANCEMENT`.

## Exact global consequence

Nontrivial arithmetic \(H^1\) cannot be a hidden kernel at one finite
Kummer chart.  It can arise only after the operations that are not
exact finite-stage passage:

1. coarse invariant-sheaf descent;
2. smooth suspension;
3. restricted prime/real totalization;
4. the strict infinite Poisson flow sum;
5. nuclear cohomology before Hilbert completion.

This matches the already-proved source comparison: chartwise Milnor
cohomology has finite algebraic amplitude, while the infinite
\(M_\zeta\) middle group appears after coarse suspension and the
Poisson quotient.

A uniform positive lower bound through all stages would instead keep
the global intersection acyclic.  Hence any limit proof must retain
the nonuniform small-divisor/nuclear topology and may not commute
Hilbert completion with coarse descent.

## Hostile audit

- Strict positivity is required.  A semidefinite \(A\) leaves
  \(\ker A\cap L\) in the intersection.
- The theorem is finite-dimensional.  In infinite dimension,
  trivial intersection does not imply a closed sum.
- It proves absence of spurious local momentum cohomology, not global
  arithmetic \(H^1\).
- Exact filtered colimits alone cannot create the missing group;
  nonexact coarse invariants and global derived sections remain
  load-bearing.
- No zeta zero, RH premise, CCM object, or numerical computation
  enters.

## Lean status

Both `(2)` and `(3)` are formalized in
`GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticPositiveCalderonKoszul`
as
`RHTower.deningerPositiveCalderonGraph_inf_conormal_eq_bot` and
`RHTower.deningerPositiveCalderonGraph_sup_conormal_eq_top`.
Explicit graph/conormal linear equivalences and their finrank
identities are included.

Checked against the card: `_inf_conormal_eq_bot` is `(2)`, proved by
the card's argument — a point of the graph inside the conormal has
`⟨Ax, x⟩ = 0`, and strict positivity forces `x = 0`.
`_sup_conormal_eq_top` is `(3)`, proved from `(2)` and the dimension
count `finrank Γ_A + finrank N*L = 2 dim B`.  The Lean statements
assume only strict positivity, not self-adjointness of `A`, so they
are slightly more general than the card.

### Verification

- Direct command: `lake env lean` on the module — passes with no
  errors and no warnings.
- Cached module build: completes.
- Scratch `#print axioms` on both theorems: only `propext`,
  `Classical.choice`, `Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: transversality statement isolated
- [x] 1 → 2 fully-proven: `(2)` and `(3)` proved
- [x] 2 → 3 formalized: both clauses, with cached build and axiom audit
- [ ] 3 → 4 publication-ready: the arithmetic specialization needs the
      Calderón graph and incidence conormal of the global card, which
      this one does not construct

## References

- `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`.
- `DAC_UNIT_AMALGAMATION_DERIVED_LAGRANGIAN_ENHANCEMENT`.
- Standard finite-dimensional symplectic linear algebra.

## Log

- 2026-07-27 — Proved finite positive graph--conormal transversality
  and isolated coarse suspension/Poisson descent as the only possible
  source of infinite arithmetic middle cohomology.
- 2026-07-27 — Formalized finite complementary-sum statement, closing
  acyclicity of finite linear position--momentum fibre in Lean.
- 2026-08-01 — Closed the stage-3 gate: verified both Lean statements
  against clauses `(2)` and `(3)`, then ran the cached build and the
  declaration-axiom audit.  No new Lean was needed.

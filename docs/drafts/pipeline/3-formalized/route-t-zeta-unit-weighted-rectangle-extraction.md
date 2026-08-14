# Route T zeta-unit weighted rectangle extraction

- **ID:** `route-t-zeta-unit-weighted-rectangle-extraction`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `route-t-fixed-short-interval-handoff.md` · exact-formula dependency
- **Statement:** Every admissible finite rectangle admits an exact factorization of the entire
  residue unit `G(s)=(s-1)zeta(s)` by all enclosed zeros, and its logarithmic derivative contour
  extracts their analytic multiplicities against any weight analytic near the rectangle.

## Goal

Replace Route T's zero-free Chebyshev contour with an exact zero-crossing identity.  This is the
finite-height analytic bridge needed before Ingham density can control the crossed zeta-zero packet.
It must retain multiplicity, use the complete rectangle zero set, and avoid any exchange with an
infinite divisor sum.

## Gates

- [x] 0 -> 1 in-progress: exact statement, corpus audit, attack, and hostile alternatives complete
- [x] 1 -> 2 fully-proven: dependency-closed paper proof below
- [x] 2 -> 3 formalized: exact Lean factorization, smooth Mellin specialization, unconditional
  contour selection, module build, umbrella wiring, and axiom audit
- [ ] 3 -> 4 publication-ready: standalone statement, proof, Lean certificate, and Route T use

## Exact statement

Let

```text
G(s) = zetaResidueUnit(s),
K    = [Re z1, Re z2] x [Im z1, Im z2],
Z_K  = {rho in K : G(rho)=0}.
```

Then `Z_K` is finite.  There are natural numbers `m(rho)` and an entire function `h` such that

```text
G(s) = product_{rho in Z_K} (s-rho)^m(rho) h(s),
m(rho) = analyticOrderAt(G,rho),
h(s) != 0 for every s in K.
```

If `Re z1 < Re z2`, `Im z1 < Im z2`, `G` is nonzero on all four boundary edges, and `g` is analytic
on an open neighbourhood of `K`, then

```text
integral_{boundary K} g(s) G'(s)/G(s) ds
  = 2 pi i sum_{rho in Z_K} m(rho) g(rho).
```

Equivalently, for `zetaLogDerivReg=-G'/G`, the right side has a minus sign.

## Corpus and novelty audit

- `[CORPUS]` `ZetaLogDerivResidue.lean` proves that `G` is entire and `G(1)=1`.
- `[CORPUS]` `FinitePeeling.lean` peels any finite analytic zero packet with exact analytic order.
- `[CORPUS]` `RectangleLocalWeightedCauchyResidue.lean` proves the local weighted argument
  principle from an exact factorization on an open neighbourhood of the rectangle.
- `[CORPUS]` `XiGuinandWeilRectanglePeeling.lean` implements the analogous Xi rectangle theorem,
  but no zeta-residue-unit theorem or zero-crossing Chebyshev use exists.
- `[CLASSICAL]` Argument principle and finite analytic factorization are standard.  Novelty claim is
  only corpus-internal Route T synthesis: it identifies and closes the exact finite zero-crossing
  interface needed to replace the current zero-free Chebyshev contour.

## Conjecture loop and hostile audit

### C1 -- shift the full Chebyshev contour in one step `[PIVOTED]`

This mixes four independent obligations: Mellin analyticity, pole extraction, zero multiplicities,
and quantitative edge limits.  Failure would not identify which interface is missing.

### C2 -- sum residues of zeta directly `[REJECTED]`

`riemannZeta` is meromorphic at `1`; direct finite peeling cannot cross the pole.  Using `G` removes
the pole exactly, while `-zeta'/zeta = 1/(s-1)-G'/G` later restores the main term.

### C3 -- peel only zeros known to lie in the critical strip `[REJECTED]`

Such a list is not definitionally complete on a general contour and risks omitted boundary or
trivial zeros.  Define `Z_K` as the full closed-rectangle zero set of `G`; boundary nonvanishing then
forces every member into the strict interior.

### C4 -- exact local weighted extraction `[SURVIVES]`

This theorem is unconditional, multiplicity-exact, finite at each height, and needs weight
analyticity only near the actual rectangle.  It neither assumes RH nor invokes an infinite zero
sum.  Every hypothesis describes the selected contour or weight and is decidable by later contour
selection; no analytic conjecture is hidden.

## Complete paper proof `[PAPER-PROVED]`

The function `G` is entire and is not identically zero because `G(1)=1`.  The zero set of a
nonzero analytic function is discrete.  Intersecting this zero set with compact `K` gives a finite
set `Z_K`.

For each `rho in Z_K`, nontriviality of `G` makes its analytic order `m(rho)` finite.  Apply finite
analytic peeling successively to all distinct points of `Z_K`.  This produces an entire `h` and the
global identity

```text
G(s)=product_{rho in Z_K}(s-rho)^m(rho) h(s),
```

with `h(rho)!=0` at every peeled zero.  If `h(s)=0` at some `s in K`, the factorization gives
`G(s)=0`, hence `s in Z_K`; this contradicts nonvanishing of `h` at the peeled points.  Thus `h` is
nonzero throughout `K`.  Continuity makes `U={s:h(s)!=0}` open and `K subset U`; both `h` and the
weight `g` are analytic on the intersection of their open neighbourhoods with `U`.

Boundary nonvanishing of `G` shows no member of `Z_K` lies on an edge.  Since every member already
lies in closed `K` and both coordinate intervals are correctly oriented, all four coordinate
inequalities are strict.  On `U`, logarithmic differentiation of the factorization gives

```text
G'/G = sum_{rho in Z_K} m(rho)/(s-rho) + h'/h.
```

Multiply by `g` and integrate around the positively oriented boundary.  Cauchy's formula sends
each first term to `2 pi i m(rho)g(rho)`.  The final term `g h'/h` is analytic throughout `U`, so its
boundary integral vanishes.  Summing the finite packet proves the identity.  Negating pointwise
gives the `zetaLogDerivReg` form.

Every dependency is a proved theorem of complex analysis.  No zero-free region, RH, density
hypothesis, asymptotic interchange, or numerical computation is used.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/Sieve/ZetaResidueUnitRectanglePeeling.lean` proves:

- finiteness and exact analytic multiplicities of every closed-rectangle residue-unit zero packet;
- global finite peeling with a cofactor nonzero on the whole rectangle;
- local-weight exact `G'/G` and regular `-G'/G` rectangle identities;
- analyticity of the actual smooth-cutoff Mellin transform on `Re s>0`;
- the exact four-edge regular Chebyshev shift with the negative zero packet;
- unconditional finite selection of all four zero-free boundary edges; and
- `exists_zetaRegularMellinBoundary_eq_neg_zeroPacket`, whose conclusion contains no boundary
  avoidance premise.

Direct `lake env lean` passes.  Final module audit
`lake build GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling` passes all 8792 jobs.
Every exported theorem in the chain has only `propext`, `Classical.choice`, and `Quot.sound` in
`#print axioms`.  Module is imported by `GaloisForLFunctions.RHTower`.

Repository-wide `scripts/formal_tools.py lint` still reports unrelated pre-existing/uncommitted
umbrella reachability failures in concurrent FieldOne, Suzuki, and HTGeometry modules; it reports no
violation in this module and specifically does not report this module unreachable.

## Log

- 2026-08-14 -- `[PAPER-PROVED] [CORPUS-BRIDGE]`; exact zero-crossing interface isolated after four
  conjecture/pivot rounds.
- 2026-08-14 -- `[LEAN-PROVED]`; smooth Mellin specialization and unconditional contour selection
  added; direct check, module build, umbrella wiring, and axiom audit pass.

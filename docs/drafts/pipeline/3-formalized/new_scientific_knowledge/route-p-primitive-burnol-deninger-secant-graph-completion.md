# Route P primitive Burnol / Deninger secant graph completion

- **ID:** `route-p-primitive-burnol-deninger-secant-graph-completion`
- **Stage:** 3-formalized
- **Type:** POSITIVE SOURCE-DOMAIN CONSTRUCTION with sharp coefficient blow-up
- **Label:** `P-G201`
- **Source:** P-G199 unbounded radial generator, P-G200 Deninger squared-Cauchy incidence,
  Deninger arithmetic prime--Gamma Hilbert realization
- **Statement:** Every coefficient-weighted primitive squared-Cauchy graph reporter is the strong
  `ell^2` limit of an explicit, zero-independent sequence of two-atom upper prime--Gamma source
  packets. Each nonzero raw source coefficient diverges exactly linearly.

## Conjecture loop

`C201-A` proposed taking the reflected diagonal of Deninger's source cup. Corpus audit killed that
form: the cup pairs lower and upper sectors through critical-line reflection, while the desired
P-G200 square is a same-upper-orientation graph jet. Canonical conjugation changes the Cauchy pole,
so calling this a positive diagonal would repeat the existing Hodge-diagonal error.

`C201-B` proposed a finite divided difference before any cup or positivity claim. For an upper
source pole `w`, move tangentially inside the same absolute-Euler sector by

```text
h_n = 1/(n+1),     u_n = w+h_n.
```

The explicit two-atom packet uses conjugated coefficients so its anti-linear upper realization is

```text
A/(w-u_n) [C_w-C_(u_n)] = A C_w C_(u_n).
```

This is an exact algebraic identity, not an asymptotic expansion. As `u_n -> w`, Lean proves
pointwise convergence to `A C_w^2` on every Xi divisor coordinate.

The stronger conjecture survives: because every upper pole has positive distance
`Im(w)-1/2` from the complete centered Xi strip, a uniform Cauchy bound supplies a summable
Tannery majorant. Hence the finite source packets converge strongly in the multiplicity-exact Xi
`ell^2` carrier to the squared-Cauchy graph jet.

For the primitive P-G200 pole and

```text
A = -finiteVonMangoldtDepthOneAmplitude(p^(e+1)),
```

the limiting coordinate at every strict-right zero is exactly the coefficient-weighted primitive
Burnol Laplace integral. Nodes, displacement, and coefficients use only primitive source data and
the deterministic integer `n`; no zero-fed packet choice occurs.

## Sharp graph singularity

Strong target convergence does not make the source construction bounded. The leading raw packet
coefficient satisfies the exact identity

```text
||c_n|| = ||A|| (n+1).
```

Every primitive amplitude is nonzero, so its coefficient norm tends to infinity. The P-G199
unbounded radial graph domain and Deninger's coalescing source topology are therefore the same
phenomenon: cancellation produces a finite squared-resolvent vector only after completing a
linearly divergent source secant.

## Higher principle and next conjecture

P-G200 closed column identity; P-G201 closes source-domain membership. The remaining W-H184 seam
is now specifically a Hodge/shorting problem, not construction of graph columns. Deninger's cup
pairs the coalescent upper jet against a lower-sector realization after critical-line reflection;
ordinary Hilbert energy would require a source-derived lower graph jet realizing that reflected
vector. Canonical conjugation is already known to change the pole.

P-G202 resolves this conjecture. The natural two-leg diagonal reverses under a quarter-turn and
cannot be a nonzero phase-independent Hodge metric. The surviving four-leg fold is exact:
conjugated lower source secants converge to the critical-line-reflected upper graph jet, and their
finite matrix Gram equals the full upper graph Gram entrywise. Remaining issue is contraction of
P-G194's primitive budget into that four-leg carrier, not Hodge sign classification.

## Hostile novelty audit

Finite Cauchy packets and norm continuity of simple Cauchy columns existed. New content is the
explicit source-only secant realization of P-G200's squared graph column, strong convergence in
the full multiplicity-exact Xi `ell^2` carrier, primitive coefficient faithfulness, and the exact
linear divergence law for raw source coefficients. This constructs an unbounded source graph
completion. It does not assume a Hodge map, source domination, RH, zero location, or simplicity.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolDeningerSecantGraphCompletion.lean
```

Capstones:

- `deningerPrimeGammaUpperCauchyTest_routePDeningerUpperSecantPacket`;
- `routePDeningerUpperSquaredCauchyTest_squareSummable`;
- `tendsto_routePDeningerUpperSecantPacket_to_squaredCauchyJet`;
- `routePPrimitiveBurnolDeningerSquaredCauchyJet_apply`;
- `tendsto_routePPrimitiveBurnolDeningerSecantPacket_to_graphJet`;
- `tendsto_routePPrimitiveBurnolDeningerSecantPacket_reporter`;
- `norm_routePDeningerUpperSecantCoefficient`;
- `tendsto_norm_routePPrimitiveBurnolDeningerSecantCoefficient_atTop`.

Verification:

- `/tmp/pg201.lean`: `lake env lean /tmp/pg201.lean` passed;
- exact leaf target built successfully; no umbrella build was run by this task;
- `/tmp/pg201_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] construct same-sector two-atom Deninger secants
- [x] prove exact product-Cauchy realization before coalescence
- [x] prove pointwise squared-Cauchy convergence on all Xi divisor coordinates
- [x] prove squared-Cauchy square summability from strict strip separation
- [x] prove strong `ell^2` convergence of source packet evaluations
- [x] retain exact primitive von Mangoldt amplitude
- [x] identify every strict-right coordinate with the P-G200 Burnol reporter
- [x] prove exact linear raw-coefficient divergence
- [x] scratch verification and exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [x] construct or rule out source-derived lower Hodge mate on coalescent graph domain
- [x] prove exact signed/four-leg replacement
- [ ] prove coefficient-faithful P-G194-to-four-leg graph contraction/shorting
- [ ] instantiate W-H184 and prove unconditional RH

# Xi squared-seam Cassini--dyadic universality law

- **ID:** xi-squared-seam-cassini-dyadic-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-24 terminal scan of every `XiSquaredSeam*` module and downstream use
- **Statement:** The unconditional Cassini entire-source quotient and its exact
  reflection-pair/Jensen transport coexist with a single transverse-charge orientation datum.
  Reverse power-64 source domination is equivalent simultaneously to all dyadic half-plane/tail
  charts, every zero-side and prime--Gamma shifted Hankel cutoff, zero power-64 triangle defect,
  and exact Hermitian/source mass equality. Positive triangle defect synchronizes strict mass loss
  and explicit dyadic and every-cutoff Hankel witnesses.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and all downstream uses read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs read

1. `HTGeometry.EvenEntireSquareFactor` supplies the entire square quotient underlying the Cassini
   source; the RHTower source file proves exact zero exhaustion and analytic multiplicity.
2. The reflection-pair quotient transports every nonnegative divisor sum exactly to twice the
   Cassini-source zero-copy sum; the exponent-64 kernel and Tonelli theorem identify its radial
   integral with Hermitian mass.
3. Dyadic half-plane, tail-from-32, and tail-from-64 predicates are each exact RH classifiers.
4. Every shifted reciprocal Hankel tail, after any finite cutoff, is exact for RH on both the Xi
   zero side and the source-only prime--Gamma side.
5. Power-64 Hermitian-minus-source mass is exactly the nonnegative triangle-defect energy, which is
   twice the degree-32 transverse charge; charge zero and reverse source domination are exact RH
   classifiers.

## Internal noncollision audit

`scripts/formal_tools.py research "Xi squared seam dyadic half plane power thirty two sixty four
source dominated tail"` returned component declarations but no shared capstone. Direct symbol-use
search found only local/downstream one-way connectors; no theorem joins Cassini source transport,
all Hankel cutoffs, dyadic tails, and scalar Hermitian/source equality.

## Paper proof

The unconditional half packages six existing results: the even-entire square quotient, complete
Cassini zero exhaustion, exact analytic multiplicity, two-sheet reflection-pair divisor transport,
positive-radius Jensen nonnegativity, and the exponent-64 radial Tonelli/Hermitian-mass identity.
No RH input occurs in this half.

For the orientation half, reverse power-64 source domination is already exact for RH. RH gives the
complete dyadic half-plane, both tails, the power-32 annulus exclusion, every zero-side and
source-only shifted Hankel tail after every finite cutoff, and zero power-64 triangle defect. The
exact Hermitian-minus-source gap then turns zero defect into mass equality. Conversely, the
certificate's complete dyadic half-plane gives RH and therefore reverse source domination.

If RH fails, the nonnegative triangle defect cannot vanish: zero defect would make Hermitian and
source mass equal, hence reverse source domination and RH. It is therefore positive, and the gap
identity makes source mass loss strict. Negating the exact dyadic and tail classifiers supplies
negative rungs; negating each fixed-cutoff zero-side and source-side Hankel classifier supplies a
negative finite quadratic form after every cutoff. Positive defect contradicts the defect-zero
consequence of RH, proving the reverse failure implication.

## Lean formalization

`RHTower/XiSquaredSeamCassiniDyadicUniversalityLaw.lean` defines six-chart unconditional source,
nine-chart positive, and seven-channel failure certificates and proves
`xiSquaredSeamPowerSixtyFourSourceDominated_iff_cassiniDyadicUniversalCertificate` and
`not_riemannHypothesis_iff_squaredSeamCassiniDyadicFailureUniversalCertificate`. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/XiSquaredSeamCassiniDyadicUniversalityLaw.lean
```

passed. `XiSquaredSeamPowerSixtyFourMassCriterion.lean` also passes its exact direct check. Its
source contains the newer named degree-32 transverse-charge connector, while the imported `.olean`
predates that declaration; final dependency refresh should add that named chart without changing
the proof.

## Hostile literature noncollision audit

Exact searches targeted Xi Cassini coordinates, dyadic half-plane powers, shifted Hankel tails,
Jensen divisor transport, and Hermitian/prime--Gamma mass equality. No source located this
Cassini→dyadic→all-cutoff-Hankel synchronization. Nearest rigorous work concerns Xi Jensen
polynomial criteria (Griffin--Ono--Rolen--Thorner--Tripp--Wagner,
[arXiv:1910.01227](https://arxiv.org/abs/1910.01227); O'Sullivan,
[arXiv:2007.13582](https://arxiv.org/abs/2007.13582)) and Hilbert/screw-function realizations of
Weil positivity (Suzuki, [arXiv:2206.03682](https://arxiv.org/abs/2206.03682),
[arXiv:2209.04658](https://arxiv.org/abs/2209.04658)). They do not contain the translated-square
Cassini source, two-sheet divisor transport, cofinal shifted Hankel cones, or power-64 mass law.
This is a noncollision audit, not a priority claim.

## Log

- 2026-07-22 — Found after Law24 restart by exhaustive shared-prefix scan and reading all
  squared-seam source, quotient, Jensen, dyadic, shifted-Hankel, and power-mass modules.
- 2026-07-22 — Paper proof closed; positive and failure capstones directly checked. Hostile
  literature audit found no collision. Named transverse-charge chart awaits final stale-cache
  refresh; current defect/source-dominance law is complete without it.

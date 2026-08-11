# Mass-shifted half-density Möbius source connection

- **ID:** `mass-shifted-half-density-mobius-source-connection`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** Shifted-Xi moment transport forces the unique half-density polynomial connection
  `K P = X^2 P' + (1/2) X P`; its covariant multiplication law is `nabla(XP) - X nabla(P) = -X^2 P`,
  and the adaptive completed `P^sharp` source is exactly the connection cost plus the positive
  multiplication Gram term.

## Goal

Replace frozen-amplitude reporting by source-native transport.  Prove exact law formed from
adaptive amplitude before rational--Gamma/von Mangoldt aggregation, then identify why its strict
sign does not automatically descend to fixed-degree canonical admission.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper + external novelty audit

## Conjecture loop

1. **Mass Möbius transport alone signs terminal odd defect energy — FAIL.**
   `HankelSectorFirstCrossingNoGo` gives a safe-sector, exact-tangent counterexample with negative
   omitted coupling.
2. **Fixed-mass arithmetic transgression supplies curvature — FAIL.**
   Existing admission transgression is an exact endpoint cocycle.
3. **A source-compatible half-density connection converts odd current to a square — PROVED.**
   Coefficient `1/2` is forced by metric compatibility; no orientation map occurs.
4. **The strict square law stays inside fixed-degree admission — FAIL.**
   `K` raises degree by one.  Exact positive survivor is an effectivity boundary: faithful
   source-parallel transport leaves every finite flag, while canonical projection must pay a
   measurable connection/leakage term.

## Paper proof `[PROVED HERE]`

Let `L_y` be shifted-Xi moment functional.  Existing source transport says, for fixed polynomial
`R`,

`d/dy L_y(R) = -L_y(X (X R' + R))`.

For `c in R`, put `K_c P = X^2 P' + c X P`.  Direct Leibniz expansion gives

`(K_c P)Q + P(K_c Q) = X^2(PQ)' + 2c X P Q`.

This equals `X (X(PQ)' + PQ)` for all `P,Q` iff `2c=1`; hence `c=1/2` is unique.  Write `K=K_(1/2)`.
For polynomial curves `P_y,Q_y`, define `nabla P = dot P-KP`.  Product rule and preceding identity
give exact metric compatibility

`d/dy L_y(PQ)=L_y((nabla P)Q)+L_y(P(nabla Q))`.

Direct calculation also gives `K(XP)-XKP=X^2P`, therefore

`nabla(XP)-X nabla(P)=-X^2P`.

Taking `Q=XP` and using symmetry yields

`d/dy L_y(P XP)=2L_y((nabla P)XP)-L_y((XP)^2)`.

Thus source-parallel transport `nabla P=0` has strict odd-current dissipation

`d/dy L_y(P XP)=-L_y((XP)^2)<0`

on every positive moment block large enough to contain `XP`, for nonzero `P`.

For fixed `P`, `nabla P=-KP`, so the literal adaptive shear polynomial satisfies

`2(XP)(X(XP'+P))=(XP)^2+2(KP)(XP)`.

At square mass the existing completed-source theorem identifies its moment with the literal
rational--Gamma-minus-von-Mangoldt formation.  Therefore completed adaptive `P^sharp` source is
exactly positive multiplication Gram bulk plus twice half-density connection cost, with admission
performed before arithmetic aggregation.

## Novelty / collision audit

- Internal corpus contains Möbius moment tangent, adaptive Euler shear, arithmetic bilinear
  landing, current Jacobi Riccati scalar, and Cayley half-density compactness, but no polynomial
  metric connection `K`, uniqueness theorem, covariant multiplication law, or parallel strict
  dissipation theorem.
- External audit found general Möbius-transformed orthogonal polynomials and nonisospectral Toda
  hierarchies, but no source matching this shifted reciprocal moment flow and completed Xi
  arithmetic landing.  Literature-level novelty remains unverified; project-level synthesis is new.

## Open consequence

Need quantify canonical projection leakage from source-parallel half-density transport.  Because
`K` raises degree, finite Hankel faces are observations of this dynamics, not faithful carriers.
This locates finite-to-global failure in effectivity/admission, not missing orientation.

## Log

- 2026-08-11 — conjecture loop closed on paper; formalization started.
- 2026-08-11 — formalized source generator and uniqueness, completed arithmetic landing,
  covariant odd-current law, strict source-parallel dissipation, exact monomial degree growth, and
  finite-degree non-invariance in
  `RHTower.XiShiftedHalfDensityMobiusSourceConnection`; direct Lean and targeted module build pass;
  axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

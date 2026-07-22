# Xi Hedenmalm orientation endpoint universality law

- **ID:** xi-hedenmalm-orientation-endpoint-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-26 terminal inventory of Hedenmalm Gaussian, orientation, moment, Cauchy, and numerical-sector modules
- **Statement:** The RH endpoint of the Hedenmalm program is one parameter-uniform phase: every
  positive-temperature complete Gaussian Hankel cone, every positive-aperture canonical
  orientation ceiling, upper-half-plane analytic continuation, and reciprocal vertical-mesh lower
  bound, the pointed-moment/source/Weil rank-one diagonal signs, and the multiplicity-aware
  reciprocal numerical sector all hold together. Failure of RH forces simultaneous failure in
  every analytic and sign chart, while the numerical chart fails in at least one of its two
  complementary factors.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and every universality-law use read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs read

1. At each positive Gaussian temperature, `HedenmalmGaussianHankelCone tau` is equivalent to RH;
   the corpus also proves existential, universal-temperature, and temperature-independence forms.
2. At every positive aperture `a`, the canonical orientation singularity ceiling and analyticity
   on `{b | a < b.im}` are each equivalent to RH.
3. At every positive aperture, eventual lower boundedness along every reciprocal vertical mesh is
   equivalent to RH; the proof uses the exact negative multiplicity residue at a forced boundary.
4. Pointed-moment Hermitian diagonal positivity is equivalent to the continued prime--archimedean
   one-Cauchy sign, and each is equivalent to RH.
5. Rank-one Weil Cauchy positivity is equivalent to RH and implies the same continued-source sign.
6. The reciprocal numerical upper sector is deliberately blind at multiple zeros. Its conjunction
   with right-half local Jordan normality is exactly RH.

## Internal noncollision audit

`scripts/formal_tools.py research "Gaussian Hankel zero aperture canonical orientation vertical
mesh pointed moment numerical sector Cauchy universality"` and direct symbol-use search found no
common consumer. Law18 consumes the positive-width Gaussian tail spectrum, not the zero-width RH
endpoint. Law19 consumes the continued-source sign only inside an RH-plus-global-simplicity phase;
it does not connect the parameter-uniform orientation, mesh, moment, Weil, or multiplicity-blind
numerical charts. No existing universality law uses the singularity-ceiling, vertical-mesh,
pointed-moment, Weil one-Cauchy, or numerical-sector endpoint predicates.

## Paper proof

Assume RH. For arbitrary positive `tau`, the fixed-temperature Gaussian equivalence gives the
complete Hankel cone. For arbitrary positive `a`, the exact singularity-ceiling, analytic
upper-half-plane, and reciprocal-mesh equivalences give all three orientation statements. The
pointed-moment, continued-source, and Weil one-Cauchy equivalences give all three diagonal signs.
Finally the numerical-sector factorization gives right-half local Jordan normality together with
the reciprocal numerical upper sector. Hence every field of the parameter-uniform certificate
holds.

Conversely, the certificate's Gaussian field at `tau = 1` implies RH by the one-temperature exact
criterion. Thus the full certificate is equivalent to RH; any other field independently recovers
the same endpoint as a consistency check.

Now assume not-RH. If any positive-temperature Gaussian cone held, its exact criterion would give
RH; therefore every such cone fails. The same contraposition, pointwise in every positive
aperture, forces failure of every singularity ceiling, analytic upper-half-plane statement, and
reciprocal-mesh lower-bound statement. Contraposition of the three exact diagonal criteria forces
failure of the pointed-moment, continued-source, and Weil one-Cauchy signs. Finally negating the
exact numerical factorization yields failure of right-half local Jordan normality or failure of
the numerical upper sector. These clauses form the synchronized failure certificate. Conversely,
its failed Gaussian cone at `tau = 1` contradicts the cone supplied by RH. Therefore not-RH is
equivalent to the full failure certificate, and positive and negative endpoint phases are exact
complements.

## Lean formalization

`RHTower/XiHedenmalmOrientationEndpointUniversalityLaw.lean` defines the thirteen-field positive
certificate and its synchronized failure certificate. It proves
`riemannHypothesis_iff_hendenmalmOrientationEndpointUniversalCertificate`,
`not_riemannHypothesis_iff_hendenmalmOrientationEndpointFailureUniversalCertificate`, and exact
complementarity of the two phases. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/XiHedenmalmOrientationEndpointUniversalityLaw.lean
```

passed on the first run.

## Hostile literature noncollision audit

Exact and adjacent searches found no paper stating the thirteen-chart parameter-uniform phase or
its synchronized failure law. Hedenmalm's 2026 spectral paper constructs a theta-based second-order
eigenvalue problem and a self-adjointness notion for the pair `(LD,L)`
([arXiv:2606.17494](https://arxiv.org/abs/2606.17494)); it does not state Gaussian complete-Hankel,
canonical multiplier ceiling/mesh, pointed-moment, rank-one Cauchy, and numerical-sector
equivalence. Suzuki's screw-function criteria formulate RH through screw/Weil positivity
([arXiv:2206.03682](https://arxiv.org/abs/2206.03682)) and his 2026 synthesis unifies several Weil
quadratic-form constructions ([arXiv:2606.09096](https://arxiv.org/abs/2606.09096)); neither
contains the Hedenmalm endpoint family or the multiplicity-blind numerical collision. The
Connes--Consani scaling Hamiltonian develops semilocal trace and Weil positivity
([arXiv:1910.14368](https://arxiv.org/abs/1910.14368)), again without this parameter-uniform
analytic/moment/numerical closure. This is a noncollision audit, not a priority claim.

## Log

- 2026-07-21 — Found bottom-up after auditing seven terminal Hedenmalm families and their existing
  universality-law consumers. Paper proof closed; Lean formalization pending.
- 2026-07-21 — Expanded before coding with zero-width tail, Krein-orbit, Fourier-current, and raw
  Hedenmalm Hermitian charts. Thirteen-field positive and synchronized-failure laws formalized;
  exact direct check passed first run.
- 2026-07-21 — Hostile literature audit found adjacent theta spectral and Weil/screw positivity
  programs but no thirteen-chart endpoint/failure law. Marked no-priority noncollision.

# Route O prolate Rayleigh--ground lock

- **ID:** `route-o-prolate-rayleigh-ground-lock`
- **Stage:** 1-in-progress
- **Type:** THEOREM / ROUTE CLASSIFICATION
- **Scientific status:** `[CONJECTURE FROZEN FOR PROOF AUDIT] [NOT AN RH PROOF]`
- **Route:** O — Connes/CCM restricted-Weil and prolate limit
- **Primary sources:** Connes--Consani--Moscovici, *Zeta Spectral Triples*
  (arXiv:2511.22755); Connes--van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the
  Spectral Action* (arXiv:2511.23257).

## Exact claim

Let `q_a` be the restricted Weil quadratic form on the multiplicative aperture
`[exp(-a), exp(a)]`, let

```text
epsilon(a)=inf_(||f||=1) q_a(f,f),
```

and let `k_a` be the normalized constrained-prolate seed of the CCM outlook.  Write

```text
r(a)=q_a(k_a,k_a),
Delta(a)=r(a)-epsilon(a).
```

Assume only the already isolated source theorem

```text
r(a) -> 0 as a -> infinity.                                (O1)
```

Then

```text
RH  <->  Delta(a) -> 0.                                    (O2)
```

More sharply, if RH is false, there are `delta>0` and `a_0` such that

```text
Delta(a) >= delta  for every a>=a_0.                        (O3)
```

Thus asymptotic Rayleigh ground-state comparison of the explicit prolate seed is the whole RH
burden, not an analytic preliminary to determinant convergence.  Any stronger projective or
determinant-transfer estimate which forces `(O2)` inherits the same classification.

## Why this is source-specific

The proof uses three literal restricted-Weil facts:

1. aperture nesting makes `epsilon(a)` nonincreasing;
2. Rayleigh--Ritz gives `epsilon(a)<=r(a)` for the actual prolate seed;
3. Weil positivity on every compactly supported test is equivalent to RH.

An arbitrary real-zero approximant family has none of this variational structure.  The claim is
therefore stronger than the existing unstructured wall
`ConnesXiGroundStateLimitWall <-> RH` and cannot be witnessed under RH by choosing a constant Xi
sequence.

## Proof plan

Under RH, `0<=epsilon(a)<=r(a)`.  Equation `(O1)` squeezes both `epsilon(a)` and
`Delta(a)=r(a)-epsilon(a)` to zero.

Conversely, `(O1)` and `Delta(a)->0` give `epsilon(a)->0`.  If RH fails, Weil's criterion supplies
one compactly supported unit vector `f` with `q(f,f)=-c<0`.  Every larger aperture contains `f`, so
`epsilon(a)<=-c` forever.  This contradicts `epsilon(a)->0` and proves `(O2)`.  Taking
`delta=c/2` after `r(a)>-c/2` proves `(O3)`.

## Falsification matrix

| Attack | Required check | Status |
|---|---|---|
| Constant-Xi theatre | Claim must mention actual nested Weil floors and prolate seed energy | passes by statement |
| Pointwise approximant loophole | No zero-set convergence is used | passes by proof plan |
| Non-nested Galerkin cutoffs | Take continuous apertures first; finite dimensions enter only through the existing diagonal transfer | passes |
| Seed not normalized | Normalize before defining `r`; scaling otherwise invalidates Rayleigh--Ritz | explicit requirement |
| Seed energy approaches zero from below | Under RH this is impossible because `epsilon>=0` and `epsilon<=r`; false-RH proof permits either sign | passes |
| Negative spectrum evacuation | Aperture nesting forbids it; one negative witness survives in every larger aperture | load-bearing |
| Stronger projective comparison without energy control | Not claimed; only estimates implying `Delta->0` are classified | passes |

## Relation to existing Route O work

- `ccm-negative-spectrum-no-evacuation-law.md` proves the nesting mechanism on paper.
- `ccm-rayleigh-transfer-collapses-to-spectral-floor.md` proves that a particular
  Rayleigh-excess/gap rate forces the cofinal floor to zero.  `(O2)` strengthens the route verdict:
  vanishing *unnormalized* prolate Rayleigh excess is already equivalent to RH once `(O1)` is
  installed.
- `FuchsFloorNoGo.lean` disproves the uniform radial floor used by one abstract constrained-prolate
  transfer.  That no-go does not prove `(O2)` and does not retire every possible ground comparison.
- The concrete finite CCM matrix and source/response determinant algebra remain separate finite
  infrastructure; their rigorous finite-to-Xi convergence cannot reduce `(O2)`.

## Novelty audit

Internal search found the two ingredients above but no exact equivalence `(O2)` or persistent
false-RH excess `(O3)`.  Primary-source search through 2026-08-01 found numerical ground-state and
determinant convergence, the simple-even real-zero theorem, and the statement that rigorous
convergence would prove RH; it found no Rayleigh-excess dichotomy matching `(O2)`--`(O3)`.

The theorem is expected to be elementary once stated.  Novelty claim is therefore limited to Route
O classification and source-specific obstruction, not a new theorem about zeta zeros.

## Lean target

Add a source-typed variational interface containing:

```text
floor_antitone
floor_le_seedEnergy
seedEnergy_tendsto_zero
riemannHypothesis_iff_floor_nonneg
```

and prove unconditionally:

```text
riemannHypothesis_iff_prolateRayleighExcess_tendsto_zero
eventually_prolateRayleighExcess_ge_of_not_riemannHypothesis
```

No abstract implication from assumed local-uniform determinant convergence will be added.

## Gates

- [x] internal corpus audit
- [x] primary external collision audit
- [x] exact conjecture frozen
- [ ] dependency-closed paper proof hostile audit
- [ ] unconditional Lean formalization
- [ ] axiom/lint audit
- [ ] Route O map and pipeline closure


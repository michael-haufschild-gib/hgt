# Canonical Pluecker--Jordan curvature transition

- **ID:** `pluecker-jordan-curvature-transition-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean candidate), CROSS-FOLDER UNIVERSAL SOURCE LAW
- **Status:** `[PAPER-PROVED] [EXTERNAL SEARCH NONCOLLISION] [LEAN CHECK PENDING] [NOT RH]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnFourRatePluckerJordanTransition.lean`

## Theorem-first origin

No law was proposed before reading the endpoints.  Three already proved branches have the same
four-rate corrected Fisher coordinate:

1. `GammaSewnFourRatePluckerConnector.lean` identifies the six boundary-pair probabilities with
   the canonical Pluecker normalization of the HilbertMetric Gram feature and identifies corrected
   Fisher with its canonical Pluecker expectation.
2. `GammaSewnFourRateSynchronizedEulerFisher.lean` proves the synchronized Gamma finite-part /
   sewing decomposition

   ```text
   H = -F/2,   S = 3F/2,   H + S = F.
   ```

3. `GammaSewnFourRateHeightLocalizedDomination.lean` proves the exact common-depth transition

   ```text
   F < Disp(e)  <->  sqrt(F/D) < e + 1/2,
   ```

   and `GammaSewnFourRateSchurFisherCurvature.lean` proves

   ```text
   C(e) = -2F - 2Disp(e).
   ```

The two descriptions had no common consumer.  Their forced closure is below.

## Law

Let `S_Pl` be the synchronized sewing observable averaged with the canonical Pluecker probability
of a nondegenerate four-rate Gamma boundary packet.  Let `C(e)` be its Schur boundary
log-curvature at common valuation depth `e`; let `F>0` be complementary Fisher mass and `D>0`
prime-log pair dispersion.  Then

```text
S_Pl = 3F/2
```

and the complete curvature transition is

```text
C(e) < -(8/3) S_Pl  <->  sqrt(F/D) < e + 1/2.            (PJ)
```

Equivalently, the synchronized height, sewing, and residual Pluecker coordinates have the fixed
projective ratio

```text
height : sewing : residual = -1 : 3 : 2,
```

and the Rees-depth phase boundary is read directly from canonical Pluecker Schur curvature.

## Paper proof

Canonical probability equality makes `S_Pl` equal to the existing boundary sewing mass.  The
synchronized Euler--Fisher theorem gives `S_Pl=3F/2`.  The Schur theorem gives
`C(e)=-2F-2Disp(e)`.  Therefore

```text
C(e) < -(8/3)S_Pl
<-> -2F-2Disp(e) < -4F
<-> F < Disp(e).
```

Apply the existing exact transition theorem to the last inequality.  Its strict positivity
hypotheses are discharged by nonzero aperture, injective rates, boundary noncollision, and
injective prime labels.  No analytic limit or target-divisor input is used.

## Why this is not a patched conjunction

`(PJ)` eliminates the intermediate corrected Fisher coordinate and identifies one sharp phase
boundary simultaneously in three native geometries: canonical Pluecker volume, synchronized
Gamma Jordan finite parts, and valuation-depth Schur curvature.  Neither parent branch states a
curvature threshold in the coordinates of the other branch.

## Literature audit

Hostile exact and structural searches were run after the theorem was derived.  Adjacent primary
literature covers:

- Pluecker coordinates as positive/dimer partition functions:
  https://arxiv.org/abs/1309.6630
- likelihood geometry of determinantal probability laws:
  https://arxiv.org/abs/1701.06501
- covariance/Fisher duality and information-geometric curvature:
  https://arxiv.org/abs/quant-ph/0106125
- realization and additivity mechanisms for Fisher metrics:
  https://arxiv.org/abs/1504.03184

No searched source states the Gamma synchronized finite-part/sewing ratio, identifies that ratio
with a canonical Pluecker expectation, or gives transition `(PJ)`.  This is a search noncollision,
not a priority guarantee.  The classical ingredients—Cauchy--Binet/Pluecker normalization,
Fisher-as-variance, Schur curvature, and Bernoulli finite parts—remain separately standard.

## Scope and falsifiers

- This is a finite source law, not a physical deep-valuation probability law.
- Literal Euler amplitudes depend on conductor and depth; replacing the boundary Pluecker packet
  by those amplitudes invalidates the transition.
- No Xi zero, RH predicate, inverse-critical positivity, or source-to-response intertwiner enters.
- Any normalization changing `H=-F/2` or `S=3F/2` destroys the coefficient `8/3`.

## Gates

- [x] theorem endpoints found bottom-up
- [x] corpus-wide exact-name and card collision search
- [x] dependency-closed paper proof
- [x] hostile primary-literature search noncollision
- [ ] direct Lean check
- [ ] axiom audit
- [ ] exact module build
- [ ] promote to stage 3 after verification


# FCRJ theta--Abel energy direct-prime source criterion

- **ID:** `fcrj-theta-abel-energy-direct-prime-source-criterion`
- **Stage:** 3 — formalized in Lean 4
- **Source route:** CCM-FU / FCRJ physical theta--Abel aperture
- **Theorem status:** Lean-proved

## Claim

Every finite multiplicity-exact Xi packet admits an explicit-formula-admissible rectangle which
crosses the unique centered archimedean pole `z=-i/2`, crosses horizontal coordinate zero, and
stays below `Im z=1/2`. On every such rectangle, the normalized physical theta--Abel source
contour is exactly the literal continued-prime-flux contour plus the explicit positive square

```text
[e^(a/2) 2(1-e^(-L/2)) c A]^2.
```

Packet-stable eventual lower boundedness of these explicitly corrected direct-prime contours is
equivalent to RH. The unit specialization is closed and premise-free.

## Gates

- [x] Exact paper statement and proof
- [x] Corpus conjecture search before construction
- [x] Targeted literature novelty audit
- [x] Direct Lean check
- [x] Umbrella wiring
- [x] Targeted module build and built-module axiom audit
- [ ] Publication-ready exposition

## Exact theorem

Write

```text
F_a(z)=the physical theta--Abel energy two-edge transform,
s(z)=1/2+i z,
P(z)=infinitePrimeFlux(s(z)),
C_P(z1,z2)=(2 pi i)^-1 contour F_a(z)^2[-i P(z)] dz,
E_a=[e^(a/2) 2(1-e^(-L/2)) c A]^2.
```

Lean proves a strengthened cofinal rectangle selector: for every finite Xi-copy packet `t`, there
are `z1,z2` such that the four edges are source-admissible, `t` lies in the rectangle interior,
and

```text
z1.re < 0 < z2.re,
z1.im < -1/2 < z2.im < 1/2.                                  (1)
```

On any admissible rectangle, edgewise analyticity and interval integrability give the exact
contour identity

```text
normalizedSource(z1,z2)=C_P(z1,z2)+normalizedArch(z1,z2).     (2)
```

Under `(1)`, the Loop-80 residue evaluation turns `(2)` into

```text
normalizedSource(z1,z2)=C_P(z1,z2)+E_a.                      (3)
```

Define corrected-prime packet stability by

```text
exists B,N0, for every n>=N0 with L<log(n)/2,
  for every finite Xi-copy packet t,
    exists a rectangle satisfying (1), containing t,
    admissible on all four edges, with
      B <= Re[C_P(z1,z2)+E_(log(n)/2)].                       (4)
```

Then, for every `L,A,c>0`, Lean proves unconditionally

```text
(4) <-> RiemannHypothesis.                                   (5)
```

## Proof

The existing finite-avoidance selector already chooses bottom height `-3/4`, top height in
`(y0,1/2)` with `y0>-1/2`, left coordinate below `-R`, and right coordinate above `R`, with
`R>0`. Exposing those inequalities proves `(1)` without a new zero theorem or a chosen
enumeration.

For `(2)`, admissibility identifies the continued source with `logDeriv XiC` on every edge, hence
the weighted source is interval integrable. The centered arch factor is analytic and nonzero at
every admissible edge point; its weighted logarithmic derivative is also interval integrable.
The direct prime channel is their difference. Rectangle-integral additivity then promotes the
pointwise prime/arch split to `(2)`. The single-pole residue law proves `(3)`.

For `RH -> (4)`, enlarge the prescribed packet by an absolute-tail control packet and use the
strengthened pole-crossing selector. The resulting source contour is within `1` of the
nonnegative complete Weil value, so `B=-1` works; `(3)` transfers the floor to the corrected
prime contour. For `(4) -> RH`, `(3)` turns every corrected-prime witness into a witness for the
already proved packet-stable source criterion, which implies RH.

## Lean certificate

- Selector module:
  `formal/GaloisForLFunctions/RHTower/XiGuinandWeilRectangleExhaustion.lean`
- Contour split module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeContour.lean`
- Criterion module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeSourceCriterion.lean`
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`
- Direct checks: PASS
- Targeted build: PASS
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Capstones:
  `exists_poleCrossing_admissible_rectangle_containing_xiZeroCopy_finset`,
  `rectIntegral_physicalThetaAbelEnergy_source_eq_prime_add_arch`,
  `xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_correctedPrime`,
  `exists_poleCrossing_admissible_physicalThetaAbelEnergySourceContour_containing_approximates_weil`,
  `xiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow_iff_riemannHypothesis`,
  `unitPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow_iff_riemannHypothesis`

## No-go closure

The remaining source criterion does not need a Gamma estimate, arbitrary deep rectangles, or an
uncontrolled archimedean remainder. Cofinal admissible rectangles can always cross exactly the
one relevant arch pole, and its full contribution is elementary. The RH-bearing open core is now
the eventual packet-stable lower floor for the direct continued prime-flux contour after adding
the displayed explicit square.

This is an exact reduction, not an RH proof: theorem `(5)` identifies the remaining prime-only
burden but does not prove predicate `(4)` unconditionally.

## Novelty audit

Classical Guinand--Weil formulas split spectral sums into prime and Gamma terms, and classical
argument-principle proofs use zero-avoiding rectangles. Corpus and literature searches through
2026-08-27 found no packet-cofinal pole-crossing selector coupled to this physical theta--Abel
detector, no exact edge-integrable direct-prime contour identity `(2)--(3)`, and no corrected
direct-prime criterion `(4)--(5)`. Candidate-new content is restricted to this route-specific
synthesis and formal equivalence.

Primary comparison points:

- R. Pérez-Marco, *Notes on the Riemann Hypothesis*, §3: classical rectangular
  `zeta'/zeta` contours and the Guinand--Weil prime/infinite-place decomposition.
- E. Carneiro et al., *Fourier Optimization and Quadratic Forms*, Q. J. Math. 73 (2022):
  explicit-formula zero, Gamma, and prime-power channels for general test functions.
- A. Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for the truncated Weil
  quadratic form*, arXiv:2607.02828.

## Verification log

- 2026-08-27: mandatory Lean-corpus research completed before conjecturing.
- 2026-08-27: direct contour split closed in scratch and source module.
- 2026-08-27: strengthened pole-crossing selector direct check passed.
- 2026-08-27: complete direct-prime RH criterion closed in scratch and source module.
- 2026-08-27: targeted literature novelty audit completed.
- 2026-08-27: targeted module build passed.
- 2026-08-27: built-module axiom audit passed with standard axioms only.

# Physical corrected-prime canonical selected-contour criterion

- **ID:** `physical-corrected-prime-canonical-selected-contour`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Source route:** CCM-FU / PPM / physical theta--Abel corrected-prime contour
- **Statement:** One fixed selected corrected-prime contour array is bounded below exactly under RH and collapses at all radii cofinally exactly under false RH.

## Goal

Remove both varying finite-packet and varying contour witnesses from the physical corrected-prime
criterion. For each logarithmic scale and canonical radius, select once and for all one admissible
pole-crossing rectangle approximating complete Weil energy within one unit. Study only the resulting
fixed two-parameter array of literal corrected-prime contour values.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure after selector definition, attack idea
- [x] 1 → 2 fully-proven: complete paper proof, no open dependency
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and constructive-selector analysis

## Exact theorem

For `A,c>0`, scale `a`, and canonical radius `m`, the corpus approximation theorem supplies a
pole-crossing rectangle `R(L,A,c,a,m)` which contains the canonical copied-zero packet `P_m`, is
admissible on all four edges, and satisfies

```text
dist(SourceContour(R), CompleteWeilEnergy) < 1.              (1)
```

Classical choice fixes one such rectangle for every parameter tuple. Let

```text
S(L,A,c,a,m)=CorrectedPrimeContour(R(L,A,c,a,m)).             (2)
```

The exact archimedean residue landing converts `(1)` into

```text
dist(S(L,A,c,a,m), CompleteWeilEnergy(L,A,c,a)) < 1.         (3)
```

Hence RH implies, simultaneously for every scale and radius,

```text
-1 < Re(S(L,A,c,a,m)).                                      (4)
```

If RH is false, complete physical energy is cofinally below every floor. Applying `(3)` at a scale
where complete energy is below `B-1` gives the stronger all-radius law

```text
for every B,N0, exists n>=N0 with L<log(n)/2 such that
  for every m, Re(S(L,A,c,log(n)/2,m)) < B.                  (5)
```

For every `L,A,c>0`, Lean proves both exact criteria

```text
[the fixed selected array is eventually bounded below] <-> RH,    (6)
[the fixed selected array satisfies (5)] <-> not RH.              (7)
```

Premise-free unit-parameter forms of `(6)--(7)` are included.

## Proof

Apply the existing pole-crossing source approximation theorem to `P_m` with error radius one and
package its full geometry, admissibility, containment, and distance contract. `Classical.choose`
defines one fixed rectangle; `Classical.choose_spec` recovers the contract. No new axiom is added.
The exact source-equals-corrected-prime theorem proves `(3)`.

Under RH, Weil positivity and the real-part norm inequality applied to `(3)` yield `(4)`. Under
false RH, choose a late scale with complete energy below `B-1`; the opposite real-part norm
inequality and `(3)` give `(5)` for every radius, since approximation error one is uniform in `m`.
Statements `(6)--(7)` follow by contradiction at radius zero.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeCanonicalSelectedContour.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS (`11808/11808`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `XiPhysicalThetaAbelEnergyCanonicalApproxRectangleSpec`,
  `xiPhysicalThetaAbelEnergyCanonicalApproxRectangle`,
  `xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample`,
  `dist_canonicalCorrectedPrimeSample_weil_lt_one`,
  `canonicalCorrectedPrimeSample_re_gt_neg_one_of_riemannHypothesis`,
  `not_riemannHypothesis_implies_canonicalCorrectedPrimeSamples_allRadii_cofinally_unbounded_below`,
  `canonicalSelectedEventuallyBoundedBelow_iff_riemannHypothesis`,
  `canonicalCorrectedPrimeSamplesAllRadiiCofinallyUnboundedBelow_iff_not_riemannHypothesis`

## Route impact, limitation, and positive survivor

The theorem eliminates existential packet and contour variables from the final logical criterion:
one fixed array is enough. It also strengthens false-RH instability from one hostile packet or
radius tail to simultaneous collapse of **every** radius at a common late scale.

The selector is noncomputable and is defined using a zero-side approximation theorem. Therefore
this result does not yet provide an explicit prime-only rectangle schedule. Remaining constructive
burden is to replace the chosen selector with an arithmetic schedule, or prove the lower floor for
the fixed selected array without invoking its zero-side approximation provenance. Strongest
positive survivor is uniform all-radius approximation `(3)` and simultaneous-collapse law `(5)`.

## Novelty audit

Targeted corpus and primary-literature searches through 2026-08-27 found no fixed two-parameter
corrected-prime contour array with uniform unit approximation, an RH lower floor, and simultaneous
all-radius false-RH collapse. Related literature treats semilocal Weil forms, finite-prime or
finite-interval spectral approximations, compact-window positivity, and classical contour
exhaustions. None states `(3)--(7)` for this physical theta--Abel direct-prime channel.
Candidate-new content is restricted to this exact formal synthesis.

Primary comparison points:

- A. Connes and C. Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368).
- A. Connes and W. van Suijlekom,
  [*Quadratic Forms, Real Zeros and Echoes of the Spectral Action*](https://arxiv.org/abs/2511.23257).
- A. Connes, C. Consani, and H. Moscovici,
  [*Zeta Spectral Triples*](https://arxiv.org/abs/2511.22755).
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096).
- M. Chuk,
  [*Weil positivity in compact windows: certified two-sided bounds and a Landau--Widom decay law*](https://arxiv.org/abs/2608.24827).

## Log

- 2026-08-27 — Mandatory corpus search isolated uniform source approximation as a contour selector.
- 2026-08-27 — Conjectured fixed-array criterion and simultaneous all-radius collapse; scratch proof passed.
- 2026-08-27 — Direct check, umbrella wiring, targeted build, and standard-axiom audit passed.
- 2026-08-27 — Current-literature search found no exact selected corrected-prime array criterion.
- 2026-08-27 — Global lint reached the wired module with no local violation; repository-wide gate
  remains blocked by unrelated concurrently edited unwired RHTower/HTGeometry modules.

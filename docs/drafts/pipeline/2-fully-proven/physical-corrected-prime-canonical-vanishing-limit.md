# Physical corrected-prime canonical vanishing-error limit

- **ID:** `physical-corrected-prime-canonical-vanishing-limit`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (Lean)
- **Source route:** CCM-FU / PPM / physical theta--Abel corrected-prime contour
- **Statement:** Canonically selected corrected-prime contours converge exactly to complete Weil energy; raw prime contours converge to Weil energy minus one explicit archimedean square.

## Goal

Upgrade the fixed unit-error selected array to an exact contour limit. At canonical radius `m`,
select a pole-crossing admissible rectangle containing the canonical copied-zero packet with error
less than `1/(m+1)`. This produces a single cofinal contour sequence at every physical scale whose
literal corrected-prime values recover complete physical theta--Abel Weil energy.

## Gates

- [x] 0 → 1 in-progress: well-posed, corpus-derived approximation schedule
- [x] 1 → 2 fully-proven: complete paper proof, no open dependency
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and constructive-selector replacement

## Exact theorem

For `A,c>0`, scale `a`, and radius `m`, choose a pole-crossing admissible rectangle `R_m` containing
the canonical copied-zero packet `P_m` such that

```text
dist(SourceContour(R_m), CompleteWeilEnergy) < 1/(m+1).      (1)
```

Let `C_m` be the corrected direct-prime contour on `R_m`. Exact residue transfer gives

```text
dist(C_m, CompleteWeilEnergy) < 1/(m+1).                    (2)
```

Since `1/(m+1) -> 0`, Lean proves

```text
C_m -> CompleteWeilEnergy.                                  (3)
```

Let `P_m^raw` be the normalized raw continued-prime contour on the same rectangle and

```text
ArchSq(L,A,c,a)
 =[exp(a/2) 2(1-exp(-L/2)) c A]^2.
```

Then the exact raw-prime limit is

```text
P_m^raw -> CompleteWeilEnergy - ArchSq(L,A,c,a).             (4)
```

Define asymptotic nonnegativity by requiring, at every admissible logarithmic scale and every
`ε>0`, that eventually

```text
-ε < Re(C_m).                                                (5)
```

For every `L,A,c>0`, Lean proves

```text
(5) at all admissible log scales <-> RH.                    (6)
```

A premise-free unit-parameter form is included.

## Proof

The packet-containing pole-crossing approximation theorem accepts every positive tolerance, so it
applies with `ε_m=1/(m+1)`. Classical choice fixes one rectangle satisfying its full geometry,
admissibility, containment, and approximation contract. The exact source-equals-corrected-prime
identity proves `(2)`. The metric `ε` criterion and `ε_m→0` prove `(3)`. Subtracting the radius-
independent explicit correction from the convergent sequence proves `(4)`.

Under RH, complete Weil energy has nonnegative real part. Real-part continuity and `(3)` place the
selected samples eventually in every half-line `(-ε,∞)`, proving `(5)`. Conversely, if a complete
Weil value had negative real part `W`, choose `ε=-Re(W)/2`. Convergence makes samples eventually
less than `-ε`, while `(5)` makes them eventually greater than `-ε`, contradiction. Existing
logarithmic-mesh completeness then proves RH, yielding `(6)`.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeCanonicalVanishingLimit.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS (`11809/11809`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `XiPhysicalThetaAbelEnergyCanonicalApproxRectangleSpecAt`,
  `xiPhysicalThetaAbelEnergyCanonicalVanishingApproxRectangle`,
  `xiPhysicalThetaAbelEnergyCanonicalVanishingCorrectedPrimeSample`,
  `xiPhysicalThetaAbelEnergyCanonicalVanishingPrimeSample`,
  `dist_canonicalVanishingCorrectedPrimeSample_weil_lt`,
  `tendsto_canonicalVanishingCorrectedPrimeSample_weil`,
  `tendsto_canonicalVanishingPrimeSample_weil_sub_archSq`,
  `canonicalVanishingAsymptoticallyNonnegative_iff_riemannHypothesis`,
  `unitCanonicalVanishingAsymptoticallyNonnegative_iff_riemannHypothesis`

## Route impact, limitation, and positive survivor

This closes the contour-limit burden for the physical direct-prime reduction: complete Weil energy
is now an exact limit of corrected literal prime-flux contours, and the uncorrected limit differs by
one closed elementary square. The RH floor sharpens from the fixed `-1` bound of Loop 86 to every
negative epsilon asymptotically.

Selector remains noncomputable and inherits zero-side approximation provenance. Remaining hard
arithmetic burden is not contour convergence but direct proof of asymptotic lower bound `(5)` from
prime flux, ideally for an explicit prime-defined admissible schedule. Strongest positive survivor
is exact raw-prime limit `(4)`, which isolates the entire archimedean contribution as one square.

## Novelty audit

Targeted corpus and primary-literature searches through 2026-08-27 found no exact canonical
vanishing-error limit `(3)--(4)` for a physical theta--Abel literal continued-prime contour and no
asymptotic epsilon-floor equivalence `(6)`. Groskin's current finite Guinand--Weil dictionary gives
exact finite zero sums and a positive omitted archimedean tail for Galerkin truncations, but not this
pole-crossing prime-flux contour limit or its explicit single-square correction. Candidate-new
content is restricted to this route-specific formal synthesis.

Primary comparison points:

- A. Connes and C. Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368).
- A. Connes, C. Consani, and H. Moscovici,
  [*Zeta Spectral Triples*](https://arxiv.org/abs/2511.22755).
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096).
- A. Groskin,
  [*A finite Guinand-Weil dictionary and archimedean tail order for the truncated Weil quadratic form*](https://arxiv.org/abs/2607.02828).
- M. Chuk,
  [*Weil positivity in compact windows: certified two-sided bounds and a Landau--Widom decay law*](https://arxiv.org/abs/2608.24827).

## Log

- 2026-08-27 — Mandatory corpus search exposed arbitrary-accuracy packet-containing approximation.
- 2026-08-27 — Conjectured `1/(m+1)` selector and exact corrected/raw prime limits; scratch passed.
- 2026-08-27 — Added asymptotic epsilon-floor RH equivalence.
- 2026-08-27 — Direct check, umbrella wiring, targeted build, and axiom audit passed.
- 2026-08-27 — Literature audit compared latest finite Guinand--Weil and compact-window results.
- 2026-08-27 — Global lint reached the wired module with no local violation; repository-wide gate
  remains blocked by unrelated concurrently edited unwired RHTower/HTGeometry modules.

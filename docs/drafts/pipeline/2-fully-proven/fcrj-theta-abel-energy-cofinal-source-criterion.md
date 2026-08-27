# FCRJ theta--Abel energy cofinal source criterion

- **ID:** `fcrj-theta-abel-energy-cofinal-source-criterion`
- **Stage:** 2 — fully proven on paper
- **Source route:** CCM-FU / FCRJ physical theta--Abel aperture
- **Theorem status:** Lean-proved

## Claim

Existence of one favorable continued source rectangle cannot be an RH converse, because rectangle
selection could discard an unstable spectral tail. The exact missing quantifier is packet
stability: after prescribing any finite multiplicity packet, an admissible rectangle containing it
must remain above one fixed eventual floor. For the unit physical theta--Abel energy family, this
cofinal source lower-bound property is equivalent to RH, with no premises.

## Gates

- [x] Exact paper statement and proof
- [x] Strongest positive survivor extracted
- [x] Direct Lean check and axiom audit
- [x] Targeted module build
- [ ] Publication-ready exposition

## Exact theorem

Let `F_n` be the exact unit physical-energy two-edge transform from Loop 77 at
`a=log(n)/2`, and let

```text
C_n(z1,z2)=(2 pi i)^-1 contour_[z1,z2]
  (F_n(z)^2 * continuedPrimeArchSourceRelativeTrace(z)).        (1)
```

For a finite multiplicity packet `t`, call `(z1,z2)` a source rectangle above `B` when

```text
z1.re<z2.re, z1.im<z2.im,
t is contained in the closed rectangle,
every point on all four edges is Xi-explicit-admissible,
B<=Re C_n(z1,z2).                                               (2)
```

Define packet-stable eventual source boundedness by

```text
exists B,N0, for every n>=N0 with 1<log(n)/2,
  for every finite packet t,
    exists a source rectangle above B containing t.             (3)
```

Lean proves the closed theorem

```text
(3) <-> RH.                                                      (4)
```

More generally `(4)` holds for every fixed `L,A,c>0`.

## Proof

For each fixed `n`, the divisor values `F_n(alpha_q)^2` are absolutely summable.

Assume RH. The complete Weil value is nonnegative. Given any prescribed packet `t`, absolute
summability supplies a finite tail-control packet `u`. Apply cofinal admissible rectangle selection
to `t union u`. The exact Guinand--Weil residue law identifies its normalized source contour with
the enclosed finite sum, which lies within `1` of the complete Weil value. Thus every `t` has an
admissible extension with source value at least `-1`; `(3)` holds with `B=-1` and `N0=0`.

Conversely, assume `(3)` and false RH. Loop 77 supplies, beyond the asserted `N0`, an aperture `n`
whose complete physical-energy Weil value is below `B-1`. Absolute summability supplies a finite
packet `t` such that every finite superset sum is within `1/2` of that complete value. Property
`(3)` gives an admissible rectangle containing `t` with contour real part at least `B`. But the
exact residue law makes that contour one of those finite superset sums, so its real part is below
`B-1/2`, contradiction.

The argument exposes why mere existence of one approximating rectangle is not enough and why the
universal packet quantifier is exactly sufficient.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyCofinalSourceCriterion.lean`
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Capstones:
  `XiPhysicalThetaAbelEnergySourceRectangleAbove`,
  `XiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow`,
  `exists_admissible_physicalThetaAbelEnergySourceContour_containing_approximates_weil`,
  `xiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow_iff_riemannHypothesis`,
  `unitPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow_iff_riemannHypothesis`

## No-go closure

Favorable contour selection is not a valid escape: the criterion must remain feasible after every
finite packet is forced into the rectangle. Absolute tail control then makes all such extensions
track the full Weil value. Conversely, RH needs no positivity theorem for individual finite
rectangles; a packet-containing rectangle within fixed distance of the nonnegative full value is
enough.

Remaining RH-bearing burden is now an exact source statement with no divisor sum or Weil value in
its conclusion: prove `(3)` directly from prime--archimedean source structure. Any producer that
only constructs one preferred rectangle per aperture is insufficient unless it is stable under
arbitrary finite-packet enlargement.

## Novelty audit

Classical ingredients are Weil positivity, Guinand--Weil residues, absolute convergence, and
cofinal finite-sum convergence. Corpus and primary-literature searches through 2026-08-27 found no
physical theta--Abel criterion with the packet-stable quantifier `(3)` or the two-directional
tail-control proof of `(4)`. Candidate-new content is restricted to the exact physical family,
the packet-stable source predicate, and equivalence `(4)`.

Primary comparison points:

- A. Weil, explicit-formula positivity criterion.
- A. Connes, C. Consani, M. Marcolli, *The Weil proof and the geometry of the adeles class space*,
  arXiv:math/0703392.
- A. Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for the truncated Weil
  quadratic form*, arXiv:2607.02828.
- M. Chuk, *Weil positivity in compact windows: certified two-sided bounds and a Landau--Widom
  decay law*, arXiv:2608.24827.

## Verification log

- 2026-08-27: corpus conjecture search completed before construction.
- 2026-08-27: targeted primary-literature audit completed.
- 2026-08-27: direct `lake env lean` check passed.
- 2026-08-27: scratch axiom audit passed with standard axioms only.
- 2026-08-27: targeted module build passed.

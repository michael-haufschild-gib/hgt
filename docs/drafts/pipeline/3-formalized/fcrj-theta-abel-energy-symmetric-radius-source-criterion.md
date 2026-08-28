# FCRJ theta--Abel energy symmetric-radius source criterion

- **ID:** `fcrj-theta-abel-energy-symmetric-radius-source-criterion`
- **Stage:** 3 — formalized in Lean 4
- **Source route:** CCM-FU / FCRJ physical theta--Abel aperture
- **Theorem status:** Lean-proved

## Claim

Arbitrary finite-packet quantification in the exact source criterion is unnecessary. The canonical
integral-radius boxes `[-m,m] × [-1,1]` exhaust every finite multiplicity-exact Xi packet because
all centered Xi points lie in `|Im z|<1/2`. Eventual lower boundedness of exact physical
theta--Abel continued-source contours along this single geometric exhaustion is unconditionally
equivalent to packet-stable cofinality and hence to RH. The unit specialization is closed and
premise-free.

## Gates

- [x] Exact paper statement and proof
- [x] Strongest positive survivor extracted
- [x] Direct Lean check and axiom audit
- [x] Targeted module build
- [ ] Publication-ready exposition

## Exact theorem

Let

```text
K_m = { Xi multiplicity copies q :
        xiSpectralPoint(q) in [-m,m] × [-1,1] }.              (1)
```

For the Loop-77 physical-energy transform at `a=log(n)/2`, define canonical symmetric-radius
eventual source boundedness by

```text
exists B,N0, for every n>=N0 with L<log(n)/2,
  for every m in N,
    exists an admissible source rectangle containing K_m
    whose normalized continued-source contour has real part >=B. (2)
```

Lean proves unconditionally

```text
(2) <-> packet-stable cofinal source boundedness,                (3)
```

and therefore, for every `L,A,c>0`,

```text
(2) <-> RH.                                                      (4)
```

The specialization `L=A=c=1` has no hypotheses.

## Proof

For a finite packet `t`, set

```text
R = 1 + sum_(q in t) |xiSpectralPoint(q)|.
```

Archimedean unboundedness supplies `m in N` with `R<m`. For every `q in t`,
`|Re xiSpectralPoint(q)|<m`. The unconditional centered-strip theorem gives
`|Im xiSpectralPoint(q)|<1/2<1`, hence `q in K_m`. Thus every finite packet is contained in one
canonical packet `K_m`.

If `(2)` holds, apply it to this `m`; any source rectangle containing `K_m` contains `t`, proving
packet-stable cofinality. Conversely, packet-stable cofinality applied to `K_m` proves `(2)`.
This proves `(3)` without RH or analytic assumptions. Loop 78 then yields `(4)`.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergySymmetricRadiusSourceCriterion.lean`
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Capstones:
  `xiZeroCopy_finset_subset_physicalThetaAbelEnergyCanonicalPacket`,
  `xiPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow_iff_cofinal`,
  `xiPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow_iff_riemannHypothesis`,
  `unitPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow_iff_riemannHypothesis`

## No-go closure

The arbitrary finite-packet interface from Loop 78 is not intrinsic. One countable, nested,
source-geometric exhaustion already forces every possible tail-control packet. No packet choices,
enumerations, or adaptive divisor ordering remain in the final criterion.

Remaining RH-bearing burden is sharper and canonical: prove one aperture-independent eventual
lower floor for exact physical-energy source contours enclosing every integral-radius box `K_m`.
It is still insufficient to produce one preferred contour at each aperture and radius unless its
value is bounded below uniformly in both indices.

## Novelty audit

Classical ingredients are the Xi critical-strip inclusion, Archimedean exhaustion, Weil positivity,
and Guinand--Weil residues. Corpus and primary-literature searches through 2026-08-27 found no
canonical integral-box reduction of the packet-stable physical theta--Abel continued-source RH
criterion. Candidate-new content is restricted to the unconditional equivalence `(3)` and exact
source criterion `(4)`.

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
- 2026-08-27: scratch and built-module axiom audits passed with standard axioms only.
- 2026-08-27: targeted module build passed.
- 2026-08-27: formal lint reports only pre-existing unrelated unreachable modules; new module is
  reachable from `GaloisForLFunctions.RHTower`.

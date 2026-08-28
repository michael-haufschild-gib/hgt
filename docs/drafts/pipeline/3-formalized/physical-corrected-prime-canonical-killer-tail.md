# Physical corrected-prime canonical killer tail

- **ID:** `physical-corrected-prime-canonical-killer-tail`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Source route:** CCM-FU / PPM / physical theta--Abel corrected-prime contour
- **Statement:** Cofinal tails of deterministic canonical-radius killer packets exist exactly when RH is false.

## Goal

Eliminate arbitrary packet choice from the persistent corrected-prime obstruction. Loop 84 shows
that false RH creates some finite copied-zero core forcing every admissible enclosing contour below
a prescribed floor. This theorem replaces that core by the fixed canonical centered-box exhaustion
and proves that every sufficiently large radius is hostile.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, route passport
- [x] 1 → 2 fully-proven: complete paper proof, no open dependency
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper

## Exact theorem

Write `P_m` for the multiplicity-exact copied Xi zeros in the centered box
`[-m,m] × [-1,1]`. Lean proves

```text
m <= k -> P_m subset P_k.                                   (1)
```

Corrected-prime killer behavior is upward-closed:

```text
t is killer and t subset u -> u is killer.                  (2)
```

Every finite copied-zero packet lies in some `P_m`. Therefore, at each fixed physical scale and
floor,

```text
[some finite killer packet exists]
  <-> [exists m0, every P_m with m>=m0 is killer].           (3)
```

A strict upper bound for complete physical theta--Abel Weil energy consequently forces a whole
canonical-radius killer tail. For every `L,A,c>0`, Lean proves the deterministic dual criterion

```text
[for every B,N0, some n>=N0 with L<log(n)/2 has
  an m0 such that every canonical P_m, m>=m0,
  forces every admissible enclosing corrected-prime contour below B]
    <-> not RH.                                               (4)
```

A premise-free unit-parameter specialization is included.

## Proof

Membership in `P_m` is exactly membership of the spectral point in
`[-m,m] × [-1,1]`; interval inclusion proves `(1)`. If every rectangle containing `t` is below the
floor and `t⊆u`, every rectangle containing `u` also contains `t`, proving `(2)`. Corpus cofinality
of canonical packets embeds any finite killer `t` in some `P_m0`; `(1)--(2)` propagate killer
behavior to all later radii. Conversely, one member of a canonical killer tail is already a finite
killer packet. This proves `(3)`.

Loop 84 identifies cofinal existence of arbitrary killer packets with false RH. Substituting the
exact classification `(3)` gives `(4)`. The result makes no new analytic assumption and performs no
numerical zero verification.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeCanonicalKillerTail.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS (`11807/11807`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `correctedPrimeKillerPacket_mono`,
  `xiPhysicalThetaAbelEnergyCanonicalPacket_mono`,
  `XiPhysicalThetaAbelEnergyCanonicalRadiusKillerTail`,
  `exists_correctedPrimeKillerPacket_iff_canonicalRadiusKillerTail`,
  `canonicalRadiusKillerTail_of_weil_re_lt`,
  `not_riemannHypothesis_implies_canonicalRadiusKillerTails_cofinally`,
  `canonicalRadiusKillerTailsCofinal_iff_not_riemannHypothesis`,
  `unitCanonicalRadiusKillerTailsCofinal_iff_not_riemannHypothesis`

## Route impact and positive survivor

Packet selection is no longer an open freedom. Under false RH, hostility does not depend on a
carefully tailored finite set: a deterministic, symmetric, integral-radius exhaustion eventually
consists entirely of killer packets. Thus any prime-side lower-floor proof may be tested against
one canonical family. Remaining RH burden is to show that at some eventual scale/floor the
canonical killer tail cannot occur, equivalently to exhibit one sufficiently large radius with an
admissible enclosing corrected-prime contour above the floor.

Strongest positive survivor is the scale-local classification `(3)`, independent of RH and of the
physical transform: every upward-closed finite divisor obstruction on this cofinal packet system is
equivalent to a canonical tail obstruction.

## Novelty audit

Targeted corpus and primary-literature searches through 2026-08-27 found no deterministic
centered-box tail formulation of the every-enclosing-rectangle corrected-prime obstruction.
Related work studies compactly supported Weil tests, finite-interval operators, finite-prime
spectral approximations, and numerical or analytic zero exhaustions. None gives the exact
upward-closed classification `(3)` or its physical prime-contour duality `(4)`. Candidate-new
content is restricted to this route-specific synthesis.

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

- 2026-08-27 — Mandatory corpus search exposed monotone cofinal canonical packet exhaustion.
- 2026-08-27 — Conjectured and proved upward-closed killer-tail classification.
- 2026-08-27 — Direct check, umbrella wiring, targeted module build, and axiom audit passed.
- 2026-08-27 — Targeted current-literature search found no exact canonical killer-tail theorem.
- 2026-08-27 — Global lint reached the wired module with no local violation; repository-wide gate
  remains blocked by unrelated concurrently edited unwired RHTower/HTGeometry modules.

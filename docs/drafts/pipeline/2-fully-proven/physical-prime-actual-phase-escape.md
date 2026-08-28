# Physical prime actual phase escape

- **ID:** `physical-prime-actual-phase-escape`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / NO-GO (Lean)
- **Source route:** D2 / FCRJ physical corrected-prime contour
- **Statement:** At every D2 point and every positive physical window triple, actual two-edge
  transform phase escapes the real axis at arbitrarily late translations.

## Goal

Close Loop 90's remaining loophole that the particular physical transform might be real throughout
the off-axis D2 locus despite generic symmetry insufficiency.

## Gates

- [x] 0 → 1 in-progress: corpus-derived two-exponential phase conjecture
- [x] 1 → 2 fully-proven: dependency-closed paper proof and no-go classification
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem/no-go note

## Conjecture C91

For `Re w != 0`, `Im w != 0`, and nonzero leading edge coefficient `P`, the real-translation family
`exp(a w)P + exp(-a w)Q` has nonreal values beyond every real threshold. Apply this to the actual
physical one-edge amplitudes at `w=s-1/2` and `-w`, whose factors are nonzero throughout D2's open
strip for `L,A,c>0`.

## Exact theorem

Define

```text
F(a)=exp(a w)P+exp(-a w)Q.
```

For arbitrary complex `Q`, Lean proves

```text
Re w != 0, Im w != 0, P != 0
  => for every R, some a>=R has Im(F(a))!=0.                (1)
```

The physical one-edge coefficient obeys the strip-wide noncensorship law

```text
L,A,c>0, -1/2<Re w<1/2, Re w!=0
  => xiPhysicalThetaAbelEntireModeAmplitude(L,A,c,w)!=0.   (2)
```

For a Gaussian-rational D2 point `s`, its physical contour coordinate `z=-i(s-1/2)` satisfies
`i z=s-1/2`. Combining `(1)--(2)` gives

```text
for every R, some a>=R has
  Im(xiPhysicalThetaAbelEnergyTwoEdgeTransform(L,A,c,a,z)) != 0. (3)
```

Loop 90's exact square-order classifier then yields

```text
for every R, some a>=R has
  not ComplexRealPartMonotoneMultiplier(T(a,z)^2).         (4)
```

Thus actual physical phase reality does not merely fail to follow from generic symmetry: it fails
cofinally at every D2 point for every positive physical window triple.

## Proof

The exact recurrence

```text
F(a+h)+F(a-h)=(exp(hw)+exp(-hw))F(a)                       (5)
```

holds for every real `a,h`. Choose `h=1/(2 Im w)`. Then `Im(hw)=1/2`, and

```text
Im(exp(hw)+exp(-hw))
  =(exp(h Re w)-exp(-h Re w)) sin(1/2) != 0.               (6)
```

For every real `b`, at least one of `F(b),F(b+1)` is nonzero. Otherwise the first equality gives
the cancellation of its two edges at `b`; substituting at `b+1` would force
`(exp(w)-exp(-w)) exp(bw)P=0`, impossible because `Re w!=0` and `P!=0`.

Assume all sufficiently late `F(a)` are real. Choose `b` late enough that `b`, `b+1`, and each
associated `+/-h` translate remain in that real tail. Apply `(5)` at whichever of `b,b+1` has
nonzero value. Its left side is real, while `(6)` times a nonzero real value has nonzero imaginary
part, contradiction. This proves `(1)`.

For `(2)`, the four physical factors are nonzero separately: the length-`L` window lies in one
open half-plane because `Re w!=0`; `w+1/2` cannot vanish inside the strip; the `c` window is in the
open right half-plane at `1/2-w`; and the `A` window is in the open left half-plane at `w-1/2`.
The D2 hypotheses give `-1/2<Re(s-1/2)<0` and `Im(s-1/2)!=0`, so `(1)` applies and proves `(3)`.
The already proved equivalence between square-weight monotonicity and real phase gives `(4)`.

## No-go closure

- **Exact killing theorem/mechanism:** `(3)--(4)` close Loop 90's actual-transform loophole. No
  pointwise D2 scalar-floor transport theorem can hold uniformly over cofinal translations through
  actual squared physical weights.
- **Strongest positive survivor:** exact recurrence `(5)`, strip-wide physical-amplitude
  noncensorship `(2)`, and cofinal actual phase escape `(3)`.
- **New insight:** off-critical displacement forces an intrinsic phase instability in the physical
  two-edge family. It is not an artifact of testing all even/Schwarz-real entire modes: every
  positive choice of physical windows exhibits cofinally late order-destroying phases.
- **Status:** dependency-closed; Lean module verified and wired.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeActualPhaseEscape.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct source check: PASS
- Targeted build: PASS (`12919/12919`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `twoEdgeExponentialMode_add_sub`,
  `twoEdgeExponentialMode_cofinally_nonreal`,
  `xiPhysicalThetaAbelEntireModeAmplitude_ne_zero_of_openStrip`,
  `xiPhysicalThetaAbelEnergyTwoEdgeTransform_cofinally_nonreal_at_gaussianRatD2`,
  `physicalTwoEdgeSquare_cofinally_not_realPartMonotone_at_gaussianRatD2`.

## Route impact and remaining burden

This retires actual off-axis phase reality as a uniform D2-to-physical positivity bridge. Any
surviving direct weld must pair conjugate contour contributions before applying order, control the
imaginary prime flux jointly with transform phase, or establish the corrected-prime floor by a
global arithmetic estimate. The theorem is over continuous real translations; it does not by
itself classify the route's discrete logarithmic aperture mesh.

## Novelty audit

Targeted corpus and primary-literature searches through 2026-08-28 found no theorem giving the
exact cofinal nonreal-phase law `(1)`, the physical strip noncensorship law `(2)`, or their D2
square-order consequence `(4)`. Current Weil/screw/operator work studies positivity and spectral
limits; current explicit logarithmic-derivative work controls zeta quantities, not this two-edge
physical phase recurrence. Candidate-new content is restricted to this exact route-specific
formal synthesis.

Primary comparison points:

- A. Chirre and B. Molero Ravines, [*Explicit conditional bounds for ζ(s) at the edge of the
  critical strip*](https://arxiv.org/abs/2602.06199).
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096).
- T. Kim et al., [*A Numerical Realization of Suzuki's Weil-Quadratic-Form Operator*](https://arxiv.org/abs/2607.24830).
- A. Connes and C. Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368).

## Log

- 2026-08-27 — Mandatory corpus search found exact two-edge exponential decomposition and window
  noncensorship, but no actual off-axis phase theorem.
- 2026-08-27 — Conjectured cofinal nonreal-phase escape using a two-step exponential recurrence.
- 2026-08-28 — Proved abstract recurrence escape and physical open-strip amplitude noncensorship.
- 2026-08-28 — Proved actual D2 phase escape and cofinal failure of squared-weight real-part
  monotonicity for every positive physical window triple.
- 2026-08-28 — Direct check, targeted `12919/12919` build, standard axiom audit, and umbrella
  wiring passed. Global lint reaches the new module with no local violation; repository-wide gate
  remains blocked only by unrelated unwired RHTower/HTGeometry modules.

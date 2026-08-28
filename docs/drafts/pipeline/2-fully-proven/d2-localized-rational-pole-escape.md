# D2 localized Gaussian-rational pole escape

- **ID:** `d2-localized-rational-pole-escape`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / exact RH and not-RH criteria (Lean)
- **Source route:** D2 pure-prime log-height defect
- **Statement:** Failure of RH forces D2's pure-prime log-height defect to tend to minus infinity
  along Gaussian-rational samples contained in one fixed rational rectangle compactly inside the
  left critical half-strip above the verified-height threshold.

## Goal

Strengthen the existing global law “for every floor, some high Gaussian-rational sample violates
it.” Prove that one hypothetical off-line zero produces all violations inside one fixed bounded
rational window. This identifies D2 failure as a local pole phenomenon and eliminates any need
for height escape.

## Gates

- [x] 0 → 1 in-progress: corpus-derived normalized-residue and rational-density attack
- [x] 1 → 2 fully-proven: dependency-closed paper proof and exact route classification
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem note and independent expert audit

## Exact theorem

For `s` in the positive-height left critical half-strip define the complex and scalar D2 defects

```text
D_C(s) = 2 * infinitePrimeFlux(s) - log(Im s),
D(s)   = Re D_C(s) = 2 Re(infinitePrimeFlux(s)) - log(Im s).
```

At every Xi zero `rho` with `0<Re rho<1` and `Im rho>0`, Lean proves the exact punctured limit

```text
(s-rho) D_C(s) -> -2 ord_rho(Xi).                         (1)
```

The log-height correction has zero residue. If `0<Re rho<1/2`, every rational rectangle `R`
containing `rho` with positive lower imaginary endpoint satisfies

```text
forall B in R, exists q in QxQ,
  gaussianRatPoint(q) in R and D(gaussianRatPoint(q)) < B. (2)
```

Call a rational rectangle admissible when its closed envelope obeys

```text
0 < u < v < 1/2,       233/20 < x < y.
```

Lean packages the localized failure law

```text
(exists one admissible R,
  forall B, exists Gaussian-rational q in R, D(q)<B)
    <-> not RiemannHypothesis.                            (3)
```

Equivalently,

```text
(every admissible R has a finite lower bound on D over its rational samples)
    <-> RiemannHypothesis.                                (4)
```

The localized violation can be chosen as one sequence in the same window:

```text
(exists admissible R and q_n in (QxQ)∩R,
  D(q_n) -> -infinity)
    <-> not RiemannHypothesis.                            (5)
```

## Proof

The corpus gives

```text
(s-rho) * zeta'(s)/zeta(s) -> ord_rho(Xi).
```

Since `infinitePrimeFlux=-zeta'/zeta`, its doubled contribution tends to minus twice the
multiplicity. Continuity of `log(Im s)` at positive height makes
`(s-rho)log(Im s)->0`, proving `(1)`.

The residue in `(1)` is nonzero at an Xi zero. Applying the coordinate-free opposite-residue
escape theorem inside a sufficiently small ball contained in `R` gives a point where `Re D_C<B`.
Zeros of zeta are isolated, so the ball is also chosen small enough that this point is regular.
At a regular point, `D_C` is continuous. The intersection of `R` with the strict sublevel set is
open and nonempty; Gaussian-rational density gives `(2)`.

Under false RH, choose a strict-right upper Xi zero. Functional-equation and Schwarz reflection
move it to a positive-height left-half zero. The formal verified-height certificate through
`243/20` and off-line strictness force its height above `243/20`, hence above the D2 threshold
`233/20`. Rational endpoint density places it inside one admissible `R`; `(2)` proves the forward
direction of `(3)`. Under RH, the corpus global D2 lower bound applies to every rational point of
every admissible window and contradicts localized escape. This proves `(3)--(4)`.

For `(5)`, choose the `n`th rational sample from `(2)` below `-n`; this sequence tends to `atBot`.
Conversely, RH's global lower bound prevents any such sequence.

## Strongest positive survivor and route impact

- **Exact killing mechanism:** One off-line zero creates a fixed bounded-height rational window
  on which D2's literal pure-prime defect has no lower bound.
- **Strongest positive survivor:** Exact residue `(1)`, local rational pole escape `(2)`, localized
  equivalences `(3)--(4)`, and the single rational divergence sequence `(5)`.
- **New insight:** D2 failure is not genuinely cofinal in height. All negative escape can be
  confined to one compact rational window around one divisor pole. Frequency escape in the prior
  global formulation was an artifact of its quantifiers, not the analytic mechanism.
- **Remaining burden:** Establish finite lower boundedness on every admissible rational window
  from unconditional prime arithmetic. Any proof may work window-by-window; no uniform bound
  across height is logically necessary.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/PrimeArchLogHeightDefectLocalizedRationalPoleEscape.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct source check: PASS
- Targeted build: PASS (`12923/12923`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `tendsto_primeArchLogHeightComplexDefect_normalizedResidue`,
  `exists_gaussianRat_primeArchLogHeightDefect_lt_in_ratRectangle_of_xiZero`,
  `exists_leftUpperXiZero_above_twoHundredThirtyThree_twentieths_of_not_rh`,
  `primeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow_iff_not_rh`,
  `primeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow_iff_rh`,
  `primeArchLogHeightDefectGaussianRatLocalizedTendstoAtBot_iff_not_rh`.
- Formal lint: new wired module clean; repository-wide lint remains blocked only by unrelated
  unwired dirty-tree modules.

## Novelty audit

Targeted corpus searches found the global D2 lower-bound equivalence, global/cofinal unboundedness
under false RH, normalized zeta residues, isolated zeros, and Gaussian-rational density. No corpus
theorem localized all D2 failure to one bounded rational window or produced one rational sequence
in that window tending to `-∞`.

Primary-literature searches through 2026-08-28 found mean-value and distribution results for
`zeta'/zeta`, local closest-zero expansions under RH and gap hypotheses, and omega theorems near
the 1-line. None states `(1)--(5)`, uses exact Gaussian-rational samples in one fixed left-strip
window, or gives this localized D2 RH/not-RH dictionary. Candidate-new content is restricted to
the exact route-specific synthesis proved here.

Primary comparison points:

- F. Ge, [*Mean values of the logarithmic derivative of the Riemann zeta-function near the
  critical line*](https://arxiv.org/abs/2211.08571).
- H. Ki, [*The zeros of the derivative of the Riemann zeta function near the critical line*](https://arxiv.org/abs/math/0701726).
- S. J. Lester, [*The distribution of the logarithmic derivative of the Riemann zeta-function*](https://arxiv.org/abs/1308.3597).
- Z. Li and S. Zhao, [*Omega Theorems for Logarithmic Derivatives of Zeta and L-functions Near the
  1-line*](https://arxiv.org/abs/2404.17250).

## Log

- 2026-08-28 — Mandatory corpus search found only global/cofinal D2 unboundedness, not fixed-window
  pole localization or a bounded-height rational witness sequence.
- 2026-08-28 — Proved exact complex-defect residue and regular-point continuity.
- 2026-08-28 — Proved Gaussian-rational strict-sublevel escape inside every containing rational
  rectangle.
- 2026-08-28 — Used formal verified height to place every hypothetical off-line witness above the
  D2 threshold and proved localized `not RH` equivalence.
- 2026-08-28 — Proved per-window boundedness iff RH and one-window rational sequence divergence
  iff `not RH`.
- 2026-08-28 — Direct source check, targeted `12923/12923` build, standard axiom audit, umbrella
  wiring, and local lint audit passed.

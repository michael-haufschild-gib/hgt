# Physical corrected-prime universal arithmetic cofinal contour

- **ID:** `physical-corrected-prime-arithmetic-cofinal-contour`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (Lean)
- **Source route:** CCM-FU / PPM / physical theta--Abel corrected-prime contour
- **Statement:** One least-coded rational, target-independent admissible rectangle sequence recovers every physical Weil energy as a corrected direct-prime contour limit.

## Goal

Remove Loop 87's dependence on copied-zero packets and target Weil energy when selecting contours.
Construct one countable rational pole-crossing sequence from geometric exhaustion and arithmetic
boundary admissibility alone, then prove that this same sequence works for every physical
theta--Abel detector.

## Gates

- [x] 0 → 1 in-progress: corpus-derived countable-selector conjecture and finite-avoidance attack
- [x] 1 → 2 fully-proven: dependency-closed proof
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and effective boundary-admission algorithm

## Exact theorem

Enumerate all pairs `(R,c) ∈ ℚ²`. At stage `m`, call a pair admissible when

```text
m+1 < R,
1/2 - 1/(m+2) < c < 1/2,
the boundary of [-R,R] × [-1,c] is Xi-explicit-formula admissible.   (1)
```

Every stage predicate is inhabited. Select its least natural-number code and call the resulting
corners `z₁(m),z₂(m)`. The selector depends only on `m`, rational enumeration, and boundary
admissibility: it contains no copied-zero packet, detector, physical scale, or target Weil value.
Lean proves

```text
for every finite t : Finset XiZeroCopy,
  eventually t ⊆ xiZeroCopyClosedRectangle(z₁(m),z₂(m)).     (2)
```

For every `A,c>0` and every physical detector scale `(L,a)`, let `C_m(L,A,c,a)` be the corrected
literal direct-prime contour on this universal rectangle. Then

```text
C_m(L,A,c,a) -> CompleteWeilEnergy(L,A,c,a).                (3)
```

For the raw normalized prime contour `P_m`,

```text
P_m(L,A,c,a) -> CompleteWeilEnergy(L,A,c,a)
                 -[exp(a/2) 2(1-exp(-L/2)) c A]^2.          (4)
```

Finally, for every `L,A,c>0`,

```text
[at every admissible logarithmic sample and every ε>0,
 eventually -ε < Re(C_m)]  <->  RH.                         (5)
```

A closed unit-parameter specialization is included.

## Proof

Fix `m`. Put the raw bounding box at horizontal radius `m+3`, bottom height `-1`, and top height
`1/2`. Its Xi divisor is finite. Rational density supplies `R` in `(m+2,m+3)` avoiding the finite
set of absolute zero ordinates and `c` in `(1/2-1/(m+2),1/2)` avoiding the finite set of centered
zero heights. The bottom edge is zero-free because every centered Xi zero has imaginary part
strictly greater than `-1/2`; the other three edges are zero-free by the two avoidance choices.
Elementary geometry also excludes the completed point `1`, proving boundary admissibility and
inhabitation of `(1)`.

Surjectively enumerate `ℚ²` and use `Nat.find` to select the least satisfying code. The radius tends
to infinity while the top height tends to `1/2`; every centered Xi point lies in the open strip
`(-1/2,1/2)`. Hence each point, and by finite-filter compactness each finite packet, is eventually
inside, proving `(2)`.

For a fixed physical detector its squared zero values are summable. The finite-set definition of a
sum therefore makes sums over any cofinal family of finite packets converge to the full `tsum`.
The residue theorem identifies each selected source contour with the corresponding finite copied-
zero sum, and pole crossing identifies source contour with corrected direct-prime contour. This
proves `(3)`. Subtracting the rectangle-independent explicit archimedean square proves `(4)`.
Weil positivity and logarithmic-mesh completeness then prove `(5)` by the same sharp negative-
epsilon separation used in Loop 87.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeArithmeticCofinalContour.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS (`11811/11811`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `XiPhysicalThetaAbelEnergyArithmeticBoxStage`,
  `exists_arithmeticBoxStage`,
  `xiPhysicalThetaAbelEnergyArithmeticBoxCode`,
  `xiPhysicalThetaAbelEnergyArithmeticBoxCode_minimal`,
  `eventually_finset_subset_xiPhysicalThetaAbelEnergyArithmeticRectangle`,
  `tendsto_xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample_weil`,
  `tendsto_xiPhysicalThetaAbelEnergyArithmeticPrimeSample_weil_sub_archSq`,
  `arithmeticAsymptoticallyNonnegative_iff_riemannHypothesis`,
  `unitArithmeticAsymptoticallyNonnegative_iff_riemannHypothesis`

## Route impact and remaining burden

This removes both zero-packet provenance and detector/target dependence from the contour schedule.
One rational rectangle sequence works simultaneously for every physical theta--Abel scale. Its
definition is still noncomputable because boundary admissibility is used as an undecidable
selection predicate, but it is zero-location-free and Weil-target-free.

Remaining RH burden is now sharply arithmetic: prove the zero-floor lower bound in `(5)` directly
for the fixed least-coded corrected-prime array. No contour existence, packet cofinality, Gamma
residue, or limiting argument remains. An effective algorithm for finding each admitted rational
box would strengthen constructivity but is not needed for `(2)--(5)`.

## Novelty audit

Targeted corpus and primary-literature searches through 2026-08-27 found no target-independent
least-coded rational pole-crossing exhaustion with the universal corrected-prime limit `(3)` and
RH criterion `(5)`. Groskin's finite Guinand--Weil dictionary treats finite Galerkin zero sums and
an omitted archimedean tail; Suzuki treats finite-interval operator limits; Connes's 2026 survey
discusses convergence from finite Euler products. None states this universal literal prime-contour
sequence or the single-square raw limit `(4)`. Candidate-new content is restricted to this exact
route-specific formal synthesis.

Primary comparison points:

- A. Connes, [*The Riemann Hypothesis: Past, Present and a Letter Through Time*](https://arxiv.org/abs/2602.04022).
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096).
- A. Groskin, [*A finite Guinand-Weil dictionary and archimedean tail order for the truncated Weil quadratic form*](https://arxiv.org/abs/2607.02828).
- T. Kim et al., [*A Numerical Realization of Suzuki's Weil-Quadratic-Form Operator*](https://arxiv.org/abs/2607.24830).
- A. Connes and C. Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368).

## Log

- 2026-08-27 — Mandatory corpus search exposed rational admissible rectangles, pole-crossing
  finite avoidance, and summable cofinal zero packets.
- 2026-08-27 — Explicit fixed-height/integer schedule failed: corpus has no theorem excluding Xi
  zeros at predetermined vertical ordinates. Pivoted to least-coded rational admissibility.
- 2026-08-27 — Proved rational stage inhabitation, minimal selector, and geometric cofinality.
- 2026-08-27 — Proved universal corrected/raw prime limits and sharp RH equivalence.
- 2026-08-27 — Direct check and targeted `11811/11811` build passed; standard axiom audit passed.
- 2026-08-27 — Global lint reached the wired module with no local violation; repository-wide gate
  remains blocked by unrelated concurrently edited unwired RHTower/HTGeometry modules.

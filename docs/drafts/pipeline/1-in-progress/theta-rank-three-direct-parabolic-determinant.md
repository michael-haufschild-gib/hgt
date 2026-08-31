# Theta rank-three direct parabolic determinant

- **ID:** S6G-DPD
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `theta-rank-three-projective-drift.md` · direct-determinant survivor
- **Statement:** Native rank-three D1 is positive on the Lean-proved refined parabolic theta cone, closing the finite S6F/TCD physical-orbit gate without proving projective-drift positivity.

## Goal

Prove unconditionally

```text
0 < thetaCuspFullReflectionEighthHankelCurvature x
```

for `0 < x < 137/2000`, using the actual source orbit and the refined cone

```text
(13/32+z²/32)z < v < (33/80+z²/16)z,
191/10+(37/5)z² < X,
0<z<3/10.
```

Together with existing seam and large-weight theorems, this discharges the remaining finite native
rank-three D1 gate. Cofinal/all-order landing remains separate.

## Gates

- [x] 0 → 1 in-progress: exact source-pure claim, hostile computation, and formal cone localization
- [ ] 1 → 2 fully-proven: computation-free direct determinant proof
- [ ] 2 → 3 formalized: exact D1 theorem and finite-interval assembly
- [ ] 3 → 4 publication-ready: integrate with full S6F/TCD landing

## Frontier

- `[CORPUS]` `thetaCuspModularProjectiveClocks_mem_refinedParabolicThinCone` proves the displayed
  cone unconditionally in Lean.
- `[CORPUS]` Native D1 is strictly positive at the modular seam and for `x≥137/2000`.
- `[LOCAL-RESEARCH]` Exact RunPod diagnostics on the larger old cone find D1 itself strictly
  positive, scale-increasing/scale-convex, and strictly concave in `w=z²`. Clock concavity reduces
  the diagnostic minimum to endpoint faces; the outer face is strictly decreasing in wall
  interpolation and minimizes at its upper corner. No output is admissible in the proof. Report:
  `../2-fully-proven/computations/2026-08-29-s6f-parabolic-d1-contact/REPORT.md`.
- `[LOCAL-RESEARCH]` Exact principal-minor reconstruction on the refined cone finds complete
  scale-velocity Hankel matrix `H_X` strictly positive definite: all diagonal, rank-two, and
  rank-three half-prism certificates are positive. This opens a Loewner/Jacobi proof of scale
  increase. Report:
  `../2-fully-proven/computations/2026-08-29-s6f-jacobi-variation/REPORT.md`.
- `[PROVED HERE][FORMALIZED]` The source-positive vector field belongs to an exact polynomial
  `sl₂` triple. In adapted coordinates `r=U+3B`, `b=B`,
  `k=Q+3/8-3B²/8`, its companion lowering field is exactly `∂b`, the scale field has
  weights `(1/2,1/2,1)`, and the source dynamics have a three-equation normal form. Formal module:
  `PolynomialODEJetRankThreeSourcePositiveSl2`.
- `[FALSIFIED][LEAN-PROVED]` A nonconstant finite graded Shapovalov carrier for this exact
  `sl₂` action cannot exist. Any finite homogeneous polynomial carrier has nonnegative Cartan
  weights with at least one positive weight, but `[E,F]=H` forces Cartan trace zero. Formal module:
  `PolynomialODEJetRankThreeSourcePositiveFiniteModuleNoGo`.
- `[FALSIFIED][LEAN-PROVED]` Passing to the full infinite polynomial carrier does not rescue any
  positive scalar-contravariant form. The affine vacuum extension `E1=0`, `FB=-1` forces its scalar
  star coefficient to vanish, while the positive lowest-weight string `Fr=0`, `Hr=2r` forces the
  same coefficient to be negative. Formal module:
  `PolynomialODEJetRankThreeSourcePositiveInfiniteContravariantNoGo`.
- `[FALSIFIED][LEAN-PROVED]` Restricting to an adapted-graded proper carrier containing the actual
  source D1 also cannot rescue a positive scalar-contravariant form. D1 has a nonzero positive
  adapted-weight boundary component; repeated lowering gives an exact finite vacuum string that
  forces the star coefficient to vanish and then violates positive definiteness. Formal module:
  `PolynomialODEJetRankThreeSourcePositiveD1CyclicContravariantNoGo`.
- `[FALSIFIED][LEAN-PROVED]` Dropping the grading assumption does not rescue a scalar carrier.
  Every source-`E,F`-stable polynomial submodule is automatically adapted-graded: `H=[E,F]`
  preserves it, and finite distinct-eigenvalue extraction recovers each adapted component. Thus no
  source-`sl2`-stable polynomial carrier containing D1 admits a positive scalar-contravariant form.
  Formal module: `PolynomialODEJetRankThreeSourcePositiveD1ScalarContravariantNoGo`.
- `[FALSIFIED — diagnostic]` Raw coefficientwise matrix-Bernstein positivity cannot explain
  `H_X`: every scale-square coefficient matrix has negative leading rank-two/rank-three pivots and
  every scale-cube coefficient matrix has negative determinant. Cross-scale cancellation is
  essential. Report: `../2-fully-proven/computations/2026-08-29-s6f-sl2-scale-structure/REPORT.md`.
- `[FALSIFIED — diagnostic]` Global reflected-fibre positive definiteness and its all-order Bochner
  completion fail at a six-point Toeplitz section. Finite-order-five positive definiteness survives
  21.12 million arbitrary-packet attacks and remains a stronger alternate route to D1. Report:
  `../2-fully-proven/computations/2026-08-29-reflected-fibre-positive-definite/REPORT.md`.
- `[FALSIFIED]` Naive factorization in source-positive or reconstructed-gap coordinates: D1 and
  its leading rank-two minor are irreducible over `QQ` there.
- `[FALSIFIED]` A higher alternating clock hierarchy: sign-corrected order four is already mixed.
- `[LITERATURE]` Planat--Solé (arXiv:2608.19160) proves a rank-two theta-kernel concavity theorem by
  autonomous phase space and polynomial shear, but not this rank-three D1 cone theorem. Salazar
  (arXiv:2606.31647) gives positive moment-representation mechanisms that do not apply to the
  reflected theta source.

## Active conjecture and hostile verdict

`[CONJECTURE TCD-D1-BOUNDARY-FLUX]` For every `0 < x < 137/2000`, if the literal raw theta D1
vanishes at `x`, then its canonical rank-three null-line boundary crossing is strictly positive.

Exact proof chain:

`positive singular-face boundary flux`
`⇔ global strict native D1 on x ≥ 0`
`→ finite TCD/S6F rank-three gate`
`→ cofinal all-order Hankel/Bezoutian landing`
`→ Weil positivity`
`→ RH`.

The first equivalence is already Lean-proved in
`ThetaCuspFullReflectionEighthBoundaryKreinFirstCrossing`. Therefore this conjecture closes the
whole finite gate rather than improving a numerical chamber. A theta-state singular face with
nonpositive crossing kills the first-crossing/TCD route.

Verdict: `ACTIVE — EXACT ROUTE-CLOSING CORE`.

`[OPEN CORE]` Eliminate one projective coordinate using the singular equation inside the
Lean-proved refined `(R,z,v)` cone, then orient the resulting boundary-crossing polynomial. Generic
finite Hankel geometry cannot orient it: a strict-head singular negative-crossing witness is
already formalized. Theta source dynamics are indispensable.

## Representation lesson

Projective drift asked for global monotonicity of D1, which is stronger than positivity. Correct
primitive is the determinant chamber itself. Its source dynamics are one-sided in scale and
second-order in clock square; complete monotonicity and source-coordinate factorization are false.
The next proof should use determinant second variation or Schur-complement geometry, not another
coefficient hierarchy.

## Log

- 2026-08-29 — Direct-cone diagnostic survives on the larger formal cone; exact boundary geometry
  and factorization/hierarchy kills independently verified.
- 2026-08-29 — Dangerous upper-clock and scale faces tightened by a computation-free paper proof
  and exact Lean theorem; active core moved from drift positivity to direct D1 positivity.
- 2026-08-29 — Exact hostile tests killed all-order reflected-fibre Bochner completion at six
  points and opened strict Loewner scale velocity as conceptual D1 scale mechanism.
- 2026-08-29 — Exact `sl₂` source structure formalized; raw matrix-Bernstein Gram killed.
- 2026-08-29 — Finite graded contravariant-form route killed unconditionally: Cartan weights are
  nonnegative, while finite `[E,F]=H` trace must vanish. Positive survivor is necessarily
  infinite graded with convergence, or a direct cross-scale congruence.
- 2026-08-29 — Full infinite scalar-contravariant carrier killed unconditionally: vacuum extension
  forces scalar star coefficient `0`, while the positive lowest-weight string forces it `<0`.
  Surviving representation must be proper/localized or non-scalar; direct cross-scale congruence
  remains the clean survivor.
- 2026-08-29 — Adapted-graded proper carriers containing actual source D1 killed unconditionally:
  a boundary-detected positive-weight component lowers to a finite vacuum string incompatible with
  positive scalar contravariance. Only automatic-grading, non-scalar/localized/indefinite, or direct
  cross-scale survivors remain.
- 2026-08-29 — Automatic grading proved by finite Cartan spectral extraction. This kills every
  positive scalar-contravariant source-`sl2` polynomial carrier containing D1, including all
  non-graded proper carriers. Only non-scalar/localized/indefinite or direct cross-scale survivors
  remain.
- 2026-08-29 — Replaced stronger-than-needed global drift/concavity target by exact
  `TCD-D1-BOUNDARY-FLUX`: positive canonical flux on every singular face is already equivalent in
  Lean to global strict D1 and therefore closes finite TCD/S6F gate outright.

## 2026-08-30 finite matrix-channel contravariant route kill

`[FALSIFIED][LEAN-PROVED]` No nonempty finite channel dimension admits a positive-definite
matrix-valued contravariant source-`sl₂` carrier containing actual D1, for either canonical left or
right action of an arbitrary matrix coefficient. The D1-generated vacuum string supplies nonzero
`u,v` with `Eu=0`, `Fv=u`, and `Ev≠0`. Contravariance on `(u,v)` makes the positive-definite matrix
`⟨u,u⟩` annihilate the coefficient, so invertibility forces that coefficient to vanish;
contravariance on `(v,Ev)` then forces the positive-definite matrix `⟨Ev,Ev⟩` to vanish.

Formal capstone:
`modularThetaSourcePositive_no_D1_finiteMatrixContravariantCarrier` in
`PolynomialODEJetRankThreeSourcePositiveD1MatrixContravariantNoGo`.

Exact proof-chain consequence: the proposed finite non-scalar representation step

```text
finite positive matrix-channel source-sl₂ carrier containing D1
→ Gram/Shapovalov positivity for native rank-three D1
→ finite TCD/S6F gate
→ cofinal all-order landing
→ Weil positivity
→ RH
```

is impossible. Remaining representation-theoretic survivors must be genuinely infinite-channel,
localized/singular, or indefinite/Krein. Direct cross-scale Hankel/singular-face geometry remains
the clean positive survivor and `TCD-D1-BOUNDARY-FLUX` remains the route-closing open core.

## 2026-08-30 infinite positive operator-channel contravariant route kill

`[FALSIFIED][LEAN-PROVED]` Passing from finite matrices to bounded operators on an arbitrary
nontrivial complete complex Hilbert channel does not rescue the positive contravariant-form route.
For every nonzero carrier vector, literal strict operator positivity makes its diagonal pairing
operator injective and gives it dense range, without coercivity or invertibility. The exact
D1-generated vacuum string then forces the channel coefficient to vanish for either canonical
left/right action and subsequently forces the strictly positive diagonal at `Ev ≠ 0` to be zero.

Formal capstone:
`modularThetaSourcePositive_no_D1_infiniteOperatorContravariantCarrier` in
`PolynomialODEJetRankThreeSourcePositiveD1InfiniteOperatorContravariantNoGo`.

Exact proof-chain consequence: the surviving representation proposal

```text
positive bounded infinite operator-channel source-sl₂ carrier containing D1
→ operator-valued Gram/Shapovalov positivity for native rank-three D1
→ finite TCD/S6F gate
→ cofinal all-order landing
→ Weil positivity
→ RH
```

is impossible. This strictly strengthens the finite matrix-channel no-go: channel dimension may be
infinite or nonseparable, and no determinant, compactness, or uniform lower spectral bound is used.
The strongest positive survivor is also formalized: strict diagonal quadratic positivity implies
both injectivity and dense range. Therefore only singular/unbounded operator pairings,
indefinite/Krein pairings, or noncontravariant direct cross-scale Hankel geometry survive.

`[NOVELTY AUDIT]` Corpus search found no bounded infinite operator-channel D1 theorem before this
module. Primary literature located standard scalar contravariant Hermitian/Shapovalov forms and
general positive operator-valued kernels/GNS constructions, but no source-specific vacuum-string
obstruction for bounded operator-valued contravariant forms. Priority claim remains limited to
the searched corpus and sources.

## 2026-08-30 algebraic zero-divisor classification and regular-star route kill

`[FALSIFIED][LEAN-PROVED]` Boundedness, positivity, channel dimension, and Hilbert topology are not
the source of the contravariant obstruction. For values in any nontrivial nonunital ring, every
right contravariant carrier containing actual D1 has a nonzero source vector whose diagonal pairing
is not left regular. For values in any nontrivial involutive ring, the same holds for every left
contravariant carrier whose diagonals are Hermitian. Thus neither canonical side admits a carrier
whose nonzero diagonals are all left regular.

Formal positive-survivor classifiers:

- `ModularThetaSourcePositiveD1RightStarAlgebraContravariantCarrier.exists_nonzero_diagonal_not_leftRegular`;
- `ModularThetaSourcePositiveD1LeftStarAlgebraContravariantCarrier.exists_nonzero_diagonal_not_leftRegular`.

Formal no-go capstone:
`modularThetaSourcePositive_no_D1_regularStarAlgebraContravariantCarrier` in
`PolynomialODEJetRankThreeSourcePositiveD1StarAlgebraZeroDivisorNoGo`.

The mechanism is the exact D1 vacuum string `Eu=0`, `Fv=u`, `Ev≠0`. If `pair(u,u)` is left
regular, contravariance forces the coefficient to vanish. On the left side, diagonal Hermiticity
and the faithful involution reverse the zero product before cancellation. Contravariance at
`(v,Ev)` then makes `pair(Ev,Ev)=0`, so that diagonal is not left regular. No analytic assumption
enters.

Exact proof-chain consequence:

```text
regular algebra-valued contravariant source-sl₂ carrier containing D1
→ singular/unbounded or indefinite Gram/Shapovalov realization
→ finite TCD/S6F gate
→ cofinal all-order landing
→ Weil positivity
→ RH
```

is impossible. Any remaining contravariant realization must now carry an actual diagonal zero
divisor on the D1 cyclic string; merely becoming infinite-dimensional, unbounded, localized, or
indefinite is insufficient. Direct theta-specific null-line orientation remains the clean survivor
and `TCD-D1-BOUNDARY-FLUX` remains the finite route-closing open core.

`[NOVELTY AUDIT]` Corpus search found no D1 zero-divisor classification before this module.
Literature located scalar nondegenerate Shapovalov forms, classifications of scalar contravariant
forms, and Cartan-algebra-valued universal forms, but no source-D1 theorem forcing a non-left-regular
diagonal in every algebra-valued contravariant carrier. Priority remains provisional pending
independent expert review.

## 2026-08-31 positive-entire lower-jet spectral-flux route kill

`[FALSIFIED][LEAN-PROVED]` Positivity, entire analyticity, and the complete current reflected jet
through order eight cannot orient a singular rank-three boundary crossing. The positive entire
family

```text
F_c(z)=cosh(z) exp(c z^9/9!)
```

has one fixed depth-eight jet. Its common reflected moment face is `(1,2,8,32,128)`, with zero
rank-three determinant and strict leading minor `4`, but its canonical crossing is exactly `32c`.
Thus every crossing sign and every real crossing value occur without changing the current face.

Formal capstone:
`reflectedBoundaryNinthJetCrossingSign_not_determinedBy_lowerJet` in
`ThetaCuspFullReflectionEighthBoundaryNinthJetTorsorNoGo`. The exact positive survivor is
`reflectedBoundaryNinthJetCrossing_eq`, the affine ninth-jet torsor law.

Exact proof-chain consequence:

```text
positive entire source + reflected moments through order eight
→ positive singular-face boundary flux
→ strict native D1
→ finite TCD/S6F gate
→ cofinal all-order landing
→ Weil positivity
→ RH
```

is impossible at its first implication. The active `TCD-D1-BOUNDARY-FLUX` conjecture survives only
in its literal theta-specific form: it must control the ninth source jet/projective drift, not infer
orientation from lower moment geometry. Failed-route card:
`../5-failed/s6f-positive-entire-lower-jet-boundary-flux.md`.

## 2026-08-31 strict Schur-tail premise discharged

`[PROVED][LEAN-PROVED][SIGNIFICANT PREMISE DISCHARGED]` The complete-theta rank-three polynomial
has the exact Schur normal form

```text
D1 = (4A²-B)(1216A⁴-32A²B+68B²-D) - (C-64A³)².
```

Both diagonal factors are now unconditionally strict on the entire physical half-line. The head
`4A²-B` follows from the already proved literal fourth-jet inequality. The new theorem
`thetaCuspFullReflectionEighthSchurTail_pos` proves

```text
0 < 1216A⁴ - 32A²B + 68B² - D
```

for the actual complete-theta jets, without a compact-interval subdivision. Its proof completes
the `B`-quadratic exactly and uses the global first-atom eighth-jet domination plus strict eighth
likelihood positivity. Formal module:
`ThetaCuspFullReflectionEighthSchurTail`.

Exact proof-chain consequence:

```text
(C-64A³)² < (4A²-B)(1216A⁴-32A²B+68B²-D)
→ strict native D1
→ finite TCD/S6F gate
→ cofinal all-order Hankel/Bezoutian landing
→ Weil positivity
→ RH.
```

The theorem
`thetaCuspFullReflectionEighthHankelCurvature_pos_iff_schurCoupling` proves the first equivalence
exactly. Therefore diagonal degeneration is no longer a possible S6F failure mode; the sole
surviving source premise is a normalized sixth-jet correlation bound. On a singular face it is
the rigid equality `(C-64A³)²=(4A²-B)(1216A⁴-32A²B+68B²-D)`, so subsequent boundary-flux work may
differentiate one correlation saturation law instead of the original eight-term determinant.

`[NOVELTY AUDIT]` Mandatory corpus search found neither this Schur normal form nor global positivity
of its transformed eighth diagonal. The primary literature audit found general reflection/Hankel
positivity and total-positivity frameworks, but no theorem for this complete-theta log-jet reserve.
Priority remains provisional pending independent expert review.

## 2026-08-31 static modular-chamber conjecture under hostile test

`[CONJECTURE TCD-D1-STATIC-CHAMBER]` Let `(Z,R,S)` be real reduced modular data and put
`A=R²(1-Z²)`, `W=(2/3)S-RZ`. Test whether the complete known local physical chamber

```text
-3/10 < Z < 0,  R>0,  S<0,  A>0,  W>0,
18 < 2S²+3A,  -S/3 < W
```

forces positivity of the universal Lyapunov rank-three D1 polynomial. Exact intended proof chain:

```text
static chamber implication at every putative singular face
→ positive projective boundary flux
→ global native D1
→ finite TCD/S6F gate
→ cofinal all-order Hankel/Bezoutian landing
→ Weil positivity
→ RH.
```

This is stronger than source/gap positivity: it includes every strict Lyapunov inequality already
proved on the actual positive theta orbit and the projective clock cap on the whole missing
interval. The conjecture is undergoing hostile falsification before any orbit-specific proof.

`[NOVELTY AUDIT]` Mandatory corpus search found no theorem or counterexample for this combined
strict chamber. Primary arXiv searches found general Painlevé/Hankel differential systems but no
complete-theta reflected D1 result with these modular coordinates. Priority remains provisional.

## 2026-08-31 static modular-chamber route killed

`[FALSIFIED][LEAN-PROVED]` The combined static chamber does not force D1.  The reduced modular ray

```text
Z=-t,  R=5/2,  S=-t,
A=R²(1-Z²)=(25/4)(1-t²),
W=(2/3)S-RZ=(11/6)t
```

enters, for sufficiently small `t>0`, every strict local chamber currently proved for the missing
physical interval: `-3/10<Z<0`, positive scale/gap/shear, `18<2S²+3A`, and `-S/3<W`.  Nevertheless
the universal Lyapunov D1 remains strictly negative.  Mechanism: at `t=0` this ray meets the exact
rational seam state `R=5/2`, where D1 is negative; polynomial continuity makes the negative chamber
open along the ray.

Formal capstone:
`HTGeometry.modularThetaLyapunov_strictClockChamber_not_sufficient_for_D1` in
`PolynomialODEJetRankThreeStaticPhysicalClockChamberNoGo`.

Exact proof-chain consequence: the implication

```text
known strict Lyapunov/source signs + projective clock localization
→ D1 positivity or positive singular-face flux
→ finite TCD/S6F gate
→ cofinal all-order landing
→ Weil positivity
→ RH
```

is impossible at its first step.  Strongest positive survivor is the open-ray penetration theorem
`exists_rightNeighborhood_modularThetaLyapunov_strictClockChamber_D1_neg`: failure is robust, not
confined to a boundary point.  Therefore `TCD-D1-BOUNDARY-FLUX` must use actual centre-anchored theta-orbit
incidence, or a strictly stronger dynamical invariant; no refinement assembled only from the
already proved static chamber signs can close D1.

`[NOVELTY AUDIT]` Mandatory corpus search found the weaker source/gap seam obstruction but not this
strict reduced-clock penetration or combined-chamber no-go.  Primary arXiv searches found general
Painlevé/Hankel differential systems but no complete-theta theorem or counterexample in these
coordinates.  Priority remains provisional pending independent expert review.

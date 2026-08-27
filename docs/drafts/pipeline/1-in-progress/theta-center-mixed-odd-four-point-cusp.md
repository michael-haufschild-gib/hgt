# Theta center-mixed odd four-point cusp

- **ID:** `theta-center-mixed-odd-four-point-cusp`
- **Stage:** 1-in-progress
- **Type:** THEOREM / TCD singular-RKHS finite-rank advance
- **Scientific status:** `[NOVEL GLOBAL C1] [PAPER-PROVED] [LEAN-PROVED] [LOCAL FOUR-POINT POSDEF CLOSED] [TCD COFINAL OPEN]`
- **Source:** literal theta-cusp center-mixed density and its completed reflected jet
- **Statement:** For every physical aperture `0 < a < 1/2`, the second--sixth
  Hankel margin of `f_a(t) = thetaCuspCenterMixedDensity a t` is strictly positive:

  ```text
  f_a''(0) f_a^(6)(0) - f_a^(4)(0)^2 > 0.             (C1)
  ```

  Consequently the reflection-odd parity wall of the equispaced four-node
  Gram matrix is strictly positive for all sufficiently small positive gaps.
  Together with the already proved even wall, this gives a genuine local
  four-node positive-definite/PSD chamber for the source current whose full
  positive definiteness is RH-equivalent.

## Exact frontier

Corpus supplies:

1. strict positivity, decay, and global order-three positive definiteness of
   `thetaCuspCenterMixedDensity`;
2. `C^6` source-integral jet construction and strict fourth Hankel margin;
3. the exact equispaced four-point parity decomposition;
4. local positivity of the even parity wall;
5. the generic identity that the odd wall's first nonzero jet, at order eight,
   is `10080 * (f''(0) f^(6)(0) - f^(4)(0)^2)`;
6. strict second--sixth reflected Hankel curvature for every individual
   theta Born--Witten atom; and
7. complete-source logarithmic jets through order six plus summable
   higher-atom derivative transport.

At card opening no corpus theorem proved (C1), the local odd wall, or a four-node chamber.  This
card now proves all three; only the all-order/cofinal TCD landing remains open.

## Conjecture loop

### C1 — pointwise reflected-curvature mixture

Prove strict positivity of `thetaCuspFullReflectionSixthCurvature u` for every
`u > 0`, then integrate reflected fibres.  Weighted Cauchy--Schwarz would give
(C1) if each fibre has consistently signed second/fourth/sixth jets.

**Risk:** sixth reflected curvature need not be preserved by arbitrary
positive mixtures.  Proof must use theta likelihood-ratio scale separation,
not generic mixture closure.

### C2 — pair-expanded derivative Gram

Expand the complete theta source into atom pairs before taking the reflected
jets.  Seek a positive `2 x 2` moment Gram for every ordered atom pair and use
strictness from the first atom plus one higher atom.  This avoids taking the
logarithm of a mixture.

**Pivot condition:** one explicit pair has wrong second--sixth determinant.

### C3 — direct center-mixture covariance

Write `-f''(0)`, `f^(4)(0)`, and `-f^(6)(0)` as weighted moments of one
source-normal observable on the joint radial/atom-pair carrier.  Then (C1) is
strict Cauchy--Schwarz; equality would force that observable constant on a
carrier containing distinct theta scales.

**Pivot condition:** jets cannot be represented by one nonnegative carrier
without assuming Fourier positivity.

## RH/TCD significance

The reduced `L2` theta-convolution defect is dense and erases the divisor,
while a faithful positive full-jet Hilbertization is RH plus simplicity.
This card attacks the first presently unproved finite-rank chamber of the
source-derived singular/RKHS orientation instead of postulating that terminal
Hilbertization.  A proof raises the irreducible support size of every possible
negative source-orientation witness from four to at least five near the
coalesced chamber and supplies the next completed reflected-jet constraint.

## Gates

- [x] exact corpus frontier audited
- [x] August 2026 primary-literature collision audit
- [x] C1 proved globally
- [x] C2 bypassed by the global source theorem
- [x] C3 realized as a signed-fibre positive two-by-two matrix mixture
- [x] dependency-closed paper proof
- [x] hostile fake-kernel audit
- [x] Lean theorem with no added axioms for global source curvature, C1, odd wall, and local four-point positive definiteness
- [x] targeted leaf build and axiom/lint audit
- [x] wire into `RHTower.lean`

## Log

- 2026-08-27 — Card opened from TCD frontier after exact corpus search.  The
  source-to-Xi jet landing is already unconditional; missing Kummer root is an
  RH-equivalent receiver.  The first nonterminal source advance is instead
  the reflection-odd four-point cusp, reduced exactly to (C1).

### 2026-08-27 — C1a modular-seam theorem

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

The first serious C1 attack by separate complete-source log-jet bounds failed:
the available sixth-likelihood envelope is too coarse and does not preserve
the modular cancellation.  Pairwise and dominant-tail decompositions failed
for the same reason.  Pivot retained the full four-state modular ODE through
eighth order.

For `M = theta_3(i)`, `R = pi M^4`, `X = R^2`, and source seam jets
`f_j = Phi^(j)(0)`, exact ODE elimination now proves

```text
f_0^2 (f_2 f_6 - f_4^2) + 9 f_0 f_2^2 f_4 - 9 f_2^4
  = M^4 P_ref(X),
```

where

```text
P_ref(X) = 127575/4096 - (1828575/16384)X
  + (6333795/65536)X^2 - (7447545/262144)X^3
  + (397305/262144)X^4 - (48411/262144)X^5
  + (229545/8388608)X^6 + (225/1048576)X^7
  - (375/33554432)X^8.
```

This differs essentially from the previously formalized Gaussian-aperture
polynomial: its leading coefficient is negative, so the old one-sided
`X > 191/10` chamber cannot prove the sign.  Existing exact `exp(-pi)`
enclosure plus a geometric theta-series majorant gives the new upper bound
`X < 20`.  Expanding `P_ref(191/10 + y)` for `0 <= y <= 1` leaves positive
terms through degree five; the positive constant alone strictly dominates
all three negative degree-six, seven, and eight terms.  Hence `P_ref(X) > 0`
on the actual bounded chamber.

At the even seam, odd source jets vanish, and the native reflected-product
determinant is exactly four times this modular invariant.  Therefore

```text
thetaCuspFullSourceReflectionSecondSixthCurvature 0 > 0.
```

Smoothness then gives an unconditional `delta > 0` on which the same strict
curvature holds for every `|x| < delta`.  This is the first completed-source
open interval of strict reflected second--sixth curvature in the corpus.  It
closes the modular-center part of C1 but not the global radial carrier or the
weighted mixture step needed for the center-mixed margin.

Primary-literature audit found no statement of this reflected theta-source
polynomial or bounded chamber.  Closest August 2026 result is Planat--Solé,
*Second-Level Concavity of the Riemann Xi Kernel* (arXiv:2608.19160), proving
second-level concavity/double Turán for a different Xi-kernel transform using
finite-interval certificates.  It neither states this modular seam invariant
nor proves the center-mixed four-node odd wall.

Lean artifacts:

- `HTGeometry.modularThetaSixthSeamJetEliminationPair`;
- `HTGeometry.modularThetaReflectedSixthSeamClosure_of_ode`;
- `thetaCuspFullSource_reflectedSixthSeam_eq_modularClosure`;
- `thetaCuspReflectedSixthSeamModularPolynomial_source_pos`;
- `thetaCuspFullSourceReflectionSecondSixthCurvature_zero_pos`;
- `exists_thetaCuspFullSourceReflectionSecondSixthCurvature_pos_near_zero`.

Audit: direct `lake env lean` passed; targeted leaf build passed; formal lint
passed; `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`.  No hypothesis, new axiom, `sorry`, `admit`, `opaque`, or
`unsafe` declaration was introduced.

Next conjecture is C1b: use modular flow to continue positivity from this
open seam chamber until the first possible polynomial/covariance crossing,
then prove the outer carrier by a scale-separated atom-pair Gram.  Generic
positive-mixture closure remains rejected.

### 2026-08-27 — C1b global theorem and center-mixture closure

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [GLOBAL C1 CLOSED]`

The seam-continuation conjecture succeeds after a second pivot.  Direct pairwise expansion and the
old sixth-likelihood envelope were too coarse.  The corpus's score-ray transform instead exposes
the exact dominant-atom variable `q`, with

```text
q >= 41/25,   e2 <= 13/10,   e4 < 2432,   e6 < 63232.
```

The sharp fourth-to-sixth spectral comparison first proves `log4 < ordinary6/25`, then the
dominant-atom estimate improves the ordinary sixth envelope to `60800` and hence `log6 < 63232`.
After multiplying by `q^8` and translating `y = q - 41/25`, the worst allowed reflected-curvature
profile has a strictly positive coefficient certificate.  Monotonicity in the three error
coordinates transfers this certificate to the exact theta source.  The exponential Bell-jet
connector then proves, for every real `x`,

```text
thetaCuspFullSourceReflectionSecondSixthCurvature x > 0.
```

Strict source log-concavity gives `J2(x) < 0`; the determinant inequality forces `J6(x) < 0`.
For each radial fibre with positive center weight `w`, set

```text
p0 = -w J2,   p2 = w J4,   p4 = -w J6.
```

Then `p0 > 0` and `p0*p4 - p2^2 > 0` pointwise.  The corpus theorem
`HilbertMetric.integral_twoByTwo_det_pos` preserves strict positive definiteness under integration,
yielding for every `0 < a < 1/2`

```text
f_a''(0) f_a^(6)(0) - f_a^(4)(0)^2 > 0.
```

This is C3's viable form: not scalar positive-mixture closure, but integration of a signed-jet
positive matrix field.

The downstream odd-wall theorem required `C^8`, while the corpus exposed only `C^6`.  Two new
binomial derivative-product jets close orders seven and eight.  Exact evenness kills origin jets
`1,3,5,7`; the generic eighth-order cusp theorem opens the reflection-odd wall.  Combining it with
the existing even wall and the exact determinant factorization

```text
det(toeplitzFour) = evenParityWall * oddParityWall
```

proves a nontrivial right-hand interval on which the literal four-node equispaced center-mixed
theta Gram matrix is positive definite for every physical aperture.

**Hostile fake-kernel audit.**  Evenness, `C^8`, positive density, and the modular-seam sign alone do
not pass this proof.  A fake kernel must additionally satisfy the exact theta score-ray transform,
the `q >= 41/25` dominant-atom floor, the three certified spectral envelopes, the exponential Bell
jet identity, global source log-concavity, and the derivative-product center-mixture landing.
Generic positive mixtures can still reverse sixth curvature; the proof uses literal theta-source
structure at every nonformal sign step.

**August 2026 novelty audit.**  Exact searches found no external statement of the global raw
reflected curvature, physical center-mixture sixth Hankel inequality, odd four-point wall, or local
four-node positive-definite chamber.  Closest result is Planat--Solé,
[*Second-Level Concavity of the Riemann Xi Kernel*](https://arxiv.org/abs/2608.19160), which proves
strict log-concavity of the first Laguerre expression for the classical Xi kernel and derives
double Turán consequences.  It does not use this reflected complete-source determinant or the
center mixture.  Salazar's
[*Order-Moment Transport and Hankel Determinants in Special-Function Inequalities*](https://arxiv.org/abs/2606.31647)
supplies a general moment-recognition calculus for other special functions, not this theta source
or four-point cusp.  Noncollision is a literature-search conclusion, not a theorem of Lean.

Lean artifacts:

- `thetaCuspFullSourceReflectionSecondSixthCurvature_pos`;
- `thetaCuspCenterMixedDensity_iteratedDeriv_secondSixthHankel_pos_all`;
- `contDiff_eight_thetaCuspCenterMixedDensity`;
- `exists_thetaCuspCenterMixed_oddParityWall_pos_right`;
- `exists_thetaCuspCenterMixedGramFourEquispaced_posDef_right`.

Audit: direct `lake env lean` passed; targeted leaf builds passed; formal lint passed; `#print
axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.  No added axiom, `sorry`,
`admit`, `opaque`, `unsafe`, numerical evaluation, or RH premise is used.

Next open TCD core: replace this finite rank-four chamber by an all-order/cofinal singular
Hardy/RKHS carrier with coefficient-faithful Xi landing.  Finite jet positivity, including the new
global sixth law, does not itself select the Xi divisor.

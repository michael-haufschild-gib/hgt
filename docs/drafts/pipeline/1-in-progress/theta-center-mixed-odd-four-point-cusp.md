# Theta center-mixed odd four-point cusp

- **ID:** `theta-center-mixed-odd-four-point-cusp`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / TCD singular-RKHS finite-rank advance
- **Scientific status:** `[NOVEL SEAM SUBTHEOREM] [PAPER-PROVED] [LEAN-PROVED] [GLOBAL C1 OPEN]`
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

No corpus theorem proves (C1), the local odd wall, or a four-node chamber.

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
- [ ] C1 proved or falsified
- [ ] C2 proved or falsified
- [ ] C3 proved or falsified
- [ ] dependency-closed paper proof
- [ ] hostile fake-kernel audit
- [x] Lean theorem with no added axioms for modular seam and open seam chamber
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

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

### 2026-08-28 — global reflection-even wall and odd stationary reduction

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [GLOBAL RANK-FOUR EVEN SECTOR CLOSED]`

The local rank-four chamber left open whether the reflection-even determinant could fail at an
intermediate separation.  A source-fibre argument now removes that possibility globally.  For one
reflected completed-source fibre, write the normalized correlations as

```text
p(k t) = cos(theta(k t)),   k = 1,2,3.
```

The global reflected Riccati theorem makes `theta` increasing and concave.  Equal-step concavity
gives

```text
(theta(t) + theta(3t))/2 <= theta(2t),
theta(3t) <= 3 theta(t).
```

Two product-to-sum identities then compare the two half-angle products and prove

```text
(1 + p(3t))(1 + p(t)) - (p(t) + p(2t))^2 >= 0.
```

Rescaling gives positive semidefiniteness of every unnormalized source-fibre even block.  The
center-mixed block is its integral against the nonnegative physical weight
`r sinh(a r)`, so matrix-kernel integration proves the literal global wall

```text
thetaCuspCenterMixedEvenParityWall a t >= 0
```

for every `0 < a < 1/2` and `t >= 0`.  Hence the four-node equispaced Gram matrix is positive
semidefinite exactly when the odd wall is nonnegative: the even wall is no longer an RH proof
burden.

The next conjecture loop attacked the surviving odd wall without numerical subdivision.  Tail
positivity and the local cusp theorem first force any failure to an interior negative stationary
point.  Global radial antitonicity additionally yields a new derivative law

```text
thetaCuspCenterMixedDensityFirstJet a t <= 0   (t > 0).
```

At a negative odd wall the middle equal-step drop must strictly dominate the first drop.  Combining
this with the stationary wall equation proves that every failed rank-four packet forces one
interior witness satisfying both

```text
F(t) - F(2t) > F(0) - F(t),
0 <= F'(t) - 2 F'(2t),
```

and the exact three-scale stationary identity.  This isolates the remaining global core as an odd
drop/decay incompatibility, not a second parity sector or an asymptotic chamber.

Lean artifacts:

- `HilbertMetric.toeplitzFourEvenParityWall_cos_nonneg_of_concave_step`;
- `thetaCuspReflectedSourceEvenParityWall_nonneg`;
- `thetaCuspCenterMixedEvenParityWall_nonneg_global`;
- `thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_oddParityWall`;
- `thetaCuspCenterMixedDensityFirstJet_nonpos_of_pos`;
- `exists_thetaCuspCenterMixedOddStationary_obstruction_of_not_posSemidef`.

August 2026 collision searches found no paper stating the reflected-source half-angle wall, its
positive center-mixture closure, or the resulting rank-four odd-only equivalence.  Planat--Solé
`arXiv:2608.19160` proves strict concavity of a different Laguerre expression attached to the
classical Xi kernel and derives double Turán inequalities; it does not state this correlation-angle
four-point theorem.  This is a literature-search conclusion, not a theorem of Lean.

Open core: exclude the stationary odd drop/decay certificate for the literal center-mixed theta
density.  Generic angle concavity alone does not control this sector, so the next attack must use
the stronger completed-source Riccati/likelihood structure rather than a finite numerical chamber.

### 2026-08-28 — strict center-mixed first jet and concentrated stationary obstruction

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [GLOBAL STRICT SHAPE LAW]`

The nonpositive first-jet law left open derivative flatness away from the reflection center.  The
completed-source factorization removes it.  Pointwise on the full physical radial support,

```text
Phi'(r/2+t) Phi(r/2-t) - Phi(r/2+t) Phi'(r/2-t)
  = Phi(r/2+t) Phi(r/2-t) (L'(r/2+t)-L'(r/2-t)) < 0,
```

where `L = log Phi`.  Strict global concavity of `L`, positivity of `Phi`, and positivity of
`r sinh(a r)` make the complete derivative-product integrand negative for every `r>0`, `a>0`, and
`t>0`.  An open-support set-integral argument preserves strictness rather than only weak order:

```text
thetaCuspCenterMixedDensityFirstJet a t < 0.
```

Consequently the physical center-mixed density is strictly decreasing on the entire nonnegative
displacement ray.  Feeding strict monotonicity back into the odd wall sharpens every hypothetical
negative witness.  With

```text
A = F(0)-F(t),   B = F(t)-F(2t),   T = F(0)-F(3t),
```

one has `A+B<T`; hence wall negativity `B^2>A*T` forces the stronger scale-free concentration law

```text
A * (A+B) < B^2.
```

At the stationary witness, strict negativity of `F'(t)` and `F'(3t)` upgrades the former weak
dyadic defect to

```text
0 < F'(t) - 2 F'(2t).
```

Thus any rank-four failure now requires simultaneous strict annular drop concentration, strict
dyadic decay reversal, and the exact three-scale stationary equation.

Lean artifacts:

- `thetaCuspCenterMixedDensityFirstJet_lt_zero`;
- `strictAntiOn_thetaCuspCenterMixedDensity`;
- `thetaCuspCenterMixedOddParityWall_neg_forces_twoStepDrop_product_lt_middleDrop_sq`;
- strengthened `exists_thetaCuspCenterMixedOddStationary_obstruction_of_not_posSemidef`.

August 2026 exact-title and formula searches found no external statement of this strict
center-mixture derivative law or its stationary rank-four concentration consequence.  The closest
current result remains Planat--Solé, `arXiv:2608.19160`, on strict log-concavity of a different first
Laguerre expression; it does not state a center-mixture jet sign or this four-point obstruction.
This is a literature-search conclusion, not a theorem of Lean.

Open core: prove that the literal theta derivative-product mixture cannot realize this simultaneous
concentration/decay certificate.  Source angle concavity by itself still permits excessive loss of
the third equal-step increment; the next conjecture must retain the completed likelihood curvature
inside the positive radial mixture.

### 2026-08-28 — global coalesced speed wall and exact Ptolemy reformulation

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [GLOBAL DIFFERENTIAL WALL] [EXACT GEOMETRIC REDUCTION]`

The next conjecture loop tested whether the odd wall follows from generic correlation-angle
concavity, convexity of the reflected logarithmic action, or pointwise positive definiteness of a
source-product fibre.  Hostile algebra rejects the first mechanism: a profile can have decreasing
angle increments and increasing logarithmic-action increments while losing enough of the third
increment to make the odd wall negative.  The corpus's exact Wigner product-fibre normal form
rejects the second shortcut as too strong: positivity of the full fibre transform is precisely an
unresolved spectral-orientation sign, not a consequence already available before RH.

The positive survivor is a new global differential consequence of the completed order-three
theorem.  For every physical aperture and every `y >= 0`, write `F` for the actual center-mixed
density.  Global nonnegativity of the three-point determinant along `0,x,x+y`, together with its
double zero at `x=0`, forces its second coalesced jet to be nonnegative:

```text
(-F''(0)) * (F(0)^2 - F(y)^2) - F(0) * F'(y)^2 >= 0.
```

This upgrades the previous local and eventual coalesced walls to the full displacement ray.  Since
`F(0)>F(y)>0` for `y>0`, division gives the global correlation-angle speed law

```text
F'(y)^2 / (F(0)^2 - F(y)^2) <= (-F''(0)) / F(0).
```

The stationary rank-four obstruction now carries this wall at its interior witness in addition to
strict annular concentration and strict dyadic decay reversal.

The same loop exposes an exact nonpositive-curvature formulation.  Define the intrinsic center
chord

```text
d_a(t) = sqrt(F_a(0) - F_a(t)).
```

For every `t>=0`, direct square-root polarization proves

```text
oddParityWall(a,t) >= 0
  iff d_a(2t)^2 <= d_a(t)^2 + d_a(t) d_a(3t).
```

The right side is precisely Ptolemy's inequality on the ordered equispaced packet
`0,t,2t,3t`.  Since the reflection-even block is already globally positive, the complete
center-mixed rank-four Gram matrix is positive semidefinite if and only if this intrinsic theta
chord is Ptolemaic on that packet.  This identifies the surviving CLG/TTF obstruction as a literal
four-point curvature defect rather than another determinant expression.

Lean artifacts:

- `thetaCuspCenterMixedGlobalCoalescedWall_nonneg`;
- `thetaCuspCenterMixedCorrelationAngleSpeedSq_le_center`;
- `thetaCuspCenterMixedChord`;
- `thetaCuspCenterMixedOddParityWall_nonneg_iff_ptolemy`;
- `thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_ptolemy`;
- strengthened `exists_thetaCuspCenterMixedOddStationary_obstruction_of_not_posSemidef`.

Exact targeted builds passed for
`GaloisForLFunctions.RHTower.ThetaCuspCenterMixedGlobalCoalescedWall`,
`GaloisForLFunctions.RHTower.ThetaCuspCenterMixedPtolemyWall`, and the strengthened stationary
module.  Axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

August 2026 corpus and literature searches found no statement of the global theta coalesced speed
wall or this Hedenmalm rank-four/Ptolemy equivalence.  Foertsch--Lytchak--Schroeder
(`arXiv:0705.1042`) studies Ptolemy geometry and nonpositive curvature abstractly, without this
theta autocorrelation tangent.  Planat--Solé (`arXiv:2608.19160`) studies a different Laguerre
expression and does not contain either theorem.  This is a collision-search conclusion, not a
theorem of Lean.

Open core: prove Ptolemy for the intrinsic theta chord using the exact autocorrelation-tangent and
completed likelihood structure.  Neither generic angle concavity nor generic convex logarithmic
action suffices; the next attack must control how radial `L2` mixing transports fibrewise
four-point curvature.

### 2026-08-28 — Ptolemy law of total variance and radial failure descent

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [NONLINEAR MIXTURE TRANSPORT] [EXACT SOURCE DESCENT]`

The radial-mixing conjecture is now closed exactly.  For one completed-source fibre set

```text
A_u = P_u(0) - P_u(t),
B_u = P_u(t) - P_u(2t),
T_u = P_u(0) - P_u(3t),
W_u = A_u T_u - B_u^2,
```

where `P_u(s) = thetaCuspFullSource(u+s) thetaCuspFullSource(u-s)`.  Strict radial monotonicity
gives `A_u>0` for `t>0`.  Polarization of two fibres has the exact decomposition

```text
A_u T_v + A_v T_u - 2 B_u B_v
  = (A_v/A_u) W_u + (A_u/A_v) W_v
      + A_u A_v (B_u/A_u - B_v/A_v)^2.
```

This is a Ptolemy law of total variance: both normalized fibre defects survive with positive
weights, while disagreement between normalized middle drops contributes a square.  Therefore the
nonlinear odd wall is closed under every positive radial mixture despite not being linear or
convex in the original four correlation values.

For the literal Hedenmalm density, product-space integration of the weighted polarization kernel
is exactly twice the physical odd wall.  Hence nonnegative fibre walls for positive source centers
imply the physical center-mixed wall.  Contrapositively, every negative physical wall descends to
some genuine `u>0` completed-source fibre with a negative wall.  Cross-centre alignment and radial
mixing are no longer independent obstructions.

Lean artifacts:

- `thetaCuspReflectedSourcePtolemyPolarization_eq_defects_add_ratioSq`;
- `thetaCuspReflectedSourcePtolemyPolarization_nonneg`;
- `integral_thetaCuspCenterMixedPtolemyPolarizationKernel`;
- `thetaCuspCenterMixedOddParityWall_nonneg_of_sourceFibres`;
- `exists_thetaCuspReflectedSourceOddParityWall_neg_of_centerMixed_neg`.

Exact `lake env lean` and targeted module build pass for
`GaloisForLFunctions.RHTower.ThetaCuspCenterMixedPtolemyTransport`.  Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Two stronger shortcuts failed before this survivor was isolated.  Monotonicity of ordinary
curvature `P''/P` leaves a signed integral balance and does not by itself imply the required TP2
minor.  Pointwise positive definiteness of every symmetrized atom-pair channel is also unavailable:
the corpus proves a strictly negative first--second cross signed-second entry.  These failures rule
out generic Riccati and atomwise-PSD substitutions; the remaining theorem must use the completed
source as a coupled object.

August 2026 exact-formula searches found no external Ptolemy-mixture identity of this form.  The
classical Schoenberg theory connects positive-definite kernels with Hilbert chord metrics, and
Foertsch--Lytchak--Schroeder study abstract Ptolemy spaces, but neither gives this defect
polarization or theta radial transport.  This is a collision-search conclusion, not a Lean
theorem.

Open core: prove

```text
thetaCuspReflectedSourceOddParityWall u t >= 0
```

for every `u>0`, `t>0`.  This is now the sole rank-four producer burden before the already-proved
radial landing.  Global reflected Riccati/angle concavity controls three-point geometry but does
not formally imply this four-point wall; the next conjecture must exploit coupled completed-source
likelihood structure without separating atom pairs.

### 2026-08-28 — literal-fibre cusp, positive return, and stationary flux rigidity

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [SOURCE-FIBRE MINIMUM PRINCIPLE] [EXACT FLUX LAW]`

The next corpus-driven conjecture loop stayed on the literal completed-source fibre rather than
weakening the rank-four target.  Put

```text
P_u(s) = thetaCuspFullSource(u+s) thetaCuspFullSource(u-s),
D_u(s) = -P_u'(s) > 0,
W_u(t) = (P_u(0)-P_u(3t))(P_u(0)-P_u(t))-(P_u(t)-P_u(2t))^2.
```

The global strict second--sixth reflection curvature is exactly the coalesced second--sixth
Hankel determinant of `P_u`.  The abstract odd-wall cusp theorem therefore gives, for every
center `u`, a right neighborhood on which `W_u(t)>0`.  At the other end, the completed source's
superexponential envelope and modular evenness give

```text
P_u(t) -> 0,
W_u(t) -> P_u(0)^2 > 0
```

as `t -> +infinity`.  Thus a negative literal fibre wall cannot be an endpoint phenomenon.  It
forces a strictly interior negative local minimum.  Differentiating the wall with the positive
decay flux gives the exact identity

```text
W_u'(t) = 3 A D_u(3t) + D_u(t) (T+2B) - 4 B D_u(2t),
```

where

```text
A = P_u(0)-P_u(t),
B = P_u(t)-P_u(2t),
T = P_u(0)-P_u(3t).
```

Consequently every hypothetical negative wall has a witness satisfying the stationary law

```text
4 B D_u(2t) = D_u(t)(T+2B) + 3 A D_u(3t).
```

Strict reflected radial monotonicity gives `A>0`, `B>0`, and `T>B`.  The positive residual term
then forces the new dyadic retention obstruction

```text
3 D_u(t) / 4 < D_u(2t).
```

This is stronger than the earlier generic stationary derivative reversal: a rank-four source
failure must simultaneously be negative, stationary, annularly concentrated, and retain this
specific amount of completed decay flux at the doubled scale.  The law is exact and
source-coupled; it does not arise from optimizing an external estimate.

Lean artifact:

- `GaloisForLFunctions/RHTower/ThetaCuspReflectedSourceOddStationary.lean`;
- `exists_thetaCuspReflectedSourceOddParityWall_pos_right`;
- `tendsto_thetaCuspReflectedSourceOddParityWall_atTop`;
- `exists_thetaCuspReflectedSourceOddParityWall_stationary_neg_of_neg`;
- `exists_thetaCuspReflectedSourceOddParityWall_stationary_flux_amplification_of_neg`;
- hypothesis-free classification
  `thetaCuspReflectedSourceOddParityWall_global_or_stationary_flux_obstruction`.

Exact foreground `lake env lean`, targeted
`lake build GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceOddStationary`, and umbrella wiring
all pass.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Two conjectures failed in the hostile pass.  Global reflected Riccati margin alone is not a
four-point principle: abstract convex actions can obey that third-order differential inequality
while their odd Ptolemy wall is negative.  Full positive definiteness of each Wigner/source fibre
would imply the target by Hilbert-space Ptolemy, but the corpus's divisor-trace normal form leaves
exactly an unresolved signed spectral orientation, so that assertion would merely rename the
open problem.  The positive survivor is the minimum-principle/flux certificate above.

Open core remains `W_u(t)>=0` for every `u>0,t>0`.  The next hard conjecture must collide the exact
stationary balance and strict dyadic flux retention with the coupled atom--likelihood curvature;
generic log-concavity, angle concavity, and separated atom-pair positivity have now been ruled out
as sufficient mechanisms.

### 2026-08-28 — single-switch flux and second-order stationary curvature obstruction

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [SECOND-ORDER MINIMUM PRINCIPLE] [SOURCE-SPECIFIC]`

The next conjecture loop differentiated the exact stationary carrier instead of weakening or
numerically optimizing the wall.  Write the reflected logarithmic action jets as `q1,q2,q3` and
put

```text
H_u(t) = q1(u,t)^2-q2(u,t) = P_u''(t)/P_u(t),
J_u(t) = D_u'(t) = P_u(t)(q2(u,t)-q1(u,t)^2) = -P_u(t)H_u(t).
```

The corpus's global reflected Riccati theorem has the exact new interpretation

```text
H_u'(t) = 2 q1(u,t)q2(u,t)-q3(u,t) >= 0       (t>=0).
```

Moreover `H_u(0)<0`.  Thus the positive decay flux is single-switch: positive `J_u` propagates
backward in displacement, while negative `J_u` propagates forward.  This is an exact unimodality
law, not an asymptotic or sampled assertion.

For the wall slope

```text
W_u'(t)=3 A D_u(3t)+D_u(t)(T+2B)-4B D_u(2t),
```

direct differentiation gives the source-coupled second-order identity

```text
W_u''(t) =
  J_u(t)(T+2B) + 9 A J_u(3t) - 8 B J_u(2t)
  + 6 D_u(t)D_u(3t) - 2(-D_u(t)+2D_u(2t))^2.
```

Every hypothetical negative wall has an interior local-minimum witness, so the same witness now
obeys all of

```text
W_u(t)<0,
4 B D_u(2t)=D_u(t)(T+2B)+3 A D_u(3t),
3 D_u(t)/4 < D_u(2t),
0 <= W_u''(t),
```

together with the global single-switch law for `J_u`.  The previous balance and retention
certificates therefore no longer live at a potentially different existential point: Lean proves
one local minimum carrying the complete first- and second-order obstruction package.

Lean artifact:

- `GaloisForLFunctions/RHTower/ThetaCuspReflectedSourceOddStationaryCurvature.lean`;
- `hasDerivAt_thetaCuspReflectedSourceSchrodingerPotential`;
- `monotoneOn_thetaCuspReflectedSourceSchrodingerPotential`;
- `thetaCuspReflectedSourceDecayFluxCurvature_single_switch`;
- `hasDerivAt_thetaCuspReflectedSourceOddParityWallSlope`;
- `iteratedDeriv_two_thetaCuspReflectedSourceOddParityWall`;
- `exists_thetaCuspReflectedSourceOddParityWall_stationary_curvature_retention_of_neg`;
- hypothesis-free classification
  `thetaCuspReflectedSourceOddParityWall_global_or_stationary_curvature_obstruction`.

Hostile audit remains essential.  The monotone potential is not by itself the missing four-point
theorem: the earlier abstract action countermodels satisfy the Riccati differential inequality
while allowing a negative odd wall.  New content is compulsory second-order multiscale curvature
at the actual completed-source minimum, where three source scales and the square of the middle
flux derivative couple exactly.

August 2026 primary-literature search found no collision.  Michałowski's 2026
[PF-order paper](https://arxiv.org/abs/2602.20313) reports the global `PF_4` problem for the
de Bruijn--Newman kernel as open while certifying a computational `PF_5` failure.  Planat--Solé's
2026 [second-level concavity theorem](https://arxiv.org/abs/2608.19160) proves a different local
Laguerre/log-concavity statement using theta differential equations and finite certificates; it
does not contain this reflected-fibre three-scale stationary identity or its Lean closure.

Open core remains literal fibrewise Ptolemy, `W_u(t)>=0` for every `u>0,t>0`.  Any counterexample
must now survive a monotone Schrödinger potential, single-switch decay flux, exact stationary
balance, strict retention, and the displayed nonnegative second-order curvature at one common
negative local minimum.  Next conjecture must use the completed atom--likelihood fourth/sixth jet
structure to contradict that joint package; Riccati alone is formally exhausted.

Exact foreground `lake env lean` and targeted
`lake build GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceOddStationaryCurvature` pass after
umbrella wiring.  The capstone axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`; the module contains no `sorry`, `admit`, added `axiom`, `opaque`, or `unsafe`
declaration.  Repo-wide formal lint reaches this module but remains red on unrelated pre-existing
unreachable modules in the `RHTower` and `HTGeometry` umbrellas; none is introduced by this work.

### 2026-08-28 — frozen C4: fifth-root divided-drop convexity

`[FROZEN CONJECTURE] [HARD FIBRE CORE]`

For a literal completed-source fibre write

```text
P_u(t) = Phi(u+t) Phi(u-t),
G_u(x) = (P_u(0)-P_u(sqrt x))/x                  (x>0).
```

Corpus endpoint laws select the power `1/5`, without fitting it to a proof: the global coalesced
second--sixth determinant says exactly that the right second jet of `G_u^(1/5)` is positive at
`x=0`, while source decay gives `G_u(x)^(1/5) ~ P_u(0)^(1/5) x^(-1/5)` in the far tail.  Freeze:

```text
x |-> G_u(x)^(1/5) is decreasing and convex on (0,infinity), for every real u.       (C4)
```

Public meaning: after dividing out the forced quadratic cusp, every completed theta fibre loses
correlation along one convex fifth-root scale.

This is not generic angle concavity, generic log-concavity, or a restatement of the wall.  Its
risky consequence is a full continuum curvature law between the already-proved coalesced and tail
chambers.  At `x=t^2`, convex interpolation across `t^2,4t^2,9t^2`, plus monotonicity, is expected
to imply the exact odd wall.  The proof route for C4 is not frozen; current attack is to expose its
literal differential numerator and collide it with the completed atom--likelihood fourth/sixth
jets.  A counterexample retires C4 unchanged and must leave its strongest curvature survivor.

### 2026-08-28 — C4 discrete bridge closed in Lean

Let `a,b,c` be values of `G_u^(1/5)` at squared scales `x,4x,9x`.  Decrease and convexity give

```text
0 <= c <= a,                 8b <= 5a+3c.
```

Source monotonicity independently gives `a^5 <= 4b^5`.  Put `c=a y^2`, `0<=y<=1`.  The exact
algebraic core is

```text
8192(1+3y^5) - (5+3y^2)^5
 = (1-y)^3 (
     243y^7 + 729y^6 + 3483y^5 + 8505y^4 + 22545y^3
     + 21027y^2 + 15201y + 5067),
```

whose remaining factor is coefficientwise positive.  Therefore

```text
(4b^5-a^5)^2 <= 9a^5c^5.
```

After restoring the common factor `t^4`, this is precisely

```text
(P_u(t)-P_u(2t))^2
  <= (P_u(0)-P_u(t))(P_u(0)-P_u(3t)),
```

the unresolved reflected-source odd/Ptolemy wall.  No estimate or fitted constant enters.

The strongest unconditional survivor is now formal: for every real `u,t`, either `t<=0`, the
source odd wall is nonnegative, the fifth-root divided drop increases between squared scales
`1` and `9`, or it violates the convex interpolation inequality at squared scale `4`.  Thus any
literal source counterexample to the wall is a certified discrete counterexample to C4.

Lean artifacts:

- `GaloisForLFunctions/HilbertMetric/FifthRootDividedDropWall.lean`;
- `GaloisForLFunctions/RHTower/ThetaCuspReflectedSourceFifthRootDividedDropWall.lean`;
- `HilbertMetric.weighted_fifth_power_wall`;
- `HilbertMetric.fifthRootConvexChord_forces_wall`;
- `thetaCuspReflectedSourceOddParityWall_nonneg_of_fifthRootShape`;
- hypothesis-free classification
  `thetaCuspReflectedSourceOddParityWall_or_fifthRootShapeFailure`.

Exact foreground checks and targeted module build pass after wiring both umbrellas.  Axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

August 2026 primary-literature search found no fifth-root divided-drop wall law.  Planat--Solé
study a different logarithmic second-level concavity functional; Salazar studies order-moment
Hankel recognition for other special functions; Michałowski still records the theta `PF_4`
problem as open.  C4 itself remains open.  Its proof burden is now exact and source-specific:
prove decrease and convexity of `G_u^(1/5)` on `(0,infinity)`, equivalently exclude the two
formalized shape failures rather than optimize any scalar bound.

### 2026-08-28 — C4 decrease closed globally; sole survivor is convexity

The corpus's already-proved global correlation-angle concavity has a stronger consequence than
its earlier three-point use.  Write the normalized fibre as

```text
P_u(t)/P_u(0) = cos(alpha_u(t)),      0 <= alpha_u(t) <= pi/2.
```

For `0<s<=t`, concavity and `alpha_u(0)=0` give

```text
(s/t) alpha_u(t) <= alpha_u(s).
```

Concavity of sine on `[0,pi]`, followed by its monotonicity on `[0,pi/2]`, gives

```text
(s/t) sin(alpha_u(t)/2) <= sin(alpha_u(s)/2).
```

Squaring and using `1-cos(alpha)=2 sin(alpha/2)^2` proves the exact continuum law

```text
(P_u(0)-P_u(t))/t^2 <= (P_u(0)-P_u(s))/s^2.
```

Thus both `G_u` and `G_u^(1/5)` are antitone on `(0,infinity)` for every real center `u`.
This is unconditional and global, including modular-seam crossing; no tail split or source
estimate is used.

New Lean theorems:

- `HilbertMetric.cosineDividedDrop_antitone_of_angleScaling`;
- `antitoneOn_thetaCuspReflectedSourceDividedDrop`;
- `antitoneOn_thetaCuspReflectedSourceDividedDropFifthRoot`;
- sharpened hypothesis-free classification
  `thetaCuspReflectedSourceOddParityWall_or_fifthRootConvexityFailure`.

Consequently a positive-displacement negative odd wall can no longer escape through either of
two shape failures: it must satisfy the strict convex-chord violation

```text
5 G_u(t^2)^(1/5) + 3 G_u(9t^2)^(1/5)
  < 8 G_u(4t^2)^(1/5).
```

C4 is therefore half closed, and its remaining burden is pure convexity.  Exact targeted build
and axiom audit pass; only `propext`, `Classical.choice`, and `Quot.sound` occur.  Repo-wide lint
still fails solely on unrelated pre-existing unreachable modules; both new modules are reachable
from their umbrellas.

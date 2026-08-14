# Formalize the `ht` stage-2 folder unconditionally

- **ID:** `formalize-ht-folder-stage2-cards`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME
- **Target:** every card in `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/ht/`
  formalized unconditionally in Lean 4 and promoted to `3-formalized`.

## Rules in force

Unconditional Lean only: no added axioms, no `Prop`-interface stand-ins for the mathematics, no
structural hypothesis that can be discharged by constructing the object instead.  Where the ambient
structure can be *built* (a free differential field, a lattice, a meromorphic model), build it and
prove its properties rather than assuming them.

## Card status

| card | state |
|---|---|
| `nonautonomous-ht-tail-projective-time-law` | **DONE — promoted to 3-formalized** |
| `triptic-orbit-residue-reciprocity` | **both unconditional theorems formalized** — additive and multiplicative reciprocity |
| `triptic-ht-kummer-content-root-classification` | abstract Kummer core audited axiom-clean; divisor layer built |
| `hypertranscendental-pair-localization-noncompression` | algebraic core audited axiom-clean |
| `nonautonomous-rational-first-order-tail-orbifold-law` | PROMOTED to 3-formalized (2026-08-14) |
| `nonautonomous-rational-complete-tail-orbifold-classification` | Euclidean signature classification closed |
| `nonautonomous-isogeny-tail-time-splitting` | (1),(3),(4),(5) formal; (2),(6),(7) formal for `G_m` |
| `helson-universal-ht-arbitrary-divisor-orthogonality` | pending |
| `irrational-power-canonical-products-…-gevrey-slope-rigidity` | pending |

## Closed: the projective time law

Five new modules, all wired into `GaloisForLFunctions.HTGeometry`, all axiom-clean:

```text
HTGeometry/FreeDifferentialFieldPresentation.lean    jet evaluation is a differential isomorphism;
                                                      every nonconstant element of a free scalar
                                                      differential field is hypertranscendental
HTGeometry/NonautonomousTailHypertranscendence.lean  the phase generator is hypertranscendental
HTGeometry/MutualGeneratorMobius.lean                two generators of one differential field are
                                                      Möbius in each other; the coefficient matrix
                                                      is unique up to a scalar
HTGeometry/NonautonomousProjectiveTimeLaw.lean       the phase transition and Schwarzian transport
HTGeometry/FreeDifferentialProtocolTimeLaw.lean      the whole law with no structural hypothesis
```

Capstone: `freeDifferentialProtocol_projective_time_law`.

**Technique worth reusing.** The card had recorded a blocking instance clash between `JetField C ι`
and `FractionRing (DifferentialPolynomial Unit C)` whenever a `Derivation` structure was carried
across.  The clash disappears entirely if the comparison is never made structurally: build the
evaluation homomorphism *out of* the jet polynomial ring, prove the intertwining `E(δp) = (E p)′` by
`MvPolynomial.induction_on`, and propagate it to fractions by clearing one denominator and
cancelling.  No `Derivation` object is ever transported.

## The common obstruction of the three triptic cards

`triptic-orbit-residue-reciprocity`, `triptic-ht-kummer-content-root-classification` and
`hypertranscendental-pair-localization-noncompression` all bottom out on one missing layer:

> **orbital principal parts of a meromorphic function on `ℂ` with a rank-three period lattice.**

What is already in the tree:

- `HTGeometry/DiscreteOrbitReciprocity.lean` — the *discrete* core of the direct reciprocity proof
  (`additively_separable_of_indep_increments`, `corner_reciprocity`), with the analytic corner
  identities left as hypotheses.  Making the card unconditional means proving those hypotheses.
- `HTGeometry/IncommensuratePeriodMeromorphicModel.lean` and the `meroField` layer — the global
  meromorphic field, translations as differential automorphisms, incommensurate-period fixed-field
  theorems.
- `HTGeometry/PairFacePrivateSector.lean` — the finite Laurent/augmentation algebra of the private
  pair sector.

What is missing and has to be built:

1. a Laurent-coefficient functional `c_k(F, w)` for a meromorphic `F`, additive in `F` and
   equivariant under translation;
2. non-accumulation of the poles of a meromorphic function, in the form: the set of `w` with
   `c_k(F, w) ≠ 0` meets every compact set in a finite set;
3. the two structural consequences of `Δ_τ Δ_σ F ∈ ℂ` on the coefficient array;
4. the mixed-quadrant corner identities, which feed `corner_reciprocity`.

Item 2 is the only genuinely analytic step; items 1, 3, 4 are bookkeeping once 1 exists.


## Closed: the orbital principal-part layer and triptic reciprocity

Three new modules, wired and axiom-clean:

```text
HTGeometry/MeromorphicLaurentTranslation.lean   translation equivariance, punctured-germ congruence,
                                                 vanishing at analytic points, linearity, and
                                                 LOCAL FINITENESS of the principal-part support
HTGeometry/TripticCornerAccumulation.lean       the compensating index `-⌈n Im τ / Im σ⌉`, the
                                                 mixed-quadrant accumulation law, and finiteness of
                                                 the nonzero coefficients along a lattice orbit
HTGeometry/TripticOrbitResidueReciprocity.lean  discrete telescoping plus the reciprocity theorem
```

Capstone: `triptic_orbit_residue_reciprocity`.

**Reusable pattern.** "Poles cannot accumulate" arguments: reduce the points into a compact
fundamental region by lattice translations under which the coefficient is invariant, prove the
reduced points pairwise distinct from ℤ-independence of the periods, then contradict
`finite_setOf_laurentCoeff_ne_zero_of_bounded`.  Packaged twice already.

## Next concrete steps

1. **Local argument principle** — DONE.  `HTGeometry/MeromorphicLogDerivResidue.lean`,
   `laurentCoeff_logDeriv_eq_order : laurentCoeff (logDeriv f) a (-1) = n` when
   `meromorphicOrderAt f a = n`.  Wired, axiom-clean.
2. **Multiplicative divisor reciprocity** — DONE.
   `triptic_multiplicative_divisor_reciprocity`, from the additive theorem at `ℓ = -1` plus the
   local argument principle.  Wired, axiom-clean.
3. The augmentation law `(A2)` needs a residue theorem on a parallelogram; `PNTPlus` has only a
   simple-pole rectangle version.
4. Then audit `triptic-ht-kummer-content-root-classification` and
   `hypertranscendental-pair-localization-noncompression` against their existing Lean cores.


## Closed: the Euclidean signature classification (cards 5 and 6)

```text
HTGeometry/EuclideanConeSignature.lean            euclidean_cone_triple, cone_pair_eq_two,
                                                   cone_quad_eq_two, parabolic_signature_classification
HTGeometry/ParabolicSignatureClassification.lean  parabolicSphereSignature_iff — the six recorded
                                                   signatures are exactly the solutions of
                                                   c + ∑(1 - 1/ν) = 2
```

## Closed: the triptic source divisor (cards 2 and 3)

```text
HTGeometry/MeromorphicLogDerivResidue.lean   laurentCoeff_logDeriv_eq_order — the local argument
                                              principle; mathlib has no complex residue
HTGeometry/TripticSourceDivisor.lean         shiftOrder, shiftOrder_mul (additive under products),
                                              shiftOrder_period, meromorphicOrderAt_comp_add
```

## Audited: the two algebraic cores

`PairFacePrivateSector.lean` (9 declarations) and `MinimalHTCompletionArchitecture.lean`'s abstract
Kummer layer (4 declarations) all resolve and all report
`[propext, Classical.choice, Quot.sound]`.  Those two cards' unconditional content is in Lean.

## Correction that changes several cards

The order-one **elliptic-gamma atomic theorem is corpus-owned**, not an external unaudited parent:
`EllipticGammaAtomicOverDAExtension.lean`,
`ellipticGammaExternalDefectFamily_differentialIndependent_daExtension`, axiom-clean, hypotheses are
data only.  Every card boundary note deferring to it is stale.

## Next concrete steps

1. **Scaling-invariant field theorem** (card 7's `(2)`, `(6)`, `(7)` for `G_m`) — half done.
   Built: `FreeDifferentialScalingAutomorphism.lean` (the deck automorphism `y ↦ a·y`, constructed
   from the two jet evaluations) and `LogarithmicDerivativeFixedField.lean`
   (`scalingAutomorphism_logDeriv`, `exists_logDerivField_coeff`,
   `adjoin_generator_over_logDerivField` — `F⟨ℓ⟩(y) = F⟨y⟩` by one ordinary adjunction).
   Left: `y` is transcendental over `F⟨ℓ⟩` (infinitely many deck conjugates), and then the fixed
   field of the deck group is `F⟨ℓ⟩` — for the last step the classical route is that an invariant
   `P(y)/Q(y)` forces `P(aY) = λ P(Y)`, `Q(aY) = λ Q(Y)`, so both are monomials of equal degree;
   one scalar `a` with `a^i ≠ a^j` for `i ≠ j` already suffices in characteristic zero.
2. Card 7's general `(2)` needs a Rosenlicht-type differential-rational quotient theorem.
3. Cards 5 and 6 still need parabolic-orbifold uniformization and the complete-tail identification.
4. Card 8 needs Pong 5.9, Andersson's arbitrary-divisor theorem and Saksman–Webb/Seip.
5. Card 9 needs Barnes asymptotics and the Sibuya–Ramis exact Gevrey-order theorem.


## Built this cycle (card 7, `G_m` instance)

```text
HTGeometry/FreeDifferentialScalingAutomorphism.lean   the deck automorphism `y ↦ a·y`, constructed
HTGeometry/LogarithmicDerivativeFixedField.lean       it fixes `ℓ = y′/y` and all of `F⟨ℓ⟩`;
                                                       `F⟨ℓ⟩(y) = F⟨y⟩`; `y` transcendental over `F⟨ℓ⟩`
HTGeometry/ScalingInvariantRationalFunction.lean      a scaling-invariant coprime fraction is constant
```

Remaining bridge for the `G_m` fixed-field theorem: write `x ∈ F⟨ℓ⟩(y)` as `P(y)/Q(y)` with `P, Q`
coprime over `F⟨ℓ⟩` (via `RatFunc.algEquivOfTranscendental` and the corpus's `ratFuncEval`),
transport `σ x = x` to `P(aY)·Q = P·Q(aY)` using transcendence of `y`, then apply
`natDegree_eq_zero_of_scaling_invariant`.


## Closed: the `G_m` position--velocity theorem (card 7)

```text
HTGeometry/FreeDifferentialScalingAutomorphism.lean   scalingAutomorphism (constructed), its
                                                       derivation compatibility and action on `y`
HTGeometry/ScalingInvariantRationalFunction.lean      a scaling-invariant coprime fraction is constant
HTGeometry/LogarithmicDerivativeFixedField.lean       ratFuncEval_eq_div,
                                                       mem_logDerivField_of_scaling_invariant,
                                                       two_pow_ne_of_ne,
                                                       fixedField_scaling_eq_logDerivField
```

Capstone: `fixedField_scaling_eq_logDerivField` —
`{x | ∀ a ≠ 0, σ_a x = x} = F⟨y′/y⟩`.  Non-vacuous: the invariance hypothesis is discharged at the
single scalar `a = 2`.

Also added `parabolic_triple_classification` to `ParabolicSignatureClassification.lean`, the
reciprocal form another session's `TriangleSignatureTrichotomy.lean` consumes.


## Built this cycle (cards 5, 6, 9)

```text
HTGeometry/HyperbolicSignatureGap.lean      hyperbolic_signature_gap — the Hurwitz `1/42` gap for
                                             arbitrary sphere signatures with cusps, plus
                                             degree_le_of_hyperbolic_defect, the card's `(22)`
HTGeometry/IrrationalSineSubsequence.lean   infinite_setOf_half_le_abs_sin — an irrational rotation
                                             is far from the integers infinitely often, by a
                                             doubling argument needing neither equidistribution nor
                                             pigeonhole; this is the card-9 sharpness step `(10)`
```

Remaining, per card, in rough order of cost:

- card 2: the augmentation law `(A2)` — needs a parallelogram residue theorem
- cards 3, 4: surjectivity of the divisor map / the exact-image realization
- cards 5, 6: parabolic-orbifold uniformization and the complete-tail identification
- card 7: a Rosenlicht-type quotient for a general connected commutative algebraic group
- card 8: Pong 5.9, Andersson's arbitrary-divisor theorem, Saksman--Webb/Seip
- card 9: two-sided Stirling for `Γ(1 + sk)` against `(k!)^s`, then Sibuya--Ramis and Barnes


## Built this cycle (cards 2, 3, 4, 5, 6, 8)

```text
HTGeometry/TripticSourceDivisor.lean (extended)   triptic_multiplicative_divisor_reciprocity_int,
                                                   laurentCoeff_shiftDiff_logDeriv,
                                                   finite_support_shiftOrder,
                                                   tripticOrbitCharge{,_mul,_shift}
HTGeometry/ParabolicSignatureClassification.lean  parabolic_of_pole_orders,
   (extended)                                      parabolicSphereSignature_of_pole_orders
HTGeometry/PrimeSupportNotFinitelyGenerated.lean  primeSupport_not_finitelyGenerated
```

Card 4's algebraic core (including the telescoping identity
`TelescopeIdeal.iInf_span_singleton_eq_span_prod_of_primes`) is audited axiom-clean; its remaining
statements rest on the exact-image parent of the all-depth card, not on anything of this card's own.


## Built this cycle (cards 8, 9)

```text
HTGeometry/PrimeSupportNotFinitelyGenerated.lean  primeSupport_not_finitelyGenerated — Pong's
                                                   hypothesis, discharged once for every character
HTGeometry/GevreyZetaTailBounds.lean              gevrey_exact_order — the exact Gevrey order of the
                                                   zeta tail in the Gamma normalization, with no
                                                   Stirling estimate needed
```


## Next executable step, stated precisely

Generalize `ScalingInvariantRationalFunction.natDegree_eq_zero_of_scaling_invariant` from one
scalar to a *family*: replace `hsep : ∀ i j, i ≠ j → a^i ≠ a^j` by a family `A : ι → L` such that
for every pair `i ≠ j` of exponents some `A t` has `(A t)^i ≠ (A t)^j`, with the cross identity
assumed for every member.  The proof is unchanged except that the monomial step chooses a witness
per pair of indices.

That single generalization does three things at once:

- it covers the deck group of a power map (roots of unity of unbounded order), which closes the
  `(∞,∞)` cusp branch of both orbifold cards without any uniformization;
- it strengthens the isogeny card's `G_m` theorem to the deck groups that actually occur;
- it is the shape needed for the compact signatures once their deck groups are available.

After that, the remaining blocks are: the rectangle residue theorem with higher-order poles
(card 2's `(A2)`; `PNTPlus/ResidueCalcOnRectangles.lean` supplies the rectangle API, the simple-pole
case, `RectanglePullToNhdOfPole` and `HolomorphicOn.vanishesOnRectangle`, so what is missing is the
vanishing of the rectangle integral of `(z-p)^{-k}` for `k ≥ 2`, provable from the primitive
`(z-p)^{1-k}/(1-k)` by four applications of the fundamental theorem of calculus);
Rosenlicht quotients (card 7's general `(2)`); Pong's conclusion and the Helson inputs (card 8);
and Barnes plus Sibuya--Ramis (card 9).


## Closed: the cusp branch of the orbifold cards

`iInter_powAdjoin_eq_logDerivField` — the tail of a degree-expanding power protocol is exactly
`F⟨y′/y⟩`.  This is the `(∞,∞)` signature, reached with no uniformization input, via the family
form of the scaling-invariance theorem (the deck group is the roots of unity, and no single root of
unity separates two exponents).

Uniformization is now needed only for `(2,2,∞)`, `(2,2,2,2)`, `(2,3,6)`, `(2,4,4)`, `(3,3,3)`.


## Built: the two deck-group rigidity statements

```text
HTGeometry/ScalingInvariantRationalFunction.lean       multiplicative deck group (single scalar and
                                                        separating family) — NEW, no counterpart
                                                        existed
HTGeometry/RatFuncTranslationFixedField.lean           additive deck group — ALREADY IN THE TREE
HTGeometry/ScalarAdditiveDifferentialTorsor.lean       additive torsor, unit translation fixes
                                                        exactly `F⟨q′⟩` — ALREADY IN THE TREE
HTGeometry/ChebyshevQuadraticCurrent.lean              `(w′/w)² = y′²/(y² - 4)` for `y = w + w⁻¹`,
                                                        the `(2,2,∞)` transported current
```

Between them these cover the deck groups of all six Euclidean signatures: `G_m` and its roots of
unity for `(∞,∞)`, the dihedral extension for `(2,2,∞)`, and translations for the four compact
lattice signatures.  What is still missing for the compact ones is the *uniformizing coordinate*
itself — a doubly periodic meromorphic function with prescribed lattice — for which the corpus
already owns the theta layer (`EllipticThetaLogComparison`, `EllipticThetaCoordinateDivisor`,
`EllipticThetaLogComparisonRigidity`, and
`differentiallyAlgebraic_of_lattice_periodic_meromorphicNF`).


## Closed: the rectangle residue theorem and the augmentation law

The card-2 gap `(A2)` is closed.  What it needed was a residue theorem valid for poles of arbitrary
order; the vendored `PNTPlus` one is restricted to simple poles, and mathlib has no complex residue.
Three new modules supply it:

```text
HTGeometry/MeromorphicPrincipalPart.lean   eq_add_principalPart — the principal-part splitting
HTGeometry/RectangleResidueTheorem.lean    rectangleIntegral'_eq_sum_laurentCoeff — the residue
                                             theorem on a rectangle, any pole order
HTGeometry/TripticAugmentationLaw.lean     triptic_augmentation_law (A2), triptic_charge_law (A4)
```

The mechanism for the higher-order part is the single-valued primitive `(s-p)^{1-m}/(1-m)` on
`ℂ ∖ {p}`, against which the four edges of a rectangle telescope to zero.  The card's period
parallelogram was replaced by the axis-parallel rectangle of width `1` and height `Im τ`, which is a
fundamental domain of `ℤ + ℤτ` because `1` is a period — so no oblique contour is needed anywhere.

`rectangleIntegral'_eq_sum_laurentCoeff` is reusable well beyond this card: it is the first general
residue theorem in the tree.


## Closed: the Gevrey normalization change (card 9, §3)

`Γ(1 + s k)` and `(k!)^s` differ by a geometric factor, and both directions of that comparison come
from log-convexity of `Γ` — no Stirling estimate.  The two Wendel-type shift bounds

```text
Γ(x)(x + s - M)^s ≤ Γ(x + s) ≤ Γ(x)(x + M)^s
```

telescope along `x = 1 + s k` against `k!`.

```text
HTGeometry/GammaFactorialNormalization.lean   Gamma_add_le_mul_rpow, mul_rpow_le_Gamma_add,
                                              Gamma_le_pow_mul_factorial_rpow,
                                              exists_pow_mul_factorial_rpow_le_Gamma
HTGeometry/GevreyFactorialNormalization.lean  gevrey_exact_order_factorial — (9), (11), (12) in the
                                              card's own `(k!)^s` normalization
```

Card 9's §3 is therefore fully formal.  What is left on that card is the Barnes expansion and
Sibuya--Ramis.


## Closed: the four compact Euclidean currents

`HTGeometry/EuclideanOrbifoldCurrents.lean` gives the transported current of every compact parabolic
signature as an exact identity in an arbitrary differential field, from the Weierstrass relation and
the chain rule alone:

```text
(2,2,2,2)  y = ℘    (y′)² = (4y³ - g₂y - g₃)(u′)²
(3,3,3)    y = ℘′   2(y′)³ = 27(y² + g₃)²(u′)³
(2,4,4)    y = ℘²   (y′)⁴ = 16y³(4y - g₂)²(u′)⁴
(2,3,6)    y = ℘³   (y′)⁶ = 729y⁴(4y - g₃)³(u′)⁶
```

The "uniformizing coordinate" that these cards were waiting on is therefore not needed as an
existence theorem: the coordinate of each signature is an explicit function of `℘` whose degree
equals the order of the rotation in the deck group, and the current transports by algebra.  All six
parabolic signatures now have a formal transported current.


## Closed: the elliptic gamma source and its quadrant divisor

Built from scratch (mathlib has no elliptic gamma, and the corpus had only its shift-quotient
algebra, never the function):

```text
HTGeometry/ExpConeProduct.lean            the double product ∏_{j,k≥0}(1 - e(ja + kb + z)):
                                          geometric convergence, entirety, zero set, simple zeros
HTGeometry/EllipticGammaConeDivisor.lean  Γ = Φ(a+b-z)/Φ(z), its exact quadrant divisor, and
                                          D_Γ = [0], D_{Γ(·-g)} = [g], charge 0 off the class
```

The mechanism that makes the charge nonzero is that the divisor meets each `b`-orbit in a *half
line* (`ord = -1` for `m ≤ 0`, `0` for `m > 0`), so its shift differences are supported at the single
index `m = 0`.  A theta function would give charge `0`: its divisor meets each orbit finitely and the
telescoping sum vanishes.  That is why the elliptic gamma, and not a theta function, is the
realizing source.


## Closed: the realizing source is a proved member of the class

`HTGeometry/EllipticGammaConeCocycle.lean` proves the two defining properties of the multiplicative
triptic source class for the constructed `Γ`:

```text
ellipticGammaCone_periodic       Γ(z+1) = Γ(z)
ellipticGammaCone_mixed_cocycle  C_Γ(z) = -e(-z), an exponential character
```

The second follows from the two shift relations `Φ(w) = P(w)Φ(w+a)` and `P(w) = (1-e(w))P(w+b)`
(added to `ExpConeProduct.lean`, with Fubini for the double product via `HasProd.prod_fiberwise` —
mathlib's `tprod` Fubini needs a `CommGroup`, which `ℂ` under multiplication is not).

So for cards 2 and 3, `Γ ∈ M` with `D_Γ = [0]` is fully formal.  The single remaining input on both
is the kernel identification: `Y` is differentially algebraic exactly when `D_Y = 0`.


## State of the programme, and the exact remaining inputs

Everything below is wired into `GaloisForLFunctions.HTGeometry` and `#print axioms`-clean.

### Built this round

```text
MeromorphicPrincipalPart / RectangleResidueTheorem   general residue theorem, any pole order
TripticAugmentationLaw                               (A2), (A4)
GammaFactorialNormalization / GevreyFactorialNormalization / ZetaTailClosedModulus
                                                     card 9 §3, unconditional, both normalizations
EuclideanOrbifoldCurrents                            the four compact parabolic currents
SourceDivisorSurjectivity                            surjectivity from single-class realization
ExpConeProduct / EllipticGammaConeDivisor / EllipticGammaConeCocycle
                                                     the elliptic gamma function, its quadrant
                                                     divisor, periodicity and mixed cocycle
TripticChargeClassFunction                           the charge is an `H₃`-class function, with
                                                     compact local finiteness
ExpandingProtocolVanishing                           §1 degree law, §2 transient zeros,
                                                     §3 quantization, Riemann–Hurwitz trapping
VerticalSymbolTransformation                         §1 symbol comparison
BarnesRemainderDATransfer                            card 9 §4, algebraic half
NewtonSlopeRationality                               card 9 §5, arithmetic half
TaylorPartialSumApproximation                        the approximation step of Mittag-Leffler
```

### What each card still needs, precisely

| Card | Remaining input |
|---|---|
| triptic-orbit-residue-reciprocity | the principal-part normal form `F − R_trip(F)Ψ ∈ Mer_DA`, hence `Y` DA ⟺ `D_Y = 0` |
| triptic-ht-kummer-content-root-classification | the same kernel identification; plus the `Finsupp` packaging of `D` |
| hypertranscendental-pair-localization-noncompression | the multiple elliptic gamma of order `d−1` and the exact-image theorem |
| nonautonomous-rational-first-order-tail-orbifold-law | §4: the isogeny-tail identification of the late tail with the invariant Maurer–Cartan field |
| nonautonomous-rational-complete-tail-orbifold-classification | the same, plus Casale's groupoid classification as an input to §2 |
| nonautonomous-isogeny-tail-time-splitting | Rosenlicht-type quotient for a general connected commutative algebraic group |
| helson-universal-ht-arbitrary-divisor-orthogonality | Pong 5.9's conclusion; Andersson's Mittag-Leffler theorem; Saksman–Webb/Seip |
| irrational-power-canonical-products | the Barnes expansion `(4)`–`(6)`; Sibuya–Ramis |

### The next shared asset — Mittag-Leffler on `ℂ`

Prescribed principal parts feed Andersson (card 8) and the normal form (cards 2, 3, 4).  Two of the
three ingredients are built:

```text
TaylorPartialSumApproximation.lean   exists_partialSum_approx — a function holomorphic on a closed
                                     disc is uniformly within ε of a Cauchy partial sum on any
                                     strictly smaller disc
MittagLefflerConvergence.lean        summable_of_growing_radii — pointwise summability once the
                                       radii pass the point
                                     differentiableOn_seriesTail — the tail is holomorphic on a disc
                                       where all its terms are (Weierstrass M-test plus
                                       `TendstoLocallyUniformlyOn.differentiableOn`)
                                     tsum_eq_head_add_seriesTail — the head–tail splitting that
                                       exhibits the sum as meromorphic with exactly the prescribed
                                       principal parts
```

**The assembly is now complete.**  `MittagLefflerConstruction.lean` (wired, axiom-clean):

```text
differentiable_partialSum            Cauchy partial sums are entire
exists_entire_approx                 the approximation, with real radii
exists_mittagLeffler_corrections     an entire `Q n` within `2⁻ⁿ` of `P n` on the disc of radius
                                       `‖a n‖/2`
summable_mittagLeffler               the corrected series converges at every point
mittagLeffler                        `f(z) = ∑ (P n z − Q n z)`
exists_mittagLeffler_cutoff          a cutoff past every pole meeting a given disc
mittagLeffler_eq_head_add_tail       the head–tail decomposition
differentiableOn_mittagLeffler_tail  the tail is holomorphic on the disc
differentiableOn_mittagLeffler_sub_head
differentiableAt_mittagLeffler_sub   **`f − P n₀` is holomorphic at `a n₀`**: the Mittag-Leffler
                                       theorem on `ℂ`, prescribed principal parts realized
```

Hypotheses are the data only: poles tending to infinity, distinct, nonzero, with principal parts
holomorphic off their own pole.  Mathlib has no Mittag-Leffler theorem, so this is a new asset; it
is the analytic input Andersson's theorem needs on card 8, and the construction the principal-part
normal form needs on cards 2, 3 and 4.


## Closed: Weierstrass factorization on `ℂ`

The multiplicative counterpart of Mittag-Leffler.  Mathlib has no general Weierstrass theorem, and
the corpus previously owned only *fixed-genus* products under summability hypotheses
(`canonicalProductE1_analytic` needs `∑ ‖aₙ‖⁻² < ∞`; `barnesConeProduct` fixes the genus at the cone
rank).  Letting the genus of the `n`-th factor be `n` removes every hypothesis but `‖aₙ‖ → ∞`.

`HTGeometry/WeierstrassFactorizationTheorem.lean` (wired, axiom-clean):

```text
weierstrassLogBound_le_one                 the genus constant is at most 1, uniformly in the genus
norm_weierstrassFactor_sub_one_le_uniform  hence ‖E_p(w) − 1‖ ≤ e·‖w‖^{p+1} on the half disc
weierstrassGenusFactorAt, weierstrassGenusProduct
finite_setOf_norm_lt                       only finitely many zeros meet any disc
hasProdLocallyUniformlyOn_weierstrassGenusFactorAt
differentiable_weierstrassGenusProduct     **the product is entire**
weierstrassFactor_eq_zero_iff, weierstrassGenusFactorAt_eq_zero_iff
summable_norm_weierstrassGenusFactorAt_sub_one, multipliable_weierstrassGenusFactorAt
weierstrassGenusProduct_eq_zero_iff        **it vanishes exactly at the prescribed points**
```

Hypotheses are the data only: the points are nonzero and tend to infinity.  Together with
Mittag-Leffler this gives both halves of the prescribed-divisor toolkit — zeros by a product, poles
by a series — which is what an arbitrary-divisor realization theorem is built from.


## Closed: realization of a prescribed divisor on `ℂ`

With Weierstrass and Mittag-Leffler both in place, an arbitrary divisor on `ℂ` is realized by a
quotient of two Weierstrass products.

`HTGeometry/PrescribedDivisorRealization.lean` (wired, axiom-clean):

```text
divisorFunction                              the quotient of the two products
exists_notMem_range                          no countable family exhausts the plane
analyticOrderAt_weierstrassGenusProduct_ne_top
meromorphicOrderAt_weierstrassGenusProduct_ne_top
                                             the products are nowhere locally zero
meromorphicOn_divisorFunction                the quotient is meromorphic on `ℂ`
meromorphicOrderAt_divisorFunction           its order is the difference of the two orders
meromorphicOrderAt_divisorFunction_eq_zero   a unit away from both sequences
meromorphicOrderAt_divisorFunction_pos       **zero exactly on the first sequence**
meromorphicOrderAt_divisorFunction_neg       **pole exactly on the second sequence**
```

Multiplicities are encoded by repetitions in the sequences.  The hypotheses are the data only: both
sequences nonzero, tending to infinity, and disjoint from one another.

This is the divisor-realization engine that card 8's Andersson input and cards 2–4's normal form
both need; what those still add on top is the *arithmetic* side — that the realizing function can be
taken to be a Helson zeta function, respectively an elliptic-gamma product.


## Closed: the two rigidity ends of the kernel identification (cards 2, 3)

The kernel identification `Y` DA `⟺` `D_Y = 0` needs three things: the *entire* end (what a member of
the class with no poles can be), the *atom* end (what realizes a single line of poles), and the
*array* step (what a vanishing divisor does to the coefficient array).  Two of the three are now
formal, and the third is the assembly.

```text
HTGeometry/TripticEntireRigidity.lean         const_of_entire_of_periodic_of_mixed_const_zero —
                                               an entire member of the class with vanishing mixed
                                               difference is constant.  Two Liouvilles: the
                                               derivative is lattice-periodic hence constant, so the
                                               function is affine, and a genuine period kills the
                                               slope
HTGeometry/MeromorphicLogDerivLocalForm.lean  exists_analyticAt_logDeriv_local_form,
                                               laurentCoeff_logDeriv_eq_zero_of_le — a logarithmic
                                               derivative has NO Laurent coefficient below the
                                               residue; the corpus previously computed only the
                                               residue itself
HTGeometry/DifferentialAlgebraicAntiderivative.lean
                                              differentialAlgebraicOver_of_deriv (field form) and
                                               differentiallyAlgebraic_of_deriv (analytic form) —
                                               differential algebraicity is stable under
                                               INTEGRATION, not only differentiation.  The field
                                               proof is `k⟨y′⟩` has finite transcendence degree,
                                               `y′ = c` over it, then finite-transcendence descent;
                                               the analytic proof is a jet reindexing
HTGeometry/JacobiThetaSourcePrincipalPart.lean
                                              analyticOrderAt_jacobiTheta₂_eq_one — every theta zero
                                               is simple; thetaSource, its `1`-periodicity, its
                                               `2πi` quasiperiod drop, and its COMPLETE principal
                                               part: residue `1` on the divisor, nothing anywhere
                                               else
HTGeometry/TripticSeparatedPrincipalPart.lean exists_finiteSupport_separation_of_orbit_sum_eq_zero —
                                               a vanishing orbital divisor makes both separated
                                               families of the coefficient array FINITELY SUPPORTED
```

### What the array theorem says, and why it is the crux

For `F ∈ Q` the order-`ℓ` coefficients on a rank-two orbit form an array `c n m` that is additively
separable, `c n m = aₙ + bₘ`, with each family eventually constant at both ends.  Reciprocity
identifies the two total jumps.  When the divisor vanishes the two end values on each side coincide,
and the mixed-corner identity forces the two limits to sum to `c 0 0`; subtracting them leaves
`aₙ`, `bₘ` **finitely supported**.  Concretely: the poles of a source of vanishing divisor lie on
finitely many full `σ`-lines and finitely many full `τ`-lines.

That is exactly the shape the theta atom realizes.  A full `σ`-line of simple poles is
`z ↦ thetaSource σ (z - q)`: `1`-periodic, dropping by `2πi` under a `σ`-step, hence with vanishing
mixed difference, and with residue `1` at each point of the line and no other singularity.  Its own
orbital divisor vanishes — consistent, since it is differentially algebraic.

### Correction recorded

`latticeTheta`/`latticeSource`, built this cycle from the `ExpConeProduct` half-line products, were
**deleted**: the corpus already owns the lattice atom on mathlib's `jacobiTheta₂` (exact divisor,
simple zeros, `thetaLogDerivMero` with both translation laws, and field-level differential
algebraicity of every translate).  Only the pointwise simple-order statement was missing, and it is
a corollary of the exact divisor plus derivative nonvanishing.

### The remaining assembly, precisely

1. the translated and differentiated atoms `δʲ (thetaSource σ)(· - q)` and their Laurent data
   (pole order `j+1`, coefficient `(-1)ʲ j!`), with `Λ_σ`-periodicity for `j ≥ 1`;
2. finiteness of the set of orbits and of the pole orders that occur — both from ellipticity of the
   two boundary functions once the mixed constant is `0`, which `(A2)` supplies from the vanishing
   divisor;
3. subtract the finite atom sum and apply `const_of_entire_of_periodic_of_mixed_const_zero` to the
   pole-free remainder;
4. conclude in `meroField Set.univ`, where sums, differences and antiderivatives of differentially
   algebraic elements are again differentially algebraic.


## Built: all orders, the leading coefficient, and the pole-free end

Five more modules, wired and axiom-clean, close everything the kernel identification needs except the
final index bookkeeping.

```text
MeromorphicLaurentDerivative  laurentCoeff_deriv : c_ℓ(f′,a) = (ℓ+1)·c_{ℓ+1}(f,a).  Proved at the
                               level of clearing shifts: with g(t) = tᵏ f(a+t), the clearing shift of
                               f′ at exponent k+1 is t·g′(t) − k·g(t) on a WHOLE neighbourhood of the
                               origin (both sides vanish at it), and reading Taylor coefficients
                               gives m − k = ℓ+1.  Mathlib has no Laurent calculus at all
MeromorphicLaurentJet         laurentCoeff_iteratedDeriv_eq — the falling-product jet law — together
                               with its two evaluations: the product vanishes for −j ≤ ℓ ≤ −1, and
                               equals (−1)ʲ j! at ℓ = −(j+1)
TripticJetAtom                jetAtom, rowJetAtom, colJetAtom and their incidence laws.  The jets are
                               PURE: an atom of order j+1 has no Laurent coefficient of any other
                               negative index, anywhere.  So the order-by-order subtraction does not
                               interfere with itself
MeromorphicLaurentLeading     laurentCoeff_leading_ne_zero (the leading coefficient of a pole is
                               nonzero) and its consequence
                               meromorphicOrderAt_nonneg_of_laurentCoeff_neg_eq_zero — vanishing
                               principal part forces nonnegative order
TripticRemainderRigidity      differentiable_toMeromorphicNFOn_of_no_principal_part — the normal form
                               of a function with no principal part is ENTIRE; and
                               const_of_entire_of_class_off_countable — the class relations need only
                               hold off a COUNTABLE set, since the complement of a countable set in
                               `ℂ` is dense and both sides are continuous
TripticLineFiniteness         meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero (a pole is
                               exactly a nonzero negative Laurent coefficient) and
                               exists_finset_pole_classes — poles with a translation-invariant pole
                               set lie on finitely many lattice cosets
```

### The single remaining step

Everything is now local except the *index set*.  What is left is to assemble, from
`exists_finset_pole_classes` applied to the two boundary functions `Δ_τ F` and `Δ_σ F`, the finite
family of `(line, order)` pairs that actually occur, choose the coefficients supplied per orbit by
`exists_finiteSupport_separation_of_orbit_sum_eq_zero`, and check that the difference of `F` and the
resulting finite atom sum has no Laurent coefficient of negative index at ANY point of the plane.
`TripticRemainderRigidity` then makes that difference constant off a countable set, and
`DifferentialAlgebraicAntiderivative` together with the corpus's field-level closure laws turn the
finite sum into a proof that `F` is differentially algebraic.


## Built: the base-point-free principal part and the finiteness of the line support

```text
TripticGlobalCoefficient      laurentCoeff_eq_transverse_sums — the principal part of a source of
                               vanishing orbital divisor read off from its two boundary functions
                               with NO choice of orbit representative:
                                 c_ℓ(F,w) = −Σ_{k≥0} c_ℓ(Δ_τF, w+kτ) + Σ_{j≥1} c_ℓ(Δ_σF, w−jσ)
TripticTransverseCoefficient  rowCoeff / colCoeff — the two transverse fields, the row field constant
                               along `σ`-lines and the column field along `τ`-lines, both `1`-periodic.
                               These are exactly the coefficients the line atoms carry
FinsumIntSplit                finsum_int_split — a finitely supported integer sum splits into its
                               forward and backward rays
TripticIndexBound             finite_shift_indices — only finitely many transverse shift indices
                               connect two points of a finite set modulo a lattice, because a second
                               solution would be a nontrivial relation between `1`, `τ` and `σ`
TripticLineSupportFinite      rowCoeff_eq_backward_sum (the row coefficient is ALSO the backward sum,
                               since the total transverse mass vanishes) and
                               exists_finset_rowCoeff_classes — hence a nonzero row coefficient forces
                               a pole both forward and backward on the ray, the two poles reduce to a
                               finite list of classes, the number of steps between them is bounded,
                               and only FINITELY MANY `σ`-classes carry a nonzero row coefficient
```

The index set of the normal form is therefore finite and explicitly constructed.  What remains is the
mechanical assembly: sum the atoms over that finite index set, evaluate the sum's Laurent coefficients
by the incidence laws, and match against `laurentCoeff_eq_rowCoeff_add_colCoeff` to see the difference
has no principal part; then `TripticRemainderRigidity` and the field-level closure laws finish.


## Built: the finite index set is complete

```text
MeromorphicLaurentOrderVanishing  laurentCoeff_eq_zero_of_lt_meromorphicOrderAt — below the order
                                   every Laurent coefficient vanishes; with the leading-coefficient
                                   law this makes `meromorphicOrderAt` exactly the least index
                                   carrying a nonzero coefficient
TripticOrderBound                 colCoeff_eq_rowCoeff — the backward column sum IS the forward row
                                   sum in the other direction, so everything is phrased with one
                                   field used twice;
                                  meromorphicOrderAt_eq_of_laurentCoeff_eq — the order is read off
                                   the principal part, hence is lattice-invariant wherever the
                                   principal parts are;
                                  exists_order_bound_rowCoeff — only FINITELY MANY ORDERS carry a
                                   nonzero row coefficient, the bound being the least order among
                                   the finitely many pole classes
```

Both coordinates of the normal-form index set — the lines and the orders — are therefore finite and
explicitly bounded, in each of the two lattice directions.


## Built: the weighted atom sum and the atoms' class membership

```text
TripticAtomSum          sameLine / lineCount / rowAtomSum — the atoms of one order in one direction,
                         each weighted by the row field at its own base point divided by its own
                         principal coefficient `(-1)ʲ j!` AND by the number of list members on the
                         same line.  The multiplicity division makes the construction independent of
                         how many representatives of a line the finite list happens to contain, so no
                         choice of canonical representatives is needed;
                        laurentCoeff_rowAtomSum_of_ne_order — invisible at every other order
                         (the jets are pure);
                        laurentCoeff_rowAtomSum_self — at its own order it reproduces the row field
                         exactly, at every point of the plane
TripticJetAtomShift     the zero set of theta is CLOSED, so the atom's shift law holds on an open
                         set; jets of an identity on an open set agree there, so every derivative
                         satisfies the same law with the constant differentiated away.  Hence
                         jetAtom_shift_succ and jetAtom_mixed_eq_zero: every jet atom has vanishing
                         mixed second difference off its own poles — a COUNTABLE set, listed
                         explicitly as `q + (1+σ)/2 + ℤ + ℤσ`
```

`iteratedDeriv_comp_add_const` was found already in mathlib and the local duplicate removed.

The remaining step is the outer assembly: sum the per-order atom sums over the bounded order range in
both directions, subtract from `F`, and observe that the difference has no Laurent coefficient of
negative index anywhere — every ingredient of that computation is now a proved lemma.


## CLOSED: the kernel identification (cards 2 and 3)

The assembly is finished.  Two capstones, both wired and axiom-clean:

```text
TripticKernelNormalForm       exists_totalAtomSum_no_principal_part — a source of vanishing orbital
                               divisor has, AT EVERY POINT OF THE PLANE and at every negative index,
                               exactly the Laurent coefficients of an explicit finite combination of
                               theta-source jets.  The two transverse fields split the principal
                               part; the order bound makes the order range finite; the line-class
                               finiteness makes each order's index list finite; the weighted atom sum
                               reproduces both fields; and the jets are pure, so no order interferes
                               with another
TripticKernelIdentification   exists_const_sub_totalAtomSum_of_vanishing_divisor — hence the source
                               EQUALS that finite atom sum plus a constant off a countable set, and
                               its mixed constant `C` is forced to `0`.  The difference has no
                               principal part, so its canonical normal form is entire; that normal
                               form is exactly `1`-periodic (both the source and the atom sum are)
                               and has constant mixed second difference off the countable union of
                               the atoms' pole lattices with the source's non-analytic points; and
                               pole-free rigidity makes it constant
```

Both `Cst = 0` and the explicit finite decomposition come out of the same theorem: nothing about the
mixed constant had to be assumed, and no augmentation law was needed on this path.

Since every atom is a jet of a translate of `δ log θ`, and jets and translates of a differentially
algebraic germ are differentially algebraic, the kernel of the orbital divisor consists of
differentially algebraic functions.  That is statement `(4)` of `triptic-ht-kummer-content-root-classification`
and the completeness half of `triptic-orbit-residue-reciprocity`.

## 2026-08-14 — `nonautonomous-rational-first-order-tail-orbifold-law` promoted to 3-formalized

The `2 → 3` gate is closed.  What closed it, beyond the symbol/quantization/signature layers that
were already formal:

- the **elliptic function field theorem** (a mathlib gap): every lattice-periodic meromorphic
  function on `ℂ` satisfies `C(℘)·f = A(℘) + ℘'·B(℘)`
  (`EllipticMeromorphicOrderTools` → `EllipticEvenPolynomialWeierstrass` →
  `EllipticEvenRationalWeierstrass` → `EllipticFunctionFieldWeierstrass`);
- the **field of meromorphic functions on the plane**, as germs along the codiscrete filter, with
  its derivation, translations and constants (`MeromorphicPlane*`), on which
  `ellipticSubfield_eq_adjoin` identifies the phase fields as `ℂ⟮℘, ℘'⟯`;
- the **generic reparametrisation** of a differential field (`CoefficientDerivation`,
  `GenericReparametrization`, `ReparametrizationAutomorphism`,
  `TwistedReparametrizationAutomorphism`, `ReparametrizationDescent`), on which the orbifold
  coordinate becomes a differential-generic point while the deck transformations stay the analytic
  translations and scalings of the plane — so no `℘` addition theorem is needed;
- the **phase tail** itself (`EllipticIsogenyDeck`, `EllipticIsogenyTailPlane`,
  `EllipticReparamProtocolTail`, `EllipticVelocityTail`, `EllipticRotationTail`,
  `EllipticPhaseTailReparam`) and the **transported current** (`EllipticReparamCurrent`).

Certificate: `../3-formalized/new_scientific_knowledge/ht/nonautonomous-rational-first-order-tail-orbifold-law-formalized.md`.

## 2026-08-14 — `nonautonomous-isogeny-tail-time-splitting` promoted to 3-formalized

The `2 → 3` gate asked for "the full algebraic-group statement in Lean", and the card's own audit had
narrowed what was missing to one thing: the class of groups.  `G_a` has no nontrivial isogeny in
characteristic zero, `G_m` and `G_m^r` were already formal, and the elliptic curve had just been
closed — so what remained was the abelian-variety column in dimension `> 1`.

Over `ℂ` every connected commutative algebraic group is, as a complex Lie group, `ℂ^n / Λ`, so one
analytic stack over `ℂ^n` settles the whole class at once.  Two things had to change relative to the
one-variable elliptic column, and both are structural rather than technical:

- **The carrier.**  For `n ≥ 2` the polar set of a meromorphic function is a hypersurface, so the
  codiscrete-germ field `MeromorphicPlane` has no analogue.  The replacement is the **fraction field
  of the entire functions** (`EntireFunctionField`), which exists in every dimension and needs no
  Cousin or Oka theorem — the domain property is the identity theorem on a connected space.
- **The deck-closure input.**  The elliptic argument used *arbitrarily small periods*, which is
  useless for `n ≥ 2`: the period group of a nonconstant function of several variables need not be
  discrete (`f(z₁,z₂) = z₁` has periods `{0} × ℂ`).  The replacement is **density** of the
  accumulated division points (`dense_divisionPoints`), which a cocompact period lattice supplies
  by an integer-part estimate.

With those, the several-velocity reparametrisation (`GeneralCoefficientDerivation`,
`MultiReparametrization`, `MultiReparametrizationAutomorphism`) carries the whole one-variable
argument over, and the columns are:

- `ComplexTorusIsogenyDeck` — the deck group of `z ↦ m z` is exactly its group of division points;
- `ComplexTorusVelocityTail` — the phase tail is `C⟨u₁′, …, uₙ′⟩`, the velocities are differentially
  independent (`dtrdeg = n = dim G`), and the tail meets `C(G)` in the constants only;
- `ComplexTorusMaurerCartan` — `deriv_coordEntire`: the Maurer–Cartan velocity of the tautological
  point IS the tuple of reparametrisation velocities.  This is the "coordinate description of
  `Lie(G)`" the card had recorded as the last scheme-level input; analytically it is `∂ₖzⱼ = δⱼₖ`;
- `ComplexTorusPositionVelocity` — the position–velocity splitting for an **arbitrary** set of deck
  translations, with no hypothesis on the protocol, of which the expanding case is the branch where
  the position invariants collapse to the constants.

`stdTorus_phase_tail` states items `(6)`, `(7a)` and `(7b)` together for the standard torus
`ℂ^n / (ℤ + iℤ)^n` with degrees `2^k` and no hypothesis at all — lattice, protocol and point all
exhibited — so the statement is not vacuous.

Certificate: `../3-formalized/new_scientific_knowledge/ht/nonautonomous-isogeny-tail-time-splitting-formalized.md`.

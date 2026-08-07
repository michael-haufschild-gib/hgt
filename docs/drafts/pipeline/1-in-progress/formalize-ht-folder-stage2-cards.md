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
| `nonautonomous-rational-first-order-tail-orbifold-law` | Euclidean signature classification closed |
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

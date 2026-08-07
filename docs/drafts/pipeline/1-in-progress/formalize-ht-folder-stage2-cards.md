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
| `triptic-orbit-residue-reciprocity` | **core theorem formalized** — `triptic_orbit_residue_reciprocity`; multiplicative corollary open |
| `triptic-ht-kummer-content-root-classification` | pending — child of the reciprocity card |
| `hypertranscendental-pair-localization-noncompression` | pending — algebraic core exists |
| `nonautonomous-rational-first-order-tail-orbifold-law` | pending |
| `nonautonomous-rational-complete-tail-orbifold-classification` | pending |
| `nonautonomous-isogeny-tail-time-splitting` | pending |
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
2. Next: that card's **multiplicative divisor reciprocity** `D_τ(Y) = D_σ(Y)` is a direct
   corollary of `triptic_orbit_residue_reciprocity` applied to `F = logDeriv Y` at `ℓ = -1`.
3. The augmentation law `(A2)` needs a residue theorem on a parallelogram; `PNTPlus` has only a
   simple-pole rectangle version.
4. Then audit `triptic-ht-kummer-content-root-classification` and
   `hypertranscendental-pair-localization-noncompression` against their existing Lean cores.

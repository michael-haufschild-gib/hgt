# Joint Gamma intensity-atlas circuit-blindness universality law

Status: Stage 2 — dependency-closed paper proof; Lean exact checks passed  
Lean targets:
`GaloisForLFunctions.HTGeometry.FamilyDifferentialCircuitBlindnessUniversalityLaw`,
`GaloisForLFunctions.RHTower.JointGammaIntensityAtlasCircuitBlindnessUniversalityLaw`  
Novelty: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`

## Theorem-generated discovery

`FiniteDifferentialCircuitBoundary` proves that every finite differential circuit whose leaves
are differentially algebraic has differentially algebraic output. Separate observability modules
prove that Coulomb, type-I de Sitter, horizon, and centered zeta--Gamma intensities are
differentially algebraic while their oriented phases and Wigner--Smith clocks are
hypertranscendental. The centered zeta--Gamma module additionally supplies hypertranscendental
projective connection and Schwarzian channels.

Existing no-go theorems give each target access only to its own intensity. They do not state the
stronger cross-system result in which one circuit may mix every intensity in the atlas.

## Statement

For any family of differentially algebraic observations over a differential field, no
hypertranscendental target belongs to a scalar-aware finite differential circuit whose genuine
atoms range over that whole family.

Specialize the observation family to four channels:

1. Coulomb reflected-frequency intensity;
2. type-I de Sitter reflected-frequency intensity;
3. horizon Gamma intensity core;
4. centered zeta--Gamma intensity.

Even with all four channels jointly available, no scalar-aware finite differential circuit
recovers any of ten oriented observables:

1. Coulomb phase;
2. Coulomb Wigner--Smith clock;
3. de Sitter phase;
4. de Sitter Wigner--Smith clock;
5. horizon phase;
6. horizon Wigner--Smith clock;
7. centered zeta--Gamma phase;
8. centered zeta--Gamma Wigner--Smith clock;
9. centered zeta--Gamma projective connection;
10. centered zeta--Gamma Schwarzian.

## Dependency-closed proof

Let the circuit atom predicate be membership in the range of the observation family. Every
genuine atom is differentially algebraic by its range witness; every base scalar is
differentially algebraic by the algebra-map theorem. Structural induction through addition,
multiplication, negation, inversion, and differentiation makes every circuit output
differentially algebraic. This contradicts hypertranscendence of the target.

For the specialization, case split over the four observation indices and discharge differential
algebraicity with the existing intensity theorems. Case split over the ten target indices and
discharge hypertranscendence with the existing phase, Wigner--Smith, projective-connection, and
Schwarzian theorems. Apply the generic family law to every target index.

The theorem enlarges the admissible atom set relative to every existing individual no-go, so it
is not their conjunction: a circuit may freely mix observations from different systems.

No computation, numerical approximation, or new analytic axiom is used.

## Lean verification

Exact source checks passed:

`lake env lean GaloisForLFunctions/HTGeometry/FamilyDifferentialCircuitBlindnessUniversalityLaw.lean`

`lake env lean GaloisForLFunctions/RHTower/JointGammaIntensityAtlasCircuitBlindnessUniversalityLaw.lean`

The generic module is wired into `GaloisForLFunctions.HTGeometry`; the specialization is wired
into `GaloisForLFunctions.RHTower`. Axiom audit, lint, and final umbrella builds remain pending.

## Novelty audit

Corpus audit found only the one-observation phase/intensity no-goes and the generic
hypertranscendental-source extraction theorem. It found no theorem enlarging one circuit's atom
predicate to the joint Coulomb/de Sitter/horizon/centered-zeta--Gamma intensity range and no
ten-target atlas.

Literature audit after exact Lean proof:

- Martius--Lampert, *Extrapolation and learning equations*
  ([arXiv:1610.02995](https://arxiv.org/abs/1610.02995)), and Udrescu--Tegmark,
  *AI Feynman* ([arXiv:1905.11481](https://arxiv.org/abs/1905.11481)), study finite
  compositional symbolic-expression recovery but do not classify hypertranscendental sources.
- Harrington--Ho--Meshkat, *Differential Algebra for Model Comparison*
  ([arXiv:1603.09730](https://arxiv.org/abs/1603.09730)), and
  Ovchinnikov--Pogudin--Thompson, *Parameter identifiability and input-output equations*
  ([arXiv:2007.14787](https://arxiv.org/abs/2007.14787)), use differential input-output fields
  and elimination, but do not give this Gamma phase/intensity atlas.
- Current work on arithmetic and closure algorithms for D-algebraic functions confirms the
  generic closure background; targeted searches for the four named intensity systems, ten
  oriented targets, or a joint hypertranscendental circuit-blindness theorem found no match.

The abstract fact that field operations and differentiation preserve differential algebraicity is
classical. Novelty claim is therefore restricted to the exact family-source formulation and its
cross-system four-observation/ten-target specialization.

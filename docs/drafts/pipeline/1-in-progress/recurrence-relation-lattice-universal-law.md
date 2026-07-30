# The recurrence-relation lattice universal law

- **ID:** `recurrence-relation-lattice-universal-law`
- **Stage:** 1-in-progress
- **Type:** MASTER CONJECTURE / FINITE QUANTUM RECURRENCE /
  ARITHMETIC TOMOGRAPHY / INTERACTION RECONSTRUCTION
- **Date:** 2026-07-30
- **Status:** `[CORE THEOREMS LEAN-PROVED] [SYNTHESIS OPEN]`
  `[EXTERNAL PRIORITY AUDIT OPEN] [NATURE GATE OPEN]`
- **Formal files:**
  `formal/GaloisForLFunctions/HTGeometry/ResolvedRecurrenceRelationCompletenessLaw.lean`,
  `formal/GaloisForLFunctions/HTGeometry/RecurrenceSwapInteractionReconstructionLaw.lean`

## One law

For a finite labelled spectrum \(E=(E_i)_{i\in I}\), define its integer
relation lattice
\[
  L_E=\left\{k\in\mathbb Z^I:
    \sum_i k_iE_i=0\right\}.
\]
Uniform completed-time sampling of the spectral phase orbit has a unique
limiting probability law \(\nu_E\), and
\[
\boxed{
  \widehat{\nu_E}(k)
  =
  \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}
    e^{it\sum_i k_iE_i}\,dt
  =
  \mathbf 1_{L_E}(k).
}                                                       \tag{U}
\]
Moreover,
\[
  \boxed{\nu_E=\nu_F\iff L_E=L_F.}                     \tag{C}
\]

Equation `(U)` is the proposed master object. Recurrence is not a list of
return-time formulas. It is Fourier tomography of the complete arithmetic
constraint lattice of the spectrum.

## Exact resolution law

For a balanced character \(k\), put
\[
  h(k)=\sum_i\max(k_i,0).
\]
The resolved \(n\)-replica recurrence hierarchy detects exactly
\[
\boxed{
  L_E^{\rm proj}\cap\{k:h(k)\le n\},
}                                                       \tag{R}
\]
where \(L_E^{\rm proj}=L_E\cap\{\sum_i k_i=0\}\). Every
projective relation first appears at exactly replica order \(h(k)\).
Consequently the complete resolved hierarchy reconstructs
\(L_E^{\rm proj}\); no projective arithmetic relation is permanently hidden,
and every finite replica order has an exact height boundary.

With full-support positive spectral weights, occurrence in `(R)` is
equivalent to a strictly positive Fourier-character coefficient in the
actual survival-fidelity replica polynomial. The zero-detuning condition is
equivalent to the pair-resolved phase average converging to one. This is not
an existence-only encoding.

## Interaction inverse law

Relative to supplied finite local coordinates, let a mask \(M\) partially
swap two energy-labelled configurations. Then
\[
  M\text{ preserves every two-history energy}
  \iff
  E\text{ is additively separable across }M\mid M^c.   \tag{I}
\]
The valid masks form a finite Boolean algebra. Its atoms:

1. are pairwise disjoint;
2. cover every supplied site exactly once;
3. determine every valid mask;
4. are the unique minimal nonempty additive blocks;
5. are reconstructed by the pair-resolved order-two recurrence kernel.

Thus `(I)` is an inverse consequence of `(U)` on a physically controlled
family of order-two characters:

> The way a quantum system repeats contains a complete map of which declared
> parts are dynamically indivisible.

## Forward shadows

The following earlier results become consequences or specializations of one
constraint object rather than adjacent theorems:

1. maximal projective rank is \(L_E^{\rm proj}=\{0\}\);
2. full projective Haar recurrence is the trivial-relation case of `(U)`;
3. all-order collision floors are the trivial-projective-lattice case;
4. component histogram and Boolean-cube collisions are the additive
   factorization part of \(L_E^{\rm proj}\);
5. product/exponential/log-normal return regimes are scalar shadows after
   discarding the resolved lattice;
6. the Boolean mask algebra recovers the finest additive factorization from
   selected order-two lattice elements;
7. generic local maximality, if its remaining formal capstone closes, says
   a connected local interaction generically destroys every nontrivial
   projective relation.

## What would make this “wow” rather than formal

The manuscript must not sell `(U)` as the elementary integral
\(\lim_T\operatorname{sinc}(T\omega)\). The candidate discovery is the
closed inverse chain
\[
\text{completed recurrence ensemble}
\Longleftrightarrow
\text{integer relation lattice}
\Longleftrightarrow
\text{all resolved replica layers},
\]
together with recovery of the unique additive interaction partition from
the order-two controlled sector and the exact height at which every hidden
relation becomes observable.

The synthesis is scientifically strong only if it answers:

> What complete structural information about a finite Hamiltonian is encoded
> in recurrence, and at which correlation order does each piece appear?

The answer must be: all global-phase-invariant integer spectral constraints,
at their exact arithmetic heights, including the finest additive interaction
blocks relative to supplied controls.

## Hostile novelty audit

Known parents already include:

- Kronecker--Weyl and Fourier theory of torus flows;
- higher-order spectra/polyspectra as detectors of phase coupling;
- spectral-form-factor moments and replica collision counting;
- rational-independence criteria for full-torus recurrence;
- rectangle tests, differential grouping and functional additive
  separability;
- independent-history product laws for free and factorized spectra.

Those ingredients receive no novelty credit.

The candidate-new exact object is the joined completeness theorem:

1. unique completed phase ensemble with Fourier transform exactly
   \(\mathbf1_{L_E}\);
2. equivalence of ensemble and full relation lattice;
3. exact replica-height filtration of the projective sublattice;
4. operational positive-coefficient and phase-kernel realization;
5. Boolean atomic reconstruction of the finest additive interaction
   partition from controlled order-two recurrence.

Preliminary searches found no source stating this full chain. Exact priority
remains unverified. A source containing the ensemble--lattice equivalence
plus the exact replica filtration and interaction inverse law kills the
headline novelty. A source containing only torus annihilators, polyspectral
coupling, or additive rectangle tests kills only that ingredient.

## Non-overclaim boundary

- Finite labelled spectra only for the exact phase-ensemble theorem.
- Supplied local coordinates and controllable partial swaps are required for
  interaction reconstruction.
- No tensor-product structure, physical space, locality, gravity or
  subsystem ontology is derived from a blind spectrum.
- Scalar SFF moments aggregate relations and need not reconstruct the
  lattice; the theorem requires resolved Fourier characters.
- Infinite-volume recurrence is not asserted.
- No black-hole, cosmological or arrow-of-time conclusion follows without a
  model-specific bridge.
- Formal verification contributes truth control only, never novelty or
  significance.

## Nature gate

Current hostile verdict: **mathematically cohesive and potentially
headline-worthy, but not yet Nature-ready**.

Required before promotion:

1. complete exact-object literature audit across torus resonance modules,
   polyspectral completeness, Hamiltonian learning and SFF moments;
2. show a nontrivial physical question or inference enabled by `(U)`--`(I)`
   that existing methods do not answer;
3. formalize the generic local-generator capstone or remove every generic
   local claim;
4. rewrite the paper around equation `(U)`, not the previous recurrence
   anatomy collage;
5. obtain a hostile review concluding that the synthesis changes physical
   interpretation rather than merely renaming standard harmonic analysis.

## Formal status

Unconditional Lean theorems currently prove:

- `existsUnique_spectralRelationPhaseEnsemble`;
- `spectralRelationLattice_eq_iff_phaseEnsemble_eq`;
- `resolvedReplicaDetects_iff_relation_and_height_le`;
- `relation_iff_detected_at_exact_replicaHeight`;
- `resolvedReplicaDetects_iff_positiveCoefficient_and_phaseAverage`;
- `relationLattice_eq_iff_all_resolvedReplicaDetectors_eq`;
- `universalRecurrenceSwap_iff_additivelySeparableAcross`;
- Boolean closure of recurrence masks;
- atom disjointness, coverage and unique site assignment;
- `isUniversalRecurrenceSwap_iff_all_phaseAverages_tendsto_one`.

Target compilation and axiom audits pass with only `propext`,
`Classical.choice` and `Quot.sound`.


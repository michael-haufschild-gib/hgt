# Differential-clock frame composition

- **ID:** differential-clock-frame-composition
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HYPERTRANSCENDENCE BRIDGE
- **Source:** coherent quantum reference-frame changes and functorial local observables
- **Statement:** The finite observable-field equivalences induced by derivation-preserving field embeddings preserve identities and composition exactly, so the differential clock slices form a strict functor with no separate coherence hypothesis.

## Goal

Upgrade finite-slice embedding covariance from isolated equivalences to a coherent multi-frame
interface.  Success means that changing through an intermediate differential presentation is
definitionally controlled by the direct change, rather than requiring a supplied comparison map.

## Gates

- [x] 0 → 1 in-progress: identity and two-stage composition laws isolated from the finite-slice construction
- [x] 1 → 2 fully-proven: derivation preservation, identity-frame equality, equivalence composition, and pointwise rewriting proved
- [x] 2 → 3 formalized: scratch certification, exact-module cache build, direct source check, and axiom audit pass
- [ ] 3 → 4 publication-ready: instantiate a nontrivial chain of analytic differential-field presentations

## Physics sources

- A.-C. de la Hamette and T. D. Galley, *Quantum reference frames for general symmetry groups*, arXiv:2004.14292, derives reference-frame changes from relational physics and explicitly requires coherent change of reference frame.
- R. Brunetti, K. Fredenhagen, and R. Verch, *The generally covariant locality principle -- A new paradigm for local quantum physics*, arXiv:math-ph/0112041, formulates locally covariant QFT as a covariant functor from spacetime embeddings to injective observable-algebra morphisms.
- P. A. Höhn and A. Vanrietvelde, *How to switch between relational quantum clocks*, arXiv:1810.04153, links reduced theories associated with different clock choices through a clock-neutral constrained theory.

The Lean result transfers the coherence/functoriality requirement to finite differential
jet-observable fields.  It does not identify those fields with QFT algebras or the physical clock
systems of the cited papers.

## Exact relation

Let `e : E ->_F L` and `f : L ->_F M` preserve their derivations.  Then the composite does as well:

```text
(f o e)(delta z) = delta''((f o e) z).                    (1)
```

At every finite resolution `N`, the existing finite-slice construction gives equivalences

```text
j_e,N : P_N(x) ~= P_N(e x),
j_f,N : P_N(e x) ~= P_N(f(e x)),
j_(f o e),N : P_N(x) ~= P_N(f(e x)).
```

The new composition theorem proves

```text
j_(f o e),N = j_e,N followed by j_f,N,                    (2)
```

and the identity embedding gives

```text
j_id,N = id.                                              (3)
```

Equations `(2)` and `(3)` make path coherence automatic.  The index `N` is observable resolution,
not elapsed time.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/DifferentialClockEmbeddingComposition.lean` proves:

- `differentialAlgHom_comp_preserves_derivation`;
- `differentialAlgHom_id_preserves_derivation`;
- `jetObservableFieldEmbeddingEquiv_id`;
- `jetObservableFieldEmbeddingEquiv_comp`;
- `jetObservableFieldEmbeddingEquiv_comp_apply`.

## Corpus value

Every multi-stage extension-field argument may now replace an assumed coherence square by an exact
rewrite.  Together with `jetObservableFieldEmbeddingEquiv_mono`, the finite observable slices are
coherent both across frame changes and across increasing resolution.  This is general
hypertranscendental-clock infrastructure; no zeta or `RHTower` premise is present.

## Status

[PROVED IN LEAN] The exact target and direct source checks pass.  The derivation-composition theorem
uses only `propext` and `Quot.sound`; the finite equivalence laws additionally use
`Classical.choice`.  No full project build, numerical experiment, or concurrent Lean process was
run.

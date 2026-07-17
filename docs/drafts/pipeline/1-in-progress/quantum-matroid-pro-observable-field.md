# Quantum Matroid Pro-Observable Field

- **ID:** QM-PRO-OBS
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** research programme · constraint-native QFT of matroid fields
- **Statement:** **[CONJECTURE]** A continuum quantum field theory whose matroidal structure is physical rather than decorative is an enriched local pro-matroid of observable constraints, and intrinsic hypertranscendence occurs exactly through an unbounded free vertical jet sector rather than through any finite matroid state sum.

## Goal

Construct a quantum field theory in which a matroid is the local geometry of dependence among observables or source constraints, not a discrete label assigned to each spacetime point and not a repackaging of a Grassmannian sigma model, Potts model, stabilizer state, or Tutte polynomial. Derive a theorem that forces hypertranscendence from the QFT axioms rather than inserting a hypertranscendental coefficient by hand.

The field is to be constraint-native: it is fixed by a compatible local dependence structure and its gluing laws, not propagated by a finite differential flow.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, novelty parents identified
- [ ] 1 → 2  fully-proven: complete construction, consistency theorem, nontrivial model, and hypertranscendence theorem
- [ ] 2 → 3  formalized: unconditional Lean theorem batch in `formal/GaloisForLFunctions/HTGeometry`
- [ ] 3 → 4  publication-ready: standalone paper with physics, mathematical construction, predictions, and Lean certificate

## Proposed object

The physically selected refinement of this programme is now the labeled Wick-contracted differential matroid field in `wick-contracted-differential-matroid-field.md`. It replaces the preliminary rank-only language by the full contraction of the algebraic matroid of connected-correlator jets over the face-complete Gaussian base. The foundation/representation-space construction below is retained as finite realization and gluing data for that interaction matroid, not as the primary microscopic field.

Let `Caus(X)` be a category of bounded causally admissible regions of spacetime. A quantum matroid pro-observable field consists provisionally of:

1. a local observable or source ground set `E(O)` for each region `O`;
2. an enriched finitary matroid `M(O)` on `E(O)`, encoding algebraic or differential-algebraic dependence;
3. restriction compatibility `M(O) = M(O')|E(O)` for `O ⊆ O'`;
4. a quantum observable algebra `A(O)` representing `M(O)`, with spacelike commutativity in `A` but not the false assumption that spacelike matroids are direct sums;
5. a gluing law for covers, with cross-region circuits recording constraints or entanglement; for generalized parallel connections the candidate universal coefficient object is the matroid foundation, whose parent theorem glues by relative tensor product;
6. a coefficient enrichment retaining sign, valuation, and integral period-closure data when physically required;
7. a jet filtration `E_0(O) ⊆ E_1(O) ⊆ ⋯` and compatible finite matroids `M_n(O)` whose limit is a pro-object.

For a source or observable `a`, its vertical jet fibre is

`J(a) = {a, Da, D²a, ...}`.

The vertical sector is hypertranscendental over the coefficient differential field precisely when every finite subset of `J(a)` is algebraically independent. Thus the restriction of the differential-algebraic matroid to `J(a)` is the free finitary matroid of infinite rank. Horizontal circuits between different sources, regions, or sectors encode interaction. The intended physical object is therefore bigraded: vertical freedom measures hypertranscendental innovation; horizontal circuits measure coupling.

## Exact discriminators

### Discrete-target no-go

For fixed finite ground set `E`, the collection of matroids on `E` is finite and discrete. Any continuous map from a connected spacetime into it is constant. A literal finite matroid-valued field has no local propagating degrees of freedom. Matroids can instead label strata, phases, or defects of a continuous realization field, or occur as a local pro-observable structure.

This elementary statement is a route-kill, not new scientific knowledge.

### Grassmannian reduction test

A matrix or Plücker field `p : X → Gr(r,n)` has a matroid support stratum determined by its nonzero Plücker coordinates. Without a load-bearing action or gluing law sensitive to matroid wall crossing, this is only a Grassmannian sigma model with renamed strata. A new theory must make circuits, minors, or matroidal gluing determine observables that the parent sigma model does not already determine.

### Tutte reduction test

Finite multiplicative deletion-contraction amplitudes lie under the universal Tutte-character framework. Such an amplitude is a combinatorial state sum, not yet a continuum QFT, and its dependence on finitely many ordinary weights is algebraic or rational. Hypertranscendence cannot be created by the finite recursion unless it is already present in an inserted coefficient. The positive successor must use a non-stabilising pro-system, an analytic completion, or a new local quantum gluing operation outside finite Tutte universality.

### Quantum-information reduction test

Circuit- or independent-set-indexed multipartite matroid states already exist as a quantum-information construction. A basis-exchange Hamiltonian or finite matroid state is not the sought QFT unless it acquires a continuum local net, relativistic locality, gluing/renormalisation, and a continuum observable with a derived hypertranscendence theorem.

### Enrichment necessity

A plain oriented matroid is not enough when global period discreteness or fixed-gauge effectivity is physical: the existing oriented-Gale fracture theorem gives identical chirotopes with opposite period behaviour. The coefficient object must retain integral period closure, Pontryagin-character data, or an explicitly justified quotient of them. Hyperfields and tracts are candidate languages, not yet a solution.

## Open core

### Q1. Local gluing

General matroid amalgams do not always exist. The strongest parent construction currently found is the Baker–Lorscheid–Walsh–Zhang theorem: under the generalized-parallel-connection hypotheses, the foundation of the glued matroid is the relative tensor product of the two foundations over that of the common restriction. Since morphisms from a foundation classify rescaling classes of representations, compatible representation moduli then glue contravariantly by a fibre product.

This supplies exact constraint gluing, but not yet a QFT. The open problem is to choose a causally meaningful class of overlaps for which iterated gluing is coherent and rich enough for interaction. Outside modular-flat or other admissible overlaps an amalgam may not exist or may have no freest choice. A derived span of all amalgams may be required instead of a single-valued functor.

### Q2. Quantisation

Construct a state space and local operator algebra from the matroid data such that:

- circuits impose genuine quantum constraints;
- cross-region circuits survive as measurable correlations rather than mere bookkeeping;
- the construction is reflection-positive or admits an algebraic-QFT formulation;
- the continuum limit is not a disguised Potts, sigma, or stabilizer theory.

### Q3. Hypertranscendental forcing theorem

The first exact boundary is a paper theorem under standard Gauss–Manin hypotheses:

> **Finite matroid-period boundary `[BRIDGE]`.** Fix a finite matroid and a finite gluing diagram of finite matroid foundations. Let a one-parameter amplitude be a period in a finite-rank algebraic Gauss–Manin system on the resulting finite-type representation moduli. Then the amplitude satisfies a nonzero finite-order linear differential equation and is therefore differentially algebraic. A hypertranscendental amplitude cannot be a period of any such fixed finite sector.

This is a synthesis of parent theorems, not new scientific knowledge. It does, however, identify where the positive theory must live: an all-scale pro-system, a non-algebraic quantum completion, or a failure of finite-rank Gauss–Manin capture.

The stronger target is:

> **[CONJECTURE]** If a local matroid observable theory has eventually bounded vertical rank innovation and its gluing/transfer data are finitely generated in differential-algebraic finite type, then every distinguished correlation or partition observable is differentially algebraic. Consequently an intrinsically hypertranscendental observable forces unbounded vertical rank innovation in the pro-matroid net.

The compatibility hypothesis is load-bearing. Arbitrary analytic limits of bounded-order holonomic functions can escape holonomicity, so finite-stage Picard–Fuchs equations alone do not force their limit to be differentially algebraic. The pro-system must carry compatible annihilators, a stabilising finite-rank connection, or an exact directed-rank law. The reverse implication is also false without an analytic realization theorem: an abstract free jet matroid does not by itself construct a function or a QFT. The missing direction is to construct a positive, local analytic model whose observable realizes the free vertical sector.

### Q4. Physical prediction

Find an observable consequence inaccessible to the parent theories. Candidate signatures are a quantised matroid-wall defect charge, a circuit-connectivity contribution to entanglement, or a universal asymptotic law for vertical rank innovation. No prediction is accepted until it survives reduction to known Grassmannian, tropical, stabilizer, and Tutte models.

## Existing project support

- `DifferentialMatroidFoundations.lean`: hereditary and finitary differential independence infrastructure.
- `AlgebraicMatroidRank.lean`: submodular rank packaging for algebraic matroids.
- `UniversalOrientedConstraintProduct.lean`: all finite orientation chambers realise the same embedded differential field, while Herglotz positivity selects the all-positive chamber.
- `HypertranscendentalObservableNet.lean`: finite jet observable fields form an exact strict inclusion net for a hypertranscendental element.
- `FiniteAlgebraicStateBoundary.lean`: every observable in a derivation-closed finite-transcendence state field is differentially algebraic; an HT observable forces at least countable state transcendence degree.
- `FiniteDifferentialSystemAlgebraicity.lean`: every coordinate of a finite linear differential system is differentially algebraic.
- `FiniteGibbsDifferentialBoundary.lean`: every finite Hamiltonian partition function is differentially algebraic.
- `HolonomicityLimit.lean` and its paper card: finite holonomic shadows need not make the limit holonomic; a compatible monotone integer corank is finite exactly when it stabilises.
- `FiniteQuantumGrassmannRepresentation.lean`: finite exterior/quantum detector kinematics, not a matroid QFT.
- `source-logarithmic-boundary-matroid.md`: source-boundary classes represent differential-algebraic dependence; the multi-observable rank theorem is a direct bridge candidate.
- `oriented-gale-period-closure-fracture.md`: exact obstruction to using a chirotope as the full physical field.

## Literature novelty boundary

- Baker–Bowler matroids over hyperfields/tracts already unify linear, oriented, and valuated matroids through circuit and Grassmann–Plücker axioms.
- MacPherson matroid bundles already provide combinatorial bundle data. The claimed general equivalence between matroid and ordinary Grassmannians is not available; Mnev identified a flaw in the published proof.
- Tropical sigma models and tropical/matroid bundles already occupy much of the obvious target-space route.
- Universal Tutte characters already control deletion-contraction invariants in broad combinatorial coalgebra settings.
- Foundations of generalized parallel connections already glue by relative tensor product under suitable hypotheses; the gluing algebra itself is parent mathematics.
- Matroidal polynomials already occur in the singularity theory of Feynman diagrams.
- Fixed Feynman integrals already admit Picard–Fuchs differential equations in external parameters, including broad massive multi-loop families.
- Chirotopes and oriented matroids have repeatedly been proposed as structures in mechanics, gauge theory, branes, loop quantum gravity, and quantum information.
- Ferreira–Silva–La Guardia–Andrade (2026) already construct multipartite matroid states from circuits and independent sets.

No checked source yet supplies a local continuum QFT whose field content is a compatible pro-matroid of differential constraints and whose axioms force a hypertranscendental observable. This is a search result, not a novelty proof.

## Falsifiers

Retire or reframe this programme if any of the following occurs:

1. the proposed local net is equivalent to an established algebraic QFT net after forgetting matroid labels;
2. the amplitude factors only through a universal Tutte character;
3. the continuum field is only a sigma model into a known Grassmannian, tropical linear space, or MacPhersonian;
4. hypertranscendence enters only through a coefficient chosen to be hypertranscendental;
5. the purported gluing law fails on the claimed class of local matroids;
6. the observable matroid carries no operational information beyond the underlying local algebra;
7. the construction cannot state a measurable or structurally rigid prediction.

## Immediate attack

1. prove and formalise only the nontrivial reusable structural core, not the elementary connected-to-discrete no-go;
2. classify gluable matroid classes and test whether generalized parallel connection supplies associative causal gluing;
3. formulate the finite-presentation obstruction with exact differential-algebraic hypotheses;
4. build the smallest positive model from a represented source-boundary matroid and a finite jet filtration;
5. derive an observable wall/entanglement/innovation law;
6. run the dual NOVEL × SIGNIFICANT gate against the exact parent theory before promotion.

## Log

- 2026-07-17 — created in 1-in-progress after corpus audit and first literature gate. The pro-matroid observable net and the hypertranscendental forcing theorem remain `[CONJECTURE]`; all finite-target and finite-Tutte statements are route-kills or bridges.
- 2026-07-17 — **directed persistence law proved and formalized** (`wick-contracted-directed-persistence.md`, `HTGeometry/WickContractedMatroidPersistence.lean`, axiom-clean): over any finitary ambient matroid, independence in the contraction by a nonempty directed base union is exactly stage-wise independence; instantiated for `differentialMatroid` and for the Wick interaction matroid on any signal window.  The Q1/O1 coherence half is closed at the undecorated skeleton level, and the persistence criterion of the WCDMF refinement is a theorem there: intrinsic vertical freedom cannot be destroyed only in the face-complete limit, and collapse is finite-stage detectable.  `[BRIDGE]`, novelty not claimed.  Open next moves: (i) decorated persistence — do circuit equations, valuations, and phase/period data pass to directed limits (O2 representation question); (ii) the relative reading `(differentialMatroid F E ／ G).Indep I ↔` differential independence over the `G`-generated differential field, which needs insensitivity of differential independence to differential-algebraic base extension.

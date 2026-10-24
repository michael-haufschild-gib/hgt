# Exact observer recurrence on every connected interaction network

- **ID:** connected-network-all-observer-recurrence
- **Stage:** 3-formalized
- **Type:** THEOREM; dependency-closed paper proof and Lean capstones complete
- **Source:** `quantum-recurrence-strongest-form-2026-10.md`
- **Statement:** Every finite connected interaction graph, with arbitrary local dimensions at least two and its full Hermitian onsite-plus-edge coefficient space, has almost everywhere the exact simultaneous all-observer continuous-time return exponent `max(D-c(G_B)-1,0)/2`.

## Exact conjecture and scientific question

Let `V` be a finite nonempty site set, `A_v` finite local alphabets with `q_v=|A_v|>=2`, and `G` a connected interaction graph. Put `D=prod_v q_v`. Let `L_G` be the full real linear space of Hermitian operators supported on single sites or graph edges, with arbitrary coefficients on those supports.

For Lebesgue-almost every `H in L_G`, its spectrum is simple and, **simultaneously for every finite matrix family** `B_a`, nonnegative weights `lambda_a`, and `t0>0`, define

`D_B(t)=sum_a lambda_a ||exp(-itH) B_a exp(itH)-B_a||_HS^2`,

`T_B(delta;t0)=inf{t>=t0 : D_B(t)<delta}`.

In the energy basis let `G_B` join `i != j` when

`sum_a lambda_a (|(B_a)_ij|^2+|(B_a)_ji|^2)>0`.

Then

`lim_(delta -> 0+) log T_B(delta;t0)/log(1/delta) = max(D-c(G_B)-1,0)/2`.

No spectral, Diophantine, eigenvector, chaos, or noncommutation condition is imposed on the generic event. Graph, factor dimensions, and locality specify the model, rather than encoding a missing analytic input. The event is chosen before the observers. Constants and onset need not be uniform over observers.

The question is whether branching, inhomogeneous site dimension, or interaction geometry can impose a smaller asymptotic exponent than observable phase connectivity permits. Connectedness alone suffices in the full coefficient family. The same result then applies to connected interaction hypergraphs under the support-contained convention, because their two-section graph terms are admissible.

## Internal and external frontier

- Corpus: `QuditPathChainEscape` and `FiniteQuantumObserverGraphExtremalityLaw` prove the all-observer law on paths; `SiteFactorGraphWitness` and hypergraph factorization prove arbitrary-network **rational** spectral maximality. Rational maximality alone does not imply the **real affine escape** needed for analytic metric extremality.
- Corpus: `leafHermitianLocalHamiltonian_spectrumEscapesAffineRelations` already proves the exact one-leaf real escape mechanism, with a maximally projective old system and connected nonbipartite endpoint probes.
- Literature: Lee--Pilatowsky-Cameo--Choi, arXiv:2609.26885, Proposition S2, now proves generic all-order nonresonance on local qubit lattices. This eliminates that old priority claim. It does not itself state the all-observer small-tolerance first-return classification.
- Classical parents: Kleinbock--Margulis analytic extremality, Dirichlet approximation, and forest phase coordinates. The return-exponent mechanism is a bridge; the model-specific discharge and simultaneous network universality are the candidate contribution.

## Attack before formalization

**Verdict: SURVIVES PRELIMINARY ATTACK.**

1. A universal graph-capacity exponent for *every* spectrum is false: commensurate spectra are periodic. Here the arithmetic conclusion is proved on a conull coefficient event, not assumed.
2. Dense rational independence does not imply real nondegeneracy: `(t,alpha*t)` with irrational `alpha` is the elementary obstruction. Therefore generic rank theorems cannot be substituted for the new escape theorem.
3. Connected graphs need not contain a spanning path. The proof removes a non-cut vertex and uses a one-leaf extension, so stars and branching trees are included.
4. The single-qubit endpoint transition graph cannot be nonbipartite. One- and two-site systems are handled directly as full matrix spaces; the recursive step uses at least two old sites.
5. Noncommuting summands with compensating coefficients do not certify intrinsic noncommutation. No such claim enters this theorem.
6. Scalar expectation histories may cancel, so their exact exponent is not claimed. Matrix return and trace-distance state return are the admitted operational meanings.
7. This is a fixed-finite-size, shrinking-tolerance law; it gives neither a uniform onset nor a fixed-error thermodynamic first-return lower bound.

## Dependency-closed paper proof

### 1. Real affine spectral escape on a connected graph

Call a Hermitian family escaping if, for every nonzero real balanced coefficient vector `c` and every real number `a`, it contains a matrix with simple energy packet `E` such that `sum_i c_i E_(sigma(i)) != a` for **every** permutation `sigma`.

If `|V|=1`, all Hermitian matrices are onsite. If `|V|=2`, connectedness supplies the edge covering both sites, hence again the entire Hermitian matrix space is available. Real diagonal entries can avoid the finitely many affine hyperplanes indexed by permutations. This is exactly `diagonalSet_spectrumEscapesAffineRelations` followed by inclusion.

Suppose `|V|>=3`. A finite connected graph has a vertex `v` whose deletion remains connected. The old graph has at least two vertices. The already closed site-chart witness supplies an old maximally projective Hermitian Hamiltonian with a physical site-product chart and a connected nonbipartite Hermitian probe family at every old site: use `exists_siteFactorChart_rootedSpanningTree` if an old factor has dimension at least three, and `exists_siteFactorChart_binarySpanningTree` otherwise. Choose an old neighbour `u` of `v`.

Apply `leafHermitianLocalHamiltonian_spectrumEscapesAffineRelations` at `u` with new factor `A_v`. This gives escape inside the full Hermitian submodule of the old architecture extended by this one edge. Transport its physical carrier by

`(old chart x identity_(A_v)) ; leafSiteEquiv`

to the named product `prod_(w in V) A_w`. Each explicitly local generator has form

`K tensor I + I tensor diag(s) + A_u tensor B`.

The old term lies in the span of old onsite and edge terms by the chart; the new onsite term is supported on `{v}`; the coupling is supported on `{u,v}`. The named graph contains every old edge and the chosen new edge. Thus the transported generator belongs to its local term span. It is Hermitian, so `mem_siteFactorLocalSubmodule_of_mem_termSpan` places it in `L_G`. Real linearity extends this inclusion from generators to the full leaf submodule. Reindexing preserves characteristic roots and escape, proving the desired real affine escape on `L_G`.

All inputs in this step are already proved corpus theorems; the new task is their exact transport and composition, not a new endpoint-probe assumption.

### 2. Generic simple spectrum and every observer at once

Choose a real basis of `L_G` and enumerate the physical carrier by `Fin D`. The coordinate family is Hermitian and inherits affine escape. It has positive parameter dimension because it contains a nonzero matrix. Existing arbitrary-network maximality supplies a maximally projective member, and polynomial spectral-obstruction genericity gives maximal projectivity, hence simple spectrum, almost everywhere in the same coordinates.

For each labelled coherence graph choose one root in each connected component. The root-to-nonroot incidence rows are linearly independent balanced vectors. There are `r=D-c` of them. Their gaps divided by one nonzero clock gap form an analytic map on every connected simple-spectrum chart. A real affine relation among its coordinates, after clearing the clock denominator, would contradict step 1. Kleinbock--Margulis therefore makes this `(r-1)`-packet non-VWA almost everywhere for `r>=2`.

The set of labelled graphs at fixed `D` is finite. Intersect their conull events, then use the countable chart cover of the simple locus. `ae_hasUniversalFiniteObserverFirstReturnLaw_simpleLocus` is precisely this closed argument, including the `r=0,1` boundaries.

For any observer selected afterwards, its squared displacement equals weighted graph chord energy. Forest paths compare that energy in both directions with the squared distance of the `r` root-relative phases to zero. Continuous time spends one phase as a clock; the non-VWA first-return theorem and Dirichlet's upper estimate give exponent `r-1` in phase radius, hence `(r-1)/2` in squared displacement. Rank zero is stationary; rank one is periodic. Both have exponent zero. This proves the stated law with no unproved arithmetic input.

### 3. Hypergraphs and ordinary state returns

For a connected finite hypergraph, the onsite-plus-edge space of its connected two-section graph is included in the full onsite-plus-hyperedge space. Affine escape persists under enlargement. Repeat step 2 in that larger coefficient space.

For a density matrix use the one-observer family `B=rho`. Finite-dimensional Hilbert--Schmidt and nuclear norms are equivalent, so trace-radius exponent is `max(D-c(G_rho)-1,0)`. For a pure projector, its coherence graph is complete on exact spectral support and isolated outside; the squared Hilbert--Schmidt defect equals twice the fidelity deficit. Support size `s` therefore gives `max(s-2,0)/2`. These transfers already have exact Lean declarations.

## Gates

- [x] Corpus-first search and exact source inspection.
- [x] Primary-literature attack and corrected priority claim.
- [x] Exact conjecture, counterexamples to stronger false variants, and admissible model scope.
- [x] Dependency-closed paper proof.
- [x] New connected-network affine-escape theorem checked in Lean.
- [x] Generic all-observer graph and hypergraph capstones checked in Lean.
- [x] Direct final source audit and transitive axiom check.
- [x] Integration into replacement paper and hostile review.

## Log

- 2026-10-24 — Exact network extension selected after September literature invalidated the old nonresonance novelty claim. Paper proof completed before new Lean source work.
- 2026-10-24 — `ConnectedGraphSpectralAffineEscape.lean` passed direct source check without warnings. Graph and support-contained hypergraph affine escape are now proved; observer capstone source written, verification pending.
- 2026-10-24 — Graph/hypergraph observer capstones and exact pure-state fidelity specialization passed direct source checks. Both new modules are wired into HTGeometry. The physical two-qubit seed was refactored to eliminate its prior raised heartbeat limit and passed under default limits. All 31 final audit roots use only propext, Classical.choice and Quot.sound. Replacement manuscript, claim trace, literature audit and nine-page PDF completed and visually checked. Candidate novelty remains subject to external expert review.

## Final artifacts

- `formal/GaloisForLFunctions/HTGeometry/ConnectedGraphSpectralAffineEscape.lean`
- `formal/GaloisForLFunctions/HTGeometry/ConnectedNetworkAllObserverRecurrenceLaw.lean`
- Manuscript and complete audit: `../4-publication-ready/universal-quantum-recurrence-anatomy/README.md`.

# Countable observer weaving and coercivity–defect law

- **Created:** 2026-08-03
- **Stage:** 3 — formalized; publication package under hostile audit
- **Type:** THEOREM
- **Status:** `[PROVED HERE; NOVELTY UNVERIFIED]`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/PythagoreanObserverBlindness.lean`
- **Paper:** `docs/drafts/pipeline/4-publication-ready/two-sided-singular-gelfand-defects/main.tex`

## Source-pure question

For bounded injective dense-range Hilbert observers `T_i : G → H_i`, classify closed source subspaces whose image remains dense under every observer. Find the strongest law requiring no target theorem, spectral ansatz, commutation, or joint stability.

## Universal law

### Arbitrary-family observer–annihilator duality

For every closed `M ≤ G`,

`(∀ i, Dense (T_i(M))) ↔ (∀ i, M⊥ ∩ ran(T_i*) = {0})`.

Lean: `dense_images_iff_orthogonal_avoids_adjointRanges`.

### Countable coercivity–wildness dichotomy

For a countable family:

1. If some observer is coercive, every closed common dense-image subspace is `G`.
2. If all observers are noncoercive, there is a closed `D ≤ G` containing a countably indexed linearly independent family such that `D ∩ ran(T_i*) = {0}` for every `i`, and every closed `L ≤ D` yields the common dense-image defect `L⊥`.

Lean: `countable_observer_coercivity_wildness_law`.

This theorem is stronger than the retired stable spectral route: it removes stability and spectral hypotheses and extends from two to countably many observers.

## Dependency-closed proof

1. For injective bounded Hilbert maps, noncoercivity is equivalent to nonclosed range.
2. Nonclosed range persists after restriction to the orthogonal complement of any finite-dimensional subspace: otherwise the full range is a closed subspace plus a finite-dimensional subspace.
3. Enumerate observer/vector/scale triples and recursively choose an orthonormal array `u_{i,k,n}` with
   `‖T_i u_{i,k,n}‖ < (a_i b_n)^2`, where `a_i=(i+1)⁻¹`, `b_n=(n+1)⁻¹`.
4. In coefficient `ℓ²(ℕ³)`, define the closed thread space
   `N = {z : z_{i,k,n}=a_i b_n z_{0,k,0}}`.
5. Synthesize the orthonormal array by a linear isometry `U` and put `D=U(N)`. Square summability of `(a_i b_n)` gives a countably indexed linearly independent family in `D`.
6. If `Uz=T_i*y`, then for each `k,n`,
   `a_i b_n |z_{0,k,0}| ≤ ‖T_i u_{i,k,n}‖ ‖y‖ < (a_i b_n)^2 ‖y‖`.
   Divide by the positive factor and let `n→∞`; every base coefficient vanishes, hence `z=0`.
7. Observer–annihilator duality transfers every closed `L≤D` to the dense defect `L⊥`.
8. In the coercive branch, a closed restriction has closed image; density gives surjectivity, and injectivity forces the restriction domain to be all of `G`.

## Rigged-Hilbert shadow

Closed operator graphs carry bounded coordinate observers. Compatible Hilbert pre-quasi negative embeddings lie in the canonical inverse-adjoint graph; quasi compatibility is graph saturation. The two-observer law therefore identifies the exact graph-coordinate defect mechanism. The explicit diagonal model produces a Hilbert pre-quasi pair that is not quasi.

Lean declarations:

- `preQuasi_graph_le_canonical_graph`
- `preQuasi_quasi_iff_eq_canonicalNegative`
- `preQuasi_of_closed_biDense_canonicalGraphSubspace`
- `twoSidedSingular_iff_hasProperClosedBiDenseSubspace`
- `exists_hilbertPreQuasiPair_not_quasi`
- `not_every_hilbertPreQuasiPair_is_quasi`

## Novelty boundary

Classical and recent sources cover one operator range, unitary disjoint copies, complements of operator ranges, and unions under span/nonclosedness hypotheses. No exact countable simultaneous theorem without a condition on the combined span was located. Priority remains independently unverified.

## No-go closure

### Retired route

Stable two-observer normalization plus spectral endpoint weaving.

### Positive survivor

Finite-codimensional persistence and direct orthonormal weaving prove a strictly stronger countable theorem. No spectral statement remains in the paper.

## Formal status

- Direct `lake env lean` on headline module: PASS during development.
- Umbrella import: present.
- Final targeted build, lint, and axiom audit: pending final publication audit.
- Manuscript claim ledger: `CLAIM_TRACE_AUDIT.md` in publication package.

## Promotion gate

Move to stage 4 only after:

- final targeted Lean build passes;
- formal lint and axiom audit pass;
- PDF has no layout defects;
- hostile referee report checks every manuscript claim against Lean ledger;
- novelty language remains qualified pending independent priority confirmation.

## Log

- 2026-08-03 — observer–annihilator law and explicit two-observer model formalized.
- 2026-08-03 — stable spectral route superseded by direct finite-family weaving.
- 2026-08-03 — construction extended to countable families and packaged as exact coercivity–wildness dichotomy.
- 2026-08-03 — manuscript rewritten to remove every unformalized Banach, spectral, and stability claim.

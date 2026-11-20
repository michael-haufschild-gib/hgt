# Can a static orbit hide its dynamics in a smaller tensor factor?

**Question.** Does robust circuit hardness survive forgetting the physical tensor coordinates? Use normalized Choi distance and allow a change of basis on the full Hilbert space.

**Snapshot conjecture.** For dimension (D=km), a single unitary admits a basis in which it is close to a diagonal unitary on (k) levels tensored with the identity on (m) levels. Seek an error of order (k^{-1/2}), uniformly in (m). Sort the eigenangles. Partition them into consecutive equal-mass blocks. The block widths have total at most one full turn.

**History conjecture.** Fix the tensor coordinates once for a simple-spectrum static Hamiltonian. The completed-time mean squared normalized Hilbert–Schmidt distance to the entire linear space (M_k\otimes I_m) is at least (1-1/m), even allowing a different approximant at every time. Dephasing leaves the sum of projected squared norms of the rank-one energy projectors. Their partial traces are density matrices of purity at most one. Equality should characterize product eigenvectors across the chosen split.

**Connection to first returns.** With fixed spectral labelling, a product spectrum across a bipartition obeys independent anchored rectangle relations. In the unlabelled problem all eigenvalue assignments are available. Any shrinking-tolerance first-return theorem from these relations needs a separate fixed-error analysis as dimension grows.

**Scope.** No fixed-error first return from the initial ramp, maximal physical gate-complexity theorem, or gravitational volume observable has been derived here. The operator-norm and normalized Choi metrics require separate arguments.

## Optimizing over every autonomous simulator

Let a source have D distinct energies with pairwise distinct nonzero ordered gaps. For every competitor with at most k distinct energies, optimize its eigenbasis, sector ranks and energies, with 1 ≤ k ≤ D. The predicted sharp long-window supremum of normalized squared trace overlap is

`[D + k(k − 1)] / D²`.

Write the unnormalized amplitude as `Σᵢₐ pᵢₐ exp(it(Eᵢ−Fₐ))`, where `pᵢₐ` is the diagonal of competitor projector a in source eigenstate i. Each row is a probability vector. After squaring, every term with equal source indices costs at most D in total. For unequal source indices and each ordered pair of distinct competitor sectors, at most one ordered source gap can match. Each such term weighs at most one. Choose k source energies for the competitor and assign their source eigenvectors to different sectors. Give each remaining source eigenvector any of those labels. The zero detuning then has weight k, and the D−k other detunings are distinct. Prescribed equal sector ranks are possible when k divides D.

Let γ be the least spacing of the distinct source gaps, including zero. In a window of half-length T, every detuning at least γ/2 from resonance costs at most 2/(Tγ) after normalization. A competitor gap can be within γ/2 of at most one nonzero source gap. The resulting upper bound is uniform in window origin and simulator, even if a new model is chosen for every window. This strengthens the fixed-model dephasing argument. Lean obligations include the sinc-window estimate, overlapping-basis trace expansion, equality construction and connected-local genericity discharge.

For the finite-aperture converse, a uniform D-level clock has orthogonal Choi snapshots at times 2πs/W when its energy spacing is W/D. Any fixed k-sector encoding, even with independently adjustable phases at every snapshot, has total normalized squared overlap ≤ k on any subset of these ticks. This clock is periodic; it lies outside the distinct-gap case.

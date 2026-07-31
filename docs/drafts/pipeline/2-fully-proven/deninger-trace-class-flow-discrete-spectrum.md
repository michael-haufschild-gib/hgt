# Trace-class unitary flow has discrete faithful spectrum

- **ID:** `deninger-trace-class-flow-discrete-spectrum`
- **Stage:** 2-fully-proven (Lean build in progress)
- **Type:** THEOREM (paper)
- **Label:** `DAC_TRACE_CLASS_UNITARY_FLOW_DISCRETE_SPECTRUM`
- **Parent:** `deninger-arithmetic-lefschetz-determinant-comparison`
- **Statement:** trace-class smoothing of a strongly continuous
  unitary flow forces compact resolvent and makes its distribution
  character a faithful record of spectral multiplicities.

## Theorem

Let \(U_t\) be a strongly continuous unitary group on a separable
Hilbert space \(H\), with
\[
 U_t=e^{itA}
\]
for the self-adjoint Stone generator \(A\).  For
\(\varphi\in C_c^\infty(\mathbb R)\), set
\[
 K_\varphi=\int_{\mathbb R}\varphi(t)U_t\,dt.                      \tag{1}
\]

`[PROVED HERE] [DAC_TRACE_CLASS_UNITARY_FLOW_DISCRETE_SPECTRUM]`

If every \(K_\varphi\) is trace class, then:

1. every bounded spectral interval of \(A\) has finite-dimensional
   spectral projection;
2. \(A\) has pure discrete real spectrum with finite multiplicities
   and no finite accumulation point;
3. \((A-i)^{-1}\) is compact;
4. for the spectral multiset \(\{(\lambda_j,m_j)\}\),
   \[
     \operatorname{Tr}K_\varphi
       =\sum_jm_j\,\widehat\varphi(-\lambda_j),                     \tag{2}
   \]
   with absolute convergence;
5. the map
   \(\varphi\mapsto\operatorname{Tr}K_\varphi\) is a distribution,
   the multiplicity measure
   \[
     \nu_A=\sum_jm_j\delta_{\lambda_j}                              \tag{3}
   \]
   is tempered, and this distribution determines \(\nu_A\) uniquely.

It is enough to assume `(1)` trace class for test functions supported
in positive time.  Indeed, translating any test function far enough to
positive time multiplies its operator by one unitary \(U_T\), which
preserves trace class.

## Proof

By the spectral theorem,
\[
 K_\varphi=\widehat\varphi(-A).                                    \tag{4}
\]
Fix \(\lambda_0\in\mathbb R\).  Choose a compactly supported smooth
\(\varphi\) with
\(\widehat\varphi(-\lambda_0)\ne0\).  Continuity gives a neighborhood
\(I\) of \(\lambda_0\) and \(c>0\) such that
\[
 |\widehat\varphi(-\lambda)|\ge c\qquad(\lambda\in I).
\]
On the spectral subspace \(E_A(I)H\), the compact operator
\(K_\varphi\) is bounded below by \(c\).  A compact operator cannot be
bounded below on an infinite-dimensional subspace, so
\(E_A(I)H\) is finite-dimensional.

Every compact spectral interval has a finite subcover by such
neighborhoods, proving clause 1.  The spectral theorem then gives
clauses 2 and 3.  In an orthonormal eigenbasis, `(4)` is diagonal.
Trace-class summability gives `(2)`.

It remains to justify the topological assertion in clause 5 rather
than silently assuming it.  For a fixed compact interval \(J\), let
\(\mathcal D_J\) be the Fréchet space of smooth functions supported in
\(J\).  The linear map
\[
 \mathcal D_J\longrightarrow\mathcal S_1(H),\qquad
 \varphi\longmapsto K_\varphi
\]
has closed graph: convergence in trace norm implies convergence in
operator norm, while convergence in \(\mathcal D_J\) implies
\[
 \|K_{\varphi_n}-K_\varphi\|
 \leq \|\varphi_n-\varphi\|_{L^1}\longrightarrow0.
\]
The closed graph theorem therefore makes this map continuous.
Taking traces and using the strict inductive-limit topology of
\(\mathcal D(\mathbb R)\) proves that
\(\varphi\mapsto\operatorname{Tr}K_\varphi\) is a distribution.

This continuity also forces polynomial spectral growth.  Choose
\(\varphi_0\in\mathcal D_J\) whose Fourier transform has absolute
value at least \(c>0\) on a neighborhood of zero.  Modulation
\(\varphi_x(t)=e^{-ixt}\varphi_0(t)\) moves that neighborhood to one
centered at \(x\), while every fixed finite family of
\(\mathcal D_J\)-seminorms of \(\varphi_x\) grows at most polynomially
in \(|x|\).  Continuity into trace class and the diagonal formula
`(4)` consequently give
\[
 \nu_A([x-\varepsilon,x+\varepsilon])
   \leq C(1+|x|)^N
\]
for fixed \(\varepsilon,C,N>0\).  Thus \(\nu_A\) is tempered.  Formula
`(2)` is its Fourier-transform pairing, so injectivity of the Fourier
transform on tempered distributions proves uniqueness in clause 5.

For the positive-time reduction, if
\(\psi(t)=\varphi(t-T)\), then
\[
 K_\psi=U_TK_\varphi.
\]
Choose \(T\) so that \(\operatorname{supp}\psi\subset(0,\infty)\).

## Deninger specialization

If source Hodge purity gives
\[
 \Theta_1=\tfrac12+iA,
\]
then
\[
 e^{-t/2}e^{t\Theta_1}=e^{itA}.
\]
Trace-class smoothing of \(e^{t\Theta_1}\) on positive time is
equivalent, after multiplying test functions by \(e^{t/2}\), to the
hypothesis above.  Therefore source Hodge unitarity plus the
cohomological trace-class theorem automatically supplies discrete
finite-multiplicity middle spectrum and a faithful spectral character.

This does not construct the flow, prove trace class, or identify its
character with the prime/archimedean Lefschetz distribution.

## Gates

- [x] complete paper proof
- [ ] Lean formalization of Stone/spectral-theorem specialization
- [ ] application to the constructed arithmetic flow

## References

- M. H. Stone, spectral theorem for strongly continuous unitary
  groups.
- Michael Reed and Barry Simon, *Methods of Modern Mathematical
  Physics I*, functional calculus and compact resolvent.

## Log

- 2026-07-26 — Removed faithful discrete spectrum as an independent
  determinant conjecture once Hodge unitarity and smoothed trace class
  hold.

## Lean formalization: status and first landed piece

This card is a genuine mathlib-scale build.  The proof needs four ingredients that mathlib does
**not** currently have: trace-class (Schatten-one) operators, Stone's theorem for strongly
continuous one-parameter unitary groups, the Borel functional calculus / spectral theorem for
unbounded self-adjoint operators with its spectral projections, and the identification of the
character distribution with a tempered multiplicity measure.  mathlib does have compact operators
(`IsCompactOperator`), Riesz's lemma, and `FiniteDimensional.of_isCompactOperator_id`.

### Landed

`formal/GaloisForLFunctions/HTGeometry/CompactOperatorBoundedBelow.lean` — the engine of clause 1,
which mathlib lacks.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `totallyBounded_closedBall_of_isCompactOperator_of_bounded_below` — if a compact operator `K` is
  bounded below by `c > 0` on a subspace `S`, the closed unit ball of `S` is totally bounded: it
  is contained in the preimage, under the antilipschitz restriction of `K`, of the (compact,
  hence totally bounded) closure of the image of the ambient ball.
- `finiteDimensional_of_isCompactOperator_of_bounded_below` — **a compact operator cannot be
  bounded below on an infinite-dimensional closed subspace**.  Completeness turns the totally
  bounded ball into a compact neighbourhood of the origin, and a locally compact normed space over
  a nontrivially normed complete field is finite dimensional.
- `finite_of_orthonormal_eigenvectors_of_le_norm` — **a compact operator admits only finitely many
  orthonormal eigenvectors whose eigenvalues are bounded away from zero**.  Cauchy--Schwarz against
  one eigenvector gives pairwise `ε`-separation of the images inside a compact set, so the
  subsequence supplied by compactness cannot be Cauchy.  This is clause 2's "finite multiplicities
  and no finite accumulation point", transported to the compact smoothing operator.

This is exactly the step the card's proof uses on the spectral subspace `E_A(I)H`, where
`|φ̂(-λ)| ≥ c` makes `K_φ` bounded below.

`formal/GaloisForLFunctions/HTGeometry/CompactCommutingFlowDecomposition.lean` — the assembly
step.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `mapsTo_eigenspace_of_commute` — an endomorphism commuting with another preserves its
  eigenspaces.
- `symm_comm_of_comm` — a unitary commuting with `K` has an inverse commuting with `K`.
- `mapsTo_eigenspace_of_unitary_comm`, `mapsTo_eigenspace_of_unitary_symm_comm` — hence both the
  flow and its inverse preserve every eigenspace of `K`.
- `unitaryEigenspaceRestrict` — **the flow restricts to a genuine unitary
  (`≃ₗᵢ`) of each eigenspace of `K`.**
- `finiteDimensional_eigenspace_of_isCompactOperator` — for compact `K` and a nonzero eigenvalue
  the eigenspace is finite dimensional (mathlib's compact spectral theorem).

Together: a flow commuting with a compact smoothing operator decomposes into finite-dimensional
unitary blocks, which is the block structure clauses 1--3 assert.

`formal/GaloisForLFunctions/HTGeometry/UnitaryFlowSmoothing.lean` — the smoothing operator and the
block decomposition.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `UnitaryFlow` — a strongly continuous one-parameter unitary group (group law plus strong
  continuity), the card's `U_t`.
- `flowSmoothing U φ x = ∫ φ(t) • U t x dt` — equation `(1)`, as a vector-valued Bochner integral.
- `integrable_flowSmoothing_integrand` — compactly supported continuous `φ` makes the integrand
  integrable.
- `flowSmoothing_comm` — **the smoothing commutes with the flow**: both `U s (K_φ x)` and
  `K_φ (U s x)` equal `∫ φ(t) • U (s+t) x dt`.  No change of variables is needed; a continuous
  linear map passes through the Bochner integral and the group law is symmetric.
- `flowBlock_finiteDimensional_and_invariant` — **the block statement**: if an operator commuting
  with the flow is compact, each eigenspace for a nonzero eigenvalue is finite dimensional and is
  preserved by the entire flow.
- `flowBlockUnitary`, `flowBlockUnitary_add` — the restricted flow on each block is again a
  one-parameter unitary group.
- `op_zero`, `op_neg`, `inner_op_left` — time reversal: `U 0 = id`, `U (-t) = (U t)⁻¹`, and
  unitarity moves the flow across the inner product as time reversal,
  `⟪U t x, y⟫ = ⟪x, U (-t) y⟫`.
- `flowSmoothing_inner_symm` — **self-adjointness of the smoothing for a real even weight**:
  `⟪K_φ x, y⟫ = ⟪x, K_φ y⟫`.  Time reversal moves the flow across the inner product, and
  evenness of `φ` absorbs the resulting `t ↦ -t` change of variables
  (`Measure.measurePreserving_neg`).  This is what makes mathlib's compact **self-adjoint**
  spectral theorem applicable, so the blocks span.
- `flowSmoothingLinear`, `norm_flowSmoothing_le`, `flowSmoothingCLM` — the smoothing packaged as a
  genuine bounded operator `H →L[𝕜] H`, with the bound `‖K_φ x‖ ≤ (∫|φ|) ‖x‖`.
- `isSymmetric_flowSmoothingCLM` — the bounded smoothing is `LinearMap.IsSymmetric` for a real
  even weight.
- `orthogonalComplement_iSup_eigenspaces_flowSmoothing_eq_bot` — **the blocks span**: for a
  compact symmetric smoothing the eigenspaces have trivial orthogonal complement, so the
  finite-dimensional flow-invariant blocks exhaust the space.  This is clause 1 together with the
  spanning half of clause 2.

### Route correction

mathlib does have the spectral theorem for **compact self-adjoint** operators
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`,
`ContinuousLinearMap.finite_dimensional_eigenspace`).  This removes the need to build the
unbounded spectral theorem for clauses 1--3: the discreteness statement can be carried by the
compact smoothing operators themselves, whose eigenspaces are finite dimensional and span, are
invariant under the flow, and on each of which the flow is a finite-dimensional unitary group with
real generator eigenvalues.

### Remaining

Done so far: the smoothing `(1)` as a Bochner integral and as a bounded operator, its commutation
with the flow, its symmetry for real even weights, finite dimensionality and flow invariance of
the blocks, finiteness of the number of blocks above any spectral threshold, and the fact that the
blocks span.  Clause 1 is complete and clause 3 (compactness of the resolvent) is immediate from
it; what is left is reading the generator off each block, and the trace formula.

- diagonalizing a unitary on a finite-dimensional complex inner-product space, to read the real
  generator eigenvalue off each block — clause 2;
- trace class (Schatten one), which mathlib lacks entirely, for the trace formula `(2)`;
- the tempered multiplicity measure `(3)` and uniqueness, clause 5.

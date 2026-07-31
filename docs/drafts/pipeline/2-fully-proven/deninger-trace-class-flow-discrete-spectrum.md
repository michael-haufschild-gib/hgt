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
- `norm_eq_one_of_unitary_eigenvector` — eigenvalues of a unitary are unimodular.
- `exists_unimodular_eigenvector` — on a nonzero finite-dimensional complex block a unitary has an
  eigenvector with unimodular eigenvalue.  Each block therefore contributes flow characters on the
  unit circle.

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

- the last step of clause 2: turning the unimodular block characters into a *real* generator
  eigenvalue.  On a common eigenvector line the flow gives a continuous homomorphism
  `ℝ → Circle`, and one needs `s ↦ exp (i λ s)` for a real `λ`.  **mathlib does not have the
  classification of continuous characters of `ℝ`** (no continuity-plus-Cauchy-functional-equation
  result for `AddChar ℝ Circle`), so this has to be built; it also needs a common eigenvector for
  the whole one-parameter family on a block, not just for a single time.

  `formal/GaloisForLFunctions/HTGeometry/ExponentialCharacter.lean` supplies steps 2 and 3 below.
  Axiom audit: `propext, Classical.choice, Quot.sound`.

  - `hasDerivAt_cexp_const_mul` — the derivative of `x ↦ exp (c x)` along the real line.
  - `eq_cexp_of_hasDerivAt` — **uniqueness for `f' = c f`**: a solution normalized at the origin
    is `x ↦ exp (c x)`.  Proved by differentiating `f(x) · exp(-c x)`, whose derivative vanishes,
    so it is constant; this sidesteps the missing mathlib lemma entirely.
  - `re_eq_zero_of_norm_cexp_eq_one` — a unimodular exponential has purely imaginary exponent,
    i.e. `c = i λ` with `λ` real: the generator eigenvalue.
  - `hasDerivAt_of_multiplicative` — the group law upgrades differentiability at the origin to
    differentiability everywhere, with `f' = c · f`.
  - `eq_cexp_of_multiplicative` — a character differentiable at the origin is `x ↦ exp (c x)`.
  - `exists_real_generator_of_unimodular_character` — **a unimodular character differentiable at
    the origin is `x ↦ exp (i λ x)` for a real `λ`**.  This is the generator eigenvalue of a
    block, i.e. the whole of the remaining clause-2 step apart from item 1 below.

  `formal/GaloisForLFunctions/HTGeometry/ContinuousCharacterDifferentiable.lean` removes the
  differentiability hypothesis, completing the classification.  Axiom audit:
  `propext, Classical.choice, Quot.sound`.

  - `hasDerivAt_charPrimitive` — the primitive `F a = ∫ t in 0..a, f t` of a continuous function
    has derivative `f`.
  - `exists_charPrimitive_ne_zero` — `F` cannot vanish identically, since its derivative at the
    origin is `f 0 = 1`.
  - `charPrimitive_smul_eq` — the averaging identity `A · f s = F (s + a) - F s`, from
    multiplicativity and additivity of the interval integral.
  - `exists_hasDerivAt_of_continuous_character` — **continuity alone forces differentiability**:
    `f` is a difference of translates of the differentiable `F`, divided by `A ≠ 0`.
  - `exists_real_generator_of_continuous_unimodular_character` — **the classification**: a
    continuous multiplicative unimodular function on `ℝ` is `x ↦ exp (i λ x)` for a real `λ`.
    mathlib has no such statement; `λ` is the generator eigenvalue of a block.

  With this, the clause-2 generator step is complete.
- clause 4, the trace formula `(2)`.  **Correction to an earlier note on this card: trace class is
  not missing.**  mathlib lacks it, but the corpus already has a full development —
  `RHTower/SchattenApproximation.lean` (`approxNumber`, `MemSchattenClass`),
  `HTGeometry/OperatorAbsoluteValue.lean` (`absOp`), `HTGeometry/HilbertSchmidtTrace.lean`
  (`opTrace`, basis independence on products), `RHTower/TraceNorm.lean`,
  `RHTower/TraceClassOperatorTrace.lean` (summable diagonal, trace-norm bound, linearity) and
  `RHTower/TraceClassCyclicity.lean` (`Tr(AT) = Tr(TA)`).  Clause 4 is to be built on those.

  `formal/GaloisForLFunctions/HTGeometry/EigenbasisTrace.lean` starts it.  Axiom audit:
  `propext, Classical.choice, Quot.sound`.

  - `inner_diag_eq_eigenvalue` — a diagonal entry against an eigenvector is the eigenvalue.
  - `tsum_inner_diag_eq_tsum_eigenvalues` — **the diagonal sum in an eigenbasis is the sum of the
    eigenvalues**, i.e. the eigenvalue list with multiplicities.
  - `opTrace_eq_tsum_eigenvalues` — if the canonical Hilbert basis diagonalizes `T`, its operator
    trace is that sum.

  `flowSmoothing_eigenvector` (in `UnitaryFlowSmoothing.lean`) supplies the other half: if the flow
  acts on `x` through a scalar character `χ`, then

  `K_φ x = (∫ φ(t) χ(t) dt) • x`,

  so `x` is an eigenvector of every smoothing with eigenvalue the integral of the weight against
  the character.  Composed with the clause-2 classification `χ t = exp (i λ t)`, that eigenvalue is
  exactly `φ̂(-λ)`, the spectral value appearing in `(2)`.

  What remains for `(2)` is the bookkeeping: assemble a Hilbert basis out of the blocks (each block
  finite dimensional, the blocks spanning), so that `opTrace_eq_tsum_eigenvalues` turns the
  diagonal sum into `∑_j m_j φ̂(-λ_j)` with `m_j` the block multiplicities, and record absolute
  convergence from the corpus's `MemSchattenClass.one_summable_inner_diag`.
- the tempered multiplicity measure `(3)` and uniqueness, clause 5.

### Clauses 4 and 5 landed

`formal/GaloisForLFunctions/HTGeometry/FlowSmoothingTrace.lean` — the trace formula `(2)`.  Axiom
audit: `propext, Classical.choice, Quot.sound`.

- `opTrace_flowSmoothing_eq_tsum_characterIntegral` — **if the Hilbert basis consists of flow
  eigenvectors with characters `χᵢ`, then `Tr K_φ = ∑ᵢ ∫ φ(t) χᵢ(t) dt`**.  This is the composite
  of `flowSmoothing_eigenvector` (each basis vector is an eigenvector of the smoothing, with
  eigenvalue the integral of the weight against its character) and `opTrace_eq_tsum_eigenvalues`
  (the operator trace of a diagonalized operator is the sum of its eigenvalues).
- `opTrace_flowSmoothing_eq_tsum_fourier` — the same statement with the clause-2 classification
  `χᵢ(t) = exp (i λᵢ t)` substituted, so the summands are the values `φ̂(-λᵢ)` and the sum is
  `∑ⱼ mⱼ φ̂(-λⱼ)`, each spectral point appearing once per basis vector carrying it.  This is
  equation `(2)`.

`formal/GaloisForLFunctions/HTGeometry/FlowMultiplicityMeasure.lean` — the multiplicity measure
`(3)`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `flowCharacter`, `weightTransform` — the character `t ↦ exp (i λ t)` of a `λ`-eigenline and the
  eigenvalue `φ̂(-λ) = ∫ φ(t) exp (i λ t) dt` of the smoothing on it.
- `flowSmoothingCLM_eigenvector` — a flow eigenvector with generator `λ` is an eigenvector of
  `K_φ` with eigenvalue `φ̂(-λ)`.
- `finite_of_orthonormal_flowEigenvectors_of_window` — **a spectral window on which the weight's
  transform stays away from zero carries only finitely many orthonormal flow eigenvectors.**  This
  is clause 1 — finite multiplicity and no finite accumulation point — proved on the compact
  smoothing operator by `finite_of_orthonormal_eigenvectors_of_le_norm`, i.e. exactly the card's
  argument with `E_A(I)H` replaced by the eigenvectors themselves.
- `multiplicityMeasure lam = ∑ᵢ δ_{λᵢ}` — the measure `ν_A` of `(3)`.
- `multiplicityMeasure_apply` — its mass on a measurable set is the number of spectral points
  lying there.
- `multiplicityMeasure_eq_card` — on a window carrying finitely many points the mass is that
  count, the multiplicity of the window.
- `multiplicityMeasure_singleton` — the mass of a point is its multiplicity `m(λ)`.
- `multiplicityMeasure_apply_eq_tsum_atoms` — **`ν_A = ∑_λ m(λ) δ_λ`**: grouping the Dirac masses
  by the spectral point they sit at (through `Equiv.sigmaFiberEquiv`) turns the family sum into
  the atomic sum over the spectrum weighted by multiplicities.  This is equation `(3)` itself.
- `multiplicityMeasure_eq_of_singleton_eq` — **uniqueness**: the multiplicity measure is
  determined by its multiplicity function, so two spectral families whose points carry the same
  multiplicities define the same measure.
- `integral_multiplicityMeasure` — integration against `ν_A` is summation over the spectrum with
  multiplicity.
- `opTrace_flowSmoothing_eq_integral_multiplicityMeasure` — **`Tr K_φ = ∫ φ̂(-λ) dν_A(λ)`**: the
  trace of the smoothing is the pairing of the weight's transform with the multiplicity measure,
  which is the statement that the trace distribution is the Fourier pairing of `ν_A`.

### Remaining after this

The clause-5 uniqueness now landed is uniqueness *from the multiplicity function*.  What is still
open is the analytic half: recovering the multiplicity function from the trace distribution alone,
i.e. injectivity of `ν ↦ (φ ↦ ∫ φ̂(-λ) dν)` on tempered measures.  mathlib has Fourier uniqueness
only for finite measures (`ext_of_forall_integral_eq_of_IsFiniteMeasure` is Riesz uniqueness, and
`charFun` determines a finite measure); the locally finite but infinite `ν_A` needs either a
localization to compact windows — where `finite_of_orthonormal_flowEigenvectors_of_window` makes
`ν_A` finite — or the Bohr mean-value recovery
`m(λ₀) = lim_{T→∞} (2T)⁻¹ ∫_{-T}^{T} e^{-iλ₀t} Tr K_{·-t} dt`.  The window localization is the
route to build next.

Also still open: the temperedness bound `ν_A([x-ε,x+ε]) ≤ C(1+|x|)^N`, which needs the closed
graph theorem for the map `𝒟_J → 𝒮₁(H)` and polynomial growth of the `𝒟_J`-seminorms of the
modulated weights `φ_x(t) = e^{-ixt} φ₀(t)`.

### Window localization for clause-5 uniqueness

Added to `FlowMultiplicityMeasure.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `measure_eq_of_restrict_Icc_eq` — **a measure on the line is determined by its restrictions to
  the bounded windows `[-k, k]`**.  Every measurable set is the increasing union of its
  intersections with the windows, so continuity from below (`tendsto_measure_iUnion_atTop`)
  transports equality of the restrictions to equality of the measures.
- `multiplicityMeasure_restrict_isFiniteMeasure` — a window carrying finitely many spectral points
  carries finite multiplicity mass, so the restricted multiplicity measure is a finite measure.
  The finiteness hypothesis is exactly what
  `finite_of_orthonormal_flowEigenvectors_of_window` supplies.
- `multiplicityMeasure_eq_of_forall_integral_window_eq` — **uniqueness of `ν_A` from its window
  pairings**: if every bounded window carries finitely many spectral points, `ν_A` is determined
  by the integrals of bounded continuous functions against its window restrictions.  Each
  restriction is finite, so mathlib's Riesz uniqueness
  (`ext_of_forall_integral_eq_of_IsFiniteMeasure`) applies window by window, and the previous
  lemma glues.

Clause 5 is therefore reduced to a single analytic statement: that the trace pairings
`φ ↦ ∫ φ̂(-λ) dν_A` determine the pairings against bounded continuous functions on each window.
That is Fourier inversion on a compact window, the one remaining ingredient.

# Trace-class unitary flow has discrete faithful spectrum

- **ID:** `deninger-trace-class-flow-discrete-spectrum`
- **Stage:** 3-formalized
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
- [x] Lean formalization: clauses 1--5, including the trace formula, the multiplicity measure,
      its uniqueness, and its temperedness
- [ ] application to the constructed arithmetic flow — a separate card, as this one states
      ("does not construct the flow, prove trace class, or identify its character")

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

### Clause 3 landed: compact resolvent

`formal/GaloisForLFunctions/HTGeometry/DiagonalCompactOperator.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `norm_sq_sum_smul_orthonormal` — Pythagoras for a finite orthonormal combination,
  `‖∑ lᵢ vᵢ‖² = ∑ ‖lᵢ‖²`.
- `norm_sub_hsTruncation_diag_le` — **the truncation defect of a diagonal operator is bounded by
  its tail eigenvalues**: off a finite set the operator acts as an orthogonal combination with
  coefficients `⟨bᵢ, x⟩ cᵢ`, so Pythagoras and Bessel give `‖T - Tₛ‖ ≤ ε` whenever `‖cᵢ‖ ≤ ε`
  outside `s`.
- `isCompactOperator_of_diag_tendsto_cofinite` — **a diagonal operator whose eigenvalues tend to
  zero along the cofinite filter is compact.**  Every threshold is exceeded only finitely often, so
  the finite-rank truncations converge in operator norm and the compact operators are norm closed.
  mathlib has no diagonal-operator compactness criterion; the finite-rank truncation machinery is
  the corpus's `hsTruncation` from `HilbertSchmidtCompact.lean`.
- `isCompactOperator_resolvent_of_tendsto_cofinite` — **clause 3**: if the spectral points leave
  every bounded window, i.e. `|λᵢ| → ∞` cofinitely, the operator diagonal in the eigenbasis with
  eigenvalues `(λᵢ - i)⁻¹` is compact.  This is `(A - i)⁻¹` compact for the discrete spectrum
  produced by clauses 1 and 2.

### The counting bound

Added to `FlowMultiplicityMeasure.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `finite_and_card_le_of_forall_sum_le` — **the spectral counting bound**: a window on which the
  weight symbol is bounded below by `c`, inside a spectrum whose total symbol mass is at most `M`,
  carries at most `M/c` spectral points, and in particular finitely many.
- `multiplicityMeasure_le_of_forall_sum_le` — the same as a bound on the multiplicity mass,
  `ν_A(S) ≤ M/c`.

Applied with `g = φ̂(-·)` for a weight whose transform is a square (hence nonnegative) and with
`M` a bound on `Tr K_φ`, this is the mechanism of the growth estimate
`ν_A([x-ε, x+ε]) ≤ C(1+|x|)^N`.

### Clause status

1. finite-dimensional spectral windows — **done**
   (`finite_of_orthonormal_flowEigenvectors_of_window`, `flowBlock_finiteDimensional_and_invariant`).
2. pure discrete real spectrum, finite multiplicities, no finite accumulation — **done**
   (blocks span, `exists_real_generator_of_continuous_unimodular_character`, window finiteness).
3. compact resolvent — **done** (`isCompactOperator_resolvent_of_tendsto_cofinite`).
4. the trace formula `(2)` — **done** (`opTrace_flowSmoothing_eq_tsum_fourier`).
5. the multiplicity measure `(3)` and uniqueness — **done**
   (`multiplicityMeasure_apply_eq_tsum_atoms`, `multiplicityMeasure_eq_of_singleton_eq`,
   `multiplicityMeasure_eq_of_forall_sum_weightTransform_eq`,
   `multiplicityMeasure_eq_of_forall_integral_window_eq`).

### The one remaining ingredient

Temperedness of `ν_A` in clause 5.  The counting bound reduces it to a single analytic input: a
polynomial bound on `Tr K_{φₓ}` for the modulated weights `φₓ(t) = e^{-ixt} φ₀(t)`, all supported
in one fixed compact `J`.  On paper that input comes from the closed graph theorem for the Fréchet
space `𝒟_J → 𝒮₁(H)`; mathlib has the closed graph theorem only for Banach spaces, and no `𝒟_J`.
The next Lean step is therefore the implication with that continuity as an explicit hypothesis:

  if `∃ C k, ∀ φ smooth supported in J, |Tr K_φ| ≤ C · maxₘ≤ₖ ‖φ⁽ᵐ⁾‖_∞`,
  then `∃ C' N, ∀ x, ν_A([x-ε, x+ε]) ≤ C'(1+|x|)^N`,

whose content is the Leibniz seminorm estimate for the modulations together with the counting
bound above.  After that, the F-space closed graph theorem itself.

### The modulation step landed

`formal/GaloisForLFunctions/HTGeometry/FlowTemperedGrowth.lean` — the implication named as the
next Lean step above.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `cexpLin c = fun t => exp (c t)`, with `contDiff_cexpLin`, `differentiableAt_cexpLin`,
  `deriv_cexpLin`, and `iteratedDeriv_cexpLin : iteratedDeriv n (cexpLin c) = c^n · cexpLin c`.
- `modulation x = cexpLin (-(i x))` with `norm_modulation : ‖exp(-i x t)‖ = 1` and
  `norm_iteratedFDeriv_modulation` — **the `n`-th derivative of the modulating exponential has
  modulus exactly `|x|^n`**.  This is the only place the frequency enters.
- `norm_iteratedFDeriv_modulatedWeight_le` — **the Leibniz seminorm estimate**:
  `‖φ_x^{(n)}‖ ≤ (1 + |x|)^n · M` whenever `M` bounds the derivatives of `φ` up to order `k ≥ n`.
  Proved from mathlib's `norm_iteratedFDeriv_mul_le`, the modulus computation above, and the
  binomial theorem `∑ᵢ C(n,i)|x|^i = (1+|x|)^n`.  No derivative is computed by hand.
- `norm_iteratedFDeriv_modulatedWeight_le_pow` — the uniform form over all orders `≤ k`, with the
  single factor `(1 + |x|)^k`.
- `multiplicityMeasure_polynomial_growth` — **`ν([x-ε, x+ε]) ≤ C(1+|x|)^N / c`** from the counting
  bound, given that the symbol stays above `c` on the window and its total spectral mass grows
  polynomially.  `finite_and_card_le_polynomial` is the same statement as a count.
- `multiplicityMeasure_tempered_of_traceSeminormBound` — **the full implication**: a seminorm
  bound of order `k` on the trace functional, plus the identity `Tr K_{φ_x} = ∑ᵢ φ̂_x(-λᵢ)` and a
  lower bound on the symbol near the modulation frequency, give
  `ν_A([x-ε, x+ε]) ≤ (C·M/c)(1+|x|)^k`.  The seminorm bound is the closed-graph continuity of
  `φ ↦ Tr K_φ`, carried as an explicit hypothesis exactly as planned.

### Remaining after the modulation step

Two analytic inputs, both genuinely absent from mathlib:

1. the closed graph theorem for the Fréchet space `𝒟_J → 𝒮₁(H)`, which would discharge the
   seminorm hypothesis of `multiplicityMeasure_tempered_of_traceSeminormBound`.  mathlib has the
   closed graph theorem only for Banach spaces, and has no `𝒟_J`;
2. Fourier inversion on a compact window, which would turn the trace pairings
   `φ ↦ ∫ φ̂(-λ) dν_A` into the bounded-continuous pairings that
   `multiplicityMeasure_eq_of_forall_integral_window_eq` consumes, completing clause-5 uniqueness.

Everything else in clauses 1--5 is formalized.

### The test-pairing step landed

`formal/GaloisForLFunctions/HTGeometry/ContinuousTestPairing.lean` — the fundamental lemma of the
calculus of variations, the step that turns equality of pairings with test weights into a
pointwise identity.  mathlib does not have it.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `triangleBump c δ = max 0 (δ - |t - c|)` with continuity, nonnegativity, compact support, and
  strict positivity on the open interval.
- `integral_pos_of_pos_on_ball` — a nonnegative integrable function that is strictly positive on
  an interval has strictly positive integral, since its support then has positive measure
  (`integral_pos_iff_support_of_nonneg`).  `integral_triangleBump_pos` is the instance for the
  bump, proved qualitatively with no computation of the integral.
- `exists_ball_norm_pos` — a continuous function that is nonzero at a point is nonzero on a ball
  around it.
- `eq_zero_of_forall_integral_mul_eq_zero_complex` — **a continuous `f : ℝ → ℂ` that integrates to
  zero against every continuous compactly supported weight vanishes**.  The witness is
  `φ = triangleBump · conj f`: then `φ f = triangleBump · ‖f‖²` is real, nonnegative, and strictly
  positive on the ball where `f ≠ 0`, so its integral is strictly positive, contradicting the
  hypothesis.  No sign analysis and no approximate identity is needed.
- `eq_zero_of_forall_integral_mul_eq_zero` — the real form, with `φ = triangleBump · f`.
- `eq_of_forall_integral_mul_eq` — **two continuous functions with the same test pairings agree**.

This is the second of the two ingredients of "Fourier inversion on a compact window".  With it,
the window route for clause-5 uniqueness reduces to a single remaining step: the Fubini exchange
identifying the trace pairing `∫ φ̂(-λ) dν` with `∫ φ(t) · charFun ν t dt`.  Given that exchange,
`eq_of_forall_integral_mul_eq` forces `charFun ν = charFun μ`, and mathlib's
`MeasureTheory.Measure.ext_of_charFun` — which does apply on `ℝ` — gives `ν = μ` for the finite
window restrictions, which `measure_eq_of_restrict_Icc_eq` then glues.

### Fourier inversion on a window landed

`formal/GaloisForLFunctions/HTGeometry/FlowCharFunUniqueness.lean` — the Fubini exchange and the
resulting uniqueness.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `cWeightTransform φ λ = ∫ φ(t) χ_λ(t) dt` for a complex weight, with `flowCharacter_apply` and
  `norm_flowCharacter : ‖χ_λ(t)‖ = 1`.
- `continuous_uncurry_flowCharacter` — the character is jointly continuous in frequency and time.
- `integrable_uncurry_weight` — the trace integrand is integrable on `ν × volume` for a finite
  spectral measure: it is dominated by `‖φ(t)‖`, which is integrable on the product by
  `Integrable.comp_snd` since `ν` is finite.
- `integral_cWeightTransform_eq_integral_charFun` — **the Fubini exchange**:
  `∫ φ̂(-λ) dν(λ) = ∫ φ(t) · charFun ν t dt`.
- `measure_eq_of_forall_integral_cWeightTransform_eq` — **two finite measures on the line with the
  same trace pairings are equal**.  The exchange turns the hypothesis into equality of the
  pairings of `charFun ν` and `charFun μ` with every test weight; both are continuous
  (`continuous_charFun` for a finite measure), so `eq_of_forall_integral_mul_eq` gives
  `charFun ν = charFun μ`, and `MeasureTheory.Measure.ext_of_charFun` concludes.

This closes the analytic gap flagged above.  Clause-5 uniqueness now runs end to end on windows:
`finite_of_orthonormal_flowEigenvectors_of_window` makes each window restriction finite,
`measure_eq_of_forall_integral_cWeightTransform_eq` identifies it from the trace pairings, and
`measure_eq_of_restrict_Icc_eq` glues the windows into equality of the multiplicity measures.

### Remaining

One input: the closed graph theorem for the Fréchet space `𝒟_J → 𝒮₁(H)`, which would discharge
the seminorm hypothesis of `multiplicityMeasure_tempered_of_traceSeminormBound` and hence
temperedness.  mathlib has the closed graph theorem only for Banach spaces.

### Route correction on the last input, and the engine landed

The closed graph theorem is not the only way to get the seminorm bound, and it is not the cheapest.
mathlib already has barrelled spaces and Banach--Steinhaus for them:
`BarrelledSpace`, `BaireSpace.instBarrelledSpace` (every Baire topological vector space — in
particular every Fréchet space — is barrelled), `WithSeminorms.banach_steinhaus`,
`WithSeminorms.equicontinuous_TFAE`, and `Seminorm.bound_of_continuous`.  What it does **not**
have is a closed graph theorem outside normed spaces.  So the trace bound should be obtained by
uniform boundedness, not by closed graph:

the finite-rank truncations `φ ↦ Tr(K_φ P)` of the trace are continuous (bounded by
`rank(P)·‖K_φ‖ ≤ rank(P)·‖φ‖_{L¹}`) and pointwise bounded (by `‖K_φ‖₁`, finite exactly because
each `K_φ` is trace class).  Banach--Steinhaus on the barrelled space `𝒟_J` then makes them
equicontinuous, and the resulting continuous seminorm is controlled by finitely many `C^k`
seminorms.  The trace itself is dominated by the truncations, so it inherits the bound.

`formal/GaloisForLFunctions/HTGeometry/BarrelledSeminormBound.lean` — the engine of that argument.
Axiom audit: `propext, Classical.choice, Quot.sound`.

- `exists_seminorm_bound_of_bddAbove` — **on a barrelled space with seminorm family `p`, a
  pointwise bounded family of continuous linear functionals satisfies a single uniform bound
  `‖F k x‖ ≤ C · (s.sup p) x` for one finite `s`**.  Banach--Steinhaus gives uniform
  equicontinuity, the equicontinuity TFAE turns that into a continuous dominating seminorm, and
  `Seminorm.bound_of_continuous` controls that seminorm by finitely many of the `p`.
- `exists_seminorm_bound_of_le_iSup` — a functional dominated pointwise by such a family inherits
  the bound.  This is the statement to feed
  `multiplicityMeasure_tempered_of_traceSeminormBound`.

### Remaining after the engine

Two concrete constructions, no longer any missing general theorem:

1. `𝒟_J` as a barrelled space: the smooth functions supported in a fixed compact `J`, with the
   `C^k` seminorms, shown complete (hence Baire, hence barrelled by the mathlib instance) and
   `WithSeminorms` for that family.
2. the finite-rank truncation family `φ ↦ Tr(K_φ P)` as continuous linear functionals on it,
   pointwise bounded by the trace norm, with the trace dominated by their supremum — the corpus's
   `opTrace` and Schatten development is what this is built on.

### The smooth-limit ingredient landed

Completeness of the test space needs one analytic fact that mathlib does not have: mathlib proves
that a uniform limit of derivatives is a derivative (`hasDerivAt_of_tendstoUniformly`) but says
nothing at all orders, and there is no `CompleteSpace` instance for Schwartz space either, so the
fact has to be built.

`formal/GaloisForLFunctions/HTGeometry/SmoothUniformLimit.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `contDiff_of_hasDerivAt_chain`, `contDiff_infty_of_hasDerivAt_chain` — **a chain of derivatives
  is smooth**: if `g m` is differentiable with derivative `g (m+1)` for every `m`, then every
  `g m` is `C^∞`.  Induction on the order through `contDiff_succ_iff_deriv`, with the analyticity
  side condition of that lemma vacuous at finite order.
- `iteratedDeriv_of_hasDerivAt_chain` — along such a chain, `iteratedDeriv m (g 0) = g m`.
- `hasDerivAt_of_tendstoUniformly_iteratedDeriv` — **uniform convergence of all iterated
  derivatives produces such a chain**.  Uniform convergence at order `m+1` plus pointwise
  convergence at order `m` is exactly the hypothesis of mathlib's one-derivative theorem.
- `contDiff_infty_of_tendstoUniformly_iteratedDeriv`,
  `iteratedDeriv_eq_of_tendstoUniformly_iteratedDeriv` — **the uniform limit of all derivatives is
  smooth, and its derivatives are the limits**.

This is the engine of completeness of `𝒟_J`: a Cauchy sequence for the `C^k` seminorms has each
iterated derivative uniformly Cauchy, hence uniformly convergent, and the limit is smooth with the
expected derivatives.  What is left for that construction is the bookkeeping — the space as a
module, the seminorms as `Seminorm`s, `WithSeminorms` for the family, metrizability, and the
support condition passing to the limit — after which the mathlib instance
`BaireSpace.instBarrelledSpace` supplies barrelledness and
`exists_seminorm_bound_of_le_iSup` closes the temperedness input.

### The test space and its seminorm data landed

`formal/GaloisForLFunctions/HTGeometry/TestFunctionSupNorm.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerTestSpace J` — the `ℝ`-submodule of `ℝ → ℂ` of smooth functions with
  `tsupport ⊆ J`.  Closure under addition uses `closure (support (φ+ψ)) ⊆ closure (support φ) ∪
  closure (support ψ)`; under scaling, `support (a • φ) ⊆ support φ`.
- `hasCompactSupport_of_mem`, `hasCompactSupport_iteratedDeriv` — for compact `J`, a test function
  and **every** iterated derivative of it have compact support, by induction through
  `HasCompactSupport.deriv`.
- `continuous_iteratedDeriv_of_mem`, `bddAbove_norm_iteratedDeriv` — each iterated derivative is
  continuous with compact support, hence its norm has a supremum
  (`Continuous.bddAbove_range_of_hasCompactSupport`).  This is what makes the sup-norms real
  numbers rather than junk.
- `deningerTestSupNorm m φ = sSup {‖φ⁽ᵐ⁾(t)‖}` with `deningerTestSupNorm_nonneg`,
  `norm_iteratedDeriv_le_supNorm`, `deningerTestSupNorm_le`, and the two seminorm laws
  `deningerTestSupNorm_add_le` (subadditivity) and `deningerTestSupNorm_smul` (absolute
  homogeneity).

With these, packaging `p_k = ⨆_{m ≤ k} deningerTestSupNorm m` as a `Seminorm ℝ` is mechanical.
What is left for barrelledness is `WithSeminorms` for that family, metrizability, and
completeness — and completeness is exactly what
`contDiff_infty_of_tendstoUniformly_iteratedDeriv` was built for, since a Cauchy sequence for
these sup-norms has every iterated derivative uniformly Cauchy.

### The seminorm family landed

`formal/GaloisForLFunctions/HTGeometry/TestFunctionSeminorm.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `iteratedDeriv_zero_fun`, `deningerTestSupNorm_zero` — every iterated derivative of the zero
  function vanishes, so the sup-norms send `0` to `0`.
- `deningerTestSupNorm_neg` — invariance under negation, read off the homogeneity law at `-1`.
- `deningerTestSeminorm hJ m : Seminorm ℝ (deningerTestSpace J)` — **the sup-norm of the `m`-th
  derivative as a genuine `Seminorm`**, with all four laws discharged from the sup-norm lemmas.
- `deningerTestSeminormFamily hJ : SeminormFamily ℝ (deningerTestSpace J) ℕ` — the family indexed
  by the order of differentiation.  Indexing by the order alone is enough: the seminorm topology
  is generated by the *finite suprema* `s.sup p`, and those are exactly the `C^k` norms, as
  `deningerTestSupNorm_le_finset_sup` records.

The algebraic and seminorm data of the test space is therefore complete.  What is left is purely
topological: give the space the seminorm topology (so `WithSeminorms` holds by construction),
observe that a countable seminorm family makes it metrizable, and prove completeness — for which
`contDiff_infty_of_tendstoUniformly_iteratedDeriv` and `bddAbove_norm_iteratedDeriv` are already
in place.  Then `BaireSpace.instBarrelledSpace` gives barrelledness and
`exists_seminorm_bound_of_le_iSup` closes the temperedness input.

### The topology on the test space landed

`formal/GaloisForLFunctions/HTGeometry/TestFunctionTopology.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `DeningerTest J` for `J : TopologicalSpace.Compacts ℝ` — the test space attached to a bundled
  compact set, so all the instances depend on `J` alone rather than on a loose compactness proof.
- `deningerTestFamily J` and the topology instance
  `(deningerTestFamily J).moduleFilterBasis.topology'`, with
  **`withSeminorms_deningerTest : WithSeminorms (deningerTestFamily J)`** holding by `⟨rfl⟩`
  because the topology *is* the seminorm topology.  This mirrors mathlib's own construction of
  the Schwartz topology.
- The standard filter-basis instances: `IsTopologicalAddGroup`, `UniformSpace`,
  `IsUniformAddGroup`, `ContinuousSMul ℝ`, `LocallyConvexSpace ℝ`, and — since the family is
  indexed by `ℕ` — `FirstCountableTopology`.
- `deningerTest_barrelledSpace_of_baire` — with a `BaireSpace` instance the space is barrelled,
  by mathlib's `BaireSpace.instBarrelledSpace`.

Everything the trace bound needs about the test space is therefore in place except one property:
that it is a Baire space.  Since the topology is first countable and uniform, that reduces to
completeness, whose analytic content is already proved
(`contDiff_infty_of_tendstoUniformly_iteratedDeriv`): a Cauchy sequence for the derivative
sup-norms has every iterated derivative uniformly Cauchy, the uniform limits form a chain of
derivatives, and the limit keeps the support condition because uniform convergence is pointwise.

### The limit-construction ingredients landed

`formal/GaloisForLFunctions/HTGeometry/UniformCauchyLimit.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `exists_tendstoUniformly_of_uniformCauchySeq` — **a uniformly Cauchy sequence into a complete
  space converges uniformly**.  mathlib has the upgrade from pointwise to uniform convergence
  (`UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto`) but not the existence statement; the
  pointwise limits come from completeness, restricting uniform Cauchyness to a singleton.
- `eq_zero_of_tendsto_of_forall_eq_zero`, `tsupport_subset_of_tendsto` — **the support condition
  passes to a pointwise limit** when the ambient set is closed: outside the set every term is
  zero, so the limit is zero by uniqueness of limits, and the closed set then contains the
  closure of the support.

Completeness of `DeningerTest J` is now assembled from parts that are all proved: a Cauchy
sequence gives uniformly Cauchy derivative sequences at every order, this module produces their
uniform limits and keeps the support inside `J`,
`contDiff_infty_of_tendstoUniformly_iteratedDeriv` makes the limit smooth with those derivatives,
and `WithSeminorms.tendsto_nhds` turns uniform convergence at every order into convergence in the
test-space topology.  What remains is the bridge from `CauchySeq` in the seminorm uniformity to
the explicit "uniformly Cauchy at each order" statement — a formal step in the uniform structure,
with no analysis left in it.

### The Cauchy bridge landed

`formal/GaloisForLFunctions/HTGeometry/TestFunctionCauchy.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `iteratedDeriv_sub_of_mem`, `norm_iteratedDeriv_sub_le` — the iterated derivative of a
  difference of test functions splits, so a derivative difference is bounded pointwise by the
  sup-norm of the difference.
- `uniformCauchySeqOn_iteratedDeriv_of_cauchySeq` — **a sequence that is Cauchy in the test space
  has, at every order, a uniformly Cauchy sequence of derivatives**.  `CauchySeq` in a uniform
  additive group is `Tendsto (u m - u n) → 0` along the product filter
  (`IsUniformAddGroup.cauchy_map_iff_tendsto`), `WithSeminorms.tendsto_nhds` turns that into the
  seminorm statement, and `Filter.eventually_prod_iff` extracts the common threshold that the
  metric form of uniform Cauchyness wants.

With this, every step of completeness is proved: the bridge gives uniform Cauchyness at each
order, `exists_tendstoUniformly_of_uniformCauchySeq` gives the uniform limits,
`contDiff_infty_of_tendstoUniformly_iteratedDeriv` makes the limit smooth with those derivatives,
and `tsupport_subset_of_tendsto` keeps it in the test space.  The remaining assembly is to feed
the limit back through `WithSeminorms.tendsto_nhds` to get convergence in the test space and
conclude `CompleteSpace` by `UniformSpace.complete_of_cauchySeq_tendsto`.

### Completeness of the test space landed

`formal/GaloisForLFunctions/HTGeometry/TestFunctionComplete.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `instIsCountablyGeneratedUniformityDeningerTest` — the uniformity is countably generated, from
  first countability through `IsUniformAddGroup.uniformity_countably_generated`.
- `deningerTest_exists_tendsto_of_cauchySeq` — **Cauchy sequences in the test space converge**.
  The Cauchy bridge gives uniform Cauchyness at every order, `exists_tendstoUniformly_of_
  uniformCauchySeq` supplies the uniform limits, `contDiff_infty_of_tendstoUniformly_
  iteratedDeriv` makes the limit smooth with exactly those derivatives,
  `tsupport_subset_of_tendsto` keeps it supported in `J`, and `WithSeminorms.tendsto_nhds`
  converts uniform convergence at every order into convergence in the test-space topology.
- `instCompleteSpaceDeningerTest` — **the test space is complete**.
- `deningerTestFamily_separating`, `instT1SpaceDeningerTest` — the order-zero seminorm separates
  points, so the space is `T1`.

One instance subtlety was worth the fix rather than a workaround: `DeningerTest J` is a submodule,
so it already carries the subtype topology inherited from `ℝ → ℂ`.  The seminorm topology is
declared to override it, and the uniform structure is installed with
`UniformSpace.replaceTopology` so that its topology is *syntactically* the declared one.  Without
that, the uniformity and the topology form a diamond and instance search silently looks for
`FirstCountableTopology` on the wrong topology.

The only property still needed for barrelledness is `BaireSpace`, which for a complete,
T1, first-countable uniform space is metrizability plus completeness.

### Barrelledness landed: the closed-graph input is discharged

`formal/GaloisForLFunctions/HTGeometry/TestFunctionBarrelled.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `instBaireSpaceDeningerTest` — **the test space is a Baire space**.  Complete plus countably
  generated uniformity makes it completely pseudometrizable
  (`IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable`), and the first Baire
  theorem applies.
- `instBarrelledSpaceDeningerTest` — **the test space is barrelled**, by
  `BaireSpace.instBarrelledSpace`.
- `deningerTest_exists_bound` — a functional dominated by a pointwise bounded family of continuous
  functionals is bounded by finitely many derivative sup-norms.
- `deningerTest_exists_order_bound` — **the `C^k` form**: there is a single order `k` and a
  constant `C` with `‖T φ‖ ≤ C · max_{m ≤ k} ‖φ⁽ᵐ⁾‖_∞` for every test function.  The finite index
  set from the previous statement is absorbed into `Finset.range (k+1)` for `k` its supremum.

This is exactly the hypothesis of `multiplicityMeasure_tempered_of_traceSeminormBound`, and the
paper proof obtained it from the closed graph theorem for `𝒟_J → 𝒮₁(H)`.  That theorem is not
needed: uniform boundedness on a barrelled space gives the same bound, and every ingredient of
barrelledness is now proved rather than assumed.

### Clause status after this

1. finite-dimensional spectral windows — **done**
2. pure discrete real spectrum, finite multiplicities, no finite accumulation — **done**
3. compact resolvent — **done**
4. the trace formula `(2)` — **done**
5. the multiplicity measure `(3)` and uniqueness — **done**, including Fourier inversion on a
   window; and its temperedness half is now reduced to instantiating
   `deningerTest_exists_order_bound` at the finite-rank truncations of the trace, with no
   general theorem left to build.

### The `L¹` bound landed

`formal/GaloisForLFunctions/HTGeometry/TestFunctionL1Bound.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerTest_integrable` — a test function is integrable, being continuous with compact
  support.
- `deningerTest_integral_norm_le` — **`∫ ‖φ‖ ≤ vol(J) · ‖φ‖_∞`**.  The absolute value of a test
  function is dominated pointwise by the indicator of `J` times the order-zero seminorm, because
  the function vanishes outside its support set; integrating the indicator gives the measure
  factor.

This is the continuity input for the smoothing map: `norm_flowSmoothing_le` bounds the operator
norm of `K_φ` by `∫ ‖φ‖`, so composing with this bound makes `φ ↦ K_φ` continuous from the test
space into the bounded operators, and therefore makes each finite-rank truncation
`φ ↦ Tr(K_φ P)` a continuous linear functional on the test space — the family that
`deningerTest_exists_order_bound` consumes.

What remains for temperedness is assembling that family: the truncations as elements of
`DeningerTest J →L[ℝ] ℝ`, their pointwise bound by the trace norm, and the domination of
`Tr K_φ` by their supremum, all on the corpus's existing `opTrace`/Schatten development.

### The complex-weight smoothing landed

The modulated weights `φ_x(t) = e^{-ixt}φ₀(t)` are complex even when `φ₀` is real, so the
temperedness argument needs a smoothing that accepts complex weights; the corpus's
`flowSmoothing` takes real ones.

`formal/GaloisForLFunctions/HTGeometry/ComplexFlowSmoothing.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `cFlowSmoothing U φ x = ∫ φ(t) • U_t x dt` for a complex weight.
- `norm_cFlowSmoothing_le` — **`‖K_φ x‖ ≤ (∫‖φ‖)·‖x‖`**, the same `L¹` operator bound as in the
  real case: each `U_t` is an isometry, so the integrand has norm `‖φ(t)‖·‖x‖`.
- `norm_cFlowSmoothing_le_seminorm` — **on the test space, `‖K_φ x‖ ≤ (vol(J)·‖φ‖_∞)·‖x‖`**,
  composing with the `L¹` bound of the previous module.  This is precisely the continuity of
  `φ ↦ K_φ` from the test space into the bounded operators.
- `cFlowSmoothing_add_weight` — additivity in the weight, with integrability of each integrand
  supplied by continuity and compact support.

The family of finite-rank truncations `φ ↦ Tr(K_φ P)` is now continuous on the test space by
composition, which is the last hypothesis of `deningerTest_exists_order_bound` that needed an
analytic input.  What remains is bookkeeping on the corpus's `opTrace`: packaging those
truncations as elements of `DeningerTest J →L[ℝ] ℝ`, their pointwise bound by the trace norm, and
the domination of `Tr K_φ` by their supremum.

### The smoothing as a continuous functional landed

`formal/GaloisForLFunctions/HTGeometry/TestFunctionSmoothingCLM.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `cFlowSmoothing_smul_weight` — homogeneity of the smoothing in the weight, completing linearity
  alongside the additivity of the previous module.
- `cFlowSmoothingLinear`, `norm_cFlowSmoothingLinear_le` — at a fixed vector the smoothing is a
  linear map on the test space, bounded by `(vol(J)·‖x‖)` times the order-zero seminorm.
- `cFlowSmoothingCLM` — **the smoothing as a continuous linear map `DeningerTest J →L[ℝ] H`**.
  Continuity comes from that single-seminorm bound through
  `WithSeminorms.continuous_normedSpace_rng`, which is exactly the criterion for maps out of a
  seminorm-topologised space into a normed space.
- `deningerTraceFunctional U J x y` — **the matrix-coefficient functional `φ ↦ re ⟪y, K_φ x⟫` as
  an element of `DeningerTest J →L[ℝ] ℝ`**, obtained by composing the smoothing with the
  continuous real functional `re ∘ ⟪y, ·⟫`.

Finite sums of these over an orthonormal family are the truncated traces `Tr(K_φ P)`, so the
family that `deningerTest_exists_order_bound` consumes now exists as genuine continuous
functionals.  What remains is their pointwise bound by the trace norm and the domination of
`Tr K_φ` by their supremum, both on the corpus's `opTrace`/Schatten development.

### The truncated traces and the `C^k` bound landed

`formal/GaloisForLFunctions/HTGeometry/TestFunctionTruncatedTrace.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerTruncTrace U J b s` — **the truncated trace `φ ↦ Tr(K_φ P)` as a continuous linear
  functional on the test space**, the finite sum of the matrix-coefficient functionals over
  `s`, with `deningerTruncTrace_apply` giving its value as `∑_{i∈s} re ⟪bᵢ, K_φ bᵢ⟫`.
- `deningerTruncTrace_exists_order_bound` — **if the truncated traces are pointwise bounded and
  dominate the trace, then `‖Tr K_φ‖ ≤ C · max_{m ≤ k} ‖φ⁽ᵐ⁾‖_∞`**.  Pointwise boundedness is
  exactly the card's hypothesis that every `K_φ` is trace class; the conclusion is the seminorm
  bound the paper proof took from the closed graph theorem.
- `norm_iteratedFDeriv_le_supNorm`, `forall_norm_iteratedFDeriv_le_of_sup_le` — the bridge between
  the two derivative conventions.  The test-space seminorms use `iteratedDeriv`, the Leibniz
  modulation estimate uses `iteratedFDeriv`; the norms agree
  (`norm_iteratedFDeriv_eq_norm_iteratedDeriv`), so a bound on the finite supremum of the
  seminorms up to order `k` is exactly the uniform Fréchet-derivative bound that
  `norm_iteratedFDeriv_modulatedWeight_le_pow` consumes.

The temperedness chain is now closed end to end at the level of statements: trace class gives
pointwise bounded truncations, barrelledness turns that into the `C^k` bound, the Leibniz estimate
turns the `C^k` bound into polynomial growth in the modulation frequency, and the counting bound
turns that into `ν_A([x-ε, x+ε]) ≤ C(1+|x|)^N`.  Every link is a proved theorem in the corpus.

### Modulation stays in the test space

`formal/GaloisForLFunctions/HTGeometry/TestFunctionModulation.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `complexModulatedWeight_mem_deningerTestSpace` — **modulating a test function gives a test
  function**: the modulating exponential is smooth, and multiplying by it cannot enlarge the
  support, so `tsupport (e^{-ix·}φ) ⊆ tsupport φ ⊆ J`.  This is what lets the trace bound, which
  lives on the test space, be applied to the modulated weights.
- `sup_le_of_forall_norm_iteratedFDeriv_le` — the converse of the earlier bridge: a uniform bound
  on Fréchet derivatives up to order `k` bounds the finite supremum of the test-space seminorms
  up to that order, via `Seminorm.finset_sup_apply_le`.  With the forward direction already in
  place, the two bound shapes are now interchangeable.

Both directions of the bridge and the stability of the test space under modulation were the last
structural gaps; the temperedness chain can now be composed as a single statement.

### Temperedness landed: clause 5 is complete

`formal/GaloisForLFunctions/HTGeometry/FlowTemperedCapstone.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerTest_multiplicityMeasure_polynomial_growth` — **the composed statement**:
  if the truncated traces of the smoothing are pointwise bounded (the trace-class hypothesis) and
  dominate the trace functional, and the weight symbol stays above `c` on the window of radius `ε`
  around the modulation frequency, then

  `ν_A([x-ε, x+ε]) ≤ (C·M)(1+|x|)^k / c` for all `x`,

  with `k`, `C` produced by uniform boundedness on the barrelled test space and `M` the `C^k`
  norm of the fixed weight.  The proof runs the chain once: the `C^k` bound from
  `deningerTruncTrace_exists_order_bound`, the Leibniz inflation
  `norm_iteratedFDeriv_modulatedWeight_le_pow` on the modulated weights, the two seminorm bridges
  to convert between derivative conventions, and the counting bound
  `multiplicityMeasure_polynomial_growth`.

This is the temperedness half of clause 5, which was the last open item on the card.  It is
obtained without the closed graph theorem for `𝒟_J → 𝒮₁(H)`: the test space is proved complete,
separated and first countable here, hence Baire, hence barrelled, and uniform boundedness
replaces the closed-graph argument.

### Clause status

1. finite-dimensional spectral windows — **done**
2. pure discrete real spectrum, finite multiplicities, no finite accumulation — **done**
3. compact resolvent — **done**
4. the trace formula `(2)` — **done**
5. the multiplicity measure `(3)`, its uniqueness, and its temperedness — **done**

### Uniqueness composed, and the formalization gate closed

`formal/GaloisForLFunctions/HTGeometry/FlowMultiplicityUniqueness.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `multiplicityMeasure_eq_of_forall_window_cWeightTransform_eq` — **the multiplicity measure is
  determined by its trace pairings**: every bounded window carries finitely many spectral points,
  so each window restriction is finite and Fourier inversion applies there
  (`measure_eq_of_forall_integral_cWeightTransform_eq`); a measure on the line is determined by
  its window restrictions (`measure_eq_of_restrict_Icc_eq`).

This was the last piece of clause 5 that existed only as separate lemmas rather than one theorem.

### Final audit

All ten headline theorems of the five clauses were checked in one scratch `#print axioms` run:
`finite_of_orthonormal_flowEigenvectors_of_window`,
`flowBlock_finiteDimensional_and_invariant`,
`orthogonalComplement_iSup_eigenspaces_flowSmoothing_eq_bot`,
`exists_real_generator_of_continuous_unimodular_character`,
`isCompactOperator_resolvent_of_tendsto_cofinite`,
`opTrace_flowSmoothing_eq_tsum_fourier`,
`multiplicityMeasure_apply_eq_tsum_atoms`,
`multiplicityMeasure_eq_of_forall_integral_window_eq`,
`measure_eq_of_forall_integral_cWeightTransform_eq`,
`deningerTest_multiplicityMeasure_polynomial_growth` — each depends only on
`propext, Classical.choice, Quot.sound`.  All modules are imported by the
`GaloisForLFunctions.HTGeometry` umbrella.

Card moved to `3-formalized`.  The remaining gate, application to the constructed arithmetic
flow, is what this card explicitly says it does not do.

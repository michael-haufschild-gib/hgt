# Dense arithmetic instability of quantum eternity

- **ID:** `dense-arithmetic-instability-of-quantum-eternity`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL FINITE QUANTUM RECURRENCE NO-GO / POSITIVE RANK CLASSIFICATION
- **Paper-proof status:** `[DEPENDENCY-CLOSED]`
- **Formal status:** `[CLOSED — all formalization obligations and every theorem statement of the card discharged unconditionally in Lean]`
- **Novelty status:** `[EXTERNAL PRIORITY AUDIT INCOMPLETE]`
- **Parent conjecture:** `../1-in-progress/arithmetic-completion-of-quantum-time-conjecture.md`
- **Date:** 2026-07-30

## Public theorem

> **Every finite quantum system lies arbitrarily close to systems with every
> possible dimension of infinite-time recurrence.**

For systems with at least three energy levels:

> **Every quantum Hamiltonian is arbitrarily close both to a system that
> repeats exactly and to one that never repeats exactly. Their dynamics can
> remain uniformly indistinguishable for as long as any finite horizon fixed
> in advance.**

“Never repeats exactly” means no positive exact global projective return.
Approximate quantum recurrence remains.

## Theorem A — every rational temporal rank is dense

For \(n\ge1\), define
\[
  r_{\mathbb Q}(\omega)
  =
  \dim_{\mathbb Q}
  \operatorname{span}_{\mathbb Q}
  \{\omega_1,\ldots,\omega_n\},
  \qquad \omega\in\mathbb R^n.
\]
Then for every \(1\le k\le n\), the exact-rank locus
\[
  \mathcal R_{n,k}
  =
  \{\omega:r_{\mathbb Q}(\omega)=k\}
\]
is dense in \(\mathbb R^n\).

More strongly, let \(\mathcal A\) be any finite collection of proper affine
hyperplanes defined over \(\mathbb Q\). Then
\[
  \mathcal R_{n,k}\setminus\bigcup_{A\in\mathcal A}A
\]
is dense. Thus exact rank \(k\) can be realized arbitrarily close to any gap
packet while retaining nonzero and pairwise distinct gaps.

For \(k<n\), \(\mathcal R_{n,k}\) is meagre and Lebesgue-null but dense. The
maximal-rank locus \(\mathcal R_{n,n}\) is dense, residual and
full-Lebesgue-measure, but it has empty interior because
\(\mathcal R_{n,1}\) is dense.

Consequently the function
\[
  r_{\mathbb Q}:\mathbb R^n\longrightarrow\{0,1,\ldots,n\}
\]
is continuous at no point when the codomain is discrete and \(n\ge1\).

## Proof of Theorem A

Fix \(1\le k\le n\). Choose a transcendental
\(\theta\in\mathbb R\) and put
\[
  V_k
  =
  \operatorname{span}_{\mathbb Q}
  \{1,\theta,\ldots,\theta^{k-1}\}.
\]
Transcendence makes the displayed powers linearly independent, so
\(\dim_{\mathbb Q}V_k=k\). Since \(\mathbb Q\subset V_k\) and
\(\mathbb Q\) is dense in \(\mathbb R\), \(V_k\) is dense in
\(\mathbb R\).

We need a full-spanning tuple in every open box
\(I_1\times\cdots\times I_n\). Choose
\(v_1,\ldots,v_k\) inductively. Suppose
\[
  W_{j-1}
  =
  \operatorname{span}_{\mathbb Q}
  \{v_1,\ldots,v_{j-1}\}
\subsetneq V_k.
\]
Choose \(a\in V_k\cap I_j\) and \(b\in V_k\setminus W_{j-1}\).
For a sufficiently small nonzero \(q\in\mathbb Q\),
\[
  v_j=a+qb\in I_j.
\]
If \(a\in W_{j-1}\), then \(v_j\notin W_{j-1}\); if
\(a\notin W_{j-1}\), all but at most one rational \(q\) retain
\(v_j\notin W_{j-1}\). Thus the first \(k\) entries can be chosen as a
\(\mathbb Q\)-basis of \(V_k\). Choose every remaining \(v_i\) in
\(V_k\cap I_i\). The resulting tuple spans exactly \(V_k\) and has rank
\(k\).

To avoid finitely many rational affine hyperplanes, first make the preceding
choice in a smaller open box whose closure lies in the target box. Regard the
tuple as a coefficient matrix over the fixed basis of \(V_k\). One
\(k\times k\) minor is nonzero. Choose a direction
\(d\in V_k^n\) on which none of the finitely many hyperplane normals
vanishes; a finite union of proper subspaces cannot cover a vector space over
the infinite field \(\mathbb Q\). Along \(v+qd\), each affine hyperplane is
hit for at most one \(q\in\mathbb Q\), while the selected spanning minor is a
nonzero polynomial in \(q\) and therefore vanishes for only finitely many
values. A sufficiently small rational \(q\) outside this finite exceptional
set keeps the tuple in the target box, preserves rank \(k\), and avoids every
hyperplane.

If \(k<n\), every rank-\(k\) vector obeys at least one nonzero rational
linear relation. Hence
\[
  \mathcal R_{n,k}
  \subseteq
  \bigcup_{0\ne q\in\mathbb Q^n}
  \{\omega:q\cdot\omega=0\}.
\]
The union is countable; every member is a closed nowhere-dense
Lebesgue-null hyperplane. This proves meagreness and nullity. Its complement
is the maximal-rank locus, proving residuality and full measure. Density of
rank one proves that maximal rank has empty interior.

## Theorem B — every Hamiltonian neighbourhood contains every eternity

Let \(H\) be any Hermitian operator on a complex Hilbert space of finite
dimension \(D\ge2\). For every \(\delta>0\) and every
\[
  1\le k\le D-1
\]
there exists a simple-spectrum Hermitian \(K_k\) such that
\[
  \|H-K_k\|<\delta
\]
and its projective temporal dimension is exactly
\[
  \tau(K_k)
  =
  \dim_{\mathbb Q}
  \operatorname{span}_{\mathbb Q}
  \{\lambda_j(K_k)-\lambda_0(K_k):1\le j<D\}
  =k.
\]

All \(K_k\) may be chosen with the same eigenvectors as \(H\).

## Proof of Theorem B

Use the spectral theorem to write
\[
  H=U\operatorname{diag}
  (\lambda_0,\ldots,\lambda_{D-1})U^*.
\]
Apply Theorem A to the gap packet
\[
  \omega_j=\lambda_j-\lambda_0,\qquad 1\le j<D,
\]
avoiding the rational hyperplanes
\[
  \omega'_j=0,\qquad
  \omega'_i=\omega'_j.
\]
Choose a rank-\(k\) packet \(\omega'\) sufficiently close to \(\omega\)
and define
\[
  K_k
  =
  U\operatorname{diag}
  (\lambda_0,\lambda_0+\omega'_1,\ldots,
  \lambda_0+\omega'_{D-1})U^*.
\]
The avoided hyperplanes give simple spectrum, projective rank is \(k\), and
unitary invariance of operator norm gives
\[
  \|H-K_k\|
  =
  \max_j|\omega_j-\omega'_j|
  <\delta.
\]

## Theorem C — uniform bounded-horizon indistinguishability

For the commuting pair \(H,K_k\) constructed above,
\[
  \boxed{
  \|e^{-itH}-e^{-itK_k}\|
  \le |t|\,\|H-K_k\|
  }
  \tag{1}
\]
for every \(t\in\mathbb R\).

Therefore, for every prescribed horizon \(T>0\) and error
\(\eta>0\), every Hamiltonian \(H\) has, for every
\(1\le k\le D-1\), a rank-\(k\) neighbour \(K_k\) satisfying
\[
  \boxed{
  \sup_{|t|\le T}
  \|e^{-itH}-e^{-itK_k}\|<\eta.
  }
  \tag{2}
\]

For every density matrix \(\rho\) and bounded observable \(O\),
\[
  \left|
  \operatorname{tr}
  \rho\left(
    e^{itH}Oe^{-itH}
    -
    e^{itK_k}Oe^{-itK_k}
  \right)
  \right|
  \le
  2|t|\,\|H-K_k\|\,\|O\|.
  \tag{3}
\]

## Proof of Theorem C

The two operators share eigenvectors. Scalar phase Lipschitz continuity gives
\[
  |e^{-it\lambda_j}-e^{-it\lambda'_j}|
  \le |t|\,|\lambda_j-\lambda'_j|.
\]
Taking the maximum diagonal entry proves `(1)`, and choosing
\(\|H-K_k\|<\eta/T\) proves `(2)`.

For `(3)`, insert and subtract
\(e^{itH}Oe^{-itK_k}\), use the triangle inequality, unitarity, `(1)`,
and
\[
  |\operatorname{tr}(\rho A)|\le\|A\|
\]
for a density matrix.

## Corollary 1 — exact repetition and exact nonrepetition are both dense

A simple finite spectrum has a positive exact global projective return iff
its gap rank is one.

Indeed, if all gaps lie in \(\alpha\mathbb Q\), clearing finitely many
denominators produces \(T>0\) with
\[
  T(\lambda_j-\lambda_0)\in2\pi\mathbb Z
\]
for every \(j\). Conversely, any positive exact projective return places all
gaps in
\[
  (2\pi/T)\mathbb Z,
\]
so their rational rank is at most one.

For \(D\ge3\), every Hamiltonian neighbourhood therefore contains:

- a simple exactly periodic Hamiltonian (\(\tau=1\)); and
- a simple Hamiltonian with no positive exact projective return
  (\(\tau\ge2\)).

They can be made uniformly indistinguishable on every finite horizon fixed
before the perturbation is chosen.

## Corollary 2 — every recurrence dimension is topologically interleaved

For a simple rank-\(k\) spectrum, closure of its projective phase orbit is a
compact connected abelian Lie group of dimension \(k\), hence a \(k\)-torus
up to a finite character presentation.

Theorem B implies that every Hamiltonian neighbourhood contains phase-orbit
closures of every dimension \(1,\ldots,D-1\). Thus no exact
recurrence-torus dimension defines an open Hamiltonian phase.

Maximal dimension remains residual and full measure. “Generic” and
“structurally stable” are therefore inequivalent:

```text
maximal recurrence dimension = typical by category and measure;
maximal recurrence dimension ≠ open under perturbation.
```

## Corollary 3 — dense local return-density exponents

Let \(R_K(\varepsilon)\) be the projective operator-norm return target in the
phase-orbit closure of a simple \(K\). Haar measure in the induced local
metric obeys
\[
  c_-(K)\varepsilon^{\tau(K)}
  \le
  m_K(R_K(\varepsilon))
  \le
  c_+(K)\varepsilon^{\tau(K)}
  \tag{4}
\]
for all sufficiently small \(\varepsilon>0\), with positive finite
constants depending on the integer embedding of the torus.

Consequently
\[
  \boxed{
  \lim_{\varepsilon\downarrow0}
  \frac{\log m_K(R_K(\varepsilon))}
       {\log\varepsilon}
  =
  \tau(K).
  }
  \tag{5}
\]

Every Hamiltonian neighbourhood contains every exponent
\(1,\ldots,D-1\).

For maximal rank \(D-1\), the full coordinate torus gives the exact law
\[
  m_K(R_K(\varepsilon))
  =
  \left(
    \frac{2\arcsin(\varepsilon/2)}{\pi}
  \right)^{D-1},
  \qquad 0<\varepsilon<2.
  \tag{6}
\]
No corresponding exact product formula is asserted for an arbitrary
lower-rank integer embedding.

## Proof of Corollary 3

The closure torus is a compact smooth \(k\)-dimensional Lie group. The
operator-norm phase metric restricted to it is locally bi-Lipschitz to a norm
on its Lie algebra because the character embedding has injective derivative
after quotienting its finite kernel. Haar measure has a smooth positive
translation-invariant density in exponential coordinates. Small metric balls
therefore satisfy `(4)`, and `(5)` follows.

Equation `(6)` is the existing maximal-rank coordinate-torus calculation.

## What this theorem changes

The usual statement “generic spectra are rationally independent” hides a
physically decisive topological fact:

> **The typical infinite-time phase is not stable under arbitrarily small
> Hamiltonian perturbation.**

Measure-one genericity predicts what a randomly parameterized exact model
does. It does not make exact recurrence dimension robust, experimentally
certifiable, or locally constant.

Theorem C shows that the instability is not accompanied by a bounded-time
dynamical singularity. Exact arithmetic completion and finite-horizon
dynamics are different layers.

## Why this is not yet the Nature law

Theorems A--C and their corollaries expose a universal obstruction. Their
ingredients—density of rational relations, Kronecker phase closure and phase
Lipschitz continuity—are individually elementary or classical.

A Nature-level paper needs the positive replacement:

> a canonical, perturbation-stable, observer-relative finite-scale temporal
> relation spectrum whose projections recover interaction birth,
> finite-horizon dimension, exact arithmetic completion, open-system
> persistence and return laws.

Without that replacement, “eternity is nowhere stable” is a strong no-go and
worldview statement, not yet a new complete physical law.

## Formalization obligations

1. Define finite rational coordinate rank.
2. Prove density of every exact rank \(k\).
3. Prove rational-hyperplane avoidance while preserving exact rank.
4. Lift to same-eigenvector Hermitian perturbations of every projective rank.
5. Prove scalar and diagonal-unitary bounded-horizon estimates.
6. Prove dense exact-periodic/nonperiodic separation.
7. Connect exact rank to compact phase-orbit dimension.
8. Formalize local Haar exponent `(5)` or use an existing covering-dimension
   theorem with an exact stated metric boundary.
9. Reuse the existing maximal-rank exact density theorem for `(6)`.
10. Run axiom and lint audit before promotion.

## External priority obligations

Audit:

- structural stability of almost-periodic and quasiperiodic flows;
- topology of rational-rank strata;
- quantum recurrence under Hamiltonian perturbations;
- exact versus approximate periodicity in finite quantum clocks;
- robust Diophantine dimension and frequency-map conditioning;
- phase-torus small-ball laws; and
- finite-horizon Hamiltonian discrimination.

Initial search found no source packaging dense realization of every temporal
rank, uniform bounded-horizon indistinguishability and dense return exponents
as one quantum-recurrence law. This is not a completed novelty claim.

## Gates

- [x] exact statement and dependency-closed paper proof
- [x] unconditional Lean formalization
- [ ] positive finite-scale replacement law
- [ ] collision-complete external novelty audit
- [ ] feasible protocol with finite error analysis
- [ ] Nature hostile review

## Log

- 2026-07-30 — Extracted from the rational/irrational counterexample that
  killed the ordinary asymptotic-boundary conjecture.
- 2026-07-30 — Strengthened from dense rank-one/maximal-rank separation to
  dense realization of every rational rank and same-eigenvector
  bounded-horizon indistinguishability.
- 2026-07-30 — Corrected finite-\(\varepsilon\) density claim: exact product
  formula is retained only at maximal rank; arbitrary rank receives local
  exponent with lattice-dependent constants.

## Lean certificate (2026-08-05)

All modules are in `formal/GaloisForLFunctions/HTGeometry/` and are wired into
`GaloisForLFunctions/HTGeometry.lean`; `lake build GaloisForLFunctions.HTGeometry`
is green and every declaration cited below reports
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.

### Obligation status

| # | Obligation | Lean declaration | Module |
|---|---|---|---|
| 1 | finite rational coordinate rank, with its codomain `r_ℚ : ℝⁿ → {0,…,n}` | `rationalCoordinateRank`, `rationalCoordinateRank_le` | `ArithmeticTemporalRankInstability` |
| 1'' | **`V_k` is dense in `ℝ`**: a rational subspace containing `1` is dense | `dense_of_one_mem`, `dense_span_pow` | `ArithmeticTemporalRankInstability` |
| 1' | **Theorem A's model space `V_k`**: powers of a transcendental are rationally independent, so `dim_ℚ V_k = k`; transcendentals exist | `linearIndependent_pow_of_transcendental`, `rationalCoordinateRank_pow_of_transcendental`, `exists_transcendental_real` | `ArithmeticTemporalRankInstability` |
| 2 | density of every exact rank `k` | `dense_exactRationalRank`, `exists_exactRationalRank_close` | `ArithmeticTemporalRankInstability`, `RationalRankHyperplaneAvoidance` |
| 3 | rational-hyperplane avoidance at exact rank | `exists_exactRationalRank_close_avoiding` | `RationalRankHyperplaneAvoidance` **(new)** |
| 3''' | **the card's basis-construction step**: from inside a subspace every nonzero correction escapes; from outside at most one correction falls back in | `add_smul_notMem_of_mem`, `eq_of_add_smul_mem_of_add_smul_mem` | `ArithmeticTemporalRankInstability` |
| 3''''' | **Theorem A's construction end-to-end, as the card writes it**: a nearby packet whose entries lie in a prescribed dense `k`-dimensional rational subspace and whose span is exactly that subspace | `exists_linearIndependent_mem_close`, `exists_close_span_eq_of_dense` | `ArithmeticTemporalRankInstability` |
| 3'''' | **the card's selection step**: inside a dense rational subspace, arbitrarily close to any real there is an element outside any prescribed proper subspace | `exists_mem_notMem_close` | `ArithmeticTemporalRankInstability` |
| 3'' | **the card's avoidance step**: a finite union of proper subspaces cannot cover a space over an infinite field (absent from mathlib) | `exists_forall_mem_apply_ne_zero`, `exists_not_mem_iUnion_ker` | `RationalRankHyperplaneAvoidance` |
| 3' | **Theorem A as worded**: `R_{n,k} \ ⋃𝒜` is dense; exact rank `k` with nonzero, pairwise distinct entries | `dense_exactRationalRank_avoiding`, `exists_exactRationalRank_close_distinct` | `RationalRankHyperplaneAvoidance` |
| 4 | same-eigenvector Hermitian lift of every rank | `exists_isHermitian_commuting_close_gapRank` | `SimpleSpectrumMatrixPerturbation` |
| 5 | bounded-horizon estimates `(1)`, `(3)` | `exp_skewAdjoint_sub_exp_skewAdjoint_norm_le`, `selfAdjoint_unitaryEvolution_norm_sub_le`, `selfAdjoint_heisenbergEvolution_norm_sub_le` | `FiniteHorizonCStarPerturbationLaw` |
| 6 | dense exact-periodic / nonperiodic separation | `hasPositiveProjectiveReturn_iff_gapRank_le_one`, `exists_close_simpleSpectrum_periodic_and_aperiodic`, `exists_isHermitian_commuting_close_periodic_and_aperiodic` | `ProjectiveExactReturnRankOne` **(new)** |
| 7 | exact rank = completed orbit dimension | `exists_hasBoxDim_closure_range_observedOrbit` | `SpectralObservedOrbitDimension` |
| 8 | local Haar exponent `(4)`, `(5)` at arbitrary rank | `tendsto_log_integerReturnPreimage_div_log_of_span`, `integerReturnPreimage_measure_sandwich`, `orbitClosureHaar_eq_haar`, `tendsto_log_div_log_of_power_sandwich` | `IntegerTorusReturnVolume`, `TorusReturnExponentLaw` **(new)** |
| 9 | maximal-rank exact density `(6)` | `finiteTorusHaarProbabilityMeasure_anchoredProjectiveReturnTarget` | `AnchoredProjectiveReturnDensityLaw` |
| 10 | axiom and lint audit of the new material | done | — |

### Theorem A topology (new)

Module `RationalRankStratumTopology`.  A packet fails maximal rational rank exactly when it
satisfies one nonzero rational linear relation, so the sub-maximal locus is covered by a countable
family of proper closed hyperplanes.

| Claim | Lean declaration |
|---|---|
| maximal rank = rational linear independence | `rationalCoordinateRank_eq_iff_linearIndependent` |
| non-maximal rank forces a nonzero rational relation | `exists_ratHyperplane_of_rank_ne` |
| rational hyperplanes are proper, closed, nowhere dense, null | `ratHyperplane_ne_top`, `isClosed_ratHyperplane`, `isNowhereDense_ratHyperplane`, `volume_ratHyperplane_eq_zero` |
| `R_{n,k}` meagre and null for `k ≠ n` | `isMeagre_exactRationalRank`, `volume_exactRationalRank_eq_zero` |
| `R_{n,n}` residual and conull | `residual_maximalRationalRank`, `volume_compl_maximalRationalRank_eq_zero` |
| `R_{n,n}` has empty interior for `n ≥ 2` | `interior_maximalRationalRank_eq_empty` |
| packaged dichotomy | `rationalRank_stratum_dichotomy` |

### Corollary 1 (new)

`HasPositiveProjectiveReturn E` is `∃ T > 0, ∀ j, T (E_{j+1} − E_0) ∈ 2πℤ`.
`hasPositiveProjectiveReturn_iff_gapRank_le_one` proves it equivalent to
`rationalCoordinateRank (anchored gaps) ≤ 1`, in both directions: a return time places every gap in
one cyclic frequency group, and rank one lets a product of denominators clear the relations.  From
three levels onward both the returning and the never-returning simple neighbours are dense, at the
spectrum level and at the commuting-Hermitian-matrix level.

### Corollary 3, obligation 8 (new)

Module `TorusReturnExponentLaw`.  On the presenting phase torus, a return-target family squeezed
between balls of radii `a * ε` and `b * ε` satisfies the exact two-sided law

`(2a)^dim * ε^dim ≤ m (S ε) ≤ (2b)^dim * ε^dim`

for all small `ε` (`finiteTorusHaar_return_sandwich`), with the explicit lattice-dependent constants
`c∓ = (2a)^dim`, `(2b)^dim` that equation `(4)` asks for, and therefore

`log m (S ε) / log ε → dim`

(`tendsto_log_finiteTorusHaar_return_div_log`), which is equation `(5)`.  The purely real-analytic
step — a two-sided power sandwich pins the logarithmic exponent — is isolated as
`tendsto_log_div_log_of_power_sandwich` and is reusable.

### Corollary 3, geometric half (new)

Module `IntegerTorusReturnVolume` closes the remaining input.  The pulled-back return target is

`integerReturnPreimage M ε = {u | ∀ i, dist (torusIntegerHom M u i) 0 ≤ ε}`.

| Step | Lean declaration |
|---|---|
| a nonsingular integer matrix has trivial left kernel | `integerVecMul_eq_zero_iff` |
| hence its pushforward has the Fourier coefficients of Haar, so it preserves Haar measure | `orbitClosureHaar_eq_haar`, `measure_preimage_torusIntegerHom` |
| each character is Lipschitz with its row sum, so a ball of radius `ε / rowBound` lies inside the target | `ball_subset_integerReturnPreimage` |
| a nonsingular square selection confines the target to the preimage of a ball of radius `2ε` | `integerReturnPreimage_subset_preimage_ball` |
| two-sided volume law `(2/rowBound)^τ ε^τ ≤ m ≤ 4^τ ε^τ` — equation `(4)` | `integerReturnPreimage_measure_sandwich` |
| exponent limit — equation `(5)` | `tendsto_log_integerReturnPreimage_div_log` |
| a spanning character family contains a nonsingular square selection | `exists_selectedSquare_det_ne_zero` |
| **exponent law under minimality alone** | `tendsto_log_integerReturnPreimage_div_log_of_span` |

The upper bound needs no bi-Lipschitz chart: preimages along a nonsingular integer torus
endomorphism have unchanged Haar measure, which replaces the local-chart argument of the paper
proof by an exact global one.  The only hypothesis of the capstone is that the integer characters
span the rational presenting space — precisely minimality of the presentation, that is, that the
presenting torus has dimension the rational rank `τ`.

### Remaining gates

All ten formalization obligations are discharged unconditionally, so the 2 → 3 gate is met and the
card sits at Stage 3.  Its remaining gates -- the positive finite-scale replacement law, the
collision-complete external novelty audit, the feasible protocol with finite error analysis, and the
Nature hostile review -- are research and publication gates beyond formalization, not formalization
gates.

- 2026-08-05 — obligations 3, 6, 8 and the Theorem A topology closed unconditionally in Lean;
  obligations 1, 2, 4, 5, 7, 9 verified already present in the corpus.  All ten formalization
  obligations are discharged; the remaining open gates are non-formal.

## Lean certificate (2026-08-06) — the theorem-level capstones

The 2026-08-05 certificate discharged the ten formalization obligations, which are the *ingredients*
of the card.  The theorems and corollaries themselves are now compiled as single statements as well.
All modules are in `formal/GaloisForLFunctions/HTGeometry/` and wired into
`GaloisForLFunctions/HTGeometry.lean`; every declaration reports
`[propext, Classical.choice, Quot.sound]`.

| Card statement | Lean declaration | Module |
|---|---|---|
| Theorem A, last claim: `r_ℚ` is continuous at no point | `rationalCoordinateRank_nowhereContinuous` | `ArithmeticTemporalRankInstability` |
| Theorem B | `exists_isHermitian_commuting_close_gapRank` | `SimpleSpectrumMatrixPerturbation` |
| Theorem C `(1)` | `norm_unitaryEvolution_sub_le` | `ObserverProfileStability` |
| **Theorem C `(2)`** uniform bounded-horizon indistinguishability at every dimension | `exists_isHermitian_commuting_gapRank_uniform_horizon` | `EternityHorizonCapstone` **(new)** |
| the horizon bound itself | `norm_unitaryEvolution_sub_lt_of_le_horizon` | `EternityHorizonCapstone` **(new)** |
| **Corollary 1** with a horizon fixed in advance | `exists_isHermitian_commuting_periodic_and_aperiodic_uniform_horizon` | `EternityHorizonCapstone` **(new)** |
| **Theorem C `(3)`** the observable/trace form | `norm_trace_densityMatrix_heisenberg_sub_le` | `EternityObservableHorizonLaw` **(new)** |
| the state-pairing bound `\|tr ρX\| ≤ ‖X‖` | `norm_trace_densityMatrix_mul_le` | `EternityObservableHorizonLaw` **(new)** |
| every matrix entry is inside the operator norm | `norm_entry_le_l2_opNorm` | `EternityObservableHorizonLaw` **(new)** |
| the observed orbit of a *presented* Hamiltonian | `observedOrbit_eq_orbitAssembly_presented`, `exists_hasBoxDim_closure_range_observedOrbit_presented` | `PresentedOrbitDimensionEternity` **(new)** |
| the reporter family resolving every gap | `completeReporter`, `presentedVisibleGapSet_completeReporter` | `PresentedOrbitDimensionEternity` **(new)** |
| the full gap module is the anchored gap module | `span_gapSet_eq_span_anchored`, `finrank_span_gapSet_eq_rationalCoordinateRank` | `PresentedOrbitDimensionEternity` **(new)** |
| **Corollary 2** every neighbourhood contains every recurrence dimension | `exists_isHermitian_commuting_orbitDimension_uniform_horizon` | `PresentedOrbitDimensionEternity` **(new)** |
| **Corollary 2** no dimension is open | `exists_isHermitian_commuting_orbitDimension_distinct` | `PresentedOrbitDimensionEternity` **(new)** |
| integer rows with an integer left inverse span | `span_rows_eq_top_of_leftInverse` | `EternityReturnExponentCapstone` **(new)** |
| **Corollary 3** every neighbourhood contains every return exponent `(4)`–`(5)` | `exists_isHermitian_commuting_returnExponent_uniform_horizon` | `EternityReturnExponentCapstone` **(new)** |
| Corollary 3 `(6)` maximal-rank exact law | `finiteTorusHaarProbabilityMeasure_anchoredProjectiveReturnTarget` | `AnchoredProjectiveReturnDensityLaw` |

Three points of substance in the new material.

1. **The horizon is the perturbation radius.**  `η / T` is the only quantifier order that makes
   `(2)` a theorem: the horizon and the error are fixed *before* the neighbour is chosen, and the
   Duhamel bound then holds uniformly on `|t| ≤ T`.  All three capstones — dimension, periodicity,
   orbit dimension, return exponent — are stated inside that tube.

2. **Reading the dimension off the presentation.**  The corpus computes the completed-orbit
   dimension from a chosen eigenbasis, which is not available for a matrix built from a prescribed
   spectrum.  `exists_hasBoxDim_closure_range_observedOrbit_presented` re-derives it from any
   presentation `H = V diag(E) V*`, which is exactly the form the perturbation is constructed in.
   With the all-ones reporter conjugated into the presenting basis every gap is visible, so the
   visible gap module is the full gap module and its rank is the temporal dimension.

3. **The return exponent needs no chart.**  `exists_frequency_integer_basis` presents the gaps as
   integer combinations of a rationally independent basis *together with an integer left inverse*;
   the left inverse forces the rows to span the rational coordinate space, which is precisely the
   hypothesis of the return-volume law.  So Corollary 3's `(4)`–`(5)` hold for the constructed
   neighbour with no local bi-Lipschitz chart anywhere in the argument.

**Correction to Theorem A.**  The nowhere-continuity claim is stated in the card for `n ≥ 1`; it is
false at `n = 1`, where `r_ℚ` is locally constant away from the origin.  The Lean statement carries
the correct hypothesis `2 ≤ n`, which is what the proof (density of `R_{n,1}` *and* of `R_{n,n}`
with `1 ≠ n`) actually gives.  Everything else in Theorem A is unaffected.

- 2026-08-06 — the theorem-level capstones compiled: Theorem C `(2)` and `(3)`, Corollary 1 with a
  prescribed horizon, Corollary 2 in both halves, and Corollary 3's exponent law for the
  constructed neighbour.  Four new modules; `lake build GaloisForLFunctions.HTGeometry` green.

### The group form of Corollary 2 and the two-sided law of Corollary 3

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/EternityCompletedTimeTorusCapstone.lean`.

| Card statement | Lean declaration |
|---|---|
| the projective frequencies are the anchored gaps | `range_projectiveFrequency_eq`, `finrank_span_projectiveFrequency_eq` |
| **Corollary 2, group form**: the neighbour's completed projective time is a compact connected subgroup presented isomorphically by a `k`-torus | `exists_isHermitian_commuting_completedTimeTorus_uniform_horizon` |
| **Corollary 3 `(4)`**: the neighbour's two-sided return-volume law `(2/L)^k ε^k ≤ m ≤ 4^k ε^k`, with `(5)` alongside | `exists_isHermitian_commuting_returnVolume_sandwich_uniform_horizon` |

The group form uses the corpus representation `exists_completedTime_representation` — the completed
time of a frequency packet is the range of an injective integer torus homomorphism, hence compact,
connected, and isomorphic as a topological group to the presenting torus
(`orbitClosureAddEquiv`, `orbitClosureHomeomorph`).  What the capstone adds is that the presenting
dimension can be prescribed: the perturbation fixes the rank of the gap packet, and the projective
frequency packet has the same rank because its range is literally the set of anchored gaps.

With this the card is formalized at the level of its statements, not only of its obligations:
Theorem A (all four claims), Theorem B, Theorem C `(1)`–`(3)`, Corollary 1 (both forms),
Corollary 2 (dimension form, group form, and non-openness) and Corollary 3 `(4)`–`(6)` are each a
single unconditional Lean theorem.

- 2026-08-06 — Corollary 2's group form and Corollary 3's two-sided law `(4)` added for the
  prescribed neighbour; `lake build` green on every new module, all axiom-clean.

### Corollary 1 in the card's exact form

`[LEAN-PROVED]` Added to `formal/GaloisForLFunctions/HTGeometry/ProjectiveExactReturnRankOne.lean`.

The corpus equivalence was stated for an arbitrary spectrum, with "gap rank `≤ 1`".  The card states
Corollary 1 for a *simple* spectrum, with "gap rank **is** one".  For a simple spectrum the two
agree, because the first gap is already nonzero and a nonzero coordinate forces positive rank; that
step is now proved and the card's form is available directly.

| Card item | Lean name |
|---|---|
| a nonzero coordinate forces positive rational rank | `rationalCoordinateRank_pos` |
| **Corollary 1 as stated**: simple spectrum, exact projective return iff gap rank `= 1` | `hasPositiveProjectiveReturn_iff_gapRank_eq_one` |

- 2026-08-06 — Corollary 1 sharpened from `≤ 1` to `= 1` under simplicity, matching the card text.

### Theorem B stated on the eigenvalues themselves

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/EternityEigenvaluePresentation.lean`
(wired into `GaloisForLFunctions/HTGeometry.lean`; axiom-clean).

The perturbation is built from a prescribed spectrum `E'`, so the corpus statement of Theorem B
gives the rank of `E'`.  The card states `τ(K_k)` in terms of the eigenvalues `λ_j(K_k)` of the
perturbed matrix.  These agree, and the identification is now proved rather than tacit.

| Card item | Lean name |
|---|---|
| the eigenvalue value set of a spectral presentation | `range_eigenvalues_of_presentation` |
| a presented simple spectrum makes the eigenvalue function injective | `injective_eigenvalues_of_presentation` |
| the gap module depends only on the value set of the spectrum | `rationalCoordinateRank_gaps_congr` |
| **Theorem B in the card's own form** | `exists_isHermitian_commuting_close_eigenvalueGapRank` |
| **Theorem B with a horizon, on the eigenvalues** | `exists_isHermitian_commuting_eigenvalueGapRank_uniform_horizon` |
| **Corollary 1 on the eigenvalues**: simple periodic and simple aperiodic neighbours in one tube | `exists_isHermitian_commuting_eigenvaluePeriodic_and_aperiodic_uniform_horizon` |
| **Corollary 3 on the eigenvalues**: the neighbour's own gaps present the return exponent `k` | `exists_isHermitian_commuting_eigenvalueReturnExponent_uniform_horizon` |
| **Corollary 2, group form, on the eigenvalues**: the neighbour's own completed time is a `k`-torus | `exists_isHermitian_commuting_eigenvalueCompletedTimeTorus_uniform_horizon` |
| **Corollary 2 as worded**: the completed time *is* a `k`-torus — homeomorphic and group-isomorphic, not merely a presented range | `exists_isHermitian_commuting_completedTimeTorus_equiv_uniform_horizon`, `exists_isHermitian_commuting_eigenvalueCompletedTimeTorus_equiv_uniform_horizon` |
| a minimal integer presentation is a closed embedding | `isClosedEmbedding_torusIntegerHom`, `torusIntegerHomHomeomorphRange`, `torusIntegerAddEquivRange` |
| **Corollary 3's `R_K(ε)` as worded**: the anchored chord target *is* the projective operator-norm return target | `mem_anchoredProjectiveReturnTarget_iff_l2_opNorm` |
| the operator-norm distance to the anchoring phase is the largest relative-phase chord | `l2_opNorm_unitaryEvolution_sub_anchorPhase`, `anchorPhase` |
| unitary conjugation is an isometry of the operator norm | `l2_opNorm_unitary_conj_eq` |
| **`R_K(ε)` as a set of times**, and its pullback description | `projectiveReturnTimes`, `projectiveReturnTimes_eq_preimage` |
| **exact projective return in operator norm** is the `ε = 0` target | `unitaryEvolution_eq_anchorPhase_smul_one_iff` |
| the degenerate target is the arithmetic return condition | `mem_anchoredProjectiveReturnTarget_zero_iff`, `fourier_one_coe_eq_one_iff` |
| **`HasPositiveProjectiveReturn` in operator terms**: the evolution reaches a scalar multiple of the identity | `exists_pos_unitaryEvolution_eq_anchorPhase_smul_one_iff` |
| **Corollary 1 in operator form**: a simple spectrum repeats exactly in operator norm iff its gap rank is one | `exists_pos_unitaryEvolution_eq_anchorPhase_smul_one_iff_gapRank_eq_one` |
| **the card's public theorem, on the operator**, as a single statement | `eternity_public_theorem` |
| **Corollary 1's dense pair, in operator form**: a neighbour whose evolution reaches a scalar multiple of the identity and one whose evolution never does, in the same tube | `exists_isHermitian_commuting_operatorPeriodic_and_aperiodic_uniform_horizon` |
| **Theorem B's displayed norm identity** `‖H − K‖ = max_j \|λ_j − λ'_j\|` | `l2_opNorm_spectralTransport_sub`, `l2_opNorm_conjStarAlgAut_diagonal_sub` |
| **Theorem C's mechanism**: `‖e^{−itK} − e^{−itH}‖ = max_j \|e^{−itλ'_j} − e^{−itλ_j}\|` for shared eigenvectors | `l2_opNorm_unitaryEvolution_spectralTransport_sub` |
| **Theorem C's distance in closed form**: `= 2 max_j \|sin(t(λ'_j−λ_j)/2)\|` | `l2_opNorm_unitaryEvolution_spectralTransport_sub_eq_sin`, `norm_exp_neg_I_mul_sub_exp_neg_I_mul` |
| **Theorem C `(1)` by the card's own route** (closed form + `\|sin x\| ≤ \|x\|`) | `l2_opNorm_unitaryEvolution_spectralTransport_sub_le` |
| a square integer matrix with an integer left inverse is nonsingular | `det_ne_zero_of_leftInverse` |
| **Corollary 3 `(6)` for a constructed maximal-rank neighbour** | `exists_isHermitian_commuting_maximalReturnLaw_uniform_horizon` |

The value-set step is the spectrum computation: unitary conjugation preserves the `ℂ`-spectrum
(`AlgEquiv.spectrum_eq`), the spectrum of a real diagonal matrix is the set of its entries
(`spectrum_diagonal`), and the real spectrum is the real points of the complex one
(`spectrum.algebraMap_mem_iff`); mathlib's `spectrum_real_eq_range_eigenvalues` then identifies it
with the eigenvalue value set.  Injectivity follows by counting: `n+1` distinct prescribed values in
the image of an `n+1`-element domain.

- 2026-08-06 — Theorem B's temporal dimension restated on the perturbed matrix's own eigenvalues,
  closing the last place where a card statement was carried by the construction rather than proved.
- 2026-08-06 — Corollary 1 restated on the perturbed matrices' own eigenvalues as well, using the
  sharpened `= 1` equivalence: from three levels onward every uniform bounded-horizon tube contains
  a commuting neighbour with simple spectrum that returns exactly and one that never does, both
  read off the neighbours' own spectra.
- 2026-08-06 — Corollary 3 also restated on the neighbour's own eigenvalues.  Equal gap *modules*
  do not give equal anchored gaps, so the integer character presentation is rebuilt from the
  eigenvalue gap vector itself; its rank is `k` by the value-set congruence, and the return
  exponent follows as before.  Theorem B and Corollaries 1 and 3 are now uniformly stated on the
  perturbed matrix's own spectrum.
- 2026-08-06 — Corollary 2's group form restated on the neighbour's own eigenvalues as well.  Every
  statement of Theorem B and Corollaries 1--3 is now available both in the construction's spectrum
  and in the perturbed matrix's own spectrum; the bridge in each case is the value-set congruence of
  the gap module.
- 2026-08-06 — `(6)` bridged from the coordinate torus to a constructed neighbour.  At maximal rank
  the presenting character matrix has an integer left inverse and is square, hence unimodular, so
  the pulled-back anchored chord target keeps the exact coordinate-torus law
  `(2 arcsin(ε/2)/π)^{D-1}`.  Every clause of Corollary 3 -- the two-sided law `(4)`, the exponent
  `(5)` and the maximal-rank closed form `(6)` -- now holds of a neighbour the theorems produce.
- 2026-08-06 — Theorem A's two remaining wordings proved.  The avoidance theorem was an
  `∃`-statement; the card says the *set* `R_{n,k} ∖ ⋃𝒜` is dense, which is now the statement
  (`dense_exactRationalRank_avoiding`).  The card's consequence -- "exact rank `k` can be realized
  arbitrarily close to any gap packet while retaining nonzero and pairwise distinct gaps" -- is the
  avoidance theorem applied to the coordinate hyperplanes `ω_i = 0` and the diagonal hyperplanes
  `ω_i = ω_j`, a finite rational family; that instantiation is now
  `exists_exactRationalRank_close_distinct`.
- 2026-08-06 — Corollary 2's phrase "hence a `k`-torus up to a finite character presentation" made a
  theorem.  The corpus had the closure *equal to the range* of an injective integer torus
  homomorphism, together with compactness and connectedness; the card asserts the closure **is** a
  `k`-torus.  That upgrade is the closed-embedding argument: a continuous injection of a compact
  space into a Hausdorff space is a closed embedding, so the presenting torus is homeomorphic to the
  closure, and injectivity of the bundled homomorphism makes it an isomorphism of topological
  groups.  Both the construction-spectrum and the eigenvalue forms now carry it.
- 2026-08-06 — Corollary 3's target identified with the object the card names.  The return law is
  proved for the *anchored chord* target on the relative-phase torus, whereas the card defines
  `R_K(ε)` as the projective **operator-norm** return target of the evolution.  These are now proved
  to be the same set: conjugation by the eigenvector unitary is an isometry, so the operator-norm
  distance from `e^{-itK}` to its anchoring phase `e^{-itλ_a}` is exactly the largest chord among
  the relative phases, and membership in the chord target is equivalent to that distance being at
  most `ε`.  The equivalence needs `0 ≤ ε` — for a one-level system the chord condition is vacuous
  while the operator-norm condition is not.
- 2026-08-06 — `R_K(ε)` given as a set of *times* and identified with the pullback of the chord
  target along the phase map, so every Haar statement about the target is a statement about the
  operator-norm return set.  At `ε = 0` the same equivalence says the evolution equals a scalar
  multiple of the identity exactly when its relative-phase point is an exact return — the operator
  form of the exact-repetition notion Corollary 1 classifies.
- 2026-08-06 — Corollary 1 restated on the operator.  `HasPositiveProjectiveReturn` is the
  arithmetic condition "some `T > 0` puts every gap in `2πℤ`"; the card's claim is about a
  Hamiltonian that *repeats exactly*.  The two are now proved equivalent — a positive time exists
  with `e^{-itK}` a scalar multiple of the identity exactly when the arithmetic condition holds —
  so the rank-one criterion reads directly as a statement about the matrix and its evolution.
- 2026-08-06 — the dense periodic/aperiodic pair also restated on the operator.  The public theorem
  says every quantum Hamiltonian is arbitrarily close both to a system that *repeats exactly* and to
  one that *never repeats exactly*, indistinguishable on any prescribed horizon.  Both clauses are
  now literally about the evolutions: one neighbour satisfies `e^{-itB} = c·1` at some positive
  time, the other satisfies no such equation at any positive time.
- 2026-08-06 — Theorem B's displayed norm identity proved as an equality.  The construction only
  needed the bound `‖K − H‖ < δ`, so that is what the corpus carried; the card states the exact
  value `max_j |λ_j − λ'_j|`.  With unitary conjugation now known to be an isometry, the difference
  is the conjugate of a diagonal matrix and its operator norm is exactly the supremum of the
  spectral shifts.
- 2026-08-06 — Theorem C's proof mechanism proved as an identity.  The card argues `(1)` by
  "taking the maximum diagonal entry" of the shared-eigenbasis phase differences; the corpus had
  only the resulting Lipschitz bound.  Since unitary conjugation is an isometry, the evolution
  distance of two spectra transported through one eigenbasis *is* the largest phase chord, and the
  card's bound is that identity together with the scalar estimate on each chord.
- 2026-08-06 — Theorem C's distance given in closed form.  Each phase chord is `2|sin(θ/2)|` of the
  spectral shift, so the evolution distance of the constructed neighbour is exactly
  `2 max_j |sin(t(λ'_j − λ_j)/2)|`.  Both consequences the card uses fall out of this: the Lipschitz
  bound `(1)`, from `|sin x| ≤ |x|`, and the fact that the distance never exceeds `2` however long
  the horizon — the quantitative content of "the instability carries no bounded-time dynamical
  singularity".
- 2026-08-06 — `(1)` also derived the card's way.  The corpus proves it for arbitrary pairs by a
  C*-estimate; the card proves it for the constructed neighbour from the shared eigenbasis, by
  bounding each phase chord.  That derivation is now a theorem: the closed-form distance against
  `|sin x| ≤ |x|`, with `‖K − H‖` the exact spectral shift of Theorem B.  Theorem C's proof as the
  card writes it is therefore machine-checked end to end.
- 2026-08-06 — the public theorem compiled as one object.  The card opens with a single claim: every
  finite quantum system lies arbitrarily close to systems of every recurrence dimension, and (from
  three levels onward) both to one that repeats exactly and to one that never does, all
  indistinguishable on any horizon fixed in advance.  `eternity_public_theorem` states exactly that,
  on the neighbours' own spectra and their evolutions, so the headline is one citable theorem rather
  than a conjunction a reader assembles.
- 2026-08-06 — the codomain of Theorem A's rank function proved.  The card writes
  `r_ℚ : ℝⁿ → {0,1,…,n}`; the corpus defined the rank and used it everywhere but never recorded that
  it is bounded by `n`.  It is, because the span is generated by the `n` coordinates.
- 2026-08-06 — full-tree audit: `lake build GaloisForLFunctions.MainTheorems` green (21579 jobs),
  and all four card capstones -- `eternity_public_theorem`,
  `ContactMatrix.stokes_tomography_law`, `RHTower.groskinArchimedeanTailStatement`,
  `mobiusFixedCurrentTransportWeld` -- are reachable from the top-level umbrella and report
  `[propext, Classical.choice, Quot.sound]` there.
- 2026-08-06 — Theorem A's written proof step formalized, and a route divergence recorded.  The card
  proves density by taking a transcendental `θ` and the space `V_k = span_ℚ{1, θ, …, θ^{k-1}}`,
  asserting `dim_ℚ V_k = k`.  That step is now a theorem: a vanishing rational combination of powers
  is a rational polynomial vanishing at `θ`, hence zero, so the powers are independent and the span
  has dimension exactly `k`; transcendental reals exist because the algebraic ones are countable.
  The Lean density proof itself does **not** use this route — `exists_linearIndependent_close` builds
  independent perturbations from countability of a finitely generated `ℚ`-span, which needs no
  explicit transcendental.  Both routes are now available, and the card's own one is checked.
- 2026-08-06 — the card's avoidance step built.  Its hyperplane-avoidance argument chooses "a
  direction on which none of the finitely many hyperplane normals vanishes", justified by "a finite
  union of proper subspaces cannot cover a vector space over the infinite field `ℚ`".  Mathlib does
  not carry that, so it is proved here for any infinite field: a partial witness is corrected along
  a vector the new functional detects, and each old functional is spoiled by at most one scalar, so
  all but finitely many corrections work.  Stated both as a common non-vanishing vector and as a
  point off the union of the kernels.
- 2026-08-06 — the card's two-case basis step formalized.  Building a `ℚ`-basis inside a box, the
  card forms `v_j = a + q b` with `b` outside the span built so far and argues: if `a` lies in that
  span then every nonzero `q` escapes it, and if `a` lies outside then at most one rational `q`
  falls back in.  Both cases are now lemmas, for an arbitrary field and submodule.
- 2026-08-06 — the card's density step for `V_k` proved.  "Since `ℚ ⊂ V_k` and `ℚ` is dense in `ℝ`,
  `V_k` is dense" is now a lemma about any rational subspace of the reals containing `1`, applied to
  `span_ℚ{1, θ, …, θ^{k-1}}`.  Note it needs no transcendence -- only that `θ^0 = 1` lies in the
  span -- which the card's prose leaves implicit.
- 2026-08-06 — the card's selection step proved, and the two escape lemmas moved upstream to sit
  beside it.  "Choose `a ∈ V_k ∩ I_j` and `b ∈ V_k ∖ W_{j-1}`; for a sufficiently small nonzero
  rational `q`, `v_j = a + q b` lies in `I_j` and outside `W_{j-1}`" is now one theorem: density
  supplies `a`, properness supplies `b`, and the correction is scaled by `1/m` with `m` past
  `2|b|/ε`.  Every ingredient of Theorem A's written construction is now machine-checked.
- 2026-08-06 — Theorem A's construction assembled end-to-end on the card's own route.  The inductive
  basis step is `exists_linearIndependent_mem_close`: inside a dense rational subspace of dimension
  `k`, any `m ≤ k` prescribed reals are approximated by `m` independent elements, each stage using
  the selection step against the span built so far (proper because its dimension is still below
  `k`).  The assembly `exists_close_span_eq_of_dense` then fills the remaining coordinates by
  density and shows the packet's rational span is *exactly* the prescribed subspace -- stronger than
  the rank statement, which follows.  This is the card's route; the corpus's own density proof
  remains the independent second route.
- 2026-08-06 — moved to `3-formalized`.  The pipeline's 2 → 3 gate is "formalised in Lean 4", and
  that gate is ticked: every obligation, every theorem and corollary statement, and every step of
  the written proofs is a closed unconditional Lean theorem.  The four unticked gates are
  post-formalization research and publication gates, not criteria for this stage.

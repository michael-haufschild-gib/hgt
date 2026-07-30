# Arithmetic completion of quantum time

- **ID:** `arithmetic-completion-of-quantum-time`
- **Stage:** 1-in-progress
- **Type:** FROZEN FOUNDATIONAL CONJECTURE / UNIVERSAL RECURRENCE LAW
- **Status:** `[TRUTH-HUNCH] [FINITE CORE OPEN] [NOT A MANUSCRIPT CLAIM]`
- **Date frozen:** 2026-07-30
- **Predecessor:** `../5-failed/asymptotic-time-boundary-principle-conjecture.md`

## Public law

> **Two quantum systems can be arbitrarily close and still have different
> numbers of dimensions in eternity.**

Foundational form:

> **Quantum eternity is an arithmetic completion. Its exact dimension is
> nowhere stable; physical time is the full spectrum of when temporal
> distinctions become resolvable.**

Shortest:

> **Eternity is nowhere stable.**

## Frozen truth-hunch

A quantum system does not possess one physically complete scalar “dimension
of time.” For every observer it has a canonical **temporal relation
spectrum**
\[
  \mathscr U_{\mathcal O}
\]
that records every observer-testable temporal character together with:

- its exact detuning from a temporal relation;
- the minimum observational/replica complexity needed to test it;
- the perturbative depth at which it is created under controlled
  interaction;
- its recurrence weight; and
- its persistence or decay scale.

Finite-horizon temporal dimension, weak-coupling temporal birth, exact
infinite-time recurrence dimension, return density, observer dependence and
open-system survival are universal projections of this one spectrum.

Exact infinite-time dimension is the zero-detuning arithmetic fiber of
\(\mathscr U_{\mathcal O}\). It is not a robust phase on Hamiltonian
parameter space: every neighborhood contains systems with every admissible
rational rank. Bounded-time dynamics remains uniformly continuous. Thus
arithmetic completion adds exact long-time information that no open
finite-horizon phase classification can contain.

This statement is frozen before selecting:

- the exact character-complexity function;
- a lattice norm or replica filtration;
- a persistence coordinate;
- a topology or measure on \(\mathscr U_{\mathcal O}\);
- a categorical, adelic, tropical or spectral realization;
- a proof strategy; or
- a Lean representation.

The elementary rational/irrational example exposed the missing object but
does not define it.

## Ontological reversal

Conventional recurrence theory assigns a torus dimension after taking exact
infinite time. Finite-time theory then approximates that terminal object. The
conjecture reverses the dependency:

1. the primary object is the complete resolution spectrum of temporal
   relations;
2. an observer at finite horizon and finite probe complexity sees one
   quotient or slice;
3. waiting longer can resolve near-relations and increase effective temporal
   dimension;
4. asking higher-order joint questions can expose relations invisible to
   simpler probes and reduce the dimension seen at that complexity;
5. interaction creates new relation-spectrum branches at definite
   perturbative depths;
6. dissipation terminates branches at definite survival horizons;
7. exact eternity is the arithmetic zero fiber reached only after all
   horizons and all character complexities are completed.

Time's dimension is therefore a resolution-dependent rank profile, not an
absolute coordinate count.

## Universal statement

The conjecture asserts all of the following.

1. **Canonical spectrum.** Every observer of every complete quantum dynamics
   has a presentation-independent temporal relation spectrum.
2. **Operational completeness.** Every finite-order, finite-horizon
   recurrence or phase-discrimination experiment factors through a bounded
   region of the spectrum; conversely every spectral point has a finite
   protocol approaching its predicted resolution threshold.
3. **Exact completion.** The exact zero-detuning fiber, completed over all
   probe complexities, is the observer-visible temporal character group and
   determines every exact recurrence law.
4. **Dense arithmetic instability.** In every finite Hermitian neighborhood
   supporting \(n\) visible projective gaps, every rational temporal rank
   \(1,\ldots,n\) occurs arbitrarily nearby.
5. **Bounded-horizon continuity.** For every finite horizon and tolerance,
   sufficiently close Hamiltonians have uniformly close complete histories
   on that horizon even when their exact completion ranks differ maximally.
6. **Scale-dependent dimension.** There is a canonical integer/rank profile
   \(d_{\mathcal O}(T,m,\varepsilon)\) determined by temporal detuning,
   observation horizon \(T\), probe complexity \(m\) and resolution
   \(\varepsilon\).
7. **Monotonic laws.** In closed systems, increasing observation horizon can
   only resolve constraints and increase effective temporal dimension;
   increasing allowed relation/probe complexity can only expose additional
   constraints and decrease the dimension at fixed resolution. The full
   two-parameter profile is the invariant, not either monotone projection.
8. **Interaction birth.** Controlled analytic interactions attach a birth
   valuation to spectrum branches. A branch becomes observable when its
   detuning times observation horizon is order one.
9. **Open-system extension.** Decay attaches a death/survival coordinate.
   Recurrent and transient time are respectively persistent and terminated
   branches of one spectrum.
10. **Infinite extension.** Countable pure-point, mixed and atomless spectra
    arise as distinct completions of compatible finite relation spectra,
    without forcing one finite-dimensional rank.
11. **Return-law completeness.** Exact and finite-resolution return
    distributions, minimax clocks and replica collision hierarchies are
    functorial projections of \(\mathscr U_{\mathcal O}\).
12. **No robust scalar substitute.** No single terminal rank, recurrence
    time, spectral entropy or genericity label determines the complete
    temporal relation spectrum.

## Candidate finite mathematical realization

This is a post-freeze realization target, not part of the truth-hunch used to
select it.

Let \(\Lambda_{\mathcal O}\) be the observer-visible integer character
lattice. For \(q\in\Lambda_{\mathcal O}\), let
\[
  \Omega(q)
\]
be its spectral detuning and let \(h_{\mathcal O}(q)\) be the minimum
observer/replica complexity that realizes the character. A first candidate
resolution spectrum is
\[
  \mathscr U_{\mathcal O}
  =
  \bigl\{(h_{\mathcal O}(q),|\Omega(q)|,q):
  q\in\Lambda_{\mathcal O}\bigr\},
\]
enriched by perturbative birth valuation and open-system decay where
present.

For fixed complexity \(m\), horizon \(T\) and phase tolerance
\(\varepsilon\), define the finite set of effectively unresolved characters
\[
  \mathcal R_{m,T,\varepsilon}
  =
  \bigl\{
  q:\ h_{\mathcal O}(q)\le m,\quad
  T|\Omega(q)|\le\varepsilon
  \bigr\}.
\]
A candidate effective dimension is
\[
  d_{\mathcal O}(T,m,\varepsilon)
  =
  r_{\mathcal O}(m)
  -
  \operatorname{rank}_{\mathbb Q}
  \operatorname{span}_{\mathbb Q}
  \mathcal R_{m,T,\varepsilon},
\]
where \(r_{\mathcal O}(m)\) is the complete character rank available at
complexity \(m\).

This formula is not yet authorized:

- approximate relations need not form a lattice;
- the correct operational complexity may not be a norm;
- linearly independent near-relations can overconstrain a naive quotient;
- finite reporter geometry and weights may require singular values rather
  than hard thresholds; and
- return distributions retain more than rank.

The realization must be derived from measurement distinguishability, not
chosen for convenience.

## First exact theorem spine to prove

### A. Dense rank spectrum

For every \(n\ge1\), every \(\omega\in\mathbb R^n\), every
\(\delta>0\), and every \(1\le k\le n\), there is
\(\omega'\) with
\[
  \|\omega-\omega'\|<\delta,
  \qquad
  \dim_{\mathbb Q}
  \operatorname{span}_{\mathbb Q}
  \{\omega'_1,\ldots,\omega'_n\}=k.
\]

Consequently every simple \(D\)-level Hermitian Hamiltonian lies arbitrarily
close to simple Hamiltonians of every projective temporal dimension
\(1,\ldots,D-1\), while keeping the eigenvectors fixed.

### B. Uniform finite-horizon indistinguishability

For Hermitian \(H,K\),
\[
  \|e^{-itH}-e^{-itK}\|
  \le |t|\,\|H-K\|.
\]
Hence for every \(T,\eta>0\), Hamiltonians with different exact temporal
dimensions can be chosen so that
\[
  \sup_{|t|\le T}
  \|e^{-itH}-e^{-itK}\|<\eta.
\]

### C. Dense return-density exponents

For a rank-\(d(H)\) phase orbit, Haar measure of a sufficiently small
operator-norm return neighbourhood has local scaling exponent \(d(H)\):
\[
  \lim_{\varepsilon\downarrow0}
  \frac{\log \operatorname{dens} R_H(\varepsilon)}
       {\log\varepsilon}
  =d(H),
\]
provided the return target is measured in the induced phase-subtorus metric.
The multiplicative constant, and the exact finite-\(\varepsilon\) formula,
can depend on the integer embedding of the rank-\(d(H)\) subtorus.

For maximal projective rank \(D-1\), the corpus's exact coordinate-torus law
specializes to
\[
  \operatorname{dens} R_H(\varepsilon)
  =
  \left(
    \frac{2\arcsin(\varepsilon/2)}{\pi}
  \right)^{D-1}.
\]
Thus every Hamiltonian neighbourhood contains systems with every local
return-density exponent \(1,\ldots,D-1\), despite uniform bounded-horizon
closeness. Only the maximal-rank stratum receives the displayed exact product
formula without additional lattice-shape data.

### D. Stable finite-scale replacement

Construct an operational finite-scale rank profile that:

1. is stable under bounded perturbation at fixed \(T,m,\varepsilon\);
2. converges to exact character rank in a declared completion order;
3. recovers interaction birth horizons;
4. recovers observer quotient laws; and
5. determines finite-resolution return statistics more sharply than scalar
   rank.

Theorems A--C expose the problem. Theorem D is the new positive law required
for a Nature paper.

## Why the corpus points here

| Corpus fact or no-go | Projection of the proposed spectrum |
|---|---|
| Projective temporal dimension is rational gap rank | Exact zero-detuning fiber |
| Observer dimension plus hidden constraint rank is conserved | Rank of observer quotient and kernel |
| Weak interaction breaks relations at analytic birth orders | Perturbative birth coordinate |
| Observation time scales as inverse detuning | Resolution coordinate |
| Graph/Steiner depth lower-bounds birth | Locality lower envelope |
| Return density exponent equals temporal rank | Terminal rank projection |
| Minimax recurrence clock uses weights and tolerance | Weighted finite-resolution projection |
| Replica collision hierarchy sees higher gap relations | Probe-complexity filtration |
| Contractive dynamics has peripheral and transient parts | Persistence/death coordinate |
| Exact moments can miss pure-point versus atomless completion | Finite complexity does not determine terminal completion |
| Exact rank is dense-discontinuous in analytic families | Scalar infinity is not a robust phase |
| Factorization and source support are presentation-sensitive | Character spectrum must be observer-operational, not coordinate sparse |

## Risky consequences

1. **Every eternity nearby.** Every neighborhood of a generic finite
   Hamiltonian contains systems with every possible projective recurrence
   dimension.
2. **No open exact recurrence phase.** Maximal rank is full measure and
   residual but is not an open phase; lower ranks are exceptional but dense.
3. **Finite-history universality.** No finite coherent observation window,
   regardless of precision fixed in advance, robustly certifies exact
   recurrence dimension.
4. **Dimension flow.** A calibrated finite system exhibits an
   observer-dependent staircase of effective temporal dimensions as
   observation horizon and probe complexity change.
5. **Interaction/Diophantine separation.** Birth valuation determines when a
   new spectral branch becomes nonzero; Diophantine detuning determines when
   its independence becomes distinguishable. These are distinct coordinates
   and can be experimentally separated.
6. **Return-law crossover.** Return-density exponents inferred on finite
   windows change in steps governed by the relation spectrum and converge
   only in a specified joint resolution limit.
7. **Open temporal barcode.** Weak loss turns the closed-system dimension
   staircase into a birth--death profile whose persistent bars are exact
   recurrent directions.
8. **Many-body compression.** In a generic local many-body system, an
   exponential number of terminal temporal directions may be compressed into
   a much smaller finite-horizon effective dimension.

## First experiment

Program a three-level system with calibrated gaps \(1\) and \(g\). Choose
sequences of rational and irrational \(g\) values that are closer than the
inverse experimental horizon.

At every fixed horizon the two families must produce uniformly convergent
unitary histories. Their completed temporal dimensions are nevertheless one
and two. Increase observation horizon and relation-probe complexity while
measuring phase-return statistics.

The finite-scale law predicts a controlled crossover governed by the
measured detuning/complexity spectrum rather than a discontinuous laboratory
observable at rational versus irrational \(g\). A claimed direct finite
measurement of exact rationality falsifies the operational interpretation.

## External parent boundary

Parents include:

- Kronecker--Weyl equidistribution and Diophantine approximation;
- Poincaré and quantum recurrence;
- finite quantum clock constructions with commensurate and
  incommensurate spectra;
- quantum speed limits and frequency metrology;
- metastability, prethermalization and weak-coupling limits;
- persistent rank, barcodes and multiscale dimension;
- spectral measures, compact abelian phase groups and Pontryagin duality;
- replica/spectral-form-factor collision hierarchies.

Initial search found each ingredient separately but no primary source proving
Theorems A--C as one quantum-recurrence instability law or constructing
Theorem D's observer-relative temporal relation spectrum. This is not a
completed priority audit.

## Hard falsifiers

1. some rational rank \(k\) is not dense in finite gap space;
2. simple Hamiltonians cannot realize all projective ranks arbitrarily close
   while retaining bounded-horizon closeness;
3. exact return-density exponent is stable on a nonempty open Hamiltonian
   set without an imposed arithmetic restriction;
4. no operationally canonical character-complexity filtration exists;
5. finite-scale effective rank cannot be made perturbation-stable;
6. the rank profile fails to converge to exact temporal completion under any
   physically meaningful order of limits;
7. finite return distributions require information absent from the full
   proposed relation spectrum;
8. observer changes do not act functorially on the spectrum;
9. interaction birth and Diophantine resolution cannot be represented as
   independent coordinates;
10. open-system persistence cannot be incorporated without a separate,
    unrelated object;
11. infinite mixed spectra have no compatible completion;
12. primary literature already contains the complete instability and
    positive replacement law;
13. Theorems A--C are judged elementary context and Theorem D produces no
    new calculation, bound or experimental prediction;
14. the only robust conclusion is that exact rational relations are
    experimentally undecidable.

## Paper gate

The paper is not authorized until:

1. Theorems A--C have dependency-closed proofs;
2. Theorem D is precisely defined and proves a nontrivial universal law;
3. every manuscript claim is unconditionally formalized;
4. the relation spectrum subsumes rather than merely lists existing
   recurrence results;
5. external priority is collision-complete;
6. a feasible finite-scale protocol and error budget are derived; and
7. hostile Nature review accepts “arithmetic completion of time” as physical
   content rather than terminology.

## Log

- 2026-07-30 — Frozen after dense rational/irrational rank strata killed the
  ordinary asymptotic-boundary conjecture. The new hunch treats smooth
  finite-horizon response and arithmetic infinite-time completion as
  irreducible coordinates of one temporal relation spectrum. No exact
  realization was chosen before freeze.

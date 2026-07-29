# Maximal stationary quantum recurrence law

- **ID:** `maximal-stationary-quantum-recurrence-law`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE UNIVERSAL LAW / PAPER PROOF OPEN
- **Scientific status:** `[CONJECTURE] [REDISCOVERY ATTACK OPEN]`
- **Parent:** `observer-time-recurrence-distribution-law.md`
- **Statement:** The empirical fidelity law of every stationary quantum return record is exactly
  the Haar pushforward of its atomic spectral component; this class contains every autonomous
  quantum survival record and is maximal because arbitrary nonstationary fidelity histories are
  realizable by a qubit.

## Goal

Earn the title **A universal law of quantum recurrence** by proving one maximal equation rather
than adjoining theorems with different domains. “Universal” must mean all stationary quantum
return records, including arbitrary Hilbert-space dimension and spectral type, not merely every
finite matrix in one norm.

## Frozen candidate

Let \(C:\mathbb R\to\mathbb C\) be a normalized continuous positive-definite stationary return
amplitude. By its spectral representation,
\[
 C(t)=\int_{\mathbb R}e^{itE}\,d\mu(E)
\]
for a probability measure \(\mu\). Decompose
\[
 \mu=\mu_{\mathrm{pp}}+\mu_{\mathrm c},\qquad
 p=\mu_{\mathrm{pp}}(\mathbb R).
\]
Enumerate the atoms as \((E_j,w_j)\), let
\[
 K=\overline{\{(e^{itE_j})_j:t\in\mathbb R\}}\subseteq\mathbb T^J,
 \qquad P(z)=\sum_jw_jz_j,
\]
and let \(m_K\) be normalized Haar measure. For
\[
 F(t)=|C(t)|^2,\qquad
 \Lambda_T=\frac1{2T}(F|_{[-T,T]})_*\operatorname{Leb},
\]
the candidate law is the single weak-convergence identity
\[
 \boxed{\quad
 \Lambda_T\Longrightarrow (|P|^2)_*m_K
 \quad(T\to\infty).\quad}                                      \tag{U}
\]

Required exact consequences of `(U)`:

1. **Frequent-return threshold**
   \[
   p^2=
   \sup\{\eta\in[0,1]:
     \underline{\operatorname{dens}}\{t:F(t)>\eta\}>0\}.
   \]
2. **Complete recurrence statistics:** every bounded continuous statistic of \(F\) has a
   long-time mean; its \(n\)-th moment is the \(n\)-fold zero-gap collision probability.
3. **Spectral phases:** pure point gives bounded-gap approximate return; atomless gives
   zero-density return above every positive threshold; Rajchman gives permanent escape.
4. **Observer dimension:** for finite atomic rank \(d>0\), high-return density has exponent
   \(d/2\).

Required maximality:

5. Every strongly continuous autonomous quantum survival amplitude
   \(\langle\psi,U_t\psi\rangle\) is an instance of `(U)`.
6. Every probability measure \(\mu\) is realized by an autonomous quantum system, so `(U)` loses
   no stationary survival record.
7. Every invariant-state quantum Markov autocorrelation is an instance after its canonical GNS
   contraction and minimal unitary dilation.
8. For every continuous \(f:[0,\infty)\to[0,1]\) with \(f(0)=1\), a continuously driven qubit has
   survival fidelity \(f(t)\). Hence no nontrivial recurrence conclusion can hold for arbitrary
   nonstationary quantum evolution without additional structure.

Clause 8 is part of the universality claim: stationarity is the exact boundary at which a
nontrivial universal recurrence law can begin, not an omitted sector hidden in limitations.

## Current frontier

### `[CORPUS]`

- `spectralReturnMomentMeanReal_tendsto_collisionHierarchy` proves all fidelity moments for every
  probability spectrum.
- `exists_tendsto_spectralReturnStatisticMeanReal` proves existence of every continuous
  long-time fidelity statistic.
- `atomlessProjectiveObserverTemporalPhaseLaw` proves continuum temporal dimension and
  zero-density positive-threshold return for atomless spectra.
- `exists_positive_unitFidelity_iff_cyclic` classifies perfect recurrence.
- Finite contraction, observer-graph, countable pure-point, water-clock and non-identifiability
  laws are already formalized.

The corpus does **not** yet prove the atomic-Haar pushforward law, the sharp \(p^2\)
positive-density threshold for mixed spectra, or maximality across stationary quantum records.

### `[LITERATURE]`

- Bochner/GNS spectral representation, Sz.-Nagy unitary dilation, Wiener averaging, Eberlein
  decomposition, compact-group unique ergodicity and Kac recurrence are parent theories.
- Quantum recurrence-time, monitored-return and quantum-channel Kac papers address different
  notions and narrower system classes.
- No checked source yet states `(U)` together with the sharp threshold, recurrence tomography,
  stationary quantum-process maximality and nonstationary qubit saturation.

Absence from search is not priority evidence. Full primary-source ancestry/descendancy audit
remains mandatory.

## Hostile falsifiers

Kill or replace the candidate if any one occurs:

1. a normalized positive-definite return record whose empirical fidelity measures fail to
   converge to the atomic Haar pushforward;
2. mixed spectrum with positive-density fidelity above \(p^2\), or zero lower density below it;
3. a stationary autonomous quantum survival record outside the positive-definite spectral class;
4. an invariant-state quantum Markov autocorrelation for which the GNS contraction/dilation does
   not preserve the measured return record;
5. a prior theorem equivalent to `(U)` plus threshold and maximality;
6. a physical recurrence notion claimed in the paper that is not a consequence of `(U)`;
7. failure of the qubit realization at continuous time, which would leave a wider structured
   nonstationary class unexplained.

## Open core

`[OPEN CORE]` Complete the primary-source collision audit, then prove `(U)` and clauses 1--8 as one
dependency-closed theorem without importing “stationary return record” as a definition that already
contains the conclusion.

No Lean infrastructure is authorized before the paper proof and rediscovery attack close.

## Gates

- [x] 0 → 1: exact maximal claim, parent corpus, falsifiers and open core recorded
- [ ] 1 → 2: complete paper proof; all representation and maximality clauses closed
- [ ] 2 → 3: exact Lean theorem; no `sorry`, new axiom, `opaque` or `unsafe`
- [ ] 3 → 4: Nature manuscript, proof audit, novelty audit, hostile review and PDF audit

## No-go closure

- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** live

## Log

- 2026-07-29 — Rejected the prior “universal anatomy” title because it joined different domains
  without one law. Froze `(U)` as a maximal single-law replacement and opened rediscovery attack.

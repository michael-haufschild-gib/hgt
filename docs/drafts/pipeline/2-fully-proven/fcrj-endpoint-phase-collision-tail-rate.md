# FCRJ endpoint phase-collision tail rate

- **ID:** FCRJ-PCTR
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean proof complete; Stage-3 global lint gate pending)
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md` · Conjecture loop 60
- **Statement:** Fixed finite physical FCRJ packet has explicit ultraviolet-tail error controlled
  exactly by pairwise endpoint chord denominators.

## Goal

For distinct unit modes `z_x=fourier_1(x)`, signed endpoint jumps `j_x`,

```text
U_n = sum_x j_x z_x^n,
J   = sum_x |j_x|^2,
C   = sum_(x != y) 2 |j_x| |j_y| / |1-conj(z_x)z_y|,
```

prove for every integer `N>=1`

```text
| N sum_(n>N) |U_n|^2/n^2 - J |
  <= J/(N+1) + N C/(N+1)^2.                           (PCR1)
```

Endpoint differentiation should give the raw FCRJ character-energy form

```text
| N sum_(n>N)|A_n|^2 - A^2 J/(4 pi^2) |
  <= A^2/(4 pi^2) [J/(N+1)+N C/(N+1)^2].             (PCR2)
```

## Gates

- [x] 0 → 1 in-progress: corpus search, primary-literature audit, frozen source statement
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile constant audit
- [ ] 2 → 3 formalized: exact Lean theorem, targeted build, axiom and lint gates
- [ ] 3 → 4 publication-ready: independent expert priority review

## Corpus frontier `[CORPUS]`

1. `tendsto_finiteExponentialPencil_cesaro_norm_sq` proves only asymptotic diagonal survival.
2. `tendsto_xiPhysicalPrimeLogCharacterAmplitude_ultravioletTail` proves exact fixed-packet limit,
   but no finite-`N` or moving-packet rate.
3. `geometric_phase_norm_ratio_lower_bound` controls a different finite geometric quotient.
4. Corpus search found Dirichlet/Abel tail machinery and recurrence bounds, but no inverse-square
   unit-phase tail bound with denominator `|1-w|`, no finite-pencil collision budget `(PCR1)`, and
   no physical FCRJ specialization `(PCR2)`.

## External frontier `[LITERATURE]`

Wiener lemmas for Fourier coefficients of measures, including arithmetic subsequences, are
classical; see Cuny--Eisner--Farkas, *Wiener's lemma along primes and other subsequences*,
arXiv:1701.00101.  Fourier jump/Gibbs theory likewise predicts `1/n` coefficient scale.  The
one-phase estimate below is elementary Abel summation and is not claimed new.  Targeted search
found no source stating `(PCR1)--(PCR2)` for signed clipped prime-log aperture endpoints.  Novelty
claim is restricted to exact physical collision budget and its moving-packet route consequence.

## Conjecture loop A — separation by minimum chord

`[CONJECTURE]` Bound error only by minimum separation
`delta=min_(x!=y)|1-conj(z_x)z_y|` and total jump variation squared.

Hostile verdict: `TOO COARSE`.  It is true when at least two nodes exist, but `delta` is undefined
for singleton node sets and one near-collision charges every pair at worst scale.  It obscures
which endpoint pairs create loss and is unsuitable for arithmetic packet decomposition.

Failure-driven replacement: retain pairwise denominators and sum their actual weighted costs.

## Conjecture loop B — pairwise collision budget

`[CONJECTURE] [FROZEN 2026-08-27]` Equations `(PCR1)--(PCR2)` hold with exact collision budget `C`.

### Paper proof plan

For `|w|=1`, `w!=1`, and `M>=1`, absolute convergence and a one-step Abel telescope give

```text
(1-w) sum_(n>=M) w^n/n^2
 = w^M/M^2
   + sum_(n>=M+1) w^n(1/n^2-1/(n-1)^2).
```

The second scalar variation telescopes to `1/M^2`; hence

```text
|sum_(n>=M)w^n/n^2| <= 2/(M^2 |1-w|).                 (PCR3)
```

Expand `|U_n|^2` over ordered endpoint pairs.  Injectivity of `fourier_1` makes every off-diagonal
ratio `conj(z_x)z_y` nontrivial.  Apply `(PCR3)` pairwise with `M=N+1`.  Diagonal term is
`J N sum_(n>N)n^-2`; integral/telescoping bounds put it between `J N/(N+1)` and `J`, so its error
from `J` is at most `J/(N+1)`.  Triangle inequality yields `(PCR1)`.  Exact endpoint
differentiation gives `(PCR2)` termwise.

### Hostile audit

- Bound remains meaningful with one endpoint node: ordered off-diagonal sum is empty.
- Ordered-pair convention matches full norm-square expansion; factor `2` belongs to one-phase tail
  estimate, not an unproved symmetry reduction.
- No uniformity is asserted without controlling `C`; near-collisions correctly blow up.
- Sufficient moving-packet condition is explicit: `C_M=o(N_M)` forces normalized tail error to
  zero along `N_M`, while `C_M=O(N_M)` gives only bounded error.
- The theorem still does not prove required arithmetic collision bound.  It replaces vague
  uniformity by exact source quantity whose growth must be estimated.

Verdict: `PROVED ON PAPER`.  Generic `(PCR3)` is classical infrastructure;
source-specific `(PCR1)--(PCR2)` is candidate-new and closes analytic side of moving-packet
uniformity once arithmetic collision budget is supplied.

## Open core

Lean formalization is complete in
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointPhaseCollisionTailRate.lean`.
Direct checking, targeted module build, and `#print axioms` audit pass; capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`.  Global formal lint is temporarily blocked by
unrelated concurrent untracked modules absent from `RHTower.lean`, so Stage 3 is not claimed yet.
Next source conjecture must bound physical `C_M` from prime-log endpoint separation or exploit
cluster cancellation beyond absolute pairwise cost.

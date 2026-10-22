# Primorial zero-edge renewal process law

- **ID:** `primorial-zero-edge-renewal-process-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / MULTIPLICATIVE NUMBER THEORY / DETERMINISTIC ARITHMETIC CHAOS /
  POINT-PROCESS RENEWAL
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED] [SURVIVES PRELIMINARY ATTACK]`
- **Statement:** After sampling the prime cutoff in natural density, the fully unfolded divisors
  nearest the square root of the primorial form a unit Poisson process; every fixed block of
  consecutive cutoffs yields independent copies, and the corresponding prime partitions have
  asymptotically zero overlap.

## Goal

This card replaces a bulk local-REM surrogate by the actual zero-edge object selected by
prime-product resonance. It is independent of RH and does not encode a zeta zero or a desired
positivity conclusion.

Let `p_j` be the `j`-th prime and put

```text
P_n = product_(j<=n) p_j,
Sigma_n^2 = sum_(j<=n) (log p_j)^2,
C_n = {-1,+1}^n /(sigma ~ -sigma),
M_n = #C_n = 2^(n-1).                                             (1)
```

For `c=[sigma] in C_n`, define

```text
E_n(c) = |sum_(j<=n) sigma_j log p_j| / Sigma_n
       = |log(D_sigma^2/P_n)| / Sigma_n,                           (2)
```

where `D_sigma` is either complementary divisor selected by `sigma`. Unique factorization makes
the values in `(2)` simple on `C_n`. Let

```text
g_0 = sqrt(2/pi),
Z_n = sum_(c in C_n) delta_[M_n g_0 E_n(c)]                        (3)
```

be the deterministically unfolded zero-edge point measure on `[0,infinity)`.

There can be no nondegenerate convergence in law of the deterministic measures `Z_n` without an
explicit source of sampling. For `0<a<b<infinity`, let `J_N` be uniform on

```text
{ceil(aN),...,floor(bN)}.                                         (4)
```

All probability below is solely the cutoff sampling `(4)`.

## The conjecture

`[ACTIVE CONJECTURE]` For every `0<a<b<infinity` and every fixed `m>=0`,

```text
(Z_(J_N), Z_(J_N+1), ..., Z_(J_N+m))
  => (Pi_0, Pi_1, ..., Pi_m),                                     (Q1)
```

where `Pi_0,...,Pi_m` are independent homogeneous Poisson point processes of intensity one on
`[0,infinity)`.

The convergence is jointly overlap-marked. For sign classes at the same cutoff put

```text
Q_n([sigma],[tau]) = |n^(-1) sum_(j<=n) sigma_j tau_j|.            (5)
```

For every `L>0` and `epsilon>0`, the probability that, for some `0<=r<=m`, two distinct points of
`Z_(J_N+r)` in `[0,L]` are carried by classes with `Q_(J_N+r)>=epsilon` tends to zero.

Equivalently, for every fixed `m`, the closest-divisor gaps at `m+1` consecutive primorials obey
an asymptotic renewal law. In particular, if

```text
G_n = min supp(Z_n),                                               (6)
```

then under `(4)`

```text
(G_(J_N),...,G_(J_N+m)) => (Y_0,...,Y_m),                          (Q2)
```

where the `Y_r` are independent `Exp(1)` variables. Equation `(Q2)` is a consequence, not a
replacement, of the point-process statement `(Q1)`.

## Why this is a universal law rather than an isolated estimate

The conjecture asserts three structures at once.

1. **Zero-edge universality.** The optimal multiplicative balancing of the first `n` primes has
   the random-energy scaling `Sigma_n 2^(-n)` and the complete Poisson gap hierarchy.
2. **Renewal under adjoining a prime.** Despite the nesting `P_n | P_(n+1)`, every fixed block of
   successive zero-edge spectra becomes independent after unfolding.
3. **Geometric erasure.** Prime partitions generating adjacent near-square-root divisors become
   orthogonal in Hamming geometry; the arithmetic energy and the hypercube geometry decouple at
   the zero edge.

This creates a deterministic arithmetic universality class. It is stronger than an asymptotic for
the single closest divisor, stronger than pair correlation, and qualitatively different from
ordinary central-limit theory.

## Exact renewal mechanism

Write the signed, unquotiented sum at cutoff `n` as

```text
S_n(sigma) = sum_(j<=n) sigma_j log p_j.                           (7)
```

Adjoining the next prime gives the exact identity

```text
S_(n+1)(sigma,+1) = S_n(sigma) + log p_(n+1),
S_(n+1)(sigma,-1) = S_n(sigma) - log p_(n+1).                     (8)
```

Hence the zero edge at cutoff `n+1` is obtained by sampling the signed cutoff-`n` spectrum in
microscopic windows around the two moving levels `+/- log p_(n+1)`. Iterating `(8)`, the zero
edges at `n,...,n+m` are obtained from cutoff `n` at the finite target family

```text
sum_(r=1)^k epsilon_r log p_(n+r),
0<=k<=m, epsilon_r in {-1,+1}.                                    (9)
```

After normalization by `Sigma_n`, these targets approach the central region at polynomial scale,
but their mutual separations are exponentially large on the unfolded scale `2^n`. Thus `(Q1)` is
the assertion that the moving microscopic windows in `(9)` decorrelate completely. This is the
specific mechanism to prove or falsify; “primes look random” is not a mechanism.

## Internal frontier

- `[CORPUS]` `DirichletPolynomialSincEnergy.lean` isolates finite-time defects in explicit
  off-diagonal prime-product frequencies. It does not estimate the zero-edge frequency count.
- `[CORPUS]` `UniversalPhaseCoherenceMinimax.lean` gives an ambient worst-frequency recurrence
  clock. It does not give arithmetic statistics for the fixed vector `(log p_j)`.
- `[LOCAL-RESEARCH]` `prime-log-level-two-entropy-budget-law.md` identifies the full signed
  resonance pressure as the open source theorem. The Boolean zero edge in `(3)` is its first
  exponential-size static shell.
- `[LOCAL-RESEARCH]` `primorial-divisor-deterministic-local-rem-law.md` concerns rooted local
  statistics around a fixed positive normalized energy. That bulk law is now backlogged because it
  does not control the zero edge selected by the Fourier kernel.
- `[LOCAL-RESEARCH]` `combination-mode-baker-reducibility.md` explains why fixed-dimensional Baker
  bounds do not provide cofinal zero-edge statistics.

The exact internal residue is the distribution, over prime cutoff, of squarefree divisors of
`P_n` inside multiplicative intervals of relative width `asymp Sigma_n 2^(-n)` about `sqrt(P_n)`.

## External frontier and anti-theatre audit

1. `[LITERATURE]` Borgs--Chayes--Mertens--Nair prove Poisson local-REM statistics and overlap
   decorrelation for number partitioning with i.i.d. random weights. Their probability is over the
   weights. It neither specializes nor quenches to the single deterministic triangular array
   `(log p_j)`.
2. `[LITERATURE]` Their growing-energy theorem identifies a breakdown scale for the same random
   model. It does not address deterministic cutoff renewal or divisors of primorials.
3. `[LITERATURE]` Raghavan determines the extremal size of subsets of `[N]` with distinct subset
   products. The first `n` primes already have exact subset-product distinctness; `(Q1)` begins at
   exponentially fine approximate equality.
4. `[LITERATURE]` Pollack--Pomerance's “primorials and Poisson” law concerns primorial divisibility
   of `phi(k)` for random integers `k`, not divisors nearest `sqrt(P_n)`.
5. Fixed-dimensional Kronecker and infinite-torus minimality theorems supply orbit closure and
   equidistribution, not the static zero-edge spectrum or its cutoff renewal.

Exact-object searches on 2026-07-20 found no theorem or conjecture for the cutoff-averaged point
process `(3)`, no limiting law for divisors nearest `sqrt(P_n)`, and no independent-renewal law
across consecutive primorials. Search absence is not a priority proof. The status remains
`[NOVELTY UNVERIFIED]` until a proof exists and citation ancestry and descendancy have been audited.

Primary comparison sources:

- C. Borgs, J. Chayes, S. Mertens, and C. Nair,
  *Proof of the local REM conjecture for number partitioning I: Constant energy scales*,
  <https://arxiv.org/abs/cond-mat/0501760>.
- C. Borgs, J. Chayes, S. Mertens, and C. Nair,
  *Proof of the local REM conjecture for number partitioning II: Growing energy scales*,
  <https://arxiv.org/abs/cond-mat/0508600>.
- R. Raghavan, *Sharp Bounds for Sets with Distinct Subset Products*,
  <https://arxiv.org/abs/2501.02695>.
- P. Pollack and C. Pomerance, *Phi, Primorials, and Poisson*,
  <https://arxiv.org/abs/2001.06727>.

## Hostile falsity audit

### Deterministic convergence fallacy removed

A deterministic sequence of point measures cannot converge in distribution to a nondegenerate
Poisson process. The cutoff sampling `(4)` is therefore structural. Any formulation omitting it is
false, not stronger.

### The nesting may destroy renewal

Equation `(8)` is also the main threat. Consecutive spectra share every old prime and may retain a
nonzero limiting covariance. Clause `(Q1)` is false if the moving windows `(9)` remember this nested
ancestry.

### Near-equal-weight degeneration

Most `log p_j` are `log p_n+O(1)`. The coefficient of variation of the weights tends to zero, so
the fixed prime array is not even a routine deterministic instance of the i.i.d. parent model.
Magnetization layers may survive at the exponential edge and falsify Poisson statistics.

### Arithmetic clustering

Unique factorization removes exact collisions but permits exponentially close ratios of coprime
squarefree integers. A positive-density family of such ratios, or a persistent higher-order
multiplicative cluster, falsifies the Poisson factorial moments.

### Exact falsifiers

The conjecture is false if any one of the following holds.

1. The first averaged edge intensity has a limit different from one or no limit.
2. Some fixed factorial moment differs from the Poisson value.
3. Two macroscopic cutoff windows `(a,b)` give different limiting laws.
4. Consecutive cutoffs retain nonzero limiting covariance.
5. A positive proportion of bounded edge clusters has overlap bounded away from zero.

The present verdict is `SURVIVES PRELIMINARY ATTACK`. This is not evidence that `(Q1)` is true.

## Exact open core

The first frontier implication is already an exponentially thin divisor theorem. For every
`0<a<b<infinity` and every `x>=0`, prove

```text
1/#I_N * sum_(n in I_N)
  #{c in C_n : E_n(c) <= x/(M_n g_0)}  -> x,                      (10)

I_N={ceil(aN),...,floor(bN)}.
```

Equivalently, the average number of divisors `D | P_n`, modulo `D <-> P_n/D`, satisfying

```text
|log(D^2/P_n)| <= x Sigma_n/(M_n g_0)                            (11)
```

tends to `x`. The central limit theorem gives the density `g_0` only in fixed-width intervals; it
does not reach the exponentially shrinking width in `(11)`.

After `(10)`, the first genuinely renewal-sensitive gate is the mixed two-cutoff factorial moment:
for bounded continuity sets `A,B subset [0,infinity)`, prove

```text
1/#I_N * sum_(n in I_N) Z_n(A) Z_(n+1)(B) -> |A| |B|.            (12)
```

The same-cutoff factorial moments, the mixed moments generated by `(9)`, and overlap removal then
form a precise hierarchy. No claim on this card is paper-proved.

## Gates

- [x] exact zero-edge process and legitimate source of randomness defined
- [x] bulk/edge mismatch in the predecessor card corrected
- [x] random-weight, subset-product, and title-collision parents separated
- [x] exact recurrence mechanism and falsifiers stated
- [x] first Google/arXiv exact-object search completed
- [ ] prove averaged edge intensity `(10)`
- [ ] prove same-cutoff Poisson factorial moments and overlap removal
- [ ] prove mixed-cutoff factorization through `(8)--(9)`
- [ ] deduce the joint point-process renewal law `(Q1)`
- [ ] complete proof-stage citation ancestry and descendancy audit
- [ ] 1 -> 2 fully-proven: dependency-closed paper proof
- [ ] 2 -> 3 formalized: exact unconditional Lean theorem and axiom audit

## Log

- 2026-07-20 -- Created by hostile-testing the bulk primorial local-REM card against the actual
  prime-phase Fourier kernel. The predecessor missed the zero edge, and a deterministic edge point
  process could not have a nondegenerate law without explicit sampling. Cutoff-density sampling
  fixes the second defect. The exact recursion under adjoining a prime then exposes the stronger
  renewal conjecture across consecutive primorials. Preliminary exact-object searches found only
  random-weight local REM, exact subset-product extremal theory, and unrelated primorial Poisson
  laws. Verdict: `[CONJECTURE] [NOVELTY UNVERIFIED] [SURVIVES PRELIMINARY ATTACK]`.

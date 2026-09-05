# Ordered deletion sums: domain and exact dilation boundary

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** A source-construction check within the current deletion candidate. No RH implication or novelty claim.

## Proved domain

Put `a_P(n)=1-P[P∣n]`, with positive integer modulus `P`. For positive integers `P,Q`, the chronological sums

`Σ_{1≤m<n≤N} a_P(m)m^(-s) a_Q(n)n^(-conjugate(t))`

converge as `N→∞` whenever `Re(s)>0`, `Re(t)>0`, and `Re(s)+Re(t)>1`. No zero assumption enters. In particular the Hermitian self level exists for every `Re(s)>1/2`. This means convergence alone cannot distinguish zeros or force their real part.

The statement concerns chronological cutoffs. It does not license arbitrary rearrangements or assert absolute summability away from zeros.

### Paper proof

The coefficient prefixes are bounded, since their sum through `N` is `N mod P`. Abel summation gives a convergent, bounded inner weighted prefix `S_n=Σ_{m≤n}a_P(m)m^(-s)` for `Re(s)>0`. Write `g_n=S_{n-1}n^(-conjugate(t))`. Then `g_n→0`, and its increment splits exactly into

`a_P(n)n^(-s)n^(-conjugate(t)) + S_n[(n+1)^(-conjugate(t))-n^(-conjugate(t))]`.

The first term is absolutely summable because the sum of real parts exceeds one. The second is absolutely summable because `S_n` is bounded and the Dirichlet kernel has summable increments for positive real part. A second Abel summation, now against `a_Q`, proves chronological convergence.

### Lean evidence

`formal/GaloisForLFunctions/RHTower/EulerDeletionQuasiShuffleCrossDomain.lean` contains the finite-variation Abel lemma and the two domain capstones:

- `RHTower.tendsto_chronologicalCrossPrefix_eulerDeletion_domain`
- `RHTower.tendsto_chronologicalSecondPrefix_eulerDeletion_domain`

The formal parameter `q` means actual modulus `q+1`. All natural parameters, including the zero deletion channel at modulus one, are covered. Scratch compilation and the targeted leaf build passed. Scratch axiom inspection reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact dilation boundary

For arbitrary complex sequences `x,y`, define

`W_{p,q}^N(x,y)=Σ_{1≤n≤floor(N/q)} Σ_{1≤m≤floor((qn-1)/p)} x_m y_n`.

The Lean-proved exact identity is

`H_N(a_p x,a_q y)=W_{1,1}^N(x,y)-p W_{p,1}^N(x∘p,y)-q W_{1,q}^N(x,y∘q)+pq W_{p,q}^N(x∘p,y∘q)`.

Here `(x∘p)_m=x_{pm}`. The strict floor keeps precisely the pairs `pm<qn`; equality pairs are excluded. Expand the outer deletion and then the inner deletion, using the existing finite divisor reindexing theorem. This is an identity for arbitrary inputs, not a zero-specific compatibility condition. Its purpose is to retain the complete ordering boundary when testing any further proposed constraint.

### Actual Dirichlet source and its grouped limit

For `x_m=m^(-s)` and `y_n=n^(-t)`, pull the dilation factors out of each wedge. The four coefficients become `1`, `-c_p(s)`, `-c_q(t)`, `c_p(s)c_q(t)`, where `c_p(s)=p*p^(-s)`. For the Hermitian cross level, conjugate the outer weight and its factor, giving `1`, `-c_p(s)`, `-conjugate(c_q(t))`, `c_p(s)conjugate(c_q(t))`.

`EulerDeletionQuasiShuffleOrderedDilation.lean` proves this specialization, identifies it with the existing zero-indexed chronological cross prefix, and proves that the complete four-term expression converges on the domain above. This last result keeps the terms grouped at each cutoff. It assumes no separate wedge limits.

The exact declarations in namespace `RHTower.DeletionOrderedDilation` are:

- `le_strict_floor_iff`: equivalence with the strict lattice inequality.
- `ordered_deletion_eq_wedges`: arbitrary input sequences.
- `ordered_dirichlet_deletion_eq_wedges`: two independent complex exponents.
- `ordered_hermitian_deletion_eq_wedges`: the actual conjugated outer coordinate.
- `hermitianDilationCombination_eq_crossPrefix`: exact agreement at every cutoff.
- `hermitianDilationCombination_converges`: convergence of the complete expression without a zero assumption.

## Literature collision audit

The underlying ordered periodic-coefficient double series is published machinery. Kelliher–Masri, [*Analytic continuation of multiple Dirichlet series of Euler–Zagier type*](https://math.ucr.edu/~kelliher/papers/LFunctionsFull.pdf), equation (1.4) and §9.2, explicitly treats strict ordered multiple series and periodic coefficients. Our coefficients fit this definition with exponents `(s,conjugate(t))`. This identifies the analytic object; it does not identify or prove the candidate's still-missing refinement law.

Komori–Matsumoto–Tsumura, [*Functional equations for double L-functions and values at non-positive integers*](https://www.math.nagoya-u.ac.jp/~kohjimat/IJNT11.pdf), also studies periodic-coefficient double series. Its coordinates and coefficient indexing differ from the present chronological expression. Its functional equations are not used here.

Corpus searches combined `scripts/formal_tools.py research` with `rg` and proof inspection of `DirichletAbelConvergence`, `DirichletIncrementSummable`, and the `EulerDeletionQuasiShuffle*` leaves. No search miss is treated as a novelty certificate.

## Research consequence

Comparing analytic continuations of the same function cannot supply an additional constraint only at zeros: on a connected common domain, agreement on an open set extends throughout that domain. The current architecture therefore still owes a source-derived refinement law before continuation. This note neither supplies that law nor retires every possible cylinder-signature construction.

## Validation

Both leaves passed scratch compilation and targeted `lake build` runs, and are imported in `RHTower.lean`. Scratch axiom inspection of the core theorems reported only standard Lean axioms. `python3 scripts/formal_tools.py lint` passed with existing large-file warnings. No full or umbrella build, external numerical experiment, added axiom, or computational proof was used. The complete paper proof above has no open mathematical dependency; the claimed new RH architecture remains unproved.

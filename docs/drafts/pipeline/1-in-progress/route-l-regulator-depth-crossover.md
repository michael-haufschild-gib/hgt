# Route L: original regulator--depth crossover

- **ID:** L-C29
- **Date:** 2026-09-11
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; paper argument below, two shell lemmas scratch-checked
- **Depends on:** [C28 complete integrand admission](../2-fully-proven/route-l-complete-integrand-admission.md), 45 audited Lean theorems; unrelated global lint errors remain
- **RH status:** unproved; no source-to-Sonin agreement supplied

## Exact target

Keep C28's actual original tail operator `T_M`, unchanged spectral point
`w`, internal orders `k,l`, fixed dilation six and original successor
normalizer `N_M`. Write `K` for C27's nonzero normalized second-boundary
limit when the top Xi-jet product is nonzero. Let `epsilon_M>0`,
`epsilon_M -> 0` and `M*epsilon_M -> tau` for finite real `tau`.

Conjecture:

`N_M * AbelDefect(epsilon_M,6,T_M) / epsilon_M^2 -> 6^(-tau)*K`.

Thus the ordered limit corresponds to `tau=0`. Every finite positive
`tau` retains a nonzero response at a top jet. The regime
`M*epsilon_M -> +infinity` should instead give zero. The latter would
erase this normalized measurement and cannot be silently identified
with the ordered fixed-cutoff reader. This is a proposed classification
of the same complete source's limiting measurements, not an RH selector.

## Source-derived proof attempt

The current Lean corpus supplies the exact identity, at each admitted
cutoff and positive regulator:

`AbelDefect(epsilon,6,T_M)/epsilon^2`
`= [(6^epsilon-1)/epsilon] * [1/(epsilon*Z_epsilon)]`
`  * sum_(6 divides a) a^(-epsilon) diag(T_M)(a)`.

Both prefactors have existing limits `log(6)` and one. This formula uses
`6^epsilon-1`, as required by the actual compression-minus-projection
reader, and preserves the Gibbs partition `Z_epsilon`.

At literal depth `m`, put
`H_m(epsilon)=sum_(6^m<=a<6^(m+1),6 divides a) a^(-1-epsilon)`.
Every retained coordinate obeys `1 <= a/6^m < 6`. Consequently

`6^(-epsilon)*H_m(0) <= 6^(m*epsilon)*H_m(epsilon) <= H_m(0)`.

This sandwich gives joint convergence to `log(6)/6` when `m->infinity`
and `epsilon->0`, using C27's actual harmonic-shell theorem; no new
Riemann-sum approximation or numerical estimate is needed.

Regroup by `m=M+j`. Exact successor-normalizer multiplication extracts
`q^j`, while the Gibbs weight extracts `6^(-M*epsilon)` and leaves
`6^(-j*epsilon)`. The latter has modulus at most one for positive
regulator. C27's normalized complete multiplier is bounded and tends
to `2*mu(successor(6))`; its geometric moving-tail majorant therefore
still dominates every `j`. Dominated summation gives the same geometric
sum multiplied by `lim 6^(-M*epsilon)`. This is `6^(-tau)` for finite
`tau`, and zero for infinite `tau` if the remaining sum stays bounded.

All divisibility-filtered sums require C28's full integrated-norm
admission before this regrouping. For positive regulator the additional
coordinate weight has modulus at most one, so it preserves that
majorant. No discarded, unadmitted coordinate integral may enter the
operator identification.

## Remaining obligations

`lake env lean /tmp/route_l_regulator_depth_crossover.lean` passed without
errors or warnings for `deningerGammaSixNormalizedGibbsShell_bounds`
and `tendsto_deningerGammaSixNormalizedGibbsShell_joint`. They retain
the actual integer shell and divisibility filter. This is scratch
verification of those two lemmas, not a completed operator crossover
or an audited new repository module. The owned scratch process completed.

Establish the weighted original-coordinate shell identity and the actual Gibbs-domain bridge for every
sufficiently late original cutoff; prove the moving-depth dominated
sum with its regulator factor retained; specialize at every Xi divisor.
Audit finite diagonal repairs separately (they disappear at late
cutoffs). Do not claim a finite-rank repair theorem or a physical
Sonin/Burnol identification from this crossover law.

## Corpus search audit

The deep search for geometric moving tails, Abel weights and normalized
two-parameter cutoffs returned 20 candidate statements and 20 method
summaries, all inspected. Coverage remained partial (generation
`823340`, semantic `2196271/2336767`). Its proposed ingredient pair was
a modified-Hurwitz exponential tail bound plus a different cutoff
exponent tending to infinity. These concern different sources and do
not preserve the present normalizer or coupled product `M*epsilon`;
the suggested transfer is rejected. The direct starting points are
the actual Abel-defect factorization, Gibbs diagonal identity, and
C27's shell and normalized-tail theorems. No computation is used.

A broad search for adiabatic mechanisms returned the July 2026
[dressed-frame counterdiabatic paper](https://arxiv.org/html/2607.28383v1).
Its laboratory commutator equation and discussion were inspected. The
auxiliary generator changes the effective Hamiltonian whose spectrum
is followed; it does not identify the original and dressed observables.
Therefore it supplies no transfer of the fixed original-anchor reader.
Any adaptation would still need an independently derived source-domain
and reader-transport law. The present crossover attack uses neither
its variational construction nor its numerical examples.

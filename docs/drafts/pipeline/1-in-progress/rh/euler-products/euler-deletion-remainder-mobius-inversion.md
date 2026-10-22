# Arithmetic inversion of the retained mixed remainder

- **Stage:** 1-in-progress
- **Type:** completed reconstruction [BRIDGE]; arithmetic RH refinement law remains unresolved
- **Frozen RH target:** a source-derived refinement equality, not merely another zero detector.

## Source and candidate tests

The starting point is the Lean-proved infinite mixed decomposition and its actual remainder `W_p=p^(1-s) sum_(n>=1)n^(-s) R_conj(s)(pn)`. The corpus mechanism is multiples-coordinate inversion (`Sieve.SelbergDiagonalLowerAsymptotic.sum_moebius_mul_selbergMultiplesInner`), inspected through both search and its finite divisor-sum proof. Finite recovery/carry and Hasse-packet mechanisms were also inspected; they require their own boundedness or atomic-admission hypotheses and do not provide the missing zero constraint.

**Test A — cancellation candidate.** Does `sum_(p>=1)mu(p) W_p/p=0` follow from a zeta zero in `Re(s)>0`, `s!=1`? The test keeps every arithmetic remainder; no leading term is discarded. It is not assumed true. The formal analytic prerequisite is absolute convergence of the entire double sum.

**Conjecture B — exact reconstruction.** For each positive integer `m`,

`sum_(p>=1)mu(p) W_(mp)/p = m^(1-s) R_conj(s)(m)`.

The proposed proof regroups the actual product index `pn`; the sum of `mu(p)` over divisors of `pn` removes every index except one. The two-dimensional absolute majorant is a product of convergent series with exponent `2 Re(s)+1>1`, supplied by the already proved remainder bound. No cancellation estimate for an unsmoothed Mobius sum is assumed.

**Conjecture C — surviving nonzero mass.** At a zeta zero with `Re(s)>0`, the `m=1` reconstructed value is `(1/2)-1/(1-conj(s))`, whose norm is strictly greater than `1/2`. Consequently the complete remainder family cannot vanish and its weighted absolute mass must exceed `1/2`. This is a candidate obstruction to Test A, not an exclusion of zeros.

## Exact outcomes

B and C are proved in Lean. The complete weighted remainder family reconstructs each original cutoff error, with every infinite regrouping justified by absolute convergence. Thus Test A cannot hold at a positive-real-part zero different from one: its left side has norm greater than `1/2`. The positive survivor is the full reconstruction identity, not merely rejection of cancellation.

D is also proved in Lean, including the boundary extension `Re(s)=1`, `s!=1`. The multiplier only needs norm at least one; strict expansion is unnecessary. The extension follows from the same decay and iteration argument below. This is a pointwise theorem about any zero, including hypothetical off-line zeros; it is not a proof that such zeros exist or that a contradiction argument is impossible.

An independently proved vanishing law restricted to hypothetical strict-right zeros would contradict D and exclude those zeros. That additional source theorem is still missing. Consequently the original arithmetic RH target is not retired, and no RH implication or proof of impossibility of all arithmetic identities is claimed.

No numerical experiment is planned for these algebraic identities: divisor regrouping decides them by reasoning. Computations will be used only if a further question has an outcome not determined by that reasoning.

## Stronger independent conjecture exposed by reconstruction

**Conjecture D — corrected refinement still carries a nonzero term.** Put `A_p=p^(2-2 Re(s))` and retain the literal correction after subtracting the explicit amplitude, quadratic, and boundary parts:

`C_(p,q)=W_(pq)-W_p-A_p W_q+A_p W_1`.

For every zeta zero with `0<Re(s)<1` and every integer `p>1`, there is a positive integer `q` with `C_(p,q)!=0`. This does not rename Test A: it is a stronger independent claim about the entire source-modulus family. The theorem concerns the displayed remainder expression; its interpretation inside the earlier mixed-sum decomposition uses that decomposition's admitted domain `1/2<=Re(s)<1`.

## Dependency-closed paper proof

Put `sigma=Re(s)>0`, `s!=1`, `g(n)=n^(-s) conjugate(R_s(n))`, and `K=|s(s+1)|/(sigma+1)`. The previously proved ordinary remainder estimate gives `|g(n)|<=K n^(-2 sigma-1)` for every positive integer `n`. Exactly `W_m/m=sum_(n>=1)g(mn)`. For fixed `m`, the double series of `|g(mpn)|` is bounded by `K m^(-2 sigma-1) (sum_(n>=1)n^(-2 sigma-1))^2`, a finite quantity. Since `|mu(p)|<=1`, the signed double series is absolutely convergent too. Grouping by `k=pn` and using `sum_(p|k)mu(p)=1` for `k=1`, zero otherwise, yields `sum_(p>=1)mu(p) W_(mp)/(mp)=g(m)`. Multiplying by `m` gives B.

At unit cutoff, `g(1)=1/2-conjugate(zeta(s))-1/(1-conjugate(s))`. At a zero it becomes `-(1+conjugate(s))/(2(1-conjugate(s)))`. The difference of squared numerator and denominator norms before the factor two is `|1+conjugate(s)|^2-|1-conjugate(s)|^2=4 sigma>0`. This proves C and, by the triangle inequality, `sum_(p>=1)|W_p/p|>1/2`. Absolute convergence of this outer norm sum follows from the same product majorant.

The row majorant also proves `|W_m|<=K (sum_(n>=1)n^(-2 sigma-1)) m^(-2 sigma)`, hence `W_m->0`. If `C_(p,q)=0` for every positive `q`, taking `q->infinity` gives `W_p=A_p W_1`, so the identity reduces to `W_(pq)=A_p W_q`. Iteration gives `W_(p^n q)=A_p^n W_q`. For `sigma<=1`, `|A_p|>=1`; the left side tends to zero while its norm is at least `|W_q|`. Hence every positive-index `W_q` is zero, contradicting C. This proves D and its closed boundary extension. No sharper remainder asymptotic or conjectural cancellation estimate is used.

## Corpus and novelty scope

[Search evidence](../../euler-deletion-remainder-mobius-inversion-searches.json) retains 31 mechanism queries, including unsuccessful queries, caps and exploration hits. This is broad brainstorming, not exhaustive corpus coverage. The finite multiples-coordinate inverse supplied the mechanism; the actual analytic remainder bound supplied its admission. Generic Möbius inversion is already present in the corpus and in [Forster's analytic-number-theory notes, chapter 3](https://www.mathematik.uni-muenchen.de/~forster/v/ann/annth_all.pdf). No literature-wide novelty claim is made for this specialization or its refinement consequence.

[Formal certificate](../../../3-formalized/euler-deletion-remainder-reconstruction.md) records the precise checked declarations and audit scope. The original RH implication remains missing.

## Grouping primes or zeros

A proof by classes remains possible if the classes exhaust the nontrivial zeros and each class has its own proved exclusion of off-line zeros. Prime classes do not automatically give zero classes. The inspected corpus `CoefficientDecimationSieve` makes finite prime-group filters exact projections onto integers coprime to the associated primorial; its divisor expansion retains products involving several prime choices. Thus dropping cross-group terms would change the source. D applies to each zero separately, so subdivision does not remove the nonvanishing obligation. A class-specific contradictory vanishing law would still need an independent arithmetic proof; no such classification or law was constructed here.

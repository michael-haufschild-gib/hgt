# Arithmetic inversion of the retained mixed remainder

- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP; [BRIDGE] to the unresolved arithmetic refinement law
- **Frozen RH target:** a source-derived refinement equality, not merely another zero detector.

## Source and candidate tests

The starting point is the Lean-proved infinite mixed decomposition and its actual remainder `W_p=p^(1-s) sum_(n>=1)n^(-s) R_conj(s)(pn)`. The corpus mechanism is multiples-coordinate inversion (`Sieve.SelbergDiagonalLowerAsymptotic.sum_moebius_mul_selbergMultiplesInner`), inspected through both search and its finite divisor-sum proof. Finite recovery/carry and Hasse-packet mechanisms were also inspected; they require their own boundedness or atomic-admission hypotheses and do not provide the missing zero constraint.

**Test A — cancellation candidate.** Does `sum_(p>=1)mu(p) W_p/p=0` follow from a zeta zero in `Re(s)>0`, `s!=1`? The test keeps every arithmetic remainder; no leading term is discarded. It is not assumed true. The formal analytic prerequisite is absolute convergence of the entire double sum.

**Conjecture B — exact reconstruction.** For each positive integer `m`,

`sum_(p>=1)mu(p) W_(mp)/p = m^(1-s) R_conj(s)(m)`.

The proposed proof regroups the actual product index `pn`; the sum of `mu(p)` over divisors of `pn` removes every index except one. The two-dimensional absolute majorant is a product of convergent series with exponent `2 Re(s)+1>1`, supplied by the already proved remainder bound. No cancellation estimate for an unsmoothed Mobius sum is assumed.

**Conjecture C — surviving nonzero mass.** At a zeta zero with `Re(s)>0`, the `m=1` reconstructed value is `(1/2)-1/(1-conj(s))`, whose norm is strictly greater than `1/2`. Consequently the complete remainder family cannot vanish and its weighted absolute mass must exceed `1/2`. This is a candidate obstruction to Test A, not an exclusion of zeros.

## Proof status

Conjectures are frozen before new Lean code. Exact reconstruction, analytic admission, the explicit zero specialization, and its norm consequence require paper and Lean closure. A successful [BRIDGE] will not be relabelled as the arithmetic RH implication. No route is retired and no claim about all possible annihilators is made.

No numerical experiment is planned for these algebraic identities: divisor regrouping decides them by reasoning. Computations will be used only if a further question has an outcome not determined by that reasoning.

## Stronger independent conjecture exposed by reconstruction

**Conjecture D — corrected refinement still carries a nonzero term.** Put `A_p=p^(2-2 Re(s))` and retain the literal correction after subtracting the explicit amplitude, quadratic, and boundary parts:

`C_(p,q)=W_(pq)-W_p-A_p W_q+A_p W_1`.

For every zeta zero with `0<Re(s)<1` and every integer `p>1`, there is a positive integer `q` with `C_(p,q)!=0`. This does not rename Test A: it is a stronger independent claim about the entire source-modulus family. Proposed proof: the actual remainder estimate gives `W_q->0`. If every correction for one fixed `p` vanished, first taking `q->infinity` and then iterating `q->pq` would force the whole `W` family to vanish, contradicting the reconstructed unit boundary. This is a precise obstruction to this scalar refinement law, not to all possible arithmetic identities.

## Grouping primes or zeros

A proof by classes remains possible if the classes exhaust the nontrivial zeros and each class has its own proved exclusion of off-line zeros. Prime classes do not automatically give zero classes. The inspected corpus `CoefficientDecimationSieve` makes finite prime-group filters exact projections onto integers coprime to the associated primorial; its divisor expansion retains products involving several prime choices. Thus dropping cross-group terms would change the source. The obstruction in Conjecture D is pointwise in the zero: if proved, dividing zeros into groups cannot restore this particular vanishing law. It does not rule out a different classification-based proof.

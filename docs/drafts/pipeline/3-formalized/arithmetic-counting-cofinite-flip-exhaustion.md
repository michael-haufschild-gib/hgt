# Finite prime exhaustion has two different harmonic limits

- **ID:** ACP-COFINITE-FLIP-EXHAUSTION
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Source:** ../3-formalized/arithmetic-counting-finite-prime-density.md; ../3-formalized/arithmetic-counting-finite-flip-exhaustion.md
- **Statement:** Cofinite prime flips have explicitly bounded harmonic sums, and the harmonic squared distance between any finite flip and Liouville tends to two despite exact pointwise stabilization.

## Goal

Identify the arithmetic topology behind the finite-flip exhaustion
obstruction. A pointwise limit forgets a full unit of harmonic correlation.
The positive content is an explicit count and a quantitative distance law,
not only failure of a uniform gap statement.

## Closed count proof

For a finite prime set F write `c_F=prod_(p in F)(p-1)/(p+1)` and
`eta_F(n)=liouvilleSign(n)*finiteFlip(F,n)`. Then

`|sum_(n<=N) eta_F(n)/n| <= 2/c_F` for every N.

The empty case is the existing elementary square-count bound
`abs_sum_liouvilleSign_div_le`. Inserting a prime p outside F exchanges
the signs on its divisibility fibre. If A is the old harmonic sum and B
the new one, the exact recurrence is

`p B(N)-B(floor(N/p))=p A(N)+A(floor(N/p))`.

A bound K for A gives the bound `C=K(p+1)/(p-1)` for B by strong induction
on N: at N=0 the sum is zero; otherwise floor(N/p)<N, so the recurrence
and triangle inequality give `p|B(N)| <= (p+1)K+C=pC`. Division by p
closes the induction. Since `c_(F union {p})=(p-1)c_F/(p+1)`, induction
over the finite set gives the asserted `2/c_F` bound. Multiplicativity
and the sign-square identity are preserved by the product with Liouville.

## Distance and quantifier law

Let

`D_F(N)=sum_(n<=N)(finiteFlip(F,n)-liouvilleSign(n))^2/n / H_N`.

For every positive N, signs square to one, so

`D_F(N)=2-2 S_eta_F(N)/H_N`,

`|D_F(N)-2| <= 4/(c_F H_N)`.

Thus for every fixed F the distance tends to two. When
`F=primesBelow Q`, existing exact pointwise agreement gives `D_F(N)=0`
for Q>N. The iterated horizon/cutoff limits are therefore two and zero,
respectively. Every source, norm, domain and order of limits is explicit.

The distance identity follows term by term from
`(omega_F(n)-lambda(n))^2=2-2 eta_F(n)`. The bounded count and H_N>0
give the stated error. Since H_N>=log N tends to infinity, the error
tends to zero. For Q>N every term of the squared difference is zero
by exact prime-cutoff agreement; this includes N=0. These arguments
prove both inner limits with their parameters fixed, without exchanging
limits or assuming a uniform count bound over all prime sets.

## Exact cofinite gap

Every cofinite flip has greatest hyperplane gap exactly zero. The already
proved `not_hasHyperplaneGap_of_abs_harmonicSum_le` rules out any positive
gap from the displayed count. The already proved
`hasHyperplaneGap_zero_of_mul_self_eq_one` supplies attainment at zero
for every sign gauge. Both source statements and their proof mechanisms
were inspected. The former projects the gauged pole onto the constraint;
the latter is the uniform Robin--Euler ceiling.

There is also a reverse pointwise exhaustion: `eta_(primesBelow Q)(n)=1`
once Q>n, whereas every fixed stage has greatest gap zero. Thus a
pointwise limit can both lose a positive gap (finite flips to Liouville)
and gain one (cofinite flips to the untwisted gauge). The count and exact
harmonic distance quantify the missing topology in these two examples.

## Corpus audit

The corpus search found the finite-prime density theorem, finite-flip
matching and existing exhaustion obstruction, but no exact distance law.
The Liouville square-count harmonic bound was read in
`ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin.lean`.
No prime number theorem or density hypothesis is needed for the
bounded-sum recurrence.

Literature scope: generalized Liouville signs and the product formula for
their means are classical; see Borwein--Choi--Coons,
[Section 2, Theorem 2](https://arxiv.org/html/0809.1691v1#S2).
No novelty is claimed for the family or mean-zero phenomenon. The present
contribution is the explicit finite-horizon count bound, its exact
prime-gap consequence in this corpus, and the quantitative exhaustion
law with both orders of limits stated. The external mean theorem is not
used as a proof input.

## Gates

- [x] Exact objects and constructive counting mechanism specified.
- [x] Dependency-closed paper proof and source-name audit.
- [x] Lean proof, direct source check and transitive axiom audit.
- [x] Umbrella, foundational README, durable evidence and cleanup.

## Formal closure

`CofinitePrimeFlipsHaveZeroGap.lean` proves twelve public endpoints:
`cofiniteFlip_mul_self`, `cofiniteFlip_isSignGauge`,
`cofiniteFlip_harmonic_recurrence`, `cofiniteFlip_harmonicSum_abs_le`,
`isGreatest_cofiniteFlip_hyperplaneGap`,
`cofiniteFlip_harmonicCorrelation_tendsto`,
`finiteFlipLiouvilleDistanceSq_eq`, `finiteFlipLiouvilleDistanceSq_error_le`,
`tendsto_finiteFlipLiouvilleDistanceSq`,
`finitePrimeExhaustion_distance_eventually_zero`,
`finitePrimeExhaustion_two_harmonic_limits`, and
`cofinitePrimeExhaustion_eventually_eq_one`.

The scratch audit and canonical installed-source check exited zero without
diagnostics. All twelve transitive axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The adjacent audit file preserves
the source hash, commands and actual reports. The leaf is wired into the
programme umbrella and explained in its foundational README. No leaf
olean or umbrella build was needed.

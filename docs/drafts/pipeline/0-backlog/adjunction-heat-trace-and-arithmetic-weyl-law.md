# Heat trace and arithmetic Weyl law for the adjunction completion

- **ID:** adjunction-heat-trace-and-arithmetic-weyl-law
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** finite-prime adjunction spectrum; proposed coherent ground-state completion; Euler products and Tauberian counting
- **Count:** uncounted; novelty, physical completion, paper proof, and Lean remain

## Target

For the actual coherent completion, if constructed, let
`E(n)=gamma+log(n)+tameDifferent(n)` for positive integers. Conjectural heat trace:

`Tr(exp(-t A))=exp(-gamma*t)*zeta(t)*G(t)` for t>1,

`G(s)=product_p [1-p^(-s)+p^(-s*p/(p-1))]`.

Conjectural counting law:

`#{n>=1:E(n)<=T}/exp(T) -> exp(-gamma)*G(1)>0`.

The heat operator should be trace class exactly when t>1. This is a proposed
spectral counting theorem for the identified arithmetic operator, not merely a
new diagonal operator defined to have these labels. No RH conclusion is proposed.

## Mechanism to audit

The tame different is additive on coprime factors. At p^k with k>=1 its value is
`log(p)/(p-1)`, independent of k. The local series is therefore

`1+p^(-s/(p-1))*p^(-s)/(1-p^(-s))`.

Removing the ordinary zeta factor gives the displayed G. On compact subsets of
Re(s)>0 the deviation of its p-factor from one should be bounded by a constant
times `log(p)/p^(1+Re(s))`, giving locally uniform convergence. At s=1 every
factor is positive, and absolute convergence should make G(1) strictly positive.
The generalized Dirichlet series of the counting measure would then have a
simple pole at one and continuation across that boundary except for the pole.
A positive-measure Tauberian theorem should yield the counting law; its exact
corpus interface and hypotheses still require inspection and discharge.

The first corpus query returned the existing tame-different bounds and unrelated
energy traces. This is only an initial lead search, not a completed novelty audit.
No numerical work, paper-proof completion, or Lean assertion has been made.

## Elementary counting route to inspect

A finite-prime truncation may remove the need for a Tauberian theorem. Put
`a(n)=tameDifferent(n)` and `a_Q(n)=sum_(p in Q,p divides n) log(p)/(p-1)`.
For fixed Q, a_Q is periodic modulo its primorial. Splitting into its finitely
many residue classes should give

`#{n>=1:n*exp(a_Q(n))<=X}/X -> C_Q`,
`C_Q=product_(p in Q)[1-1/p+exp(-log(p)/(p-1))/p]`.

The omitted additive tail is nonnegative, and ordinary divisor counting gives

`sum_(1<=n<=X)(a(n)-a_Q(n))/X
 <= sum_(p notin Q) log(p)/(p*(p-1)) = T_Q`.

The series on the right converges even when primes are replaced by all integers
at least two. Markov's inequality would bound the bad integers with tail>eta
by `X*T_Q/eta`. Comparing the actual count with the truncated count at X and
at exp(-eta)*X would squeeze the limiting density between C_Q and
`exp(-eta)*C_Q-T_Q/eta`. Let Q exhaust the primes, then eta decrease to zero.
This uses the corpus's periodic counting and summable divisor mechanisms rather
than assuming a Tauberian input. Exact finite-prime counting, positive convergence
of C_Q, the real cutoff formulation, and the operator heat-trace identification
still need source audits and Lean proofs. `TheAnomalyCostsHalfALogarithm` already
contains a tame-different average bound. Its source was inspected through that
proof: `log_div_mul_le` bounds each prime tail weight by `4*p^(-3/2)`, and
`summable_tame` proves the required dominating series summable. The existing
mean is harmonic; the proposed counting squeeze needs the ordinary-count variant,
retaining the omitted-prime tail rather than only its global constant.

The ordinary-count corpus search found the exact anchored divisor count
`BVI.card_filter_dvd_Icc_eq_div` in
`FermiCellJumpReciprocityAndPronicTailBridge.lean`, whose source was checked.
`RHTower.Sieve.cast_div_bounds` in `Sieve/IntervalMultiples.lean` gives the real
floor sandwich, and its source was checked too. Thus each omitted prime
contributes at most `N*log(p)/(p*(p-1))` to the ordinary sum: swap the finite
prime-divisor sums, replace the count by `floor(N/p)`, and use the nonnegative
weight and floor upper bound. The existing RAPT `filter_dvd_Icc_eq_image` is an
alternative direct reindexing route. These are baseline counting inputs, not
additional contributions. The new density squeeze and corrected Euler constant
remain unproved.

For the finite-prime threshold count, partition by residues modulo the primorial.
On residue r the cutoff is `floor(exp(-a_Q(r))*N)`. The source of
`RHTower.tendsto_fixedCoreSquarefree_scaled_count` in
`FixedCoreSquarefreeMoments.lean` was inspected: its floor-cutoff argument
composes an ordinary density limit with `floor(c*N)->infinity` and
`floor(c*N)/N->c`. The same mechanism applies to each periodic residue indicator,
then summing the finitely many residues gives the average of `exp(-a_Q)`.
The product formula for this average can be obtained by expanding the finite
product of divisor indicators and applying exact counts for squarefree products
of the chosen primes; no new CRT theorem is necessary. These are proof-design
leads, not a completed theorem or a novelty certificate.

The positive-product search found the checked source pattern in
`HTGeometry/QPochhammer.lean`, `realQFactorial_multipliable` and
`realQFactorialInf_ne_zero`: use `Real.multipliable_one_add_of_summable`
and `tprod_one_add_ne_zero_of_summable`. For the proposed factors, their
defects have absolute value `(1-exp(-w_p))/p <= w_p/p`, already dominated
by the summable tame-weight majorant. Each factor is strictly positive.
Product convergence plus nonzero and nonnegative limits should therefore
give the desired strict positivity without a new logarithmic-product theorem.
`HTGeometry/InfiniteProductNearOne.lean` was also inspected; its quantitative
finite and infinite perturbation bounds are baseline, not specific to these
arithmetic energies. Whole-corpus additive-distribution and periodic-threshold
queries did not expose an existing arithmetic Weyl statement. Novelty audit
remains open; the absence of a query hit is not a proof of novelty.

The heat-trace novelty query surfaced `HTGeometry/RamificationSpectralFusion.lean`.
Its clock and heat sections were inspected through the trace theorem. They treat
diagonal `log(n)` clocks on Euler shells and their power-map range/defect split,
not the torsion-adjunction correction or the literal full prime matrices. Its
`FormationExcess.diag_traceClass` is a reusable baseline: summable nonnegative
diagonal weights bounded by one give positivity, trace class, and trace equal
to their sum. Any eventual heat interpretation should reuse this theorem after
identifying the actual coherent operator; the generic trace identity is not new.

Literature baseline: Hilberdink--Pushnitski's
[LCM spectral paper, Sections 2 and 4](https://arxiv.org/html/2401.06892v1)
passes from prime-factor eigenvalue products to counting laws by extracting
a zeta factor and applying Wiener--Ikehara. This general method is established.
The candidate must prove the specific torsion-adjunction Euler factor and an
actual operator or full-horizon spectral consequence. The elementary periodic
truncation argument above is an alternative proof route, not by itself a new
spectral object.

## Direct physical consequence to audit

The arithmetic counting statement does not itself require the proposed infinite
completion. The full-matrix quasimode packet theorem is now formalized. The
finite set of conductors with E(n)<T should force at least that many distinct
actual P_N eigenvalues in `(log(N)-T, log(N)-gamma+epsilon)` for all sufficiently
large N. Choose the approximation tolerance below both epsilon and every finite
lower-window margin T-E(n). The counting law would then give an exponential
lower count of actual full-matrix spectral branches. This provides a possible
unconditional physical endpoint even if the infinite-completion project remains
open. A trace interpretation must wait for the actual operator identification;
an abstract prescribed-label trace must not stand in for that identification.

The separate spectral-exhaustion candidate now has a dependency-closed paper
proof and is undergoing Lean verification. If that verification succeeds,
the counting-law endpoint can concern the eventual exact full-matrix count,
not only a lower count: first take the actual horizon limit at a non-arithmetic
threshold T, then let T tend to infinity. No joint growing-window limit or
interchange of those limits is justified by the present arguments. The counting
law, corrected Euler constant, and any trace identification remain unproved.

A further literature check located Tenenbaum--Verwee,
[Effective Erdos--Wintner Theorems](https://www.mathnet.ru/eng/tm4162).
Only its abstract was inspected: existence of limiting distributions for real
additive functions and effective errors are established general theory. Thus
additive-prime truncation and statistical independence cannot themselves count
as novelty. The proposed contribution still requires the specific corrected
constant and a proved consequence for the actual prime operator. Refreshed
corpus searches for tame-conductor counting and periodic additive truncation
returned neighboring Euler and density results, with no matching theorem among
the inspected results; this is not an exhaustive absence claim.

The exact product probability carrier for a possible expectation formula is
already available: `HTGeometry.primeValuationMeasure` uses independent geometric
laws with occupancy 1/p. Its sector, independence, infinite-support and local-tail
sources were inspected in the completion audit. The prospective constant G(1)
can be identified with the expectation of exp(-sum_p 1_(v_p>0)*log(p)/(p-1))
after proving convergence of that nonnegative additive sum and the integral
limit. This carrier construction and independence are existing baseline.

The critical heat threshold has a simpler lower-bound route than the full
counting law. For prime p, E(p)=gamma+log(p)+log(p)/(p-1), while
log(p)/(p-1)<=1. Hence, for 0<t<=1,
`exp(-t*E(p))>=exp(-t*(gamma+1))/p`.
The corpus's divergent prime reciprocal sum forces divergence of the heat sum
already on prime labels. For t>1 the lower bound E(n)>=gamma+log(n) gives
summability by the ordinary p-series. For t<=0, properness gives divergence
as well. These are proposed exact proof steps for the actual identified
operator, still requiring Lean and the completion interface; no abstract
prescribed-spectrum trace is being counted.

# Cofactor diagonals read horizon energy ratios

- **ID:** cofactor-diagonals-read-horizon-energy-ratios
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
- **Statement:** The diagonal of every actual common cofactor limit
  determines the asymptotic receiver-energy ratio at each integer-contracted
  horizon. Mixed entries obey an analogous change-of-horizon identity.

## Corpus inputs and scope

`TheDilationSelfSimilarityOfThePronicMeasure.sum_Icc_pronic_dilation_fibre`
proves exact pronic mass on each complete integer-dilation block. The same
file proves contraction by enlarging incomplete fibres, but does not retain
the last-fibre correction. `TheWorkIsACorrelationWithWindowMeans` records
exact truncated fibre averages. The actual receiver has zero origin and
absolute value at most its horizon. These are arithmetic source inputs.

Searches: exact pronic pairing of dilated rows at truncated horizons;
cofactor Gram diagonal energy ratios; dilation last fibre. No exact
horizon-ratio theorem surfaced. This is a refinement of the existing block
identity, not a new general theory of regular variation.

## Paper derivation under audit

Write Q_T(u,v)=sum_{1<=n<=T} u(n)v(n)/(n(n+1)). For p>=1, N=floor(T/p),
and zero-origin rows, fibre telescoping gives

`Q_T(D_p u,D_p v) = Q_N(u,v)/p
  - u(N)v(N)*(1/(T+1)-1/(p*(N+1)))`.

When |u(n)|<=C_u*n and |v(n)|<=C_v*n, the absolute last-fibre correction
is uniformly bounded: its tail has fewer than p cells, each at least pN,
so the product bound cancels the N^2 denominator. The N=0 case vanishes.
Every fixed actual cofactor satisfies such a bound.

Consequently, on escape and along an actual common-limit sequence T_m,

`E(floor((T_m+1)/p))/E(T_m+1) -> p*K(p,p)`.

The ratio lies in [0,1], and p*K(p,p) is nonincreasing in p. Mixed dilation
entries similarly retain the smaller-horizon Gram, weighted by this energy
ratio. No multiplicative law for these ratios follows without additional
information. In particular, this does not assume regular variation or
identify dilation eigenvalues with arithmetic zeros.

## Gates

- [x] Existing block law and common-limit definitions inspected.
- [x] Exact finite-horizon identity, including N=0 and incomplete block.
- [x] Uniform correction bound for actual rows.
- [x] Actual diagonal limit and monotonicity: canonical Lean and standard axioms.
- [x] Mixed change-of-horizon consequences.
- [x] Source checks, transitive axiom audit, umbrella import.

## Stronger unconditional formulation

The finite-block proof can avoid estimating the explicit correction.
Monotonicity sandwiches the dilated self-pairing between E(N-1)/p and
E(N)/p. Actual energy jumps are at most one, so on escape its normalized
error vanishes. On admission, complete-block equality and convergence of
the full energy show K(p,p)=1/p, while both contracted and original energies
converge to the same positive total. Hence the horizon-ratio identity holds
for every actual common limit, without an escape premise. This extra branch
uses the already checked admitted-kernel convergence theorem.

The ratio reads the norm of the dilated cyclic vector. It does not by itself
read the entire operator norm or spectral radius; those stronger claims need
homogeneity of all mixed entries. White noise remains compatible with ratio
one, and the stronger-contracting faithful models remain compatible with
power ratios. This invariant alone does not settle the hull classification.

## Dependency-closed proof of the diagonal theorem

For a zero-origin row A let Q(T)=sum_{n=1}^T A(n)^2/(n(n+1)).
Grouping complete fibres proves

`Q_{p*(N+1)-1}(D_p A)=Q(N)/p`.

Each positive fibre has exactly the already proved mass
1/(p*N*(N+1)); the zero fibre contributes zero. For N=floor(T/p)>0,
monotonicity then gives

`Q(N-1)/p <= Q_T(D_p A) <= Q(N)/p`.

For N=0 both quantities vanish. For the actual row |A(n)|<=n,
Q(N)-Q(N-1)<=1, hence the difference between Q(N)/p and the dilated
energy lies in [0,1/p]. On the escaping branch, division by Q(T) sends
this difference to zero. The prescribed common Gram limit therefore
forces Q(floor(T/p))/Q(T) to converge to p*K(p,p).

On the admitted branch, Q(T) converges to some e>0, by positivity of the
first actual cell. The existing full-horizon pairing theorem gives a
unique full-horizon Gram limit. Evaluate that limit at complete-block
horizons: its p-diagonal is (e/p)/e=1/p. Since floor(T/p) also tends to
infinity, the energy ratio tends to one=p*K(p,p). The admission/escape
dichotomy covers every actual common limit.

Finally p<=q implies floor(T/q)<=floor(T/p). Energy monotonicity and
the ratio limits give q*K(q,q)<=p*K(p,p). The endpoints lie in [0,1]
and the scale-one value is one. This proves the unconditional invariant
without a regular-variation premise. The mixed identity is a separate
refinement; it is not required for this diagonal result.

The complete-block and diagonal arguments are now canonical in
`ThePronicPairingHasExactDilationBlocks` and
`ActualCofactorDiagonalsAreHorizonEnergyRatios`. Their final checks passed.

## Existing sandwich reused

A more targeted corpus search surfaced
`ArithmeticCompensationTheory.pronicEnergy_rowDilate_sandwich` and
`pronicEnergy_rowDilate_eq_complete` in
`TheNormalizedReceiverBlowUpProfile`. The diagonal error draft now consumes
that existing sandwich directly, rather than reproving its horizon bounds.
The bilinear complete-block draft remains for the mixed pairing refinement.
Energy jumps likewise use the existing `receiverEnergy_succ_le` from
`EnergyQuantilesRetainDiffuseEscape`.

## Current verification status

The complete-block and actual diagonal leaves passed their final source-only
checks and standard transitive axiom audits in session `90975`.
`IncompleteDilationFibresHaveBoundedPairingCost` passed final source-only
check `89066`, including the exact terminal fibre, zero quotient, general
C*D/p bound and actual unit-bound specialization.
`ContractingHorizonsProducesActualCofactorLimits` passed final source-only
check `13848`, including the mixed limits and admitted branch. No mixed
result is inferred from the diagonal theorem alone.

The explicit interval theorem `scaled_diagonal_mem_Icc` is installed and
wired in `NumericHorizonOrderControlsTheCofactorAction`. Its required olean
passed in `68599` and final source-only audit in `42266`, with only
`propext`, `Classical.choice`, `Quot.sound`. All claims on this card are
formalized; exact canonical audit records are in
[the completion ledger](../1-in-progress/q-iii-existing-findings-lean-completion.md).

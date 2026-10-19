# Finite coefficient recovery from selected Fermi boundaries

- **ID:** thim-selected-fermi-coefficient-observability
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** At horizon N, the N normalized readings
  `R(n)=-J(n)` for odd n and `R(n)=J(2n)` for even n, `1<=n<=N`,
  determine every admitted coefficient c(d), without a support restriction.

## Why the earlier obstruction does not settle this

The finite-pair counterexample in `../3-formalized/thim-fermi-valuation-observability.md`
invalidates a uniform pointwise inverse energy bound for unrestricted weights.
It does not show that the complete selected trace loses coefficients. Exact
pointwise sieve recovery and recovery of the coefficient vector are different
questions. The latter can survive through a nontrivial coefficient transport.

## Corpus audit

Searches issued through `scripts/formal_tools.py research`: `Fermi injective`,
`sieveSeq zero iff`, `sieveSeq dilation`, and deep queries for selected-boundary
coefficient recovery and origin observation. The first two returned no matching
Fermi recovery result. The existing BVI origin-prefix and translated-window
observability results must be checked before treating this as a new advance.
Deep results, source applicability, and significance review remain pending.

The completed origin-observation deep search recovered
`SharpInitialPrefixObservabilityAndExactGramDeterminants`: the first N-1
centered-prefix observations already determine all nonconstant coefficients;
explicit interpolation, sharp horizons, and Gram determinants are prior work.
Its `sievePrefix_initial_eq_iff_tail_eq` and reconstruction source were checked.
`ArithmeticLagSchedulesAndSharpRecoveryHorizon` instead classifies literal
shifted pair observations by visibility clocks. Neither statement is the
selected Fermi-boundary map above. Reuse the existing divisor-sum inversion
machinery; do not count triangular inversion itself as new mathematics.

The selected-boundary deep search returned the existing all-octave jump and
dyadic-prefix inversion identities. It was partial (dyadic-alias query and
reranking unfinished). These identities are prerequisites, not contributions.

## Paper mechanism

Extend c by zero beyond N, denoting this extension by a. Define

`b(d)=a(d)` if d is odd, and
`b(d)=(if 4|d then 2 else 1)*a(d)-a(2d)` if d is even.

Claim: `R(n)=sieveSeq N b n` for every positive n. This is checked by the
coefficient columns. A divisor d not divisible by four contributes its usual
divisibility indicator. A divisor divisible by four contributes
`2*1_(d|n)-1_(d/2|n)`. Odd n gives zero in both terms of this latter column;
even n gives exactly `2*s(n)-s(2n)`. Summing the columns gives the transport.

If the first N readings vanish, the lower-triangular divisor-incidence matrix
forces b(d)=0 for every admitted d. Descending induction on d then forces
a(d)=0: the only off-diagonal term is a(2d), already zero or outside N, while
the diagonal multiplier is either one or two. Applying this to a difference
of two coefficient vectors gives injectivity.

The corresponding normalized observation determinant should be
`2^(N/4)` (natural quotient): the divisor-incidence determinant is one and
exactly the four-divisible coefficient columns have diagonal multiplier two.
This determinant statement is a further conjecture until formalized.

## Stronger positive survivor: coefficient energy

The transport also has a uniform inverse bound after arithmetic inversion of
the observations. Write `t(d)=a(2d)` and, for even d,
`alpha(d)=1` when `4` does not divide d and `alpha(d)=2` otherwise. Define
`r(d)=alpha(d)*a(d)-3*t(d)` for even d and `r(d)=a(d)` for odd d. Then

`3*sum_(1<=d<=N) b(d)^2 - 2*sum_(1<=d<=N) a(d)^2
 = sum_(1<=d<=N) r(d)^2`.

Pointwise expansion leaves `6*a(d)^2` on four-divisible d and
`-6*a(2d)^2` on even d. Doubling bijects those index sets after the cutoff
zero extension, so these terms cancel exactly. Hence coefficient energy is
at most `3/2` times transported coefficient energy. This also proves the
transport's injectivity without a second descending induction.

The constant is sharp on paper. For K>=0 and H=2^(K+2), take c(2)=3,
c(2^(j+2))=(2/3)^j for 0<=j<=K, and zero elsewhere. Every residual
except the last vanishes; at H it equals 2*(2/3)^K. Thus, writing A and B
for the coefficient and transported energies, A>=9 and
3B-2A=4*(2/3)^(2K). If A<=C*B universally, then C>0 and
(3-2C)A<=4C*(2/3)^(2K). For C<3/2 the left side is at least
delta=9*(3-2C)>0. Induction gives (2/3)^K<=2/(K+2), while
0<=(2/3)^K<=1, so the right side is at most 8C/(K+2).
Choose K>8C/delta to obtain a contradiction. This uses finite symbolic
packets and the Archimedean property; no numerical experiment or limiting
interchange is needed. This optimality argument is now verified in Lean.

Corpus searches for `"3 / 2" Fermi` found only an unrelated inner-factor norm
theorem. The partial deep coefficient-energy search also found BVI's
`successorPhaseLoss_le_three_halves_successorReserve`. Its source controls
Selberg-diagonal phase loss, with equality at mode six; it is a different
operator and norm. Do not infer global novelty from these search results.

Verified Lean module: `FermiSelectedCoefficientTransportAndRecovery.lean`.
The exact transport, square completion, inverse bound, and finite-trace
equality classification passed final named-leaf source audit with
`lake --old env lean` (exit 0, no diagnostics). All nine public declarations
passed a scratch-file axiom audit: only `propext`, `Classical.choice`, and
`Quot.sound`. The leaf is wired into the field umbrella. Generated indexes
were refreshed. The latest `scripts/formal_tools.py lint --check-generated`
passed (exit 0). Determinant remains a separate conjecture; it is not part
of the verified statement or the contribution count.

The further deep query `dyadic geometric coefficient finite support sharp
three halves` returned no matching declaration. All 20 source arguments,
20 candidate lemmas, and the ingredient set were inspected: geometric KL
splits, Burnol contractions, and dyadic fold sums concern different operators.
This query was partial; several retrieval stages remained unfinished. Exact
Mathlib-filtered searches missed existing `Nat.log_pow`, so dependency names
are also checked against local source and compiled scratch probes. Search
absence is not treated as an exhaustive novelty certificate.

Two further lexical audits were paginated completely: `Fermi coefficient`
(50 hits) and `coefficient dyadic energy` (47 hits). The broader exploratory
query `coefficient dyadic` had 358 hits and was narrowed by the energy term;
it was not exhausted. The closest additional result,
`RHTower.integral_normSq_finiteNymanError_le_six`, controls the continuous
half-line Nyman error by its full Fermi dilation difference. Its whole source
was read; neither its norm nor its observation operator is the present one.

External overlap check: the coefficient operator on one even valuation chain
is the upper bidiagonal matrix with diagonal `1,2,2,...` and superdiagonal
`-1`. Its Gram matrix has diagonal `1,5,5,...` and off-diagonal `-1,-2,-2,...`.
This is a finite-rank perturbation of a constant Jacobi matrix. General spectral
analysis of this class is established work; see Webb–Olver,
[Spectra of Jacobi Operators via Connection Coefficient Matrices](https://link.springer.com/article/10.1007/s00220-021-03939-w)
(2021), introduction and Theorem 4.22. This operator identification is our
paper inference, not a claim that the paper states the selected-Fermi theorem.
Do not count the isolated `3/2` spectral calculation as an independent novelty.

Sharpness leaf: `FermiSelectedCoefficientSharpInverse.lean`. The capstone
`fermiSelectedCoefficient_inverse_constant_iff` passed the final named-leaf
source audit with `lake --old env lean` (exit 0, no diagnostics). It states
that the uniform inverse coefficient-energy inequality holds exactly for
constants C>=3/2. The leaf is wired into the field umbrella; its scratch-file
axiom audit passed (exit 0), with only `propext`, `Classical.choice`, and
`Quot.sound`. No further source audit is needed absent code changes.

## Scope

No claim yet that these finite readings have a horizon-independent inverse
bound in the physical pronic norm. The earlier alias example prohibits that
particular local estimate. No claim about centered-prefix energy or RH.
Do not count this separately until its mathematical relation to the first
sampling package and its independent significance have been audited.

## Next steps

1. Continue physical-norm analysis in
   `../1-in-progress/thim-full-trace-valuation-depth-stability.md`.
2. Audit significance of the combined sampling/recovery package; count remains zero.
3. Audit the determinant conjecture independently before pursuing it.

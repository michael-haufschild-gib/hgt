# Finite prime exhaustion loses uniform positive gaps

- **ID:** ACP-FINITE-FLIP-EXHAUSTION
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean formalization follows)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Source:** obstacles-summary.md, parity and exhaustion questions
- **Statement:** Every finite-prime cutoff is multiplicative, matched and positively gapped, but the cutoffs stabilize to Liouville on each fixed horizon and admit no positive gap with a cutoff-uniform horizon bound.

## Exact family

Let `omega_Q=finiteFlip(primesBelow Q)`. Every prime factor of `n<Q` lies
below `Q`, so

`omega_Q(n)=(-1)^(sum_p v_p(n))=liouvilleSign(n)`.

This includes `n=0` under the existing conventions. Thus for each fixed
integer, equality holds for every sufficiently large cutoff; on the whole
horizon `1<=n<=N`, equality holds whenever `Q>N`.

## Positive finite stages

The companion closed proof in `../3-formalized/arithmetic-counting-finite-prime-density.md`
gives the exact positive harmonic density

`c_Q=prod_{p<Q, p prime}(p-1)/(p+1)`

with a bounded harmonic error, and hyperplane gap `(2 log 2)c_Q^2>0`.
The existing finite-flip matching theorem gives complete multiplicativity
and the untwisted Mertens matching coefficient, with its explicit constant
`log 4+4+2 sum_{p<Q} log(p)/(p-1)`.

## Uniformity obstruction: closed proof

Suppose some `g>0` admits the following bound: for every `epsilon>0` there
are `Q_0,N_0` such that, for every `Q>=Q_0`, `N>=N_0`, and every vector on
the harmonic hyperplane,

`P_N(omega_Q x)<=(log N-gamma-g+epsilon)||x||^2`.

Fix `epsilon`, `N>=N_0`, and the vector, and choose
`Q=max(Q_0,N+1)`. The gauges agree with Liouville throughout the horizon;
the literal finite prime forms are therefore equal term by term. The bound
would give `HasHyperplaneGap liouvilleSign g`, contradicting the checked
Liouville zero-gap theorem. This rules out even a cofinal rectangle in the
two cutoffs, not only a bound valid at all prime cutoffs.

## Positive survivor and implication

The exact finite-prime count and its positive paid gap survive with their
prime-set dependence intact. Equality on every bounded horizon, complete
multiplicativity, and matching at every finite stage do not supply the
uniform horizon bound required to pass a positive gap to the exhaustion.
This identifies an explicit missing quantifier, rather than assuming
positivity is closed under pointwise arithmetic convergence.

The conclusion concerns the prime-form hyperplane gap. It neither proves
nor refutes complete Weil positivity for the original source, and it does
not replace the independent single-prime maximal-gap theorem for primes
at least 11.

## Corpus audit

Searches for finite prime flips, harmonic means, Liouville exhaustion and
uniform hyperplane gaps found the singleton count, finite-prime Mertens
matching, and Liouville zero-gap theorem. The arbitrary finite-prime
harmonic count and this explicit exhaustion conjunction were not found.
The exact identification uses the verified prime-factor support and
`ArithmeticFunction.cardFactors_eq_sum_factorization`; finite-form
congruence is an existing corpus lemma.

## Gates

- [x] Exact family, quantifiers, positive survivor and closed paper proof.
- [x] Corpus search before mathlib; imported statements inspected.
- [x] Companion finite-prime density formalized, canonically checked, and axiom-audited.
- [x] All five exhaustion theorems pass Lean and transitive axiom checks, with only the three standard axioms.
- [ ] Canonical source checks, umbrella, README, scratch cleanup.

Installed as `ArithmeticCountingPositivity/FinitePrimeExhaustionLosesUniformGaps.lean`
and wired into the own umbrella and foundational README. Final installed-source
check is running; no own olean is needed by the next leaf.

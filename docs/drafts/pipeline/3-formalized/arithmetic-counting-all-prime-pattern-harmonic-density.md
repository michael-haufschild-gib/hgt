# Every prime pattern has its Euler-product harmonic mean

- **ID:** ACP-ALL-PRIME-PATTERN-HARMONIC-DENSITY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Lean target:** EveryPrimePatternHasItsEulerProductHarmonicMean.lean
- **Input:** ../3-formalized/arithmetic-counting-uniform-prime-stripping.md

## Exact statements

For any set P of natural numbers, let omega_P be the multiplicative sign
that flips exactly the primes in P. Nonprime members have no effect. Put
F_Q={p<=Q: p prime and p in P}, c_Q=prod_(p in F_Q)(p-1)/(p+1), and
c=inf_Q c_Q. Then:

1. c_Q decreases to c.
2. 0<=c<=1.
3. S_(omega_P)(N)/H_N tends to c as N tends to infinity.
4. omega_P has selective hyperplane gap (2 log 2)c^2.

No summability, prime-pattern density, harmonic mean or gap hypothesis is
added. The conclusion concerns every prime-sign pattern, finite or infinite.

## Product and reciprocal counts

Each local factor c_p lies in (0,1), so c_Q is decreasing and positive.
Completeness gives c_Q -> c in [0,1]. In particular c<=c_Q for every Q.

For every finite prime set F, write eta_F=sum_(p in F)1/p. The local identity
c_p(1+1/p)=1-1/p<=1, combined with induction, gives

c_F(1+eta_F)<=1.

Indeed, if c_F(1+eta_F)<=1, then
c_p c_F(1+eta_F+1/p)
 =c_p[c_F(1+eta_F)+c_F/p]
 <=c_p(1+1/p)<=1,
since c_F<=1. This is a finite positive counting inequality.

For N>=Q, the visible flipped primes decompose into the disjoint head F_Q
and tail T_(Q,N). Their density factors multiply. Thus

c_N(1+eta_T)<=c_Q.

When c>0, c<=c_N yields the uniform tail bound

eta_T<=c_Q/c-1.

## Exact stripping and the zero-product case

Let omega_T flip P without the primes at most Q. Its values at every prime
in F_Q equal one, and omega_P=omega_(F_Q)*omega_T exactly. The uniform
stripping theorem gives, for every N>=1,

|C_P(N)-c_Q C_T(N)|<=K_Q/H_N,

where C=S/H and K_Q is the explicit finite stripping cost. Every sign
correlation lies between -1 and 1. Hence

-c_Q-K_Q/H_N<=C_P(N)<=c_Q+K_Q/H_N.

For fixed Q, H_N tends to infinity, so both error terms vanish. If c=0,
the lower and upper limiting bounds then tend to zero as Q increases.
The two-parameter packet lemma proves C_P(N)->0 without exchanging limits
or assuming any cancellation in the residual sign.

## Positive-product case

Divisibility counting gives C_T(N)>=1-2 eta_T. Combine this with the paid
tail bound and the exact stripping estimate:

c_Q[1-2(c_Q/c-1)]-K_Q/H_N
 <=C_P(N)<=c_Q+K_Q/H_N             (N>=max(1,Q)).

For each fixed Q the outer bounds tend respectively to
c_Q[1-2(c_Q/c-1)] and c_Q as N increases. Since c_Q->c>0, both of these
limits tend to c as Q increases. The same packet lemma gives C_P(N)->c.
Every finite packet has its own eventual horizon; no common horizon is
asserted or needed.

## Paid gap

The existing uniform squared-correlation inequality pays
(2 log 2)C_P(N)^2 at each sufficiently large horizon, with arbitrary small
additive error. The proved mean makes C_P(N)^2 tend to c^2. Allocate half
the requested error to this limit and half to the uniform inequality.
The resulting eventual quadratic bound is exactly HasHyperplaneGap
omega_P ((2 log 2)c^2), including c=0.

## Dependencies, scope and novelty

The proof uses the formalized uniform stripping estimate, arbitrary-pattern
divisibility count, finite Euler factors, harmonic divergence and the
existing two-parameter packet and squared-correlation lemmas. All are
unconditional mathematical inputs already audited in the corpus. The
zero/positive case split is internal to the proof, not an assumption binder.

Generalized Liouville mean-value theory is classical background; see
[Borwein--Choi--Coons](https://arxiv.org/abs/0809.1691). No literature-wide
priority is claimed for existence of these means. The contribution here is
a dependency-closed count-based proof using the uniform stripping currency,
with its actual selective-gap payment formalized in the same framework.

Vanishing harmonic density does not imply zero greatest gap: this payment
is a lower bound, not a converse. No optimal-gap continuity or complete Weil
positivity is claimed.

- [x] Complete paper proof for every prime set, including zero product.
- [x] Immediate full Lean draft with the same four endpoints.
- [x] Scratch and transitive axiom audit.
- [x] Canonical source check, umbrella and durable evidence.

## Lean endpoints and audit

EveryPrimePatternHasItsEulerProductHarmonicMean.lean proves
tendsto_primeSetCutoff_density, primeSetHarmonicDensity_bounds,
primeSetFlip_harmonicCorrelation_tendsto and primeSetFlip_hasHyperplaneGap.
Scratch 83412 and canonical 76375 exited zero without diagnostics. Every
transitive audit uses only propext, Classical.choice and Quot.sound. The
adjacent audit preserves exact commands, source hash and actual output.

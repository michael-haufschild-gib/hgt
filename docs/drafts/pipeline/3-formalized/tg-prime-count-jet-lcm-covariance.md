# TG: signed prime-count jet fibres in the native covariance

- **ID:** tg-prime-count-jet-lcm-covariance
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TG, C9.12a–b
- **Statement:** The literal Möbius prime-count jet has negative complete LCM self-convolution, an exact two-coordinate Möbius/gcd incidence law, and a full signed decomposition of the original prime–polar reciprocal-maximum covariance.

## Source and mathematical target

The corpus fixes `j(n)=mu(n)*omega(n)` and proves
`sum_(d|n)j(d)=-1_IsPrimePow(n)` for n>0. A prime power is counted once,
independently of exponent. This is the derivative at one of the actual
prime-count-damped Möbius source. It is not a new arithmetic model.

For each n,k,m define the complete fibre

`H(n;k,m)=sum_(lcm(d,e)=n) j(d)j(e) 1_(d|k)1_(e|m)`.

All d,e in this sum are divisors of n. The main exact laws are:

1. `sum_(lcm(d,e)=n) j(d)j(e)=-j(n)`.
2. `H(n;k,m)=sum_(r|n)mu(n/r)1_IsPrimePow(gcd(r,k))1_IsPrimePow(gcd(r,m))`.
3. `H(n;k,k)=-j(n)1_(n|k)` and H vanishes unless n divides k*m.
4. For every finite physical cutoff N and k,m in [1,N],
   `1_IsPrimePow(k)1_IsPrimePow(m)=sum_(n in L_N)H(n;k,m)`,
   where `L_N={lcm(d,e):1<=d,e<=N}`. The labels n>N remain.
5. This identity survives every real two-coordinate kernel K(k,m), with
   no absolute value, averaging or removal of cross terms.

## Complete paper proof [PROVED HERE]

For law 1, the divisor transform of the LCM fibre is the square of the
jet's divisor transform: pairs whose LCM divides n are exactly pairs of
divisors of n. Hence that transform is `1_IsPrimePow(n)`, which is also the
divisor transform of -j. Möbius inversion proves equality for positive n;
the zero fibre is empty and j(0)=0.

For law 2, the incidence-restricted divisor sum is

`sum_(d|r,d|k)j(d)=sum_(d|gcd(r,k))j(d)=-1_IsPrimePow(gcd(r,k))`.

The complete bilinear fibre's divisor transform is the product of these
two restricted sums. Inverting gives the displayed formula. The signs are
retained. For the diagonal, when n|k all divisors of n are admitted and
law 1 applies. When n does not divide k, no LCM=n pair can have both entries
dividing k. The product support follows since d|k and e|m imply lcm(d,e)|k*m.

For law 4, expand the two complete divisor sums on the finite carrier
[1,N] and regroup pairs by their exact LCM. Although n can exceed N, its
incidence-weighted complete fibre still equals the finite-carrier fibre:
any contributing d divides k and therefore d<=k<=N; likewise e<=m<=N.
Thus all nonzero terms are already inside the finite carrier. Conversely,
every pair with LCM=n consists of divisors of n. This proves the equality
without a low-LCM restriction. Law 5 follows by finite sum interchange.

## Native TG specialization

Keep the exact original polar cell masses alpha_i from
`SoninPolarGroundDiscretization`. Set

`b_i=alpha_i+1_(i+2 is a proper prime power)`.

Then the original coefficient satisfies exactly

`c_i=1_Prime(i+2)-alpha_i=1_IsPrimePow(i+2)-b_i`.

Let `K_ij=1/max(i+2,j+2)` and retain i,j=0,...,N. The original physical
covariance is

`Q_N=sum_ij K_ij c_i c_j`.

The full LCM decomposition is

`Q_N=sum_(n in L_(N+2)) sum_ij K_ij H(n;i+2,j+2)`
`    +sum_ij K_ij [b_i b_j-1_IsPrimePow(i+2)b_j-b_i1_IsPrimePow(j+2)]`.

This keeps every polar/prime-power cross term and every high-LCM label.
The actual ordered ground covariance proves `||G_N||²=2a Q_N`. Comparing
with the audited cofinal-energy theorem gives exactly

`Q_N=sum_(i<=N) E_i + A_N²/(N+3)`.

The endpoint square is unchanged. No discarded tail, rescaled weight,
period covariance or coefficient-square surrogate appears.

## What failed and what survives

The initial conjecture that complete jet LCM pairs have prime-only support
is false: their exact coefficient is -j, retaining squarefree composites.
The strongest proved survivor is the two-coordinate incidence law and its
full native-kernel transport. These expose where signed shared-prime
cancellation must be used, while preventing deletion of high-LCM terms.

A finer prime-factor classification `H=mu(n)*(L*R-S)` on squarefree product
support is a separate paper conjecture, not part of the Lean claims here.
L,R count prime factors exclusive to the two coordinates and S counts the
shared factors. Its full formal proof remains future work.

The native signed form has not been bounded. Arithmetic energy finiteness,
Gamma completion, Hardy compatibility, strict sub-unit control and RH remain
open. Finite identities are not an unconditional RH proof or falsification.

## Corpus and audit

Core dependencies: `EulerDeletionPrimeCountEndpointVariance`,
`EulerDeletionPrimeCountEndpointTransfer`,
`EulerDeletionTruncatedDivisorPairCorrelation`,
`SoninPrimePolarCofinalGroundEnergy`.

Search evidence:
`/tmp/tg-c912-jet-lcm-search.json`,
`/tmp/tg-c912-shifted-jet-search.json`,
`/tmp/tg-c912-lcm-damping-search.json`.
All three are nonpartial snapshots with background refresh incomplete;
returned candidate/source statements and proposed ingredients were inspected.

Production: `formal/GaloisForLFunctions/RHTower/SoninPrimePolarJetLcmCovariance.lean`.
The final foreground leaf audit exits 0 with empty diagnostics:

`lake --old env lean GaloisForLFunctions/RHTower/SoninPrimePolarJetLcmCovariance.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninPrimePolarJetLcmCovariance.olean`

All twelve public declarations pass the separate `/tmp` foundation audit,
using only `propext`, `Classical.choice` and `Quot.sound`. The module is wired into `RHTower.lean`; no umbrella
build, added axiom, numerical experiment or heartbeat increase was used.
Logs: `/tmp/tg-c912-final.log`, `/tmp/tg-c912-axioms.log`.

## Log

- 2026-10-03 — Negative jet convolution and shifted complete-fibre laws checked in Lean; full native centering drafted and under audit.

- 2026-10-03 — Full native covariance, exact cumulative-plus-terminal identity and final production leaf pass Lean with empty diagnostics. Foundation audit running.

- 2026-10-03 — All twelve public foundation queries pass; only the three standard Lean foundations occur. Index exits 0; all twelve public declarations appear in LEAN_API.md. Global lint exits 1 on twelve unrelated unwired leaves, with no error in the new leaf.

Index/lint logs: `/tmp/tg-c912-index.log`, `/tmp/tg-c912-lint.log`.

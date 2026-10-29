# Prime stripping has an explicit additive harmonic error

- **ID:** ACP-UNIFORM-PRIME-STRIPPING
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Lean target:** `PrimeStrippingHasAnAdditiveHarmonicError.lean`

## Exact statement

Let omega be any completely multiplicative sign, and let F be a finite
prime set on which omega(p)=1. Write S_omega(N)=sum_(n<=N)omega(n)/n,
c_F=prod_(p in F)(p-1)/(p+1), and

`K_F=sum_(p in F)2(1+log p)/(p+1)`.

Then, for every N,

`|S_(finiteFlip(F)*omega)(N)-c_F S_omega(N)|<=K_F`.

If every p in F is at most Q and Q>=1, the same error is at most

`2(1+1/log 2)*(log Q+mertensFirstConst)`.

The constants are uniform in N and the remaining sign pattern omega.
With omega=1 this gives an explicit O(log Q) error for finite-prime harmonic
means, including prime sets growing with the integer horizon. No residual
harmonic mean, positivity estimate or analytic cancellation is assumed.

## Exact one-prime identity

For p prime with omega(p)=1, put nu=omega*finiteFlip({p}). The two gauges
agree off multiples of p, and multiplicativity counts that fibre exactly:

`p S_nu(N)+S_nu(floor(N/p))
 =p S_omega(N)-S_omega(floor(N/p))`.

Rearrangement yields

`(p+1)S_nu(N)-(p-1)S_omega(N)
 =[S_nu(N)-S_nu(floor(N/p))]
  +[S_omega(N)-S_omega(floor(N/p))]`.

Every signed shell has absolute value bounded by its unsigned harmonic
mass. The existing shell estimate bounds that mass by 1+log p. Division
by p+1>0 therefore gives

`|S_nu(N)-((p-1)/(p+1))*S_omega(N)|<=2(1+log p)/(p+1)`.

All identities hold also at N=0, where the sums are empty.

## Finite-set induction

Remove one p from F. The intermediate gauge finiteFlip(F without p)*omega
is still unflipped at p. Apply the one-prime estimate, then the induction
hypothesis. The new error is at most K_p+c_p K_(F without p), and
0<c_p<=1, so it is at most the additive sum K_F. The density factors
multiply exactly. This proves the first endpoint uniformly over the base
sign, rather than only for the constant sign.

## Growing-cutoff bound

For every prime p, log p>=log 2>0. Thus
`1+log p<=(1+1/log 2)log p`, and the positive denominators give

`2(1+log p)/(p+1)<=2(1+1/log 2)*log p/p`.

Sum over F and extend the nonnegative prime sum to all p<=Q. The existing
first elementary Mertens theorem gives
`sum_(p<=Q)log p/p<=log Q+mertensFirstConst`.
This proves the second endpoint with an explicit constant. All analytic
inputs are already unconditional theorems in the corpus.

## Scope and continuation

This is an arithmetic error bound, not complete Weil positivity. It supplies
an explicit currency for growing finite prime sets; it does not exchange
limits or assert continuity of optimal gaps. The proposed consequence for
the harmonic mean of every infinite prime pattern is preserved separately in
`../3-formalized/arithmetic-counting-all-prime-pattern-harmonic-density.md`.

Corpus searches found the existing one-prime error and an unspecified
finite-set error, but no bound uniform in the residual infinite sign. The
prime-sign construction and its classical mean-value background are reused;
no literature-wide priority claim is made.

- [x] Exact one-prime identity, finite-set induction and explicit cutoff bound.
- [x] Both Lean endpoints and standard transitive axiom audit.
- [x] Canonical installed-source check, umbrella and durable evidence.

## Lean endpoints and audit

PrimeStrippingHasAnAdditiveHarmonicError.lean proves finiteFlip_harmonic_stripping_error and
finiteFlip_harmonic_stripping_error_le_log_cutoff. Scratch 78550 and
canonical 25523 exited zero without diagnostics. Both transitive audits use
only propext, Classical.choice and Quot.sound. The adjacent audit records
actual axiom output, exact commands and source SHA256.

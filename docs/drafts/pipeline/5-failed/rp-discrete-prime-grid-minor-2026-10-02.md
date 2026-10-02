# Actual prime-grid minor and quotient profile

- **ID:** RP-29
- **Stage:** 5-failed
- **Type:** FALSIFIED; positive survivor THEOREM (Lean)
- **Source:** Route RP; complete signed arithmetic pair compensation.

## Target and conjecture

Write V(M,d)=divisorUnsignedDilationChannel M d and
c=log(2*pi)/2-gamma-1/4. A possible pair-sign ingredient was
V(M,1)V(M,p*q) <= V(M,p)V(M,q) for distinct primes p,q.
No implication from this ingredient alone to RH is assumed.

## Dependency-closed paper proof

For every fixed N>=1 and independent integer dilations a,b tending to infinity,
the exact homothety and the corpus's uniform unit-channel limit give

    [V(N*a*b,1)V(N*a*b,a*b)-V(N*a*b,a)V(N*a*b,b)]/(N*a*b)
       -> c*(V(N,1)/sqrt(N)-c).

Indeed the four normalized channels tend respectively to c, V(N,1)/sqrt(N),
c, and c. This retains the literal top product; it is not replaced by its
large-quotient limit. The corpus proves V(12,1)/sqrt(12)>=c+1/2000 and c>0
(the latter follows from its smooth mean >1/6). Thus every sufficiently large
pair of distinct primes gives a strictly positive minor at M=12*p*q.
At N=2 the corpus gives V(2,1)/sqrt(2)<=1/15, whereas c>1/12, so the
limiting minor is strictly negative. Prime infinitude supplies the same
cofinal actual prime pairs with opposite minor signs at 2*p*q and 12*p*q.
Every product index is active at both cutoffs. No new numerical experiment
or bound is needed. The four-channel minor is unchanged on replacing V by
the actual signed Möbius channels: the singleton signs both reverse and the
distinct-prime product has positive Möbius coefficient.

## No-go closure

- **Killing mechanism:** the actual quotient-12 overshoot survives the top
  product channel while all three proper quotient channels approach c.
- **Positive survivor:** coefficient-exact joint limit at every fixed quotient
  N, classifying the limiting sign by the actual normalized unit profile.
- **New insight:** continuous cusp failure did not address discrete primes.
  This argument uses distinct actual primes and macroscopic integer cutoffs.
- **Scope:** neither sign family bounds the complete pair sum. A positive
  unsigned minor is not itself a positive full Möbius energy increment.
- **Status:** paper proof closed on corpus ingredients. The 183-line leaf
  `RoutePDiscretePrimeGridMinor.lean` passed final foreground
  `lake --old env lean GaloisForLFunctions/RHTower/RoutePDiscretePrimeGridMinor.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/RoutePDiscretePrimeGridMinor.olean`,
  exit 0 without diagnostics, and is wired once into RHTower. No umbrella
  build ran. Separate `/tmp` axiom audit exited 0: all five public theorems
  depend exactly on `[propext, Classical.choice, Quot.sound]`.

## Exact Lean statements

- `routeP_prime_grid_minor_eq_signed`: literal Möbius sign transport.
- `routeP_prime_grid_minor_limit`: joint limit retaining every fixed quotient.
- `routeP_prime_grid_minor_positive_tail`: positive linear minor margin at 12*a*b.
- `routeP_prime_grid_minor_negative_tail`: negative linear minor margin at 2*a*b.
- `routeP_prime_grid_opposite_minors_cofinal`: same cofinal actual distinct
  primes, opposite signed-channel minors at two fully active cutoffs.

## Log

- 2026-10-02 — Corpus searches checked before code. Aggregate gcd and coprime
  rearrangements supplied no critical estimate. The discrete-grid candidate
  is tested independently using the exact quotient profile.
- 2026-10-02 — Final leaf and axiom audits passed; selected whitespace and
  forbidden-token/resource checks passed. Global lint failed on ten unrelated
  unreachable modules, with this leaf unflagged. No global pass claimed.

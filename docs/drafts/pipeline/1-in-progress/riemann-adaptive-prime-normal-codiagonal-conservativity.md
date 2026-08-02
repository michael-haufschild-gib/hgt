# Adaptive prime-normal codiagonal conservativity

- **ID:** `riemann-adaptive-prime-normal-codiagonal-conservativity`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / TOPOLOGICAL GATE SURVIVOR / NOT RH
- **Parent:** `riemann-mobius-theta-prime-normal-source-graph.md`
- **Frontier:** Route R polarized singular arithmetic descent
- **Statement:** One divisor-independent depth schedule makes the exact all-prime Mobius--theta residual codiagonal a Mobius diagonal plus an `l1` contraction, uniformly over primes at every fixed point of the open critical strip.

## Goal

Construct a source-derived completed arithmetic sector with a positive lower modulus.  This targets
the stability/conservativity gate in the updated Hellinger--Hodge Green-descent frontier.  It does
not assume Xi evaluation boundedness, Green-range support, RH, or a target spectral measure.

The theorem is useful only because its columns are the exact physical residual coefficients already
proved by `mobiusThetaInternalJetPrimeNormalResidualFourierLaplace_eq`; an arbitrary triangular
change of coordinates or a norm defined from its inverse would be theatre.

## Exact source matrix

Let `P` be the set of ordinary primes, let `s` lie in the open critical strip, and put

```text
m(p,N) = 8 p N.
```

For `p in P` and `n in N`, define

```text
C_(N,s)(n,p)
  = 0                                      if n < p,
  = mu(n) (p/n)^(m(p,N)s)                 if p <= n.       (APN-1)
```

Complex powers use the positive real ratio.  This is exactly the coefficient of channel `n` in the
full recentered Mobius--theta prime-normal residual at exponent `m(p,N)`.  Its head is

```text
C_(N,s)(p,p) = mu(p) = -1.                              (APN-2)
```

For `a in l1(P,C)`, define the arithmetic codiagonal

```text
(A_(N,s)a)(n) = sum_(p in P, p<=n) a(p) C_(N,s)(n,p).   (APN-3)
```

The sum in each row is finite.  Write `D a` for the prime-supported Mobius diagonal and `K_(N,s)`
for the strict tail, so `A_(N,s)=D+K_(N,s)`.

## Dependency-closed paper proof

`[PROVED HERE: APN-TAIL] [PROVED HERE: APN-CODIAGONAL]`

### 1. Uniform quarter-tail bound

Fix `p>=1`, put `n=p+j+1`, and assume

```text
N Re(s) >= 1/2.                                        (APN-4)
```

The exact residual norm law gives

```text
|C_(N,s)(p+j+1,p)|
 <= (p/(p+j+1))^(8 p N Re(s))
 <= (p/(p+j+1))^(4p).                                  (APN-5)
```

The second inequality uses `0<p/(p+j+1)<1` and `(APN-4)`.  Bernoulli's inequality gives

```text
(1+(j+1)/p)^p >= 1+p((j+1)/p)=j+2,
```

hence

```text
(p/(p+j+1))^(4p) <= 1/(j+2)^4.                         (APN-6)
```

For every `j>=0`,

```text
1/(j+2)^4 <= (1/4) / ((j+1)(j+2)),                     (APN-7)
```

because `4(j+1)<=(j+2)^3`.  The right side telescopes:

```text
sum_(j>=0) 1/((j+1)(j+2))
 = sum_(j>=0) (1/(j+1)-1/(j+2)) = 1.                  (APN-8)
```

Therefore every prime column obeys the divisor-independent uniform bound

```text
sum_(n>p) |C_(N,s)(n,p)| <= 1/4.                       (APN-9)
```

No prime-counting estimate is used.

### 2. Full infinite synthesis

Tonelli for the nonnegative absolute-value array and `(APN-9)` give, for every
`a in l1(P,C)`,

```text
||K_(N,s)a||_1
 <= sum_p |a(p)| sum_(n>p)|C_(N,s)(n,p)|
 <= (1/4)||a||_1.                                      (APN-10)
```

Thus `(APN-3)` defines one bounded all-prime codiagonal on the complete coefficient space.  Since
ordinary primes have `mu(p)=-1`, `D` is an isometric embedding:

```text
||Da||_1=||a||_1.                                      (APN-11)
```

The reverse triangle inequality now yields

```text
||A_(N,s)a||_1
 >= ||Da||_1-||K_(N,s)a||_1
 >= (3/4)||a||_1.                                      (APN-12)
```

Consequently `A_(N,s)` is injective, anti-Lipschitz, and has closed range.  Its inverse on its
range has norm at most `4/3`.  Equivalently, after identifying the prime-supported diagonal with
`l1(P,C)`, the completed arithmetic sector is `identity + strict contraction` and is recovered by
the Neumann series.

### 3. One global source schedule works pointwise on the whole strip

The schedule `m(p,N)=8pN` is fixed before any divisor is selected.  For each fixed open-strip point
`s`, `Re(s)>0`, so `(APN-4)` holds for every sufficiently large `N`.  The same threshold works for
all primes simultaneously.  Hence every actual Xi divisor point sees the same cofinal source
schedule and eventually the same lower modulus `3/4`; only the entry stage depends on the point.

This is stronger than separate prime isolation: it proves simultaneous countable codiagonal
conservativity on a complete source coefficient space.

## Hostile anti-theatre audit

1. **Triangular recoding.**  All-order invertible coordinates alone add no positivity or source
   information.  Here `(APN-1)` is the already-constructed physical Mobius--theta residual, and
   `(APN-9)` is a new uniform source estimate.  Verdict: survivor is source-specific.
2. **Finite-prefix fitting.**  `(APN-10)` is on full `l1`, not finite support; closed range follows
   on the Banach completion.  Verdict: excluded.
3. **Divisor-fed damping.**  `m(p,N)=8pN` depends only on ordinary prime and cofinal depth, never on
   `s`, Xi, or a zero.  Verdict: excluded.
4. **Product/Hilbert vertical saturation.**  Existing saturation retains infinitely many collapsing
   exponent packets in one common fibre.  The new sector retains the arithmetic row support before
   collapse and has an explicit lower modulus.  This is the index-dependent source renormalization
   survivor allowed by the saturation theorem, not a contradiction to it.
5. **Hidden RH.**  Only `0<Re(s)<1`, `|mu(n)|<=1`, Bernoulli, Tonelli, and exact residual coefficients
   are used.  Verdict: unconditional.
6. **Does this prove admission?**  No.  It closes a coefficient-level stability gate but does not yet
   identify the actual Green resolved range with this sector, build its Gamma/co-Poisson reporter,
   or derive four-unit Gram domination.  Claiming RH here would be false.
7. **Does the prime head reach Gamma incidence?**  Interval transgression sees strict tails; the
   zero-length head must remain as the affine boundary coordinate.  Any next reporter must therefore
   be nondivisive and retain `head direct-sum interval`, not discard the head after proving stability.

## New frontier after this theorem

Construct the bounded source-derived map

```text
closed adaptive arithmetic sector
  -> affine-head direct-sum Gamma/co-Poisson interval reporter
  -> coefficient-faithful Hellinger/Hodge incidence,                 (APN-13)
```

prove that `(APN-13)` preserves the `3/4` lower modulus through the forced singular completion, and
derive the four-unit Gram domination relative to the actual Green resolved range.  The present
theorem removes countable codiagonal instability as an excuse: remaining loss, if any, is precisely
the affine Gamma/Hermitian edge.

## Gates

- [x] 0 -> 1: source-pure exact claim and hostile audit
- [x] 1 -> 2 mathematical content: dependency-closed paper proof `(APN-1)`--`(APN-12)`
- [ ] 1 -> 2 pipeline move: formal theorem and audit complete
- [ ] 2 -> 3: unconditional Lean module, umbrella wiring, targeted build, axiom audit
- [ ] Route-R consumer: construct and calibrate `(APN-13)`

## Lean plan

1. Prove exact pointwise Bernoulli/telescoping quarter-tail estimate for the existing residual
   coefficient at `m=8pN`.
2. Package each full exact column in `lp (fun _ : Nat => C) 1`.
3. Construct the all-prime synthesis `lp (fun _ : Nat.Primes => C) 1 ->L
   lp (fun _ : Nat => C) 1` by summing its absolutely summable column family.
4. Prove tail operator norm at most `1/4`, exact Mobius diagonal isometry, lower bound `3/4`,
   injectivity, and closed range.
5. Wire through `GaloisForLFunctions.RHTower` and audit only the new module.

## Log

- 2026-08-02 — Full residual source-to-Xi landing and eventual single-prime nonannihilation proved
  in Lean.
- 2026-08-02 — Global adaptive schedule, uniform quarter-tail law, and all-prime closed-range
  codiagonal theorem paper-proved; exact Gamma/Hermitian successor isolated.

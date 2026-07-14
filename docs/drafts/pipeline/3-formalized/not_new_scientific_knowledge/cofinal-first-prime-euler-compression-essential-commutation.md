# Cofinal anchored Euler commutators suffice for RH

- **ID:** `cofinal-first-prime-euler-compression-essential-commutation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[TOP-DOWN GAP SIMPLIFICATION]`, `[VALUE INTERFACE]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPrimeSeamCofinalAnchoredCommutator.lean`
- **Parent:** `semilocal-compressed-euler-constraint-orientation.md`
- **Statement:** On each Xi divisor fibre, compactness of the two-prime compressed Euler source
  commutator for the anchored packets `{2,q}` at arbitrarily large primes `q` is equivalent to RH.

## Exact reduction

For a fixed positive Sonin aperture `a`, a strip point `rho`, and a prime `q>2`, let

```text
p=(2,q),
u=(a_2(rho),a_q(rho)),
T_u=P_a (u_0 G_2+u_1 G_q) P_a,
T_1=P_a (G_2+G_q) P_a,                                  (1)
```

where

```text
a_p(rho)=log(p)(p^(-conj(rho))-p^(-(1-rho)))              (2)
```

and `G_p` is the literal positive Euler Gram multiplier on the Hardy--Titchmarsh source line.
The finite quadratic Calkin injection and the exact compression identity give

```text
[T_u,T_1] is compact  <->  a_2(rho)=a_q(rho).             (3)
```

Lean packages the commutator as

```text
firstPrimeAnchoredEulerCompressionCommutator a rho q
```

and proves `(3)` as

```text
firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff.
```

Using the rational-Hurwitz distribution law already formalized in the corpus, Lean also identifies
the same compactness event with the finite value relation

```text
rationalHurwitzFiberReflectionSeam 2 rho
  = rationalHurwitzFiberReflectionSeam q rho.              (3a)
```

Every Hurwitz value in `(3a)` is shifted into its half-plane of absolute convergence. This does
not prove the equality, but it removes analytic continuation at the divisor point from the
remaining source interface.

## Cofinal collapse

The crucial weakening is that `(3)` need not hold for every prime, every prime pair, or every
finite packet. Suppose only that, for each Xi divisor point `rho` and each threshold `N`, there is
a prime

```text
q > max(N,2)                                               (4)
```

for which the anchored commutator is compact. Then `(3)` identifies `a_q(rho)` with the fixed
value `a_2(rho)` along a cofinal prime subnet. Independently, the open-strip source formula gives

```text
a_q(rho) -> 0  as q -> infinity.                           (5)
```

Therefore `a_2(rho)=0`. The first-prime seam criterion gives `Re rho=1/2`, fibre by fibre.

The global source property is

```text
XiCofinalFirstPrimeEulerCompressionEssentiallyCommuting a.
```

Lean proves the exact endpoint

```text
XiCofinalFirstPrimeEulerCompressionEssentiallyCommuting a
  <-> RH                                                   (6)
```

for every `a>0`. It also proves directly that the former all-finite-packet hypothesis implies
this cofinal anchored property.

## New proof obligation

The source-side target is now strictly smaller in quantifiers:

```text
[OPEN] For every actual Xi divisor rho and every N,
       produce one prime q>N such that
       [T_(a_2(rho),a_q(rho)), T_1] is compact.             (7)
```

No uniformity in `q`, no compactness for a prescribed prime, no compatibility between the chosen
primes on different fibres, and no all-prime operator sum is required. A source construction may
therefore discard an arbitrary finite exceptional set separately on each divisor fibre.

The known semilocal geometry does not yet prove `(7)`. Individual nonarchimedean local ratios are
not quasi-inner, and Lean proves the corresponding one-prime Sonin normal is noncompact. The
relevant literature instead supplies two possible ends of a future value relation:

- Connes--Consani, [*Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974),
  proves compact Hardy off-diagonal blocks only after finite prime--archimedean completion.
- Connes--Consani--Moscovici,
  [*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423), supplies the
  semilocal Sonin square and its flat primal--dual pairing.
- Burnol,
  [*Two complete and minimal systems associated with the zeros of the Riemann zeta function*](https://arxiv.org/abs/math/0203120),
  supplies bounded zero and multiplicity-jet evaluators indexed by the full zeta divisor.

No cited source proves the anchored compactness in `(7)`. The positive reduction is that a future
Burnol/semilocal value theorem only has to produce a compact completed remainder for one
arbitrarily large partner prime per fibre.

## Gates

- [x] define the anchored two-prime packet and compressed source commutator
- [x] prove compactness iff equality of the two seam charges
- [x] identify each anchored compactness event with a finite convergent rational-Hurwitz value relation
- [x] prove cofinally many compact anchored commutators force the first-prime charge to vanish
- [x] prove the global cofinal anchored condition iff RH
- [x] prove the all-finite-packet condition implies the cofinal anchored condition
- [x] import the module through the `RHTower` umbrella
- [ ] produce the cofinal compact source remainder in `(7)` from an actual divisor value relation

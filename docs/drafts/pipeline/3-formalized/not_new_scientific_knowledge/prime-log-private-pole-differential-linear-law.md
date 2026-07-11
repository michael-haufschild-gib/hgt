# Prime-log private-pole differential-linear law

- **ID:** `prime-log-private-pole-differential-linear-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED] [FORMALIZED] [BRIDGE]`
- **Lane:** prime-log Herglotz source geometry; finite complex-translation packets
- **Statement:** Distinct complex translates of the prime-log divisor share at most one pole.
  Consequently every translate in a finite packet has infinitely many private poles, and every
  nontrivial finite constant-coefficient differential combination of the corresponding prime-log
  Herglotz translates is nonzero.

## The law

Put `lambda_p=log p` for primes `p`.  The exact oriented-difference law is

```text
lambda_p-lambda_q=lambda_r-lambda_s
  iff (p=r and q=s) or (p=q and r=s).                         (1)
```

Indeed, exponentiation gives `p/q=r/s`, hence `ps=rq`.  If `p=q`, injectivity gives `r=s`.
Otherwise primality forces `p=r`, and cancellation then gives `q=s`.

For complex shifts `h!=k`, a common translated pole has the form

```text
lambda_p-h=lambda_q-k.                                       (2)
```

Two different solutions `(p,q)` and `(p',q')` to (2) give equal oriented differences.  Equation
(1) either identifies both ordered pairs or puts both pairs on the diagonal.  The diagonal case
would force `h=k`, so it is impossible.  Thus the two translated divisors share at most one pole.

For a finite shift packet `H` and `h in H`, at most one source prime is lost to each `k in H\{h}`.
The union of these collision sets is finite.  Its complement is therefore infinite, and every
prime in that complement gives a pole of the `h`-translate belonging to no other packet member.

Now let

```text
g_u(z)=sum_p 2^(-p) exp(u_p)/(log p-z),
```

where `u` is bounded above.  Every declared pole is simple with nonzero residue.  If

```text
sum_(h in H) L_h(D) g_u(z+h)=0                               (3)
```

and some `L_h` is nonzero, choose a private pole for that `h`.  The summand `L_h(D)g_u(z+h)` has
exact pole order `-(deg L_h+1)`, while all other summands are analytic there.  The most singular
order cannot cancel, contradicting (3).  Hence every `L_h` is zero.

This proves differential-linear independence over the constant-coefficient operator ring.  It
does not prove nonlinear differential-algebraic independence over `C(z)`.

## Lean certificate

The source geometry is formalized in
`GaloisForLFunctions.HTGeometry.PrimeLogTranslationGeometry`:

- `primeLogSupport_sub_eq_sub_iff` proves (1);
- `primeLogComplexShiftCollisionPrimes_subsingleton` proves the one-collision law;
- `infinite_primeLogComplex_privatePrimes` proves infinite private-pole supply.

The analytic conclusion is formalized in
`GaloisForLFunctions.HTGeometry.PrimeLogDifferentialLinearIndependence`:

- `meromorphicOrderAt_primeLogHerglotz` proves exact simple-pole order;
- `meromorphicOrderAt_primeLogTranslate` transports it to every complex translate;
- `finite_primeLogTranslate_differentialCombination_ne_zero` proves (3) is impossible whenever
  one operator is nonzero.

All declarations have only the standard foundational dependencies `propext`, `Classical.choice`,
and `Quot.sound`.

## Classification

The additive Sidon property of prime logarithms is an elementary consequence of unique
factorization, and private-pole differential separation is a standard principal-part mechanism.
The result is therefore infrastructure for the facet-sewn nonlinear matroid theorem, not new
scientific knowledge.  Its geometric value is exact: it removes every pole-collision obstruction
from finite complex-translation packets and isolates nonlinear jet transversality as the sole
remaining source-freeness problem.

## Gates

- [x] 0 → 1: exact source-geometric statement isolated
- [x] 1 → 2: complete unconditional paper proof
- [x] 2 → 3: unconditional Lean theorem, module build, lint, and axiom audit
- [ ] 3 → 4: no publication planned; classified as a bridge

# Positive prime-tail translation and failure of continuation limits

- **ID:** RH-PTT-20260906
- **Stage:** 3-formalized
- **Type:** CLOSED LEAN AUDIT; not new mathematical knowledge or an RH architecture
- **Source:** current corpus research search plus `rg` on statements and proof bodies
- **Statement:** Positive completely multiplicative coefficients can retain every finite zeta
  prefix and converge in every weighted square distance below, while their analytic
  continuations are zero-free and fail to converge to zeta at every real point in `(0,1)`.

## Exact construction and closed result

For real `t >= 0`, change only primes above a cutoff:

```
a_(N,t)(p) = 1                 if p <= N,
           p^(-t)             if p > N,
a_(N,t)(n) = product_p a_(N,t)(p)^v_p(n),  n >= 1,
a_(N,t)(0) = 0.

F_(N,t)(s) = zeta(s+t) * product_(p <= N)
              (1-p^(-s-t))/(1-p^(-s)).
```

The source is strictly positive on positive integers and completely multiplicative, bounded
by one, and agrees with every coefficient of zeta through `N`. Its ordinary Dirichlet series
converges absolutely and equals `F_(N,t)` on `Re(s)>1`. On `Re(s)>0` the finite quotient is
analytic and nonzero. Thus `F_(N,t)(s)=0` if and only if `zeta(s+t)=0` there. For general `t`,
`F_(N,t)` can have the shifted zeta pole; the analytic claim for the whole positive half-plane
below uses `t=2`.

For every fixed `sigma > 1/2`, its squared coefficient distance to the literal all-one source
obeys

```
sum_(n >= 1) |a_(N,t)(n)-1|^2 / n^(2 sigma)
  <= sum_(n > N) 1/n^(2 sigma)  --> 0.
```

The bound is independent of `t`. Lean proves convergence even for every arbitrary sequence
of nonnegative shifts `t_N`, without a bound on that sequence.

At the fixed shift `t=2`, every `F_(N,2)` is analytic and zero-free on `Re(s)>0`. Nevertheless,
for every fixed real `0<sigma<1`,

```
not Tendsto (N ↦ F_(N,2)(sigma)) (zeta(sigma)).
```

This nonconvergence follows from opposite signs of real parts, not from the zero-free claim:
`Re F_(N,2)(sigma)>0` for every `N`, whereas `zeta(sigma)<0`. It needs no actual zeta zero,
numerical zero approximation, or zero-location hypothesis.

## Dependency-closed paper proof

1. Unique factorization makes `a_(N,t)` completely multiplicative. Every prime value is in
   `(0,1]`. Each prime divisor of `1<=n<=N` is at most `N`, giving `a_(N,t)(n)=1`.
2. The squared error is at most one and vanishes for `n<=N`. The displayed tail estimate
   follows; the convergent positive series `sum n^(-2 sigma)` makes its tail tend to zero.
   The Lean proof uses dominated convergence and eventual exact equality of each coefficient.
3. Since `|a_(N,t)(n)|<=1`, the ordinary Dirichlet series is absolutely convergent on `Re(s)>1`.
   Its completely multiplicative Euler product differs from that of `zeta(s+t)` exactly at
   the primes at most `N`, yielding the stated finite quotient.
4. For every prime `p` and `Re(s)>0`, `|p^(-s)|<1`. Both numerator and denominator in the finite
   quotient are nonzero when `t>=0`. They are analytic functions of `s`; hence so is the
   quotient. At `t=2`, `Re(s+2)>2`, where zeta is analytic and nonzero. This proves the asserted
   analytic continuation and zero-free property.
5. For real `sigma>0`, both sides of each Euler quotient are positive real numbers, and
   `zeta(sigma+2)>0` by its positive ordinary series. Hence `Re F_(N,2)(sigma)>0`. For
   `0<sigma<1`, the existing paired alternating-series identity gives `zeta(sigma)<0`: its
   paired series has positive sum and its factor `1-2^(1-sigma)` is negative. A limit of
   nonnegative real parts cannot be negative. This proves the nonconvergence assertion.

## Scope and consequence for RH research

Coefficient convergence in these weighted distances does not justify taking a limit after
analytic continuation. Failure of that interchange also occurs at regular, nonzero real
values of zeta, so failure alone cannot detect a zeta zero or its horizontal location.

The functions vary with `N`; no single different function has all zeta coefficients. No
functional equation is imposed on the approximants. The result does not exclude a stronger
topology with an independently proved arithmetic estimate, and says nothing about whether
the actual nontrivial zeros lie on the critical line.

## Corpus and ancestry gates

- `TwoProductDiagonalGaugeRigidity` was read in full; its proposed Mellin realization is already
  retired in `5-failed/universal-law-field/two-product-gauge-occurrence/`.
- `FormalInvolutionJetRigidity` supplies rigidity conditional on a constructed commuting action;
  `EulerSquarefreeWickProjectiveTransgressionNoGo` already uses that theorem to reject its local
  gauge repair. No zero-forced arithmetic action was found.
- `PrimeShiftResidueClosability` already contains an RH-equivalent residue-graph closability
  criterion. Replacing the missing source law by that criterion would not supply a new producer.
- `HelsonFinitePrefixDivisor` already gives prescribed off-line divisors with arbitrary exact
  finite prefixes, using complex unimodular coefficients. The present test is the explicit
  positive coefficient family obtained from a shifted zeta function and finite Euler factors.
- Searches included `prime tail derivative`, `continuation closable`, `tail shift Euler`,
  `prefix shift`, `prime restored`, and `rough Dirichlet`, followed by `rg` of the sources.
  Search misses are not novelty certificates. These were wide discovery searches followed by
  specific proof-body audits, not a reading of every declaration in the corpus.
- The construction uses the classical [Euler product](https://dlmf.nist.gov/25.2.E11), a
  horizontal shift, and a finite correction. The real-strip sign uses the classical
  [alternating-series representation](https://dlmf.nist.gov/25.2.E3). Packaging these facts
  together supplies a useful formal audit witness, not a new mathematical mechanism.
- Prime-coordinate derivations and the logarithmic derivation are published algebraic tools:
  [Algebraic independence of arithmetic functions](https://www.impan.pl/shop/publication/transaction/download/product/91275).
  Meromorphic continuation using derivations is also published:
  [Emmons, 2011](https://www.tandfonline.com/doi/abs/10.4169/amer.math.monthly.118.06.551).
  The latter abstract was checked; its full proof was not obtained. Neither reference is claimed
  to state this exact packaged test. The construction uses elementary shifted Euler products;
  no new mathematical mechanism or absence from literature is claimed.

## Lean and verification

[PrimeTailTranslation.lean](../../../../../formal/GaloisForLFunctions/RHTower/PrimeTailTranslation.lean)
contains the premise-free capstone
`RHTower.PrimeTailTranslation.positive_zero_free_tail_approximation`, bundling the positive
bounded coefficients, every exact finite prefix, analytic zero-free continuations, ordinary
series identity, weighted convergence, and real-strip nonconvergence. Complete multiplicativity
is part of the coefficient map's type. The separate `squaredDistance_tendsto_zero` theorem
allows arbitrary nonnegative shift schedules; `continued_zero_iff` allows every nonnegative
shift on `Re(s)>0`.

- Scratch and direct production checks passed using `lake env lean <file>`.
- Final serialized leaf audit passed:
  `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.PrimeTailTranslation`.
  Only this leaf was rebuilt against cached dependencies. It is wired into `RHTower.lean`;
  no full or umbrella build ran.
- An imported scratch audit of all 26 public theorems reports only `propext`, `Classical.choice`,
  and `Quot.sound`. No additional axiom, admitted proof, or computed certificate is used.
- Repository formal lint passed, with large-file warnings.
- No mathematical computation or Runpod experiment was needed for this result.

## No-go closure

The failed claim is coefficient-only continuity of the continued values under these prefix,
positivity, multiplicativity, and weighted-distance controls. The strongest proved positive
statement is the explicit approximation family, including arbitrary nonnegative shift schedules
and the exact translated-zero identity. A second pass strengthens the failure witness to every
real point of `(0,1)` and shows why it is not zero-specific. Both are closed above.

This survivor is an elementary consequence of classical Euler products and continuation, so it
does not meet the requested novelty gate. **NO POSITIVE SALVAGE FOUND as a new RH producer.**
The global RH search remains active; its new zero-forced arithmetic relation and off-line
contradiction are still missing. See the [retired principle](../../5-failed/prime-tail-coefficient-continuation.md).

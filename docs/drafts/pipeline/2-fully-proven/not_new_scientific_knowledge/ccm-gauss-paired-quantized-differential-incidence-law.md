# Gauss-paired quantized differentials transport prime incidence linearly through the trace

- **ID:** `ccm-gauss-paired-quantized-differential-incidence-law`
- **Stage:** 2-fully-proven / paper proof complete
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent sources:** Connes--Consani's quantized-calculus formulation of local Weil terms and their
  Gauss-paired quasi-inner factorization
- **Statement:** A finite product of commuting unitary local-ratio multipliers retains every local
  quantized differential as a conjugated degree-one channel before tracing. Any commuting test
  smoothing that makes the local channels trace class turns the total trace into their exact sum.
  Thus the Connes finite-place product simultaneously carries multiplicative covariance and the
  unsquared additive local Weil functional.

## 1. Finite-product quantized-differential identity

Let `H` be a complex Hilbert space, let

```text
F=F^*=F^(-1)                                                   (1)
```

be a self-adjoint unitary, and let `U_1,...,U_m` be pairwise commuting unitaries. Put

```text
U=U_1...U_m,
W_j=U_(j+1)...U_m,       W_m=1.                               (2)
```

For the quantized differential

```text
dU=[F,U],                                                       (3)
```

one has the exact operator identity

```text
U^*dU=sum_(j=1)^m W_j^* U_j^*[F,U_j]W_j.                      (4)
```

### Proof

The commutator Leibniz rule gives

```text
[F,U]=sum_j U_1...U_(j-1)[F,U_j]U_(j+1)...U_m.                (5)
```

Multiplying by `U^*` on the left and cancelling the factors preceding `U_j` gives `(4)`. No
commutation with `F` is used. The tail conjugations in `(4)` are therefore not optional error
terms: they are the exact multiplicative covariance retained by the product.

## 2. Exact trace additivity after legitimate smoothing

Let `A` be a bounded operator commuting with every `U_j`. Assume

```text
A U_j^*[F,U_j] is trace class for every j.                     (6)
```

Then `(4)` implies that `A U^*[F,U]` is trace class and

```text
Tr(A U^*[F,U])
 =sum_(j=1)^m Tr(A U_j^*[F,U_j]).                              (7)
```

Indeed, because `A` commutes with `W_j`, the `j`-th smoothed summand in `(4)` is

```text
W_j^*(A U_j^*[F,U_j])W_j.                                     (8)
```

It is trace class and has the same trace as `A U_j^*[F,U_j]` by unitary invariance of the trace.
Finite summation proves `(7)`.

The trace-class hypothesis is load-bearing. Equation `(7)` is not an appeal to a formal cyclic
renormalized trace; it applies only after the chosen test or resolvent smoothing has established
the ordinary trace domain.

## 3. Gauss-paired Connes--Consani specialization

Let

```text
S_f={p_1,...,p_m}                                              (9)
```

be a finite set of rational primes. Gauss multiplication factorizes the single archimedean local
ratio as

```text
rho_infinity=product_(j=1)^m rho_infinity^(m,j).               (10)
```

Define the paired boundary multipliers

```text
u_j=rho_infinity^(m,j)rho_(p_j),
u_S=product_j u_j=rho_infinity product_(p in S_f)rho_p,        (11)
U_j=M_(u_j),
U_S=M_(u_S).                                                   (12)
```

Connes--Consani prove that every `u_j` and the product `u_S` are quasi-inner on the relevant Hardy
half-plane. With `P` the Hardy projection and

```text
F_H=2P-1,                                                      (13)
```

equation `(4)` becomes

```text
U_S^*[F_H,U_S]
 =sum_j W_j^*U_j^*[F_H,U_j]W_j,                               (14)
```

while unitarity gives

```text
U_S^*[F_H,U_S]=2(U_S^*PU_S-P).                                (15)
```

For a scaling test multiplier `A=theta(f)` commuting with all boundary multipliers, any source
theorem establishing `(6)` therefore yields

```text
Tr(theta(f)U_S^*[F_H,U_S])
 =sum_j Tr(theta(f)U_j^*[F_H,U_j]).                            (16)
```

The local Weil contributions are consequently transported at degree one, without squaring their
Euler coefficients. At the same time, the untraced operator `(14)` retains the conjugated channel
geometry needed for prime--prime covariance and Sonin compression.

This is the positive carrier forced by
`ccm-coherent-euler-logarithm-square-exclusion-law.md`: resolve the local directions before taking a
positive square, carry their exact multiplicative covariance, and recover additivity only after a
legitimate trace-class smoothing.

## 4. Coefficient--state accounting

On the critical line, the finite-prime ratio `rho_p(1/2+it)` is a nonconstant rational function of
`exp(-it log p)`. Hence the finite coefficient vector

```text
a_S=(rho_p)_(p in S_f)                                        (17)
```

is jointly Bohr almost periodic and has rational frequency module

```text
Gamma(a_S)=span_Q{log p:p in S_f}.                             (18)
```

Thus in the coefficient--state budget of
`nonautonomous-kolchin-frequency-budget-law.md`, the canonical channel-resolved finite-prime
multiplier pays the entire arithmetic rank in its coefficient hull:

```text
A_S=V_S/(V_S intersection Gamma(a_S))=0.                      (19)
```

There is no additional Kolchin-state charge to pay for the same prime characters. Conversely, if a
compression, scalar trace, or limit forgets some coefficient channels, the exact quotient of the
forgotten submodule must reappear in the relative state kernel or another explicitly global
carrier. This is the precise sense in which every prime direction is paid once rather than twice.

More generally, if a jointly almost-periodic coefficient/solution realization retains `V_N`, and
its nondegenerate fixed-coefficient scalar ADE has order `n_N` and degree `d_N`, then the
coefficient--state law and the bounded-syntax capacity theorem combine to give

```text
pi(N)
 <=dim_Q(V_N intersection Gamma(a_N))+2B(n_N,d_N).            (19a)
```

Consequently cofinal prime transport continuously pays through growing order, growing degree,
coefficient-side frequency, or state outside bounded finite Kolchin capacity. In the canonical
Gauss-paired realization `(17)`--`(19)`, the payment is explicitly coefficient-side.

The Gamma components in `(10)` are not asserted to be Bohr almost periodic. Equation `(19)` applies
to the finite-prime coefficient vector `(17)`, not to an unsupported almost-periodic hull for the
full archimedean product.

## 5. Positive Connes requirement

The finite-place source already supplies all three structural pieces:

```text
prime incidence in the labeled coefficient channels
  + multiplicative covariance in the conjugated sum (14)
  + additive local Weil trace after smoothing (16).           (20)
```

Therefore a successful cofinal Connes construction must extend `(20)` through the growing-prime
and growing-aperture limit by proving:

1. a uniform trace-class or relative-trace domain for the smoothed channel sum;
2. preservation of the coefficient incidence `(18)` until the corresponding local Weil term has
   entered the trace;
3. positivity of the resulting Sonin/restricted-Weil compression;
4. index- or divisor-preserving convergence to the global Weil operator or to `Xi`.

The missing theorem is no longer the construction of the von Mangoldt coefficient. It is uniform
positivity and cofinal transport of the already exact degree-one finite-place carrier.

## 6. Exact scope

- `[SEARCH]` Gauss factorization, quasi-innerness, and the local quantized-differential trace
  interpretation belong to Connes--Consani.
- `[PROVED]` Equations `(4)` and `(7)` are finite operator-algebra consequences of Leibniz and
  ordinary trace cyclicity.
- `[PROVED]` The finite prime coefficient vector has the exact module `(18)`.
- `[NOT PROVED]` No uniform trace-ideal estimate in `|S_f|` is established here.
- `[NOT PROVED]` No positivity of the full semilocal trace remainder is established here.
- `[NOT PROVED]` No cofinal index/divisor transport is established here.
- `[NOT PROVED]` This theorem does not prove RH.

## 7. Scientific classification and Lean decision

The operator identity is standard, and its application only exposes the architecture already
present in the Connes--Consani construction. It is a corpus bridge, not new scientific knowledge.

The current Lean tree lacks the Hardy multiplier, trace-class ideal, and quasi-inner infrastructure
needed to certify `(16)`. Formalizing only the finite Leibniz identity would be a wrapper around the
analytic theorem rather than progress on RH. No Lean file is added.

## Gates

- [x] exact finite-product quantized-differential identity
- [x] exact trace additivity under an ordinary trace-class hypothesis
- [x] Gauss-paired local-factor specialization
- [x] coefficient--state prime budget identified without double counting
- [ ] uniform cofinal trace-class or relative-trace theorem
- [ ] semilocal Sonin trace-remainder positivity
- [ ] index/divisor transport to the true restricted-Weil operator or `Xi`
- [ ] RH

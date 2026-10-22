# Gauss-paired quantized differentials transport prime incidence linearly through the trace

- **ID:** `ccm-gauss-paired-quantized-differential-incidence-law`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
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

## 2a. Canonical descent modulo conjugation coboundaries

The product identity has a factorization-independent quotient form. In any unital algebra with a
derivation `delta`, put

```text
omega(U)=U^(-1)delta(U)                                      (8a)
```

for invertible `U`. The Leibniz rule gives the crossed-homomorphism identity

```text
omega(UV)=V^(-1)omega(U)V+omega(V).                          (8b)
```

Let `Coinv` be the additive quotient by the span of conjugation coboundaries

```text
V^(-1)TV-T.                                                  (8c)
```

Then `(8b)` becomes the exact homomorphism law

```text
[omega(UV)]=[omega(U)]+[omega(V)] in Coinv.                  (8d)
```

Consequently every finite factorization of the same multiplier defines the same class. In
particular, for a Gauss splitting

```text
rho_infinity=product_k g_k
```

and any pairing `w_k=g_krho_(p_k)`, commutativity of the boundary multipliers gives

```text
sum_k[omega(w_k)]
 =[omega(rho_infinity)]+sum_(p in F)[omega(rho_p)]
 =[omega(rho_infinity product_(p in F)rho_p)].               (8e)
```

Thus Gauss splitting and the bijection between components and primes do not create ambiguity at the
cyclic-coinvariant level. Their dependence lives entirely in explicit conjugation coboundaries.
Every conjugation-invariant trace annihilates `(8c)`, recovering `(7)`.

This closes the **algebraic Gauss-descent** problem. It does not choose a positive representative of
the class: squaring, Hardy compression, Schatten norm, and negative index do not factor through
`Coinv`. The RH-bearing datum must therefore be a pointed positive/relative lift of `(8e)`, selected
by the Hardy polarization, Sonin projection, cyclic vector, or determinant line.

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
- [x] factorization- and pairing-independent descent to the cyclic coinvariant class
- [x] Gauss-paired local-factor specialization
- [x] coefficient--state prime budget identified without double counting
- [ ] uniform cofinal trace-class or relative-trace theorem
- [ ] semilocal Sonin trace-remainder positivity
- [ ] index/divisor transport to the true restricted-Weil operator or `Xi`
- [ ] RH

## Lean status

**Formalized unconditionally, 2026-08-15**, in
`formal/GaloisForLFunctions/RHTower/CCM/CCMGaussPairedQuantizedDifferential.lean`, on the commutator
calculus of `RHTower/CCM/CCMSoninEdgeTrace.lean`.  The earlier decision ("formalizing only the finite
Leibniz identity would be a wrapper") measured the wrong object: the card's `[PROVED]` list is
exactly `(4)`, `(7)`, the coinvariant descent `(8a)`--`(8e)`, the reflection form `(15)`, and the
frequency module `(18)`, and none of these needs the analytic Hardy/quasi-inner layer.

- `logQuantizedDifferential F U = U⁻¹ [F, U]` and `logQuantizedDifferential_one` — equation `(8a)`.
- **`logQuantizedDifferential_mul`** — equation `(8b)`, the crossed-homomorphism law.  Only the
  Leibniz rule and `U⁻¹U = 1` are used; `F² = 1` and self-adjointness are not.
- `channelSum`, **`logQuantizedDifferential_list_prod`** — equations `(4)`--`(5)`: the exact
  conjugated channel decomposition of a finite factorization, with the tail conjugations retained.
  Stated for `List Rˣ`, so no commutativity of the factors is assumed.
- **`trace_logQuantizedDifferential_list_prod`** — equation `(7)`: any conjugation-invariant additive
  functional turns the channel decomposition into a plain sum over the factors.  This is the exact
  algebraic content of the card's trace step; the trace-class hypothesis `(6)` is what supplies such
  a functional and is not re-proved.
- `conjCoboundary`, `CyclicCoinvariants`, `conj_sub_mem_conjCoboundary`,
  **`coinv_logQuantizedDifferential_mul`**, **`coinv_logQuantizedDifferential_list_prod`** —
  equations `(8c)`--`(8d)`.
- **`coinv_sum_eq_of_prod_eq`** — equation `(8e)`: two finite factorizations of the same unit have
  the same total class, so the Gauss splitting and the component/prime pairing create no ambiguity.
- **`logQuantizedDifferential_reflection`** — equation `(15)`, `U^*[F_H,U] = 2(U^*PU - P)` for
  `F_H = 2P - 1`.
- **`coefficientState_quotient_trivial`** — equation `(19)`: a coefficient hull contained in the
  frequency module leaves no residual state charge.

Equation `(18)` is already in the corpus: `HTGeometry/PrimeEulerProductAperture.lean` proves
`bohrFrequencyModule (eulerProductLine N σ) = primeApertureCharacterModule N`, the span of the prime
logarithms, and `finrank_bohrFrequencyModule_eulerProductLine` gives its exact rational dimension.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized, and either imported or explicitly `[NOT PROVED]` in the card: the Connes--Consani
Gauss factorization and quasi-innerness, the trace-class hypothesis `(6)`, and the four cofinal
obligations of section 5.

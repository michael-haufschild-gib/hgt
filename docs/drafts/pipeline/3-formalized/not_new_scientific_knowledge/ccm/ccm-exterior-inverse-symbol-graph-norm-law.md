# The CCM exterior inverse-symbol block forces a logarithmic graph norm

- **ID:** `ccm-exterior-inverse-symbol-graph-norm-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Plancherel, modulation covariance of the Fourier transform, and
  `ccm-characteristic-crossing-interior-mode-reduction-law.md`

## Statement

Fix an aperture `a>0`. Choose the symmetric characteristic factorization

```text
W_a(xi)=b_a(xi)c_a(xi)                                    (1)
```

so that `b_a` removes every real zero with its multiplicity and tends to a nonzero constant at
infinity. This normalization is always available: `W_a` is even, so its nonzero real zeros occur
in opposite pairs with equal multiplicity, while any zero at the origin has even multiplicity.
Hence the characteristic polynomial has even degree `d_a`; taking
`b_a=p_a/(1+xi^2)^(d_a/2)` gives the claimed nonzero limit. Since

```text
W_a(xi)=log|xi|+O_a(1),                                   (2)
```

the real-zero-free factor satisfies

```text
|c_a(xi)| -> infinity,
m_a(xi)=1/c_a(xi) -> 0.                                   (3)
```

After multiplying by a constant sign, `m_a` is bounded, continuous, and positive on the real
axis. Let

```text
R_a=m_a(D)                                                (4)
```

be its bounded Fourier multiplier on `L2(R)`. Put

```text
E_a=(-infinity,-a) union (a,infinity),
D_(a,E)=1_(E_a) R_a 1_(E_a) : L2(E_a)->L2(E_a).          (5)
```

Then `D_(a,E)` is positive and injective, with dense nonclosed range, but it is not bounded below.
In particular it has no bounded inverse on the raw exterior `L2` space. More strongly, for every
nonempty bounded interval `J` contained in `(a,infinity)` there are unit vectors `f_n` supported
in `J` such that

```text
||D_(a,E)f_n||_2 -> 0.                                   (6)
```

## 1. Positivity, injectivity, and dense range

For `f in L2(E_a)`, extend `f` by zero to the line. Plancherel gives

```text
<f,D_(a,E)f>
 =<f,R_a f>
 =integral_R m_a(xi)|hat f(xi)|^2 dxi>=0.                (6a)
```

Because `m_a(xi)>0` everywhere, equality in `(6a)` forces `hat f=0` almost everywhere, hence
`f=0`. Thus `D_(a,E)` is positive and injective. It is self-adjoint, so

```text
closure(range D_(a,E))=(ker D_(a,E))^perp=L2(E_a).       (6b)
```

The range is therefore dense.

## 2. Fixed-support approximate null vectors

Choose a nonzero smooth function `chi` compactly supported in `J` and normalize it in `L2`. Put

```text
f_n(x)=exp(i n x)chi(x).                                  (7)
```

Every `f_n` is supported in `J` and has norm one. Plancherel and modulation covariance give

```text
||R_a f_n||_2^2
 =integral_R |m_a(xi)|^2 |hat chi(xi-n)|^2 dxi
 =integral_R |m_a(eta+n)|^2 |hat chi(eta)|^2 deta.        (8)
```

The integrand tends pointwise to zero by `(3)` and is dominated by
`||m_a||_infinity^2|hat chi(eta)|^2`, which is integrable. Dominated convergence gives

```text
||R_a f_n||_2 -> 0.                                      (9)
```

Exterior compression is contractive, so

```text
||D_(a,E)f_n||_2<=||R_a f_n||_2->0.                      (10)
```

This proves `(6)` and the failure of a lower bound. An injective bounded self-adjoint operator with
closed range is bounded below on the orthogonal complement of its kernel. Hence the range here is
not closed. `QED`

## Positive CCM carrier law

Write `v=c_a(D)u`. The compact-support condition on `u=m_a(D)v` naturally produces the exterior
equation

```text
1_(E_a)m_a(D)1_(E_a)v_E
 =-1_(E_a)m_a(D)1_(-a,a)v_I.                             (11)
```

Equation `(6)` proves that `(11)` cannot be solved by a bounded inverse on raw exterior `L2`.
Therefore the exact characteristic reduction is forced into a strengthened carrier of one of the
following types:

```text
a logarithmic graph space on which m_a(D) has closed inverse,
a closed linear relation with the support seam in its domain,
a Feshbach map using an unbounded or regularized boundary inverse,
or a relative-resolvent determinant before scalarization.                    (12)
```

This is a positive regularity obligation: every successful construction must pay the missing
high-frequency factor `|c_a(xi)|`, asymptotically one logarithmic Fourier weight, in the topology
of its boundary state.

Positivity and injectivity sharpen the remaining incidence problem. Put

```text
g(v_I)=-1_(E_a)m_a(D)1_(-a,a)v_I.                        (12a)
```

For a prescribed finite characteristic trace `v_I`, the exterior datum exists exactly when

```text
g(v_I) in range D_(a,E),                                 (12b)
```

and is then unique. Thus the exact CCM Evans relation is a finite-to-infinite **range-incidence
condition** for a dense nonclosed operator range. A successful Feshbach construction must prove
membership in `(12b)` before applying the unbounded inverse; it cannot define the inverse on all
of exterior `L2`.

The graph norm alone does not solve the arithmetic transport. The formal theorem
`not_summable_primeLogHerglotzTransportMassOrder_of_pos` says that every finite logarithmic
cancellation order still fails after positive prime transport. Thus the complete CCM carrier must
simultaneously provide

```text
logarithmic Gamma graph regularity
  + infinite prime-side renormalization rank
  + the exact principal--relative source coupling.        (13)
```

## Scope and classification

The modulated-wave-packet proof is standard Fourier multiplier theory. Its application fixes the
correct functional category for the CCM Evans boundary problem but is a route bridge, not new
scientific knowledge. The current Lean tree does not contain the needed localized modulation and
Fourier-multiplier convergence interface. Formalizing only the abstract bounded-below implication
would be wrapper work, so no Lean file is added.

## Gates

- [x] normalize the zero-free characteristic factor with logarithmic growth
- [x] identify the natural exterior inverse-symbol compression
- [x] prove positivity, injectivity, and dense range
- [x] construct fixed-support high-frequency approximate null vectors
- [x] prove the range is nonclosed and refute bounded invertibility on raw exterior `L2`
- [x] isolate the forced logarithmic graph-space resource
- [x] reduce exterior matching to exact range incidence
- [ ] construct the exact closed graph/relation for `(11)`
- [ ] prove its Feshbach map is Fredholm and source-compatible
- [ ] couple it to the finite characteristic packet and the two screw anchors
- [ ] prove the resulting relation has zero kernel for every aperture
- [ ] RH

## Lean status

`[FORMALIZED]` — supersedes the "no Lean file is added" decision recorded above.  Plancherel and the
exterior compression remain cited parents, but the card's own proof happens on the Fourier side, and
every step there is reachable.

Module: `formal/GaloisForLFunctions/RHTower/CCM/CCMExteriorInverseSymbol.lean`
(6 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]` — two are
axiom-free — wired into `formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `symbol_quadratic_nonneg` — **equation (6a), positivity**: a nonnegative symbol gives a
  nonnegative quadratic form `∫ m |f̂|²`.
- `symbol_quadratic_eq_zero` — **equation (6a), injectivity**: with a *strictly* positive symbol the
  form vanishes only when the Fourier profile vanishes almost everywhere, which is exactly the
  card's injectivity argument.
- `tendsto_integral_modulated_symbol` — **equations (8)–(9)**: the dominated-convergence heart of
  the fixed-support modulated wave packets.  If the symbol is measurable, bounded, and tends to `0`
  at infinity, then `∫ |m(η+n)|² |χ̂(η)|² dη → 0`; domination is by `‖m‖_∞² |χ̂|²` and the pointwise
  limit is `0` because `η + n → ∞`.
- `not_boundedBelow_of_tendsto_zero` — **equations (6), (10)**: a sequence of unit vectors whose
  images tend to zero refutes every lower bound, hence the compression is not bounded below and its
  range is not closed.
- `range_incidence`, `range_incidence_unique` — **equations (12a)–(12b)**: for an injective operator
  the exterior datum exists *uniquely* exactly when the interior forcing lies in the range, which is
  the card's reformulation of the Evans relation as a range-incidence condition.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the symmetric characteristic factorization `(1)` and the growth `(2)`–`(3)` of the exact symbol;
- Plancherel and modulation covariance, which convert `(7)` into the Fourier integral `(8)`;
- the exterior compression `(5)` and its contractivity;
- the closed-range theorem step from "not bounded below" to "range not closed", and the
  self-adjointness identity `(6b)`.

The prime–Gamma resource wall quoted in section "Positive CCM carrier law" is the corpus theorem
`GaloisForLFunctions.HTGeometry.not_summable_primeLogHerglotzTransportMassOrder_of_pos`.

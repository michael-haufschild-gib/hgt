# Additive boundary evaluation is not closable on the prime co-shift row graph

- **ID:** `prime-coshift-row-boundary-trace-nonclosable`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper); fringe-route no-go
- **Scientific status:** `[PROVED HERE] [BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `prime-coshift-row-orthogonal-spectral-gap.md` and
  `prime-coshift-additive-trace-coercivity-conjecture.md`
- **Statement:** For `Re(s)>1/2`, the graph domain of the canonical all-prime co-shift row is the
  weighted space

  ```text
  Dom(R_s)={x in l2(N):sum_n omega(n)|x_n|^2<infinity},     (1)
  ```

  with equivalent graph norm, where `omega(n)` is the number of distinct prime divisors of `n`.
  Ordinary Abel boundary evaluation on finite Dirichlet polynomials is not closable in this graph
  norm.  Consequently there is no canonical closed scalar trace on the natural row graph that
  extends finite-support additive evaluation.

## 1. Exact graph domain

Put

```text
T_(p,s)=V_p^*-p^(-s)I,
R_s x=(T_(p,s)x)_p,
A_s=sum_p p^(-2Re(s))<infinity.                            (2)
```

Define

```text
W(x)=sum_p ||V_p^*x||^2.                                  (3)
```

Since `(V_p^*x)_n=x_(pn)`, Tonelli's theorem and unique factorization give

```text
W(x)
 =sum_p sum_n |x_(pn)|^2
 =sum_m omega(m)|x_m|^2.                                  (4)
```

The elementary inequality `||u-v||^2<=2||u||^2+2||v||^2`, applied prime by prime, gives

```text
||R_s x||^2<=2W(x)+2A_s||x||^2.                           (5)
```

Writing `V_p^*x=T_(p,s)x+p^(-s)x` gives the converse estimate

```text
W(x)<=2||R_s x||^2+2A_s||x||^2.                           (6)
```

Thus `(1)` holds, finite-support vectors form a graph core, and

```text
||x||^2+||R_sx||^2
  equivalent to sum_n(1+omega(n))|x_n|^2.                 (7)
```

## 2. Prime-supported nonclosability sequence

Choose distinct primes `q_1,...,q_M` and define the finite-support vector

```text
x_M(q_j)=1/M,       1<=j<=M,
x_M(n)=0 otherwise.                                      (8)
```

Then

```text
||x_M||^2=1/M,
W(x_M)=1/M,                                               (9)
```

because `omega(q_j)=1`.  Equation `(5)` yields

```text
||R_sx_M||^2<=2(1+A_s)/M ->0.                            (10)
```

Hence `x_M->0` in the row graph norm.

Every ordinary Abel, heat, or radial boundary evaluation of the finite Fourier polynomial of
`x_M` has boundary value

```text
B(x_M)=sum_n x_M(n)=1.                                   (11)
```

There is no singular branch to subtract: `x_M(1)=0` and the vector has finite support.  Therefore

```text
x_M->0 in the row graph,
B(x_M)->1.                                                (12)
```

This is exactly failure of closability.

More abstractly, the coefficient functional `x |-> sum_n x_n` would be bounded on the weighted
space `(7)` only if

```text
sum_n 1/(1+omega(n))<infinity.                            (13)
```

The prime subsequence alone makes `(13)` diverge.

## 3. Route consequence

The proposed chain

```text
closed prime row R_s
  -> canonical closed scalar additive trace B_s on its natural graph
  -> mixed off-line coercivity
  -> RH                                                       (14)
```

fails at its second arrow.  The failure occurs before analytic continuation and before any zero is
read.  The row detects multiplicative constraint violations but its graph norm charges a new prime
coordinate by only one unit; additive evaluation coherently sums arbitrarily many such coordinates.

The orthogonal spectral gap remains valid and useful.  It does not repair `(12)`: the vectors
`x_M` are small in norm as well as in row energy, while scalar boundary evaluation accumulates
their coherent prime amplitudes.

Any successor must change the source object, not merely the closure convention.  At least one of
the following is necessary:

1. a genuinely second analytic direction whose norm controls coherent prime summation;
2. an additional unbounded additive operator included in the graph before taking a trace;
3. a vector-valued boundary object retaining the prime coordinates, together with a
   noncomponentwise action or a second analytic base direction; ordinary componentwise channels
   on one complex variable still principalize under the full-matroid hypothesis;
4. a stronger prime row with source-justified weights for which the arithmetic ground state and
   the required boundary operation remain compatible.

The first and third alternatives are constrained by
`ht-period-rank-one-scalar-stanley-reisner-principalization.md`: ordinary scalar packaging,
arbitrarily many componentwise one-variable channels, constant finite internal monodromy, and
DA-gauge-flat finite internal cocycles cannot realize a nonpure full Stanley--Reisner
prime/reflection relation complex.  The no-go here is more concrete and does not require that
full-matroid hypothesis.  Conversely, the principalization theorem is not a universal
one-variable RH obstruction: a source using weaker relation geometry, a nonadditive action, or
positivity outside the full-matroid setting remains logically possible.

## Lean decision

The domain identity and countersequence are elementary and suitable for Lean only after the
concrete multiplicative shifts and all-prime row exist.  An abstract closability wrapper is not
added independently.

## Gates

- [x] graph domain identified exactly
- [x] graph norm equivalence proved
- [x] explicit prime-supported nonclosability sequence
- [x] canonical scalar trace route retired
- [ ] formalize together with the concrete co-shift row

## 2026-08-19 — unconditional Lean formalization (stage 3)

Formalized in `formal/GaloisForLFunctions/RHTower/PrimeCoShiftRowGraph.lean` (model in
`PrimeCoShiftModel.lean`).  All energies are stated in `ℝ≥0∞`, so every identity below is
unconditional — no summability hypothesis appears anywhere.  `#print axioms` on each capstone
reports only `propext, Classical.choice, Quot.sound`.

| Card item | Lean declaration |
|---|---|
| `omega(n)` | `omegaPNat`, `primeDivisors`, `card_primeDivisors` |
| `W(x) = sum_p ||V_p^* x||^2`, eq. (3) | `coShiftEnergy` |
| `||R_s x||^2`, eq. (2) | `rowEnergy` |
| `A_s = sum_p p^{-2 Re s} < infinity` | `primeZetaEnergy`, `primeZetaEnergy_ne_top` |
| eq. (4) `W(x) = sum_m omega(m)|x_m|^2` | `coShiftEnergy_eq_omegaEnergy` (via `tsum_prime_shift`) |
| eq. (5) | `rowEnergy_le` |
| eq. (6) | `coShiftEnergy_le` |
| eq. (1) the exact graph domain | `rowEnergy_ne_top_iff` |
| eq. (7) graph-norm equivalence | `graphEnergy_le_weight`, `weight_le_graphEnergy` |
| eq. (8)–(9) the vectors `x_M` | `exists_prime_uniform_vector` (`finsetVector`) |
| eq. (10)–(12) failure of closability | `exists_small_graphEnergy_unit_coefficient_sum` |
| eq. (13) divergence of `sum 1/(1+omega(n))` | `not_summable_inv_one_add_omega` |

The auxiliary identity behind (4) is a pure double-counting statement proved for an arbitrary
`ℝ≥0∞`-valued weight: `tsum_prime_shift`, `∑_p ∑_m G(pm) = ∑_k ω(k) G(k)`.

## Gates

- [x] graph domain identified exactly
- [x] graph norm equivalence proved
- [x] explicit prime-supported nonclosability sequence
- [x] canonical scalar trace route retired
- [x] formalized together with the concrete co-shift row

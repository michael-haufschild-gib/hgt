# Nonreal factorial slope forces formal hypertranscendence

- **ID:** `nonreal-factorial-slope-formal-hypertranscendence`
- **Stage:** 2-fully-proven
- **Type:** GENERAL HYPERTRANSCENDENCE LAW
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Source:** the HTGeometry coefficient-face laws, Bender endpoint asymptotics for rapidly
  growing formal series, and the Riemann zeta functional equation
- **Statement:** A formal series whose coefficients have one nonreal factorial slope
  `a_n ~ C Lambda^n Gamma(1 + alpha n)`, with `Re(alpha)>0` and
  `Im(alpha)!=0`, is hypertranscendental over `C(z)`.

## Goal

Prove a complex-phase refinement of the Maillet--Malgrange Gevrey obstruction.  Ordinary
Gevrey order sees only `Re(alpha)` and therefore misses a nonzero imaginary factorial slope.
The theorem says that an algebraic differential equation cannot absorb the resulting
`n log n` chirp, even when the real Gevrey order is rational.

This is not an RH theorem.  Its first arithmetic application would be the formal zeta-moment
family

```text
R_alpha(z)=sum_(n>=0) (-1)^n zeta(-alpha n) z^n.             (1)
```

For `alpha=2m`, all positive-index coefficients vanish by the trivial zeros.  For
`Im(alpha)!=0` and `Re(alpha)>0`, the functional equation gives the factorial asymptotic
required by the theorem.  Thus the theorem makes `R_(2+i delta)` differential
algebraic exactly at `delta=0` and hypertranscendental for every `delta!=0`.  Applied with
`delta=2 Re(s)-1`, this is an exact functional-equation fixed-line reader, not a mechanism
forcing zeta zeros onto that line.

## Exact theorem

Let `alpha=r+it`, where `r>0` and `t!=0`.  Let `C,Lambda` be nonzero complex constants and let
`a=(a_n)_(n>=0)` be eventually nonzero.  Assume

```text
a_n / (C Lambda^n Gamma(1+alpha n)) = 1 + O(exp(-c n))       (2)
```

for some `c>0`.  Then the formal series

```text
f(z)=sum_(n>=0) a_n z^n in C[[z]]
```

satisfies no nonzero algebraic differential equation over `C(z)`.

The exponential error in `(2)` is stronger than the expected sharp hypothesis.  It is chosen
because the zeta application has it and because it isolates the new obstruction from
second-order asymptotic bookkeeping.

## Paper proof

### 1. Fixed-shift factorial chirp

Complex Stirling asymptotics give, for every fixed integer `h`,

```text
a_(N+h)/a_N
 = (Lambda alpha^alpha)^h N^(alpha h)(1+O_h(1/N)).           (3)
```

Thus a differential endpoint term

```text
(N-q+j)_j a_(N-q+j)
```

has leading complex power

```text
constant * a_N * N^(j+alpha(j-q)).                           (4)
```

Distinct pairs `(j,q)` can have the same complete complex exponent only when they are equal:
if

```text
j_1+alpha(j_1-q_1)=j_2+alpha(j_2-q_2),
```

the imaginary parts first give `j_1-q_1=j_2-q_2`, and the real parts then give
`j_1=j_2`.

### 2. Real factorial envelope

Put `alpha=r+it`.  Stirling's formula on the fixed ray through `alpha` gives a positive
constant `A` and constants `0<c_0<C_0` such that, for all sufficiently large `n`,

```text
c_0 A^n Gamma(1+rn) <= |a_n| <= C_0 A^n Gamma(1+rn).        (5)
```

Indeed, after subtracting `log Gamma(1+rn)` from `log |Gamma(1+alpha n)|`, every
term of order `n log n` cancels and the remaining order-`n` term is absorbed into
`A^n`; the logarithmic terms agree up to a bounded factor.  Changing the constants
absorbs the finite initial segment.

For `0<=j<=m`, write

```text
u_(j,n)=(n+j)_j a_(n+j)=[z^n]f^(j).                         (6)
```

The same estimate and the fixed shift `j` give

```text
|u_(j,n)| <= C_j A^n Gamma(1+rn)(n+1)^((r+1)j).             (7)
```

All exponential factors caused by the fixed shifts have been absorbed into `C_j`.

### 3. Uniform factorial-convolution tail

We need the following endpoint lemma.

**Lemma (finite multijet endpoint bound).**  Fix `r>0`, integers `D,J>=0`, and sequences
`u_(j,n)` satisfying `(7)` for `j<=J`.  For a fixed polynomial in the series
`U_j(z)=sum_n u_(j,n)z^n`, split the coefficient of degree `N` into:

1. terms in which one series factor has degree `N-q` with `q<R`;
2. all remaining terms.

For `N>2R+O(1)`, the large factor in the first class is unique.  There is a constant
`B`, depending only on `r,D,J` and the polynomial degrees, such that the absolute value
of the second class is

```text
O_R(A^N Gamma(1+rN) N^(B-rR/2)).                            (8)
```

Since `(5)` has the same exponential base, `(8)` is also

```text
O_R(|a_N| N^(B-rR/2)).                                      (9)
```

**Proof.**  It suffices to treat one monomial

```text
z^p U_(j_1)...U_(j_d),   d<=D, j_l<=J.                      (10)
```

Polynomial weights in `(7)` contribute at most `N^B`, for a fixed `B`.  Order every
composition `n_1+...+n_d=N-p` so that `n_1` is maximal and put

```text
s=N-n_1=p+n_2+...+n_d.
```

The excluded endpoint region is exactly `s<R`.  Two-sided Stirling bounds, uniformly
for the fixed `r` and fixed number of factors, give

```text
product_l Gamma(1+rn_l) / Gamma(1+rN)
 <= C N^L exp(-r Delta(n_1,...,n_d)),                       (11)

Delta=N log N-sum_l n_l log(max(1,n_l)).
```

Here `C,L` depend only on `r,d,p`; zero parts are absorbed into `C`.  If
`s<=N/2`, convexity of `x log x` gives

```text
sum_(l>=2) n_l log(max(1,n_l)) <= s log(max(1,s))
```

and therefore

```text
Delta >= N log N-(N-s)log(N-s)-s log s
      >= s log(N/s).                                       (12)
```

If `s>N/2`, maximality of `n_1` forces every normalized part away from `1`;
compactness of the fixed `d`-simplex gives `Delta>=c_d N`.

There are at most `(N+1)^(d-1)` compositions.  For
`R<=s<=sqrt(N)`, `(12)` is at least `(s/2)log N`, so summing by `s` gives
`O_R(N^(-rR/2))` up to a fixed polynomial.  For
`sqrt(N)<s<=N/2`, `(12)` is at least
`(sqrt(N)/2)log N`; for `s>N/2` the loss is exponential in `N`.
Consequently

```text
sum_(n_1+...+n_d=N-p, max n_l<=N-R)
  product_l Gamma(1+rn_l) / Gamma(1+rN)
 <= C_R N^(L'-rR/2).                                      (13)
```

The fixed polynomial weights and finitely many choices of maximal factor only
increase `L'`.  Absorbing them into `B` gives `(8)`.

The exponent `rR/2` is deliberately non-sharp.  Its only required feature is that
it tends to infinity with `R`.

### 4. Endpoint expansion of an ADE coefficient

Assume that a nonzero differential polynomial

```text
P(z,f,f',...,f^(m))=0.                                     (13)
```

After clearing a rational denominator, take one of least order `m` and, subject to that,
least degree in its highest jet `Y_m`.  Then

```text
P_(Y_m)(z,f,f',...,f^(m)) != 0:                            (14)
```

otherwise the derivative with respect to `Y_m` would be another annihilating polynomial of
the same order and smaller highest-jet degree.  Characteristic zero ensures that this
derivative is not the zero polynomial.

For a fixed cutoff `R`, split every convolution atom contributing to `[z^N]P(f)` according
to whether one differentiated factor carries all but less than `R` units of the output
degree.  Such an endpoint factor is unique for large `N`.  Summing the endpoint atoms gives

```text
[z^N]P(f)
 = sum_(j=0)^m sum_(q<R) c_(j,q)
     (N-q+j)_j a_(N-q+j) + E_(N,R),                        (15)
```

where

```text
c_(j,q)=[z^q] P_(Y_j)(z,f,f',...,f^(m)).                   (16)
```

This identity is combinatorial, not asymptotic.  In a differential monomial, choosing the
unique large factor and then summing the complementary coefficient of degree `q` is exactly
differentiation of the monomial with respect to that factor.  Repeated equal factors acquire
their correct multiplicity.  Equation `(14)` says the family `(c_(j,q))` is not identically
zero.  The endpoint lemma gives a constant `B_P` with

```text
E_(N,R)=O_R(|a_N| N^(B_P-rR/2)).                            (17)
```

### 5. Logarithmic chirps cannot cancel at every integer

Let

```text
M=max {j+r(j-q) : c_(j,q)!=0}.                             (18)
```

For each fixed `j`, the expression decreases strictly with `q`, so the maximum is attained
among the finitely many first nonzero coefficients of the nonzero series in `(16)`.  Choose
`R` beyond every pair attaining `M` and so large that

```text
B_P-rR/2<M.                                                (19)
```

Among the finitely many endpoint pairs with `q<R`, let `eta>0` be smaller than both the
gap from `M` to the next real exponent and the gap in `(19)`.  Divide `(15)` by
`a_N N^M` and use `(3)`.  Equation `(13)` would imply

```text
T(log N)=O(N^(-eta)),                                      (20)
```

where

```text
T(x)=sum_((j,q):j+r(j-q)=M)
  c_(j,q)(Lambda alpha^alpha)^(j-q) exp(i t(j-q)x).         (21)
```

This is a nonzero finite trigonometric polynomial.  Indeed, if two terms in `(21)` had the
same frequency, then `j_1-q_1=j_2-q_2`; equality of their real exponents would then force
`j_1=j_2` and hence `q_1=q_2`.  Thus no two distinct nonzero coefficients are combined.

For every large real `x`, choose the nearest integer `N_x` to `exp(x)`.  Then
`|log N_x-x|=O(exp(-x))`.  The derivative of `T` is bounded, so `(20)` gives
`T(x)->0` as `x->infinity`.  But every frequency in `(21)` is an integral multiple of
`t`; hence `T` is periodic.  A periodic continuous function tending to zero at positive
infinity is identically zero, a contradiction.  This proves the theorem.

## Zeta-moment application

For `alpha=r+it`, `r>0`, the functional equation is

```text
(-1)^n zeta(-alpha n)
 = (-1)^(n+1) sin(pi alpha n/2)
   Gamma(1+alpha n) zeta(1+alpha n)
   / (pi (2 pi)^(alpha n)).                                 (22)
```

If `t>0`, the `exp(-i pi alpha n/2)` branch of the sine dominates exponentially, and

```text
(-1)^n zeta(-alpha n)
 = 1/(2 pi i)
   (-exp(-i pi alpha/2)(2 pi)^(-alpha))^n
   Gamma(1+alpha n)(1+O(exp(-c n))).                        (23)
```

If `t<0`, the conjugate sine branch gives

```text
(-1)^n zeta(-alpha n)
 = -1/(2 pi i)
   (-exp(i pi alpha/2)(2 pi)^(-alpha))^n
   Gamma(1+alpha n)(1+O(exp(-c n))).                        (24)
```

Here `zeta(1+alpha n)=1+O(2^(-rn) poly(n))`, so the error remains exponential.
Equations `(23)`--`(24)` reduce the nonreal zeta-moment claim to the theorem.

## Hostile audit

1. **Ordinary Gevrey order is insufficient.**  It sees `r`, not `t`.  No proof may cite
   rational-slope rigidity alone when `r` is rational.
2. **Kamimoto does not close the claim.**  His finite singular-support theorem treats a
   normalized explicit nonlinear system with invertible linear part.  An arbitrary singular
   scalar ADE branch is not automatically in that class.
3. **The complex-order moment Borel transform is not a standard algebraic ramification.**
   Its logarithmic-spiral poles are evidence, not by themselves a DA contradiction.
4. **The endpoint remainder is the load-bearing theorem.**  A pointwise assertion that
   "factorials are endpoint dominated" is inadequate.  `(8)` must be proved uniformly over
   every finite differential monomial, including derivative weights and all intermediate
   splittings.
5. **Minimality is essential.**  A squared or otherwise nonreduced ADE can have identically
   vanishing first derivative at its solution.  The proof selects least order and then least
   degree in the highest jet before invoking the separant.
6. **The RH use is target-fed.**  `alpha=2+i(2 Re(s)-1)` reads the fixed line but supplies no
   source theorem making `R_alpha` DA at zeta divisor points.

## Literature boundary

- E. A. Bender, *An Asymptotic Expansion for the Coefficients of Some Formal Power Series*,
  J. London Math. Soc. (2) 9 (1975), 451--458, proves endpoint expansions
  `b_n=sum_(k<R)c_k a_(n-k)+O(a_(n-R))` for rapidly growing formal series under explicit
  hypotheses.  The needed result is a complex, multijet differential-polynomial extension.
- K. Mahler, *On formal power series as integrals of algebraic differential equations*
  (1971), and the Maillet--Malgrange theory give Gevrey bounds for formal ADE solutions but
  do not detect the imaginary part of a factorial slope.
- S. Kamimoto, *Resurgent functions and nonlinear systems of differential and difference
  equations*, Adv. Math. 406 (2022), Theorem 7.4, gives finite-generator resurgent support
  for a normalized nonlinear system; it does not supply the arbitrary-ADE normalization
  required here.
- Ordinary differential equations for generalized Wright functions in the accessible literature
  first replace all Gamma step parameters by integer numerator/denominator blocks.  The resulting
  Euler-operator equation therefore requires rational real steps.  It neither covers a nonreal
  step `alpha` nor contradicts the theorem; rather, it identifies the expected DA boundary.

Targeted searches for `Gamma(alpha n)` differential transcendence, nonreal factorial slopes,
factorial chirp ADEs, and complex Maillet slopes found no equivalent theorem.  This is an
absence-of-hit, not a priority certificate.

## Independent hostile audit

`[PAPER-PROVED]` The factorial-endpoint core was independently rechecked on 2026-07-28.

1. **Complex Gamma envelope.**  Stirling on the fixed ray through `alpha` gives exactly
   `(5)`: after subtracting `log Gamma(1+rn)`, every `n log n` term cancels and the remaining
   discrepancy is linear in `n` plus a bounded logarithmic term.  One positive exponential base
   and two fixed constants therefore give the required two-sided bound.
2. **Zero composition parts.**  In `(11)`, indices equal to zero contribute the fixed value
   `Gamma(1)=1`.  They are absorbed uniformly because the number of factors is fixed.
3. **Fixed derivative shifts.**  Replacing `n` by `n+j`, with bounded `j`, multiplies the
   envelope by only a fixed exponential constant and a fixed power of `n`.  These enter `B_P`
   and do not depend on the cutoff `R`.
4. **Interior entropy.**  For `R<=s<=sqrt(N)`, `(12)` gives
   `exp(-r Delta)<=N^(-rs/2)`; the polynomial number of compositions and all derivative weights
   add one fixed exponent.  The ranges `sqrt(N)<s<=N/2` and `s>N/2` are exponentially smaller.
   Hence the loss `B_P-rR/2` is uniform over every monomial of the fixed differential polynomial.
5. **Endpoint uniqueness.**  Two factors cannot both have degree greater than `N-R` once
   `N>2R+O(1)`.  Differentiating the monomial with respect to the unique large factor gives
   exactly the coefficient series in `(16)`, including multiplicities.
6. **Separant.**  Choose a relation of least differential order and then least degree in its
   highest jet.  If the evaluated separant vanished, it would be an annihilating relation of the
   same order and smaller highest-jet degree.  Characteristic zero excludes a syntactically zero
   derivative.  Thus some endpoint coefficient is nonzero.
7. **Rational coefficients.**  Multiplying by a common denominator and a sufficient power of
   `z` turns a relation over `C(z)` into one with polynomial coefficients.  This changes only the
   fixed degree shift `p` in `(10)`.
8. **Chirp noncancellation.**  Equality of complete endpoint exponents forces equality of the
   endpoint pair.  The surviving finite trigonometric polynomial is nonzero and periodic, while
   `(20)` would make it tend to zero on all large real arguments.  This is impossible.

No unproved resurgence normalization is used.  The audit found no remaining paper-proof
obligation.

## RH open core

`[RH OPEN CORE: NON-TARGET-FED SOURCE]` Construct from the Euler--Gamma source, before reading a
zeta zero, a carrier which the source forces to be DA at every divisor point while the nonreal
factorial-slope theorem forces it to be HT at every off-critical point.  The displayed
`R_alpha` family does not do this.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure general theorem, exact attack, RH scope stated
- [x] 1 -> 2 fully-proven: complete independent hostile audit of the factorial-endpoint core
- [ ] 2 -> 3 formalized: formalize the exact endpoint theorem and zeta-moment application
  without analytic hypotheses standing in for the actual sequence
- [ ] 3 -> 4 publication-ready: standalone theorem, primary-source comparison, Lean certificate

## Log

- 2026-07-27 — Created after the complex-resurgence route was found to require an unsupported
  arbitrary-ADE normalization theorem.
- 2026-07-27 — Replaced the resurgent obstruction by a direct coefficient-endpoint attack using
  the existing HTGeometry coefficient-face method.
- 2026-07-27 — Closed the endpoint remainder on paper by a uniform fixed-simplex entropy bound
  and isolated the source implication as the exact RH-bearing gap.
- 2026-07-28 — Independently audited the complex envelope, mixed derivative weights, endpoint
  uniqueness, separant, and entropy remainder; promoted the exact theorem to Stage 2.

## Lean formalization (in progress)

Target statement.  With `formalJetsOver` (in `HTGeometry/AlgebraicallyIndependentCoefficientFormalGerm.lean`)
the card's conclusion "satisfies no nonzero algebraic differential equation over `ℂ(z)`" is

```
∀ (m : ℕ) (P : MvPolynomial (Fin (m+2)) ℂ), P ≠ 0 →
  MvPolynomial.aeval (formalJetsOver m (PowerSeries.mk a)) P ≠ 0
```

(clearing a rational denominator and a power of `z` turns a relation over `ℂ(z)` into one with
polynomial coefficients, which is exactly an `MvPolynomial` in `X` together with the jets).

Layer plan, bottom up.

| layer | content | module | status |
|---|---|---|---|
| G1 | `ψ(z) = log z − 1/(2z) + O(‖z‖⁻²)` on the **whole** right half plane (the corpus had only the vertical form) | `HTGeometry/DigammaHalfPlaneAsymptotic.lean` | **done** |
| G2 | `Γ(z+w) = Γ(z)·exp(∫₀¹ w ψ(z+uw) du)` for a **complex** shift | `HTGeometry/GammaComplexShiftIntegral.lean` | **done** |
| G3 | `(3)`: `Γ(1+αn+w)/(Γ(1+αn)(1+αn)^w) → 1`; principal-log additivity `(αn)^w = α^w n^w` | `HTGeometry/GammaRayShiftAsymptotic.lean` | **done** |
| E1 | ray-log split `Re(α log(1+αn)) = Re(α log α) + r log n + O(1/n)`; one-step Gamma ratio in log form; the defect recursion `D(n+1) − D(n) = (α log(1+(αn)⁻¹)).re − (r log(1+(rn)⁻¹)) + ReE_α(n) − ReE_r(n)` | `HTGeometry/GammaRayRealEnvelope.lean` | **done** |
| E2 | **`(5)`**: the two-sided envelope `exists_rayEnvelope` | `HTGeometry/GammaRayRealEnvelope.lean` | **done** |
| C | `(8)`/`(13)`: the uniform factorial-convolution endpoint bound | — | open |
| D | `(15)`/`(14)`: endpoint expansion of an ADE coefficient and the separant | — | open |
| T | `(20)`/`(21)`: a nonzero periodic trigonometric polynomial cannot vanish at infinity | — | open |

Design notes fixed by the audit of the paper proof:

* Only the **sequential** ray asymptotic is needed, not uniform Stirling in a sector: `(3)` is used
  through `T(log N) → 0`, so `1 + o(1)` errors suffice everywhere except in the envelope `(5)`.
Named objects now in the tree: `rayPoint`, `rayShiftExponent`, `norm_rayShiftExponent_le`
(the quantitative `O(1/n)` form — this is what E2 consumes), `tendsto_gamma_ray_shift_ratio`,
`rayEnvelopeSlope`, `rayEnvelopeDefect`, `rayEnvelopeDefect_succ_sub`, `re_mul_log_rayPoint`,
`abs_re_mul_log_one_add_inv_le`, `log_mul_natCast_of_re_pos`, `cpow_mul_natCast_of_re_pos`.

The envelope, in the exact form the endpoint lemma will consume:

```
exists_rayEnvelope (hre : 0 < α.re) :
  ∃ (B : ℕ) (C : ℝ), 0 < C ∧ ∀ n ≥ 1,
      ‖Γ(1+αn)‖ ≤ C · n^B · (e^{n·S} · Γ(1+rn))
    ∧ e^{n·S} · Γ(1+rn) ≤ C · n^B · ‖Γ(1+αn)‖,      S = rayEnvelopeSlope α = Re(α log α) − r log r
```

Mechanism actually used: with `R_n = (rayPoint α n).re = 1 + n r`, once `2‖α‖ + 4 ≤ R_n`, the four
terms of `rayEnvelopeDefect_succ_sub` are bounded by `2/n`, `2/n`, `‖α‖(6+2‖α‖)/(n r)`, `(6+2r)/n`,
so `|D(n+1) − D(n)| ≤ K/n ≤ 2K/(n+1)`; `1/(n+1) ≤ log(n+1) − log n` telescopes this to
`|D n| ≤ C₀ + 2K log n` (`abs_rayEnvelopeDefect_le`), a `Finset.sup'` over `Finset.range (n₀+1)`
absorbs `n ≤ n₀` (`exists_rayEnvelopeDefect_bound`), and `B := ⌈2K⌉₊` exponentiates it.

* `(5)` does **not** need the sharp Stirling constant.  A two-sided envelope with a fixed polynomial
  factor, `c₁ n^{-B₀} A^n Γ(1+rn) ≤ ‖Γ(1+αn)‖ ≤ C₁ n^{B₀} A^n Γ(1+rn)`, is enough: the endpoint
  lemma already absorbs fixed polynomial weights into its exponent `B`.  That form follows from the
  ratio estimate `ρ_{n+1}/ρ_n = 1 + O(1/n)`, i.e. from G1–G3 and nothing stronger.

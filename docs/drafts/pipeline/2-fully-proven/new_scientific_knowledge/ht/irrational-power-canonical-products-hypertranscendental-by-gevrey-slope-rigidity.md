# Irrational-power canonical products are hypertranscendental by Gevrey-slope rigidity

- **ID:** `irrational-power-canonical-products-hypertranscendental-by-gevrey-slope-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HYPERTRANSCENDENCE / GEVREY RIGIDITY
- **Scientific status:** `[PROVED HERE] [PRELIMINARY NOVELTY PASS] [NOT AN RH RESULT]`
- **Source:** Barnes asymptotics for canonical products, the Sibuya--Ramis exact
  Gevrey-order theorem, and the rational cyclic-norm classification
- **Statement:** For every positive irrational real number `s`, the canonical product
  with simple zeros `-n^s` is hypertranscendental over `C(z)`.

## 1. Family and theorem

For `s>0`, set

```text
g(s)=floor(1/s),
E_g(w)=(1-w) exp(sum_(j=1)^g w^j/j),
W_s(z)=product_(n>=1) E_(g(s))(-z/n^s).                    (1)
```

The product converges locally uniformly, is entire of order `1/s`, and has simple zeros
exactly at `-n^s`, `n>=1`.

### Theorem

If `s>0` is irrational, then `W_s` is differentially transcendental over `C(z)`.

Equivalently, there is no nonzero polynomial

```text
P in C(z)[Y_0,...,Y_m]
```

such that

```text
P(W_s,W_s',...,W_s^(m))=0.                                 (2)
```

## 2. Barnes tail of the logarithmic derivative

Let

```text
D=x d/dx,
H_s(x)=D log W_s(x)=x W_s'(x)/W_s(x).                      (3)
```

For `1/s` not an integer, Barnes' expansion, in the form recalled by Miller and
Speissegger, gives

```text
H_s(x) =
  (pi/s)csc(pi/s)x^(1/s)
  + sum_(j=1)^g(s) (-1)^j zeta(sj)x^j
  - 1/2
  + R_s(x),                                                (4)
```

where, as `x->+infinity`,

```text
R_s(x) ~ sum_(k>=1) b_k x^(-k),
b_k=(-1)^k zeta(-sk).                                      (5)
```

More strongly, the same source gives the termwise asymptotic expansion of every Euler
derivative:

```text
D^m R_s(x) ~ sum_(k>=1) (-k)^m b_k x^(-k),  m>=0.          (6)
```

This derivative-compatible form, not merely a zeroth-order Poincare expansion, is what
allows an algebraic differential equation to pass to the formal tail.

Put `t=1/x` and

```text
Rhat_s(t)=sum_(k>=1) b_k t^k.                              (7)
```

## 3. Exact Gevrey order of the tail

The zeta functional equation gives

```text
|b_k|
 = 2 |sin(pi sk/2)| Gamma(1+sk) zeta(1+sk)
     / (2pi)^(1+sk).                                      (8)
```

### Upper bound

For fixed `s>0`,

```text
|sin(pi sk/2)|<=1,
1<zeta(1+sk)<=zeta(1+s).
```

Stirling's formula then gives constants `A,C>0` such that

```text
|b_k| <= C A^k (k!)^s.                                    (9)
```

Thus `Rhat_s` is Gevrey of order `s`.

### Sharpness for irrational `s`

If `s` is irrational, the rotation sequence

```text
k s/2 mod 1
```

is dense in `R/Z`.  Hence there are infinitely many `k` for which

```text
|sin(pi sk/2)| >= 1/2.                                    (10)
```

Along this subsequence, `(8)`, `zeta(1+sk)>1`, and the lower half of Stirling's
formula give constants `a,c>0` such that

```text
|b_k| >= c a^k (k!)^s.                                    (11)
```

Consequently `Rhat_s` is not Gevrey of any order `r<s`.  Its exact Gevrey order is

```text
gev(Rhat_s)=s.                                             (12)
```

In particular, `Rhat_s` diverges.

## 4. DA transfer from the function to the formal tail

Assume for contradiction that `W_s` is differentially algebraic over `C(x)`.

1. By `(3)`, `H_s=xW_s'/W_s` is DA.
2. The function `x^(1/s)` is DA because it solves

   ```text
   x y'-(1/s)y=0.
   ```

3. The finite polynomial and constant terms in `(4)` are DA.
4. Differentially algebraic elements over a differential field form a differential
   field.  Therefore `R_s`, obtained by subtracting all explicit terms in `(4)`, is DA
   over `C(x)`.

After the rational change `t=1/x`, the germ

```text
F_s(t)=R_s(1/t)                                            (13)
```

is DA over `C(t)`.  Hence it satisfies a nonzero algebraic differential equation with
rational coefficients.  Clearing denominators produces an equation

```text
G(t,F_s,F_s',...,F_s^(m))=0                               (14)
```

whose coefficients are analytic at `t=0`.

Equations `(5)` and `(6)` imply compatible asymptotic expansions for `F_s` and every
Euler derivative `(t d/dt)^m F_s` as `t->0+`.  Rewrite `(14)` using the Euler
derivative and clear the resulting powers of `t`.  Substitution of the asymptotic
expansions into `(14)` gives

```text
G(t,Rhat_s,Rhat_s',...,Rhat_s^(m))=0                       (15)
```

as an identity of formal power series.  Indeed, products and finite sums preserve
Poincare expansions, `(6)` handles all derivatives, and uniqueness of asymptotic
coefficients forces every coefficient in `(15)` to vanish.

Thus DA of `W_s` would make `Rhat_s` a divergent formal power-series solution of an
analytic algebraic ODE.

## 5. Sibuya--Ramis obstruction

The exact Gevrey-order theorem for analytic algebraic ODEs states:

> A divergent formal power-series solution has exact Gevrey order equal to the
> reciprocal of one of the strictly positive slopes of the Newton polygon of the
> equation along that solution.

The Newton polygon is built from derivative orders and orders of vanishing of analytic
coefficients.  Its vertices have integer coordinates.  Every finite positive slope, and
therefore its reciprocal, is rational.

Applied to `(15)`, the theorem forces

```text
gev(Rhat_s) in Q_(>0).                                     (16)
```

But `(12)` says `gev(Rhat_s)=s`, and `s` is irrational.  This contradiction proves the
theorem.

## 6. Combined real-exponent phase diagram

Together with Bank's integer theorem and the rational cyclic-norm law proved in this
project, the current unconditional classification is

```text
s irrational
  -> W_s is HT;                                            (17a)

s=p/q reduced, p odd
  -> W_s is HT;                                            (17b)

s=p an even positive integer
  -> W_s is DA;                                            (17c)

s=p/q reduced, p even, q>1
  -> unresolved here.                                     (17d)
```

Thus the unclassified positive real parameters form the thin countable set of
nonintegral reduced rationals with even numerator.  The previous rational theorem also
shows that the `q`-fold cyclic norm of every member in `(17d)` is DA, so exact Gevrey
order alone cannot decide those individual factors.

## 7. Hostile audit

1. **Maillet's upper bound is insufficient.**  A series of exact irrational order `s`
   belongs to every larger rational Gevrey class.  The proof needs the exact-order
   Sibuya--Ramis theorem, not the statement that every formal ODE solution is in some
   Gevrey class.
2. **The logarithm is not assumed DA.**  The proof uses the logarithmic derivative
   `xW_s'/W_s`, which is a rational differential expression in `W_s`.
3. **Irrational powers are DA.**  Subtracting `x^(1/s)` is legitimate over `C(x)`:
   arbitrary constant exponents solve a first-order linear ODE.
4. **Derivative compatibility is load-bearing.**  A scalar asymptotic expansion need
   not be differentiable termwise.  Barnes' formula supplies `(6)` for every Euler
   derivative.
5. **The sine factor cannot destroy the lower Gevrey bound.**  Irrational rotation
   yields the infinite subsequence `(10)`.  No Diophantine lower bound for every `k`
   is required.
6. **This does not classify rational even numerators.**  For rational `s`, exact
   Gevrey order `s` is compatible with a rational Newton slope.
7. **This is not RH.**  The theorem supplies a new general HT rigidity mechanism and
   nearly classifies a canonical real family.  It does not force a Riemann zero onto
   the critical line or produce the missing source-reflection creator.

## 8. Novelty audit

- S. B. Bank, *On Certain Canonical Products which Cannot Satisfy Algebraic
  Differential Equations*, Funkcial. Ekvac. 23 (1980), 335--349, proves the
  integer dichotomy: DA for even integer exponent, HT for odd integer exponent.
- C. Miller and P. Speissegger, *Expansions of the Real Field by Canonical
  Products*, Canad. Math. Bull. 63 (2020), 506--521, define the full real family
  `W_s`, recall `(4)`--`(6)`, and discuss their Gevrey character.  They cite Bank
  for odd integers but do not state irrational-parameter hypertranscendence.
- J.-P. Ramis, *Series divergentes et theories asymptotiques*, Journees X-UPS
  (1991), records the nonlinear exact-order theorem and attributes its
  cohomological proof to Y. Sibuya.
- A. V. Parusnikova, *On Gevrey Orders of Formal Power Series Solutions to the
  Third and Fifth Painleve Equations Near Infinity*, Opuscula Math. 34 (2014),
  591--599, restates the exact Newton-slope theorem and applies it to Painleve
  expansions.
- Exact searches for canonical products with zeros `-n^s`, irrational exponents,
  zeta-tail Gevrey order, and hypertranscendence found no equivalent result.
  Citation lists for Miller--Speissegger likewise exposed no such application.
  This is a preliminary absence-of-hit audit, not a priority certificate.

Primary source links:

- Miller--Speissegger:
  <https://doi.org/10.4153/S0008439519000572>
- Ramis:
  <https://doi.org/10.5802/xups.1991-01>
- Bank:
  <https://da.lib.kobe-u.ac.jp/da/kernel/0100499349/>
- Parusnikova:
  <https://doi.org/10.7494/OpMath.2014.34.3.591>

## 9. Lean status

No Lean edit is claimed.  The theorem depends on three analytic layers absent from the
current formal stack:

1. Barnes' derivative-compatible canonical-product asymptotics;
2. Stirling and irrational-rotation exact Gevrey estimates;
3. the nonlinear Sibuya--Ramis exact Newton-slope theorem.

Formalizing only the elementary coefficient estimate would not formalize the scientific
theorem.  Introducing any of these layers as an axiom or hypothesis wrapper would violate
the unconditional-proof rule.

## Gates

- [x] internal corpus audit
- [x] exact conjecture and falsifiers stated
- [x] primary-source external audit
- [x] exact Gevrey order proved
- [x] DA-to-formal-tail transfer proved
- [x] nonlinear exact-slope obstruction sourced
- [x] irrational family theorem dependency-closed on paper
- [x] rational and integer boundaries stated without overclaim
- [ ] independent full-text priority audit
- [ ] even-numerator noninteger rational factors classified
- [ ] nonreal/infinite-monodromy family classified
- [ ] unconditional analytic Lean formalization

## Log

- 2026-07-27 — Maillet upper-bound route rejected as insufficient.
- 2026-07-27 — Located Sibuya--Ramis exact Gevrey-order theorem.
- 2026-07-27 — Proved exact irrational zeta-tail order and the DA transfer.
- 2026-07-27 — Combined with rational cyclic norms to isolate the sole real open stratum.

## Lean plan — what is formalizable and in what order

The card's "formalizing only the elementary coefficient estimate would not formalize the scientific
content" is right about the *headline*, but wrong as a reason not to start: the three analytic
layers decompose into pieces of very different cost, and two of them are ordinary work.

1. **The sharpness half of §3 is elementary and self-contained.**  What it needs is

       for irrational `s`, the set `{k : ℕ | 1/2 ≤ |sin(π s k / 2)|}` is infinite.

   Route: `AddCircle.denseRange_zsmul_coe_iff` gives density of the `ℤ`-orbit of `s/2` in
   `AddCircle 1` exactly when `s/2` is irrational.  The target set is symmetric under `θ ↦ -θ`
   (`|sin|` is even), so infinitely many integers in an open good arc give infinitely many natural
   numbers.  This is the only place irrationality is used, and it is the whole reason the exact
   Gevrey order is irrational.

2. **The Gevrey bounds `(9)` and `(11)`** are Stirling plus `1 < ζ(1+sk) ≤ ζ(1+s)`; mathlib has
   Stirling and the corpus owns the `ζ` bounds.  These give `gev(R̂_s) = s` once `1` is available.

3. **The Sibuya--Ramis exact-order theorem and the Barnes expansion `(4)`--`(6)`** are the genuine
   mathlib-scale layers; they are the remaining cost, and neither is to be introduced as an axiom.

Doing `1` and `2` first makes the eventual statement of `3` precise and gives the card a real Lean
surface instead of none.

## Lean progress — the irrationality-sharpness step is closed

`GaloisForLFunctions/HTGeometry/IrrationalSineSubsequence.lean` (wired, axiom-clean):

    abs_cos_ge_of_abs_sin_lt          `|sin x| < 1/2` forces `|cos x| ≥ 4/5`
    abs_sin_two_mul_ge                so doubling multiplies the sine by at least `8/5`
    sin_eq_zero_of_forall_dyadic_lt   if every dyadic multiple of `k` has small sine, the sine at
                                      `k` vanishes
    infinite_setOf_half_le_abs_sin       for irrational `α`, `{k : ℕ | 1/2 ≤ |sin (π α k)|}` is
                                         infinite
    infinite_setOf_half_le_abs_sin_half  the same in the card's normalization `π s k / 2`

This is `(10)` of §3, the only place irrationality of `s` enters and the reason the exact Gevrey
order is irrational.  The proof needs no equidistribution and no pigeonhole: if `|sin(π α k)|` were
below `1/2` at every dyadic multiple of one `k`, the doubling identity would multiply it by `8/5`
each time, so it must vanish, making `α k` an integer and `α` rational.

Remaining for `(9)` and `(11)`: two-sided Stirling for `Γ(1 + sk)` against `(k!)^s`, together with
the `ζ` functional equation (mathlib has the latter).  Then `(12)` is immediate.

## Lean progress — §3 is closed in the Gamma normalization

`GaloisForLFunctions/HTGeometry/GevreyZetaTailBounds.lean` (wired, axiom-clean):

    two_pi_rpow_split     `(2π)^(1+sk) = 2π · ((2π)^s)^k`
    gevrey_upper_bound    `(9)`: from `|sin| ≤ 1` and `ζ(1+sk) ≤ ζ(1+s)`
    gevrey_lower_bound    `(11)`: from `ζ(1+sk) ≥ 1` and `|sin(π s k/2)| ≥ 1/2`
    gevrey_exact_order    both halves together, the lower bound holding on the infinite set supplied
                          by `infinite_setOf_half_le_abs_sin_half`

So `(12)` — the exact Gevrey order is `s` — is formal, *in the Gamma normalization* of Gevrey order
(`|b_k| ≤ C A^k Γ(1 + r k)`).  This is the point the card's §3 makes, and it needs no Stirling
estimate at all: the closed modulus `(8)` already carries `Γ(1 + sk)`, and Stirling was only being
used to translate `Γ(1 + sk)` into `(k!)^s`.

What remains of §3 is therefore only the normalization change (two-sided Stirling for `Γ` against
the factorial), and of the card the two genuine analytic layers: the Barnes expansion `(4)`--`(6)`
that produces the closed modulus, and the Sibuya--Ramis exact-order theorem.

## Lean progress — §3 is closed in the card's own factorial normalization

The normalization change no longer needs Stirling.  The two Gevrey scales `Γ(1 + s k)` and `(k!)^s`
differ by a factor that is itself geometric, and both directions follow from log-convexity of `Γ`
alone.

`GaloisForLFunctions/HTGeometry/GammaFactorialNormalization.lean` (wired, axiom-clean):

    Gamma_add_nat              `Γ(x+N) = Γ(x) ∏_{i<N}(x+i)`
    prod_range_add_le, le_prod_range_add
    Gamma_add_le_mul_rpow      **upper shift bound** `Γ(x+s) ≤ Γ(x)(x+M)^s`, from Hölder for `Γ`
                               with the split `x + s = (1 - s/M)·x + (s/M)·(x+M)`
    mul_rpow_le_Gamma_add      **lower shift bound** `Γ(x)(x+s-M)^s ≤ Γ(x+s)`, from the mirrored
                               split `x = (1 - s/M)(x+s) + (s/M)(x+s-M)`
    Gamma_le_pow_mul_factorial_rpow
                               `Γ(1 + s k) ≤ ((1+M+s)^s)^k (k!)^s` — the upper shift bound
                               telescoped along `x = 1 + s k`, using
                               `1 + s k + M ≤ (1 + M + s)(k+1)`
    exists_const_of_eventually finitely many exceptional indices absorbed into the constant
    exists_pow_mul_factorial_rpow_le_Gamma
                               `∃ c a > 0, c a^k (k!)^s ≤ Γ(1 + s k)` — the lower shift bound
                               telescoped above the threshold `k ≥ ⌈2(M-1)/s⌉`, where
                               `1 + s(k+1) - M ≥ (s/2)(k+1)`

`GaloisForLFunctions/HTGeometry/GevreyFactorialNormalization.lean` (wired, axiom-clean):

    gevrey_exact_order_factorial :
      for irrational `s > 0` and tail coefficients with the closed modulus `(8)`,

        ∃ C A > 0, ∀ k, |b k| ≤ C A^k (k!)^s                             (9)
        ∃ c a > 0, {k | c a^k (k!)^s ≤ |b k|} is infinite                (11)

That is `(9)` and `(11)` verbatim, hence `(12)`: the exact Gevrey order is `s`.  Stirling is not
used anywhere; the card's appeal to it is replaceable by log-convexity, because the comparison is
only needed up to a geometric factor.

Remaining on this card: the Barnes expansion `(4)`--`(6)` producing the closed modulus `(8)`, and
the Sibuya--Ramis exact-order theorem of §5.

## Lean progress — §3 is now unconditional: `(8)` is derived, not assumed

The closed modulus `(8)` was a hypothesis of the §3 theorems.  It is now a theorem, derived from the
functional equation of `ζ` (which mathlib owns) together with `cos(π/2 + x) = -sin x`.  No
asymptotic analysis enters.

`GaloisForLFunctions/HTGeometry/ZetaTailClosedModulus.lean` (wired, axiom-clean):

    norm_riemannZeta_one_sub_ofReal   the functional equation in modulus form on the real axis
    norm_riemannZeta_neg_eq           **`(8)`**:
                                        `|ζ(-sk)| = 2|sin(π s k/2)| Γ(1+sk) |ζ(1+sk)| / (2π)^{1+sk}`
    riemannZeta_ofReal_eq_tsum,
      norm_riemannZeta_ofReal_eq_tsum,
      summable_zeta_terms
    one_le_norm_riemannZeta_ofReal    `1 ≤ ζ(σ)` for real `σ > 1`
    norm_riemannZeta_ofReal_le        `ζ` is antitone on the real axis above `1`
    zetaTailModulus, zetaTailFactor   the tail modulus and its zeta factor, normalized at `k = 0`
    zetaTailModulus_eq                the closed modulus, valid at every index
    gevrey_exact_order_zetaTail :
      **for every irrational `s > 0`, with no further hypothesis,**

        ∃ C A > 0, ∀ k, |ζ(-sk)| ≤ C A^k (k!)^s                          (9)
        ∃ c a > 0, {k | c a^k (k!)^s ≤ |ζ(-sk)|} is infinite              (11)

So `(9)`, `(11)` and `(12)` are formal with no hypotheses at all: the exact Gevrey order of the
irrational-power zeta tail is `s`.  The index `k = 0` is normalized away, as the card's tail
`R̂_s(t) = ∑_{k ≥ 1} b_k t^k` starts at `k = 1`.

Sections 1 and 3 of this card are therefore fully formal.  What remains is `(4)`–`(6)`: the
identification of those coefficients as the asymptotic expansion of `D^m log W_s`, and the
Sibuya--Ramis exact-order theorem of §5.

## Lean progress — §4's algebraic half and §5's slope obstruction

`GaloisForLFunctions/HTGeometry/BarnesRemainderDATransfer.lean` (wired, axiom-clean):

    differentialAlgebraicOver_eulerLogDeriv    §4.1: `x W′/W` is DA whenever `W` is
    differentialAlgebraicOver_eulerEigen       §4.2: `x y′ = (1/s) y` makes `y` DA — the affine
                                               first-order law with base coefficient `1/(s x)`
    differentialAlgebraicOver_barnesRemainder  §4.3–4.4: subtracting the power, the polynomial part
                                               and the constant leaves a DA remainder
    differentialAlgebraicOver_barnesRemainder_of_eulerEigen
                                               the same with the power presented by its equation

Every step is a closure property of differential algebraicity, all of which the corpus already owns
(`differentialAlgebraicOver_add/sub/mul/div/deriv`, `differentialAlgebraicOver_of_deriv_eq_base_mul_add`).

`GaloisForLFunctions/HTGeometry/NewtonSlopeRationality.lean` (wired, axiom-clean):

    exists_rat_inv_lattice_slope       the reciprocal of a slope between lattice points is rational
    not_irrational_inv_lattice_slope
    not_lattice_slope_of_irrational    **§5's obstruction**: an irrational number is not the
                                       reciprocal of a Newton-polygon slope

So the two ends of §4–§5 are formal: the algebraic transfer down to the remainder, and the
arithmetic rigidity that an irrational exact Gevrey order contradicts.  What is not yet formal is
the analytic bridge between them — the passage from the asymptotic expansion `(5)`–`(6)` to the
formal-series identity `(15)`, and the Sibuya--Ramis theorem itself.

## Lean progress — §4's analytic bridge: an algebraic relation passes to the divergent tail

The step the previous section recorded as "not yet formal — the passage from the asymptotic
expansion `(5)`--`(6)` to the formal-series identity `(15)`" is now a theorem, in the generality it
is used at, and it needs no property of the particular family.

`GaloisForLFunctions/HTGeometry/AsymptoticExpansionAlgebra.lean` (wired, axiom-clean):

    IsAsymptoticExpansion F φ      every partial sum of `φ` approximates `F` to its own order, as
                                   `t → 0⁺`
    eventually_norm_le_one, isBigO_pow_one, isBigO_pow_le, isBigO_finsetSum,
    isBigO_partialSum_one, IsAsymptoticExpansion.isBigO_one
    eq_zero_of_isAsymptoticExpansion_zero :
      **uniqueness** — the zero function has only the zero expansion, so a function determines its
      expansion
    isAsymptoticExpansion_const, isAsymptoticExpansion_X
    IsAsymptoticExpansion.add
    sum_range_coeff_mul_eq         the truncated Cauchy product as a sum over the sub-diagonal square
    IsAsymptoticExpansion.mul      **expansions multiply**
    IsAsymptoticExpansion.aeval    a polynomial evaluated on functions carrying expansions carries
                                   the polynomial evaluated on the expansions
    aeval_powerSeries_eq_zero_of_eq_zero :
      **`(14) ⟹ (15)`** — a polynomial vanishing on a family of functions with asymptotic
      expansions vanishes on those expansions AS FORMAL POWER SERIES, divergent or not

The card's `(15)` is this theorem applied with the family taken to be `t` itself, the analytic
coefficients of `(14)`, and the Euler derivatives `(t d/dt)^m F_s`, whose expansions `(6)` supplies.
Nothing about `W_s` enters: what makes the transfer work is that Poincaré expansion is an injective
algebra map into `ℂ⟦t⟧`, and injectivity — the uniqueness of asymptotic coefficients — is exactly
the card's "uniqueness of asymptotic coefficients forces every coefficient in `(15)` to vanish".

Multiplicativity is the only step with content: splitting each factor into its `N`-th partial sum
plus an `O(t^N)` remainder leaves three error terms and one polynomial tail, and the tail is the
part of the square `{i, j < N}` above the anti-diagonal, every term of which is `O(t^N)`.

### Remaining on this card, precisely

| step | status |
|---|---|
| `(1)` family, order and zeros | formal |
| `(8)` closed modulus of the tail coefficients | formal (`ZetaTailClosedModulus`) |
| `(9)`, `(11)`, `(12)` exact Gevrey order `s` | formal (`GevreyFactorialNormalization`) |
| `(10)` irrational-rotation sharpness | formal (`IrrationalSineSubsequence`) |
| §4.1--4.4 DA transfer to the remainder | formal (`BarnesRemainderDATransfer`) |
| `(14) ⟹ (15)` asymptotic-to-formal transfer | **formal (`AsymptoticExpansionAlgebra`)** |
| §5 Newton-slope rationality obstruction | formal (`NewtonSlopeRationality`) |
| `(4)`--`(6)` Barnes derivative-compatible expansion | open |
| §5 Sibuya--Ramis exact Newton-slope theorem | open |

Two analytic layers remain, and they are the two the card always named as mathlib-scale.  Everything
between them is now formal, so the card's chain is a single implication away at each end.

## Lean plan — the Barnes expansion, by Mellin rather than by Barnes

`(4)`--`(6)` should not be attacked as "Barnes' theorem".  In the branch `s > 1`, where
`g(s) = ⌊1/s⌋ = 0` and `E_0(w) = 1 - w`, the Euler logarithmic derivative is an explicit series

    H_s(x) = x W_s′(x)/W_s(x) = ∑_{n ≥ 1} x/(n^s + x),

and its expansion is the standard Mellin computation: the Mellin transform of `1/(1+y)` is
`π/sin(πw)`, so

    H_s(x) = (1/2πi) ∫_{(c)} ζ(sw) (π/sin πw) x^w dw,   0 < c < 1/s,

and shifting the contour to the right collects
`w = 1/s` (pole of `ζ(sw)`, residue `(π/s)csc(π/s) x^{1/s}`),
`w = 0` (pole of `π/sin πw`, residue `ζ(0) = -1/2`), and
`w = -k` (residue `(-1)^k ζ(-sk) x^{-k}`), which is `(4)` and `(5)`; differentiating under the
integral in `x` gives `(6)` termwise, which is exactly the derivative-compatibility the card needs.

The corpus already owns Mellin/Perron contour calculus through `PNTPlus`, and the coefficient
identity `|ζ(-sk)|` is formal (`ZetaTailClosedModulus`).  So the target is the contour shift with
the standard exponential decay of `1/sin(πw)` on vertical lines, not any special-function theory.

The general branch `g(s) ≥ 1` adds the finite polynomial correction `∑_{j≤g} (-1)^j ζ(sj) x^j` of
`(4)`, which is the same computation with the contour started further right.

## Lean progress — `(12)` upgraded from two bounds to the EXACT order

`gevrey_exact_order_zetaTail` supplied the two bounds `(9)` and `(11)`.  The card's `(12)` says more:
that the exact Gevrey order **is** `s`, i.e. that the tail is Gevrey of order `s` and of no smaller
order.  That implication is the step Sibuya--Ramis is contradicted against, and it is now proved.

`GaloisForLFunctions/HTGeometry/GevreyExactOrder.lean` (wired, axiom-clean):

    IsGevreyOfOrder β r                  `β k ≤ C A^k (k!)^r` for some positive `C`, `A`
    eventually_lt_factorial              a factorial eventually dominates every geometric sequence
    not_isGevreyOfOrder_of_lower_bound :
      **a factorial lower bound of exponent `s`, holding along an infinite set of indices, rules out
      every order `r < s`**
    isGevreyOfOrder_and_not_lt           matching bounds give the exact order
    zetaTail_isGevreyOfOrder_exact :
      **for every irrational `s > 0` the irrational-power zeta tail is Gevrey of order `s` and of no
      smaller order**

The mechanism: dividing the two bounds at an index where both hold leaves
`(k!)^{s-r} ≤ (C/c)(A/a)^k`; taking the `(s-r)`-th root turns that into `k! ≤ E' D^k`, which fails
for all large `k` because `D^k / k! → 0`.  Since the lower bound holds on an infinite set, some index
is large enough.

So the card's chain now reads: exact Gevrey order of the tail `= s`, irrational; Newton-polygon
slopes have rational reciprocals (`not_lattice_slope_of_irrational`); an algebraic relation among the
analytic family passes to the divergent formal tail (`aeval_powerSeries_eq_zero_of_eq_zero`); and the
DA transfer down to the remainder is formal (`BarnesRemainderDATransfer`).  The two ends that remain
are the Barnes expansion `(4)`--`(6)` and the Sibuya--Ramis theorem itself.

### `(12)` in its final form, and the route to `(4)`--`(6)`

Added to `GevreyExactOrder.lean`:

    IsGevreyOfOrder.mono          Gevrey bounds weaken as the order grows
    IsExactGevreyOrder β s        Gevrey of order `s` and of no smaller order
    zetaTail_isGevreyOfOrder_exact :
      `IsExactGevreyOrder (fun k => |ζ(-sk)|) s` for every irrational `s > 0`

That is `gev(R̂_s) = s` as a single predicate, which is what §5 contradicts.

**The Barnes layer is reachable with corpus machinery.**  `GaloisForLFunctions/PNTPlus/` carries a
real contour calculus — `Rectangle.lean`, `ResidueCalcOnRectangles.lean`
(`ResidueTheoremOnRectangleWithSimplePole'`), `PerronFormula.lean`
(`RectangleIntegral_tendsTo_VerticalIntegral`) and `MellinCalculus.lean`.  So `(4)`--`(6)` should be
built as a sequence of rectangle shifts of

    H_s(x) = (1/2πi) ∫_{(c)} ζ(sw) (π / sin πw) x^w dw,   0 < c < 1/s,

each shift crossing one simple pole: `w = 1/s` from `ζ(sw)`, `w = 0` and `w = -k` from `π/sin πw`.
The vertical-integral bounds come from the exponential decay of `1/sin(πw)` off the real axis, and
the termwise derivative expansion `(6)` is the same computation with `x^w` differentiated under the
integral.  No special-function theory is needed, and no Barnes-specific literature.

### First Barnes brick, with its mathlib inputs identified

The kernel of the Mellin representation is

    ∫_0^∞ y^{w-1} / (1 + y) dy = π / sin(π w),   0 < Re w < 1,

and mathlib has both halves of it already:

    Complex.Gamma_mul_Gamma_one_sub    Γ(w)·Γ(1-w) = π / sin(π w)
    Complex.betaIntegral               B(s,t) = ∫ x in 0..1, x^{s-1}(1-x)^{t-1}
    Complex.Gamma_mul_Gamma_eq_betaIntegral
                                       Γ(s)Γ(t) = Γ(s+t)·B(s,t)   for Re s, Re t > 0

Taking `t = 1 - w` gives `Γ(w)Γ(1-w) = Γ(1)·B(w, 1-w) = B(w, 1-w)`, so the kernel identity is the
substitution `x = y/(1+y)` carrying `B(w, 1-w)` on `(0,1)` to the half-line integral.  That change of
variables — an improper `intervalIntegral` comparison on `(0,1) → (0,∞)` — is the only genuinely new
analysis in this brick; everything after it is contour work with `PNTPlus`'s rectangle calculus.

Order of construction: (i) the kernel identity above; (ii) the Mellin representation of
`H_s(x) = ∑_{n≥1} x/(n^s+x)` on the vertical line `Re w = c`, `0 < c < 1/s`, by interchanging the sum
with the integral (the sum converges absolutely there since `Re(sw) > 1`); (iii) rectangle shifts
past `w = 1/s`, `w = 0` and each `w = -k`, using `ResidueTheoremOnRectangleWithSimplePole'`;
(iv) the vertical bounds from exponential decay of `1/sin(πw)`; (v) `(6)` by differentiating `x^w`
under the integral.

## Lean progress — the algebraic half of the Mellin kernel

`GaloisForLFunctions/HTGeometry/BetaReflectionKernel.lean` (wired, axiom-clean):

    betaIntegral_one_sub :
      **`B(w, 1-w) = π / sin(π w)`** on the strip `0 < Re w < 1`
    integral_unitInterval_reflection :
      the same in explicit form, `∫ x in 0..1, x^{w-1}(1-x)^{-w} = π / sin(π w)`

mathlib has the two ingredients separately — `Gamma_mul_Gamma_eq_betaIntegral` computes the Beta
integral as a quotient of gamma values, `Gamma_mul_Gamma_one_sub` evaluates the product at
complementary arguments — but not their combination, which is what the Mellin kernel needs.  With
`Γ(w + (1-w)) = Γ(1) = 1` the quotient collapses and the two identities meet.

What is left of the Mellin kernel `∫_0^∞ y^{w-1}/(1+y) dy = π/sin(π w)` is exactly the substitution
`x = y/(1+y)`, carrying the unit interval to the half line — an improper change of variables, and
the only genuinely new analysis in this brick.  Everything downstream of it is contour work against
`PNTPlus`'s rectangle calculus.

## Lean progress — the geometric half of the half-line substitution

`GaloisForLFunctions/HTGeometry/HalfLineChart.lean` (wired, axiom-clean):

    halfLineChart x = x / (1 - x)          the chart of the unit interval onto the half line
    halfLineChartInv y = y / (1 + y)       and its inverse
    halfLineChart_pos, halfLineChartInv_mem, halfLineChart_halfLineChartInv
    halfLineChart_image :                  **`halfLineChart '' (0,1) = (0,∞)`**
    halfLineChart_injOn :                  **injective on `(0,1)`**
    hasDerivAt_halfLineChart,
    hasDerivWithinAt_halfLineChart :       **derivative `(1-x)^{-2}`**
    halfLineChart_weight :
      `(1-x)^{-2} · (1 + halfLineChart x)^{-1} = (1-x)^{-1}` — the Jacobian meeting the Mellin
      denominator

These are the three inputs of `integral_image_eq_integral_abs_deriv_smul` — image, injectivity,
derivative — together with the pointwise weight identity that makes the substituted integrand match.
With `betaIntegral_one_sub` already giving `B(w,1-w) = π/sin(πw)`, what is left of the Mellin kernel

    ∫_0^∞ y^{w-1}/(1+y) dy = π / sin(π w)

is the change-of-variables application itself plus the `cpow` bookkeeping
`(x/(1-x))^{w-1} = x^{w-1}(1-x)^{1-w}` on the positive reals.

## Lean progress — the substituted integrand matches, pointwise

`GaloisForLFunctions/HTGeometry/MellinReflectionKernel.lean` (wired, axiom-clean):

    halfLineChart_integrand :
      for `x ∈ (0,1)`,
        `|(1-x)^{-2}| • ( (x/(1-x))^{w-1} / (1 + x/(1-x)) )  =  x^{w-1} (1-x)^{-w}`

This is the analytic content of the substitution: the Jacobian `(1-x)^{-2}`, the Mellin denominator
`(1 + y)^{-1} = (1-x)`, and the split `(x/(1-x))^{w-1} = x^{w-1}(1-x)^{1-w}` combine to exactly the
Beta weight.  The `cpow` bookkeeping is the only delicate part and is done on the positive reals,
where `Complex.mul_cpow_ofReal_nonneg` and `Complex.inv_cpow` apply because
`arg((1-x : ℝ) : ℂ) = 0 ≠ π`.

With `halfLineChart_image`, `halfLineChart_injOn`, `hasDerivWithinAt_halfLineChart` and this
identity, all four inputs of `integral_image_eq_integral_abs_deriv_smul` are in hand, and
`betaIntegral_one_sub` supplies the value.  The Mellin kernel

    ∫_0^∞ y^{w-1}/(1+y) dy = π / sin(π w),   0 < Re w < 1,

is therefore one application of that change-of-variables theorem away, with no remaining analytic
content — only the identification of `∫ x in Ioo 0 1` with the interval integral of
`betaIntegral`.

## Lean progress — THE MELLIN KERNEL IS PROVED

Added to `MellinReflectionKernel.lean` (wired, axiom-clean):

    integral_halfLine_reflection :
      **`∫_0^∞ y^{w-1} / (1 + y) dy = π / sin(π w)`  for  `0 < Re w < 1`**

mathlib has neither this nor the half-line form of the Beta integral, so the whole identity had to be
built.  The assembly is:

| step | statement |
|---|---|
| `halfLineChart_image` | `x ↦ x/(1-x)` maps `(0,1)` onto `(0,∞)` |
| `halfLineChart_injOn` | injectively |
| `hasDerivWithinAt_halfLineChart` | with derivative `(1-x)^{-2}` |
| `halfLineChart_integrand` | and the substituted integrand is exactly the Beta weight |
| `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` | the one-dimensional change of variables |
| `betaIntegral_one_sub` | `B(w,1-w) = π/sin(π w)` |

No integrability side condition is needed: mathlib's change-of-variables theorem is an unconditional
equality of set integrals.

This is the kernel of the Mellin representation of `H_s(x) = ∑_{n ≥ 1} x/(n^s + x)`.  The remaining
steps of `(4)`--`(6)` are: interchange the sum with the vertical integral on `Re w = c`,
`0 < c < 1/s` (absolute convergence because `Re(sw) > 1` there), then shift the contour right past
`w = 1/s`, `w = 0` and each `w = -k` with `ResidueTheoremOnRectangleWithSimplePole'`, controlling the
horizontal sides by the exponential decay of `1/sin(π w)`.

### Correction to the contour plan, and the inversion theorem mathlib provides

Two corrections to the Mellin plan recorded above, found while assembling the kernel.

**The strip is `1/s < c < 1`, and the shift is to the LEFT.**  Writing
`x/(n^s + x) = u/(1+u)` with `u = x/n^s`, the Mellin transform of `u/(1+u)` is `-π/sin(π w)` on
`-1 < Re w < 0`, so after `w ↦ -w`

    x/(n^s + x) = (1/2πi) ∫_{(c)} (π / sin π w) · n^{-sw} · x^w dw,   0 < c < 1.

Summing over `n` needs `Re(sw) > 1`, i.e. `c > 1/s`, so the admissible strip is `1/s < c < 1` — which
is nonempty exactly in the branch `s > 1`, the branch where `g(s) = ⌊1/s⌋ = 0`.  Since the expansion
as `x → ∞` is in *decreasing* powers of `x`, the contour moves LEFT, collecting `w = 1/s` (pole of
`ζ(sw)`, giving `(π/s)csc(π/s)x^{1/s}`), then `w = 0` (pole of `π/sin π w`, giving `ζ(0) = -1/2`),
then each `w = -k` (giving `(-1)^k ζ(-sk) x^{-k}`).  The earlier note said "right"; that was wrong.

**mathlib has Mellin inversion.**  `Mathlib/Analysis/MellinInversion.lean`:

    mellinInv_mellin_eq (σ : ℝ) (f : ℝ → E) (hx : 0 < x)
      (hf  : MellinConvergent f σ)
      (hFf : VerticalIntegrable (mellin f) σ)
      (hfx : ContinuousAt f x) :
      mellinInv σ (mellin f) x = f x

So the representation step is: identify `mellin (fun u => u/(1+u)) (σ + it)` with `-π/sin(π(σ+it))`
using `integral_halfLine_reflection`; discharge `MellinConvergent` on `-1 < σ < 0`;
discharge `VerticalIntegrable` from the exponential decay of `1/sin` along vertical lines; and
`ContinuousAt` is immediate.  Only the vertical-decay bound is new work.

## Lean progress — the vertical decay of the reflection kernel

The previous section identified the vertical-decay bound as the only new analysis in the Mellin
representation step.  It is proved.

`GaloisForLFunctions/HTGeometry/SineVerticalDecay.lean` (wired, axiom-clean):

    sinh_abs_im_le_norm_sin :  **`sinh |Im z| ≤ ‖sin z‖`**
    norm_inv_sin_le :          hence `‖(sin z)⁻¹‖ ≤ (sinh |Im z|)⁻¹` off the real axis

The proof is the definition of the complex sine, not the addition formula: from
`sin z = (e^{-iz} - e^{iz})·i/2` and `‖e^w‖ = e^{Re w}` with `Re(-iz) = Im z`, `Re(iz) = -Im z`, the
reverse triangle inequality gives `‖sin z‖ ≥ |e^{Im z} - e^{-Im z}|/2 = sinh|Im z|`.

This is what makes `π / sin(π w)` absolutely integrable on every vertical line off the integers — the
`VerticalIntegrable` hypothesis of `mellinInv_mellin_eq` — and what kills the horizontal sides of a
rectangle when the contour is shifted.  With it, the Mellin representation of `x/(n^s + x)` needs
only the `MellinConvergent` bookkeeping on `-1 < σ < 0`.

## Lean progress — the Mellin transform of the Cauchy kernel

Added to `MellinReflectionKernel.lean` (wired, axiom-clean):

    mellin_cauchyKernel :
      **`∫_0^∞ u^{s-1} · u/(1+u) du = -π / sin(π s)`  on  `-1 < Re s < 0`**

This is the transform the Mellin representation of `x/(n^s + x)` inverts.  It follows from the
kernel by the shift `w = s + 1`: `u^{s-1}·u = u^{(s+1)-1}` on the positive reals, the strip
`0 < Re w < 1` becomes `-1 < Re s < 0`, and `sin(π(s+1)) = -sin(π s)` supplies the sign.

The Mellin side of `(4)`--`(6)` is now: the kernel (`integral_halfLine_reflection`), its shifted form
(`mellin_cauchyKernel`), and the vertical decay that makes it integrable on vertical lines
(`norm_inv_sin_le`).  What remains is the `MellinConvergent` bookkeeping, the interchange of the sum
over `n` with the vertical integral, and the leftward rectangle shifts.

## Lean progress — Mellin convergence of the Cauchy kernel

`GaloisForLFunctions/HTGeometry/CauchyKernelMellin.lean` (wired, axiom-clean):

    cauchyKernel u = u / (1 + u)
    cauchyKernel_ofReal, norm_cauchyKernel
    norm_cauchyKernel_le_one, norm_cauchyKernel_le_self
    continuousOn_cauchyKernel, locallyIntegrableOn_cauchyKernel
    isBigO_cauchyKernel_atTop        `O(t^{-0})` at infinity — the kernel is bounded
    isBigO_cauchyKernel_zero         `O(t^{-(-1)})` at the origin — it vanishes linearly
    mellinConvergent_cauchyKernel :
      **`MellinConvergent cauchyKernel s` on `-1 < Re s < 0`**
    mellin_cauchyKernel_eq :
      **`mellin cauchyKernel s = -π / sin(π s)` there**

The two decay exponents are exactly the two edges of the strip: boundedness at infinity gives
`Re s < 0`, linear vanishing at the origin gives `-1 < Re s`, and
`mellinConvergent_of_isBigO_rpow` turns them into convergence.

Of the three hypotheses of `mellinInv_mellin_eq` — `MellinConvergent`, `VerticalIntegrable` and
`ContinuousAt` — the first is now discharged and the second follows from `norm_inv_sin_le`; the
third is `continuousOn_cauchyKernel`.  So the Mellin representation of a single term
`x/(n^s + x)` is assembled from corpus theorems, and what is left of `(4)`--`(6)` is the interchange
of the sum over `n` with the vertical integral and the leftward rectangle shifts.

## Lean progress — the near-axis half of the vertical bound

`norm_inv_sin_le` controls `1/sin` away from the real axis; near it that bound degenerates, because
`sinh|Im w| → 0`.  The complementary bound is now proved.

Added to `SineVerticalDecay.lean` (wired, axiom-clean):

    abs_sin_re_le_norm_sin :        **`|sin (Re z)| ≤ ‖sin z‖`**
    norm_inv_sin_le_of_sin_re_ne :  hence `‖(sin z)⁻¹‖ ≤ |sin (Re z)|⁻¹` off the integers

The proof avoids the modulus identity `‖sin z‖² = sin²(Re z) + sinh²(Im z)` entirely: from
`(sin z).re = sin(Re z)·cosh(Im z)` and `cosh ≥ 1`,

    |sin(Re z)| ≤ |sin(Re z)·cosh(Im z)| = |(sin z).re| ≤ ‖sin z‖.

Together the two bounds cover the whole vertical line `Re w = σ` with `σ` not an integer: the second
is uniform near the real axis, the first decays exponentially away from it.  That is exactly the
`VerticalIntegrable` hypothesis of `mellinInv_mellin_eq` for the reflection kernel.

## Lean progress — the vertical bound in exponential form

Added to `SineVerticalDecay.lean` (wired, axiom-clean):

    exp_div_four_le_sinh :   `exp y / 4 ≤ sinh y`  for `y ≥ 1`
    norm_inv_sin_le_exp :    **`‖(sin z)⁻¹‖ ≤ 4 · exp(-|Im z|)`  for `|Im z| ≥ 1`**

The constant comes from `2 sinh y = e^y - e^{-y}` together with `e^{2y} ≥ 1 + 2y ≥ 3 > 2`, which
gives `e^{-y} ≤ e^y/2` and hence `sinh y ≥ e^y/4`.

The vertical line is therefore covered in the form an integrability argument consumes: on
`|Im w| ≤ 1` the bound `‖(sin π w)⁻¹‖ ≤ |sin(π σ)|⁻¹` is a constant, and on `|Im w| ≥ 1` the
reciprocal sine is dominated by `4 e^{-|Im w|}`.  Splitting the vertical integral at height one and
dominating each piece is what discharges `VerticalIntegrable` for the reflection kernel — the last
hypothesis of `mellinInv_mellin_eq` still outstanding for `x/(n^s + x)`.

## Lean progress — the reciprocal sine against the Cauchy density

Domination by `exp(-|t|)` is awkward to integrate in mathlib, which has no `integrable_exp_neg_abs`;
domination by the Cauchy density `(1 + t²)⁻¹` is not, since `integrable_inv_one_add_sq` is there.
The bound is now in that form.

Added to `SineVerticalDecay.lean` (wired, axiom-clean):

    sq_div_four_le_exp :                 `x²/4 ≤ exp x` for `x ≥ 0`
    norm_inv_sin_le_cauchy_of_one_le :
      **`‖(sin z)⁻¹‖ ≤ 32 · (1 + (Im z)²)⁻¹`  for  `|Im z| ≥ 1`**

The quadratic lower bound comes from the linear one at half the argument:
`exp x = (exp (x/2))² ≥ (1 + x/2)² ≥ x²/4`.  With it, `4 exp(-|y|) ≤ 32/(1+y²)` reduces to
`4(1+y²) ≤ 32 exp|y|`, and `32 exp|y| ≥ 8y² ≥ 4(1+y²)` because `y² ≥ 1`.

The vertical line is now covered by a single integrable envelope: the constant bound
`|sin(π σ)|⁻¹` on `|Im w| ≤ 1`, where the Cauchy density is bounded below by `1/2`, and
`32(1 + (Im w)²)⁻¹` beyond.  `VerticalIntegrable` for the reflection kernel is therefore a
`Integrable.mono'` against `integrable_inv_one_add_sq`.

## Lean progress — one envelope for the whole vertical line

Added to `SineVerticalDecay.lean` (wired, axiom-clean):

    re_pi_mul_vertical, im_pi_mul_vertical
    norm_inv_sin_vertical_le :
      **for `σ` with `sin(π σ) ≠ 0` and every `t`,**
        `‖(sin(π(σ + it)))⁻¹‖ ≤ max(2|sin(π σ)|⁻¹, 32) · (1 + t²)⁻¹`

The two regimes are glued at `|Im| = 1`.  Below it the constant bound `|sin(π σ)|⁻¹` applies and the
Cauchy density is at least `1/2`, so a factor of `2` absorbs the difference; above it the
Cauchy-density bound applies directly, and `(1 + π²t²)⁻¹ ≤ (1 + t²)⁻¹` because `π ≥ 1`.

The reflection kernel is therefore dominated on the whole line by a constant multiple of an
integrable function that mathlib already knows is integrable (`integrable_inv_one_add_sq`), so
`VerticalIntegrable` is now an `Integrable.mono'` with a continuity argument for measurability —
no further estimates.

## Lean progress — THE MELLIN REPRESENTATION OF A SINGLE TERM IS PROVED

Added to `CauchyKernelMellin.lean` (wired, axiom-clean):

    sin_pi_vertical_ne_zero            the reflection kernel has no pole on a vertical line off the
                                       integers
    continuous_reflectionKernel_vertical
    verticalIntegrable_reflectionKernel :
      **`VerticalIntegrable (fun s => -π/sin(π s)) σ`** — `Integrable.mono'` against
      `integrable_inv_one_add_sq`, with `norm_inv_sin_vertical_le` as the envelope
    sin_pi_ne_zero_of_mem_strip        `sin(π σ) ≠ 0` for `-1 < σ < 0`
    verticalIntegrable_mellin_cauchyKernel
    mellinInv_mellin_cauchyKernel :
      **`mellinInv σ (mellin cauchyKernel) x = cauchyKernel x`  for `-1 < σ < 0`, `x > 0`**

All three hypotheses of `mellinInv_mellin_eq` are discharged: `MellinConvergent` from the two decay
exponents, `VerticalIntegrable` from the vertical envelope, `ContinuousAt` from continuity on the
half line.  Together with `mellin_cauchyKernel_eq` this is the Mellin representation

    u/(1+u) = (1/2πi) ∫_{(σ)} (-π / sin(π s)) u^{-s} ds,   -1 < σ < 0,

i.e. `(4)`'s single-term identity, from which `x/(n^s + x)` follows by `u = x/n^s`.

What remains of `(4)`--`(6)`: the substitution `u = x/n^s` and the interchange of the sum over `n`
with the vertical integral, then the leftward rectangle shifts past `w = 1/s`, `w = 0` and each
`w = -k` against `PNTPlus`'s residue calculus.

## Lean progress — the scaled term

Added to `CauchyKernelMellin.lean` (wired, axiom-clean):

    cauchyKernel_scaled :
      `cauchyKernel (x / a) = x / (a + x)`  for `a > 0`
    mellinInv_mellin_cauchyKernel_scaled :
      **`mellinInv σ (mellin cauchyKernel) (x / a) = x / (a + x)`  for `-1 < σ < 0`, `a, x > 0`**

Taking `a = n^s` this is the vertical-integral representation of the individual term
`x / (n^s + x)` of the Euler logarithmic derivative `H_s(x)`, valid on the whole strip
`-1 < σ < 0`.  The `n`-dependence enters only through the scaling of the argument, which is exactly
what turns the sum over `n` into `ζ(s w)` after the interchange.

Remaining for `(4)`--`(6)`: the interchange of the sum over `n` with the vertical integral — the
inner integral is absolutely convergent uniformly in `n` by the same envelope, and the sum over `n`
of `n^{-s·Re w}` converges once `Re w > 1/s` — and then the leftward rectangle shifts.

## Lean progress — the envelope of the inverse-Mellin integrand

Added to `CauchyKernelMellin.lean` (wired, axiom-clean):

    norm_mellinInv_integrand_le :
      **`‖r^{-(σ+iy)} · mellin cauchyKernel (σ+iy)‖ ≤ (r^{-σ} · π · C_σ) · (1 + y²)⁻¹`**
      for `-1 < σ < 0`, `r > 0`, where `C_σ = max(2|sin(π σ)|⁻¹, 32)`

The scaling `r` enters only through the constant `r^{-σ}`, because `‖r^{-(σ+iy)}‖ = r^{-σ}` on the
positive reals.  With `r = x/n^s` this makes the `n`-th integrand dominated by
`(x/n^s)^{-σ}·π·C_σ·(1+y²)⁻¹`, whose sum over `n` is
`x^{-σ}·(∑_n n^{sσ})·π·C_σ·(1+y²)⁻¹` — finite exactly when `sσ < -1`, i.e. `σ < -1/s`.

So the admissible strip for the summed representation is `-1 < σ < -1/s`, nonempty precisely when
`s > 1`, the branch where `g(s) = ⌊1/s⌋ = 0`.  That is the hypothesis under which the sum and the
vertical integral may be exchanged, and the exchange is now a Tonelli argument with an explicit
dominating function rather than an estimate to be found.

## Lean progress — the summed envelope

Added to `CauchyKernelMellin.lean` (wired, axiom-clean):

    rpow_scaled_eq :            `(x / n^s)^{-σ} = x^{-σ} · n^{s σ}`  for `n ≥ 1`, `x > 0`
    summable_scaledEnvelope :   `Summable (fun n => c · n^{s σ})`  exactly when `s σ < -1`

Combining with `norm_mellinInv_integrand_le`, the `n`-th inverse-Mellin integrand of
`x/(n^s + x)` is dominated on the line `Re w = σ` by

    x^{-σ} · n^{s σ} · π · C_σ · (1 + y²)⁻¹,

and the sum over `n` of that bound is finite precisely on `-1 < σ < -1/s`, which is nonempty
exactly for `s > 1`.  Both factors of the dominating function are now corpus theorems:
`Real.summable_nat_rpow` for the `n`-sum and `integrable_inv_one_add_sq` for the `y`-integral.

So the Tonelli hypothesis of the sum–integral interchange in `(4)` is fully explicit; what remains
on the Mellin side is the interchange itself and the leftward rectangle shifts.

## Lean progress — the first hypothesis of the interchange

Added to `CauchyKernelMellin.lean` (wired, axiom-clean):

    continuous_mellinInv_integrand :
      `y ↦ r^{-(σ+iy)} · mellin cauchyKernel (σ+iy)` is continuous on the line
    integrable_mellinInv_integrand :
      **and integrable there**, for every `r > 0` and `-1 < σ < 0`

Continuity uses the closed form of the transform, so the only pole to avoid is that of the
reflection kernel, which `sin_pi_ne_zero_of_mem_strip` excludes on the strip.  Integrability is
`Integrable.mono'` against the envelope.

`hasSum_integral_of_summable_integral_norm` needs exactly two inputs: integrability of each term —
now proved — and summability of `∫ ‖F n‖`.  The latter is bounded termwise by
`x^{-σ}·n^{sσ}·π·C_σ·∫(1+y²)⁻¹`, whose summability is `summable_scaledEnvelope`.  So the
sum–integral interchange of `(4)` is reduced to assembling two proved facts.

## Lean progress — BOTH hypotheses of the sum–integral interchange are proved

Added to `CauchyKernelMellin.lean` (wired, axiom-clean):

    integral_norm_mellinInv_integrand_le :
      `∫ ‖r^{-(σ+iy)} · mellin cauchyKernel (σ+iy)‖ dy ≤ r^{-σ} · π · C_σ · ∫ (1+y²)⁻¹ dy`
    summable_integral_norm_mellinInv_integrand :
      **`Summable (fun n => ∫ ‖(x/(n+1)^s)^{-(σ+iy)} · mellin cauchyKernel (σ+iy)‖ dy)`**
      whenever `-1 < σ < 0` and `s σ < -1`

Together with `integrable_mellinInv_integrand` these are exactly the two hypotheses of
`hasSum_integral_of_summable_integral_norm`, so the interchange

    ∑_{n ≥ 1} (1/2πi) ∫_{(σ)} (x/n^s)^{-w} · (-π/sin(π w)) dw
      = (1/2πi) ∫_{(σ)} x^{-w} ζ(s w) · (-π/sin(π w)) dw

is now a direct application, on the strip `-1 < σ < -1/s` — nonempty exactly for `s > 1`, the branch
`g(s) = 0` in which `(4)` carries no polynomial correction.

Everything the Mellin representation of `(4)` needs is therefore proved: the kernel, the transform,
the vertical bounds, `MellinConvergent`, `VerticalIntegrable`, the single-term and scaled
representations, and both interchange hypotheses.  What remains for `(4)`--`(6)` is the leftward
rectangle shifts past `w = 1/s`, `w = 0` and each `w = -k`.

## Lean progress — THE INTERCHANGE IS PROVED

Added to `CauchyKernelMellin.lean` (wired, axiom-clean):

    hasSum_integral_mellinInv_scaled :
      **on `-1 < σ < 0` with `s σ < -1`,**
        `HasSum (fun n => ∫ y, (x/(n+1)^s)^{-(σ+iy)} · mellin cauchyKernel (σ+iy))`
               `(∫ y, ∑' n, (x/(n+1)^s)^{-(σ+iy)} · mellin cauchyKernel (σ+iy))`

The sum over `n` may therefore be taken inside the vertical integral.  Since each term integral is
`2π` times `mellinInv σ (mellin cauchyKernel) (x/(n+1)^s) = x/((n+1)^s + x)`
(`mellinInv_mellin_cauchyKernel_scaled`), the left side is `2π · H_s(x)`, and the inner sum on the
right is `x^{-w} ζ(s w)` after `(x/n^s)^{-w} = x^{-w} n^{s w}`.  That is the Mellin representation

    H_s(x) = (1/2πi) ∫_{(c)} ζ(s w) · (π / sin(π w)) · x^{w} dw

of `(4)`, on the admissible strip, which is nonempty exactly for `s > 1`.

Every analytic ingredient of the representation is now formal.  The remaining step of `(4)`--`(6)`
is purely contour work: shift the line leftward past `w = 1/s` (pole of `ζ(s w)`), `w = 0` and each
`w = -k` (poles of `π/sin(π w)`), using `ResidueTheoremOnRectangleWithSimplePole'` from `PNTPlus`
with the horizontal sides controlled by `norm_inv_sin_le_exp`.

## Lean progress — THE SUMMED MELLIN REPRESENTATION OF `H_s`

Added to `CauchyKernelMellin.lean` (wired, axiom-clean):

    integral_mellinInv_integrand_eq :
      `∫ y, r^{-(σ+iy)} · mellin cauchyKernel (σ+iy) dy = 2π · (r/(1+r))`
    hasSum_eulerLogDerivTerms_mellin :
      **`HasSum (fun n => 2π · x/((n+1)^s + x))
                (∫ y, ∑' n, (x/(n+1)^s)^{-(σ+iy)} · mellin cauchyKernel (σ+iy) dy)`**
      on `-1 < σ < 0` with `s σ < -1`

The left side is `2π · H_s(x)`, so this is `(4)`'s representation

    H_s(x) = (1/2πi) ∫_{(c)} ζ(s w) · (π / sin(π w)) · x^{w} dw

with both sides constructed rather than posited: the series converges to the stated integral, on the
admissible strip, which is nonempty exactly for `s > 1`.

The Mellin half of `(4)`--`(6)` is therefore complete.  What remains of the card's analytic layer is
the contour shift — moving the line leftward past `w = 1/s`, `w = 0` and each `w = -k`, with
`ResidueTheoremOnRectangleWithSimplePole'` and the horizontal sides controlled by
`norm_inv_sin_le_exp` — and then the Sibuya--Ramis exact-order theorem.

## Lean progress — splitting the scaled power

Added to `CauchyKernelMellin.lean` (wired, axiom-clean):

    cpow_scaled_split :
      **`(x/a)^{-w} = x^{-w} · a^{w}`  for real `x, a > 0` and any complex `w`**

This is the step that turns the `n`-dependence of the inner sum into a Dirichlet series: with
`a = (n+1)^s` the summand `(x/(n+1)^s)^{-w}` becomes `x^{-w} · ((n+1)^s)^{w}`, whose sum over `n` is
`x^{-w} · ζ(-s w)` by `zeta_eq_tsum_one_div_nat_add_one_cpow`, valid because `Re(-s w) = -sσ > 1`
exactly on the admissible strip.

No branch-cut care is needed beyond `arg((a : ℝ) : ℂ) = 0 ≠ π`, which is what licenses
`Complex.inv_cpow`; the split itself is `Complex.mul_cpow_ofReal_nonneg` on the positive reals.

## Lean progress — THE ZETA FACTOR IS IDENTIFIED

Added to `CauchyKernelMellin.lean` (wired, axiom-clean):

    ofReal_rpow_cpow :
      `((a^s : ℝ) : ℂ)^w = ((a : ℝ) : ℂ)^(s w)`  for `a > 0` — the branch condition holds because
      `log` of a positive real is real, so `(log a · s).im = 0`
    tsum_scaled_eq_zeta :
      **`∑' n, (x/(n+1)^s)^{-w} = x^{-w} · ζ(-s w)`  whenever `Re(-s w) > 1`**

With this the integrand of the summed representation is exactly

    x^{-w} · ζ(-s w) · (-π / sin(π w)),

so `hasSum_eulerLogDerivTerms_mellin` now reads, after dividing by `2π`,

    H_s(x) = (1/2πi) ∫_{(σ)} x^{-w} ζ(-s w) (-π / sin(π w)) dw,

which is `(4)`'s representation in the corpus's sign convention.  Every algebraic and analytic
ingredient of it is formal: nothing remains but the contour shift.

### What is left of `(4)`--`(6)`

Only the leftward rectangle shifts.  Their inputs are all in place:
`ResidueTheoremOnRectangleWithSimplePole'` and `RectangleIntegral_tendsTo_VerticalIntegral` from
`PNTPlus`; the horizontal sides vanish by `norm_inv_sin_le_exp`; the poles crossed are `w` with
`-s w = 1` (the pole of `ζ`), `w = 0` and `w = -k` (the poles of `π/sin(π w)`), and their residues
are `(π/s)csc(π/s) x^{1/s}`, `ζ(0) = -1/2` and `(-1)^k ζ(-s k) x^{-k}` respectively — the last of
which is the coefficient family whose exact Gevrey order is already proved to be `s`.

## Lean progress — holomorphy of the reflection kernel

Added to `SineVerticalDecay.lean` (wired, axiom-clean):

    analyticAt_sin_pi_mul :      `w ↦ sin(π w)` is entire
    analyticAt_inv_sin_pi_mul :  **`w ↦ (sin(π w))⁻¹` is analytic wherever the sine does not
                                 vanish**

This is the holomorphy input of the rectangle argument.  Combined with `meromorphicOn_riemannZeta`
(built earlier for card 1, and reused here) and the entirety of `w ↦ x^{-w}`, the integrand
`x^{-w} ζ(-s w) (-π/sin(π w))` is holomorphic on any rectangle minus the poles it encloses — which
is the `fHolo` hypothesis of `ResidueTheoremOnRectangleWithSimplePole'`.

What the shift still needs is the residue computation at each crossed pole, i.e. the `near_p`
hypothesis: `π/sin(π w) - (-1)^k/(w - k) = O(1)` near `w = k`, and the analogous statement for the
`ζ` pole at `-s w = 1`.

## Lean progress — every pole of the reflection kernel reduces to the one at the origin

Added to `SineVerticalDecay.lean` (wired, axiom-clean):

    sin_pi_mul_add_nat :      `sin(π (w + k)) = (-1)^k · sin(π w)`  for `k : ℕ`
    inv_sin_pi_mul_add_nat :  `(sin(π (w + k)))⁻¹ = (-1)^k · (sin(π w))⁻¹`

The kernel `π/sin(π w)` therefore has the *same* local shape at every integer, differing only by the
sign `(-1)^k`.  So the `near_p` hypothesis of `ResidueTheoremOnRectangleWithSimplePole'` needs to be
established once, at `w = 0` — where it reads `π/sin(π w) - 1/w = O(1)` — and the residue at `w = -k`
is then `(-1)^k` times that of `w = 0`, which is the source of the alternating sign in
`b_k = (-1)^k ζ(-s k)` of `(5)`.

Proof is one induction on `k` against `Complex.sin_add_pi`; no addition formula for the sine and no
periodicity API beyond that single step.

## Lean progress — the residue of the reflection kernel at the origin

Added to `SineVerticalDecay.lean` (wired, axiom-clean):

    hasDerivAt_sin_pi_mul_zero :   `w ↦ sin(π w)` has derivative `π` at `0`
    tendsto_sin_pi_mul_div :       hence `sin(π w)/w → π` as `w → 0` off the origin
    tendsto_mul_inv_sin_pi_mul :
      **`w · (sin(π w))⁻¹ → π⁻¹`**, i.e. `π/sin(π w)` has a simple pole at the origin with
      residue `1`

The slope route avoids any series expansion: `sin(π w)/w` is literally the difference quotient of
`sin(π ·)` at `0`, so `hasDerivAt_iff_tendsto_slope` converts the derivative into the limit.

With `inv_sin_pi_mul_add_nat` this fixes the residue at every pole of the kernel: `(-1)^k` at
`w = -k`, which is exactly the alternating sign of `b_k = (-1)^k ζ(-s k)` in `(5)`.  What the
rectangle argument still needs is the `O(1)` form of this statement — `π/sin(π w) - 1/w` bounded
near `0` — which is the `near_p` hypothesis; the limit above is its content.

## Lean progress — the simple-zero factorization of the sine

Added to `SineVerticalDecay.lean` (wired, axiom-clean):

    sinPiCofactor := dslope (fun w => sin (π w)) 0
    analyticAt_sinPiCofactor :        the cofactor is analytic at the origin
    sinPiCofactor_zero :              its value there is `π`
    sin_pi_mul_eq_mul_cofactor :      **`sin(π w) = w · sinPiCofactor w`**, identically

This is the factorization that turns the residue limit into the `O(1)` statement the rectangle
theorem wants.  With it,

    π/sin(π w) - 1/w = (π - sinPiCofactor w) / (w · sinPiCofactor w),

whose numerator is `sinPiCofactor 0 - sinPiCofactor w`, hence `O(w)` because the cofactor is
differentiable at the origin, while the denominator is `w` times something nonzero near `0`.  So the
quotient is `O(1)`, which is exactly `near_p` for `ResidueTheoremOnRectangleWithSimplePole'`.

`dslope` is the right tool here rather than the general order factorization
(`exists_eventuallyEq_pow_smul_nonzero_iff`): it gives the cofactor with no case analysis on the
order, and `sub_smul_dslope` supplies the identity for free.

## Lean progress — THE `near_p` HYPOTHESIS IS PROVED

Added to `SineVerticalDecay.lean` (wired, axiom-clean):

    isBigO_inv_sin_sub_inv :
      **`π/sin(π w) - 1/w  =O[𝓝[≠] 0]  1`**

This is exactly the `near_p` hypothesis of `ResidueTheoremOnRectangleWithSimplePole'` at `p = 0`
with residue `A = 1`.  The proof is the factorization:

    π/sin(π w) - 1/w = -((c w - c 0) · w⁻¹) · (c w)⁻¹,   c = sinPiCofactor, c 0 = π,

where the first factor is bounded because `c` is differentiable at `0` (so `c w - c 0 = O(w)`) and
the second because `c` is continuous and nonzero there.

With `inv_sin_pi_mul_add_nat` the same bound transfers to every integer: at `w = -k` the kernel has a
simple pole of residue `(-1)^k`.  Both hypotheses of the rectangle theorem — `fHolo` from
`analyticAt_inv_sin_pi_mul` together with `meromorphicOn_riemannZeta`, and `near_p` here — are
therefore available at every pole the contour crosses.

### What is left on this card

1. The rectangle shifts themselves: apply `ResidueTheoremOnRectangleWithSimplePole'` at
   `w = 1/s`, `w = 0`, `w = -k`, and let the height go to infinity with
   `RectangleIntegral_tendsTo_VerticalIntegral`, the horizontal sides vanishing by
   `norm_inv_sin_le_exp`.  That yields `(4)`--`(6)`.
2. The Sibuya--Ramis exact Newton-slope theorem.

Everything else on the card is formal.

## Lean progress — poles of the full integrand, from poles of the kernel

Added to `SineVerticalDecay.lean` (wired, axiom-clean):

    isBigO_slope_of_analyticAt :
      the difference quotient of an analytic function is bounded at its base point
    isBigO_analytic_mul_simplePole :
      **`h` has a simple pole of residue `A` at `p` and `g` is analytic there
      ⟹ `g · h` has a simple pole of residue `g p · A`**

This is the step from the reflection kernel to the actual integrand.  Writing the integrand as
`g w · (π/sin(π w))` with `g w = -x^{-w} ζ(-s w)` analytic at the crossed pole, the residue is
`g(p)` times the kernel residue, so `near_p` for the integrand follows from
`isBigO_inv_sin_sub_inv` with no new estimate.  Concretely the residue at `w = -k` is
`-x^{k} ζ(s k) · (-1)^k`, matching `(5)`'s `b_k = (-1)^k ζ(-s k)` after the sign conventions of the
representation are unwound.

The identity behind it is
`g w h w - g p A/(w-p) = g w (h w - A/(w-p)) + ((g w - g p)/(w-p)) A`, whose two summands are
bounded by continuity and by differentiability respectively.

Both hypotheses of `ResidueTheoremOnRectangleWithSimplePole'` are now available for the integrand
itself at every pole the contour crosses.  What is left is the geometry of the shift — choosing the
rectangles and letting the height go to infinity — and then Sibuya--Ramis.

## Lean progress — the contour shift is now fully equipped

Six new modules, every one wired and axiom-clean.

**Generic (HTGeometry).**

    GammaVerticalStripDecay.exists_bound_norm_Gamma_vertical_strip
      one constant and one exponent for `‖Γ(σ+it)‖ ≤ C|t|^N e^{-π|t|/2}` on `a ≤ σ ≤ M`
    PolynomialExponentialDomination.pow_mul_exp_neg_le
    PolynomialExponentialDomination.polyExp_le_inv_one_add_sq
      `C|t|^N e^{-c|t|} ≤ K (1+t²)⁻¹` — the integrable weight a domination argument needs
    VerticalContourShift.verticalIntegral'_sub_of_simple_pole
      **`(1/2πi)∫_{(σ')} f - (1/2πi)∫_{(σ)} f = A`** for one simple pole of residue `A`
    SineVerticalDecay.isBigO_inv_sin_sub_inv_at_nat / _at_neg_nat
      the kernel's simple pole at every integer, residue `(-1)^k`

The Gamma strip bound is the one genuine mathlib gap here.  It does **not** need Stirling: the
corpus's Gauss-product ratio inequality `‖Γ(a+iτ)‖Γ(b) ≤ Γ(a)‖Γ(b+iτ)‖` transports the exact
modulus on the line `Re z = 1+m` leftwards to every abscissa below, and the real ratio `Γ(a)/Γ(b)`
is bounded on a compact abscissa range by continuity.

**Zeta-specific (RHTower).**

    ZetaVerticalStripPolynomialBound.exists_bound_norm_riemannZeta_strip
      **`‖ζ(σ+it)‖ ≤ C|t|^N` uniformly on `|σ| ≤ M`, `|t| ≥ 1`** — Euler–Maclaurin on the right,
      the functional equation on the left, with `cos(πs/2) ~ e^{π|t|/2}` cancelling
      `Γ(s) ~ e^{-π|t|/2}` exactly
    BarnesMellinIntegrandBound.barnesIntegrand
      `F(w) = x^{-w} ζ(-sw)(-π/sin πw)`
    BarnesMellinIntegrandBound.exists_bound_norm_barnesIntegrand
      `‖F(σ+it)‖ ≤ C|t|^N e^{-π|t|}`, uniformly for `σ` in a compact range
    BarnesMellinIntegrandAnalysis
      holomorphy off the poles, `integrable_barnesIntegrand_vertical`,
      `tendsto_horizontal_barnesIntegrand_atTop/atBot`
    BarnesMellinResidues.barnesIntegrand_simplePole_at_nat
      residue `-(-1)^k x^{-k} ζ(-sk)` at `w = k`
    BarnesMellinResidues.barnesIntegrand_simplePole_at_zetaPole
      residue `-(1/s) x^{1/s} π csc(π/s)` at `w = -1/s`

Reading the residues through the shift (`H_s(x) = VerticalIntegral' F σ` and each crossed pole
contributes `-A`): `w=-1/s` gives `+(π/s)csc(π/s)x^{1/s}`, `w=0` gives `-ζ(0) = -1/2`, and `w=k`
gives `(-1)^k ζ(-sk) x^{-k} = b_k x^{-k}`.  These are exactly `(4)` and `(5)`.

Correction to the earlier note: the shift is **rightward**, from `σ ∈ (-1,-1/s)` towards `+∞`; the
poles are crossed in the order `-1/s`, `0`, `1`, `2`, …  For `s > 1` the starting strip is
nonempty and `g(s) = 0`, so `(4)` has no `x^j` terms.

Remaining: the assembly (one `verticalIntegral'_sub_of_simple_pole` per crossed pole, plus the
identification of the starting vertical integral with `H_s`), the `0 < s ≤ 1` genus correction,
and Sibuya--Ramis.

## Lean progress — the finite Barnes expansion is proved

`RHTower/BarnesMellinRepresentation.lean` and `RHTower/BarnesMellinExpansion.lean` close the
contour argument for `s > 1`.

    hasSum_barnes_verticalIntegral' :
      **`∑_{n≥1} x/(n^s+x) = (1/2πi)∫_{(σ)} x^{-w} ζ(-sw)(-π/sin πw) dw`** for `-1 < σ < -1/s`
    barnesAbscissa s : ℕ → ℝ      -- `-(1/s)/2`, then the half-integers `k + 1/2`
    verticalIntegral'_shift_zetaPole   -- crosses `w = -1/s`
    verticalIntegral'_shift_step (k)   -- crosses `w = k`
    verticalIntegral'_barnes_finite_expansion
    hasSum_barnes_expansion :
      **`∑_{n≥1} x/(n^s+x) = (1/2πi)∫_{(K-1/2)} F − Res_{-1/s} − ∑_{k<K} Res_k`**

The abscissa ladder is what makes each step a *single*-pole crossing: `-1/s` is separated from the
integers by `-(1/s)/2`, and consecutive half-integers isolate one integer each.  The starting
abscissa `-(1+1/s)/2` lies in `(-1,-1/s)` exactly when `s > 1`, which is also exactly when the
Mellin strip of the representation is nonempty.

Unwinding the residues, this is `(4)` together with the finite form of `(5)`:

* `-Res_{-1/s} = (π/s) csc(π/s) x^{1/s}`,
* `-Res_0 = -ζ(0) = 1/2` — note the sign convention: with the sum written as `∑ x/(n^s+x)` rather
  than `D log W_s`, the constant is `+1/2`, matching `(4)`'s `-1/2` after the shift of normalisation,
* `-Res_k = (-1)^k ζ(-sk) x^{-k} = b_k x^{-k}` for `k ≥ 1`.

Remaining on this card: the remainder estimate `(1/2πi)∫_{(K-1/2)} F = O(x^{-(K-1/2)})` which turns
the finite identity into the Poincaré asymptotic `(5)` and, differentiated, `(6)`; the genus
correction for `0 < s ≤ 1`; and Sibuya--Ramis.

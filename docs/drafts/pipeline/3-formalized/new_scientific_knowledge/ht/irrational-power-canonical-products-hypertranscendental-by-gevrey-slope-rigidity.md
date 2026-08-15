# Irrational-power canonical products are hypertranscendental by Gevrey-slope rigidity

- **ID:** `irrational-power-canonical-products-hypertranscendental-by-gevrey-slope-rigidity`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / HYPERTRANSCENDENCE / GEVREY RIGIDITY
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [PRELIMINARY NOVELTY PASS] [NOT AN RH RESULT]`
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
- [x] unconditional analytic Lean formalization

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

## Lean progress — (4), (5) and (6) are all proved for `s > 1`

Three further modules complete the Barnes side of the card.

    BarnesMellinPowIntegrand    -- `F_m(w) = (-w)^m x^{-w} ζ(-sw)(-π/sin πw)`, its uniform decay,
                                   holomorphy, vertical integrability, horizontal vanishing
    BarnesMellinPowResidues     -- residues of `F_m`: the entire factor `(-w)^m` multiplies each
                                   residue by `(-p)^m`
    BarnesMellinRemainder       -- `‖(1/2πi)∫_{(σ)} F_m‖ ≤ C_σ x^{-σ}`, hence
                                   **`barnes_poincare_expansion`**: the error after `K+1` terms is
                                   `O(x^{-(K+1/2)})`
    BarnesMellinEulerDerivative -- `d/dx (1/2πi)∫ F_m = x^{-1}(1/2πi)∫ F_{m+1}`
                                   (differentiation under the integral, dominated by the kernel's
                                   exponential decay), hence `eulerDeriv^[m]` of the Euler sum is
                                   again a contour integral, hence
                                   **`barnes_poincare_expansion_euler`**

The shift, ladder and expansion modules were generalised in place to carry the weight `m`, so the
`m = 0` statements are the special case and no proof is duplicated.

`barnes_poincare_expansion_euler` is exactly `(6)`:

```text
D^m ( ∑_{n≥1} x/(n^s+x) ) + (-p_ζ)^m·Res_ζ + ∑_{k≤K} (-k)^m·Res_k  =  O(x^{-(K+1/2)}) ,
```

the `k`-th coefficient of the `m`-th Euler derivative being `(-k)^m` times the `k`-th coefficient of
the original — the termwise-differentiable form the card asks for.  The estimate is uniform: one
constant per `(m, K)`, valid for every `x > 0`.

The whole chain is unconditional and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

Remaining on this card: the genus correction for `0 < s ≤ 1` (where the Mellin strip
`-1 < σ < -1/s` is empty and the `E_g` subtractions enter), and Sibuya--Ramis.

## The genus correction, `0 < s ≤ 1` — the route

For `s ≤ 1` the Mellin strip `-1 < σ < -1/s` of the representation is empty, because the Dirichlet
series `∑ n^{sw}` needs `Re w < -1/s ≤ -1` while the Cauchy kernel needs `Re w > -1`.  The fix is
not to widen the kernel's strip but to differentiate: with `g = floor(1/s)` the `E_g` subtraction in
`(1)` is a polynomial in `x` of degree `g`, so

```text
d^{g+1}/dx^{g+1} H_s(x) = ∑_{n≥1} d^{g+1}/dx^{g+1} [ x/(n^s+x) ]
                        = -(-1)^{g+1}(g+1)! ∑_{n≥1} n^s/(n^s+x)^{g+2} ,
```

with **no** subtractions left.  Writing `n^s/(n^s+x)^{g+2} = n^{-sg}·κ(x/n^s)/x` with

```text
κ(u) = u/(1+u)^{g+2} ,
```

the Mellin transform of the summand is `n^{sw}·M_κ(w)` and the Dirichlet sum is `ζ(sg - sw)`, which
converges for `Re w < g - 1/s`.  The kernel converges for `-1 < Re w < g+1`.  So the strip is

```text
-1 < Re w < g - 1/s ,
```

nonempty exactly when `g + 1 > 1/s` — which is the definition of `g = floor(1/s)` whenever `1/s` is
not an integer, precisely the hypothesis of `(4)`.

The kernel is again the sine kernel with a polynomial weight:

```text
M_κ(w) = B(w+1, g+1-w) = Γ(w+1)Γ(g+1-w)/Γ(g+2)
       = [ w ∏_{i=1}^{g} (i-w) ] · π/sin(πw) / (g+1)! .
```

So the machinery already built applies after two parameter generalisations:

1. the weight `(-w)^m` becomes an arbitrary polynomial in `w` (all estimates are polynomial-in-`|t|`
   and every residue is linear in the weight);
2. the zeta argument `-sw` becomes `a - sw` for a real constant `a = sg`, which moves the zeta pole
   from `w = -1/s` to `w = (a-1)/s`.

First brick: `HTGeometry/HalfLineBetaKernel.lean`,

    integral_halfLine_beta :
      **`∫_0^∞ y^{w-1}(1+y)^{-c} dy = Γ(w)Γ(c-w)/Γ(c)` on `0 < Re w < Re c`**

proved by the same `halfLineChart` change of variables that gave the reflection kernel, so the
`c = 1` case is recovered.

### First bricks of the genus route, built and wired

`GaloisForLFunctions/HTGeometry/HalfLineBetaKernel.lean` (wired into the umbrella, axiom-clean):

    integral_halfLine_beta :
      **`∫_0^∞ y^{w-1}(1+y)^{-c} dy = Γ(w)Γ(c-w)/Γ(c)`** on `0 < Re w < Re c`
    Gamma_natCast_add_one_sub :
      `Γ(g+1-w) = (∏_{i<g}(i+1-w))·Γ(1-w)` off the integers
    Gamma_add_one_mul_Gamma_natCast_sub :
      **`Γ(w+1)Γ(g+1-w) = [w ∏_{i<g}(i+1-w)] · π/sin(πw)`**

The first is the same `halfLineChart` change of variables that produced the reflection kernel, now
with a free exponent, so the `c = 1` case is recovered.  The second pair turns the genus-`g` Beta
kernel into the *same* sine kernel already carried through the whole contour argument, multiplied by
an explicit polynomial of degree `g+1` — and that polynomial vanishes at `w = 0,1,…,g`, exactly
cancelling the sine poles the Beta kernel does not have.  So the genus route reuses the existing
machinery verbatim once the weight is allowed to be a polynomial and the zeta argument is allowed
the shift `a - sw`.

## Lean progress — `(4)`–`(6)` ARE CLOSED AT EVERY GENUS

The genus branch `0 < s ≤ 1` no longer needs a second Mellin theory.  The right model factor is the
logarithmic derivative of the Weierstrass factor itself:

```text
D log E_g(-u) = (-1)^g · u^{g+1}/(1+u) ,
```

because `u/(1+u) + ∑_{j≤g} (-1)^j u^j = ∑_{j>g} (-1)^{j+1} u^j = (-1)^g u^{g+1}/(1+u)`.  So the
`E_g` subtractions are *inside* the model factor, and the sum `∑_n (-1)^g barnesModel g (x/n^s)`
converges with no regularization.  The Mellin transform of `t ↦ t^{g+1}/(1+t)` is the reflection
kernel translated by `g+1`,

```text
mellin (barnesModel g) w = (-1)^g · (-π / sin (π w)) ,   -(g+1) < Re w < -g ,
```

whose parity sign cancels the `(-1)^g` of the model.  Hence the summed integrand is **the same**

```text
F(w) = x^{-w} ζ(-s w) (-π / sin (π w))
```

as at genus zero, only on the strip `-(g+1) < σ < -g`, which is where the Dirichlet series converges
because `-1/s` lies in it exactly when `g = ⌊1/s⌋`.

    HTGeometry/BarnesKernelMellin.lean          barnesModel, its transform, vertical bounds
    RHTower/BarnesMellinGenusRepresentation.lean
      mellin_barnesModel_eq, mellinInv_mellin_barnesModel,
      norm_barnesModelInv_integrand_le, summable_integral_norm_barnesModelInv,
      hasSum_integral_barnesModelInv_scaled, tsum_barnesModelInv_eq,
      **hasSum_barnesModel_verticalIntegral'**
    RHTower/BarnesMellinNegResidues.lean, RHTower/BarnesMellinGenusExpansion.lean
      barnesIntResidue, verticalIntegral'_shift_int (crossing an arbitrary integer),
      genusAbscissa (the ladder `σ₀ = -((g+1)+1/s)/2`, `σ₁ = -(g+1/s)/2`, `σ_{k+2} = k-g+1/2`),
      verticalIntegral'_shift_genusZetaPole, verticalIntegral'_genus_shift_step,
      verticalIntegral'_genus_finite_expansion,
      **hasSum_barnes_genus_expansion**, **barnes_genus_poincare_expansion**

`GaloisForLFunctions/RHTower/BarnesMellinGenusEulerDerivative.lean` (wired, axiom-clean) closes the
derivative-compatible half:

    barnesGenusEulerSum s g            `x ↦ ∑_n (-1)^g barnesModel g (x/n^s)` — the Euler
                                       logarithmic derivative `H_s` at genus `g`
    barnesGenusEulerSum_eqOn           it is the contour integral at `σ₀`
    genusStart_zeta
    eulerIterate_barnesGenusEulerSum   **every Euler derivative `D^m H_s` is again a contour
                                       integral, with weight `(-w)^m`**
    barnes_genus_poincare_expansion_euler :
      **`(6)` at genus `g`** — for every `m` and `K`,
        `D^m H_s(x) + (-p_ζ)^m Res_ζ + ∑_{k<K} (-(k-g))^m Res_{k-g} = O(x^{-σ_{K+1}})`
      uniformly in `x > 0`, whenever `g < 1/s < g+1`

The Euler operator raises the weight independently of the abscissa, so the genus-zero
differentiation-under-the-integral machinery applies verbatim at the genus ladder.

### Status of the card after this session

| step | status |
|---|---|
| `(1)`, `(8)`–`(12)` exact Gevrey order `s` | formal |
| §4.1–4.4 DA transfer to the remainder | formal |
| `(14) ⟹ (15)` asymptotic-to-formal transfer | formal |
| §5 Newton-slope rationality obstruction | formal |
| **`(4)`–`(6)` for `s > 1` (genus `0`)** | **formal** |
| **`(4)`–`(6)` for every `s` with `1/s ∉ ℤ` (arbitrary genus)** | **formal** |
| §5 Sibuya--Ramis exact Newton-slope theorem | open — the single remaining item |

Every irrational `s > 0` has `1/s ∉ ℤ`, so the Barnes layer of the card is complete for the whole
irrational family.  Only the nonlinear exact-order theorem remains.

## Lean progress — the Gevrey filtration on formal series, and the exact statement of what is left

The card's §3 machinery works with coefficient *sequences*; §5 needs the same notion for formal
*series*, together with the ambient algebra in which a differential polynomial is evaluated.  Both
are now built.

`GaloisForLFunctions/HTGeometry/GevreyFormalSeries.lean` (wired, axiom-clean):

    exists_pow_le_const_mul_pow        every polynomial growth is beaten by every geometric one
    exists_succ_pow_le_const_mul_pow
    IsGevreySeries r F                 `‖aₙ‖ ≤ C Aⁿ (n!)^r`
    IsGevreySeries.mono                the filtration increases in `r`
    isGevreySeries_C
    IsGevreySeries.add
    IsGevreySeries.mul                 **Cauchy products stay in the class** — `i!·j! ∣ (i+j)!`
                                       collapses the two factorials and the antidiagonal
                                       contributes only the polynomial factor `n+1`
    IsGevreySeries.derivativeFun       **and so do formal derivatives**
    isGevreySeries_iff_isGevreyOfOrder the bridge to the coefficient-sequence notion of §3
    IsExactGevreySeriesOrder
    barnesTailSeries s                 **`R̂_s(t) = ∑_{k ≥ 1} (-1)^k ζ(-s k) t^k` as a formal
                                       series**
    norm_coeff_barnesTailSeries
    barnesTailSeries_isExactGevreySeriesOrder :
      **for every irrational `s > 0` the formal Barnes tail has exact Gevrey order `s`**

`GaloisForLFunctions/HTGeometry/FormalAnalyticADE.lean` (wired, axiom-clean):

    isGevreySeries_zero, isGevreySeries_one, IsGevreySeries.pow
    isGevreySeries_finsetSum, isGevreySeries_finsetProd
    IsGevreySeries.derivative, IsGevreySeries.iterate_derivative
    IsAnalyticDifferentialPolynomial   every coefficient is a convergent (Gevrey-`0`) series
    formalJetVector, IsFormalAnalyticADESolution
    isGevreySeries_aeval_of_analytic :
      **a differential polynomial with analytic coefficients does not leave the Gevrey class of its
      argument** — the elementary half of Maillet's circle of ideas
    SibuyaRamisRationalExactOrder      the exact-order theorem, as an explicit interface
    not_isFormalAnalyticADESolution_barnesTailSeries :
      **granted that interface, the irrational-power Barnes tail solves no analytic algebraic
      differential equation**

So the card's chain is now a single named implication:

```text
W_s DA  ⟹  R̂_s is a formal solution of an analytic ADE      (formal: §4 + (14)⟹(15))
R̂_s has exact Gevrey order s, irrational                     (formal: §3 + Barnes (4)–(6))
exact Gevrey order of such a solution is rational            (Sibuya--Ramis — OPEN)
```

### The Sibuya--Ramis layer, decomposed

What a proof needs, in order:

1. the Gevrey filtration as a differential algebra — **done**;
2. the linearized operator `L = ∑_j (∂P/∂y_j)(jets of F) ∂^j` along the formal solution, with
   coefficients in `ℂ[[t]]`;
3. the Newton polygon of such an operator: the shift polynomials
   `Φ_μ(N) = ∑_j (coeff_{μ+j} A_j)·[N]_j`, whose `(deg Φ_μ, μ)` are lattice points, so every slope
   ratio is rational — the arithmetic half is already formal
   (`NewtonSlopeRationality.not_lattice_slope_of_irrational`);
4. Maillet--Malgrange: the formal solution is Gevrey of order at most the largest slope ratio;
5. the sharp half: the exact order is one of the slope ratios, not merely below the largest.

Steps 4 and 5 are the mathlib-scale content.  Step 5 is the one the card actually contradicts, and
the reason step 4 alone does not suffice is recorded in the card's hostile audit: a series of exact
irrational order belongs to every larger rational Gevrey class, so an upper bound is compatible with
an irrational exact order.

## Lean progress — the Euler-form operator, its shift polynomials, and MAILLET'S THEOREM

The Sibuya--Ramis layer needs the recursion that a differential equation imposes on the coefficients
of a formal solution.  In the Euler basis that recursion is a single convolution.

`GaloisForLFunctions/HTGeometry/FormalEulerOperator.lean` (wired, axiom-clean):

    eulerOp                        `θ = t d/dt`, diagonal on monomials
    coeff_eulerOp_iterate          `coeff_n (θ^j F) = n^j coeff_n F`
    IsGevreySeries.eulerOp         `θ` preserves every Gevrey class
    eulerLinearOp B                `L = ∑_{j ≤ m} B_j θ^j`
    shiftPolynomial B μ            **`Φ_μ(N) = ∑_j (coeff_μ B_j) N^j`**
    eval_shiftPolynomial, natDegree_shiftPolynomial_le
    coeff_eulerLinearOp :
      **`coeff_n (L F) = ∑_{i+k=n} Φ_i(k) f_k`** — the operator acts by one convolution against its
      shift polynomials
    coeff_eulerLinearOp_range
    shiftPolynomial_zero_mul_coeff :
      **`Φ_0(n) f_n = coeff_n (L F) - ∑_{k<n} Φ_{n-k}(k) f_k`** — the recursion

The pairs `(deg Φ_μ, μ)` are lattice points, which is where the Newton polygon and the rationality of
its slopes live (`NewtonSlopeRationality` already owns the arithmetic half).

`GaloisForLFunctions/HTGeometry/ShiftPolynomialBounds.lean` (wired, axiom-clean):

    exists_lower_bound_eval_natCast :
      a nonzero complex polynomial is bounded below along `ℕ` by `c (n+1)^{deg}`
    exists_bound_shiftPolynomial :
      for convergent `B_j`, `‖Φ_μ(k)‖ ≤ C ρ^μ (k+1)^m` — geometric in the shift, polynomial in the
      argument

`GaloisForLFunctions/HTGeometry/MailletLinearGevrey.lean` (wired, axiom-clean):

    factorial_ratio_le             `k!/n! ≤ 1/n` for `k < n`
    cast_sub_le
    shiftFactor_le :
      **`(k+1)^m (k!/n!)^r ≤ (n+1)^d` for `k < n`, with `r = m - d`** — the exponent that makes the
      recursion close
    geom_shift_sum_le              `∑_{k<n} q^{n-k} ≤ q/(1-q)`
    isGevreySeries_of_eulerLinearOp_eq :
      **MAILLET'S THEOREM** — every formal solution of `L F = G` with convergent `B_j` and `G` is
      Gevrey of order `m - deg Φ_0`

The proof is exactly the recursion: divide by `Φ_0(n)`, whose modulus is at least `c (n+1)^{d}`;
each convolution term is geometric in the shift and, by `shiftFactor_le`, carries at most the factor
`(n+1)^d`; the geometric series is made small by choosing the Gevrey base `A` large.  Note the
resulting order is the *integer* `m - deg Φ_0`, the crude Newton bound obtained from
`deg Φ_μ ≤ m`; the refined polygon gives the smaller rational bounds.

### What the Sibuya--Ramis layer still needs

| step | status |
|---|---|
| Gevrey filtration as a differential algebra | formal |
| Euler-form operator, shift polynomials, coefficient recursion | formal |
| size of the shift polynomials, above and below | formal |
| **Maillet's theorem, linear case with convergent coefficients** | **formal** |
| Maillet's theorem, nonlinear case (linearize at a truncation of the solution) | open |
| the sharp half: the exact order is a slope ratio, not merely below the largest | open |

The last row is the one the card contradicts.  An upper bound alone is compatible with an irrational
exact order, so the sharp half is unavoidable.

## Lean progress — MAILLET IN NEWTON-POLYGON FORM

The crude Maillet bound `m - deg Φ_0` uses only `deg Φ_μ ≤ m`.  The polygon gives the sharp upper
bound, and its proof is shorter, because the factorial gain over a shift of `μ` steps is exactly the
power the polygon condition allows:

```text
k!/n! ≤ (k+1)^{-(n-k)}        (the n-k factors of n!/k! are all ≥ k+1),
```

so with `d = deg Φ_0` and the polygon condition `j ≤ d + r μ` on the coefficients present at shift
`μ ≥ 1`,

```text
(k+1)^{d + r(n-k)} · (k!/n!)^r ≤ (k+1)^{d} ≤ (n+1)^{d} .
```

Added to `ShiftPolynomialBounds.lean` and `MailletLinearGevrey.lean` (wired, axiom-clean):

    exists_bound_shiftPolynomial_newton   `‖Φ_μ(k)‖ ≤ C ρ^μ (k+1)^{d + r μ}` under the polygon
                                          condition
    pow_succ_mul_factorial_le_factorial   `(k+1)^{n-k} k! ≤ n!`
    factorial_ratio_pow_le
    shiftFactor_newton_le                 the displayed inequality
    isGevreySeries_of_eulerLinearOp_eq_newton :
      **Maillet in Newton form** — no slope ratio above `r` forces the formal solution to be Gevrey
      of order `r`
    isGevreySeries_zero_of_eulerLinearOp_eq :
      **no positive slope forces the formal solution to CONVERGE**

The last statement is the `r = 0` case and is the classical "regular singular ⟹ convergent formal
solutions" law.

This closes the sharp *upper* half of the Sibuya--Ramis programme for linear equations with
convergent coefficients.  What remains for the card is the nonlinear reduction and the sharp *lower*
half.

## Lean progress — the Maillet order is RATIONAL

The Newton bound that Maillet's theorem consumes has a least admissible value, and that value is a
maximum of finitely many ratios of integers: for each index `j` the condition `j ≤ d + r μ` is
hardest at the **smallest** shift `μ` at which `B_j` is present, and there are only `m+1` indices.

`GaloisForLFunctions/HTGeometry/NewtonBoundRational.lean` (wired, axiom-clean):

    NewtonBoundedBy B r                the Newton condition at level `r`
    newtonBoundedBy_natSub             the crude level `m - deg Φ_0` always works
    exists_rat_least_newtonBound :
      **the least admissible level is RATIONAL** (and it is a least element, not just a bound)
    exists_rat_isGevreySeries_of_eulerLinearOp_eq :
      **every formal solution of a linear analytic equation is Gevrey of a rational order**
    exactOrder_le_rat_of_eulerLinearOp_eq :
      **its exact Gevrey order is at most a rational number determined by the operator**

This is the arithmetic half of §5's obstruction, now attached to the analytic machinery rather than
to an abstract lattice: an irrational number is never the least Newton bound of an operator, and the
exact order of a solution is always bounded by such a rational.

What is still missing for the card is precisely that the exact order is **equal** to one of those
rationals rather than merely below the largest — the sharp half of Sibuya--Ramis — together with the
nonlinear reduction that produces a linear operator with convergent coefficients from the card's
algebraic differential equation.

## Lean progress — linearizing the nonlinear equation along a base point

The nonlinear equation reduces to the linear theory by Malgrange's truncation: linearize not at the
formal solution — whose jets are only formal — but at a **truncation** of it, whose jets are
polynomials and therefore convergent.

`GaloisForLFunctions/HTGeometry/EulerADELinearization.lean` (wired, axiom-clean):

    eulerJetVector F                   the `θ`-jets `(F, θF, …, θ^m F)`
    eulerOp_add, eulerOp_iterate_add, eulerJetVector_add
    IsFormalEulerADESolution P F       the equation in the Euler basis
    linearizationCoeff P Y j           `(∂_j P)(jets Y)`
    aeval_eulerJetVector_add :
      **`P(jets (Y+H)) = P(jets Y) + L_Y(H) + defect`**, with `L_Y = ∑_j (∂_j P)(jets Y) θ^j` the
      linearized operator in Euler form
    X_pow_dvd_eulerOp, X_pow_dvd_eulerOp_iterate
                                       `θ` preserves divisibility by a power of `t`
    taylorDefect_mem_sq_X_pow :
      **a perturbation divisible by `t^k` has defect divisible by `t^{2k}`**
    eulerLinearOp_linearization_eq :
      the equation around a base point, `L_Y(H) = -P(jets Y) - defect`

The Euler basis is what makes this work: `θ` preserves the order of a series, while `d/dt` lowers
it, so the perturbation and all of its jets stay divisible by the same power of `t`.  The corpus's
`MvPolynomialFirstOrderTaylor.taylorDefect_mem_sq` supplies the quadratic defect.

With `Y` a truncation of the solution at order `N`, `P(jets Y)` is convergent *and* divisible by
`t^{N+1}`, the coefficients of `L_Y` are convergent, and the defect is divisible by `t^{2N+2}`, so
its coefficient at level `n` involves only the perturbation below level `n - N`.  That is exactly
the shape the linear recursion consumes, and it is the remaining assembly step of the nonlinear
Maillet theorem.

## Lean progress — the truncation reduction

`GaloisForLFunctions/HTGeometry/EulerADETruncation.lean` (wired, axiom-clean) supplies the three
facts the nonlinear reduction needs, for a formal solution `F` truncated at order `N`:

    truncSeries N F, coeff_truncSeries
    isGevreySeries_zero_truncSeries        the truncation is convergent
    X_pow_dvd_sub_truncSeries              its tail is divisible by `t^{N+1}`
    isGevreySeries_eulerOp_iterate         Gevrey classes are `θ`-stable
    isGevreySeries_aeval_eulerJetVector    a differential polynomial does not leave the class
    isAnalyticDifferentialPolynomial_pderiv
    isGevreySeries_zero_linearizationCoeff :
      **the linearization at a truncation has CONVERGENT coefficients**
    isGevreySeries_zero_aeval_truncSeries :
      the value of the equation at the truncation is convergent
    X_pow_dvd_aeval_truncSeries :
      **and it is divisible by `t^{N+1}`** — because it equals minus the linearized term and the
      defect, both of which are

So for each `N` the solution's tail `H` satisfies

```text
L_N(H) = -P(jets F_N) - defect ,
```

with `L_N` a linear operator with convergent coefficients, `P(jets F_N)` convergent and of order
`≥ N+1`, and the defect of order `≥ 2N+2`, so that its coefficient at level `n` involves only `H`
below level `n - N`.  Every hypothesis of the linear Maillet theorem is available; what remains is
the induction that absorbs the defect, which is where the largeness of `N` is used.

## Lean progress — the Taylor defect, quantitatively

An ideal membership `defect ∈ J²` is enough to see that the defect is quadratic, but not to bound
it.  The defect now has an explicit representation.

`GaloisForLFunctions/HTGeometry/MvPolynomialQuadraticDefect.lean` (wired, axiom-clean):

    aeval_sumElim_rename_inl
    exists_taylorDefect_repr :
      **`defect = ∑_{a,b} L_a L_b · Q_{ab}(S, L)`** with `Q_{ab}` polynomials in the base point and
      the increment depending only on the differential polynomial

The induction is the same one that proves the ideal membership: the multiplication step
`defect(p·X_i) = (S_i + L_i)·defect(p) + L_i·∑_j ∂_j p(S) L_j` multiplies every entry by
`X_{inl i} + X_{inr i}` and creates the entries `∂_a p` in the column `b = i`.

With this representation a Gevrey bound on the defect is a Gevrey bound on a finite sum of products
of two increment jets with an evaluated polynomial, so it carries the **square** of the increment's
Gevrey constant — the gain the nonlinear recursion needs, once the increment's constant is at most
one, which the truncation order arranges.

## Lean progress — MAILLET'S THEOREM IN THE NONLINEAR CASE

The nonlinear reduction recorded above as "the remaining assembly step" is now a theorem.  Five new
modules, all wired and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

`GaloisForLFunctions/HTGeometry/GevreyWeightedNorm.lean`

    antidiagonal_inv_pow_le      `(n+1)^a ∑_{i+j=n} 1/((i+1)^a (j+1)^a) ≤ 2^{a+2}` for every `a ≥ 2`
    GevreyWeightBound w C A r F  `‖f_n‖ (n+1)^w ≤ C A^n (n!)^r`, integral order
    .mono_weight/.mono_const/.mono_base/.mono_order
    .eulerOp, .eulerOp_iterate   **`θ` costs exactly one unit of weight**
    .mul                         **submultiplicative at every exponent `a ≥ 2`**
    .isGevreySeries, exists_gevreyWeightBound
    factorial_mul_factorial_le_of_le, factorial_prod_le_of_dvd_order
    .mul_of_dvd :
      **a product of two series that both vanish to order `M` GAINS `M r` units of weight**, the
      binomial coefficient `((n+1)/2)^M / M!` separating the two factorials from the total one

`GaloisForLFunctions/HTGeometry/MvPolynomialTaylorFamily.lean`

    jetMonomial, jetDegree, jetDegree_eq_zero_iff, exists_jetDegree_pred
    HasTaylorDefectFamily A R₀ P
    hasTaylorDefectFamily :
      **`defect = ∑_α (coefficient in the base point alone) · L^α`, every `α` of degree ≥ 2**, with
      all coefficients in any subsemiring `R₀` containing those of `P`

The subsemiring clause is what makes the coefficients of the family convergent, and it is why the
induction runs along `P = ∑ monomial` (via `MvPolynomial.as_sum`) rather than along an arbitrary
decomposition into a sum: the hypothesis "all coefficients lie in `R₀`" is not inherited by the
summands of an arbitrary splitting, but it is inherited by monomials.

`GaloisForLFunctions/HTGeometry/GevreyJetMonomial.lean`

    gevreyWeightBound_jetMonomial      a monomial of degree `d` in factors of size `ε` has size `ε^d`
    X_pow_dvd_jetMonomial, X_pow_dvd_jetMonomial_sub
    X_pow_dvd_jetMonomial_sub_of_two_le :
      **replacing the perturbation by a truncation moves a monomial of degree ≥ 2 only above the
      truncation level plus the vanishing order**
    gevreyWeightBound_jetMonomial_dvd :
      **a monomial of degree ≥ 2 in factors vanishing to order `M` gains `M r` units of weight**
    GevreyWeightBound.finsetSum, exists_common_gevreyWeightBound

`GaloisForLFunctions/HTGeometry/NonlinearMailletAux.lean`

    convergentSubsemiring              the convergent series as a subsemiring of `ℂ⟦t⟧`
    shiftFactor_nat_le                 the shift factor at every integral exponent above the drop
    polyGeom_shift_sum_le              a geometric sum survives a polynomial weight
    gevreyWeightBound_truncSeries, X_pow_dvd_truncSeries, eulerOp_iterate_sub
    coeff_taylorDefect_eq_of_sub_dvd :
      **the defect at level `n` only sees the perturbation below level `n`** — so the nonlinear
      recursion is still a recursion

`GaloisForLFunctions/HTGeometry/NonlinearMailletGevrey.lean`

    exists_isGevreySeries_of_isFormalEulerADESolution :
      **MAILLET'S THEOREM, NONLINEAR CASE** — a formal solution of an analytic algebraic
      differential equation `P(t, θF, …, θ^m F) = 0` whose linearization along the truncation at
      order `N ≥ m − 1` has a nonzero indicial polynomial is Gevrey of a finite INTEGRAL order

The estimate is the weighted recursion `‖h_n‖ (n+1)^{m+2} ≤ ε A^n (n!)^r`, `r = max(m − deg Φ_0, 1)`,
for `H = F − trunc_N F`.  Three features make it close.

* Each `θ^j` costs one unit of weight, so the jets of `H` still carry weight `2`.
* A monomial of degree ≥ 2 in series vanishing to order `N+1` gains `(N+1) r` units of weight, and
  `N + 1 ≥ m` restores exactly what the jets cost.  This is the quantitative form of "the defect is
  quadratic", and it is where the largeness of the truncation order is used.
* The defect at level `n` involves only `H` below level `n`, so the strong induction is legitimate.

The size `ε` of the induction is chosen so small that the defect — quadratic in it — is dominated by
the indicial lower bound, and only then is the geometric base `A` chosen large enough for the
convolution, the value at the truncation, and the finitely many initial coefficients.  Both choices
are made in that order because the defect constant is independent of `A`.

### What is left of the Sibuya--Ramis layer

| step | status |
|---|---|
| Gevrey filtration as a differential algebra | formal |
| Euler-form operator, shift polynomials, coefficient recursion | formal |
| Maillet, linear case, crude and Newton forms | formal |
| the Maillet order is rational | formal |
| linearization at a truncation, quadratic defect, locality | formal |
| **Maillet, nonlinear case, with a nondegenerate indicial polynomial** | **formal** |
| the nondegeneracy hypothesis, discharged by a minimal annihilator | open |
| the sharp half: the exact order is a slope ratio, not merely below the largest | open |

The nondegeneracy hypothesis is not vacuous and is not automatic: the indicial polynomial of the
linearization can vanish, and the classical remedy is to divide the operator by the largest power of
`t` dividing it.  That divides the whole equation by `t^v`, which costs `A^v` in the defect estimate
and is repaid by the vanishing order `N+1−v` of the value at the truncation — solvable exactly when
`N + 1 > 2v`, hence for a large enough truncation, since `v` stabilises once `N` exceeds the order of
vanishing of the linearization along the solution itself.

## Lean progress — MAILLET'S NONLINEAR THEOREM IS NOW UNCONDITIONAL

The nondegeneracy hypothesis recorded above as the remaining obstruction of the nonlinear layer is
discharged.  Two further modules, both wired and axiom-clean.

`GaloisForLFunctions/HTGeometry/NonlinearMailletShift.lean`

    factorial_add_le, factorial_add_rpow_le      `(n+v)! ≤ n!·((v+1)(n+1))^v`
    exists_isGevreySeries_of_isFormalEulerADESolution_shift :
      **the estimate at an arbitrary leading shift `v`** — if the linearization along the
      truncation at order `N` vanishes to order `v` and `m + 2v ≤ N`, the solution is Gevrey of a
      finite integral order

The indicial polynomial of the linearization may vanish; what cannot vanish is the shift polynomial
at the order `v` to which the linearization vanishes, and the recursion is then the same recursion
read `v` levels higher.  Three costs appear and are each paid: the convolution weights gain the
fixed factor `ρ^v`; the value at the truncation is read at level `n+v` and so loses `A^v`, repaid by
the order `N+1−v` to which it vanishes (this is where `N + 1 > 2v` enters); and the defect loses
`((n+v)!/n!)^r ≤ ((v+1)(n+1))^{vr}`, which is exactly the slack the truncation order supplies.
Because the induction size `ε` must absorb `A^v` it is now defined **after** the geometric base,
as `ε = c/(3(K+1)(c+1)A^v)`, and every constraint on `A` is then free of `ε`.

`GaloisForLFunctions/HTGeometry/NonlinearMailletUnconditional.lean`

    coeff_shiftPolynomial, shiftPolynomial_ne_zero_of_coeff
    aeval_add_sub_mem                 perturbing the point moves the value inside the ideal
    coeff_aeval_eulerJetVector_truncPowerSeries_eq :
      the linearization along the truncation at order `N` agrees with the linearization along the
      solution itself up to level `N`
    totalDegree_pderiv_lt, eq_C_of_forall_pderiv_eq_zero
    exists_nondegenerate_annihilator :
      **a nonzero annihilator of least total degree has a partial derivative that does not
      annihilate**
    exists_isGevreySeries_of_annihilator :
      **MAILLET'S THEOREM, NONLINEAR CASE, UNCONDITIONALLY** — every formal power series
      annihilated by a nonzero algebraic differential polynomial with convergent coefficients is
      Gevrey of a finite integral order

The selection is the classical one: among the nonzero annihilators take one of least total degree;
a polynomial all of whose partial derivatives vanish is a constant, and a constant annihilator is
zero, so some partial derivative is nonzero; it has strictly smaller total degree, hence by
minimality does not annihilate.  Its order of vanishing `v` along the solution is finite, and
taking the truncation order `N = m + 2v` meets both requirements of the shifted estimate, because
the linearization along the truncation agrees with the linearization along the solution up to
level `N`.

### The single remaining item

| step | status |
|---|---|
| everything else on this card | formal |
| **the sharp half of Sibuya--Ramis** | open |

The sharp half is *not* reachable by the scalar recursion.  Writing `u_n = f_n/(A^n (n!)^s)`, the
irrationality of `s` does give a **unique** dominant shift `μ*` — the exponents
`e_μ = deg Φ_μ − deg Φ_0 − s μ` are pairwise distinct because `s` is irrational — and the recursion
then bounds `u_{n−μ*}` by `n^{−e*}` times the neighbouring values.  But solving the recursion for
`f_{n−μ*}` expresses it through `f` at indices **above** `n−μ*` as well as below, so the estimate is
not an induction, and bounding those higher indices by the a priori Gevrey bound of order `s` is
too lossy by a factor `(n!)^δ`.  Decoupling the high part is exactly what the Newton--Ramis
factorization `L = M ∘ N` in `ℂ{t}[θ]` does, and that factorization is therefore the remaining
construction.  In the shift-polynomial presentation the ring law is
`(t^a Ψ(θ))·(t^b Φ(θ)) = t^{a+b} Ψ(θ+b) Φ(θ)`, so the factorization is a Hensel-type recursion in
the shift with a majorant convergence proof.

## Lean progress — the operator ring, and the irrational leading vertex

The remaining item is the sharp half of Sibuya--Ramis, whose classical proof factors the operator
along its Newton polygon.  The ring in which that factorization lives, and the arithmetic that makes
an **irrational** level non-degenerate, are now formal.  Four new modules, all wired and axiom-clean.

`GaloisForLFunctions/HTGeometry/EulerShiftOperatorAlgebra.lean`

    shiftOp Φ                     the operator of a family of shift polynomials,
                                  `coeff_n (L F) = ∑_{k ≤ n} Φ_{n-k}(k) f_k`
    shiftOp_shiftPolynomial       it agrees with the `∑_j B_j θ^j` presentation
    shiftComp Ψ Φ                 `(Ψ ⋆ Φ)_ν = ∑_{a+b=ν} Ψ_a(X + b) · Φ_b(X)`
    shiftOp_shiftComp :           **the convolution IS composition of operators**
    natDegree_shiftComp_le
    IsBoundedShiftFamily m Φ      `‖Φ_μ(k)‖ ≤ C ρ^μ (k+1)^m`, the estimate a convergent operator
                                  supplies
    isBoundedShiftFamily_shiftPolynomial
    isBoundedShiftFamily_shiftComp :
      **boundedness is stable under composition**, with the orders adding
    coeff_shiftPolynomial, shiftPolynomial_ne_zero_of_coeff

The composition law is the commutation `θ ∘ t^b = t^b ∘ (θ + b)` read on coefficients; the proof is
the triangular sum swap `∑_{k ≤ n} ∑_{j ≤ k} = ∑_{j ≤ n} ∑_{k ∈ [j, n]}` followed by `k = j + b`.

`GaloisForLFunctions/HTGeometry/NewtonIrrationalLevelVertex.lean`

    weightedLevel r Φ μ = deg Φ_μ − r μ
    weightedLevel_injective_of_irrational :
      **at an irrational level distinct shifts have distinct weights** — equality exhibits `r` as a
      quotient of integers
    exists_max_weightedLevel      the maximum is attained: degrees are bounded, so only finitely
                                  many shifts can compete
    exists_gap_weightedLevel      and on any finite window the leading shift has a uniform positive
                                  advantage

`GaloisForLFunctions/HTGeometry/NewtonLevelComposition.lean`

    natDegree_comp_X_add_C, leadingCoeff_comp_X_add_C, comp_X_add_C_ne_zero
    natDegree_shiftComp_le_of_bound
    coeff_shiftComp_leading :
      **the leading vertex of a composition is the sum of the leading vertices**, with leading
      coefficient the product of the two — at an irrational level no other pair of monomials can
      reach the same shift and degree, so there is nothing to cancel it
    shiftComp_leading_ne_zero, natDegree_shiftComp_leading

`GaloisForLFunctions/HTGeometry/NewtonIrrationalPositiveVertex.lean`

    newtonBoundedBy_iff_weightedLevel_le :
      the Newton condition at level `r` is exactly `λ_r(μ) ≤ λ_r(0)`
    exists_positive_weightedLevel_of_irrational_exactOrder :
      **an irrational exact Gevrey order forces the leading vertex to a positive shift**

The last statement halves the remaining problem.  If the leading vertex sat at shift `0`, the
Newton condition would hold at level `s`, the least admissible level would be a **rational** `q ≤ s`,
hence `q < s` because `s` is irrational, and Maillet's theorem at `q` would make the solution Gevrey
of order `q < s` — contradicting exactness.  So the only surviving configuration is the one in which
the polygon genuinely has a slope above `s`, and that is precisely the configuration a factorization
`L = M ∘ N` at the cut `s` is designed to split.

### The single remaining construction

`L = M ∘ N` at an irrational cut `s`, with `N` Newton-bounded at level `s` and every slope of `M`
above `s`.  Given it, the chain closes: `U := N F` lies in `E_s` because `N` is convergent, solves
`M U = G` with `G` convergent, so by induction on the number of slopes `gev(U) = 0`; then `N F` is
convergent and Maillet at the least Newton level of `N` — a rational number below `s` — makes `F`
Gevrey of an order strictly below its exact one.  The ring, its estimates, and the multiplicativity
of leading vertices that the construction must respect are now all formal.

## Lean progress — THE LINEAR HALF OF SIBUYA--RAMIS IS PROVED FOR THIS SOLUTION

The card's remaining item was the sharp half of Sibuya--Ramis, whose classical proof factors the
operator along its Newton polygon.  For **this** solution the factorization can be bypassed: the
Barnes tail has a two-sided *regular profile*, and against such a profile the leading Newton vertex
of a convergent operator dominates the whole rest of the coefficient recursion directly.

`GaloisForLFunctions/HTGeometry/BarnesTailLinearObstruction.lean` (wired, axiom-clean):

    not_eulerLinearOp_barnesTail_eq :
      **for every irrational `s > 0`, every nonzero convergent operator `L = ∑_j B_j θ^j` and every
      convergent `G`, the Barnes tail is not a formal solution of `L F = G`**

The estimate that makes it work is new infrastructure, all axiom-clean and wired:

`RegularFactorialProfile.lean`

    IsRegularFactorialProfile s c₁ c₂ Θ    one-step ratio comparable to `(k+1)^s`
    block_lower, block_upper               `Θ a c₁^{b−a} (b!/a!)^s ≤ Θ b ≤ Θ a c₂^{b−a} (b!/a!)^s`
    const_mul
    isRegularFactorialProfile_gammaProfile(_of_irrational) :
      `Γ(1+sk) β^k` is one, with explicit constants `β(s+1−M)^s`, `β(1+M+s)^s` for any natural `M`
      with `s < M < s+1` — the ceiling, when `s` is irrational

`FactorialProfileShiftRatio.lean`

    pow_le_factorial_div, factorial_div_le_pow
    shift_above_factorial / shift_above_pow, shift_below_factorial / shift_below_pow
      the profile ratio across a shift, in both the power and the factorial form

`ShiftPolynomialDegreeBound.lean`

    exists_bound_shiftPolynomial_natDegree :
      `‖Φ_μ(k)‖ ≤ C ρ^μ (k+1)^{deg Φ_μ}` — the degree-sensitive bound a weighted level needs

`NewtonIrrationalUniformGap.lean`

    exists_uniform_weightedLevel_gap :
      the leading vertex beats every other shift by a **uniform** margin `γ`, because
      `λ_s(μ) ≤ m − s μ → −∞` leaves only finitely many competitors

`ShiftTermPowerBound.lean`, `ShiftTermFactorialBound.lean`, `ShiftTermUnifiedBound.lean`

    shiftTerm_le_of_lt, shiftTerm_le_of_gt, shiftTerm_le_factorial, shiftTerm_le_unified

`ShiftSumLimits.lean`, `ShiftSumDominance.lean`

    tendsto_halfFactorial_ratio_mul, geomSum_le_two
    tendsto_shiftTail_div_leading :
      **the whole tail of the recursion is negligible against the leading shift**

### The mechanism

Both the below- and above-shift comparisons produce the same exponent `λ_s(μ) + sν`, so dividing by
`(n+1)^{deg Φ_ν} Θ(n−ν)` leaves exactly the difference of weighted levels.  Two effects then have to
be separated.

* While `2μ ≤ n` the power form applies, and the uniform gap `γ` combines with the crude bound
  `λ_s(μ) − λ_s(ν) ≤ m − s(μ−ν)` in a **convex combination** with weight `ε = γ/(2(m+γ))`:
  `λ_s(μ) − λ_s(ν) ≤ −γ/2 − ε s (μ−ν)`.  One exponent supplies both the decay in `n` and the
  summability in `μ`, so no separate treatment of small and large shifts is needed.
* Past the halfway point the power form is empty — `n − μ + 1` is bounded — and the factorial form
  takes over: every index above `⌊n/2⌋` contributes to `(n−ν)!/(n−μ)!`, so the whole range is
  controlled by the single `μ`-independent quantity `(⌊n/2⌋)!/(n−ν)!`, which is super-exponentially
  small and absorbs both the geometric factors and the number of terms.

### What remains

Only the **nonlinear** reduction.  Writing an analytic differential polynomial as
`P = c + ∑_j b_j y_j + Q` with `Q` of total degree `≥ 2` gives the exact identity
`eulerLinearOp b F = −c − Q(jets F)` with `b_j` convergent, so the recursion above applies verbatim
once `Q(jets F)` is shown negligible against the leading vertex of the linear part.  That needs a
convolution estimate for the profile — `∑_{i+j=n, i,j ≥ 1} Θ(i)Θ(j) = O(n^{-s} Θ(n))` and its
`d`-fold form — and, in the degenerate case where the linear part is too small, the Newton polygon of
the nonlinear equation itself.

## Lean progress — the convolution estimate for the nonlinear reduction

`GaloisForLFunctions/HTGeometry/GammaConvolutionBound.lean` (wired, axiom-clean):

    gammaPair_le_endpoint :
      **on any block `[p, n−p]` the pair product `Γ(1+si)Γ(1+s(n−i))` is largest at the ends** —
      log-convexity of `Γ`, applied to the two Hölder splittings `i = αp + β(n−p)` and
      `n−i = βp + α(n−p)`, whose exponents add to `1` in each factor
    exists_gammaConvolution_bound :
      `∑_{i=1}^{n−1} Γ(1+si)Γ(1+s(n−i)) ≤ K · Γ(1+s)Γ(1+s(n−1))` eventually
    exists_gammaProfile_convolution_bound :
      the same for the full profile `Γ(1+sk)β^k`, the geometric factor cancelling

The mechanism: the endpoint bound at depth `1` controls the `p−1` terms at each end; at a fixed
depth `p` with `s(p−1) ≥ 2` it controls the whole middle block by `Γ(1+sp)Γ(1+s(n−p))`, which the
shift bound `Γ(1+s(n−p))/Γ(1+s(n−1)) ≤ (1+s(n−1)−M)^{−s(p−1)}` makes smaller than the first term by
a factor beating the number of terms.  All thresholds are explicit — `p = ⌈2/s⌉ + 2`,
`M = ⌈s(p−1)⌉ + 1`, and an explicit `N` — so the statement is an unconditional eventual bound with
constant `2p + 1`.

An abstract `IsRegularFactorialProfile` is **not** enough for this estimate: a profile whose
one-step ratio oscillates between `c₁(k+1)^s` and `c₂(k+1)^s` can make
`Θ(n/2)²/Θ(n)` as large as `(c₂/c₁)^{n/2}`, which beats the binomial gain when `c₂/c₁ > 4^s`.  The
estimate is genuinely a property of `Γ`, and that is why it is proved here directly from
log-convexity rather than from the abstract profile axioms.

## Lean progress — the nonlinear reduction is NOT blocked: linearize at a truncation

An earlier note on this card recorded a degeneracy obstruction to the nonlinear step.  That
obstruction is an artefact of linearizing at `t = 0`, and it disappears when one linearizes at a
**truncation**, which is exactly what the corpus's Maillet development already does.

Write `Y = truncPowerSeries N F` and `H = F − Y`.  Then `eulerLinearOp_linearization_eq` gives the
exact identity

```text
eulerLinearOp (linearizationCoeff P Y) H = −aeval (jets Y) P − taylorDefect (jets Y) (jets H) P ,
```

in which

* `linearizationCoeff P Y` is **convergent** (`isGevreySeries_zero_linearizationCoeff`) — it is a
  polynomial expression in a polynomial, not in the formal solution;
* `aeval (jets Y) P` is **convergent** (`isGevreySeries_zero_aeval_truncPowerSeries`);
* `H` vanishes below order `N+1` and has the same profile as `F` above it;
* `taylorDefect` is, by `hasTaylorDefectFamily`, a finite sum `∑_α aeval (jets Y) (T α) ·
  jetMonomialValue (jets H) α` with `jetDegree α ≥ 2`, i.e. a sum of monomials of degree **at least
  two** in the tail.

So every defect term is a Cauchy product of factors that all vanish below order `N+1`, and the
endpoint bound at depth `N+1` collapses each such convolution to `Θ(N+1)·Θ(n−N−1)` times the number
of terms.  Since `Θ(n−N−1)/Θ(n−ν) ≍ n^{−s(N+1−ν)}`, the defect can be made smaller than the leading
Newton term `n^{deg Φ_ν} Θ(n−ν)` **by choosing `N` large** — the truncation order is ours to pick,
and the shift polynomials at shifts `≤ N₀` do not change when `N` grows past `N₀`, so a
non-degeneracy established once persists.

`GaloisForLFunctions/HTGeometry/GammaProfileProduct.lean` (wired, axiom-clean) supplies the two
quantitative ingredients:

    gammaProfilePair_le_endpoint      the endpoint bound on the full profile
    gammaProfile_zero, gammaProfile_mul_le
                                      **submultiplicativity** `Θ(i)Θ(j) ≤ Θ(i+j)`, the depth-`0`
                                      case, which lets a `d`-fold monomial stay profile-bounded
    norm_coeff_mul_le_of_vanishing    two factors vanishing below order `N+1` convolve into
                                      `(n+1)·c_A c_B·Θ(N+1)Θ(n−N−1)`

What is left for the card is assembly: iterate `gammaProfile_mul_le` along `jetMonomialValue` to
bound a monomial of degree `d ≥ 2`, apply `norm_coeff_mul_le_of_vanishing` at the top level for the
`Θ(n−N−1)` gain, and feed the result into `false_of_dominant_transfer` alongside
`tendsto_shiftTail_div_leading`.

## Lean progress — the Taylor-defect bound

`GaloisForLFunctions/HTGeometry/ProfileBoundedSeries.lean` (wired, axiom-clean):

    HasProfileBound s β A          `‖a_k‖ ≤ c (k+1)^a Θ(k)` for some constants
    HasProfileBound.add / .mul / .pow
      the class is closed under sums, Cauchy products and powers.  The polynomial correction is what
      makes the product step work: submultiplicativity `Θ(i)Θ(j) ≤ Θ(i+j)` handles the profile
      factors, `(i+1)^a (j+1)^b ≤ (n+1)^{a+b}` the polynomial ones, and the term count contributes
      the last power
    jetMonomialValue_single_pow, HasProfileBound.jetMonomialValue
      closure under jet monomials, by `Finsupp.induction`
    norm_coeff_mul_le_of_vanishing_poly
      the two-tail convolution bound, with the polynomial correction
    norm_coeff_jetMonomialValue_le_of_two_le :
      **a jet monomial of degree at least two in a tail vanishing below order `N+1` satisfies**
      `‖coeff n‖ ≤ c (n+1)^a Θ(N+1) Θ(n−N−1)`

The proof of the last one splits `α = single i 1 + γ` at any `i` in the support — via
`Finsupp.single_add_erase` — so that `jetDegree γ = jetDegree α − 1 ≥ 1` and the corpus's
`X_pow_dvd_jetMonomialValue` makes `jetMonomialValue L γ` vanish below `N+1` as well; the two-tail
bound then applies to `L i · jetMonomialValue L γ`.

Since `hasTaylorDefectFamily` writes `taylorDefect (jets Y) (jets H) P` as a **finite** sum
`∑_α aeval (jets Y) (T α) · jetMonomialValue (jets H) α` with `jetDegree α ≥ 2`, and each
`aeval (jets Y) (T α)` is convergent hence profile bounded, this bounds the whole defect by
`c (n+1)^a Θ(N+1) Θ(n−N−1)` — smaller than the leading Newton term `n^{deg Φ_ν} Θ(n−ν)` once `N` is
large, because `Θ(n−N−1)/Θ(n−ν) ≍ n^{−s(N+1−ν)}`.

Remaining for the card: assemble — sum the defect bound over the (finite) family support, verify the
profile hypotheses for the tail `H = F − truncPowerSeries N F`, and feed the result into
`false_of_dominant_transfer` alongside `tendsto_shiftTail_div_leading`.

## Lean progress — THE TAYLOR DEFECT AT A TRUNCATION IS BOUNDED

`GaloisForLFunctions/HTGeometry/ProfileBoundedSeries.lean` (extended) and
`GaloisForLFunctions/HTGeometry/TaylorDefectProfileBound.lean` (new), both wired and axiom-clean:

    exists_pow_le_const_mul_factorial, exists_pow_le_const_mul_factorial_rpow
      `M^k ≤ c (k!)^s` — the factorial beats every geometric growth, at every positive exponent
    hasProfileBound_of_isGevreySeries_zero :
      **every convergent series is profile bounded**, because the block bound gives
      `Θ(k) ≥ c₁^k (k!)^s` and the previous lemma absorbs the geometric ratio
    norm_coeff_mul_jetMonomialValue_le_of_two_le :
      a profile-bounded multiple of a jet monomial of degree `≥ 2` in a tail vanishing below `N+1`
      obeys `‖coeff n‖ ≤ c (n+1)^a Θ(N+1) Θ(n−N−1)`
    exists_norm_coeff_taylorDefect_le :
      **the whole Taylor defect obeys that bound** — `hasTaylorDefectFamily` at the *convergent*
      subsemiring writes it as a finite sum `∑_α aeval (jets Y) (T α) · jetMonomialValue (jets H) α`
      with `jetDegree α ≥ 2` and every `T α` carrying convergent coefficients, so every summand is a
      convergent series times such a monomial; the exponents are merged by
      `T.support.sup` and the constants by summation over the finite support

This is the last analytic ingredient of the nonlinear reduction.  With `Y = truncPowerSeries N F` and
`H = F − Y`, the identity `eulerLinearOp_linearization_eq` now has all three of its pieces
quantified: the operator is convergent, the right-hand side `aeval (jets Y) P` is convergent, and the
defect is `O((n+1)^a Θ(N+1) Θ(n−N−1))` — smaller than the leading Newton term `n^{deg Φ_ν} Θ(n−ν)`
once `N` is chosen with `s(N+1−ν)` above the fixed exponent, which is free.

Remaining for the card: instantiate — `H` inherits the two-sided profile of `F` (upper bound
everywhere, lower bound on the infinite realising set minus its finitely many indices `≤ N`), the
jets of `H` are divisible by `X^{N+1}` by `X_pow_dvd_sub_truncPowerSeries` and
`X_pow_dvd_formalEulerOp_iterate`, the non-degeneracy of `shiftPolynomial (linearizationCoeff P Y)`
comes from the corpus's `exists_nondegenerate_annihilator`, and the contradiction is
`false_of_dominant_transfer` together with `tendsto_shiftTail_div_leading`.

## Lean progress — §5 IS CLOSED, BY BYPASSING SIBUYA–RAMIS ENTIRELY

The single remaining item recorded above — the sharp half of Sibuya–Ramis, i.e. the Newton–Ramis
factorization `L = M ∘ N` at an irrational cut — is **no longer needed**.  What §5 was used for is
the single implication

> the Barnes tail `R̂_s` cannot be a formal solution of an analytic algebraic ODE,

and that implication is now a theorem, proved directly from the two-sided profile of `R̂_s` rather
than from the exact-order theorem.  The sharp half of Sibuya–Ramis is a statement about *every*
divergent solution of *every* analytic ODE; the card only ever needed it for one series whose
coefficients are known on both sides, and for such a series the leading-vertex comparison closes by
itself.

Three new modules, all wired into `HTGeometry.lean`, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

`GaloisForLFunctions/HTGeometry/TaylorDefectUniformExponent.lean`

    HasProfileBoundExp s β a A            a profile bound with a NAMED polynomial exponent
    HasProfileBoundExp.mono/.mul/.pow/.jetMonomialValue
                                          the exponent arithmetic: a product costs `a+b+1`, a jet
                                          monomial costs `|α|(a+2)`
    hasProfileBoundExp_zero_of_isGevreySeries_zero :
      a convergent series is dominated by the profile with **no** polynomial factor at all
    norm_coeff_mul_jetMonomialValue_le_exp
    exists_uniform_norm_coeff_taylorDefect_le :
      **the defect exponent is chosen BEFORE the truncation order** — `∃ A, ∀ N Y H, …` — because
      the Taylor family presenting the defect is attached to the equation alone, the coefficients
      evaluated at the base point are convergent (exponent `0`), and the jets of the tail carry an
      exponent supplied in advance.  This ordering of the quantifiers is the whole point: the gain
      `Θ(n−N−1)/Θ(n−ν) ≍ n^{−s(N+1−ν)}` beats `n^A` only if `A` is fixed first.

`GaloisForLFunctions/HTGeometry/ProfileRatioLimits.lean`

    tendsto_convergent_div_leading        a convergent right-hand side is negligible against
                                          `(n+1)^{deg Φ_ν} Θ(n−ν)`
    tendsto_shiftedProfile_div_leading :
      **the shifted profile is negligible too**, as soon as `A < deg Φ_ν + s(N+1−ν)`; the proof is
      `shift_above_pow` plus `(n−N)+1 ≥ (n+1)/2` past the halfway point

`GaloisForLFunctions/HTGeometry/BarnesTailNonlinearObstruction.lean`

    norm_coeff_barnesTail_sub_truncPowerSeries_le, coeff_barnesTail_sub_truncPowerSeries_of_lt
    hasProfileBoundExp_eulerJetVector_barnesTail_tail :
      the jets of the tail are profile bounded with exponent `m`, uniformly in `N`
    not_isFormalEulerADESolution_barnesTail_of_nondegenerate :
      the obstruction, for an equation whose linearization along `R̂_s` is nonzero
    **not_isFormalEulerADESolution_barnesTail** :
      `∀ P ≠ 0 analytic, ¬ IsFormalEulerADESolution P (barnesTailSeries s)` for every irrational
      `s > 0` — **the Barnes tail is hypertranscendental**

### Why the reduction is unconditional

Writing `F = Y + H` with `Y = truncPowerSeries N F`, the equation becomes
`L_Y H = −P(Y) − defect` with `L_Y` and `P(Y)` convergent.  Three facts close it.

1. **The defect exponent does not move with `N`** (`exists_uniform_norm_coeff_taylorDefect_le`).
2. **The leading vertex does not move with `N`**: `coeff_aeval_eulerJetVector_truncPowerSeries_eq`
   makes `shiftPolynomial (linearizationCoeff Q Y) μ = shiftPolynomial Bf μ` for `μ ≤ N`, where
   `Bf` is the linearization along the solution itself; so `Φ_v ≠ 0` at the fixed shift `v` of `Bf`,
   and maximality of the weighted level forces `ν ≤ ⌈m/s⌉ + v` — a ceiling free of `N`.
3. **The truncation order is free**: taking `N = ⌈m/s⌉ + v + ⌈A/s⌉ + 1` makes
   `A < deg Φ_ν + s(N+1−ν)`, so the defect loses to the leading Newton term.

The nondegeneracy hypothesis is discharged by the corpus's `exists_nondegenerate_annihilator`
(minimal total degree), exactly as in the unconditional nonlinear Maillet theorem.

### Ruled out, and no longer needed

The Newton–Ramis factorization `L = M ∘ N` at an irrational cut is not required for this card.  It
remains the right construction for the general sharp Sibuya–Ramis statement, and the operator ring
built for it (`EulerShiftOperatorAlgebra`, `NewtonLevelComposition`) stands; but the card's own
chain no longer passes through it.

### Status

| step | status |
|---|---|
| `(1)`, `(4)`–`(6)`, `(8)`–`(12)` | formal |
| §4.1–4.4 DA transfer to the remainder | formal (`BarnesRemainderDATransfer`) |
| `(14) ⟹ (15)` asymptotic-to-formal | formal (`AsymptoticExpansionAlgebra`) |
| §5 obstruction on `R̂_s` | **formal (`BarnesTailNonlinearObstruction`)** |
| end-to-end statement `W_s` is not DA | assembly of the four rows above |

## Lean progress — THE ANALYTIC CHAIN IS CLOSED: THE BARNES REMAINDER IS HYPERTRANSCENDENTAL

The three rows of the previous status table are now joined into one theorem.  Three new modules,
wired, axiom-clean.

`GaloisForLFunctions/RHTower/BarnesTailAsymptoticExpansion.lean`

    barnesEulerRemainder s m x     `D^m (x W_s'/W_s)` with the leading power, the ascending
                                   polynomial part and the constant removed
    barnesEulerJet s m t           the same read in `t = 1/x`, with the sign that turns `x d/dx`
                                   into `t d/dt`
    neg_barnesIntResidue_succ      at a positive integer the crossed residue IS the term
                                   `(-k)^m b_k x^{-k}` of the tail
    barnesEulerRemainder_expansion the descending expansion with error `O(x^{-(J+1/2)})` after `J`
                                   terms
    isAsymptoticExpansion_barnesEulerJet :
      **`(6)` in Poincaré form** — the `m`-th Euler jet of the Barnes remainder has the `m`-th
      Euler jet of `R̂_s` as its expansion at `0⁺`.  The half-integer of room in the contour ladder
      is exactly what lets the error after one extra term absorb that term.

`GaloisForLFunctions/HTGeometry/AsymptoticPolynomialCoefficients.lean`

    isAsymptoticExpansion_pow, isAsymptoticExpansion_polynomial :
      a polynomial coefficient is its own expansion
    IsAsymptoticExpansion.congr                  the notion only sees the germ at `0⁺`
    isAsymptoticExpansion_eval₂_polyCoeff        a relation with `ℂ[t]` coefficients has the formal
                                                 relation as its expansion
    eval₂_powerSeries_eq_zero_of_eventually      **`(14) ⟹ (15)` with polynomial coefficients**
    isGevreySeries_zero_polynomial, isAnalyticDifferentialPolynomial_map_coe, map_coe_ne_zero :
      the transferred relation is analytic and stays nonzero, because `ℂ[t] → ℂ⟦t⟧` is injective
    isFormalEulerADESolution_map_of_eventually   the bridge into the Euler-form formalism

`GaloisForLFunctions/RHTower/PowerCanonicalProductHypertranscendence.lean`

    powerGenus_ne_inv_of_irrational   an irrational `s` never has `1/s` equal to its genus, so the
                                      Barnes ladder applies to the whole irrational family
    **not_polynomial_relation_barnesEulerJet** :
      for every irrational `s > 0`, no nonzero `P ∈ ℂ[t][Z_0,…,Z_m]` satisfies
      `P(t, R_s, θ R_s, …, θ^m R_s) = 0` near `t = 0⁺`

`#print axioms` on the headline: `[propext, Classical.choice, Quot.sound]`.

### What this is, and what is left

This is the card's chain with §5 replaced by the direct obstruction and `(4)`–`(6)` used in the
Poincaré form they were proved in.  Concretely it says: **the Barnes remainder of an
irrational-power canonical product is differentially transcendental over `ℂ(1/x)`.**

The card's headline sentence is about `W_s` rather than about its Barnes remainder, and the passage
between them is §4.1–4.4: `W_s` DA ⟹ `x W_s'/W_s` DA ⟹ `R_s` DA.  Those implications are formal —
`BarnesRemainderDATransfer.differentialAlgebraicOver_barnesRemainder` — but in an abstract
`Differential` field.  What is not yet formal is the *instantiation*: realising `W_s`, `x^{1/s}` and
`R_s` inside a concrete differential field (the corpus's `meroField U` on a slit plane is the
natural home) and converting `¬ AlgebraicIndependent` there into the pointwise relation with `ℂ[t]`
coefficients that `not_polynomial_relation_barnesEulerJet` refutes.  That is plumbing — evaluation
of `meroField` elements, clearing denominators from `RatFunc ℂ` to `ℂ[t]` under `t = 1/x`, and the
triangular change between `x^k d^k/dx^k` and `θ^k` — and adds no new mathematics.

| step | status |
|---|---|
| `(1)`, `(4)`–`(6)`, `(8)`–`(12)` | formal |
| `(14) ⟹ (15)` with polynomial coefficients | formal |
| §5 obstruction on `R̂_s` | formal |
| **`R_s` is differentially transcendental over `ℂ(1/x)`** | **formal** |
| §4 instantiation `W_s` DA ⟹ `R_s` DA in a concrete differential field | open (plumbing) |

## Lean progress — §4 INSTANTIATION: SIX MODULES, THE JET BRIDGE IS CLOSED

The card's §4 is a two-line closure argument on paper, but making it Lean-level concrete means
realising `W_s`, `x^{1/s}` and `R_s` in an actual differential field and converting the corpus's
*ordinary-derivative* relation into the *Euler-jet* relation the obstruction consumes.  Six modules,
all wired, all clean.

`GaloisForLFunctions/HTGeometry/MvPolynomialLinearSubstitution.lean`

    matrixSubst M                 the substitution `X_i ↦ ∑_j M_{ij} X_j`
    matrixSubst_comp              substitutions compose by matrix multiplication
    matrixSubst_injective         **a substitution by an invertible matrix is injective** — the
                                  inverse matrix is a left inverse, so nonzero relations stay nonzero
    isUnit_det_of_lowerTriangular

`GaloisForLFunctions/HTGeometry/EulerOrdinaryJetChange.lean`

    cEulerDeriv, eulerJetCoeff    the Euler operator and the integers `d(m,k)`
    eulerJetCoeff_self = 1, eulerJetCoeff_eq_zero_of_lt
    weightedJet_succ              `z^{m+1}f^{(m+1)} = (θ − m)(z^m f^{(m)})`
    weightedJet_eq_sum :
      **`z^m f^{(m)} = ∑_{k ≤ m} d(m,k) θ^k f`** — unitriangular, hence invertible against the
      substitution lemma above

`GaloisForLFunctions/HTGeometry/PowerCanonicalProductRightHalfPlane.lean`

    rightHalfPlane, its openness, convexity, preconnectedness, infinitude, and inclusion in the
    slit plane
    powerCanonicalProduct_ne_zero_of_re_pos :
      **`W_s` has no zero where `Re z > 0`** — its zeros are the negative reals `-n^s`

`GaloisForLFunctions/RHTower/EulerJetRealRestriction.lean`

    eulerDeriv_iterate_ofReal     the real Euler jets of a complex-analytic function are its complex
                                  Euler jets restricted

`GaloisForLFunctions/RHTower/BarnesEulerRemainderStep.lean`

    eulerDeriv_const_mul_ofReal_cpow   the Euler operator multiplies `c x^A` by `A`
    eulerDeriv_barnesIntResidue, eulerDeriv_barnesLeadingGenusResidue :
      the residue weights `(-p)^m` ARE the Euler derivatives of the residues
    differentiableAt_eulerIterate_powerCanonicalEulerSum
    barnesEulerRemainder_succ, **barnesEulerRemainder_eq_iterate** :
      the weighted Barnes remainders are the Euler jets of the single function `R_s`

`GaloisForLFunctions/RHTower/BarnesRemainderComplex.lean` and `BarnesRemainderJetBridge.lean`

    barnesRemainderC s            `z W_s'/W_s − (π/s)csc(π/s) z^{1/s} − ∑_{j=-g}^{0} (-1)^j ζ(-sj) z^{-j}`
    barnesRemainderC_ofReal       it restricts on the axis to `barnesEulerRemainder s 0`
    analyticOnNhd_barnesRemainderC  it is analytic on the right half-plane
    cEulerDeriv_iterate_barnesRemainderC, barnesEulerRemainder_eq_jet
    **weightedJet_barnesRemainderC** :
      `z^m R^{(m)}` at a positive real point is `∑_{k≤m} d(m,k)(-1)^k · barnesEulerJet s k (1/x)`

So the two ends now meet: `exists_relation_of_differentialAlgebraicOver_analyticMeroElement` returns
a relation in `z` and the ordinary jets `R^{(j)}(z)` valid on the half-plane, and
`weightedJet_barnesRemainderC` rewrites those jets in terms of the functions whose Poincaré
expansions are the Euler jets of `R̂_s`.

### What is left

| step | status |
|---|---|
| the whole analytic chain, §5 obstruction, `(14) ⟹ (15)` | formal |
| jet change, half-plane analyticity, remainder-is-an-Euler-jet | formal |
| `x^{1/s}` in `meroField rightHalfPlane` with its eigen-equation `z u' = (1/s)u` | open |
| the `z ↦ 1/t` reversal of the extracted relation | open |

Both remaining items are bookkeeping: the first is `ratfuncToMero (C(1/s)/X)` against
`analyticMeroElement (barnesLeadingTermC s)` — the corpus supplies
`ratfuncToMero_algebraMap_polynomial` and `analyticMeroElement_congr/_mul` for it; the second is
`Polynomial.reverse` applied to `finSuccEquiv P`, whose leading coefficient is the constant term of
the reversal and so is nonzero.

## Lean progress — THE CARD IS CLOSED

```text
RHTower.hypertranscendental_powerCanonicalProduct_irrational :
  ∀ {s : ℝ}, 0 < s → Irrational s → Hypertranscendental (powerCanonicalProduct s)

#print axioms → [propext, Classical.choice, Quot.sound]
```

This is §1's Theorem verbatim: for every positive irrational `s` the canonical product with simple
zeros `-n^s` satisfies no algebraic differential equation over `ℂ(z)`.  `Hypertranscendental` is the
corpus's own concrete predicate on entire functions — `¬ DifferentiallyAlgebraic`, with
`DifferentiallyAlgebraic f` the existence of a nonzero `P ∈ ℂ[z, y_0, …, y_n]` with
`P(z, f, f', …, f^{(n)}) ≡ 0` — the same predicate Bank's integer theorem is stated in.

`GaloisForLFunctions/RHTower/PowerCanonicalProductHypertranscendental.lean` (wired, axiom-clean)

    jetChangeMatrix n                 lower-triangular, diagonal `C((-1)^j) X^j`
    matrixSubst_jetChangeMatrix_injective
                                      a unit determinant over `ℂ(t)`, so the jet change loses
                                      nothing
    reversedRelation P                `Polynomial.reverse` of `finSuccEquiv P`: the substitution
                                      `z = 1/t` made polynomial
    reversedRelation_ne_zero          the reversal's `b`-th coefficient is the original's `(N−b)`-th
    eval₂_reversedRelation            it evaluates to the original relation at `z = t`
    jetChange_sum_eq                  the matrix rows evaluate to the ordinary jets `R^{(i)}(1/t)`
    **hypertranscendental_powerCanonicalProduct_irrational**

### The chain, as formalised

| step | Lean |
|---|---|
| `W_s` DA ⟹ its realization in `meroField` of the right half-plane is DA | `differentialAlgebraicOver_analyticMeroElement_of_relation` |
| §4.1–4.4: the Barnes remainder is DA | `differentialAlgebraicOver_barnesRemainderC` |
| the remainder is analytic on the half-plane and restricts to `barnesEulerRemainder s 0` | `analyticOnNhd_barnesRemainderC`, `barnesRemainderC_ofReal` |
| a DA element gives a pointwise relation in `z` and the ordinary jets | `exists_relation_of_differentialAlgebraicOver_analyticMeroElement` |
| `z = 1/t` cleared by reversal; ordinary jets traded for Euler jets | `reversedRelation`, `jetChangeMatrix` |
| `(4)`–`(6)`: the Euler jets have the Euler jets of `R̂_s` as expansions | `isAsymptoticExpansion_barnesEulerJet` |
| `(14) ⟹ (15)`: the relation passes to the formal series | `eval₂_powerSeries_eq_zero_of_eventually` |
| §5: `R̂_s` solves no analytic ADE | `not_isFormalEulerADESolution_barnesTail` |

### What replaced §5

The card's §5 invoked the **sharp** half of Sibuya--Ramis — a statement about every divergent
solution of every analytic ODE.  It is not used.  The card only ever needed one implication about
one series whose coefficients are known on *both* sides, and for such a series the leading Newton
vertex dominates the recursion by itself.  `BarnesTailNonlinearObstruction` proves that directly:
the defect exponent is fixed before the truncation order, the leading vertex is pinned below a
ceiling free of the truncation order, and the truncation order is then taken past both.

The Newton--Ramis factorization `L = M ∘ N` remains the right construction for the general sharp
statement, and the operator ring built for it stands; the card's chain no longer passes through it.

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

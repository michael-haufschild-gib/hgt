# Polynomial aperture detection from an arbitrary off-line zero

- **ID:** centered-heat-polynomial-aperture-detection
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean open
- **Source:** CROSS-250-2026-10-22, C002
- **Scientific status:** `[PROVED HERE ON PAPER] [LEAN OPEN] [NOVELTY PROVISIONAL]`
- **Contribution credit:** 0 pending formalization and final significance audit.
- **Statement:** A single off-line zeta zero supplies a negative smooth compact Weil test at an aperture bounded polynomially in its height and inverse-square depth, without a near-top or separation premise.

## Exact theorem

There is an absolute constant `C > 0` such that, for every nontrivial zeta zero
`rho = 1/2 + eta + i gamma` with `delta = |eta| > 0`, there are `a > 0` and
`f in C_c^infinity(R,C)` satisfying

```text
support(f) subset [-a,a],
a <= C delta^(-2) (4 + |gamma|)^38,
Re W_zeta(f,f) < 0.                                      (T)
```

Every zero is counted with its actual multiplicity. No zero separation, attained maximal depth,
near-top condition, or uniform local off-line count is an assumption. The exponent 38 is a coarse
choice, not the scientific claim. The claim is uniform control from the data of any one off-line
zero. It concerns the full test cone, not the fixed two-bump lag family.

One consequence is quantitative: positivity on every smooth test supported in `[-a,a]` excludes
any zero of height `|gamma| <= H` and depth `delta` with
`C delta^(-2) (4+H)^38 <= a`. This does not turn one bounded aperture into a global width bound.

## Corpus inputs and novelty boundary

Write `z_q = -i(rho_q - 1/2)`, indexed by `XiZeroCopy`. The following inputs are unconditional:

1. `|(z_q).im| < 1/2`; `z_q != 0`.
2. `S := sum_q |z_q|^(-2) < 1`. The sharper `198/3175` cap follows from
   `XiResolventMassBudget.tsum_norm_xiResolventPoint_le_budget` at shift zero.
3. For an absolute `C0 >= 0`,
   `#{q : |Re z_q - gamma| <= 1} <= 16(C0 + log(|gamma|+4))`.
   This is `XiWindowZeroCount.ncard_xiOrdinateWindow_one_le_log`, with
   `C0 = xiLineTwoLogDerivConstant`; finiteness is proved there, not assumed.
4. Dirichlet phase recurrence for a finite set of `N` real frequencies:
   some `1 <= k <= 8^N` makes every cosine at the scaled time at least `1/2`.
   Use `HTGeometry/DirichletSimultaneousApproximation.exists_dirichlet_phase` and `pi <= 4`.
5. The Gaussian Fourier transform, integration by parts, and the actual Weil zero sum.
   Relevant existing modules are `XiGaussianHeatTestPhysicalSide`,
   `XiGaussianHeatSharpWitnessComparison`, and the compact-source explicit-formula bridges.

Existing arbitrary-zero Weil and polynomial-Gaussian detectors are qualitative. The explicit
contact-aperture theorem in `NearTopZerosForceNegativeGroundEnergyBeyondAnExplicitAperture`
assumes near-topness. `FiniteOffLineSetsAreVisible` uses a finite off-line set and a depth gap.
`GaussianArithmeticBoundedCeilingReceiver` already proves qualitative amplification in a light
cone. `XiSliceHeatedOffLineDetection` uses inverse-square mass after deleting a pair and a
nonvanishing central Xi value. None is credited again here.

The new candidate mechanism is to align **all** copies in one fixed height window, whether or not
they are deeper than the selected zero. Their phases then have the same favorable sign. A
Gaussian makes the complementary height range harmless without selecting a maximal packet or
estimating any spectral gap. The logarithmic local count converts the recurrence bound into a
polynomial in height. Quantitative compact cutoff retains that bound.

External searches are excluded by the user's instruction. Whole-corpus searches have been run;
the final polynomial-aperture search returned usable partial results after reranking services
stopped. No universal priority claim is made.

## Complete paper proof

Fix an off-line zero and choose its divisor copy `q0`. Put

```text
gamma = Re z_q0,  delta = |Im z_q0|,
r_q = Re z_q - gamma,  e_q = Im z_q,
F = {q : |r_q| <= 1},  N = #F,
B = 6(1 + gamma^2),
T = delta^(-2) log(4B+4),
U = T 8^N.
```

The strip gives `0 < delta < 1/2`, so `T > 1` and `U > 1`. The count in input 3 makes `F` finite.

### 1. A uniform bound for the exterior heat tail

For every real `r`, `r^2 exp(-r^2) <= 1`. Also

```text
|z_q|^2 = (r_q+gamma)^2 + e_q^2
        <= 2 r_q^2 + 2 gamma^2 + 1/4.
```

It follows that

```text
|z_q|^2 exp(-r_q^2) <= 3(1+gamma^2),
sum_q exp(1/4-r_q^2) <= 6(1+gamma^2) S <= B.             (1)
```

Here `exp(1/4) < 2`, and reciprocal-square summability justifies the sum. Define

```text
H(t) = Re sum_q exp(-t (z_q-gamma)^2),  t > 0.
```

At `t=1`, `(1)` gives `|H(1)| <= B`. If `q` is outside `F`, then
`r_q^2-e_q^2 > 3/4`. Consequently, for every `t >= 1`,

```text
sum_(q outside F) |exp(-t (z_q-gamma)^2)| <= B.           (2)
```

All heat sums and their first derivatives converge locally uniformly for `t>0`. For completeness,
on `t in [u,v]`, `0<u<=v`, their termwise norms are bounded by

```text
exp(v/4) (1 + |z_q-gamma|^2) exp(-u r_q^2).
```

Multiplication by `|z_q|^2` leaves a polynomial in `|r_q|` times `exp(-u r_q^2)`, which is bounded
on the real line. Thus a constant multiple of `|z_q|^(-2)` dominates both series. The Weierstrass
test and differentiation of locally uniformly convergent derivative series prove

```text
H'(t) = -Re sum_q (z_q-gamma)^2 exp(-t (z_q-gamma)^2).    (3)
```

### 2. Recurrence makes the entire head favorable

Apply Dirichlet phase recurrence at step `T` to the `N` frequencies `-2 r_q e_q`, `q in F`.
There is an integer `1 <= k <= 8^N` such that, at `t=kT`,

```text
cos(-2 t r_q e_q) >= 1 - 2 pi^2/64 >= 1/2
```

for every copy in `F`. Hence every head term has nonnegative real part. The selected copy has
`r_q0=0` and supplies at least `exp(t delta^2)/2`; retaining only it and using `(2)` gives

```text
H(t) >= exp(t delta^2)/2 - B
     >= (4B+4)/2 - B = B+2 >= H(1)+2.                    (4)
```

No comparison between depths of distinct zeros was used. Since `1<t<=U`, the mean-value theorem
gives some `s in (1,t)` with

```text
H'(s) = (H(t)-H(1))/(t-1) >= 2/(t-1) > 2/U.             (5)
```

### 3. The derivative is a negative Weil value

With Fourier convention `F_h(z)=integral h(x) exp(ixz) dx`, define

```text
h(x) = x exp(-x^2/(2s)) exp(-i gamma x) / (sqrt(2 pi) s^(3/2)).
```

The Gaussian transform and its first frequency derivative give

```text
F_h(z) = i(z-gamma) exp(-s(z-gamma)^2/2).
```

Because `s,gamma` are real,

```text
F_h(z) conjugate(F_h(conjugate(z)))
  = (z-gamma)^2 exp(-s(z-gamma)^2).
```

The zero sum is absolutely convergent by the domination used in `(3)`. Define its value on this
Gaussian directly; no extension of the compact explicit formula is needed. Equations `(3)` and
`(5)` give

```text
Re Q(h) < -2/U,                                        (6)
Q(v) := sum_q F_v(z_q) conjugate(F_v(conjugate(z_q))).
```

### 4. One universal smooth cutoff

Fix once and for all a smooth real function `theta` with `0<=theta<=1`, equal to `1` on
`(-infinity,0]` and `0` on `[1,infinity)`. Such a function is obtained by integrating a normalized
nonnegative smooth bump supported in `(0,1)` and subtracting its cumulative integral from one.
Its first two derivatives have compact support and finite suprema `M1,M2`. Set

```text
M = 1 + 2 M1 + 2 M2 + 2 M1^2,
chi_A(x) = theta(x-A) theta(-x-A).
```

For `A>=1`, this is smooth, `0<=chi_A<=1`, equals one on `[-A,A]`, vanishes outside
`[-A-1,A+1]`, and has `|chi_A'|, |chi_A''| <= M`. These follow directly from the product rule.
All constants depend only on this one fixed cutoff.

Set

```text
K = 1024 (1+S) M (1+|gamma|)^2,
A = 16 U K,
f = chi_A h,
e = f-h.
```

In particular `K>=1024`, `A>=2U>=2`, and `f` is smooth with the desired compact support.

### 5. Weighted cutoff error

Write `V_j(v) = integral |v^(j)(x)| exp(|x|/2) dx`. Completing the square weakly gives

```text
-x^2/(2s) + |x|/2 <= -x^2/(4s) + s/4,
V_0(h) <= 4 exp(U/4).                                  (7)
```

Indeed the integral of `|x| exp(-x^2/(4s))` is `4s`, and
`s>=1`, `sqrt(2pi)>1` remove the normalization factor. Also `V_0(f)<=V_0(h)`.

For clarity, the first two derivative factors of `h`, after removing its constant and the common
Gaussian and modulation, are

```text
h' : 1 - x^2/s - i gamma x,
h'' : x^3/s^2 - 3x/s - 2i gamma (1-x^2/s) - gamma^2 x.
```

On `|x|>=A>=1`, using `s>=1`, the three absolute factors for `h,h',h''` are bounded respectively
by `(1+|gamma|)^2 |x|^3`, `2(1+|gamma|)^2 |x|^3`, and
`4(1+|gamma|)^2 |x|^3`. The normalization is at most one. The product rule
`e''=(chi_A-1)h''+2chi_A'h'+chi_A''h` therefore gives the deliberately weaker bound

```text
|e''(x)| <= 20 M (1+|gamma|)^2 (1+|x|^3) exp(-x^2/(2s)).
```

Inside `[-A,A]`, `e''=0`. Since `s<=U` and `|x|>=A>=2U`,
`-x^2/(2s)+|x|/2 <= -x^2/(4U)`. Elementary Gaussian tail integration, using `1<=x` for `x>=A`,
now yields

```text
V_2(e) <= 80 M U (1+|gamma|)^2 (A^2+4U+1) exp(-A^2/(4U)). (8)
```

The integrals used here are exactly
`integral_A^infinity x exp(-x^2/(4U)) dx = 2U exp(-A^2/(4U))` and
`integral_A^infinity x^3 exp(-x^2/(4U)) dx = 2U(A^2+4U) exp(-A^2/(4U))`.

For every `z` with `|Im z|<=1/2`, direct integration and two integrations by parts give

```text
|F_v(z)| <= V_0(v),
|z|^2 |F_e(z)| <= V_2(e).
```

Every boundary term vanishes: outside a compact set `e=-h`, whose derivatives have Gaussian
decay. Applying these bounds to the difference of the two product terms in `Q(f)-Q(h)` gives

```text
|Q(f)-Q(h)| <= S V_2(e) (V_0(f)+V_0(h))
 <= 640 S M U (1+|gamma|)^2 (A^2+4U+1) exp(U/4-A^2/(4U)). (9)
```

The same estimates with `V_2(f),V_2(h)` prove separate absolute convergence, so subtraction of the
two sums is justified.

Substitute `A=16UK`. Since `U,K>=1`,

```text
A^2+4U+1 <= 261 U^2 K^2,
S M (1+|gamma|)^2 <= K/1024.
```

Multiplying `(9)` by `U` bounds its right-hand side by

```text
164 U^4 K^3 exp(U/4-64 U K^2)
 <= U^4 K^4 exp(U/4-64 U K^2) < 1.                      (10)
```

For the last strict inequality, take logarithms and use `log U<=U`, `log K<=K`:

```text
4log U+4log K+U/4-64UK^2
 <= 4U+4K+U/4-64UK^2
 <= (33/4-64)UK^2 < 0.
```

Combining `(6)` and `(10)` proves `Re Q(f)<-1/U<0`. For compact smooth `f`, the actual Weil
explicit formula identifies `Q(f)=W_zeta(f,f)`. Thus the cutoff preserves strict negativity.

### 6. The aperture is polynomial in height

Put `L=4+|gamma|`. The local count and `16log 8<34` imply

```text
8^N <= exp(34 C0) L^34.
```

Also `B<=6L^2`, so `log(4B+4)<=28L^2`, and `S<1` gives `K<=2048 M L^2`. Therefore the support
half-width `a=A+1` satisfies

```text
a <= 17 U K
  <= (17 * 28 * 2048 * M * exp(34 C0)) delta^(-2) L^38.
```

Taking `C=17 * 28 * 2048 * M * exp(34 C0)>0` proves `(T)`. Every constant is absolute, fixed
before selecting the zero. This closes the paper proof.

## Formalization checkpoints

- [x] exact theorem, hostile corpus comparison, no near-top or separation input
- [x] locally uniform heat/derivative domination and finite head recurrence
- [x] negative odd-Gaussian transform with correct conjugation sign
- [x] smooth compact cutoff with quantitative second-derivative control
- [x] polynomial aperture bound, absolute constants, no open paper dependency
- [ ] audit exact Lean input signatures and source identification
- [ ] formalize centered heat bounds and recurrence
- [ ] formalize Gaussian cutoff and exact compact Weil conclusion
- [ ] run leaf audits, inspect axioms, wire umbrellas, refresh declaration index
- [ ] final significance audit; no contribution credit before completion

## Failure checks

The proof never drops an unsigned term from a potentially negative head: the recurrence makes
each head cosine nonnegative first. A deeper nearby zero is helpful at the recurrence time.
The far tail is suppressed by **height distance**, not by a missing depth gap. The mean-value
step asserts existence of one derivative sign and does not claim monotonicity. The Gaussian is
only an intermediate zero-sum test; the delivered test is compact and smooth. The proof does not
exhibit an off-line zero or prove either RH or its negation.

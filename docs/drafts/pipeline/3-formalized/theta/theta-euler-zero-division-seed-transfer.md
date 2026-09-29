# Zero division commutes with the theta Euler resolvent on its physical half-line

- **ID:** `theta-euler-zero-division-seed-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean); certificate
  [`theta-euler-zero-division-seed-transfer-formalized.md`](theta-euler-zero-division-seed-transfer-formalized.md)
- **Routes:** STC, CSB, U, K-RVM, MPLF; prime–archimedean seam audit
- **Status:** `[PROVED HERE ON PAPER] [NOT AN RH PROOF]`

## Statement

Let `h=thetaCuspLogSeed` and `k=thetaCuspFullSource`. On `x≥0`, the
literal all-integer Euler resolvent is

```text
(R h)(x) = Σ_(n≥1) n^(-1/2) h(x+log n) = k(x).
```

For `α∈ℂ`, define the outward sine Green operator on the positive
half-line by

```text
(T_α^+ f)(x)=α ∫₀∞ sin(αt) f(x+t)dt.
```

All displayed series and integrals are absolutely convergent for the
literal seed and every fixed finite iterate of these operators. **Zero
division commutes exactly with every finite-prime resolvent and with
the all-integer limit:**

```text
T_α^+ (R h) = R (T_α^+ h)                       on x≥0,
T_α^+ (R_N h) = R_N (T_α^+ h)                   on x≥0.
```

The same identities hold for products of outward Green operators and
real linear combinations of their conjugate-parameter pairs. Moreover,
`T_α^+ h/h` is bounded on `[0,∞)` and tends to zero as `x→∞`; this also
holds for each nonempty finite iterate.

There is a concrete consequence if `F=XiC` has any off-line zero
quartet `±α,±conj(α)` of multiplicity `m≥1`. Put

```text
P_α(z)=(1−z²/α²)^m(1−z²/conj(α)²)^m.
```

Then a real even source `u_α`, bounded relative to `k`, and a real
positive-half-line seed `v_α`, bounded relative to `h`, exist with

```text
Fourier(u_α)(z)=z² F(z)/P_α(z),
u_α(x)=Σ_(n≥1)n^(-1/2)v_α(x+log n)   (x≥0),
u_α/k→0,       v_α/h→0              (x→+∞).
```

For every sufficiently small `ε>0`, both `k+εu_α` on the full real
line and `h+εv_α` on the physical half-line are strictly positive, and

```text
k(x)+εu_α(x)
  = Σ_(n≥1)n^(-1/2)[h+εv_α](x+log n)            (x≥0).
```

The perturbed full source has the same total mass, the same leading
first-atom theta tail, and **exactly the same complete real-zero
divisor** as `k`. Nevertheless it removes the selected original
off-line quartet, replacing it by the nonreal roots of
`P_α(z)+εz²`; all other original zeros remain. The even extension
is smooth at the reflection seam because `F(α)=0` through the stated
multiplicity. Thus positive all-prime coefficients, a positive
archimedean seed, exact outward prime covariance, smooth reflection,
the source mass, the leading tail and every real zero do not by
themselves select the literal source.

## Proof

`ThetaCuspFinitePrimeSource.lean` proves the literal identity
`n^(-1/2)h(x+log n)=thetaCuspSourceTerm(x,n)` and the convergence of its
sum. For `x≥0`, `h(x)>0`: its polynomial factor is
`2π exp(2x)−3>0`. The explicit polynomial-Gaussian formula gives
constants `A,C` with

```text
|h(y)| ≤ C exp(Ay−π exp(2y))                    (y≥0).
```

For fixed `x≥0`, multiplication by
`|sin(αt)|≤exp(|Im α|t)` leaves
`Σ_(n≥1)n^(-1/2)∫₀∞|h(x+t+log n)|exp(|Im α|t)dt`
finite. Tonelli/Fubini therefore interchanges the sum and integral.
Outward shifts commute pointwise with `T_α^+`:

```text
T_α^+[f(·+a)](x)=(T_α^+f)(x+a).
```

These facts prove both resolvent identities; the same majorant proves
their finite iterations. More precisely, the first-atom exponential
implies for large `x`

```text
|h(x+t)|/h(x)
 ≤ C exp(A t−π exp(2x)(exp(2t)−1))
 ≤ C exp(−[2π exp(2x)−A]t).
```

Integrating against `exp(|Im α|t)` shows
`|T_α^+h(x)|/h(x)=O(exp(−2x))`. The same argument inductively handles
finite iterates. Continuity and `h>0` bound the ratio on each compact
interval, completing the seed estimate.

Repeated one-sided zero division at `α` and `conj(α)` is valid through
their multiplicity because each remaining transform still vanishes at
the divided zero. The complex division theorem proved in the
[endpoint completeness card](theta-endpoint-harmonic-completeness.md)
gives sources for `F/P_α` bounded relative to `k`. Real partial
fractions of the **proper** rational function `z²/P_α(z)` express
`u_α` as a real combination of nonempty repeated zero divisions.
Apply the same combination to `h` to define `v_α`. Commutation just
proved gives the Euler expansion on `x≥0`, and the tail estimates give
`u_α/k→0` and `v_α/h→0`. On compact intervals both ratios are bounded,
so small positive `ε` makes both perturbed functions positive.

Finally, `P_α(x)>0` for real `x`, since it is a product of conjugate
factors, so `1+εx²/P_α(x)>0` for every `ε>0`. The Fourier identity
then preserves every real zero with exactly its multiplicity and adds
no real zero. Its value at zero is unchanged, and the relative-tail
limit preserves the first-atom leading term. At a selected off-line
root, `F/P_α` is nonzero and `εα²≠0`, so that root is absent from
the new transform. The polynomial `P_α+εz²` has the same degree as
`P_α`; for small `ε`, its roots remain in disjoint neighborhoods of
the original nonreal quartet. The full even source is smooth because
each division step has its necessary zero at the join, as in the
endpoint card.

## Exact Gaussian-base defect

The transfer identifies precisely which archimedean equation the
modified seed loses. Put

```text
ψ(x)=exp(x/2−π exp(2x)),
L=∂_x−(1/2−2π exp(2x)).
```

Direct differentiation gives `Lψ=0` and
`h=(∂_x²−1/4)ψ`. The outward Green operator commutes with constant
coefficient derivatives but not with `L`; for every `α≠0`,

```text
[L,T_α^+]ψ(x)
 = −2πα exp(2x)∫₀∞ sin(αt)(exp(2t)−1)ψ(x+t)dt.       (3)
```

This defect is **not identically zero**. If it were, `T_α^+ψ` would
solve the same first-order equation `Lf=0` as `ψ`, so
`T_α^+ψ=cψ`. But the tail estimate gives
`T_α^+ψ/ψ→0`, hence `c=0`; the Green equation
`(T_α^+ψ)''+α²T_α^+ψ=α²ψ` then contradicts `α≠0` and `ψ>0`.
Thus zero division preserves the Euler sum and the second-order
scaling-Hamiltonian form while making an explicit, unavoidable change
to the Gaussian base. Equation (3) is a concrete seam observable to
test in a future source-specific Ward law. Its nonzero value by itself
does not constrain the zeros of `F`.

## Sharp two-ended moment–tail law

There is an exact relation between what a zero-division deformation hides
at the spectral origin and what it hides in the physical theta tail.
Select finitely many off-line quartets, counting multiplicity, and write

```text
P(w)=∏_α (1−w/α²)^(m_α)(1−w/conj(α)²)^(m_α),
D=deg P=2∑_α m_α.
```

For any nonzero real polynomial `N` with `N(0)=0` and `deg N≤D`, let
`r(w)=N(w)/P(w)`, and construct `u` and `v` by the same real
partial-fraction zero divisions as above, so `Fourier(u)(z)=F(z)r(z²)`
and `u=Rv` on `x≥0`. Put `d=D−deg N` and let `c` be the quotient of
the leading coefficients of `N` and `P`. Then both tails have the
**same sharp leading coefficient**:

```text
lim_(x→∞) exp(4d x) u(x)/k(x)
 = lim_(x→∞) exp(4d x) v(x)/h(x)
 = (−1)^d c/(2π)^(2d) ≠ 0.                         (4)
```

For `d=0`, this says both ratios tend to the rational multiplier's
constant part at infinity. For `d≥1`, the deformation preserves the
leading theta tail and has exact relative decay `exp(−4d x)`. In
particular the single-quartet mass-preserving, tail-preserving
direction `r(w)=w/P(w)` decays like `exp(−4x)`, sharper than the
`O(exp(−2x))` estimate above.

Here is a direct proof of (4). The literal seed has the exact
first-atom asymptotic

```text
h(x) ∼ 4π² exp(9x/2−π exp(2x)),       k(x)/h(x)→1.
```

The second assertion follows from the positive Euler sum: every
`n≥2` has the additional factor
`exp(−π(n²−1)exp(2x))`, and the polynomial factors and
`n^(−1/2)` weights admit a common summable majorant for large `x`.
Set `y=exp(2x)`. For either `f=h` or `f=k`, one consequently has

```text
f(x+t/y)/f(x) → exp(−2πt)                 (fixed t≥0),
```

with an exponential majorant in `t` after restricting to large `x`.
When `d≥1`, `r(−s²)` is a proper rational function of `s`. Its causal
inverse Laplace kernel `K(t)` is a finite sum of polynomial times
exponential functions, hence analytic at `t=0` and of at most
exponential growth. The outgoing Green formula gives
`u(x)=∫₀∞K(t)k(x+t)dt` and `v(x)=∫₀∞K(t)h(x+t)dt`.
Since

```text
r(−s²)=(−1)^d c s^(−2d)+O(s^(−2d−2))
```

at positive infinity, uniqueness of the Laplace expansion gives
`K(t)=(−1)^d c t^(2d−1)/(2d−1)!+O(t^(2d))` at zero. Substitute
`t↦t/y` in the two causal integrals. Dominated convergence and
`∫₀∞t^(2d−1)exp(−2πt)dt=(2d−1)!/(2π)^(2d)` yield (4).
For `d=0`, split off the constant part `c`; the remainder is proper
and its relative tail tends to zero.

The same polynomial carries an exact **two-ended filtration**. If
`w^J` divides `N`, with `J≥1`, then the first `J` even moments of `u`
(orders `0,2,…,2J−2`) vanish because `F(0)≠0`. Conversely these
moment vanishings force this divisibility. Requiring in addition
`u/k=O(exp(−4d x))` is equivalent by (4) to `deg N≤D−d`.
Therefore the real dimension of the bounded, real-even
zero-division directions satisfying both requirements is exactly

```text
max(D−J−d+1, 0).                                (5)
```

The exact classification of bounded real-zero annihilators in the
[endpoint completeness card](theta-endpoint-harmonic-completeness.md)
shows (5) is an equality for the full bounded source-difference space,
not merely for a chosen set of partial fractions. Every such direction
also has a bounded seed difference and gives, for sufficiently small
real perturbation parameter, a positive full source, positive physical
seed, unchanged real-zero divisor, unchanged first `J` moments and
the stated tail agreement. If infinitely many off-line quartets exist,
arbitrarily large finite products `P` make this space infinite
dimensional for every fixed pair `(J,d)`. This is a precise
identifiability obstruction, not a source-side exclusion of those
quartets.

The **complete** tail germ, unlike every finite truncation, determines
the rational defect. For a proper `r`, write its causal kernel near
zero as `K(t)=∑_(j≥0) κ_j t^j/j!`. The explicit first atom has

```text
h(x)=4π² y^(9/4) exp(−πy)(1−3/(2πy)),       y=exp(2x),
```

and all other Euler atoms are exponentially smaller. Expanding
`h(x+t/y)/h(x)` in `1/y`, with `t` fixed, begins with
`exp(−2πt)`; each later coefficient depends only on the explicit
first-atom expression. The same expansion holds for `k` up to an
exponentially small remainder. Watson's lemma, justified by the
exponential majorant above, consequently gives a full asymptotic
series

```text
u(x)/k(x) ∼ ∑_(n≥0) a_n y^(−n−1),
a_n = κ_n/(2π)^(n+1) + a known linear combination of κ_0,…,κ_(n−1).
```

The diagonal coefficient never vanishes, so the tail coefficients
recover every Taylor coefficient of `K` recursively. Because `K` is
an exponential polynomial, its Taylor series determines `K`, whose
Laplace transform is `r(−s²)`. Thus the full tail asymptotic germ
determines `r`; a nonzero rational defect cannot be flat to **all**
orders in `exp(−2x)`. The constant part of a nonproper `r` is first
read from `lim u/k`, after which the proper argument applies. This
sharpens the inverse-problem interpretation: finite endpoint sensors
have the exact blind dimension (5), whereas the infinite endpoint
germ is faithful on the rational zero-division space. It still does
not provide an independent law forcing that germ to vanish for the
literal theta source.

## Meaning and limit

The prime sum and all its finite-prime truncations transport the
zero-division defect without changing its algebra. This locates the
selection problem at the **exact archimedean seed and its interaction
with the reflection seam**, not at prime covariance by itself. The
positive perturbed seed is not the literal polynomial Gaussian; its
existence does not contradict any source identity that pins that exact
seed. Conversely, proving uniqueness of the literal seed among Euler
representations would not prove RH: the off-line alternative is not
asserted to satisfy that extra seed identity. A producer must extract
a contradiction from the hypothetical off-line divisor using a
source-specific joint prime–archimedean law.

This is a conditional source-deformation theorem, not an exclusion of
off-line zeros. The exact commutation, positive-seed consequence, and
tail-germ law were not found in the partial current corpus searches;
external novelty is not asserted.

## Formalization gate

- [x] Paper proof of absolute sum–integral interchange, shift
      commutation, and the seed-relative tail bound.
- [x] Paper construction of the positive-seed off-line deformation
      from repeated complex zero division and real partial fractions.
- [x] Paper derivation and nonvanishing of the Gaussian-base
      commutator (3).
- [x] Paper derivation of the sharp two-ended tail coefficient and
      moment–tail dimension law (4)–(5), and full-tail-germ faithfulness.
- [x] Formalize the outward Green operator, its commutation with the
      existing finite-prime source and the all-integer limit
      (`ThetaSeedHalfLineDivision`).
- [x] Formalize repeated complex zero division and the positive seed
      transfer (`ThetaZeroDivisionRealization`, `ThetaSeedTransferQuartet`,
      `ThetaGaussianBaseCommutator`).
- [x] Formalize the Laplace-kernel endpoint asymptotic, the moment–tail
      dimension law and the full tail germ (`ThetaTailScalingAsymptotics`,
      `ThetaTwoEndedTailLaw`, `ThetaTailIntegralCalculus`,
      `ThetaTailGermExpansion`); see the certificate for the theorem map.

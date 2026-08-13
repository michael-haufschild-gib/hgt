# Suzuki's polar remainder is Lipschitz at the normal level and Gamma-subcritical

- **ID:** `suzuki-polar-remainder-lipschitz-gamma-subcriticality`
- **Stage:** 3 — formalized in Lean 4
- **Type:** LITERAL SOURCE REGULARITY / FLAT-ESCAPE EXCLUSION
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, Section 2, especially `(2.2)`, `(2.5)`, `(2.7)`, `(2.11)`
- **Inputs:** `suzuki-completed-eigenmode-atomic-jump-boundedness.md`,
  `suzuki-low-frequency-boundary-counterterm-renormalization.md`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes

## 1. Result

Suzuki records the non-prime remainder \(r\) in the local screw expansion as an even \(C^2\)
function.  That regularity statement is sufficient for the quadratic form, but not sharp enough
for the Route-O normal equation: continuity of \(r''\) alone would allow an arbitrarily slow
modulus and could hide inverse-log-flat forcing.

The exact source formula removes that escape.

### Theorem 1

`[PROVED]` Suzuki's polar remainder satisfies

```text
r'' in C^(0,1)_loc(R).                                  (1)
```

Consequently, at every fixed aperture \(a>0\), the integral operator

```text
(K_a u)(x)=integral_(-a)^a r''(x-y)u(y)dy               (2)
```

maps

```text
L2(-a,a) -> C^(0,1)([-a,a])                            (3)
```

and

```text
||K_a u||_infinity
 +Lip(K_a u)
 <=C_a||u||_2.                                         (4)
```

### Theorem 2

`[PROVED]` Let \(x_0\in[-a,a]\), choose either orientation, and put

```text
G_(x_0,+)(L)=(K_a u)(x_0+exp(-L)),
G_(x_0,-)(L)=(K_a u)(x_0-exp(-L)).                     (5)
```

Then

```text
G_(x_0,sign)(L)=G_(x_0,sign)(infinity)+O(exp(-L)),      (6)
|G_(x_0,sign)'(L)|<=C_a||u||_2 exp(-L)                 (7)
```

for almost every sufficiently large \(L\).  Hence, for every \(0<\sigma<1\),

```text
exp(sigma L)G_(x_0,sign)' in L2(dL).                   (8)
```

The constant in `(6)` disappears after differentiating the Suzuki boundary equation.  Therefore
the complete polar convolution is a genuine Gamma-subcritical forced term.  It cannot generate or
sustain an inverse-log-flat non-\(H^1\) completed zero mode.

## 2. Exact source formula

Suzuki splits

```text
r(t)=r_0(t)+r_1(t),
r_0(t)=-4[exp(t/2)+exp(-t/2)-2],                       (9)
```

and computes, for \(t\ne0\),

```text
r_1''(t)
 =exp(-|t|/2)/[1-exp(-2|t|)]-1/[2|t|].                (10)
```

Put, for \(s>0\),

```text
h(s)=exp(-s/2)/[1-exp(-2s)]-1/(2s).                    (11)
```

The apparent pole in `(11)` is removable.  Indeed,

```text
1-exp(-2s)=2s[1-s+O(s^2)],
exp(-s/2)=1-s/2+O(s^2),
```

so

```text
exp(-s/2)/[1-exp(-2s)]
 =1/(2s)+1/4+O(s).                                     (12)
```

More structurally, define

```text
A(s)=[1-exp(-2s)]/(2s),
B(s)=exp(-s/2).                                        (13)
```

Both extend real-analytically across \(s=0\), with \(A(0)=B(0)=1\).  Thus

```text
h(s)=[B(s)/A(s)-1]/(2s)                                (14)
```

extends real-analytically to a one-sided neighborhood of zero.  In particular \(h'\) is bounded
there.

Equation `(10)` says

```text
r_1''(t)=h(|t|).                                       (15)
```

An even function of the form \(h(|t|)\), with \(h\in C^1([0,\epsilon])\), is Lipschitz:

```text
|h(|t|)-h(|s|)|
 <=||h'||_infinity ||t|-|s||
 <=||h'||_infinity |t-s|.                              (16)
```

Away from zero, `(10)` is real analytic.  The term \(r_0''\) is real analytic on the whole line.
Every compact interval can therefore be covered by the zero neighborhood and finitely many
analytic neighborhoods with bounded derivative.  This proves `(1)`. `QED`

The proof sharpens, rather than contradicts, Suzuki's \(C^2\) statement.  The possible cusp is in
the third derivative: an \(|t|\) term in \(r''\) is Lipschitz but need not be \(C^1\).

## 3. Convolution gains a literal Lipschitz modulus

Let

```text
M_a=sup_(|t|<=2a)|r''(t)|,
L_a=Lip_(|t|<=2a)(r'').                                (17)
```

Both are finite by Theorem 1.  Cauchy--Schwarz gives

```text
||u||_1<=sqrt(2a)||u||_2.                              (18)
```

Therefore

```text
|(K_a u)(x)|
 <=M_a||u||_1
 <=M_a sqrt(2a)||u||_2,                                (19)
```

and

```text
|(K_a u)(x)-(K_a u)(x')|
 <=integral |r''(x-y)-r''(x'-y)||u(y)|dy
 <=L_a|x-x'| ||u||_1
 <=L_a sqrt(2a)||u||_2 |x-x'|.                         (20)
```

Equations `(19)`--`(20)` prove `(3)`--`(4)`. `QED`

## 4. Boundary-log rate and differentiated source

Set \(x_L=x_0\pm e^{-L}\).  Equation `(20)` gives

```text
|(K_a u)(x_L)-(K_a u)(x_0)|
 <=C_a||u||_2 exp(-L),                                 (21)
```

which is `(6)`.

Every Lipschitz function is absolutely continuous on lines and has an almost-everywhere derivative
bounded by its Lipschitz constant.  The chain rule for absolutely continuous functions gives

```text
|d/dL (K_a u)(x_0+/-exp(-L))|
 <=Lip(K_a u)exp(-L),                                  (22)
```

proving `(7)`.  Finally

```text
integral_(L_0)^infinity
 |exp(sigma L)G'(L)|^2dL
 <=C_a^2||u||_2^2
   integral_(L_0)^infinity exp(-2(1-sigma)L)dL
 <infinity                                             (23)
```

for every \(0<\sigma<1\), proving `(8)`. `QED`

## 5. Literal Suzuki normal-source decomposition

The exact weak eigenfunction equation from Suzuki's `(2.5)` and `(2.11)`, in the normalization
used by the boundary normal papers, is

```text
(1/2)L_Delta u
 = [lambda+log(2pi)]u
   +sum_(n<=exp(2a)) Lambda(n)/sqrt(n)
      [u(.-log n)+u(.+log n)]
   +K_a u.                                              (24)
```

After passing to the oriented valuation carrier and differentiating in \(L=-\log r\):

- the scalar term \(\lambda+\log(2\pi)\) is a bounded self-adjoint diagonal part of \(T\);
- the finite von-Mangoldt translations are the full self-adjoint valuation adjacency;
- the literal logarithmic jump becomes \(2L+R\);
- by `(7)`--`(8)`, the polar term becomes Gamma-subcritical forcing.

Thus the source-faithful normal equation is

```text
(2L I+R-T_(a,lambda))F'+F=G_polar,                     (25)

T_(a,lambda)
 = [lambda+log(2pi)]I
   +sum_(n<=exp(2a)) Lambda(n)/sqrt(n)
      [U_(nu(n))+U_(-nu(n))],                           (26)

exp(sigma L)G_polar in L2(dL),       0<sigma<1.         (27)
```

The exact scalar coefficient in `(26)` depends on whether `(24)` or the doubled
\(L_\Delta\) convention is used; `(24)` fixes the convention displayed here.  It does not affect
root first-grade observation because \(P I\beta=0\) for exterior root trace.

Low-frequency cutoff replacement adds only the already proved two counterterms plus another
source satisfying `(27)`.  Consequently:

```text
prime breadth                     homogeneous T;
eigenvalue/scalar potential       homogeneous diagonal T;
literal Gamma jump                homogeneous R;
polar convolution                 Gamma-subcritical forcing;
low cutoff remainder              Gamma-subcritical forcing.              (28)
```

There is no remaining “bounded regular multiplier might be inverse-log-flat” escape.  The only
unclosed analytic step is constructing the actual completed zero-mode valuation normal family so
that `(25)` holds in the root-retained rigged carrier.

## 6. Exact frontier movement

Before `(1)`, the \(C^2\) source statement left the modulus of \(r''\) uncontrolled.  A continuous
kernel can have an arbitrarily slow boundary modulus, so treating it as analytic forcing would
have been invalid.  The exact formula proves the missing rate.

```text
polar source boundedness:                    [PREVIOUSLY CLOSED]
polar source boundary rate exp(-L):          [CLOSED HERE]
polar source Gamma strip 0<sigma<1:          [CLOSED HERE]
scalar/eigenvalue normal placement in T:      [CLOSED HERE]
completed-mode valuation normal intertwiner: [OPEN HARD CORE]
```

## 7. Hostile audit

1. **No \(C^2\Rightarrow C^{2,1}\) fiction.**  Lipschitz regularity comes from the exact formula
   `(10)`, not from abstract \(C^2\).
2. **No smoothness overclaim.**  \(r''\) may have an \(|t|\) cusp; only the proved Lipschitz
   property is used.
3. **No pointwise derivative premise on \(u\).**  Differentiation occurs after convolution;
   \(K_a u\) is Lipschitz for every \(u\in L^2\).
4. **No bounded-forcing shortcut.**  The explicit exponential rate `(7)` is load-bearing.
5. **No prime deletion.**  Prime shifts remain in the homogeneous carrier \(T\), not in
   \(G_{\rm polar}\).
6. **No source-carrier claim.**  Equation `(25)` is the exact normal equation once the valuation
   normal family is constructed; this theorem supplies the polar term in that construction.
7. **No RH or whole-Connes claim.**  Intertwining, weighted trace-zero return, and other producer
   classes remain open.

## 8. Novelty boundary

Lipschitz convolution estimates and removable analytic singularities are standard.  Candidate-new
source knowledge is the exact Suzuki implication

```text
displayed polar Gamma remainder
 -> r'' locally Lipschitz
 -> completed L2 polar convolution has exp(-L) normal rate
 -> no inverse-log-flat polar forcing channel.          (29)
```

Suzuki states \(r\in C^2\) and uses boundedness of the compact convolution; the source does not
record `(1)`, `(7)`, or `(29)`.  Targeted Route-O corpus search found no prior proof.  External
priority remains unverified.

## 9. Lean status

Formalized unconditionally.  Suzuki's literal polar kernel is
`RHTower.suzukiWeilRemainderKernel` (the even extension of
`-2 cosh(t/2) + e^{t/2}/(2 sinh t) - 1/(2t)`), already in the tree; this card adds its sharp
regularity and the convolution operator:

```text
formal/GaloisForLFunctions/HTGeometry/ExponentialDividedDifference.lean
formal/GaloisForLFunctions/RHTower/SuzukiPolarRemainderLipschitz.lean
formal/GaloisForLFunctions/RHTower/SuzukiPolarConvolutionRate.lean
```

The removable singularity `(11)`--`(14)` is realized by the exact identity
`suzukiPolarCore s = e^{s/2}/(2 sinh s) - 1/(2s)` for `s > 0`, where `suzukiPolarCore` is the
pole-free quotient of the two exponential divided differences
`∫₀¹ e^{tx} dt` and `∫₀¹ (1-t) e^{tx} dt`; `(1)` is
`abs_suzukiWeilRemainderKernel_sub_le`, `(3)`--`(4)` are
`abs_suzukiPolarConvolution_le` and `abs_suzukiPolarConvolution_sub_le` with the literal constants,
`(18)` is `sq_integral_abs_le`, `(6)` is `abs_suzukiPolarBoundaryTrace_sub_le`, `(7)` is
`abs_deriv_suzukiPolarBoundaryTrace_le`, and `(8)`/`(23)` is
`integrableOn_sq_expMul_deriv_suzukiPolarBoundaryTrace`.  Every theorem audits to
`[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] prove removable singularity in the exact \(r_1''\) formula
- [x] prove \(r''\in C^{0,1}_{\rm loc}\)
- [x] prove \(K_a:L^2\to C^{0,1}\)
- [x] prove exponential boundary-log rate for the differentiated polar source
- [x] place scalar/eigenvalue term inside homogeneous self-adjoint \(T\)
- [x] exclude polar inverse-log-flat forcing
- [x] formalize `(1)`, `(3)`--`(8)`, `(10)`--`(14)`, `(18)`--`(23)` unconditionally in Lean 4
- [ ] construct completed-mode valuation normal family
- [ ] prove exact cutoff intertwining for `(25)`
- [ ] close weighted trace-zero source gate
- [ ] RH or whole-program no-go

# Hedenmalm reflection fold is a rank-one Dirac source defect

- **ID:** `hedenmalm-reflection-folded-dirac-source-defect`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / EXACT OPEN-CORE REFINEMENT
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent:** Hedenmalm's theta boundary-value problem and the corpus Fourier equation
  `(alpha-z) U_alpha(z)=-i XiC(z)`.

## Question

Can functional-equation reflection be made internal before constructing Hedenmalm's missing
positive self-adjoint realization, and what defect remains after doing so?

## Setup

Put

```text
k(x)=2 VarTheta_00(i exp(2x)),
D=-i partial_x,
F(z)=hat k(z)=XiC(z).
```

For a zero `F(alpha)=0`, let `u_alpha` be the source-pointed two-ended Hedenmalm solution,
normalized by

```text
(D+alpha)u_alpha=-i k.                                   (1)
```

The evenness of `k` and `F` gives

```text
R u_alpha=-u_(-alpha),   (R f)(x)=f(-x).                 (2)
```

Define the reflection folds

```text
E_alpha=(u_alpha-u_(-alpha))/2,
O_alpha=(u_alpha+u_(-alpha))/2.                           (3)
```

Then `R E_alpha=E_alpha` and `R O_alpha=-O_alpha`.

On the Fourier side, with `D` having symbol `-z`,

```text
hat E_alpha(z)=-i alpha F(z)/(alpha^2-z^2),
hat O_alpha(z)=-i z F(z)/(alpha^2-z^2).                   (4)
```

Both quotients are entire: the apparent poles at `z=alpha` and `z=-alpha` are removed by
`F(alpha)=F(-alpha)=0`.

## Theorem: folded Dirac defect

For every Xi zero `alpha`,

```text
D E_alpha=-alpha O_alpha,
D O_alpha=-alpha E_alpha-i k.                            (5)
```

Equivalently,

```text
(D^2-alpha^2)E_alpha= i alpha k,
(D^2-alpha^2)O_alpha=-i Dk.                              (6)
```

In Fourier coordinates these are

```text
z hat E_alpha=alpha hat O_alpha,
z hat O_alpha=alpha hat E_alpha+i F,                     (7)

(z^2-alpha^2)hat E_alpha=i alpha F,
(z^2-alpha^2)hat O_alpha=i z F.                          (8)
```

### Proof

Equation `(1)` at `alpha` and `-alpha` reads

```text
D u_alpha=-alpha u_alpha-i k,
D u_(-alpha)=alpha u_(-alpha)-i k.
```

Subtracting and adding gives `(5)`. Applying `D` and substituting `(5)` gives `(6)`.

For `(2)`, Fourier reflection sends `hat u_alpha(z)` to `hat u_alpha(-z)`. Since `F` is even,

```text
hat u_alpha(-z)
 =-i F(z)/(alpha+z)
 =-hat u_(-alpha)(z).
```

Equations `(4)`, `(7)`, and `(8)` follow by elementary algebra from
`hat u_alpha(z)=-i F(z)/(alpha-z)`. QED.

## What this changes

The original first-order presentation makes reflection look like a requested identification
between two different eigenmodes. The fold proves that no such identification is missing.
Reflection is already internal in one parity-graded source system. The unresolved datum is the
single affine source term `-i k` in the even equation of `(5)`.

Thus the positive self-adjoint problem is not

```text
identify alpha with -alpha,
```

but

```text
dilate the rank-one affine Dirac defect k to a source-defined self-adjoint system
whose source-pointed two-ended modes remain faithful.     (9)
```

This also explains why merely squaring the spectral parameter does not solve the problem:
`D^2-alpha^2` is self-adjoint in the ordinary ambient `L^2`, but `(6)` is a forced resolvent
equation, not an eigenvalue equation.

## Exact finite-dilation obstruction

Consider the most direct one-channel Hilbert dilation on `L^2(R) direct_sum C`,

```text
A_g,a = [ -D   g  ]
        [ g*   a  ],                                     (10)
```

where `a` is real and `g` is the source coupling. It is self-adjoint on the standard rank-one
extension domain. Eliminating the scalar channel at a nonreal spectral parameter `alpha` gives
the characteristic equation

```text
a-alpha-<g,(-D-alpha)^(-1)g>=0.                           (11)
```

The last term is a Herglotz/Nevanlinna Cauchy transform of the positive measure
`|hat g(x)|^2 dx`. Consequently every eigenvalue of `(10)` is real, as it must be.

Taking the literal theta coupling `g=-i k` does **not** turn `(11)` into `XiC(alpha)=0`.
Its characteristic function is the Cauchy transform of `|XiC(x)|^2 dx`, whereas Hedenmalm's
two-ended compatibility function is the unsquared Fourier--Laplace transform `XiC(alpha)`.
No theta identity in the corpus identifies these functions, and such an identity would impose a
new nonlinear equation on Xi.

Therefore a finite rank-one Friedrichs dilation is not the missing realization. Any valid
dilation must contain an infinite source bath or a singular boundary relation whose Weyl
function is the **unsquared** Euler--Poisson--Gamma transfer, not the ordinary positive
`|Xi|^2` Cauchy response.

## Causal/anti-causal coincidence interpretation

For arbitrary `alpha` off the real axis, the free resolvent of `D` supplies an `L^2` solution of
the inhomogeneous equation `(1)`. Hedenmalm's distinguished left-Volterra solution and the
right-Volterra solution differ by

```text
XiC(alpha) exp(-i alpha x).                               (12)
```

Hence a Xi zero is exactly a coincidence of the source-pointed causal and anti-causal inverses.
The free momentum and free Helmholtz operators are already self-adjoint; their self-adjointness
does not force such coincidences to occur on their spectrum. The missing theorem must say that
the **ordinary-integer completed source**, unlike a generic Schwartz source, makes every
two-ended coincidence spectrally conservative.

This is a strictly more concrete open core than “find a positive metric”:

> Construct a singular infinite source dilation of `(5)` whose boundary Weyl transfer is the
> literal unsquared Euler--Poisson--Gamma function `XiC`, and prove that causal/anti-causal
> coincidence vectors are nonzero Hilbert eigenvectors of the dilation.

If such a dilation is self-adjoint, its folded eigenvalue is `alpha^2`. Since Xi has no zero on
the centered imaginary segment corresponding to real `0<s<1`, reality of `alpha^2` forces
`alpha` real and proves RH.

## Hostile audit

1. Equations `(5)`--`(8)` are unconditional but do not make `alpha` real.
2. Ordinary free-resolvent self-adjointness is irrelevant: every nonreal parameter has a forced
   resolvent response.
3. Adding one scalar source channel replaces Xi by a positive Cauchy transform and therefore does
   not preserve the Hedenmalm characteristic function.
4. Declaring the required singular Weyl function to be Xi is target-fed unless it is derived from
   the integer Euler product, Poisson summation, and Gamma completion before zero specialization.
5. Positivity of a divisor-supported metric is still RH. The point of this theorem is to expose
   the exact one-way source defect that a genuine construction must dilate.
6. The result does not claim novelty until searches cover Hedenmalm's paper, rank-one momentum
   restrictions, Friedrichs models, nonradiating-source transmission problems, and singular
   canonical systems.

## Lean target

Formalize the entire Fourier-side fold:

```text
xiHedenmalmEvenFold
xiHedenmalmOddFold
xiHedenmalmEvenFold_equation
xiHedenmalmOddFold_equation
xiHedenmalmEvenFold_quadratic
xiHedenmalmOddFold_quadratic
```

using the existing unconditional equation
`xiThetaEigenFourier_equation` and `XiC_even`. The operator-dilation obstruction remains a paper
theorem until the project has an unbounded self-adjoint block-operator API.


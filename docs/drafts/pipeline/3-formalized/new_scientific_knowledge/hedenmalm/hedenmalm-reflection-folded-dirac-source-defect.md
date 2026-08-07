# Hedenmalm reflection fold is a rank-one Dirac source defect

- **ID:** `hedenmalm-reflection-folded-dirac-source-defect`
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT OPEN-CORE REFINEMENT
- **Scientific status:** `[PROVED HERE] [LEAN FORMALIZED] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Formalized companion:** `hedenmalm-reflection-folded-dirac-source-defect-formalized.md`
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

## Theorem: each parity channel retains the first conormal

The centered origin is not a Xi zero.  Hence, at any zero `alpha`, the reflected point
`-alpha` is distinct from `alpha`.  Evaluation of `(3)` at the base divisor point gives

```text
hat E_alpha(alpha)=hat O_alpha(alpha)
  = i XiC'(alpha)/2.                                    (4a)
```

Indeed, the based quotient has removable value `i XiC'(alpha)`, while the quotient based at
`-alpha` vanishes at the distinct zero `alpha`.  Consequently, if `alpha` is simple, both the
even and odd folds are separately nonzero and each retains exactly half of the first Xi conormal.
Reflection folding therefore does not pay for internal reflection by erasing the local divisor
normal.

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

## Minimal invariant homogenization

There is one algebraic way to remove the affine term without adding a channel.  Let

```text
C_k=span{D^n k:n>=0}.
```

This is the least `D`-invariant subspace containing `k`.  On the algebraic quotient by `C_k`, the
two equations `(5)` become the homogeneous Dirac eigenproblem

```text
D [E_alpha]=-alpha [O_alpha],
D [O_alpha]=-alpha [E_alpha].                            (9a)
```

No smaller quotient can both annihilate `k` and carry a descended `D`: invariance forces it to
annihilate every `D^n k`.  On the Fourier side this is the quotient by the polynomial module

```text
XiC(z) C[z].
```

The Hedenmalm divided quotient is not in that module.  At a zero of multiplicity `m`, it has
vanishing order exactly `m-1`, whereas every polynomial multiple of `XiC` has order at least `m`.
Thus the algebraic quotient retains every divisor mode and every multiplicity-first conormal.

This quotient is the exact algebraic skeleton of a self-adjoint realization, but not its Hilbert
completion.  Since the real translates of `k` are cyclic in ordinary `L^2`, the ordinary Hilbert
closure of `C_k` is the whole ambient space.  Hence its ordinary `L^2` quotient is zero.  Any
Hausdorff completion retaining `(9a)` must be discontinuous relative to ordinary `L^2`; the
essential singularity is forced before positivity is discussed.

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

## Collision with the prime-tail conormal chart

The later source theorem
`prime-tail-reflection-folded-second-order-resolvent.md` constructs, from the literal
ordinary-integer prime-power forcing before zero specialization, the reflection-folded monodromy
modes

```text
2 pi i m_rho cosh(lambda_rho L),
2 pi i m_rho sinh(lambda_rho L)/lambda_rho,
lambda_rho=rho-1/2.                                     (13)
```

They are nonzero homogeneous solutions of

```text
(partial_L^2-lambda_rho^2)u=0
```

with source-fixed Neumann/Dirichlet Cauchy data.  Equations `(4a)` and `(13)` now give two
unconditional charts of the same divisor conormal:

```text
theta chart:       all-orders-flat forced mode retaining XiC'(alpha);
prime-tail chart:  homogeneous indicial mode retaining m_rho.
```

This removes “produce the conormal,” “make reflection internal,” and “retain multiplicity” from
the open list.  The exact missing map is a source-defined boundary transgression from the
prime-tail indicial chart to the Hedenmalm flat quotient which:

1. is nonzero on every conormal before zero specialization;
2. intertwines the folded second-order generators;
3. commutes with source reflection as Hilbert adjunction;
4. is invariant under every nonreal resolvent of one self-adjoint realization.

If such a map exists, the prime-tail mode is a nonzero transpose eigenfunctional of a
self-adjoint operator.  Nonreal resolvent surjectivity forces its eigenvalue
`lambda_rho^2` to be real, and the open critical strip then forces `Re rho=1/2`.

The corpus rules out all currently explicit regular candidates for this map:

- ordinary `L^2` closure kills the cyclic quotient;
- analytic compactification cannot isolate one accumulating theta heat node;
- every fixed finite-Rees map preserves the all-orders-flat radical and cannot sew it to the
  half-normal reflected sector;
- the explicit smooth essential-phase Sonin corona is nonzero and partially unitary, but every
  fixed Mellin/Xi conormal is all-orders invisible there.

Therefore “infinite rank” is no longer an adequate description.  The unresolved object must mix
the nonsmooth ordinary-prime jump face with the theta flat face through an essential-singular,
resolvent-stable boundary operation.  No such operation is constructed here.

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

## Lean status

The entire Fourier-side fold and first-conormal retention are formalized in
`formal/GaloisForLFunctions/RHTower/XiHedenmalmReflectionFoldedDirac.lean`:

```text
xiHedenmalmEvenFold
xiHedenmalmOddFold
xiHedenmalmEvenFold_equation
xiHedenmalmOddFold_equation
xiHedenmalmEvenFold_quadratic
xiHedenmalmOddFold_quadratic
xiHedenmalmEvenFold_self
xiHedenmalmOddFold_self
xiHedenmalmFolds_self_ne_zero_of_deriv_ne_zero
xiHedenmalmEvenFold_ne_zero
```

The proofs use the existing unconditional equation `xiThetaEigenFourier_equation`, Xi evenness,
and the multiplicity-sensitive removable-quotient laws.  The operator-dilation obstruction and
the prime-tail/Hedenmalm transgression remain paper-level because no such positive source
operation is known; an abstract unbounded-operator API would not supply it.

The **minimal invariant homogenization** theorem is formalized in
`formal/GaloisForLFunctions/RHTower/XiHedenmalmInvariantHomogenization.lean`:

```text
xiThetaEigenFourier_notMem_xiPolynomialModule
  : the Hedenmalm removable quotient at a Xi divisor point is never a polynomial multiple of XiC.
```

So the quotient by the least differentiation-invariant subspace containing the theta source is
faithful on the divisor: it retains every divisor mode.  The companion minimality theorem
`eval_mul_XiC_mem_of_coordinateMultiplication_stable` proves the other half of the card's claim ---
any subspace containing `XiC` and stable under multiplication by the spectral coordinate already
contains every polynomial multiple of `XiC`, so `XiC(z) C[z]` really is the least such subspace and
no smaller quotient can both annihilate the source and carry a descended generator.  The proof needs no case split on the
multiplicity.  `xiThetaEigenFourier alpha = i * xiThetaDividedChain alpha 1` holds definitionally
and `xiThetaDividedChain_partial_factorization` gives `XiC z = (z-alpha) Q z` directly, so assuming
`i Q z = P(z) XiC z` and cancelling `Q z` --- nonzero on a punctured neighbourhood of `alpha`,
because `XiC z = (z-alpha)^m C z` with `C(alpha) != 0` --- leaves `i = P(z)(z-alpha)` near `alpha`,
and continuity at `alpha` forces `i = 0`.

The **exact finite-dilation obstruction** `(10)`--`(11)` is formalized in
`formal/GaloisForLFunctions/RHTower/HedenmalmRankOneDilationObstruction.lean`:

```text
rankOneDilationCharacteristic a mu z = a - z - C[mu](z)
im_rankOneDilationCharacteristic_neg
  : its imaginary part is strictly negative above the real axis;
rankOneDilationCharacteristic_ne_zero
  : hence every eigenvalue of the rank-one dilation is real;
XiC_ne_zero_of_rankOneDilationCharacteristic_eq
  : if a rank-one characteristic function agrees with XiC above the axis, XiC has no zero there;
not_forall_rankOneDilationCharacteristic_eq_XiC
  : a single off-axis Xi zero obstructs every such identification.
```

The Lean form makes the hostile-audit point 3 exact and unconditional: the rank-one ansatz is
*equivalent* to the zero-free upper half plane, so it re-encodes the missing statement rather than
supplying it.  Passivity needs no operator theory --- only that the Cauchy transform of a positive
finite measure is Herglotz, which the corpus already owns as
`im_cauchyTransform_pos_of_ne_zero`; the zero-measure case is separate because that lemma needs a
nonzero measure.

The **causal/anti-causal coincidence** `(12)` is formalized in
`formal/GaloisForLFunctions/RHTower/HedenmalmTwoEndedVolterraDefect.lean`:

```text
hedenmalmCausalVolterra, hedenmalmAntiCausalVolterra
hedenmalmCausalVolterra_sub_antiCausal
  : the two source-pointed one-sided inverses differ by -i exp(-i alpha x) XiC(alpha);
hedenmalmCausalVolterra_eq_antiCausal_iff
  : they coincide identically exactly when XiC(alpha) = 0.
```

Both hold on the strip `|im alpha| < 1`, which contains the whole centered critical strip.  No
operator theory is needed: the difference of the two one-sided integrals is the full-line
Fourier--Laplace integral of the theta cusp source, and the corpus already identifies that with
`XiC` on the same strip (`thetaCuspFourierLaplace_eq_XiC_on_strip`).  The exponential decay that
makes both one-sided integrals converge for complex `alpha` comes from the tilted theta source
layer, not from Schwartz decay, which would not suffice off the real axis.

The **reality step** cited for the folded second-order realization is formalized in
`formal/GaloisForLFunctions/RHTower/XiRealAxisNonvanishing.lean`:

```text
xi_ne_zero_of_real            : xi has no zero on the real axis;
XiC_ne_zero_of_imaginary      : the centered xi has no purely imaginary zero;
XiC_im_eq_zero_of_sq_im_eq_zero
  : a centered Xi zero whose square is real is itself real.
```

The card only needed the segment corresponding to real `0 < s < 1`, but the same argument covers
the whole axis: on `(0,1)` the fractional-part representation of zeta has a strictly positive
integrand, to the right of `1` the Euler product is nonvanishing, `xi 1 = 1/2`, and the reflection
`xi (1 - s) = xi s` transports both to the left half.  So the last step of the dilation argument ---
reality of the folded eigenvalue `alpha^2` forcing `alpha` real --- is unconditional; what remains
missing is only the self-adjoint realization that would make `alpha^2` real.

### Status of the ordinary-`L^2` quotient remark

The remark that the ordinary Hilbert closure of `C_k` is the whole ambient space, so its ordinary
`L^2` quotient is zero, is **not** yet formalized, and its stated justification has a soft step: it
argues from cyclicity of the real *translates* of `k`, but `C_k` is the span of the *derivatives*.
Derivatives are limits of difference quotients of translates, so the derivative span sits inside the
closed translate span; the reverse inclusion does not follow in general.

The Fourier-side form is the true statement and is a determinacy question: polynomials must be dense
in `L^2(|XiC|^2 dt)` on the real axis.  That needs exponential decay of `XiC` along the real axis,
which the corpus does not yet own --- the available bound
`norm_XiC_le_exp_of_summable` grows, and the Fourier--Laplace layer only gives boundedness on
horizontal substrips.  Sharp decay would follow from analyticity of the theta source in the strip
`|im x| < pi/4`, which is where `i exp(2x)` leaves the upper half plane.

The finiteness half of that argument is now in
`formal/GaloisForLFunctions/RHTower/XiCSchwartzRestriction.lean`:

```text
xiCSchwartz                 : the real restriction of XiC as a Schwartz function;
memLp_pow_mul_XiC_ofReal    : every polynomial weight of it is square integrable;
integrable_mul_pow_mul_XiC  : every polynomial moment against an L^2 function converges absolutely.
```

so all the moment integrals in the determinacy argument are defined.  What is missing is only the
analytic input that makes their vanishing propagate.

The first layer of that analytic input is now built in
`formal/GaloisForLFunctions/RHTower/ThetaCuspComplexStrip.lean`:

```text
thetaCuspComplexSeed, thetaCuspComplexTerm  : the entire complexifications;
norm_exp_neg_pi_sq
  : the Gaussian factor has modulus exp (-pi n^2 exp (2 re z) cos (2 im z));
norm_thetaCuspComplexTerm_le
  : a uniform Gaussian majorant on every closed substrip of |im z| < pi/4 with bounded real part;
thetaCuspStripSource, summable_thetaCuspComplexTerm
  : the complexified series converges absolutely on the strip;
thetaCuspStripSource_ofReal
  : it restricts to the real theta-cusp source on the real axis;
differentiableAt_thetaCuspStripSource, analyticOnNhd_thetaCuspStripSource
  : **it is holomorphic on the whole strip** (Weierstrass, from the uniform majorant);
thetaCuspStripSource_neg
  : it is even on the strip, by the identity theorem from evenness on the real axis;
norm_thetaCuspComplexTerm_le_pointwise
  : the sharp pointwise term bound, keeping the actual real part in the Gaussian;
exists_norm_thetaCuspStripSource_le_of_nonneg, exists_norm_thetaCuspStripSource_le
  : **uniform two-sided decay**, `||K z|| <= C_delta exp (-|re z|)` on each closed substrip;
integrable_thetaCuspStripSource_horizontal
  : **absolute integrability along every horizontal line of the strip**;
thetaStripFourierIntegrand, norm_thetaStripFourierIntegrand
  : the Fourier--Laplace integrand and its modulus `exp (t im w) ||K w||`;
differentiableAt_thetaStripFourierIntegrand,
integrable_thetaStripFourierIntegrand_horizontal
  : it is holomorphic on the strip and integrable on every horizontal line there;
integral_thetaStripFourierIntegrand_shift
  : the full-line integral does not depend on the height inside the strip (the contour shift);
exists_norm_XiC_ofReal_le
  : **exponential decay of the centered xi function on the real axis**,
    `||XiC t|| <= C_delta exp (-delta |t|)` for every `delta < pi/4`;
volume_xiCRealZeroSet, XiC_ofReal_ne_zero_ae
  : the real zero set of the centered xi function is **null**.
```

The zero set is null because on each `[-n,n]` it is finite: an infinite subset of a compact set has
an accumulation point, and an accumulation point of zeros forces `XiC` to vanish identically by the
identity theorem, contradicting `XiC_zero_ne`.  Mathlib has no lemma that the zero set of a nonzero
analytic function is countable, so this is built from
`Set.Infinite.exists_accPt_of_subset_isCompact` plus the transfer of the accumulation from the real
line into the plane along `ofReal`.

The strip `|im z| < pi/4` is exactly where `i exp (2 z)` stays in the upper half plane, so it is the
natural analyticity domain of the theta source in logarithmic coordinates, and `cos (2 im z) > 0`
there is precisely what keeps the Gaussian factor decaying.  Strip analyticity of the source is therefore done.  Evenness is recorded because the termwise
Gaussian majorant is **not** enough on its own for the contour shift: summed over the index it grows
like `exp (-x/2)` as `x -> -infinity`, so it does not give integrability of the shifted source on a
whole horizontal line.  The real source decays at both ends only through the modular reflection, and
evenness on the strip is what transports the `+infinity` decay to `-infinity` for the complexified
source.

The right-hand decay is proved by splitting the Gaussian exponent: for `n >= 1` and `re z >= 0`,
`n^2 exp(2 re z) >= exp(2 re z)/2 + n^2/2`, so half the Gaussian is spent on the index and half on
the real part.  The index half sums to a finite Gaussian moment; the real-part half is
`exp(-(c/2) exp(2 re z))`, which beats every polynomial weight through `s^3/3! <= exp s`.  Reflecting
by `thetaCuspStripSource_neg` gives the same bound to the left.

The shift itself is done, and no new Cauchy theory was needed: the corpus already owned the
Cauchy-rectangle machinery for **vertical** contours in
`GaloisForLFunctions/HTGeometry/VerticalContourShift.lean`
(`integral_vertical_line_eq_of_horizontal_tendsto`), and the rotation `w |-> -i w` carries a
horizontal shift to a vertical one --- it sends `re` to `im` and `im` to `-re`, so the strip
`|im z| < pi/4` becomes a vertical strip and horizontal-line integrals become vertical-line
integrals, while the vertical edges of the rotated rectangle are the horizontal ones of the
original and vanish by the two-sided decay bound.

The decay is therefore **proved**, for every `delta < pi/4`, which is the classical
`Xi(t) = O(exp(-pi|t|/4))` up to the constant.  The final step needed only the modulus identity
`||exp(-i t w) K w|| = exp (t im w) ||K w||`: evaluating the height-independent integral at height
`delta` gives the factor `exp (t delta)`, which is `exp (-delta |t|)` for `t <= 0`, and evenness of
`XiC` covers `t > 0`.  So the shift is used at a *single* fixed height, not a `t`-dependent one.

This closes the analytic input the `L^2` quotient remark was missing, and the last step of that
remark --- passing from `conj(f) XiC = 0` almost everywhere to `f = 0` almost everywhere --- is now
also available.  The weighted integrability the determinacy argument runs on is also built
(`memLp_two_exp_neg_mul_abs`, `integrable_memLp_mul_XiC_mul_expWeight`): for an `L^2` function `f`
and any weight strictly below the decay rate, `||f|| exp(-delta|x|) exp(a|x|)` is integrable, by
Cauchy--Schwarz against the `L^2` exponential.

Two corpus assets found while building this, which shorten what is left:

- `RHTower/BoundedSupportFourierUncertainty.lean` already proves Fourier injectivity for integrable
  functions (`integrable_ae_eq_zero_of_fourier_eq_zero`), which is the last step of the argument;
- `RHTower/WeightedEulerStripFourierAnalytic.lean` already builds the complexified Fourier transform
  `Phi(w) = integral g(x) exp(-i w x)` and proves it analytic on a horizontal strip --- but only for
  *entire* `g` with a two-ray Phragmen--Lindelof bound, so it does not apply directly to
  `g = f XiC` with `f` merely square integrable.  Its auxiliary integrability lemmas are reused.

The analyticity for a non-entire `g` is now built, in
`formal/GaloisForLFunctions/RHTower/ExpDecayFourierAnalytic.lean`:

```text
expFourier g w = integral g(x) exp(-i w x)
integrable_expFourier_kernel, hasDerivAt_expFourier, analyticOnNhd_expFourier
```

for a **merely measurable** `g : R -> C` dominated by `K exp(-eps|x|)`, analytic on `|im w| < eps`.
This is the corpus's `stripFourier` layer with the hypothesis weakened to what its proof actually
uses: entirety of `g` entered only through continuity, and continuity only through the three
measurability side conditions of differentiation under the integral.  The weaker form is what a
product of an analytic decaying factor with a merely square-integrable factor needs.

The power-series step is now under construction in the same module:

```text
pow_abs_mul_exp_neg_le        : |x|^n exp(-a|x|) <= (2/a)^n n! exp(-(a/2)|x|);
integrable_expDecay_mul_pow   : every moment integrand of an exponentially decaying g is integrable;
expFourierSeriesTerm          : the n-th term of the exponential series against g;
integral_expFourierSeriesTerm_eq_zero : each term integrates to zero, given vanishing moments;
hasSum_expFourierSeriesTerm   : the terms sum pointwise to g(x) exp(-i w x).
```

The factorial bound is what keeps the term-by-term estimate elementary: writing
`|x|^n exp(-a|x|)` as `(2/a)^n ((a/2)|x|)^n exp(-(a/2)|x|) exp(-(a/2)|x|)` and using
`s^n / n! <= exp s` bounds the middle factor by `n!`, so the sum of the term norms is dominated by a
geometric series in `2|w|/a` --- convergent exactly on the disc `|w| < a/2`, which is all the
identity theorem needs.

These are now assembled:

```text
integral_norm_expFourierSeriesTerm_le
  : the term norms integrate to at most K A (2||w||/eps)^n;
expFourier_eq_zero_of_moments
  : **the transform vanishes on the disc ||w|| < eps/2**.
```

and the determinacy theorem itself is proved:

```text
ae_eq_zero_of_moments_eq_zero
  : an exponentially decaying function all of whose polynomial moments vanish is zero a.e.
```

The disc vanishing propagates to the strip by the identity theorem (the strip is convex, hence
preconnected), and on the real axis the strip transform is the ordinary Fourier transform after the
substitution `t = 2 pi w`, so the corpus's Fourier injectivity applies.

Specialising it to `g = f XiC` needed one correction, worth recording.  A *pointwise* exponential
bound on `g` is **false** for `f` merely square integrable: `||f x||` is unbounded.  What the whole
argument actually consumes is only the weighted integrability

```text
ExpWeightIntegrable g eps  :  for every |a| < eps, ||g x|| exp(a|x|) is integrable,
```

which holds both for a pointwise bound (`expWeightIntegrable_of_bound`) and for `f XiC` with `f` in
`L^2`, by Cauchy--Schwarz against the `L^2` exponential.  That hypothesis is now built, together
with `integrable_abs_mul_of_expWeightIntegrable` --- the `|x|` weight of the derivative estimate is
absorbed by an arbitrarily small exponential gain, since `|x| <= (1/c) exp(c|x|)`.

The strip lemmas are now restated on it:

```text
integrable_expFourier_kernel', hasDerivAt_expFourier', analyticOnNhd_expFourier'
pow_abs_le_factorial_mul_exp : |x|^n <= (2/a)^n n! exp((a/2)|x|)
```

The primed proofs are shorter than the originals: with the weighted hypothesis there is no constant
`K` to carry and no splitting of the decay rate, since the majorant is supplied directly by the
hypothesis at a slightly larger weight.

and so is the whole determinacy argument:

```text
integrable_expDecay_mul_pow', integrable_expFourierSeriesTerm',
integral_norm_expFourierSeriesTerm_le', expFourier_eq_zero_of_moments'
ae_eq_zero_of_moments_eq_zero'
  : **a function with exponentially weighted integrability and all polynomial moments zero is zero
    almost everywhere.**
```

and the specialisation is done, in
`formal/GaloisForLFunctions/RHTower/XiPolynomialDensity.lean`:

```text
expWeightIntegrable_memLp_mul_XiC
ae_eq_zero_of_orthogonal_polynomial_XiC
  : **a square-integrable function orthogonal to every polynomial multiple of the real restriction
    of XiC vanishes almost everywhere.**
```

That is the Fourier-side form of the remark: the closed span of `XiC(z) C[z]` in ordinary `L^2` is
everything, so its ordinary `L^2` quotient is zero, and any Hausdorff completion retaining the
homogeneous folded system `(9a)` must be discontinuous relative to ordinary `L^2`.

## Formalization gates

- [x] Fourier-side reflection fold and the parity-graded first-order system `(5)`--`(8)` in Lean
- [x] first-conormal retention `(4a)` in Lean, with the simple-zero nonvanishing
- [x] minimal invariant homogenization: `XiC(z) C[z]` is the least coordinate-invariant subspace
      containing `XiC`, and the divided quotient is not in it
- [x] the exact finite rank-one dilation obstruction `(10)`--`(11)`: passivity, reality of every
      eigenvalue, and the equivalence of the ansatz with the zero-free upper half plane
- [ ] the singular *infinite* source dilation with unsquared Weyl transfer `XiC` (paper-level open
      core --- ruled out at finite rank one by the theorem above)
- [x] the causal/anti-causal coincidence `(12)` on the strip `|im alpha| < 1`
- [x] the reality step: `xi` has no real zero, so a centered zero with real square is real
- [x] the ordinary-`L^2` quotient remark, in its Fourier-side form: polynomial multiples of `XiC`
      have dense span in `L^2`, so the ordinary `L^2` quotient of the source module is zero
- [ ] the prime-tail/Hedenmalm boundary transgression (paper-level open core)
- [ ] independent specialist novelty audit

## 2026-07-31 refinement: the regular transgression is explicit

The claim above that the exact prime-tail/Hedenmalm map is wholly missing is now too coarse.
`prime-tail-hedenmalm-wiener-hopf-transgression.md` constructs the source-defined bounded maps

```text
T_-f(x)=integral_0^infinity k(x-L)f(L)dL,
T_+f(x)=integral_0^infinity k(x+L)f(L)dL.
```

For `lambda=rho-1/2=i alpha` and `Re lambda>0`, their even/odd folds send
`exp(-lambda L)` exactly to `(E_alpha,O_alpha)`.  Their endpoint trace is precisely the affine
theta defect in `(5)`.

What remains missing is not the regular transgression but its singular boundary-cohomology lift.
Ordinary `L^2` admits the decaying exponential for hypothetical right off-line zeros and excludes
the oscillatory critical-line input.  The required completion must reverse that bulk--boundary
polarity: kill regular resolvent primitives, retain tempered threshold classes, and prove from
the ordinary-integer source that every Xi conormal lands nontrivially.  That nonannihilation
statement, not construction of another formal differential operator, is the RH-bearing core.

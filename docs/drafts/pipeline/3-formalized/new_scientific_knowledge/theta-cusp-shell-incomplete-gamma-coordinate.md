# Theta-cusp shell incomplete-Gamma coordinate

- **Stage:** 3-formalized
- **Type:** theorem / exact nonperturbative coordinate
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaCuspShellIncompleteGammaCoordinate.lean`

## Statement

For every positive theta shell `n`, set

```text
t = n^2 exp(2x),
x_n(t) = (1/2) log(t/n^2).
```

For every continuous complex kernel `P` whose shell product is integrable, Lean proves the exact
pushforward

```text
integral_(0,infinity) phi_n(x) P(x) dx
  = integral_(n^2,infinity)
      A_n(t) P(x_n(t)) dt,                              (1)
```

where

```text
A_n(t)
  = pi exp(log(t/n^2)/4) (2 pi t - 3) exp(-pi t).        (2)
```

For the spectral phase `P(x)=exp(ixz)`, shell dependence separates exactly:

```text
A_n(t) exp(i x_n(t) z)
  = exp(-log(n)/2) exp(-i log(n) z)
      * U_z(t),                                         (3)

U_z(t)
  = pi exp(log(t)/4) (2 pi t - 3) exp(-pi t)
      * exp(i (log(t)/2) z).
```

Consequently, for `-1 < Im z`,

```text
thetaCuspShellHalfLineTransform(exp(i·z), n)
  = exp(-log(n)/2) exp(-i log(n) z)
      * integral_(n^2,infinity) U_z(t) dt.               (4)
```

The tail is universal; only its lower cut and Dirichlet prefactor depend on the shell.

On product fibre `mn=k`, the two lower cuts satisfy

```text
m^2 n^2 = k^2.                                          (5)
```

The universal amplitude is strictly positive for `t>=1`. Exact norm laws are

```text
|U_z(t)|
  = A_*(t) exp(-(log(t)/2) Im z),

|exp(-log(n)/2) exp(-i log(n) z)|
  = exp((Im z - 1/2) log n).                             (6)
```

Both are independent of `Re z`.

The source polynomial admits an exact integrated recurrence. If

```text
G_z(t) = exp(log(t)/4) exp(-pi t) exp(i(log(t)/2)z),
H_z(N) = integral_(N,infinity) G_z(t) dt,
```

then

```text
integral_(N,infinity) U_z(t) dt
  = 2 pi N G_z(N) + pi(iz-1/2) H_z(N).                 (7)
```

At the shell cut `N=n^2`, multiplication by the shell prefactor cancels both Mellin amplitude
and phase:

```text
exp(-log(n)/2) exp(-i log(n)z) * n^2 G_z(n^2)
  = n^2 exp(-pi n^2).                                  (8)
```

Thus one positive branch has the exact form

```text
shell_n(z)
  = 2 pi n^2 exp(-pi n^2)
    + pi(iz-1/2) R_n(z),                                (9)
```

where `R_n` is one base incomplete-Gamma remainder. Lean also proves the uniform bound

```text
|R_n(z)|
  <= exp((Im z-1/2)log n) * exp(-2n^2)/2,              (10)
```

for `|Im z|<1`. This bound is independent of `Re z`.

Spectral differentiation is exact. With

```text
H'_z(N) = integral_(N,infinity) i*log(t)/2 * G_z(t) dt,
```

Lean proves

```text
d H_z(N) / dz = H'_z(N),                               (11)
R'_n(z)
  = exp(-log(n)/2) exp(-i log(n)z)
      * (H'_z(n^2) - i log(n) H_z(n^2)).               (12)
```

Logarithms in `(12)` combine pointwise into intrinsic shell coordinate
`i log(t/n^2)/2`. For existing even-shell value `V_n` and existing shell spectral derivative
`D_n`, Lean proves both `D_n=V'_n` and

```text
D_n(z)
  = pi [i R_n(z) + (iz-1/2) R'_n(z)]
    - pi [i R_n(-z) + (i(-z)-1/2) R'_n(-z)].           (13)
```

Thus every ordered term of already-formalized actual Hedenmalm current is now written exactly in
Gamma remainder coordinate.

The same recurrence identifies the remainder with a positive Ward-density transform:

```text
W_n(z)
  = integral_(0,infinity)
      thetaCuspWardGibbsAtom(n,x) exp(ixz) dx,
R_n(z) = 2 W_n(z),                                     (14)
```

where the second identity holds in the critical strip away from the noncritical zero of
`iz-1/2`. For `z=b-ia`, define

```text
f_(a,n)(x) = exp(ax) thetaCuspWardGibbsAtom(n,x).
```

Its logarithmic derivative is exact:

```text
f'_(a,n)(x)
  = (a+5/2-2 pi n^2 exp(2x)) f_(a,n)(x).               (15)
```

For `a<1/2`, positive `n`, and `x>=0`, the score in `(15)` is strictly negative. A weighted
integration by parts then proves, for `b>0`,

```text
b integral_(0,infinity) f_(a,n)(x) sin(bx) dx
  = integral_(0,infinity) (-f'_(a,n)(x))(1-cos(bx)) dx > 0.
```

Together with `(14)`, this gives the uniform sector law

```text
Im R_n(b-ia) > 0                                       (16)
```

for every `0<a<1/2`, `b>0`, and positive shell `n`.

This sector law extends holomorphically after the shift
`u=b+i(1/2-a)`: the map `u ↦ R_n(u-i/2)` sends its first-quadrant neighborhood into the upper
half-plane. A centered Cayley transform followed by Schwarz lemma yields

```text
(1/2-a) |R'_n(b-ia)| <= 2 Im R_n(b-ia),               (17)
```

provided `b>1/2-a`. Hence `(17)` holds automatically for every positive shell in unresolved
Hedenmalm region `b>218/25`.

Exact normalized curvature is

```text
f''_(a,n)(x) / f_(a,n)(x)
  = (a+5/2-2 pi n^2 exp(2x))^2
      -4 pi n^2 exp(2x).                               (18)
```

Lean proves `(18)` is strictly positive whenever `a<1/2`, `x>=0`, and `n>=2`; hence every
higher-shell tilted Ward density is strictly convex on positive half-line. Only ground shell
`n=1` can carry a curvature defect.

Two half-line integrations by parts then give

```text
b^2 integral_(0,infinity) f_(a,n)(x) cos(bx) dx
  = integral_(0,infinity) f''_(a,n)(x)(1-cos(bx)) dx > 0       (19)
```

for `b>0` and `n>=2`. Combining `(14)`, `(16)`, and `(19)` proves

```text
Re R_n(b-ia) > 0,   Im R_n(b-ia) > 0                          (20)
```

throughout the critical aperture for every higher shell.

The first spectral moment admits an exact third-order identity for every positive shell. Define

```text
K3(u) = u(2+cos u)-3 sin u.
```

Lean proves

```text
K3(u)>0                                                     (u>0),  (21)

b^4 integral_(0,infinity) x f_(a,n)(x) sin(bx) dx
  = -integral_(0,infinity) f'''_(a,n)(x) K3(bx) dx.                (22)
```

For `n>=2`, exact score algebra gives `f'''_(a,n)<0` on `x>=0`; therefore

```text
Re R'_n(b-ia)<0                                             (n>=2). (23)
```

The reflected higher-shell derivative has positive real part. Together with `(20)`, Lean proves
the six-component cone

```text
Re R_n(z)>0,  Im R_n(z)>0,  Re R'_n(z)<0,
Re R_n(-z)>0, Im R_n(-z)<0, Re R'_n(-z)>0.                        (24)
```

For every positive shell, including ground shell, `f'''_(a,n)<0` once `x>=1/2`. Lean proves the
exact split

```text
b^4 integral x f_(a,n)(x) sin(bx) dx
  = integral_(0,1/2] -f'''_(a,n)(x)K3(bx) dx
    + integral_(1/2,infinity) -f'''_(a,n)(x)K3(bx) dx,             (25)
```

and proves second term is strictly positive. Independently, derivative-rotation density is
strictly positive after `x=1/3`, with an exact compact-head split there.

## Proof

The derivative of `t=n^2 exp(2x)` is `2t`. Dividing the source shell by this Jacobian and using

```text
(n exp(x_n(t)))^2 = t
```

gives `(2)`. A monotone vector-valued change-of-variables theorem supplies `(1)` without a
conditional integral interchange. The logarithmic identity

```text
x_n(t) = log(t)/2 - log(n)
```

and additivity of the spectral phase prove `(3)`. The corpus exponential-tilt integrability
theorem proves `(4)` throughout the required strip. Cast arithmetic gives `(5)`. Positivity and
the phase norm identity give `(6)`.

Differentiating `tG_z(t)` gives the source polynomial as a total derivative plus
`pi(iz-1/2)G_z(t)`. Absolute Gamma integrability and exponential decay justify integration over
the half-line, proving `(7)`. The two identities

```text
log(n^2)/2 = log n,
exp(-log(n)/2) exp(log(n^2)/4) = 1
```

prove `(8)` and hence `(9)`. For `(10)`, the strip gives
`1/4-Im(z)/2 <= 1`; on `t>=1`,

```text
|G_z(t)| <= t exp(-pi t) <= exp(-2t),
```

using `pi>3`. Integrating the last exponential gives `exp(-2N)/2`.

For `(14)`, integration by parts in the original shell coordinate gives a second exact recurrence
whose residual integral has the Ward density. Comparing it with `(9)` cancels the shared Gaussian
boundary and nonzero recurrence coefficient. Formula `(15)` follows from the corpus polynomial
step identity. The score is bounded above by
`3-2*pi<0` because `a<1/2`, `n>=1`, and `exp(2x)>=1`.

To prove `(16)`, integrate `f'_(a,n)(x)(1-cos(bx))`. Both boundary terms vanish: the trigonometric
factor vanishes at zero and the tilted Gaussian density vanishes at infinity. The remaining
integrand is nonnegative and is strictly positive at `x=pi/b`; hence its integral is positive.
Pointwise expansion of `exp(ix(b-ia))` identifies this sine integral with `Im W_n(b-ia)`.

For `(17)`, center the upper-half-plane Cayley transform at the value of shifted `R_n`. The
Euclidean ball of radius `1/2-a` around `u` stays in the first quadrant when `b>1/2-a`; `(16)`
therefore maps this ball to the upper half-plane. The Cayley transform maps it to unit disk and
has derivative norm `|R'_n|/(2 Im R_n)` at center. Schwarz lemma gives `(17)`.

For `(18)`, differentiate exact score `(15)`. Writing
`q=2 pi n^2 exp(2x)` and `c=a+5/2`, curvature is `(q-c)^2-2q`. For `n>=2`, `x>=0`, and
`a<1/2`, one has `q>24` and `c<3`; elementary monotonic algebra gives strict positivity.

For `(19)`, first integrate `f cos(bx)` against the derivative of `sin(bx)`, obtaining
`b integral f cos = integral (-f') sin`. Integrate the latter against the derivative of
`1-cos(bx)`. Density and first derivative vanish at infinity; sine and `1-cos` remove the
zero-endpoint terms. Resulting integrand is nonnegative by `(18)` and strictly positive at
`x=pi/b`. Polynomial logarithmic-derivative recursion supplies integrability and decay of the
second derivative. Pointwise real-part expansion of Ward phase plus `(14)` proves `(20)`.

For `(21)`, propagate positivity through three exact derivatives on `0<u<=3`; above `3`, use
`-1<=cos u` and `sin u<=1`. Kernel and first two derivatives vanish at zero. Three integrations
by parts therefore give `(22)` with no boundary residue. Writing

```text
q=2 pi n^2 exp(2x), c=a+5/2, r=q-c
```

gives `f'''/f=-r^3+6qr-4q`. For `n>=2`, inequalities `q>24`, `c<3`, and `r>21` force this
coefficient negative, proving `(23)`. Replacing `(a,b)` by `(-a,-b)` proves reflected horizontal
direction in `(24)`. For arbitrary positive shell, `x>=1/2` gives `q>12`, enough for same
coefficient sign; set-integral splitting at `1/2` proves `(25)` and strict positivity of tail.

## New knowledge

The high-frequency completed-source problem is not a real stationary-phase problem in `x`.
Gaussian factor is damping. Its genuine transition is a complex incomplete-Gamma saddle with a
moving lower cut `n^2`. Product-fibre regrouping preserves this transition arithmetically through
the exact cut product `k^2`.

This identifies the object left after all endpoint jets cancel: a cofinal family of universal
upper tails, weighted by critical Dirichlet characters. It also explains why fixed-shell endpoint
expansions miss the sign: they expand before resolving whether the moving cut lies below, near,
or above the complex Gamma saddle.

The recurrence adds a second reduction: source-polynomial complexity and one entire boundary
channel are now removed exactly. Spectral dependence lives only in `R_n(z)`. Equations
`(11)`--`(13)` close previously open derivative connector to actual Hedenmalm current. Absolute
far-shell control is closed by `(10)`.

Equations `(14)`--`(16)` expose a previously hidden monotonicity mechanism: despite the complex
incomplete-Gamma presentation, every positive-shell remainder in the positive-frequency critical
aperture lies strictly in the upper half-plane. This statement is uniform in shell number and
frequency and survives the moving-cut transition. Unresolved information is now joint orientation
of `R_n`, `R'_n`, and reflected branch, not one-component phase quadrant, mass, or analyticity.

Equation `(17)` strengthens phase information to a quantitative derivative cone. Equations
`(21)`--`(24)` now determine horizontal derivative direction for every higher shell and its
reflection. Remaining derivative information is the transverse imaginary component, not an
arbitrary complex direction.

Equation `(18)` further shows directional obstruction is structurally localized. Higher shells
have both strict decrease and strict convexity; only ground shell can violate convex phase shape.
Any proof or counterexample must therefore explain how ground-shell defect interacts with
cofinal higher-shell and reflected sums.

Equations `(19)`--`(20)` close the second component of higher-shell phase. Every higher-shell
remainder lies in strict first quadrant for every positive frequency, uniformly across moving-cut
transition. Equations `(22)`--`(25)` close higher-shell derivative rotation and prove ground
failure is compact with a strictly positive tail. Open data are ground head domination,
transverse derivatives, and cofinal reflected compensation.

## Lean surface

```text
thetaCuspShellGammaCoordinate_map
thetaCuspShellHalfLineTransform_eq_gammaIntegral
thetaCuspShellGammaIntegrand_eq_explicit
thetaCuspShellGammaCoordinate_eq_sub_log
thetaCuspShellGammaAmplitude_eq_universal
thetaCuspShellGammaPhaseIntegrand_eq_universal
thetaCuspShellGammaThreshold_productFiber
integrableOn_thetaCuspSourceTerm_mul_phase_of_neg_one_lt_im
integrableOn_thetaCuspSourceTerm_mul_phaseSpectralDerivative
hasDerivAt_thetaCuspShellPhaseTransform
thetaCuspShellPhaseTransform_eq_universalGammaTail
thetaCuspUniversalGammaAmplitude_pos
norm_thetaCuspUniversalGammaPhaseIntegrand
norm_thetaCuspShellGammaDirichletPrefactor
hasDerivAt_thetaCuspUniversalGammaCore
thetaCuspUniversalGammaPhaseIntegrand_eq_primitiveDerivative
thetaCuspUniversalGammaPhaseTail_eq_boundary_add_coreTail
thetaCuspShellGammaPrefactor_mul_primitive_cut
thetaCuspShellPhaseTransform_eq_boundary_add_coreRemainder
norm_thetaCuspUniversalGammaCoreTail_le
hasDerivAt_thetaCuspUniversalGammaCoreTail
norm_thetaCuspShellGammaCoreRemainder_le
hasDerivAt_thetaCuspShellGammaCoreRemainder
thetaCuspShellEvenPhaseValue_eq_gammaRemainders
hasDerivAt_thetaCuspShellEvenPhaseValue
thetaCuspShellEvenPhaseSpectralDerivativeValue_eq_gamma
thetaCuspShellPairHedenmalmCurrent_eq_gamma
thetaCuspShellPhaseTransform_eq_gammaBoundary_add_ward
thetaCuspShellGammaCoreRemainder_eq_two_mul_ward
thetaCuspWardGibbsAtom_step_eq_score
hasDerivAt_thetaCuspTiltedWardDensity
hasDerivAt_thetaCuspTiltedWardDensityDerivative
thetaCuspTiltedLogDerivativeStep
hasDerivAt_exp_mul_thetaCuspPolynomialAtom
thetaCuspTiltedWardDensityDerivative_eq_polynomial
thetaCuspTiltedWardDensitySecondDerivative_eq_polynomial
integrableOn_thetaCuspTiltedWardDensitySecondDerivative
tendsto_thetaCuspTiltedWardDensityDerivative_atTop_zero
thetaCuspTiltedWardScore_neg
thetaCuspTiltedWardCurvature_pos_of_two_le
strictConvexOn_thetaCuspTiltedWardDensity_of_two_le
integral_thetaCuspTiltedWardDensity_mul_sin_pos
integral_thetaCuspTiltedWardDensity_mul_cos_pos_of_two_le
thetaCuspShellWardPhaseTransform_im_eq_sine
thetaCuspShellWardPhaseTransform_re_eq_cosine
thetaCuspShellWardPhaseTransform_im_pos
thetaCuspShellWardPhaseTransform_re_pos_of_two_le
thetaCuspShellGammaCoreRemainder_im_pos_of_neg_one_lt
thetaCuspShellGammaCoreRemainder_im_pos
thetaCuspShellGammaCoreRemainder_re_pos_of_two_le
upperHalfPlane_local_derivative_bound
thetaCuspShellGammaCoreRemainder_shift_im_pos
norm_thetaCuspShellGammaCoreRemainderSpectralDerivative_le_im
norm_thetaCuspShellGammaCoreRemainderSpectralDerivative_le_im_highFrequency
thirdOrderSineKernel_pos
integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_thirdOrder_identity
integrableOn_thetaCuspTiltedWardThirdDerivative_mul_thirdOrderSineKernel
integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_pos_of_two_le
thetaCuspShellGammaCoreRemainderSpectralDerivative_re_neg_of_two_le
thetaCuspShellGammaCoreRemainderSpectralDerivative_reflected_re_pos_of_two_le
thetaCuspHigherShellGammaFourDirectionalCone
thetaCuspTiltedWardDerivativeRotationDensity_pos_of_one_div_three_le
integral_Ioi_one_div_three_thetaCuspTiltedWardDerivativeRotationDensity_pos
thetaCuspTiltedWardDerivativeRotation_compact_defect_split
thetaCuspTiltedWardThirdDerivativeCoefficient_neg_of_pos_of_half_le
integral_Ioi_half_neg_thetaCuspTiltedWardThirdDerivative_mul_kernel_pos
thetaCuspTiltedWardThirdOrder_compact_defect_split
thetaCuspShellEvenGammaSpectralDerivative_re_at_tilt
thetaCuspShellEvenGammaSpectralDerivative_im_at_tilt
```

## Open successor

Attack ground compact-head domination

```text
Re R'_1(b-ia) < 0                                      (b > 218/25),
```

using exact split `(25)`. Then combine all horizontal directions with scale-sensitive
`Im R'_n`, reflected branches, and cofinal product fibres in exact current `(13)`. Absolute
far-shell mass is controlled by `(10)` but cannot orient exponentially small current. Final
target remains

```text
0 < a < 1/2,  |b| > 218/25.
```

No fixed-order endpoint expansion can substitute for this uniform estimate.

# Global radial-prolate defect measure of the constrained CCM source

- **ID:** `ccm-radial-prolate-global-defect-measure`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE] [NECESSITY THEOREM]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Dunster's uniform radial PSWF Bessel expansion, fixed-mode prolate eigenvalue asymptotics, and the exact CCM endpoint/leakage laws
- **Statement:** In the global radial coordinate `x=y/lambda>1`, the squared exterior Fourier profile of the constrained CCM source has an explicit weak limit. The previously isolated outer coordinate `r=lambda(y-lambda)` is not tight: all of its normalized mass escapes to `r` of order `lambda^2`.

## Setup

Let `e_(n,lambda)` be the normalized order-zero fixed-degree prolate mode on
`[-lambda,lambda]`, with

```text
c=2*pi*lambda^2,
Phi_(n,lambda)(y)=Fourier(e_(n,lambda))(y).
```

The finite-Fourier eigenrelation and analytic continuation identify, for `x>1`,

```text
Phi_(n,lambda)(lambda*x)/Phi_(n,lambda)(lambda)
 =Ps_n^0(x,c^2)/Ps_n^0(1,c^2).                                  (1)
```

Here the right side is the order-zero radial prolate function normalized at the band edge.
For the constrained source

```text
g_lambda=(ell_1 e_(0,lambda)-ell_0 e_(4,lambda))
          /sqrt(ell_0^2+ell_1^2),
Phi_lambda=Fourier(g_lambda),                                    (2)
```

put

```text
R_lambda(x)=Phi_lambda(lambda*x)/Phi_lambda(lambda),  x>=1.       (3)
```

The denominator is nonzero for all sufficiently large `lambda` by the exact endpoint-response
law.

## Fixed-mode radial asymptotic

For fixed degree `n`, Dunster's radial Bessel expansion gives, uniformly for `1<x<infinity`,

```text
Ps_n^0(x,c^2)
 =K_(n,c) A_(sigma,x)
   [J_0(c*xi_(sigma,x))+O(c^(-1) env J_0(c*xi_(sigma,x)))],       (4)
```

where

```text
xi_(sigma,x)=integral_1^x sqrt((t^2-sigma^2)/(t^2-1))dt,
A_(sigma,x)
 =[xi_(sigma,x)^2/((x^2-1)(x^2-sigma^2))]^(1/4),                  (5)
```

and the fixed-degree separation law is

```text
sigma^2=(2*n+1)/c+O(c^(-2)).                                     (6)
```

At `x=1`, `A_(sigma,x)->1` and `J_0(0)=1`; hence division by the endpoint removes
`K_(n,c)` and changes the uniform error only by `1+O(c^(-1))`.

Fix a compact interval `K` in `(1,infinity)` and write

```text
theta(x)=arccos(1/x).
```

Expansion of `(5)` using `(6)` gives uniformly on `K`

```text
xi_(sigma,x)
 =sqrt(x^2-1)-sigma^2*theta(x)/2+O(sigma^4),
A_(sigma,x)=x^(-1/2)+O(c^(-1)).                                  (7)
```

The large-argument expansion of `J_0` therefore yields

```text
sqrt(c) Ps_n^0(x,c^2)/Ps_n^0(1,c^2)
 =sqrt(2/pi) /[x^(1/2)(x^2-1)^(1/4)]
   *cos(c*sqrt(x^2-1)-(2*n+1)*theta(x)/2-pi/4)
   +o_K(1).                                                      (8)
```

This is the missing global radial profile. The degree survives only as a bounded phase marking;
the amplitude is universal.

## Weak squared-profile law

Let `phi` be continuous with compact support in `(1,infinity)`. Squaring `(8)` and using
`cos^2 u=(1+cos(2u))/2` gives one nonoscillatory term and one oscillatory term. The derivative of
the principal phase is

```text
d/dx sqrt(x^2-1)=x/sqrt(x^2-1)>0.                                (9)
```

Integration by parts, followed by uniform approximation for continuous `phi`, makes the
oscillatory term tend to zero. Thus

```text
integral_1^infinity phi(x)c
  |Ps_n^0(x,c^2)/Ps_n^0(1,c^2)|^2 dx
 ->integral_1^infinity phi(x)
   dx/[pi*x*sqrt(x^2-1)].                                       (10)
```

For the constrained source, the endpoint laws give

```text
Phi_(0,lambda)(lambda)/Phi_(4,lambda)(lambda)=O(lambda^(-4)),
ell_0,ell_1 -> nonzero constants.                                (11)
```

The two normalized radial profiles in `(8)` are uniformly `O_K(c^(-1/2))`. Hence the degree-four
term dominates `(2)` on every compact subset of `(1,infinity)`, and `(10)` also holds with the
ratio `R_lambda` from `(3)`:

```text
c |R_lambda(x)|^2 dx
  => dx/[pi*x*sqrt(x^2-1)]                                      (12)
```

vaguely on `(1,infinity)`.

## No missing boundary or far-field mass

The exact constrained leakage and endpoint theorems state

```text
delta_lambda/ d_1(lambda) ->8/11,
|Phi_lambda(lambda)|^2/[lambda*d_1(lambda)] ->16*pi/11,           (13)
```

where, by evenness,

```text
delta_lambda
 =2 integral_lambda^infinity |Phi_lambda(y)|^2dy.                 (14)
```

Changing variables `y=lambda*x` in `(14)` gives

```text
integral_1^infinity |R_lambda(x)|^2dx
 =delta_lambda/[2*lambda*|Phi_lambda(lambda)|^2].                 (15)
```

Since `c=2*pi*lambda^2`, equations `(13)`--`(15)` imply

```text
c integral_1^infinity |R_lambda(x)|^2dx ->1/2.                   (16)
```

The limiting density in `(12)` has exactly the same total mass:

```text
integral_1^infinity dx/[pi*x*sqrt(x^2-1)]=1/2.                   (17)
```

Therefore vague convergence plus convergence of the total masses upgrades `(12)` to weak
convergence of finite measures on the compactification `[1,infinity]`. No mass is lost at the band
edge or at radial infinity.

Equivalently, in the CCM normalization,

```text
lambda^2 |R_lambda(x)|^2dx
 =>dx/[2*pi^2*x*sqrt(x^2-1)],                                    (18)
```

whose total mass is `1/(4*pi)`.

## Escape from the former outer coordinate

The earlier outer profile was

```text
R_lambda^out(r)=R_lambda(1+r/lambda^2),  r>=0.                    (19)
```

For every fixed `A>0`, weak convergence in `(18)` and the absence of an atom at `x=1` give

```text
integral_0^A |R_lambda^out(r)|^2dr ->0.                           (20)
```

Its total integral still tends to `1/(4*pi)`. Hence this family is not tight on bounded `r`; all
normalized mass escapes to `r` of order `lambda^2`, exactly the global scale
`x=y/lambda`.

The inner coordinate `rho=lambda^3(y-lambda)` remains the correct derivative scale at the single
endpoint. It carries asymptotically zero total mass. The global radial coordinate carries the
leakage mass. These are complementary boundary and bulk data, not two candidate one-scale limits.

## Route consequence

The full lower summation tail is

```text
E(g_lambda)(1/v)
 =sqrt(v) sum_(k>=1) Phi_lambda(k*v)
  -g_lambda(0)/(2*sqrt(v)).                                      (21)
```

Equation `(12)` supplies the exact oscillatory profile for every fixed dilation `k` after replacing
`x` by `k*x`. Its phase derivative is nonzero for each fixed pair of distinct dilations. Therefore
fixed-dilation cross terms are candidates for nonstationary cancellation; the nonzero sawtooth
constant of the first endpoint-jet component cannot be promoted to the exact radial tail without
resumming `(21)`.

The next source theorem is now precise:

```text
uniform-in-k radial Bessel bounds
  + cancellation of the central term in (21)
  -> von-Mangoldt-weighted dilation correlations of the exact tail
  -> closed-Weil Rayleigh excess and parity transfer.             (22)
```

The all-prime interchange in `(22)` is not proved here. In particular, fixed-`k` oscillatory
cancellation alone does not justify summation against `Lambda(k)`.

## Attacks and boundaries

1. **Fixed endpoint jets.** Equation `(8)` resums all endpoint jets. The phase, rather than any
   fixed inverse-power term, controls the cofinal tail.
2. **One-scale boundary profile.** The endpoint derivative layer has zero limiting mass; the
   previous outer coordinate loses all mass to infinity. Neither alone is the global carrier.
3. **Degree-zero contamination.** The degree-zero endpoint is `O(lambda^(-4))` relative to degree
   four and cannot alter the compact radial limit.
4. **Pointwise convergence.** The rescaled profile remains oscillatory and has no pointwise global
   limit. The correct invariant is the squared-profile defect measure.
5. **All-prime conclusion.** No claim is made until a summable uniform dilation estimate is proved.

## Novelty and significance verdict

After vocabulary erasure, `(8)` is Dunster's uniform Bessel expansion specialized to fixed
order zero, `(10)` is elementary nonstationary phase, and the global mass upgrade uses the existing
exact prolate leakage identity. The theorem materially changes the CCM route but remains a direct
parent-theory specialization. It is `[NOT NEW SCIENTIFIC KNOWLEDGE]`.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, Journal of Classical Analysis
  11 (2017), 1--21; arXiv:1601.00699, especially equations (3.1), (3.5), (3.6), and (3.10).
- D. Slepian, *Some Asymptotic Expansions for Prolate Spheroidal Wave Functions*, J. Math. Phys. 44
  (1965), 99--140.

## Lean status

**Partially formalized, 2026-08-04.**  The original decision recorded here ("the formal tree has no PSWF
differential equation, normalized radial branch, Bessel asymptotics ...  No Lean file is added") is now out
of date: the tree owns Bessel's equation for the integral representation, a second solution with its
Wronskian normalisation, the `u^{-1/2}` envelopes, the large-argument phase asymptotic, the radial prolate
equation in Liouville normal form, and the pole-uniform comparison estimate with an explicit
`1 + O(c^{-1})` factor (see `ccm-exact-finite-aperture-first-row-vanishing.md` and
`formal/GaloisForLFunctions/RHTower/CCMRadialProlateDefect.lean`).  What the present card adds is the
*profile* side, in `formal/GaloisForLFunctions/RHTower/CCMRadialProlateProfileMeasure.lean`.

**The radial angle and equation `(17)`:**

- `radialAngle`, `radialAngle_one`, `continuous_radialAngle`, **`hasDerivAt_radialAngle`**,
  `tendsto_radialAngle_atTop` — the angle `theta(x) = arctan(sqrt(x²-1))`, which is the card's `arccos(1/x)`,
  with `theta(1) = 0`, `theta' = 1/(x sqrt(x²-1))` and `theta(x) -> pi/2`.
- `profileDensity`, `profileDensity_nonneg`, `hasDerivAt_radialAngle_div_pi`,
  `integrableOn_profileDensity` — the limiting density `1/(pi x sqrt(x²-1))` is exactly `(theta/pi)'`, and
  its integrability on the open ray comes with the improper fundamental theorem rather than being assumed.
- **`integral_Ioi_profileDensity`** — equation `(17)`:
  `int_1^infinity dx/(pi x sqrt(x²-1)) = 1/2`, exactly.  No asymptotics enter: the mass is the angle swept
  from the band edge to radial infinity, `(1/pi)(pi/2)`.

**The second-order phase expansion, equation `(7)`:**

- **`abs_sqrt_sq_sub_sub_le`** — the scalar Taylor bound `|sqrt(t²-s) - t + s/(2t)| <= s²/4`, uniform for
  `t >= 1`, `0 <= s <= 1/2`.  The upper half is `(t - s/(2t))² >= t² - s`; the lower half is a polynomial
  inequality after squaring.
- **`abs_xiSpeed_sub_second_order_le`** — the integrand form: the Liouville speed minus its two leading
  terms is at most `(s²/4)(t²-1)^{-1/2}`.  Multiplying by `sqrt(t²-1)` turns the statement into the scalar
  bound, so no expansion of the singular factor is needed.
- `intervalIntegrable_invMulSqrtSqSubOne`, **`integral_invMulSqrtSqSubOne`** — the radial angle is the exact
  primitive of `1/(t sqrt(t²-1))` from the band edge, the integrand being singular but dominated by
  `(t²-1)^{-1/2}`.
- **`abs_xiEndpointPhase_sub_second_order_le`** — equation `(7)`, first half, with an explicit error:

  ```text
  |xi_s(x) - (sqrt(x²-1) - (s/2) theta(x))| <= (s²/4) log(x + sqrt(x²-1)),
  ```

  for `0 <= s <= 1/2` and `x >= 1`.  With `s = sigma²` and the separation law `sigma² = (2n+1)/c + O(c^{-2})`
  this is `xi = sqrt(x²-1) - sigma² theta/2 + O(sigma⁴)`, uniformly on compacts — and the two leading terms
  are exact primitives, not approximations.

**The amplitude half of `(7)`:**

- **`xiAmplitude_pow_four`** — the fourth power of the Liouville–Green amplitude is the elementary rational
  expression `xi²/((x²-1)(x²-s))`; no root survives.
- `xiAmplitude_pos`, **`abs_xiEndpointPhase_sq_sub_le`** — the endpoint bracket `(4)` pins `xi²` to relative
  accuracy `s`: `|xi_s(x)² - (x²-1)| <= s (x²-1)`.
- **`abs_xiAmplitude_sub_inv_sqrt_le`** — `|A_s(x) - x^{-1/2}| <= 4 s` for every `x > 1` and
  `0 <= s <= 1/2`.  The passage from fourth powers to the amplitude is the factorisation
  `A⁴ - B⁴ = (A-B)(A+B)(A²+B²)` with `(A+B)(A²+B²) >= B³ = x^{-3/2}`, so the bound is global rather than
  compact-dependent — stronger than the card's `O(c^{-1})` on compacts.

The *constant* in the large-argument Bessel asymptotic is now proved as well (see below): the tree had
`exists_besselJ0_phase_asymptotic` in the form `sqrt(u) J_0(u) = p cos u + q sin u + O(1/u)` with `p, q`
deliberately unidentified, and `p = q = 1/sqrt(pi)` is now a theorem.  So every analytic ingredient of `(8)`
is unconditional: the phase and amplitude expansions of `(7)` and the Bessel asymptotic with its constant.
What `(8)` still needs is the PSWF-specific normalisation — the identification `(1)` of the radial profile
with the Fourier ratio, and the endpoint-response nonvanishing — and `(10)`, `(16)`, `(20)` then need the
exact leakage identities `(13)`, which belong to the endpoint-response cards.

**The Fresnel constant is now proved**, in `formal/GaloisForLFunctions/RHTower/FresnelIntegral.lean`.  It is
the one irreducible input of `(8)`: the amplitude `sqrt(2/pi)` and the phase shift `-pi/4` of the Bessel
asymptotic are exactly `int_0^infinity exp(i x²) dx = sqrt(pi) exp(i pi/4)/2`.  mathlib has the Gaussian
integral for every complex `b` with `re b > 0` but not this boundary case, where the integrand does not decay
and the integral is only conditionally convergent.

- `cexp_fresnel_split`, `fresnelKernel`, `fresnelValue`, `fresnelRegValue` — the regularised kernel
  `exp(-(eps - i)x²) = exp(-eps x²) exp(i x²)`: a nonnegative decreasing weight against a convex phase.
- **`norm_integral_fresnel_tail_le`** — every tail is at most `2/A`, *uniformly in the regularisation*: the
  weighted first-derivative van der Corput test applies with `w = exp(-eps x²)`, `g = x²`, `g' >= 2A`.  This
  is the estimate that replaces contour rotation.
- `integrable_fresnelKernel`, `integral_Ioi_fresnelKernel`, `norm_integral_Ioi_fresnelKernel_tail_le`,
  `integral_Ioi_fresnelKernel_split` — for `eps > 0` the ray integral is mathlib's complex Gaussian value and
  splits at `R` with the same tail bound.
- `norm_integral_fresnel_dereg_le` — removing the regularisation costs at most `R(1 - exp(-eps R²))` on
  `[0, R]`.
- `tendsto_fresnelRegValue`, **`norm_integral_fresnel_sub_le`** — hence
  `|int_0^R exp(i x²) dx - fresnelValue| <= 2/R`: the regularised comparison plus continuity of
  `(pi/(eps - i))^{1/2}` at `eps = 0`.
- **`tendsto_integral_cexp_sq_atTop`** — the Fresnel integral converges to the boundary Gaussian value.  No
  separate Cauchy argument is needed: the `2/R` bound gives convergence and the value at once.
- `pi_mul_I_ne_zero`, **`cpow_pi_mul_I_half`**, **`fresnelValue_eq`** — the constant in explicit form,
  `sqrt(pi) exp(i pi/4)/2`, from `log(pi i) = log pi + i pi/2`.
- **`tendsto_integral_cos_sq_atTop`**, **`tendsto_integral_sin_sq_atTop`** —
  `int_0^infinity cos(x²) dx = int_0^infinity sin(x²) dx = sqrt(pi/2)/2`.  The equality of the two is the
  phase `pi/4` itself.

The route from the Fresnel constant to the Bessel constant is under construction in
`formal/GaloisForLFunctions/RHTower/BesselJZeroConstant.lean`.  The key point is that the substitution is
*exact*, so no asymptotic expansion of the phase is ever needed:

- **`norm_integral_cexp_neg_sq_sub_le`** — the conjugate Fresnel integral, with the same `2/X` rate.
- **`integral_cexp_neg_half_mul_sq`** — the rescaling `int_0^{sqrt 2} exp(-i u v²/2) dv
  = sqrt(2/u) int_0^{sqrt u} exp(-i w²) dw`.
- `quadJacobian`, `continuousOn_quadJacobian`, **`integral_cexp_cos_eq_quad`** — the exact substitution
  `v = 2 sin(φ/2)`: since `1 - cos φ = 2 sin²(φ/2)`, the phase `u cos φ` becomes `u(1 - v²/2)` *identically*
  and the Jacobian is `(1 - v²/4)^{-1/2}`.  This replaces the usual "expand `cos φ` near the stationary
  point" step by an identity.
- `jacCorr`, `jacCorrDeriv`, `sqrt_one_sub_quarter_pos`, `sqrt_one_sub_quarter_le_one`, `jacCorr_nonneg`,
  **`jacCorr_le`**, **`hasDerivAt_jacCorr`**, `jacCorrDeriv_nonneg`, `continuousOn_jacCorrDeriv`,
  **`quadJacobian_eq`** — the Jacobian splits as `1 + g(v)` with `0 <= g(v) <= v²/4` on `[0, sqrt 2]` and
  `g'(v) = v/(4 (1-v²/4)^{3/2}) >= 0`.  The `1` gives the Fresnel integral; `g` is nonnegative increasing
  with an explicit derivative, which is what the weighted van der Corput test consumes.

**The Bessel constant is proved.**  `abs_sqrt_mul_besselJ0_sub_le`:

```text
|sqrt(u) J_0(u) - (cos u + sin u)/sqrt(pi)| <= 5 / u^{1/4}      (u >= 1),
```

i.e. `J_0(u) = sqrt(2/(pi u)) cos(u - pi/4) + O(u^{-3/4})`, with the amplitude `sqrt(2/pi)` and the phase
shift `pi/4` identified.  This is the last analytic input of `(8)`, and it is the Fresnel constant in
disguise.  The remaining steps beyond the substitution already recorded:

- `jacCorr_le_sqrt_two_sub_one`, `jacWeight`, `jacWeight_nonneg`, `hasDerivAt_jacWeight`,
  **`norm_integral_jacCorr_far_le`** — the far block.  Writing the increasing correction as
  `g = g(sqrt 2) - (g(sqrt 2) - g(v))` turns it into two *nonincreasing* weights, so the corpus weighted
  van der Corput test applies to both with `phase' = u v >= u δ`; the bound is `8 g(sqrt 2)/(u δ)`.
- `continuousOn_jacCorr`, **`norm_integral_jacCorr_near_le`** — the near block: `|g| <= δ²/4` there, so the
  contribution is at most `δ³/4`.
- `norm_integral_jacCorr_split_le`, **`norm_integral_jacCorr_le`** — balancing at `δ = u^{-1/4}` (written
  `1/sqrt(sqrt u)`, so no `rpow` is needed) gives `4/sqrt(sqrt u)³ = O(u^{-3/4})`.  This is `o(u^{-1/2})`:
  the correction provably cannot reach the leading term, which is why the constant is exactly Fresnel's.
- `besselPhaseIntegral`, `besselJ0_eq_re_besselPhaseIntegral`, `norm_integral_jacCorr_neg_le`,
  **`norm_sqrt_mul_besselPhaseIntegral_sub_le`** — the scaled oscillatory integral:
  `‖sqrt(u) Psi(u) - e^{iu} sqrt 2 conj(fresnelValue)‖ <= (2 sqrt 2 + 4)/sqrt(sqrt u)`, where
  `sqrt(u) · sqrt(2/u) = sqrt 2` converts the Fresnel scaling into the amplitude.
- **`re_exp_mul_conj_fresnelValue`** — the real part of the limit constant:
  `Re[e^{iu} sqrt 2 conj(fresnelValue)] = (sqrt(pi)/2)(cos u + sin u)`, which is `cos(u - pi/4)` in disguise;
  the factor `2/pi` of the integral representation turns it into `(cos u + sin u)/sqrt(pi)`.

**Equation `(8)` is assembled**, in `formal/GaloisForLFunctions/RHTower/CCMRadialProfileAsymptotic.lean`.
The key structural point is that the rescaled amplitude is *exactly* algebraic:

```text
sqrt c · A_s(x) / sqrt(c xi_s(x)) = [(x²-1)(x²-s)]^{-1/4},
```

with no error whatsoever — the `xi^{1/2}` inside `A_s` cancels the Bessel amplitude `(c xi)^{-1/2}`.  So the
profile is the fourth root times a cosine, and there are exactly three errors.

- `cos_add_sin_eq`, `sqrt_two_div_pi_eq`, **`abs_besselJ0_sub_amplitude_le`** — the Bessel asymptotic in
  amplitude–phase form: `|J_0(v) - sqrt(2/pi) cos(v - pi/4)/sqrt v| <= 5 v^{-3/4}`.
- **`abs_cos_phase_sub_le`** — the phase expansion transported through the cosine: replacing `c xi_s(x)` by
  `c sqrt(x²-1) - c(s/2) theta(x)` costs at most `c (s²/4) log(x + sqrt(x²-1))`, by `|cos a - cos b| <= |a-b|`.
  With `c s = 2n+1` from the separation law this is the card's degree marking `-(2n+1) theta(x)/2`, and the
  cost is `O(1/c)`.
- `ampFourth`, `ampFourth_pos`, **`sqrt_mul_xiAmplitude_div_eq`** — the exact amplitude identity above.
- `ampFourth_pow_four`, **`abs_ampFourth_sub_le`** — the `s`-dependence of the fourth root is linear:
  `|A_s-root - A_0-root| <= s A_0-root/(x²-s)`, again by the `a⁴-b⁴` factorisation.
- **`abs_radialProfile_sub_le`** — equation `(8)`:

  ```text
  |sqrt c A_s(x) J_0(c xi_s(x))
     - sqrt(2/pi) [(x²-1)x²]^{-1/4} cos(c sqrt(x²-1) - c(s/2) theta(x) - pi/4)|
   <= sqrt(2/pi) A_s-root (c s²/4) L(x) + sqrt(2/pi) |A_s-root - A_0-root| + 5 A_s-root (c xi_s(x))^{-1/4},
  ```

  for every `c > 0`, every `0 <= s <= 1/2` and every `x > 1` with `c xi_s(x) >= 1`.  All three errors are
  `o(1)` on compacts once `s = O(1/c)`: the first is `O(c s²) = O(1/c)`, the second `O(s) = O(1/c)`, the third
  `O(c^{-1/4})`.  Note `sqrt(2/pi)[(x²-1)x²]^{-1/4} = sqrt(2/pi)/(x^{1/2}(x²-1)^{1/4})` is exactly the card's
  amplitude.

What `(8)` still imports is only the PSWF normalisation: the identification `(1)` of the radial profile with
the Fourier ratio, Dunster's `(4)` for the actual mode (available in this tree as the pole-uniform envelope
and approximation bounds of `ccm-exact-finite-aperture-first-row-vanishing`), and the separation law `(6)`.

## Lean gates

- [x] Lean: the radial angle and its derivative law
- [x] Lean: equation `(17)` — the limiting density has total mass exactly `1/2`
- [x] Lean: equation `(7)`, phase half — the second-order expansion of `xi_sigma` with explicit error
- [x] Lean: the amplitude half of `(7)` — `|A_sigma(x) - x^{-1/2}| <= 4 sigma²`, globally on the ray
- [x] Lean: the **Fresnel constant** `int_0^infinity exp(i x²) dx = sqrt(pi) exp(i pi/4)/2` — new general
  infrastructure, absent from mathlib
- [x] Lean: the constant in the Bessel large-argument asymptotic —
  `|sqrt(u) J_0(u) - (cos u + sin u)/sqrt(pi)| <= 5 u^{-1/4}`, i.e. `p = q = 1/sqrt(pi)`
- [x] Lean: equation `(8)`, the fixed-degree radial profile — the model profile
  `sqrt c A_s J_0(c xi_s)` equals the card's amplitude times the card's cosine up to three explicit `o(1)`
  errors; the PSWF normalisation `(1)`, `(4)` and `(6)` remain imports
- [ ] Lean: equation `(10)`, the weak squared-profile law
- [ ] Lean: equations `(16)`, `(20)` — total-mass matching and outer-coordinate escape (need `(13)`)


## Gates

- [x] fixed-mode normalized radial profile proved
- [x] constrained degree-four dominance proved
- [x] global weak squared-profile law proved
- [x] total mass matched and boundary escape excluded
- [x] former outer-coordinate non-tightness proved
- [ ] uniform all-dilation summation-vector asymptotic
- [ ] von-Mangoldt-weighted exact-tail correlation law
- [ ] true Weil Rayleigh-excess and parity transfer

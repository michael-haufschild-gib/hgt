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

What remains for `(8)` is the *constant* in the large-argument Bessel asymptotic: the tree has
`exists_besselJ0_phase_asymptotic` in the form `sqrt(u) J_0(u) = p cos u + q sin u + O(1/u)` with `p, q`
deliberately unidentified, whereas `(8)` needs `p = q = 1/sqrt(pi)`, i.e.
`J_0(u) = sqrt(2/(pi u)) cos(u - pi/4) + O(u^{-3/2})`.  Identifying them is a separate classical task (a
Fresnel-type constant), independent of everything above.  `(10)`, `(16)` and `(20)` then need that constant
plus the exact leakage identities `(13)`, which belong to the endpoint-response cards.

## Lean gates

- [x] Lean: the radial angle and its derivative law
- [x] Lean: equation `(17)` — the limiting density has total mass exactly `1/2`
- [x] Lean: equation `(7)`, phase half — the second-order expansion of `xi_sigma` with explicit error
- [x] Lean: the amplitude half of `(7)` — `|A_sigma(x) - x^{-1/2}| <= 4 sigma²`, globally on the ray
- [ ] Lean: the constant in the Bessel large-argument asymptotic (`p = q = 1/sqrt(pi)`)
- [ ] Lean: equation `(8)`, the fixed-degree radial profile
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

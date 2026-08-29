# Regular-variation weighted Steinhaus large-deviation law

- **ID:** `regular-variation-weighted-steinhaus-ldp`
- **Stage:** 3-formalized
- **Type:** THEOREM / PROBABILISTIC COMPARISON MODEL / RATE-FUNCTION FOUNDATION
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOT THE DETERMINISTIC PRIME-LOG LAW]`
- **Feeds:**
  `../../1-in-progress/prime-log-kronecker-coherence-capacity-conjecture.md`

## Theorem

Fix `0 <= alpha < 1`.  Let `L` be a positive slowly varying function, locally bounded above and
away from zero, and put

```text
W_X = sum_(p<=X) (log p) p^(-alpha) L(p),
a_(p,X) = (log p) p^(-alpha) L(p) / W_X,
d_X = pi(X).                                                (1)
```

Let `(U_p)_p` be independent Haar-uniform random variables on the complex unit circle and define

```text
Y_X = sum_(p<=X) a_(p,X) U_p.                              (2)
```

Set

```text
w_alpha(v) = (1-alpha)v^(-alpha),

Lambda_alpha(lambda)
  = integral_0^1 log I_0(lambda w_alpha(v))dv,

I_alpha(q)
  = sup_(lambda>=0){lambda q-Lambda_alpha(lambda)}.         (3)
```

Then:

1. `Y_X`, regarded as an `R^2`-valued random variable, satisfies a large-deviation principle at
   speed `d_X` with good radial rate function

   ```text
   J_alpha(z)=I_alpha(|z|)       for |z|<1,
   J_alpha(z)=infinity          for |z|>=1.                 (4)
   ```

   The value at the boundary `|z|=1` is infinite; the random variables themselves remain in the
   closed unit disk.

2. For every `0<q<1`,

   ```text
   (1/d_X) log P(|Y_X|>=q) -> -I_alpha(q).                  (5)
   ```

3. `I_alpha` is continuous and strictly increasing on `[0,1)`, with `I_alpha(0)=0` and
   `I_alpha(q)->infinity` as `q->1-`.

4. As `q->0+`, the exact square-integrability trichotomy is

   ```text
   alpha<1/2:
     I_alpha(q)~[(1-2alpha)/(1-alpha)^2]q^2,

   alpha=1/2:
     I_alpha(q)~2q^2/log(1/q),

   alpha>1/2:
     I_alpha(q)~C_alpha q^(1/(1-alpha)),                   (6)
   ```

   where

   ```text
   K_alpha=((1-alpha)^(1/alpha)/alpha)
     integral_0^infinity log I_0(x)x^(-1/alpha-1)dx,

   C_alpha=(1-alpha)alpha^(alpha/(1-alpha))
     K_alpha^(-alpha/(1-alpha)).                            (7)
   ```

5. As `q->1-`, every member of the family has the universal high-coherence law

   ```text
   I_alpha(q)
    =1/2 log(1/(1-q))
     +1/2 log(pi(1-alpha))-(1-alpha)/2+o(1).                (8)
   ```

The rate function depends only on the regular-variation index.  The slowly varying factor `L`
disappears completely after normalization.

## Proof

### 1. Prime normalization and the limiting weight profile

The prime number theorem in von Mangoldt form and partial summation give the prime Karamata law

```text
W_X~X^(1-alpha)L(X)/(1-alpha).                              (9)
```

Since `d_X~X/log X`, for `p=vX` with `v` in a fixed compact subinterval of `(0,1]`,

```text
d_X a_(p,X)
 =(1-alpha)v^(-alpha)L(vX)/L(X)+o(1)
 ->w_alpha(v),                                             (10)
```

uniformly in `v` on that compact set.  The uniform convergence theorem for slowly varying
functions supplies the last step.

The singular endpoint `v=0` is uniformly integrable.  Indeed, `log I_0(x)<=x` for `x>=0`, and
the prime Karamata law at `epsilon X` gives, uniformly for fixed `lambda>=0`,

```text
(1/d_X) sum_(p<=epsilon X)
  log I_0(lambda d_X a_(p,X))
 <=lambda sum_(p<=epsilon X)a_(p,X)
 ->lambda epsilon^(1-alpha).                               (11)
```

Letting `epsilon->0` removes the endpoint.  On `[epsilon,1]`, `(10)`, the prime number theorem,
and ordinary Riemann-sum convergence apply.  Consequently

```text
(1/d_X) sum_(p<=X) log I_0(lambda d_X a_(p,X))
 ->Lambda_alpha(lambda).                                   (12)
```

This also proves directly that the integral in `(3)` is finite.

### 2. Logarithmic moment generating function

Identify the complex plane with `R^2`.  Rotational invariance of a Haar unit phase gives, for
every `theta in R^2`,

```text
E exp(d_X <theta,Y_X>)
 =product_(p<=X) I_0(d_X a_(p,X)|theta|).                  (13)
```

Taking logarithms, dividing by `d_X`, and using `(12)` yields

```text
lim_(X->infinity) (1/d_X)log E exp(d_X<theta,Y_X>)
 =Lambda_alpha(|theta|).                                   (14)
```

The limiting cumulant is finite everywhere.  For positive radius it is differentiable under the
integral because

```text
0<=I_1(x)/I_0(x)<=1,
```

so the differentiated integrand is dominated by the integrable function `w_alpha`.  At the
origin, `log I_0(rw)/r->0` pointwise and is again dominated by `w`; hence the radial derivative is
zero.  Thus the `R^2` cumulant in `(14)` is differentiable on its entire effective domain.

The Gärtner--Ellis theorem now gives the full LDP.  Exponential tightness is automatic because
`|Y_X|<=1`.  Rotational invariance reduces the Legendre transform to

```text
J_alpha(z)
 =sup_(lambda>=0){lambda|z|-Lambda_alpha(lambda)}.          (15)
```

For `m(x)=I_1(x)/I_0(x)`, strict positivity of the variance in the exponentially tilted circle
law gives `m'(x)>0`.  Therefore

```text
Lambda_alpha'(lambda)
 =integral_0^1 w_alpha(v)m(lambda w_alpha(v))dv             (16)
```

is strictly increasing from `0` to `integral_0^1 w_alpha=1`.  It follows that `(15)` is finite
and strictly increasing for `|z|<1`, and infinite at and beyond `1`.  Applying the LDP to the
closed set `{|z|>=q}` and the open set `{|z|>q}` proves `(5)`, since both rate infima equal
`I_alpha(q)`.

### 3. Small coherence below the square-integrability threshold

The power series of `I_0` gives

```text
log I_0(x)~x^2/4             as x->0,
0<=log I_0(x)<=x^2/4.                                (17)
```

If `alpha<1/2`, then `w_alpha` is square-integrable.  Dominated convergence in `(3)` gives

```text
Lambda_alpha(lambda)
 ~lambda^2/4 integral_0^1 w_alpha(v)^2dv
 =[(1-alpha)^2/(4(1-2alpha))]lambda^2.                     (18)
```

Taking the Legendre transform of the quadratic leading term yields the first line of `(6)`.

### 4. The critical logarithmic law

For `alpha=1/2`, substitute `x=lambda/(2sqrt(v))`.  Then

```text
Lambda_(1/2)(lambda)
 =(lambda^2/2) integral_(lambda/2)^infinity
    log I_0(x)x^(-3)dx.                                    (19)
```

Near zero, `log I_0(x)=x^2/4+O(x^4)`; at infinity it is `O(x)`.  Hence

```text
Lambda_(1/2)(lambda)
 =(lambda^2/8)log(1/lambda)+O(lambda^2).                   (20)
```

Differentiation, or the standard conjugacy rule for a regularly varying convex function, gives

```text
Lambda_(1/2)'(lambda)
 ~(lambda/4)log(1/lambda).                                 (21)
```

Solving `q=Lambda_(1/2)'(lambda)` gives

```text
lambda~4q/log(1/q).                                        (22)
```

At this saddle, `Lambda_(1/2)(lambda)~lambda q/2`, and therefore

```text
I_(1/2)(q)~lambda q/2~2q^2/log(1/q).                       (23)
```

This is the middle line of `(6)`.

### 5. Small coherence above the square-integrability threshold

Suppose `alpha>1/2`.  With `x=lambda(1-alpha)v^(-alpha)`, one obtains

```text
Lambda_alpha(lambda)
 =[(lambda(1-alpha))^(1/alpha)/alpha]
   integral_(lambda(1-alpha))^infinity
     log I_0(x)x^(-1/alpha-1)dx.                           (24)
```

The integral converges at zero because `alpha>1/2`, and at infinity because `alpha<1`.
Consequently

```text
Lambda_alpha(lambda)~K_alpha lambda^(1/alpha).              (25)
```

The Legendre transform of `K lambda^(1/alpha)` is

```text
(1-alpha)alpha^(alpha/(1-alpha))
 K^(-alpha/(1-alpha))q^(1/(1-alpha)),                      (26)
```

which proves the final line of `(6)` and the constant `(7)`.

### 6. Universal high-coherence endpoint

The classical uniform large-argument expansion

```text
log I_0(x)=x-(1/2)log(2 pi x)+O(1/x)                       (27)
```

applies throughout the integral once `lambda(1-alpha)->infinity`.  Since

```text
integral_0^1 w_alpha(v)dv=1,
integral_0^1 log w_alpha(v)dv=log(1-alpha)+alpha,           (28)
```

integration of `(27)` gives

```text
Lambda_alpha(lambda)
 =lambda-(1/2)log(2 pi lambda)
  -(1/2)log(1-alpha)-alpha/2+o(1).                         (29)
```

Writing `q=1-epsilon`, the maximizing parameter satisfies

```text
lambda~1/(2epsilon).                                       (30)
```

Substitution into `lambda q-Lambda_alpha(lambda)` gives

```text
I_alpha(1-epsilon)
 =(1/2)log(1/epsilon)
  +(1/2)log(pi(1-alpha))-(1-alpha)/2+o(1),                 (31)
```

which is `(8)`.

## Anti-theatre audit

- The Gärtner--Ellis mechanism, Bessel cumulant, Karamata normalization, and convex-dual
  asymptotics are classical parent theory.  This theorem is therefore classified as a
  `[BRIDGE]`, not as new scientific knowledge.
- The exact three-regime family is valuable because it fixes every constant in the comparison
  model and makes the critical logarithmic member falsifiable.
- Replacing the actual deterministic orbit `p^(-it)` by the independent phases `U_p` does not
  prove the prime-log entropy-censoring conjecture.
- The new frontier remains the signed prime-product spectral pressure at moment depth
  `k asymp pi(X)` and observation entropy `log T asymp pi(X)`.

## Lean formalization map

Every statement of the theorem is unconditionally proved in Lean 4 (axiom audit: only
`propext, Classical.choice, Quot.sound`).  Build log: `docs/drafts/pipeline/1-in-progress/steinhaus-ldp-lean.md`.

| Card item | Lean declaration | Module |
|---|---|---|
| `w_α`, `∫₀¹ w_α = 1` | `weightProfile`, `integral_weightProfile` | `HTGeometry/SteinhausWeightProfile.lean` |
| `Λ_α`, finiteness `(11)`–`(12)` | `rvCumulant`, `intervalIntegrable_rvCumulant_integrand`, `rvCumulant_le` | `HTGeometry/SteinhausWeightProfile.lean` |
| `I_α = Λ_α^*` | `rvRate` | `RHTower/SteinhausRateFunction.lean` |
| part 3 (continuity, strict monotonicity, `I_α(0)=0`, blow-up) | `rvRate_zero`, `rvRate_pos`, `rvRate_strictMono`, `continuousOn_rvRate`, `tendsto_rvRate_atTop` | `RHTower/SteinhausRatePositive.lean`, `RHTower/SteinhausRateStrictMono.lean`, `RHTower/SteinhausProfileLogIntegral.lean` |
| `(17)` `log I₀(x)/x² → 1/4` | `tendsto_steinhausLogLaplace_div_sq` | `RHTower/SteinhausCumulantTaylor.lean` |
| `(18)`, `(6)` line 1 (`α<1/2`) | `tendsto_rvCumulant_div_sq`, `tendsto_rvRate_div_sq` | `RHTower/SteinhausSubcritical*.lean` |
| scaling identity | `rvCumulant_eq_rpow_mul_tail` | `HTGeometry/SteinhausScalingIdentity.lean` |
| Legendre power law | `tendsto_rvRate_div_rpow` | `RHTower/SteinhausRatePowerAsymptotic.lean` |
| `(20)`, `(23)`, `(6)` line 2 (`α=1/2`) | `tendsto_rvCumulant_crit`, `tendsto_rvRate_crit` | `RHTower/SteinhausCriticalCumulant.lean`, `RHTower/SteinhausCriticalRate.lean` |
| `(24)`–`(26)`, `(7)`, `(6)` line 3 (`α>1/2`) | `rvSuperConst`, `tendsto_rvCumulant_div_rpow_super`, `rvLegConst_inv_eq`, `tendsto_rvRate_div_rpow_super` | `RHTower/SteinhausSuperConstant.lean`, `RHTower/SteinhausSupercriticalLimit.lean` |
| `(27)` sharp | `tendsto_steinhausLogLaplace_sub_sharp` | `HTGeometry/SteinhausSharpAsymptotic.lean` |
| `(28)` | `integral_log_weightProfile` | `RHTower/SteinhausProfileLogIntegral.lean` |
| `(29)`, `(8)` = part 5 | `tendsto_rvCumulant_deficit`, `tendsto_rvRate_endpoint` | `RHTower/SteinhausEndpointCumulant.lean`, `RHTower/SteinhausEndpointRate.lean` |
| `(16)` | `hasDerivAt_rvCumulant`, `continuous_rvCumulantDeriv`, `strictMono_rvCumulantDeriv`, `exists_rvCumulantDeriv_eq` | `RHTower/SteinhausCumulantDeriv.lean` |
| Karamata UCT, Potter | `isSlowShift_uniform`, `isSlowlyVarying_uniform`, `isSlowlyVarying_potter` | `HTGeometry/SlowShiftUniform.lean`, `HTGeometry/SlowlyVarying.lean` |
| `(9)` prime Karamata | `tendsto_rvWeightSum` | `RHTower/PrimeKaramata.lean` |
| `(10)` | `rvNormReal_bounds` | `RHTower/RVNormalizedWeight.lean` |
| `(12)` | `tendsto_rvCumulantAverage` | `RHTower/RVCumulantLimit.lean` |
| `(13)` | `integral_exp_weightedSteinhausProjection`, `integral_exp_steinhausRotProj`, `integral_steinhausLaplace_norm` | `HTGeometry/SteinhausLaplaceProduct.lean`, `HTGeometry/SteinhausComplexSum.lean` |
| `(5)` = part 2 | `tendsto_log_rvDeviationProb` | `RHTower/RVDeviationLower.lean` |
| `(4)` = part 1 (planar LDP) | `isLDP_rvLaw`, `rvPlanarRate` | `RHTower/RVPlanarLDP.lean`, `RHTower/SteinhausExtendedRate.lean` |

Mathlib gaps closed on the way, all reusable: Karamata's uniform convergence theorem and Potter's
bound (there is no regular-variation theory in mathlib); the sharp Laplace asymptotic of `I₀`; the
logarithmic Cesàro theorem; the sub-critical prime power sum `∑_{p≤Y}(log p)p^{−β} ≪ Y^{1−β}`; the
Chebyshev linear bound for `θ`; and the first large-deviation principle in the corpus.

## Gates

- [x] dependency-closed paper proof
- [x] exact regular-variation normalization
- [x] full radial LDP and event exponent
- [x] exact low-coherence trichotomy
- [x] exact high-coherence constant
- [x] novelty honesty: classified as bridge
- [x] exact finite Haar-product Laplace identity, evenness, positivity, and exponential envelopes
  formalized in `HTGeometry/SteinhausLaplaceProduct.lean`
- [x] Lean probability and convex-duality infrastructure
- [x] unconditional Lean theorem batch
- [x] narrow leaf check and final module audit

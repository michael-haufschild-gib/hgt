# Finite Nyman approximants have one hypertranscendental Mellin gauge class

- **ID:** `nyman-finite-mellin-ht-gauge-collapse`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / NYMAN--BEURLING IMPLEMENTATION NO-GO / BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every nonzero finite linear combination of the Báez--Duarte fractional-part
  generators has a hypertranscendental Mellin transform. Any two such transforms differ by a
  nonzero differentially algebraic exponential-polynomial gauge, whereas the Nyman target has the
  differentially algebraic Mellin transform `1/s`. Consequently DA/HT status, holonomicity, and
  finite algebraic-differential state complexity cannot distinguish progress in the genuine
  Nyman--Beurling `L2` approximation problem.

## Nyman generators

Put

```text
rho_a(x)={1/(a x)},   a>=1, x>0,                           (1)
```

where braces denote fractional part. Let

```text
g(x)=sum_(j=1)^m c_j rho_(a_j)(x)                          (2)
```

with distinct positive `a_j` and not all `c_j` zero. The strengthened Nyman--Beurling criterion
uses the integer subfamily `a_j in N`, but the theorem below needs only positivity and finiteness.

For `0<Re(s)<1`, use the Mellin transform

```text
M[h](s)=integral_(0,infinity) h(x)x^(s-1) dx.              (3)
```

## Mellin identity `[SEARCH]`

For every `a>0` and `0<Re(s)<1`,

```text
M[rho_a](s)=-a^(-s) zeta(s)/s.                             (4)
```

### Proof

Scaling `y=ax` gives

```text
M[rho_a](s)=a^(-s)M[rho_1](s).
```

After `t=1/x`,

```text
M[rho_1](s)=integral_(0,infinity) {t}t^(-s-1)dt.           (5)
```

The integral converges absolutely in the strip. Splitting it into `(0,1)` and the intervals
`[n,n+1]`, integrating `t-n` on each interval, and telescoping gives

```text
integral_(0,infinity) {t}t^(-s-1)dt=-zeta(s)/s.
```

This is the classical Mellin identity underlying the Nyman--Beurling criterion. `square`

By linearity,

```text
M[g](s)=-zeta(s)P_g(s)/s,                                  (6)
P_g(s)=sum_(j=1)^m c_j a_j^(-s).                            (7)
```

The exponential polynomial `P_g` is nonzero. Indeed, exponentials with distinct real frequencies
`-log a_j` are linearly independent. It is D-finite, since it is annihilated by

```text
product_(j=1)^m (d/ds+log a_j).                            (8)
```

In particular `P_g` is DA over `C(s)`.

## Zeta is hypertranscendental `[SEARCH]`

The Riemann zeta function is HT over `C(s)`. If it were DA, then its affine reflection
`zeta(1-s)` would be DA. The functional equation

```text
zeta(s)=2^s pi^(s-1) sin(pi s/2) Gamma(1-s) zeta(1-s)      (9)
```

would solve meromorphically for `Gamma(1-s)` using only DA functions. Closure under quotient and
affine substitution would make `Gamma` DA, contradicting Holder's theorem.

## Finite-approximant HT theorem `[PROVED]`

For every nonzero finite Nyman combination `g`, its meromorphic Mellin continuation `M[g]` is HT
over `C(s)`.

### Proof

Suppose `M[g]` were DA. Equation (6), the nonvanishing of `P_g`, and differential-field closure
would give

```text
zeta(s)=-s M[g](s)/P_g(s),
```

so `zeta` would be DA. This contradicts the preceding theorem. `square`

The result is stronger than non-holonomicity: no algebraic differential equation of any finite
order can hold for the Mellin transform of a nonzero finite approximant.

## One DA-gauge class `[PROVED]`

For nonzero finite combinations `g` and `h`,

```text
M[g](s)/M[h](s)=P_g(s)/P_h(s).                             (10)
```

The right side is a nonzero DA meromorphic function. Thus all nonzero finite Nyman Mellin
transforms represent the same multiplicative class modulo nonzero DA gauges: the common HT carrier
is `zeta(s)/s`; only the exponential-polynomial gauge changes.

By contrast, for the Nyman target `chi=1_(0,1)`,

```text
M[chi](s)=1/s,                                             (11)
```

which is rational and therefore DA.

Hence differential-algebraic type is maximally discontinuous with respect to the relevant Hilbert
closure: every nonzero point in every finite approximation space is HT in Mellin coordinates,
while the target is DA. The Nyman--Beurling theorem asks whether the target belongs to the `L2`
closure of those spaces; it does not ask for differential-algebraic convergence.

## Exact implementation no-go

No proof through Nyman--Beurling can use any of the following as its decisive finite-to-infinite
mechanism:

1. finite Nyman approximants eventually becoming DA or holonomic after Mellin transform;
2. a drop in their differential order or algebraic-differential state dimension as the
   approximation improves;
3. DA/HT status separating good finite approximants from bad ones; or
4. a finite algebraic-differential state system with DA coefficients whose output is exactly a
   nonzero finite Nyman Mellin transform.

Every nonzero finite approximant already has the full HT zeta factor, and all of them occupy one DA
gauge class. A finite algebraic differential system would have DA component outputs, contradicting
the HT theorem.

The result does **not** exclude the Nyman--Beurling or Báez--Duarte criterion. The exact criterion is
RH-equivalent and uses the distinguished `L2` norm, the dilation geometry, and closure of an
infinite union of finite spans. None of those data factors through DA/HT status.

## Attack and scientific verdict

The apparent finiteness of (2) is misleading: each single fractional-part generator already
contains all integer discontinuities, and equation (4) transports that infinite arithmetic content
to the full zeta factor. Thus this theorem is not a new obstruction inside Nyman theory; it is the
classical Mellin formula viewed through Holder hypertranscendence and differential-field closure.

The proof is exact and route-useful but routine from its parents. It therefore fails the
scientific-novelty gate.

Primary sources:

1. L. Báez-Duarte, *A strengthening of the Nyman--Beurling criterion for the Riemann Hypothesis*,
   https://arxiv.org/abs/math/0202141.
2. J.-F. Burnol, *On an analytic estimate in the theory of the Riemann zeta function and a theorem
   of Báez-Duarte*, https://arxiv.org/abs/math/0202166.
3. L. Báez-Duarte, *Arithmetical aspects of Beurling's real variable reformulation of the Riemann
   hypothesis*, https://arxiv.org/abs/math/0011254.
4. Holder's theorem on the differential transcendence of `Gamma`, combined with the zeta
   functional equation.

## Lean status

**Formalized unconditionally, 2026-08-17.**  The tree now exposes the whole chain; see the Lean
formalization section below.

## Gates

- [x] Exact Mellin formula and finite-combination factorization proved.
- [x] HT of every nonzero finite approximant proved.
- [x] Single DA-gauge-class collapse proved.
- [x] Exact noncategorical route no-go stated.
- [x] Scientific-novelty claim rejected.
- [x] Whole theorem formalized unconditionally in Lean — `hypertranscendentalOver_nymanMellinMero`.

## Lean formalization — 2026-08-17

Module: `formal/GaloisForLFunctions/RHTower/NymanMellinGaugeCollapse.lean`
(wired into the `GaloisForLFunctions.RHTower` umbrella).

| Card step | Lean name |
|---|---|
| the generator `ρ_a(x) = {1/(ax)}` | `NymanMellin.nymanGen` |
| **(4)** `M[ρ_a](s) = −a^{−s} ζ(s)/s` on `0 < Re s < 1` | `NymanMellin.mellin_nymanGen` |
| convergence of the Mellin integral in the strip | `NymanMellin.mellinConvergent_nymanGen` |
| a finite combination `g = ∑ c_j ρ_{a_j}` | `NymanMellin.nymanCombination` |
| **(6)–(7)** `M[g](s) = −P_g(s) ζ(s)/s`, `P_g(s) = ∑ c_j a_j^{−s}` | `NymanMellin.mellin_nymanCombination`, `NymanMellin.freqPoly` |
| **(8)** `P_g` is D-finite, hence DA over `ℂ(s)` | `NymanMellin.differentiallyAlgebraic_freqPoly` |
| `P_g ≠ 0` (distinct real frequencies are independent) | `NymanMellin.exists_freqPoly_ne_zero` |
| **(11)** the target `χ = 1_{(0,1]}` has `M[χ](s) = 1/s` | `NymanMellin.nymanTarget`, `NymanMellin.mellin_nymanTarget` |
| the meromorphic continuation `M[g]` as an upper-end germ | `NymanUpper.nymanMellinMero` |
| **the finite-approximant HT theorem** | `NymanUpper.hypertranscendentalOver_nymanMellinMero` |
| **(10)** one DA-gauge class: `M[g]/M[h] = P_g/P_h` | `NymanUpper.nymanMellinMero_div` |

**Where each classical input comes from.**  The Mellin identity `(4)` is built on the corpus's
`RHTower.FractionalPartZeta.integral_Ioi_zero_fract_dilate_cpow` (the dilated fractional-part Mellin
integral on the critical strip, itself proved by Abel summation and analytic continuation),
transported through mathlib's `mellin_comp_inv` and `mellin_comp_mul_left`.  The
hypertranscendence of `ζ` is the corpus's
`HTGeometry.zeta_hypertranscendentalOver_gammaCoefficientField` — which is stronger than the card's
own argument, since it excludes relations over the whole differential field generated by `Γ`, not
only over `ℂ(s)`; the card's functional-equation-plus-Hölder derivation is therefore not needed and
is not used.  The exponential-polynomial independence is
`HTGeometry.CExpPoly.eq_zero_of_cexpFn_eq_zero`, and the D-finiteness of `P_g` is
`differentiallyAlgebraic_finset_expSum_general`.

**New reusable infrastructure built for this card** (in the same module): the upper-end germ of an
analytic function (`NymanUpper.upperAnalyticOf`, `upperMeroOf`) with its derivative, sum, product
and constant laws; the exponential germ `expMero` with `expMero_deriv` and its differential
algebraicity `differentialAlgebraicOver_expMero`; the base change of a differential relation from
`ℂ(s)` to the Gamma coefficient field (`differentialAlgebraicOver_gammaField_of_ratFunc`); and
`zetaUpperMero_ne_zero`, `upperEndCoordinateMero_ne_zero`.

**Route note.**  The card's `M[g]` is the meromorphic continuation of the Mellin transform.  The
formal statement separates the two halves cleanly and proves both: `mellin_nymanCombination` is the
analytic identity on the strip `0 < Re s < 1` where the integral converges, and
`hypertranscendentalOver_nymanMellinMero` is the hypertranscendence of the germ of the closed form
`−P_g·ζ/s` at the complex upper end, where every factor is analytic.  Hypertranscendence is stated
over `ℂ(s)` in the upper-end meromorphic field, which is a genuine field, so the division by `P_g`
in the card's proof is legitimate there without any nonvanishing hypothesis on `P_g` as a function.

**Not formalized, and not an obligation of this card:** the "Exact implementation no-go" list, which
is an interpretive scope statement about proof strategies rather than a mathematical proposition;
its mathematical content is exactly `hypertranscendentalOver_nymanMellinMero` together with
`nymanMellinMero_div` and `mellin_nymanTarget`, all of which are proved.

Verification: `lake build GaloisForLFunctions.RHTower.NymanMellinGaugeCollapse` — PASS;
`#print axioms` on all fifteen named results reports only
`[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-17 — Formalized unconditionally in Lean 4 and promoted to stage 3.  The Mellin identity for
  the Báez-Duarte generators and their finite combinations, the nonvanishing and differential
  algebraicity of the exponential-polynomial gauge, the hypertranscendence of every nonzero finite
  approximant's Mellin transform, the single-gauge-class collapse, and the rational Mellin transform
  of the Nyman target are unconditional Lean theorems.

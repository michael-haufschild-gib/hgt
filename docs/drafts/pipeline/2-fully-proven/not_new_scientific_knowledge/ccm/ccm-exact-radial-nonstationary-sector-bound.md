# The exact CCM radial nonstationary prime sector vanishes cofinally

- **ID:** `ccm-exact-radial-nonstationary-sector-bound`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Dunster's exterior Liouville--Green expansion with Olver remainders,
  nonstationary phase, and the Hilbert-kernel summation bound
- **Statement:** For the actual constrained prolate source, every off-diagonal radial Gram entry
  with both indices at least two satisfies
  `|G_lambda(j,k)|<=C*d_1/(c*j*k*|j-k|)`. The complete logarithmically weighted sector is therefore
  `O(d_1/c)=o(d_1)`.

## Setup

Let

```text
G_lambda(j,k)
 =lambda integral_1^infinity
   q_lambda(lambda*j*x)q_lambda(lambda*k*x)dx,

c=2*pi*lambda^2,
d_1=1-chi_4(lambda)^2.                                         (1)
```

Here `q_lambda` is the Fourier transform of the constrained `m=0,4` prolate source. The `m=4`
component carries the `d_1` scale; the `m=0` component and its cross term are smaller by
`O(lambda^(-4))` in exterior norm.

## Phase-preserving exterior expansion

Dunster's Section 2 Liouville--Green construction applies uniformly on every unbounded interval
`z>=1+delta`. Fix `delta=1`. For an integer `r>=2`, put

```text
U_(lambda,r)(x)=sqrt(lambda*x)q_lambda(lambda*r*x),   x>=1.
```

Retaining two terms in his expansions `(2.19)`--`(2.22)` gives, after the boundary and
constrained-source normalizations, an exact representation of the form

```text
U_(lambda,r)(x)
 =sqrt(d_1)/r *sum_(epsilon in {+1,-1})
    exp(i*epsilon*c*xi_c(r*x))a_(epsilon,c,r)(x),                 (2)
```

where the amplitudes, including the Olver remainder, satisfy symbol bounds

```text
|a_(epsilon,c,r)(x)|<=C*x^(-1/2),
|d/dx a_(epsilon,c,r)(x)|<=C*x^(-3/2),                            (3)
```

uniformly in `c`, `r>=2`, and `x>=1`. Dunster states the Olver remainder bound on complex
unbounded domains containing `z>=2`, but that additive bound alone does not justify factoring the
remainder through an oscillatory exponential. The exact interaction-picture theorem in
`radial-pswf-interaction-picture-transport.md` supplies the missing phase-preserving statement:
after Dunster's Liouville transform, the two amplitudes satisfy exact first-order transport
equations driven by the short-range potential `psi=O(xi^(-2))`. Their total variation is therefore
`O(c^(-1))`, uniformly on the exterior sector. Restoring the explicit geometric prefactor gives
`(3)`. The phase is

```text
xi_c(z)=integral_1^z sqrt((t^2-sigma_4(c)^2)/(t^2-1))dt,
sigma_4(c)^2=O(c^(-1)).                                         (4)
```

The point of `(2)` is that the remainder remains inside the two oscillatory branches. The
pointwise Bessel-envelope remainder from the pole-uniform Section 3 formula does not retain this
information and is not the correct tool in the sector `z>=2`.

## Exact two-index estimate

For `r>=2`,

```text
d/dx xi_c(r*x)
 =r*sqrt((r^2*x^2-sigma_4(c)^2)/(r^2*x^2-1)).                   (5)
```

As a function of `r>=2`, the right side has derivative bounded above and below by positive
absolute constants, uniformly for `x>=1` and large `c`. Hence

```text
|d/dx[xi_c(j*x)-xi_c(k*x)]|>=c_0*|j-k|,
|d/dx[xi_c(j*x)+xi_c(k*x)]|>=c_0*(j+k).                         (6)
```

Since

```text
G_lambda(j,k)=integral_1^infinity
 U_(lambda,j)(x)U_(lambda,k)(x)dx/x,
```

insert `(2)` for both factors. The product amplitudes, including the `dx/x` measure, obey

```text
|b_(j,k,c)(x)|+|b_(j,k,c)'(x)|
 <=C/(j*k*x^2),                                                 (7)
```

and vanish at infinity. One integration by parts in each of the four phase branches, using
`(6)`--`(7)`, gives the exact bound

```text
|G_lambda(j,k)|
 <=C*d_1/(c*j*k*|j-k|),
 j,k>=2, j!=k.                                                   (8)
```

No fixed-index limit is taken in `(8)`: all constants are uniform in the two arithmetic indices.

## Arithmetic summation

The elementary estimate

```text
sum_(j>=2;j!=k)1/(j*k*|j-k|)
 <=C*(1+log k)/k^2                                              (9)
```

and `(8)` imply

```text
sum_(k>=2)log(k)
 sum_(j>=2;j!=k)|G_lambda(j,k)|

 <=C*d_1/c *sum_(k>=2)log(k)(1+log k)/k^2
 =O(d_1/c)=o(d_1).                                              (10)
```

Thus the complete exact radial prime sector with `j,k>=2`, `j!=k`, vanishes at the leakage scale.

## Positive route consequence

The actual off-diagonal radial charge now has only one unsolved sector:

```text
-2 sum_(k>=2)log(k)G_lambda(1,k).                               (11)
```

The limiting-model theorem `ccm-limiting-radial-first-row-weber-bound.md` proves the required
summable scale for `(11)`. What remains is a hybrid transfer: use Dunster's pole-uniform Bessel
representation for the first factor and his phase-preserving exterior expansion for the second,
uniformly through `k/c`.

## Novelty and significance verdict

The theorem closes a real CCM estimate, but its mathematical content is an application of
Dunster's published Olver expansion and standard one-dimensional nonstationary phase. It does not
clear the parent-theory novelty gate and is classified as a bridge.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699, especially
  Section 2, formulas `(2.19)`--`(2.22)`.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- `radial-pswf-interaction-picture-transport.md`, exact ODE transport and Lean formalization.

## Lean decision

**Correction, 2026-07-27.**  The Liouville--Green *coordinate* and the exact interaction-picture
decomposition **are** formalized — `RHTower/RadialPSWFExteriorPhase.lean` and
`RHTower/RadialPSWFInteractionPicture.lean`, the latter stating explicitly that the oscillatory
decomposition is an exact consequence of the differential equation rather than a factored big-`O`.
What is absent is the **remainder estimate** on the interaction potential and any
nonstationary-phase interface.  Formalizing this bridge would still not close the surviving
first-row or true-Weil comparison.  No Lean file is added by this card.

The arithmetic-summation layer `(9)`--`(10)` of this card **is** now formalized, in
`RHTower/RadialGramOffDiagonalDecay.lean` (exact partial-fraction row sum, the row bound
`R K <= 3(1 + log K)/K`, and summability of `sum_K log K (1 + log K)/K^2`), axiom-clean.

## Gates

- [x] phase-preserving exterior expansion selected
- [x] two-index phase derivative separated uniformly
- [x] Olver remainder retained inside oscillatory branches
- [x] exact `j,k>=2` Gram estimate proved
- [x] logarithmically weighted arithmetic sector summed
- [x] nonstationary-phase interface `|∫ g cos(cξ)| ≤ …/(c·m)` in Lean
- [x] two-index phase separation `(6)` in Lean, uniform in `x`, `s`, and both indices
- [x] amplitude symbol bounds `(3)` in Lean (`O(c⁻¹)` interaction-picture total variation)
- [x] four-branch assembly of `(2)`, `(3)`, `(6)` into the entry estimate `(8)`, for arbitrary
  two-branch representations on a finite exterior interval
- [x] `(8)` with every constant explicit, for any symbol-decaying two-branch pair, uniformly in
  the right endpoint
- [x] phase-curvature bound `|j²ξ''(jx) ∓ k²ξ''(kx)| ≤ (16/9)/x³` in Lean, so `(8)` needs only
  the two symbol records
- [ ] instantiation: a `SymbolTwoBranch` record for the actual radial PSWF solutions with
  `M = C√d₁/r`
- [ ] exact first-row hybrid Bessel/Liouville--Green transfer

## Lean progress — the nonstationary-phase interface and the two-index separation `(6)`

Two of the three pieces the "Lean decision" above listed as absent are now built, wired and
axiom-clean.

`formal/GaloisForLFunctions/HTGeometry/NonstationaryPhaseLowerBound.lean`

```text
abs_integral_mul_cos_phase_le
    |∫_a^b g cos(cξ + φ)| ≤ (1/c)[ (|g a| + |g b|)/m + ∫ (|g'|/m + |g||ξ''|/m²) ]
    whenever |ξ'| ≥ m > 0
```

This is the first-derivative test in the form the two-index product consumes.  It is obtained from
the corpus's `abs_integral_mul_cos_comp_le` — which bounds `∫ g·(ξ' cos(cξ + φ))`, i.e. the weight
already carrying the phase speed — by dividing the weight by `ξ'`; the quotient's variation costs one
power of `m` on `g'` and two on the phase curvature `ξ''`.

`formal/GaloisForLFunctions/RHTower/RadialDilatedPhaseSeparation.lean`

```text
dilatedPhaseSpeed s r x = r · xiSpeed s (r x) = r √((r²x² − s)/(r²x² − 1))     -- (5)
dilatedPhaseSpeed_sq        = r² + (1 − s) r²/(r²x² − 1)
le_dilatedPhaseSpeed        r ≤ speed
dilatedPhaseSpeed_le        speed ≤ (4/3) r
sub_dilatedPhaseSpeed_ge    (2/3)(j − k) ≤ speed(j) − speed(k)     for 2 ≤ k ≤ j, x ≥ 1   -- (6)
le_add_dilatedPhaseSpeed    j + k ≤ speed(j) + speed(k)                                    -- (6)
```

`(6)` is proved **without differentiating in the index**.  The squared speed is
`r² + (1 − s)r²/(r²x² − 1)`; its two-index difference of correction terms is
`(1 − s)(j² − k²)/((k²x² − 1)(j²x² − 1))`, and both denominator factors are at least `3` once
`j, k ≥ 2` and `x ≥ 1`, so that difference is at most `(j² − k²)/9`.  Hence the difference of squares
is at least `(8/9)(j² − k²)`, the sum of speeds is at most `(4/3)(j + k)`, and the quotient gives the
gap.  All constants are absolute and uniform in `x`, in the turning parameter `s ∈ [0, 1/2]`, and in
the two indices.

**What is still absent** is only the amplitude side: the symbol bounds `(3)`
`|a| ≤ Cx^{−1/2}`, `|a'| ≤ Cx^{−3/2}`, i.e. the `O(c⁻¹)` total-variation estimate for the
interaction-picture amplitudes driven by the short-range potential.  The variable-coefficient
Grönwall inequality that estimate needs — total mass of the control in the exponent, not a uniform
bound times the interval length — is already formal in
`formal/GaloisForLFunctions/HTGeometry/GronwallVariableCoefficient.lean`.

## Lean progress — the amplitude variation estimate

The third missing piece, the `O(c⁻¹)` total-variation bound on the interaction-picture amplitudes,
is now built.  Two modules, wired, axiom-clean.

`formal/GaloisForLFunctions/HTGeometry/GronwallScaledBound.lean`

```text
abs_le_const_mul_exp_of_volterra_bound
    |h| ≤ K + ∫ φ|h|   ⟹   |h| ≤ K · exp(∫ φ)        for every K ≥ 0
```

The corpus's variable-coefficient Grönwall inequality is normalized at `1`; a Volterra inequality
coming from an actual differential equation carries the initial size instead, and that size may be
zero.  Rescaling by `K + ε` and shrinking `ε` removes the normalization with no positivity
hypothesis on `K`, so the `K = 0` case is the uniqueness statement.

`formal/GaloisForLFunctions/RHTower/RadialPSWFAmplitudeVariation.lean`

```text
radialInteractionTotal c W V x = ‖a₊(x)‖ + ‖a₋(x)‖
norm_le_radialInteractionTotal        ‖W‖ ≤ A                          (|e^{±icx}| = 1)
radialInteractionTotal_volterra       A(x) ≤ A(a) + ∫_a^x (‖ψ‖/c) A
radialInteractionTotal_le_exp         A(x) ≤ A(a) · exp((1/c)∫_a^x ‖ψ‖)
integral_norm_deriv_radialInteraction_le
    ∫_a^b ‖ψ‖‖W‖/(2c)  ≤  A(a)·(exp((1/c)∫_a^b ‖ψ‖) − 1)/2
```

The last is the total variation of each amplitude — `‖a₊'‖ = ‖a₋'‖ = ‖ψ‖‖W‖/(2c)` exactly, by the
transport laws — so with `V = ∫‖ψ‖` finite the amplitudes move by `O(V/c)` over the whole exterior
ray.  This is the statement the card calls "their total variation is therefore `O(c⁻¹)`, uniformly
on the exterior sector"; the geometric prefactor `x^{−1/2}` of `(3)` is the corpus's already-formal
`xiAmplitude_le`.

Everything the card lists as absent is therefore built.  What remains is the assembly: combine the
two-phase decomposition, the symbol bounds, the two-index separation `(6)`, and the first-derivative
test into the four-branch integration by parts that yields `(8)`.

## Lean progress — the four-branch assembly

The assembly of `(2)`, `(3)`, `(6)` into an entry estimate of the shape `(8)` is now formal, wired
and axiom-clean, in three layers.

`formal/GaloisForLFunctions/HTGeometry/NonstationaryPhaseLowerBound.lean`

```text
abs_integral_mul_cos_phase_le      the first-derivative test, global hypotheses
abs_integral_mul_cos_phase_le_on   the same with EVERY hypothesis local to [a,b]:
                                   |∫ g cos(cξ+φ)| ≤ (1/c)[(|g a|+|g b|)/m + ∫(|g'|/m + |g||ξ''|/m²)]
```

The local version is the one the exterior radial phase can actually feed: `ξ_s(rx)` is smooth and
fast only on the ray, and the division by the phase speed happens under the integral sign, so it is
enough to have `|ξ'| ≥ m` there.  The proof is one integration by parts against `sin(cξ+φ)/c`.

`formal/GaloisForLFunctions/HTGeometry/TwoPhaseOscillatoryProduct.lean`

```text
oscBudget a b m g g' Θ''            = (|g a| + |g b|)/m + ∫(|g'|/m + |g||Θ''|/m²)
twoBranch_product_eq                the product-to-sum expansion of
                                    (g₁cos cΦ + g₂ sin cΦ)(g₃cos cΨ + g₄ sin cΨ)
                                    into four oscillations on Φ−Ψ and Φ+Ψ
abs_integral_fourOsc_le(_on)        each weight pays its own budget against its own phase
abs_integral_twoBranch_product_le(_on)
                                    the assembled product estimate, four explicit budgets over c
```

`formal/GaloisForLFunctions/RHTower/RadialTwoIndexOscillatoryBound.lean`

```text
dilatedPhase s r x  = ξ_s(r x)  ,  dilatedPhaseAccel s r x = r² ξ''_s(r x)
hasDerivAt_dilatedPhase, hasDerivAt_dilatedPhaseSpeed, continuity on every Icc a b with a ≥ 1
abs_integral_radial_twoBranch_product_le  (0 ≤ s ≤ 1/2, 2 ≤ k < j, 1 ≤ a ≤ b, 0 < c) :
    |∫_a^b U_j U_k| ≤ (four budgets, each divided by (2/3)(j − k)) / c
```

That is `(8)` for the exterior radial phases, with absolute constants uniform in the radius, the
turning parameter, and both indices — modulo supplying the two-branch representations of the actual
solutions, which is the next item.

`formal/GaloisForLFunctions/RHTower/RadialPSWFAmplitudeVariation.lean` supplies the bridge to those
representations:

```text
radialAmpCos c W V = 2 Re a₊ ,   radialAmpSin c W V = −2 Im a₊
realPart_eq_twoBranch      a real solution is  radialAmpCos · cos(cx) + radialAmpSin · sin(cx)
abs_radialAmpCos_le, abs_radialAmpSin_le      both amplitudes are ≤ 2‖a₊‖
hasDerivAt_radialAmpCos, hasDerivAt_radialAmpSin
```

together with the already-recorded `A(x) ≤ A(a)exp((1/c)∫‖ψ‖)` and the `O(V/c)` total variation.
What is left is the composition step: transporting these amplitudes through the Liouville variable
`ξ_s(rx)` and inserting the `x^{−1/2}` geometric prefactor and the `d₁` normalization, then the
tail beyond a finite interval.

## Lean progress — `(8)` with every constant explicit

`formal/GaloisForLFunctions/HTGeometry/OscBudgetSymbolBound.lean` and
`formal/GaloisForLFunctions/RHTower/RadialSymbolTwoBranchBound.lean` (wired, axiom-clean) turn the
four-branch estimate into the numerical shape of `(8)`.

```text
integral_one_div_sq_le          ∫_a^b x⁻² ≤ 1/a
integral_one_div_pow_four_le    ∫_a^b x⁻⁴ ≤ 1/(3a³)
oscBudget_le_of_symbolBounds
    |g| ≤ M/x , |g'| ≤ M'/x² , |Θ''| ≤ N/x³ on a ray from 1
      ⟹ oscBudget a b m g g' Θ'' ≤ 2M/m + M'/m + M N/(3m²)
abs_half_mul_{add,sub}_le'        the four product weights obey |w| ≤ M_j M_k/x
abs_half_mul_deriv_{add,sub}_le'  and |w'| ≤ (M_j' M_k + M_j M_k')/x²
```

The budget is **independent of the right endpoint**, which is the property `(8)` needs to survive the
passage to the whole exterior ray (available as
`HTGeometry.abs_setIntegral_Ioi_le_of_tendsto`).

```text
SymbolTwoBranch a b M M' g₁ g₂ g₁' g₂'
    the two amplitudes are C¹ on [a,b] with |g| ≤ M/x and |g'| ≤ M'/x²

abs_integral_radial_twoBranch_symbol_le  (0 ≤ s ≤ 1/2, 2 ≤ k < j, 1 ≤ a ≤ b, 0 < c) :
    |∫_a^b U_j U_k| ≤ 4 (2 M_j M_k/m + (M_j' M_k + M_j M_k')/m + M_j M_k N/(3m²)) / c ,
    m = (2/3)(j − k)
```

That is `(8)`: with the geometric prefactor `√d₁/r` folded into `M_j = C√d₁/j`, `M_k = C√d₁/k`, the
right-hand side is `O(d₁/(c j k (j−k)))`, with absolute constants uniform in the radius, the turning
parameter, and both indices.

**What is left** is only the *instantiation*: producing, for the actual radial PSWF solutions, a
`SymbolTwoBranch` record with `M = C√d₁/r` and `M' = C√d₁/r`, and the phase-curvature bound
`|ξ''_s(jx) j² ∓ ξ''_s(kx) k²| ≤ N/x³`.  The first comes from the interaction-picture amplitudes
(`RadialPSWFAmplitudeVariation`: real two-branch form, `A(x) ≤ A(a)exp((1/c)∫‖ψ‖)`, `O(V/c)` total
variation) composed with the Liouville amplitude `xiAmplitude_le` (`≤ 2^{1/4}/√x`); the second is an
elementary computation with `xiSpeedDeriv`.

### The phase curvature is now proved, not assumed

`RadialTwoIndexOscillatoryBound.lean` adds

```text
one_le_xiSpeed                         1 ≤ ξ'_s(t) for s ≤ 1, t > 1
abs_dilatedRadialPhaseAccel_le         |r² ξ''_s(r x)| ≤ (16/9)/(r x³)   for r ≥ 2, x ≥ 1
abs_dilatedRadialPhaseAccel_{sub,add}_le
                                       |j² ξ''(jx) ∓ k² ξ''(kx)| ≤ (16/9)/x³
```

proved from `ξ''_s(t) = t(s−1)/((t²−1)² ξ'_s(t))` together with `ξ' ≥ 1` and `t² − 1 ≥ (3/4)t²`.
Consequently

```text
abs_integral_radial_twoBranch_symbol_le'  (0 ≤ s ≤ 1/2, 2 ≤ k < j, 1 ≤ a ≤ b, 0 < c) :
    |∫_a^b U_j U_k| ≤ 4 (2 M_j M_k/m + (M_j' M_k + M_j M_k')/m + M_j M_k (16/9)/(3m²)) / c
```

takes **only the two `SymbolTwoBranch` records** as input: nothing about the phase is assumed.

### The symbol record is now built by composition

`RadialSymbolTwoBranchBound.lean` states `SymbolTwoBranch` in the **half-power class** the problem
actually produces — `|g| ≤ M/√x`, `|g'| ≤ M'/(x√x)` — since a Liouville-transformed amplitude decays
like `x^{-1/2}`; it is the *product* of two such that lands in the `1/x` class the budget consumes
(`abs_mul_le_of_halfSymbol`, `abs_mul_le_of_halfSymbol_deriv` and the four
`abs_half_{add,sub}_halfSymbol` variants).

```text
symbolTwoBranch_of_composition
    |A| ≤ C/√x , |A'| ≤ C'/(x√x) ,  |P|,|Q| ≤ K ,  |P'(Φ)Φ'|,|Q'(Φ)Φ'| ≤ K'/x²
      ⟹ SymbolTwoBranch a b (C K) (C' K + C K')
           (A·(P∘Φ)) (A·(Q∘Φ)) (A'·(P∘Φ) + A·(P'∘Φ)Φ') (A'·(Q∘Φ) + A·(Q'∘Φ)Φ')
```

That is exactly the composition of the Liouville amplitude with the interaction-picture amplitudes.
The three numerical inputs it still wants for the actual radial PSWF solutions are:

1. `|A| ≤ C/√x` and `|A'| ≤ C'/(x√x)` for the Liouville amplitude — the first is the corpus's
   `xiAmplitude_le` (`≤ 2^{1/4}/√x`); the second is its derivative bound;
2. `|P|, |Q| ≤ K` with `K = 2 A(a) exp((1/c)∫‖ψ‖)` — this is
   `abs_radialAmpCos_le`/`abs_radialAmpSin_le` together with `radialInteractionTotal_le_exp`;
3. `|P'(Φ(x))Φ'(x)| ≤ K'/x²` — the transported derivative bound, which is
   `‖ψ‖‖W‖/(2c)` times the bounded phase speed, with `ψ = O(ξ^{-2})`.

### Input 1 of the symbol record was already in the corpus

`RHTower/XiAmplitudeDecay.lean` already proves exactly the half-power symbol bounds for the
Liouville amplitude:

```text
abs_xiAmplitude_le_four   |A_s(x)| ≤ 4/√x         for x ≥ 2
abs_xiAmplitudeDeriv_le   |A_s'(x)| ≤ 4/(x√x)     for x ≥ 2
```

so `C = C' = 4`, and no new module is needed for the first of the three inputs
`symbolTwoBranch_of_composition` asks for.  (A duplicate module written for this was deleted.)  The remaining two are the uniform bound on the
interaction amplitudes (already `abs_radialAmpCos_le` + `radialInteractionTotal_le_exp`) and the
transported derivative bound `|P'(Φ(x))Φ'(x)| ≤ K'/x²`.

### Inputs 2 and 3 of the symbol record

`RadialPSWFAmplitudeVariation.lean` now also proves the derivative half:

```text
abs_transport_deriv_re_le    |P'(t)| = |2 Re a₊'(t)| ≤ ‖ψ(t)‖‖W(t)‖ / c
abs_transport_deriv_im_le    the same for the sine amplitude
abs_transport_deriv_comp_le  ‖ψ(Φ x)‖ ≤ κ/x² , ‖W(Φ x)‖ ≤ K , |Φ'(x)| ≤ L
                             ⟹ |P'(Φ x) Φ'(x)| ≤ (κ K L / c)/x²
```

so `K' = κ K L / c` — one power of the bandwidth small, as the card's `(3)` asserts.  Input 2, the
uniform bound `|P|, |Q| ≤ K`, is `abs_radialAmpCos_le`/`abs_radialAmpSin_le` together with
`radialInteractionTotal_le_exp`, both already formal.

**All three numerical inputs of `symbolTwoBranch_of_composition` are therefore reduced to two
statements about the actual radial normal form**: the potential decay `‖ψ(ξ)‖ = O(ξ^{-2})` and the
comparison `Φ(x) ≳ x` that converts it into `κ/x²`.

### Both remaining normal-form statements are closed

```text
RHTower/RadialTwoIndexOscillatoryBound.lean
  sub_one_le_xiEndpointPhase   ξ_s(z) ≥ z − 1        (ξ' ≥ 1 integrated)
  le_dilatedRadialPhase        x ≤ ξ_s(r x)          for r ≥ 2, x ≥ 1

RHTower/RadialNormalFormPotentialDecay.lean
  abs_lgNormalFormDefect_radialProlate_le_sq
      |ψ(x)| ≤ 54/x²   for x ≥ 2, uniformly in the bandwidth
```

The second is the corpus's own `abs_lgNormalFormDefect_radialProlate_le` (`|ψ| ≤ 40/(x²−1)`) read
beyond the second dilation, where `x² − 1 ≥ (3/4)x²`; the aperture cancels exactly in the normal
form, so no `c` survives in the potential.  The first says the Liouville variable grows at least like
the radius, which is what converts a `ξ^{-2}` potential bound into an `x^{-2}` one.

Every ingredient of `(8)` for the actual radial PSWF solutions is therefore formal: the two-branch
representation, the amplitude bounds and their `O(1/c)` variation, the Liouville amplitude symbol
bounds, the potential decay, the phase growth, the phase separation, the phase curvature, the
oscillatory budget, and the endpoint-uniform assembly.  What is left is the bookkeeping instantiation
that names `W`, `V`, `ψ`, `Φ` for the concrete signed-mode data and reads off the constants.

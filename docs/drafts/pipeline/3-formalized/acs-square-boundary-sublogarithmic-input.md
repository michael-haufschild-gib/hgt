# Sublogarithmic zeta logarithmic derivative on Re s = 1

- **ID:** acs-square-boundary-sublogarithmic-input
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every ε>0, eventually in |t|,
  `‖logDeriv riemannZeta (1+it)‖ ≤ ε log |t|`; consequently the absolute
  regular square-prime multiplier is eventually ≤ε times the Gamma symbol.

## Role in ACS

This supplies the high-frequency analytic input to
[the formalized square mixed-source theorem](acs-square-mixed-source-lower-order.md).
Its low-frequency pairing and exact BV transfer are recorded in that chain.

## Dependency-closed paper proof

Write θ(L)=L^(-2/3)(log L)^(-2/3)/100 and
w(u)=θ(log(5u))/(16000 log log(5u)). These are the existing
`vinogradovKorobovWidth` and `vinogradovKorobovZeroFreeWidth`.
The corpus proves that ζ has no zeros when t is sufficiently large and
Re s>1−w(t), and that |ζ|≤C log(5t)+1 on the larger growth disks of
radius θ(log(5t)) centred at 1+δ+ih, t≤h≤4t, 0<δ≤1/2.

Fix sufficiently large positive t. Set L=log(5(t+1)), M=log L,
r=w(t+1), δ=r/4 and c=1+δ+it. Both θ and w decrease in this range.
Also 0<r≤1/100. For |z−c|<r, we have
t−1<Im z<t+1 and Re z>1−3r/4>1−w(Im z). Thus the disk is zero-free
and misses the pole. Since r≤θ(log(5t)), its zeta values are bounded
by Φ=C L+1. The same growth bound holds at 1+δ+2it.

The proved three-four-one lower bound at c gives

`−log|ζ(c)| ≤ (3/4)log(1+1/δ)+(1/4)log Φ+22/4`.

For sufficiently large t, `vk_log_Phi_le` gives log Φ≤2M and
`vk_log_delta_le` gives log(1+1/(7r))≤4M. Since
1+4/r≤28(1+1/(7r)) and log28≤27≤M,
log(1+1/δ)≤5M. Hence log(Φ/|ζ(c)|)+1≤8M.

Apply `HTGeometry.norm_logDeriv_le` with outer radius r, middle radius
r/2, inner radius r/4 and anchor m=|ζ(c)|. The target 1+it lies on
the inner disk. Therefore

`|ζ′/ζ(1+it)| ≤ 64 M/r
 = 102400000 L^(2/3) (log L)^(8/3)`.

For each η>0, `(log L)^(8/3)≤η L^(1/3)` eventually, by the proved
power-log asymptotic. Thus this upper bound is o(L). Finally
L≤2 log t for sufficiently large t, so it is o(log t).
Complex conjugation gives the identical estimate for negative t.

All analytic inputs are proved corpus declarations. No RH premise or
new zero-free assumption is introduced.

## Exact Gamma comparison

The existing conductor lower bound gives
`gammaIncrementSymbol(t) ≥ log|t|−C` for |t|≥2, with one fixed C.
Thus Γ(t)≥(log|t|)/2 eventually. Off t=0, taking real parts of
the exact pole splitting gives
`squarePrimeRegularSymbol(t)=−2 Re(ζ′/ζ(1+2it))`.
Apply the preceding theorem with ε/8. For |t|≥2,
log(2|t|)≤2log|t|; therefore

`|squarePrimeRegularSymbol(t)| ≤ (ε/4)log(2|t|)
 ≤ (ε/2)log|t| ≤ ε gammaIncrementSymbol(t)`.

This is an absolute estimate, so it controls either sign of the mixed
Fourier multiplier. No separate positive Gamma reserve is spent.

## Verification

Both modules passed direct checks from `formal/`:

```text
lake --old env lean GaloisForLFunctions/RHTower/Sieve/ZetaLogDerivIsSublogarithmic.lean
lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/TheSquarePrimeBoundaryIsLowerOrder.lean
```

Public endpoints:

- `RHTower.Sieve.exists_logDeriv_zeta_bound_loglog_div_width`
- `RHTower.Sieve.exists_logDeriv_zeta_le_epsilon_log_pos`
- `RHTower.Sieve.exists_logDeriv_zeta_le_epsilon_log_abs`
- `GaloisForLFunctions.ArithmeticIndexDescent.exists_half_log_le_gammaIncrement`
- `GaloisForLFunctions.ArithmeticIndexDescent.squarePrimeRegularSymbol_eq_neg_re_logDeriv`
- `GaloisForLFunctions.ArithmeticIndexDescent.exists_squarePrime_regular_abs_le_epsilon_gamma`

Both modules are wired into their umbrellas; umbrellas were not compiled.
No web search, novelty checks, numerical experiments or axiom checks.

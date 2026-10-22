# Endpoint oscillation Poisson tail bound — formalized closure

- **ID:** `ccm-endpoint-oscillation-poisson-tail-bound-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-endpoint-oscillation-poisson-tail-bound.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.SawtoothFourierSeries` — the conditionally convergent sawtooth sine
  series, absent from mathlib.
- `GaloisForLFunctions.RHTower.PeriodicFourierDecay` — absolutely convergent Fourier series and
  pointwise inversion for periodic `C²` functions, absent from mathlib.
- `GaloisForLFunctions.RHTower.PoissonSummationPiecewise` — Euler–Maclaurin at arbitrary real
  endpoints, both orders, and Poisson summation at `Ff(y) = O(1/y)` regularity.
- `GaloisForLFunctions.RHTower.CCM.CCMEndpointFourierJet` — the twice-integrated endpoint Fourier
  formula and the endpoint tail bounds.
- `GaloisForLFunctions.RHTower.CCM.CCMTwoModeDeficitScale` — the two-mode central correction.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(7)` | `expCoeff`, `norm_sum_exp_le`, `exists_tendsto_sum_expCoeff`, `tsum_expCoeff_mul_pow`, `one_sub_exp_mul_I_eq`, `arg_one_sub_exp_mul_I`, `im_neg_log_one_sub_exp`, `tendsto_sum_expCoeff`, `tendsto_sum_sawtoothSine`, `exists_sum_sawtoothSine_abs_le`, `exists_mem_Ioo_sub_int_mul_two_pi`, `sawtoothSine_periodic`, `exists_sum_sawtoothSine_abs_le_of_ne` | the one step unavailable in mathlib: `∑ sin(nθ)/n` is only conditionally convergent, so it cannot be stated as a `HasSum` at all (mathlib's Bernoulli Fourier expansions start at exponent three for this reason). Dirichlet's test with the corpus bound `RHTower.norm_geom_sum_le`, the generating function `-log(1 - x e^{iθ})` from `hasSum_taylorSeries_neg_log`, the polar chord `1 - e^{iθ} = 2 sin(θ/2) e^{i(θ-π)/2}`, and Abel's limit theorem; the sum is at most `π/2` in absolute value for every angle off the lattice `2πZ` |
| `(8)` | mathlib `hasSum_zeta_two` | no corpus work needed |
| `(5)`, `(1)`, `(2)` | Euler–Maclaurin and Poisson layer of `PoissonSummationPiecewise`, `sum_Ioc_symm`, `tendsto_poissonHalfSum` | Poisson summation at `Ff(y) = O(1/y)` regularity and the positive-half form `√u ∑_{m≥1} f(mu) = (1/√u)∑_{n≥1} Ff(n/u) - √u f(0)/2` for an even zero-integral source. The hypotheses `a/u ∉ ℤ`, `b/u ∉ ℤ` are exactly the card's "for almost every `v`". Both Euler–Maclaurin orders are needed: first order produces the endpoint jump terms, second order makes the remainder absolutely convergent |
| `(6)` | `hasDerivAt_linScaled`, `hasDerivAt_sinScaled`, `hasDerivAt_negCosScaled`, `integral_mul_cos_ibp`, `integral_mul_sin_ibp`, `integral_mul_cos_twice_ibp`, `integral_symm_eq_two_mul_of_even`, `integral_symm_eq_zero_of_odd`, `integral_symm_mul_cos_eq`, `integral_symm_mul_sin_eq_zero`, `integral_symm_mul_cos_endpoint_jet` | the twice-integrated endpoint Fourier formula with the `f'(0)` boundary term kept explicit, plus the even/odd reduction; vanishing of the sine transform is the reality of the Fourier transform of the even extension, used implicitly by the card |
| `(3)` | `endpointLeadTerm`, `endpointRemTerm`, `endpointLeadTerm_eq`, `exists_tendsto_sum_endpointLeadTerm`, `summable_one_div_sq`, `abs_endpointRemTerm_le`, `summable_endpointRemTerm`, `abs_tsum_endpointRemTerm_le`, `abs_fourierTail_le` | the leading series is exactly the sawtooth series at angle `2πλv`, so it is summed through `(7)` rather than term by term (term by term it would only give a divergent harmonic sum); the remainder converges absolutely with constant `1/12 = (1/2π²)(π²/6)`, so `(8)` enters exactly once |
| `(4)` | `L²(d*v)` bound in `CCMEndpointFourierJet` | proved without Minkowski |
| `(9)`–`(11)` | `twoModeSource`, `twoModeSource_eq_of_eigen`, `tendsto_one_of_tendsto_deficit`, `deficitScale_const`, `tendsto_twoModeSource_div_deficit` | `(10)` as an exact identity with no asymptotics — the *difference* of the two eigenvalues appears, which is the first-order cancellation the zero-integral normalisation creates; a vanishing deficit `d = 1 - c²` forces `c → 1`; the limiting constant evaluates in closed form to `-2^{-3/4}√(3/11)`; and the ratio to `d₁` has a finite nonzero limit, so the zero-mode Poisson correction of `(2)` is of concentration-deficit order, not square-root-leakage order |

The fixed-mode asymptotics enter `tendsto_twoModeSource_div_deficit` as explicit `Tendsto`
hypotheses, exactly as the card imports them from `constrained-prolate-two-mode-ground-state.md`;
the content of the statement is the *scale*.

## Axioms

`#print axioms` on every theorem of all five modules returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

The card's own remaining open gates: fixed-mode endpoint-jet asymptotics at cofinal strength, the
closed-Weil residual estimate relative to the constrained gap, and projective determinant transfer
to `Xi`.

## Verification performed

- `lake env lean` on a scratch file importing the modules: no errors.
- `#print axioms` on every theorem: clean.

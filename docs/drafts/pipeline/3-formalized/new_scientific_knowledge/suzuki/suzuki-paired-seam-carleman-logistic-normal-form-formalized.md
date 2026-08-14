# The paired seam Carleman logistic normal form, formalized

- **ID:** `suzuki-paired-seam-carleman-logistic-normal-form`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-paired-seam-carleman-logistic-normal-form.md`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/ReflectionIntegral.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiPairedSeamScalar.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiLogisticCoupling.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiPairedSeamNormalForm.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)` the two oriented seam germs | `seamRight`, `seamLeft`, `seamRight_comp_neg`, `seamLeft_comp_neg` |
| `(2)` the fixed-window logarithmic jump | `jumpNear`, `jumpFar`, `jumpOpposite`, `logJumpRight`, `logJumpLeft` |
| `(3)` the seam operators | `seamR`, `seamC` |
| `(5)` the seam scalar | `seamScalar`, `hasDerivAt_seamScalar` |
| exponential charts | `image_nearChart`, `image_farChart`, `image_oppositeChart` |
| `(9)` near same-side window | `jumpNear_eq` |
| `(10)` far same-side window | `jumpFar_eq` (unsplit), `jumpFar_split` (Volterra–Gamma form) |
| `(12)` opposite window | `jumpOpposite_eq` |
| `(13)` exact scalar seam integral | `integral_Ioi_carlemanCutoffFactor` = `L + log(1+e^{-L})`, `carlemanScalarPrimitive` |
| `(14)` opposite window, split | `jumpOpposite_split`, `integrableOn_carlemanCutoffFactor` |
| `(4+)`, `(4-)` exact paired normal form | `logJumpRight_eq`, `logJumpLeft_eq` |
| `(8)` physical endpoint | `logJumpRight_eq_of_zero_exterior` |
| `(15)` cutoff derivative | `hasDerivAt_carlemanCutoffFactor_left` |
| `(6)` logistic cross coupling | `logisticCoupling`, `hasDerivAt_seamC` |
| `(16)` Gamma conjugation | `expMul_logisticCoupling_eq` |
| `(17)` the moment as a beta integral | `mobiusChart`, `integral_Ioi_comp_mobiusChart`, `integral_Ioi_rpow_div_one_add_sq_eq`, `betaIntegral_shift_eq_ofReal`, `integral_Ioi_comp_exp`, `integral_exp_neg_mul_logistic` |
| `(7)` exact weighted norm | `logisticMoment`, `logisticMoment_eq` = `σπ/sin(πσ)`, `logisticMoment_zero` = `1`, `integrable_expMul_logisticKernel`, `lintegral_sq_expMul_logisticCoupling_le` |
| `(19+)` differentiated paired equation | `normalFormRight`, `hasDerivAt_seamPrimitive`, `hasDerivAt_normalFormRight` |
| `(20)` terminal coercivity | `eventually_terminal_coercive` |
| reflection value | `integral_Ioi_rpow_div_one_add` = `π/sin(πσ)` |

## What the card actually closes

The three windows of the fixed-window logarithmic jump are transported by the exponential charts
`y = e^{-L}e^{-s}`, `y = e^{-L}e^{s}`, `y = -e^{-v}`, each an injective chart with an explicit
derivative, so `integral_image_eq_integral_abs_deriv_smul` gives the chart identities `(9)`, `(10)`
and `(12)` with no integrability hypothesis whatever.  Splitting `e^s/(e^s-1) = 1 + 1/(e^s-1)` and
reflecting `s ↦ L - s` by the measure-preserving map produces the Volterra term
`L F₊(L) - ∫₀^L F₊`; the opposite window separates against the exact scalar
`∫₀^∞ dv/(1+e^{v-L}) = L + log(1+e^{-L})`, whose primitive `v - log(1+e^{v-L})` also certifies that
the cutoff factor is integrable on the ray.  Adding the three gives `(4+)` on the nose, and
composing with `x ↦ -x` gives `(4-)`.

The cross block is bounded exactly as the card claims.  Differentiating the cutoff factor in the
cutoff scale gives the logistic density `k(v-L)`; a bounded profile dominates the differentiated
integrand by `C e · e^{-|v-L|}` uniformly on a ball, so differentiation under the integral sign
applies and `(C F)' = K F`.  Conjugating by `e^{σL}` and reflecting `v = L - y` turns `K` into
convolution by `e^{σt}k(t)`, whose mass is evaluated in closed form: the Möbius chart
`x ↦ x/(1-x)` carries `∫₀^∞ z^{-σ}/(1+z)² dz` to the Euler integral of the first kind, which is
`Β(1-σ,1+σ) = Γ(1-σ)Γ(1+σ) = σπ/sin(πσ)` by the complex beta identity and Euler reflection, and
the exponential chart `z = e^t` returns it to `m_σ`.  Evenness of `k` extends the value to
`-1 < σ < 0`, and `m_0 = 1` is the probability normalization.  Young's inequality in the
hypothesis-free `ℝ≥0∞` form then bounds the conjugated cross block by `m_σ` on the whole open
strip `|σ| < 1`: the paired Carleman block is a bounded zero-order operator with its first
singularity at the same height one as Gamma transport.

## Hypotheses

Object data only.  The chart identities `(9)`, `(10)`, `(12)`, the scalar `(13)`, the cutoff
derivative `(15)`, the moment `(17)`/`(7)` and the weighted bound carry no hypothesis on the
profile beyond measurability.  The splittings `(10)`-split and `(14)` and the normal forms `(4±)`
carry exactly the convergence assumptions the card states — the germ is integrable on `(0,L)`, the
same-side difference integral converges, and the cross integrand is integrable on the ray — and
`hasDerivAt_seamC` assumes the profile is bounded, which is the card's standing assumption on `u`.
No RH, no spectral premise, no `sorry`, `axiom`, `opaque`, or `unsafe`.  Every theorem named above
audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The card's own open gates are untouched and remain open: the infinite paired orbit assembly, the
half-log trace support theorem, shifted `L²` for the complete paired state, trace-zero entry into
`H¹₀`, completed Evans injectivity, and RH.  What is now closed is the local statement: the
Carleman cross block is not an additional weighted source obstruction.

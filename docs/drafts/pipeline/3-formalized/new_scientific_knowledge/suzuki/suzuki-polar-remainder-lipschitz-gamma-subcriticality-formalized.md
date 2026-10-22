# Suzuki's polar remainder is Lipschitz and Gamma-subcritical, formalized

- **ID:** `suzuki-polar-remainder-lipschitz-gamma-subcriticality`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-polar-remainder-lipschitz-gamma-subcriticality.md`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/ExponentialDividedDifference.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPolarRemainderLipschitz.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPolarConvolutionRate.lean`
  - kernel and removable singularity (pre-existing):
    `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiWeilPositionTorqueCurvature.lean`,
    `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiWeilRemainderRegularity.lean`
  - Cauchy–Schwarz (pre-existing): `formal/GaloisForLFunctions/HTGeometry/IntegralCauchySchwarz.lean`

## Formal content

| Card | Lean |
|---|---|
| `(9)`–`(10)` literal source formula | `suzukiWeilRemainderSecondDerivative`, `suzukiWeilRemainderKernel` (pre-existing) |
| `(11)`–`(14)` removable singularity, structural form | `expDivOne`, `expDivTwo` (pole-free `∫₀¹ e^{tx}dt`, `∫₀¹ (1-t)e^{tx}dt`), `expDivOne_eq_of_ne`, `expDivTwo_eq_of_ne`, `suzukiPolarCore`, `suzukiPolarCore_eq_of_pos`, `suzukiPolarCore_zero` (`= 1/4`) |
| `(15)` even form `r₁''(t) = h(|t|)` | `suzukiWeilRemainderKernel_eq` (`r'' t = -2 cosh(t/2) + suzukiPolarCore |t|`, all `t`) |
| `(16)`, `(1)` local Lipschitz | `abs_expDivOne_sub_le`, `abs_expDivTwo_sub_le` (1-Lipschitz on `Iic 0`), `abs_suzukiPolarCore_sub_le`, `abs_suzukiWeilRemainderKernel_sub_le` |
| `(17)` finite `M_a`, `L_a` | `abs_suzukiPolarCore_le`, `abs_suzukiWeilRemainderKernel_le`, `suzukiPolarSup`, `suzukiPolarLip` |
| `(18)` Cauchy–Schwarz on the aperture | `sq_integral_abs_le` |
| `(19)`, `(3)`–`(4)` sup bound | `abs_suzukiPolarConvolution_le` |
| `(20)`, `(4)` Lipschitz bound | `abs_suzukiPolarConvolution_sub_le` |
| `(5)`–`(6)`, `(21)` boundary-log rate | `suzukiPolarBoundaryTrace`, `abs_suzukiPolarBoundaryTrace_sub_le` |
| `(7)`, `(22)` derivative rate | `abs_deriv_suzukiPolarBoundaryTrace_le` |
| `(8)`, `(23)`, `(27)` Gamma-subcriticality | `integrableOn_sq_expMul_deriv_suzukiPolarBoundaryTrace` |

## What the card actually closes

The apparent pole of `e^{-s/2}/(1-e^{-2s}) - 1/(2s)` is removed *structurally*, not by a limit:
both the numerator and the denominator of Suzuki's polar block factor through the first two
exponential divided differences, which are defined here as parameter integrals over `[0,1]`.  On
the closed negative half line those integrals are trapped between `exp x` and `1` (respectively
`exp x / 2` and `1/2`) and are 1-Lipschitz, because `exp` is 1-Lipschitz there.  Hence the polar
core is a quotient of Lipschitz functions with denominator at least `e^{-2T}` on `[0,T]`, so it is
Lipschitz with constant `5 e^{4T}` — and composing with the contraction `|·|` transports that to
the even kernel.  This is the exact strengthening the card asks for: `C²` regularity of the
remainder was already formal, and the modulus of `r''` was the missing datum.

The operator half follows with literal constants: on the collar `|x| ≤ a+1` the kernel argument
stays in `|t| ≤ 2a+1`, so `K_a u` is bounded by `suzukiPolarSup a · ‖u‖₁` and Lipschitz with
constant `suzukiPolarLip a · ‖u‖₁`, and `‖u‖₁² ≤ 2a ‖u‖₂²`.  In the chart `x = x₀ + ε e^{-L}` the
Lipschitz property becomes the exponential boundary rate.  For the derivative the `deriv`
convention makes the statement unconditional: at a point of differentiability the slope comparison
against `L ↦ e^{-L}` gives `|G'(L)| ≤ C e^{-L}`, and at a point of non-differentiability `deriv` is
zero, so the bound holds everywhere on `L > 0` with no Rademacher input.  Squaring and integrating
against `e^{2σL}` then gives square integrability for every `σ < 1` — the polar convolution is
Gamma-subcritical forcing and cannot sustain an inverse-log-flat completed zero mode.

## Hypotheses

Object data only: `0 ≤ a`, the collar bounds `|x| ≤ a+1`, `|x₀| ≤ a`, `|ε| ≤ 1`, `0 < L`,
`0 < σ < 1`, and interval integrability of the profile `u` (and of `u²` for the Cauchy–Schwarz
step).  No RH, no spectral premise, no regularity of `r''` assumed in order to prove it, no
numerical certificate, and no `sorry`, `axiom`, `opaque`, or `unsafe`.  Every theorem named above
audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The open gates are research and remain open: constructing the completed-mode valuation normal
family so that the normal equation `(25)` holds in the root-retained rigged carrier, the exact
cutoff intertwining, the weighted trace-zero source gate, and RH or a whole-program no-go.

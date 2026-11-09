# Local identification of the Euler–FE defect

- **Stage:** 3-formalized
- **Programme:** Euler–FE transport theory; exact-event theory.
- **Statement:** The actual Hamburger theta kernel on any nonempty open interval
  of positive scales determines every measurable polynomially bounded defect
  almost everywhere. Integrable defects in the original strip class vanish pointwise.

## Mathematical mechanism

Write `H_g(t)=Γℝ(½+2it)g(t)`. Gamma decay makes `H_g` integrable with a positive
exponential moment, even when `g` has infinite unweighted mass and energy. In
logarithmic coordinates the actual kernel satisfies

    exp(u/4) K_g(exp u) = (2π)⁻¹ Fourier(H_g)(u/(2π)).

The exponential moment gives holomorphic extension to a strip. Equality on an
open scale interval therefore propagates to all positive scales. Fourier
injectivity and nonvanishing of Gamma then identify `g` almost everywhere.
The original strip identity upgrades the vanishing conclusion to pointwise vanishing.

This establishes faithfulness from local data for the full polynomial-growth
defect class, beyond finite energy. It supplies no missing height recurrence or
positivity statement for ζ.

## Paper proof

The Gamma bound is `|Γℝ(½+2it)| ≤ A(1+|t|)^M exp(-|t|)`.
For polynomially bounded `g`, the exponential series absorbs the polynomial,
giving `|H_g(t)| ≤ K exp(-|t|/2)`. Thus
`F_g(z)=∫ H_g(t) exp(-izt)dt` is holomorphic on `|Im z|<½`.
Factoring `exp(-u(¼+it))` proves the displayed Fourier identity, with
`F_g(u)=Fourier(H_g)(u/(2π))`.

If `K_g` vanishes on `(a,b)`, `0<a<b`, then `F_g` vanishes on
`(log a,log b)`. The identity theorem on the connected strip gives `F_g=0`
on the real axis. Injectivity of the Fourier transform on `L¹` gives `H_g=0`
almost everywhere. Gamma has no zeros on this line, hence `g=0` almost
everywhere. Apply this to `g-h` for identification of two defects.

After rational-prime classification, Jacobi's exact theta law sets `K_g=0`;
the same argument annihilates the original integrable defect almost everywhere.
This gives membership in the zero `L²` class. The proved finite-energy strip
theorem then gives pointwise vanishing, using continuity of the Gamma-weighted
source forced by the original boundary identity. No `L²` premise is added.

## Lean

`EulerFETransportTheory/LocalThetaDataDetermineTheDefect.lean` proves
`gammaWeightedDefect_exponential_bound`, `defectKernel_exp_eq_fourier`,
`ae_eq_zero_of_defectKernel_eq_zero_on_interval`, and
`ae_eq_of_defectKernel_eq_on_interval`. Direct check and transitive axiom audits
pass with only `propext`, `Classical.choice`, and `Quot.sound`.

`IntegrableRigidityAnnihilatesTheDefect.lean` proves the terminal theorem
`beurling_integrable_strip_defect_eq_zero`, with the same successful direct check
and transitive standard-axiom audit. Both modules are wired into the programme umbrella.

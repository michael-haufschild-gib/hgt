# Recovering the exceptional layer at escaping heights

- **ID:** ELT-PHASE
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** review-0911/obstacles-summary.md §2.10, tower/current comparison
- **Statement:** At supercritical exponential damping, the pole-subtracted prime current has a finite almost-periodic profile in the phase `(at+log(t/2))/2`, with the actual top ordinates as frequencies.

## Exact law

Let β be the isolated top, `θ<σ<β`, `a(β−σ)>π/2`, `s=σ+it`,
`y=e^(−at)`, and `K(y,w)=½Γ(w/2)y^(−w/2)`. The normalized expansion is

    [ΣΛ(n)n^(−s)e^(−yn²) + e^(−y)ζ′/ζ(s) − K(y,1−s)] / K(y,β−s)
      + Σ_{Re ρ=β} exp(π Im ρ/4)
          exp(i Im ρ · (at+log(t/2))/2) → 0.

Copies encode multiplicity. The finite-profile statement must be derived
from the full infinite-current expansion, not imposed on an abstract model.

## Proof [PROVED HERE]

The analytic input is the Gamma quotient on a vertical line:
`Γ(z+iγ/2)/(Γ(z)z^(iγ/2))→1`, `z=(β−σ)/2−it/2`.
The corpus proves a complex-shift integral and a half-plane digamma estimate;
its existing complex-ray quotient theorem assumes a positive real slope and
does not cover this vertical line. Integrate the digamma estimate along the
fixed imaginary segment, retaining the principal-log branch. More precisely,
for `Re z>0`, `Re(z+w)>0`, `|z|≥2|w|+4`, the integral exponent satisfies

    |∫₀¹ wψ(z+uw)du − w log z|
      ≤ |w|(3/(|z|−|w|)+2|w|/|z|).

The first term bounds `ψ(z+uw)−log(z+uw)`; the second follows from
`log(z+uw)−log z=log(1+uw/z)`. Both factors in this logarithm splitting
have positive real part, so their arguments sum inside `(-π,π)`.
For the descending vertical line, `|z|→∞`, giving the quotient limit.

For a top ordinate γ, divide its Gaussian mode by the real reference mode.
The damping ratio is exactly `exp(iγat/2)`. The Gamma quotient is
`z^(iγ/2)(1+o(1))`. Since
`log z=log(t/2)−iπ/2+o(1)`, the ratio differs by `o(1)` from
`exp(πγ/4)exp(iγ(at+log(t/2))/2)`. Its norm stays bounded, allowing
the multiplicative Gamma error to be converted to an additive error.

For a lower mode ρ, multiply its polynomial/exponential upper bound by
the reciprocal reference bound. Their exponential rates differ by
`a(Re ρ−β)/2<0`; hence their ratio tends to zero. This avoids any
unproved uniform Gamma quotient across lower layers.

The supercritical reference mode grows, so the complete expansion error
divided by it vanishes. Summing the finitely many mode limits proves
the displayed profile from the full infinite-current expansion.
An almost-periodic recurrence argument would then give unbounded-height
excursions of the normalized pole-subtracted current.

## Consequence and limit

This identifies the high-height echo of the low exceptional layer and
the observation phase at which it is read. It does not produce any new
zero at those heights: a current excursion and a zero replica are distinct.
## Formalization

`formal/GaloisForLFunctions/ExceptionalLayerTheory/TheExceptionalLayerAtEscapingHeights.lean`
passed `lake --old env lean` without output artifacts. Audited declarations:

- `tendsto_gamma_imaginary_shift_ratio`
- `tendsto_gaussianMode_ratio_sub_ordinateWave`
- `tendsto_gaussianMode_ratio_zero_of_re_lt`
- `not_asymptoticAbscissaLaw_has_escaping_layer_profile`

All are in namespace `GaloisForLFunctions.ExceptionalLayerTheory` and use
only `propext`, `Classical.choice`, and `Quot.sound`. The programme umbrella
imports the module. Sharp recurrent envelopes are a separate open refinement
in `../1-in-progress/elt-recurrent-layer-envelope.md`.

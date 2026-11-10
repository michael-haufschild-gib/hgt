# The first variation of the arithmetic Green limit

- **ID:** the-first-variation-of-the-arithmetic-green-limit
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B133; the arithmetic-clock realization of Weil's form.
- **Target:** Identify the exact first-order defect of the coupled Green energy,
  including its strict positivity on nonzero compact smooth packets.

## Statement

For real `f ∈ C_c²(ℝ)`, write `A_f(t)=∫f(u)f(u+t)du` and set

`J(f)=∫ [exp(−5|t|/2)/(1−exp(−2|t|))²] [A_f(0)−A_f(t)] dt`.

The boundary law is

`(weilQuad(f)−coupledGreenEnergy(r,f))/(1−r²) → J(f)` as `r↑1`,

with `0≤J(f)≤∫(f')²/2` and `J(f)>0` whenever `f≠0`.
Thus the damping error has a nonzero first-order coefficient, not merely
an upper bound. No positivity assertion about Weil's form is involved.
In particular, for each nonzero packet, eventually
`(1−r²)J(f)/2 < weilQuad(f)−coupledGreenEnergy(r,f) < 2(1−r²)J(f)`.

## Proof

Arithmetic saturation cancels the prime term exactly. Away from `t=0`,
the remaining normalized kernel is

`exp(−5|t|/2)/[(1−exp(−2|t|))(1−r²exp(−2|t|))]`.

Its limit is the kernel defining `J`. For `0≤r<1`, both denominators are
positive away from zero. The autocorrelation deficit is nonnegative and
at most `t²∫(f')²/2`. The established kernel inequality
`t²(ω−K_r)≤(1−r²)exp(−|t|/2)/4` therefore bounds the normalized
integrand by `exp(−|t|/2)∫(f')²/8`. This majorant integrates to
`∫(f')²/2`. All integrands are measurable; dominated convergence proves
the boundary law, integrability of `J`, and its bounds. Values at zero
do not affect the integral.

For a nonzero continuous compact packet, `∫f²>0`: its squared function
is positive on a nonempty open interval. The autocorrelation has compact
support. On a nonempty open interval to the right of that support and
of zero, the deficit is exactly `∫f²`; the limiting kernel is strictly
positive there. The nonnegative integrand consequently has positive
integral. This proves strict positivity without assuming Weil positivity.
Convergence of the normalized defect into `(J/2,2J)` and multiplication
by the positive damping gap prove the two-sided bound.

## Inputs and formalization

Corpus search of every `archDamped` declaration found convergence and
Sobolev upper bounds, but no normalized-defect limit. Inputs:
`weilQuad_sub_coupledGreenEnergy_eq`,
`sq_mul_archProfile_sub_archDamped_le`,
`autocorr_origin_deficit_le_derivative_energy`, and dominated convergence.
Formalized in
`formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheFirstVariationOfTheArithmeticGreenLimit.lean`.
Plain `lake --old env lean` passes without warnings. All four printed
axiom audits contain only `[propext, Classical.choice, Quot.sound]`.
The module is imported by the programme umbrella.

In namespace `GaloisForLFunctions.HyperbolicArakelovTheory`:

- `greenResponse_bounds`, `greenResponse_pos`;
- `PrimeSuspension.tendsto_normalized_coupledGreen_defect`;
- `PrimeSuspension.coupledGreen_defect_exact_order`.

The amplitude-growth endpoint is not claimed without a formal
quadratic-scaling bridge.

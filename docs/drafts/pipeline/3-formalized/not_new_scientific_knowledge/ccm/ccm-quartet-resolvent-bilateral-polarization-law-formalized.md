# Quartet resolvent bilateral polarization — formalized closure

- **ID:** `ccm-quartet-resolvent-bilateral-polarization-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-quartet-resolvent-bilateral-polarization-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCM.CCMQuartetResolventPolarization` — the scalar algebra.
- `GaloisForLFunctions.RHTower.CCM.CCMQuartetPaleyWiener` — the Paley–Wiener half.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(2)`–`(4)` | `ccmQuartetPairResolvent`, `ccmCausalResolvent`, `ccmAntiCausalResolvent`, `ccmQuartetCrossPacket`, `ccmQuartetPositiveSquare`, `ccmQuartetNegativeSquare`, `ccmQuartetCrossPacket_eq_positive_sub_negative` | the objects, and the cross packet as one positive square minus one negative square |
| `(9)` | `ccmQuartetPairResolvent_kernel_split` | the kernel split |
| `(5)`, `(10)` | `ccmQuartetResolvent_eq_crossPackets` | the full quartet quotient is exactly the sum of the `λ` and `conj λ` cross packets |
| transverse charge | `ccmCausal_sub_antiCausal`, `ccmCausal_sub_antiCausal_ne_zero` | the negative coordinate is `λ + conj λ = 2 Re λ` over the two resolvent denominators, hence nonzero at every real node away from the poles exactly when the zero is off the line — the formal form of "in the critical-line limit the odd mode vanishes; off the line it is nonzero" |
| Laplace ray | `integrableOn_Ioi_cexp_neg_mul`, `integral_Ioi_cexp_neg_mul`, `integral_Ioi_exp_neg_mul` | `∫_0^∞ e^{-bt} dt = 1/b` for `Re b > 0`. Mathlib has the Gaussian and Gamma integrals but not this one; proved from the fundamental theorem of calculus on `Ioi 0`, tail limit from `‖e^{-bt}‖ = e^{-(Re b)t}` |
| `(7)`, `(11)` | `ccmCausalResolvent_eq_laplace`, `ccmAntiCausalResolvent_eq_laplace` | each resolvent coordinate is the Laplace transform of its shifted ray, on exactly the node range the card specifies |
| `(3)` | `quartetSymCoord`, `quartetAntisymCoord`, `ccmQuartetPositiveSquare_eq`, `ccmQuartetNegativeSquare_eq` | the two light-cone coordinates `u`, `v`, and the identification of the squares as `u(x) conj u(y)` and `v(x) conj v(y)`, which makes `(4)` a statement about coordinates rather than about squares |
| `(6)`, `(12)` | `cexp_ray_cosh_split`, `cexp_ray_sinh_split`, `quartetSymCoord_eq_laplace`, `quartetAntisymCoord_eq_laplace` | the two coordinates are the `cosh` and `sinh` Laplace transforms, so the horizontal displacement `a` is carried by the odd hyperbolic mode and not by the ordinate phase |
| `(15)` | `quartetResidueMode`, `norm_quartetResidueMode`, `integral_norm_sq_quartetResidueMode` | the residue mode of `(14)` has squared norm exactly `2m²/a` |
| `(16)` | `four_mul_lt_integral_norm_sq_quartetResidueMode` | for `0 < a < 1/2` and multiplicity at least one, the metric reading strictly exceeds four trace units per multiplicity unit; the inequality reduces to `m > 2a`, which is exactly why `a < 1/2` is the right hypothesis |

## Axioms

`#print axioms` on every theorem of both modules returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

The index equality `(13)` — the Krein–Langer minimality statement the card *cites* rather than
proves — and the operator-level identification of `J`, which needs an analytic Xi logarithmic kernel
and a half-plane Hardy graph. Everything the card proves, `(2)`–`(12)` and `(14)`–`(16)`, is
unconditional in Lean.

## Verification performed

- `lake env lean` on a scratch file importing both modules: no errors.
- `#print axioms` on every theorem: clean.

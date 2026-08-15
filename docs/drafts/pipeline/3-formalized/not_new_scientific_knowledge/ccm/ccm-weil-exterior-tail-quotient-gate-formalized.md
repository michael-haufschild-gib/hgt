# Weil exterior-tail quotient gate — formalized closure

- **ID:** `ccm-weil-exterior-tail-quotient-gate-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-weil-exterior-tail-quotient-gate.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCMWeilRadicalTailQuotient`

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| setup | `IsBiadditive`, `weilRadical`, `weilRadicalSubgroup` | the pairing and its two-sided radical. Only additivity in each argument is assumed: no sesquilinearity, no scalars, no topology, no form domain — which is why the identity needs none of the analytic interface |
| `(2)` | `radical_pair_left`, `radical_pair_right` | radical pairing vanishes on either side |
| `(3)` | `radical_diag_eq` | `QW(a,a) = QW(b,b)`, by expanding `a = h - b` and killing every term containing `h` |
| `(4)` | `radical_quotient_eq_neg` | in `D/Rad(QW)` the aperture class is exactly the negative of the exterior-tail class |
| density lemma core | `integral_scaledBump`, `integral_sq_scaledBump`, `tendsto_integral_sq_scaledBump` | `β_R x = R⁻¹ β(x/R)` preserves the integral while its squared `L²` norm scales by `R⁻¹`, so the integral of an approximant can be corrected to zero at `L²` cost tending to zero |
| `(6)`–`(7)` | `lt_setIntegral_normSq_of_exceeds` | the unboundedness step with no closed-operator extension: if `‖m‖²` exceeds `C²` on a set of positive finite measure, the multiplier bound already fails at the indicator of that set. The card routes `(6)` through closedness of the multiplication operator and its extension to all of `L²`; the Lean statement exhibits the failing test vector directly |

## Axioms

`#print axioms` on every theorem returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

Genuinely external and imported: Connes–Consani's radical membership `E(f) ∈ Rad(QW)` and the Mellin
multiplier formula `(5)`; the Schwartz/Fourier side conditions defining `S_0`; and unboundedness of
`zeta` on the critical line, which supplies the set `S` consumed by
`lt_setIntegral_normSq_of_exceeds`. The graph norm `(8)` is a definition, not a theorem.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.

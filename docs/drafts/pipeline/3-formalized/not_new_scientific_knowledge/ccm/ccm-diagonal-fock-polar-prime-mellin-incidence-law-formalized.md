# Formalization certificate — `ccm-diagonal-fock-polar-prime-mellin-incidence-law`

- **Card:** `ccm-diagonal-fock-polar-prime-mellin-incidence-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMDiagonalFockColligation.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 7 theorems
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(9)` Cauchy channel | `cauchy_channel_eq` |
| `(11)` shifted polar channel | `polar_channel_eq` |
| `(10)` prime feature Gram | `prime_feature_mul` |
| `(6)`, `(8)` incidence rearrangement | `colligation_rearrange`, `colligation_rearrange'` |
| `(18)` quadratic-form colligation | `quadratic_colligation` |
| `(19)` four-channel passivity criterion | `passivity_iff` |

Reused, not rebuilt: `RHTower.integral_exp_ray` (`CCMHalfUnitCauchySeam.lean`).

## Deliberately outside the Lean statement

- the Laplace–Stieltjes identity `(7)`;
- the Krein Gram representation `(12)`;
- the RKHS `H_A` and the diagonal Fock theorem;
- the Paley–Wiener identification of `T₀` with the residue bundle.

The card's remaining open gates (derive the colligation from the Gauss-paired/Sonin source
operator; prove cofinal passivity `(19)`; RH) are route gates, not statements of this card.

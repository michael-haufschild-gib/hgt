# Prime-source ground incidence and divisor response — formalized closure

- **ID:** `ccm-prime-source-ground-incidence-response-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-prime-source-ground-incidence-response.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCMPrimeSourceGroundIncidence` (new)
- `GaloisForLFunctions.HTGeometry.HellmannFeynman` — pre-existing, carrying equation `(4)`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)`, `(3)` | `weilEnergy`, `weilFloor` | the coefficient-pointed energy and its floor |
| affineness | `weilEnergy_affine` | the energy is affine in the coefficient vector — the whole mechanism of the concavity proof |
| concavity | `weilFloor_concave` | the floor is the pointwise infimum of an affine family, hence concave |
| local Lipschitz | `abs_weilFloor_sub_le` | explicit modulus `M ∑_n \|b_n − b'_n\|` from a uniform bound on the correlation forms |
| `(4)` | `HTGeometry.hellmann_feynman` (pre-existing) | applied along the coordinate line `t ↦ b + t e_n` with `w = −v_n ξ`, giving `∂_{b_n} ε = −V_n(ξ,ξ)` |
| `(8)` | `eigenvector_response` | `(A − ν)ξ' = ν'ξ − w` along a differentiable eigenpair. Neither the normalization nor the phase condition is needed for the identity; they are what make the reduced resolvent invert it |
| `(6)`–`(7)`, sign | `hessian_nonpos` | a nonnegative reduced resolvent makes the Hessian form nonpositive |
| `(10)` | `readout_response` | any continuous linear readout of the ground state has derivative the readout of the eigenvector response; the Mellin transform is one such readout |

## Axioms

`#print axioms` on all six declarations returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- Kato's bounded-form perturbation theorem supplying the differentiable local eigenpair under the
  simple-isolated hypothesis.
- Positivity of the reduced resolvent, which is what the sign statement consumes.
- The cofinal estimates of the route consequence, which are the card's own open gates.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMPrimeSourceGroundIncidence`: success.
- `#print axioms` on every theorem: clean.
- Umbrella import added.

# Formalization certificate — `ccm-source-normalized-nonschatten-birman-schwinger-line-law`

- **Card:** `ccm-source-normalized-nonschatten-birman-schwinger-line-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMNonSchattenBirmanSchwinger.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 5 theorems
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(4)` Birman–Schwinger factorization | `birmanSchwinger_factorization` |
| `(5)` canonical normalization | `birmanSchwinger_identity_at_normalization` |
| `(11)` sufficient direction of the norm criterion | `posDef_one_sub_smul` |
| `(16)`–`(17)` explicit lower chamber estimate | `inv_sqrt_le_telescope` |
| `(8)` non-Schatten comparison | `not_summable_of_eventually_inv_nat_le` |

## Deliberately outside the Lean statement

- the analytic operator `A_a^+`, its compact resolvent and the frame identity `(2)`;
- the form comparison `(12)` and the eigenvalue asymptotics `(13)`–`(15)`;
- the min–max principle;
- Yoshida's criterion and the determinant-line identification `(20)`.

The card's remaining open gates (prove `μ_a‖R_a‖ < 1` at every aperture; RH) are route gates, not
statements of this card.

# Formalization certificate — `ccm-spectral-parameter-evans-completion-carrier-law`

- **Card:** `ccm-spectral-parameter-evans-completion-carrier-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMSpectralParameterEvans.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 7 declarations
- **Hypotheses:** the operator identities of Suzuki's construction and the card's own fibrewise
  isomorphism `(9)`, both carried explicitly; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(5)` shifted symbol | `shiftedSymbol`, `shiftedSymbol_mul_eq_zero_iff` |
| `(2)` → `(7)` reduction | `multiplier_eq_of_generalized`, `shiftedOperator_eq_zero_of_generalized` |
| `(9)` → `(10)` Morse sum | `finrank_ker_eq_of_linearEquiv`, `sum_finrank_ker_eq` |
| `(11)` positivity ⟺ injectivity | `forall_ker_eq_bot_iff` |
| prime–Gamma resource wall | corpus `HTGeometry.not_summable_primeLogHerglotzTransportMassOrder_of_pos` |

## Deliberately outside the Lean statement

- the closed screw form, `S_{a,μ}` and the completion `H(S_{a,μ})`;
- the non-inclusion `(3)` (Suzuki, Section 8);
- the Neumann inverse and the exact multiplier `W_a(D)`;
- the isometry `(6)`.

The card's remaining open gates (prove the generalized eigenvectors enter the logarithmic Evans
domain, or construct the Evans/Fredholm complex on `H(S_{a,μ})`; identify the determinant line;
prove zero Morse charge; RH) are route gates, not statements of this card.

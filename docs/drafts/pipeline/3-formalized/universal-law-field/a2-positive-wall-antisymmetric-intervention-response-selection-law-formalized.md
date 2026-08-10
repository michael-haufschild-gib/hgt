# A₂ positive wall and antisymmetric intervention-response selection — Lean certification

- **ID:** ULF-A2R-1
- **Paper card:** `a2-positive-wall-antisymmetric-intervention-response-selection-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveAntisymmetricWallResponse`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Reused, not rebuilt

- `ConstitutiveStabilityWall` (certification of ULF-LSW-1): `wallCharge₁`, `wallCharge₂`,
  `wallCharge₁_im`, `wallCharge₂_im`, `wallCharge_im_pos`, `wallCharge_cross`, `wallCharge_sum`,
  `arg_lt_arg_iff_cross_pos`, `stability_iff`, `arg_eq_of_arg_eq`, `wallFamily_stable_iff_pos`;
- `ConstitutivePositiveResponse`: `constitutivePositiveDoctrine`, `constitutiveAdditiveResponse`,
  `constitutivePositiveDoctrine_hasDerivAt_intervention`,
  `constitutivePositiveDoctrine_unit_phase`.

## Certified declarations

### Clause 1 — the passive packet is even

- `wallPositivePacket` — the triple `(|z₁|², |z₂|², |z₁+z₂|²)` of equation (3);
- `wallPositivePacket_eq` — it equals `(1, 1, 4 cos²θ)`;
- `wallPositivePacket_even` — `𝒫(−θ) = 𝒫(θ)`, so the complete passive positive data do not
  determine the chamber.

### Clause 2 — the fixed intervention and equation (4)

- `wallCharge₁_re θ = −sin θ`, `wallCharge₂_re θ = sin θ` (new);
- `constitutiveAdditiveResponse_one z = 2 Re z`;
- `wallResponse₁_hasDerivAt`, `wallResponse₂_hasDerivAt` — the component responses are the genuine
  real derivatives `d/dε|₀ |z_j(θ) + ε|²`, not merely an algebraic definition;
- `wallResponse₁_eq = −2 sin θ`, `wallResponse₂_eq = 2 sin θ`;
- `antisymmetricWallResponse`, `antisymmetricWallResponse_eq` — equation (5): `Δ(θ) = 4 sin θ`.

### Clause 3 — the full stability trichotomy

`ConstitutiveStabilityWall` certified only the stable side.  This module completes it:

- `im_mul_conj_swap` — the cross product changes sign under swapping the factors;
- `wallFamily_unstable_iff_neg` — `(z₁+z₂).arg < z₂.arg ↔ θ < 0`;
- `wallFamily_semistable_iff_zero` — `(z₁+z₂).arg = z₂.arg ↔ θ = 0`, the backward direction from
  `arg_eq_of_arg_eq` at the point where the two charges coincide;
- `sin_pos_iff_of_abs_lt`, `sin_neg_iff_of_abs_lt`, `sin_eq_zero_iff_of_abs_lt` — the sign
  dictionary on `(−π/2, π/2)`;
- `stable_iff_response_pos` (6), `semistable_iff_response_zero` (7), `unstable_iff_response_neg`
  (8).

### Capstones

- `antisymmetric_response_selects_chamber` — all three clauses in one statement;
- `antisymmetric_response_not_factoring` — at `θ` and `−θ` the complete passive packet agrees while
  `Δ` changes sign, so this response provably does **not** descend through the positive quotient.
  This is the card's operational test made into a theorem.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveAntisymmetricWallResponse.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,424 jobs.  `#print axioms` on every
declaration listed above reports only `propext`, `Classical.choice`, and `Quot.sound`.  No project
axiom, placeholder, hypothesis interface, or unresolved theorem premise is used.

## Exact field consequence

"Positivity erases phase" is an endpoint statement, not an unselectability statement.  Here the
complete passive modulus packet is provably even while a single source-fixed additive intervention
has an antisymmetric first response whose sign is *exactly* the stability trichotomy.  Three
nonisomorphic organs — exact-law stability, positive observation, intervention response — are joined
in one finite certified experiment, and the middle one is the only one that loses the chamber.

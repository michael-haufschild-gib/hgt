# CHMD: bound-state dimension; RH ⟺ dim P = 1 (2026-10-16)

Contribution 12 of this lane. STATUS row MUST-1559. Card: 3-formalized/chmd-bound-state-dimension-2026-10-16.md.
Module (ns RHTower.CHMDPolar): `RHTower/CHMDBoundStateDimension`; 12 declarations, wired.

## Results
- `inner_eigen_eq_zero_of_ne`; **`inner_resolvent_sum_ge`** (⟪Ru,u⟫ ≥ a‖u‖² on spans of eigenvectors with μ ≥ a,
  via ‖Σ cᵢ√(μᵢ−a) eᵢ‖² — no eigenvalue grouping); `sourceEnergy_rieszLift_le_of_lower_bound`;
  `finrank_span_eigen_le` (≤ 2·#quarter + 1); `finiteDimensional_boundStateSpace`, `finrank_boundStateSpace_le`
  (off-line set finite); **`riemannHypothesis_iff_finrank_boundStateSpace_eq_one`** (unconditional);
  `weilNegIndex_le_two_mul_quarter_add_one`, `card_visible_le_two_mul_quarter_add_three`.

## Assessment / pivot (user remark 2026-10-16)
The spectral layer (MUST-1541…1559) is a closed receiver: generic for operators SS* on difference graphs; it cannot
exclude bound states. Arithmetic enters only through the prime edges / prime generator. Next conjectures must use the
prime term non-generically (explicit-formula prime side, corpus PNT/ZFR/density assets, prime chain factorization),
not more operator theory. Do not add further generic spectral modules to this lane.

## Lean traps
- `rw [sq]` can rewrite the wrong power; use `(pow_two _).symm` with `trans_eq`.
- `LinearIsometry.orthonormal_comp_iff` fails to unify with a `let`-bound family; prove `Orthonormal` via
  `orthonormal_iff_ite` and the defeq of subtype inner products.
- Injectivity of `fun x : t => (⟨x.1, _⟩ : b)`: `Subtype.ext (by simpa using congrArg Subtype.val h)`.

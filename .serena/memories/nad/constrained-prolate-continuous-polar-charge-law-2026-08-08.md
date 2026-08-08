# constrained-prolate-continuous-polar-charge-law (stage 2) — Lean state 2026-08-08

## Closed this session

`(19e)` **is now closed in Lean, unconditionally.**  Card gate updated.

Chain, all axiom-clean (`propext, Classical.choice, Quot.sound`):

- `HTGeometry/DerivSignMonotone.lean` — universal Sturm-flux → finite critical set →
  `boundedVariationOn_of_finite_rhs_zeros`, plus `finite_zeros_of_deriv_ne_zero`,
  `finite_zeros_mul`.
- `HTGeometry/SturmWronskian.lean` — `hasDerivAt_sturmWronskian`,
  `sturmWronskian_eq_of_hasDerivAt`, `eq_const_mul_of_sturmWronskian_eq_zero`,
  **`sturmWronskian_eq_zero_of_weight_eq_zero`**, **`eq_const_mul_of_weight_eq_zero`**
  (vanishing weight at an endpoint ⟹ Wronskian ≡ 0 ⟹ proportionality; no boundary
  condition imposed by hand).
- `RHTower/ProlateProportionality.lean` (NEW) — `deriv_const_mul_eq`,
  `prolateSLAction_const_mul`, **`prolate_eqOn_const_mul`** (prolate eigenspace is
  one-dimensional), `prolate_eq_zero_of_eq_zero`, **`prolate_deriv_ne_zero_of_eq_zero`**
  (prolate zeros are simple).
- `RHTower/ProlateModeVariation.lean` (NEW) — `finite_zeros_prolate_quadratic`,
  **`prolate_boundedVariationOn`**: a nontrivial prolate mode has bounded variation on every
  compact subinterval of `(-1,1)`.  Hypotheses: smoothness, eigen-equation, nontriviality,
  `χ ≠ 0 ∨ c ≠ 0`.  No asymptotics, no spectral index, no endpoint boundedness, no RH.
- `RHTower/VanDerCorputIBP.lean` (NEW) — `norm_integral_cexp_le_of_antiderivative`,
  `norm_antiderivative_le`, `norm_integral_cexp_le_of_frequency_lower_bound`.

All wired into the `RHTower` / `HTGeometry` umbrellas.

## Corpus facts worth not re-deriving

- The prolate Wronskian layer already existed: `RHTower/ProlateWronskian.lean`
  (`prolateWronskian`, conservation, `prolateWronskian_eq_zero` at the singular endpoint,
  `prolate_firstOrder_relation`).  It stops at `ψ₁ψ₂' = ψ₂ψ₁'` and does **not** conclude
  proportionality — that was the real gap, now filled.
- Interior ODE uniqueness already existed:
  `RHTower/ProlateEndpointNonvanishing.eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq_at`.
  It is the workhorse behind both proportionality and simple zeros.
- Per-cell critical-point laws already existed:
  `RHTower/ProlateOneTurningVariation.lean` (`deriv_sturmFlux_prolate_eq`,
  `prolate_criticalSet_subsingleton_of_rhs_pos/neg`).
- `prolateSLAction c ψ x = (1-x²)·ψ'' - 2x·ψ' - c²x²·ψ`, defined in
  `RHTower/FuchsProlateScale.lean`.
- **Every existing van der Corput test in the corpus assumes `φ'' ≥ 0`** (`firstDerivTest`,
  `norm_integral_weight_cexp_le`, …).  The card's `(49)` gives only bounded variation of
  `1/ξ'`, so none of them applies to `(50)`; hence `VanDerCorputIBP.lean`.

## Still open on the card

- `[ ] identify the classical real h₀,h₄ pair in the actual spectrum` — a question about which
  modes occupy the constrained spectrum, not about the general theory.  Not touched by the
  simplicity work: that settles degeneracy, not occupancy.
- `[ ] formalize the concrete radial-PSWF/Bessel realization and (51)`.  `VanDerCorputIBP` is the
  `(50)` mechanism; still needed are the Dunster/Bessel amplitude asymptotics `(47)–(49)`.
- `[ ] promote (18) and (32)`; `[ ] true even ground/gap comparison`;
  `[ ] locally uniform determinant convergence to Xi`; `[ ] true cofinal Weil floor (RH-bearing)`.

## Traps hit

- `lake env lean <file>` reads the **oleans** of imports.  After appending to a module, you must
  `lake build` it before a dependent file will see the new declaration — otherwise you get a
  bogus "Unknown identifier".
- Appending with a here-doc lands **after** `end Namespace`; splice before it.
- `rw [deriv_const_mul_eq h1]` fires on the inner `deriv` first; rewrite the second-derivative
  equation before the first-derivative one, and use `show` to beta-reduce.
- The lint gate fails on `unusedSimpArgs` warnings.

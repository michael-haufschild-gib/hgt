# CHMD: quarter-strip Birman–Schwinger bound (2026-10-16)

RH goal ACTIVE. Contribution 11 of this lane. STATUS row MUST-1558.
Card: docs/drafts/pipeline/3-formalized/chmd-quarter-zero-bound-2026-10-16.md.
Module (ns RHTower.CHMDPolar): `RHTower/CHMDQuarterZeroBound`; 17 declarations, standard axioms, wired.

## Results (unconditional)
- `zeroDefect_reflect : zeroDefect f (reflect ρ) = −zeroDefect f ρ`; `zeroDefect_conj_ofReal` (real tests: conj).
- `quarterZeros := {ρ ∈ carrier | 1/2 < Re ρ ∧ 0 ≤ Im ρ}`; `exists_quarter_of_offLine` (orbit representatives);
  `zeroDefect_ofReal_eq_zero_of_quarter`; `two_mul_ncard_quarterZeros_le : 2·#quarter ≤ #offLine`.
- **`card_le_two_mul_quarter_of_negative_definite`**, **`orthonormal_primitive_bound_states_le_two_mul_quarter`**
  (k ≤ 2·#quarter), `orthonormal_primitive_bound_states_le_offLine` (k ≤ #offLine). Improves MUST-1553 by 2–4×.

## Next
dim P ≤ 2·#quarter + 1 (finite off-line set) via eigenspace decomposition; exact per-orbit signature.

## Lean traps
- `gammaOf_reflect` lives in `RHTower.CHMDGrowthCollapse`; `conj_mem_zetaCarrier` in ZetaZeroCountUpperBound
  (import explicitly); `ZeroConfig.reflect_mem ρ hρ` is a structure field.
- `congr 2; simp` does not close `2 = conj 2`; use `map_ofNat`.

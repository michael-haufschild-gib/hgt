# Identity-zero componentwise Pauli modular nuclearity — formalized

- **ID:** `identity-zero-componentwise-pauli-modular-nuclearity-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `identity-zero-componentwise-pauli-modular-nuclearity.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/FermionicFactorialTraceBound.lean` | the identity-zero twist and componentwise antisymmetrizer `(3)`–`(4)`, the elementary-symmetric factorial gain `(7)`, its positive-operator form, and the internal multiplicity `(9)` |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `(3)`–`(4)` `identityZeroTwist`, `identityZeroTwist_one`, `identityZeroTwist_mul`,
  `componentwiseAntisymmetrizer`, `identityZeroTwist_componentwiseAntisymmetrizer`,
  `componentwiseAntisymmetrizer_idempotent`, `componentwiseAntisymmetrizer_eq_self_iff`,
  `identityZeroTwist_eq_self_iff_antisymm` — the twist permutes the **external** variables alone and
  carries the sign, the internal indices are untouched, and the antisymmetrizer is exactly the
  projection onto the identity-zero symmetric subspace;
- `(7)` `pow_succ_two_term_le`, `sum_powersetCard_succ_insert`,
  `factorial_mul_sum_powersetCard_le_sum_pow` — the fermionic factorial gain
  `n!·eₙ(f,s) ≤ (∑ f)ⁿ` for every nonnegative weight, by induction on the ground set through the
  Pascal recursion for elementary symmetric sums, together with the divided form
  `sum_powersetCard_le_sum_pow_div_factorial`;
- the positive-operator form `sum_powersetCard_eigenvalues_le_trace_pow_div_factorial`:
  `eₙ(spectrum A) ≤ (Tr A)ⁿ/n!` for `A` positive semidefinite;
- `(9)` `trace_kronecker_one` (`Tr(A ⊗ I_K) = d·Tr A`) and
  `multiplicity_mul_sum_powersetCard_eigenvalues_le` — the `dⁿ` factor that componentwise
  antisymmetrization produces.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/FermionicFactorialTraceBound.lean
```

## What closed last

The combinatorial source of the `1/n!`.  A corpus search found no factorial or elementary-symmetric
bound anywhere, and mathlib has none either, so the Pascal-recursion proof of
`n!·eₙ ≤ (∑ f)ⁿ` is new infrastructure; the positive-operator form then follows from
`Matrix.PosSemidef.eigenvalues_nonneg` and `IsHermitian.trace_eq_sum_eigenvalues`.  Together with
the permutation-projection half this is exactly the reusable unconditional skeleton the card's open
core item 5 asks for.

## Boundary

The card records the scope boundary itself: the identification of `eₙ(spectrum)` with the trace of
the compression of `A^{⊗n}` to the antisymmetric subspace, and the trace-class setting on
`L²(ℝ) ⊗ K`, are not formalized because mathlib has no exterior-power trace or Hardy-space
nuclearity API.  The remaining paper gates — a uniformly `exp(O(n))`-conditioned identity-zero
intertwiner, a compact-local intrinsically mixing projective-HT quantum field theory, and a
literature novelty audit — are open-core constructions and an external audit, not formalization
gates for the skeleton certified above.

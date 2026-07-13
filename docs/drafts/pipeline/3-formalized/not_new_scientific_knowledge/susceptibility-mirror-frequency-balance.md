# Susceptibility mirror-frequency balance

- **ID:** susceptibility-mirror-frequency-balance
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean certificate split from `../2-fully-proven/prime-zero-susceptibility-transverse.md`)
- **Owner:** Leaner
- **Lean file:** `formal/GaloisForLFunctions/RHTower/SusceptibilityBalance.lean`

## Statement

For `beta : ℝ`, finite multiplicity `m : ℕ` with `m ≠ 0`, define the mirror-frequency factor

> `F_{beta,m}(n) := n^((1 - 2 beta) / m)`.

Then:

1. The exponent vanishes exactly on the critical line:
   > `(1 - 2 beta) / m = 0 ↔ beta = 1/2`.
2. The mirror-frequency factor is identically `1` on every real probe frequency `n > 1` exactly on the
   critical line:
   > `(∀ n > 1, F_{beta,m}(n) = 1) ↔ beta = 1/2`.

This is the algebraic frequency-balance step in the parent susceptibility card. It does not claim the
implicit-function/Puiseux zero-splitting, the zeta functional-equation leading-coefficient match, or the
curvature-hierarchy identification.

## Paper proof

Because `m ≠ 0`, its real cast is nonzero. Therefore
`(1 - 2 beta) / m = 0` iff `1 - 2 beta = 0`, which is equivalent to `beta = 1/2`.

For the frequency statement, first assume `F_{beta,m}(n) = 1` for every `n > 1`. Specialize to `n = 2`.
Taking real logarithms gives

> `((1 - 2 beta) / m) * log 2 = 0`.

Since `log 2 > 0`, the exponent is zero, hence `beta = 1/2` by the first paragraph. Conversely, if
`beta = 1/2`, the exponent is zero, so `F_{beta,m}(n) = n^0 = 1` for every `n > 1`.

## Lean certificate

The Lean definitions and theorems are:

```lean
def susceptibilityMirrorFrequencyFactor (beta : ℝ) (m : ℕ) (n : ℝ) : ℝ :=
  n ^ ((1 - 2 * beta) / (m : ℝ))

theorem susceptibilityExponent_zero_iff {beta : ℝ} {m : ℕ} (hm : m ≠ 0) :
    ((1 - 2 * beta) / (m : ℝ) = 0) ↔ beta = 1 / 2

theorem susceptibilityMirrorFrequencyFactor_eq_one_forall_iff {beta : ℝ} {m : ℕ}
    (hm : m ≠ 0) :
    (∀ n : ℝ, 1 < n → susceptibilityMirrorFrequencyFactor beta m n = 1) ↔
      beta = 1 / 2
```

## Gates

- [x] 2 -> 3 formalized: Lean file added, root import added, audited with `#print axioms`.
- [x] No `sorry`, no `axiom`, and no hypothesis beyond `m ≠ 0`.
- [x] Paper proof and Lean proof are synchronized: both prove the exponent-zero step and the `n = 2` log
  specialization.

## Verification

- `cd formal && lake env lean GaloisForLFunctions/RHTower/SusceptibilityBalance.lean`
- `cd formal && lake build GaloisForLFunctions`
- `bash scripts/check_axioms.sh`

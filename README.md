# Infinite-base difference Galois for L-functions

This is the Lean 4 formalization track for the draft
`docs/publications/drafts/infinite-base-difference-galois-for-L-functions.md`.

## Scope

The current Lean ledger proves the draft's Tier A elementary core:

| Draft target | Lean theorem |
|---|---|
| A1, inversion and scale under `s ↦ 1-s` | `GaloisForLFunctions.cpow_inversion_scale` |
| A2, involution | `GaloisForLFunctions.sigma_involutive` |
| A3, fixed-modulus critical-line test | `GaloisForLFunctions.norm_cpow_eq_critical_iff` |
| A4, finite integer log-prime relation | `GaloisForLFunctions.log_prime_int_relation_eq_zero` |
| A4, integer linear independence form | `GaloisForLFunctions.logPrime_linearIndependent_int` |
| A4, full rational linear independence | `GaloisForLFunctions.linearIndependent_log_primes` |
| A4, finite no-rational-resonance corollary | `GaloisForLFunctions.logPrime_no_rat_relation` |
| Euler product iff finite Bohr-prime factorization | `GaloisForLFunctions.isMultiplicative_iff_bohr_factorization` |
| Finite pre-spectral non-Euler-product witness | `GaloisForLFunctions.fake_fails_factorization` |
| B2 zero-free half, local Euler factor | `GaloisForLFunctions.localEulerFactor_ne_zero` |
| B3 finite zero-free stepping stone | `GaloisForLFunctions.finiteEulerProduct_ne_zero` |

It does not formalize RH, LI, a difference Siegel-Shidlovsky theorem, or the conjectural
infinite-base difference-Galois field. Those remain research/frontier statements, not Lean theorems.

## Build

```sh
cd formal
lake exe cache get
lake build
bash ../scripts/check_axioms.sh
```

The project is pinned to Lean/mathlib `v4.30.0`, matching the sibling publication formalizations.

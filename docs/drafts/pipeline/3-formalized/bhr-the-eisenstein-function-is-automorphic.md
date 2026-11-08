# BHR — the Eisenstein function is automorphic at every spectral parameter

- **ID:** bhr-eisenstein-automorphic
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `TheNormalizedEisensteinFunction` proves `SL₂(ℤ)`-invariance of `E(u; ·)` only on the critical line
  `u ∈ iℝ∖0`; continuation arguments (Rankin–Selberg against the cusp modes) need it at all `u`.
- **Statement:** Let `N(u; z) = ξ(1+2u) E(u; z)` (the numerator) and `E*(u; z) = N(u; z)/((1+2u)(2u))`.
  1. `u ↦ N(u; z)` is holomorphic on `u ≠ ½`; `u ↦ E(u; z)` is holomorphic wherever `u ≠ ½`, `ξ(1+2u) ≠ 0`.
  2. `N(u; γz) = N(u; z)` for every `γ ∈ SL₂(ℤ)` and `u ≠ ½`; hence `E(u; γz) = E(u; z)` at every regular `u`.
  3. `E*(−u; z) = E*(u; z)` for `u ∉ {0, ±½}`.

## Paper proof
1. `N = Y^{½+u}ξ(1+2u) + ((1+2u)/(2u−1)) ξ(2u) Y^{½−u} + (1+2u)(2u) T(u)`; the tail `T` is entire in `u` (corpus),
   `ξ` is entire, and `2u − 1 ≠ 0`.
2. `{½}ᶜ ⊂ ℂ` is open and connected. On the line (`u = iξ`, `ξ ≠ 0`) `ξ(1+2u) ≠ 0` and `E` is invariant (corpus),
   so `N(·; γz) = N(·; z)` at the points `iξ`, which accumulate at `i`. Identity theorem.
3. For `Im u ≠ 0`, `ξ(s) = s(s−1)Λ(s)/2` gives `N = (1+2u)(2u)/2 · (Λ(2u)Y^{½−u} + Λ(1+2u)Y^{½+u} + 2T)`, so
   `E*` is half the completed Fourier model, which is even (`Λ(s) = Λ(1−s)`, corpus `cuspLeg_neg`). Both
   `E*(−u)` and `E*(u)` are holomorphic on the connected set `ℂ∖{0, ±½}`; identity theorem from the line.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheEisensteinFunctionIsAutomorphic.lean`, wired into `BlackHoleRingdown.lean`,
checked with `lake --old env lean`, no messages. Axioms of `normalizedEisenstein_smul_of_regular`,
`completedEisenstein_neg`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.EisAuto`) |
|---|---|
| (1) | `differentiableAt_numerator`, `differentiableAt_normalizedEisenstein_of_regular`, `differentiableAt_completed` |
| (2) | `frequently_line`, `numerator_smul`, `normalizedEisenstein_smul_of_regular`, `completedEisenstein_smul` |
| (3) | `completedEisenstein_eq_lineModel`, `lineModel_neg`, `completedEisenstein_neg` |

## Scope
Selberg's continuation of the Eisenstein series as an automorphic function with functional equation, obtained
from the line by analytic continuation. Uniform bounds of `E(u; z)` in `u` (for differentiating integrals against
cusp modes) are not packaged here.

## Log
- 2026-11-08 — created and formalized.

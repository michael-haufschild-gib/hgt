# CCM Euler-Pick transfer requires dephased logarithmic derivatives — formalized closure

- **ID:** `ccm-euler-pick-logderivative-transfer-boundary-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-euler-pick-logderivative-transfer-boundary-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

`GaloisForLFunctions.RHTower.CCMEulerPickTransferBoundary` (new), over the Pick-cluster modules.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(6)`, `(15)` | `pairedZeroKernel`, `pairedZeroKernel_eq` | one paired zero contributes the sum of two rank-one Gram kernels |
| section 2 transfer | `posSemidef_of_tendsto_entrywise` | the positive cone of finite Hermitian matrices is closed under entrywise limits |
| `(14)` | `rightCauchyKernel`, `aperturePhaseDefect` | the canonically phased kernel is `K_G − 2a·Cauchy` |
| `(14a)`, `(14b)` | `periodicBackground`, `hasDerivAt_periodicBackground`, `periodicBackgroundLogDeriv_eq` | the periodic background and its logarithmic derivative `2a/(e^{2aw}−1)` |
| `(14c)` | `norm_periodicBackgroundLogDeriv_le` | `|L₀,ₐ(w)| ≤ 2a/(e^{2aσ}−1)` on `Re w ≥ σ` |
| finite-aperture indefiniteness | `periodicBackgroundLogDeriv_neg` | at `w = x + iπ/(2a)` the value is real and negative |
| `(23)`, `(24)` | `relativeDeterminant`, `im_relativeDeterminant` | the imaginary part of the relative determinant |
| Herglotz sufficiency | `im_relativeDeterminant_nonneg` | `c_j ≥ 0` ⟹ upper half-plane maps into its closure |

## Axioms

`#print axioms` on all nine declarations returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The Hadamard factorization `(3)` of an even real-rooted order-one function; the tree already owns
  the Xi case (`XiHadamardFactorization`, `XiRelativeResolventTrace`).
- The CCM regularized determinant `(11)` and the complete-detector theorem identifying `(9)` with
  full Weil positivity.
- The integral identity `(16)` and hence the spectral-discrepancy representation `(17)`–`(18)`.
- The Harnack/Stirling incompatibility `(24g)`–`(24h)` and the four-currency carrier budget `(27)`.
- The card's open gates: a positive relative-background renormalization, dephased Euler half-plane
  convergence, divisor-preserving determinant convergence, and RH.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMEulerPickTransferBoundary`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.

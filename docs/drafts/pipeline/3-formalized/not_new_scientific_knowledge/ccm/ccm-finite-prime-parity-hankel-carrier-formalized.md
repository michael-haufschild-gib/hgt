# Finite prime parity Hankel carrier — formalized closure

- **ID:** `ccm-finite-prime-parity-hankel-carrier-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-finite-prime-parity-hankel-carrier.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.Suzuki.SuzukiParityHankelDecomposition` — the parity lifts and the
  `T ± H` decomposition.
- `GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeHankelCarrier` — the convolution carrier, shear identities,
  cutoff, atomic split, and cocycle.

Standing on the screw layer of `ccm-screw-kernel-positivity-improving-breakdown` (already Stage 3):
`SuzukiExplicitScrewRegularKernel`, `SuzukiScrewDisjointCrossCoupling`,
`SuzukiScrewDistributionalKernel`, `SuzukiScrewCorrelationPairing`. `K_reg` of `(6)` is
`screwRegularKernel`; the right-hand pairing of `(12)` is `screwCorrelationForm` at `φ = ψ`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| forms | `diffBilinForm`, `sumBilinForm` | `∫∫ K(x−y) f y g x` and `∫∫ K(x+y) f y g x`; for `φ, ψ` supported in `(0,a)` these are exactly `T_a` and `H_a`, zero extension being harmless |
| `(2)` | `evenParityLift`, `oddParityLift`, `evenParityLift_eq_of_vanishing`, `oddParityLift_eq_of_vanishing` | the lifts, defined with `\|x\|` and `Real.sign` as published, and proved to be symmetrisation/antisymmetrisation `(φ ± φ∘(-·))/√2` on functions vanishing on `(-∞,0]`. This replaces the four-quadrant split |
| reflections | `measurePreserving_negSnd`, `measurePreserving_negFst`, `measurePreserving_negBoth`, `diffBilinForm_negReflect_left/right/both` | the three reflections of `ℝ × ℝ` are measure preserving, so the reflection identities hold with no integrability hypothesis at all |
| `(4)` | `diffBilinForm_evenParityLift`, `diffBilinForm_oddParityLift` | `Q_even = T + H`, `Q_odd = T − H` |
| `(5)` | `diffBilinForm_parity_difference` | the parity gap is `2H` |
| `(11)` | `screwConvolve`, `screwCrossCorr_negReflect` | the carrier `c_(φ,ψ)` and its identification with the reflected correlation |
| `(10)` | `screwConvolve_eq_zero_of_two_mul_le` | the convolution vanishes for `t ≥ 2a`, so only prime powers with `log n < 2a`, i.e. `n < λ²`, contribute |
| `(9)` | `screwConvolve_eq_intervalIntegral` | at `0 < t < 2a` the carrier is the integral over `(max 0 (t−a), min a t)` |
| `(8)`, `(12)` | `diffBilinForm_eq_correlation_pairing`, `sumBilinForm_eq_convolution_pairing` | each two-variable form is the kernel paired against the one-variable carrier, by two Fubini applications and one translation |
| `(9)` atomic | `atomicHankelPart`, `primeHankelPart`, `atomicHankelPart_eq_primeHankelPart` | the atomic part, and that enlarging the index range past `e^{2a}` adds nothing |
| `(16)` | `atomicHankelPart_add`, `atomicHankelPart_sub` | the exact coefficient cocycle `H_(b+δb) − H_b = −∑ δb n · c(log n)` |
| `(7)` | `sumBilinForm_sub_atomic` | the Hankel carrier is the regular convolution pairing minus the finite prime-power samples |
| `(13)` | `parityGap_eq_regular_sub_atomic`, `parityGap_autocorrelation` | the even sector exceeds the odd sector by exactly twice the difference between the archimedean convolution pairing and the finite prime-power convolution samples |

The only hypotheses in `(4)`–`(5)` are evenness of `K`, vanishing of `φ, ψ` on `(-∞,0]`, and
integrability of the two basic integrands.

## Axioms

`#print axioms` on every theorem of both modules returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

The passage from a kernel that is a genuine distribution (Suzuki's `-g''`, whose Toeplitz part is
singular on the diagonal) to the closed parity forms. The card itself only claims this "by form-core
density"; the Lean statements are the exact integrable-kernel content, and
`ccm-screw-kernel-positivity-improving-breakdown` supplies the distributional identification
`-∫ g φ'' = ∫ K φ` on atom-free intervals.

## Verification performed

- `lake env lean` on a scratch file importing both modules: no errors.
- `#print axioms` on every theorem: clean.

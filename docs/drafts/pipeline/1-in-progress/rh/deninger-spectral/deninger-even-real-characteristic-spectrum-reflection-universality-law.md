# Deninger even-Real characteristic-spectrum reflection universality law

Status: **Stage 3 — formalized in Lean 4**

## Discovery

Whole-corpus theorem-posting closure joined:

- `deningerArithmeticH1CenteredCharacteristic_eq_zero_iff_eigenvector`, which identifies zeros of
  the source characteristic section with point spectrum of the quotient Frobenius generator;
- `deningerEntireFunctionalEquationSigma_Xi`, which fixes the characteristic relation under the
  functional-equation Schwarz reflection; and
- `deningerArithmeticH1EvenKReal_commutes_theta`, which descends that conjugate-linear involution to
  middle cohomology and makes it commute with the Frobenius generator.

No corpus theorem closes these source, characteristic, and Real-structure statements into a
single reflected spectral transport law.

## Universal law

Write `α♯ = -conj(α)`. Then:

1. the centered source characteristic vanishes at `α` exactly when it vanishes at `α♯`; and
2. if `x ≠ 0` is a Frobenius eigenvector with eigenvalue `1/2 + I α`, its even-Real conjugate
   `σx` is nonzero and is an eigenvector with eigenvalue `1/2 + I α♯`.

Because `σ² = 1`, this transport is involutive and therefore pairs the two point-spectrum fibres
bijectively, including the fixed fibre when `α = α♯`.

## Dependency-closed paper proof

1. The centered characteristic is `XiC`.
2. Functional-equation Schwarz reflection fixes the entire source relation, so
   `conj(XiC(-conj α)) = XiC(α)`. Hence vanishing at `α` is equivalent to vanishing at
   `-conj α`; apply the same identity twice for the reverse direction.
3. Let `θx = (1/2 + Iα)x`. Commutation gives `θ(σx) = σ(θx)`.
4. Conjugate-linearity gives
   `σ((1/2 + Iα)x) = conj(1/2 + Iα) σx
    = (1/2 + I(-conj α)) σx`.
5. If `σx = 0`, apply `σ` again. Even parity gives `σ²x = x`, hence `x = 0`, contradiction.
6. The same square law makes the reflected transport its own inverse.

No divisor enumeration, RH premise, topological determinant, or numerical evidence enters.

## Formal targets

- `deningerCenteredSpectralReflection`
- `deningerCenteredSpectralReflection_involutive`
- `deningerArithmeticH1CenteredCharacteristic_reflection`
- `deningerArithmeticH1EvenKReal_sigma_eigenvector`
- `deninger_evenReal_characteristicSpectrumReflectionUniversality`

## Novelty audit

Post-proof searches found Deninger's conjectural arithmetic-cohomology program, determinant
realizations over finite fields, and obstructions to real-coefficient Weil cohomology. They did
not reveal this exact source-quotient theorem in which one constructed even-Real involution both
preserves the characteristic zero set and transports every quotient-Frobenius eigenvector.

The exact characteristic-spectrum transport remains **[NOVELTY UNVERIFIED]**:

- https://arxiv.org/abs/math/0605724
- https://arxiv.org/abs/1602.01980
- https://arxiv.org/abs/2204.02714

## Lean formalization

Formalized in:

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerEvenRealCharacteristicSpectrumReflectionUniversalityLaw.lean`

with declarations:

- `deningerCenteredSpectralReflection`
- `deningerCenteredSpectralReflection_involutive`
- `deningerArithmeticH1CenteredCharacteristic_reflection`
- `deningerArithmeticH1EvenKReal_sigma_eigenvector`
- `deninger_evenReal_characteristicSpectrumReflectionUniversality`

Exact-file verification passed:

`lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerEvenRealCharacteristicSpectrumReflectionUniversalityLaw.lean`

Wired into `GaloisForLFunctions/RHTower.lean` immediately after the characteristic and Real-source
modules.

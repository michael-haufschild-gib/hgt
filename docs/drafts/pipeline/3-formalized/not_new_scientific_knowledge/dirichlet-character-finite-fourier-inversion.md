# Dirichlet-character finite Fourier inversion

## Status

- Pipeline: formalized in Lean 4
- Novelty: `[LITERATURE]`
- Proof status: `[PAPER-PROVED]`
- Lean status: `[LEAN-PROVED]`
- Role: Fourier core of Kaczorowski–Perelli 2024, Lemma 1

## Exact claim

Let `D>0`, let `f : Z/DZ → ℂ`, and for every Dirichlet character `χ mod D` define

`ĉ(χ)=∑_{x mod D} χ⁻¹(x) f(x)`.

For every `n mod D`,

`χ₀(n)f(n) = φ(D)⁻¹ ∑_{χ mod D} ĉ(χ)χ(n)`,

where `χ₀` is the principal character. Thus arbitrary data restricted to reduced residue classes
has an exact Fourier expansion over all Dirichlet characters.

## Dependency-closed proof

Expand the right-hand double sum and interchange the two finite sums. If `n` is not a unit, every
`χ(n)` vanishes and both sides are zero. Suppose `n` is a unit. For each residue `x`:

- if `x` is not a unit, every `χ⁻¹(x)` vanishes;
- if `x` is a unit, character orthogonality gives
  `∑_χ χ⁻¹(x)χ(n)=φ(D)` when `x=n`, and `0` otherwise.

Only `x=n` survives, so the unnormalized double sum is `φ(D)f(n)`. Since `D>0`, `φ(D)>0`; division
by `φ(D)` proves the formula.

## Relation to published Lemma 1

Applying this theorem to the additive phase `f(x)=e(-ax/D)` produces equation (3.1) of
arXiv:2405.03186 with the Fourier coefficient written as its defining finite residue sum. The
closed-form coefficient in equation (3.2), involving the conductor, primitive inducing character,
Möbius factor, and Gauss sum, is a separate remaining theorem.

## Lean realization

Module: `GaloisForLFunctions.RHTower.SelbergClass.DirichletFourier`

Declarations:

- `RHTower.dirichletCharacterFourierCoeff`
- `RHTower.dirichletCharacterFourier_sum_eq`
- `RHTower.dirichletCharacterFourier_expansion`

Targeted source check and named-module build passed. `#print axioms` reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

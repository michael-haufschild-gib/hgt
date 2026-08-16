# Differential algebraicity descends to the leading Laurent coefficient

- **ID:** `leading-laurent-coefficient-differential-algebraicity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SPECIALIZATION BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Statement:** For a coefficientwise differential Laurent series in a differential-constant
  parameter, differential algebraicity over the rational parameter field forces its leading
  coefficient to be differentially algebraic over the coefficient base.
- **Scientific status:** `[PROVED HERE] [PARENT DIFFERENTIAL ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`

## Theorem

Let `k subset K` be differential fields of characteristic zero with derivation `D`.  Adjoin a
formal parameter `E` with `D(E)=0`, and extend `D` coefficientwise to `K((E))`.  Let

```text
F(E) = E^m (a + a_1 E + a_2 E^2 + ...),      a != 0,        (1)
```

where `m` is an integer and all coefficients lie in `K`.

If `F` is differentially algebraic over `k(E)`, then `a` is differentially algebraic over `k`.
Equivalently,

```text
a hypertranscendental over k
  implies
F hypertranscendental over k(E).                              (2)
```

The statement also holds for the first nonzero coefficient after any finite principal part.

## Proof

Put `G=E^(-m)F`.  Multiplication by the differential constant `E^(-m)` preserves differential
algebraicity, so `G` is differentially algebraic over `k(E)`.  Choose a nonzero differential
polynomial

```text
P(E;Y,DY,...,D^rY) in k(E){Y}
```

with `P(E;G)=0`.

Clear the finitely many denominators in `E`.  This gives a nonzero differential polynomial with
coefficients in `k[E]` and the same vanishing property.  Divide all its coefficients by their
largest common power of `E`.  The resulting differential polynomial `Q` still satisfies
`Q(E;G)=0`, and its specialization

```text
Q_0(Y,DY,...,D^rY) = Q(0;Y,DY,...,D^rY)
```

is nonzero.

Because `D` acts coefficientwise and fixes `E`, constant-term extraction commutes with every
iterate of `D`, addition, and multiplication.  Taking the constant term of `Q(E;G)=0` therefore
gives

```text
Q_0(a,Da,...,D^r a)=0.
```

Thus `a` is differentially algebraic over `k`.  Contraposition proves `(2)`.

## Exact boundary

The parameter must be differential-constant for the chosen derivation.  The theorem does not say
that every coefficient of an arbitrary differentially algebraic two-variable function is DA after
an analytic, derivation-mixing coordinate change.  It applies to a fixed Laurent expansion in a
transverse parameter while differentiating only the remaining physical kinematic variables.

## Cosmological use

For a cosmological wavefunction coefficient with a total-energy expansion

```text
Psi(E_T,z) = E_T^(-p) A_flat(z) + less singular terms,
```

take `D=d/dz` and hold `E_T` differential-constant.  If the flat-space coefficient `A_flat` is HT,
then `Psi` is HT.  The physical existence of the expansion and the identification of its leading
coefficient with a scattering amplitude are separate QFT inputs.

## Novelty gate

This is formal specialization of a differential-polynomial relation and is not a novelty claim.
Its role is to make the flat-space-to-cosmology transfer logically exact.

## Lean gate

- [x] Prove that constant-term extraction commutes with normalized finite differential-polynomial
  evaluation.
- [x] Prove that a nonzero specialized relation forces differential algebraicity of the leading
  coefficient.
- [x] Define the coefficientwise differential structure on the formal-series carrier:
  `formal/GaloisForLFunctions/HTGeometry/CoefficientwisePowerSeriesDerivation.lean`
  (`coeffwiseAdd`, `coeffwiseAdd_mul` (Leibniz), `coeffwiseAdd_X` (the parameter is a differential
  constant), `constantCoeff_coeffwiseAdd`, `coeffwiseJet`, `constantCoeff_coeffwiseJet`),
  axiom-clean.  The Laurent case reduces to this by `LaurentSeries.powerSeriesPart`.
- [ ] Formalize denominator clearing, principal-part removal, and removal of the common
  `E`-valuation.
- [ ] Assemble the unrestricted Laurent theorem and contrapositive without new axioms.

The completed normalized receiver is recorded in
`../../3-formalized/not_new_scientific_knowledge/formal-leading-coefficient-specialization.md`.

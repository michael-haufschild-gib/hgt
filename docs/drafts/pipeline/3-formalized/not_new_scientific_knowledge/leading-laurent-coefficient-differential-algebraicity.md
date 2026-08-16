# Differential algebraicity descends to the leading Laurent coefficient

- **ID:** `leading-laurent-coefficient-differential-algebraicity`
- **Stage:** 3-formalized
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
- [x] Formalize removal of the common `E`-valuation:
  `formal/GaloisForLFunctions/HTGeometry/FormalParameterRelationNormalization.lean`
  (`exists_normalized_relation`: every nonzero `Q ∈ MvPolynomial ι (Polynomial F)` factors as
  `C (X^d) * P` with `formalParameterSpecialization P ≠ 0`, using the minimum trailing degree over
  the support; `eval₂_of_eq_C_X_pow_mul`: the removed power factors out of the evaluation).
- [x] Assemble the power-series theorem:
  `differentialAlgebraicOver_constantCoeff_of_formalRelation` — a nonzero formal-parameter relation
  on the coefficientwise jets of `G ∈ K[[E]]` forces `G(0)` to be differentially algebraic over the
  coefficient base.  `X` is a nonzerodivisor in `K[[E]]`, which is what cancels the removed power.
- [x] Extend the carrier from `K[[E]]` to `LaurentSeries K`:
  `formal/GaloisForLFunctions/HTGeometry/LaurentCoefficientwiseDerivation.lean`
  (`laurentCoeffwise`, `laurentCoeffwise_mul` (Leibniz, both terms over one Hahn antidiagonal via
  `HahnSeries.coeff_mul_left'`/`coeff_mul_right'`), `laurentCoeffwise_single_one` (every monomial
  `E^m` is a differential constant), `laurentCoeffwise_coe`, `laurentCoeffwiseJet`,
  `laurentCoeffwiseJet_eq_single_mul`, `constantCoeff_powerSeriesPart`).
- [x] Assemble the Laurent theorem and its contrapositive:
  `formal/GaloisForLFunctions/HTGeometry/LeadingLaurentCoefficientDescent.lean`
  (`laurentParameterMap`, `parameterRescale`, `coeff_parameterRescale`,
  `parameterRescale_ne_zero`, `ofPowerSeries_eval₂_parameterRescale`,
  `differentialAlgebraicOver_leadingCoeff_of_laurentRelation`,
  `no_laurentRelation_of_not_differentialAlgebraicOver_leadingCoeff`).

## Lean formalization

| Paper step | Lean |
|---|---|
| `D` extended coefficientwise to `K[[E]]`, Leibniz, `D(E)=0` | `PowerSeriesDeriv.coeffwiseAdd`, `coeffwiseAdd_mul`, `coeffwiseAdd_X` |
| constant-term extraction commutes with every `D^j` | `constantCoeff_coeffwiseJet` |
| `D` extended coefficientwise to `K((E))`, Leibniz, `D(E^m)=0` | `LaurentDeriv.laurentCoeffwise`, `laurentCoeffwise_mul`, `laurentCoeffwise_single_one` |
| `F = E^m G`, `G = powerSeriesPart F`, jets shift | `laurentCoeffwiseJet_eq_single_mul` |
| `a = ` leading coefficient `= G(0)` | `constantCoeff_powerSeriesPart` |
| `G = E^{-m}F` differentially algebraic over `k(E)` | `parameterRescale`, `ofPowerSeries_eval₂_parameterRescale` (the degreewise rescaling `k(d) = c + m·deg(d)`, valid for either sign of `m`) |
| clear denominators and divide by the common `E`-power | `exists_normalized_relation`, `eval₂_of_eq_C_X_pow_mul`, `parameterRescale_ne_zero` |
| specialize at `E = 0`; `Q_0(a, Da, …) = 0` | `differentialAlgebraicOver_of_normalized_formalParameterRelation`, `differentialAlgebraicOver_constantCoeff_of_formalRelation` |
| the theorem (1) | `differentialAlgebraicOver_leadingCoeff_of_laurentRelation` |
| the contraposition (2) | `no_laurentRelation_of_not_differentialAlgebraicOver_leadingCoeff` |

All declarations audit to `[propext, Classical.choice, Quot.sound]`.

The completed normalized receiver is recorded in
`../../3-formalized/not_new_scientific_knowledge/formal-leading-coefficient-specialization.md`.

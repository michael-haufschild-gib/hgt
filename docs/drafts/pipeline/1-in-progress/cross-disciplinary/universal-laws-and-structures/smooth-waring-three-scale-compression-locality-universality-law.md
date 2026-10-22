# Smooth Waring three-scale compression–locality universality law

## Status

`[PAPER PROVED — LEAN IN PROGRESS]`

## Lean-derived statement

For every projectively smooth Waring form in at least four law directions, take:

1. its original finite quantum Waring packet;
2. the linear-width principal-symbol completion of that exact packet;
3. the quadratic-width principal-symbol completion of that exact packet.

The three representations have the same complete differential dependence horizon, namely the
Waring hypersurface.  All three exterior derivation symbols are injective.  Every membrane-local
presentation is pair-complete and obeys the same `choose r 2` covering lower bound.  The original
packet additionally retains its independent twisted-monomial normal form and multiplication law,
while the clocked linear completion has strictly smaller coordinate width than the clocked
quadratic completion.

## Corpus inputs

- `smoothMvWaring_normalForm_holographicLocalityUniversality`
- `principalSymbolDetectorCompression_localityUniversality`
- `linearWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol`
- `finiteQuantumTorusSymbol_pow`
- `eval_mvWaringPolynomial`

No numerical computation or external mathematical premise is used.

## Paper proof

Let

```text
A(c) = finiteQuantumWaringSymbol(q, a.mulVecLin)(c)
F(c) = eval(c, mvWaringPolynomial(d,a)).
```

The exact torus power identity and the evaluation identity give, for every `c`,

```text
A(c)^d = F(c) * id.
```

Thus `A` satisfies the scalar-pencil premise of both detector-completion theorems, with the
nonzero finite-quantum delta root.  The smooth-Waring law identifies the original packet horizon
with `F=0`, proves its exterior-symbol injectivity and normal form, and derives its locality
obstruction.  The linear-width theorem identifies the linear completion horizon with the same
`F=0`.  The compression–locality law identifies the linear and quadratic horizons, proves both
completed exterior symbols injective, proves strict width separation for `4 <= r`, and derives
both completed locality obstructions.  Transitivity gives one horizon across all three actual
Waring realizations.

## Hostile subsumption audit

- The smooth-Waring parent has no linear- or quadratic-width meta-completion and no detector-width
  comparison.
- The detector-compression parent is representation-free and does not instantiate its scalar
  pencil with a Waring form, identify its horizon as a smooth Waring hypersurface, or retain the
  finite quantum twisted-monomial normal form.
- The connector is not a conjunction wrapper: the exact Waring primitive-order power identity
  discharges the detector theorem's central premise, and equality transitivity proves a new
  three-representation horizon statement.
- Whole-corpus search found no existing application of either principal-symbol completion to
  `finiteQuantumWaringSymbol`.

## Lean verification

Formal module:

```text
formal/GaloisForLFunctions/HTGeometry/SmoothWaringThreeScaleCompressionLocalityUniversalityLaw.lean
```

The two parent sources pass exact source checks.  The connector exact check is pending because its
fresh parent `.olean` files are intentionally not materialized with `lake build` before final
audit.

The module is imported by `formal/GaloisForLFunctions/HTGeometry.lean`.

## Literature boundary

Literature search is forbidden until the connector itself passes Lean.

## Gates

- [x] whole-corpus source search
- [x] exact conjecture stated from theorem interfaces
- [x] dependency-closed paper proof
- [x] hostile corpus-subsumption audit
- [ ] Lean exact check
- [x] umbrella wiring
- [ ] post-proof literature audit
- [ ] final axiom/lint/build audit

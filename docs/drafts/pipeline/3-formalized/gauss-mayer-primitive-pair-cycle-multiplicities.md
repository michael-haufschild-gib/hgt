# Primitive pair-cycle multiplicities of actual Gauss words

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [primitive modular orbit product](gauss-mayer-primitive-orbit-product.md).

## Theorem

Every nonempty word has a unique primitive root and positive repetition
exponent. Two positive powers of primitive words are cyclic rotations of
one another exactly when their primitive roots are cyclic rotations and
their repetition exponents agree.

For a primitive cycle `c`, choose a representative of length `ℓ(c)>0`.
There is an exact bijection

```text
nonempty pair words ↔ (c, r, i),  r≥1,  0≤i<ℓ(c),
word(c,r,i) = (rotation_i representative(c))^r.
```

Its word length is `rℓ(c)`. The repeated word therefore has exactly
`ℓ(c)` distinct pair rotations, independent of `r`. The actual even
Gauss words of length `2n+2` are bijective with pair words of length
`n+1`, preserving the reversed source digit convention.

## Proof

Existence of a primitive root follows by induction on word length: every
proper whole-word power has a strictly shorter nonempty base. For a
primitive word `u`, let `m` be its minimal rotation period. It is positive
and at most `length(u)`. Cutting at `m` gives commuting prefix and suffix,
because rotation by `m` fixes `u`. The certified commuting-word theorem
makes both pieces powers of one common word. Primitivity forces the sum
of these exponents to be at most one; the prefix is nonempty, so the
suffix is empty. Thus `m=length(u)`.

Rotation commutes with whole-word repetition. Positive word powers are
injective: equality gives equal base lengths and then equality of the
initial base-length prefixes. Consequently repetition preserves minimal
rotation period. Equal positive powers of primitive words have equal
primitive lengths, and prefix extraction gives equal roots. Their
positive repetition exponents then agree by length comparison. Applying
this argument after rotation gives the cyclic classification.

Rotation offsets below the minimal period are distinct, and every offset
reduces modulo that period. Thus a primitive word has precisely its
length many rotations. Quotient primitive words by rotation and select
one representative per class. Primitive-root existence gives surjectivity
of the displayed indexing; root uniqueness, cyclic classification and
distinct primitive rotations give injectivity.

For the source convention, `pairedDigits` reverses the pair order and
lists each pair `(a,b)` as `[b,a]`. Its associated positive unipotent
matrix word determines the pair sequence uniquely by the certified run
boundary theorem. The actual extraction `evenWordPairs` recovers those
digits exactly. Converting finite functions to lists and back therefore
gives the claimed even-word bijection and its exact length law.

## Lean certificate

All modules are in `RenormalizedIntersectionTheory`:

- `GaussMayerPrimitivePairCycles.lean`: primitive roots, rotation periods,
  root uniqueness and cyclic-power classification. Namespace `MayerPrimitiveCycles`;
  principal declarations `exists_primitive_root`, `minimalPeriod_primitive`,
  `primitive_root_unique`, `primitive_powers_isRotated_iff`, `primitiveRotationEquiv`.
- `GaussMayerPrimitiveCycleIndex.lean`: the global quotient index.
  Namespace `MayerCycleIndex`; `wordCycleEquiv`, `expand_length`.
- `GaussMayerEvenWordIndex.lean`: exact source-to-pair conversion.
  Namespace `MayerEvenWordIndex`; `pairedDigits_injective`, `toPairs_length`,
  `evenWordPairEquiv`.

The full namespace prefix is
`GaloisForLFunctions.RenormalizedIntersectionTheory`.

All three direct production checks passed without diagnostics. The seventeen
transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. The RenormalizedIntersectionTheory umbrella imports all three modules.

## Scope

These are the multiplicities required to turn the trace coefficient
`1/(rℓ(c))` into `1/r`. [Multiplier laws and source terms](gauss-mayer-primitive-orbit-words.md)
and [absolute regrouping](gauss-mayer-primitive-orbit-logarithm.md) are certified.
Primitivity here is whole-pair primitivity, as required by
the certified integral determinant-one root classification; ordinary
single-digit primitivity would give incorrect multiplicities.

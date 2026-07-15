# Differential-independent observable factorization

- **ID:** `differential-independent-observable-factorization`
- **Status:** `[PROVED IN LEAN] [BRIDGE] [CORPUS-USEFUL] [NOT AN RH PROOF]`
- **Scope:** general hypertranscendental families, Xi-zero-indexed Hurwitz family, AQFT-style observable independence

## Statement

Let `F ⊆ E` be fields with a derivation on `E`, and let `x : ι → E` be differentially
independent over `F`.  For a resolution vector `M : ι → ℕ`, write

`P_M = F(δ^n x_i | n < M_i)`.

If two resolution vectors have disjoint clock support,

`∀ i, M_i = 0 or N_i = 0`,

then:

1. `P_M` and `P_N` are linearly disjoint over `F`;
2. `P_M ⊗_F P_N` is a domain;
3. `P_M ∩ P_N = F` inside `E`.

The same three conclusions hold unconditionally for every finite injective family of actual
Xi-divisor support points indexing the continued Hurwitz family.

## Physics relation

Algebraic quantum field theory treats separated observable sectors as independent when their
joint representation is faithful to a tensor product and when they have no hidden common local
observable algebra.  The split property is the operator-algebraic setting in which this tensor
factorization is available.  The theorem above is the exact commutative field analogue for
differentially independent clock sectors:

- injectivity of the tensor comparison is expressed by linear disjointness;
- absence of tensor zero divisors is recorded by the domain theorem;
- absence of hidden shared observables is the exact intersection law `P_M ∩ P_N = F`.

This concerns the factorization of an observability structure.  It does not introduce temporal
evolution.

Primary physics sources used for the bridge:

- Brunetti--Fredenhagen--Imani--Rejzner, *The Locality Axiom in Quantum Field Theory and Tensor
  Products of C*-algebras*, arXiv:1206.5484.
- Fewster--Rejzner, *Algebraic Quantum Field Theory -- an introduction*, arXiv:1904.04051.
- Hoehn--Vanrietvelde, *How to switch between relational quantum clocks*, arXiv:1810.04153.

## Formalization

General module:

- `formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentObservableFactorization.lean`

Main declarations:

- `algebraicIndependent_sum_adjoin_linearDisjoint`;
- `algebraicIndependent_disjoint_adjoin_linearDisjoint`;
- `differentialIndependent_disjointJetFields_linearDisjoint`;
- `differentialIndependent_disjoint_familyObservableFields_linearDisjoint`;
- `differentialIndependent_disjoint_familyObservableFields_inf_eq_bot`;
- `differentialIndependent_disjoint_familyObservableFields_tensor_isDomain`.

Direct Xi/Hurwitz consumer:

- `formal/GaloisForLFunctions/RHTower/XiZeroHurwitzObservableFactorization.lean`;
- `xiZeroHurwitz_disjoint_familyObservableFields_linearDisjoint`;
- `xiZeroHurwitz_disjoint_familyObservableFields_inf_eq_bot`;
- `xiZeroHurwitz_disjoint_familyObservableFields_tensor_isDomain`.

## Corpus value

The previous faithful-net theorem reconstructed the resolution order from field inclusion.  This
result adds exact composition data: separated clock sectors form a faithful tensor product and
have exactly the expected common base.  It therefore discharges future assumptions of the forms

- “the two generated observable fields are linearly disjoint”;
- “their tensor product is a domain”;
- “their intersection contains no nontrivial common observable”.

It also expands the clock picture beyond one hypertranscendental function.  The natural object is
now a family of source observables carrying both an order-faithful net and exact factorization on
disjoint sectors.

## RH impact and hard boundary

For the Xi/Hurwitz family the factorization theorem is unconditional and preserves the individual
divisor labels.  This prevents a proposed RH mechanism from manufacturing cross-zero algebraic
couplings out of disjoint finite jet sectors: no such coupling is present in the Hurwitz observable
fields themselves.

It is not an RH selector.  The proof uses differential independence of the divisor-indexed Hurwitz
family and is insensitive to the real parts of the indexing Xi zeros.  A genuine RH advance still
requires an independent prime--archimedean source relation whose value changes with transverse
zero location.  The present theorem sharpens that search by proving that such a relation cannot be
an ordinary algebraic overlap between disjoint Hurwitz jet sectors.

## Boundary attacks

1. **Tensor-product metaphor attack.**  The theorem does not infer a Hilbert-space tensor product
   from differential algebra.  It proves the precise commutative substitute: linear disjointness,
   tensor-domain injectivity, and base-field intersection.
2. **Existing-infrastructure attack.**  Rational-function tensor injectivity already existed in
   `DisjointRationalFunctionFields`; the new content transports it to arbitrary algebraically and
   differentially independent observable families and supplies the direct Xi/Hurwitz consumer.
3. **Singleton attack.**  For a single clock, disjoint support forces one sector to be empty.  The
   substantive theorem is genuinely family-level and therefore lies beyond single-function HT.
4. **RH-circularity attack.**  No RH premise is used and no zero-location conclusion is claimed.

## Verification

- Exact target: `GaloisForLFunctions.RHTower.XiZeroHurwitzObservableFactorization`.
- Direct source checks: both touched Lean modules.
- Axiom audit: expected only Lean/mathlib logical foundations.

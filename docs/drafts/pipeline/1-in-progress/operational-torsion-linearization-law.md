# Operational torsion linearization law

- **ID:** `operational-torsion-linearization-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL HT LAW / OPERATOR-MODULE LINEARIZATION
- **Scientific status:** `[UNIVERSAL COMMUTATIVITY PHASE LAW PROVED IN SOURCE] [PRIME-CLOCK TORSION INSTANCE PROVED] [NOVELTY PROVISIONAL]`
- **Paper target:** `analytic-grassmann-lattice-dirichlet-fields`

## Master law UL-0: commutativity linearizes hypertranscendence geometry

The stronger corpus-wide law is a sharp phase boundary, not merely a prime-clock closure formula.

Let a commutative `K`-algebra `A` act linearly on an arbitrary state space `M`, choose one root
state `m`, and let a law vector `v` select an element `L(v)` of `A`.  On the symmetric observable
algebra, the complete directional jet of the root is algebraically dependent exactly when the
class of `L(v)` in the root-annihilator quotient is algebraic over `K`.  Therefore

```text
every autonomous one-root commutative complete dependence horizon is a vector subspace.
```

The converse is now exact: every vector subspace is realized by the regular action of the
symmetric algebra on the quotient law space.  Thus the possible horizons in this commutative
phase are **exactly** the vector subspaces, not merely a subclass of them.

This is sharp.  Every finite homogeneous projective zero locus is the exact complete dependence
horizon of a free-word realization, and the realization may be chosen with injective exterior
commutator symbol.  Hence

```text
nonlinear HT horizon topology is an intrinsic witness of escape from autonomous commutativity.
```

This is the universal law around which the paper should be written.  The invariant Grassmannian
and operator-torsion theorem below is its field-level positive classification in a source-faithful
one-clock sector; projective universality is the sharp noncommutative converse.

Exact capstone source:

`formal/GaloisForLFunctions/HTGeometry/HypertranscendenceCommutativityPhaseLaw.lean`

## Law UL-1: algebraically faithful carrier systems

Let `C <= F <= L` be fields, with `L` differential over `F`. Let `V` be a complex source space,
`T : V -> V` a linear clock, and `q : V -> L` a linear carrier map satisfying

```text
delta^n(q(v)) = q(T^n v)
```

for every `n`. Assume **static algebraic faithfulness**:

```text
every C-linearly independent source family maps to an F-algebraically independent carrier family.
```

For `W <= V`, let

```text
Sat_T(W) = span_C {T^n w : w in W, n >= 0},
D(W) = F<q(W)>_delta.
```

Then:

1. `D(W) = F(q(Sat_T(W)))`.
2. `D(U) <= D(W)` iff `Sat_T(U) <= Sat_T(W)`; equality is equivalent to equality of saturations.
3. The generated differential fields are order-isomorphic to the `T`-invariant Grassmannian.
4. For an arbitrary packet `g_i`, relative differential independence over `D(W)` is equivalent to
   linear independence of all orbit classes `T^n g_i + Sat_T(W)`.
5. For one source `g`,

   ```text
   q(g) is differential-algebraic over D(W)
     iff
   P(T) g belongs to Sat_T(W) for some nonzero P in C[X].
   ```

   Hence every nonlinear differential-algebraic relation linearizes in source space to operator
   torsion.
6. If the intermediate-field lattice has finite character, the ordinary source-field
   representation of invariant subspaces preserves arbitrary joins and every nonempty meet.

The universal slogan is

```text
relative HT = torsion-freeness in the operational source quotient.
```

## Multi-operator extension UL-2

For commuting operators `T_1,...,T_r` (and invertible difference operators where present), replace
`C[X]` by the commutative operator algebra

```text
C[X_1,...,X_r,Y_1^{+/-1},...,Y_k^{+/-1}].
```

The expected law is the same: generated difference-differential fields are classified by
operator-submodule saturation, and relative DA is operator torsion in the quotient.

This extension is not yet proved by the current prime-clock leaf.

## Existing evidence

- **Arbitrary autonomous commutative representations:** the full one-root dependence horizon is
  the carrier of a vector subspace, with no cyclicity, finite-dimensionality, grading,
  reducedness, or finite-generation assumption on the represented commutative algebra.
- **Exact commuting converse:** every vector subspace of law space is the complete horizon of an
  explicit autonomous one-root commutative regular representation.
- **Free-word converse:** every finite projective zero locus is realized as an exact complete
  horizon; the same construction has injective exterior commutator symbol.  A nonlinear cone is
  therefore impossible in the commutative phase and realized in a maximally detected
  noncommutative phase.
- **Prime-power profiles:** UL-1 clauses 1--5 are proved by the prime-clock completion,
  invariant-Grassmann, and clock-saturation modules.
- **Tail-dense analytic carriers:** the static decoder, all joins, all nonempty meets, and quotient
  relative independence are proved. Their natural source for UL-1 is the free jet module
  `E tensor C[X]`, not the order-zero space `E` alone.
- **Difference-differential source systems:** exact observation kernels and quotient
  conservativity are proved, as is the data-processing law for source-factorized reporters.
  The full multi-operator field-classification theorem is open.
- **Orientation gauges:** rational gauges preserve every finite observable field while Herglotz
  positivity varies. This shows why order/positivity enrichment is external to the operator-field
  hull rather than a counterexample to it.

## Anti-theatre gate

The abstract proof from static algebraic faithfulness is expected to be elementary pure
transcendental field theory. It is not by itself a major novelty claim. The publishable content is
the sharp commutative/noncommutative phase theorem together with the source-faithful field
classification.  It requires:

1. the general commuting horizon theorem, not merely the cyclic polynomial quotient;
2. the all-projective free realization with a noncommutativity certificate;
3. a minimal field theorem proving the exact field/relative/Kolchin conclusions from static
   faithfulness and clock intertwining; and
4. at least two nontrivial field realizations, not merely a renaming of the prime-profile theorem.

If only the prime-clock realization closes, the paper must call this the **prime-clock torsion
law**, not a universal law.

## Lean target

Proposed module:

`formal/GaloisForLFunctions/HTGeometry/OperationalTorsionLinearization.lean`

Required exact declarations:

- algebraically faithful linear carrier structure;
- least operator saturation and closure laws;
- differential adjunction equals ordinary field of saturation;
- field order/equality classification;
- relative independence iff quotient-orbit independence;
- differential algebraicity iff nonzero polynomial-operator torsion;
- nonempty arbitrary meet and arbitrary join law on the invariant source lattice.

## RH pressure test

Any RH route expressed entirely inside an algebraically faithful carrier field can create new HT
information only by creating a torsion-free class in the operational quotient. Repackaging,
source-factorized reporting, rational gauge correction, and finite differential closure cannot do
so. A successful route must either change the operational source hull or add structure not
represented by the field, such as positivity, reflection, completion, or boundary order.

## Gates

- [x] exact universal candidate stated
- [x] arbitrary autonomous commutative horizon proved linear
- [x] every linear horizon explicitly realized in the commutative phase
- [x] every finite projective zero locus realized in the free phase
- [x] maximal exterior commutator certificate proved for the free realization
- [x] combined commutative/free capstone written in source
- [x] prime-clock instance proved
- [x] anti-theatre boundary recorded
- [ ] abstract single-operator theorem formalized
- [ ] analytic free-jet realization formalized
- [ ] second non-prime realization proved
- [ ] multi-operator extension proved or explicitly excluded
- [ ] specialist literature audit
- [x] paper recut around the verified scope

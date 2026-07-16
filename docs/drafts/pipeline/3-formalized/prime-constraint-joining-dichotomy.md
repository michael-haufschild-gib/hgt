# Prime constraint-joining dichotomy and native collision law

- **ID:** `prime-constraint-joining-dichotomy`
- **Stage:** 3-formalized
- **Type:** GENERAL HT STRUCTURE THEOREM / JOINING REALIZATION AND MAXIMALITY
- **Scientific status:** `[UNCONDITIONALLY FORMALIZED] [NOVELTY PROVISIONAL: HIGH]`
- **Parent:** `prime-valuation-fusion-reconstruction.md`
- **Statement:** Local tail-complete constraint geometry and finite correlation geometry are
  different data. Unrestricted injective prime configurations force the maximal Cartesian joining,
  while every nonempty countable subdirect relation is realizable as the exact recurrent joining of
  a selected family of disjoint prime rows from one source with the same full local recurrent
  locus. Native binary Dirichlet multiplication selects the maximal joining: its same-prime face is
  valuation fusion, its unequal-degree distinct-prime face is ordered tensor product, and its
  equal-degree face is exact symmetrization.

## Master theorem

Let `x : P -> V` be cofinally tail-dense on `K subset V`, and let `I` be a nonempty finite type.
Write

```text
Conf_I(P) = {a : I -> P | a is injective},
X_I(a)    = (x(a_i))_(i in I).
```

Then:

1. **Independent-configuration maximality.** `X_I` is cofinally tail-dense on `K^I`.
   Consequently a continuous observable on `V^I` is nonzero on only finitely many injective
   configurations exactly when it vanishes on `K^I`.

2. **Joining universality.** Let `C subset V^I` be nonempty and countable, and suppose every
   coordinate projection of `C` is all of `V`. There exist one prime source

   ```text
   z : Primes -> V
   ```

   and injective prime rows `a_n : I -> Primes` such that

   ```text
   recurrent_locus(z)                         = V,
   z is cofinally recurrent,
   recurrent_locus((z(a_n(i)))_(i in I))      = C,
   independent configuration constraint of z = V^I.
   ```

   Thus every countable subdirect joining is compatible with the same maximal one-point
   constraint. The joining is independent structure; it is neither determined by the local
   recurrent locus nor forbidden by prime distinctness.

3. **Native binary collision law.** For pure prime-power columns

   ```text
   A_e(c)(p^(e+1)) = c(p),
   A_f(d)(p^(f+1)) = d(p),
   ```

   ordinary Dirichlet convolution satisfies

   ```text
   (A_e(c) * A_f(d))(p^(e+f+2))
       = c(p)d(p),

   (A_e(c) * A_f(d))(p^(e+1) q^(f+1))
       = c(p)d(q)                         if p != q and e != f,

   (A_e(c) * A_e(d))(p^(e+1) q^(e+1))
       = c(p)d(q) + c(q)d(p)              if p != q.
   ```

   Projecting the first product onto its output prime-power layer is exactly the already-defined
   prime-valuation fusion product. Fusion is therefore the one-block collision face of native
   convolution, not an externally adjoined multiplication.

## Positive law

> **Constraint-joining law.** A tail-complete hypertranscendental source determines its local
> constraint geometry, but finite correlation is determined by a joining: a rule selecting which
> source coordinates are observed together. Complete independent sampling forces the maximal
> Cartesian joining. Conversely, every countable subdirect joining can occur without changing the
> maximal local recurrent locus. Native unrestricted Dirichlet multiplication carries only the
> maximal joining and its collision symmetrizations.

This identifies a precise missing datum. A proposed global HT carrier that uses only local source
constraints and unrestricted finite Dirichlet multiplication cannot manufacture a proper
prime-correlation law. It must supply a source-defined joining, incidence restriction, common
clock, reflection coupling, or infinite completion that selects one.

## Why this is stronger than finite factorization

The statement is not merely that products of dense sets are dense. It proves both extremal
directions on one prime-supported source architecture:

```text
unrestricted finite configurations  -> forced maximal product joining,
selected disjoint configurations     -> arbitrary countable subdirect joining.
```

The realization theorem rules out the opposite overclaim that a proper joining must arise from a
different local source geometry. The local geometry can remain maximally recurrent while the
coupled geometry varies through every countable subdirect relation.

## Formal declaration ledger

| Clause | Declaration |
|---|---|
| injective finite configurations | `DistinctConfiguration` |
| configuration source profile | `distinctConfigurationProfile` |
| finite system of distinct representatives | `exists_injective_mem_of_forall_infinite` |
| independent-configuration Cartesian saturation | `cofiniteTailDenseOn_distinctConfigurationProfile` |
| continuous configuration-kernel law | `cofiniteTailDenseOn_distinctConfiguration_continuous_support_finite_iff` |
| subdirect constraint relation | `IsSubdirectConstraint` |
| coupled prime-row realization | `joinedPrimeSource_realizes_subdirect_recurringConstraint` |
| exact repeated countable constraint | `recurringValueSet_repeatedCountableConstraintProfile` |
| countable joining universality | `exists_primeSource_realizing_countable_subdirectConstraint` |
| maximal-independent/arbitrary-coupled dichotomy | `exists_primeSource_independentMaximal_coupledArbitrary` |
| positive prime-power layer projection | `primePowerLayerProjection` |
| same-prime native coefficient | `arithmeticOfPrimePowerColumn_mul_apply_samePrime` |
| fusion is native collision projection | `primePowerLayerProjection_mul_columns` |
| unequal-degree orientation rigidity | `primePower_pair_orientation` |
| ordered distinct-prime coefficient | `arithmeticOfPrimePowerColumn_mul_apply_distinct_unequal` |
| equal-degree unordered rigidity | `equalPrimePower_pair_unordered` |
| symmetrized distinct-prime coefficient | `arithmeticOfPrimePowerColumn_mul_apply_distinct_equal` |

The formal surface is in:

- `formal/GaloisForLFunctions/HTGeometry/PrimeConstraintJoining.lean`;
- `formal/GaloisForLFunctions/HTGeometry/PrimeCollisionConvolution.lean`.

## Literature and novelty boundary

The following parents are classical and are not claimed as new:

- Hall's marriage theorem and finite systems of distinct representatives;
- finite Cartesian-product density and continuous separation;
- Furstenberg joinings and the distinction between product and nonproduct joinings;
- Dirichlet convolution, Bell series, arithmetic functions of several variables, and unique
  factorization of prime-power coefficients;
- the Cashwell--Everett identification of the Dirichlet ring with a countable formal power-series
  ring;
- coefficientwise and exponent-adding products of Dirichlet series.

The candidate new result is the exact prime-supported HT constraint theorem coupling:

```text
cofinite local tail completeness
  -> maximality of every unrestricted finite injective configuration,

arbitrary countable subdirect relation
  -> realization by selected disjoint prime rows of one locally maximal source,

native Dirichlet convolution
  -> the maximal joining's exact collision/tensor/symmetrization faces.
```

Targeted searches found the separate parent theories, including the classical theory of joinings,
Toth's multivariable arithmetic-function survey, and the Cashwell--Everett Dirichlet-ring theorem.
They did not locate this local-maximal/arbitrary-coupled realization dichotomy for prime-supported
HT constraint sources or its exact native collision interface. The novelty score remains
provisional pending specialist review.

## Anti-theatre attack

1. **Topology attack.** Cartesian saturation alone is routine and carries no novelty score.
2. **Joining attack.** Calling `C` a joining does not create a theorem; the load-bearing result is
   the explicit one-source prime realization of every countable subdirect `C` together with the
   simultaneous independent maximality theorem.
3. **Arithmetic attack.** The three binary coefficient identities are unique-factorization
   consequences and are not novel separately. Their role is to prove that native multiplication
   implements the maximal joining rather than a hidden correlation structure.
4. **Dynamics attack.** No invariance or measure is asserted. This is a constraint joining, not a
   Furstenberg joining of dynamical systems.
5. **Higher-order attack.** The formal theorem proves arbitrary finite configuration saturation and
   arbitrary countable finite-coordinate joining realization, but only the binary native
   convolution coefficient stratification. A full `k`-fold partition formula remains optional
   classical packaging unless it produces a new invariant.

## RH pressure test

For zeta's scalar positive Euler source, the one-point constraint is already rank one. The theorem
forces a sharper architectural conclusion than “finite local algebra is insufficient”:

> Any RH-relevant prime correlation must be specified by a nontrivial joining. It cannot emerge
> from unrestricted finite Dirichlet multiplication, because that operation realizes only the
> maximal independent joining and universal collision symmetrization.

The joining must come from data that genuinely couples primes: the functional equation and its
archimedean factor, a common analytic cutoff, an ordered or metric prime incidence, a positivity
completion, or an infinite limiting law. The theorem neither selects such a joining nor proves an
RH criterion.

## Physical research lens

Independent configurations behave like freely addressable modes and force product-state geometry.
Same-mode collisions give local fusion; equal-energy labels create bosonic symmetrization. A proper
joining behaves like coherence or entanglement imposed by a preparation/measurement rule. The
mathematical result says that coherence is not a hidden property of the local spectrum: it is
additional coupling data. This analogy is not part of the theorem.

## Antagonistic score

- **Correctness / rigor:** 100/100 on the stated theorem surface. Every declaration is
  unconditional; the axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- **Novelty:** 88/100 provisional. The joining vocabulary and each proof ingredient are classical;
  the exact one-source maximal/arbitrary dichotomy and prime-collision coupling appear new after a
  targeted search, but require expert priority review.
- **Scientific significance:** 91/100. The theorem classifies the entire finite-correlation freedom
  left after local HT constraint reconstruction and identifies the exact datum any global theory
  must add.
- **Anti-theatre:** pass, provisionally. Removing the arbitrary-joining realization collapses the
  statement to routine product density; removing independent maximality loses the dichotomy;
  removing the native collision law loses the arithmetic consequence.

## Verification

One exact leaf build of
`GaloisForLFunctions.HTGeometry.PrimeCollisionConvolution` compiled both new modules. Each touched
file then passed direct elaboration. The principal declarations depend only on the standard logical
axioms used by the library, and the formal lint gate passes. No full or parallel build was run.

## Gates

- [x] independent finite configuration saturation proved
- [x] continuous finite-support kernel proved
- [x] arbitrary countable subdirect joining realization proved
- [x] same local source plus maximal-independent/arbitrary-coupled dichotomy proved
- [x] same-prime convolution/fusion projection proved
- [x] unequal-degree ordered coefficient law proved
- [x] equal-degree symmetrized coefficient law proved
- [x] exact cached target build and direct touched-file checks passed
- [x] axiom and formal lint gates passed
- [x] primary parent-theory search completed
- [ ] independent specialist priority review
- [ ] canonical infinite joining/completion defect
- [ ] Stage 4 standalone paper

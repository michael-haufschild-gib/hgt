# Countability and Complexity Escape of DA Translation Spectra

- **ID:** ht-da-translation-spectrum-countability
- **Stage:** 3-formalized / not new scientific knowledge
- **Type:** THEOREM (Lean) / BRIDGE
- **Scientific status:** `[BRIDGE]` — correct, but routine from Mahler's 1971 normalization theorem plus one-variable meromorphic identity
- **Statement:** If a meromorphic function `F` on `C` is hypertranscendental over `C(z)`, then the subgroup of shifts `h` for which `F(z+h)-F(z)` is differentially algebraic is countable. More sharply, DA defects at accumulating shifts must have unbounded differential order or unbounded total jet degree.

## Goal

Replace construction-specific translation examples by a universal constraint on every HT meromorphic function. Define

`Stab_DA(F) = {h in C : Delta_h F is DA over C(z)}`,

where `Delta_h F(z) = F(z+h)-F(z)`.

The theorem would show that an HT function may carry dense DA translation constraints, but never uncountably many. Accumulation is possible only through escape of differential order or total jet degree.

## Gates

- [x] 0 -> 1 in-progress: exact theorem, finite-complexity stratification, proof mechanism, and sharp boundary example identified.
- [x] Autonomous reduction: coefficient degree is unnecessary because DA over `C(z)` implies DA over `C` by differential-algebraic transitivity and `z' - 1 = 0`.
- [x] Paper-proof gate: determinant proof below; countability also has the shorter Mahler proof recorded below.
- [x] Significance gate: the countable-or-total law is structurally useful.
- [x] Parent-theory gate: **FAILS scientific novelty.** Mahler's countable normalization makes countability a routine analytic-family corollary; bounded-complexity discreteness is a routine determinantal rank-locus argument.
- [x] Literature and rediscovery gates: coherent-family theory, Mahler normalization, difference-property theory, and fixed-shift DA literature checked.
- [x] Formalization: complete and unconditional in Lean 4 (see **Lean status** below).

## Complexity strata

For nonnegative integers `r,d`, with `d >= 1`, let `E_(r,d)(F)` be the set of shifts `h` for which `Delta_h F` satisfies a nonzero autonomous equation

`P(y, y', ..., y^(r)) = 0`,

where `P` has total degree at most `d`.

Every function DA over `C(z)` is DA over `C`: the element `z` is DA over `C` because `z' - 1 = 0`, and differential algebraicity is transitive. Equivalently, every DA meromorphic function satisfies an autonomous ADE. Hence every DA defect belongs to one of these strata and

`Stab_DA(F) = union_(r,d) E_(r,d)(F)`.

## Bounded-complexity accumulation theorem `[PROVED HERE]` pending proof polish

For every meromorphic `F` on `C` and every fixed pair `(r,d)`, if `E_(r,d)(F)` has a finite accumulation point, then `F` is DA over `C(z)`. Equivalently, if `F` is HT, every fixed-complexity stratum is closed-discrete.

### Finite monomial family

Let

`I = {alpha in N^(r+1) : |alpha| <= d}`

and define meromorphic functions of `(h,z)` by

`M_alpha(h,z) = product_(m=0)^r (F^(m)(z+h)-F^(m)(z))^(alpha_m)`.

For fixed `h`, membership in `E_(r,d)(F)` is exactly linear dependence over `C` of the finite family

`{M_i(h, .) : i in I}`.

### Accumulation forces dependence for every shift

Choose evaluation points away from the discrete pole set of `F`. If the family is dependent for shifts `h_n -> h_*`, then every square evaluation determinant

`det(M_i(h,z_j))`

vanishes at every `h_n`. It is meromorphic in `h`. A nonzero meromorphic function has isolated zeros and cannot have zeros accumulating even at one of its finite-order poles, so the determinant vanishes identically. The standard evaluation criterion for independence of finitely many meromorphic functions then shows that the family is dependent for every `h in C`.

### Meromorphic relation in the shift parameter

View the functions `M_i` as functions of `z` with values in the field `K = Mer(C_h)`. The following evaluation lemma is elementary: if finitely many `K`-valued meromorphic functions of `z` are `K`-linearly independent, there are regular evaluation points `z_1,...,z_N` at which their evaluation matrix has nonzero determinant in `K`. The proof is by induction, using a maximal nonzero minor and Cramer's rule.

All full evaluation determinants vanish, so the `M_i` are dependent over `K`. Equivalently, meromorphic functions `a_i(h)`, not all zero, satisfy

`sum_i a_i(h) M_i(h,z) = 0`

identically as a meromorphic function of `(h,z)`.

### Lowest shift order produces an ADE for `F`

In the Laurent-series field over `Mer(C_z)`, translation at `h=0` gives

`F^(m)(z+h)-F^(m)(z) = h F^(m+1)(z) + O(h^2)`.

If `v_i` is the Laurent order of `a_i` at zero, then

`M_alpha(h,z) = h^|alpha| product_m (F^(m+1)(z))^(alpha_m) + O(h^(|alpha|+1))`.

Take the smallest value of `v_i + |alpha|` occurring in the meromorphic relation. Its coefficient is a differential polynomial

`Q(F',F'',...,F^(r+1))`.

The relation forces `Q=0`. Distinct multi-indices `alpha` give distinct formal monomials, so the extracted polynomial is nonzero. A leading term involving only `alpha=0` would be a nonzero constant vanishing identically and is therefore impossible. Hence a positive-jet monomial occurs, and `Q(F',...,F^(r+1))=0` is a genuine autonomous ADE for `F`.

## Countability theorem `[BRIDGE]`

If `F` is HT, each `E_(r,d)(F)` is closed-discrete and therefore countable. Since the pairs `(r,d)` form a countable set,

`Stab_DA(F)`

is countable.

## Complexity-escape corollary

Let `F` be HT and let distinct DA-defect shifts `h_n` converge in `C`. For any autonomous ADE chosen for each `Delta_(h_n)F`, the pairs

`(differential order, total jet degree)`

cannot remain bounded. At least one component is unbounded along every such sequence.

This is a nonlinear statement. It is stronger than the linear spectral-rank divergence in the factorial-frequency example.

## Multiplicative corollary

If `G` is a nonzero meromorphic HT function on `C`, then

`MultStab_DA(G) = {h : G(z+h)/G(z) is DA}`

is countable. Indeed `L=G'/G` is meromorphic and HT: if `L` were DA, the equation `G'=LG` and differential-algebraic transitivity would make `G` DA. For every `h in MultStab_DA(G)`,

`Delta_h L = (G(z+h)/G(z))' / (G(z+h)/G(z))`

is DA. Thus `MultStab_DA(G) subset Stab_DA(L)`, which is countable.

## Boundary and sharpness

The proved Carroll--Ostrowski bridge in

`../2-fully-proven/not_new_scientific_knowledge/03-ht-translation-projective-geometry/ht-exact-da-translation-stabilizer.md`

realizes `Stab_DA(F)=Q` for an entire HT function. Therefore countability, if correct, is sharp even among dense nonclosed subgroups. The new content cannot be the existence of dense examples; it must be the universal exclusion of uncountable spectra and the bounded-complexity escape mechanism.

## Mahler parent reduction and scientific-novelty verdict

Mahler proved in 1971 that every formal power series over an arbitrary characteristic-zero coefficient field which satisfies an ADE with parameter-dependent coefficients also satisfies an ADE with rational-integer coefficients. Thus all DA analytic germs are covered by the countable family of integer-coefficient ADEs.

Fix a regular base point for `F`. Only countably many shifts make one of the finitely many translated terms singular there, so they can be discarded for the countability argument. For every remaining DA defect, Mahler assigns one of countably many integer-coefficient ADEs. For a fixed ADE `P`, the set of shifts satisfying

`P(z, Delta_h F, (Delta_h F)', ..., (Delta_h F)^(r)) = 0`

is discrete unless `F` is DA. Indeed, an accumulating sequence makes the left side vanish identically in the meromorphic parameter `h`; its first nonzero coefficient at `h=0` is a nonzero ADE for `F'`, hence for `F`. A countable union of these discrete parameter sets is countable.

The same argument applies to any fixed nonzero finite translation stencil

`A_h F = sum_j c_j F(z + lambda_j h)`.

The first nonzero stencil moment `sum_j c_j lambda_j^k` replaces `F'` by `F^(k)` in the lowest-order extraction. Consequently the DA-parameter set of every fixed finite stencil is all of `C` when `F` is DA and countable when `F` is HT.

**Audit verdict:** this theorem is correct and useful, but it is not new scientific knowledge under the routine-parent test. Mahler supplies the countable DA cover, and the remaining identity-theorem argument is standard. The bounded-complexity refinement is likewise a standard finite-rank determinantal locus. Retain the result as a bridge and as a constraint on stronger classification questions.

Primary parent: K. Mahler, *A remark on algebraic differential equations*, Rend. Accad. Naz. Lincei 50 (1971), 402--412.

## Parent attacks completed

1. **Coherent families.** Boshernitzan--Rubel concerns one common ADE; it is adjacent rather than the shortest parent.
2. **Mahler normalization.** This is the decisive parent: arbitrary DA germs lie in a countable union of fixed integer-coefficient ADE solution families.
3. **Analytic determinantal loci.** These routinely imply the fixed-order/fixed-degree discreteness refinement.
4. **Difference property.** Carroll and Montel-type theory provide the sharp dense countable boundary examples and the finite-dimensional analogues.

## Log

- 2026-07-10 - Opened after the exact tail-gcd realization theorem was downgraded to a Carroll--Ostrowski bridge. The surviving universal residue is countability plus nonlinear complexity escape.
- 2026-07-10 - Strengthened from entire to meromorphic functions. The evaluation-minor and lowest-shift-order proof survives moving poles by working over meromorphic function fields.
- 2026-07-10 - Removed coefficient degree from the complexity measure using autonomous reduction. Also corrected the rigidity statement from an exclusive dichotomy to the precise implication `accumulation => F is DA`.
- 2026-07-10 - Parent-killed by Mahler's 1971 integer-coefficient normalization theorem. Downgraded to `[BRIDGE]`; the finite-stencil extension is recorded only as infrastructure for the next classification problem.

## Lean status (2026-08-29)

Fully formalized unconditionally in Lean 4, for sources analytic off an arbitrary **closed
countable** singular set — a class that contains every meromorphic function on `C`.  The
dependency-closed implementation is:

- `HTGeometry/DomainJetRelationLocus.lean` — the bounded-complexity `(n,d)` sample-minor
  certificate for `DifferentiallyAlgebraicOn f Ω` on an arbitrary open preconnected domain, with
  sample nodes placed inside a disc of `Ω`
  (`differentiallyAlgebraicOn_iff_forall_coordinateMinor_det_eq_zero`);
- `HTGeometry/DomainTranslationSlopeMinor.lean` — the `h⁻¹`-normalized translation-defect minor on
  a domain, its continuity at `h = 0`, the diagonal factorization away from `0`, antiderivative
  closure on a domain (`differentiallyAlgebraicOn_of_deriv`) and the uniform branch
  (`differentiallyAlgebraicOn_deriv_of_uniform_domain_translation_relations`);
- `HTGeometry/MeromorphicTranslationDefectCountability.lean` — the singular-set bookkeeping, the
  shift-analytic minor determinant, and the capstone
  `countable_defectDAStabilizer`: for `S` closed and countable, `F` analytic on `Sᶜ` and
  `¬ DifferentiallyAlgebraicOn F Sᶜ`, the set of shifts `h` with
  `DifferentiallyAlgebraicOn (fun z => F (z + h) - F z) (defectDomain S h)` is countable;
- `HTGeometry/MeromorphicTranslationComplexityEscape.lean` — the fixed-complexity stratum
  (`HasDifferentialRelationOfComplexityOn`), a sample disc whose nodes avoid a prescribed countable
  set, the accumulation theorem
  `differentiallyAlgebraicOn_of_boundedComplexity_defects_accumulate` and the complexity-escape
  corollary `not_exists_injective_tendsto_boundedComplexity_defect`;
- `HTGeometry/MeromorphicMultiplicativeTranslationDefect.lean` — the domain logarithmic-derivative
  equivalence `differentiallyAlgebraicOn_logDeriv_iff`, relation extension from a subdomain, and
  the multiplicative capstone `countable_multDefectDAStabilizer`;
- `HTGeometry/StencilJetExpansion.lean` — a local affine chain rule for iterated derivatives, the
  stencil moments, and the moment formula `iteratedDeriv_stencilShiftProfile_zero` together with
  the `k`-fold removable division `dslopeIterZero`;
- `HTGeometry/DifferentialAlgebraicOnSum.lean` — additive closure of differential algebraicity on a
  domain (constants, binary sums, finite sums, scalar multiples);
- `HTGeometry/StencilTranslationDefectCountability.lean` — the finite-stencil extension:
  `countable_stencilDAStabilizer` (countable parameter set when the source is
  hypertranscendental, with `M_m = 0` for `m < k` and `M_k ≠ 0`) and
  `stencilDAStabilizer_eq_univ_of_differentiallyAlgebraicOn` (all of `C` when the source is
  differentially algebraic).

The already-owned entire case is `HTGeometry/EntireTranslationDefectCountability.lean`
(`countable_differentiallyAlgebraic_translationDefect`) and
`HTGeometry/EntireMultiplicativeTranslationDefectCountability.lean`.

No `sorry`, `admit`, new axiom or heartbeat increase is used.  Targeted `lake env lean` and
`lake build` of each new module pass; axiom audits of every new capstone report only `propext`,
`Classical.choice` and `Quot.sound`.  All new modules are wired into
`GaloisForLFunctions.HTGeometry`.

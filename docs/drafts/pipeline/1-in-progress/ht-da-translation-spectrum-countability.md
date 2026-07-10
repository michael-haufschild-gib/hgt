# Countability and Complexity Escape of DA Translation Spectra

- **ID:** ht-da-translation-spectrum-countability
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / UNIVERSAL OBSTRUCTION
- **Scientific status:** `[NOVELTY UNVERIFIED]`
- **Statement:** If a meromorphic function `F` on `C` is hypertranscendental over `C(z)`, then the subgroup of shifts `h` for which `F(z+h)-F(z)` is differentially algebraic is countable. More sharply, DA defects at accumulating shifts must have unbounded differential order or unbounded total jet degree.

## Goal

Replace construction-specific translation examples by a universal constraint on every HT meromorphic function. Define

`Stab_DA(F) = {h in C : Delta_h F is DA over C(z)}`,

where `Delta_h F(z) = F(z+h)-F(z)`.

The theorem would show that an HT function may carry dense DA translation constraints, but never uncountably many. Accumulation is possible only through escape of differential order or total jet degree.

## Gates

- [x] 0 -> 1 in-progress: exact theorem, finite-complexity stratification, proof mechanism, and sharp boundary example identified.
- [x] Autonomous reduction: coefficient degree is unnecessary because DA over `C(z)` implies DA over `C` by differential-algebraic transitivity and `z' - 1 = 0`.
- [ ] Paper-proof gate: polish the analytic linear-dependence lemma and the meromorphic-kernel extraction.
- [ ] Significance gate: test whether countability changes the known structural picture of HT functions rather than merely rephrasing genericity.
- [ ] Parent-theory gate: attack with coherent-family theory, analytic-set/Noetherian arguments, differential algebraic families, and classical difference-property theory.
- [ ] Literature and rediscovery gates: search exact cardinality, bounded-complexity, and analytic-family formulations in all parent fields.
- [ ] Formalization: only after scientific novelty survives.

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

## Countability theorem `[PROVED HERE]` pending parent/literature audit

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

`../2-fully-proven/not-new/ht-exact-da-translation-stabilizer.md`

realizes `Stab_DA(F)=Q` for an entire HT function. Therefore countability, if correct, is sharp even among dense nonclosed subgroups. The new content cannot be the existence of dense examples; it must be the universal exclusion of uncountable spectra and the bounded-complexity escape mechanism.

## Parent attacks to run

1. **Coherent families.** Determine whether Boshernitzan--Rubel coherent-family theory already states that a holomorphic parameter family whose members satisfy possibly different autonomous ADEs of uniformly bounded order and degree forces the parameter derivative to be DA.
2. **Analytic determinantal loci.** Search for an existing theorem that bounded differential-algebraic complexity pulls back to a discrete-or-total analytic subset under a holomorphic curve.
3. **Differential algebraic families.** Compare with Ritt, Kolchin, Seidenberg, and specialization theorems for differential polynomial families.
4. **Difference property.** Search whether the class of DA entire functions is known to have a cardinal or local difference property.
5. **Meromorphic specialization literature.** Search whether the countable-or-total DA-parameter locus for a jointly meromorphic family is already known in differential algebraic geometry or coherent-family theory.

## Log

- 2026-07-10 - Opened after the exact tail-gcd realization theorem was downgraded to a Carroll--Ostrowski bridge. The surviving universal residue is countability plus nonlinear complexity escape.
- 2026-07-10 - Strengthened from entire to meromorphic functions. The evaluation-minor and lowest-shift-order proof survives moving poles by working over meromorphic function fields.
- 2026-07-10 - Removed coefficient degree from the complexity measure using autonomous reduction. Also corrected the rigidity statement from an exclusive dichotomy to the precise implication `accumulation => F is DA`.

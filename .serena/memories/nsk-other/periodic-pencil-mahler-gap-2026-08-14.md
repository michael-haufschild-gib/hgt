# periodic-pencil `(11)`: the exact remaining gap after steps (i)–(iii)

`HTGeometry/FamilyBoundedRelationSurvival.exists_coeff_ne_zero_famJets_of_boundedRelation`
kills every nonzero jet relation `Q` **with algebraic coefficients**.  To get
`DifferentialIndependent ℂ` we must drop that hypothesis.  This note records why it is not routine
and which route works, so the next session does not rediscover the dead ends.

## Dead ends (verified by hand this session)

1. **`formal_mahler_descent` with `K = ℚ̄`.**  That theorem descends the *coefficient field of the
   relation* to any subfield containing the *series' coefficients*.  Ours are `u_i e^{−b_i}`,
   transcendental, so the smallest usable `K` is far bigger than `ℚ̄` — no gain.
2. **Independence over `ℚ̄` ⇒ independence over `ℂ`.**  FALSE for families.  With `c` a
   transcendental constant, `x₁` and `c·x₁` are ℂ-dependent as *values*; a trdeg count shows
   `ℚ`-independence of a finite jet set is compatible with `ℚ(c)`-dependence whenever
   `trdeg_ℚ ℚ(c) ≥ 1`.  Adding more jets does not help: the relation lives on a fixed finite set.
3. **Wronskian descent.**  Linear dependence over a field of constants does give a vanishing
   Wronskian, but only returns dependence over the *full* constant field of the ambient — here `ℂ` —
   so it recovers nothing.
4. **Reduce to the single-element case.**  Differential dependence of the family `{rescale q_i H}`
   does not make `H` itself differentially algebraic, so
   `differentialAlgebraicOver_of_intermediate_trdeg_lt_aleph0` (which is about ONE element) does not
   apply directly.

## The route that works

The classical statement is: *a family differentially dependent over a differential field extension
`F` which is differentially algebraic over `k` is already differentially dependent over `k`* — this
is additivity of **differential** transcendence degree,
`dtrdeg_k(k⟨x⟩) ≤ dtrdeg_k F + dtrdeg_F(F⟨x⟩) = 0 + dtrdeg_F(F⟨x⟩) < |x|`.
The corpus has ordinary `Algebra.trdeg` additivity (`trdeg_add_eq`) and
`differentialAdjoin_trdeg_lt_aleph0_of_finite_jetSet`, and the single-element consequence
`differentialAlgebraicOver_of_intermediate_trdeg_lt_aleph0`, but **no differential transcendence
degree**.  So the missing brick is a family analogue of that single-element descent, i.e. Kolchin's
dtrdeg additivity in the special case needed:

> `F` a derivation-closed intermediate field of finite ordinary trdeg over `k`, `x : ι → K` finite,
> `¬ DifferentialIndependent F x` ⇒ `¬ DifferentialIndependent k x`.

In the application `F = differentialAdjoin ℚ S` with `S` the (finitely many, constant) coefficients
of the relation, exactly as in `FormalMahlerIntegerNormalization`.  Building this is the whole of
the remaining step; after it, the family Mahler normalization and step (iv) are bookkeeping.

See `mem:nsk-other/periodic-pencil-item11-progress-2026-08-14`.

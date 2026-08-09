# The Gram diagonal for every modulus, as digamma differences

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The find

`QuarterGramEntry` assembled the `q = 4` entry with three hand-made reindexings along `k ↦ 4k + j`. Mathlib
already has the general tool — `Mathlib/Analysis/SumOverResidueClass.lean`, `Nat.sumByResidueClasses`:

`∑' n, f n = ∑ j : ZMod N, ∑' m, f (j.val + N·m)`   (for summable `f`, `0 < N`)

The corpus was not using that file. Connecting it generalises the assembly from one modulus to all of them.

## What is proved

`RHTower/GramResidueDecomposition.lean`:

* `gramTerm q k = (k mod q)²/(q²k(k+1))` with `gramTerm q 0 = 0`, and `hasSum_gramTerm` reindexing the Gram
  series of `hasSum_bdGram_discrete` onto all of `ℕ` (the `k = 0` term vanishes, so
  `Function.Injective.hasSum_iff` applies);
* **`bdGram_self_eq_sum_residueClasses` — `bdGram (1/q) (1/q) = ∑_{j : ZMod q} ∑'ₘ gramTerm q (j.val + qm)`**;
* `gramTerm_residue_class` — the `j`-th class contributes `(j.val)²/q²` times the progression sum
  `∑'ₘ 1/((j.val+qm)(j.val+qm+1))`.

The `j = 0` class contributes nothing, and for `j.val ≥ 1` the progression sum is
`(ψ((j+1)/q) − ψ(j/q))/q` by `ResidueClassRecipSeries`. So for **every** modulus

`bdGram (1/q) (1/q) = (1/q³) · ∑_{j=1}^{q-1} j²·(ψ((j+1)/q) − ψ(j/q))`,

which is Vasyunin's structure, obtained unconditionally and without any restriction on `q`.

## Scope

This is the *reduction* to digamma values, valid for all `q`. Which `q` yield closed forms is separate and
already settled: duplication and reflection close only `q | 4` (`quarter-gram-entry.md`), so `q = 3, 8, …` need
Gauss's general theorem. The value of this file is that any future digamma value plugs straight in, and the
`q = 4` assembly is no longer a special construction but an instance of a general decomposition.

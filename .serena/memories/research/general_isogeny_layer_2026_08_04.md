# General isogeny layer (corpus-owned, 2026-08-04)

Mathlib v4.32.2 has **zero** occurrences of "isogeny". The corpus now owns a general layer under
`formal/GaloisForLFunctions/HTGeometry/Isogeny*.lean` (8 modules, all in the HTGeometry umbrella,
no `sorry`/`axiom`, axioms = propext/Classical.choice/Quot.sound).

## The definition that makes it general

`IsIsogeny (f : G →* H)` for commutative `G H` := `Finite (ker f) ∧ Finite (H ⧸ range f)`.
Degree `isogenyDegree f : ℚ := kerCard f / cokerCard f` where `cokerCard f = (range f).index`.

- surjective + finite kernel (abelian varieties, tori) → `deg = |ker|`
- injective + finite cokernel (lattices) → `deg = 1/|det|`
The reciprocal is forced by contravariance of the lattice picture; it is what makes the degree
compose across both classical conventions.

## Modules and headline results

- `IsogenyIndexArithmetic` — `MonoidHom.card_ker_mul_index_range_comp`:
  `|ker(gf)|·[H:im f]·[K:im g] = |ker f|·|ker g|·[K:im(gf)]`, **unconditional** (Nat.card/index
  zero conventions). Counting shadow of the 6-term snake sequence, proved with pure index
  bookkeeping — no exactness machinery.
- `IsogenyGeneral` — `IsIsogeny` (structure), `IsIsogeny.comp`, `isogenyDegree_comp`.
- `IsogenyComplement` — `MonoidHom.exists_complement`: for **every** hom of commutative groups
  there is `f'` with `f'∘f = [n]_G`, `f∘f' = [n]_H`, `n = kerCard·cokerCard`. No hypotheses.
  Also `exists_complement_isIsogeny` (two-sided criterion).
- `IsogenyRegular` — class `IsIsogenyRegular` (`[n]` an isogeny for all n>0); transported along
  isogenies in **both** directions; `IsIsogenous` refl/trans/symm; `isogenyDegree_pow_eq_of_isogeny`
  (deg[n] is an isogeny invariant → dimension for AVs, rank for lattices).
- `IsogenyKernel` — kerCard=1 ↔ injective, cokerCard=1 ↔ surjective; quotient by finite subgroup is
  a surjective isogeny of that degree; every surjective isogeny = quotient by its kernel.
- `IsogenyLattice` — endo of finite free ℤ-module is an isogeny iff `det ≠ 0`; `|coker| = |det|`;
  lattices are isogeny-regular; **isogenous lattices have equal rank**.
- `IsogenyFinitelyGenerated` — every f.g. abelian group is isogenous to `Fin n → ℤ`; f.g. ⇒
  isogeny-regular; **rank is a complete isogeny invariant** (torsion is invisible).
- `IsogenyGroupObject` — `pointHom` (postcomposition on point groups of commutative group objects),
  `IsPointwiseIsogeny`, `pointwiseDegree_comp`. Needs `[BraidedCategory C]` in the binders
  (mathlib gives only `Nonempty`/`Subsingleton (BraidedCategory C)` for cartesian categories).

## Lean traps hit while building this

- `to_additive` **cannot** create a `structure`/`class` from scratch ("has no value"). Declare the
  additive version manually FIRST, then `@[to_additive TheAddName] structure/class ...`.
- Applying `Subgroup.relIndex_ker` with a metavariable target blows the heartbeat budget; supply
  `(K := ...)` explicitly. `Subgroup.relIndex` is a plain `def`, so state facts at the `relIndex`
  level rather than via `subgroupOf ... |>.index`.
- `omit [inst] in` must precede the docstring, not sit between docstring and `theorem`.
- If `IsIsogeny` were a `def` to `And`, dot-notation resolves to `And.*` after `obtain` whnf's it —
  hence it is a `structure`.
- Additive names to remember: `IsAddIsogeny`, `IsAddIsogenyRegular.isogeny_nsmul`,
  `IsAddIsogeny.isAddIsogenyRegular_target/_source`, `AddMonoidHom.isogenyDegree_nsmul_eq_of_isogeny`.

## Prior corpus `Isogeny*` modules are unrelated

`IsogenyKernelClosure`, `TorusIsogenyTail`, `AbelianVarietyIsogenyTail`,
`IsogenyTailMaurerCartanHolography`, `MultiplicativeIsogenyTailHolography`,
`NonautonomousIsogenyTransport` are about stable tails of iterated endomorphisms in differential
and function-field settings. They use the word descriptively and never define the notion.

Card: `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/general-isogeny-theory-for-commutative-groups.md`

## Unrelated pre-existing breakage found

`lake build +GaloisForLFunctions.HTGeometry` fails at HEAD with
`environment already contains 'GaloisForLFunctions.HTGeometry.kgDuhamelKernel._proof_1'` —
`KleinGordonMildSolution` vs `KleinGordonPotentialFlow`. Both are imported at HEAD; not caused by
the isogeny work. Individual module builds are unaffected.

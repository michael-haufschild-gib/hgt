# F2 — exact finite suffix partitions of source Hecke matrices

- **Stage:** 3-formalized
- **Result:** Every nonnegative matrix of determinant `n>0` has a unique positive word times terminal Hecke-basis factorization. Source branch transitions give a complete, uniquely labelled finite suffix partition of sufficiently long words.
- **Purpose:** Supply the finite identity needed to transport the Lewis equation through the actual Hecke correspondence.

## Normal forms

Write `L=[[1,1],[0,1]]`, `R=[[1,0],[1,1]]`, and `M(u)` for their ordered word product. A terminal matrix `B=[[a,b],[c,d]]` satisfies `c<a`, `b<d`, and `ad=bc+n`.

For a nonnegative matrix of positive determinant, either its rows are comparable coordinatewise or these terminal inequalities hold. In the comparable case, subtract the smaller row. The determinant stays `n`; the sum of entries strictly decreases because the diagonal entries are positive. Induction gives

`A=M(u)B`.

A terminal matrix cannot begin with either generator. If a nonterminal matrix begins with `L`, its top row dominates; if it begins with `R`, its bottom row dominates. Opposite initial letters are incompatible with positive determinant. Each generator is cancellable on natural matrices, so induction proves uniqueness of both `u` and `B`.

Terminal matrices have every entry at most `n`, hence total size at most `4n`. Every letter increases total size by at least one. Transposition gives right subtraction: any matrix with size greater than `4n` has a unique last letter and right predecessor.

Conversion between natural matrices and integral quadruples identifies terminal matrices exactly with `heckeSet n`, the finite set in the actual source operator. No enlarged or substituted basis set is used.

## Transition words

For a terminal `B` and `b∈{L,R}`, uniquely reduce

`B b=M(u)C`.

Right multiplication increases size by at most a factor two. Therefore `|u|≤8n`, and `C` is again an actual Hecke basis.

Fix a terminal target `C` and a word `W` with `|W|>4n`. Then `M(W)C` has size greater than `4n`, so uniquely write it as `A b`. Reduce `A=M(v)B`, then reduce `B b=M(u)C'`. Uniqueness of left normal forms gives

`C'=C`, `W=v u`.

Thus every sufficiently long word ends in a transition word targeting `C`. The label `(B,b,u)` and remaining prefix `v` are unique: right cancellation recovers `(b,A)`, then left normal-form uniqueness recovers `(v,B)`, and word cancellation recovers `u`.

The partition is by **suffixes**. Prefixes act on the left, exactly as required when iterating the Lewis binary splitting equation.

## Scope

This is an exact finite combinatorial statement about the actual source matrices. Harmonic summation, all-prime boundary evaluation, and physical signed-form positivity require further proofs.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/HeckePositiveWordReduction`:

- `heckeWordNormalForm_exists`
- `heckeWordNormalForm_unique`
- `heckeMatrixSize_word_growth`
- `heckeTerminal_isHeckeBasis`
- `heckeTerminal_size_le`
- `heckeRightDivision_exists`
- `heckeRightDivision_unique`
- `hasHeckeDeterminant_mul_generator`
- `heckeMatrixTuple_natMatrix`
- `heckeMatrixTuple_mem_iff`
- `mem_naturalHeckeSet_iff`
- `heckeTransition_exists`
- `heckeTransition_suffix_exists`
- `heckeTransition_suffix_unique`

Individual final `lake --old env lean` audit passed without warnings. All fourteen declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Umbrella import wired.

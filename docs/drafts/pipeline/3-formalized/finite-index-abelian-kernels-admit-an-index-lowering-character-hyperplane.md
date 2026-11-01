# An index-lowering character hyperplane at every finite index

- **Stage:** 3-formalized.
- **Type:** THEOREM (Lean).
- **Count:** Contribution 6; helper theorems are not counted separately.
- **Source:** B9 in `docs/reports/review-3110/route-obstacles.md`.
- **Statement:** Every Hermitian kernel on an arbitrary abelian group with
  negative index at most `r+1` admits a character `χ` such that each finite
  Gram form restricted to `ker(charEval χ)` has negative index at most `r`.
  No growth, freeness, or countability assumption is needed.

## Corpus bridge and novelty

The index-one result `exists_positive_character_hyperplane_of_negIndex_le_one`
uses eigenvalue uniqueness specific to one negative direction.
`exists_common_eigenvector_family` handles arbitrary commuting families only
on finite-dimensional spaces. The finite-index column completion and
`exists_nonpositive_eigenvector` supply the single-operator input needed
for a minimal closed-subspace argument in arbitrary Hilbert dimension.

Final searches `/tmp/hgt-character-hyperplane-final-novelty.json` and
`/tmp/hgt-common-finite-line-final-novelty.json` find the finite-dimensional
common-line theorem, the index-one result, and the bounded free-lattice
classification. The source of `negIndex_le_iff_exists_rank` supplies arbitrary
correction functions; it does not construct a character. No earlier general
finite-index common nonpositive line or global character hyperplane was
found. Newly written helper modules are not independent evidence or
separate contributions.

## Paper proof

Write the completed column form as
`B((x,a),(y,b)) = ⟨x,y⟩−⟨a,b⟩` on `H×E`, with `E` finite-dimensional.

1. **Compact normalized directions.** Give `H` its weak topology and `E`
   its norm topology. The set `||x||≤1, ||a||=1` is compact. Every nonzero
   nonpositive vector can be scaled into this set. Norm-closed linear
   subspaces are closed in this mixed topology: transport to the Hilbert
   product and express a closed subspace as the common zero set of inner
   products against its orthogonal complement. Decreasing chains of
   closed subspaces containing a nonpositive direction therefore retain
   one in their intersection.

2. **Minimal invariant subspace.** Among closed subspaces containing such
   a direction and invariant under every operator and its inverse, Zorn's
   lemma gives a minimal `W`. All operators are commuting invertible
   isometries of `B`.

3. **Complete splitting of a closed subspace.** Put
   `V={x:(x,0)∈W}` and `F={w∈W:w.1∈V⊥}`. Orthogonal projection onto the
   closed Hilbert subspace `V` gives a continuous orthogonal decomposition
   `W=(V×{0})⊕F`. Projection `F→E` is injective, since its kernel has positive
   coordinate in both `V` and `V⊥`. Hence `dim F≤dim E`. The radical of `W`
   lies in `F`. If it vanishes, the Hermitian form on `F` is nondegenerate.
   A basis, the finite Hermitian matrix spectral theorem, and separation
   of positive and negative eigenvalues split `F` into two finite complete
   weighted Hilbert spaces. Combining the positive finite part with `V`
   gives a complete signed Hilbert model for `W`.

4. **Common nonpositive line.** If the radical is nonzero, it is a finite
   invariant subspace; inverse invariance and preservation of `B` prove
   its invariance. The finite-dimensional arbitrary-family common
   eigenvector theorem supplies a common null vector. Otherwise use the
   complete signed model from step 3. Its negative factor is nontrivial
   because `W` contains a nonzero nonpositive vector. For each operator,
   `exists_nonpositive_eigenvector` supplies an eigenvector inside `W`.
   Its eigenspace in `W` is closed and invariant under every commuting
   operator and inverse. Minimality makes that eigenspace all of `W`.
   Thus every operator is scalar on `W`; any fixed nonzero nonpositive
   vector is a common eigenvector.

5. **Character and index drop.** Completed abelian translations commute.
   Their common nonpositive vector `w` has eigenvalues forming a character
   `α`, since `w≠0` and translations multiply. Set `χ(g)=conj(α(g⁻¹))`.
   Invariance gives `B(w,T_g v)=χ(g)B(w,v)`. Consequently every finite
   column synthesis with `χ`-mass zero is orthogonal to `w`. For a strictly
   negative coefficient subspace `U` in that hyperplane, synthesis is
   injective. The verified theorem
   `finrank_add_one_le_of_negative_orthogonal` gives
   `dim U+1≤dim E≤r+1`, including when `w` is null. If the completed
   negative factor has dimension zero, the kernel is positive definite
   and the trivial character suffices.

The only analytic inputs are existing Hilbert weak compactness, orthogonal
projection, completion, and the verified single-isometry nonpositive
vector theorem. Finite Hermitian signature follows from mathlib's matrix
spectral theorem. No invariant-subspace or spectral hypothesis is added
to the kernel statement.

## Lean verification

Capstones: HKT `FiniteNegative.exists_common_nonpositive_eigenvector` and
`exists_index_lowering_character_hyperplane`, in
`Index/CommutingFiniteIndexIsometries.lean` and
`Index/FiniteIndexCharacterHyperplane.lean`.

All twelve new modules pass Lean. The kernel capstone passes its final direct
`lake --old env lean` check. Both transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Required helper oleans are
built; programme umbrellas are wired. No placeholders or proof-limit
increases occur in the source.

The general unbounded higher-index spectral decomposition remains open.

# Translation-stable positive constraints at finite index

- **Stage:** 2-fully-proven on paper; Lean incomplete.
- **Type:** THEOREM (paper).
- **Source:** B9 in `docs/reports/review-3110/route-obstacles.md`.
- **Statement:** A Hermitian kernel on an abelian group has negative index
  at most `r` iff there is a translation-invariant space `Φ` of scalar
  functions, of dimension at most `r`, such that every finite coefficient
  vector annihilating `Φ` has nonnegative kernel quadratic form.
- **Count:** Not counted until formalized.

## Mathematical gain and novelty

The existing `negIndex_le_iff_exists_rank` supplies arbitrary correction
functions. Here all constraints belong to one finite-dimensional translation
module. This preserves the group action needed for an unbounded spectral
classification. One character lowering the index does not supply the
simultaneous positive constraint space.

Searches `/tmp/hgt-next-finite-index-frontier.json`,
`/tmp/hgt-maximal-invariant-positive-frontier.json`, and
`/tmp/hgt-translation-stable-constraints-novelty.json` find single-operator
invariant contraction graphs, common nonpositive lines, orthogonal models
of subquotients, and affine Haar corrections under periodicity. The finite
rank repair and Haar source statements do not give the proposed general
translation-stable constraints. No earlier common maximal nonpositive
subspace or equivalent kernel result was found.

## Dependency-closed paper proof

Complete the kernel column representation as `X=H×E`, with `H` Hilbert,
`E` finite-dimensional of dimension at most `r`, and
`B((x,a),(y,b))=⟨x,y⟩−⟨a,b⟩`. Translations are commuting continuous
invertible `B`-isometries.

1. **Signed orthogonal complements.** For a subspace `U`, write
   `Uᵇ={x:B(u,x)=0 for all u∈U}`. This is closed. If `U` is closed,
   `(Uᵇ)ᵇ=U`: in the positive Hilbert product, use the unitary involution
   `J(x,a)=(x,−a)` to convert `B`-orthogonality to Hilbert orthogonality,
   then apply the Hilbert double-complement identity. If `U` is invariant
   under every translation and inverse, so is `Uᵇ`.

2. **A maximal finite invariant nonpositive space.** Negative-coordinate
   projection is injective on every nonpositive subspace: a vector with
   zero negative coordinate has zero positive norm. Thus such a subspace
   has dimension at most `dim E`. The zero subspace is invariant, so choose
   an invariant nonpositive `U` of largest dimension. It is finite and
   closed. Put `W=Uᵇ` and `R=rad(B|W)=W∩U`. The radical is finite and
   invariant, by preservation of `B` and two-sided invariance of `W`.

3. **Complete radical quotient.** Give `X` its positive Hilbert product
   norm. Let `P_R` be Hilbert orthogonal projection onto the finite space
   `R`, set `Q=1−P_R`, and `S=W∩R^⊥`. Since `R⊆W`, every `w∈W` splits
   uniquely as `P_R w+Qw∈R⊕S`. The closed space `S` represents `W/R`.
   Its restricted `B` is nondegenerate: a vector in `S` orthogonal to `S`
   is orthogonal to `R` as well, hence belongs to `R∩R^⊥={0}`.
   The verified closed-subspace signed splitting therefore gives `S` a
   complete Hilbert model with finitely many negative directions.

   On `S`, set `A_i s=Q T_i s`. These maps are continuous, preserve `B`,
   and have inverses `Q T_i⁻¹`. Indeed `Q` removes only radical vectors,
   and translations preserve the radical, so `Q T_i Q=Q T_i` on `W`.
   The same identity proves that all `A_i` commute. Thus every hypothesis
   of the common nonpositive line theorem is discharged on this quotient.

4. **Positivity of the orthogonal complement.** Suppose `W` contains a
   negative vector. Its `Q`-image is still negative, so the signed model
   of `S` has a nontrivial negative factor. The common-line theorem gives
   a nonzero nonpositive `s∈S` such that each `T_i s−α_i s` lies in `R`,
   with `α_i≠0`. It also gives inverse invariance modulo `R`.
   Since `R⊆U`, the space `U+ℂs` is invariant in both directions.
   Since `s∈Uᵇ`, its quadratic form is the sum of the two nonpositive
   summand forms. Finally `s∉U`: otherwise `s∈W∩U=R`, contradicting
   `s∈R^⊥` and `s≠0`. This strictly increases dimension, contradicting
   maximality. Therefore `B` is nonnegative on `Uᵇ`.

5. **Translation-stable kernel constraints.** Let `v` be the column at
   the identity and put `Φ={g↦B(u,T_g v):u∈U}`. Conjugate linearity in
   `u` makes this a complex vector space. A basis of `U` spans `Φ`, so
   `dim Φ≤dim U≤r`. Translation by `h` sends this function to
   `g↦B(T_h⁻¹u,T_gv)`, which remains in `Φ`. If finite coefficients
   annihilate every function of `Φ`, their column synthesis lies in
   `Uᵇ`, and its kernel quadratic form is nonnegative.

6. **Converse.** Choose a basis of `Φ`. On any strictly negative finite
   coefficient subspace, evaluation against this basis is injective:
   its kernel would be both nonnegative by the assumed constraint law
   and strictly negative. The subspace therefore has dimension at most
   `dim Φ≤r`. Taking all finite Gram restrictions proves the index bound.

The quotient construction uses only Hilbert projection and the already
verified complete signed splitting. No quotient completeness, invariant
subspace, or spectral hypothesis is assumed in the kernel statement.

## Lean status

`SignedOrthogonalComplements` passes Lean; its three printed axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
The radical-complement retraction, induced isometries, maximal invariant
nonpositive subspace, finite pairing space, and kernel capstones are drafted
and awaiting verification. No contribution is counted from these drafts.

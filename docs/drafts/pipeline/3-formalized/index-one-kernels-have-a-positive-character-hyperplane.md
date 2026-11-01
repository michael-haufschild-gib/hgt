# A positive character hyperplane for every index-one abelian kernel

- **Stage:** 3-formalized.
- **Obstacle:** B9, invariant structure of arbitrary unbounded finite-index kernels.
- **Statement:** Every Hermitian kernel `k` on an abelian group with negative
  index at most one admits a character `χ : G → ℂˣ` such that
  `Σᵢ cᵢ χ(xᵢ) = 0` implies nonnegativity of its finite Gram form.
  Conversely, existence of such a hyperplane implies index at most one.
  No boundedness, countability, freeness, or growth assumption is needed.
- **Not claimed:** The character is unitary. That requires a separate argument.
- **Count:** Contribution 3; all supporting lemmas belong to this result.

## Corpus bridge

HKT `ColumnForm` supplies the nondegenerate Hermitian column form, its cyclic
generators, and the form-preserving translation representation.
`FiniteIndexIsPositiveMinusFiniteRank` supplies finite Gram index control.
HTGeometry `BrouwerFixedPoint` supplies the finite-dimensional fixed-point
theorem. The new bridge is a common nonpositive line for commuting isometries
of a completed index-one space.

Searches for invariant nonpositive lines, positive character hyperplanes,
and commuting indefinite isometries found no corresponding corpus theorem.
Existing finite-rank repairs do not make the repairing functional a character.

## Paper proof

If the kernel is positive definite, choose the trivial character. Otherwise
its column space `V` has a nondegenerate Hermitian form `B` of index one.
Choose `e` with `B(e,e) = -1` and put `W = e⊥`. The restriction of `B` to `W`
is positive semidefinite: a negative vector there and `e` would give two
negative squares. It is definite: a zero-norm vector is orthogonal to `W`
by Cauchy–Schwarz and to `e` by definition, hence is zero by nondegeneracy.
Thus `V = W ⊕ ℂe`, with

`B((x,a),(y,b)) = ⟪x,y⟫ - conjugate(a)b`.

Complete `W` to a Hilbert space `H`. Every translation extends to a bounded
invertible operator on `H ⊕ ℂ`, preserving `B`. Indeed, writing the Hilbert
norm associated to this splitting as `‖·‖J`,

`‖Tv‖J² = B(v,v) + 2|B(e,Tv)|²`
`         ≤ (1 + 2‖T⁻¹e‖J²) ‖v‖J²`.

The same bound applies to the inverse. Preservation of `B`, inverses, and
commutation extend by density. The orbit of the column at the identity
still has dense linear span.

Represent every nonpositive line uniquely by `(z,1)` with `‖z‖ ≤ 1`.
A `B`-isometry induces a fractional linear self-map of this closed ball.
Its denominator cannot vanish: the image would have last coordinate zero
and nonpositive square, forcing it to be zero, contrary to invertibility.
The map is weakly continuous, since bounded linear maps and linear
functionals are weakly continuous. The ball is weakly compact.

We use the following fixed-point consequence of Brouwer. Every continuous
self-map of a nonempty compact convex subset of a locally convex space has
a fixed point. To derive it, embed the space by its separating continuous
linear functionals into a product of scalar spaces. If there is no fixed
point, compactness gives finitely many coordinates whose total displacement
has positive minimum `δ`. Cover the compact set by finitely many balls of
radius `δ` for the sum of distances in these coordinates. The normalized
weights `max(0, δ - distance)` give a continuous convex-combination map
approximating the original map by less than `δ` in those coordinates.
Brouwer on the finite coefficient simplex gives a fixed point of this
approximation, contradicting the minimum displacement. The simplex is a
continuous retract of its ambient finite-dimensional real space: first
shift all coordinates equally so their sum is one, take positive parts,
then normalize their sum. The latter sum is at least one.

Apply this fixed-point theorem to obtain a nonpositive eigenline for each
translation. If some translation has such an eigenvalue `λ` with `|λ| ≠ 1`,
its whole `λ`-eigenspace is totally isotropic, since preservation gives
`B(v,w) = |λ|² B(v,w)`. A totally isotropic subspace of `H ⊕ ℂ` has dimension
at most one: its last-coordinate map is injective. Every commuting
translation therefore preserves that eigenline.

Otherwise all eigenvalues on nonpositive lines are unitary. Two distinct
normalized nonpositive vectors `(z,1)` and `(w,1)` have nonzero pairing:
`⟪z,w⟫ = 1` and `‖z‖, ‖w‖ ≤ 1` force `z = w`. Thus two fixed lines of one
translation have eigenvalues satisfying `conjugate(λ)μ = 1`, hence the same
eigenvalue. Its projective fixed set is consequently the intersection of
the ball with an affine eigenspace, so is convex and weakly closed.
Commuting projective maps preserve each other's fixed sets. Successive
applications of the fixed-point theorem show that every finite intersection
is nonempty. Weak compactness supplies a common fixed line `ℂw`.

Write `Tg w = α(g)w`. Invertibility and the representation law make `α` a
character. Set `χ(g)=conjugate(α(g))⁻¹`. The functional `L(v)=B(w,v)`
satisfies `L(Tg v)=χ(g)L(v)` by form invariance. For the identity column
`v₀`, therefore,

`L(Σᵢ cᵢ Txi v₀) = L(v₀) Σᵢ cᵢ χ(xᵢ)`.

Thus zero character mass forces orthogonality to `w`, without division.
Finally `w⊥` is positive semidefinite.
For `w = (u,a)` nonzero and nonpositive, `a ≠ 0` and `‖u‖ ≤ |a|`;
orthogonality of `(x,b)` gives `|b| ≤ ‖x‖` by Cauchy–Schwarz. Thus every
finite column combination of zero `χ`-mass has nonnegative square, as
claimed.

For the converse, a negative-definite subspace of any finite Gram form
intersects the kernel of a nonnegative hyperplane only at zero. The defining
scalar functional is therefore injective on that subspace, whose dimension
is at most one. Taking the supremum over Gram forms gives index at most one.

## Lean verification

HKT `Index/PositiveCharacterHyperplane.lean`:
- `exists_positive_character_hyperplane_of_negIndex_le_one`
- `negIndex_le_one_iff_positive_character_hyperplane`

Direct `lake --old env lean` check passed. Both transitive axiom audits
contain exactly `propext`, `Classical.choice`, and `Quot.sound`. Ten supporting
modules pass Lean; required oleans exist. HTGeometry and HKT umbrellas are
wired. No common-line, completion, growth, or countability assumption remains.

Final novelty searches found arbitrary finite-rank repairs, forward index
bounds, and special conditionally positive kernels; none supplied this
character for an arbitrary index-one abelian kernel. Search records:
`/tmp/hgt-index-one-hyperplane-final-novelty.json`,
`/tmp/hgt-index-one-conditional-final-novelty.json`,
`/tmp/hgt-akg-index-one-character-audit.json`.

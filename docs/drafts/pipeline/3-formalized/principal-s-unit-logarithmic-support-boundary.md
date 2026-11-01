# Principal S-unit logarithmic support boundary

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [three approaches, C](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

Let `S,T` be finite prime sets. For a resolution function `n:T→ℕ`, let
`U(S;T,n)` consist of positive rational `S`-units satisfying
`|u|ₚ=1` and `|u−1|ₚ<(n(p)+1)⁻¹` at every `p∈T`.
Put `F=S\T`.

1. `U(S;T,n)=U(F;T,n)` exactly.
2. If `F=∅`, the group is trivial.
3. If `F={q}`, its logarithms are exactly `d log(q)·ℤ` for some integer `d>0`.
4. Its logarithms are dense in `ℝ` iff `|F|≥2`.
5. On the dense side, restriction preserves the full negative and mass-zero
   Weil indices. Every global correlation value lies in the closure of the
   restricted values. One fixed positive oscillation works simultaneously
   for every `S,T,n` with at least two free primes.

This settles simultaneous finite-place restrictions with prescribed prime
support. It does not identify logarithmic density with index preservation
in the one-prime case: a discrete tower can still detect the whole finite
zero stratum.

## Dependency-closed paper proof

**Support deletion.** For a nonzero rational, `|u|ₚ=p^(−vₚ(u))`. As `p>1`,
unit norm forces `vₚ(u)=0`. Thus every valuation coordinate in `S∩T`
vanishes. Conversely, reducing allowed support changes none of the principal
congruences. Unique factorization reconstructs each positive rational from
its finitely supported valuation vector.

**Common powers.** Choose `kₚ` such that
`p^(−kₚ)<(n(p)+1)⁻¹`. Every free prime `q∈F` is coprime to `p`, so Euler's
congruence gives `q^φ(p^kₚ)≡1 mod p^kₚ`. Take the product `M` of these
positive totients over `T`; an empty product is one. Every generator `q^M`
lies in every prescribed principal subgroup. Closure under products and
integer powers therefore places the entire `M`th-power subgroup of positive
`F`-units inside `U(F;T,n)`.

**Logarithmic classification.** With no free prime, unique factorization
gives only one. With one free prime `q`, every logarithm lies in
`log(q)·ℤ`, and the common-power construction supplies the nonzero logarithm
`M log(q)`. A subgroup of this discrete cyclic group is exactly
`d log(q)·ℤ` for a positive integer `d`.

With distinct free primes `q,r`, irrationality of `log(q)/log(r)` makes
`ℤ log(q)+ℤ log(r)` dense. Multiplication by the positive integer `M`
preserves density and lands inside the prescribed group. Conversely, a
subgroup supported on at most one prime is contained in a discrete real
cyclic subgroup and cannot be dense. These alternatives prove the exact
cardinality criterion.

**Index and values.** Apply the established dense-logarithm mass-zero
index theorem to the concrete subgroup. Its polar index is the full global
negative index; the ordinary restriction inequality and the polar lower
bound give equality for the ordinary index too. Continuity of the real
scale profile makes each global correlation value approximable.

The corpus supplies a slope `v` with `K(v)≠K(1)`. Choose
`ε=|K(v)−K(1)|/2>0`. Approximate `K(v)` within `ε` in each group above.
The triangle inequality forces oscillation at least `ε`, uniformly across
all finite supports, selected places, and depths retaining two free primes.

## Lean certificate

Module: `AdelicKreinGeometry/PrincipalSUnitLogarithmicBoundary.lean`.
Namespace: `GaloisForLFunctions.AdelicKreinGeometry.PrincipalSUnits`.

- `delete_local_support`.
- `common_supported_power`.
- `group_eq_bot_of_no_free_primes`.
- `cyclic_logGroup_of_one_free_prime`.
- `dense_logGroup_iff`.
- `polarIndex_full`, `negIndex_full`.
- `correlation_near`, `uniform_correlation_oscillation`.

Direct production check and all five transitive axiom audits pass. Dependencies
are exactly `propext`, `Classical.choice`, `Quot.sound`. The umbrella import is wired.

## Boundary

Finite congruences away from two remaining prime directions do not reduce
Weil's global index or remove correlation oscillation. Constraining every
allowed prime to be a local unit instead collapses the positive slope group.
Neither statement supplies a two-place RH proof or a local Fourier-support
model for the actual correlation. Finite intersections here are not being
identified with neighborhoods in the finite-idèle topology.

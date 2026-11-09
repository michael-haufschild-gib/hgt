# Simultaneous logarithm bounds with rank in the exponent

- **ID:** CDG-SIM
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Goal:** A proved collective small-form estimate beyond maximal-minor
  reduction to a scalar Baker bound.

## External benchmark

For distinct primes `p_j≤y`, an integer `r×k` matrix of rank `r`, and
`|a_ij|≤H`, put `L_i=Σ_j a_ij log p_j`, where `H≥1`, `1≤r≤k`.
Theorem 1.1 of [Gaudron (2014), pp. 2–3](https://lmbp.uca.fr/~gaudron/art12.pdf)
specializes to

`max_i |L_i| ≥ exp(−G)`,

`G=(10k)^(58k²/r) A^(1/r) (max(1,log H)+A) (1+e log y)^(k/r)`,

`A=floor(log(e+1+ek log y))+1`.

Here the number field is `ℚ`, the theorem's exponential parameter is `e`,
`log a=e log y`, and `log b=max(1,log H)`.
Unique factorization supplies independence of the prime logarithms.
This is an external theorem, not a new result or a Lean dependency.
The 2012 arXiv text has different constants; the formula above uses the
published version.

## Why this comparison matters

At proportional rank `r≈k/2`, the published dimension factor is
`exp(O(k log k))`. The current Cramer reduction uses a scalar Baker
exponent in about `k/2` logarithms, with dimension dependence
`exp(O(k² log(k log y)))`. Thus scalar slicing does not exhaust the
available collective arithmetic. Near full rank the existing elementary
determinant bound, or the two-logarithm reduction, can instead be stronger.
Any replacement must retain these regimes.

## Proof gap

The corpus's Fel'dman argument handles one form. Replacing its pivot by
several pivots does not prove a simultaneous estimate: the auxiliary-section
dimension, multiplicity estimate, and small-values construction must all
retain the rank gain. Gaudron's proof supplies these through approximate
Siegel theory and multiplicity estimates on an additive group times a torus.
No version of that input is assumed here.

## Rational-coefficient construction to test

Choose a largest absolute `r×r` column minor `B`, put `D=det B`, and
write the remaining columns as `C`. For an exponent vector `(u,v)` in
`[0,q)^r×[0,q)^(k−r)`, use the integral free coordinates

`γ(u,v)=D v−u adj(B) C`.

The perturbed frequency is `Σ_j (γ_j/D) log p_j`, over free coordinates.
Its difference from the true frequency is `u B⁻¹ L`.
Maximality of the minor bounds each entry of `B⁻¹C` by one; the error
still pays the explicit adjugate bound against `max_i|L_i|`.

Fel'dman's polynomial jets can then use `k−r` free directions and one
polynomial direction. The proposed Siegel system has
`X₀ S^(k−r+1)` equations and `(N+1)q^k` unknowns. Its entries are integers,
so the existing integer Siegel lemma applies directly; an approximate
Siegel lemma is not automatically necessary in this rational specialization.
The corpus's `Matveev/FeldmanSiegelSystem.lean` and
`Matveev/FeldmanAuxiliaryBounds.lean` give the one-pivot construction.

## Collective normalization and parameter closure

`CollectiveAuxiliaryConstruction.lean` proves the bounded projection and
exact frequency defect. The same pivot determinant clears every free jet.
The companion retains all original prime frequencies, so a nonzero
coefficient vector has a nonzero value before `(N+1)q^k`.

Put `d=k−r`, `h=floor(d/r)+1`, and `E=1000Wk(R+1)`. The parameters

`q=E^h(R+1)`, `M=1000Wkq`, `S=RM+1`,
`c=16k²(R+1)q`, `a=2cE^h`

satisfy the Siegel count, analytic growth inequality, and terminal count
provided `4(1000Wk)^(h(k+1))(R+1)^(h(k+1)+k)≤2^R`.
An explicit binary-logarithmic `R` satisfies this inequality. The polynomial
degree is `h(k+1)+k≤3k+2` when `r≥d`; it is quadratic at rank one.
These exact arithmetic statements are proved in Lean, not assumed as
parameter fields. They do not establish the analytic bounds for the new
auxiliary family.

The bounded-height integer-kernel construction is also formalized:
`exists_collective_auxiliary` gives exact initial vanishing and a nonzero
true value before the full interpolation length. Its proof and scope are
in [CDG-AUX](../3-formalized/cdg-collective-auxiliary.md).

Analytic extrapolation remains. The growth and error majorants can use
the enlarged box parameter `Q=kq`, since `(r+1)q≤2kq` and `d≤k−1`.
The integer system and terminal count must retain the actual `q`.
The scalar `FeldmanParams` structure imposes the wrong Siegel count here;
its parameter-free growth and error inequalities are the reusable inputs.
Only the closed logarithm argument can advance this card to stage 2.

## Scope

This addresses collective small forms and the rank profile. Even the
published bound does not by itself prove early-return exclusion: a form
acts on a return through its total coefficient height times phase error.
The constant-precision breadth mechanism remains a separate open problem.

# Descent of the global width square class

- **ID:** galois-zero-width-squareclass-descent
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/fable.md`, §§10.5(2–3).
- **Statement:** Characterize splitting of the central width involution by descent of its square class to the source field.

## Objects and target

Let `K` be the complete-fibre source field, `F=K(all δ_q)` the signed-width
field, and `E=K(all δ_qδ_r)`. Both are normal over `K`. For a nonzero anchor
`δ₀`, put `d=δ₀²∈E×`; the established presentation is `F=E(δ₀)`.

First construct an anchor-independent class `[d]∈E×/(E×)²` and prove it
fixed by `Gal(E/K)`, with square witnesses from the actual width action.
Its triviality is exactly `F=E`.

In the nontrivial case, establish the equivalence

```
Gal(F/K) → Gal(E/K) has a continuous group section
  ⇔ [d] comes from K×/(K×)²
  ⇔ ∃ a∈K×, u∈E×, d=a u².
```

This concerns the full infinite source fields and their Krull topologies.
The all-zero-width case belongs to the already formalized trivial-width
regime; no off-line zero is presumed to exist.

## Approach

For nonzero widths, `δ_q/δ₀=(δ_qδ₀)/δ₀²∈E`. This supplies the square
witness comparing anchors. Extend an automorphism of `E/K` to `F/K` by
normality and use its action on complete source width fibres to obtain
the invariance witness.

If `d=a u²`, put `b=δ₀/u`. Then `b²=a∈K` and `F=E(b)`, with `b∉E`.
The subgroup fixing `b` restricts bijectively to `Gal(E/K)`: extend an
`E`-automorphism to `F`, then adjust its sign on `b` by the quadratic kernel.
The root presentation gives uniqueness. This subgroup is closed and compact;
its continuous restriction bijection to the Hausdorff Galois group is a
homeomorphism, giving a continuous section without assuming continuity of
a chosen algebraic extension.

Conversely let `H` be the image of a continuous section. It is closed by
compactness. The central quadratic kernel `N` gives `G=NH` and `N∩H=1`,
so `H` is normal of index two. Infinite Galois correspondence should give
`D=F^H` quadratic over `K`, with `DE=F` and `D∩E=K`. Choose `b∈D` with
`D=K(b)` and `b²=a∈K×`. In the basis `1,δ₀` over `E`, the condition
`b²∈E` and `b∉E` forces `b` onto the `Eδ₀` line. Thus `δ₀/b∈E×`,
which is the required square witness. Formalizing the infinite correspondence,
finite-index step and quadratic generator remains necessary.

## Arithmetic question

Determine whether complete-fibre prime-source coefficients constrain this
descent class. Centrality alone must not be substituted for a splitting:
a central quadratic extension of groups need not split. Any obstruction
must retain the square-class criterion and its exact field interpretation.

## Status

The field presentations, normality, complete source width equations, and
centrality are formalized. The square-class object, descent equivalence,
and any decision about the actual class remain unproved in Lean.

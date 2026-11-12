# Rational weights and reflection-orbit rigidity

- **ID:** galois-zero-rational-orbit-rigidity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Questions:** Arithmetic action on zero relations; pointwise orbit separation; functional-reflection obstruction.

## Target

Extend the proved action of `Gal(E/B)` on actual zeros to an additive action
on their full integral span `Δ`, transporting every prime character. It must
fix `Δ∩ℚ` pointwise. Deduce that the rational prime spectral field is contained
in the concrete mixed-trace ground field `B`.

Prove that every arithmetic image of a rational-real-part zero is either
that zero or its complex conjugate. Thus rational real parts are preserved
and critical-line membership is invariant under the entire arithmetic group.
In particular, prove

`1−ρ lies in the arithmetic orbit of ρ  ⇔  Re ρ=1/2`.

Thus a rational-real-part zero off the critical line has `F_ρ=H_ρ`; a
nontrivial reflection-pair quadratic extension at an off-line zero forces
irrational real part. In particular, a global functional-reflection lift
would force every off-line zero to have irrational real part. Combine this
with the proved prime-relation rigidity: its algebraic prime-relation rank
is then at most one, and two algebraic prime values are excluded there.

## Paper mechanism

All prime characters of an integral zero relation are products of the
original prime values. Applying an arithmetic automorphism preserves those
products. Two-prime injectivity preserves the relation itself, producing the
additive action on `Δ`. The unit weight is fixed, and clearing denominators
fixes every rational weight. Infinite Galois fixed-field duality places its
prime values in `B`.

Write `q=ρ+conjugate(ρ)=2 Re ρ∈ℚ`. If an arithmetic automorphism `σ` sends
`ρ` to `1−ρ`, then the additive action of `g=σc` sends `ρ` to `ρ+q−1` and
fixes `q−1`. Its iterates are `ρ+n(q−1)`, all actual zeros. Bounded real parts
of actual zeros force `q=1`. Conversely, a critical zero is sent to its
functional reflection by ordinary conjugation.

This applies pointwise to every actual zero, with no terminal height. The
existing residue-field orbit criterion converts it into the field and degree
statements above.

Each off-line prime reflection difference is nonzero: equality of its two
prime values would force equality of their norms and hence `Re ρ=1/2`.
For rational off-line `ρ`, the equality `F_ρ=H_ρ` places that difference
in `H_ρ`, so its discriminant is already a square in the global pair field.
One such index gives a singleton odd square relation, explicitly obstructing
the uniform reflection lift.

## Stronger orbit rigidity

Fix `ρ=β+it` with rational `β` and let `q=2β`. For any arithmetic
automorphism `σ`, its inverse image `ζ=σ⁻¹ρ` has ordinate `±t`, so
`conjugate(ζ)=ζ∓(2ρ−q)`. Applying `σ` shows that `σcσ⁻¹ρ` has horizontal
displacement from `β` equal to `∓2(Re σρ−β)`. The bounded set
`{|Re σρ−β| : σ∈Gal(E/B)}` is therefore closed under doubling; its
supremum forces every displacement to vanish. Absolute-height preservation
then leaves only `ρ` and `conjugate(ρ)`. Applying this to the inverse action
proves critical-line invariance in both directions.

This uses the whole arithmetic group and the uniform critical strip. No
finite orbit truncation, continuity of the arithmetic action on `ℂ`, or
centrality of conjugation is assumed. The reflection-pair field is therefore
exactly `B` at critical zeros, and only there: every automorphism fixes
its symmetric generators; conversely the ground field is real and the
proved pair-field reality criterion forces the line.

## Boundary

The paper argument is complete; Lean verification is in progress. Rationality
of real parts of actual zeros is not assumed globally. Neither existence of
a functional-reflection lift nor purity is asserted.

The additive action also supplies the character-module input for an eventual
arithmetic descent of the full zero motive over `B`; constructing that descended
infinite object is a separate task.

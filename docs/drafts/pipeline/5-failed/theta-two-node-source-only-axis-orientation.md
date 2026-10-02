# RN-P-7f: source-only single-axis orientation is false

Status: formalized and audited, including the positive survivor. This retires a source-only extension
of the simultaneous-zero argument, not the actual Schur barrier RN-P-7e.

Let `k` be the actual theta source, `p=-(log k)'`, and `0≤x₁<x₂<y`.
For arbitrary coefficients define the source ports `A,B` and free
derivatives `W,C` as in RN-P-7e. Put `h=x₂-x₁`,

    s=(p₂-p₁)/h, j=(x₁p₂-x₂p₁)/h,
    t=(x₂p₂-x₁p₁)/h, r=x₁x₂s,
    a=(x₂-y)/h, b=(y-x₁)/h,
    E=p(y)-a p₁-b p₂,
    F=y p(y)-a x₁p₁-b x₂p₂.

The exact source equations are

    W=jA-sB-k(y)E,
    C=rA-tB-k(y)F.

The existing actual-source convexity theorem proves `E,F>0`; strict log
concavity proves `s>0`; strict increase of `p(x)/x` proves `j>0` when
`x₁>0`. Consequently:

1. On `A=0,B≥0`, always `W<0`.
2. If `x₁=0`, on `B=0` both free derivatives are negative, regardless of A.
3. If `x₁>0`, there are coefficients with `A>0,B=0,W>0,C>0`.

For (3), choose `T=k(y)E/j+k(y)F/r+1>0`, and

    c₁=((x₂-y)k(y)-x₂T)/(h k(x₁)),
    c₂=((y-x₁)k(y)+x₁T)/(h k(x₂)).

They give `A=T,B=0` exactly, and the two affine identities prove both
positive free derivatives. This is a symbolic construction for every
strictly positive ordered triple, without numerical evaluation.

Positive survivor: the two exact affine laws classify the source terms
on both axes and distinguish the rigid center-anchored case from positive
anchor sign flexibility. Formalize these laws and their sign consequences.

Essential scope boundary: the counterexample coefficients are not asserted
to satisfy `Mc=h`. Thus it does not refute the actual Schur barrier. For
actual projection coefficients the missing inequalities become exactly

    (α-s)B < k(y)E at A=0,B>0,
    (1+γ+r)A < k(y)F at B=0,A>0.

This explains why further source-jet signs alone cannot replace the
projection equations. The next attack must prove these actual projection
comparisons, not merely negativity of the free terms.

Corpus basis: `ThetaTwoNodePortTransversality` supplies both strict
extrapolation signs; `ThetaTailTwoPointPositivity` supplies strict increase
of `p(x)/x`; `ThetaTiltLogDensity` supplies strict log concavity. Current
Schur searches were partial/source-only or had no applicable exact hits.

Lean: `ThetaTwoNodePortBoundaryClassification.lean`, namespace
`RHTower.ThetaPortBoundary`. The eight public theorems include both affine
laws, their source signs, `freeSource_neg_on_source_axis`,
`center_free_derivatives_neg`, and the constructive capstone
`exists_positive_anchor_reversed_free_derivatives`.
Targeted `lake --old build`, umbrella wiring and final
`lake env lean GaloisForLFunctions/RHTower/ThetaTwoNodePortBoundaryClassification.lean`
passed. All eight axiom audits list only `propext`, `Classical.choice`,
`Quot.sound`. Repository lint reports ten unrelated unwired leaves,
none from this result.

# Actual rough modulus and exact nodal energy

## Statement

For every physical L² velocity q and c∈ℝ, write F(t)=∫₀ᵗq and G(t)=c+F(t).
There is a constructed physical L² velocity m such that, pointwise for every t,

    |c| + primitive m t = |G(t)|,
    m(t)=sign(G(t))q(t) almost everywhere,
    ∫ₐᵇm(t)²dt=∫ₐᵇq(t)²dt for every a,b.

Thus f(x)=G(exp x) has modulus represented by actual inputs (m,|c|).
For every constructed mixed edge measure D (energies possibly infinite),

    jumpEnergy D q = jumpEnergy D m + nodalEnergy D q c.

For the compact-source mixture, all these energies are finite, and
sourceMass ψ m |c| = sourceMass ψ q c. Additive energy is unchanged while
the exact nonlocal energy decrease is opposite-sign pairing.

## Dependency-closed paper proof

F is locally absolutely continuous and F'=q a.e., by the existing constructed
L² primitive theorem. G is locally absolutely continuous. The inequality
`||G(b)|−|G(a)||≤|G(b)−G(a)|` shows directly from the disjoint-interval
definition that |G| is locally absolutely continuous. Applying the a.e.
differentiability theorem on [-n,n] and taking a countable intersection gives
differentiability of |G| almost everywhere on ℝ.

Fix a point where G'=q and |G| is differentiable. If G is positive, the derivative
of |G| is q; if negative, it is −q. If G=0, |G| and |G|+G are nonnegative
functions attaining their minimum zero at that point. Fermat's theorem says
both derivatives vanish. Subtraction gives q=0. Thus the zero-level law is
proved and `(|G|')²=q²` a.e.; also |G|'=sign(G)q a.e.

The derivative of a real function is measurable. Its a.e. absolute value equals
|q|, so |G|' belongs to L². Define m as its actual L² equivalence class. The
fundamental theorem for absolutely continuous functions gives
`∫₀ᵗm=|G(t)|−|G(0)|=|G(t)|−|c|`, including negative t. A.e. equality of
squares gives every oriented local-energy identity. Substitution t=exp x gives
the exact logarithmic modulus representative. The existing exponential energy
transport consequently preserves the weighted logarithmic Dirichlet integral.

For real a,b, expansion by their signs gives

    (b−a)²=(|b|−|a|)²+4(max(b,0)max(−a,0)+max(−b,0)max(a,0)).

Set a=f(u), b=f(u+h). The first squared difference is the jump of q; the
modulus identity identifies the second with the jump of m. Every term is
nonnegative and measurable. Nonnegative integration gives the exact identity
for the full diffuse/countable-atom mixed measure, even at infinite energy.
Compact-source admission makes the identities finite for that graph. The
pointwise equality |f|²=f² gives source-mass equality.

The same local-energy equality fixes every resistance path budget. Therefore
the exact local slack identity transfers the nodal loss from jump energy into
slack: `slack(m,e)=slack(q,e)+nodal(q,c,e)`. Integration gives the corresponding
extended slack identity. This identifies how the additive path budget is
redistributed under modulus, rather than merely bounding the contracted jump.

## Significance and boundary

This closes nonlinear domain realization for the actual rough states: the
algebraic nodal identity now acts within constructed L² primitives. Singular
diffuse edges and every arithmetic atom are retained. The result addresses the
nodal mechanism in Pillar VII and Trap 3; it does not supply a full affine
unitary action, a closed-form operator identification, or a new general Sobolev
chain rule. Those classical ingredients are not claimed as externally novel.

[Sobolev lecture notes, §4.1.2–4.1.3](https://www.math.stonybrook.edu/~joa/PUBLICATIONS/SOBOLEV.pdf)
give background on the absolute-value weak derivative, absolute-continuity
characterization and the Cantor-function obstruction. The proof above uses the
actual local primitives and proves the needed modulus/zero-level claims directly.

## Lean certificate

`RoughSobolevModulus.lean` constructs the physical modulus velocity and proves
the zero-level, primitive and energy laws (14 public theorems, 2 definitions).
`RoughModulusGraphDecomposition.lean` proves the exact edge/full-measure jump,
slack, congestion and compact-source consequences (11 public theorems).
Both final serial direct checks passed without diagnostics. All 27 public
declarations use only `propext`, `Classical.choice`, `Quot.sound`; the main
signatures have no analytic admission or chain-rule assumptions. Both imports
are wired, all theorem names indexed, and whitespace check passed.

Global lint reports four unrelated concurrent modules missing umbrella imports;
neither leaf is implicated. Exact certificates and limitations are recorded in
`ContinuumCoprimeShear-FACTS.md`. This is one connected contribution, package 6
of the active 100-package goal.

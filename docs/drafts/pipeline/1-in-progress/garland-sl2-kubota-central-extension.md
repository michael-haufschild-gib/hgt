# Rank-one loop central extension by the Kubota cocycle

- **Stage:** 1-in-progress
- **Type:** BRIDGE / known mathematics
- **Parent:** [Garland loop Eisenstein series](garland-loop-eisenstein-over-q.md)
- **Target:** Construct a central extension of `SL₂(F((t)))` by `Fˣ` using the
  inverse tame-symbol class, with no assumed cocycle identity or injectivity input.

## Dependency and literature audit

The corpus proves rank-four Steinberg-kernel centrality, but its inspected
Milnor-to-Steinberg map is only proved surjective. That map does not yet give
the homomorphism from the Steinberg kernel required for a tame-symbol pushout.
The direct rank-one cocycle avoids this missing inverse.

Primary references: Dongwen Liu, *Eisenstein Series on Loop Groups*, §3.1,
<https://arxiv.org/abs/1103.4212>; Peter McNamara, *Principal Series
Representations of Metaplectic Groups over Local Fields*, formula (3.2),
<https://petermc.net/maths/papers/pcrepssep10.pdf>. The following argument proves
the cocycle directly in Milnor `K₂`, so it does not import their extension theorem
or impose local-field/Hilbert-symbol hypotheses.

## Dependency-closed paper proof

For `g∈SL₂(K)`, put `x(g)=g₂₁` if this is nonzero, and `x(g)=g₂₂` otherwise.
The determinant-one identity proves `x(g)≠0`. In additive Milnor `K₂(K)`, define

`C(g,h) = {x(gh)/x(g), x(gh)/x(h)}`.

All symbols have nonzero arguments. `C(1,g)=C(g,1)=0`. For any six units
`a,b,c,d,e,f`, bilinearity and antisymmetry give the exact identity

`{d/a,d/b}+{f/d,f/c}-{f/a,f/e}-{e/b,e/c}
 = {ac/(de),bf/(de)}`.

To verify it, expand both slots in every symbol. Antisymmetry cancels each
off-diagonal pair; the remaining discrepancy is twice `{e,e}`, which vanishes
by antisymmetry. This is an identity in the already constructed Milnor group,
not an asserted relation on a proposed group extension.

Take `a=x(g), b=x(h), c=x(k), d=x(gh), e=x(hk), f=x(ghk)`, and write
`R=ac/(de)`, `S=bf/(de)`. The cocycle defect is `{R,S}`. Its vanishing follows
from the following exhaustive cases, in the stated order:

1. `g₂₁=0`: multiplication gives `d=ab`, `f=ae`; hence `S=1`.
2. `h₂₁=0` with `g₂₁≠0`: `d=a/b`, `e=bc`; hence `R=1`.
3. `(gh)₂₁=0` with both preceding entries nonzero: determinant one gives
   `d=-a/b`; the first case applied to `gh` gives `f=dc`. Thus `S=-R`.
4. `k₂₁=0` with `(gh)₂₁≠0`: `e=b/c`, `f=d/c`; hence `S=1`.
5. `(hk)₂₁=0` with `h₂₁,k₂₁≠0`: `e=-b/c` and `f=a/e`; hence `S=-R`.
6. All five entries above are nonzero, but `(ghk)₂₁=0`: the matrix identity
   `(gh)₂₁(hk)₂₁=g₂₁k₂₁+h₂₁(ghk)₂₁` gives `de=ac`, so `R=1`.
7. All six entries are nonzero: the same matrix identity gives `de=ac+bf`;
   hence `R+S=1`.

The symbols in these cases vanish respectively by the unit identity, the unit
identity, `{u,-u}=0`, the unit identity, `{u,-u}=0`, the unit identity, and the
Steinberg relation. This proves
`C(g,h)+C(gh,k)=C(g,hk)+C(h,k)` without a case left over.

Let `K=F((t))`. The corpus constructs its integer-valued valuation, identifies
its residue field with `F`, and constructs the tame homomorphism on Milnor `K₂`
from any such actual valuation. Compose to obtain `T:K₂(K)→Fˣ`. On
`SL₂(K)×Fˣ`, define

`(g,u)(h,v)=(gh,uv T(C(g,h)))`.

The proved cocycle identity gives associativity. Identity is `(1,1)` and inverse
is `(g⁻¹,u⁻¹ T(C(g,g⁻¹))⁻¹)`; the cocycle at `(g,g⁻¹,g)` makes left and right
inverse formulas agree. Projection is onto `SL₂(K)`; its kernel is exactly
`{(1,u)}` and this copy of `Fˣ` is injective and central. For diagonal matrices
`diag(a,a⁻¹), diag(b,b⁻¹)`, the cocycle is `{b,a}=-{a,b}`, so the torus section
defect is the inverse tame symbol, matching the stated loop normalization.

For the upper unipotent matrices `u(s)`, `x(u(s))=1`, so the section is an
additive homomorphism. For lower unipotents `l(s)`, zero parameters are handled
by normalization. If `s,t,s+t` are nonzero, the symbol is
`{(s+t)/s,(s+t)/t}={s/(s+t),t/(s+t)}=0`: invert both slots and apply Steinberg.
If `s+t=0`, it is `{s⁻¹,-s⁻¹}=0`. Thus both actual root groups split.
For a constant unit `a∈Fˣ` and the Laurent uniformizer `X`, the valuation and
residue formulas give `T{a,X}=a`. The diagonal section therefore has central
commutator `a⁻²` at `diag(a,a⁻¹)` and `diag(X,X⁻¹)`. This also tests the
central-extension orientation against the loop-root normalization.

## Exact status

Paper argument complete; Lean construction in progress. No statement here counts
as formally established until its declaration and transitive axiom audit exist.
This extension alone does not construct Iwasawa coordinates, the arithmetic
Eisenstein series, its convergence, or its constant-term integral.

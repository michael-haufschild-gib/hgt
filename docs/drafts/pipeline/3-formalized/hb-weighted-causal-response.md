# HB: weighted admission of the original causal response

Status: formalized in nine individually audited leaves and 52 new public
theorems. RH remains open. Frontier map is read-only.

Chain: theta cusp → Xi occurrence → complete native source → original
outgoing response and physical adjoint residue → independent Hawking-clock
extinction → RH.

## Original domain and bounded cusp tests

The response is the existing `jointWaveResponse`, in the closure of the
literal radial/modular differential graph. Its four components are the
field, radial derivative, and two angular derivatives multiplied by the
original radial factor `sech(t)`. The proof constructs multiplication on
this domain; it does not assume a new domain or replace its operator.

Let `eta(y)=smoothTransition(y-2)`. Compactness supplies a nonnegative
bound `B` for `|eta'|` on `[2,3]`. Define

```text
K = 18 B + 1,
p_N(y) = N y/(N+y),                   N > 0,
m_N(y) = K + eta(y) p_N(y),
m(y) = K + eta(y) y.
```

Each bounded multiplier is constant below height two. Its cell-germ
extension is smooth and modular invariant, and agrees with the complete
original profile germ on the closed fundamental domain, including seams.
It satisfies `K <= m_N <= K+N`, `m_N <= m`, and `y <= 3m`.

The uniform derivative estimate is `|y m_N'(y)| <= (3/2)m_N(y)`.
On `[2,3]`, the cutoff-derivative contribution has size at most `9B`;
outside that interval it vanishes. The remaining contribution is bounded
by `eta(y)p_N(y)`. The horizontal derivative vanishes on the closed cell.

Let `M_N` be the resulting bounded spatial multiplier and let `R_N` be
multiplication by `sech(t) (y m_N'/m_N)` on the fundamental domain. Both
are real and self-adjoint, commute, and `||R_N v|| <= (3/2)||v||`.
The exact product rule on the smooth modular core extends by continuity
to the actual closed graph:

```text
W_N(u_0,u_1,u_2,u_3)
  = (M_N u_0, M_N u_1, M_N u_2, M_N u_3 + R_N M_N u_0).
```

Thus `W_N^2 u` is a legitimate test of the original weak equation.

## Full complex energy and frequency range

Write `v=M_N J u`, `r=R_N v`, and `d=(W_N u)_3`. The proved complex identity is

```text
<W_N^2 u,u> = <W_N u,W_N u> - <r,r> + <r,d> - <d,r>.
```

The last two terms are retained. Taking only the real part gives a valid
bound when `Re(w^2)>9/4`, but this restricts imaginary frequency and does
not cover the full source corridor. Rotation by the actual `conj(w)`
removes that restriction. With `a=Re(w)`, `b=Im(w)`, `S=a^2+b^2`, the
original wave equation gives

```text
a ||W_N u||^2 + a(S-1)||v||^2 - a||r||^2
  + 2b Im<r,d> = Re(conj(w) <v,M_N F>).
```

Use `||W_N u||^2 >= ||v||^2+||d||^2`,
`|Im<r,d>| <= ||r|| ||d||`, and
`(a||d||-|b|||r||)^2 >= 0`. The slope bound then yields

```text
S(a^2-9/4)||v||^2 <= a |w| ||v|| ||M_N F||,
||M_N J u|| <= [a |w| / (S(a^2-9/4))] ||M_N F||,    a > 3/2.
```

There is no restriction on `Im(w)` in this bound. The inverse and forcing
are exactly the existing original ones. The finite real-part estimate is
also retained as an independently proved consequence of the exact energy.

## Removing the truncation and admitting the complete response

For `N=n+1`, the profiles converge pointwise to `m`. Their weighted source
norms are bounded by the norm of `mF`. The uniform response estimate and
Fatou's inequality in the original product measure prove `mJu` is in L2.
Since `y<=3m`, the actual response satisfies `yJu in L2` whenever `yF in L2`
and `Re(w)>3/2`. Conversely, `mF=KF+eta(y)yF` is in L2 for every such
height-admitted source, because `0<=eta<=1`.

`continuedCuspResidualL2_height_memLp` identifies the previous weighted
forcing admission with the representative of the original complete source
class. Consequently `completeCuspResponse_height_memLp` proves admission
of the actual response for every Xi source, both branches, every amplitude,
and every frequency satisfying

```text
Im(w) != 0,     3/2 < Re(w) < 2.
```

No source channel or cutoff derivative is removed. This includes the
original source corridor at real part `7/4` for every nonzero imaginary
part. No response-admission hypothesis is supplied to this source-specific
theorem.

## Literal physical response integral

The existing physical dual is `conj(E_r/y)` in the original angular L2
space. Its radial tensor insertion has bounded adjoint `P_r`. Define the
physical response by applying this same `P_r` to the constructed weighted
class `yJu`. For every radial L2 test `h`, the new proof establishes both
integrability of the original product and the identity

```text
<h, P_r(yJu)> = integral conj(h(t)) E_r(z) Ju(t,z) d(nu x mu).
```

The two height factors cancel exactly. The complete original physical
angular field, original measure, and actual original causal solution are
retained. `physicalCuspResponse_integral` applies the identity directly to
the complete theta-cusp forcing with arbitrary Xi source and target.

## Scope and verification

All nine scratch checks used `lake env lean`; final audits used nine
individual `lake build <module>` targets with cached dependencies. All
52 new public theorem axiom probes report only the standard foundational
axioms `propext`, `Classical.choice`, and `Quot.sound`. No proof debt,
additional axiom, numerical experiment, full build, or umbrella build is
part of this construction. Finished leaves are wired into `RHTower.lean`.

The global static lint gate remains failing on three separate unwired
Fokas--Lenells modules (`FokasLenellsOperatorNormCauchy`,
`FokasLenellsOperatorNormObstruction`, `FokasLenellsOperatorNormRegularity`)
and stale generated indexes. The nine HB leaf audits and their wiring
checks passed; the global gate is not reported as passed.

Modules share prefix `ThetaCuspHawkingBM`: `CuspWeightProfile`,
`ModularCuspWeight`, `CuspWeightCore`, `CuspWeightSpatialMultipliers`,
`CuspWeightGraph`, `CuspWeightEnergy`, `CuspWeightRotatedEnergy`,
`CuspWeightLimit`, and `PhysicalWeightedResponse`.

The outgoing continuation into the QNM region, original endpoint/domain
identification there, physical left resonance and pole residue,
complete-source pole survival, spin-two/AIME reconstruction, and independent
Hawking-clock extinction remain open. A physical response integral on the
proved causal overlap does not establish any of those conclusions or RH.

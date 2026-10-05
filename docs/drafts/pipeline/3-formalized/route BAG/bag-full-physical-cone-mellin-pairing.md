# BAG full physical cone and two-variable Mellin pairing

- **Stage:** 3-formalized

- Route: BAG signed physical cubic.
- Stage: both production leaves and all25 public axiom audits pass.
- Corpus basis: actual physical Fourier Schwartz amplitude; exact rational
  cone HasSum with numerator cofactors; mathlib Schwartz composition and
  Fréchet derivative operators, Fourier inversion and dominated summation.
- No signed cubic saving or RH proof.

## Complete logarithmic profile [PROVED HERE]

For any Schwartz function f on the real plane, with values in any real
normed space, set

    e(u,v)=(exp(-u),exp(-v)),
    G_f(u,v)=exp(-2u-2v)*f(e(u,v)).

The coordinate Euler transforms E_i f=-2f-x_i*partial_i f are Schwartz.
Assemble them into the Schwartz function A_f taking values in continuous
linear maps, A_f(x)(h)=h_0 E_0 f(x)+h_1 E_1 f(x). The chain rule gives the
EXACT Frechet derivative DG_f=G_(A_f). Repeating this argument in the
successive normed operator codomains reduces every derivative estimate to
the zeroth-order estimate; no mixed derivative or quadrant is omitted.

Put S=|u|+|v| and B=1+norm(e(u,v)). Each coordinate satisfies
exp(-2u+|u|)<=B^3: for u>=0 the exponential is at most one; for u<=0 it is
exp(-u)^3, bounded by the cube of B. Hence exp(-2u-2v)*exp(S)<=B^6.
The Schwartz seminorm bounds B^6*norm(f(e(u,v))) uniformly. Also
norm(u,v)<=S and S^k<=k!*exp(S). Their product bounds every polynomially
weighted logarithmic profile. Applying this to A_f and iterating proves
G_f is Schwartz, including both coordinate boundaries and mixed quadrants.

## Two-variable inversion [PROVED HERE]

Let M_f be the FULL two-dimensional Fourier transform of G_f, and use
the normalized vertical coordinates s(t)=2+2*pi*i*t. For x,y>0 define

    K(x,y;t,u)=x^(-s(t))*y^(-s(u)).

Its norm is x^(-2)*y^(-2), independent of t,u. Thus K*M_f is integrable,
since M_f is Schwartz. Fourier inversion at (-log x,-log y), together with
the exact complex-power exponential identity, gives

    f(x,y)=integral_(R^2) K(x,y;t,u)*M_f(t,u) dt du.

Both frequencies remain; no tensor-product approximation is taken. The
definition through the full logarithmic Fourier transform specifies the
normalization without assuming a separate vertical-integrability premise.

## Actual cone restriction and source pairing

The polynomial embedding j(x,y)=(x,y,-x*y) has temperate growth and its
norm bounds the norm of (x,y). Consequently the existing Schwartz
composition theorem makes Phi=(Fourier F) composed with j Schwartz for
every full physical Schwartz amplitude F. This exact restriction passes
production audit. No stationary approximation is used.

For each denominator-supported positive rational pair w, let m(w) be the
complete distinguished cubic mass with both literal label exclusions.
The current rational cone HasSum says that sum_w m(w)x^(-s)y^(-t) equals
the completed Euler/cofactor expression C_S(s,t) in both right half planes.
On the lines Re(s)=Re(t)=2, every summand has the same norm as at (2,2).
That norm sequence is summable. Its product with norm(M_Phi) is therefore
an integrable summable majorant. Dominated summation and the full inversion
formula give

    sum_w m(w)*Phi(w)=integral_(R^2) C_S(s(t),s(u))*M_Phi(t,u) dt du.

The complete physical cone pairing is Lean verified. Arbitrary numerator
cofactors, both label exclusions and the entire Mellin plane remain. The
unconditional actual cutoff family preserves the original negligible
sharp/smooth comparison, all lifted lattice summability and this identity.
The Mellin profile is defined through logarithmic Fourier transform on
real parts (2,2). General vertical lines, a canonical positive-axis integral
identity, holomorphic continuation and contour displacement are not proved.

## Hard obligations still open

This is the exact positive rational cone. It does not discard or bound the
full near-cone/tail region or the other frequency sectors. The proved
negative double residue is nonzero. Its actual physical contribution and
the coupled remainder must yield the signed complex norm o(N/log^2 N).
Growing moments, moving cofactors, common-height self-return and RH remain
open.

## Audit log

PositiveQuadrantLogSchwartz (264 lines,16 public declarations) production71522
and ChiPrimeGaussianCubicConeMellin (195 lines,9 public declarations)
production10862 pass with empty logs using lake --old env lean leaf -o.
Axiom93534 passes all25 with only propext, Classical.choice and Quot.sound.
Index69307 passes; all25 exact API rows and both single umbrella imports
verified. Lint59769 exits1 with28 unrelated unreachable modules, all inspected;
no new-leaf or proof-debt finding. Global lint is not clean. No full build,
new axioms, numerical experiment or resource-limit change.

Corpus searches11570/90276/31282 complete nonpartial with no errors and
inventories65777/65781/65783. Background refresh incomplete; compiler
metadata mostly pending/source-only. All candidates, source arguments,
ingredients and generated ideas inspected. Cap premises were replaced by
the proved all-Schwartz logarithmic theorem. Weighted valuation shifts do
not account for the additive transverse defect zeta+xi*upsilon. Unrelated
uniformizer and already-known squarefree-transfer suggestions were rejected.
The complete local base/tag Fourier identities provide the next arithmetic
source mechanism; no transverse saving follows yet.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.PositiveQuadrantLogSchwartz`, `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicConeMellin`, `GaloisForLFunctions.RHTower.ChiRamanujanRationalCofactors`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean`/`lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the RHTower umbrella; statements re-verified claim by claim against this paper card):
`GaloisForLFunctions.HTGeometry.PositiveQuadrantLogSchwartz`, `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicConeMellin`; base `GaloisForLFunctions.RHTower.ChiRamanujanRationalCofactors`.

| Claim | Declaration |
|-|-|
| `G_f(u,v) = e^{−2u−2v}f(e^{−u},e^{−v})` Schwartz for every Schwartz `f` into any normed space | `quadrantLogSchwartz`, `quadrantLogSchwartz_apply`, `quadrantLogNode`, `quadrantLogNode_apply`, `quadrantLogWeight`, `quadrantLogEuler`, `quadrantLogGradient` |
| two-variable inversion `f(x,y) = ∫ K(x,y;t,u)M_f(t,u)`, `\|K\| = x^{−2}y^{−2}`, integrable | `quadrantMellinLine`, `quadrantMellinProfile`, `quadrantMellinKernel`, `norm_quadrantMellinKernel`, `continuous_quadrantMellinKernel`, `integrable_quadrantMellin_inversion`, `quadrantMellin_inversion` |
| cone restriction `Φ = F̂∘j`, `j(x,y) = (x,y,−xy)`, Schwartz | `bagCubicConeNode`, `bagCubicConeSchwartz`, `bagCubicConeSchwartz_apply`, `bagCubicConeSchwartz_physical` |
| `Σ_w m(w)Φ(w) = ∫ C_S(s(t),s(u))M_Φ(t,u)` | `criticalRationalMass`, `criticalRationalPoint`, `criticalRationalCone_physical_hasSum` |
| actual cutoff family with the pairing | `exists_bagCubicPhysicalConeMellinFamily` |

General vertical lines, contour displacement, the signed cubic and RH are not claimed.

The earlier Lean certificate of this lane is `../bag-full-physical-cone-mellin-pairing.md` (stage 3, flat folder).

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.

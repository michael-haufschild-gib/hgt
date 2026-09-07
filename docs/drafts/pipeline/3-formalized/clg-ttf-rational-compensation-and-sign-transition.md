# CLG/TTF rational compensation and its unique sign transition

- **Stage:** 3-formalized
- **Scope:** Exact bounds on the literal source-selected coefficient; the unique sign transition of its correction; common positive center ends for an explicit coefficient interval.
- **Full chain:** Literal theta source → every signed center-mixed Hankel section nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.
- **Remaining:** Source determinant comparisons beyond the [proved explicit initial interval](clg-ttf-explicit-compact-odd-compensation.md), then positivity at every order. Neither global rank-six positivity nor RH is proved.

## Exact coefficient bounds

Let `Φ` be the complete theta source, `H` its signed odd rank-three reflected determinant, and `Δ>0` its leading odd minor. The canonical coefficient is

`K_*=−H(0)/(Δ(0)Φ(0)²)`.

The existing modular seam closures and the public source-positive coordinate give, with mass `M>0` and squared scale `S`,

`H(0)=M⁶P₁₅(S)`, `Δ(0)=4M⁴P₈(S)`, `Φ(0)=M(S−6)/16`.

Here `P₁₅` is `modularThetaReflectedTenthSeamPolynomial` and `P₈` is `thetaCuspReflectedSixthSeamModularPolynomial`. The source satisfies `191/10<S<20` and `P₈(S)>0`. Cancellation therefore gives

`K_*=−P₁₅(S)/[P₈(S)(S−6)²/64]`.

Set `D(S)=P₈(S)(S−6)²/64`. Exact symbolic polynomial identities prove

`−P₁₅(S)−10⁹D(S)>0`,

`3·10⁹D(S)+P₁₅(S)>0`

throughout the closed scale box. Each certificate shifts `y=S−191/10`, where `0≤y≤1`, and expresses the polynomial as a strictly positive rational constant plus positive rational multiples of `y^n` and `1−y^n`. Both expansions are recorded explicitly in `ThetaCuspOddCompensationCoefficient` and verified by `ring`; their signs follow from the order laws for powers. Division by `D(S)>0` proves the unconditional bounds

`10⁹<K_*<3·10⁹`.

No numerical theta evaluation enters these proofs.

## Unique sign transition

Write `L=log Φ`, `g(x)=3+2xL′(x)`, and `G(x)=3Φ(x)²+2xΦ(x)Φ′(x)`.

The exact quotient derivative gives `G=Φ²g`. The corpus strict logarithmic concavity theorem makes `L′` strictly decreasing; evenness gives `L′(0)=0`. Hence `L′(x)<0` for `x>0`. For `0≤a<b`,

`bL′(b)<aL′(b)≤aL′(a)`,

so `g` decreases strictly on the complete nonnegative ray. It is continuous and `g(0)=3`. Let `l=L′(1)<0` and `T=1−4/l>1`. Monotonicity gives

`g(T)≤3+2Tl=−5+2l<0`.

The intermediate value theorem supplies a unique `τ>0` with `g(τ)=0`. Strict monotonicity identifies all signs: positive before `τ`, zero at `τ`, negative after `τ`. The positive factor `Φ²` gives exactly the same classification for the literal correction `G`.

## Explicit coefficient family and the remaining comparison

Set `H_C=H+CΔG`. At the seam,

`H_C(0)=Δ(0)Φ(0)²(3C−K_*)`.

Thus every `C≥10⁹` repairs the seam strictly. At any fixed center, `H_C` is affine in `C`. On `G≥0` it increases with `C`; on `G≤0` it decreases. Positive endpoint determinants therefore imply positivity for every intermediate coefficient.

Continuity gives positive neighborhoods for `C=10⁹` and `C=3·10⁹`. Intersecting them gives one neighborhood for the full coefficient interval. The existing cofinal source theorem applies separately to those same two endpoints; intersecting their rays gives one tail for the full interval. Consequently there exist `0<δ<X` such that every `C∈[10⁹,3·10⁹]` has `H_C>0` on `(0,δ)` and `[X,∞)`.

The canonical determinant satisfies the global lower comparisons

`H_(K_*)(x)≥H_(10⁹)(x)` for `0≤x≤τ`,

`H_(K_*)(x)≥H_(3·10⁹)(x)` for `τ≤x`.

These select explicit rational coefficients for the compact source inequalities. The present theorem supplies no effective numerical bounds on `δ`, `X`, or `τ`, and does not prove the remaining compact determinant signs. The center correction still has its previously proved zero integral, so a global positive comparison would apply to the literal tenth mixed moment.

## Lean landing and verification

- `ThetaCuspOddCompensationCoefficient`: actual seam formulas, mass cancellation, and rational coefficient bounds.
- `ThetaCuspCenterCompensationSign`: exact normalized sign carrier and unique literal-source sign transition.
- `ThetaCuspOddCompensationRationalFamily`: seam margin, coefficient monotonicity, common positive ends, and canonical rational lower comparisons.

All three modules passed targeted `lake env lean` checks and are wired into the RHTower umbrella. Five new capstones report only `propext`, `Classical.choice`, and `Quot.sound`; no axioms were added. No numerical certificate is used. Formal lint passes; all 19 new public names have no outside conflicts, and each new module has exactly one umbrella import. No full or umbrella build was run.

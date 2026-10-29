# The exact positive range of the certified Trans-Metzler scheme

- **ID:** review-2910-w01-optimal-certified-perturbation-floor
- **Stage:** 3-formalized
- **Type:** THEOREM / optimization
- **Source:** [W01](../../../reports/review-2910/obstacles-summary.md).
- **Statement:** Optimize the reference floor and every center Young parameter,
  characterize the largest certified fixed overlap, and transfer its full open
  positive range to the actual complete Weil matrices.

## Exact constants and range

Fix the actual plateau φ=`transMetzlerProfile`. Write

`q₀=(∫φ)²/∫φ²`, `b₀=bumpRobin φ 1/∫φ²`, `ψ=log 4+4/exp 1`,
`α(c)=c q₀`, `r(c)=1−α(c)`, `s(c)=b₀−log(2π)−log c`,
`f(c)=s(c)+α(c)`, `A(c)=α(c)²ψ`,
`R(c)=1276c²+α(c)(ψ+15)−s(c)`,
`q(c)=R(c)+f(c)=1276c²+α(c)(ψ+16)`.

For `1≤c<1/q₀`, define

`d*(c)=(√A(c)+√(A(c)+r(c)q(c)))²/r(c)²`,
`L(c)=f(c)−2000(c−1)(1+d*(c))`.

There is exactly one c* in `(1,1/q₀)` with L(c*)=0. It lies before
`(1+1/q₀)/2`. For every `1≤c≤c*` and ε>0, eventually in N,

`⟨completeWeilMatrix φ c N · x,x⟩ ≥ (L(c)−ε)‖x‖²`.

For `1≤c<c*`, the actual matrix is eventually positive definite. The explicit
rational enclosure is

`1+10⁻¹⁶<c*`,

and at `c=1+10⁻¹⁶` the actual matrix eventually has floor `‖x‖²/400`.
At c* the theorem gives every strict relaxation of zero; eventual positivity
at the boundary is not asserted.

The constants 1276=1264+12 and 2000 are the existing certified cross/pole and
perturbation bounds. The optimization is exact over the reference energy,
all Young parameters, convex weights and vanishing error allowances in this
bound family. It does not locate the actual spectral boundary beyond it.

## Dependency-closed proof

### Reference energy and parameter coercivity

Let M=‖x‖², D=poleDefect(x), E the actual reference-matrix energy, and F the
actual complete-matrix energy at width c/N. The prime-form deficit theorem,
center estimate with λ>0, cross error 1264c²M and pole error 12c²M give,
for every ε>0 and all sufficiently large N,

`E ≥ (r−α/λ−ε)D−(R+αψλ+ε)M`.

The Euler constant in the prime deficit cancels the explicit subtraction in
the reference matrix. No fixed extra mass loss is introduced.

When α<1, conductor one minimizes the limiting adjunction spectrum: every
other conductor has Ramanujan excitation at least 2 log 2>1. The conductor-one
energy is exactly f(c). Coercivity bounds the defect of a putative lower
normalized eigenvector. Arithmetic compactness approximates it by finitely
many Ramanujan modes, forcing nonzero coordinate mass. The norm-quasimode
residuals and the fixed spectral gap contradict this mass. Hence every floor
strictly below f(c) eventually holds. Conversely, the actual conductor-one
quasimode has norm tending to one and energy tending to f(c), so no larger
uniform reference floor can hold eventually.

### Exact scalar optimization

Set x=α/λ>0. The limiting Young family is

`E ≥ fM`, `E ≥ (r−x)D−(A/x+R)M` for every x>0,
`|F−E|≤e(D+M)`.

Put `u=(√A+√(A+r(R+f)))/r`, so `d*=u²`. It satisfies
`r u²−2√A u=R+f`. Completing a square proves

`(r−x)u²≤A/x+R+f`,

with equality at x*=√A/u. Thus the exact minimum of the defect-loss ratio is
u², and the optimal reserve is a*=r−x*>0. Convex interpolation spends weight
e/a* and gives `F≥(f−e(1+u²))M` for 0≤e≤a*.
The scalar data M=1,D=u²,E=f attain every Young inequality and this floor.

For a*≤e<r, the exact floor is `−R−e−A/(r−e)`, attained at
`D=A/(r−e)²`. For e≥r, the family admits arbitrarily negative energies.
All these witnesses satisfy every Young bound, not just the minimizing one.
Since R>0, a nonnegative first-regime floor forces e<a*, and no second positive
regime exists. If r≤0, the same obstruction follows from a stronger positive
reserve equal to e. Consequently the scalar family certifies a positive
uniform floor exactly when c<c*.

### Transfer and unique boundary

The plateau bounds give `99/100≤q₀<1` and `1−q₀≥1/128000`. Its Robin–Euler
bound implies s(c)<0 for c≥1; hence R(c)>0. On the charge-reserve interval,
f(c)>1/25 and c<100/99<5/4, within the original perturbation theorem's domain.

For e=2000(c−1), choose a small τ>0. The actual reference floor f−τ,
coercivity reserve a*−τ, mass cost B+τ and perturbation coefficient e+τ give

`f−τ−(e+τ)(1+(B+f)/(a*−τ))`.

This coefficient is continuous at τ=0 and tends to L(c). When L(c)≥0,
e<a* leaves room for these errors. This proves every asserted actual-matrix
floor without an additional analytic hypothesis.

The ceiling d* increases as r decreases and A,q increase: compare both Young
families at the second family's minimizing parameter. For 1≤c<d,
`f(d)−f(c)≤d−c` by logarithm monotonicity and q₀<1, while the perturbation
coefficient increases by `2000(d−c)`. Therefore L strictly decreases.
It is positive at one. At c=(1+1/q₀)/2, e≥r, so L is negative by the necessary
reserve condition. Continuity proves existence and uniqueness of c*.

For the explicit rational point, the plateau shape gives f(1)>69/1000.
At c=1+10⁻¹⁶, choose λ=256000. The variance bound gives reserve at least
1/257000; ψ≤4 gives mass loss at most 1026000; f(c)>3/50. Exact convex
interpolation yields L(c)≥1/200. A tail allowance 1/400 gives the actual
matrix floor 1/400. No numerical experiment or floating-point certificate
is used.

## Lean declarations and audit

`HTGeometry/OptimalYoungDefectFloor.lean` proves the exact Young minimum,
attainment in both regimes, unboundedness, positivity criterion, parameter
monotonicity, and continuous relaxation of the coefficient.

`TransMetzlerWeilPositivity/TransMetzlerReferenceFloor.lean` proves the actual
parameter coercivity, exact limiting reference floor, conductor-one energy
limit, and analytic charge/self-energy bounds.

`TransMetzlerWeilPositivity/TransMetzlerYoungOptimization.lean` contains:

- `exists_unique_transMetzlerCertifiedBoundary`
- `eventually_completeWeilMatrix_young_floor_to_boundary`
- `eventually_completeWeilMatrix_posDef_before_young_boundary`
- `transMetzler_young_positive_certificate_iff`
- `eventual_transMetzlerMainMatrix_floor_le_reference`
- `transMetzlerCertifiedBoundary_explicit_lower`
- `eventually_completeWeilMatrix_floor_at_explicit_young_ratio`

All three leaves passed final plain checks from `formal/`:

```text
lake --old env lean GaloisForLFunctions/HTGeometry/OptimalYoungDefectFloor.lean
lake --old env lean GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerReferenceFloor.lean
lake --old env lean GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerYoungOptimization.lean
```

The six scalar, five reference, and seven capstone transitive-axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`. All three
modules are wired into their umbrellas; no umbrella was compiled. The
support-module oleans were built only for the capstone's imports. No
capstone olean is needed.

The earlier `OptimizedTransMetzlerFloor.lean` retains the exact optimum of the
coarser three fixed bounds. The present result optimizes the underlying
parameter family and exact reference energy.

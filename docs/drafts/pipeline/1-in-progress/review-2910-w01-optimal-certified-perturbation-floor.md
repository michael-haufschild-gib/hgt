# Optimal floor from the certified Trans-Metzler estimates

- **ID:** review-2910-w01-optimal-certified-perturbation-floor
- **Stage:** 1-in-progress
- **Type:** THEOREM (formalized certified-bound optimization; analytic-constant audit open)
- **Source:** [W01](../../../reports/review-2910/obstacles-summary.md)
- **Statement:** Optimize the exact existing reference/coercivity/perturbation inequalities and
  transfer their full open positive range to the actual complete Weil matrices.

## Paper argument

[FORMALIZED] Let M=‖x‖² and D=poleDefect(x). The current source proves
`E≥M/25`, `E≥−2100000M+D/1024000`, and
`F≥E−e(D+M)`, with `e=2000δ+o(1)` for overlap at most 1+δ.
For `0≤e≤1/1024000`, combine the first inequalities with weights
`1−1024000e` and `1024000e`. This yields

`F≥(1/25−Ke)M`, where `K=1+1024000(2100000+1/25)`.

The exact optimal asymptotic floor furnished by these inequalities is
`L(δ)=1/25−2000Kδ`. Indeed, the scalar data
`M=1`, `D=K−1`, `E=1/25`, `F=1/25−Ke` attain all relevant inequalities.
Thus their positive range has exact supremum
`δ*=1/(50000K)=1/107520002048050000`.
The existing width, geometry and coercivity constraints are all weaker than this constraint.
For any ε>0, choose a positive tail allowance at most ε/K and half the defect reserve. Since
`C_short/log(N/3)→0`, the actual complete Weil matrix eventually has floor `L(δ)−ε`.
For δ<δ*, choose ε=L(δ)/2 to obtain positive definiteness.

The optimum here is for the displayed, already-proved estimates. It is not an upper bound on
actual positivity, nor a claim that every analytic constant in the underlying method is optimal.
Any further improvement must sharpen at least one estimate rather than change their convex weights.

## Verification

- [x] Read exact reference floor, coercivity, and perturbation statements and their domains.
- [x] Optimal algebraic floor and sharpness formalized.
- [x] Actual-matrix transfer over the full open certified range checked.
- [x] Transitive axioms and umbrella import audited.

Leaf `TransMetzlerWeilPositivity/OptimizedTransMetzlerFloor.lean` passed
`lake --old env lean GaloisForLFunctions/TransMetzlerWeilPositivity/OptimizedTransMetzlerFloor.lean`.
All three terminal declarations report only `propext`, `Classical.choice`, `Quot.sound`.

## Remaining scope

The spectral-floor argument uses adjunction energies strictly above 1/20 but states only 1/25.
Consequently the optimum of these three displayed inequalities does not yet certify the largest
reach of the underlying analytic proof. Generalize its reference floor before closing W01;
also retain the c-dependence of the charge reserve when auditing the coercivity constants.

## Parameter-dependent refinement to formalize

At width `c/N`, write `α=c q₀`, `r=1−α`, `ψ=psiConstant`,
`s=completeWeilSelfFinitePart φ c`, and `f=completeWeilAdjunctionEnergy φ c 1`.
The prime-form deficit theorem permits arbitrarily small positive ε. Keeping the
center's Young parameter λ therefore gives the limiting coercivity coefficients

`aλ=r−α/λ`, `Bλ=1276c²+α((1+λ)ψ+15)−s`.

The ε-loss is `ε(D+M)` and must be retained until the final eventual estimate.
For `c≤1.001`, the existing adjunction proof shows conductor 1 lies below every
other positive conductor. The finite-approximation argument should thus supply
every reference floor strictly below f, with the actual conductor-1 quasimode
certifying its optimality.

Set `R=1276c²+α(ψ+15)−s`, `A=α²ψ`, and `q=R+f`.
For `r>0`, `A>0`, and `q≥0`, optimizing the entire Young family gives

`d*=(√A+√(A+rq))²/r²`, `a*=r−√A/√d*`.

The candidate optimized perturbation floor is `f−e(1+d*)` for `0≤e≤a*`.
Indeed, Young optimization yields `E/M≥rd−2√(Ad)−R`, with `d=D/M`;
its intersection with `E/M=f` is d*. Equality there would certify sharpness
for the displayed family. This refinement, its actual-matrix transfer, and its
maximal positive c-range remain unformalized. No stronger range is claimed.

The candidate tail completes the scalar optimization: for `a*≤e<r`, the floor
is `−R−e−A/(r−e)`, attained at `D/M=A/(r−e)²`. For `e≥r`, no finite lower
floor survives the Young family. If R>0, the tail is negative, so every positive
certificate belongs to the first regime. These claims require formalization.

Conductor-one minimality extends to every positive c with α<1: the next
Ramanujan energy is separated by at least 2 log 2>1. Thus the natural domain is
`1≤c<1/q₀`, within the geometric perturbation range because the profile integral
bounds give q₀>4/5. On this domain f decreases and d* increases. The proposed
maximal range is the interval ending at the unique zero of
`f(c)−2000(c−1)(1+d*(c))`; existence, uniqueness and matrix transfer remain open.

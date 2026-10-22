# Exact constrained-ground source moment and unavoidable pole coupling

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Modules:** `RHTower.CCMRestrictedWeilPolarGroundSourceMoment` (7 public theorems, 1 definition); `RHTower.CCMRestrictedWeilPolarSourceNonvanishing` (11 public theorems). Both wired into `RHTower.lean`.
- **Predecessor:** [Actual Gamma action and full source cancellation](weil-gamma-physical-action-and-pole-source-cancellation.md).
- **Open continuation:** [Signed boundary–arithmetic ground control](../1-in-progress/weil-gamma-pole-boundary-action.md).

## Full proof chain and precise boundary
Exact prime–Gamma action → signed control of constrained ground forcing → exclusion of a zero ground → positive floor at every aperture → weighted pole exclusion → RH. These modules determine the forcing scalar from the actual source, exclude automatic pole-space invariance, and separate the divergent symmetric boundary term from its bounded asymmetry. They do not select the source moment of a particular constrained ground or exclude its forced zero equation.

## Conjecture → proof / fail-and-pivot loop
1. **Scalar identification conjecture:** self-adjointness and the exact pole Gram matrix determine the even/odd forcing coefficient from the boundary–arithmetic source. **Proved:** no energy term survives the constrained pole pairing, and the denominator is positive in both parity sectors.
2. **Shortcut tested:** perhaps the literal Weil operator preserves the two-pole space, making its constrained source coupling vanish identically. **False:** the actual source defect diverges at the aperture endpoint and lies outside every two-pole combination.
3. **Positive survivor:** the source functional is nonzero on the completed constrained sector at every aperture and realizes every complex value. **Proved.** This retains actual source geometry; it is stronger than only denying invariance.
4. **Stronger decomposition exposed:** the two divergent endpoint logarithms have a common reflection-symmetric part. Their complete reflection asymmetry is an explicit bounded logarithmic difference. **Proved, with strict uniform bound `log 2`.**
5. **Live comparison:** use the exact parity coefficient and this decomposition to control the source on the selected ground. Nonzero coupling on the whole space does not imply nonzero coupling on that ground, and arbitrary complex source moments rule out a universal linear sign argument on all constrained vectors.

## Dependency-closed paper proof
Fix `a>0`, `p±=1_[-a,a] exp(±x/2)`, and write `J_a` for the completed form-domain embedding. Let

`K_a(x)=exp(x/2)[B(a-x,a+x)-E_psi(exp(a-x))-E_M(a+x)]`,

where `E_psi(Y)=psi(Y)-Y`, `E_M(t)=sum_(2≤n≤floor(exp t)) Lambda(n)/n-t`, and

`B(R,L)=-(1/2)log(1-exp(-2R))-(1/2)log(tanh(L/2))`.

The preceding source-cancellation theorem constructs an actual aperture L² vector `d_a` with coefficient `1_[-a,a]K_a`. Define the continuous complex-linear functional

`F_a(u)=<d_a,J_a u>=integral_[-a,a] K_a(x)(J_a u)(x) dx`.

This integral identity holds for every complete form vector. Its product is absolutely integrable by L² pairing, and

`|F_a(u)|≤||d_a||₂ ||J_a u||₂`.

For constrained `u`, both exponential moments vanish and the full operator cancellation gives `F_a(u)=<H_a p+,J_a u>`.

### Exact parity-ground coefficient
Suppose an actual domain vector `f=J_a u` satisfies both constraints and

`H_a f=E f+c(p++r p-)`, `r∈{1,-1}`.

Actual self-adjointness gives `<H_a p+,f>=<p+,H_a f>`. The first term is zero by the positive-pole constraint. Exact Gram entries `<p+,p+>=2sinh(a)` and `<p+,p->=2a` therefore give

`F_a(u)=c[2sinh(a)+2ar]`.

Since `sinh(a)>a>0`, both denominators are strictly positive. Thus

`c=F_a(u)/(2sinh(a)+2ar)`.

The existing unconditional parity-ground existence theorem provides such a nonzero actual domain vector at every aperture with `E=mu_0(a)`. Substitution gives the new unconditional existence theorem `exists_polarGround_boundarySource_forcing`, whose coefficient is the explicit source quotient. No forcing coefficient or parity is assumed to vanish or have a selected sign.

### Endpoint divergence survives every arithmetic term
As `x→a` from below, `1-exp(-2(a-x))→0` from above. Its logarithm tends to negative infinity, so its coefficient `-1/2` tends to positive infinity. Both terms belonging to `L=a+x→2a>0` have finite limits. Hence

`B(a-x,a+x)→+infinity`.

For `-a<x<a`, monotonicity of the literal Chebyshev function gives

`psi(exp(a-x))≤psi(exp(2a))`.

The already proved elementary Mertens bound gives `E_M(a+x)≤log 4+5`. Consequently

`B-E_psi-E_M≥B-[psi(exp(2a))+log 4+5]`.

The lower bound tends to positive infinity, and `exp(x/2)→exp(a/2)>0`; therefore `Re K_a(x)→+infinity` from the aperture interior. This is a theorem about the literal arithmetic profile, with every prime power retained.

No almost-everywhere finite upper bound can hold on the aperture: any sufficiently short left neighborhood of the endpoint has `Re K_a>C+1`, contains an open interval of positive measure, and therefore contains a point satisfying any proposed almost-everywhere bound `Re K_a≤C`. The two inequalities contradict each other.

### Actual nonvanishing and its positive survivor
A two-pole vector `c_+p++c_-p-` has a continuous coefficient function before cutoff, bounded on the compact aperture. If `d_a` equalled such a vector, the exact almost-everywhere representatives would give an essential upper bound for `Re K_a`, contradicting the preceding theorem. Thus

`d_a ∉ span{p+,p-}`.

If `F_a` vanished on every constrained complete form vector, the corpus's exact continuous-annihilator classification would represent it by a unique two-pole vector. Density of `J_a` would identify that vector with `d_a`, again a contradiction. Hence some constrained `u` has `F_a(u)≠0`. Scaling this same constrained vector by `z/F_a(u)` realizes every `z∈ℂ`.

The full image `H_a p+` differs from `d_a` by a two-pole vector. Therefore `H_a p+` also lies outside the entire two-pole span. Automatic invariance is excluded for the actual unrestricted operator, with its domain membership already proved. The survivor does not specify which constrained ground, if any, lies in the kernel of `F_a`.

### Exact bounded reflection asymmetry
Factor

`1-exp(-2L)=(1-exp(-L))(1+exp(-L))`.

Both factors are positive for `L>0`; the ordinary real logarithm product identity gives

`B(R,L)=-(1/2)log(1-exp(-2R))-(1/2)log(1-exp(-2L))+log(1+exp(-L))`.

The first two terms are reflection-symmetric. Thus

`B(R,L)-B(L,R)=log(1+exp(-L))-log(1+exp(-R))`.

For every positive `t`, `0<log(1+exp(-t))<log 2`. Subtracting the two bounds proves

`|B(R,L)-B(L,R)|<log 2`.

Both divergent logarithms are retained in the symmetric term; no numerical approximation or neglected endpoint term is used.

## Verification
- Scratch `lake env lean /tmp/hgt-ground-source.3dwu8uiu/Force.lean` and `Boundary.lean`: PASS.
- Named final builds of `GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundSourceMoment` and `GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarSourceNonvanishing`: PASS. No full or umbrella build.
- No numerical experiment, computational oracle, added axiom, or RH premise supplies these results.
- Scratch `Audit.lean`: all 18 public theorems have exactly `[propext, Classical.choice, Quot.sound]`; actual mathlib `RiemannHypothesis` printed and remains unproved.
- Final `python3 scripts/formal_tools.py lint`: PASS (`formal lint passed`); existing size warnings remain. Logs: `/tmp/hgt-ground-source.3dwu8uiu/Lint.txt` and `.err`.
- `git diff --check`: PASS; all owned Lean/build processes terminal. No full or umbrella build, numerical experiment, or commit.

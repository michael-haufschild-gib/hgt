# CGL conductor-uniform safe-line exponential tail

- **ID:** CGL-SAFE-LINE-CONDUCTOR-UNIFORM-EXP-TAIL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Chen--Gupta--Li, arXiv:2507.08296v2, Section 12.1
- **Statement:** Every primitive Class-I safe-line integrand and its actual two-sided exterior integral have a universal exponential bound with all row dependence explicit: mollifier scale `X+1`, conductor square `q²`, zero geometry `(‖ρ‖+5)³`, and rate `exp(-πB/4)`.

## Goal

Close the source's `|Im z| >= log²T` Mellin-tail truncation without hiding character dependence in a compactness constant. The fixed-row tail is insufficient for zero-density aggregation; the amplitude must remain uniform as conductor and selected row vary.

## Gates

- [x] 0 → 1  in-progress: source-pure problem and exact cutoff identified
- [x] 1 → 2  fully-proven: complete proof below, no open analytic dependency
- [x] 2 → 3  formalized: targeted Lean checks and axiom audit green
- [ ] 3 → 4  publication-ready: novelty audit and standalone exposition

## Proof

**[PROVED HERE]** The old `Re(s)=-2` functional-equation edge meets parity-dependent Gamma poles at bounded ordinate, forcing a character-dependent compact segment bound. Move instead to the first pole-avoiding half-integer edge whose reflection lies in absolute convergence:

`s = -3/2 + it`, `1-s = 5/2 - it`.

For even parity the Gamma arguments are `-3/4+it/2` and `5/4-it/2`; for odd parity they are `-1/4+it/2` and `7/4-it/2`. Conjugation preserves Gamma norm, and in both cases the arguments differ by exactly two. Two applications of `Gamma(z+1)=z Gamma(z)` give the exact quotient as a product of two linear moduli, bounded by `(1+|t|)²` for every real `t`. The conductor cpow contributes exactly `q²`; primitive root number has norm one; the remaining `π⁻²` factor is at most one. Hence

`‖Gχ(-3/2+it)‖ <= q²(1+|t|)²`.

The reflected `L(5/2-it,χ⁻¹)` is bounded by the universal absolute-convergence constant

`C₀ = 1 + Σ_{n>=0} n⁻²`,

independent of modulus and character. Dividing `L(s,χ)` by `(s-4)³` makes both edges bounded. Existing order-one growth supplies the Phragmén--Lindelöf interior-growth premise but does not enter the boundary constant. Propagation across `-3/2 <= Re(s) <= 2` yields

`‖L(s,χ)‖ <= 4 C₀ q² ‖s-4‖³`,

and on the critical line

`‖L(1/2+it,χ)‖ <= 4 C₀ q² (4+|t|)³`.

Combining this with the contractive smoothing factor, `‖M_X‖ <= X+1`, uniform strip Gamma decay, and polynomial absorption gives one universal `D >= 0` such that every primitive row satisfies

`‖integrand(t)‖ <= D (X+1) (4 C₀ q²) (‖ρ‖+5)³ exp(-π|t|/4)`

for `|t|>=1`. Exact integration over `(-∞,-B]` and `[B,∞)` gives

`‖exterior(B)‖ <= (8/π) D (X+1) (4 C₀ q²) (‖ρ‖+5)³ exp(-πB/4)`

for `B>=1`. This is the literal CGL safe-line tail with no hidden character-dependent amplitude.

## Lean certificate

Modules:

- `formal/GaloisForLFunctions/RHTower/ChenGuptaLiPoleAvoidingConductorStrip.lean`
- `formal/GaloisForLFunctions/RHTower/ChenGuptaLiSafeLineExponentialTail.lean`

Key declarations:

- `norm_cglLemma62PrimitiveFunctionalFactor_poleAvoidingLeftPoint_le`
- `cglPrimitiveLFunction_poleAvoidingLeftPoint_reflection`
- `norm_LFunction_le_cglDirichletLRightEdgeConstant`
- `norm_primitiveLFunction_conductorUniform_strip_le`
- `norm_primitiveLFunction_criticalLine_conductorUniform_le`
- `exists_uniform_norm_cglPrimitiveClassI_leftLineIntegrand_polynomialExponential_le`
- `exists_uniform_norm_cglPrimitiveClassI_leftLineIntegrand_exponential_le`
- `cglPrimitiveClassI_leftLine_exteriorIntegral_exponential_bound_of_pointwise`
- `exists_uniform_cglPrimitiveClassI_leftLine_exteriorIntegral_exponential_bound`

Direct targeted source checks passed. `#print axioms` for all fourteen new public declarations reports only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint reports no task-caused error; three unrelated pre-existing HTGeometry umbrella reachability errors remain.

## Frontier effect

CGL Section 12.1's safe-line analytic tail and its cross-conductor amplitude are closed. At `B=log²T`, the exponential is superpolynomial in `T`; the remaining source-facing task is only to substitute the paper's polynomial parameter ranges during final Class-I aggregation. Nearby live obligations are actual selected-row construction, `S2/S3`, nonprincipal finite head, bounded-head principal census, and global collision-budget aggregation.

## Log

- 2026-08-23 — fixed-row safe-line exterior tail formalized; opaque character-dependent strip constant isolated.
- 2026-08-23 — pole-avoiding `Re(s)=-3/2` edge conjectured after corpus-wide Gamma/functional-equation audit.
- 2026-08-23 — exact two-recurrence Gamma quotient, universal right-edge constant, conductor-uniform Phragmén--Lindelöf strip, and actual two-ray CGL exterior bound proved and formalized.

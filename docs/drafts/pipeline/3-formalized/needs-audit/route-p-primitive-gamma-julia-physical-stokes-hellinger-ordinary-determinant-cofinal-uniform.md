# Route P primitive Gamma--Julia physical Stokes Hellinger ordinary determinant cofinal uniformity

- **ID:** `route-p-primitive-gamma-julia-physical-stokes-hellinger-ordinary-determinant-cofinal-uniform`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105O]`
- **Parent:** `route-p-primitive-gamma-julia-physical-stokes-hellinger-ordinary-determinant.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryDeterminantCofinalUniform.lean`

## Goal

Upgrade P-G105N's pointwise convergence of literal finite ordinary determinants to local uniform
convergence, the minimum topology that can support divisor passage.

## Conjecturing loop

### Conjecture 1 — pointwise convergence plus entireness is enough for divisor passage

**Rejected.** Pointwise convergence of entire functions does not control zeros or even preserve a
nonzero analytic limit. A Hurwitz/Rouché step requires local uniform convergence.

### Conjecture 2 — existing uniform multiplication theorem combines exponential and det2 factors

**Falsified at the exact type boundary.** Available theorem is for uniform groups. Complex
multiplication is not a group operation at zero, exactly where determinant factors may vanish.
Applying that theorem would erase the divisor problem rather than solve it.

### Conjecture 3 — bounded limit functions suffice for uniform multiplication with zeros

**Proved.** On a nonempty set, if `f_i -> f` and `g_i -> g` uniformly and norms of `f,g` are bounded,
then `f_i g_i -> fg` uniformly. Proof chooses a common bound `B`, gets eventual bound on `f_i`, and
uses exact error decomposition

```text
fg - f_i g_i = (f-f_i)g + f_i(g-g_i).
```

No nonvanishing or inverse bound is used.

### Conjecture 4 — trace-restoring exponential may fail to converge uniformly on discs

**Falsified.** Cofinal finite traces converge as scalars. Multiplication by disc coordinate is
uniform because coordinate is bounded. Real parts of limiting exponents are bounded above, so
complex exponential preserves uniform convergence.

### Conjecture 5 — reflection `z -> -z` breaks det2 disc convergence

**Falsified exactly.** Reflection preserves every centered closed disc. Composing P-G105L's det2
uniform convergence with reflection gives uniform convergence of reflected det2 factors. Compact
disc boundedness plus zero-safe multiplication theorem combines factors.

### Conjecture 6 — closed-disc result may not yield corpus-level local uniformity

**Falsified.** Every compact subset of complex plane lies in a positive-radius centered closed
disc. Monotonicity of uniform convergence therefore yields `TendstoLocallyUniformly` globally.

## Paper proof

First prove bounded-product lemma by epsilon estimate above, choosing error threshold
`min(1, epsilon/(2B))`. Scalar trace convergence becomes uniform convergence of constant functions.
Multiply by bounded coordinate on a closed disc, then compose with exponential using an upper bound
on real parts. Reflect existing locally uniform det2 approximants; reflection preserves centered
disc. Limiting exponential and det2 factors are bounded on compact disc, so bounded-product lemma
gives uniform convergence of their product, exactly P-G105N's literal finite ordinary determinant.
Compact exhaustion upgrades disc statement to global local uniformity. `QED`

## Novelty and anti-theatre audit

This closes exact topology needed for future divisor transport:

- proves zero-safe uniform multiplication missing from imported library surface;
- upgrades literal finite physical determinant convergence from pointwise to local uniform;
- retains ordinary trace restoration and reflected sign convention;
- produces exact `TendstoLocallyUniformly` statement, not prose compact convergence;
- makes finite cofinalization compatible with Hurwitz/Rouché arguments.

Result is not RH. It controls finite-section limit at fixed positive aperture only. Aperture-wall
local uniformity, nonzero wall limit, divisor retention, and Xi divisor identification remain open.

## Formal status

Lean proves unconditionally:

- bounded-product uniform convergence theorem for complex functions with possible zeros;
- uniform trace-exponential convergence on every positive-radius closed disc;
- reflected det2 uniform convergence on same disc;
- uniform convergence of literal finite ordinary determinants on every closed disc;
- global `TendstoLocallyUniformly` cofinal convergence;
- P-G105O capstone over full physical parameter domain.

Direct Lean and axiom audit pass; only `propext`, `Classical.choice`, and `Quot.sound` are reported.
Target-only Olean audit is pending serialized cache stabilization. Module is umbrella-wired; no
umbrella build was run.

## Refined open core

Finite cofinalization is now analytically closed at fixed aperture. Next hard gate is parameter
wall: prove ordinary determinant family converges locally uniformly as `d -> 0+`, limit is not
identically zero, and zeros do not escape/collapse incorrectly. Then identify wall divisor with Xi
from source transport without fitting.

## Higher universal principle

Two limits are categorically different: cofinal carrier limit and aperture renormalization limit.
P-G105O closes first in compact-open topology. Earlier pointwise obstruction was shadow of mixing
these limits before choosing correct topology. Universal rule is: trace restore before wall passage,
then close carrier limit in compact-open topology, only afterward study singular parameter wall.

## Log

- 2026-08-16 — Zero-safe bounded-product theorem, uniform closed-disc finite ordinary determinant
  convergence, and global local uniformity paper-proved and formalized.

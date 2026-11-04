# Every finite theta rank is strict near aperture one half

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6
- **Statement:** For every `N`, there is `0<δ≤1/4` such that every actual signed center-mixed Hankel section of size `n≤N` is positive definite whenever `|a−1/2|<δ`.

At `a=1/2`, the exact current is
`J(b)=2|Ξ(b−i/2)|² Re(ξ′/ξ)(1+ib)>0`.
The nonvanishing and logarithmic-derivative sign hold on `Re s≥1`.
Every nonzero real polynomial therefore has `∫p(b)²J(b)db>0`:
its nonzero locus contains an open interval, and the density is continuous
and strictly positive. Thus every finite raw moment matrix is strict.

On `|a|≤3/4`, one exponential majorant controls the current. Multiplication
by any fixed power of `b` preserves integrability, so dominated convergence
gives continuity of each raw moment at `a=1/2`. Finite-dimensional positive
definiteness is open. The exact identity
`mₖ(a)=2π·2⁻ᵏ·sₖ(a)` transfers this neighborhood to the actual signed jets
by a positive scalar and an invertible diagonal congruence. Principal
submatrices give the same neighborhood simultaneously for all `n≤N`.

## Lean

`GaloisForLFunctions/ThetaCuspSections/FiniteRankCriticalCollar.lean`,
namespace `GaloisForLFunctions.ThetaCuspSections.CriticalCollar`:

- `signedHankel_boundary_posDef`
- `signedHankel_posDef_near_half`
- `signedHankel_posDef_near_half_upto`

Canonical source check and transitive axiom audit: only `propext`,
`Classical.choice`, `Quot.sound`. Imported by `ThetaCuspSections.lean`.

Stronger bound: [the logarithmic critical collar](theta-cusp-logarithmic-critical-collar.md).

**Open:** a rank-independent critical neighborhood, or positivity for a
fixed rank above eight throughout `0<a<1/2`. The neighborhood here may
shrink with rank; Σ6 remains partially solved.

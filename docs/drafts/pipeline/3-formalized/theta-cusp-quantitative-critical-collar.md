# A factorial critical collar for every finite theta rank

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6
- **Statement:** There are constants `A≥1`, `c>0`, independent of rank, such that every actual signed center-mixed theta Hankel section of size `n≤N` is positive definite whenever
  `|a−1/2| < c/[A^(N+1)·((2N+1)!)^(N+2)]`.

## Proof

The actual boundary current `J(1/2,b)` is strictly positive at every frequency.
It therefore has a fixed lower bound `m>0` on some `[0,r]`, with `0<r≤1`.

For the uniform moment matrix `H_N[i,j]=1/(i+j+1)`, put `D=(2N)!`.
The matrix `D H_N` is integral and positive definite. Its determinant is a
positive integer, hence `det H_N≥D^(−N)`. Each cofactor is at most `(N−1)!`
in absolute value. Thus the inverse quadratic form is at most `N!D^N‖v‖²`.
Completing the square gives `‖v‖²≤N!D^N vᵀH_Nv`.

The compact moment matrix on `[0,r]` is a diagonal congruence of `rH_N`.
Since `0<r≤1`, the actual boundary matrix `M_N(1/2)` satisfies

`m r^(2N+1)‖v‖² ≤ N!((2N)!)^N vᵀM_N(1/2)v`.

Uniform Xi and Xi-derivative exponential bounds, transferred through Cauchy
circles, give
`|J(a,b)−J(1/2,b)|≤C|a−1/2|exp(−π|b|/4)` for `|a−1/2|≤1/8`.
Absorbing powers into a half-rate exponential yields fixed `M>0`, `K≥1` with
`|m_k(a)−m_k(1/2)|≤M K^k k! |a−1/2|` for every moment order `k`.
The rank-`N` quadratic perturbation is consequently at most
`N M K^(2N)(2N)! |a−1/2| ‖v‖²`.

Choose `A=1+(K/r)²`, `c=min(1/8,mr/(2M))`.
The inequalities

`N·N!·((2N)!)^(N+1) ≤ ((2N+1)!)^(N+2)`,

`K^(2N) ≤ A^(N+1)r^(2N)`

leave at least half the boundary floor throughout the stated collar.
The exact identity `m_k(a)=2π·2^(−k)·s_k(a)` transfers strict positivity to
the actual signed jets by a positive diagonal congruence. Principal
submatrices give the same collar for all `n≤N`.

## Lean

`GaloisForLFunctions/ThetaCuspSections/QuantitativeCriticalCollar.lean`,
namespace `GaloisForLFunctions.ThetaCuspSections.QuantitativeCollar`:

- `signedHankel_posDef_factorial_collar`
- `signedHankel_posDef_factorial_collar_upto`

Canonical source checks and transitive axiom audits: only `propext`,
`Classical.choice`, `Quot.sound`. Imported by `ThetaCuspSections.lean`.

Stronger bound: [the logarithmic critical collar](theta-cusp-logarithmic-critical-collar.md).

**Open:** a rank-independent critical collar, or any fixed rank above eight
throughout `0<a<1/2`. The factorial collar shrinks with rank; Σ6 remains
partially solved.

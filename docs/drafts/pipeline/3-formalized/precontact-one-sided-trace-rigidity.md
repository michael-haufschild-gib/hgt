# One-sided growth fixes the Weil Hamiltonian determinant

- **ID:** precontact-one-sided-trace-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ35; Σ75.
- **Statement:** The actual precontact traces satisfy `|τ_L(i)|²−|τ_R(i)|²=2K_a(i,i)`. The trace-derived canonical Hamiltonian is strictly positive with determinant one. Its two endpoint densities have exact difference `i(conj w−z)K_a(w,z)`.

## Proof

Write `q=K_a(i,i)`, `u=τ_L(a,i)`, `v=τ_R(a,i)`. The anchor traces are
real, and the symmetric right derivative is `q′=u²+v²`.
Physical translation `T_s f(x)=f(x+s)` has Fourier multiplier
`exp(−izs)`, hence multiplier `exp(s)` at `i`.

For `b=a+h/2` and `s=±h/2`, the orthogonal residual
`R_s=E_b(i)−exp(s)T_s E_a(i)` has squared norm
`q(b)−exp(2s)q(a)`. Multiplication by `exp(−s)` makes its pairing with
the entering constant collar exactly the full exterior response of the
old window. Reverse translation identifies that collar with the literal
left or right interval of width `h`.

In a fixed precontact enclosure, its energy is at most
`h(log(1/h)+D)`. The normalized response tends to the actual endpoint
trace. Testing the residual against the collar scaled by
`τ/√log(1/h)` therefore gives the respective limiting lower bounds

`u²≤q+(u²+v²)/2`, `v²≤−q+(u²+v²)/2`.

The right sides are the exact derivatives of
`exp(h)q(a+h/2)` and `exp(−h)q(a+h/2)`. Together the two inequalities
force `u²−v²=2q`; no one-sided upper estimate is needed.

The [canonical construction](precontact-trace-canonical-system.md) gives
`h₁h₂=((u²−v²)/(2q))²=1`. Nonnegativity then gives strict positivity.
Its exact trace readouts have coefficients
`α=(u+v)/(2√q)`, `β=(u−v)/(2√q)`. Since `2αβ=1`, their polarized
difference and Christoffel–Darboux give

`conj(τ_L(z))τ_L(w)−conj(τ_R(z))τ_R(w)=i(conj w−z)K_a(w,z)`.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheWeilHamiltonianHasDeterminantOne`,
namespace `WeilHilbertBeforeContact`, wired into its umbrella:

- `evalVector_anchorTrace_energy_difference`
- `canonicalHamiltonian_determinant_one`
- `canonicalHamiltonian_pos`
- `evalVector_endpoint_flux`

Final `lake --old env lean` source audit passed. All four printed transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

No contact-uniform arithmetic bound or regular canonical gauge at zero
follows from these identities.

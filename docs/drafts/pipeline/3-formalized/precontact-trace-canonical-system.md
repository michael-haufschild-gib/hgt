# The actual precontact Weil chain has a canonical system

- **ID:** precontact-trace-canonical-system
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ35; Σ75.
- **Statement:** The actual trace-derived Hamiltonian is nonnegative and locally integrable. Its entire canonical coordinates are locally absolutely continuous and satisfy the canonical equations, exact kernel identity and exact density identity.

## Construction

Write `q=K_a(i,i)`, `u=τ_L(a,i)`, `v=τ_R(a,i)`. The anchor traces are
real. Set `p=(u²+v²)/(2q)`, `r=uv/q`, and `e=E_a/√q`. For a fixed
precontact base aperture, define

`θ(a)=∫_base^a r`, `A₀=e^(−θ)(e−e♯)/(2i)`, `B₀=e^θ(e+e♯)/2`,

`h₁=(p+r)e^(2θ)`, `h₂=(p−r)e^(−2θ)`.

On each compact precontact interval containing the base,

`A₀′=−zh₂B₀`, `B₀′=zh₁A₀` almost everywhere.

For all complex `w,z`, the literal kernel and its actual trace density obey

`(conj w−z)K_a(w,z)=A₀(z)conj B₀(w)−B₀(z)conj A₀(w)`,

`D_a(w,z)=h₁A₀(z)conj A₀(w)+h₂B₀(z)conj B₀(w)`.

At the base, `A₀(i)=√q`, `B₀(i)=i√q`. The determinant is exactly
`h₁h₂=((u²−v²)/(2q))²`.

## Proof

The [exact trace span](precontact-endpoint-traces-hermite-biehler-span.md)
and [polarized kernel derivative](precontact-polarized-kernel-density.md)
give `e′=−izpe+(iz−1)re♯`. Its real entire pair has drift `±r`; the
displayed reciprocal gauge removes it. Positivity follows from
`p±r=(u±v)²/(2q)`.

Both coefficients are real parts of integrable polarized densities divided
by `2q`. The positive continuous anchor kernel has a positive lower bound
on each compact precontact interval. Composition with inverse square root
and exponential preserves the required local absolute continuity.
The trace span gives the exact readouts of both endpoint traces; their
polarization yields the Hamiltonian density. The determinant-one diagonal
gauge preserves Christoffel–Darboux. This refers to the gauge determinant,
not an asserted normalization of the Hamiltonian determinant.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheWeilTowerHasItsPrecontactCanonicalSystem`,
namespace `WeilHilbertBeforeContact`, wired into its umbrella:

- `ae_canonicalSystem_equations`
- `canonicalSystem_christoffelDarboux`
- `precontactKernelEndpointDensity_eq_canonicalHamiltonian`
- `canonicalHamiltonian_nonneg`, `intervalIntegrable_canonicalHamiltonian`
- `absolutelyContinuousOnInterval_canonicalSolutionA`
- `absolutelyContinuousOnInterval_canonicalSolutionB`
- `canonicalSystem_base_anchor`, `differentiable_canonicalSolution`
- `canonicalHamiltonian_determinant`

Final `lake --old env lean` source audit passed. All thirteen printed
transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`.

Hamiltonian determinant one and strict positivity follow from
[one-sided trace rigidity](precontact-one-sided-trace-rigidity.md).
No contact-uniform arithmetic bound or regular gauge at zero is asserted.

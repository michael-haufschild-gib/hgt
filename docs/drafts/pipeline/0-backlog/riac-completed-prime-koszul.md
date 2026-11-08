# Does the completed prime Koszul complex still contract?

- **ID:** RIAC-completed-Koszul
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md), completed topology
- **Statement:** The standard weighted exterior Hilbert completion is contractible whenever its original augmentation admits a closed extension.

## Exact candidate

Give a prime face `S` squared norm `(∏_(p∈S) p)^δ`, orthogonal to other faces,
and retain the augmented Dirichlet boundary. After conductor normalization,
the coefficient vector is `b_p=p^(−s−δ/2)`.

When `2 Re(s)+δ>1`, construct bounded differentials on every completed exterior
degree, with norm at most `(Σ_p |b_p|²)^(1/2)`. Extend the actual prime-two cone
with norm at most `2^(Re(s)+δ/2)` and prove `dh+hd=id`, including degree zero.
This would force every reduced completed homology group to vanish throughout
the exact bounded-extension region. The degree-one result excludes closed
boundary extensions throughout the complementary closed half-plane.

## Proof obligations and positive survivor

Construct the isometric comparison from the actual exterior prime chains to
the orthonormal face model; do not assume a norm-compatible exterior basis.
Prove the differential and cone bounds, their finite-chain comparisons, and
the extended Cartan identity. A candidate sharper survivor is the Hodge identity
`dd*+d*d=(Σ_p |b_p|²)id` and an explicit norm-controlled filling operator.
These are conjectured arithmetic realizations, not accepted theorems.

## Prior mechanisms

`RHTower.PrimeProductCutoffContraction` gives the algebraic prime-two cone and
Cartan identity on the original chains. `HTGeometry.FermionExteriorModel`
gives algebraic creation and contraction; it has no Hilbert completion.
Bounded fermionic creation operators and canonical anticommutation are
classical; see [Benedikter’s Fock-space notes](https://nielsbenedikter.de/advmaphys2/fockspace.pdf).
The contribution sought is the exact arithmetic norm, domain and chain-map
comparison, not a priority claim for those operator identities.

## Scope

Only the ordinary exterior Hilbert completion with the original augmentation
is tested. Relative, equivariant or modified complexes remain outside this
class. No statement about zeta zeros follows without a zero-detection theorem.

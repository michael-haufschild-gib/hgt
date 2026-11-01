# Exact pole and cancellation of the actual Mayer determinant

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).
- **Input:** [actual source holomorphy](gauss-mayer-source-parameter-holomorphy.md).

## Theorem

For the genuine operator `L(w)=R(w)+ζ(w)P`, `P f=f(0)·1`, the actual
Fredholm determinant satisfies

`D(w,λ)=A(w,λ)+ζ(w)B(w,λ)` on `Re w>0`,

where `A=det(I−λR)` and `B=det(I−λ(R+P))−det(I−λR)` are holomorphic in
`w` through one and entire in `λ`. Its exact residue at one is `B(1,λ)`.
Multiplication by `w−1` has a holomorphic extension, so the source pole is
at most simple. It is removable exactly when `B(1,λ)=0`; otherwise its
meromorphic order is `−1`.

For every `Re w>0`, `B(w,0)=0` and `∂λ B(w,0)=−1`. Its spectral zero set
is closed, discrete, and countable. Thus cancellation at `w=1` occurs only
at this exceptional set, includes `λ=0`, and every sufficiently small
nonzero `λ` gives a genuine simple pole.

## Proof

1. In the actual Cauchy matrix, the constant projection has entries
   `P_ij=δ_i0 (6/5)^(−j)(−1)^j`. Its diagonal sums to one and its entries
   obey the same geometric bound as the source matrix.
2. The remainder entries are holomorphic on `Re w>0`. Around any point,
   choose a closed parameter disc in this half-plane whose boundary avoids
   one. The existing compact source bound and boundedness of zeta bound
   the remainder entries there by `C(15/16)^(i+j)`. The scalar maximum
   principle extends this bound throughout the disc. The geometric
   Fredholm parameter theorem therefore applies to every `R+tP`.
3. Only row zero of each finite matrix changes with `t`. Determinant
   multilinearity makes every finite determinant affine in `t`.
   Passing the actual finite-determinant limits gives
   `det(I−λ(R+tP))=A+tB`; choosing `t=ζ(w)` proves the source identity.
4. The geometric trace bounds identify each determinant near zero with
   `exp(−Σ_{k≥1} λ^k Tr(M^k)/k)`. Termwise differentiation gives
   `D_M′(0)=−Σ_i M_ii`. Subtracting the derivatives for `R+P` and `R`
   cancels the remainder diagonal and leaves `−1`.
5. The entire zeta residue unit `G(w)=(w−1)ζ(w)`, with `G(1)=1`, gives
   the holomorphic numerator `H=(w−1)A+GB`. Off one, `H=(w−1)D`, and
   `H(1)=B(1,λ)`. A nonzero value gives meromorphic order `−1`. At a zero,
   the analytic divided difference of `H` extends `D`. Conversely, any
   analytic extension of `D` makes `(w−1)D` tend to zero, forcing `B=0`.
6. The derivative `−1` excludes an identically zero residue function.
   The analytic isolated-zero theorem gives its closed discrete zero set;
   second countability gives countability and isolates its zero at `λ=0`.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerRankOneDeterminantPole.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPole`.

- `projectionMatrix_eq`, `remainderMatrix_local_bound`.
- `differentiableOn_perturbedDeterminant`, `perturbedDeterminant_affine`.
- `sourceDeterminant_decomposition`, `determinant_residue`.
- `polePart_zero`, `polePart_deriv_zero`.
- `analyticAt_clearedDeterminant_one`, `clearedDeterminant_eq`.
- `meromorphicAt_sourceDeterminant_one`.
- `sourceDeterminant_order_of_residue_ne_zero`, `sourceDeterminant_removable_iff`.
- `polePart_zeros_closed_discrete`, `countable_polePart_zeros`.
- `eventually_sourceDeterminant_simple_pole`.

Direct production check passed without diagnostics. Fourteen transitive axiom
audits use only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella
import wired.

## Scope

This identifies the exact singularity and cancellation mechanism of the
constructed source determinant. General finite determinant multilinearity,
normal convergence, and analytic zero isolation are existing inputs.
No literature-priority claim is made.

The successor response now proves [cancellation at `λ=−1` throughout the source
half-plane](gauss-mayer-negative-unit-pole-cancellation.md). The parameter `λ=1`,
primitive modular coding, Selberg/scattering comparison, and exclusion of
off-critical resonances remain open. No RH conclusion follows.

The same coefficient now controls the [exact finite part of raw finite-branch
determinants](gauss-mayer-raw-determinant-finite-part.md). In the critical strip,
its zero set is precisely the set of spectral parameters admitting any finite
raw determinant limit.

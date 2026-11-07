# Conductor control of radial regularization

- **ID:** hhac-conductor-controlled-regularization
- **Stage:** 3-formalized
- **Type:** THEOREM

## Exact target

For primitive torsion orbits of orders `m,n`, the inverse squared chord cost
of distinct ordered pairs satisfies

`C(m,n) ≤ (mn)² c(m,n)`.

Together with the finite-radius decomposition this gives a conductor-explicit
error bound, including for signed finite pairings. The constant is deliberately
coarse; the point is uniformity as the conductors grow.
The [exact chord-energy certificate](hhac-torsion-chord-energy.md) sharpens
this cost and controls the spacing-regulated diagonal uniformly in conductor.

## Paper proof

If `u≠1`, `|u|=1`, and `u^L=1` with `L>0`, the geometric sum is zero.
Therefore `L=Σ_{k<L}(1−u^k)`. Telescoping gives
`|1−u^k|≤k|1−u|≤L|1−u|`, so `1≤L|1−u|`.
Consequently `|1−u|⁻²≤L²`.

For distinct `z∈O_m`, `w∈O_n`, take `u=z conjugate(w)` and `L=mn`.
Both orders are positive, `u^L=1`, and `|1−u|=|z−w|`.
Sum the preceding bound over the actual punctured orbit pairs.

The signed-pairing radial error is thus bounded by
`(1−r)²/(2r) Σ |a(m,n)|(mn)² c(m,n)`.
This removes geometric separation constants from the finite-radius certificate.
It does not control the diagonal self-energy or prove a global positive height.

## Prior work and proof status

The corpus already proves a sharper trigonometric root-separation bound in
`RHTower.RootOfUnityIntervalCompletion.norm_exp_sub_one_ge`.
The elementary geometric-sum argument here avoids angular parametrization;
its application gives the conductor certificate for the radial remainder.

Root-of-unity Riesz energies are classical; see Brauchart–Hardin–Saff,
[The Riesz energy of the N-th roots of unity](https://arxiv.org/abs/0808.1291).
No priority claim is made for root separation or root energy. The additional result
is the uniform certificate for the corpus's primitive-orbit regulator.

## Lean formalization

Module: `HeightHomotopyArithmeticCounts.ConductorControlledRegularization`.
Namespace: `GaloisForLFunctions.HeightHomotopyArithmeticCounts`.

- `root_chord_conductor_bound`, `inverse_chord_le_conductor_sq`: geometric-sum separation.
- `torsionPairCount_self`, `torsionPairCount_of_ne`: exact totient coefficients.
- `torsionInverseChordCost_le`: conductor control of the actual punctured orbit sum.
- `torsionRadialError_conductor_bound`, `finite_radius_conductor_certificate`:
  scalar and signed-pairing certificates, with all separation premises discharged.

The module passes a direct `lake --old env lean` check. The capstone axiom
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.

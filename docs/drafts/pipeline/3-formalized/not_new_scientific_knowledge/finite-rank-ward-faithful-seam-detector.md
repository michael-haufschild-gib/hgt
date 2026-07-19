# Finite-rank Ward faithfulness and Sonin seam-energy reflection

## Status

- Stage: formalised in Lean 4.
- Classification: not new standalone scientific knowledge.  The result is a dependency-closing
  synthesis of the finite-rank Ward pairing, Hilbert--Schmidt positive-definiteness, the exact
  projection-commutator/off-diagonal energy law, and the Fourier-reflected Sonin cutoffs.
- Scope: unconditional operator identities.  No assertion identifies the abstract polynomial
  torsion-seam witness with the actual semilocal Sonin source action.

## Corpus audit

The live tree already proves:

1. `finiteRankCutoffWardForm_self_eq_hsNormSq`: the diagonal finite-packet Ward value is the
   Hilbert--Schmidt norm square of its cutoff commutator;
2. `ContinuousLinearMap.hsNormSq_eq_zero_iff`: Hilbert--Schmidt norm square is positive definite;
3. `hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint`: for an orthogonal cutoff and a
   self-adjoint source, total commutator energy is twice the one-way crossing energy;
4. `finiteRankCutoffWardTrace_conjugate_involution` and the concrete even Fourier/indicator
   reflection laws;
5. `SoninSeamDefect` and `CutoffTorsionSeam`: the pinned presentation commutator is Fitting-trace
   blind, while the surviving polynomial cutoff witness remains explicitly abstract and is not the
   actual semilocal Sonin action.

No live theorem converts the diagonal Ward value into the exact proposition that the packet
preserves the cutoff, nor joins that faithful value to the one-way Sonin boundary corner.

## General law

Let `H` be a complete complex Hilbert space, let `e : H -> H` be bounded, and let

`P = sum_i c_i |x_i><y_i|`

be a finite-rank packet.  Define

`W_e(P,Q) = <[P,e],[Q,e]>_HS`, where `[P,e] = P e - e P`.

Then

1. `W_e(P,P) = ||[P,e]||_HS^2`;
2. `W_e(P,P) = 0` if and only if `[P,e] = 0`, equivalently `P e = e P`;
3. `Re W_e(P,P) > 0` if and only if `P e != e P`.

Thus the diagonal Ward value is a faithful scalar detector of the finite packet modulo the cutoff
commutant.  This strengthens nonnegativity to an exact kernel classification and discharges the
value-to-proposition interface.

## Projection seam law

Assume first only that `e` is an orthogonal projection.  Write

`L_e(P) = (1-e) P e` and `U_e(P) = e P (1-e)`.

For every Hilbert--Schmidt `P`, the two corners are Hilbert--Schmidt and orthogonal in the
Hilbert--Schmidt pairing.  Therefore the source-self-adjointness-free general law is

`W_e(P,P) = ||L_e(P)||_HS^2 + ||U_e(P)||_HS^2`.

It follows that `W_e(P,P)=0` exactly when both directional crossings vanish.  If `P` is additionally
self-adjoint, the two corners are adjoints and have equal energy, so the law reduces to

`W_e(P,P) = 2 ||L_e(P)||_HS^2`.

Consequently `W_e(P,P)=0` if and only if `L_e(P)=0`, and this is also equivalent to `P` preserving
the cutoff decomposition.  For real diagonal packets

`P = sum_i r_i |x_i><x_i|`, `r_i in R`,

self-adjointness and Hilbert--Schmidt regularity are automatic.

## Sonin value reflection

Let `A_a` be the concrete even indicator cutoff, `F` the even Fourier involution, and
`B_a = F A_a F` the even Fourier cutoff.  For every complex finite packet `P`, put
`P^F = F P F`.  Simultaneous involutive conjugation gives the general reflected law

`W_{B_a}(P^F,P^F) = W_{A_a}(P,P)`

`= ||(1-A_a) P A_a||_HS^2 + ||A_a P (1-A_a)||_HS^2`.

This value vanishes exactly when both physical directional crossings vanish.  If `P` is a real
diagonal packet, it is self-adjoint and the reflection sharpens to

`W_{B_a}(P^F,P^F) = W_{A_a}(P,P) = 2 ||(1-A_a) P A_a||_HS^2`.

This is an exact value-reflection law: the Fourier-side diagonal Ward value is the physical-side
one-way boundary energy.  It is hypothesis-free after choosing the concrete Sonin cutoffs and real
diagonal packet.

## Hostile audit

- The law is not an RH criterion.  It detects whether the chosen finite packet crosses the actual
  Sonin cutoff, but no theorem here identifies a canonical prime--Gamma packet whose crossing
  vanishing or sign is equivalent to the Riemann hypothesis.
- The polynomial torsion-seam witness cannot be substituted for that missing source.  The live
  module explicitly says it is an abstract existence witness, and its scalar pinned commutator is
  Fitting-trace blind.
- The factor `2` requires self-adjointness of the source and orthogonality of the cutoff; without
  those conditions the faithful full-commutator law remains valid, but a single corner need not
  determine the other.
- The result is standard operator geometry rather than novel science.  Its value is the exact
  formal interface: signed Ward values, Hilbert--Schmidt energy, cutoff commutation, boundary
  crossing, and Sonin Fourier reflection become one dependency-closed law.

## External primary-source audit

- Burnol, *The Explicit Formula and the conductor operator* (1999), supplies the local conductor
  and Fourier-dual operator setting.
- Burnol, *Sur certains espaces de Hilbert de fonctions entieres...* (2001), supplies the Sonine
  space and zeta-zero carrier context.
- Connes--Consani, *The Scaling Hamiltonian* (2019), discusses Sonine cutoffs and positive
  projection-corner operators in the attempted Weil-positivity route; it also makes clear that
  positivity alone does not close the source-to-RH implication.

## Remaining scientific core

Construct, from the actual prime--Gamma source rather than an arbitrary finite packet, a canonical
Sonin boundary action whose faithful crossing value has a proved orientation relation to the Xi
divisor.  That source-action theorem is not present in the corpus and is not assumed here.

## Lean surface and verification

- `HTGeometry.FiniteRankCutoffWardTrace`
  - `adjoint_finiteRankProbe_ofReal_self`
  - `finiteRankCutoffWardForm_self_eq_zero_iff`
  - `finiteRankCutoffWardForm_self_eq_zero_iff_commute`
  - `finiteRankCutoffWardForm_self_re_pos_iff_not_commute`
- `RHTower.SoninFiniteRankWardBoundaryEnergy`
  - `hsNormSq_commutator_eq_boundary_sum_of_hilbertSchmidt`
  - `finiteRankCutoffWardForm_self_eq_boundary_energy_sum`
  - `finiteRankCutoffWardForm_self_eq_zero_iff_boundaries`
  - the hypothesis-free even-indicator two-corner value and zero interfaces
  - the arbitrary-packet even-Fourier/physical two-corner value reflection and zero interface
  - `finiteRankCutoffWardForm_self_eq_two_mul_crossBoundary`
  - `finiteRankCutoffWardForm_self_eq_zero_iff_crossBoundary`
  - the hypothesis-discharged even-indicator value and zero interfaces
  - the concrete even-Fourier/physical-boundary value reflection and zero interface

Targeted build:

`lake build GaloisForLFunctions.HTGeometry.FiniteRankCutoffWardTrace GaloisForLFunctions.RHTower.SoninFiniteRankWardBoundaryEnergy`

Result: success.  The key declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
The generated declaration maps were refreshed.  A first
`scripts/formal_tools.py lint --check-generated` pass succeeded; the final replay was stopped only
by the unrelated concurrent module `HTGeometry.NevanlinnaKernelRigidity` being unreachable from the
HT umbrella.  No full Lean build was run.

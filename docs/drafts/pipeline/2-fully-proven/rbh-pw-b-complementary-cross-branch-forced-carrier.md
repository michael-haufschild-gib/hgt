# RBH / PW-B complementary cross-branch forced carrier

- **ID:** RBH-PW-B-CBFC
- **Stage:** 2-fully-proven
- **Type:** exact bridge theorem

## Statement

Let `H₊, H₋` be the literal full angular responses on the two physical source
branches.  Their product `B = H₊H₋` has complementary clock `-6`; at its clock
parameter `χ = 20`, it obeys the exact forced equation

`ΔB = χB + Fcross`,

where

`Fcross = crossBranchAngularForcing + (crossBranchAngularParameter - χ)B`.

The covector `Vcross = coexact B` is smooth and divergence-free.  No
same-branch contact, homogeneous eigenfield replacement, or omitted
cross-gradient is used.

With `Jcross` defined from this displayed scalar defect, the actual stream
operator also obeys

`roughLaplacian(Vcross) + Vcross = 20 Vcross + Jcross`.

The curvature shift is therefore accounted for at vector level; `Jcross` is
not a free metric source.

The literal bulk metric is now fixed as

`streamMetricField(-6, a²b²/64, false, Vcross)`.

It is an actual exterior `C²` metric field and all sixteen linearized
cosmological Einstein components equal its displayed stream current tensor.
The normalization is inherited from the exact full incoming-horizon current.
The tensor's actual angular master slot is exactly `20 Vcross + Jcross`.

## Proof

The literal product rule gives

`Δ(H₊H₋) = (parameter₊ + parameter₋)H₊H₋ + crossBranchAngularForcing`.

Add and subtract `χH₊H₋`.  Coexactness gives divergence zero from the actual
third-order regularity of `B`, and the coexact rough-Laplacian intertwining
gives the displayed forced vector equation.  All identities are pointwise on
positive angular height.  The existing actual stream-metric jet theorem then
applies directly to `Vcross`, using its proved `C²` regularity and divergence
law, and identifies every Einstein component with the stream tensor.  Its
angular-slot identity rewrites that tensor's master operator to `20Vcross +
Jcross` exactly.

## Whole-route meaning

The same-rate scalar Peierls route is retired.  This theorem discharges the
next missing bulk object for its complementary-rate survivor: an explicit
literal cross source and divergence-free carrier at the only possible total
clock.  It discharges both scalar-to-vector and vector-to-actual-metric B2
bulk premises. It does not identify that stream tensor with the ordered
two-leg causal action/current, nor supply noncompact causal boundary
transport.

The raw full-kernel cap horizon limit is already available elsewhere in the
corpus.  Consequently the remaining incidence problem is sharper: derive an
ordered two-leg action/current transgression from the complete cap expression,
including its lift defect.  A symmetric scalar product alone cannot represent
both orders of the skew causal pairing.

## Lean status

- Direct source audit passed:
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLiteralCyclicPeierlsCrossBranchBidegree.lean`.
- Wired to `GaloisForLFunctions/RHTower.lean`; umbrella was not built.
- No `.olean` build or umbrella build was run for this new leaf.

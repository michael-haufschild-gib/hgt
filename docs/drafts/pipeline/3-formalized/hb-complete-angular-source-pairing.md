# Complete angular source integral at the physical Xi frequencies

## Mathematical statement

Write `E_u` for the literal completed-Eisenstein scalar cusp field and `mu`
for the original hyperbolic measure restricted to the modular fundamental
domain. For every Xi source `q`, let `R_q` be its complete subtracted square
residual. For every complex exponent `k`, let

`C_k = Delta_H(cutoff*y^k) - cutoff*k*(k-1)*y^k`.

The actual bilinear integrals

`J(q,u) = integral E_u R_q dmu`,

`K(u,k) = integral E_u C_k dmu`

are absolutely convergent for every complex testing parameter `u`. Both
integrands also belong to the original angular L² space. These are literal
integrals of the full fields; their values are not prescribed constants.

The complete continued source has its previously proved four-channel form

`F(q,branch,w,a;t,z) = M(w,t)R_q(z) + sum_i N_i(w,t)C_(k_i)(z)`.

Its actual angular projection is defined before any rewriting by

`P(w,t) = integral E_u(z)F(q,branch,w,a;t,z) dmu(z)`.

Lean proves absolute convergence for every complex `w` and every real `t`,
and the exact identity

`P(w,t) = M(w,t)J(q,u) + sum_i N_i(w,t)K(u,k_i)`.

All three principal cutoff commutators remain present. For nonreal `w` with
`|Re w|<2`, `P(w,.)` lies in the original radial L² space. Its actual L²
class is a norm-valued meromorphic frequency family on this band.

## Proof

The exact scalar decomposition is `E_u=A_u+T_u`, where `A_u` contains both
Weyl powers and `T_u` is the complete Fourier--Bessel tail. The corpus already
proves that every complex height power times `T_u` is bounded on every
positive-height half-strip. Applying those bounds at the two shifted Weyl
exponents proves the same weighted bound for

`E_u²-A_u² = 2A_u T_u+T_u²`.

Multiplication by any other full scalar field preserves boundedness of this
remainder. Above height three, `R_q` is exactly half that remainder. On the
compact lower part of the fundamental domain, actual smoothness gives a
bound. The finite hyperbolic measure therefore supplies angular L² admission
and absolute integrability. Each actual cutoff commutator is continuous and
vanishes above height three, so its scalar-field product has the same
admission.

Linearity of admitted integrals yields the exact four-channel decomposition.
The native radial coefficient is analytic in the required band; the three
continued cutoff coefficients are meromorphic in radial L². Constant scalar
multiplication, finite sums, and equality of the actual integral classes
transfer this meromorphy to `P`.

## Physical angular parameter

The literal scalar equation is `Delta_H E_u=(u²-1/4)E_u`. At `u=i*chi` it
therefore becomes

`Delta_H E_(i*chi)=-(1/4+chi²)E_(i*chi)`,

the separation eigenvalue of the original radial equation. For each Xi
target `r`, the capstone uses the actual physical momentum `chi=z_r/2+i/4`.
Both fundamental frequencies belong to the required nonreal band. For
every source `q`, independently of target `r`, it proves the scalar equation,
absolute angular integrability, radial L² admission, and meromorphy at both
frequencies. No endpoint, projection-value, nonresonance, or RH premise is
supplied to that capstone.

## Lean modules

- [BMWeightedSquareCuspBound](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMWeightedSquareCuspBound.lean): two weighted full-field bounds.
- [BMScalarSourcePairingAdmission](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMScalarSourcePairingAdmission.lean): four angular admission theorems.
- [BMCompleteAngularSourceProjection](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCompleteAngularSourceProjection.lean): actual integral definitions, complete integrability, and exact channel decomposition.
- [BMCompleteAngularProjectionMeromorphy](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCompleteAngularProjectionMeromorphy.lean): radial L² admission, exact class assembly, and norm-valued meromorphy.
- [BMFundamentalAngularSourcePairing](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFundamentalAngularSourcePairing.lean): original separation eigenvalue and unconditional all-Xi specialization.

## Remaining physical identification

This is a bilinear source integral over the original fundamental domain.
The local scalar eigenvalue identity does not identify a global physical
advanced/adjoint left resonance or prove its boundary conditions. Evaluating
the periods, constructing the joint outgoing inverse with its original
causal overlap, completing the radial endpoint pairing, and identifying the
physical left residue remain necessary. Neither nonvanishing nor extinction
of that full residue is asserted. Independent Hawking-clock extinction and
RH remain unproved.

## Verification

All five scratch leaves passed `lake env lean`. Each canonical module passed
its own foreground `lake build <module>` audit without Lean warnings. The
isolated audit reused 4083 existing dependency oleans and produced exactly
five new target oleans. Five installed sources and ten installed olean/ilean
artifacts were byte-verified against that audit. All five imports are wired
into the RHTower umbrella, which was not built.

The 13 new public theorems occupy 312 source lines. Their scratch-only
`#print axioms` check reports exactly `propext`, `Classical.choice`, and
`Quot.sound` for each. No old theorem axiom check, numerical experiment, or
computational proof certificate was used.

The corpus index was refreshed. Global `lint --check-generated` returned
exit code 1 solely because these 12 independently added modules were not
reachable from their area umbrellas at the time of the check:

- RHTower: `FokasLenellsSpaceDifferentiability`, `SelbergEisensteinBoundary`,
  `SelbergEisensteinBounds`, `SelbergEisensteinMass`, `SelbergEisensteinPlane`,
  `SelbergPositiveEisenstein`, `SelbergPowerCurvature`.
- HTGeometry: `FokasLenellsCorrectedDecay`, `FokasLenellsCorrectedOrbit`,
  `FokasLenellsDiagonalTest`, `FokasLenellsSecondDecay`, `FokasLenellsWeightedData`.

There was no new HB module, proof-debt, or generated-file freshness error.
Those independent modules were not modified or wired by this work. The
global gate remains incomplete; the five individual HB audits passed.

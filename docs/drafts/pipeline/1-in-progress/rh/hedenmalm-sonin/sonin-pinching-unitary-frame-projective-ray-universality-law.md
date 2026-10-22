# Sonin-pinching unitary-frame projective-ray universality law

Status: Stage 3 — formalized in Lean 4; final umbrella audit pending  
Lean target: `GaloisForLFunctions.RHTower.SoninPinchingUnitaryFrameProjectiveRayUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`SoninLogPinchingProjectiveRayUniversalityLaw` puts every pinched Sonin observable on a physical
zero locus and a zero projective scattering ray, but states this only in the native Sonin frame.

`FiniteClockUnitaryReferenceFrameMasterObservabilityUniversalityLaw` proves that physical kernels
are transported exactly by simultaneous two-sided unitary conjugation.  Its inner-product
calculation also supplies the missing invariance of the two-vector projective Gram energy.  No
corpus theorem transports the Sonin projective-ray certificate through an arbitrary unitary
reference frame.

## Statement

Let `Y` be the two-outcome pinching of a Sonin observable, `V` a two-sided unitary frame map, and
`ψ` a normalized physical Sonin state.  Then:

1. `V(Yψ)` is physical for the conjugated scattering constraint
   `V S V† - 1`;
2. projective Gram energy between `V(Yψ)` and its conjugated-scattering image equals the native
   Sonin projective Gram energy;
3. both energies vanish.

Thus the pinched Sonin physical/projective ray is reference-frame invariant, not an artifact of
the native logarithmic coordinate frame.

## Dependency-closed proof

1. Native Sonin pinching universality gives physicality of `Yψ` and zero projective energy of
   `(Yψ, S(Yψ))`.
2. `V†V = 1` makes `V` preserve squared norms and inner products, hence the complete projective
   Gram determinant.
3. The same identity gives
   `(V S V†)(V(Yψ)) = V(S(Yψ))`.
4. Two-sided physical-state conjugation transports the kernel of `S - 1`.
5. `VSV† - 1 = V(S - 1)V†` follows from `VV† = 1`.
6. Rewrite the transformed projective energy by steps 2–3 and use native vanishing.

No computation or new spectral premise is introduced.

## Novelty audit

Corpus audit: native Sonin projective-ray vanishing and generic two-sided physical transport exist
separately.  Projective-energy covariance and the conjugated Sonin zero locus are absent.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

- Exact source check passed:
  `lake env lean GaloisForLFunctions/RHTower/SoninPinchingUnitaryFrameProjectiveRayUniversalityLaw.lean`.
- Wired into `GaloisForLFunctions.RHTower`.

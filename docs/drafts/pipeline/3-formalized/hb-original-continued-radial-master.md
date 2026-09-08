# HB: original forced radial equation at fundamental Xi QNMs

- **Stage:** formalized in Lean 4.
- **RH:** unproved. Full joint continuation, physical left pairing and independent extinction remain open.
- **Validation:** eight individual canonical leaf builds; 31 new public theorems; 691 source lines.

## Exact result

The native response constructed in
[the endpoint continuation](hb-original-fundamental-qnm-endpoint-continuation.md)
satisfies its original forced radial equation after continuation. For nonreal
`w` with `Re w > -2`, every interior radius `b`, and arbitrary fixed source and
angular parameters, the equation holds in a punctured frequency neighborhood:

```text
radialJet (I*u) chi b
  (continuedResponse s chi a J K b u)
  (deriv (fun t => continuedResponse s chi a J K t u) b)
  (deriv (deriv (fun t => continuedResponse s chi a J K t u)) b)
  = sqrt(1-b) * continuedSourceProfile s a J K u b / 2.
```

The derivatives are actual real radial derivatives. The source retains its
fixed smooth-onset correction and original source pole. The full Gamma
connection coefficient supplies the Green normalization. No endpoint admission,
continuation, numerator nonvanishing or nonresonance premise is supplied to the
germ theorem.

`continuedResponse_allXi_fundamental_original_equation` proves this germ identity
at both fundamental physical QNM frequencies for every Xi copy. The previously
proved meromorphy and equality to the original Green response in its convergence
chamber continue to apply to this same response.

## Dependency-closed argument

1. The actual Gauss formal series has radius at least one for all parameters.
   A terminating parameter gives infinite radius; otherwise the corpus's radius
   theorem gives radius one. Both spatial jets therefore exist throughout the
   unit disk. The horizon Gauss ODE holds for nonreal frequency, where its
   denominator avoids negative natural numbers. The outer denominator is the
   fixed positive number `3/2`. Dressing and coordinate reversal yield the
   original physical homogeneous radial equations.
2. The exact coefficient identity
   `(n+1) A[n+1](a,b,c) = (a*b/c) A[n](a+1,b+1,c+1)`
   identifies the first derivative-series sum with the shifted Gauss sum. This
   retains terminating numerators. Local continuity bounds and denominator pole
   separation feed the established dominated-sum holomorphy theorem. Hence the
   actual first physical spatial jets are analytic in frequency off the real axis.
3. The original spatial Wronskian and `-connection/2` are analytic on each
   nonreal half-plane. Each half-plane intersects the original convergence
   chamber. The identity theorem extends their proved chamber equality across
   both half-planes, including connection zeros. The chamber also proves that
   the connection is not identically zero; its zeros are isolated.
4. For the restored first-subtraction Mellin moment,
   `M(b,w) = F(w,0)*b^(w+1)/(w+1) + integral_0^b t^w*(F(w,t)-F(w,0))`,
   the existing first-difference bound proves remainder integrability when
   `Re w > -2`. FTC and differentiation of the restored term give exactly
   `dM/db = b^w*F(w,b)`. The source-weighted outer branch is continuous through
   the true outer endpoint, so its moment has the original lower-endpoint
   derivative at every frequency.
5. Differentiating the two-moment response cancels the first moving-endpoint
   terms. Its second derivative retains the source jump. The homogeneous
   equations and exact Wronskian reduce that jump to the literal forcing.
   Away from connection zeros this is a pointwise identity. Isolated zeros give
   the asserted punctured germ without a supplied nonresonance assumption.
6. The corpus's unconditional strict Xi strip and nonzero real spectral
   coordinate place both fundamental QNM frequencies in the nonreal strip
   `Re w > -2`. This supplies the all-Xi specialization.

## Formal modules

Under `formal/GaloisForLFunctions/HTGeometry/`:

- `HypergeometricSpatialJets.lean`
- `HypergeometricLocalFamilies.lean`
- `FirstEndpointMellinSpatial.lean`

Under `formal/GaloisForLFunctions/RHTower/`, with prefix `ThetaCuspHawking`:

- `BMLaplaceSpatialODE.lean`
- `BMLaplaceJetHolomorphy.lean`
- `BMLaplaceWronskianContinuation.lean`
- `BMLaplaceMomentSpatial.lean`
- `BMLaplaceContinuedForcedODE.lean`

Each canonical module passed its own foreground `lake build <module>` in an
isolated audit package reusing 3,998 existing dependency oleans. Exactly eight
new oleans were built. All 31 new public theorem axiom checks use only
`propext`, `Classical.choice`, and `Quot.sound`. All 16 installed olean/ilean
artifacts match the audited bytes. Modules are wired into their area umbrellas;
no umbrella or full build was run. No numerical experiment or computational
certificate enters these proofs.

Global `lint --check-generated` reports no errors in these leaves or generated
index drift. Its remaining errors are the unrelated, concurrently unwired
`HTGeometry.FokasLenellsScatteringContinuity` and
`HTGeometry.FokasLenellsSpectralContinuity` modules; existing large-file warnings
also remain. Those files are outside this change's scope.

## Remaining physical obligation

Transport this actual radial equation through the tortoise chart into the
original principal responses, their full-square lift subtraction, and all three
cutoff commutators. Establish the weighted joint-domain continuation of the
complete forcing and response, then identify the physical advanced/adjoint left
residue. This radial germ theorem does not establish that joint-domain result,
pole survival, a physical left-source projection, spin-two/AIME identification,
or Hawking-clock extinction. Higher overtones still require further endpoint
subtractions.

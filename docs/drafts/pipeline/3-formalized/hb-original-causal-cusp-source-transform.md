# HB: the original causal cusp-source transform

- **Stage:** 3-formalized.
- **Result:** the actual principal causal Laplace profiles equal the original endpoint Green corrections. The complete causal spatial source has exactly `cuspResidualVector` as its Bochner transform on one explicit nonempty right half-plane.
- **RH:** unproved. This identifies the original source; it does not establish left-QNM continuation or independent Hawking-clock extinction.
- **Frontier map:** read-only.

For every literal Xi zero copy `q`, physical branch and amplitude `a`, put
`T(w) = onsetTransform (2*physicalRate q branch) w`. For each of the three
principal channels, the actual norm-convergent causal transform satisfies

```
principalLaplaceProfile q branch a i w hw x
  = principalDifference q branch w a T(w) i x,   x < 0.
```

The frequency lies in the intersection of the proved causal growth half-plane
and `PrincipalChamber q w`. The equality also holds for the original L² class,
almost everywhere in the original negative-ray measure.

Set `C(q) = max (causalPrincipalThreshold q) (principalThreshold q)`.
For every `Re(w)>C(q)`, the complete original spatial source satisfies

```
integral_{tau>0} exp(-w*tau) • causalCuspSourceVector q branch a tau
  = cuspResidualVector q branch w a T(w) hc.
```

The integral is absolutely convergent in the original joint Hilbert norm.
The finite real threshold makes this a nonempty open right half-plane.
The native squared-scalar remainder, all three principal powers, angular
cutoff commutators, radial horizon factors and original onset are retained.

The proof closes the endpoint comparison as follows.

1. Compact Schwartz integration by parts needs no global growth condition on
   an auxiliary primitive. Subtract a double primitive of the continuous weak
   second-derivative density. Two applications of the corpus local
   distributional constant-function theorem classify the remainder as affine.
   Local differentiation then supplies the actual classical spatial jets.
   Applied to the already proved transformed weak equation, this gives the
   original classical radial equation for the causal profile.
2. Transport the proved Green endpoint limit through the original horizon
   coordinate. The exact full-square lift vanishes there, so both compared
   profiles have zero negative-ray endpoint trace.
3. The causal profile's proved Sobolev order two gives an L¹ Fourier
   representative and hence a global bound on its actual continuous
   representative. The Green endpoint limits give a continuous compact-radius
   extension and a uniform bound. The lift is bounded by its original
   exponential factor times a continuous compact-radius profile.
4. Their actual difference `F` satisfies the homogeneous equation, has zero
   endpoint trace and is bounded on the whole negative ray. The original
   potential is bounded there. Applying the corpus real Landau inequality to
   both complex components gives `||F'|| <= 4*C+M` on every unit interval
   sufficiently far toward the horizon, where `||F||<=C` and `||F''||<=M`.
   No derivative phase or horizon boundary condition is supplied.
5. Transport both original homogeneous modes and their two jets. Their exact
   tortoise Wronskian is `W(H,N)=-connection`, which is nonzero in the original
   chamber. The actual horizon mode `H` and its first tortoise jet tend to zero
   at negative infinity. This follows from the proved power limit, the actual
   analytic Gauss jets at radius zero, and the bounded compact-radius factor.
6. `W(F,H)` is constant. Bounded actual jets of `F` and decaying actual jets of
   `H` force it to be zero. Write `A=W(F,N)`, also constant. The exact Cramer
   identity gives `F*(-connection)=H*A`. At the physical endpoint, `F` tends
   to zero and `H` tends to the nonzero connection coefficient. Thus `A=0`
   and `F=0` throughout the original negative ray.
7. Transfer the pointwise identity to the original L² transform class. The
   actual radial cutoff operator retains the horizon multiplier and negative
   restriction. Product-measure compatibility identifies each original angular
   channel. Adding all three channels to the already identified native source
   proves the complete Bochner transform identity.

The capstones are
[`principalLaplaceProfile_eq_principalDifference`](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMJointSourcePrincipalGreenIdentification.lean),
[`causalCuspSourceVector_original_transform`](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMJointSourceCausalCuspSourceIdentification.lean),
and the reusable
[`negative_homogeneous_eq_zero`](../../../../formal/GaloisForLFunctions/HTGeometry/NegativeWronskianUniqueness.lean).

Validation: 14 new leaves, 45 public theorems and 1,014 source lines. Each new
canonical module is audited individually with `lake build <module>` against
existing dependency artifacts in an isolated package. All 45 new theorem axiom closures are
checked separately in scratch and contain only `propext`, `Classical.choice`
and `Quot.sound`. All 14 individual canonical audits pass without warnings.
All 28 installed artifacts are byte-identical to those audits, and every new
leaf has exactly one direct import in its area umbrella. No umbrella or full build, numerical experiment,
certificate, added axiom or unfinished proof is used in this construction.
`formal_tools.py lint --check-generated` passes with no errors; its 141
existing large-file warnings concern other corpus files.

The next physical obligation is the original joint causal response to this
now-identified complete time source. Its convolution, metric finite
propagation, modular patching and constrained Einstein-sector identifications
must feed the physical left-QNM pairing. Independent Hawking-clock extinction
and the RH conclusion remain open. A right-half-plane source identity does not
continue the response inverse across its physical poles.

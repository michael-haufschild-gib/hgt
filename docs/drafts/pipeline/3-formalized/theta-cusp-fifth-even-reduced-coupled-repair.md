# Reduced coupled repair of the fifth even theta source

- **Stage:** 3-formalized; canonical checks and standard-axiom audits complete.
- **Wall:** Σ6; integrated rank-nine positivity remains open.
- **Claim:** `(C,D)=(10⁷,10¹²)` gives a positive definite origin, an origin neighborhood and a cofinal tail; it preserves every mixed entry and passes both established scale-seven directional tests.

Use `u₁=(0,0,1,420,0)`, `u₂=(0,0,0,1,1568)` and the actual source
`R(x)=H₅(x)+G(x)(C u₁u₁ᵀ+D u₂u₂ᵀ)`.
The complete normalized origin moments are `M²p_j(X)`, with
`19.1<X<19.2`, and `G(0)=3M²p₀(X)`.
After the positive first two coordinates, the denominator-cleared Schur
matrix is `S=dT−Bᵀadj(A)B`, where `d=det A>0`.

For `(C,D)=(10⁷,10¹²)`, all three leading minors of `S` are strictly
positive throughout `19.1≤X≤19.2`. Exact shifted-polynomial certificates
for these three statements pass Lean's standard-axiom audit. Sylvester
and Schur elimination therefore give the actual full origin's strict sign.

Continuity supplies an origin neighborhood. The proved limit
`G/(f₁²q⁴)→0` preserves the positive Gaussian tail for this fixed pair.
Both coefficients are positive, so the literal weighted flux correction
preserves these signs at every positive aperture. For `0<a<1/2` it is
integrable with zero integral in every entry.

At scale seven the eighth-degree witness is unchanged. The sixth-degree
load is `10⁷+10¹²/176400<16·10⁶`, below both proved capacities.
Thus both native and weighted sixth-degree tests are strictly positive.
A further [Schur direction](../5-failed/theta-cusp-fifth-even-reduced-coupled-schur-obstruction.md)
refutes the full matrix's scale-seven sign. The origin and tail results
remain valid.

Lean: `EvenFiveOrigin.coupledRepair_reduced_zero_posDef`,
`EvenFiveCoherent.reduced_coupledRepair_posDef_near_zero`, and
`reduced_coupledWeightedRepair_compact_gap`, together with the proved
integral-preservation and sixth-degree capacity theorems, in
`ThetaCuspSections/FifthEvenOriginObstruction.lean` and
`ThetaCuspSections/FifthEvenCoherentRepair.lean`. Both modules are imported
by their owner umbrella. The audited dependencies use only `propext`,
`Classical.choice`, and `Quot.sound`.

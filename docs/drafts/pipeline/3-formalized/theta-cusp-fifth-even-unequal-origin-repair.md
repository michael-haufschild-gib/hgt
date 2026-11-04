# Unequal coupled loads at the fifth even theta origin

- **Stage:** 3-formalized; canonical checks and standard-axiom audits complete.
- **Wall:** Σ6; global rank-nine sign remains open.
- **Claim:** `H₅(0)+G(0)(10⁸u₁u₁ᵀ+10¹²u₂u₂ᵀ)` is positive definite,
  where `u₁=(0,0,1,420,0)` and `u₂=(0,0,0,1,1568)`.

Use the actual normalized origin moments `m_j=M²p_j(X)`,
`19.1<X<19.2`, and `G(0)=3M²p₀(X)`. The native head
`A=[[p₀,p₁],[p₁,p₂]]` is positive definite. Set `d=det A>0`,
`B=[[p₂,p₃,p₄],[p₃,p₄,p₅]]`, and let `T` be the normalized
last three rows and columns after the stated correction.

The denominator-cleared Schur matrix is `S=dT−Bᵀ adj(A)B`.
Its three leading minors are strictly positive on `19.1≤X≤19.2`.
For the first minor this is the already checked `C=10⁸` certificate,
independent of the second load. Exact shifted-polynomial certificates
check positivity of the second and third minors for `(C,D)=(10⁸,10¹²)`.
Sylvester's criterion gives `S≻0`; since `d>0`, Schur elimination gives
positivity of the actual five-dimensional matrix.

The actual origin theorem `EvenFiveOrigin.coupledRepair_unequal_zero_posDef`
passes its canonical Lean check and standard-axiom audit. The
[equal-coefficient route](../5-failed/theta-cusp-fifth-even-common-coupled-obstruction.md)
is refuted globally, including the weighted representative.

The same explicit pair also has a dependency-closed origin-and-tail proof.
Each coupled load is positive semidefinite, supported in indices at least two,
and annihilates the established scale-seven vector. The proved limit
`G/(f₁²q⁴)→0` therefore preserves the positive Gaussian tail for every fixed
pair. Continuity gives an origin neighborhood. Adding the literal flux
derivative preserves every mixed integral for `0<a<1/2`. The nonnegative
aperture slack preserves positivity near zero and cofinally for every
positive aperture.
The unequal-coefficient extensions are formalized as
`EvenFiveCoherent.coupledRepair_posDef_near_zero`,
`coupledRepair_posDef_eventually`, `coupledWeightedRepair_integral`, and
`coupledWeightedRepair_compact_gap`. `coupledRepair_witness_energy` and
`coupledWeightedRepair_witness_energy` preserve the witness exactly at
every center. Every fixed real pair preserves the Gaussian tail; positive
coefficients additionally preserve aperture slack.

Lean: `ThetaCuspSections/FifthEvenOriginObstruction.lean` and
`ThetaCuspSections/FifthEvenCoherentRepair.lean`. Canonical checks pass; these results use only
`propext`, `Classical.choice`, and `Quot.sound`. Both modules are in the
owner umbrella. The [sixth-degree obstruction](../5-failed/theta-cusp-fifth-even-large-coupled-load-obstruction.md)
excludes full positivity for this fixed pair; the origin-and-tail theorem
remains valid.

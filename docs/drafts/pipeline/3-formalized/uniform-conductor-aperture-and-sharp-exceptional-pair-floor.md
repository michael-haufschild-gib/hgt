# Uniform conductor aperture and sharp exceptional-pair floor

- **ID:** A100
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every `κ>2` admits an absolute `C≥0` such that `primeMass a + primeMass(a/2) + archConstant χ ≤ κ exp(a)+C`, uniformly in conductor and character. Thus `4 exp(a)+C≤log q` forces nonnegativity of the primitive twisted zero form on real C² packets of aperture `a`. For `δ,a>0`, the simple real-pair form has exact mass-floor coefficient `2 pairEnergy(δ,a)=sinh(2δa)/δ−2a`, even when restricted to C² packets supported in `[-a,a]`. Unit-mass packets approach this lower edge; actual zero-pair contributions scale by multiplicity.

## Proof

The sharpened prime mass divided by `exp(a)` tends to `2`. Monotonicity bounds the remaining range, and the two possible archimedean constants have an absolute common bound. Substitution into the aperture inequality gives the uniform quantitative lower bound and coefficient-four consequence.

The real-pair form equals twice the cosh-moment square minus twice the sinh-moment square. Cauchy–Schwarz bounds the negative square by `pairEnergy(δ,a)∫f²`. For the converse, multiply `sinh(δu)` by even smooth cutoffs equal to one on `[-a′,a′]`, with `a′↑a`. Oddness kills the cosh moment, while the sinh moment is at least `pairEnergy(δ,a′)` and the mass is at most `pairEnergy(δ,a)`. Continuity proves sharpness; rescaling gives unit mass. The literal zero-pair identity supplies the multiplicity factor.

## Formalization

- `AbsoluteGeometryOfSpecZ/AUniformConstantForTheTrivialConductorAperture.lean`: `exists_uniform_conductor_aperture_cost`, `exists_uniform_twistedZeroSum_aperture_margin`, `exists_uniform_trivial_conductor_aperture`.
- `AbsoluteGeometryOfSpecZ/TheExceptionalSquareHasASharpSmoothFloor.lean`: `realPairForm_mass_floor_iff`, `exists_unit_realPairForm_near_lower_edge`, `real_zero_pair_eq_mult_realPairForm`, `exists_unit_real_zero_pair_near_lower_edge`.
- Both modules passed Lean checks and are wired into the programme umbrella. Axiom audits omitted as requested.

The smooth-packet lower edge is an infimum, not an asserted smooth minimizer. The pair statement concerns its two zero summands, not the contributions of other zeros.

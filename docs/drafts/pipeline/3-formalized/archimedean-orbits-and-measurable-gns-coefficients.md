# Archimedean dilation orbits and measurable GNS coefficients

- **ID:** archimedean-orbits-and-measurable-gns-coefficients
- **Stage:** 3-formalized
- **Type:** Supporting analysis; uncredited
- **Source:** APD successor visibility classification
- **Statement:** The cyclic rational dilation orbit of a finite archimedean measure extends uniformly continuously to every real logarithmic scale. Borel positive-definite functions have measurable matrix coefficients on their whole GNS spaces.

## Exact mathematical content

Let φ be positive definite on Aff(ℚ), and suppose its positive dilation
restriction is the characteristic function of a finite positive real measure ν:
`φ(D(u)) = ∫ exp(i γ log u) dν(γ)` for every positive rational unit u.
In the original GNS space, with cyclic vector v, there exists a uniformly
continuous map V:ℝ→H such that

- `V(log u)=π(D(u))v` for every positive rational u;
- `⟨V(s),V(t)⟩=charFun ν(t−s)` for every real s,t;
- `‖V(t)‖²=ν(ℝ)` for every real t.

Separately, let Φ be a positive-definite function on an arbitrary group G,
and u:A→G a parameter map from a measurable space. If every function
`a↦Φ(g⁻¹u(a)h)` is measurable, then every scalar matrix coefficient
`a↦⟨x,π(u(a))y⟩` in the completed GNS space is measurable. In particular,
a Borel positive-definite function on a group with continuous multiplication
has Borel GNS matrix coefficients. No separability of the GNS space is used.

The auxiliary logarithmic affine group has coordinates `(b,t)`, multiplication
`(b,t)(c,s)=(b+exp(t)c,t+s)`, and exact quotient
`(b,t)⁻¹(c,s)=(exp(−t)(c−b),s−t)`.

## Paper proof

For a Hilbert curve with stationary kernel `⟨v_i,v_j⟩=K(t_j−t_i)`, every
squared norm equals `Re K(0)`, and
`‖v_i−v_j‖²=2 Re K(0)−2 Re K(t_j−t_i)`.
Continuity of K at zero therefore gives uniform continuity. Equal parameter
values have zero Hilbert distance, so the curve descends even if the parameter
map is not injective. Completeness extends it uniquely from the dense range;
continuity and product density retain the full inner-product identity.

For the rational dilation orbit, unitarity and the GNS coefficient identity
give precisely the stationary kernel `charFun ν`. Positive rational logarithms
are dense by the existing rational approximation to exp(t), and finite ν gives
continuity of its characteristic function. The generic extension applies.
Its diagonal identity at zero yields the stated mass.

A pairing of two finite pre-GNS vectors with π(u(a)) is a finite sum of
`conj(x_g) Φ(g⁻¹u(a)h) y_h`; hence it is measurable. Completion density gives
sequences of such finite vectors converging to arbitrary x,y. For each a,
the isometry π(u(a)) and continuity of the Hilbert inner product give convergence
of the scalar coefficients. Pointwise limits of measurable complex functions
are measurable. For Borel Φ, continuity of the two fixed group multiplications
supplies the translated-coefficient hypothesis.

The affine-coordinate identities follow directly from exp(t+s)=exp(t)exp(s).

## Declaration map

- `HTGeometry.StationaryHilbertCurvesExtendFromDenseParameters`:
  `uniformContinuous_of_stationary_inner`,
  `exists_stationary_hilbert_extension`,
  `exists_stationary_hilbert_extension_indexed`.
- `HTGeometry.LogarithmicAffineGroup`:
  `LogAffineGroup`, `LogAffineGroup.inv_mul_coordinates`.
- `APD.TheArchimedeanDilationOrbitExtendsToRealScales`:
  `denseRange_logPos`, `inner_rational_dilation_orbit`,
  `exists_real_dilation_orbit`.
- `APD.TheGNSRepresentationInheritsWeakMeasurability`:
  `inner_preGNS_gnsRep`, `exists_preGNS_seq_tendsto`,
  `measurable_inner_gnsRep`, `measurable_gnsRep_coefficient`.

## Verification status

All four actual modules passed individual `lake --old env lean` source checks;
main axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
The HTGeometry and APD umbrellas include the modules; no umbrella was compiled.
Only the stationary-curve dependency olean was built, for its orbit importer.

## Scope and significance

These are classical supporting lemmas, not accepted RH contributions. They do
not construct the full real-affine extension, prove its Borel property, or
establish translation regularization or absolute continuity of its visible
spectrum. In particular the generic measurability theorem does not discharge
measurability of an as-yet unconstructed affine coefficient. APD necessity
remains a separate conjecture, deferred at its significance gate. Accepted
count remains 0 / 250.

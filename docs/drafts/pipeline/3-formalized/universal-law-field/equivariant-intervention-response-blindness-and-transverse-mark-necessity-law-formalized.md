# Equivariant intervention-response blindness and transverse-mark necessity — Lean certification

- **ID:** ULF-EIR-1
- **Paper card:**
  `equivariant-intervention-response-blindness-and-transverse-mark-necessity-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveEquivariantResponseBlindness`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Model

Theorem 1 is stated on a genuine smooth manifold, not on a linear model: `X` is a charted space over
a model with corners `I`, `Q` over `J`, `P : X → Q` is the doctrine map, and an intervention is a
section `V : ∀ x, TangentSpace I x`.  The response is mathlib's `mfderiv`, so the chain rule used is
the manifold chain rule `mfderiv_comp`, not a normed-space `fderiv` computation.

## Certified declarations

### Theorem 1 — equivariant response blindness

- `doctrineResponse I J P V x = mfderiv I J P x (V x)` — equation (3);
- `mfderiv_comp_eq_of_invariant` — the naturality identity `dP_{Φx} ∘ Φ_* = dP_x`, from
  `P ∘ Φ = P` and the manifold chain rule;
- `doctrineResponse_eq_of_equivariant` — equation (4) for one symmetry;
- `doctrineResponse_smul` — equation (4) for a group `G` acting by smooth maps, with an invariant
  doctrine map and an equivariant field;
- `responseCoframe`, `responseCoframe_smul`, `responseCoframe_constant_on_orbit` — an arbitrary
  indexed family of equivariant interventions has combined first response constant on `G`-orbits;
- `orbitResponseCoframe`, `orbitResponseCoframe_mk` — the combined response is literally a function
  on `MulAction.orbitRel.Quotient G X`.  This is the exact content of "it cannot identify a hidden
  coordinate along those orbits".

### Corollary 2 — necessity of an escape

`separation_forces_escape` is the exact contrapositive: if the first-order coframe separates `x`
from `g • x`, then

1. the doctrine map is not `G`-invariant, **or**
2. some member of the family is not `G`-equivariant, **or**
3. the action is not smooth, **or**
4. the doctrine map is not differentiable.

The card's escape route 4 — a higher or nonlocal response — is exactly the statement that the
separating datum is not of the certified form `dP_x(V x)`; route 2, a mark with a proper stabilizer,
is the replacement of `G` by a subgroup, under which the theorem still applies with smaller orbits.

### Non-sufficiency, certified concretely

One fixed model carries both halves: `X = Q = ℂ`, `G = Circle` acting by rotation, doctrine map
`circleDoctrine z = z · conj z`.

- infrastructure: `rotCLM`, `rot_eq`, `mdifferentiable_rot`, `mfderiv_rot`, `circle_mul_conj`,
  `hasFDerivAt_circleDoctrine`, `mdifferentiable_circleDoctrine`, `circleDoctrine_smul`,
  `mfderiv_circleDoctrine`;
- `radialField z = z` is equivariant (`radialField_equivariant`) and its response
  `z · conj z + conj z · z` is orbit-constant — Theorem 1 in action;
- `conjField z = conj z` is **not** equivariant (`conjField_not_equivariant`) and **does** separate:
  `conjField_response_one` gives `2` at `1`, `conjField_response_smul_one` gives `−2` at the quarter
  turn of `1`.  Bundled as `circleModel_escape_separates`;
- `tangentModulatedField z = (Re z) · i · z` is **equally** non-equivariant
  (`tangentModulatedField_not_equivariant`) and yet `doctrineResponse_tangentModulatedField` proves
  its first response identically zero, so it separates nothing.  Bundled as
  `circleModel_escape_not_sufficient`.

So the escape routes are certified necessary and certified insufficient, on the same model.

### §2 exact radial-source instantiation — reuse, not rebuild

The graded source, the radial gauge family, the identity-sector trace, the Kummer derivation and its
cyclic one-cocycle already exist in `HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness`
(`gradeDiag`, `gradeGauge`, `identityTrace`, `identityTrace_gradeDiag`, `kummerCocycle`,
`kummerCocycle_gradeDiag`, `radialMultiplier`, `radialMultiplier_zero`, `radialMultiplier_add`,
`radial_line_invariant_iff`, `radial_parameter_transitive`).  None of it is rebuilt.  The new content
is the CEM reading:

- `kummerReporter` — the trace and the cocycle as one reporter coframe;
- `kummerReporter_gradeDiag` — the whole coframe is invariant under every character gauge;
- `absoluteGrade_zero` — the normalisation `ν 0 = 1` is *derived* from positivity and
  multiplicativity, so it is not carried as a hypothesis;
- `kummerReporter_radial` — the coframe is invariant under the whole radial family `Γ_c`;
- `kummerReporter_not_separating` — hence it takes the same value at any two members of one radial
  orbit: the valuation/Kummer coframe can never be the transverse intervention-response coframe;
- `reporter_eq_of_mem_orbit`, `orbitReporter`, `orbitReporter_mk` — the general set-level statement
  that an invariant reporter is a function of the orbit alone.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveEquivariantResponseBlindness.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,423 jobs.  `#print axioms` on
`mfderiv_comp_eq_of_invariant`, `doctrineResponse_eq_of_equivariant`, `doctrineResponse_smul`,
`responseCoframe_constant_on_orbit`, `orbitResponseCoframe`, `separation_forces_escape`,
`circleModel_escape_separates`, `circleModel_escape_not_sufficient`, `orbitReporter`,
`kummerReporter_radial`, and `kummerReporter_not_separating` reports only `propext`,
`Classical.choice`, and `Quot.sound`.  No project axiom, placeholder, hypothesis interface, or
unresolved theorem premise is used.

## Exact field consequence

Reporter richness and interventional identifiability are separated by a formal wall.  A complete
first-order coframe of equivariant interventions is, provably, a function on the orbit space; adding
reporters cannot cross that wall, and breaking equivariance is necessary but demonstrably not
sufficient — the orbit-tangent counterexample is non-equivariant and totally blind.  For the literal
graded source this says: the valuation/Kummer family, however far it is extended, is a `Γ_c`-orbit
function and can never select the radial origin.  A live source-normal mechanism must break
equivariance *and* prove its separation power.

# Finite-jet indistinguishability and clock covariance — Lean certificate

- **ID:** `finite-jet-indistinguishability-and-clock-covariance-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `finite-jet-indistinguishability-and-clock-covariance.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Modules

| File | Contents |
|---|---|
| `HTGeometry/TriangularSubstitution.lean` | invertible linear substitutions of polynomial variables |
| `HTGeometry/ClockChangeTriangular.lean` | §3 Thm 3.1, the triangular expansion of `(u δ)ⁿ` and clock invariance |
| `HTGeometry/DifferentialBirationalCovariance.lean` | §3 Cor 3.2, generator covariance |
| `HTGeometry/FiniteJetIndistinguishability.lean` | §4 Thm 4.1, Cor 4.2, Cor 4.3 |
| `HTGeometry/LocalInverseHypertranscendence.lean` | §5 Prop 5.1 and the inversion closure it needs |

Namespace `GaloisForLFunctions.HTGeometry`.

## Card statement to Lean name

| Card | Lean |
|---|---|
| §3 (3.1) `δ_uⁿ f = uⁿ δⁿ f + Σ_{j<n} a_{n,j} δʲ f` | `clockRescale`, `exists_iterate_clockRescale` |
| §3 (3.1) the inverse triangular expansion | `exists_iterate_clockRescale_inv` |
| §3 (3.2) the two finite jet algebras coincide | `adjoin_jets_clockRescale` |
| §3 a triangular jet change preserves nonzero relations | `linSub`, `linSub_comp`, `linSub_injective`, `isUnit_det_of_lowerTriangular`, `isDifferentiallyAlgebraicOver_of_triangular` |
| §3 Thm 3.1 clock invariance of hypertranscendence | `isDifferentiallyAlgebraicOver_clockRescale_iff`, `isHypertranscendentalOver_clockRescale_iff` |
| §3 Cor 3.2 `K⟨f⟩ = K⟨g⟩` transports the property | `differentialAlgebraicOver_of_differentialAdjoin_le`, `differentialAlgebraicOver_iff_of_differentialAdjoin_eq`, `hypertranscendentalOver_iff_of_differentialAdjoin_eq` |
| §4 jet coordinates and the interpolating polynomial | `jetAtZero`, `jetPolynomial`, `jetAtZero_jetPolynomial` |
| §4 the polynomial realization is differentially algebraic | `differentiallyAlgebraic_of_iteratedDeriv_eq_zero`, `differentiallyAlgebraic_jetPolynomial` |
| §4 the entire hypertranscendental witness | `entireHypertranscendentalWitness`, `hypertranscendental_entireHypertranscendentalWitness` |
| §4 Thm 4.1 every finite jet has both realizations | `exists_finiteJet_da_and_ht` |
| §4 the finite-jet topology | `JetSpace`, `jetVector`, `continuous_jetAtZero`, `nhds_jetSpace`, `exists_mem_of_mem_nhds` |
| §4 Cor 4.2 mutual density | `dense_differentiallyAlgebraic`, `dense_hypertranscendental` |
| §4 Cor 4.2 no interior, not closed | `interior_differentiallyAlgebraic_eq_empty`, `interior_hypertranscendental_eq_empty`, `not_isClosed_differentiallyAlgebraic`, `not_isClosed_hypertranscendental` |
| §4 Cor 4.3 no continuous finite-precision classifier | `no_continuous_classifier` |
| §5 differential algebraicity survives local inversion | `differentiallyAlgebraicOn_of_localInverse` |
| §5 a local relation of an entire function is global | `differentiallyAlgebraic_of_differentiallyAlgebraicOn` |
| §5 Prop 5.1 a hypertranscendental pair composing to the identity | `exists_hypertranscendental_inverse_pair` |

The card's §4 witness is `p + z^{r+1} Γ(z+1)`.  The Lean witness is
`p + (P − T)`, where `P` interpolates the prescribed jet, `T` interpolates the jet of the entire
hypertranscendental witness `powerCanonicalProduct 1`, and `differentiallyAlgebraic_add_polynomial`
transports the property.  Both realize the same statement; the corpus already owns the
hypertranscendence of `powerCanonicalProduct 1` unconditionally.

## The §5 construction

The card's Prop 5.1 needs the classical fact that differentially algebraic germs with nonvanishing
derivative are closed under local functional inversion.  The corpus did not have it, and it is
proved here by a transcendence count rather than by an elimination:

- `inverseJet F G k = F⁽ᵏ⁾ ∘ G` and `deriv_inverseJet` give `(F⁽ᵏ⁾ ∘ G)′ = (F⁽ᵏ⁺¹⁾ ∘ G) · G′`;
- hence every `F⁽ᵏ⁾ ∘ G` lies in `differentialAdjoin ℂ(z) {G}` inside the meromorphic differential
  field of the domain of `G`;
- if `G` is differentially algebraic that field has finite transcendence degree over `ℂ(z)`, hence
  over `ℂ` by `trdeg_add_eq`;
- a hypertranscendental `F` would make `{G, id, F′ ∘ G, F″ ∘ G, …}` an infinite algebraically
  independent family inside it, which is impossible.

The bridge between pointwise relations and field relations is
`eval₂_analyticFunctionElement_eq_zero_iff` and `aeval_analyticMeroElement_eq_zero_iff`.

The witness pair itself is the entire hypertranscendental function and its analytic local inverse
at a point where its derivative does not vanish.

## Verification

Foreground per-file elaboration and a cached foreground `lake build` of the five modules pass.
The axiom audit of `exists_finiteJet_da_and_ht`, `no_continuous_classifier`,
`dense_hypertranscendental`, `isHypertranscendentalOver_clockRescale_iff`,
`hypertranscendentalOver_iff_of_differentialAdjoin_eq`,
`differentiallyAlgebraicOn_of_localInverse` and `exists_hypertranscendental_inverse_pair` reports
only `propext`, `Classical.choice`, `Quot.sound`.

## Boundary

The uncertainty statement is topological: no continuous map to a Hausdorff space separates the two
classes in the finite-jet topology.  It gives no quantitative tradeoff, and it says nothing about
which arithmetic objects are hypertranscendental.

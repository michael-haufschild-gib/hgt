# Thermodynamic affinity Fisher coercivity and incidence Gini control

- **ID:** `thermodynamic-affinity-fisher-coercivity`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, quantitative entropy-production value relation
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.ThermodynamicAffinityFisherBound`
  - `GaloisForLFunctions.RHTower.MobiusIncidencePseudoEntropyBound`

## General value law

For positive oriented values `a,b`, define the quadratic current or pseudo-entropy value

```text
Q(a,b) = 2 (a-b)^2 / (a+b).
```

The exact formal inequality is

```text
Q(a,b) <= (a-b) log(a/b).                                 (1)
```

The proof applies the sharp scalar logarithm bound

```text
2x/(x+2) <= log(1+x),   x >= 0,
```

in the orientation where `b <= a`, then uses reversal symmetry.  Unlike mere nonnegativity,
`Q(a,b)` is coercive: it vanishes exactly when `a=b` and is positive exactly when the observed
current is nonzero.

## Positive holonomy consequence

The existing thermodynamic-holonomy theorem says that a nonunit rate-ratio loop exposes an edge
with positive entropy production.  Equation `(1)` sharpens the positive residue: the loop exposes
an edge with strictly positive symmetric quadratic current cost.  Thus nonflat clock calibration
has an algebraic, logarithm-free observable witness.

## KMS and passive-response consequences

Weight `Q` for two Gibbs populations by the Hermitian transition probability.  Every resulting
KMS pseudo-entropy intensity is nonnegative and is pointwise bounded by the existing KMS
entropy-production intensity.  Summing gives

```text
total quadratic current cost <= total entropy production.  (2)
```

The new general response monotonicity laws show that increasing Lehmann weights:

- makes the upper-half-plane absorptive value more negative;
- increases the diagonal Pick/Cauchy value.

Consequently the entropy-production response has at least the absorptive and Pick strength of its
quadratic-current response.  These facts are reusable for any finite transition system, not only
the KMS specialization.

## Direct RHTower application

The finite Mobius-incidence construction already identifies total KMS entropy production with
the exact incidence Gini clock energy and with the layer-cake relative clock energy.  Combining
that identity with `(2)` gives

```text
finiteIncidencePseudoEntropyEnergy
  <= finiteIncidenceGiniEnergy
   = finiteIncidenceRelativeClockEnergy.                  (3)
```

The corresponding Gini/entropy response also has at least the upper-half-plane absorptive strength
of the incidence pseudo-entropy response.  This is a direct application to the existing corpus,
not a renamed passivity wrapper.

## Physics and chemistry provenance

The quadratic current cost is the pseudo entropy production used in thermodynamic uncertainty
relations for Markov jump systems and nonequilibrium transport.  Relevant primary literature:

- N. Shiraishi and K. Saito, *Fundamental relation between entropy production and heat current*,
  arXiv:1806.09389.
- C. Dieball and A. Godec, *Direct Route to Thermodynamic Uncertainty Relations and Their
  Saturation*, Phys. Rev. Lett. 130, 087101 (2023).
- T. Van Vu and Y. Hasegawa, *Thermodynamic uncertainty relations under arbitrary control
  protocols*, Phys. Rev. Research 2, 013060 (2020).

The formal theorem is useful for chemical reaction networks, biochemical and genetic regulatory
currents, open quantum systems, and finite transport networks because it replaces a logarithmic
entropy lower layer by a rational function of observable populations.

## Lean surface

- `pseudoEntropyProductionValue`
- `pseudoEntropyProductionValue_nonneg`
- `pseudoEntropyProductionValue_eq_zero_iff_eq`
- `pseudoEntropyProductionValue_pos_iff_ne`
- `pseudoEntropyProductionValue_le_entropyProductionValue`
- `exists_adjacent_pseudoEntropyProductionValue_pos_of_nontrivial_holonomy`
- `finiteKMSPseudoEntropyProductionTransitionIntensity`
- `finiteKMSPseudoEntropyProductionTransitionIntensity_nonneg`
- `finiteKMSPseudoEntropyProductionTransitionIntensity_le_entropyProduction`
- `sum_finiteKMSPseudoEntropyProductionTransitionIntensity_le_entropyProduction`
- `finiteTransitionPassiveResponse_im_anti_mono_of_intensity_le`
- `finiteTransitionPassiveResponse_cauchyDiagonal_mono_of_intensity_le`
- `finiteKMSEntropyProductionResponse_im_le_pseudo`
- `finiteKMSPseudoEntropyProductionResponse_cauchyDiagonal_le_entropyProduction`
- `finiteIncidencePseudoEntropyEnergy`
- `finiteIncidencePseudoEntropyEnergy_le_gini`
- `finiteIncidencePseudoEntropyEnergy_le_relativeClockEnergy`
- `finiteIncidenceKMSResponse_im_le_pseudoEntropyResponse`

## RH impact and boundary

The new inequalities strengthen finite passive-response approximants used by the existing
prime--archimedean anti-Herglotz and one-Cauchy gates.  They provide an algebraic lower certificate
that is easier to estimate than the logarithmic entropy intensity and is automatically compatible
with response ordering.

They do not identify the continued prime--archimedean source with such a response and therefore do
not prove RH.  The source-value comparison or convergence theorem remains the producer step.

## Verification

- [x] exact HT module target built and cached
- [x] exact RHT application target built and cached
- [x] both touched Lean files check directly
- [x] no numerical computation used

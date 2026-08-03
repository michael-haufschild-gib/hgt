# Two-species conformal clock scale law

- **ID:** `two-species-conformal-clock-scale-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / CONFORMAL SCALE / INVERSE PROBLEM
- **Parent:** `../../1-in-progress/continuum-chronometric-equivalence-theorem.md`
- **Status:** every proved theorem of this card is unconditional in Lean, including the literal
  smooth pseudo-Riemannian realization of the conformal wave operator and formula `(4)`. The only
  remaining item is the coupled inverse theorem of step 1 below, which is open research, not a
  proved statement awaiting formalization.

## Headline

> **Light gives spacetime its shape. Two different clocks give it size.**

Sharper mathematical form:

> **Two scalar clock species with different calibrated masses determine the conformal scale
> algebraically.**

This targets the exact gap left by nonlinear Lorentzian inverse theorems, which commonly recover
only conformal geometry from light-cone interactions.

## Conformal clock operator

Let \((M,g)\) be a \(d\)-dimensional Lorentzian manifold, \(d\geq 3\), and let

\[
  \widetilde g=e^{2\sigma}g,\qquad
  a=\frac{d-2}{2}.                                                         \tag{1}
\]

For a minimally coupled scalar clock species of squared mass \(\mu=m^2\), define the conjugated
Klein--Gordon operator

\[
  \mathcal P_\mu^\sigma
  =
  e^{(a+2)\sigma}
  \bigl(\Box_{\widetilde g}+\mu\bigr)
  e^{-a\sigma}.                                                            \tag{2}
\]

## Theorem 1 — exact conformal conjugation

\[
  \boxed{
  \mathcal P_\mu^\sigma
  =
  \Box_g+V_\mu^\sigma,}
  \qquad
  V_\mu^\sigma
  =
  \mu e^{2\sigma}
  -a\Box_g\sigma
  -a^2\langle d\sigma,d\sigma\rangle_g.                                   \tag{3}
\]

### Proof

For every scalar \(f\),

\[
  \Box_{\widetilde g}f
  =
  e^{-2\sigma}
  \left(
    \Box_g f+(d-2)\langle d\sigma,df\rangle_g
  \right).                                                                \tag{4}
\]

Set \(f=e^{-a\sigma}u\). Product and chain rules give

\[
\begin{aligned}
  \Box_g(e^{-a\sigma}u)
  =e^{-a\sigma}\bigl(
    \Box_g u
    -2a\langle d\sigma,du\rangle_g
    +(a^2|d\sigma|_g^2-a\Box_g\sigma)u
  \bigr),\\
  2a\langle d\sigma,d(e^{-a\sigma}u)\rangle_g
  =e^{-a\sigma}\bigl(
    2a\langle d\sigma,du\rangle_g
    -2a^2|d\sigma|_g^2u
  \bigr).
\end{aligned}                                                             \tag{5}
\]

The first-derivative terms cancel. Multiplying the result by
\(e^{(a+2)\sigma}\), and adding the mass term, yields `(3)`. \(\square\)

In four dimensions \(a=1\), so

\[
  V_\mu^\sigma
  =
  \mu e^{2\sigma}-\Box_g\sigma-|d\sigma|_g^2.                              \tag{6}
\]

## Theorem 2 — two species reconstruct conformal scale

Let \(\mu_1\neq\mu_2\) be two independently calibrated squared masses. Then

\[
  \boxed{
  e^{2\sigma}
  =
  \frac{V_{\mu_1}^\sigma-V_{\mu_2}^\sigma}
       {\mu_1-\mu_2}.}                                                     \tag{7}
\]

### Proof

Subtract the two instances of `(3)`. The terms
\(-a\Box_g\sigma-a^2|d\sigma|_g^2\) are identical for both species and cancel:

\[
  V_{\mu_1}^\sigma-V_{\mu_2}^\sigma
  =
  (\mu_1-\mu_2)e^{2\sigma}.
\]

Division by the nonzero calibrated mass difference proves `(7)`. \(\square\)

The same pair also reconstructs the shared geometric defect

\[
  D_\sigma=a\Box_g\sigma+a^2|d\sigma|_g^2
  =
  \mu_1e^{2\sigma}-V_{\mu_1}^\sigma.                                      \tag{8}
\]

Thus the map

\[
  (e^{2\sigma},D_\sigma)
  \longmapsto
  (V_{\mu_1}^\sigma,V_{\mu_2}^\sigma)
\]

is injective whenever \(\mu_1\neq\mu_2\). This algebraic injectivity and formula `(7)` are
unconditional in Lean, both algebraically and for the d'Alembertian of a literal smooth
nondegenerate metric field.

## Why one species is structurally weaker

One recovered potential gives only

\[
  V_\mu^\sigma=\mu e^{2\sigma}-D_\sigma,
\]

which mixes scale with a derivative defect. A second mass supplies a second equation with the same
defect and a different scale coefficient. The cancellation in `(7)` does not require integrating a
nonlinear hyperbolic equation or imposing analytic continuation.

This is not a claim that one species can never recover scale with additional boundary data. It is
the exact statement that two species remove the ambiguity pointwise and algebraically.

## Continuum-gravity bridge

Published active inverse results for Einstein--scalar systems recover topology, smooth structure,
and conformal class in the causal diamond of a worldtube under nondegenerate scalar-reference and
source-control hypotheses. To upgrade conformal class to metric:

1. reconstruct the effective zeroth-order potentials of two calibrated scalar probe species;
2. apply `(7)` pointwise to recover \(e^{2\sigma}\);
3. combine with conformal geometry to recover the full metric;
4. combine full metric response with chronometric graph rigidity to identify the complete metric
   gravity operator.

Step 2 is closed. Step 1 is the hard remaining inverse theorem in the coupled backreacting
Einstein--scalar setting. Existing potential-recovery theorems treat semilinear waves on a fixed
Lorentzian geometry and do not by themselves close this coupled bridge.

Its determination question is nevertheless settled exactly. For an arbitrary wave operator, with no
linearity, smoothness or geometry assumed, a family of probes solving `□u + Vu = 0` determines `V`
at an event **precisely when some probe of the family is nonvanishing there**; on the common zero
set of the family `V` can be altered arbitrarily without disturbing a single probe solution. So the
missing input of step 1 is exactly a probe family without a common zero — which is why wavefront
data, locating only where solutions are singular, cannot supply it (audit point 5).

`formal/GaloisForLFunctions/HTGeometry/ClockPotentialDetermination.lean`:

- `SolvesPotentialWave`, `potentialDeterminationSet`;
- `potential_eq_of_solvesPotentialWave`, `potential_eqOn_potentialDeterminationSet` — a
  nonvanishing probe pins the potential, and the family determines it on the whole determination
  set;
- `solvesPotentialWave_update_of_notMem_potentialDeterminationSet`,
  `exists_ne_potential_with_same_probeSolutions` — off that set the potential is invisible;
- `potential_determined_iff_mem_potentialDeterminationSet` — the exact **iff** criterion;
- `exists_notMem_potentialDeterminationSet_of_common_zero`,
  `potentialDeterminationSet_empty` — the criterion is not vacuous.

`formal/GaloisForLFunctions/HTGeometry/ClockScaleDeterminationLocus.lean` carries this through to
the scale itself, which is what the bridge actually needs:

- `reconstructedScale`, `reconstructedScale_eqOn_inter` — the reconstructed scale is unambiguous
  exactly on the **intersection** of the two species' determination loci;
- `exists_ne_reconstructedScale_of_notMem` — off the determination locus of either species the
  reconstructed scale is genuinely ambiguous;
- `reconstructedScale_wellDefined_of_subset_inter` — the bridge condition in usable form;
- `potentialDeterminationSet_mono`, `potentialDeterminationSet_eq_iUnion`,
  `isOpen_potentialDeterminationSet`, `isOpen_scaleDeterminationLocus` — the locus is monotone in
  the probe family and **open** for continuous probes, so securing one nonvanishing probe per
  species at an event secures a whole neighbourhood.

So the entire remaining content of step 1 is one condition: *the two clock species must have probe
families with no common zero where the scale is wanted.* Nothing about the geometry, the wave
operators, or the coupling enters the determination question.

That condition is far weaker than it looks for the family a laboratory actually produces. Repeating
an intervention at moved events gives a probe family closed under the action that moves them, and
for such a family the determination locus is a union of orbits — all-or-nothing when the action is
transitive. `formal/GaloisForLFunctions/HTGeometry/ClockProbeTranslationFamily.lean`:

- `ProbeActionClosed`, `mem_potentialDeterminationSet_of_act` — the determination locus is a union
  of orbits;
- `potentialDeterminationSet_eq_univ_of_transitive`,
  `potentialDeterminationSet_eq_univ_of_exists_ne_zero` — **one nonvanishing observation anywhere
  determines the potential everywhere**;
- `potential_eq_of_repeatable` — a repeatable experiment pins the potential globally;
- `reconstructedScale_eq_of_repeatable` — **one nonvanishing probe per species reconstructs the
  conformal scale unambiguously at every event**;
- `constantProbes`, `probeActionClosed_constantProbes`,
  `potentialDeterminationSet_constantProbes` — the hypothesis class is inhabited.

The determination half of step 1 is therefore closed, and the construction is carried out in the
flat diagonal case. `formal/GaloisForLFunctions/HTGeometry/ClockProbeAxisExponential.lean` builds an
explicit family for the corpus's own geometric d'Alembertian:

- `axisExponential`, `axisExponential_ne_zero`, `contDiff_axisExponential` — the probes
  `x ↦ c e^{s x_{i₀}}`, smooth and everywhere nonvanishing;
- `coordPartial_axisExponential`, `coordPartial_coordPartial_axisExponential` — they are
  eigenfunctions of the coordinate second derivatives;
- `dalembert_axisExponential`, `solvesPotentialWave_axisExponential` — they solve the chart wave
  equation of `SmoothPseudoMetric.ofSignature` for the constant potential `-ε_{i₀}⁻¹ s²`, so both
  signs are reachable in Lorentzian signature;
- `axisExponentialFamily`, `probeActionClosed_axisExponentialFamily`,
  `eventTranslation_transitive` — the nonzero multiples form a translation-closed family and
  translations act transitively;
- `potentialDeterminationSet_axisExponentialFamily` — the family determines its potential at
  **every** event;
- `potential_eq_axisPotential` — any potential explaining the family is the axis potential.

The translation hypothesis is then removable altogether.
`formal/GaloisForLFunctions/HTGeometry/ClockProbeNonvanishing.lean` drops flatness, homogeneity and
the group action:

- `inducedPotential`, `solvesPotentialWave_inducedPotential` — running the wave equation backwards,
  every nowhere-vanishing `u` solves the explicit potential `-(□u)/u`;
- `potential_eq_inducedPotential` — **one nowhere-vanishing probe pins the potential globally, on
  any geometry**;
- `exists_nonvanishing_probe_iff` — the potentials admitting a nowhere-vanishing probe are exactly
  those of the form `-(□u)/u`;
- `reconstructedScale_eq_of_nonvanishing_probes` — two such probes reconstruct the conformal scale
  everywhere;
- `potential_eq_inducedPotential_exp`,
  `potential_eq_inducedPotential_exp_conformalMinkowski`, `reconstructedScale_eq_of_exp_probes` —
  on any smooth chart, and in particular on a **conformally rescaled Minkowski chart**, every
  exponential `e^{f}` is such a probe, giving a variable-potential family on a curved background.

A globally nonvanishing probe is in any case more than the argument needs.
`formal/GaloisForLFunctions/HTGeometry/ClockProbeSolutionSpace.lean` works with the full solution
space:

- `LinearWave`, `solutionSet`, `zero_mem_solutionSet`, `add_mem_solutionSet`,
  `smul_mem_solutionSet` — for a linear wave operator the solutions form a linear space;
- `NoCommonZero`, `potentialDeterminationSet_solutionSet_eq_univ_iff` — determination is complete
  exactly when the solution space has no common zero;
- `potential_eq_of_noCommonZero`, `potential_eq_of_solutionSet_eq` — **two potentials with the same
  solution space are equal** as soon as that space has no common zero;
- `noCommonZero_of_exists_normalized` — normalized Cauchy data at each event suffice;
- `noCommonZero_of_nonvanishing_probe`, `noCommonZero_axisPotential` — a globally nonvanishing
  probe is the special case, and the condition is inhabited;
- `reconstructedScale_eq_of_noCommonZero` — pointwise probes for both species reconstruct the
  conformal scale everywhere.

The requirement is therefore only that **for each event separately** some solution be nonvanishing
there — the solutions may differ from event to event, which is exactly what solvability of the
Cauchy problem with normalized data delivers.

So the identifiability content of step 1 is settled in full generality, and the reachable potential
class is characterized. What remains open is the physical selection problem: a laboratory does not
choose `u` and read off `-(□u)/u`; it prepares sources and must obtain solutions with the required
nonvanishing behaviour for the *given* clock species. Supplying normalized Cauchy data in a
backreacting Einstein--scalar geometry is a hyperbolic-PDE construction, and is what the bridge
still lacks.

All depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Hypertranscendence role

The two species must remain operationally distinguishable after propagation and reporter mixing.
The corpus already proves that a complete clock compass preserves DA/HT species and contains exact
strong-field response sectors whose differential species depend on scalar gap. This supplies a
candidate invariant barcode for the \(\mu_1\) and \(\mu_2\) channels.

HT is not used to prove `(7)`. The new HT task is to prove that two calibrated mass channels cannot
be exchanged or collapsed by admissible DA exterior matching while their clock response species
are distinct.

## Hostile audit

1. **Conformal coupling:** `(3)` is for minimally coupled Klein--Gordon operators. A conformally
   coupled massless scalar has extra covariance and can be scale-blind. Proved sharp: a single
   species — equivalently two species of equal calibrated mass — determines only the combination
   `μ e^{2σ} - D_σ`, and explicit distinct `(e^{2σ}, D_σ)` states share one potential.
2. **Mass renormalization:** \(\mu_i\) must be independently calibrated physical pole masses, not
   theory-dependent coordinate labels.
3. **Field redefinitions:** the common conjugation weight in `(2)` must be fixed by the same
   reporter normalization for both species. Proved sharp: the geometric defect cancels from the
   potential difference for all geometric data **exactly when** the two conjugation weights agree.
4. **Backreaction:** the inverse experiment must separate each probe potential while both fields
   alter the metric.
5. **Potential recovery:** wavefront locations alone recover conformal geometry, not the
   zeroth-order amplitudes required by `(7)`.
6. **Species mixing:** a non-diagonal mass matrix must first be reconstructed and diagonalized by
   physical source/reporter channels. Proved sharp and quantitative: for a symmetric mass matrix
   with diagonal entries `a, d` and mixing `b`, the calibrated gap is the spectral gap
   `√((a-d)² + 4b²)`, which equals the naive channel gap `|a-d|` exactly when `b = 0` and strictly
   exceeds it otherwise, so dividing by the raw channel labels strictly **overestimates**
   `e^{2σ}`.
7. **Clock-dark sector:** a scale mode invisible to both probe species defeats the operational
   bridge and violates detector completeness.

## Lean status

Unconditional in
`formal/GaloisForLFunctions/HTGeometry/ContinuumChronometricGravity.lean`:

- `twoSpeciesConformalPotential_difference`;
- `twoSpeciesConformalScale_reconstruction`;
- `twoSpeciesConformalPotentialPair_injective`.

`formal/GaloisForLFunctions/HTGeometry/ConformalClockDiffusion.lean` now also formalizes the exact
general-dimensional exponential calculation in an abstract second-order clock calculus:

- `ExponentialSecondOrderClockCalculus.conformalWaveSigma_conjugation`;
- `ExponentialSecondOrderClockCalculus.conformalKleinGordonSigma_conjugation`;
- `ExponentialSecondOrderClockCalculus.conformalWaveSigma_dimension_conjugation`;
- `ExponentialSecondOrderClockCalculus.conformalKleinGordonSigma_dimension_conjugation`.

These theorems prove the chain/product-rule expansion, first-derivative cancellation, geometric
defect, and mass term at `a=(d-2)/2` without assuming the displayed conclusion.

### Smooth pseudo-Riemannian realization

The abstract calculus is now realized by a literal smooth metric field. Three new modules:

`formal/GaloisForLFunctions/HTGeometry/SmoothMatrixDeterminantCalculus.lean`

- `contDiff_matrix_det`, `contDiff_matrix_adjugate_apply`, `contDiff_matrix_inv_apply` — a
  matrix field with `C^∞` entries has `C^∞` determinant, adjugate and (off the vanishing locus of
  the determinant) inverse entries;
- `contDiff_sqrt_abs` — `√|u|` is `C^∞` wherever `u` does not vanish.

`formal/GaloisForLFunctions/HTGeometry/ConformalMetricDalembertian.lean`

- `coordPartial` with its constant, sum, product, constant-multiple, exponential and smoothness
  rules;
- `SmoothMetricChart` — smooth symmetric inverse-metric field with smooth positive density; its
  `gradPair` (carré du champ), `flux` and divergence-form `dalembert`
  `□f = ρ⁻¹ ∑ᵢ ∂ᵢ(ρ ∑ⱼ Gⁱʲ ∂ⱼ f)`;
- `SmoothMetricChart.dalembert_conformalRescale` — **formula `(4)` in full generality**:
  `□_{(e^{-2σ}G, e^{dσ}ρ)} f = e^{-2σ}(□ f + (d-2) Γ(σ,f))`;
- `SmoothPseudoMetric` — smooth symmetric metric field with nowhere-vanishing determinant, its
  chart `(g⁻¹, √|det g|)`, and the literal conformal rescaling `g ↦ e^{2σ}g`;
- `SmoothPseudoMetric.chart_conformal` — the chart of `e^{2σ}g` **is** the rescaled chart, i.e.
  `(e^{2σ}g)⁻¹ = e^{-2σ}g⁻¹` and `√|det(e^{2σ}g)| = e^{dσ}√|det g|`;
- `SmoothPseudoMetric.dalembert_conformal` — formula `(4)` for a literally rescaled metric;
- `SmoothPseudoMetric.ofSignature`, `minkowski`, `ofSignature_dalembert` — the class is inhabited,
  and for a constant diagonal signature the divergence-form operator is the literal
  `∑ᵢ εᵢ⁻¹ ∂ᵢ²`.

`formal/GaloisForLFunctions/HTGeometry/ConformalMetricClockCalculus.lean`

- `smoothScalarAlgebra` — the `ℝ`-algebra of `C^∞` functions of `d` coordinates;
- `SmoothMetricChart.dalembert_mul`, `gradPair_comm`, `gradPair_mul_left/right`,
  `dalembert_expSmul`, `gradPair_expSmul_left/right` — the Leibniz and exponential chain rules of
  the metric d'Alembertian (symmetry of `Gⁱʲ` is exactly what supplies the factor `2`);
- `SmoothMetricChart.secondOrderCalculus`, `SmoothMetricChart.expClockCalculus` — the metric
  d'Alembertian **is** a `SecondOrderClockCalculus` and an
  `ExponentialSecondOrderClockCalculus`;
- `SmoothMetricChart.conformalWaveSigma_eq_dalembert_conformalRescale` — the abstract conformal
  wave operator at `a=(d-2)/2` equals the d'Alembertian of the conformally rescaled chart.

`formal/GaloisForLFunctions/HTGeometry/ConformalClockTwoSpeciesScaleLaw.lean`

- `SmoothMetricChart.conformalDefect`, `conformalPotential` — `D_σ` of `(8)` and `V_μ^σ` of `(3)`;
- `SmoothPseudoMetric.conformalKleinGordon_conjugation` — **Theorem 1, boxed `(3)`, for a literal
  smooth metric field**;
- `SmoothMetricChart.conformalKleinGordon_dimension_conjugation` — its `d ≥ 3` literal form;
- `SmoothPseudoMetric.conformalKleinGordon_four` — equation `(6)`, the `d=4`, `a=1` form;
- `SmoothMetricChart.conformalPotential_difference` — the defect cancellation of Theorem 2;
- `SmoothMetricChart.conformalScale_reconstruction`,
  `SmoothPseudoMetric.conformalScale_reconstruction` — **Theorem 2, boxed `(7)`**;
- `SmoothMetricChart.conformalDefect_reconstruction` — equation `(8)`;
- `SmoothMetricChart.conformalPotentialPair_injective` — injectivity of
  `(e^{2σ}, D_σ) ↦ (V_{μ₁}^σ, V_{μ₂}^σ)`.

All of the above depend only on `propext`, `Classical.choice`, `Quot.sound`.

Missing:

1. coupled inverse theorem recovering both effective potentials from clock data (open research;
   step 1 of the continuum-gravity bridge below).

## Exact boundary of the reconstruction

`formal/GaloisForLFunctions/HTGeometry/ConformalClockScaleBlindness.lean` isolates the effective
potential's independent algebraic channels — conjugation weight, calibrated squared mass, conformal
scale, and the two geometric defect channels — and proves both hypotheses of `(7)` necessary:

- `conformalPotentialData`, `SmoothMetricChart.conformalPotential_eq_data` — the chart potential is
  the algebraic potential evaluated on `(e^{2σ}, □_g σ, Γ_g(σ,σ))`;
- `conformalPotentialData_difference` — with a shared weight the difference is the pure scale term
  of `(7)`;
- `conformalPotentialData_difference_eq_zero_of_eq_mass`,
  `conformalPotentialData_eq_of_eq_mass` — equal calibrated masses give an identically vanishing
  difference, so two such species are exactly as blind as one;
- `exists_ne_scaleDefect_with_eq_conformalPotentialData` — **one species separates neither scale
  nor defect**: for every weight and mass two distinct `(scale, defect)` states share a potential.
  This is audit points 1 and 2;
- `conformalPotentialData_difference_of_weights`,
  `conformalPotentialData_difference_pure_iff_weight_eq` — the defect cancels for all geometric
  data **iff** the two conjugation weights agree. This is audit point 3;
- `exists_conformalPotentialData_difference_ne_scale` — an explicit weight mismatch that destroys
  the scale channel.

`formal/GaloisForLFunctions/HTGeometry/ConformalClockSpeciesMixing.lean` closes audit point 6:

- `massMixingGap`, `massEigenvalueHigh`, `massEigenvalueLow`, `massEigenvalueHigh_isRoot`,
  `massEigenvalueLow_isRoot` — the calibrated masses of a mixed pair are the roots of the
  characteristic polynomial of the symmetric mass matrix;
- `massEigenvalue_difference` — the calibrated mass difference is the spectral gap;
- `massMixingGap_eq_abs_sub_iff` — the spectral gap equals the naive channel gap **iff** the
  mixing vanishes;
- `abs_sub_lt_massMixingGap` — mixing strictly widens the gap;
- `conformalPotentialData_mixed_reconstruction` — after diagonalization `(7)` holds verbatim;
- `conformalPotentialData_mixed_naive_overestimate`,
  `conformalPotentialData_mixed_naive_ne` — using un-diagonalized channel labels returns a
  strictly larger value than the true scale, and never the true scale.

All depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Closest SOTA

- Y. Kurylev, M. Lassas, L. Oksanen, and G. Uhlmann,
  *Inverse problem for Einstein--scalar field equations*,
  <https://arxiv.org/abs/1406.4776>.
- M. Lassas, G. Uhlmann, and Y. Wang,
  *Inverse problems for semilinear wave equations on Lorentzian manifolds*,
  <https://arxiv.org/abs/1606.06261>.
- A. Feizmohammadi and L. Oksanen,
  *Recovery of zeroth order coefficients in non-linear wave equations*,
  <https://arxiv.org/abs/1903.12636>.
- N. Pinamonti,
  *Conformal generally covariant quantum field theory: the scalar field and its Wick products*,
  <https://arxiv.org/abs/0806.0803>.

Targeted searches found no prior result stating the two-mass cancellation `(7)` as a Lorentzian
inverse-gravity scale reconstruction theorem. This is a priority claim, not an exhaustive
bibliographic guarantee.

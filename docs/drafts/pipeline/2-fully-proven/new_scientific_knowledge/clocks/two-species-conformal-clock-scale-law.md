# Two-species conformal clock scale law

- **ID:** `two-species-conformal-clock-scale-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / CONFORMAL SCALE / INVERSE PROBLEM
- **Parent:** `../../1-in-progress/continuum-chronometric-equivalence-theorem.md`
- **Status:** every proved theorem of this card is unconditional in Lean, including the literal
  smooth pseudo-Riemannian realization of the conformal wave operator and formula `(4)`. Step 1 of
  the continuum-gravity bridge is now **closed end to end on any chart admitting a non-null
  foliation whose invariants are functions of the leaf label**
  (`twoSpecies_foliation_reconstruction`) — cosmological, static and curved alike — with the probes
  constructed rather than assumed, and the massless species is free on every chart
  (`noCommonZero_conformalPotential_zero`), so the remaining content is a probe family for a single
  massive species — equivalently, by `noCommonZero_of_rescaled_probeFamily`, a local existence
  theorem for the physical massive Klein--Gordon field. What remains open is exactly that: open
  research, not a proved statement awaiting formalization.

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

Step 2 is closed. Step 1 is closed unconditionally whenever probes can be constructed, which now
includes every conformal factor constant on the leaves of a non-null foliation whose invariants
`Γ(φ,φ)` and `□φ` are functions of the leaf label — cosmological, static and curved alike. There
`twoSpecies_foliation_reconstruction` composes steps 1 and 2 into a pointwise recovery of `e^{2σ}`
from clock data. Step 1 remains the hard inverse theorem in the general coupled
backreacting Einstein--scalar setting. Existing potential-recovery theorems treat semilinear waves
on a fixed Lorentzian geometry and do not by themselves close this coupled bridge.

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

That weakening is not cosmetic. `formal/GaloisForLFunctions/HTGeometry/ClockProbeOneDimensional.lean`
settles both constant-potential regimes of `u'' + Vu = 0` by explicit solutions:

- `cosProbe`, `solvesPotentialWave_cosProbe`, `cosProbe_self`, `noCommonZero_oscillatory` — in the
  **oscillatory** regime the probes are cosines centred at each event; each is nonvanishing at its
  own centre, so the potential is determined;
- `cosProbe_eq_zero` — every cosine probe has a zero, so **no member of that family is globally
  nonvanishing**: the oscillatory case is determined only because the pointwise condition allows
  the probe to vary with the event;
- `coshProbe`, `solvesPotentialWave_coshProbe`, `coshProbe_ne_zero`,
  `noCommonZero_nonOscillatory` — in the non-oscillatory regime one hyperbolic cosine suffices
  globally;
- `potential_eq_of_oscillatory`, `potential_eq_of_nonOscillatory` — both regimes determine their
  potential.

Variable potentials need no existence theory either, if the equation is read in the other direction.
`formal/GaloisForLFunctions/HTGeometry/ClockProbeRiccati.lean` substitutes `u = e^{w}`:

- `expProbe`, `secondDeriv_expProbe` — the substitution turns `u'' + Vu = 0` into the Riccati
  relation `V = -(w'' + (w')²)`;
- `riccatiPotential`, `solvesPotentialWave_expProbe`, `noCommonZero_riccatiPotential`,
  `potential_eq_riccatiPotential` — **for every smooth `w` the potential `-(w'' + (w')²)` carries a
  globally nonvanishing probe and is determined**;
- `riccatiPotential_sq`, `noCommonZero_quadraticRiccati` — `w = x²` gives the nonconstant potential
  `-(2 + 4x²)`, so the class is genuinely variable.

This is the one-dimensional form of the characterization already proved in general: the potentials
admitting a nowhere-vanishing probe are exactly those of the form `-(□u)/u`.

Finally, the global-solution requirement is itself unnecessary.
`formal/GaloisForLFunctions/HTGeometry/ClockPotentialLocalDetermination.lean` replaces it by the
pointwise one, which is what the argument actually reads:

- `SolvesPotentialWaveAt`, `SolvesPotentialWaveOn`, `potential_eq_of_solvesPotentialWaveAt` — the
  pointwise core: a probe nonvanishing at an event pins the potential there, using the equation only
  at that event;
- `LocalProbesOn`, `potential_eqOn_of_localProbes`, `potential_eqOn_of_solvesOn` — **a probe solving
  only on a region determines the potential on that region**;
- `potential_eq_of_localProbes_univ`, `localProbes_of_noCommonZero` — the global statements are the
  special case;
- `reconstructedScale_eqOn_of_localProbes` — the scale is reconstructed on the common region;
- `exists_solvesOn_not_solves` — the local notion is strictly weaker, so this is a genuine
  relaxation.

This is the form an existence theorem plugs into: solutions of wave equations come with a domain,
and a laboratory works in a worldtube, so both sides now speak about regions.

One caution is recorded in
`formal/GaloisForLFunctions/HTGeometry/ClockProbePointwiseVacuity.lean`. The bare pointwise
condition `LocalProbesOn`, which asks only for a probe solving *one* candidate potential at each
event, is **empty**: a cosine or hyperbolic cosine of the right frequency centred at the event
matches any prescribed potential value there (`localProbesOn_trivial`), so two different potentials
both satisfy it on every region (`exists_ne_potential_with_localProbesOn`). The content is entirely
in the *shared* requirement — one and the same probe solving for both candidates — and
`solvesPotentialWaveAt_iff_of_ne_zero` shows a probe nonvanishing at an event is shared exactly when
the two potentials already agree there. Physically that is the right reading: the probe is an
observed solution of the actual species, and both candidates are tested against that observation.

The condition the determination theorems actually rest on, `NoCommonZero`, survives the same audit.
`formal/GaloisForLFunctions/HTGeometry/ClockProbeConditionAudit.lean`:

- `solutionSet_identityWave_eq_singleton`, `not_noCommonZero_identityWave` — for a degenerate
  operator whose only solution is zero, `NoCommonZero` **fails**;
- `exists_ne_potential_with_eq_solutionSet` — and then the solution space genuinely fails to pin the
  potential: two visibly different potentials share it;
- `noCommonZero_satisfiable_and_falsifiable` — the condition holds in the oscillatory case and fails
  in the degenerate one, so it is two-sided.

`NoCommonZero` is therefore a genuine hypothesis, not a formality, and the determination theorems
built on it are not vacuous.

So the identifiability content of step 1 is settled in full generality, and the reachable potential
class is characterized. What remains open is the physical selection problem: a laboratory does not
choose `u` and read off `-(□u)/u`; it prepares sources and must obtain solutions with the required
nonvanishing behaviour for the *given* clock species. That selection problem is now **solved
whenever the geometry admits a foliation whose two invariants are functions of the leaf label**: if
`Γ(φ,φ) = P∘φ` with `P` nowhere zero and `□φ = R∘φ`, then normalized local solutions exist for every
`C¹` potential in every dimension (`exists_foliation_localProbe`), so the potential is determined
outright (`chartPotential_eq_of_foliation`). This covers the cosmological slicing, the static
gravitational field, and charts whose metric varies arbitrarily **along** the leaves. It is also
solved, on any chart and with no foliation at all, for every potential of the form
`-(□w + Γ(w,w))` — and that is *exactly* the class carrying a globally nonvanishing smooth probe
(`chartRiccati_iff`) — and, on flat space, for every constant potential, by plane waves
(`noCommonZero_const_minkowski`). The last of these lies strictly outside the other two
(`exists_noCommonZero_not_riccatiPotential`), so lacking a nowhere-vanishing probe is no obstruction
either. What the bridge still lacks is a potential admitting no probe family without a common zero:
supplying normalized Cauchy data there is a hyperbolic-PDE construction.

### Scope of the one-dimensional results

The one-dimensional cases above — constant, oscillatory, Riccati — are illustrations that the
`NoCommonZero` condition is realizable and two-sided. They are **not** progress on the bridge, whose
bottleneck is the four-dimensional coupled Einstein--scalar system.

The one-dimensional corner is now closed at its natural limit. `ClockProbeLocalExistence.lean`
autonomises `u'' + Vu = 0` as the field `(x,u,v) ↦ (1, v, -(V x)·u)` on `ℝ³`, applies Picard--Lindelöf
(`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`) and identifies the
first component with `a + t` by `IsOpen.is_const_of_fderiv_eq_zero` on an open interval. This gives,
for **every** `C¹` potential and every event:

- `exists_localProbe` — a solution of `u'' + Vu = 0` on an interval about the event with `u(a) = 1`;
- `exists_localProbe_ne_zero` — the local form of the nondegeneracy condition, unconditionally;
- `eq_of_solvesOn_localSolutions` — a competitor solving those local solutions equals `V` everywhere;
- `reconstructedScale_eq_of_solvesOn_localSolutions` — the two-species conformal scale is thereby
  reconstructed with no nondegeneracy hypothesis at all.

This is the sharp contrast with the audit of the global condition: `NoCommonZero` can fail for a
degenerate operator (`ClockProbeConditionAudit.lean`), while for the second-derivative operator with
a `C¹` potential its local form never fails. The extension does **not** advance step 1 itself, whose
bottleneck remains the four-dimensional coupled Einstein--scalar system; it removes the last
hypothesis from the one-dimensional model.

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

`formal/GaloisForLFunctions/HTGeometry/ClockProbeLocalExistence.lean` closes the one-dimensional
model of step 1 with no residual hypothesis:

- `contDiff_waveField` — the autonomised field `(x,u,v) ↦ (1, v, -(V x)·u)` is `C¹` whenever `V` is;
- `exists_localProbe` — every `C¹` potential carries a local solution normalized at any event;
- `exists_localProbe_ne_zero` — the local nondegeneracy condition, unconditionally;
- `eq_of_solvesOn_localSolutions` — local solutions pin the potential on the whole line;
- `reconstructedScale_eq_of_solvesOn_localSolutions` — hence the two-species scale, hypothesis-free.

### The homogeneous sector in every dimension

The one-dimensional model lifts to a chart of arbitrary dimension whenever the geometry and the
potential are homogeneous — constant on the level sets of the zeroth coordinate. This is the
cosmological sector, the sector in which two-species clock comparison is actually performed.

`formal/GaloisForLFunctions/HTGeometry/ClockProbeSturmLiouville.lean` supplies the analytic input,
local existence for the divergence-form equation the chart produces:

- `first_component_affine` — the unit-speed identification `(α t)₀ = a + t` of any autonomisation;
- `sturmField`, `contDiff_sturmField` — the field `(x,u,v) ↦ (1, v/A(x), -(B x)u)` in the momentum
  variable `v = A u'`;
- `exists_localSturmProbe` — for `C¹` coefficients with `A` nowhere zero, a solution of
  `(A u')' + B u = 0` about every event, normalized to one there.

`formal/GaloisForLFunctions/HTGeometry/ClockProbeHomogeneousChart.lean` performs the reduction:

- `coordPartial_timeLift_of_ne` — transverse constancy, with **no** differentiability hypothesis
  (the case where the lift is not differentiable is settled by the junk value of `fderiv`);
- `coordPartial_timeLift_zero`, `flux_timeLift` — only the zeroth column of `Gⁱʲ` contributes;
- `dalembert_timeLift` — **the reduction** `□(w ∘ x⁰) = ρ⁻¹ (ρ G⁰⁰ w')'`, proved from the
  divergence-form definition by an eventual-equality transfer on the open slab `{x⁰ ∈ S}`;
- `exists_homogeneous_localProbe` — clock probes on every homogeneous chart with `G⁰⁰` non-null;
- `chartPotential_eq_of_homogeneous` — **determination of the homogeneous potential from clock
  data**, in every dimension, with no nondegeneracy hypothesis.

`formal/GaloisForLFunctions/HTGeometry/ClockProbeFRWChart.lean` shows the hypothesis class is
inhabited by a physically live family rather than by flat space alone:

- `frwChart` — the Friedmann--Robertson--Walker chart of an **arbitrary** smooth expansion history
  `σ`, inverse metric `diag(-1, e^{-2σ}, …, e^{-2σ})` and density `e^{dσ}`, built as a literal
  `SmoothMetricChart (d+1)`;
- `exists_frw_localProbe` — clock probes about every time, for every `C¹` potential of time;
- `frw_potential_eq` — the clock potential of an expanding chart is determined by clock data.

So an arbitrary expansion history is no obstruction: the inverse step is unconditional throughout
the homogeneous sector.

### Arbitrary non-null slicings, and the static field

Nothing in the reduction uses the zeroth coordinate. What it uses is that the chart data are
constant on the level sets of a fixed linear phase `⟪n,x⟫` and that `n` is non-null.
`formal/GaloisForLFunctions/HTGeometry/ClockProbeCovectorSlicing.lean` proves the reduction in that
generality:

- `covectorPhase`, `covectorCLM`, `covectorLift`, `covectorNorm` — the phase, its continuous linear
  form, the lifted field, and `G(n,n)`;
- `coordPartial_covectorLift`, `flux_covectorLift` — each direction contributes its component of `n`,
  and the inverse metric enters only through its pairing with `n`;
- `dalembert_covectorLift` — **`□(w ∘ ⟪n,·⟫) = ρ⁻¹ (ρ G(n,n) w')'`**;
- `exists_covector_localProbe`, `chartPotential_eq_of_covector` — probes and determination;
- `covectorLift_single_zero` — the homogeneous case is the zeroth basis covector;
- `covectorPhase_basis`, `covectorNorm_basis` — for a basis covector the norm is the diagonal entry.

Taking `n` **spatial** gives the configuration of the actual clock-comparison experiment: two clocks
at different heights of a gravitational potential.
`formal/GaloisForLFunctions/HTGeometry/ClockProbeStaticChart.lean` builds it:

- `staticChart` — the static planar chart `g = diag(-e^{2Φ(z)}, 1, …, 1)` of an arbitrary smooth
  gravitational potential, as a literal `SmoothMetricChart`;
- `staticChart_inhomogeneous` — this geometry is **not** homogeneous: where `Φ` differs, so does the
  metric;
- `exists_static_localProbe`, `static_potential_eq` — clock probes about every height, and
  determination of the clock potential from clock data.

So inhomogeneity as such is not the obstruction, and neither is the Lorentzian signature: the
determination is unconditional whenever the data are constant along some non-null slicing.

### The general foliation reduction, and charts inhomogeneous along their own leaves

All the slicing results specialise one identity, proved in
`formal/GaloisForLFunctions/HTGeometry/ClockProbeFoliationReduction.lean` for an **arbitrary** smooth
scalar `φ`:

- `coordPartial_comp`, `differentiableAt_comp` — the coordinate chain rule;
- `dalembert_comp` — **`□(w∘φ) = Γ(φ,φ)·(w''∘φ) + (□φ)·(w'∘φ)`**, with no condition on `φ` beyond
  smoothness and on `w` beyond two local derivatives. The `Γ` term is exactly the corpus identity
  `inv_density_mul_sum_flux`;
- `linField`, `contDiff_linField`, `exists_localLinearProbe` — local existence for the general
  linear second-order equation `u'' + p u' + q u = 0`;
- `exists_foliation_localProbe`, `chartPotential_eq_of_foliation` — probes and determination whenever
  the two invariants are functions of the leaf label, `Γ(φ,φ) = P∘φ` and `□φ = R∘φ` with `P` nowhere
  zero.

This is strictly weaker than the slicing hypothesis: the **chart data need not be constant on the
leaves**, only the two invariants. `formal/GaloisForLFunctions/HTGeometry/ClockProbeInhomogeneousChart.lean`
shows the gap is real:

- `inhomChart` — the chart of `g = diag(-1, e^{2σ}, …, e^{2σ})` for an arbitrary smooth `σ`;
- `gradPair_coord_zero` — `Γ(dx⁰,dx⁰) = -1`, independent of `σ`;
- `dalembert_coord_zero` — `□x⁰ = -d ∂₀σ`;
- `exists_inhom_localProbe`, `inhom_potential_eq` — probes and determination under the single
  condition that `∂₀σ` be a function of `x⁰`;
- `tiltedFactor`, `exists_tilted_localProbe`, `tilted_potential_eq` — the explicit member
  `σ(x) = α(x⁰) + x¹` for an arbitrary smooth expansion history `α`;
- `tiltedChart_not_leafConstant` — two points of one leaf carry **different** metrics, so no slicing
  theorem applies to this chart, and yet its potential is determined.

### Potentials that are not functions of any leaf label

Every result above recovers a potential that is a function of a leaf label. The exponential
substitution leaves that restriction behind, and
`formal/GaloisForLFunctions/HTGeometry/ClockProbeChartRiccati.lean` settles the resulting class
exactly:

- `SmoothMetricChart.dalembert_const_mul` — linearity of the chart d'Alembertian (absent from the
  corpus until now);
- `chartExpProbe`, `dalembert_chartExpProbe` — `□e^w = (□w + Γ(w,w))e^w`, from the corpus's
  `dalembert_expSmul` at `c = 1`;
- `chartRiccatiPotential`, `solvesPotentialWave_chartExpProbe`,
  `noCommonZero_chartRiccatiPotential`, `potential_eq_chartRiccatiPotential` — `-(□w + Γ(w,w))`
  carries a **globally** nonvanishing probe and is determined outright, for every smooth `w` and
  every chart;
- `sign_const_of_ne_zero` — a nowhere-vanishing continuous function on a coordinate space has
  constant sign (the step that legitimises taking the logarithm);
- `exists_chartRiccati_of_nonvanishing_probe`, `chartRiccati_iff` — **the exact class**: a potential
  carries a globally nonvanishing smooth probe *if and only if* it is `-(□w + Γ(w,w))`;
- `ofSignature_gradPair`, `chartRiccatiPotential_ofSignature_sqCoord`,
  `exists_determined_potential_not_leafConstant` — on Minkowski space the exponent `w = (x¹)²`
  yields `V = -(2 + 4(x¹)²)`, determined, and **not** constant on the level sets of `x⁰`.

So the determined class is not confined to leaf-constant potentials.

### The determined class is strictly larger than that

Determination never needs one probe nonvanishing everywhere — it needs, at each event, *some* probe
nonvanishing there. `formal/GaloisForLFunctions/HTGeometry/ClockProbeOscillatorySeparation.lean`
proves the two conditions differ:

- `oscWronskian`, `hasDerivAt_oscWronskian`, `oscWronskian_const` — the Wronskian of a solution
  against `sin(kx)` is conserved;
- `half_period_neg` — hence `u(π/k) = -u(0)` for **every** solution, so every solution changes sign;
- `not_exists_nonvanishing_oscillatory_probe`, `not_riccatiPotential_oscillatory` — the oscillatory
  potential therefore carries no nowhere-vanishing probe and is not a Riccati potential;
- `exists_noCommonZero_without_nonvanishing_probe`, `exists_noCommonZero_not_riccatiPotential` —
  **strict separation**: `V = 1` is determined (centred cosines) yet lies outside the exact class of
  the previous section.

The higher-dimensional witnesses are the plane waves.
`formal/GaloisForLFunctions/HTGeometry/ClockProbePlaneWave.lean`:

- `coordPartial_covectorPhase`, `gradPair_covectorPhase`, `dalembert_covectorPhase` — a linear phase
  has constant carré du champ `G(n,n)` and vanishing d'Alembertian;
- `planeWave`, `solvesPotentialWave_planeWave` — hence `cos(⟪n,x⟫ + θ)` solves `□u + G(n,n)u = 0`;
- `noCommonZero_covectorNormConst` — sliding the offset gives a probe nonvanishing at each event, so
  every constant potential in the range of `n ↦ G(n,n)` is determined;
- `exists_covectorNormConst_minkowski`, `noCommonZero_const_minkowski`,
  `potential_eq_const_minkowski` — on Minkowski space that range is **all of `ℝ`**, so *every*
  constant potential is determined.

In flat space the clock potential of a species is its squared mass, so this closes the flat case of
step 1 for both species at once, with no nondegeneracy hypothesis.

### Step 1 closed end to end for the cosmological conformal class

`formal/GaloisForLFunctions/HTGeometry/ClockTwoSpeciesConformalTime.lean` assembles the pieces into
the card's headline claim for a conformal factor depending only on the zeroth coordinate — the
Friedmann geometry `e^{2σ}η` written in conformal time.

- `dalembert_timeLift_flat`, `gradPair_timeLift_flat` — the two invariants of a lifted conformal
  factor on a constant-signature chart, `(ε₀)⁻¹σ''` and `(ε₀)⁻¹(σ')²`;
- `conformalTimePotential`, `conformalPotential_timeLift`,
  `twoSpecies_conformalTime_potential_agrees` — hence
  `V_μ^σ(x) = μe^{2σ(x⁰)} - a(ε₀)⁻¹σ''(x⁰) - a²(ε₀)⁻¹σ'(x⁰)²`, a function of `x⁰` alone;
- `contDiff_conformalTimePotential`, `flat_leading_ne_zero` — the hypotheses of the homogeneous
  probe theorem, discharged;
- `exists_conformalTime_localProbe` — **the probes are constructed**, not assumed;
- `conformalTimePotential_determined` — each species' effective potential is pinned by its own clock
  data;
- `twoSpecies_conformalTime_reconstruction` — **`(V_{μ₁} - V_{μ₂})/(μ₁ - μ₂) = e^{2σ}` pointwise**,
  for every smooth expansion history and every pair of distinct calibrated masses.

So for the cosmological conformal class step 1 is no longer open: the missing input — a probe family
without a common zero for each species — is supplied by construction, and steps 1 and 2 compose into
an unconditional reconstruction of the conformal scale from clock data.

### The same along any non-null basis slicing, including the static case

Nothing in that argument uses the zeroth coordinate beyond its non-nullity.
`formal/GaloisForLFunctions/HTGeometry/ClockTwoSpeciesBasisSlicing.lean` runs it along an arbitrary
basis direction `k` of a constant-signature chart:

- `coordPartial_basisLift_self`, `coordPartial_basisLift_ne`, `coordPartial_sq_basisLift_self`,
  `coordPartial_sq_basisLift_ne` — the partial derivatives of a conformal factor constant on the
  level sets of `xᵏ`;
- `dalembert_basisLift_flat`, `gradPair_basisLift_flat` — `(ε_k)⁻¹σ''` and `(ε_k)⁻¹(σ')²`;
- `conformalPotential_basisLift` — hence
  `V_μ^σ(x) = μe^{2σ(xᵏ)} - a(ε_k)⁻¹σ''(xᵏ) - a²(ε_k)⁻¹σ'(xᵏ)²`;
- `exists_basisSlicing_localProbe`, `basisSlicing_potential_determined` — probes constructed, each
  species' potential pinned;
- `twoSpecies_basisSlicing_reconstruction` — **`e^{2σ}` recovered pointwise**, for every basis
  direction;
- `twoSpecies_staticSlicing_reconstruction` — the case `k = 1` written out on Minkowski space: a
  conformal factor varying with height, which is the geometry of the clock-comparison experiment.

Taking `k = 0` recovers the cosmological statement above, so the two physically distinct
configurations — expanding universe and static gravitational field — are one theorem.

### The general form: any chart, any foliation

Neither the constant signature nor the coordinate slicing is needed.
`formal/GaloisForLFunctions/HTGeometry/ClockTwoSpeciesFoliation.lean` runs the argument on an
arbitrary chart along an arbitrary foliation whose two invariants are functions of the leaf label:

- `gradPair_comp` — the chain rule for the carré du champ, `Γ(σ₀∘φ, σ₀∘φ) = Γ(φ,φ)·σ₀'(φ)²`;
- `foliationPotential`, `conformalPotential_foliation`,
  `conformalPotential_eq_foliationPotential` — with `Γ(φ,φ) = P∘φ` and `□φ = R∘φ`, the card's own
  effective potential is
  `V_μ^σ = F∘φ`, `F(t) = μe^{2σ₀(t)} - a(P(t)σ₀''(t) + R(t)σ₀'(t)) - a²P(t)σ₀'(t)²`;
- `contDiff_foliationPotential`, `exists_foliationConformal_localProbe` — the probes are
  constructed;
- `foliationConformal_potential_determined` — each species' potential is pinned by its clock data;
- `twoSpecies_foliation_reconstruction` — **`e^{2σ}` recovered pointwise**.

This subsumes everything above: cosmological, static, basis and covector slicings are the special
cases `φ = ⟪n,·⟫` on a constant-signature chart, and the curved and leaf-inhomogeneous charts built
earlier are covered too. The hypotheses are exactly: `P` nowhere zero (the foliation is non-null),
`P` and `R` are `C¹` functions of the leaf label, and the conformal factor is constant on the
leaves.

### The massless species is free: one species carries the whole inverse step

The requirement of **two** species is weaker than it looks.
`formal/GaloisForLFunctions/HTGeometry/ClockMasslessReference.lean` observes that at `μ = 0` the
effective potential is minus the defect, and the defect is exactly a Riccati expression:

- `gradPair_const_mul` — scalar multiples in the carré du champ (absent from the corpus until now);
- `conformalDefect_eq_riccati` — **`D_σ = □(aσ) + Γ(aσ, aσ)`**, so `V_0^σ = -(□(aσ) + Γ(aσ,aσ))`;
- `conformalPotential_zero_eq_chartRiccati`, `solvesPotentialWave_masslessProbe` — hence `e^{aσ}` is
  a globally nonvanishing probe of the massless species on **any** chart and for **any** smooth
  conformal factor. It is the conjugate of the constant solution of the massless wave equation;
- `noCommonZero_conformalPotential_zero`, `conformalDefect_determined` — the massless potential, and
  with it the shared geometric defect `D_σ` of `(8)`, is determined **with no hypothesis at all**;
- `scale_of_one_massive_species` — `e^{2σ} = (V_μ^σ - V_0^σ)/μ` for `μ ≠ 0`;
- `twoSpecies_reconstruction_massless_reference`,
  `scale_reconstruction_of_one_massive_probe_family` — the reconstruction carries **one** hypothesis,
  on the massive species alone.

So the card's two-species requirement reduces: take the massless species as reference and the whole
remaining content of the inverse step is a probe family for a **single** massive species. Note the
contrast with `(8)`, which recovers `D_σ` only after the scale is known — the massless species gives
`D_σ` directly and unconditionally.

### The remaining input, transported to the physical Klein–Gordon equation

Theorem 1 is an identity between operators; read as a statement about *solutions* it is a bijection.
`formal/GaloisForLFunctions/HTGeometry/ClockRescaledProbeTransfer.lean`:

- `SolvesRescaledKleinGordon` — solutions of the physical equation `□_{g̃} f + μ f = 0` on the
  rescaled chart;
- `solvesPotentialWave_of_rescaled`, `rescaled_of_solvesPotentialWave` — `u ↦ e^{-aσ}u` and
  `f ↦ e^{aσ}f` are mutually inverse between probes of `V_μ^σ` and physical solutions, and both
  preserve smoothness and zeros because `e^{aσ}` is smooth and nowhere zero;
- `noCommonZero_of_rescaled_probeFamily`, `exists_rescaled_probe_of_noCommonZero` — hence the
  probe-family condition for the effective potential **is** the physical condition;
- `scale_reconstruction_of_rescaled_probeFamily` — the conformal scale from that single physical
  hypothesis, the massless reference contributing nothing.

### Separable potentials: probes varying in two directions at once

Every determination result above uses probes constant on the leaves of one foliation. Products break
that restriction, and the obstruction to using them was regularity, not mathematics: the chart
calculus of the corpus is stated at `ContDiff ℝ ∞`, which Picard--Lindelöf probes do not satisfy.
`formal/GaloisForLFunctions/HTGeometry/ClockProbeSeparablePotential.lean` rebuilds what is needed at
the regularity those probes actually have:

- `coordPartial_congr`, `ofSignature_flux_eq`, `ofSignature_dalembert_of_differentiableAt` — the flat
  d'Alembertian from **pointwise differentiability of the first partials** alone;
- `coordPartial_covectorLift_of_zero` — transverse constancy of a covector lift, with no
  differentiability hypothesis at all;
- `dalembert_covectorLift_flat` — `□(w∘⟪n,·⟫) = G(n,n)·w''(⟪n,x⟫)` at that regularity;
- `dalembert_mul_transverse` — **`□(fg) = g□f + f□g`** when `f` varies only along `i₀` and `g` not at
  all along `i₀`, because the carré du champ of transverse factors vanishes on a diagonal chart;
- `exists_separable_localProbe`, `separable_potential_determined` — hence probes for
  `V(x) = V₁(⟪n₁,x⟫) + V₂(⟪n₂,x⟫)` with **arbitrary `C¹` profiles**, and the determination of that
  potential.

This is the first class on the card whose probes are not constant on any single foliation: both
factors vary, in independent directions.

The support condition on the first factor is an artefact.
`formal/GaloisForLFunctions/HTGeometry/ClockProbeOrthogonalSeparable.lean` isolates the real one:

- `dalembert_mul_of_differentiableAt` — the **full** Leibniz rule at that regularity,
  `□(fg) = f□g + g□f + 2Γ(f,g)`, with no support hypothesis;
- `covectorPairing`, `gradPair_covectorLift_pair` — for covector lifts the cross term is
  `⟨n₁,n₂⟩_G · w₁'w₂'`, so what the product needs is exactly **metric orthogonality**
  `⟨n₁,n₂⟩_G = ∑ᵢ (εᵢ)⁻¹ n₁ᵢ n₂ᵢ = 0`;
- `exists_orthogonal_separable_localProbe`, `orthogonal_separable_potential_determined` — probes and
  determination for `V(x) = V₁(⟪n₁,x⟫) + V₂(⟪n₂,x⟫)` for **any** non-null `G`-orthogonal pair;
- `covectorPairing_twoIndex`, `exists_boosted_orthogonal_pair` — the class is not confined to
  coordinate directions: `(2,1,0,…)` and `(1,2,0,…)` on Minkowski space are non-null, orthogonal, and
  neither is a coordinate covector.

Two orthogonal factors extend to a whole orthogonal frame.
`formal/GaloisForLFunctions/HTGeometry/ClockProbeFullySeparable.lean`:

- `coordPartial_eq_zero_of_invariant` — a field invariant under translation in a direction has no
  derivative there, with **no** differentiability hypothesis; this is what makes the induction cheap;
- `coordFactor`, `boxProduct`, `coordPartial_boxProduct_of_notMem` — the partial product over a set
  of coordinates is literally invariant transversally to that set;
- `boxProduct_solves` — the induction over subsets: `∏ᵢ wᵢ(xᵢ)` solves the equation with the sum
  potential as soon as each factor solves `(εᵢ)⁻¹wᵢ'' + Vᵢwᵢ = 0`;
- `exists_fullySeparable_localProbe`, `fullySeparable_potential_determined` — hence **every fully
  separable potential** `V(x) = ∑ᵢ Vᵢ(xᵢ)` with arbitrary `C¹` profiles is determined.

In four dimensions that is a potential varying independently in time and in all three spatial
directions.

All of these constructions are tied to the coordinate frame.
`formal/GaloisForLFunctions/HTGeometry/ClockFlatFrameCovariance.lean` removes that tie:

- `fderiv_apply_eq_sum` — the differential is the coordinate expansion of the partial derivatives;
- `frameMap`, `frameCLM`, `coordPartial_comp_frame` — the chain rule through a linear change of
  frame `y ↦ (⟪n_k,y⟫)_k`, at Picard--Lindelöf regularity;
- `dalembert_comp_frame` — **`□(u∘F)(x) = ∑_{k,l} ⟨n_k,n_l⟩_G · (∂_l∂_k u)(Fx)`**: the transformed
  operator has the metric pairings of the frame covectors as coefficients;
- `dalembert_comp_orthogonal_frame` — for a `G`-orthogonal frame only the pure second derivatives
  survive, so every flat construction above transports verbatim to that frame.

The same formula is the entry point to the characteristic route: for a **null** frame in two
dimensions the diagonal pairings vanish and only the mixed derivative survives, which is the form in
which the wave equation is solved by Riemann's method.

So the last open input of the whole programme is now stated in its physical form:

> the massive Klein–Gordon field on the rescaled spacetime admits, at every event, a smooth solution
> nonvanishing there.

That is what a local hyperbolic existence theorem supplies, and it is the only thing still missing.

Missing:

1. a local existence theorem for the physical massive Klein--Gordon field: at every event, a smooth
   solution of `□_{g̃} f + μ f = 0` nonvanishing there, for a **single** massive species (the
   massless species needs nothing, and the transfer
   `noCommonZero_of_rescaled_probeFamily` shows this is equivalent to the probe-family condition on
   the effective potential) (open research; step 1 of the
   continuum-gravity bridge below). The one-dimensional, homogeneous, static, leaf-inhomogeneous,
   globally-nonvanishing-probe, flat constant-potential, and general foliated-conformal cases are
   now proved outright, the last end to end through the scale reconstruction. Note the boundary
   is *not* "no nowhere-vanishing probe" — the oscillatory potential has none and is still
   determined; what is still absent is local solvability of `□u + Vu = 0` for the remaining
   potentials, which is a hyperbolic Cauchy problem.

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

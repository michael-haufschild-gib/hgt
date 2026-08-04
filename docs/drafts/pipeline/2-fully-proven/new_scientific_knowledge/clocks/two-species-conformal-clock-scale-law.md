# Two-species conformal clock scale law

- **ID:** `two-species-conformal-clock-scale-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / CONFORMAL SCALE / INVERSE PROBLEM
- **Parent:** `../../1-in-progress/continuum-chronometric-equivalence-theorem.md`
- **Status:** **complete.** Every proved theorem of this card is unconditional in Lean, including
  the literal smooth pseudo-Riemannian realization of the conformal wave operator and formula `(4)`.
  Step 1 of the continuum-gravity bridge is closed end to end on any chart admitting a non-null
  foliation whose invariants are functions of the leaf label (`twoSpecies_foliation_reconstruction`)
  — cosmological, static and curved alike — and, on the flat chart, for an *arbitrary* smooth
  conformal factor in every dimension (`twoSpecies_scale_reconstruction`). The massless species is
  free on every chart (`noCommonZero_conformalPotential_zero`), and the probe family for the massive
  species — equivalently, by `noCommonZero_of_rescaled_probeFamily`, a local existence theorem for
  the physical massive Klein--Gordon field — is **constructed**, not assumed
  (`openProbes_of_smooth_spacetime`). Nothing on this card is open.

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

The same formula is the entry point to the characteristic route, taken in
`formal/GaloisForLFunctions/HTGeometry/ClockNullFrameReduction.lean`:

- `nullCovectors`, `covectorPairing_null_zero_zero`, `covectorPairing_null_one_one` — in the null
  frame `ξ = x⁰+x¹`, `η = x⁰-x¹` of two-dimensional Minkowski space **both frame covectors are
  null**, so the diagonal pairings vanish;
- `dalembert_nullFrame` — hence **`□(u∘F)(x) = -2·((∂₁∂₀u) + (∂₀∂₁u))(Fx)`**, the characteristic
  form;
- `nullFrame_zero`, `nullFrame_one`, `exists_event_of_nullPoint` — the frame and its inverse;
- `solvesPotentialWaveAt_of_characteristic` — a solution of `∂₁∂₀u + ∂₀∂₁u = ½V·u` at a null point
  is a clock probe at the corresponding event;
- `potential_eq_of_characteristic_family` — a family of such solutions without a common zero
  determines the potential.

The reduction is exact, not merely sufficient.
`formal/GaloisForLFunctions/HTGeometry/ClockNullFrameEquivalence.lean`:

- `invNullCovectors`, `invNullFrame`, `nullFrame_invNullFrame`, `invNullFrame_nullFrame` — the null
  frame is invertible, `x⁰ = (ξ+η)/2`, `x¹ = (ξ-η)/2`;
- `characteristic_of_solvesPotentialWaveAt` — a clock probe transports to a characteristic solution;
- `solvesPotentialWaveAt_iff_characteristic` — **the two are the same data**.

One apparent gap in the foliation reconstruction turns out to be empty. That theorem requires the
foliation to be **non-null**, so a potential constant along a null direction falls outside it.
`formal/GaloisForLFunctions/HTGeometry/ClockNullFoliationRiccati.lean` shows the null case is
nevertheless covered, by a different mechanism:

- `nullExponent`, `gradPair_nullExponent`, `dalembert_nullExponent` — for `w = F(ξ) + η` one has
  `□w = 0` and `Γ(w,w) = -4F'(ξ)`;
- `chartRiccatiPotential_nullExponent` — hence `-(□w + Γ(w,w)) = 4F'(ξ)`, a potential constant along
  the null direction `ξ`, carried by the globally nonvanishing probe `e^{w}`;
- `noCommonZero_nullFoliated`, `potential_eq_nullFoliated` — every such potential is in the Riccati
  class and is determined outright.

So the non-nullity hypothesis of `twoSpecies_foliation_reconstruction` is a limitation of that route,
not of the result: in two dimensions the null-foliated potentials are reached through the Riccati
class instead.

So in 1+1 dimensions the card's last open input is now **exactly the Goursat problem**: local
solvability of `∂ξ∂η u = ¼ V u` with prescribed nonzero data on the characteristics — and nothing
weaker, since the equivalence runs both ways. That is the equation Riemann's method solves by Picard
iteration on a rectangle, and it is the concrete target that would close the remaining gap in two
dimensions.

The first layer of that construction is built.
`formal/GaloisForLFunctions/HTGeometry/ClockVolterraOperator.lean` integrates the characteristic
equation once in `η`, turning it into an ordinary differential equation in `ξ` whose values are
functions of `η`, `∂ξ U(ξ) = A(ξ)U(ξ)` with `(A(ξ)v)(η) = ∫_b^η K(ξ,t)v(t)dt`:

- `clampTo`, `volterraFun`, `continuous_primitive_of_continuous`, `continuous_volterraFun` — the
  operator, with the range of integration clamped to a fixed compact interval so that it is bounded;
- `abs_volterraFun_le`, `abs_volterraFun_sub_le` — the pointwise norm and difference estimates;
- `volterraBCF`, `norm_volterraBCF_le`, `dist_volterraBCF_le` — the operator on the Banach space of
  bounded continuous functions, with **`‖A(ξ)U‖ ≤ M(b'-b)‖U‖`** and the matching Lipschitz bound.

Those two estimates are exactly the hypotheses `IsPicardLindelof` requires of a vector field, and
mathlib's Picard–Lindelöf theorem is stated for an arbitrary Banach space.

`formal/GaloisForLFunctions/HTGeometry/ClockVolterraParameter.lean` supplies the third hypothesis,
the dependence on the characteristic parameter:

- `exists_kernel_bound` — a continuous kernel is bounded on a compact rectangle;
- `exists_kernel_delta` — and uniformly continuous there, in `ε`–`δ` form;
- `abs_clampTo_sub_le` — clamping to an interval is nonexpansive;
- `abs_volterraFun_kernel_sub_le` — changing the kernel changes the operator by at most the kernel
  gap;
- `goursatBCF`, `continuous_goursatBCF` — the vector field of the characteristic ODE, with both
  variables clamped to the rectangle so the bounds are global, and **its continuity in `ξ` in the
  norm of the Banach space**.

`formal/GaloisForLFunctions/HTGeometry/ClockGoursatSolution.lean` assembles them:

- `norm_goursatBCF_le`, `dist_goursatBCF_le` — the vector-field bounds in the exact form the
  structure asks for;
- `exists_goursat_solution` — **the characteristic ODE has a local solution**: for every continuous
  kernel and every `ξ₀` there is `h > 0` and `α : ℝ → (ℝ →ᵇ ℝ)` with `α(ξ₀) = 1` and
  `∂ξ α(ξ) = A(ξ)α(ξ)` on `[ξ₀-h, ξ₀+h]`.

This is the analytic content of Riemann's method, and it is unconditional.

`formal/GaloisForLFunctions/HTGeometry/ClockGoursatPointwise.lean` reads that solution pointwise:

- `hasDerivWithinAt_bcf_eval` — evaluation at a second null coordinate is a continuous linear map,
  so it commutes with the derivative, and `∂ξ u` is the Volterra transform of `u`;
- `hasDerivAt_volterraFun` — that transform differentiates in `η` to `K·u`, by the fundamental
  theorem of calculus;
- `exists_goursat_pointwise` — hence **`∂η ∂ξ u = K u` on the open rectangle**, with `u(ξ₀,·) = 1`,
  for every continuous kernel.

`formal/GaloisForLFunctions/HTGeometry/ClockGoursatContinuity.lean` supplies the regularity the
remaining step needs:

- `continuousOn_bcf_eval` — a differentiable curve of bounded continuous functions is jointly
  continuous when read as a function of two variables, because evaluation is continuous;
- `exists_goursat_jointly_continuous` — hence the Goursat solution is jointly continuous on the
  strip where it is defined;
- `continuousOn_kernel_mul_solution` — the integrand of the second mixed derivative is continuous
  along the characteristic parameter.

`formal/GaloisForLFunctions/HTGeometry/ClockGoursatIntegralForm.lean` recovers the integral equation
itself:

- `continuous_volterraFun_param` — the Volterra transform of a jointly continuous family is
  continuous in the characteristic parameter;
- `exists_goursat_integral_form` — hence, by the fundamental theorem of calculus,
  **`u(ξ,η) = 1 + ∫_{ξ₀}^{ξ} (∫_b^η K(τ,t)u(τ,t)dt) dτ`** on the open interval.

`formal/GaloisForLFunctions/HTGeometry/ClockGoursatGlobal.lean` prepares the exchange:

- `integrableOn_uncurry_of_continuous`, `intervalIntegral_swap_of_continuous` — **Fubini for
  interval integrals of a jointly continuous integrand**, with no integrability side condition,
  since a continuous function is integrable on the compact rectangle containing the region;
- `exists_goursat_global` — the Goursat solution repackaged so that it is **globally** jointly
  continuous, by clamping the characteristic parameter. Nothing is lost, because every differential
  statement is local, and every integrability condition downstream becomes automatic.

`formal/GaloisForLFunctions/HTGeometry/ClockGoursatMixed.lean` completes the analytic construction:

- `exists_goursat_mixed` — exchanging the order of integration exhibits `u` as a primitive in `η` as
  well as in `ξ`, so the fundamental theorem of calculus gives
  `∂η u(ξ,η) = ∫_{ξ₀}^{ξ} K(τ,η)u(τ,η)dτ`, and differentiating that in `ξ` gives `K(ξ,η)u(ξ,η)`.
  **Both mixed second derivatives exist and both equal `K·u`**, with `u(ξ₀,·) = 1`, for every
  continuous kernel.

That is the full Goursat datum the chart d'Alembertian needs.

`formal/GaloisForLFunctions/HTGeometry/ClockBivariateChart.lean` builds the bridge to the chart
calculus, which reads partial derivatives off the **total** derivative and so needs more than the
existence of the two partials:

- `pairCLM`, `toCLM` — the linear identification `x ↦ (x⁰,x¹)` and the scalar-to-operator embedding;
- `hasFDerivAt_bivariateChart`, `differentiableAt_bivariateChart` — via mathlib's
  `hasStrictFDerivAt_uncurry_coprod`, continuous partial derivatives give a **totally**
  differentiable chart function;
- `coordPartial_bivariateChart_zero`, `coordPartial_bivariateChart_one` — and its `coordPartial` in
  the two coordinate directions are exactly the bivariate partial derivatives.

Instantiating that bridge at the Goursat solution turns out to need more than the mixed derivatives.
The chart d'Alembertian reads second partials one direction at a time, and in Minkowski coordinates
`∂₀∂₀(u∘F) = ∂ξ²u + 2∂ξ∂ηu + ∂η²u`; the pure terms cancel in `-∂₀∂₀ + ∂₁∂₁`, but each must exist for
the formula to apply. So the two-dimensional closure needs `u ∈ C²`, which for a merely continuous
kernel is false and for a smooth kernel requires a regularity bootstrap — differentiating

`∂ξ u(ξ,η) = ∫_b^η K(ξ,t)u(ξ,t)dt`

again under the integral sign. That is no loss of generality for this card, whose potentials are
smooth.

`formal/GaloisForLFunctions/HTGeometry/ClockParametricDerivative.lean` supplies the tool:

- `hasDerivAt_parametric_intervalIntegral` — the **Leibniz rule for continuous data**: if the
  integrand and its partial derivative in the parameter are jointly continuous, the parametric
  interval integral is differentiable and its derivative is the integral of the derivative.
  mathlib's general statement carries measurability and domination hypotheses; on a compact
  rectangle they are automatic.
- `hasDerivAt_parametric_intervalIntegral_on` — the same rule with the differentiability of the
  integrand required only for parameters in an open set and only for integration variables inside
  the interval of integration. Both localisations are needed downstream, because the derivatives of
  the Goursat solution are known only where the characteristic equation holds.

The bootstrap itself is now built. `ClockGoursatDerivContinuity.lean` records that the two first
derivatives are jointly continuous — each is a parametric interval integral of a jointly continuous
integrand with a continuous limit of integration:

- `continuous_goursatXiDeriv`, `continuous_goursatEtaDeriv`.

`ClockGoursatRegularity.lean` then differentiates the two Goursat identities once more:

- `hasDerivAt_goursat_xi_second` — for a kernel with a jointly continuous partial derivative in the
  characteristic parameter, `∂ξ²u` exists at every point of an open set inside the domain, and
  equals `∫_b^η (∂ξK·u + K·∂ξu) dt`. The clamp used to globalise the solution is invisible here:
  on the open set it is the identity, so the integrand agrees with a genuine product near each
  point and the product rule applies through `HasDerivAt.congr_of_eventuallyEq`.
- `hasDerivAt_goursat_eta_second` — symmetrically, `∂η²u` exists and equals
  `∫_{ξ₀}^{ξ} (∂ηK·u + K·∂ηu) dτ`. Here the localisation in the integration variable is essential:
  the `η`-derivative of `u(τ,·)` is known only for `τ` in the window, which is exactly the range of
  integration.

So a `C¹` kernel already forces the Goursat solution to be `C²`, and all four second derivatives of
the solution are available.

`ClockBivariateSecondOrder.lean` turns that into chart calculus. `chartFun` reads a bivariate
function as a function on a two-dimensional coordinate space, `chartBox` is the coordinate preimage
of a planar set, and `IsC1On u A B Ω` records that `u` has the continuous partial derivatives `A`
and `B` on the open set `Ω`:

- `hasFDerivAt_chartFun`, `differentiableAt_chartFun`, `coordPartial_chartFun_zero/_one` — first
  order;
- `differentiableAt_coordPartial_chartFun` and the four
  `coordPartial_coordPartial_chartFun_*` — second order, from three `IsC1On` records on one set.
  The step that makes this work is that `coordPartial 0 (chartFun u)` agrees with `chartFun A` on a
  whole neighbourhood, not only at the point, so `Filter.EventuallyEq.fderiv_eq` transports both the
  differentiability and the value.

`ClockCharacteristicProbe.lean` feeds that into the null-frame equivalence:

- `nullChartFun`, `nullChartFun_comp_invNullFrame`;
- `solvesPotentialWaveAt_nullChartFun` — **a twice continuously differentiable solution of the
  characteristic equation is a clock probe.**

`ClockGoursatC2.lean` assembles the Goursat data into exactly that package:

- `exists_goursat_C2` — for a kernel with jointly continuous partial derivatives, the normalised
  Goursat solution together with `A = ∂ξu`, `B = ∂ηu`, `Aa = ∂ξ²u`, `Ab = Ba = K·u`, `Bb = ∂η²u`
  and the three `IsC1On` records on the rectangle where all the construction's derivative statements
  hold at once.

`ClockTwoDimensionalProbe.lean` closes the two-dimensional inverse step:

- `nullKernel`, `contDiff_nullKernel` — the kernel `V/4` read in null coordinates is as regular as
  the potential;
- `planarFst`, `planarSnd`, `hasDerivAt_planarFst/Snd`, `continuous_planarFst/Snd` — the partial
  derivatives of a `C¹` function of two variables, read off its total derivative;
- **`exists_clockProbe_two_dimensional`** — *every continuously differentiable potential on a
  two-dimensional clock spacetime admits a clock probe taking the value `1` at any prescribed
  event*. The normalisation `u(ξ₀,·) = 1` of the Goursat data is what makes the probe nonvanishing
  at the event, with no continuity argument needed;
- `localProbesOn_univ_two_dimensional` — hence `LocalProbesOn … Set.univ`;
- **`potential_eq_of_probes_two_dimensional`** — *the clock probes determine a two-dimensional
  potential completely*: if every probe of a `C¹` potential is a probe of a second potential, the
  two potentials agree everywhere. No regularity whatever is assumed of the second potential.

So in two dimensions the inverse step is **closed unconditionally**, with the sole hypothesis that
the potential has one derivative. This is not a determined *class* of potentials in the sense of the
earlier sections — it is all of them, in that dimension. It also settles the status of the
Riccati characterisation: `chartRiccati_iff` says that a *globally* nonvanishing probe forces the
Riccati form, and the theorem here produces a probe nonvanishing only at the event in question, which
is all local determination needs.

`ClockConformalTwoDimensional.lean` removes the flatness restriction. In dimension two the conformal
transformation law degenerates twice over: the gradient correction carries the factor `d - 2`, and
the *flux* of the rescaled chart is literally the flux of the original one, so

- `SmoothMetricChart.flux_conformalRescale_two` — `flux_{e^{2σ}g} = flux_g`;
- `SmoothMetricChart.dalembert_conformalRescale_two` — `□_{e^{2σ}g} f = e^{-2σ} □_g f`, **for an
  arbitrary function `f`**, with no differentiability hypothesis. This matters: the general law
  `dalembert_conformalRescale` asks for a smooth argument, and the Goursat probes are only twice
  differentiable, so the general law does not apply to them;
- `solvesPotentialWaveAt_conformalRescale_two` — a clock equation on a conformally rescaled surface
  is the clock equation on the flat one with potential `e^{2σ}V`;
- `exists_clockProbe_conformal_two_dimensional`, `potential_eq_of_probes_conformal_two_dimensional`
  — existence and determination transport verbatim. Since every Lorentzian metric on a surface is
  locally conformally flat, this is the two-dimensional inverse problem in its physical form.

`ClockLocalTwoSpecies.lean` then closes the card's own reconstruction in that dimension. The
reconstruction was stated with a probe family without a common zero — that is, with *global*
solutions — but determination never needs that much:

- `potential_eq_of_localProbesOn`, `localProbesOn_of_noCommonZero` — a family of purely local probes
  suffices, and a family without a common zero is one;
- `scale_reconstruction_of_local_probes` — the two-species scale law with `LocalProbesOn … univ` in
  place of `NoCommonZero`, on any chart and in any dimension. The massless species still needs
  nothing;
- `conformalPotential_weight_zero` — at the two-dimensional conformal weight `(d-2)/2 = 0` the
  effective potential of a species of squared mass `μ` is exactly `μ e^{2σ}`;
- `localProbesOn_conformalPotential_two` — hence a two-dimensional clock species has local probes at
  every event, **unconditionally**;
- **`twoSpecies_scale_reconstruction_two_dimensional`**, **`twoSpecies_reconstructedScale_two_dimensional`**
  — *the two-species conformal clock scale law holds unconditionally in two dimensions*:
  `(V₁ - V₂)/μ = e^{2σ}` with no hypothesis on the probe families beyond smoothness of `σ` and
  `μ ≠ 0`. The card's open input is discharged in that dimension, not assumed.

A word on what "probe" must mean here, because the pointwise reading is too weak to carry the
statement. `SolvesPotentialWaveAt` is a *single linear relation* between the second derivatives at
one event; a quadratic polynomial satisfies it for any potential whatever, so pointwise probes exist
trivially in every dimension and the corresponding determination hypothesis — "every function
solving at `x` for `V₁` solves at `x` for `V₂`" — is correspondingly strong. The physical notion is
a solution on an open region. The construction delivers that:

- `exists_clockProbe_on_two_dimensional` — the strengthened existence theorem: an **open**
  neighbourhood `W` of the event, a probe solving `SolvesPotentialWaveOn … V U W`, nonvanishing
  throughout `W`, and equal to `1` at the event. `W` is the preimage under the null frame of the
  Goursat rectangle, intersected with the (open) nonvanishing locus of the probe;
- `potential_eqOn_of_probes_on_two_dimensional` — determination with the hypothesis quantified over
  solutions on open regions;
- `OpenProbes`, `potential_eq_of_openProbes`, `openProbes_of_solves` — the corresponding probe-family
  notion, its determination principle, and the fact that a single globally nonvanishing global
  solution supplies it (this is how the massless species enters);
- `scale_reconstruction_of_openProbes`, `openProbes_conformalPotential_two`, and
  **`twoSpecies_scale_reconstruction_open_two_dimensional`** /
  **`twoSpecies_reconstructedScale_open_two_dimensional`** — the scale law again, now with both
  species' probe families consisting of genuine solutions on open regions, and the massive family
  proved to exist rather than assumed.

### The characteristic reduction is not confined to two dimensions

`ClockSlabProbe.lean` and `ClockSlabExistence.lean` carry the whole construction into arbitrary
dimension `n + 2`, for fields and potentials depending only on the two null coordinates
`ξ = x⁰ + x¹`, `η = x⁰ - x¹`. The transverse directions contribute nothing and the two pure second
derivatives cancel between the timelike and the spacelike direction, exactly as in two dimensions:

- `slabEps`, `slabCLM`, `slabLift`, `slabBox` — the Minkowski signature in dimension `n + 2`, the
  null projection as a continuous linear map, the lift of a bivariate function, and the (open)
  preimage of a planar set;
- `coordPartial_slabLift_zero/_one/_transverse` — the chain rule through the null projection:
  `∂₀ = ∂ξ + ∂η`, `∂₁ = ∂ξ - ∂η`, and every transverse partial derivative vanishes identically;
- `differentiableAt_coordPartial_slabLift`, `IsC1On.add`, `IsC1On.sub`;
- **`dalembert_slabLift`** — `□(slab lift) = -2(∂η∂ξ u + ∂ξ∂η u)` in every dimension;
- **`exists_clockProbe_on_slab`** — *for every continuously differentiable slab potential and every
  dimension `n + 2`, there is a clock probe on an open neighbourhood of any prescribed event,
  nonvanishing there and equal to `1` at the event*;
- `slabPotential_eq_of_probes_on` — hence slab potentials are determined by their probes, in every
  dimension.

`ClockSlabConformal.lean` then closes the card's own reconstruction on a slab, in every dimension:

- `gradPair_slabLift` — `Γ(σ, σ) = -4 ∂ξσ ∂ησ` for a slab lift; the null directions pair only with
  each other;
- `isC1On_univ_of_contDiff`, `planarFstU`, `planarSndU`, `contDiff_planarFstU/SndU` — a smooth
  bivariate function packaged with its partial derivatives to all orders;
- **`exists_slab_conformalPotential`** — the effective potential `μ e^{2σ} - (a □σ + a² Γ(σ,σ))` of a
  slab conformal factor is itself a slab potential, and continuously differentiable. This is what
  keeps the statement from being vacuous: the hypothesis class is inhabited by every smooth `σ` of
  slab form;
- `openProbes_conformalPotential_slab` — hence a slab clock species has probes on open regions at
  every event, in every dimension;
- **`twoSpecies_scale_reconstruction_slab`** — *the two-species conformal clock scale law holds
  unconditionally, in every dimension, for a conformal factor depending only on the two null
  coordinates*. No hypothesis on the probe families: the required probes are proved to exist.

In dimension two every conformal factor is of slab form, so this contains the two-dimensional
theorem.

`ClockSlabSeparable.lean` multiplies the slab block by the fully separable construction. On a
diagonal chart the gradient pairing is a sum over coordinates; a slab lift has no transverse
derivative and a product of transverse coordinate factors has no derivative in the two null
directions, so the two factors pair to zero and the Leibniz rule turns a product of solutions into a
solution for the sum of the potentials:

- `gradPair_slabLift_boxProduct` — the two factors are metrically orthogonal;
- `slabSeparable_solves` — the product of a slab probe with transverse coordinate factors solves the
  sum equation;
- **`exists_clockProbe_on_slabSeparable`** — *in every dimension, every potential of the form*

  `V(x) = v(x⁰ + x¹, x⁰ - x¹) + ∑ⱼ Vⱼ(xʲ)`

  *with `v` and every `Vⱼ` continuously differentiable admits a clock probe on an open neighbourhood
  of any prescribed event, nonvanishing there and equal to `1` at the event.* The two-dimensional
  block is solved by Goursat, each transverse block by Picard–Lindelöf.

That class is strictly larger than either constituent: it contains the fully separable potentials
(empty slab part) and the slab potentials (no transverse profiles), and neither contains the other.

The coupled case in dimension `≥ 3` — a potential which is neither a function of the two null
coordinates alone nor a sum of one-variable profiles — is settled below by
`ClockDatum.exists_clockProbe_nullTransverse`, for one transverse coordinate with analytic
dependence. What follows is the analysis that reaches it. There the
characteristic reduction produces

`∂ξ∂η u = (Δ⊥ u + V u) / 4`,

so the Volterra iteration loses two transverse derivatives at each step. The classical remedy is to
run it in a *scale* of Banach spaces of transverse-analytic functions, paying for the lost
derivatives by shrinking the radius of analyticity: this is the Ovsyannikov / Nirenberg–Nishida form
of Cauchy–Kovalevskaya. `ClockAnalyticWienerScale.lean` builds the scale in its concrete Fourier
form — a function analytic in a strip of half-width `ρ` around a circle is exactly one whose Fourier
coefficients are summable against `e^{ρ|k|}`:

- `sq_le_four_mul_exp`, `sq_mul_exp_neg_le` — the elementary bound `t² e^{-δt} ≤ 4/δ²` behind the
  whole method, obtained by squaring `1 + s ≤ e^s`;
- `wienerNorm`, `WienerSummable`, `wienerNorm_nonneg`;
- `wienerSummable_of_le`, `wienerNorm_mono` — the scale is decreasing;
- `sqMul`, `abs_sqMul_weight_le`, `wienerSummable_sqMul`, **`wienerNorm_sqMul_le`** — *the transverse
  Laplacian maps radius `ρ` to radius `ρ'` with norm at most `4/(ρ-ρ')²`*. This is the derivative-loss
  estimate the iteration is built on.

- `wienerConv`, `exp_weight_triangle`, `wienerSummable_conv`, **`wienerNorm_conv_le`** — each radius
  carries a Banach-algebra estimate `‖f ⋆ g‖_ρ ≤ ‖f‖_ρ ‖g‖_ρ`, since multiplication of functions is
  convolution of coefficients and the weight is submultiplicative by `|k| ≤ |j| + |k - j|`. This is
  how the potential enters the iteration. The proof runs on `ℤ × ℤ` through the shear
  `(k, j) ↦ (j, k - j)`.

`ClockStripCauchyScale.lean` builds the same scale in its sup-norm form, where the elements are
functions rather than sequences — this is the form the passage back to the clock equation needs,
since there the transverse Laplacian must be the actual second derivative:

- `imStrip`, `isOpen_imStrip`, `imStrip_mono`, `closedBall_subset_imStrip` — the open strip
  `|Im z| < ρ` and the discs it contains;
- **`norm_deriv_le_on_imStrip`** — one derivative costs one power of the gap: `‖f'‖ ≤ 2M/(ρ-ρ')` on
  the strip of half-width `ρ'`, by Cauchy's estimate on a disc of radius `(ρ-ρ')/2`;
- **`norm_deriv_deriv_le_on_imStrip`** — two derivatives cost two powers: `‖f''‖ ≤ 16M/(ρ-ρ')²`,
  applying the first estimate twice through the intermediate half-width `(ρ+ρ')/2`. Between the two
  applications the derivative must be known holomorphic, which is `AnalyticOnNhd.deriv_of_isOpen`.

The two forms are the same scale seen from opposite sides: the coefficient form supplies the algebra
estimate, the sup-norm form the passage back to functions.

`ClockOvsyannikovSeries.lean` supplies the convergence estimate that makes the iteration close. Each
step pays two transverse derivatives and earns a double integration, so after `m` steps, with the
radius shrunk in `m` equal instalments,

`(loss) × (gain) = (m/δ)^{2m} × T^{2m}/(m!)² = (m^m/m!)² (T/δ)^{2m}`.

Everything therefore rests on `m^m/m! ≤ e^m`, which is nothing but the single term `m^m/m!` of the
exponential series evaluated at `m`:

- `pow_self_le_exp_mul_factorial`, `pow_self_div_factorial_le_exp` — that bound;
- `sq_pow_self_div_factorial_le` — squared, so the loss–gain product becomes geometric;
- **`ovsyannikov_term_le`**, **`summable_ovsyannikov`** — the `m`-th term is at most `(A e²)^m`, and
  the iteration converges as soon as `A e² < 1`, that is as soon as the rectangle is small compared
  with the radius of analyticity.

The statement is in terms of an abstract ratio `A`, so it serves either form of the scale — the
coefficient form, where two derivatives cost `4/(ρ-ρ')²`, or the sup-norm form, where they cost
`16/(ρ-ρ')²`.

`ClockOvsyannikovInduction.lean` pins the step down exactly. The step is performed at the
intermediate radius `σ = ρ + (ρ₀-ρ)/(m+1)`, so that the loss factor `K/(σ-ρ)²` is exactly
`K(m+1)²/(ρ₀-ρ)²` while the gap remaining above `σ` is `(ρ₀-ρ)·m/(m+1)`, and the two integrations
contribute `1/(m+1)²`:

- `sq_pow_ratio_intermediate` — the shrunken gap cancels the `m^{2m}` carried by the induction
  hypothesis;
- **`ovsyannikov_step_identity`** — the three factors multiply to *exactly* the next bound. Not an
  inequality with room to spare: the leftover `(m+1)²` is absorbed precisely by
  `((m+1)!)² = (m!)²(m+1)²`. That is what makes the scheme close rather than merely almost close;
- `ovsyannikov_bound_le`, **`summable_ovsyannikov_bound`** — the bound carried by the induction,
  `Kᵐ m^{2m} T^{2m}/((m!)²(ρ₀-ρ)^{2m})`, is dominated by `(K T² e²/(ρ₀-ρ)²)ᵐ` and hence summable
  whenever `K T² e² < (ρ₀-ρ)²`.

`ClockAnalyticStepOperator.lean` assembles the operator that the iteration actually applies. In the
coefficient form the characteristic equation reads, coefficient by coefficient, as an infinite
system of Goursat problems whose right-hand side is the image of the state under
`w ↦ (V ⋆ w - k² w)/4`:

- `wienerSummable_of_abs_le_add`, `wienerNorm_le_add`, `wienerSummable_const_mul`,
  `wienerNorm_const_mul` — the triangle inequality in the form a difference needs, and homogeneity;
- `clockCoeffStep` — the operator;
- `wienerSummable_clockCoeffStep`, **`wienerNorm_clockCoeffStep_le`** — *it maps radius `ρ` to
  radius `ρ'` with norm at most `1/(ρ-ρ')² + ‖V‖_ρ/4`*. The Laplacian part is the derivative loss of
  the scale, the potential part is the Banach-algebra estimate, and nothing else enters.

That is precisely the hypothesis the step identity consumes, with `K = 1 + ‖V‖_ρ(ρ₀-ρ)²/4`.

`ClockFourierSynthesis.lean` closes the other end: it turns coefficients back into a field on the
transverse circle and checks that multiplication by `-k²` really is the second derivative there:

- `mul_exp_neg_le`, `abs_le_exp_weight`, `sq_le_exp_weight` — one power of `k` costs `1/ρ`, two cost
  `4/ρ²`, against the exponential weight;
- `summable_abs_of_wienerSummable`, `summable_of_wienerSummable`, `summable_absMul`,
  `summable_absSq` — hence a sequence in the scale has coefficients summable against any power;
- `cosSeries`, `sinSeries`, `hasDerivAt_cos_term`, `hasDerivAt_sin_term`;
- `hasDerivAt_cosSeries`, `hasDerivAt_sinSeries` — the series may be differentiated term by term,
  by mathlib's `hasDerivAt_tsum` with the summable dominating bound `|gₖ||k|`;
- `abs_int_le_sq`, **`deriv_deriv_cosSeries`** — *`(∑ₖ gₖ cos kz)'' = -∑ₖ k² gₖ cos kz`*. The
  transverse Laplacian of the synthesised field is exactly the multiplication that the coefficient
  iteration performs.

`ClockFourierProduct.lean` supplies the other half of the dictionary — synthesis turns convolution
into multiplication, which is what lets the synthesised potential multiply the synthesised field:

- `EvenCoeff`, `evenCoeff_sqMul`, `evenCoeff_wienerConv` — evenness is preserved by multiplication by
  `k²` and by convolution, so a potential even in the transverse variable produces an even state at
  every step of the iteration and every quantity stays real. The restriction costs nothing;
- `summable_prod_of_abs_bound`;
- **`cosSeries_wienerConv`** — *`(∑ⱼ Vⱼ cos jz)(∑ₘ gₘ cos mz) = ∑ₖ (V ⋆ g)ₖ cos kz`*. The proof is the
  Cauchy product on `ℤ × ℤ`, the product-to-sum identity `2 cos a cos b = cos(a+b) + cos(a-b)`, the
  involution `m ↦ -m` which identifies the two halves using evenness, and the shear `(k,j) ↦ (j,k-j)`
  which folds the result back into a convolution.

The dictionary between the coefficient picture and the field picture is now complete in both
directions: `-k²` is the transverse Laplacian, and `⋆` is multiplication.

`ClockOvsyannikovRecursion.lean` closes the estimate side. **`ovsyannikov_induction`** takes a
single hypothesis — one step with loss `K/(σ-ρ)²` and the gain of a double integration, in the exact
form the double integral produces it — and derives the closed bound

`N m ρ x y ≤ Kᵐ m^{2m} xᵐ yᵐ / ((m!)² (ρ₀-ρ)^{2m})`

at every stage, by induction with the intermediate radius `σ = ρ + (ρ₀-ρ)/(m+1)`. The statement is
purely scalar: `N m ρ x y` is any nonnegative bound on the `m`-th stage at radius `ρ` over a
rectangle of sides `x` and `y`. So it applies verbatim to either form of the scale, and the concrete
construction has only to discharge the step. The `m = 0` stage needs the base hypothesis rather than
the induction hypothesis, since there the intermediate radius is `ρ₀` itself.

`ClockIteratedIntegralBound.lean` supplies the integration that discharges that hypothesis:

- `integral_pow_zero_left` — `∫₀ˣ sᵐ ds = x^{m+1}/(m+1)`, by the fundamental theorem of calculus
  rather than by importing the special-functions integral tables;
- `abs_integral_pow_bound` — a power-dominated integrand integrates to a power;
- **`abs_iterated_integral_le`** — *an integrand dominated by `c sᵐ tᵐ` on the rectangle integrates
  to at most `c x^{m+1} y^{m+1}/(m+1)²`*. Both factorials of the recursion come from here, one from
  each characteristic direction, and they are exactly what compensates the derivative loss.

`ClockStripStepOperator.lean` moves the operator itself into the sup-norm form, which is where the
iteration should be run. The reason is the double integration: in a supremum norm

`‖∫∫ F‖ ≤ ∫∫ ‖F‖`

is the pointwise monotonicity of the integral, whereas in an `ℓ¹` norm it is an exchange of a sum
and an integral. So the iterates are functions holomorphic on a strip, and the operator is the
honest differential operator:

- `clockStripStep V w = (w'' + V w)/4`;
- `differentiableOn_clockStripStep` — it preserves holomorphy, since the derivative of a holomorphic
  function on an open set is holomorphic;
- **`norm_clockStripStep_le`** — *it maps radius `ρ'` to radius `ρ` with norm at most
  `4/(ρ'-ρ)² + ‖V‖/4`*, by Cauchy's estimate for the second derivative together with the product
  bound. This is the sup-norm counterpart of the coefficient estimate, and it is the form the
  recursion consumes.

Since the iterates take values in a space of holomorphic functions, the double-integration bound is
needed for a Banach-valued integrand; `ClockIteratedIntegralBound.lean` also carries that form:

- `norm_integral_pow_bound`, **`norm_iterated_integral_le`** — the same estimate with `‖·‖` in place
  of `|·|`, for an integrand valued in any real normed space. Nothing changes in the proof: the norm
  of an integral is at most the integral of the norm, and the comparison is then between real
  integrals.

Everything the construction needs is now proved: the algebra estimate, the derivative loss in both
forms, the step operator in both forms, the exact step identity, the convergence bound, the
recursion, the double integration in scalar and vector form, and both halves of the synthesis
dictionary. What remains is to define the iterates

`W₀ = 1`,  `W_{m+1}(ξ,η,z) = ∫₀^ξ ∫₀^η (W_m(s,t,·)'' + V W_m(s,t,·))(z)/4 dt ds`,

assemble the estimates into the step hypothesis, and identify the limit with a clock probe. The
first thing that needed proving about them was a regularity fact of independent interest, and
`ClockParametricHolomorphy.lean` now has it:

- `iteratedDeriv_two`, `iteratedDeriv_eq_circleIntegral` — Cauchy's formula for derivatives, solved
  for the derivative: `f⁽ⁿ⁾(z) = (2πi/n!)⁻¹ ∮_{|ζ-z|=R} f(ζ)/(ζ-z)^{n+1} dζ`;
- **`continuous_iteratedDeriv_parametric`**, **`continuous_deriv_deriv_parametric`** — *the
  derivatives of a family of holomorphic functions depending continuously on parameters depend
  continuously on those parameters.*

There is no such statement for `deriv` directly, and none can be had by differentiating: a
derivative is a limit, and limits do not commute with parameters for free. Cauchy's formula converts
the derivative into a contour integral of the function itself, a contour integral is an interval
integral in the angle, and continuity of a parametric interval integral is standard.

The iteration needs it jointly in the null coordinates and the transverse point, since the next
iterate integrates in the former and is evaluated at the latter. Moving the contour with the point
costs nothing, because the integral only ever sees `ζ - z`, which is `circleMap 0 R θ` and does not
depend on `z`:

- `cauchySecond`, `circleMap_eq_add`, `continuous_cauchySecond` — the Cauchy representation of the
  second derivative as a function of parameters and point together, and its joint continuity;
- **`continuousAt_deriv_deriv_parametric`** — *for a family holomorphic on the strip of radius `ρ'`,
  the second derivative is continuous at every point of the strip of radius `ρ < ρ'`, jointly in the
  parameters and the point.* The representation is valid only on the strip, so the transfer is by
  congruence on the neighbourhood where it holds.

This is what makes the iterated integrals defining the iterates well defined. The parameter space is
an arbitrary topological space — no countability or local compactness is needed anywhere — so the
same statements serve the null-coordinate pair, a single coordinate, or the pair together with the
transverse point.

The iterates are continuous only on a strip, not on the whole plane, so the joint-continuity
hypothesis has to be localised. Nothing in the argument ever uses the family away from the contour,
so continuity on any region containing the closed disc suffices:

- `iteratedDeriv_eq_circleIntegral` now asks only for `ContinuousOn` on the closed disc — which is
  what Cauchy's formula itself asks for;
- `continuous_iteratedDeriv_parametric_on`, `continuous_deriv_parametric_on` — the parametric
  continuity of the derivatives from a `ContinuousOn` hypothesis on `univ ×ˢ U`, for any region `U`
  containing the disc.

This localisation is what the holomorphy of the iterates needs, since the retraction that repairs
continuity destroys holomorphy and cannot be used there. With it,
`ClockParametricIntegralHolomorphy.lean` carries the localised holomorphy statement as well:

- **`hasDerivAt_intervalIntegral_of_holomorphic_on`**,
  **`differentiableOn_intervalIntegral_of_holomorphic_on`** — *the integral of a family holomorphic
  on a strip is holomorphic on that same strip, assuming only continuity on the strip.* All three
  places where global continuity was used — the compact bound, the slices, and the measurability of
  `t ↦ (F t)'(z)` — are local to the strip, the last one through the localised parametric-derivative
  continuity.

`ClockParametricIntegralHolomorphy.lean` closes the last purely analytic gap on this route — the
iterates are holomorphic, so the induction can continue and differentiate twice again:

- `continuous_deriv_parametric` — the first derivative of a holomorphic family is continuous in the
  parameter, which is what makes the derivative measurable in the integration variable;
- **`hasDerivAt_intervalIntegral_of_holomorphic`**, `differentiableAt_…`,
  **`differentiableOn_intervalIntegral_of_holomorphic`** — *the integral of a family holomorphic on
  the strip of radius `ρ'` is holomorphic on the strip of radius `ρ < ρ'`, with the expected
  derivative* `∫ (F t)'(z) dt`.

The proof is differentiation under the integral sign with a *complex* parameter: mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` is stated over any `RCLike` field, so it produces
the complex derivative directly and no appeal to Morera's theorem is needed. The domination it
requires is Cauchy's estimate on a disc of radius `(ρ'-ρ)/4` about each nearby point, with the bound
uniform in the integration variable by compactness of `[a,b] × closedBall z ((ρ'-ρ)/2)`.

The strip does not in fact shrink: `differentiableOn_intervalIntegral_of_holomorphic_self` applies
the above at an intermediate radius chosen separately for each point, and so covers the whole strip.
Holomorphy of the iterates therefore persists at a fixed radius; only the *bounds* shrink, which is
what the Ovsyannikov recursion is for.

One mismatch remains between the corpus and mathlib's parametric-integral statements: those ask for
a globally continuous integrand, whereas the iterates are continuous only on a strip. The repair is
a retraction, which changes nothing inside:

- `stripRetract`, `continuous_stripRetract`, `stripRetract_im`, `abs_stripRetract_im_le`,
  `stripRetract_eq_self` — the continuous retraction of the plane onto the closed strip of half-width
  `ρ`, which is the identity there.

`ClockStripIteratedContinuity.lean` uses it to give the iterates their continuity:

- `continuous_iteratedIntegral` — for a globally continuous family, the double integral
  `∫₀^ξ ∫₀^η G s t z` is continuous jointly in `(ξ, η, z)`, by two applications of the
  parametric-integral continuity theorem, once per direction;
- **`continuousAt_iteratedIntegral_of_strip`** — *the same for a family continuous only on a strip,
  at every point of that strip*. The retraction onto a slightly smaller closed strip makes the
  integrand global without changing any value inside, and the smaller radius is chosen separately
  for each point, exactly as for holomorphy;
- **`continuousAt_deriv_deriv_of_strip`** — the joint continuity of the second derivative from a
  hypothesis of continuity on the strip alone. Here the retraction is legal, because what is being
  proved is continuity and not holomorphy: anchoring the Cauchy contour at the *retracted* point
  makes the representation globally continuous, and inside the strip the retraction is the identity.

- `continuousAt_innerIntegral_of_strip` — the same for a single integration, which is the form the
  holomorphy statement consumes, since it takes the two integrations one at a time.

With these the two properties the iterates need — holomorphy and joint continuity — are both
available from hypotheses the iterates actually satisfy, at a fixed radius. Nothing shrinks: at each
point of the strip the intermediate radius is chosen between `|Im z|` and the radius of the strip,
so every statement holds on the whole strip.

`ClockIterates.lean` defines the iteration and proves exactly that:

- `clockIterate` — `W₀ = 1` and
  `W_{m+1}(ξ,η) = ∫₀^ξ ∫₀^η (W_m(s,t)'' + V·W_m(s,t))/4 ds dt`, with `clockIterate_zero` and
  `clockIterate_succ`;
- **`clockIterate_regular`** — *for a potential holomorphic and continuous on the strip, every
  iterate is holomorphic in the transverse variable on that same strip, and the family is continuous
  jointly in the two null coordinates and that variable.*

The induction is exactly as designed: the step operator applied to the previous iterate is
continuous by the localised second-derivative continuity; the inner integral is then holomorphic and
jointly continuous; and the outer integral inherits both. No radius is lost at any stage.

`ClockIterateBound.lean` then proves that the iterates obey the bound the scheme predicts:

- `continuousAt_clockStripStep_clockIterate`, `continuous_clockStripStep_slice` — the step operator
  applied to an iterate is continuous, in the form the double-integration estimate requires;
- **`clockIterate_norm_le`** — *for a potential holomorphic, continuous and bounded by `Mv` on the
  strip of radius `ρ₀`,*

  `‖W_m(s,t,z)‖ ≤ Kᵐ m^{2m} sᵐ tᵐ / ((m!)² (ρ₀-ρ)^{2m})`  for `|Im z| ≤ ρ < ρ₀`,

  *with `K = 4 + Mv ρ₀²/4`.* Each step is taken at the intermediate radius
  `σ = ρ + (ρ₀-ρ)/(m+1)`; the step operator loses `4/(σ-ρ)²` and the potential contributes `Mv/4`,
  which together are at most `K/(σ-ρ)²` because `σ-ρ ≤ ρ₀`; the double integration supplies
  `s^{m+1}t^{m+1}/(m+1)²`; and the closing algebra is the step identity already proved. The stage
  `m = 0` uses the normalisation `W₀ = 1`, which holds on the whole plane, since there the
  intermediate radius is `ρ₀` itself.

Combined with the convergence estimate, the series `∑ₘ W_m` therefore converges. `ClockSolution.lean`
records that:

- `clockSolution V ξ η z = ∑ₘ W_m(ξ, η, z)`;
- **`summable_clockIterate`** — *the series converges absolutely for `|Im z| ≤ ρ < ρ₀` on any
  rectangle of side at most `T` with `K T² e² < (ρ₀ - ρ)²`*, by domination against the geometric
  series of the convergence estimate.

Checking that the sum solves `∂ξ∂η u = (u'' + V u)/4` needs the sum to be differentiable twice in
the transverse variable, term by term. `ClockSeriesDerivative.lean` supplies that:

- `convex_imStrip`, `isPreconnected_imStrip` — the strip is convex, hence preconnected, which is what
  the localised form of mathlib's term-by-term differentiation requires;
- **`hasDerivAt_tsum_of_holomorphic`**, `differentiableOn_tsum_of_holomorphic`,
  `deriv_tsum_of_holomorphic` — *a series of functions holomorphic on a strip with summable
  sup-bounds may be differentiated term by term on any smaller strip*, the bound on the derivatives
  being Cauchy's estimate applied to the bound on the functions.

- `differentiableOn_deriv_of_holomorphic`, **`deriv_deriv_tsum_of_holomorphic`** — iterating it on
  the family of first derivatives, which is again holomorphic and carries the summable bound Cauchy's
  estimate supplies, gives *the second derivative of the sum as the sum of the second derivatives*.

`ClockSeriesIntegral.lean` supplies the other exchange:

- **`tsum_intervalIntegral_of_bound`** — *a series of continuous functions with summable uniform
  bounds may be integrated term by term over an interval.* This is mathlib's
  `integral_tsum_of_summable_integral_norm` transported to interval integrals, which differ from set
  integrals by a sign that is the same on both sides.

Both exchanges the equation needs — sum with derivative, sum with integral — are therefore
available, and `ClockStepSeries.lean` applies the first to the operator itself:

- **`clockStripStep_tsum`** — *the step operator commutes with a series of holomorphic functions
  carrying summable bounds.* It is linear, so this is the term-by-term differentiation together with
  the behaviour of a sum under multiplication by a fixed value and division by a constant; the
  summability of the second derivatives is Cauchy's estimate applied to the bound on the functions.

`ClockStepMajorant.lean` supplies what those exchanges need — a bound on the integrand that is
uniform over the rectangle and summable in `m`:

- `stepMajorant`, **`norm_clockStripStep_clockIterate_le`**, `summable_stepMajorant` — taking the
  intermediate radius to be the midpoint `(ρ + ρ₀)/2` makes both gaps equal to `(ρ₀-ρ)/2`, and the
  majorant is the iterate bound at that radius times the norm of the step operator between the two
  strips. It is summable exactly when the rectangle is small compared with the half-gap.

`ClockSumIntegral.lean` performs the inner of the two integrations:

- **`tsum_inner_integral`** — the sum passes through `∫₀^η`, since the integrand is continuous in the
  integration variable for a fixed value of the other and the majorant dominates it uniformly on the
  interval. (The integral-exchange lemma was correspondingly weakened to ask for the bound only on
  the interval of integration, which is all the iterate bound provides.)

- **`tsum_outer_integral`** — and through `∫₀^ξ` as well: the inner integral is continuous in the
  outer variable, and is dominated by the majorant times the length of the inner interval.

- **`clockStripStep_tsum_clockIterate`** — and the step operator commutes with the sum of the
  iterates, which is the operator exchange instantiated at the family the construction produces. The
  three radii it needs are taken inside the gap between `ρ` and the midpoint `(ρ+ρ₀)/2`, where the
  iterate bounds already hold.

All three exchanges are therefore available at the iterates themselves, and combining them gives the
equation:

- **`clockSolution_integral_equation`** — *for a potential holomorphic, continuous and bounded on the
  strip of radius `ρ₀`, and a rectangle small compared with the half-gap,*

  `u(ξ,η,z) = 1 + ∫₀^ξ ∫₀^η (u(s,t,·)'' + V·u(s,t,·))(z)/4 ds dt`  for `|Im z| ≤ ρ < ρ₀`.

  Split off the `m = 0` term, rewrite the rest by the recursion, and pull the sum inside the outer
  integral, the inner integral and the operator in turn.

This is the integral form of the characteristic clock equation. Differentiating it needs its
right-hand side to be continuous in the null coordinates:

- `boxClamp` and **`continuousAt_clockStripStep_clockSolution`** — the right-hand side is a series of
  continuous functions, but the majorant holds only on the rectangle, so the arguments are clamped to
  it before summing; inside the rectangle the clamp is the identity, which gives continuity at every
  interior point.

Every estimate of the construction was first proved on a quarter-neighbourhood `0 ≤ s, t ≤ T`,
which is not enough: a clock probe must solve the equation on a genuinely open neighbourhood of the
event, two-sided in each null coordinate, and moving the base point does not help — wherever the
normalisation is placed, the event needs room on both sides of it. The estimates are now restated on
the two-sided rectangle `|s|, |t| ≤ T`. None of the arguments changed; only the interval bookkeeping
did. The chain is:

- `abs_integral_abs_pow` — `|∫₀ʸ |t|ᵐ dt| = |y|^{m+1}/(m+1)`, whatever the sign of `y`;
- `norm_integral_le_abs_of_norm_le` — an interval integral dominated in norm on `Ι a b` is bounded by
  the absolute value of the dominating integral, on an interval of either orientation;
- **`norm_iterated_integral_le_abs`** — hence the double-integration bound in two-sided form: an
  integrand dominated by `c |s|ᵐ|t|ᵐ` on the rectangle spanned by the endpoints integrates to at most
  `c |x|^{m+1}|y|^{m+1}/(m+1)²`, whatever the signs of `x` and `y`;
- `abs_le_abs_of_mem_uIcc_zero`, `abs_le_abs_of_mem_uIoc_zero` — a point of the interval spanned by
  `0` and `x` is no further from the origin than `x` is, which is what replaces the interval
  splittings the one-sided proofs used;
- and then, unchanged in substance, `clockIterate_norm_le`, `summable_clockIterate`,
  `norm_clockStripStep_clockIterate_le`, `tsum_inner_integral`, `tsum_outer_integral`,
  `clockStripStep_tsum_clockIterate` and `clockSolution_integral_equation`, all now on `|ξ|, |η| ≤ T`.

The clamp used for the continuity of the right-hand side is symmetric accordingly:
`boxClamp T x = max (-T) (min T x)`, with `abs_boxClamp_le` and `boxClamp_eq_self`, and the clamped
right-hand side `clampedStep` is continuous on the whole plane of null coordinates
(`continuous_clampedStep`), agreeing with the true one inside the rectangle (`clampedStep_eq`).

The two applications of the fundamental theorem of calculus are then immediate, and give the
differential form of the equation:

- `clockSolution_eq_clamped` — on the rectangle the solution is `1` plus the double integral of the
  clamped step, whose integrand is globally continuous;
- `continuous_clampedInner` — the inner integral is continuous in the outer null coordinate;
- **`hasDerivAt_clockSolution_fst`**, `deriv_clockSolution_fst` — hence the solution is
  differentiable in the first null coordinate at every interior point, with derivative
  `∫₀^η (u(ξ,t,·)'' + V·u(ξ,t,·))(z)/4 dt`. The clamped identity is transported to the solution along
  an eventual equality on the open rectangle, which is where the two-sidedness is used;
- **`hasDerivAt_deriv_clockSolution`** — **the characteristic clock equation.** For `|ξ|, |η| < T`
  and `|Im z| ≤ ρ`,

  `∂η ∂ξ u (ξ, η, z) = (u(ξ,η,·)'' + V·u(ξ,η,·))(z)/4`;

- `clockSolution_zero_zero` — with the normalisation `u(0,0,z) = 1`.

The potential is not required to be independent of the null coordinates, and this is the whole point
of the construction: a potential depending only on the transverse variable is separable, and the
separable case was already closed. The class carried by the chain is

- `StripPotential V ρ` — `V : ℝ → ℝ → ℂ → ℂ` jointly continuous on `ℝ² × {|Im z| < ρ}` and
  holomorphic in the transverse variable for each pair of null coordinates, with a uniform bound
  `‖V s t z‖ ≤ Mv`. No regularity in the null coordinates is asked;
- `stripPotential_const` — a potential independent of the null coordinates is one of these.

So the dependence on the null coordinates is arbitrary up to continuity, and the dependence on the
transverse one is analytic on a strip. Every statement of the chain — the iterates, their holomorphy
and joint continuity, the Ovsyannikov bound, the majorant, the three exchanges, the integral
equation, and the characteristic equation above — is proved at that generality.

The transverse variable is settled:

- **`differentiableOn_clockSolution`** — the solution is holomorphic on the strip for every pair of
  null coordinates in the rectangle, by the Weierstrass M-test on the Ovsyannikov majorant;
- `continuousOn_clockSolution_clamped`, **`continuousAt_clockSolution`** — and jointly continuous in
  the two null coordinates and the transverse variable, at every interior point of the rectangle;
- **`eventually_clockSolution_ne_zero`** — hence, with the normalisation, nonvanishing on a
  neighbourhood of the event. This is the nonvanishing a clock probe asks for.

The geometric half of the conversion is done. A field on Minkowski space of dimension `n + 3` that
depends on the two null coordinates and on the single transverse coordinate `x²` — not a slab lift,
which is constant transversally — is handled by:

- `IsC1On3`, **`hasFDerivAt_uncurry3`** — the three-variable form of "continuous partial derivatives
  imply total differentiability". It is not a fresh argument: group the two null variables, apply the
  bivariate statement on the plane at a fixed transverse value, then apply it once more with the
  plane as first factor and the transverse line as second;
- `nullTransCLM`, `nullTransLift`, `nullTransBox` and the four first-order `coordPartial`
  identities — `∂₀ = A + B`, `∂₁ = A − B`, `∂₂ = C`, and `0` in the remaining directions;
- **`dalembert_nullTransLift`** — hence
  `□ u = −2(∂η∂ξ u + ∂ξ∂η u) + ∂₂∂₂ u` in dimension `n + 3`: the pure null terms cancel between the
  timelike and the first spacelike direction exactly as on a slab, the transverse coordinate
  contributes its own second derivative, and the rest contribute nothing;
- **`solvesPotentialWaveAt_nullTransLift`**, `solvesPotentialWaveOn_nullTransLift` — so a field
  satisfying `∂η∂ξ u + ∂ξ∂η u = (∂₂∂₂ u + V u)/2` is a clock probe for `V`, and `V` may now depend on
  all three coordinates.

Of the analytic half, the mixed derivative is now proved in both orders:

- `hasDerivAt_parametric_intervalIntegral` — the Leibniz rule of the Goursat bootstrap, generalised
  to an integrand with values in any Banach space over the reals, so that it serves the complex
  clock iteration as well;
- `continuous_clampedInnerSnd`, **`hasDerivAt_clockSolution_snd`**, `deriv_clockSolution_snd` — the
  solution is differentiable in the *second* null coordinate, with derivative
  `∫₀^ξ (u(s,η,·)'' + V(s,η)·u(s,η,·))(z)/4 ds`. This one sits inside the outer integral, so it is
  the Leibniz rule rather than the fundamental theorem of calculus; the clamped data are continuous
  on the whole plane, so there is no domination hypothesis left to check;
- **`hasDerivAt_deriv_clockSolution_snd`** — differentiating that once more in the first null
  coordinate returns the same step operator. So `∂ξ∂η u = ∂η∂ξ u = (u'' + V u)/4`, which is the
  symmetric pair `Ab + Ba` the chart d'Alembertian consumes.

The transverse direction is settled the same way, and the Cauchy representation does all the work:

- `continuousAt_iteratedDeriv_of_strip` — for a family holomorphic on a strip and jointly continuous
  there, *every* iterated transverse derivative is jointly continuous. (The corpus previously had
  only the second-derivative case; the general statement is the same proof with the order left
  free, and `continuousAt_deriv_of_strip` and `continuousAt_deriv_deriv_of_strip` are now its two
  corollaries.);
- `clampedSolution`, `continuousAt_deriv_clampedSolution`,
  `continuousAt_deriv_deriv_clampedSolution` — hence the solution's transverse derivatives are
  jointly continuous in all three variables;
- **`continuousAt_clampedStep_joint`** — hence so is the step operator itself, as a function of the
  two null coordinates *and* the transverse point. This is the joint continuity every later
  interchange consumes;
- `differentiableOn_clampedStep`, `differentiableOn_clampedInner`,
  `hasDerivAt_clampedInner_transverse`, `hasDerivAt_clampedBox_transverse` — the transverse
  derivative passes through each integration in turn;
- **`deriv_clockSolution_transverse`** — so the transverse derivative of the solution is the double
  integral of the transverse derivative of the step operator,

  `∂_z u(ξ,η,z) = ∫₀^ξ ∫₀^η ∂_z S(s,t,z) ds dt`.

  Differentiating *that* along either null coordinate is again the fundamental theorem of calculus,
  so the four mixed null–transverse second derivatives cost nothing beyond this identity.

The four mixed null–transverse derivatives follow, and the second transverse one with them:

- **`continuousAt_dClampedStep_joint`**, `continuous_dClampedStep_slice` — the transverse derivative
  of the step operator is jointly continuous, again by the Cauchy representation;
- `hasDerivAt_clampedOuter_transverse` — the transverse derivative also passes through the *outer*
  integration, which is the second null derivative's counterpart of the inner statement;
- **`hasDerivAt_deriv_clockSolution_transverse_fst`**, `..._snd` — hence the two null derivatives of
  the transverse derivative are `∫₀^η ∂_z S(ξ,t,z) dt` and `∫₀^ξ ∂_z S(s,η,z) ds`. These are the
  same two functions as the transverse derivatives of the two null derivatives, as the symmetry of
  mixed partials requires;
- `hasDerivAt_deriv_clockSolution_transverse` — and the second pure transverse derivative is free
  from holomorphy: the derivative of a holomorphic function is holomorphic;
- **`deriv_deriv_clockSolution_eq`** — finally, the identity one level up:
  `∂²_z u = ∫₀^ξ ∫₀^η ∂²_z S(s,t,z) ds dt`, proved by repeating on `∂_z u = ∫∫ ∂_z S` the argument
  that produced it.

That last identity is what makes the pure null second derivatives accessible without any new
analysis: `∂ξ (∂²_z u)` is the fundamental theorem of calculus applied to a double integral, so no
Cauchy representation ever has to be differentiated in a parameter.

The pure second derivatives in the null coordinates are now proved as well, and they are the one
place where the potential's own regularity enters:

- `StripPotentialC1 V Vs Vt ρ` — a strip potential which is moreover continuously differentiable in
  the two null coordinates. This is exactly the `C¹` hypothesis the statement of the theorem asks
  for, and nothing more;
- `d2ClampedStep`, **`continuousAt_d2ClampedStep_joint`** — the second transverse derivative of the
  step operator, jointly continuous;
- **`hasDerivAt_deriv_deriv_clockSolution_fst`**, `..._snd` — the two null derivatives of `∂²_z u`,
  read off `∂²_z u = ∫∫ ∂²_z S` by the fundamental theorem of calculus and the Leibniz rule;
- `clampedStepFst`, `clampedStepSnd`, `continuous_clampedStepFst`, `continuous_clampedStepSnd`,
  **`hasDerivAt_clampedStep_fst`**, **`hasDerivAt_clampedStep_snd`** — hence the step operator is
  differentiable along each null coordinate on the open rectangle, with

  `∂ξ S = (∂ξ(∂²_z u) + (∂ξ V)·u + V·∂ξ u)/4`,

  and a derivative that is continuous on the *whole* plane of null coordinates, which is what the
  Leibniz rule consumes;
- **`hasDerivAt_deriv_clockSolution_fst_fst`**, **`hasDerivAt_deriv_clockSolution_snd_snd`** — and
  therefore the pure second derivatives `∂ξ²u` and `∂η²u` exist on the open rectangle.

All nine second derivatives of the solution are now in hand.

The assembly is prepared by `ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T`, which bundles the whole
construction — potential, strip, bound, rectangle, and the decreasing chain of inner radii the
Cauchy estimates consume — into one hypothesis, and by the observation that along the *real*
transverse axis every kernel is continuous on the whole of `ℝ³`. That is not a convenience: the real
axis lies in the interior of every strip, so the transverse variable never has to be clamped, and the
parametric integrals may therefore be taken with variable limits with no further hypothesis:

- `continuous_stepReal`, `continuous_dStepReal`, `continuous_d2StepReal`, `continuous_solReal`,
  `continuous_dSolReal`, `continuous_d2SolReal`, `continuous_VReal`, `continuous_VsReal`,
  `continuous_VtReal` — the nine kernels;
- `continuous_innerReal`, `continuous_outerReal` — the two parametric integrals with variable limit;
- **`continuous_stepFstReal`**, **`continuous_stepSndReal`** — hence the two null derivatives of the
  step operator are continuous on all of `ℝ³` as well.

The packaging is done. `hasDerivAt_re` and `hasDerivAt_re_ofReal` transport every derivative through
the real part — it is a continuous linear map, so it commutes with all of them, and along the real
axis the transverse variable is a genuine real variable:

- `probeU`, `probeA`, `probeB`, `probeC`, `probeAa`, `probeAb`, `probeAc`, `probeBb`, `probeBc`,
  `probeCc` — the field, its three first derivatives and its nine second derivatives, as real
  functions of three real variables. The two mixed pairs coincide, as they must: `probeAc` serves
  both as `∂_w ∂ξ u` and as `∂ξ ∂_w u`, and `probeBc` likewise;
- `clockBox T`, `isOpen_clockBox` — the open rectangle of null coordinates, with the transverse axis
  unrestricted;
- the ten continuity lemmas, and then
- **`isC1On3_probeU`**, **`isC1On3_probeA`**, **`isC1On3_probeB`**, **`isC1On3_probeC`** — the four
  records the chart d'Alembertian consumes.

The construction closes with

- `div_four_re`, **`probe_characteristic`** — the characteristic identity in real form,
  `probeAb + probeAb = (probeCc + v·probeU)/2`, whose only new hypothesis is that the potential is
  real on the real transverse axis, so that `re(V·u) = v·re(u)`. The solution itself is *not*
  required to be real;
- `continuous_probeField`, and finally

- **`ClockDatum.exists_clockProbe_nullTransverse`** — **clock probes for potentials with coupled
  transverse dependence, in every dimension `n + 3`.** Given a potential which is continuously
  differentiable in the two null coordinates, holomorphic and bounded on a strip about the real
  transverse axis, real there, and a rectangle small compared with the strip's gap, there is an open
  neighbourhood of the event carrying a field `U` with

  `□ U + V U = 0` on that neighbourhood,  `U ≠ 0` there,  `U = 1` at the event.

  The field is the real part of the sum of the Ovsyannikov iterates, and the equation it satisfies is
  the null form of the potential wave equation, delivered by `solvesPotentialWaveOn_nullTransLift`;
- `translatePotential`, `translateSet`, `IsC1On3.translate`, `stripPotential_translate`,
  `stripPotentialC1_translate`, `ClockDatum.translate` — every ingredient of the datum is translation
  invariant, and a translated field is again continuously differentiable with translated
  derivatives. Both translations are of *functions*, not of spacetime, so the translation invariance
  of the chart d'Alembertian is never needed: the same lift applied to the shifted field already
  solves the wave equation for the unshifted potential;
- **`ClockDatum.exists_clockProbe_nullTransverse_at`** — hence the same conclusion **at an arbitrary
  event**, which is the form the determination theorems consume.

This is the first genuinely coupled case: the potential is neither a slab potential nor a separable
one, and the probe is obtained by solving rather than by an ansatz.

The two consequences follow at once:

- `ClockDatum.openProbes_nullTransverse` — such a potential has probes on open regions at every
  event;
- **`ClockDatum.nullTransversePotential_eq_of_openProbes`** — hence **it is determined by its
  probes**, in every dimension at least three;
- **`ClockDatum.twoSpecies_scale_reconstruction_nullTransverse`** — and **the two-species scale law
  `(other₁ − other₂)/massSq = e^{2σ}` holds in every dimension at least three**, whenever the
  effective potential of the massive species is of this class. The massless species needs nothing,
  since its probe is the explicit exponential.

That is the card's headline law `(7)` in a dimension and a potential class where it was previously
out of reach: the transverse dependence is coupled, not separable, and not confined to a slab.

The class is inhabited, so none of this is vacuous. `V(ξ,η,z) = sin ξ · cos η · cos z` carries a
clock datum:

- `norm_cos_le_cosh` — the cosine is bounded on a strip by `cosh` of its half-width, which is what
  makes an unbounded transverse direction admissible;
- `cosPotential`, `cosPotentialFst`, `cosPotentialSnd`, `stripPotentialC1_cosPotential`,
  `norm_cosPotential_le`, `cosPotential_im` — the potential, its two null derivatives, its
  regularity, its bound and its reality on the real axis;
- `exists_small_side` — for any bound and any pair of radii the smallness condition holds once the
  side is small enough, with the explicit admissible value `1/(1 + K)`;
- **`exists_clockDatum_coupled`** — hence a potential of the class which varies with the transverse
  coordinate (so it is not a slab potential) and with the null coordinates, exhibited with explicit
  witnesses for both.

The hypothesis of the scale law is now an explicit condition on the *scale function*, not on the
effective potential:

- `sum_of_transverse_zero₃`, **`gradPair_nullTransLift`** — the carré du champ of a field of the two
  null coordinates and one transverse one is `-4 ∂ξσ ∂ησ + (∂₂σ)²`: the null directions pair with
  each other, not with themselves, and the transverse one pairs with itself;
- `conformalPotentialTri`, **`conformalPotential_nullTransLift`**,
  `conformalPotential_eqOn_nullTransLift` — hence the effective potential `V_μ^σ = μ e^{2σ} − D_σ`
  of such a scale function is again a function of the same three coordinates, given explicitly by
  the derivatives of the scale;
- **`ClockDatum.twoSpecies_scale_reconstruction_of_scale`** — so the two-species law can be stated
  with the hypothesis moved to the scale: its effective potential, computed from its own derivatives
  by that formula, is the real part of a potential carrying a clock datum. Nothing is added to the
  mathematics; the hypothesis becomes checkable in terms of the scale itself.

Recognising a combination as admissible is now mechanical, because the class is closed under the
operations that build an effective potential:

- `BoundedC1Potential V Vs Vt ρ Mv` — holomorphic and bounded on the strip, continuously
  differentiable in the two null coordinates — and `RealOnAxis`;
- `BoundedC1Potential.add`, `.sub`, `.mul`, `.const`, `.mono`, and the same four closures for
  `RealOnAxis` — bounds add and multiply as expected;
- `BoundedC1Potential.ofFst`, `.ofSnd`, `.ofTransverse` — the three kinds of atom: a bounded
  differentiable function of either null coordinate, and a holomorphic function of the transverse
  variable bounded on the strip;
- **`BoundedC1Potential.cexp_two`** — and the exponential atom `e^{2Σ}`, bounded by `e^{2‖Σ‖}`, which
  is the one term of the effective potential that is not polynomial in the scale's derivatives.

The scale side is being built the same way. `σ(ξ,η,w) = ε sin(ξ + η + w)` depends on all three
coordinates through their sum, so it is neither a slab scale nor a separable one, and it is bounded
together with all its derivatives:

- `coupledScale`, `coupledScaleD`, `coupledScaleDD` — the scale and its two derivative levels. Every
  first derivative is `ε cos(ξ + η + w)` and every second derivative is `-ε sin(ξ + η + w)`, so the
  whole two-jet is carried by two records;
- **`isC1On3_coupledScale`**, **`isC1On3_coupledScaleD`** — those two records;
- `contDiff_nullTransLift_coupledScale` — and the lift to Minkowski space is smooth;
- `BoundedC1Potential.ofSum` — the matching atom on the complex side: a holomorphic function of the
  sum of the three coordinates, which is the first atom with genuinely coupled dependence;
- `norm_sin_le_cosh`, `coupledSin`, `coupledCos`, `boundedC1_coupledSin`, `boundedC1_coupledCos` —
  the complexified scale and its derivative, admissible on every strip;
- `coupledPotential`, **`exists_boundedC1_coupledPotential`** — and hence its effective potential
  `μ e^{2εsinθ} − 3aε sinθ + 3a²ε² cos²θ`, assembled from the atoms by the closure lemmas, is
  admissible on every strip;
- `coupledPotential_ofReal`, `realOnAxis_coupledPotential`,
  **`conformalPotentialTri_coupledScale`** — it is real on the real transverse axis, and its real
  part is exactly the effective potential computed from the *real* scale's derivatives. That is the
  identity the scale law asks for;
- `clockDatum_of_boundedC1` — and an admissible potential carries a clock datum once the radii and
  the rectangle are chosen, the rectangle by `exists_small_side`.

Hence, with no hypothesis left on the potential:

- **`twoSpecies_scale_reconstruction_coupledScale`** — **the two-species scale law holds outright for
  the coupled scale `σ(ξ,η,w) = ε sin(ξ + η + w)`, in every dimension at least three.** Two species
  of the same conjugation weight and different calibrated masses return the conformal scale of the
  spacetime,

  `(other₁ − other₂)/massSq = e^{2σ}`,

  and the admissibility of the effective potential is proved rather than assumed.

Two transverse coordinates can be coupled as well. A field of the two null coordinates and of the
*diagonal* `(x² + x³)/√2` varies along one direction of the transverse plane and is constant along
the other, so it depends on two transverse coordinates and is not a sum of one-variable profiles:

- `diagScale`, `diagCLM`, `diagTransLift`, `diagTransBox` and the five first-order `coordPartial`
  identities — `∂₀ = A + B`, `∂₁ = A − B`, `∂₂ = ∂₃ = C/√2`, and `0` elsewhere;
- `IsC1On3.const_mul`, `sum_of_transverse_zero₄` — the two bookkeeping lemmas the extra direction
  needs;
- **`dalembert_diagTransLift`** — and the d'Alembertian is *unchanged*:
  `□u = −2(∂η∂ξ u + ∂ξ∂η u) + ∂w∂w u`. The scaling by `√2` is what does it: each of `x²` and `x³`
  contributes half of the transverse second derivative, so the two together contribute exactly one;
- **`solvesPotentialWaveAt_diagTransLift`**, `solvesPotentialWaveOn_diagTransLift` — so the same
  characteristic equation makes such a field a clock probe, now for a potential depending on two
  coupled transverse coordinates.

The analytic construction is reused unchanged, and the three consequences follow as before:

- **`ClockDatum.exists_clockProbe_diagTransverse_at`** — a clock probe at every event, for a
  potential coupling two transverse coordinates;
- `ClockDatum.openProbes_diagTransverse`,
  **`ClockDatum.diagTransversePotential_eq_of_openProbes`** — such a potential is determined by its
  probes;
- **`ClockDatum.twoSpecies_scale_reconstruction_diagTransverse`** — and the two-species scale law
  holds for it.

The diagonal is one direction of the transverse plane, and nothing distinguishes it. The general
statement replaces it by an arbitrary unit direction, in any number of transverse dimensions:

- `UnitDirection`, `unitCLM`, `unitTransLift`, `unitTransBox`, `sum_smul_single` and the three
  first-order `coordPartial` identities — `∂₀ = A + B`, `∂₁ = A − B`, and `∂ⱼ = cⱼ·C` for every
  transverse direction;
- **`dalembert_unitTransLift`** — and the d'Alembertian is again unchanged. Each transverse direction
  contributes `cⱼ²` of the transverse second derivative, and the direction being a *unit* vector is
  exactly the statement that those contributions sum to one.

So the whole construction applies to a field — and a potential — depending on the two null
coordinates and on one arbitrary linear combination of all the transverse coordinates: a genuinely
coupled dependence on all of them at once. The three consequences follow as before, at this widest
generality:

- `solvesPotentialWaveAt_unitTransLift`, `solvesPotentialWaveOn_unitTransLift` and
  **`ClockDatum.exists_clockProbe_unitTransverse_at`** — a clock probe at every event;
- `ClockDatum.openProbes_unitTransverse`,
  **`ClockDatum.unitTransversePotential_eq_of_openProbes`** — the potential is determined by its
  probes;
- **`ClockDatum.twoSpecies_scale_reconstruction_unitTransverse`** — and the two-species scale law
  holds for it, in every dimension at least two.

Two or more *independent* transverse combinations need a domain of several complex variables. The
first step is built, and it shows that no several-variable complex analysis is needed:

- `tube k ρ`, `isOpen_tube`, `tube_mono`, `update_mem_tube`, `differentiable_updateSlice`,
  `differentiableOn_updateSlice` — the tube of half-width `ρ`, and the fact that a function
  holomorphic on it restricts along each coordinate through a point of the tube to a function
  holomorphic on the strip of the *same* half-width, bounded by the *same* constant;
- `cpartial`, **`cpartial_cpartial_eq`** — the partial derivative along a coordinate is the
  one-variable derivative of that slice, and the second partial derivative is the one-variable second
  derivative: the two coordinate updates collapse into one;
- **`norm_cpartial_le_on_tube`**, **`norm_cpartial_cpartial_le_on_tube`** — so the two Cauchy
  estimates the clock iteration consumes are the one-variable estimates, applied slice by slice and
  unchanged.

That is what makes the several-variable case reachable: every estimate of the scheme is a
one-variable estimate in one coordinate at a time, and the only change in the recursion is that the
transverse Laplacian contributes `k` copies of the derivative loss instead of one. The step operator
itself is then built:

- `cpartial_eq_fderiv` — the partial derivative is the total derivative evaluated on a coordinate
  vector;
- `analyticAt_cpartial`, `analyticOnNhd_cpartial` — hence the partial derivative of an analytic
  function is analytic, since the total derivative of an analytic map is analytic;
- `tubeStep`, **`analyticOnNhd_tubeStep`** — so `w ↦ (∑ᵢ ∂ᵢ²w + V w)/4` preserves analyticity on the
  tube;
- **`norm_tubeStep_le`** — and its estimate in the scale is `(4k/(ρ'−ρ)² + ‖V‖/4)·‖w‖`: each of the
  `k` coordinates costs two powers of the gap, and nothing else changes.

Regularity in several variables cannot be carried as differentiability, because the implication from
it to analyticity is Hartogs's theorem, which mathlib does not have. What the iteration carries
instead is the property its estimates actually use:

- `SliceHolo w ρ` — holomorphy along every coordinate slice through every point of the tube, with
  `sliceHolo_of_differentiableOn` and `sliceHolo_mono`;
- `norm_cpartial_le_of_sliceHolo`, `norm_cpartial_cpartial_le_of_sliceHolo`,
  **`norm_tubeStep_le_of_sliceHolo`** — all three estimates hold from slice holomorphy alone;
- **`sliceHolo_intervalIntegral`** — and slice holomorphy passes through a parametric integral for
  free, because along a fixed slice the integral is a one-variable parametric integral of a family
  holomorphic on a strip.

That last point is what the one-variable chain obtained from "differentiable on an open subset of the
plane implies analytic". Slice holomorphy replaces it, and needs nothing beyond the one-variable
tools already built.

The joint continuity the iteration also needs transports the same way:

- `tubeRetract`, `continuous_tubeRetract`, `abs_tubeRetract_im_le`, `tubeRetract_eq_self`,
  `update_tubeRetract_mem_tube` — the retraction clamping every coordinate into the closed tube,
  which is the identity inside it;
- **`continuousAt_cpartial_cpartial_of_tube`** — with it, the second partial derivative along a
  coordinate is continuous in the parameter and the point of the tube together. The Cauchy
  representation is applied on the strip, with the parameter enlarged by the point of the tube and
  the family defined everywhere by retraction;
- `continuous_iteratedIntegral` — restated for an arbitrary transverse space, so that one statement
  serves one transverse coordinate and several;
- **`continuousAt_iteratedIntegral_of_tube`**, **`continuousAt_innerIntegral_of_tube`** — hence the
  double integral and the inner integral of a family continuous on a tube are continuous on the
  smaller tube, which is what the induction defining the iterates consumes;
- `exists_inner_radius` — and a point of an open tube admits a strictly smaller tube around it, the
  finitely many coordinates having a largest imaginary part still below the half-width.

What the induction needs beyond this is that the step operator is itself slice holomorphic. Along the
coordinate being differentiated the statement is one-variable:

- `cpartial_cpartial_update_same`, `cpartial_cpartial_update_other` — the second partial derivative
  restricted to a slice is the second derivative of a slice, either at the same point or at a shifted
  one;
- **`sliceHolo_cpartial_cpartial_same`** — so along that coordinate slice holomorphy is just the fact
  that the derivative of a holomorphic function is holomorphic.

- **`sliceHolo_cpartial_cpartial_other`** — and along a *different* coordinate, where the two
  variables are genuinely separate, the argument is the Cauchy representation: the second derivative
  in one coordinate is a contour integral of the function, whose integrand is holomorphic in the
  other coordinate, so holomorphy passes through the contour integral by the one-variable statement
  already available.

Both statements hold on the *same* tube, with no loss of radius — in one variable because the
derivative of a holomorphic function is holomorphic on the same open set, and in the cross case
because the contour radius may be chosen from the point alone. That matters: an iteration losing
radius at every step would have none left.

- **`sliceHolo_tubeStep`** — hence the step operator `w ↦ (∑ᵢ ∂ᵢ²w + V w)/4` is slice holomorphic on
  the tube it starts from, which is the last regularity input the several-variable iteration needs.

With the regularity closed, the whole Ovsyannikov chain runs in several transverse variables, and it
runs on the *same* arithmetic as in one variable — the number of coordinates enters only through one
constant:

- `TubePotential V ρ`, `tubeIterate`, **`tubeIterate_regular`** — the iterates of the tube equation
  are slice holomorphic and jointly continuous in the null coordinates and the transverse point;
- **`tubeIterate_norm_le`** — the Ovsyannikov bound, with `K = 4k + Mv ρ₀²/4` in place of
  `K = 4 + Mv ρ₀²/4`. The `k` coordinates cost `k` times the derivative loss and nothing else: the
  intermediate radius, the double integration and the recursion identity are the one-variable ones,
  reused verbatim (`sq_pow_ratio_intermediate`, `ovsyannikov_step_identity`);
- `tubeSolution`, **`summable_tubeIterate`**, `tubeStepMajorant`, **`norm_tubeStep_tubeIterate_le`**,
  **`summable_tubeStepMajorant`** — the series of iterates converges on a small rectangle, and the
  step applied to the iterates has a summable majorant;
- **`cpartial_cpartial_tsum`**, **`tubeStep_tsum`** — the transverse Laplacian commutes with a
  convergent series of slice holomorphic functions. Along a fixed slice the second partial derivative
  *is* a one-variable second derivative, so `deriv_deriv_tsum_of_holomorphic` applies slice by slice
  and the finitely many coordinates are exchanged with the sum by `Summable.tsum_finsetSum`;
- **`tsum_inner_integral_tube`**, **`tsum_outer_integral_tube`**, **`tubeStep_tsum_tubeIterate`**,
  **`tubeSolution_integral_equation`** — hence the sum of the iterates satisfies the integral
  equation `u = 1 + ∫∫ (∑ᵢ ∂ᵢ²u + V u)/4`;
- `clampedTubeStep`, **`continuous_clampedTubeStep`**, **`continuousAt_tubeStep_tubeSolution`** — the
  right-hand side is continuous in the null coordinates at every interior point of the rectangle;
- **`hasDerivAt_deriv_tubeSolution`**, **`tubeSolution_zero_zero`** — and differentiating once in
  each null coordinate returns the characteristic clock equation with several coupled transverse
  coordinates, `∂η∂ξ u = (∑ᵢ ∂ᵢ²u + V u)/4`, with `u(0,0,·) = 1`.

The regularity of the solution in all its variables then follows exactly as in one variable, with the
slice replacing the strip at every step:

- **`sliceHolo_tubeSolution`**, **`continuousOn_tubeSolution_clamped`**,
  **`continuousAt_tubeSolution`**, **`eventually_tubeSolution_ne_zero`** — the solution is slice
  holomorphic in the transverse point, jointly continuous, and nonvanishing near the origin of the
  null coordinates, which is what a clock probe needs;
- **`hasDerivAt_deriv_tubeSolution_snd`** — the mixed null derivative is the same in both orders;
- `clampedTubeSolution`, **`continuousAt_cpartial_clampedTubeSolution`**,
  **`continuousAt_cpartial_cpartial_clampedTubeSolution`**, **`continuousAt_clampedTubeStep_joint`**
  — the transverse partial derivatives, and the step operator itself, are continuous jointly in the
  null coordinates and the transverse point (`continuousAt_cpartial_of_tube`, the first-order twin of
  the second-order lemma, is proved for this);
- **`sliceHolo_cpartial_same`**, **`sliceHolo_cpartial_other`**, **`sliceHolo_cpartial`** — a single
  transverse partial derivative of a slice holomorphic function is again slice holomorphic, by the
  same two arguments as for the Laplacian (derivative of a holomorphic function along its own
  coordinate; Cauchy representation of the first derivative across coordinates);
- **`hasDerivAt_tubeSolution_transverse`** — the transverse partial derivative passes through both
  integrations, so `∂ᵢu` is the double integral of `∂ᵢS`;
- **`hasDerivAt_cpartial_tubeSolution_fst`**, **`hasDerivAt_cpartial_tubeSolution_snd`**,
  **`hasDerivAt_cpartial_tubeSolution_transverse`** — the mixed null–transverse derivatives, and the
  second derivative along a single transverse coordinate;
- **`cpartial_cpartial_tubeSolution_eq`** — `∂ᵢ²u` is the double integral of `∂ᵢ²S`;
- `TubePotentialC1`, `clampedTubeStepFst`, `clampedTubeStepSnd`,
  **`hasDerivAt_deriv_tubeSolution_fst_fst`**, **`hasDerivAt_deriv_tubeSolution_snd_snd`** — and the
  two pure second null derivatives, the only place where the potential's own regularity in the null
  coordinates enters. The `k` coordinates contribute a finite sum there, differentiated term by term.

Every one of these is unconditional, with axioms `[propext, Classical.choice, Quot.sound]`. The whole
analytic layer of the clock construction is therefore available for a potential coupling arbitrarily
many transverse directions.

The geometric layer follows. Its one genuinely new ingredient is a classical theorem that mathlib
states for two factors only:

- `IsC1OnPi`, **`hasFDerivAt_of_isC1OnPi`** — *a function of finitely many real variables with
  continuous partial derivatives is totally differentiable*, with differential `z ↦ ∑ᵢ zⁱ ∂ᵢu`.
  mathlib has `hasStrictFDerivAt_uncurry_coprod` for a product of two normed spaces and nothing for a
  domain `Fin k → ℝ`; the proof here is an induction on the number of coordinates, splitting the
  first one off with `Fin.cons` and joining the two blocks with the two-factor theorem;
- `IsC1OnMulti`, **`hasFDerivAt_uncurryMulti`** — the same for the domain `(ℝ × ℝ) × (Fin k → ℝ)` of
  two null coordinates and `k` transverse ones, by grouping the null plane and using the bivariate
  statement there;
- `transIdx`, `nullMultiCLM`, `nullMultiLift`, **`coordPartial_nullMultiLift_zero/one/trans/other`**
  — the chart derivatives of a field of the two null coordinates and `k` transverse ones;
- **`sum_over_nullMultiIdx`**, **`dalembert_nullMultiLift`** — and its d'Alembertian in dimension
  `k + n + 2` is `-2(∂η∂ξ + ∂ξ∂η)u + ∑ᵢ ∂ᵢ²u`: the two null directions cancel as on a slab, each
  transverse direction contributes its own second derivative, the remaining `n` contribute nothing;
- **`solvesPotentialWaveAt_nullMultiLift`**, **`solvesPotentialWaveOn_nullMultiLift`** — so a field
  solving the characteristic equation `∂ξ∂η u = (∑ᵢ ∂ᵢ²u + V u)/4` **is** a clock probe for a
  potential depending on the two null coordinates and on all `k` transverse ones;
- `TubeDatum`, `realTube`, and the continuity of every kernel of the construction along real
  transverse points (`continuous_stepReal`, `continuous_dStepReal`, `continuous_d2StepReal`,
  `continuous_solReal`, `continuous_dSolReal`, `continuous_d2SolReal`, `continuous_stepFstReal`,
  `continuous_stepSndReal`) — the real points lie in the interior of every tube, so the transverse
  variables are never clamped and the kernels are global objects.

The probe data is then assembled exactly as in one variable, with the real part taken at real
transverse points (`probeMultiU`, `probeMultiA`, `probeMultiB`, `probeMultiC i`, and the second
derivatives `probeMultiAa`, `probeMultiAb`, `probeMultiAc i`, `probeMultiBb`, `probeMultiBc i`,
`probeMultiCc i j`), together with the two derivatives the several-variable case needs and the
one-variable case did not: the transverse derivative of the *outer* integral
(`hasDerivAt_clampedTubeOuter_transverse`) and the mixed transverse–transverse derivative
`∂_j ∂_i u` along two *different* coordinates (`sliceHolo_cpartial_clampedTubeSolution`,
`continuousAt_cpartial_cpartial_mixed`). The four records

**`isC1OnMulti_probeMultiU`**, **`isC1OnMulti_probeMultiA`**, **`isC1OnMulti_probeMultiB`**,
**`isC1OnMulti_probeMultiC i`**

are what the chart consumes, and with them:

- **`probeMulti_characteristic`** — the characteristic identity in real form, with the full
  transverse Laplacian: `2∂ξ∂η u = (∑ᵢ ∂ᵢ²u + V u)/2`;
- **`TubeDatum.exists_clockProbe_nullMulti`** — **clock probes for potentials coupling several
  transverse coordinates.** On Minkowski space of dimension `k + n + 2`, a potential depending on the
  two null coordinates continuously differentiably and on `k` transverse coordinates analytically —
  a genuinely coupled dependence in all of them, not a slab, not a separable product, and not a
  single transverse direction — admits a clock probe on an open neighbourhood of the event,
  normalised to `1` there and nonvanishing on that neighbourhood.

Axioms: `[propext, Classical.choice, Quot.sound]`. This closes the open item recorded above: the
construction is no longer restricted to one transverse combination.

The rest of the programme then runs exactly as in one variable:

- `translateTubePotential`, **`IsC1OnMulti.translate`**, **`TubeDatum.translate`**,
  **`TubeDatum.exists_clockProbe_nullMulti_at`** — probes at *every* event, by translating functions
  rather than spacetime (so the translation invariance of the chart d'Alembertian is never needed);
- **`TubeDatum.openProbes_nullMulti`**, **`TubeDatum.nullMultiPotential_eq_of_openProbes`** — such a
  potential has probes on open regions at every event, hence is determined by its probes;
- **`gradPair_nullMultiLift`** — the carré du champ of such a scale is
  `−4 ∂ξσ ∂ησ + ∑ᵢ (∂ᵢσ)²`: the two null directions pair with each other, each transverse one with
  itself;
- `conformalPotentialMulti`, **`conformalPotential_nullMultiLift`** — so the effective potential of
  such a scale is again a function of the same coordinates, explicit in the scale's derivatives;
- **`TubeDatum.twoSpecies_scale_reconstruction_nullMulti`** and
  **`TubeDatum.twoSpecies_scale_reconstruction_of_scale_multi`** — and the two-species scale law
  holds in every dimension at least `k + 2`, both with the hypothesis on the effective potential and
  with it moved to the scale function itself: two species of the same conjugation weight and
  different calibrated masses return `(other₁ − other₂)/massSq = e^{2σ}`.

All unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

Finally, the several-variable class is shown to be **inhabited**, so none of the above is vacuous:

- **`exists_tubeDatum_coupled k`** — the potential `V(ξ,η,z) = sin ξ · cos η · cos(z¹ + ⋯ + zᵏ)`
  carries a clock datum on a tube for every `k`: slice holomorphic, bounded by `cosh(kρ)`, `C¹` in
  the null coordinates, real at real transverse points, and depending on *every one* of the
  transverse coordinates as well as on both null ones. A cosine of a sum is a sum of products, so the
  transverse dependence is genuinely coupled, not a sum or a product of one-variable profiles;
- `BoundedC1TubePotential` with its closure algebra (`add`, `sub`, `mul`, `const`, `mono`,
  `congr_deriv`, **`ofSum`**, **`cexp_two`**) and `RealOnAxisTube` — so a concrete potential is
  certified by composing closure lemmas rather than by re-proving the conditions;
- `coupledScaleMulti`, **`isC1OnMulti_coupledScaleMulti`**, **`isC1OnMulti_coupledScaleMultiD`**,
  **`conformalPotentialMulti_coupledScaleMulti`**,
  **`twoSpecies_scale_reconstruction_coupledScaleMulti`** — and for the explicit scale
  `σ(ξ,η,y) = ε sin(ξ + η + y¹ + ⋯ + yᵏ)` the two-species law holds with **no hypothesis left on the
  potential**: its admissibility is proved, not assumed. Two species of the same conjugation weight
  and different calibrated masses return `(other₁ − other₂)/massSq = e^{2σ}` in every dimension at
  least `k + 2`.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### The physical dimension

The physical case is `k = 2` transverse coordinates and no spectator directions: Minkowski space of
dimension `2 + 0 + 2 = 4`. `ClockFourDimensionalScaleLaw.lean` states it, with no casts needed —
`Fin (2 + 0 + 2)` *is* `Fin 4` and `slabEps (2 + 0)` *is* the four-dimensional signature:

- **`TubeDatum.exists_clockProbe_fourDim`** — clock probes at every event of four-dimensional
  spacetime, for a potential coupling the two null coordinates and **both** transverse ones;
- **`TubeDatum.twoSpecies_scale_reconstruction_fourDim`** — the two-species scale law in four
  dimensions;
- **`twoSpecies_scale_reconstruction_coupledScale_fourDim`** — the same for the explicit scale
  `σ(ξ,η,y) = ε sin(ξ + η + y¹ + y²)`, with no hypothesis left on the potential;
- **`exists_tubeDatum_coupled_fourDim`** — and the four-dimensional class is inhabited.

So the construction reaches the physical dimension with the transverse dependence fully coupled. The
hypothesis that remains is analyticity in the transverse directions, and it is not a technical
artifact of the proof: the characteristic (Goursat) problem for `∂ξ∂η u = (∑ᵢ ∂ᵢ²u + V u)/4` is
elliptic in the transverse directions, so for merely smooth `V` it is ill-posed in Hadamard's sense.
Smooth transverse dependence has to be reached by the *Cauchy* problem on a spacelike hypersurface —
hyperbolic energy theory, which mathlib does not have. That, and not the several-variable structure,
is the open ground.

That claim is now a theorem rather than a remark. `ClockCharacteristicIllPosed.lean` exhibits the
Hadamard family for the characteristic operator itself:

`u_{k,n}(ξ, η, z) = e^{-n/2} n^{-k} · exp(nξ/2 + nη/2 + nz)`,

- **`hadamardWave_characteristic`** — each one solves `∂ξ∂η u = ∂_z²u/4` exactly, i.e. the clock
  equation with vanishing potential;
- `iteratedDeriv_hadamardWave_trans`, **`abs_iteratedDeriv_hadamardWave_le`** — on the two
  characteristic faces of the unit box every transverse derivative of order `j` is bounded by
  `n^{j-k}`;
- `hadamardWave_corner`, **`tendsto_hadamardWave_corner`** — while the value at the far corner is
  `e^{n/2} n^{-k}`, which grows without bound for every fixed `k`;
- **`exists_characteristic_illPosed`** — hence for every order `m`, every tolerance `ε > 0` and every
  target `C` there is an exact solution whose characteristic data is below `ε` together with all
  transverse derivatives up to order `m`, and which exceeds `C` at the corner.

So no estimate bounding the solution by finitely many transverse derivatives of its characteristic
data can hold, and analyticity in the transverse directions is *necessary* for this route, not merely
convenient. Axioms: `[propext, Classical.choice, Quot.sound]`.

One hypothesis has been localised. `ClockDatum.mass` now asks for the bound only on the rectangle,
`|s|, |t| ≤ T`, which is all the construction ever uses — the iterates integrate over
`[0,ξ] × [0,η]`, and every appeal to the bound is at a point of that rectangle. The single-event
probe therefore needs no control of the potential away from the event. What does not localise is the
step from one event to all of them: `ClockDatum.translate` needs the bound on the *translated*
rectangle, so `openProbes_nullTransverse` and the two theorems that rest on it carry the uniform
bound `‖V s t z‖ ≤ Mv` explicitly. That is intrinsic to the method — a single constant has to serve
every event — and it is honest to see it in the statement rather than hidden in the datum. What
the class still asks for, and what the next generalisation has to remove, is that the potential be
bounded over *all* null coordinates and the whole strip; the construction itself only ever uses it on
the rectangle.

The first genuinely coupled target this reaches is dimension three: a potential
`V(x⁰, x¹, x²)` with arbitrary continuously differentiable dependence on the null coordinates and
periodic-analytic dependence on the transverse one. The last open input of the whole programme is
stated in its physical form:

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
   **In dimension two this is now proved outright**, for every `C¹` potential, by
   `exists_clockProbe_two_dimensional`. **In every dimension `≥ 3` it is proved, at every event, for
   potentials with coupled transverse dependence in one transverse coordinate**, by
   `ClockDatum.exists_clockProbe_nullTransverse_at`: continuously differentiable in the two null
   coordinates, holomorphic and bounded on a strip about the real transverse axis, and real there.
   **All the transverse coordinates are reached, coupled along an arbitrary unit direction**, by
   `ClockDatum.exists_clockProbe_unitTransverse_at`: the potential may depend on any single linear
   combination `∑ᵢ cᵢ xⁱ` of them. What is left is transverse dependence which is merely smooth
   rather than analytic, and dependence on two or more independent transverse combinations.

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

## Status update: the massive probe family is constructed (every smooth conformal factor)

The open core recorded above — "a probe family for a single massive species", equivalently a local
existence theorem for the physical massive Klein–Gordon field — is **closed**, for an arbitrary
smooth conformal factor and in any dimension:

`GaloisForLFunctions.HTGeometry.twoSpecies_scale_reconstruction_static` derives the scale law with
the massive family *constructed*, from
`GaloisForLFunctions.HTGeometry.openProbes_conformalPotential_static`, whose probes come from the
hyperbolic construction of the child card `hyperbolic-clock-probe-smooth-potential`:

- the evolution is solved on the frequency side in a weighted Wiener algebra (Peetre + Volterra,
  no smallness, global in time);
- the synthesis is differentiated twice in time and twice in space under the integral;
- the field solves `□u + (V-1)u = 0` classically at every event and is nonvanishing near a
  prescribed one;
- probes at every event follow by translation invariance of the coordinate calculus, and every
  smooth static potential is covered by cutting off near the event.

`GaloisForLFunctions.HTGeometry.twoSpecies_scale_reconstruction` is the same statement with no
time-independence hypothesis:

```
(other₁ x - other₂ x) / massSq = Real.exp (2 * σ (x 0, kgSpatial d x))     (σ smooth, arbitrary)
```

Its probes come from `GaloisForLFunctions.HTGeometry.openProbes_of_smooth_spacetime`, which covers
every smooth potential on spacetime: the potential is cut off in space *and* time around the event,
and the resulting curve of Schwartz potentials satisfies the uniform and Lipschitz bounds the family
constructor asks for because it is a continuous function of the event supported in a compact set —
the bound by continuity on a compact support, the Lipschitz estimate by the mean value inequality
applied to the partial derivative in time.

## Status update: the scale law on every conformally flat chart

The hyperbolic construction produces probes on the flat chart. They transfer to any conformal
rescaling of it, which extends the reconstruction from Minkowski space to the whole conformally flat
class — every two-dimensional chart, and the cosmological ones in higher dimensions.

`formal/GaloisForLFunctions/HTGeometry/ConformalMetricLowRegularity.lean` runs the conformal calculus
at the regularity the constructed probe actually has:

- `SmoothMetricChart.DifferentiablePartials` — value and first partials differentiable; the corpus
  proves exactly this of its field and no more (`differentiableAt_coordPartial_kgChartField`);
- `differentiableAt_flux`, **`dalembert_conformalRescale_of_differentiablePartials`** — the conformal
  transformation law with smoothness of the field dropped, which is exact: inspecting the smooth
  proof shows infinite smoothness entered through differentiability of the flux and nothing else;
- `flux_mul_left`, `gradPair_mul_right_left`, `dalembert_mul_left` — the Leibniz rules with one
  smooth factor at the same regularity;
- **`dalembert_conformalRescale_conjugation_of_differentiablePartials`** — conjugation by `e^{-aσ}`,
  `a = (d-2)/2`, cancels every first-order derivative of the field, because `-2a + (d-2) = 0`;
- `conformalTransferPotential`, **`solvesPotentialWaveAt_conformalRescale`** — hence probes transfer,
  with `Ṽ = e^{-2σ}(V + a□σ + a²Γ(σ,σ))`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonRegularProbes.lean` carries the regularity through
the probe interface (`RegularOpenProbes`, `regularOpenProbes_kgChartPotential`,
`regularOpenProbes_of_smooth_spacetime`, `regularOpenProbes_conformalRescale`), and
`formal/GaloisForLFunctions/HTGeometry/KleinGordonConformallyFlat.lean` closes the loop:

- `kgEventInvCLM`, `kgEventInvCLM_split`, **`regularOpenProbes_of_smooth_chart`** — probes for every
  smooth potential of the flat chart, stated intrinsically, with no product form required;
- `conformalPullbackPotential`, `conformalTransferPotential_pullback` — the base-chart potential that
  transfers to a prescribed one;
- **`regularOpenProbes_conformalRescale_kgChart`** — clock probes for every smooth potential on every
  conformal rescaling of the flat chart;
- **`twoSpecies_scale_reconstruction_conformallyFlat`** — the two-species scale law there, with the
  massive species' probes constructed rather than assumed.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Foliated charts join the transfer

The conformal calculus was localized so that it consumes the regularity a probe *actually* has on
the region where it solves, rather than infinite smoothness everywhere
(`SmoothMetricChart.DifferentiablePartialsOn` and the `…_on` forms of the conformal law, the Leibniz
rules, the conjugation identity and the transfer, in
`formal/GaloisForLFunctions/HTGeometry/ConformalMetricLowRegularity.lean`; the global statements are
now one-line corollaries with `W = univ`). `RegularOpenProbes` records the regularity on its own
region for the same reason.

`formal/GaloisForLFunctions/HTGeometry/ClockFoliationRegularProbes.lean` then brings the foliation
route into the transfer:

- **`differentiablePartialsOn_comp`** — a field constant along the leaves, `w ∘ φ`, has
  differentiable partials on the tube over the interval where the ODE for `w` was solved; that is
  exactly what the leaf-label construction produces and no more;
- **`regularOpenProbes_foliation`**, `regularOpenProbes_foliationConformal` — hence the foliation
  probes satisfy the regular probe interface, on a neighbourhood of every event;
- **`regularOpenProbes_conformalRescale_foliation`** — and therefore transfer: every conformal
  rescaling of a foliated chart carries clock probes;
- **`twoSpecies_scale_reconstruction_conformalRescale_foliation`** — the scale law there:

  ```
  (other₁ x - other₂ x) / (μ₁ - μ₂) = exp (2 (σ₀ (φ x) - σ x))
  ```

  the foliation scale corrected by the rescaling. This is conformal covariance of the reconstruction
  itself, and it is new ground: when `σ` is *not* a function of the leaf label the rescaled chart is
  no longer foliated, so the corpus's foliation theorem does not reach it.

The foliation hypotheses are inhabited, so none of this is vacuous:
`formal/GaloisForLFunctions/HTGeometry/ClockFlatTimeFoliation.lean` shows the flat chart is foliated
by its own time coordinate — `timeCoord`, with `Γ(t,t) = -1` and `□t = 0`
(`gradPair_kgChart_timeCoord`, `dalembert_kgChart_timeCoord`) — whence
`regularOpenProbes_kgChart_timeFoliation`, a second and entirely ordinary-differential construction
of clock probes for potentials depending only on time, and
`regularOpenProbes_conformalRescale_kgChart_timeFoliation`, its transfer to an arbitrary conformal
rescaling.

So the reconstruction now covers the conformal orbit of the flat chart *and* the conformal orbit of
every foliated chart, with the probes constructed in both cases.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Cosmological charts, and causality as a conformal invariant

`formal/GaloisForLFunctions/HTGeometry/ClockCosmologicalChart.lean`:

- `SmoothPseudoMetric.squaredInterval_conformal`, `neg_conformal_iff`, `timelikeCone_conformal` — a
  conformal rescaling multiplies every squared interval by a positive factor, so it moves no
  timelike direction;
- **`chronoFuture_conformal`, `chronoPast_conformal`, `chronoDiamond_conformal`** — hence the cones
  and the chronological diamond are conformal invariants: the laboratory region of a conformally
  flat chart is the same set as in the flat one;
- `cosmologicalFactor`, **`cosmologicalChart`** — the flat chart rescaled by a smooth function of the
  time coordinate, that is, a Friedmann metric in conformal time;
- **`regularOpenProbes_cosmologicalChart`**, **`twoSpecies_scale_reconstruction_cosmological`** —
  probes and the scale law on it, so the cosmological case of the card is an instance rather than a
  separate construction;
- **`twoSpecies_scale_reconstruction_conformallyFlat_diamond`** — and the diamond form of the law on
  every conformally flat chart, with experiments confined to the diamond.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## Status update: the scale law inside a causal diamond

The determination hypotheses of the card quantify over *all* open regions, which is more than a
laboratory supplies. `formal/GaloisForLFunctions/HTGeometry/ClockRegionalTwoSpecies.lean` confines
both the probes and the experiments to one region:

- `OpenProbesOn`, `openProbesOn_of_openProbes` — probes with their neighbourhoods inside the region;
  probes everywhere restrict to any open region;
- `potential_eqOn_of_openProbesOn` — experiments on open subsets *of the region* determine the
  potential on the region, and claim nothing outside it;
- **`scale_reconstruction_on_region`** — hence the two-species scale law at every event of the
  region, with the massless species' probe supplied by the corpus's global nonvanishing solution;
- `kgMetric`, `kgMetric_eq_minkowski`, `kgDiamond`, `isOpen_kgDiamond`, `mem_kgDiamond_segment` —
  the chronological diamond of the construction's own causal structure: an open region, non-empty
  because the interior of the clock's worldline segment lies in it
  (`formal/GaloisForLFunctions/HTGeometry/ChronometricCausalDiamond.lean` supplies the cones);
- **`twoSpecies_scale_reconstruction_diamond`** — for an arbitrary smooth conformal factor on
  spacetime, experiments performed only inside the diamond reconstruct the conformal scale at every
  event of the diamond, with the massive species' probes constructed rather than assumed.

Axioms: `[propext, Classical.choice, Quot.sound]`.

Axioms of all the above: `[propext, Classical.choice, Quot.sound]`.

## Status update: a third class of charts — time-dependent propagation speed

The probe classes of this card are the conformal orbit of the flat chart and the conformal orbit of
a foliated chart. A chart whose propagation speed varies in time,

```
□u = -∂₀²u + c(t)² ∑ᵢ ∂ᵢ²u,
```

is in neither: its inverse metric is not a multiple of the flat one, and the foliation route only
sees potentials that are functions of the leaf label. That class is now closed for the mass
potential, in the child card
`../../../3-formalized/new_scientific_knowledge/time-dependent-principal-part-clock-probes.md`:

- **`regularOpenProbes_hillSpeedChart`** — the speed chart carries a regular clock probe at every
  event, built by Fourier synthesis of Hill oscillators whose Grönwall constant is uniform in the
  frequency;
- **`hillSpeedChart_dalembert`** — the operator is the divergence-form d'Alembertian of an explicit
  smooth chart, so the corpus's conformal machinery applies to it verbatim;
- **`twoSpecies_scale_law_hillSpeedChart`** — hence the two-species scale law on the whole conformal
  orbit of a variable-speed chart.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## Status update: the variable-speed class, with an arbitrary potential

The child card
`../../../3-formalized/new_scientific_knowledge/variable-speed-arbitrary-potential-clock-probes.md`
removes the restriction its predecessor left. A chart whose propagation speed varies in time now
carries clock probes for an **arbitrary smooth potential**, at every event:

- **`openProbes_hillWaveOp_smooth`** — the corpus's `OpenProbes` interface for `hillWaveOp d c` and
  any smooth spacetime potential, the potential realized as the chart potential of a real convolving
  family exactly as in the flat case;
- **`regularOpenProbes_hillSpeedChart_driven`** — those probes are probes of the divergence-form
  d'Alembertian of an explicit smooth chart;
- **`twoSpecies_scale_law_hillDriven`** — hence the two-species scale law on the whole conformal
  orbit of a variable-speed chart, with a shared potential that cancels in the difference.

Two pieces of infrastructure the corpus lacked were built for it and are reusable: a Volterra theory
with **locally bounded** data (`VolterraWindowedEquation.lean`) and a Duhamel calculus with an
**abstract fundamental pair** (`DuhamelVariableOscillator.lean`), the latter because a variable
frequency has no addition formula.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## Status update: a principal part that varies in space

Both classes above still have a principal part independent of the *spatial* point. The child card
`../../../3-formalized/new_scientific_knowledge/product-chart-clock-probes.md` crosses that
frontier, by a product argument rather than by variable-coefficient hyperbolic theory.

In two dimensions the corpus already owns the full variable-coefficient inverse step
(`exists_clockProbe_on_two_dimensional`, Goursat), and the two-dimensional conformal law of the
d'Alembertian holds with no differentiability hypothesis. Crossing that surface with a flat factor
and pulling the probe back along the projection gives a probe of the product; rescaling the product
conformally by an arbitrary smooth factor of *all* the coordinates then produces a chart whose
inverse metric varies in every coordinate:

- **`SmoothMetricChart.prodFlat_dalembert_comp_front`** — the d'Alembertian of the product chart on
  a transversally constant field is the d'Alembertian of the factor, read at the projected point;
- **`regularOpenProbes_conformalRescale_warpedProductChart`** — regular clock probes for the widest
  class the construction reaches: an arbitrary conformal factor on the two-dimensional block, a
  second arbitrary conformal factor on all `2 + k` coordinates, an arbitrary `C¹` potential of the
  two-dimensional factor;
- **`twoSpecies_scale_law_warpedProductChart`** — two species of different mass reconstruct the
  *product* of the two conformal factors pointwise.

The two-dimensional existence theorem was strengthened in place to record the regularity its
construction already produced (`SmoothMetricChart.DifferentiablePartialsOn U W`), which is what the
transfer to the product consumes.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## Status update: the regularity threshold of the last open input

"Missing 1" above is stated in terms of *analytic* transverse dependence, and its closing sentence —
"what is left is transverse dependence which is merely smooth rather than analytic" — was already
stale when written: `regularOpenProbes_of_smooth_spacetime` gives probes at every event of every
dimension for an arbitrary **smooth** spacetime potential, by realizing it locally as the chart
potential of a real convolving family. The analytic (Ovsyannikov) family is what reaches potentials
of *low* regularity in the null directions; the Fourier family is what reaches merely smooth
transverse dependence.

The child card `../../../3-formalized/new_scientific_knowledge/finite-regularity-clock-probes.md`
now replaces the remaining smoothness hypothesis by an explicit finite order:

- **`kgFreq_pow_mul_norm_fourier_le`** — the weighted decay `⟨w⟩^{2j}‖𝓕f(w)‖ ≤ 2^j(‖f‖₁ +
  (2π)^{-2j}‖D^{2j}f‖₁)` for a compactly supported `C^{2j}` function: the transform of the `j`-th
  iterated derivative, evaluated at `2j` copies of the unit vector along `w`;
- **`WienerFamily.ofContDiffCurve`** — hence a curve of compactly supported `C^{2j}` functions with
  bounded, Lipschitz decay functional is an admissible family, with no Schwartz hypothesis;
- **`regularOpenProbes_of_contDiff_spacetime_explicit`** — *in `1+d` dimensions a potential of class
  `C^{2d+5}` carries regular clock probes at every event*; in the physical case `d = 3` that is
  class `C^{11}`;
- **`regularOpenProbes_conformalRescale_kgChart_contDiff_explicit`** — the same on every conformal
  rescaling of the flat chart, the conformal factor still an arbitrary smooth function.

So the open ground of the programme is now exactly: a potential of class `C^k` with `k < 2d+5` in
dimension `≥ 3` — in particular `C¹`, which in dimension two is already covered by Goursat. Below
the threshold the Fourier route provably cannot work (a `C^k` density decays only to order `k`,
while the synthesis needs order `> d+2`), and the replacement is the Cauchy problem on a spacelike
hypersurface: hyperbolic energy estimates in Sobolev spaces, which mathlib does not have.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## Status update: the hyperbolic energy estimate

The closing note of `finite-regularity-clock-probes` named "hyperbolic energy estimates in Sobolev
spaces, which mathlib does not have" as what stands between the corpus and low-regularity potentials.
The first half of that theory is now built, in the child card
`../../../3-formalized/new_scientific_knowledge/hyperbolic-energy-estimate.md`:

- **`integral_laplacian_mul`** — the Green identity `∫(∑ᵢ∂ᵢ∂ᵢf)·g = -∑ᵢ∫∂ᵢf·∂ᵢg` for compactly
  supported fields, from mathlib's directional integration by parts;
- **`integral_dirDeriv_energyDensity`** — the flux identity `∫∂ₜ(energy density) = 2∫(V+1)·u·∂ₜu`:
  the equation, the symmetry of mixed partials and the Green identity cancel both derivative terms,
  so no derivative of `u` survives on the right;
- **`hasDerivAt_waveEnergy`** — differentiation under the integral sign, the domination supplied by
  the compact spatial support;
- **`waveEnergy_le_exp`** — `E(t) ≤ E(0)·exp((‖V‖_∞+1)t)`;
- **`eq_zero_of_waveEnergy_zero`** — hence a solution with vanishing initial energy vanishes;
- **`eq_of_solvesWaveEq_of_data_eq`** — and, since the equation is linear (`solvesWaveEq_sub`), two
  solutions with the same Cauchy data agree at every later time;
- **`eq_of_solvesWaveEq_of_data_eq_all`** — at every time, by time reflection
  (`solvesWaveEq_comp_timeReflect`): only the second time derivative enters the equation;
- **`waveEnergy_le_exp_abs`**, **`waveEnergy_sub_le_exp_abs`** — the estimate on both sides of the
  initial slice, and hence continuous dependence: the energy of the difference of two solutions at
  any time is controlled by the energy of the difference of their Cauchy data.

- **`kgWaveOp_eq_of_contDiff`**, **`solvesWaveEq_comp_eventCLM`** — and the bridge: a solution of the
  corpus's own `SolvesPotentialWaveAt (kgWaveOp d) V u` is a solution in time-space coordinates, so
  every Fourier-built probe with spatially compact support inherits all of the above, and
  **`solvesWaveEq_comp_eventCLM_iff`** records that the two formulations are the same statement;
- **`eq_of_solvesPotentialWave_of_data_eq`** — the capstone in the corpus's own language: two smooth
  spatially compactly supported solutions of `□u + Vu = 0` with a bounded continuous potential and
  the same Cauchy data on the initial slice agree at every event.

The estimate no longer needs compact spatial support: `DecayingSolution` collects the integrability
and domination conditions that replace it, and **`waveEnergy_le_exp_of_decaying`** proves
`E(t) ≤ E(0)·exp((‖V‖_∞+1)t)` in that generality — the form a Fourier-built probe, which decays
rather than vanishes outside a compact set, can meet. In the corpus's own language that reads
**`eq_zero_of_solvesPotentialWave_of_decaying`**: a smooth decaying solution of `□u + Vu = 0` whose
value and time derivative vanish on the initial slice vanishes at every event. The decay hypotheses
are a genuine restriction, not a consequence of the equation: `not_decayingSolution_one_field` shows
the constant field solves the free equation with non-integrable energy density, so a Fourier-built
probe — bounded, not automatically decaying — needs its energy and Green products shown integrable
before the estimate applies to it.

This is uniqueness, not existence. The existence half — a Galerkin scheme or a fixed point in a
Sobolev scale — is what would lower the regularity threshold of the probe construction below
`C^{2d+5}`; the estimate above is its quantitative input.

Axioms: `[propext, Classical.choice, Quot.sound]`.

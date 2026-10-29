# Hecke theta Mellin continuation and unit unfolding

- **ID:** hecke-theta-mellin-continuation-and-unit-unfolding
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Hecke and class-field programme](hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** Regularize the actual Hecke theta Mellin integral, unfold the actual global-unit domain, identify its Gamma factors and ideal Dirichlet series, and obtain full continuation without a class-field-theoretic input.

## Proved inputs

The actual finite-character theta has a trace-dual finite Fourier transform,
explicit physical and dual zero modes, and uniform exponential tails on
bounded place profiles. Its global-unit logarithm periodicity is proved.
The actual unit-log hyperplane, discrete range, and full-rank results already
exist in the corpus. Full Mellin unfolding and its normalization are not yet
proved.

## Analytic route

Write `n=[K:ℚ]`, `k` for the actual parity degree,
`a(s)=(n*s+k)/2`, and `κ=n/2+k`. The proved theta inversion has the form
`Θ(y,t)=A(y)*t^(-κ)*Θdual(-y,1/t)`, with explicit arithmetic `A`.
Splitting the Mellin integral and subtracting both zero modes produces entire
large-parameter tails plus rational terms
`A(y)*cdual/(a(s)-κ) - cphysical/a(s)` when splitting at one.
If a different positive cutoff is used, retain its exact power factors.
For `k>0` both zero modes vanish. For `k=0` the possible poles correspond to
`s=0,1`.

First prove the actual kernels measurable and locally integrable on positive
parameters, using the countable ideal sums and a Gaussian majorant uniform for
`t≥δ>0` and upper-bounded place profiles. Do not assume normal convergence.
Mathlib's Mellin differentiability theorem accepts local integrability and
power bounds at both ends. The corpus wrapper
`RHTower.differentiable_mellin_of_rapidDecayRay` is source-inspected; it uses
`mellin_differentiableAt_of_isBigO_rpow`. Its continuity interface need not be
imported or assumed. `HTGeometry.differentiable_truncatedMellin` is also
source-inspected and handles integrable finite intervals away from zero.

## Working unfolding derivation — not yet a proved normalization

Choose one infinite place `v0` and coordinates `y_v` for the weighted-zero
hyperplane `Σ_v mult(v)*y_v=0`, omitting `v0`. With `q=log(t)/2`, put
`u_v=q-y_v`. The expected absolute Jacobian is `n/mult(v0)`, so
`dt/t * dy = (2*mult(v0)/n) du` for this explicitly chosen coordinate measure.
Each place integral should then be

`∫ exp((mult(v)*s+ε_v)*u) exp(-π*mult(v)*|v(a)|²*exp(2u)) du`

`= (1/2)*(π*mult(v)*|v(a)|²)^(-(mult(v)*s+ε_v)/2)
   * Γ((mult(v)*s+ε_v)/2)`.

Here `ε_v` is the actual real parity and is zero at complex places.
Multiplying by the real monomial leaves its sign character and
`|Norm(a)|^(-s)`. This suggests the scalar normalization
`mult(v0)/(n*2^(r-1))`, where `r` is the number of infinite places, times the
torsion-unit cardinality from unfolding the unit logarithm kernel. Every
Jacobian, Gamma integral, and torsion multiplicity must be proved before use.
The chosen Gamma product is `π^(-(s+ε)/2)Γ((s+ε)/2)` at real places and
`(2π)^(-s)Γ(s)` at complex places; verify conversions to any named library
Gamma factor explicitly.

For a nonzero ideal `b` coprime to the modulus, unit orbits of nonzero
`a∈b` correspond to integral ideals `J=(a)/b` in ordinary ideal class `[b]⁻¹`.
The actual finite/sign character identity should give
`χ_fin(a)*sign(a)^ε = ψ(J)*ψ(b)` on supported terms, and
`|Norm(a)|=N(b)*N(J)`. Thus the unfolded integral should equal the proved
Gamma scalar times `ψ(b)*N(b)^(-s)` times that partial Hecke L-series.
Sum over actual coprime representatives of ordinary ideal classes, weighting
by `ψ(b)^(-1)*N(b)^s`.

When the finite character and parity are trivial, the ray character descends
to the ordinary class group. Character orthogonality should then cancel the
remaining zero-mode residues for every nontrivial character. This descent and
orbit identification are still required proofs, not hypotheses to add.

## Search state

Completed corpus searches returned scalar periodization integrals, truncated
Mellin entirety, rapid-decay Mellin wrappers, and actual unit-log definitions.
Generic fundamental-domain integration and Mellin APIs are being checked in
Mathlib after those corpus searches. Primitive arithmetic Gauss evaluation
remains a separate input for the final primitive functional equation; it is
not needed to postulate continuation.

## Existing abstract Mellin continuation

Mathlib `NumberTheory/LSeries/AbstractFuncEq.lean` is source-inspected. Its
`WeakFEPair` already proves the regularized Mellin continuation, functional
equation, and zero/weight residues. Instantiate it with the actual physical
theta at `y` and actual finite-Fourier dual theta at `-y`, weight
`n/2+k`, and scalar `exp(Σ mult*y)/(N(𝔪.fin*b)*sqrt(|disc K|)) * (-i)^k`.
Every field must be proved from the actual data: local integrability, positive
weight, nonzero scalar, the proved Poisson identity, and rapid decay from the
proved exponential tails. No abstract FE-pair or analytic field is an input
assumption. This removes the need to reprove the generic regularization.

The actual Mellin construction is now formalized in
`HeckeThetaHasMellinContinuation.lean`; see
[the completed theta Mellin card](../3-formalized/actual-hecke-theta-mellin-continuation.md).
The final direct source audit passes without warnings, seven transitive axiom
audits are standard only, and the consumer olean is built. Its two completed
scratches are removed. Full unit-domain averaging and Gamma/ideal unfolding
remain open.

## Weighted logarithmic coordinates from Mathlib

After the corpus unit-log and kernel searches, Mathlib
`NumberTheory/NumberField/Units/DirichletTheorem.lean` supplies the exact missing
arithmetic infrastructure: `NumberField.Units.logEmbedding`, its torsion kernel,
`unitLattice`, actual discreteness/full lattice instances, and
`logEmbeddingEquiv : Additive (units / torsion) ≃ₗ[ℤ] unitLattice`.
Its `logSpace` omits one distinguished place and uses **weighted** coordinates
`ℓ_v=mult(v)*log|v(u)|`. Reuse these actual constructions instead of rebuilding
a unit basis or assuming a torsion kernel.

The inverse profile must be `y_v=ℓ_v/mult(v)` away from the omitted place and
`y_v0=-(Σℓ_v)/mult(v0)`. Relative to this weighted coordinate measure, the working
Jacobian above changes by `∏_(v≠v0) mult(v)`. Thus the proposed scalar after the
place Gamma integrals becomes `|torsion| * 2^(1-r₁) / n`, independent of the
omitted place, for the stated Gamma product. This remains an unproved
normalization; prove the linear determinant and each change of variables.


## Joint continuity and averaging consumer

`/tmp/HeckeThetaJointContinuityScratch.lean` is written and imports the completed
Mellin module. It proves a proposed uniform summable Gaussian majorant for
`t ≥ δ > 0` and `y_v ≤ M`, then joint continuity of both actual theta sums.
The majorant uses the parity bound at `δ`, parameter monotonicity, and
`norm_sq_placeScale_ge`; its fixed Gaussian rate is
`(δ/2)*exp(-M)^2 > 0`. This is the next compile after the Mellin source audit
and its required consumer olean.

Mathlib `CanonicalEmbedding/FundamentalCone.lean` also supplies actual normalized
ideal-element sets, torsion actions and stabilizers, and ideal/principal-generator
equivalences. Source-inspected declarations include `integerSetEquiv`,
`idealSetEquiv`, and `idealSetEquivNorm`. They can support the orbit-count and
normalization step; no new unit or principal-generator hypothesis is needed.



## Existing exact Jacobian lead

The source-inspected Mathlib `CanonicalEmbedding/NormLeOne.lean` already proves
`abs_det_completeBasis_equivFunL_symm = n * regulator`, the full derivative and
absolute determinant of `expMapBasis`, and `setLIntegral_expMapBasis_image`.
Its complete basis consists of the actual fundamental-unit logarithms and
the radial multiplicity vector. `logMap_expMapBasis` identifies the unit
fundamental domain with the half-open unit cube in all nonradial coordinates.
These exact results can replace a new determinant calculation after proving
the profile/parameter conversion. They do not yet identify our complex
Mellin integrand or justify its sum/integral exchanges.


The next independent geometric scratch, `/tmp/HeckeUnitLogDomainScratch.lean`,
connects Mathlib's weighted log coordinates to our full place profiles and
defines the actual unit fundamental domain. It includes the target exact
volume equality with `NumberField.Units.regulator` (defined in Mathlib as the
unit-lattice covolume), finite measure, compact closure, and a uniform profile
bound. It has not yet been compiled; only the joint-continuity scratch is
currently compiling. The Mellin module's consumer olean is now built.


## Current verification frontier

- Joint-continuity scratch: both actual uniform summable majorants check.
  Explicit ideal-element subtype annotations removed an elaboration timeout.
  The final neighborhood argument now uses one typed helper; the complete
  scratch is compiling with unchanged proof limits.
- Unit-domain geometry scratch: written, not compiled yet.
- `/tmp/HeckeUnitThetaAverageScratch.lean`: written, not compiled yet. It imports
  the planned final joint-continuity and unit-domain modules, justifying their
  consumer oleans once finalized. It contains actual integrability, continuity,
  regulator-scaled zero modes, exponential tails, averaged inversion, and the
  proposed fully discharged averaged Mellin pair. None of these new averaged
  declarations is claimed formalized until the scratch and final audits pass.

The next required source names are `HeckeLFunctions/HeckeThetaIsJointlyContinuous.lean`
and `HTGeometry/NumberFieldUnitLogFundamentalDomain.lean`. No olean exists yet
for either. Only one owned Lean process is running: the joint-continuity check.


The joint-continuity source is now written and wired as
`HeckeThetaIsJointlyContinuous.lean`. The final direct source audit is running
with the neighborhood coercions made explicit. The unit-domain scratch imports
it only to combine its transitive axiom checks with the next geometric check;
this audit-only import must be omitted from the final geometric source.
After the source audit, build the required joint-continuity olean for the
written averaging consumer, then check the unit-domain scratch. All consumed
search JSON files from these batches are removed.

Source-inspected integration APIs for the averaging scratch:
`continuous_parametric_integral_of_continuous` integrates a jointly continuous
family over a compact set; use the restricted domain measure and its compact
closure. `ContinuousOn.integrableOn_compact` supplies the actual integrability.
`norm_setIntegral_le_of_norm_le_const` bounds the integral by the pointwise
constant times the domain's real measure. `setIntegral_const` gives the exact
regulator-scaled zero mode. No dominated-continuity assumption is left in an
actual averaged theorem.


`HeckeThetaIsJointlyContinuous.lean` now passes its final direct source audit
without warnings. The umbrella is wired and the completed joint-continuity
scratch is removed. Its required olean is building for the written averaging
consumer. The next unit-domain scratch includes both joint-continuity
`#print axioms` checks; these imported checks remain to be consumed before
closing its formalized card. Next active scratch:
`/tmp/HeckeUnitLogDomainScratch.lean`, followed by the unit-average scratch.


## Coprime class representatives and generators already in the corpus

A new corpus query surfaces and source-checks
`HeckeLFunctions.exists_integral_rep` in
`RayClassesOfPrincipalIdealsAreReadByResidues.lean`: every ordinary ideal class
has an actual nonzero integral representative coprime to the finite modulus.
Do not rebuild that existence argument. `IdealsOfARayClassAreConePoints.lean`
already proves principality of `I*b` in the inverse class and the exact
fundamental-cone torsion multiplicity via Mathlib's `integerSetEquiv`.
Its equivalence construction can support a weighted-series version; the
existing cardinality identity alone is not a Mellin unfolding proof.


The required joint-continuity olean is now built. The sole active compile is
`/tmp/HeckeUnitLogDomainScratch.lean`, including its own geometric checks and
the two imported joint-continuity transitive axiom audits. The averaging
scratch now also contains weighted-unit covariance/periodicity, an entire
regular part, both regulator-scaled residues, and entire continuation for
nonzero parity. These remain unverified until its dependencies and full
scratch are checked.


## Absolute-integrability requirement for unfolding

The averaged Mellin pair alone does **not** justify exchanging its ideal sum
with both integrals: Mellin convergence of a weighted theta difference does
not imply convergence of the sum of absolute summands. Prove the nonnegative
Tonelli identity first. After decomposing nonzero ideal elements into unit
orbits, integrate the absolute Gaussian monomial over the full logarithmic
space and positive radial variable. The real place Gamma integrals then
reduce the total absolute mass to a finite scalar times the already proved
nonzero-ideal norm series for `Re s>1`. This proves the exact Fubini hypothesis
before the complex character identity is used. Keep the zero element removed
throughout.

The geometric unit-domain source is now written as
`HTGeometry/NumberFieldUnitLogFundamentalDomain.lean` and wired into the
umbrella. Its scratch proves the profile conversion, tiling, regulator volume,
and uniform profile bound with standard transitive axioms. An explicit
measure argument fixes the sole remaining positivity-lemma elaboration issue;
its final direct source audit is running. The completed joint-continuity
result is recorded in
[its formalized card](../3-formalized/hecke-theta-joint-continuity-on-positive-parameters.md).


The actual unit-domain geometry is now final-source audited without warnings
and recorded in
[the formalized domain card](../3-formalized/actual-unit-log-domain-and-regulator-volume.md).
Its scratch is removed, its umbrella import is wired, and its required olean
is building for `/tmp/HeckeUnitThetaAverageScratch.lean`. That averaging
scratch is now the only unfinished owned scratch. Once the dependency build
finishes, compile it, resolve its actual proof obligations, audit its transitive
dependencies, and perform the final direct source check. Do not treat the
already written averaging code as a proved result.


Both required consumer oleans are now built. The sole active check is
`/tmp/HeckeUnitThetaAverageScratch.lean`. It includes five transitive audits
for the averaged construction and a sixth for unit-domain volume positivity.
No completed scratch or consumed search JSON remains from the preceding
batches. The averaged module has not yet been copied into the corpus.


## Residue cancellation still required after unfolding

At parity degree zero, the proposed class-weighted reconstruction uses the
factor `ψ(b)^(-1)*N(b)^s`. At `s=1`, the `N(b)` factor cancels the `N(b)^(-1)`
in the Poisson scalar; the residual class sum is therefore proportional to
`Σ_b ψ(b)^(-1)`. At `s=0`, a physical zero mode occurs only for the unit finite
modulus, and the same class sum appears. For a ray character with trivial
finite character and parity, prove its actual descent to the ordinary class
group, then apply finite-character orthogonality. A nontrivial finite character
or nonzero parity already kills the dual mode; prove the corresponding
physical-mode vanishing from the actual finite character. These are working
algebraic deductions to formalize, not assumed pole-cancellation premises.


The actual unit-averaged Mellin construction is now formalized and fully audited
in `HeckeThetaAveragesOverTheUnitDomain.lean`; see
[its formalized card](../3-formalized/actual-unit-averaged-hecke-theta-mellin-continuation.md).
The complete scratch, six transitive checks, and final direct source audit pass
without warnings. Its umbrella import is wired and completed scratch removed.
No consumer olean for this new module is needed yet. The next active algebraic
card is [nonzero ideal elements as unit orbits](../3-formalized/hecke-ideal-elements-as-unit-orbits.md),
whose first written scratch is `/tmp/HeckeIdealUnitOrbitsScratch.lean`.
Full Gamma/Hecke-series unfolding and class-character residue cancellation
remain unproved.


The active algebraic scratch is `/tmp/HeckeIdealUnitOrbitsScratch.lean`.
It first constructs the explicit principal-ideal/unit generator map for any
commutative domain. Its class-number-field extension will reuse the newly
source-checked `ClassGroup.mk0_eq_mk0_inv_iff`. The preceding unit-averaged
Mellin source and all its audits are complete; it has no olean yet because
no written importing consumer currently requires one.


The exact ideal-element/global-unit orbit equivalence is now formalized in
`HeckeLFunctions/NonzeroIdealElementsAreGlobalUnitOrbits.lean` and recorded
in stage 3. The final source audit passed; four transitive axiom checks are
standard only. The actual inverse-class generator, principal ideal, and
absolute norm identities are available. The next scratch constructs actual
units as torsion times the actual logarithmic lattice, using Mathlib's proved
unique fundamental-unit decomposition.


For fixed positive Gaussian parameter, the full unit-orbit/log-lattice
reindexing is implemented in the uncompiled
`/tmp/HeckeThetaUnitOrbitSumsScratch.lean`. It proves absolute convergence by
injecting actual units times a nonzero generator into the ideal, and exact
zero removal by subtype reindexing. Its geometric unit-decomposition scratch
has passed all three standard axiom audits; the geometric final source check
is running.

Source-inspected Mathlib `MeasureTheory/Group/FundamentalDomain.lean`
provides `IsAddFundamentalDomain.lintegral_eq_tsum'` for nonnegative
unfolding and `integral_eq_tsum'` after integrability. A bounded-domain
summable majorant will bound the sum of translated norm integrals. The
identity `ofReal_integral_norm_eq_lintegral_enorm` and
`ENNReal.ofReal_tsum_of_nonneg` then prove the whole-space kernel's finite
norm integral. This avoids an unproved integrability premise.

Countability lead: corpus `RHTower/Deninger/DeningerPlaceCountable.lean`
proves number-field countability with `(Module.finBasis ℚ K).equivFun`,
then ring/ideal countability. The actual unit lattice is directly countable
via `(Units.basisUnitLattice K).equivFun`; no countability of the ambient real
logarithm space is needed. Mathlib `integral_tsum_of_summable_integral_norm`
is source-checked in `Integral/DominatedConvergence.lean` and has orientation
`tsum integral = integral tsum`.


The global-unit/log-lattice module is now final-audited and recorded in
stage 3. Its olean is being generated for the written periodization consumer.
The actual fixed-parameter unit-domain unfolding is separately written in
`/tmp/HeckeUnitDomainUnfoldingScratch.lean`, not yet compiled. Its active card
is `hecke-unit-domain-unfolding-is-absolutely-integrable.md`.


A new corpus check found no existing exact radial/logarithmic Jacobian or
place-parity-degree sum identity. It did recover the separate archimedean
block-determinant framework, whose matrices are not this radial map. The
source-inspected `NormLeOne.completeBasis` has radial vector `(mult v)` and
fundamental-unit weighted logarithms, with absolute determinant
`[K:ℚ]*regulator K`. Its explicit `expMapBasis` Jacobian and nonnegative
change-of-variables theorem remain reusable leads for the final Mellin
normalization. No such normalization is claimed yet.

The needed arithmetic character input already exists as
`character_rayClassOfElt_eq` plus `infiniteSignCharacter_eq_prod`: the finite
residue value times real sign parities is the principal ray-class value.
This must still be transported to `heckeValue` for the chosen class
representative generators, including the non-coprime zero case.


The next arithmetic weight bridge has a reusable exact corpus lemma:
`ConePointsOfARayClassAreLatticeCosets.lean` defines
`idealUnit_span_eq`, identifying the actual integral principal ideal's
fractional-ideal unit with `toPrincipalIdeal (Units.mk0 a)`. Its source has
been checked. Combine this with `rayHom_algebraMap`,
`character_rayClassOfElt_eq`, and `infiniteSignCharacter_eq_prod`; use
`heckeValue_mul` and `span_inverseClassGenerator` to obtain the class-series
coefficient. For the non-coprime case, use the existing
`isUnit_mk_of_forall_not_mem` / `not_mem_of_isUnit_mk` rather than adding a
coprimality premise for each chosen generator.

The finite-character zero-mode branch is also still open: prove that
`m.fin=top` forces `finiteHeckeWeight=1`, hence a nontrivial finite weight
kills both physical and dual modes. Together with the already proved
nonzero-parity branch, this reduces residual poles to characters descending
to the ordinary class group. No such descent or cancellation is claimed yet.


Current owned Lean state: the corrected transparent subtype aliases in
`NonzeroIdealElementsAreGlobalUnitOrbits.lean` passed their final source
audit. Their changed olean is being regenerated for the written importing
periodization scratch. The next command after that process exits is
`lake --old env lean /tmp/HeckeThetaUnitOrbitSumsScratch.lean` from `formal/`.
Its first implicit-map timeouts were fixed with explicit `i` arguments;
remaining subtype rewriting fixes await the changed dependency. The later
`/tmp/HeckeUnitDomainUnfoldingScratch.lean` contains fixed-orbit and full-class
integral unfolding but is not compiled. No unsafe reducibility or raised
proof limits are present.


`HeckeThetaUnitOrbitsAreLogPeriodizations.lean` now passed its full scratch,
three standard transitive axiom audits, and final direct source check. The
stage-3 card records all exact unit/class/lattice sum identities. Its olean
is being generated for the written consumer. Next compile:
`lake --old env lean /tmp/HeckeUnitDomainUnfoldingScratch.lean` from `formal/`.
That is the only unfinished owned Lean scratch.


Gamma normalization convention is now source-checked:
Mathlib `Complex.Gammaℂ` includes the factor two,
`Gammaℂ(s)=2*(2*pi)^(-s)*Gamma(s)`. Therefore with Mathlib's real and complex
Gamma factors, the proposed scalar is
`torsionOrder K / ([K:ℚ] * 2^(Units.rank K))`, not the earlier scalar for
complex Gamma without its factor two. The radial Jacobian and this scalar
remain unproved Lean obligations on `hecke-radial-logarithmic-jacobian.md`.


The fixed-parameter unit-domain unfolding is now fully formalized in
`HeckeUnitOrbitsUnfoldOverTheLogSpace.lean`. The actual averaged theta minus
its regulator-weighted zero mode equals the exact torsion order times the
sum over inverse-class ideals of whole-log-space kernel integrals. Whole-space
integrability and both infinite exchanges follow from the actual summable
Gaussian majorant; no analytic premise is added. Three transitive axiom
checks are standard-only, and the final direct source audit passed without
warnings. The card is now
`3-formalized/hecke-unit-domain-unfolding-is-absolutely-integrable.md`.
Earlier scratch-status paragraphs are superseded. The next bridge is the
exact radial/logarithmic Jacobian and Gamma evaluation, followed by the
arithmetic coefficient identity and absolutely convergent ideal-series
Mellin exchange. Full Hecke continuation/primitive functional equation and
class field theory are still unfinished.

The exact radial/logarithmic Jacobian is now fully formalized in
`HTGeometry/NumberFieldRadialLogarithmicJacobian.lean`: `(q,l) ↦ q-P(l)`
has measure pushforward density `2^r₂/[K:Q]`, with both integral formulas
and an absolute-integrability equivalence. Seven axiom checks are
standard-only and the final source audit passed without warnings. The card
moved to `3-formalized/hecke-radial-logarithmic-jacobian.md`.

`/tmp/HeckeLogGaussianMellinScratch.lean` is under its first check.
`/tmp/HeckeArchimedeanGammaFactorsScratch.lean` is a written, uncompiled
consumer of that planned module and the finished Jacobian. It defines the
actual place parities, standard Gamma product, independent logarithmic
kernel, and proposed normalization `1/(degree*2^unitRank)` using finite-product
Fubini. These Gamma results are not yet certified; see their active card.

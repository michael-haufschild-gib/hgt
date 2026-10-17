# Quantitative uncertainty: working ledger

Purpose: reusable facts, obstructions, and open obligations. Not a chronological work log.

## Domain contract

- Target: normalized archimedean increment energy for real autocorrelations with zeros at `log n`, `2≤n≤N`, and hyperbolic polar neutrality.
- Initial paper domain: nonzero real smooth compactly supported sources, unrestricted support radius. Separate constructions now cover even sources and the full continuous real positive-definite cone with finite energy.
- Polar integrals on the full cone require absolute integrability. No common support bound is imposed. Infimum equality across different source classes is not claimed.
- Original research target: 100 significant contributions. User cleared the active goal; research is stopped, not complete. Routine lemmas and restatements do not count.

## Established facts

| Fact | Evidence | Limits |
|---|---|---|
| Each divisibility chain plus origin obeys an exact Bessel sphere law. | Existing `autocorr_dyadic_coset_sphere_sub_le`. | Separate chains need not be mutually orthogonal. |
| One zero at `log 2` forces positive integrated energy despite failure of uniform pointwise interpolation. | Existing `biScaleLevyEnergy_ge_folded_collar_integral`, `archFoldedCollarConstant_pos`. | Existing formal certificate integrates away from singular endpoint. |
| Shared-origin block support function is `R sqrt(W²+(Σ_m ||w_m||₂)²)`. | Paper proof and equality witness, §1. Lean-certified `shared_origin_weighted_sum_le`, `shared_origin_support_attained`; literal grid endpoint `autocorr_multi_dyadic_coset_leverage`. | Sharp for block-sphere relaxation; not proved sharp for autocorrelations. |
| Left collars of lengths `δ_n=log(n/(n−1))`, `n≥3`, partition `(log 2,log N)`. | Exact substitutions in `quantitative-constant.md`, §2. | Origin interval `(0,log 2)` is charged once. |
| Explicit integral certificate `B_N` is nonnegative, increasing, positive for `N≥3`. Combine with folded certificate using `max`, giving positivity for `N≥2`. | Complete paper proof in `quantitative-constant.md`, §2. | Lean integration/partition proof pending; global optimality open. |
| Reflection allocation `L_N(β)` puts node 2 back into its dyadic block while charging `(1−β)` of origin directly and `β` by reflection. `max_{β∈[0,1]}L_N(β)≥max(F,B_N)`. | §2 reflection-allocation proof, including endpoint domination and maximum attainment. | Paper-proved, Lean integration pending; no numerical optimization performed. |
| A distant translated correction enforces polar neutrality, preserves finite-grid zeros, and costs `O(e^{-T})` energy. Therefore polar and nonpolar infima agree on real compact sources of any differentiability order at least two. | Lean-certified `normalizedArchEnergy_polarCopy_error`, `exists_polar_source_local_energy_close`, `polar_log_grid_lower_bound_iff`; paper §3. | Includes smooth sources. Does not impose source-evenness or a common support bound. |
| A symmetric three-copy correction preserves even sources and cancels both exponential moments. Hence imposing both moments costs nothing at the infimum, within either the even-source or unrestricted-source class. | §3, even-source extension; error `≤K_D(2e^{-T}+e^{-2T})`. | Does not identify even-source and unrestricted-source infima with each other. |
| For compactly supported positive-definite `h`, polar enforcement can preserve its normalized values on any prescribed bounded interval exactly. | §3 full-cone extension: GNS vector `g−e^{-T/2}U_Tg`; cross terms vanish locally. Scalar source version Lean-certified by `normalized_autocorr_subtractCopy_local`. | General GNS version still paper-only. |
| Polar and nonpolar finite-grid infima agree on the full continuous real positive-definite cone with finite energy. | Taper `h_A=h(1−|x|/A)_+`, energy error `≤M_w/A`; then distant-copy polar enforcement. | Paper proof; Lean pending. Finite grid essential to this proof. |
| Any finite list of real exponential source moments can be set to zero without changing the finite-grid energy infimum. Rates may be zero or negative. | Lean-certified `exists_source_cancel_rates_local_energy_close`, `finite_moment_log_grid_lower_bound_iff`; the uniform single-copy bound handles every real coefficient. Paper §3 also gives a common-separation polynomial construction with error `≤mK_D e^{−T/2}`. | Formal proof uses successive separations and preserves every differentiability order at least two. The common-separation polynomial estimate remains paper-only. No source-evenness or common support bound. |
| A finite list of real compact sources has one real compact source with exactly the same summed correlation on any bounded window and no greater energy. Thus finite real vector rank does not improve the grid energy infimum. | Lean-certified `exists_scalar_list_local_energy_le`, `finite_source_log_grid_lower_bound_iff`, and `polar_finite_source_log_grid_lower_bound_iff`; paper §4. Separate supports; both signs preserve local data; their energies average to the component sum. | Real `C^r`, `r≥2`, with support enlargement. Components may cancel at grid nodes; separate component grid zeros are unnecessary. Does not realize arbitrary positive-definite kernels. |
| The unit-mass scalar-source local correlation/energy epigraph is convex before closure. | Lean-certified `convex_localSourceEnergyEpigraph`; paper §4. Absorb convex coefficients into sources by square roots; scalarize the pair with energy domination. | Support enlargement allowed. This does not prove closedness, attainment, or strong duality. |
| For a finite spectral probability `μ`, cosine/sine modulation of a compact source gives exact correlation `h_f m_μ` and normalized vector energy within `E(f)` of `S(μ)=Σp_j Ψ(ω_j)`, uniformly in frequencies. Here `Ψ(ω)=gammaBracket(ω)−gammaBracket(0)`. | Lean-certified `autocorr_cosineSource_add_sineSource`, `abs_spectralEnvelopeEnergy_sub_cost_le`, and `archFrequencyCost_eq_gammaBracket_sub_zero`; paper §5. | The two-sided error belongs to the vector source. Scalar sign selection only preserves an upper energy bound. |
| Every feasible finite spectral probability admits actual smooth compact polar scalar sources with exact logarithmic-grid zeros and energy `<S(μ)+ε`, for every `ε>0`. Thus every valid smooth polar grid lower bound is at most `S(μ)`. | Lean-certified `exists_smooth_polar_grid_source_lt_spectral_cost` and `polar_grid_lower_bound_le_spectral_cost`. A concrete bump and dilation discharge the small-envelope premise. | Only the upper realization direction. Reverse Fourier-measure reduction, exact atomization, attainment, and strong duality remain open. No common support bound. |
| Compact `C²` sources have `R−h(t)≤M|t|`; dilation `f_δ(u)=f(δu)` gives `E(f_δ)≤δ M M₁/R→0`, with `M₁=∫₀∞xw_arch(x)dx<∞`. | Lean-certified `exists_autocorr_increment_linear_bound`, `autocorr_sourceRescale`, and `exists_source_normalized_energy_lt`; explicit bound `xw_arch(x)≤(2x+1)e^{−x/2}`. | The stronger derivative-based `O(δ²)` rate is paper-only. Dilation alone does not preserve prescribed nonzero-lag zeros; modulation supplies them. |

## Failed approaches and their positive survivors

- **Reuse full origin weight in every coset:** invalid energy accounting. Survivor: joint block norm `Q=Σ_m||w_m||₂`; loss is `Q²/(2W)`. Cross terms cannot be dropped. Optimal allocation `W_m=W q_m/Q`.
- **Integrate crossover floor beyond its sign range:** invalid; coefficient `w−μ cosh(x/2)` becomes negative. Survivor: local floor remains valid where that coefficient is nonnegative, exactly as in existing Lean theorem.
- **Infer a positive uniform polar premium from negative-lobe mass alone:** incompatible with distant-copy construction on unrestricted-support finite-grid domain. Survivor: exact polar constraint-enforcement operation with exponential error bound. Combined certificates may still improve lower bounds for the common infimum.
- **Add folded and coset certificates without budgeting overlap:** counts some energy twice. Survivor: `max` is valid; addition needs a proved allocation.
- **Claim global sharpness from a sharp finite-dimensional relaxation:** unwarranted. A tuple equality witness need not extend to a positive-definite function with all grid zeros.
- **Require every translate coefficient to tend to zero:** unnecessary and fails for zero/negative exponential rates. Survivor: normalize by `r₀=Σc_k²`; Cauchy–Schwarz bounds each relative coefficient correlation by 1, uniformly even when coefficients grow.
- **Require a small cross-energy error to remove finite vector rank:** unnecessarily weak. Survivor: exact sign averaging gives a separated scalar source with no energy increase, not merely convergence. Local cross-products vanish for both signs.
- **Carry the vector's two-sided spectral error through scalar sign selection:** unjustified. Survivor: the upper bound survives and suffices for spectral-cost upper certificates; a lower comparison needs a separate Fourier argument.
- **Leave a low-energy envelope as an existence premise:** incomplete source realization. Survivor: an actual smooth compact bump, global Lipschitz control, and the finite first weight moment construct such envelopes at every tolerance.
- **Infer finite atomic reduction or strong duality from scalar epigraph convexity:** unsupported. Exact moment preservation, closure, and compactness require independent proofs; current corpus search did not supply them.

## Deformation identities and sign guardrails

- Correct deformation: `(R−h)w+μhc = Rw−h(w−μc)`.
- The candidate expression `R(w+μc)−h(w−μc)` has an extra `μRc`; do not use it.
- Existing Lean deformation theorem is correct. The negative-lobe coefficient changes sign beyond crossover. The current rewritten field overview no longer displays the erroneous identity.

## Verification and tooling facts

All six leaves passed direct `lake --old env lean -o ...`, exit 0 with no diagnostics. Paths are
under `formal/GaloisForLFunctions/BiScaleUncertainty/`; all six are imported by the umbrella.
Scratch `#print axioms` results contain only `propext`, `Classical.choice`, and `Quot.sound`.

| Leaf | Audited public theorems | Specialization evidence |
|---|---:|---|
| `SharedOriginMultiCosetLeverage.lean` | 5 | Literal dyadic grid endpoint. |
| `DistantCopyPolarEnforcement.lean` | 23 | Explicit smooth-order specialization passed. |
| `FiniteMomentEnergyInvariance.lean` | 5 | Smooth sources, rates `0,±1/2`, passed. |
| `FiniteSourceEnergyScalarization.lean` | 14 | Smooth convexity and polar/vector equivalence passed. |
| `FiniteSpectralEnvelopeRealization.lean` | 13 | Joint spectral audit passed. |
| `BroadSpectralCostRealization.lean` | 11 | Joint spectral audit and explicit `N=2`, `ω=π/(2log2)` specialization passed. |

- Index regeneration passed and lists all 24 spectral theorems. Scoped `git diff --check` passed. Latest `scripts/formal_tools.py lint` returned one error: concurrent `PhysicalCollarDualCertificate` is unreachable from the field umbrella. It also reported 381 large-file warnings. No error names this task's six modules; global lint is not green. All owned Lean processes exited.
- Source order is `WithTop ℕ∞`; smooth means coerced inner top, with `WithTop.coe_le_coe.mpr le_top` supplying `2≤smooth`.
- Weighted translated correlations and spectral error integrands have explicit integrability proofs; no use of totalized nonintegrable Bochner integrals to manufacture identities.
- Verified toolchain names: `abs_add_le`, `HasCompactSupport.zero`, `Prod.smul_fst`, and global `integrableOn_exp_mul_Ioi`. The alternatives `abs_add`, `hasCompactSupport_zero`, `Prod.fst_smul`, and `Real.integrableOn_exp_mul_Ioi` are unavailable.
- Scratch literal `Finset.Icc 2 2` needs a natural-number type annotation: without it the log expression can infer real indices and request nonexistent `LocallyFiniteOrder ℝ`.
- Broad corpus searches reported partial or unmeasured semantic coverage and source-only candidates. No exact finite-atom reduction was located; absence from these results is not an exhaustive novelty proof.
- Serena ignores Lean paths; use source reads. `update_plan` is unavailable; pipeline card tracks work. Independent reads use parallel promises.
- Missing cached dependency objects can require serial direct leaf rebuilds. A missing object does not by itself establish a source regression; no cause for the observed cache loss was established.
- No numerical experiments, added axioms, raised heartbeat limits, full builds, umbrella builds, or commits. Scratch evidence belongs under `/tmp/biscale-quantitative-audit-20261017/`.

## Adjacent work and contribution accounting

- Concurrent `OriginCollarTransport-FACTS.md` and `MultiChainGramLedger.md` independently derive the shared-origin norm formula. Treat the formalized support law as a shared bridge; do not inflate the contribution count for rediscovery or helper lemmas.
- Transport work studies general overlap allocations; this task's reflection-allocation family is an explicit feasible quantitative certificate, not a solution of their global transport optimization.
- Adjacent transport now includes `IntegratedOriginCollarLeverage.lean`. Its `integrated_logarithmic_origin_collar_real_bound` statement was inspected: a positive finite real collar coefficient bounds the extended nonnegative energy on a finite interval for `LogarithmicGridSource`. This is an available bridge, not yet an identification with this note's reflection-allocation family; its owner's ledger records verification.
- Corpus already has whole-profile scalarization in `EvenSectorSmoothSourceScalarization.lean` and fixed-window purification in `EvenSectorWindowPurification.lean` for smooth complex even pole-free mixtures. The new direct real-source argument extends to arbitrary order `r≥2` without source parity or factorization, preserves bounded-window data and dominates energy, but enlarges support. Do not claim scalarization as a wholly new general phenomenon.
- **Significant contribution 1, Lean-certified core:** quantitative polar enforcement preserving local normalized data and equality of finite-grid lower-bound sets for real compact sources of every order at least two, including smooth sources. Full-cone and even-source-preserving extensions remain paper-proved, not Lean-certified.
- **Significant contribution 2, Lean-certified core:** arbitrary finite real exponential-moment constraints have no infimum cost on compact sources of every differentiability order at least two with finite-grid zeros. The coefficient-normalized error estimate handles zero/negative rates and permits exponentially growing filters. Prior `SuzukiPolarTranslateMultiplier.lean` already contains translate-symbol multiplication and a filter for `0,±1/2`; those algebraic facts are not counted as new. Exact local preservation plus uniform vanishing energy cost is the new assertion. The explicit common-separation polynomial estimate remains paper-only.
- **Significant contribution 3, Lean-certified:** exact finite real vector rank removal with local data preservation and energy domination; equality of finite-grid lower bounds with the polar scalar class; convexity of the actual scalar local energy epigraph. Count this as one package, not one advance per theorem. The prior complex-even scalarization results above delimit its contribution.
- Prior `WeilWorkPBAPJointProfiles.lean` already proves cosine/sine correlation modulation for complex smooth sources. The elementary modulation identity is not new; the added result is uniform archimedean energy control and actual smooth real polar scalar realization with exact finite-grid zeros.
- **Significant contribution 4, Lean-certified:** every feasible finite spectral probability supplies actual smooth compact polar scalar grid sources with energy below its cost plus arbitrary positive tolerance. The envelope premise is discharged by a concrete bump and dilation. Count the two spectral leaves as one package, not separate advances per helper or rate estimate.
- **Lean-certified significant core contributions: 4.** No claim of exhaustive external novelty. Do not count supporting theorems individually or mark the 100-contribution goal complete.

## Next obligations

1. Prove the reverse source-to-spectral comparison and exact finite atomic moment reduction. `CHMDWindowFourierTail.lean` contains an existing Fourier energy identity; `HTGeometry/FiniteRealAtomicMeasure.lean` computes integrals of already-finite atomic measures but does not provide atomization. Verify applicability before reuse.
2. Formalize triangular taper/full-cone extension and source-evenness preservation where needed. The scalar finite-moment core is complete; do not redo it.
3. Connect the now-available adjacent integrated collar theorem to this note's explicit reflection-allocation family, proving any required comparison rather than identifying different partitions without proof.
4. Shared-origin bound, equality witness, rational bound, and literal dyadic specialization are certified; do not redo them.
5. Derive stronger bounds or matching extremizers/asymptotics for actual constant. Existing certificates are not a global solution.
6. Both overview copies now have the corrected deformation and crossover sign. Keep source claims aligned with proof scope.

## Guardrails for future conjectures

- The sequence of optimal constants is nondecreasing in `N` but uniformly bounded above: any fixed nonzero smooth source of support diameter below `log 2` has all logarithmic-grid zeros and finite energy; polar infimum invariance transfers this upper bound. Hence unbounded growth with `N` is impossible on this domain. This is an elementary consequence, not another contribution count.
- A potential route to globally sharp constants is a Bochner-measure moment optimization with cost equal to the archimedean Fourier symbol and constraints `∫cos(r log n)dμ=0`. Strong duality, attainment, and finite-atomic reduction require proof and corpus verification before use; they are not established by the current note.
- Finite-vector scalar-source admissibility, finite cosine modulation, uniform energy error, and the vanishing-envelope construction are now Lean-certified. The remaining spectral route needs the reverse measure comparison, exact atomization, and finite-moment optimization/duality; upper realization alone does not prove spectral equivalence.

Proof details: [quantitative-constant.md](quantitative-constant.md). Task state: `docs/drafts/pipeline/1-in-progress/bi-scale-quantitative-constant-2026-10-17.md`.

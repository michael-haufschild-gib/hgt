# Quantitative uncertainty: working ledger

Purpose: reusable facts, obstructions, and open obligations. Not a chronological work log.

## Domain contract

- Target: normalized archimedean increment energy for real autocorrelations with zeros at `log n`, `2≤n≤N`, and hyperbolic polar neutrality.
- Initial paper domain: nonzero real smooth compactly supported sources, unrestricted support radius. Separate constructions now cover even sources and the full continuous real positive-definite cone with finite energy.
- Polar integrals on the full cone require absolute integrability. No common support bound is imposed. Infimum equality across different source classes is not claimed.
- Full user goal: 100 significant contributions. Routine lemmas and restatements do not count.

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
| Any finite list of real exponential source moments can be set to zero without changing the finite-grid energy infimum. Rates may be zero or negative. | New finite-filter proof in `quantitative-constant.md`, §3: `P_T(z)=∏(1−e^{−β_jT}z)`; normalized coefficient autocorrelations satisfy `|r_l|≤r₀`, giving energy error `≤mK_D e^{−T/2}`. | Paper proof; finite-filter energy theorem not yet formalized. |

## Failed approaches and their positive survivors

- **Reuse full origin weight in every coset:** invalid energy accounting. Survivor: joint block norm `Q=Σ_m||w_m||₂`; loss is `Q²/(2W)`. Cross terms cannot be dropped. Optimal allocation `W_m=W q_m/Q`.
- **Integrate crossover floor beyond its sign range:** invalid; coefficient `w−μ cosh(x/2)` becomes negative. Survivor: local floor remains valid where that coefficient is nonnegative, exactly as in existing Lean theorem.
- **Infer a positive uniform polar premium from negative-lobe mass alone:** incompatible with distant-copy construction on unrestricted-support finite-grid domain. Survivor: exact polar constraint-enforcement operation with exponential error bound. Combined certificates may still improve lower bounds for the common infimum.
- **Add folded and coset certificates without budgeting overlap:** counts some energy twice. Survivor: `max` is valid; addition needs a proved allocation.
- **Claim global sharpness from a sharp finite-dimensional relaxation:** unwarranted. A tuple equality witness need not extend to a positive-definite function with all grid zeros.
- **Require every translate coefficient to tend to zero:** unnecessary and fails for zero/negative exponential rates. Survivor: normalize by `r₀=Σc_k²`; Cauchy–Schwarz bounds each relative coefficient correlation by 1, uniformly even when coefficients grow.

## Deformation identities and sign guardrails

- Correct deformation: `(R−h)w+μhc = Rw−h(w−μc)`.
- The candidate expression `R(w+μc)−h(w−μc)` has an extra `μRc`; do not use it.
- Existing Lean deformation theorem is correct. The negative-lobe coefficient changes sign beyond crossover. The current rewritten field overview no longer displays the erroneous identity.

## Verification and tooling facts

- Read full task brief and the field README, including its concurrently expanded seven-pillar architecture. Its newer distant-copy discussion is consistent with the verified source theorem.
- Corpus research returned relevant one-chain/folded-pair endpoints; broad semantic search reported partial coverage and source-only candidates. Exhaustive novelty not established.
- Serena symbol lookup rejects Lean paths as ignored; use source reads for these files.
- `update_plan` unavailable; pipeline card tracks work. Independent reads use parallel promises.
- No numerical experiments, added axioms, raised heartbeat limits, full builds, umbrella builds, or commits.
- Scratch name probe resolves all currently used helper names; an over-general probe of `Real.sqrt_pos.2` failed implicit-argument inference, not theorem availability.
- Direct `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/SharedOriginMultiCosetLeverage.olean GaloisForLFunctions/BiScaleUncertainty/SharedOriginMultiCosetLeverage.lean` passed, exit 0, no diagnostics.
- Scratch audit of all five public result endpoints passed. Axiom sets contain only `propext`, `Classical.choice`, `Quot.sound`. No added axioms or computational proof oracle.
- `DistantCopyPolarEnforcement.lean` passed direct `lake --old env lean -o ...` with no diagnostics. Separate scratch audit checked all 23 theorems: only `propext`, `Classical.choice`, `Quot.sound`. The explicit smooth-order specialization also passed. Source order is `WithTop ℕ∞`; smooth means the coerced inner top, with `WithTop.coe_le_coe.mpr le_top` supplying `2≤smooth`.
- The weighted translated-correlation integrability is proved by an explicit integrable envelope; the proof does not exploit totalized nonintegrable Bochner integrals.
- Umbrella imports both verified task modules. Index regeneration passed. Current lint snapshot has two concurrent wiring errors (`CliqueSphereDualityAndExtremalTheory`, `SignedDyadicCollarPartition`), neither in this task's verified modules. Other previously unlinked modules are now wired. Final lint remains to be run after the finite-moment leaf is audited and wired.

## Adjacent work and contribution accounting

- Concurrent `OriginCollarTransport-FACTS.md` and `MultiChainGramLedger.md` independently derive the shared-origin norm formula. Treat the formalized support law as a shared bridge; do not inflate the contribution count for rediscovery or helper lemmas.
- Transport work studies general overlap allocations; this task's reflection-allocation family is an explicit feasible quantitative certificate, not a solution of their global transport optimization.
- **Significant contribution 1, Lean-certified core:** quantitative polar enforcement preserving local normalized data and equality of finite-grid lower-bound sets for real compact sources of every order at least two, including smooth sources. Full-cone and even-source-preserving extensions remain paper-proved, not Lean-certified.
- **Significant contribution 2, paper-proved:** arbitrary finite real exponential-moment constraints have no infimum cost on smooth compact sources with finite-grid zeros. The coefficient-normalized error estimate handles zero/negative rates and permits exponentially growing filters. Prior `SuzukiPolarTranslateMultiplier.lean` already contains translate-symbol multiplication and a filter for `0,±1/2`; those algebraic facts are not counted as new. Exact local preservation plus uniform vanishing energy cost is the new assertion.
- **Lean-certified significant core contributions: 1.** Contribution 2's finite-moment module is under audit. Do not count the 23 supporting theorems individually or mark the 100-contribution goal complete.

## Next obligations

1. Finish audit of `FiniteMomentEnergyInvariance.lean`: uniform arbitrary-coefficient estimate, single-rate cancellation preserving old moments, finite-list induction, and finite-grid lower-bound equivalence. Then formalize triangular taper/full-cone extension and source-evenness preservation where needed.
2. Formalize exact integration with active collar sets and endpoint integrability, reusing adjacent transport results when available.
3. Shared-origin bound, equality witness, rational bound, and literal dyadic specialization are certified; do not redo them.
4. Derive stronger bounds or matching extremizers/asymptotics for actual constant. Existing certificates are not a global solution.
5. Both overview copies now have the corrected deformation and crossover sign. Keep source claims aligned with proof scope.

## Guardrails for future conjectures

- The sequence of optimal constants is nondecreasing in `N` but uniformly bounded above: any fixed nonzero smooth source of support diameter below `log 2` has all logarithmic-grid zeros and finite energy; polar infimum invariance transfers this upper bound. Hence unbounded growth with `N` is impossible on this domain. This is an elementary consequence, not another contribution count.
- A potential route to globally sharp constants is a Bochner-measure moment optimization with cost equal to the archimedean Fourier symbol and constraints `∫cos(r log n)dμ=0`. Strong duality, attainment, and finite-atomic reduction require proof and corpus verification before use; they are not established by the current note.
- For a spectral optimization route, scalar-source admissibility must also be proved: a finite spectral mixture times a smooth compact correlation gives a vector-valued autocorrelation. Separating its finitely many scalar components far in physical space may preserve all local grid data while making cross-energy vanish. This is a concrete next conjecture, not an already available equivalence.

Proof details: [quantitative-constant.md](quantitative-constant.md). Task state: `docs/drafts/pipeline/1-in-progress/bi-scale-quantitative-constant-2026-10-17.md`.

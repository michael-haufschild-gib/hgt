# Multi-chain Gram research ledger

Working state, not history. Replace superseded entries; retain failed mechanisms and their witnesses. Scope: independent Bi-Scale Uncertainty, coupling across odd dyadic cosets. Novelty checks use the local corpus; no literature-wide priority claim.

**Work status:** User cleared the research goal. No autonomous continuation is active. Preserve the results and unresolved checks below; resume research only on a new request.

## Established facts

### F1. Full Gram energy gives exact origin leverage

For actual real autocorrelation `h`, set `R=h(0)`, `v_t=U_t g`, `P=Σ_i w_i v_(t_i)`, `Q=||P||²`, `B=Σ_i w_i h(t_i)`, and `W>0`. Then

`W(R-h(y))+Σ_i w_i(R-h(t_i-y))`

`= RΣ_i w_i - B - Q/(2W) + ||W(v_y-g)-P||²/(2W)`.

- **Status:** Paper and Lean verified. Arbitrary real weights and actual compactly supported continuous tests; `W=exp(a)` parametrizes positive weights without an added premise.
- **Evidence:** `autocorr_gram_leverage_remainder`, `autocorr_gram_leverage_bound`, `autocorr_odd_coset_gram_leverage` in `MultiChainToeplitzGramCoupling.lean`.
- **Use:** Keep every cross entry in `Q`. Keep anchor error `B` until actual zeros remove it.

### F2. Exact loss from forgetting cross-coset compatibility

For finite real Hilbert packets,

`D=(Σ_m ||P_m||)²-||Σ_m P_m||²`

` =Σ_(m,m') (||P_m|| ||P_m'||-<P_m,P_m'>) ≥ 0`.

The coupled rational bound improves the **optimally allocated** independent-packet bound by exactly `D/(2W)`. Equality holds exactly when every pair of nonzero packets is positively collinear; the all-zero family is included.

- **Status:** Paper and Lean verified: `packetPartitionLoss_eq_sum`, `packetPartitionLoss_nonneg`, `packet_coupling_gain`, `packetPartitionLoss_eq_zero_iff`.
- **Use:** Seek a lower bound for `D`. Negative cross correlations are unnecessary: failure of positive alignment already gives gain.
- **Benchmark:** With orthogonal within-coset chains and `||P_m||²=R a_m²`, the independent penalty is `R(Σ a_m)²/(2W)`. `SharedOriginMultiCosetLeverage.lean` already proves the sharp independent-block support bound and an attaining witness. That source was inspected, not independently audited here. Its result is not counted as our contribution.

### F3. Synchronized chains admit a robust sine improvement

Let the two chain nodes be `base+k log 2` and `base+b+k log 2`, for `0≤k<L`, with the **same** real coefficient vector `c`. Put `S=Σ c_k²` and `ρ=cos(π/(L+1))`. Define

`Γ_ij=h((j-i)log 2)`, `C_ij=h((j-i)log 2-b)`,

`δ=||Γ-RI||`, `ε=||C-strictUpper(C)||`.

All matrix norms mean **Euclidean operator norms**. For every actual test, without a grid-zero or frame premise,

`Q=||P_base+P_(base+b)||² ≤ 2(1+ρ)(R+δ+ε)S`,

`4RS-Q ≥ 2[(1-ρ)R-(1+ρ)(δ+ε)]S`.

The resulting origin bound is

`E ≥ 2RΣ c_k - B - (1+ρ)(R+δ+ε)S/W`.

- **Status:** Paper and Lean verified. Final direct-source, axiom, generated-index, and formal-lint audits passed.
- **Evidence:** `synchronizedDyadicGramEnergy_le_sine`, `synchronizedDyadic_gain_with_errors`, `synchronizedDyadic_origin_leverage`, `oddCoset_synchronized_origin_leverage` in `SynchronizedCosetSineLeverage.lean`.
- **Proof mechanism:** Actual synthesis gives `C=B†A` and `A†A=B†B=Γ`. The strictly upper truncation `T` is nilpotent by construction. Normalize by its actual norm, separating the zero case, then apply the existing sharp nilpotent numerical-radius theorem. Since `||T||≤||C||+ε`, `|<Cx,x>|≤[ρ||C||+(1+ρ)ε]||x||²`. Also `||A||²,||B||²,||C||≤R+δ`. Expand the packet norm square.
- **Use:** At exact zeros, recover the uniform sine gain. With errors, this bound certifies positive gain over the exact-grid benchmark when `(1+ρ)(δ+ε)<(1-ρ)R` and `S>0`. The theorem does not assert that arbitrary defects are small.

### F4. Every defect entry is an actual integer-log sample

Take odd integers `m,q≥3`, `base=log m`, and `b=log q`. Lean represents them as `2*m₀+3` and `2*q₀+3`.

- Off-diagonal within-chain entries are `h(log(2^|i-j|))`; the defect diagonal is exactly zero.
- In orientation `C=B†A`, `C-strictUpper(C)` has entries zero for `i<j`, and `h(log(q 2^(i-j)))` for `j≤i`.
- The nodes themselves are exactly `log(m2^i)` and `log(qm2^i)`.
- **Evidence:** `dyadicWithinGram_grid_entry`, `dyadicWithinDefect_grid_formula`, `oddCoset_triangularError_grid_formula`, `oddCoset_pairNode_inl`, `oddCoset_pairNode_inr`.
- **Consequence:** Pinning `h(log r)=0` for `2≤r≤N`, with `N≥qm2^(L-1)`, removes both defects and every anchor sample. Then `Q≤2R(1+ρ)S`, `D≥2R(1-ρ)S`, and the rational gain is at least `R(1-ρ)S/W`.
- **Formal boundary:** The actual-entry identities and unconditional error-aware inequalities are formalized. The finite-cutoff zero-grid corollary is a paper substitution, not a separately packaged Lean theorem with extra hypotheses.
- **Minimal instance:** `L=2`, unit coefficients, nodes `{m,2m,3m,6m}`. Only `{2m,3m}` can have nonzero cross correlation. `ρ=1/2`, so `Q≤6R` versus independent numerator `8R`; gain at least `R/W`. `chainSineFactor_one` proves the exact coefficient symbolically. The four-node specialization is not a separate counted contribution.

### F5. Unequal coefficient profiles retain a quantified coupling gain

Keep F3's actual errors and put `K=R+δ`, `G=(1-ρ)R-(1+ρ)(δ+ε)`. For arbitrary coefficient vectors `c,d`, let `r=||c||`, `s=||d||`, `u=normalize(c)`, `v=normalize(d)`, and `η=||u-v||`. Normalization sends zero to zero. Set

`gain=rs [max(0, sqrt(2G)-sqrt(K)η)]²`.

Here `sqrt(t)=√max(0,t)`, matching Lean's total real square root. Let `A₀,A₁` be the actual synthesis maps of the two chains. Then

`||A₀c+A₁d||² ≤ K(r+s)²-gain`,

`D=(||A₀c||+||A₁d||)²-||A₀c+A₁d||² ≥ gain-2δrs`.

The latter adds `(gain-2δrs)/(2W)` directly to the measured, optimally partitioned origin lower bound, retaining the exact anchor error.

- **Status:** Paper proof, targeted Lean build, final direct-source check, and all 17 theorem axiom audits passed. Global repository lint has not been revalidated after concurrent integration repairs. This third proved result is pending the final gate and is not yet added to the fully verified count.
- **Evidence:** `dyadic_profile_energy_bound`, `dyadicPairPartitionLoss_ge_profile`, `dyadic_profile_partition_origin_leverage` in `ProfileStableCosetLeverage.lean`. `dyadicProfileGain_pos_iff` characterizes positivity of the certificate itself.
- **Mechanism:** Lower and upper Gram bounds give `||A₀x-A₁x||²≥2G||x||²`. Triangle inequality spends at most `sqrt(K)||u-v||` of this separation. The weighted norm identity transfers it to arbitrary amplitudes. For unit profiles, `p=||A₀u||`, `q=||A₁v||` satisfy `(p-q)²≤2δ`; the exact identity `D=rs[||A₀u-A₁v||²-(p-q)²]` gives the measured-partition correction.
- **Use at exact pinning:** With `δ=ε=0`, `R>0`, and both coefficients nonzero, positive gain is certified for `η<sqrt(2(1-ρ))`, equivalently `Re⟨u,v⟩>ρ`. Amplitudes may differ arbitrarily. This removes exact coefficient synchronization as a structural restriction.
- **Use with errors:** This certificate proves positive improvement of the true measured partition bound when `gain>2δrs`; `gain>0` alone is insufficient. For nonzero coefficients the certificate condition is equivalent to `sqrt(2G)>sqrt(K)η+sqrt(2δ)`.
- **Boundary:** These are positivity criteria for the explicit lower-bound certificate, not necessary conditions for actual `D>0`. Zero certificate does not imply zero actual gain. The error-free/coherence reformulations are paper consequences; the unconditional inequalities and general certificate criterion are Lean-certified.

## Failed mechanisms and boundaries

- **Distinct odd cosets are not orthogonal.** Under grid constraints alone, choose `log(5/3)<L<log 2` and a continuous nonnegative bump supported on `[0,L]`, positive inside, e.g. `u(L-u)` there and zero elsewhere. Disjoint support gives every `h(log n)=0` for `n≥2`; overlap gives `h(log(5/3))>0`. This counterexample asserts no polar neutrality. Do not discard cross entries between cosets `3` and `5`.
- **Sine numerical radius is not a bilinear bound.** Unrelated coefficient vectors produce `<a,Cb>`, not `<c,Cc>`. The explicit operator `T(x₁,x₂)=(x₂,0)` has `T²=0`, norm one, and sends one coordinate unit vector to the other. Do not replace its operator norm by `ρ` in arbitrary bilinear pairings. F5 instead retains a profile mismatch term. This operator counterexample does not assert realization by an actual translation autocorrelation.
- **Qualitative strictness is not a uniform gap.** Compact support may exclude exact alignment without excluding approximating sequences. F3's uniformity comes from arithmetic triangularity and finite chain length.
- **Sharpness is unproved for actual translation orbits.** Sharp abstract nilpotent numerical radius does not prove its extremizer is realizable by these autocorrelations. The Hilbert support optimum need not lie on a one-parameter translation orbit.
- **Origin cannot be silently treated as a zero node.** Using `m=1` introduces `h(0)`. Keep `B`, or use odd bases at least three and sufficient grid cutoff.
- **Zero packets require care in optimization.** `W_m=W a_m/Σa_m` assigns zero budget to zero packets. Omit them or state an infimum; do not assert attainment with all budgets strictly positive.
- **Classical helpers are not separate research contributions.** Packet triangle geometry and the existing nilpotent theorem are inputs. Count each substantive Bi-Scale result once.

## Reusable local machinery and proof failures

- `RHTower.norm_inner_nilpotent_contraction_le_sine` in `RHTower/CCMNilpotentContractionSine.lean`: sharp `cos(π/(N+1))` numerical-radius theorem. General Hilbert mathematics despite its storage namespace; using it adds no RH objective.
- `HTGeometry.nilpotent_contraction_real_inner_gap`: weaker elementary deficit `1/(2N²)`; do not reprove it as a new result.
- `HTGeometry.StrictlyLowering.pow_eq_zero_of_strictlyUpper`: constructed strict triangularity implies finite nilpotence.
- `HTGeometry.finiteSynthesis` and `adjoint_finiteSynthesis_apply`: actual coefficient synthesis and Gram composition.
- `ContinuousLinearMap.norm_adjoint` and `norm_comp_le` do not exist in this toolchain. Use `LinearIsometryEquiv.norm_map` for adjoints and `.opNorm_comp_le` for composition.
- Broad `simp` on a self-inner product can turn it back into a norm before sums expand. Use ordered `rw [norm_sq_eq_re_inner, sum_inner]` and `simp_rw` for finite packet energies.
- For a real integral cast to complex, use explicit `Complex.ofReal (∫ ...)`; a type annotation alone can change the inferred integrand. The lemma is root `integral_ofReal`.
- `inner_self_eq_norm_sq_to_K` introduces `RCLike` casts that reverse `Complex.ofReal_pow` rewriting may not match. Force explicit `Complex.ofReal` in the target, then expand `pow_two` and `Complex.mul_re` when needed.
- For real weighted norm identities, `norm_add_sq_real` and `norm_sub_sq_real` avoid residual `RCLike.re` expressions that stop `ring`.
- `ContinuousLinearMap.map_smul_of_tower` is namespaced; no root `map_smul_of_tower` exists here. It transports real normalization through complex-linear synthesis.
- `rw [sub_div]` rewrites only one matching numerator. Use `simp only [sub_div] at hcost ⊢` before linear arithmetic when both sides and the target contain differences over the shared origin weight.
- An imported theorem's axiom audit covers private dependencies; audit every new public theorem, not only the headline bound.

## Research options if resumed

1. Determine the strongest useful coefficient-profile certificate. F5 supplies a quantitative mismatch term; its triangle estimate is not claimed optimal. The absolute numerical-radius input suggests sign/phase variants, but automatic variants alone must not become separate counted contributions.
2. Test whether actual translation autocorrelations can approach the abstract sine constant. Either construct admissible near-extremizers or prove an additional orbit rigidity gap. No sharpness claim before this audit.
3. Extend from a pair of multiplicatively related odd cosets to a network. Pairwise summation alone is not automatically a significant new contribution; seek a stronger joint compatibility constraint.
4. Formalize the coupled exact square-root comparison if it exposes information beyond the already verified rational loss identity.

## Candidate next result: realize the nilpotent shift by actual pulse trains

**Uncounted construction to audit.** For odd `q≥3`, choose spacing `a=log(q/2)`, and a train of `M+1` sufficiently narrow, disjoint smooth packets at spacing `a`. Exact overlap counting should give `h(a)/h(0)=M/(M+1)`. The arithmetic obstruction needed for isolation is `log n≠k a` for integer `n≥2` and integer `k`: positive `k` would make `n=q^k/2^k` an integer, impossible for odd `q`; negative `k` gives a value below one.

For any fixed chain length, the other cross lags `(j-i)log 2-log q` coincide with a train difference only when `j=i+1`. Choose packet width below the positive minimum of the finitely many forbidden distances. The proposed actual cross matrix is then `C=R[M/(M+1)]S`, where `S` is the one-step strictly upper shift, while `Γ=RI` and the required integer-log anchors vanish. A sine coefficient vector would give

`Q=2R[1+ρ M/(M+1)] Σc_k²`,

approaching the existing sine upper bound. This would settle its sharpness for actual translation autocorrelations, not merely abstract contractions. It must not be claimed before the finite-lag isolation, source construction, and sine-vector identity are verified. Global integer-grid pinning and polar/even packaging are stronger possible extensions requiring their own audits.

**Local evidence:** `RHTower.EvenSector.SmoothBlindInterpolation.train_autocorr`, `train_autocorr_zero`, and `train_autocorr_spacing` in `EvenSectorSmoothBlindInterpolationObstruction.lean` were inspected. They already prove smooth centered pulse-train overlap counts, but only for a fixed spacing and a single blind node. Their theorem does not supply the new arbitrary-spacing/full finite-grid construction. Lexical corpus search returned all 13 matching declarations in that module; the first `pulseTrain` name query had no hits, then broadening to `train autocorr` found the actual API.

The deep query `smooth compact pulse train finite forbidden shifts autocorrelation lattice separation` completed, but its AND lexical search matched no declarations. Returned suggestions do not establish the proposed realization. Coverage reports an older-generation snapshot and unmeasured semantic coverage; this is not evidence of absence from the corpus. Search output: `/tmp/bsu-shift-realization-search.log`. Its owned process has exited. No Lean implementation of this candidate has been started.

## Contribution accounting and verification

Cleared objective: 100 significant contributions. Recorded fully verified count: **2 / 100**, plus **one Lean-proved result awaiting the global repository gate**. The objective is inactive and was not completed.

1. **Verified:** Gram-resolved origin leverage and exact optimized partition loss (F1–F2).
2. **Verified:** Robust synchronized-coset sine leverage with actual arithmetic defect formulas (F3–F4). All new operator, feature, and arithmetic helpers belong to this single contribution.
3. **Proof verified; global gate pending:** Coefficient-profile stability and the measured partition-gain correction (F5). All 17 theorems constitute one contribution, not separate counts.

Contribution 1 evidence:

- `MultiChainToeplitzGramCoupling.lean`, SHA-256 `5fae9738e06f22f6da8e9f54a3b407c7b0c96dbacc48e4debcf4fae8692fecba`.
- Targeted build and final direct `lake env lean` passed; direct audit had no warnings.
- All 14 public theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wiring, generated API, index refresh, and `scripts/formal_tools.py lint --check-generated` passed.

Contribution 2 evidence:

- Sources: `TriangularGramSineBound.lean` (11 public theorems) and `SynchronizedCosetSineLeverage.lean` (18 public theorems, one private integrability theorem).
- Targeted `lake build --old +GaloisForLFunctions.BiScaleUncertainty.SynchronizedCosetSineLeverage`: PASS. Both owned leaves rebuilt successfully.
- Final direct `lake env lean` on each owned leaf: PASS, empty output, no warnings.
- All 29 public theorems audited via `lake env lean /tmp/bsu-synchronized-axioms.lean`: only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or `Lean.ofReduceBool`.
- Both umbrella imports and generated API entries present. `scripts/formal_tools.py index`: PASS. `scripts/formal_tools.py lint --check-generated`: PASS, with unrelated existing large-file warnings.
- `TriangularGramSineBound.lean` SHA-256: `4ba95b34e5069843278eb980af7f627952846eacc1c2d948c0dbf4a8e2c7c8bc`.
- `SynchronizedCosetSineLeverage.lean` SHA-256: `cc95f4f1bb9cbe18e75834237d3ad1310cd9bb46ff5cd7adf16d51f09974d658`.
- Owned prototype scratch files removed; successful axiom-audit scratch and logs retained. No commits or numerical experiments.

Contribution 3 evidence and remaining integration:

- `ProfileStableCosetLeverage.lean`, SHA-256 `ccf56ddf05e783bde8dc5daebf92761066cbabf38b7b49f5d690fd15c5ca8121`.
- `lake build --old +GaloisForLFunctions.BiScaleUncertainty.ProfileStableCosetLeverage`: PASS.
- Final `lake env lean GaloisForLFunctions/BiScaleUncertainty/ProfileStableCosetLeverage.lean`: PASS, empty output, no warnings.
- All 17 public theorems audited: only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or `Lean.ofReduceBool`. Own umbrella import and generated API entries present.
- Index refresh passed. The last recorded lint run failed on concurrent missing imports and generated drift. Current umbrella imports include `PhysicalCollarPartition`, `PhysicalCollarDualPrices`, and `BroadSpectralCostRealization`. The latter's source now replaces the previously failing integrability/extensionality and integrand-equality steps with explicit almost-everywhere congruence proofs. These source changes were inspected, but no fresh targeted build or global lint pass is claimed here. Its theorem bodies were not edited by this workstream.
- Earlier missing imports for `AbstractBiScaleSystemAndSchurKreinCoupling`, `CosecantSecantDualDecomposition`, `DisjointCollarCliqueDivergenceAndTuransProblem`, and `FiniteSpectralEnvelopeRealization` were added after all four targeted builds passed. These integration repairs are not research contributions.
- **Gate action if resumed:** Revalidate current concurrent sources with targeted builds, refresh the index, and run `scripts/formal_tools.py lint --check-generated`. Imports already present do not need to be added again. Advance the verified count to 3 only after the required gate passes. Do not reprove or recount F5.
- Logs: `/tmp/bsu-profile-build.log`, `/tmp/bsu-profile-final.log`, `/tmp/bsu-profile-axioms.log`, `/tmp/bsu-profile-lint-final.log`, `/tmp/bsu-profile-broad-wiring-build.log`. Successful axiom scratch retained; owned failed/prototype scratch files removed. No owned build/check process remains live. No commits.

Full dependency-closed paper arguments and implementation state: [research card](../../drafts/pipeline/1-in-progress/bi-scale-multichain-gram-coupling-2026-10-17.md).

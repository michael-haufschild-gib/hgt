# Arithmetic Defect Rigidity (ADR)

**One question.** Which failures of critical arithmetic estimates survive normalization, localization
and passage to infinity — and which relations of the actual source restrict an escaping defect strongly
enough to control the signed quantity an established receiver consumes?

The working receiver is the centered damped Möbius receiver at damping `0 < ε < ½`. ADR separates its
energy from the much larger positive forcing, keeps the receiver as a signed Gram difference, locates
the forcing in the cofactor tail, prices successor/dilation words, pays the forcing by an explicit power
subtraction defined by the source's own pole trace, and extracts limits (energy quantiles; common
cofactor Gram limits carrying a cyclic critical Wiener module) that retain signed data. Each result
constrains what an escaping state can be.

**Open core: exclusion.** None of this bounds receiver energy. A source estimate excluding every escaping
state for a cofinal family of dampings would give RH through the critical-energy receiver; no such
estimate is an input or axiom here.

Namespace `GaloisForLFunctions.ArithmeticDefectRigidity`; umbrella `ArithmeticDefectRigidity.lean`.

---

## 1. Place in the research

The corpus has exact receivers (critical energy, continuation, Weil positivity, Hodge index, source
effectivity, orientation). Compensation theory proves normalized receiver profiles escape every fixed
window. ADR asks what survives that escape: a pointwise limit can be zero with total energy one; a
cofactor identity can become homogeneous on fixed cells while its forcing grows; a successor label can
act as the identity in the chosen norm. ADR keeps source data, observation costs, and the signed
residual with its moving support together.

| Programme | Relationship |
|---|---|
| [ArithmeticCompensationTheory](../ArithmeticCompensationTheory/README.md) | Normalized profiles, origin costs, escape; ADR studies what survives normalization |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Receiver, inversion identity, signed pairings, dilation calculus |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Actual-source bounds, VK estimate, successor covariance; mixed interactions as rigidity sources |
| [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md) | Smooth-power expansion, remainder estimates, Mellin cells, first-moment identity |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Critical Wiener algebra, paid ideals, hulls, operator hulls; ADR's cofactor limits are Wiener modules |
| [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md) | Successor counts; transfer must beat fixed-successor collapse |
| [SignedArithmeticEnergyIncidence](../SignedArithmeticEnergyIncidence/README.md) | Sign discipline through energies; compact negativity vs escape |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md), [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Geometric carriers and source effectivity; must preserve the adverse mode and its cost |
| APT, AIP, ACT, SRT, SSIC, BSU, TTPC | Global form and allocation; ground energies; width transfers; observation limits; countermodels; proportion results |

---

## 2. Objects and language

At damping `ε`: `c_ε(n) = Σ_{d|n} μ(d)d^{−ε}`, `m_ε = ζ(1+ε)⁻¹`, receiver prefix `A_ε(n) = Σ_{j≤n}(c_ε(j) − m_ε)`,
pronic pairing `⟨u,v⟩_T = Σ_{n≤T} u(n)v(n)/(n(n+1))`, receiver energy `E_T = ‖A_ε‖²_T`. Inversion identity:
`ρ_ε(n) = n − m_εΣ_{j≤n}j^{−ε}⌊n/j⌋ = A_ε(n) + D_ε(n)`, `D_ε(n) = Σ_{2≤j≤n} j^{−ε}A_ε(⌊n/j⌋)`.

| Object | Meaning | Lean |
|---|---|---|
| Forcing energy / floor | `F_T = ‖ρ_ε‖²_T ≥ b_εT^{1−2ε}` | `forcingEnergy`, `forcingFloor` |
| Signed covariance; Gram | `P_T = ⟨A,ρ⟩`; `G_T = ‖D‖²`, `Q_T = ⟨ρ,D⟩`; `F_TG_T − Q_T²` | `receiverForcingPairing`, `cofactorEnergy`, `forcingCofactorPairing`, `forcingGramDefect` |
| Cofactor tail | `D − D_{≤J}`; head coefficient `H_{ε,J} = Σ_{2≤j≤J} j^{−ε}/√j` | `cofactorTail`, `cofactorHeadCoefficient`, `cofactorTailErrorEnergy` |
| Moving window | `⌊log(F_T/E_T)⌋` | `forcingCofactorWindow` |
| Forcing power / remainder | `c_εn^{1−ε}`, `c_ε = −m_εζ(1−ε)/(1−ε) > 0`; `R_ε = ρ_ε − c_εn^{1−ε}` | `forcingPower`, `forcingRemainder` |
| Renormalized cofactor | `D̃_ε = D_ε − c_εn^{1−ε}` | `renormalizedCofactor` |
| Forcing mass | `Σρ_ε/(n(n+1)) → L_ε = −ζ'/ζ(1+ε)` | `forcingPronicMass`, `forcingMassLimit` |
| Pole-trace domain / operator | rows with absolute Mellin pairing at `1−ε`; `D̃v = Σ j^{−ε}v(⌊n/j⌋) − 𝓛(v)n^{1−ε}` | `poleTraceDomain`, `renormalizedCofactorOperator`, `traceDilation`, `traceCofactorPacket` |
| Energy quantile; quantile work | first crossing of `rE_T`; renormalized pairing between crossings | `receiverEnergyQuantile`, `quantileCofactorWork` |
| Cofactor Gram | `K_T(j,k) = ⟨D_jA, D_kA⟩_T/E_T`, `D_jv(n) = v(⌊n/j⌋)` | `cofactorGram` |
| Common limit / module | subsequence with all entries converging; Hilbert realization, `V_pv_j = v_{pj}`, Wiener action | `ActualCofactorLimit` |
| Cell word | successor translations + floor dilations; boundary cost `B(w)` | `CellWord`, `CellWord.boundaryCost` |

**Words.** *Defect state*: a proposed carrier of escaping energy with its operations, signed covariances,
scales and forcing — no abstract interface asserting exclusion is supplied. *Escape*: `E_T → ∞`;
*admission*: bounded. Distinctions: data vs estimate; reconstruction vs bounded output; uniqueness vs
coercivity; relative vs absolute smallness; a limiting Gram can lose its small signed coordinate; divisor
support loses multiplicity; moving parameters can have growing boundary cost.

---

## 3. Foundational results

### Scales and signed geometry
1. **Forcing dominates the receiver.** `F_T ≥ b_εT^{1−2ε}` and `E_T ≤ C_εe^{−κσ(T)/270}F_T` (VK,
   `σ = (log T)^{3/5}(log log T)^{−5/3}`) (`exists_receiver_le_vk_mul_forcingEnergy`); `F_T/E_T → ∞`
   (`tendsto_forcingEnergy_div_receiver_atTop`) whether or not `E_T` diverges. No scalar `a_T` keeps `a_T²F_T`
   bounded and `a_T²E_T` positive (`no_common_scalar_normalization`). Source-selective: the unsigned majorant
   has constant ratio (`majorant_div_forcingEnergy_eq`).
2. **Receiver = Gram tangent.** `G = F + E − 2P`, `Q = F − P`, `F + G − 2Q = E`, `0 ≤ FG − Q² = EF − P² ≤ EF`
   (`forcingGramDefect_bounds`); determinant/`F²` → 0 while distance/`E` = 1 (`gram_distance_div_receiverEnergy_eq_one`).
   Rank/positivity of the limiting matrix loses the receiver.
3. **Cofactor tail carries the forcing.** `‖D_{>J} − ρ‖² ≤ (1+H_J)²E_T` (`cofactorTailErrorEnergy_le`), so fixed
   tails converge to the forcing in forcing normalization; moving window `J_T = ⌊log(F_T/E_T)⌋ → ∞` with error
   `→ 0` (`tendsto_movingCofactorTailError_div_forcingEnergy_zero`). Fixed-label limits lose the whole forcing.

### Successors and words
4. **Fixed successors disappear on escape.** `‖A(·+k) − A‖² ≤ k²` ⇒ admission or normalized displacement → 0
   (`admits_or_fixed_successors_disappear`). Recentred energy is `o(k)` (`admits_or_energyScale_recentered_successors_disappear`);
   with VK, recentred `o(k^{1−ε})`, raw `o(k^{2−2ε})` (`admits_or_sourcePower_successors_disappear`).
5. **Words have boundary budgets.** `⌊n/q(w)⌋ ≤ w(n) ≤ ⌊n/q(w)⌋ + B(w)`; normalized displacement `≤ B(w)²/E_T`;
   forcing work `|W| ≤ B(w)L_ε` (`abs_wordForcingWork_le`, `admits_or_fixed_word_forcing_work_disappears`); new
   horizon cells paid uniformly: tail work `≤ B(w)C^{tail}(H+1)^{−ε}` (`abs_wordForcingHorizonTailWork_le`).

### Paid renormalization and the pole trace
6. **Power subtraction pays the forcing.** `ρ = c_εn^{1−ε} + R`, `‖R‖_T ≤ B_ε` at every horizon
   (`forcingRemainderEnergy_le`); `A + D̃ = R` (`receiver_add_renormalizedCofactor_eq`); admission or
   `‖A + D̃‖²/E_T → 0` (`admits_or_renormalized_inversion_is_homogeneous`). Renormalized pairing is **antipodal**:
   `(P̃/E + 1)² ≤ B²/E` (`renormalizedCofactorVariation_sq_le`); total variation `V_T ≤ B√E` pays every moving
   localization (`admits_or_all_moving_localizations_retain_density`). **Trace-free form:** the alternating
   sum `H_εv = Σ_{j≤n}(−1)^{j+1}j^{−ε}v(⌊n/j⌋) = (I − 2^{1−ε}D₂)Sv` kills the pole exactly, `‖H_εA‖_T ≤ B` at every
   horizon with no domain or trace (`exists_pronicNorm_etaCofactorSum_actual_le`); its power-row symbol is
   `(1 − 2^{1−ε−s})ζ(s+ε)` (`exists_pronicNorm_etaCofactorSum_powerRow_le`). One Euler law `w − p^αD_pw` admitted
   leaves the ghosts `n^αΠ({log_p n})` (`one_euler_factor_leaves_a_ghost`); the laws at `2` and `3` together ⟺
   `w − cn^α` admitted with unique `c` (`exists_pronicEnergy_sub_pole_ne_top`), so for `Sv` the eta and 3-adic
   laws are the renormalized inversion law on every row (`cofactor_two_euler_laws_iff`).
7. **Finite forcing mass.** `0 ≤ ρ ≤ m_εM_εn^{1−ε}`; pronic mass → `L_ε = −ζ'/ζ(1+ε)`, optimal
   (`forcingMassLimit_eq_logarithmicDerivative`, `forcingMassLimit_isLUB`). Pays bounded cell errors, not
   `⟨A, ρ⟩`.
8. **Absolute pole trace.** `Σ|A(n)|n^{ε−2} < ∞` (VK envelope) and `𝓛(A) = α⁻¹ΣA(n)Δ_α(n) = c_ε > 0`, `α = 1−ε`
   (`actualPoleTrace_eq_forcingPowerCoefficient`, `actualPoleTrace_pos`). The domain `𝒳_ε` and linear operator
   `D̃` realize the subtraction; actual image lies in the domain (`actual_renormalizedCofactor_mem_poleTraceDomain`).
   Fixed dilations preserve `𝒳_ε` with trace weight `j^{−α}`; packets cost `Σ_{j∈S}1/j·𝓛(v)`
   (`poleTrace_traceCofactorPacket`) — harmonic, not summable.
9. **Bounded commutator.** `(D̃D_p − D_pD̃)v(n) = 𝓛(v)(⌊n/p⌋^α − p^{−α}n^α)`, norm `≤ |𝓛(v)|` uniformly in `p`, `T`
   (`pronicNorm_renormalizedCofactorOperator_commutator_le`); vanishes on escape for every moving `p(T)`
   (`admits_or_moving_cofactor_commutator_vanishes`).
10. **Residual + trace determine the row.** `v = Σ_dμ(d)d^{−ε}𝓡(v)(⌊n/d⌋) + 𝓛(v)q_ε(n)`
    (`residual_and_trace_injective`, `actual_receiver_reconstruction`). `q_ε ∈ 𝒳_ε` with `𝓛(q_ε) = 1` (PNT with
    rate), so `ker(I + D̃) = ℝq_ε` exactly (`ker_renormalizedResidualOperator`); the unestimated term is the
    Möbius floor inverse of `R`.
11. **Symbol of `D̃`.** On power rows, `0 < Re s < 1−ε`: `Σ_{j≤n} j^{−ε}⌊n/j⌋^s = ζ(s+ε)n^s + 𝓛_s n^{1−ε} +
    O(n^{(Re s−ε)/2})` (`norm_powerRowCofactorSum_sub_le`), so `(I + D̃)n^s = ζ(s+ε)n^s` modulo admitted rows.
    For `Re s ≥ ½` a power row satisfies `D̃v ≈ −v` iff `ζ(s+ε) = 0`
    (`powerRow_renormalizedInversion_bounded_iff`); real exponents never do. **Index:** on
    `log^k n·n^s` rows `I + D̃` is the Leibniz matrix of `ζ^{(i)}(s+ε)`; the power-log eigenspace at
    `s` has dimension `ord_{s+ε}ζ` (`powerLogRows_renormalizedInversion_iff_order`), and over any
    finite exponent set it is the direct sum of the zero blocks, dimension `Σ ord`
    (`powerLogRows_global_renormalizedInversion_iff_order`; exponents separated by `D_2`, `D_3`).
    **Mellin residues:** `v = Σc_sn^s + r`, `S_εv = c'n^{1−ε} + r'` (`r, r'` finite energy) forces
    `ζ(s+ε) = 0` whenever `c_s ≠ 0` (`riemannZeta_add_eq_zero_of_powerLike_solution`): `𝓜(S_εv) = ζ(·+ε)𝓜v`,
    `𝓜r` continues to `Re w > ½`, `𝓜(n^s)` has its pole at `s`.

### Extraction
12. **Energy quantiles.** Increments ≤ 1 ⇒ quantile intervals keep mass `(s−r) ± 1/E`
    (`admits_or_quantile_interval_error_vanishes`) and antipodal work `W/E → −(s−r)`
    (`admits_or_quantiles_preserve_antipodal_work`); every positive level crossed with unit overshoot
    (`admits_or_every_positive_level_has_unit_overshoot`).
13. **Common cofactor limit.** One subsequence makes every `K_T(j,k)` converge (`exists_cofactorGram_limit`, also
    along any prescribed cofinal family `exists_actualCofactorLimit_along_cofinal`): `K(1,1) = 1`, symmetric,
    `|K(j,k)| ≤ 1/√(jk)`, PSD, packet contraction `Q(pa) ≤ Q(a)/p` (`cofactorGram_packet_dilation_le`). Normalized
    Gram steps vanish (`cofactorGram_succ_sub_tendsto_zero`); paid corrections and vanishing-relative-energy
    perturbations preserve moving Grams (`normalized_moving_gram_perturbation_tendsto_zero`). Diagonal
    `pK(p,p) = lim E(⌊T/p⌋)/E(T)`, nonincreasing (`contracted_energy_ratio_tendsto`, `scaled_diagonal_antitone`);
    all scaled dilation quadratic forms decrease in numeric order
    (`scaled_dilation_norm_sq_antitone`), and every `pK(p,p)` lies in `[0,1]`
    (`scaled_diagonal_mem_Icc`). Exact incomplete fibres give the uniform mixed error `C·D/p`.
    admission ⇒ unique full-horizon kernel (`kernel_eq_of_admits`). Every intermediate coordinate limit
    occurs in another actual kernel (`exists_kernel_with_intermediate_coordinate`); the kernel family is
    a singleton or has exactly continuum cardinality (`actualCofactorKernelSet_singleton_or_continuum`).
    Nonuniqueness forces escape (`not_admits_of_kernel_ne`). Module isomorphism classes remain unclassified.
14. **Wiener module.** Every actual limit has a cyclic Hilbert realization with `‖V_p‖ ≤ p^{−½}`, integrating to a
    contractive unital `𝒲_{1/2}` representation; annihilator closed, proper, nonempty hull
    (`moduleHull_nonempty`). On escape the paid ideal annihilates it, so `∅ ≠ hull ⊆ obstructionHull(μ_ε)`
    (`admits_or_moduleHull_subset_obstructionHull`); repairing kernels have bounded dilation energy, vanishing
    after normalization (`admits_or_all_gram_limits_annihilate_repairs`). Signed realization: residual vectors are
    `−v_j`, remainder vectors 0, normalized fixed traces 0 (`admits_or_signedCofactorGram_tendsto`).
    Every positive cofactor diagonal yields an actual contracted state
    `K_p(j,k)=K(pj,pk)/K(p,p)` (`exists_actual_contracted_module`), with full Wiener intertwining
    (`contractedKernelIsometry_wiener`) and annihilator `I:δ_p` (`cofactorAnnihilator`).
    Its module is exactly the closed dilation range (`range_contractedKernelIsometry`);
    finite quotient index drops by `dim ker D_p` (`cofactor_index_add_dilation_nullity`). Positive
    contractions compose on kernels and ideals (`contracted_kernel_compose`, `cofactorAnnihilator_compose`).
15. **Module structure.** Admitted modules are faithful with full Bohr hull, infinite-dimensional, continuum
    quotient (`faithful_or_receiver_escapes`, `receiver_escapes_of_finiteDimensional`): a finite-dimensional or
    non-faithful actual module forces escape. Annihilator quotient is finite or continuum, never countable
    (`annihilator_quotient_finite_or_continuum`); finite index = Σ joint character multiplicities
    (`finrank_quotient_eq_sum_normalizedModuleHull`); a zero diagonal at `p` forces dimension ≤ `p−1`
    (`finiteDimensional_and_finrank_le_of_kernel_diag_eq_zero`). Rank-one modules: augmentation or
    `χ(p) = η(p)p^{−s}`, `s ≥ ½`, `η` multiplicative sign (`rankOneCharacter_eq_augmentation_or_signed_rpow`) —
    magnitudes forced, signs/exponent not tied to zeros. At the row level tiedness is automatic: a row
    with `w − 2^{s₂}D₂w`, `w − 3^{s₃}D₃w` admitted, `Re s₂ = Re s₃ ∈ (½,1]`, is `cn^s` + admitted with
    `2^s = 2^{s₂}`, `3^s = 3^{s₃}`, or admitted (`exists_cPronicEnergy_sub_cpow_ne_top`); untied pairs
    allow no escaping row. Operator hull obeys dilation radii.
    Every defined rank-one contraction preserves the kernel and complete annihilator
    (`contracted_kernel_eq_of_finrank_one`, `cofactorAnnihilator_eq_of_finrank_one`).
    Every hull character of a finite-dimensional actual module has augmentation or radial modulus
    (`finite_moduleHull_modulus_classification`), and one sequence of half-plane evaluations converges
    to it on every Wiener element (`exists_halfPlane_sequence_of_mem_finite_moduleHull`).
    Complete source pairings respect conjugation; cyclic norms are unchanged,
    the annihilator is conjugation-invariant (`conjW_mem_annihilator_iff`),
    and every actual module hull is conjugation-symmetric (`conj_mem_moduleHull`).
16. **Unit transport.** Real Wiener unit convolution transports Grams and preserves escape
    (`admits_or_real_unit_convolution_gram_tendsto`); Möbius and Liouville modules are unit-equivalent
    (`admits_or_liouville_gram_is_unit_transport`).
17. **Origin boundaries.** Constant-row dilates reset at zero have the max kernel `1/max(j,k)`
    (`pronicPairing_originSteps_tendsto`), a faithful module with full Bohr hull; positive max-kernel mixtures of
    actual Grams are faithful (`representation_injective` in `PositiveOriginMixturesAreFaithful`). Escape records
    (sublinear square-prefix records, `admits_or_exists_record_horizons`) realize every positive origin mass
    `c`, giving shifted rows with Gram `K + c/max(j,k)` (`admits_or_every_positive_resetOrigin_boundary_is_realized`,
    `admits_or_every_positive_faithful_boundary_is_realized`) — shifted, not unshifted limits. A constant
    origin boundary violates cofactor contraction (`unreset_boundary_ne_actual_kernel`); bounded rows pair
    boundedly with subcritical cofactors (`exists_uniform_bounded_row_pairing`). Raw shifted rows realize
    `(K+c)/(1+c)` for every positive `c` on escape and cannot equal any actual zero-origin kernel
    (`admits_or_every_positive_unreset_boundary_is_realized`). The step module and every positive
    reset mixture are infinite-dimensional with continuum annihilator-quotient rank
    (`not_finiteDimensional`, `annihilator_quotient_rank` in the two origin-module namespaces).
    When `k/E → 0` and `A(k)/√E → a`, normalized raw displacement converges in pronic norm to
    the scalar origin trace (`normalized_successor_tendsto_origin_trace`). On escape, any nonvanishing
    cofinal displacement forces `k²/E` above every bound frequently
    (`admits_or_nonvanishing_successors_require_unbounded_scale`).

The origin-boundary leaves, raw-origin convergence, boundary-index corollaries,
vanishing-relative-energy perturbation, complete cofactor contractions, numeric operator order and finite-hull approximation
passed canonical Lean checks and standard-axiom audits. The
[completion ledger](../../../docs/drafts/pipeline/3-formalized/q-iii-existing-findings-lean-completion.md)
records each completed audit.

### Countermodels (Gram laws do not classify the source)
18. White noise satisfies the compactness laws and has a unique antipodal extension
    (`whiteNoise_has_unique_antipodal_extension`); prime-deleted white noise keeps positivity and packet
    contraction but violates horizon order (`actual_kernel_ne_oddWhiteNoise`); the augmentation model satisfies
    positivity, contraction and diagonal order with hull outside every half-plane point
    (`augmentation_character_hull_eq_singleton`).

---

## 4. Mechanisms and principles

Mechanisms: scale separation via a proved arithmetic estimate; signed Gram coordinates; tail accounting;
word calculus; paid renormalization; dual mass control; paid commutation; source boundary trace; joint
covariance extraction; energy-quantile transport; Wiener-module structure of limits.

Principles: construct from actual coefficients/identities; keep signs until a loss has a proved budget;
keep horizon, damping, cutoff, location and scale quantifiers visible; preserve the defect studied;
charge overlap, new cells, boundaries and the Gamma/polar reserve once; keep multiplicity; test
selectivity against countermodels; allow diffuse escape and growing carriers (no fixed bad packet, no
assumed gap); separate identity, estimate, extraction and exclusion.

---

## 5. Pillar theorems

1. Scale separation (`tendsto_forcingEnergy_div_receiver_atTop`, `no_common_scalar_normalization`).
2. Gram tangent (`gram_distance_div_receiverEnergy_eq_one`).
3. Paid renormalization and antipodality (`admits_or_renormalized_inversion_is_homogeneous`, `renormalizedCofactorVariation_sq_le`).
4. Pole trace (`actualPoleTrace_eq_forcingPowerCoefficient`) and commutator (`admits_or_moving_cofactor_commutator_vanishes`).
5. Quantile transport (`admits_or_quantiles_preserve_antipodal_work`).
6. Common limit and Wiener module (`exists_cofactorGram_limit`, `admits_or_moduleHull_subset_obstructionHull`).
7. Faithfulness dichotomy (`faithful_or_receiver_escapes`, `receiver_escapes_of_finiteDimensional`).

---

## 6. Traps

- Pointwise disappearance of forcing does not justify discarding its global pairing.
- Power subtraction on the actual row is not a bounded operator on arbitrary rows.
- Finite forcing mass controls bounded cell errors, not the receiver prefix.
- Vanishing `E_T/F_T` allows `E_T → ∞`.
- A PSD or rank-one limiting Gram can lose the critical distance coordinate.
- Floor commutators and multiplicativity identities need not contain Möbius cancellation.
- Fixed words lose successor selectivity under energy normalization.
- Termwise absolute cofactor control has the half-damping threshold.
- Entrywise convergence does not justify a moving cutoff or infinite cofactor sum.
- Existence of a nonzero common Gram module is not evidence of escape (it exists when admitted).
- Antipodality and Gram laws are satisfied by white noise; source realization is essential.
- Shifted origin-reset rows are not unshifted actual limits.
- `h = D + R` with `D, R ≥ 0` gives no upper bound forcing `D = 0`.
- Density-one or eventual-height results may leave finitely many off-line zeros; aperture ≠ damping.

---

## 7. Open problems

| Topic | Required output |
|---|---|
| Joint extraction | One carrier holding fixed covariances, quantile signed work and the moving cofactor tail, with rate and spatial data, without exchanging an uncontrolled infinite sum and a limit; via `H_ε` the tail is bounded by consecutive dilation differences `‖D_jA − D_{j+1}A‖` (`pronicNorm_etaCofactorTail_le`), so this is a dilation-regularity question |
| Exclusion / source selectivity | An independently proved estimate excluding the tangent state or its approximate eigenrelation `D̃u ≈ −u`, violated by impure models; rows with two dilation laws (`O(1)` errors) satisfying the inversion law exist at `s` iff `ζ(s+ε) = 0` (`riemannZeta_add_eq_zero_iff_exists_rankOneEscapeRow`), so the gap is that escape states need not be joint `D₂,D₃` eigenrows with absolute errors |
| Module classification | Which Wiener modules occur on escape: is `hull ⊆ obstructionHull` an equality; are signs/exponents of rank-one characters tied to zeros; exclude finite-dimensional escape modules by a source law |
| Mixed Bézout/Vaughan covariance | Summable signed gain after centering, with horizon and damping dependence |
| Successor dynamics | Moving words or amplified operations acting nontrivially at the escape scale with proved boundary cost |
| Operator domains | Domain invariance and critical-norm bounds for the full renormalized operator; harmonic packet costs |
| Absolute compensation | Signed tail and new horizon cells paid in the receiver norm with cross terms |
| Shared allocation | One certificate for the full signed form across overlapping carriers and one Gamma/polar reserve |
| Anti-collapse | Quantitative local depth mass of actual divisor packets, with multiplicity |
| Enumerative certificates | `D + H = B`, `H ≥ 0`, with an independent bound below the defect quantum |

---

## 8. Contribution criteria

A full no-escape theorem extracts a nonzero state from any divergent receiver, retains the signed and
moving data, and excludes it by an independent source relation for a cofinal damping family; or proves a
direct absolute energy estimate. A contribution supplies a new estimate, exact decomposition,
classification, transport law, or obstruction with a positive survivor, and states the source property
used and countermodels excluded, the signed residual and its norm, treatment of moving support, overlap,
boundary and multiplicity, the consuming receiver or extraction step, and the separation between proved
input and open estimate.

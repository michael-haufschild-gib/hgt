# Route obstacles — status quo

Scope: the 38 live route formulations, the 12 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** `065c78c2b5` (2026-11-13), working-tree sources included; the frontier map at the same checkpoint. Fact log: `logs/review-1311-frontier-facts.md` (cited as "log §n"). Companions: [obstacles-summary.md](obstacles-summary.md) (A/B lists, openings, programmes, the one question), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ), [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem).

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means the source-to-receiver step is missing. HJ is PA; the BSY criterion of FEL belongs to CTF; PCS, DR, PW-B, HAT-G, ISC-polar are retired labels.

**Evidence.**
- `[L*]` Lean statement read at its declaration for this report and recorded in the fact log with file and line.
- `[F]` stated by the [frontier map](../rh-current-frontier-map.md) at the checkpoint; `[KR]` stated by the [scoped-obstruction ledger](../rh-killed-routes.md). `[S]` a module the frontier map grades unfinished or unintegrated.
- `[D]` deduction made here from `[L*]` statements (log §15, §16, §19, §21); not a Lean theorem. `[doc]` mechanism described in a module docstring whose statements were read. `[C]` classical mathematics, not in the corpus. `[A]` assessment.
- `[X]` the half-plane `7/8`, taken as proved: every Dirichlet `L`-function, ζ included, and every Hecke `L`-function of the family over `ℚ(√−3)` is zero-free in `Re s>7/8`; so `Θ≤7/8`. It is an external theorem (OpenAI, 30 September 2026). In the Lean source it is stated without hypotheses (`riemannZeta_ne_zero_of_seven_eighths_lt_re`, `DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, `riemannZeta_zero_mem_quasiRH_strip`, `ProbeFinalAssemblyUnconditional.common_probe`; log §8). The frontier map grades this source `[S]`: a statement in source, not a verified theorem; validating the producer chain is just work (A118). Consequences of `[X]` on receivers are deductions `[D]`: no receiver is stated in Lean with the half-plane inserted (A138).

**Strength.** RH; ≥qRH (implies a zero-free half-plane, Lindelöf or ZAL; open where it gives a half-plane below `7/8`); AAL; sub (implies neither a half-plane nor AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in [obstacles-summary.md](obstacles-summary.md) §2.1–2.2. `(unverified)` marks A items whose difficulty is not established. Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; `w=Θ−½` the zero width (`zetaZeroWidth`). **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **World I** ¬AAL (a finite isolated top layer); **World II** AAL ∧ ¬ZAL (a tail). `2Re S(log p)` is the prime trace; a **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. The **restricted Weil form** at aperture `a` acts on tests supported in `[−a,a]`. A **step packet** is constant on the blocks `(a,a+1]`. The **block matrix** of a window `(R,R+J]` at modulus `Q` is the Weil form on step packets; `neutralBlock Q a b = blockMatrix Q a b − deg a − deg b` and the **neutral part** is `neutralWindow Q R J`; its off-diagonal entries are negative: **jets** (archimedean) and **contacts** (block `b` meets block `⌊b/k⌋` with weight `Λ(k)/k`, `2≤k≤Q`). A **bound state** is a negative square of the neutral part; `−λ` (lowest eigenvalue `λ<0`) is the **binding energy**. The **ratio** of a window is `(R+J)/R`; the **block size** is `R`. The **Doob chain** of a window is the reversible chain obtained by the ground-state transform of its neutral part with a positive eigenvector; its **gap** is its Poincaré constant. A **margin** `C` of a window: the neutral part plus `C·1` has at most one negative square. The **step-packet floor** at ratio `3K+1`: the least `c` with `packetForm ≥ −c·Σσ²` on step packets. For a window `(R,2D+b]`, `D=R+a`: the **dyadic middle** is `(D,2D]`, the **ends** are `(R,D]` and `(2D,2D+b]`; the **conditional energies** `E₁,E₂` of the ends and the **conditional coupling** `X=K−P₁ᵀM⁻¹P₂` are the blocks of the Schur complement of the middle `M` (`overlapLeftEnergy`, `overlapRightEnergy`, `overlapCoupling`). The **two-end family** `o_v` is the pole-free antisymmetric profile at separation `v`. A **completion** `G_d` of the couplings is the matrix with off-diagonal entries `neutralBlock` and diagonal `d` (**self-pairings**). The **critical half-line state** at a finite critical ratio `W=inf_A windowThreshold(A)` is a unit vector supported on `u<0` with nonpositive truncated Weil form at every cutoff. A **system** is a weight system with a mass; the **trivial aperture** is `log log(mass)+o(1)`. The **signal** of a kernel `G` is `(1/2π)∫G(2+it)Z^{2+it}dt`. The **probe** is the cubic-theta sum of `[X]` over `ℚ(ζ₃)`, twist order `n=6`. A **two-sided edit** is the system of the rational primes with some primes deleted and some doubled; it is a **fake** at `β` if its count is `Ax+O(x^β)` and its zeta function continues with a zero that ζ lacks. The **FE defect** `g` of a system is its critical-line functional-equation defect in the Hamburger strip class. The **heat family** is `H_τ(z)=∫Φ(x)e^{τx²}e^{izx}dx`, `H_0=Ξ`; a **forward time** has `Re τ>0`; a **branch time** is a `τ` at which `H_τ` has a multiple zero; the **forward monodromy group** `G₊(b)` consists of the permutations of the zeros of `H_b` obtained by transport along loops of forward times avoiding the branch times; two zeros are **simply joined** if a continuous family of simple zeros along a path of forward times connects them. `Λ_dBN` is the de Bruijn–Newman constant (`newmanConstant`).

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| Width `≤σ` ⇔ the prime trace is `≥−Kp^σ` on cofinal logarithmic windows after `≤Ce^{δT}` omissions; the upper bound alone on undeleted windows is equivalent; two fixed primes on difference lags in windows of radius `r√T` suffice. Every radius `R=o(log T)` admits a tempered countermodel | [F] (log §9, SRT) | one inequality per prime on sparse windows; no window below the logarithmic radius decides |
| RH ⇔ on every window `(R,R+J]`, `R≤J`, disjointly supported nonnegative packets `x,y` with `N(x,x)<0` satisfy `N(x,x)N(y,y)≤N(x,y)²` ⇔ every eigenvector of the neutral part with negative eigenvalue has one sign. The supremum of the index of the block window is governed by the number of zeros right of the line | [L*] (`riemannHypothesis_iff_forall_wells_bound`, `riemannHypothesis_iff_forall_bound_state_one_sign`, `exists_le_hermNegIndex_blockWindow_iff`; log §10, §16) | RH is a Hodge index inequality between positive packets without common blocks: a binding inequality |
| Certified: block-matrix floor `1/5000` and exactly one bound state for `R≤J`, `50J≤53R` at every block size; margins `1/20`, `1/100` on the first step packets of ratio four and seven; nonnegativity on thin step packets at every ratio; index `≤300000` at ratio four, uniformly bounded at each ratio | [L*] (`sum_blockMatrix_ge_of_short`, `hermNegIndex_neutralWindow_eq_one`, `packetForm_stepPacket_ratioFour_ge`, `exists_forall_packetForm_thin_stepPacket_nonneg_ratio`, `hermNegIndex_blockWindow_ratioFour_le`; log §10, §12, §16) | certified range: ratio `≤103/50`, first blocks, thin packets |
| The floor at ratio `≤103/50` is the ground energy `≥1/5000` of Weil's form at aperture `181/500`, carried to the step packets of every block size; at that aperture the Liouville-twisted form is negative on an odd test. The certificate: pole square, rational envelope and a `23×23` Legendre factorization on the even sector, Schur lending on the odd sector. The dilation tower above it is frozen: `a_k<0.3621` | [L*] (`one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths`, `groundEnergy_mul_nested_mass_le_packetForm_of_log_lt`, `exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg`, `weilFloorApertureTower_lt`; log §19, §21); [doc]; [KR] `frozen-weil-floor-tower` | the certified sign is selective in the prime 2; a certificate at an aperture `A` is the index at every block size at ratio `<e^{2A}` [D18]; continuation in the aperture by dilation stops |
| The neutral part of every window of ratio `≤103/50` has second-lowest eigenvalue `≥1/5000`; the conditional energy of an end given a dyadic middle inside such a window is `⪰1/5000` | [D4], [D10] (log §15, §16) | at the first overlap step the open quantity is the conditional coupling; with these floors alone the step needs `‖X‖≤1/5000`, and the direct coupling has norm up to `≈0.03` [D12], [D25] |
| Overlap law. The window `(R,2(R+a)+b]` holds one bound state iff its two overlapping parts hold one each and `(uᵀXv)²≤(uᵀE₁u)(vᵀE₂v)` for all `u,v`. RH ⇔ this contraction on every window with `R≥34`, `a,b≥1`. Equivalently the neutral form is nonnegative on the `N`-orthogonal complement of the dyadic middle | [L*] (`hermNegIndex_neutralWindow_overlap_eq_one_iff`, `riemannHypothesis_iff_forall_overlap_contraction`; log §12); [D11] | an exact full-rank recursion on the ratio: parts of ratio `≤ρ` glue to ratio `≤ρ²/2` [D1]; ratio three is four steps from `103/50` |
| Doob chain. RH ⇔ on every window the Doob chain of the neutral part has gap `≥` binding energy ⇔ gap `≥` binding `−C` with one `C`. Unconditionally gap `≤` binding `+c₀`. A cut whose conductance is below the product law gives a second bound state | [L*] (`riemannHypothesis_iff_forall_doob_poincare`, `riemannHypothesis_iff_forall_doob_poincare_sub`, `exists_doob_test_le`, `two_le_hermNegIndex_of_bottleneck`; log §5) | RH is a mixing statement for explicit reversible chains |
| Margin. RH ⇔ `∃C`: every neutral window plus `C·1` has index `≤1`; the initial windows `(1,2M]` suffice. RH ⇔ `∃D`: step packets at every ratio `3K+1` have floor `−DΣσ²`. A positive uniform margin is incompatible with RH: under RH long windows carry planes with `0≤N≤ε·mass` | [L*] (`riemannHypothesis_iff_neutralWindow_margin_bddBelow`, `riemannHypothesis_iff_initialWindow_margin_bddBelow`, `riemannHypothesis_iff_packetForm_stepPacket_bddBelow`, `exists_plane_neutralForm_le_of_riemannHypothesis`; log §5); [KR] `continuum-doob-margin` | RH is a bounded additive loss, not a gap |
| Exponent. A step-packet floor `−CK^θ`, or a neutral margin `CK^θ`, with `0≤θ<½` gives width `≤θ`. Unconditionally the floor is `−C√K` | [L*] (`zetaZeroWidth_le_of_packetForm_stepPacket_ge`, `zetaZeroWidth_le_of_neutralWindow_marginRate`, `exists_packetForm_stepPacket_ge_sqrt`; log §11) | every exponent below `½` at the matrices is a zero-free strip; the baseline is exactly the trivial strip |
| Two-end family. `N(o_v)=2Re S(0)−2Re S(v)`. RH ⇔ `N(o_v)≥−C` for all `v≥0`; width `≤θ` ⇔ `N(o_v)≥−Ce^{θv}` | [L*] (`neutralForm_twoEndOdd`, `riemannHypothesis_iff_twoEndOdd_bddBelow`, `zetaZeroWidth_le_iff_twoEndOdd_rate`; log §5, §16) | one explicit one-parameter family decides; with `[X]` it satisfies `N(o_v)≥−Ce^{3v/8}` [D5] |
| Binding at long ratio. On `(R,20mR]` the binding energy is `≥c√m` from the two ends; under RH it is `≤√ρ−1/√ρ+log ρ`; the ground state of a long window concentrates on its two ends | [L*] (`eigenvalue_le_twoEnds`, `sq_binding_excess_le`; log §5); [F] | the bound state of a long window is a two-end state |
| Gluing kills. Rank-one charge gluing of the halves of ratio four exists iff `R=1`; no rank-`r` lowered model with `600(r+1)≤H` has index one; fixed-rank absolute-error gluing fails | [L*] (`halves_of_ratio_four_glue_iff_eq_one`, `two_le_hermNegIndex_lowered_model_of_rank`; log §10); [KR] `ratio-four-low-rank-gluing` | the binding has rank proportional to the block size; only full-middle inversion with signed coupling survives |
| Contacts. Liouville-twisted contacts give index `≥2` on every window of ratio `≥3`; contact multipliers `ω₂,ω₃∈[−5/2,19/40]` give index `≥2` at ratio `≥4`. With the true contacts `N(σ,0,−U₂σ)≥Σσ²/30` on `(2r,6r]` | [KR] `weakened-contact-binding`; [L*] (`bilin_neutralWindow_lowerEnd_upperEnd_le`; log §8, §12) | the true contacts of 2 and 3 hold a window of ratio three or four together; the binding is not perturbative in the jets [D8] |
| Floor trees alone. At ratio four the contact graph has `r` isolated triples in `(6r,24r]`; the continuum dilation form has zero gap at every fixed `Q`; the log-coordinate jump generator has `Γ₂≥0` and no positive curvature bound. On component indicators the full-chain energy equals the jet energy | [L*] (`component_ratio_four`, `doobEnergy_component_eq_prime_free`, `dilationForm_le_of_no_gap`, `not_curvature_pos`; log §5, §11); [KR] `floor-tree-only-mixing` | no mixing proof from the contacts alone and none from curvature; the jets enter at the binding scale |
| Self-pairings. On `J≤R`, a completion of the couplings with index `≤1` has, on one of two runs of `m` blocks `≥m` apart, self-pairings summing to `≥m log m−2m`; with nonpositive diagonal (`R,J≥24`) the index is `≥2`; couplings `−N` with nonnegative diagonal have `≥2` positive squares; the dyadic window `(3m,6m]` attains `m log m+m/2` | [L*] (`sum_selfPairing_ge_of_hermNegIndex_le_one`, `two_le_hermNegIndex_of_selfPairing_nonpos`, `two_le_hermNegIndex_neg_of_couplings`, `hermNegIndex_neutralWithDiagonal_self_le_one`; log §11); [KR] `nonnegative-self-pairing-realization` | mixed areas and nef classes are excluded; a geometric pairing `−N` has self-intersections of size `−log m` per block |
| Below ratio two the contacts vanish; for aperture `A<log 2` the Weil form is archimedean plus pole | [L*] (`contactW_eq_zero_of_window`, `weilQuad_eq_arch_of_primeFree`; log §16) | no unconditional sign theorem below ratio two uses a prime contact [D] |
| The index of the restricted Weil form at an aperture is the sum of the nullities below it and the number of crossings of the aperture conormals with the graph of Weil's operator | [L*] (`negativeRank_eq_sum_nullity`, `negativeRank_eq_sum_apertureCrossing`; log §16) | the Morse index of the sign problem is a Maslov index |
| RH, or a finite critical ratio `W` with a critical half-line state. At every confinement ratio the unit-mass floor is attained, the minimizer is unique up to sign with Laplace transform zero-free on `Re z>0`; the floor is strictly concave in the inverse ratio; at finite `W` the state is outer and cyclic, with `λ′(W)=−a(W)∫F²e^{−8u}/W`. Strong confinement: `λ−a−log a→μ`. Coercivity `Q≥L₊+4M−16`; every unit trial Rayleigh sublevel has compact `L²` closure | [F] (HF; log §11); [L*] (`universal_softLogarithmic_confinement_limit`, `SoftLogarithmicHalfLineDomain.coercive`, `isCompact_closure_softLogarithmicRayleighSublevel`; log §8, §10, §11) | a failure of RH has one canonical extremal function; every property proved for it holds on both sides of the charge question |
| A finite-`W` critical state satisfies `\|F(u)\|≤C_βe^{βu}`, `½<β<15/2`, and `∫F²e^{−bu}<∞`, `b<15`; sharp collars obey a trace-free shifted-energy lower bound | [S] (`criticalHalfLineGroundState_exponential_bounds`, `terminalCut_energy_lower`; log §8) | the counterexample object decays exponentially; the wall trace and its flux law are not supplied |
| The critical comb has growth exponent the zero width; RH ⇔ subpolynomial growth ⇔ absolute logarithmic Abel integrability at every damping; the Laguerre tails tend to the paired Li coefficients | [L*] (`strictGrowth_criticalPowerCombTail_iff_zeroWidth`; log §10); [F] (ACS, LI) | the width and the Li coefficients are read on one explicit sequence |
| `Θ≤7/8`; AAL ⇔ `Θ∞=Θ`; ZAL ⇔ `Θ∞=½`; RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ the supremal negative index is `0` or `∞` | [X]; [F] (scope guards; log §9) | a failure of RH is world I or world II with top `≤7/8` |
| Two-sided edits of the rational primes with a count rate add exactly a pair `β±iγ` right of some `σ₁<½` when `½<β<2/3`, `Θ+2β<2`, `ζ(β+iγ)≠0`; globally meromorphic distinct-prime models with `0≤Λ̃≤2Λ` exist for every `Θ<β<1` when `Θ<1`; every prime-deletion fake has a real fake zero dominating its extra zeros | [L*] (`exists_isIntegerNormFakeAt_sEdit_lt_half`; log §8); [KR] `two-sided-prime-edits`, `meromorphic-euler-firewall`, `integer-norm-fakes-above-half` (log §4) | Euler product over the rational primes, integer norms and a count rate constrain no finite layer |
| Order law of edits: `k!` divides `Σ_{j=2}^k(k!/j)n(js₁)`; prime multiples; an `M`-fold twin pays `Re ρ/p` for every prime `p∤M` with `Re ρ(1−1/p)<13/30` | [L*] (`factorial_dvd_sum_order_of_count`, `re_div_le_of_count_multiple_edit`; log §8) | the count sees a fake zero through divisibility of orders |
| FE rigidity. A unit-multiplicity Beurling system in the Hamburger strip class with defect `O((1+\|t\|)^{−1/2+ε₀})` is the rational primes. Positive real weights admit arbitrarily slow defects with prescribed off-line zeros. A real-weighted fake on the integers has an Abel floor and no decaying defect; a signed fake has bounded defect | [L*] (`beurlingSystem_rigidity_of_decaying_defect`, `exists_positiveWeighted_beurling_slow_defect`, `fake_abelMass_floor`, `signedPoly_fake`; log §10, §16) | among unit multiplicities decay selects ζ; among positive weights no growth bound short of boundedness does |
| `Θ=1` with AAL, or `Θ<1` and fake edits with subpolynomial defect energy | [L*] (`frontier_dichotomy`; log §10) | the reflection decides only up to a decaying error |
| The cubic probe is a coupled tower: `T(b)=(3+b)/6`, limit `3/5`; every `6r`-periodic Gauss pairing has coupled fixed point `(4r−1)/(6r−1)≥3/5`, equality iff `r=1`; crossing the model floor needs a bilinear saving before Cauchy–Schwarz (`≥1/12` for boundary `¾`, `≥1/3` for boundary `½` at `n=6`); the binding bin has endpoint exponent `−7/30672` at `7/8` | [L*] (`gauss_pairing_6r_thresholds`, `signedGram_phase_endpoints`, `endpoint_binding_bin`; log §10, §12); [KR] `cubic-tower-half-plane-barrier`, `phase-blind-floor-gram`, `seven-eighths-budget` | the one producer stops above `½` at every period |
| The centred Jensen equation has the full signed-permutation group or a rational relation among its moments; `K_even⊆ℝ` ⇔ RH | [L*] (`jensenGal_full_or_exists_moment_relation`; log §10); [KR] `zero-field-transitivity` | RH is the triviality of a group of sign families |
| Heat cover. RH ⇔ no positive real branch time ⇔ fibre conjugation is the identity at every positive real non-branch time. Conjugation is a forward monodromy. Transport is bijective, non-escaping, homotopy-invariant. Every forward monodromy moves finitely many zeros and commutes with `z↦−z`; the global reflection is not a monodromy; the turns generate the group. The orbits of `G₊(b)` are the classes of simple joins; a zero alone and simple in a moving region is followed across branch times | [L*] (`riemannHypothesis_iff_forall_pos_not_mem_branchTimes`, `riemannHypothesis_iff_fibreConj_eq_one`, `fibreConj_mem_forwardMonodromy`, `finite_setOf_forwardMonodromy_ne`, `fibreNeg_not_mem_forwardMonodromy`, `forwardMonodromy_eq_closure_turnLassos`, `transports_of_homotopy`, `simplyJoined_iff_exists_mem_forwardMonodromy`, `exists_simplyJoined_of_alone`; log §6, §10, §11, §16) | the sign of every zero is a monodromy of one cover; RH is the triviality of one element at each real time |
| Off-centre collisions exist at forward times of arbitrarily large real part; every forward base has a monodromy moving a zero outside its pair `{z,−z}`; pair preservation ⇔ every forward collision is central | [S] (`exists_forward_multipleZero_ne_zero`, `not_forwardMonodromy_preserves_pairs`: statements hypothesis-free, the cosine-model dependency has a call mismatch); [L*] (`forwardMonodromy_preserves_pairs_iff`; log §6, §11) | pair preservation of the whole group is a false target; only the real-time criterion remains |
| `Λ_dBN≤1/8` strictly; `Λ_dBN≥δ²/(200 log γ)` for an off-line zero of depth `δ` at height `γ≥e^{1600}`; `Λ_dBN≤s+D/2` when the zeros of `H_s` have `(Im z)²≤D`; for `t>0` `H_t` has finitely many non-real zeros; width zero ⇔ `Λ_dBN=0` | [L*] (`newmanConstant_lt_eighth`, `le_newmanConstant_of_offLine_zero_quadratic`, `newmanConstant_le_of_zeros_im_sq_le`, `riemannHeat_nonreal_zeros_finite`, `zetaZeroWidth_eq_zero_iff_newmanConstant_eq_zero`; log §12) | the heat constant is a two-sided quantitative reading of the width; with `[X]` `Λ_dBN≤9/128` [D5] |
| RH through `exp(exp(Ca))` gives the sign on `[−a,a]` for `a≥1`; the verified height is 67; no declaration transfers height 67 to an aperture `½log 3` | [L*] (`exists_doubleExp_windowPositive`, `windowPositiveAt_of_rhVerifiedThrough`, `rhVerifiedThrough_sixtySeven`; log §12) | each window is a finite-height statement; no finite procedure of the corpus reaches ratio three |
| Weil sign at aperture `a` confines zeros of height `≤2πe^a` to depth below an explicit cube-log bound | [L*] (`zeta_depth_lt_of_positive_aperture_closed_form`; log §16) | sign on a window is a depth bound on a height range |
| `(log x)^{−1}Σ_{n≤x}λ(n)λ(n+h)/n→0` for every `h≥1`; short-interval mean squares of `λ` and `λχ` | [L*] (`tendsto_logAvg_liouville_shift`; log §10); [F] (MC) | logarithmic two-point Chowla and Matomäki–Radziwiłł are native |
| Displaced twisted second moments for `θ<½`; a positive critical proportion at `θ=13/50`; simple-critical proportion `≥0.6725−ε` (imported `Zeta23` plus local input); cameras isolate exterior mass `≤¼` for zeros of depth `≥exp(−c log³(T/2π))` | [F] (MZF, census, ZCG; log §9) | the in-law half of the near-line picture is native |
| `N_d=4Q_d`; `sup N_d` is the off-line multiplicity; `N_d≤300√(d log d)` for `log d≥6.1·10⁶`; at each degree finitely many shifts fail real-rootedness | [F] (LA) | the Jensen census counts quartets |
| Every Artin Euler product is a product of integer powers of Hecke `L`-series of fixed fields of Brauer-elementary subgroups with finitely many Euler factors, on `Re s>1`; reciprocity for every linear character of an abelian extension; the Artin map is trivial on a ray and its kernel is the norm group; completed primitive Hecke `L`-functions are meromorphic with functional equation | [L*] (`exists_artinEulerProduct_eq_prod_zpow_heckeL`, `exists_artinEulerProduct_linearCharacter_eq_heckeL_mul`, `exists_rayPrincipal_le_ker_artinMap`, `exists_mulEquiv_quotient_normIdealGroup`, `meromorphic_heckeCompletedLFunction`; log §7, §12). Every ray class character is induced from the primitive character of its conductor; on `ℂ∖{1}` its `L`-function is that of the primitive character times the Euler factors at the modulus; Weil's form of a nontrivial ray class character has `n` negative squares on some family of `n` tests iff `L(s,ψ)` has `n` distinct zeros right of the line [L*] (`heckeLFunction_eq_primitiveHecke_mul`, `exists_le_negIndex_rayClassGram_iff`; log §18; frontier grade [S]); the Artin symbols of a linear character are the values of a primitive ray class character outside finitely many primes [L*] (`exists_primitive_heckeCharacter_artinSymbol`; log §20) | Artin `L`-functions are meromorphic quotients of Hecke `L`-functions natively; the index law holds for every ray class character, primitive or not |
| No Maass cusp form with `0<λ<3/16` on a congruence subgroup; none in `(0,¼)` for `N≤25`; a weight-`½` eigenfunction at `3/16` | [L*] (`selberg_status`; log §10) | `3/16` is sharp for every argument whose inputs hold in weight `½` |
| Zeros `≤1−2δ` ⇔ pulse decay `e^{−(δ−ε)τ}` for `0<δ≤¼`; pulse rate = horocycle rate | [L*] (`zeroFreeStrip_iff_pulse_ringdown`, `pulse_ringdown_iff_horocycle_rate`; log §10) | every ringdown rate is a zero-free strip; `[X]` is the rate `1/16` [D] |
| Cocompact Fuchsian quotients: resolvent identity, discrete spectrum, Mercer expansion and trace `Σν_j=∫_FK(z,z)` of `T_a−T_b`; the congruence groups `Γ(N)`, `N≥3`, of the order of `(2,3)_ℚ` are cocompact and act freely | [L*] (`resOp_comp`, `resOp_specVec_eq`, `hasSum_nu`; log §8, §11); [S] (`isCocompactFree_congGroup`; log §20) | the spectral side of a compact trace formula and an explicit compact surface are native; no geometric side and no Selberg zeta function |
| The Goss zeta function at `z∈ℤ_p∖ℕ` has nonzero roots of strictly decreasing norms | [L*] (`gossZeta_riemannHypothesis`; log §16) | one Riemann hypothesis is proved by dominance, with no sign |
| No heavy return of the prime orbit for `log t≤(log y)^{3/2−ε}`; under `Θ≤b` heavy returns are bounded on three rungs | [L*] (`eventually_no_heavy_return_before_vk`, `heavy_return_bound_of_halfPlane`; log §10, §12) | the dark range begins at the Vinogradov–Korobov height |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | exact on every window; a window at aperture `a≥1` follows from verification to `exp(exp(Ca))` [L*] |
| M2 Calibration | window cones, feasible sets, margins | RH ⇔ each aperture admits weights making the full form nonnegative; all-aperture weights pinned to `Λ` [F] |
| M3 Canonical flow | `L, r, Ψ` of the Weil chain | RH ⇔ `Ψ` bounded on the precontact portion of every finite interval [F] |
| M4 Reflection | Krein forms, ringdown, horocycles, cavity energies | sharp receivers; pulse rate = horocycle rate [L*]; exponents `1−Θ/2`, filtered `1−Θ∞/2` [F] |
| M5 Square-root cancellation | prime counts, long moments, squarefree counts | receivers closed; estimates open; logarithmic two-point Chowla proved [L*] |
| M6 Continuation | heat, cosine, Jensen | RH ⇔ no positive real branch time [L*]; `Λ_dBN<1/8`, quadratic detection rate [L*] |
| M7 Zero geometry | cameras, Blaschke factors | adaptive clusters pay their exterior mass [F]; prime cost at the selected centres open [F] |
| M8 Finite-layer receiver | filters, currents, non-attainment, tangent data | complete in world I, including additive twists [L*] |
| M9 Production | integer stencils, Stepanov | rates `K^{−a}` through `a↑½` give RH; compensated producer reaches `a<2σ/(3+2σ)`; Heilbronn sum `≤5p^{11/12}` [F] |
| M10 Count | `ℕ`-counts with quadratic Tate limit | receivers [F]; no count over ℤ |
| M11 Orbit at finite time | prime phases, returns, resonators | no heavy return before the Vinogradov–Korobov height [L*]; under `Θ≤b` three rungs [L*] |
| M12 Critical compactness | thresholds, pole channel, the critical half-line state | the state is unique, outer, cyclic, stable, exponentially bounded [S]; sublevels compact [L*]; its charge and its existence undecided |
| M13 Topology of the prime complex | orientation cover | half-power ceiling [KR] |
| M14 Infinite-rank elimination | towers, thick sets | attained top + thick `O(√X)` deviation ⇔ RH [F] |
| M15 Prime-degree sampling | logarithmic windows, two-prime lags | complete receiver [F] |
| M16 Intersection on half-products | adelic carrier, Green kernels | critical adelic inverse unbounded [KR] |
| M17 Absolute geometry | couplings, self-pairings, combs | couplings `−N` are not mixed areas; index `≤1` forces logarithmic self-pairings; the dyadic completion attains the rate [L*] |
| M18 FE rigidity | Hamburger, defects | decaying defect forces the rational primes among unit multiplicities; slow defects among positive weights [L*] |
| M19 Exceptional-coordinate atoms | ZAL, B13, Landing | RH = ZAL ∧ B13 ∧ Landing [F]; all open for ζ |
| M20 Families and monodromy | covers, class characters, Artin | Artin Euler products are Hecke products natively [L*] |
| M21 Index and limits | index law, unit gaps | index-one approximants give RH; no approximant with a gap [F] |
| M22 Separation and dominance | ordinate injectivity, ultrametric Newton polygons | receiver for ξ [F]; proof for the Goss zeta function [L*] |
| M23 Hodge lattice at finite scale | step packets, neutral part, block matrices | RH ⇔ the Hodge inequality on positive packets without common blocks; certified on ratio `≤103/50`, first blocks, thin packets [L*] |
| M24 Constituents | bounded and Wiener classes | a zero-bearing construction of ξ leaves these classes [F] |
| M25 The ladder | mass, aperture, rung | sign changes across `2δκ=1` at aperture `κ log log q` [KR] |
| M26 Family continuation | two estimates, reciprocal kernels, reciprocity | `Re s>7/8` [X]/[S]; coupled tower to `3/5`; barrier of every `6r`-periodic pairing [L*] |
| M27 Dressed positivity | lag aggregate at a level | level one ⇔ RH [F]; constant-vector signs on infinitely many dyadic prime shells give AAL [L*] |
| M28 Floor-free receivers | homogeneous, unit gap, certificate, amplification | each kind has a receiver and a kill [F] |
| M29 Models of the count and of the Euler product | deletions, two-sided edits, signed and positive weights | fakes at every count exponent above the pair, and below `½` under `Θ+2β<2` [L*] |
| M30 Index in the aperture | Morse = Maslov index | index = number of crossings [L*] |
| M31 Coherence of reciprocity families | modes, columns, root numbers, signed Gram | row root number `G(c)γ₂(c)²`; averaging rows kills the target mode [KR] |
| M32 Galois theory of zeros | zero field, Jensen equations, orderings | `K_even⊆ℝ` ⇔ RH; Jensen group full or moments dependent [L*] |
| M33 Bound states and gluing | potentials, couplings, susceptibilities, low-rank models | every fixed-rank model fails beyond block size one [L*]/[KR] |
| M34 Selective binding | the contacts of 2 and 3 | weakened or twisted contacts create a second bound state [KR]; packet and dilate bound at ratio three [L*]; middle-supported and unequal-child directions open (B192) |
| M35 Monodromy of the heat cover | branch times, transport, forward monodromy | group structure determined: finite support, generated by turns, orbits = simple-join classes [L*]; pair preservation false [S]; the real-time element is RH |
| M36 Mixing of the Doob chain | gap, binding, margin, exponent | RH ⇔ gap `≥` binding `−C` ⇔ bounded margin [L*]; exponent `θ<½` ⇒ strip [L*]; contacts alone have zero gap and zero curvature [L*] |
| M37 Screening through the dyadic middle | conditional energies, conditional coupling | exact law; RH ⇔ contraction [L*]; conditional energies `⪰1/5000` at the first step [D10]; the coupling bound open (B194) |
| Amplifiers | Diophantine repulsion, integrality, Turán, positive annihilators | amplify or reshape a certificate, produce none [KR] |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACS (atomic), SC, RW. Programmes: AHD/CausalReflection, AID, HTGeometry/HardyBoundary, CSTW.

Established:
- `0<R_PD=R_PSD=R_polar=R_halfline≤W=R_prim=R_high=inf_A windowThreshold(A)`, each infinite iff RH; ¬RH gives a finite-`W` half-line ground state [F] (log §9).
- At every `R>0` an attained unit minimizer, unique up to sign, with Laplace transform zero-free on `Re z>0`; `λ(1/t)` strictly concave; at finite `W`: outer, cyclic, transverse coercivity, weighted and polar stability, `λ′(W)=−a(W)∫F²e^{−8u}/W` [F] (log §11).
- Strong confinement `λ−a−log a→μ`, `aδ_R→1`, `a∫(−u)F_R²→1/8` [L*] (`universal_softLogarithmic_confinement_limit`; log §10). Coercivity `Q≥L₊+4M−16`; compact trial sublevels, strongly convergent minimizing sequences and a compact family of rescaled minimizers [L*] (log §8, §11, §20). The closed `L²` domain of the limiting form contains the trial profiles with the same energy [L*] (`SoftLogarithmicHalfLineDomain.closedEnergy_eq`; log §20).
- Exponential bounds of every minimizer including a finite-`W` state; trace-free collar bound [S] (log §8).
- Polar payment holds on every window for a band `0<R≤R₀` [L*] (`exists_polarPaymentAt_on_every_window`; log §12); the full tilted-spline matrix is positive definite for every exponent below `1/8` [F].

| | Obstacle | Strength |
|---|---|---|
| A9, A13 | constants of the eighth-root horizon; near-gcd charges (unverified) | — |
| A158 | Lean attainment of the limiting infimum on the closed domain (paper proof written; closed domain, weighted Fatou and moment-continuity tools present): lower semicontinuity of the signed energy, cutoff recovery, sign rigidity, uniqueness and convergence of the profile (unverified) | — |
| A161 | verification and integration of the barrier, collar and Gamma-cutoff modules [S] | — |
| B6, B101 | full-space sign at every critical multiple; polar payment at every ratio | RH |
| B104 | exclusion of a finite-`W` ground state, charged (`R_polar<W`) or polar-orthogonal (`R_polar=W`); first step: identify the localized critical state with the bounded Green solution (forcing/domain bridge, first-order cross terms, collar-energy transfer) | RH (method at the first step) |
| B123 | correlated arithmetic pairings dominating the depleted kernel | method |

### S2. Window tower, canonical flow, aperture path
Routes: RW, EWU, OWU, ACT, CHMD, TT (odd), SZ, RN, LI, HF, ACS, SRT. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, CHT, AIF, VHR, SA, AGZ.

Established:
- RH ⇔ each positive aperture admits weights making the full ζ form nonnegative; all-aperture weights are pinned to `Λ` [F] (RW).
- Index law in the aperture [L*] (log §16).
- Verification: RH through `exp(exp(Ca))` ⇒ the sign on `[−a,a]`, `a≥1`; explicit `windowHeight` [L*] (log §12).
- Floor `1/5000` at aperture `181/500` by a finite certificate; floors `1/(20000·2^k)` through the dilation tower `a_k`, frozen below `0.3621<½log 3` [L*] (log §19, §21); [KR] `frozen-weil-floor-tower`. Exact `{2,3}` band below `log 2` [F] (RW).
- For any precontact base RH ⇔ `Ψ` bounded on the precontact portion of every finite interval ⇔ `L` bounded there; restoring bound; actual atom kicks [F] (RW).
- Sign at aperture `a` confines depth on heights `≤2πe^a` [L*] (log §16).
- Prime entry: for `2c<log 5` only `{2,3,4}` enter [F] (ACT).
- First-contact weights: at `a=181/500` every `w(2)` within `√2/10000` of `log 2` is feasible; the endpoints of the feasible set are undetermined [KR] `first-contact-weights`.

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6 | certified verification past 67, numeric heights, first-window membership, cone widths | — |
| A142 | an explicit constant in the verification rate; a transfer stated for apertures below one | — |
| A140 | fixed-aperture certificates of the kind proved at `181/500` at larger apertures: above `½log 3` (the index at ratio three at every block size [D18]), above `log 2` (ratio four), up to `½log 5` (unverified: the size of a certificate at the floors of these apertures) | — |
| A117 | end points of the feasible interval of `w(2)` on the first selective window | — |
| B1, B2, B4, B5 | sign on every window; bounded `Ψ` to contact; outer predictors; kick admission | RH |
| B3, B16, B17 | variation of `r` free of `1/μ`; decay law of the margin; signed ground states past `log ρ` | sub / method |

### S3. Prime-degree sampling and scale locality
Routes: ACS, SRT, WL, HF, ZCG, PM (count door), HAT-C. Programmes: SOSZ, CDGeo, FFA.

Established: the minimal face and its two-prime form; countermodels at every radius `o(log T)`; one exponent for all even trace moments [F] (SRT; log §9).

| | Obstacle | Strength |
|---|---|---|
| A58 | effective gap iteration (unverified) | — |
| B130 | the bound on any decisive sample; `Kp^σ`, `σ<½`, is a zero-free strip | RH (≥qRH at `p^σ`) |
| B144 | separation of the deep off-line ordinates | sub |

### S4. Continuation, index, constituents, the heat cover
Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD, TH. Candidate: W1C. Programmes: NGF, FFP, ADO, IRP, CTZ, GaloisTheoryOfZeros, RHTower/Heat.

Established:
- The two real-time criteria and the structure of `G₊` (§0) [L*].
- `Λ_dBN<1/8`; quadratic detection; restart law `Λ_dBN≤s+D/2`; finiteness of non-real zeros at positive times (§0) [L*]. The same finiteness follows from membership of conjugation in `G₊` and finite support [D6].
- At the time of ζ: real branch times accumulate at `0` unless zeros escape [F] (ZCG sources).
- Jensen: `N_d=4Q_d`, bulk reality, finitely many exceptional shifts; nonnegative discriminants [F] (LA).
- Positive-time collision exclusion ⇔ RH; times `≥1/8` closed; uniformly bounded `N(t)` ⇔ finite off-line support [KR] `kr-cal`.
- A zero-bearing construction of ξ leaves bounded and Wiener classes [F] (CTZ).

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | heat horizon with an explicit height; Jensen rung past `d⁴≪T log T` (unverified) | — |
| A160 | repair of the saddle-error call (`leftErr R a`) in the cosine-model dependency of the off-centre collision theorem [S] | — |
| B22–B25 | outer Jensen roots; `N_d` bounded (⇔ finite off-line support); collisions at small positive time; frequency below one | RH / ≥qRH |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH |
| B146 | an independent family of bounded index converging to ξ | RH (producer) |
| B27, B47 | longer runs of simple critical zeros than five; multiplicity by a non-size input | sub |
| B190 | the orbit of a zero with irrational real part under the embeddings fixing the prime trace field | method |
| B197 | transitivity of `G₊` (path-connectedness of the simple part of the heat cover); no RH yield by itself | method |

### S5. Near-line geometry, long moments, census, cameras
Routes: WD, CTF, MC, TG. Programmes: CDG, APR, MZF, AIF, MatomakiRadziwill, LogarithmicChowla.

Established: RH ⇔ the fixed-window `ζM_N` second moment is subpolynomial in `N`; a cofinal bound `O_θ(T^K)` with fixed `K` and unbounded `θ` suffices; sparse subpolynomial compact parity energy gives `K=3` [F] (WD); `zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope`, `eventual_depth_bound_of_dyadic_moebius_moment` [L*] (log §12); positive critical proportion at `θ=13/50` [F]; subcritical mollifiers have corridor defect `≥cV` and normalized moment `≥1+1/(8+6θ)` [KR] `subcritical-disc-corridor`, `kr-llm`; logarithmic two-point Chowla [L*].

| | Obstacle | Strength |
|---|---|---|
| A18 | twisted moments past the square root [C] | — |
| B57 | depth density `o(T)` | sub |
| B58–B61 | `D_win`; pointwise prime cost of the adaptive profile at its selected centres; Green moments at deep zeros; a detector past the last scale | sub |
| B62, B66 | cofinal long moment with `θ`-independent exponent; near-unit holomorphic budgets | RH |
| B150 | a form factor bounded by `4` on `(1,10/9)` | sub |

### S6. Production, precision, the Mertens level
Routes: WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP. Programmes: APR, AAD, RAC, MMD, HWV, RIAC, ALST.

Established: finite families of convergent linear laws cannot imply the count; pole matching and Möbius gauge do not give half power [KR] `mertens-not-count`, `pole-matching-half-power`, `mobius-gauge-genericity`; producer rates through `a↑½` give RH [F]; logarithmic correlations of `λ` vanish at every fixed shift [L*]; Schur ceiling `(log N+C)Σ|c|²` for the von Mangoldt correspondence form [L*] (`exists_vonMangoldt_toeplitz_le`; log §12).

| | Obstacle | Strength |
|---|---|---|
| A30, A33, A46 | best stencil exponent under RH; cubic residue coefficients; singular indices (unverified) | — |
| B48–B54 | the deciding input at square-root precision and its classical faces | RH |
| B55, B67 | polynomial stencil rate; parity at power saving | ≥qRH to RH |
| B15 | pointwise savings past Vinogradov–Korobov in the Lean graph | sub |
| B56 | `Θ<1⇒Θ=½`; with `[X]` it is RH | RH |
| B106 | a correspondence on the orientation cover with bounded local indices | RH |

### S7. Reflection, carriers, the modular horizon
Routes: PM, HAT-C. Candidate: W1C. Programmes: RIT, BHR, ASH, AHMH, CTH, IRP, HAT, STCC, CompactHyperbolicSurfaces.

Established: ringdown ⇔ strip and pulse rate = horocycle rate [L*]; universal horocycle exponent `1−Θ/2`, Euler-filtered `1−Θ∞/2`; filtered rates approaching `3/4` ⇔ ZAL, no acceleration ⇔ AAL [F] (PM); mixed cuspidal/Hecke sources see every right resonance, a single eigenform can miss halving pairs [F]; `selberg_status` [L*]; Mayer resonances and the three-term equation [L*] (`three_term_absolute`, `mayerResonanceMultiplicity_pos_iff`; log §12); spectral side of the compact quotient [L*] (log §8, §11); scattering spectrum alone supplies no estimate [KR] `kr-sel`.

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| A54 | cusp expansion for Bianchi resolvents (unverified) | — |
| A120 | geometric side of the trace formula and the Selberg zeta function of a compact surface with a small eigenvalue [C]; spectral side present; the compact quotients `Γ(N)\ℍ`, `N≥3`, of the order of `(2,3)_ℚ` present [S] | — |
| A148 | the layers `m=0,1` of the theta-square series and the target component of a twisted column [C] | — |
| B68, B71 | independent reflection Krein positivity; universal decay and the horizon rates | RH |
| B87 | a count with Tate limit `Q`, defined without `Q` | RH |
| B147 | Shimura nonvanishing for one eigenform | indep. |
| B114, B117, B171 | partner involution; a regulator with a gap before the limit; a form of signature `(1,∞)` | producer |
| B178, B188 | a relaxation rate beyond the tempered exponent; a mechanism for the scattering resonances whose inputs fail in weight `½` | producer |

### S8. The exceptional coordinate: two worlds and three atoms
Routes: BAG, ZCG, JAS (shell), SC (undamped), WL (thick runs), ACS (sampling), LA (finite support). Programmes: ZCG AbscissaLaws, ELT, EFT, IWT, IRW, APD, TAPO, FFA, WZC.

Established:
- `Θ≤7/8` [X]; the scope guards [F] (log §9).
- World I receivers: under `Θ∞<Θ` tangent data of `μ` and `λ` and their Ramanujan twists [L*] (`tangentDatum_ramanujanTwist`, `ramanujanNumerator_div_eq`; log §8).
- Models: two-sided edits, the signed grouped edit below `½`, the order law at every multiple (§0) [L*]/[KR].
- FE axis: §0 [L*]. Tempered symmetric models, FE with fixed-height data, order-`≤1` Γ-completed products do not force AAL [KR] `fe-finite-exceptional-layers`, `aal-trace-nonattainment`, `beurling-isolated-zeros`.
- Positive tempered configurations with zeros of depth `δ` at unbounded heights and count `N_ζ(T)+O(T)` exist for every aperture [KR] `kr-crt`.

| | Obstacle | Strength |
|---|---|---|
| A120 | a finite nonempty stratum with both structures (Selberg zeta functions) as calibration model [C] | — |
| B13, B138, B141 | finite stratum; landing; Deuring–Heilbronn for ζ | sub |
| B83, B170 | AAL; non-attainment for ζ | sub / AAL |
| B89, B112, B128 | bounded aligned return; FE into vertical transport; replication by another mechanism | sub |
| B145 | the restricted prime-weighted cofactor sum at a growing isolated mode | AAL [D] |
| B110, B126, B127 | thick crude count; sampling set; lag recurrence | AAL |
| B157 | which structure of ζ that a Selberg-type zeta function lacks excludes a finite stratum | method |
| B191 | a unit-multiplicity fake with subpolynomial defect energy at `β₀≥3/2−Θ`; whether a bounded defect forces the rational primes among unit multiplicities | method |
| — | ZAL | ≥qRH |

### S9. Prime orbit at finite time
Routes: BAG, TH, SRT. Candidate: S3. Programmes: PTT, TAPO, TTPO, CDGeo, ALST.

Established: no heavy return for `log t≤(log y)^{3/2−ε}` [L*]; under `Θ≤b` three rungs [L*]; under `Θ<1` the return transfer ⇔ RH [F]; fewer than `T^c` separated self-returns of some zero disc for `c>(30/13)(1−σ)` [F] (BAG). The exponent question at the matrices and the heavy-return bound at polylogarithmic prime length are one estimate [D7].

| | Obstacle | Strength |
|---|---|---|
| A24 | certified scans (unverified) | — |
| B46, B97, B137, B121 | proportional saving at length `(log X)^{2K}`; first return past VK; collective depth floor; freezing control | sub |
| B148 | the transfer of S3 | RH (the strip is [X]) |

### S10. The diagonal, counts, realization
Routes: ACS, HF, HAT-C, PM (count), LI. Programmes: SOSZ, HAT, AGZ, HFP, RIAC, CTH, LST, ALG, RHTower/Artin, HeckeLFunctions.

Established:
- Forced data: scaled comb Bézout ⇔ `ε=0`, RH and `c≥sup P_δ`; all-packet comb positivity ⇔ RH and `w=Λ` [KR] `bezout-shift`, `first-contact-weights`.
- Realization: the self-pairing laws (§0) [L*]; trickle-down from hyperbolic nonnegative links [L*] (`weightedTrickleDown_of_links`; log §12); `P_N−(log N−γ−η)1` has exactly one positive direction on every full finite-sieve partition for `0<η<2log 2` [KR] `uniform-margin`.
- Artin (§0) [L*].
- The Robin diagonal of HAT is identified and is not Weil's degree diagonal [F].

| | Obstacle | Strength |
|---|---|---|
| A28, A41, A48 | reciprocal-quadric traces; count law for plane quartics [C]; Hasse–Weil tests (unverified) | — |
| A141 | the half-plane `[X]` for fields containing `ζ₃` and every ray class character (unverified); the Artin transfer of the index needs virtual zero and pole configurations with orders and the matching of local conductors with ramification [F] | — |
| B87, B88 | a count on the rays defined without `Q`; the sign of the comb finite part | RH |
| B149, B169 | Bézout from a property of the object; a doubling with a canonical height | RH (producer) |
| B196 | a realization of the couplings `−N(a,b)` as intersection numbers with self-pairings of size `−log m` per block, on which an index theorem holds | producer |

### S11. Families, rigidity, exactness
Routes: ACS (tensor), ECP, HF, SC, BAG. Programmes: AWT, ALST, SignFreePurityMechanisms, EFT.

Established: glued index `=κ_ζ+1`; sublinear tensor loss ⇒ RH [F] (SC); FE rigidity (§0); the Goss Riemann hypothesis [L*].

| | Obstacle | Strength |
|---|---|---|
| B86 | positivity of the endpoint character at unbounded rank | RH |
| B80 | FE twins with off-line zeros in the full class | sub |

### S12. The scale, the level, the signal, the probe
Routes: RW, HF, ACS, SRT (rungs); JAS, MC, WL, S3 (legs). Programmes: SA, FCT, MMD, CRF, STCC.

Established:
- Ladder: `cancellation_and_depth_ladder`, `zeta_companion_of_rung` (`2δκ>1`), `heavy_return_bound_of_halfPlane` [L*] (log §10).
- Frame: `zetaZeroAbscissa_le_of_two_estimates` (conditional transfer) [L*]; coupled tower, pairing barrier, phase endpoints, binding bin (§0) [L*].
- Signal: `Θ≤b` ⇔ the reciprocal-ζ signal is `O(Z^{b′})` for every `b′>b`; an `O(Z^b)` bound gives large-prime dressed PSD at level `b+½+ε` [F] (JAS).
- Coherence kills [KR] (log §4).
- The half-plane in source [X]/[S] (log §8).

| | Obstacle | Strength |
|---|---|---|
| A118 | validation of the producer and dependency chain of the hypothesis-free `7/8` assembly [S] | — |
| A138 | corollaries of `Θ≤7/8` on the receivers as Lean statements: rung, return bound, ringdown rate `1/16`, comb growth `3/8`, `Λ_dBN≤9/128`, two-end rate `e^{3v/8}` [D5] | — |
| B198 | converse exponent law on all packets: does width `≤θ` give a step-packet floor `≥−C_εK^{θ+ε}` uniformly in the block size? It holds on the odd two-end states [L*] (`zetaZeroWidth_le_iff_twoEndOdd_rate`); a sum over the zeros loses the logarithm of the block size [A] | method |
| A149 | the function-field calibration of the floor bin over `𝔽_q[T]`, `q≡1 mod 6` (unverified) | — |
| B174 | the row count of the binding bin | a half-plane in `[13/15,7/8)` |
| B185 | the long columns: a power saving in the first moment of the root numbers against a dual column, uniformly in the column | a half-plane in `(2/3,13/15)` |
| B187 | a Möbius-signed pairing outside the `6r`-periodic Gauss pairings whose coupled fixed point is below `3/5` | producer |
| B180 | the reflection of the completed theta row without Eisenstein series | method |
| B160, B161 | level-one dressed PSD; a signal bound below `7/8` | RH; a half-plane below `7/8` |
| B159 | a rung `κ≥4/3` with a saving that fails for the Liouville twist | a half-plane below `7/8` |
| B156 | arithmetic cluster exclusion on a rung | method |

### S13. Floor-free receivers and their kills
Routes: every route (as a filter). Programmes: FFA, WZC.

Established: window floors, non-attainment and moment receivers; AAL branches need ZAL [F] (log §9); an index-one realization is a unit gap [F] (W1C).

| | Obstacle | Strength |
|---|---|---|
| B170 | non-attainment for ζ | AAL |
| B171 | a form of signature `(1,∞)` from the places in which the right zeros are a symmetric spectrum | RH (producer) |
| B172 | a functional decreasing under projection that is not a function of finitely many linear statistics | producer |
| B173 | a two-sided subexponential bound of the trace on late windows of one length | AAL |

### S14. Window matrices: binding, mixing, margin, overlap
Routes: ACS, HF, RW, EWU, OWU. Programmes: AGZ, MixingArithmeticOfTheFloorTrees, HFP, ALG.

Established: §0 rows on the Hodge inequality, the certified range, the overlap law, the Doob chain, margin, exponent, two-end family, long-ratio binding, gluing kills, contacts, floor trees, self-pairings [L*]. Unconditional two-sided control of the binding energy: `A(0)−2Σ_{k≤Q}Λ(k)/√k≤λ` and `−λΣφ²+packetForm≤poleCapacity·Σφ²` [L*] (`le_eigenvalue_of_contacts`, `binding_add_packetForm_le`; log §5). A contact is selective: with `(b−a)/2≤log k` it is `≥0` on packets with a node at the centre and `≤0` on packets of one sign [L*] (`shallow_contact_selective`; log §5).

| | Obstacle | Strength |
|---|---|---|
| A162 | Lean statements of the second-eigenvalue floor `1/5000` at ratio `≤103/50`, the conditional-energy floor at the first overlap step, the `N`-orthogonal and Green forms of the overlap criterion, and the additive loss law below the binding energy of the middle [D4], [D10], [D11], [D21], [D22] | — |
| A163 | the converse exponent law with a logarithm of the block size: width `≤θ` ⇒ step-packet floor `≥−CK^θ log K·log(KR+2)`; with `[X]` the exponent `3/8` on the initial windows [A2] (unverified) | — |
| B198 | converse exponent law on all packets (S12) | method |
| B152 | one bound state at every ratio and block size | RH |
| B192 | the selective sign at ratio three and four: one bound state of `(R,3R]` and `(R,4R]` at every block size by a proof from the contacts; proved on packets and their dyadic dilates; middle-supported and unequal-child directions open. The conclusion at each ratio also follows from a fixed-aperture certificate (A140) | sub (a finite certificate at each ratio); method |
| B194 | the contraction of the conditional coupling at the first overlap steps: `‖E₁^{−1/2}XE₂^{−1/2}‖≤1` for `a≤3R/100`, `b≤3(R+a)/50` (ratio `2.12`), then at ratios `2.25, 2.53, 3.21`, by a bound for the Green matrix of the prime-free dyadic middle between its slivers [D20], [D21]; the certified floors alone do not give it [D25]; the conclusion at each of these ratios also follows from a fixed-aperture certificate (A140) | sub; method |
| B195 | an exponent `θ<½` for the step-packet floor or the neutral margin from arithmetic; a gluing estimate whose loss per overlap step is weaker than squaring gives every `θ>0` [D3] | ≥qRH; RH at subsquaring loss |
| B16 | the limit and decay law of the margin at finite block size | sub / method |

## 3. Live routes

Receiver statements follow the frontier map at the checkpoint unless marked `[L*]`.

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, or positive semidefiniteness of every finite Gram matrix of the prime lag, or an attained top with an `O(√X)` deviation on a thick set → RH.
- **Established:** endpoint energy bounded ⇔ RH ⇔ first-band growth `O_ε(N^{1+ε})`; gauge exponents span `[Θ,1]`; RH ⇔ attained top ∧ thick `O(√X)` deviation, no ZAL premise; RH ⇔ every finite Gram matrix of `primeLag` is PSD, with `primeLag(u)=e^{−|u|/2}·primeDeviation(e^{|u|})` off zero [F].
- **(a)** A30. **(b)** B49 (endpoint energy), B48 (deciding input), B110 (attained top with the thick estimate), B1. Neither top attainment nor the square-root estimate follows from the lag identity [F].

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every aperture → RH; equivalently feasible weights at every aperture; equivalently `Ψ` bounded on the precontact portion of every finite interval.
- **Established:** S2; RH ⇔ relative compactness of every Weil orbit correlation ⇔ moving-bubble energies have convergent subsequences with nonnegative limits [F].
- **(a)** A1–A3, A117, A140, A142.
- **(b)** B1, B2, B4; B104 for the polar channel. Bounds strictly before contact do not suffice: Green and variation constants retain the inverse ground energy; Bohr compactness is an RH-equivalent target, not a source bound [F].

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH. **Established:** for fixed `m≥1` either one-sided bound on `A(j^m)/j^m` ⇔ RH; one controlled sample per backward window of length `N^{1−δ}` suffices; bounded-size prime blocks are paid at fixed horizon [F].
- **(a)** none. **(b)** complete-history bounds across advancing clocks (B42); fixed-horizon payment does not control cross-clock debt [F].

### CFC — First-clock lower bound
- **Path:** first-clock sine coefficient bounded below on an aperture tail → RH. **Established:** exact tail criterion; ¬RH forces unboundedness below on every tail [F].
- **(a)** none. **(b)** the lower bound with prime, archimedean and endpoint terms (B42).

### RP — History floor
- **Path:** eventual linear defect floor of the matched−quantile prime history → RH. **Established:** linear-floor criterion; low-LCM and copied-diagonal payment; a sublinear floor is impossible [F].
- **(a)** none. **(b)** high-LCM pairs, moving core, singular-domain terms in one floor (B42).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−archimedean trace sign or subexponential mismatch → RH. **Established:** calibrated Hausdorff-row sign for `r≥min(C₀(k+1)²,S(k))` with explicit cutoffs; exterior scalar-diagonal criterion with discharged radius `218/25` [F].
- **(a)** A1. **(b)** signs below the explicit shift uniformly in unbounded `k`; these entries ⇔ RH (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius/Liouville cancellation → RH.
- **Established:** damped critical energy, fixed-height subpolynomial prefixes, eventual mollifier zero-freeness each characterize RH; ¬AAL gives some Mertens power saving [F]; logarithmic two-point Chowla, short-window cancellation of `λ` and `λχ` [L*] (log §10); the coupled tower and its barrier [L*].
- **(a)** A33, A46, A118.
- **(b)** B48, B50, B15, B106; B161; B174, B185, B187. Logarithmic correlation decay supplies no half-power rate; the bootstrap of the probe cannot pass `3/5` [F]/[KR].

### SQF — Weighted squarefree count
- **Path:** a one-sided `O_ε(t^{−¼−ε})` bound of `Σμ(n)²e^{−nt}−6/(π²t)` → RH. **Established:** either one-sided law ⇔ RH; `Ω_±(t^{−1/4})`; the `k`-free ladder detects the strip `Re s>1−1/k` [F].
- **(a)** none. **(b)** the quarter-power bound for one sign (B48 family).

### TT — Theta tail / Wold
- **Path:** bounded weighted endpoint energy at each `0<t<½` → RH. **Established:** RH ⇔ a bound `C_t` for every `t`; Wold residual `O(exp(−c·vkScale(N)))`; uniform bound on a shrinking band [F].
- **(a)** none. **(b)** `C_t` at every fixed `t` (B34); the shrinking band does not reach a fixed positive `t`; `t=½` fails [F].

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted at infinitely many degrees, or sublinear upper root height → RH.
- **Established:** the Jensen census (§0, S4) [F]; excluding nonempty finite exceptional shifts at every degree suffices [F]; Jensen group full or moments dependent [L*].
- **(a)** A20, A1. **(b)** B22; B23 then B13, B138; B124; B190. Bounded nonreal multiplicity gives only finite off-line support; bulk reality and quartet parity are blind [KR] `jensen-bulk-reality`, `jensen-quartet-parity`.

### ZCG — Zero-configuration geometry / heat descent
- **Path:** exclusion of positive-real-time heat collisions → RH; or ZAL with finite-slope linear AAL → RH.
- **Established:** S4, S8; cameras [F].
- **(a)** A19, A120, A160.
- **(b)** B24, B25, B47, B27, B124; B130; B145, B170; B13, B138, B141; B59; B191; B197. Whole-group pair preservation is false; complex-time collisions do not settle the real-time criterion; forward control is not uniform as `τ→0` and gives no finiteness of off-line ζ zeros; Euler/count models and subpower mean-square FE defects cannot select ζ [F]/[KR].

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH. **Established:** exact integer trace; enclosed multiplicity `≤` trace norm; endpoint and Gaussian central-gap receivers [F].
- **(a)** none. **(b)** trace norm below one on every formation rectangle (B38); a scalar prime budget below one is not a trace-norm bound [F].

### HF — Hodge / critical half-line state
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** S1, S14.
- **(a)** A9, A13, A141, A158, A161.
- **(b)** B6, B101, B104, B123, B8, B41, B10, B87, B88, B149, B152, B192, B194. Stability and nonzero polar pairing do not exclude the charged case; exponential decay supplies neither the wall trace nor its flux law; `L²` cyclicity is not energy-norm density; `R→0` asymptotics do not settle the sign at `R→∞`; universal holomorphic multiplier domination fails [F]/[KR].

### HAT-C — Arithmetic-clock Green energy
- **Path:** one clock, or one fixed scattering height → energy floor → `W≥0` on packets ⇔ RH.
- **Established:** `E_r↑W` with error `≤(1−r²)‖f′‖²/2`; `E_r≤W` at every cutoff; an aperture-independent floor `−C‖f‖²` at one cutoff per large aperture implies RH; at any fixed height the corrected energy plus the nonnegative jump tail equals `W` [F].
- **(a)** none. **(b)** the corrected-energy floor at one fixed height on all apertures (B1); the sign of the tail alone does not bound the energy; negative Weil directions remain negative at every cutoff [F].

### CHMD — Causal hyperbolic–modular duality
- **Path:** bounded prime wave, or the odd Doob half-threshold bound → RH. **Established:** wave and Doob receivers; normalized decay `O(exp(−√log Y/92160000))`; the nonfirst source retains any fraction `1−ε` of Gamma energy [F].
- **(a)** none. **(b)** either side of the unnormalized wave bound; the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel positivity → RH.
- **Established:** ranks `≤14` positive definite for `0<a≤½`; rank `N` from verified height `41+6(N+2)log(N+2)`; first-atom floor; adaptive head `M(b)=⌈|b|/2+B⌉` pays the omitted pair sum; the critical Dirichlet sum of half the height approximates `ζ(½+ib)` [F].
- **(a)** A4, A5, A24, A42. **(b)** B102, B20, B21: the signed adaptive-head payment at every aperture and degree; no summable frequency-uniform absolute pair majorant [F]/[KR].

### RN — Theta renewal
- **Path:** exclusion of joint nodes, or the theta-ground energy comparison → RH. **Established:** two-ended formula recovers Ξ with multiplicities; full-divisor zeros are the joint nodes; complete Weil sign ⇔ Gamma/polar jump energy `≤` prime jump energy [F].
- **(a)** none. **(b)** B36. The renewal spectrum is nonreal and the loop Pick index is infinite in both signs [KR].

### WD — Ward / collision / long moments
- **Path:** cofinal long-mollifier moments, or collision bounds → RH.
- **Established:** S5.
- **(a)** A18. **(b)** B62, B57–B61, B63. WD needs unbounded `θ` with a `θ`-independent exponent; the proved moment sits at `θ=13/50`; coefficient bounds, short weights and almost-everywhere corridor control leave finite and shallow exceptions [F]/[KR].

### LI — Paired Li / prime–Gamma balances
- **Path:** primitive bounded below, or `R(t)≥−C_εe^{εt}`, or the Cayley–Li sign → RH.
- **Established:** guarded history-zero set finite, RH iff empty; Li signs `n≤314` from height 67; paired Li coefficients are limits of damped comb tails; undamped Laguerre tails `combW(P_n)/N→2λ_n` [F].
- **(a)** A1. **(b)** B43: a sign uniform in `n`. Finite `Z_S` is not finite off-line support [F].

### SZ — Suzuki screw
- **Path:** completed Abel residual bounded, or the rectangular Ward lower bound → RH. **Established:** completed Abel source bounded ⇔ RH; `|A_N|≤C√N·exp(−c·vkScale(N))`; aligned ratio `≤C exp(−c·vkScale(N))` [F].
- **(a)** none. **(b)** B37, B1. The Vinogradov–Korobov saving leaves the `√N` scale [F].

### PM — Physical model
- **Path:** scattering source → reflection Krein sign, ringdown rate, horocycle rate, Farey error or a count → RH.
- **Established:** S7.
- **(a)** A26, A54, A120, A148. **(b)** B68, B71, B87; B147; B114, B117, B171; B178, B188. Visibility is proved, decay is not; polynomial filtering may erase finite exceptions: ZAL needs AAL [F].

### PTR — Cosine source
- **Path:** collision-free descent of `A_h` in `h` → RH.
- **Established:** strict Laguerre sign for `h≥½` and near the Vinogradov–Korobov boundary; the sign at every `0<h<½` ⇔ RH; ZAL gives finite nonreal defects at every positive shift [F].
- **(a)** none. **(b)** B29, B69.

### JAS — Joint ancestry
- **Path:** level-one dressed positivity on large primes; or subpower moving-window control; or signal cancellation at every `b>½` → RH.
- **Established:** moving Riesz-window subpower bounds ⇔ RH; level-one dressed PSD on all sufficiently large primes ⇔ RH; `Θ≤b` ⇔ signal `O(Z^{b′})`; under `Θ∞<Θ` top-residue asymptotics and their Ramanujan twists [F]; constant-vector signs on infinitely many dyadic prime shells ⇒ AAL [L*] (log §12).
- **(a)** A118, A138. **(b)** B160, B161 (through B174, B185), B51. A `7/8` signal bound gives a strip, not level-one positivity; the shell-sign alternative needs ZAL [F].

### CTF — Chronological tail / Báez–Duarte
- **Path:** unit-bounded rows, BSY sign, cut-kernel mass annihilation, mollifier infimum one, or a uniform positive-proportion condition for `ζM_N−1` → RH. **Established:** the criteria; exact holomorphic-mollifier infimum `exp(2I(1))`; sharp `μ` defect `D_y≥c_ρy^{2Re ρ−1}` [F].
- **(a)** none. **(b)** B52, B66, B91. Full sharp-sequence decay fails; good-height restriction retains the zero-forced exponent [KR].

### HCF — Heat trace
- **Path:** two prime-log heat grids nonnegative at every degree → RH. **Established:** two-grid criterion at fixed offsets; every off-line zero gives a pole-annihilating negative test on `log 2` or `log 3`; detector degree explicit from the outer spectrum [F].
- **(a)** A1. **(b)** B30.

### XN — Newton discs
- **Path:** line-centred self-map discs covering every zero → RH. **Established:** coverage and closed-margin criteria; the margin has nonnegative Laplacian [F].
- **(a)** none. **(b)** B32. Boundary sign does not control the interior minimum [F].

### BAG — Self-return
- **Path:** cutoff-uniform head-target density → RH; transport → AAL.
- **Established:** strong recurrence ⇔ RH; AAL ⇔ arbitrarily high all-cut zero transport; fewer than `T^c` separated self-returns of some zero disc for `c>(30/13)(1−σ)`; under a finite nonempty right-zero layer every locally uniform limit of scalar-normalized phase returns joining the zero to `Re s>1` is zero [F].
- **(a)** none. **(b)** B72, B83, B89, B97, B137, B145. The graded count excludes a zero only if power-many separated returns are produced; the exponent threshold is `≥1` for `σ≤17/30` [F].

### EWU — Even sector
- **Path:** even blind minimum `≥0` at every aperture → RH. **Established:** blind minimum `≥1/20` for `a≤(log 2+1/50)/2`; even sign ⇔ `−C≤Q` ⇔ Hamburger moments; sign-gauge balance iff `c≤log ρ`, `ρ³=ρ+1` [F] (log §9).
- **(a)** A1–A3. **(b)** B4, B17, B44: blind minimum beyond that interval; variance paid by complete signed jumps; Perron saturation gap.

### GTA — Schur charge
- **Path:** cofinally small quartic charge → RH. **Established:** full-mode compactness ⇔ RH ⇔ finite-prefix operator-norm convergence; late packets `≤` Hilbert–Schmidt mass`/400` [F] (log §9).
- **(a)** none. **(b)** B33: `∀ε,N ∃k≥N` charge `<ε`; the `1/400` ceiling does not vanish.

### OWU — Odd sector
- **Path:** joint odd sign with the polar hyperplane → RH. **Established:** odd criterion; unit-window floors; no sign gauge removes an acting negative prime antidiagonal [F]; through ACS a constant lower bound on the pole-free two-end family suffices [L*] (log §5).
- **(a)** A1–A3, A6. **(b)** B4, B17, B44; in two-end form `N(o_v)≥−C` (B1). At the prime 3 collar-mass replacement fails for `c≥287/500` [F].

### PBM — Regularized abscissa
- **Path:** `|Σ_{n<N}(Λ(n+1)−1)/log(n+1)|≤C_εN^{1/2+ε}` → RH. **Established:** exact equivalence [F] (log §9).
- **(a)** none. **(b)** B53. Regularization supplies no cancellation.

### RB — Robin / Nicolas
- **Path:** eventual extremal inequality → RH. **Established:** eventual criteria without a premise `Θ<1`; colossally abundant and lcm reductions [F] (log §9).
- **(a)** none. **(b)** B54.

### SRT — Lag localization
- **Path:** the cubic prime trace on a decisive sample → RH. **Established:** S3 [F].
- **(a)** A9. **(b)** B130 at `σ=0`: a uniform lower bound with omissions, or the upper bound at every prime; B6, B101, B104.

### ACT — Single shift
- **Path:** the variation inequality at one shift → RH. **Established:** receiver `Ẑ(m_au)=2S_a−D_a+8V_c+8τ_cA₂`; for `2c<log 5` only `{2,3,4}` enter; reflected-pair floor `1/(20000·2^k)` [F] (log §9).
- **(a)** A7, A140. **(b)** B44, B4: one shift uniform in profile and support; variance-free certificates fail for `c>273/400`.

### AIP — Incidence
- **Path:** global incidence allocation → RH. **Established:** full odd signed cost `≤K exp(r−c(2r)^{3/5}(log 2r)^{−5/3})`·Sobolev mass; capacity `log log N+O(1)`; orthogonal mixed error `→0` [F] (log §9).
- **(a)** A9, A13. **(b)** B45: `|reflectedPrimePolarCost(F,r)|≤C_σe^{2σr}(¼∫F²+∫F′²)` for every `σ>0`; B101, B104.

### SC — Stokes / Witt–Krein
- **Path:** bounded Gaussian-damped coupling, sublinear tensor loss, or glued index `≤1` → RH. **Established:** glued index `=κ_ζ+1`; Gaussian-damped `ℕ²` coupling bounded ⇔ RH; an undamped bound on a fixed two-prime cone or infinitely many bounded prime towers ⇒ AAL [F] (log §9).
- **(a)** none. **(b)** the damped bound; sublinear tensor loss (B39); ZAL for the undamped branch; B104.

### ACS — Castelnuovo–Severi on the degree points
- **Path:** the Hodge inequality on every window; a uniform lower margin of the window matrices; a bounded two-end family; subpolynomial critical-comb growth; or critical Abel integrability → RH.
- **Established:** S14, S10; §0.
- **(a)** A28, A41, A48, A140, A141, A162, A163.
- **(b)** B152, B192, B194, B195, B198, B196, B149, B169, B88, B87; B130; B16. Gap−binding `≥−C` with one `C`, or `N(o_v)≥−C` at every separation, is the open estimate; cut-share and pole-capacity estimates use index `≤1`; a uniform positive margin is incompatible with RH; fixed-rank gluing, contact-only mixing and nonnegative self-pairings fail [F]/[KR].

### ECP — Endpoint character positivity
- **Path:** endpoint jets → class functions → PSD character Grams at every rank ⇔ RH. **Established:** column projections nonnegative; exterior Toeplitz minors through order 200; mixed shapes `(2,1)`, `(3,1)`, `(2,2)`, `(2,1,1)` paid [F] (log §9).
- **(a)** none. **(b)** B86.

## 4. Candidates

Each needs its source-to-receiver step (B81). Dormant pending a source mechanism: SEC, CDC/BSH, APF, EWJ, RFHM, WBF [F].

| Candidate | Established [F] | (a) | (b) |
|---|---|---|---|
| S3 | a strip of depth `h<½` excludes heavy identity returns up to `exp(ηT)`; under `Θ<1` the transfer ⇔ RH | A118 | B148: with `[X]` the transfer is RH; BAG target returns are not identity returns |
| SEC | factorial-Fock boundedness at every strip parameter ⇔ `Re s=½` | none | a ζ-selective bound or exact edge compactness from the Sonin source |
| CDC/BSH | marked prices agree iff `Re s=½` | none | arithmetic descent or a nondivergent-price dark response on actual zero fibres |
| APF | prime/grade/cap trace reconstruction | none | full-divisor exhaustion |
| EGC | zero-pair contour; count error `<1/(n+1)` at explicit heights | none | height-fibre isolation and outer landing |
| EWJ | all-depth reporter; norm exhaustion iff `c=0` or `−a+b+2d=0` | none | source-faithful endpoint admission outside the blind plane |
| FEL | KL accounting | none | a predeclared history forcing the BSY sign |
| IRK | integral finite-idempotent traces; a finite free resolution | none | projective/descent construction identifying trace with Chern charge |
| MSC | `L²` discrepancy; conormal transport | none | Sonin/Weil sign landing |
| RFHM | full support/phase/grade admission | none | a phase/depth law with RH-sufficient wall orientation |
| W1C | index-one approximants, or a self-adjoint realization of the right zeros with a form positive on codimension `≤1`, give RH | none | B146, B171: independent finite nonnegative couplings converging on an interval, or a positive arithmetic reflection form |
| WBF | Gram determinants recover magnitudes and phase-gauge class | none | arithmetic certificate stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| AGZ | Hodge inequality form of RH; certified ratio `≤103/50`; first step packets and thin packets; uniform index bound at each ratio; index law in the aperture; gluing law and its rank kills; weakened and twisted contacts; packet and dilate at ratio three; self-pairing laws; power and critical combs; Laguerre tails [L*] | A162 | B152, B192, B196, B149, B169, B88, B87 |
| MixingArithmeticOfTheFloorTrees | Doob chain criterion; gap `≤` binding `+c₀`; two-end binding at `√ρ`; pole capacity; overlap law; cut and share law; odd sector and two-end criteria; margin laws for forms and matrices; exponent laws; zero gap and zero curvature of the trees [L*] | A162, A163 | B194, B195, B198, B16 |
| AHD / AID / HTGeometry-HardyBoundary | thresholds; the half-line energy branch and the critical state; strong-confinement limits; coercivity; compact sublevels and profiles, the closed domain [L*]; barriers, collars [S] | A9, A13, A158, A161 | B104, B123 |
| ALG | trickle-down from hyperbolic nonnegative links; Cayley ladder criterion [L*]/[F] | — | B196 (links with negative self-pairings) |
| HFP | short windows do not see the contacts; Li coefficients as limits of comb tails [L*]/[F] | — | B152 |
| WZC | two-sided edits; signed grouped edit below `½`; order law at every multiple; frontier dichotomy [L*] | — | B191 |
| EFT / APD | FE rigidity; slow defects among positive weights; Abel floors; signed fake [L*] | — | B191 |
| CRF / STCC | root numbers, columns, average row; theta-square series [KR] | A148, A149 | B185, B187, B180 |
| FCT | frame, coupled tower to `3/5`, pairing barrier, budget vertex, signal exponent [L*] | A118, A138 | B161, B174, B187 |
| MMD | the half-plane `7/8` for ζ, Dirichlet characters and the Hecke family over `ℚ(√−3)`, stated without hypotheses [S] | A33, A118 | — |
| GaloisTheoryOfZeros | Jensen equations; heat cover: transport, homotopy invariance, finite support, generation by turns, orbits = simple-join classes, real-time criteria [L*]; off-centre collisions [S] | A160 | B190, B197 |
| RHTower/Heat | `Λ_dBN<1/8`; quadratic detection; restart law; finiteness of non-real zeros at positive times [L*] | A19, A138 | B24, B124 |
| RHTower/Artin, HeckeLFunctions | Brauer induction; reciprocity for linear characters; kernel of the Artin map; Artin Euler products as Hecke products; completed Hecke `L`-functions [L*] | A141 | — |
| CompactHyperbolicSurfaces | resolvent, spectrum, Mercer expansion, trace of `T_a−T_b` for a cocompact group acting freely; the order `ℤ⟨1,i,j,ij⟩` of the division algebra `(2,3)_ℚ` in `M₂(ℝ)`, its congruence groups `Γ(N)` discrete and, for `N≥3`, acting freely [L*] (log §8, §11, §18); `Γ(N)`, `N≥3`, cocompact: a compact hyperbolic surface [S] (`isCocompactFree_congGroup`; log §20) | A120 | B157 |
| FFA | floors; receivers and kills of the off-scale kinds; tangent data under additive twists [L*]/[F] | — | B170–B173 |
| SA | ladder; exceptional heights; Liouville twist beyond the trivial aperture [L*]/[KR] | A117 | B159, B156 |
| ELT | growing-order reduction; restricted prime-weighted cofactor sum [F] | — | B141, B145, B138, B13 |
| CTZ, IRP | no bounded or Wiener constituent; unit gap of scattering-tower quotients is RH [F] | — | B146 |
| MZF / CDG / AIF | twisted moments; positive proportion; cameras; holomorphic-mollifier infimum [F] | A18 | B62, B57, B59 |
| MatomakiRadziwill, LogarithmicChowla | short-interval mean squares of `λ` and `λχ`; logarithmic two-point Chowla [L*] | — | — |
| SignFreePurityMechanisms | Goss Riemann hypothesis [L*]; return transfer [F] | — | a norm for ξ; B148 |
| HAT | clock; tower; Robin diagonal [F]; unbounded critical inverse [KR] | A54 | B88, B117 |
| BHR / AHMH / ASH / CTH / RIT | ringdown ⇔ strip; pulse rate = horocycle rate; `selberg_status`; Mayer resonances [L*]; filters; sharp shells [F] | A26, A41 | B68, B71, B87, B147, B178, B188 |
| TTPO / PTT / TAPO / CDGeo | no heavy return before the Vinogradov–Korobov height [L*]; resonator means [F] | A24 | B46, B97, B137 |
| ALST / AAD / RAC / APR | Stepanov degrees; producer rates; cut kernel; necessary mollifier lengths [F] | A30 | B48, B55, B67 |
| VHR / TCS | height 67; rank 14; double-exponential window height [L*]/[F] | A1–A5, A142 | — |
| Census | simple-critical proportion; runs of simple zeros; positivity cost `≥1+3/π²` [F] | — | B150, B57, B27 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| The minimal face: the prime trace bound on logarithmic windows off power-thin exceptions; in two-prime form on windows of radius `r√T` | ACS, SRT, WL, HF, ZCG, HAT-C, PM (count) |
| Σ: the sign on every window = no crossing along the aperture = the Hodge inequality on positive packets without common blocks = a bounded margin of the window matrices = the contraction of every conditional coupling = a bounded two-end family | RW, EWU, OWU, ACT, CHMD, SZ, RN, AIP, SC, LI, TT (odd), HF, HAT-C, ACS |
| Σ: binding. The union of two windows holds one bound state only through the true contacts and the jets together; contacts alone have zero gap and zero curvature; every fixed-rank model fails; the certified sign ends at aperture `0.3621` (ratio `2.063`); beyond it a certificate (A140) or the conditional coupling through the prime-free middle (B194); ratio three (B192) | ACS, HF, RW |
| Σ: the exponent. The unconditional matrix floor is `−C√K`; every `θ<½` is a strip (B195); the loss law of the overlap recursion decides | ACS, HF, SRT |
| Σ: the critical half-line state: its existence is the failure of RH (B104) | HF, SRT, AIP, SC |
| Σ: continuation at small time: positive real branch times = nontrivial conjugation monodromy; theta heads | ZCG (heat), PTR, LA, GTA, XN, HCF, PA, TH |
| Π: square-root precision; long moments past the height | WL, MC, SQF, PBM, RB, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| One scale, one producer: `[X]` at `7/8`; every `6r`-periodic Gauss pairing has frame `≥3/5`; no other source | JAS; MC (signal); S3; every graded receiver |
| Γ: reflection and count; the congruence mechanism is sharp at `3/16` in weight `½`; realization needs logarithmically negative self-pairings (B196) | PM, ECP, ACS (realization) |
| The exceptional coordinate: world I needs unit multiplicities with the reflection up to a decaying error, or a count below half the real part of the layer; world II is the scale | BAG, ZCG, JAS shell, SC undamped, WL thick runs, LA finite support |
| The dark range: prime sums shorter than the Vinogradov length; polynomials longer than the height; window heights beyond every verified height | every route at all heights; BAG; WD; MC |
| Missing source landing | the twelve candidates |

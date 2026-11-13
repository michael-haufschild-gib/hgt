# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: `065c78c2b5` (2026-11-13), working-tree sources included; the frontier map at the same checkpoint. Fact log: `logs/review-1311-frontier-facts.md` (cited as "log §n").

**Evidence.** `[L*]` Lean statement read at its declaration and recorded in the fact log; `[doc]` mechanism described in a module docstring whose statements were read; `[F]`, `[KR]` stated by the [frontier map](../rh-current-frontier-map.md) and the [scoped-obstruction ledger](../rh-killed-routes.md) at the checkpoint; `[S]` a module the frontier map grades unfinished or unintegrated; `[D]` deduction made here from `[L*]` statements (log §15, §16, §19, §21), not a Lean theorem; `[C]` classical mathematics, not in the corpus; `[A]` assessment; `[X]` the half-plane `7/8`, taken as proved: every Dirichlet `L`-function, ζ included, and every Hecke `L`-function of the family over `ℚ(√−3)` is zero-free in `Re s>7/8`. It is an external theorem (OpenAI, 30 September 2026). In the Lean source it is stated without hypotheses (`riemannZeta_ne_zero_of_seven_eighths_lt_re`, `DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, `riemannZeta_zero_mem_quasiRH_strip`, `ProbeFinalAssemblyUnconditional.common_probe`; log §8); the frontier map grades this source `[S]`, and validating its producer and dependency chain is just work (A118). Consequences of `[X]` on receivers are `[D]`. Sections 2.3–2.21 are interpretation and proposals: every untagged statement there is a proposal.

**38 live formulations; 12 candidates** (SEC, CDC/BSH, S3, APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF) [F].

**Notation.** As in [route-obstacles.md](route-obstacles.md). In addition:
- the **reach** of a producer is the least `σ₀` for which its implication gives `Θ≤σ₀`; a **pairing** `(c,k)` has local resonance norm `Q^{c−ks}` at a prime of norm `Q`, **uncoupled boundary** `(c+1)/k` and **coupled fixed point** `c/(k−1)`;
- a **certificate** at an aperture `A` is a proof of `0≤ccmRestrictedWeilGroundEnergy A` by finitely many explicit inequalities;
- `G_D` is the inverse of the neutral part of the dyadic window `(D,2D]` (its **Green matrix**), `μ_D` its binding energy, `φ_D` its positive eigenvector, `G₊` its positive part;
- the **slivers** of a window of logarithmic length `L∈(log 2,log 3)` are `[0,L−log 2]` and `[log 2,L]`; `c₂=(log 2)/√2`;
- the **excess** of an overlap step at level `C` is the negative part of the least eigenvalue of the Schur complement of `M+C` in `N+C`; a **loss law** of the recursion is a bound of the margin at ratio `ρ²/2` by the margin at ratio `ρ`.

## 1. Big picture

### 1.1 One problem, five exact forms
- **One inequality per prime.** Width `≤σ` ⇔ the prime trace `2Re S(log p)` is `≥−Kp^σ` on cofinal logarithmic windows after `≤Ce^{δT}` omissions; the upper bound alone on the undeleted windows is equivalent; two fixed primes on difference lags in windows of radius `r√T` suffice. Every radius `R=o(log T)` admits a tempered countermodel [F] (log §9).
- **One matrix at finite scale.** Weil's form on the step packets of a window is the block matrix `d(a)+d(b)+δ_{ab}ϱ(a)−J(a,b)−C_Q(a,b)`: the degrees `d(a)=log((a+1)/a)`, a logarithmic potential `ϱ(a)−J(a,a)≈log(a/2π)+1−γ` on the diagonal, the jets `J(a,b)≈½(1/|a−b|+1/(a+b+1))`, and the contacts `Λ(k)/k` along the floor maps `b↦⌊b/k⌋` [L*] (log §19). RH ⇔ on every window `(R,R+J]`, `R≤J`, disjointly supported nonnegative packets `x,y` with `N(x,x)<0` satisfy `N(x,x)N(y,y)≤N(x,y)²` ⇔ every eigenvector of the neutral part with negative eigenvalue has one sign [L*] (`riemannHypothesis_iff_forall_wells_bound`, `riemannHypothesis_iff_forall_bound_state_one_sign`; log §10).
- **One recursion on the ratio.** The window `(R,2(R+a)+b]` holds one bound state iff its two overlapping parts hold one each and the conditional coupling `X` of its ends through the dyadic middle is a contraction between their conditional energies; RH ⇔ this contraction on every window with `R≥34`, `a,b≥1` [L*] (`hermNegIndex_neutralWindow_overlap_eq_one_iff`, `riemannHypothesis_iff_forall_overlap_contraction`; log §12). The middle carries no contact: it is the archimedean matrix at its block size, the same for every window [D20].
- **One cover.** RH ⇔ no positive real branch time of the heat cover ⇔ conjugation of the fibre, which is an element of the forward monodromy group, is the identity at every positive real non-branch time [L*] (`riemannHypothesis_iff_forall_pos_not_mem_branchTimes`, `fibreConj_mem_forwardMonodromy`, `riemannHypothesis_iff_fibreConj_eq_one`; log §10).
- **One scale.** Every graded receiver reads one number, the zero width (§1.2).

### 1.2 The scale

| Reading | Statement | Evidence |
|---|---|---|
| rung `κ` of the sign | for `2δκ>1`: the sign on `[−κ log m,κ log m]`, `m=A₀log(\|γ₀\|+3)`, forces a second off-line zero within `m^κ` of an off-line zero of depth `δ` | [L*] (`zeta_companion_of_rung`, `cancellation_and_depth_ladder`; log §10) |
| exceptional heights of a rung | measure `≤T^{1−1/(2κ)+ε}` | [L*] (`eventually_boundedShape_rung_exceptions_sharp`; log §17) |
| signal of the reciprocal kernel | `Θ≤b` ⇔ the signal is `O(Z^{b′})` for every `b′>b` | [F] (JAS) |
| growth of the critical comb; of a power tail | growth exponent `σ` ⇔ width `≤σ`; exponent `σ` at `a` ⇔ zeros `≤½−a+σ` | [L*] (`strictGrowth_criticalPowerCombTail_iff_zeroWidth`, `powerCombTailGrowth_iff_zeroHalfPlane`; log §10) |
| two-end family | width `≤θ` ⇔ `N(o_v)≥−Ce^{θv}`, `0≤θ<½` | [L*] (`zetaZeroWidth_le_iff_twoEndOdd_rate`; log §5) |
| margin and step-packet floor of the matrices | a margin `CK^θ` or a floor `−CK^θ`, `θ<½`, gives width `≤θ`; unconditionally `−C√K` | [L*] (`zetaZeroWidth_le_of_neutralWindow_marginRate`, `zetaZeroWidth_le_of_packetForm_stepPacket_ge`, `exists_packetForm_stepPacket_ge_sqrt`; log §11) |
| ringdown; horocycle | zeros `≤1−2δ` ⇔ pulse decay `e^{−(δ−ε)τ}`, `0<δ≤¼`; pulse rate = horocycle rate | [L*] (`zeroFreeStrip_iff_pulse_ringdown`, `pulse_ringdown_iff_horocycle_rate`; log §10) |
| heavy returns of the prime orbit | under `Θ≤b` bounded on three rungs; none for `log t≤(log y)^{3/2−ε}` | [L*] (`heavy_return_bound_of_halfPlane`, `eventually_no_heavy_return_before_vk`; log §10, §12) |
| heat constant | `δ²/(200 log γ)≤Λ_dBN` for an off-line zero of depth `δ` at height `γ≥e^{1600}`; `Λ_dBN≤s+D/2` when the zeros of `H_s` have `(Im z)²≤D`; width zero ⇔ `Λ_dBN=0` | [L*] (`le_newmanConstant_of_offLine_zero_quadratic`, `newmanConstant_le_of_zeros_im_sq_le`, `zetaZeroWidth_eq_zero_iff_newmanConstant_eq_zero`; log §12) |

Sizes reach the rung `1`: the trivial aperture is `log log(mass)+o(1)`, and the sign changes across `2δκ=1` [L*]/[KR] (`exists_abs_trivialAperture_sub_le`; `domination-depth-blindness`). The level `7/8` is `[X]`: rung `κ<4/3`, returns `y^{1/8}`, ringdown rate `1/16`, comb growth `≤3/8`, two-end rate `e^{3v/8}`, `Λ_dBN≤9/128` [D5]. No receiver is stated in Lean with the half-plane inserted (A138). At the matrices the unconditional exponent `½` is the bound of the margin by the binding energy, which is of order `√ρ` [D23]; an exponent `θ<½` is a gap of size `√ρ−ρ^θ` between the first two eigenvalues.

### 1.3 The sign at finite scale: what is certified, and by what

**Certified.**
- Weil's form has the floor `1/5000` on every `C²` test supported in `[−181/500,181/500]` (even sector `1/5000`, odd sector `1/1000`) [L*] (`zetaZeroConfig_re_W_ge_of_aperture_le_threeHundredSixtyTwoThousandths`, `fullZeroForm_ge_of_even_support_le_threeHundredSixtyTwoThousandths`, `fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths`; log §21). The proof is a finite certificate: pole square, a rational envelope and a `23×23` Legendre factorization on the even sector, Schur lending on the odd sector [doc].
- The aperture `181/500` lies beyond `½log 2`: the prime 2 acts. At this aperture the Liouville-twisted form is negative on an odd test on which ζ's form is `≥(1/1000)∫F²` [L*] (`exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg`). The certified sign is selective in the prime 2 [D19].
- A ground energy at one aperture `A` is carried to the step packets of every window of logarithmic length `<2A` at every block size [L*] (`groundEnergy_mul_nested_mass_le_packetForm_of_log_lt`). Hence: block-matrix floor `1/5000` and exactly one bound state for `R≤J`, `50J≤53R` at every block size [L*] (`packetForm_stepPacket_ge_of_short`, `sum_blockMatrix_ge_of_short`, `hermNegIndex_neutralWindow_eq_one`; log §10, §12, §21); second eigenvalue of the neutral part `≥1/5000` there [D4].
- No bound state on narrow windows `16J≤R`; margins `1/20`, `1/100` on the first step packets of ratio four and seven; nonnegativity on thin step packets at every ratio; index `≤300000` at ratio four and uniformly bounded at each ratio [L*] (log §12, §16, §17).

**Not certified.** The dilation tower above `181/500` is frozen: `a_k<0.3621`, limit within `10^{−7800000}` of its base, below `½log 3` [L*] (`weilFloorApertureTower_lt`, `weilFloorApertureLimit_bounds`; log §19); [KR] `frozen-weil-floor-tower`. No declaration gives the sign for all tests at an aperture above this limit (log §21). The verified height is 67; the transfer from a verified height to a window is stated for apertures `a≥1` with a double-exponential height [L*] (`rhVerifiedThrough_sixtySeven`, `windowPositiveAt_of_rhVerifiedThrough`, `exists_doubleExp_windowPositive`; log §12).

**The recursion.**
- Parts of ratio `≤ρ` glue to a window of ratio `≤ρ²/2`: from `103/50` the steps reach `2.1218, 2.2510, 2.5335, 3.2093, 5.1498` [D1]. The first step is the aperture `0.3762`, above the frozen limit [D14].
- With `B` the couplings of the two ends to the middle and `N_e` the neutral form on the ends, the criterion of a step is `BG₊Bᵀ⪯N_e+(Bφ_D)(Bφ_D)ᵀ/μ_D`: the ends, together with the attraction through the bound state of the middle, dominate the coupling through its positive modes [D21].
- At the first step the conditional energies are `⪰1/5000` [D10]; with these floors alone the step needs `‖X‖≤1/5000`, and the direct coupling of the ends has norm up to `≈0.03` [D12], [D25]. Every contact by 2 of an end lands in the middle: the prime 2 couples the ends only through `G_D` [D12].
- Below the binding energy of the middle the margin of the whole exceeds the margin of the parts by at most the excess of the step, because the Schur complement of `M+C` increases in `C` at rate `≥1` [D22].
- In the one-prime range `log 2<L<log 3` Weil's form is `W⁰(f)−c₂‖s‖²+c₂‖t‖²`, with `W⁰` the prime-free form and `s,t` the symmetric and antisymmetric parts of `f` on its slivers under the shift by `log 2`; the Liouville twist exchanges `s` and `t` [D24]. A contact is `≥0` on packets with a node at the centre and `≤0` on packets of one sign [L*] (`shallow_contact_selective`; log §5).

**Binding and margin.**
- RH ⇔ the Doob chain of every window has gap `≥` binding energy `−C` ⇔ a bounded margin of the window matrices (the initial windows `(1,2M]` suffice) ⇔ a bounded two-end family; unconditionally gap `≤` binding `+c₀`; a positive uniform margin is incompatible with RH [L*]/[KR] (log §5; `continuum-doob-margin`).
- The binding energy of `(R,20mR]` is `≥c√m` from its two ends, and the ground state of a long window lives at its two ends [L*] (`eigenvalue_le_twoEnds`, `sq_binding_excess_le`; log §5). Unconditional two-sided control: `A(0)−2Σ_{k≤Q}Λ(k)/√k≤λ` and `−λΣφ²+packetForm≤poleCapacity·Σφ²` [L*] (`le_eigenvalue_of_contacts`, `binding_add_packetForm_le`).

**Kills.**
- Rank-one charge gluing of the halves of ratio four exists iff `R=1`; no rank-`r` lowered model with `600(r+1)≤H` has index one [L*]/[KR] (log §10; `ratio-four-low-rank-gluing`).
- Liouville-twisted contacts give index `≥2` at ratio `≥3`; contact multipliers in `[−5/2,19/40]` give index `≥2` at ratio `≥4` [KR] `weakened-contact-binding`. With the true contacts a packet and its dilate by two are bound on `(2r,6r]` [L*] (`bilin_neutralWindow_lowerEnd_upperEnd_le`; log §8).
- The floor trees alone: isolated components at every ratio below `9/2`, zero gap of the continuum dilation form, curvature exactly zero [L*] (`floorContact_eq_zero_of_component`, `dilationForm_le_of_no_gap`, `not_curvature_pos`; log §5, §11, §18). The jets alone bind a bounded amount [L*] (`le_eigenvalue_of_prime_free`).
- A completion of the couplings with index `≤1` has self-pairings summing to `≥m log m−2m` on one of two runs; nonpositive self-pairings give index `≥2`; couplings `−N` with nonnegative diagonal have `≥2` positive squares; the dyadic window attains the rate [L*] (log §11); [KR] `nonnegative-self-pairing-realization`.

### 1.4 The critical half-line state
`0<R_PD=R_PSD=R_polar=R_halfline≤W=R_prim=R_high=inf_A windowThreshold(A)`, each infinite iff RH; a failure of RH gives a finite-`W` half-line ground state [F] (log §9). At every `R>0` the unit-mass floor is attained, the minimizer is unique up to sign with Laplace transform zero-free on `Re z>0`; `λ(1/t)` is strictly concave; at finite `W` the state is outer and cyclic, with transverse coercivity, weighted and polar stability and `λ′(W)=−a(W)∫F²e^{−8u}/W` [F] (HF). Strong confinement: `λ−a−log a→μ`, `aδ_R→1`, `a∫(−u)F_R²→1/8` [L*] (`universal_softLogarithmic_confinement_limit`; log §10). Coercivity `Q≥L₊+4M−16`; compact trial sublevels; strongly convergent minimizing sequences; a compact family of rescaled minimizers; the closed `L²` domain with the trial energy; weighted Fatou and moment-continuity tools [L*] (log §8, §11, §18, §20). A finite-`W` state satisfies `|F(u)|≤C_βe^{βu}`, `½<β<15/2`, with a trace-free collar bound [S] (log §8). Attainment of `μ` on the closed domain is paper-only; lower semicontinuity of the signed energy, cutoff recovery, sign rigidity and convergence to a unique profile are open [F]. Every one of these properties holds on both sides of the charge question: stability and a nonzero polar pairing do not exclude the charged case, and exponential decay supplies neither the wall trace nor its flux law [F].

### 1.5 The producer: a theorem at `7/8`, a frame of `3/5` at every period
`Θ≤7/8` [X]. Its mechanism: a completed sum of cubic Gauss-sum coefficients over the twists over `ℚ(ζ₃)` is bounded directly and compared with its signal; two estimates give a half-plane (`zetaZeroAbscissa_le_of_two_estimates`, `heckeHalfPlane_of_family_corrected_signal`: conditional transfers) [L*] (log §10, §19).

| Fact | Evidence |
|---|---|
| the probe is a coupled tower: `T(b)=(3+b)/6`, `b_d=3/5+(2/5)6^{−d}`; every `6r`-periodic Gauss pairing has uncoupled boundary `2/3` and coupled fixed point `(4r−1)/(6r−1)≥3/5`, equality iff `r=1` | [L*] (`gauss_pairing_6r_thresholds`); [KR] `cubic-tower-half-plane-barrier` |
| the continued correction `L^S(6s−3,ψ₆η⁶)E(s)` has infinitely many zeros in `7/12≤Re s<2/3` | [KR] `cubic-correction-zeros` |
| exponent-model limit `1−4/(5n)`: `13/15` at twist order six | [KR] `seven-eighths-budget` |
| the binding bin `δ=79/204` has endpoint exponent `−7/30672` at `7/8`; its row count stays within `10⁻⁴` of the count used for `11/15≤κ≤3/4`; the corner of the cubic-coefficient design is `8/9` | [L*] (`endpoint_binding_bin`, `rowCountAt_binding_ge`, `corner_two_six`; log §19) |
| crossing the model floor needs a bilinear saving before Cauchy–Schwarz: `≥1/12` for the boundary `¾`, `≥1/3` for the boundary `½` at `n=6`; the row sieve has a threshold | [KR] `phase-blind-floor-gram`; [L*] (`signedGram_phase_endpoints`, `two_le_of_sieve_threshold`) |
| the short sextic Gram is diagonal; the average row is blind to the target; the row root number is the theta phase times a square; the theta-square series has a double pole; the rotated correlations see only the three-divisible layer; the Möbius sign comes from Gauss sums of odd order | [L*] (`sum_pairColumn_eq_zero`, `norm_gramEntry_le`, `average_rowLocalSum`, `rowRootNumber_eq_thetaPhase_mul_sq`, `thetaSqDirichlet_double_pole`, `rotatedCorrelation_eq_three_layer`, `exists_gaussSum_pow_orderOf_eq_of_odd`; log §17, §19) |

One mechanism has produced a pointwise theorem, and its class of `6r`-periodic Gauss pairings stops above `½` [D]. Every other mechanism of the corpus is a receiver, a model, a rigidity theorem or a certificate at one aperture.

### 1.6 Worlds, models, rigidity
`Θ≤7/8` [X]; AAL ⇔ `Θ∞=Θ`; ZAL ⇔ `Θ∞=½`; RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ the supremal negative index is `0` or `∞` [F] (log §9). A failure of RH is world I (a finite isolated top layer) or world II (a tail), with top `≤7/8`.

| Structures kept | Model | Evidence |
|---|---|---|
| the functional equation with Gamma factor, order `≤1`, the Riemann count within one | a landing countermodel | [L*] (`exists_riemann_gamma_counting_model_without_landing`; log §19) |
| Euler product over the rational primes, multiplicities `0,1,2`, integer norms, a count rate | two-sided edits adding exactly a pair `β±iγ` right of some `σ₁<½`, for `½<β<2/3`, `Θ+2β<2`; edits with zeros symmetric in a strip | [L*] (`exists_isIntegerNormFakeAt_sEdit_lt_half`, `exists_isEdit_zeros_symmetric_in_a_strip`; log §8); [KR] `two-sided-prime-edits` |
| globally meromorphic, distinct primes, `0≤Λ̃≤2Λ` | a model with exactly `β±iγ` right of `Θ` for every `Θ<β<1`, if `Θ<1`; each has an extra pole in `0<Re s<1−Θ` | [KR] `meromorphic-euler-firewall` |
| the same edits with subpolynomial defect energy | a fake at every `½<β₀<3/2−Θ`, if `Θ<1`; otherwise `Θ=1` with AAL | [L*] (`frontier_dichotomy`; log §10) |
| positive real weights, Hamburger strip class | arbitrarily slow defects with prescribed off-line zeros `1−μ±iγ` | [L*] (`exists_positiveWeighted_beurling_slow_defect`) |
| real weights on the integers | a signed fake with the zero `¾+i` and bounded defect; an Abel floor for every fake | [L*] (`signedPoly_fake`, `fake_abelMass_floor`; log §16) |
| unit multiplicities, Hamburger strip class, defect `O((1+\|t\|)^{−1/2+ε₀})`, `ε₀<½` | none: the rational primes | [L*] (`beurlingSystem_rigidity_of_decaying_defect`) |

**Laws of the models [L*].** A fake two-sided edit with a deleted prime `p` has defect energy `≥(A²/(256πp))T log T` and no decaying defect (`editSystem_fake_defect_energy`, `editSystem_defect_not_decaying`). A zero of an edit exponential beyond twice its count, continuation and summability exponents has even order; the greedy pair twin at `ρ`, `½<Re ρ<13/15`, has count exponent `≥Re ρ/2`; a fake below `√x` is balanced or has a real zero on top; `k!` divides `Σ_{j=2}^k(k!/j)n(js₁)` (`even_order_of_count`, `half_re_le_of_count_edit`, `balance_or_real_top_of_fake`, `factorial_dvd_sum_order_of_count`; log §8, §10, §19).

**The door [D].** Among unit multiplicities the reflection selects ζ at every rate of decay; among positive weights no growth bound short of boundedness selects anything. A proof of AAL, B13 or Landing has to use unit multiplicity with the reflection up to a decaying error, or the count below half the real part of the layer. **Recurrent receivers [L*].** Level-one positivity of the constant vector on infinitely many dyadic prime shells gives AAL, and under a maximal off-line zero it fails on all late shells; floors on windows of every bounded length give AAL, floors on windows of one length have models (`asymptoticAbscissaLaw_of_frequently_jasConstProductPositiveOn_shell`, `not_frequently_jasConstProductPositiveOn_shell_of_maximal_offLine`, `asymptoticAbscissaLaw_of_lengthDependent_floors`, `not_forall_abscissaLaw_of_windowFloor`; log §12, §17, §19). Under `Θ∞<Θ` the Möbius and Liouville signals and their Ramanujan twists have top-residue asymptotics [L*] (`tangentDatum_ramanujanTwist`; log §8).

### 1.7 The zero field and the heat cover
- **Field.** `K_even⊆ℝ` ⇔ RH; the centred Jensen equation has the full signed-permutation group or a rational relation among its moments [KR] `zero-field-transitivity`; [L*] (`jensenGal_full_or_exists_moment_relation`; log §10).
- **Cover.** Transport over forward times is bijective, non-escaping and homotopy-invariant; every forward monodromy moves finitely many zeros and commutes with `z↦−z`; the global reflection is not a monodromy; the turns generate the group; the group is the same at every base time; every forward branch time gives a nontrivial element; the orbits are the classes of simple joins, and a zero alone and simple in a moving region is followed across branch times [L*] (`finite_setOf_forwardMonodromy_ne`, `fibreNeg_not_mem_forwardMonodromy`, `forwardMonodromy_eq_closure_turnLassos`, `nonempty_mulEquiv_forwardMonodromy`, `exists_mem_forwardMonodromy_ne_one_of_mem_branchTimes`, `simplyJoined_iff_exists_mem_forwardMonodromy`, `exists_simplyJoined_of_alone`; log §6, §11, §16, §18).
- **Pairs.** Pair preservation of the whole group ⇔ every forward collision is central [L*] (`forwardMonodromy_preserves_pairs_iff`); an off-centre forward collision exists at arbitrarily large `Re τ`, so pairs are moved [S] (`exists_forward_multipleZero_ne_zero`; the cosine-model dependency has a call mismatch, A160). The criterion that remains is the real-time one.
- **Heat.** `Λ_dBN<1/8`; for `t>0`, `H_t` has finitely many non-real zeros [L*] (`newmanConstant_lt_eighth`, `riemannHeat_nonreal_zeros_finite`; log §12); the same finiteness follows from membership of conjugation in the group and finite support [D6]. Forward control is not uniform as `τ→0` [F].

### 1.8 Law and point
One pointwise theorem holds past the Vinogradov–Korobov region: no zero right of `7/8` [X]. Left of it the native theorems on ζ and on the Liouville function are in law: displaced twisted second moments for `θ<½` and a positive critical proportion at `θ=13/50`; a simple-critical proportion `≥0.6725−ε` (imported `Zeta23` plus local input); runs of five consecutive simple critical ordinates; cameras isolating exterior mass `≤¼` [F] (log §9); short-interval mean squares of `λ` and `λχ` and `(log x)^{−1}Σ_{n≤x}λ(n)λ(n+h)/n→0` for every `h≥1` [L*] (`tendsto_logAvg_liouville_shift`; log §10). Logarithmic correlation decay supplies no half-power rate [F]. Two kinds of pointwise statement are available below RH: a level of the scale, and the sign at one aperture by a certificate.

### 1.9 What is ruled out

| Mechanism | Verdict | Evidence |
|---|---|---|
| continuation of a Weil floor in the aperture by the dilation modulus | frozen below `0.3621` | [L*]; [KR] `frozen-weil-floor-tower` |
| a verified height as a route to the sign at ratio three | the transfer is stated for `a≥1` with double-exponential height; the verified height is 67 | [L*] |
| the certified floors `1/5000` as the only input of the first overlap step | they need `‖X‖≤1/5000` against a direct coupling of norm `≈0.03` | [D25] |
| gluing through finitely many charges or a model of bounded rank | fails beyond block size one; rank `r` fails for `600(r+1)≤H` | [L*]/[KR] |
| the sign from the sizes of the contacts, or for a sign twin | weakened and Liouville-twisted contacts hold two bound states; the Liouville twist fails already at aperture `181/500` | [KR]; [L*] |
| mixing from the floor trees alone, or from curvature | zero gap, zero curvature, isolated components | [L*] |
| a realization of the couplings by mixed areas or nef classes | couplings `−N` with nonnegative diagonal have `≥2` positive squares | [L*]; [KR] |
| a positive uniform margin | incompatible with RH | [KR] `continuum-doob-margin` |
| pair preservation of the forward monodromy group | false | [S] |
| an exponent below `3/5` from the frame of a `6r`-periodic Gauss pairing | the coupled tower | [L*] |
| the explicit formula, positivity, the Euler product over the rational primes with a count rate, the functional equation as a growth bound among positive weights, as a constraint on a finite layer | models | [L*]/[KR] |
| windows below the logarithmic radius; floors of one length | countermodels | [F]; [L*] |
| an improvement of `3/16` by inputs valid in weight `½` | a weight-`½` eigenfunction at `3/16` | [L*] (`selberg_status`) |
| half-power rates from logarithmic correlations | none | [F] |
| finite families of convergent linear laws, pole matching, Möbius gauge as sources of the count | no half power | [KR] |

### 1.10 Where a proof step is available

| # | Opening | Converts through | First lemma | Yield | Kind |
|---|---|---|---|---|---|
| O1 | the half-plane `7/8` as a verified theorem with its receivers | the hypothesis-free statements in source [S] | A118; then A138, A163 | `Θ≤7/8` verified; `Λ_dBN≤9/128`; two-end rate `3/8`; exponent `3/8` at the matrices on the initial windows up to logarithms | just work |
| O2 | the binding bin of the probe | `endpoint_binding_bin`: the bin `δ=79/204` is within `7/30672` of equality at `7/8` | a row count in that bin below the count used by a fixed amount (B174) | a half-plane in `[13/15,7/8)` | density estimate |
| O3 | the long columns | the frame of the two estimates | a power saving in the first moment of the row root numbers against one fixed dual column, then uniformly (B185); calibration A148, A149 | a half-plane below `13/15`, down to `2/3` | an estimate that is not a square |
| O4 | certificates in the one-prime range | `groundEnergy_mul_nested_mass_le_packetForm_of_log_lt` | a certificate at aperture `0.3762` in the normal form [D24]; then above `½log 3` (A140) | one bound state at ratio three at every block size: the conclusion of B192 | just work (unverified) |
| O5 | the Green matrix of the prime-free dyadic window | the overlap law in Green form [D21] | two-sided bounds for the blocks of `G_D` between the slivers of `(D,2D]`, with the bound-state part `(Bφ_D)(Bφ_D)ᵀ/μ_D` separated (B194) | a proof of the first overlap steps with a stated excess; the mediator of every later step | method, below RH |
| O6 | the loss law | [D22]; `riemannHypothesis_iff_neutralWindow_margin_bddBelow`; `zetaZeroWidth_le_of_neutralWindow_marginRate` | the shifted overlap law in Lean (A162); then a bound of the excess of one step | excesses summable below `inf_D μ_D` along every chain of doublings ⇒ RH; a loss weaker than squaring ⇒ RH [D3] (B195) | RH strength |
| O7 | the critical state | `riemannHypothesis_or_exists_exponentially_bounded_criticalState` [S] | identification of the localized critical state with the bounded Green solution: forcing/domain bridge, first-order cross terms, collar-energy transfer (B104) | exclusion of a finite-`W` state is RH on HF, SRT, AIP, SC | RH; method at the first step |
| O8 | world I | the receivers of §1.6 | a bound for the restricted prime-weighted cofactor sum at a growing isolated mode (B145), or non-attainment (B170) | AAL | AAL |

The real-time conjugation criterion has no first lemma below RH: transitivity of the group (B197) needs only fixed-time isolation estimates [D9] and has no RH yield.

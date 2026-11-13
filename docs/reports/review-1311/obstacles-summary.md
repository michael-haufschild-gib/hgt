# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: `065c78c2b5` (2026-11-13), working-tree sources included; the frontier map at the same checkpoint. Fact log: `logs/review-1311-frontier-facts.md` (cited as "log §n").

**Evidence.** `[L*]` Lean statement read at its declaration and recorded in the fact log; `[doc]` mechanism described in a module docstring whose statements were read; `[F]`, `[KR]` stated by the [frontier map](../rh-current-frontier-map.md) and the [scoped-obstruction ledger](../rh-killed-routes.md) at the checkpoint; `[S]` a module the frontier map grades unfinished or unintegrated; `[D]` deduction made here from `[L*]` statements (log §15, §16, §19, §21, §22), not a Lean theorem; `[C]` classical mathematics, not in the corpus; `[A]` assessment; `[X]` the half-plane `7/8`, taken as proved: every Dirichlet `L`-function, ζ included, and every Hecke `L`-function of the family over `ℚ(√−3)` is zero-free in `Re s>7/8`. It is an external theorem (OpenAI, 30 September 2026). In the Lean source it is stated without hypotheses (`riemannZeta_ne_zero_of_seven_eighths_lt_re`, `DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, `riemannZeta_zero_mem_quasiRH_strip`, `ProbeFinalAssemblyUnconditional.common_probe`; log §8); the frontier map grades this source `[S]`, and validating its producer and dependency chain is just work (A118). Consequences of `[X]` on receivers are `[D]`. Sections 2.3–2.21 are interpretation and proposals: every untagged statement there is a proposal.

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
- No bound state on narrow windows `16J≤R` [F]; margins `1/20`, `1/100` on the first step packets of ratio four and seven; nonnegativity on thin step packets at every ratio; index `≤300000` of the block matrices with contacts up to four at ratio four, and a bound uniform in the block size at each ratio [L*] (log §12, §16, §17).

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
| the exponent budget of the probe has a vertex at `7/8`: three estimates meet there, the low bound, the row count of the bin `δ=79/204` and the dual length of the reflected rows; that bin has endpoint exponent `−7/30672`; every geometry with low boundary `≤7/8−1/4000` fails in it; its row count moves by less than `10⁻⁴` for `κ=2β−1∈[11/15,3/4]`; with the count `U^{1−δ}` in every bin the budget reaches `13/15`; rows of conductor `q_m²` with sextic frequencies have corner `8/9` | [L*] (`endpoint_binding_bin`, `endpointExponent_pos_of_lowBoundary_le`, `rowCountAt_binding_ge`, `corner_two_six`; log §22); [doc] |
| crossing the model floor needs a bilinear saving before Cauchy–Schwarz: `≥1/12` for the boundary `¾`, `≥1/3` for the boundary `½` at `n=6`; a bound for the rows through the twists is no low estimate; a sieve term `K^uN^v` with `4u+3v≥5` gives no half-plane | [KR] `phase-blind-floor-gram`; [doc]; [L*] (`two_le_of_sieve_threshold`; log §22) |
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

**Laws of the models [L*].** A fake two-sided edit with a deleted prime `p` has defect energy `≥(A²/(256πp))T log T` and no decaying defect (`editSystem_fake_defect_energy`, `editSystem_defect_not_decaying`). A zero `ρ` of an edit exponential with `Re ρ>2max(β,c₀,θ/3)`, for count exponent `β`, continuation abscissa `c₀` and summability exponent `θ`, has even order; the greedy edit at a non-real `ρ`, `½<Re ρ<13/15`, has every count exponent `≥Re ρ/2`; an integer-norm fake at an exponent `≤½` is balanced or has a real zero on top; `k!` divides `Σ_{j=2}^k(k!/j)n(js₁)` (`even_order_of_count`, `half_re_le_of_count_edit`, `balance_or_real_top_of_fake`, `factorial_dvd_sum_order_of_count`; log §8, §10, §19, §22).

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
| O2 | the vertex of the probe | `endpoint_binding_bin`, `endpointExponent_pos_of_lowBoundary_le`: at `7/8` the bin `δ=79/204` is within `7/30672` of equality and binds every geometry | a count of the rows of that bin below the published count by a fixed power (B174) [A3] | a half-plane in `[13/15,7/8)` | a large-value count |
| O3 | the long columns | the frame of the two estimates | a power saving in the first moment of the row root numbers against one fixed dual column, then uniformly (B185); calibration A148, A149 | a half-plane below `13/15`, down to `2/3` | an estimate that is not a square |
| O4 | certificates in the one-prime range | `groundEnergy_mul_nested_mass_le_packetForm_of_log_lt` | a certificate at aperture `0.3762` in the normal form [D24]; then above `½log 3` (A140) | one bound state at ratio three at every block size: the conclusion of B192 | just work (unverified) |
| O5 | the Green matrix of the prime-free dyadic window | the overlap law in Green form [D21] | two-sided bounds for the blocks of `G_D` between the slivers of `(D,2D]`, with the bound-state part `(Bφ_D)(Bφ_D)ᵀ/μ_D` separated (B194) | a proof of the first overlap steps with a stated excess; the mediator of every later step | method, below RH |
| O6 | the loss law | [D22], [D26]; `riemannHypothesis_iff_neutralWindow_margin_bddBelow`; `zetaZeroWidth_le_of_neutralWindow_marginRate` | the shifted overlap law and a lower bound for `μ_D` uniform in `D` in Lean (A162); then a bound of the excess of one step | a window of ratio `ρ` is `≈log₂log(ρ/2)+5` steps from the certified range; excesses with sum below `inf_Dμ_D` ⇒ RH; a loss weaker than squaring ⇒ RH [D3] (B195) | RH strength |
| O7 | the critical state | `riemannHypothesis_or_exists_exponentially_bounded_criticalState` [S] | identification of the localized critical state with the bounded Green solution: forcing/domain bridge, first-order cross terms, collar-energy transfer (B104) | exclusion of a finite-`W` state is RH on HF, SRT, AIP, SC | RH; method at the first step |
| O8 | world I | the receivers of §1.6 | a bound for the restricted prime-weighted cofactor sum at a growing isolated mode (B145), or non-attainment (B170) | AAL | AAL |

The real-time conjugation criterion has no first lemma below RH: transitivity of the group (B197) needs only fixed-time isolation estimates [D9] and has no RH yield.

## 2.1 Tasks that are just work

A task is listed when a known argument exists or its statement is a deduction from Lean statements; `(unverified)` marks tasks whose difficulty is not established. None of them decides RH. "Opening" refers to §1.10.

### Steps of an opening
| # | Task | Opening | Routes | Basis |
|---|---|---|---|---|
| A118 | validation of the producer and dependency chain of the hypothesis-free `7/8` assembly | O1 | JAS, MC, S3 | `ProbeFinalAssemblyUnconditional.common_probe`, `riemannZeta_zero_mem_quasiRH_strip` [S] |
| A138 | the corollaries of `Θ≤7/8` on the receivers as Lean statements: rung `κ<4/3`; a heavy return at `t` needs `log t≥cy^{1/8}`; ringdown rate `1/16`; critical-comb growth `≤3/8`; `Λ_dBN≤9/128`; two-end rate `e^{3v/8}`; fake edits with subpolynomial defect energy at every `½<β₀<5/8`; the signed grouped edit at every `½<β<9/16` | O1 | every scale route | the receivers of §1.2 [L*]; `frontier_dichotomy`, `exists_isIntegerNormFakeAt_sEdit_lt_half` [L*]; [D5] |
| A163 | the converse exponent law with a logarithm of the block size: width `≤θ` ⇒ step-packet floor `≥−CK^θ log K·log(KR+2)`; with `[X]` the exponent `3/8` on the initial windows (unverified) | O1, O6 | ACS, HF | [A2]; `zetaZeroWidth_le_iff_twoEndOdd_rate` [L*] |
| A162 | Lean statements of: the second-eigenvalue floor `1/5000` at ratio `≤103/50`; the conditional-energy floor at the first overlap step; the `N`-orthogonal and Green forms of the overlap criterion; the additive loss law below the binding energy of the middle; a lower bound for `μ_D` uniform in `D` | O5, O6 | ACS, HF, RW | [D4], [D10], [D11], [D21], [D22], [D26] |
| A140 | fixed-aperture certificates of the kind proved at `181/500`: at aperture `0.3762` (the first overlap step), above `½log 3` (ratio three at every block size), above `log 2` (ratio four), up to `½log 5` (unverified: the size of a certificate at the floors of these apertures) | O4 | RW, ACT, EWU, OWU, ACS | `one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths`, `groundEnergy_mul_nested_mass_le_packetForm_of_log_lt` [L*]; [D18], [D24] |
| A148 | the layers `m=0,1` of the theta-square series and the target component of a twisted column [C] | O3 | MC, JAS, PM | `thetaSqDirichlet_double_pole`, `rotatedCorrelation_eq_three_layer` [L*] |
| A149 | the floor bin over `𝔽_q[T]`, `q≡1 mod 6`, with the long columns evaluated exactly (unverified) | O3 | MC, JAS | CRF |
| A158 | Lean attainment of the limiting infimum on the closed domain (paper proof written): lower semicontinuity of the signed energy, cutoff recovery, sign rigidity, uniqueness and convergence of the profile (unverified) | O7 | HF | compact sublevels, minimizing sequences, compact family, closed domain, weighted Fatou and moment continuity [L*] |
| A161 | verification and integration of the barrier, collar and Gamma-cutoff modules | O7 | HF | `criticalHalfLineGroundState_exponential_bounds`, `IsHalfLineEnergyMinimizer.terminalCut_energy_lower` [S] |
| A120 | the geometric side of the trace formula and the Selberg zeta function of a compact surface `Γ(N)\ℍ` of the order of `(2,3)_ℚ`, with a small eigenvalue: a finite nonempty stratum with an Euler product and a functional equation [C] | O8 (calibration) | BAG, ZCG, PM | spectral side `hasSum_nu` [L*]; `isCocompactFree_congGroup` [S] |

### Further assemblies
| # | Task | Routes | Basis |
|---|---|---|---|
| A141 | the half-plane `[X]` for fields containing `ζ₃` and every ray class character (unverified); the Artin transfer of the index needs virtual zero and pole configurations with orders and the matching of local conductors with ramification [F] | ACS, HF | `exists_le_negIndex_rayClassGram_iff` [S]; `exists_artinEulerProduct_eq_prod_zpow_heckeL`, `exists_primitive_heckeCharacter_artinSymbol` [L*]; [D13] |
| A160 | repair of the saddle-error call (`leftErr R a`) in the cosine-model dependency of the off-centre collision theorem | ZCG | `exists_forward_multipleZero_ne_zero` [S] |
| A142 | an explicit constant in the verification rate `exp(exp(Ca))`; a transfer stated for apertures below one | RW, SRT, TH, LI, HCF | `exists_doubleExp_windowPositive`, `windowPositiveAt_of_rhVerifiedThrough` [L*] |
| A117 | the end points of the feasible interval of `w(2)` at aperture `181/500` | RW, SA | [KR] `first-contact-weights` |

### Finite verification and explicit constants
A1 certified `RHVerifiedThrough T` past 67; A2, A3 numeric heights and first-window membership; A4, A5 theta ranks beyond 14 (unverified); A6, A7 cone widths, anti-diagonal certificates (unverified); A9, A13 constants of the eighth-root horizon, near-gcd charges (unverified); A19 a heat horizon with an explicit height; A20 the Jensen rung past `d⁴≪T log T` (unverified).

### Classical inputs to formalize
| # | Task | Basis |
|---|---|---|
| A18 | twisted second moments past the square root [C]. Through the dyadic receiver a Möbius mollifier of length `T^θ` with bound `O(T)` improves on `[X]` exactly for `θ>4/3` [D28] | `θ<½` native [F]; `eventual_depth_bound_of_dyadic_moebius_moment` [L*] |
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| A41 | count law for plane quartics [C] | hyperelliptic case [F] |
| A33, A54 | Fourier coefficients of the cubic residue; cusp expansion for Bianchi resolvents (unverified) | [F] |

Further (unverified): A24, A28, A30, A42, A46, A48, A58.

## 2.2 Open mathematical obstacles

`≥qRH`: implies a zero-free half-plane below `7/8`, Lindelöf or ZAL. "sub": implied by RH and not known to imply RH or AAL. Wall numbers refer to [walls-ledger.md](walls-ledger.md).

### The common minimal face
| # | Problem | Strength | Routes | Wall |
|---|---|---|---|---|
| B130 | the prime trace bound on any decisive sample: `2Re S(log p)≥−K` on the primes of late logarithmic windows after omissions, or the upper bound at every prime; in two-prime form on windows of radius `r√T`; with `Kp^σ`, `σ<3/8`, a half-plane below `7/8` | RH (≥qRH at `p^σ`) | ACS, SRT, WL, HF, ZCG, HAT-C | Σ137–Σ151, Σ198 |
| B159 | a rung `κ≥4/3` with a saving that fails for the Liouville twist | a half-plane below `7/8` | sign routes, BAG | Σ162 |
| B144 | separation of the deep off-line ordinates | sub | SRT, ACS | — |

### Σ — critical sign
| # | Problem | Strength | Routes | Wall |
|---|---|---|---|---|
| B1, B152 | the sign on every window; one bound state at every ratio and block size | RH | all sign routes; ACS, HF | Σ183, Σ184 |
| B194 | the contraction of the conditional coupling at the first overlap steps (ratios `2.12, 2.25, 2.53, 3.21`) by a bound for the Green matrix of the prime-free dyadic middle between its slivers; the certified floors alone do not give it; the conclusion at each ratio also follows from a certificate (A140) (§2.21) | sub; method | ACS, HF, RW | Σ199 |
| B192 | the selective sign at ratio three and four from the contacts: one bound state of `(R,3R]` and `(R,4R]` at every block size; proved on packets and their dyadic dilates; middle-supported and unequal-child directions open | sub (a finite certificate at each ratio); method | ACS, HF, RW | Σ188 |
| B195 | an exponent `θ<3/8` for the step-packet floor or the neutral margin; any `θ<½` from the matrices alone; a gluing estimate whose loss per overlap step is weaker than squaring | ≥qRH; RH at subsquaring loss | ACS, HF, SRT | Σ202 |
| B198 | the converse exponent law on all packets uniformly in the block size | method | ACS | Σ202 |
| B104 | exclusion of a finite-`W` ground state, charged (`R_polar<W`) or polar-orthogonal (`R_polar=W`); first step: identification of the localized critical state with the bounded Green solution (§2.8) | RH (method at the first step) | HF, SRT, AIP, SC | Σ135, Σ177, Σ207 |
| B196 | a realization of the couplings `−N(a,b)` as intersection numbers with self-pairings of size `−log m` per block, on which an index theorem holds (§2.13) | producer | ACS, HF | Σ205 |
| B2, B4, B5 | bounded `Ψ` to contact; outer predictors; kick admission | RH | RW, EWU, OWU, CHMD | — |
| B6, B101 | full-space sign at every critical multiple; polar payment at every ratio | RH | HF, SRT, AIP | — |
| B3, B16, B17 | variation of `r` free of `1/μ`; limit and decay law of the margin at finite block size; signed ground states past `log ρ` | sub / method | RW, ACS, EWU | — |
| B123, B156 | correlated arithmetic pairings dominating the depleted kernel; arithmetic cluster exclusion on a rung | method | HF; SA, RW | Σ163 |
| B160 | level-one dressed positivity on all large primes | RH | JAS | Σ164 |
| B20–B25, B102 | theta ranks and the signed adaptive-head payment at every aperture and degree; outer Jensen roots; `N_d` bounded (⇔ finite off-line support); collisions at small positive time; frequency below one | RH / ≥qRH | TH, LA, ZCG | Σ197 |
| B27, B47 | runs of simple critical zeros longer than five; multiplicity by an input that is not a size | sub | ZCG, census | Π181 |
| B29–B45 | the single open estimates of PTR, HCF, PA, XN, GTA, TT, CHMD, RN, SZ, TG, SC, ACS, HF, FU/CFC/RP, LI, ACT, AIP | RH | as named | — |
| B88 | the sign of the comb finite part | RH | ACS, HF | — |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH | ZCG, LA | — |
| B146, B171 | an independent family of bounded index converging to ξ; a form of signature `(1,∞)` from the places in which the right zeros are a symmetric spectrum | RH (producer) | W1C, PTR, IRP, PM | Γ195, Γ222 |

### Π — precision and production
| # | Problem | Strength | Routes | Wall |
|---|---|---|---|---|
| B174 | a count of the rows of the bin `δ=79/204` of the probe below the published count by a fixed power (§2.4) | a half-plane in `[13/15,7/8)` | JAS, MC | Π160 |
| B185 | the long columns: a power saving in the first moment of the row root numbers against a dual column, uniformly in the column (§2.4) | a half-plane in `(2/3,13/15)` | JAS, MC | Π175 |
| B161 | a signal bound `O(Z^b)` for some `b<7/8` | a half-plane below `7/8` | JAS, MC | Π159, Π162 |
| B187 | a Möbius-signed pairing outside the `6r`-periodic Gauss pairings whose coupled fixed point is below `3/5` (§2.5) | producer | JAS, MC, every scale route | Π174, Π177 |
| B180 | the reflection of the completed theta row without Eisenstein series (§2.6) | method | JAS, MC | — |
| B48–B54 | the deciding input at square-root precision and its classical faces: endpoint energy, half-power Möbius cancellation, level-one positivity, the BSY sign, the regularized abscissa, Robin and Nicolas | RH | WL, MC, SQF, JAS, CTF, PBM, RB | Π1, Π4 |
| B55, B67 | polynomial stencil rate; parity at power saving | ≥qRH to RH | WL, MC | Π3 |
| B56 | `Θ<1⇒Θ=½`; with `[X]` it is RH | RH | whole programme | — |
| B57–B61 | depth density `o(T)`; `D_win`; pointwise prime cost of the adaptive profile at its selected centres; Green moments at deep zeros; a detector past the last scale | sub | WD, MC, ZCG | Π22, Π171 |
| B62, B63, B66, B91 | cofinal long moment with `θ`-independent exponent; collision bounds; near-unit holomorphic budgets; cut-kernel mass annihilation | RH | WD, CTF, AIF, RAC | Π41 |
| B46, B97, B121, B137 | proportional saving at length `(log X)^{2K}`; first return past the Vinogradov–Korobov height; freezing control; collective depth floor | sub | BAG, PTT, TAPO, TTPO | — |
| B106 | a correspondence on the orientation cover with bounded local indices | RH | MC, HAT | — |
| B110, B126, B127 | thick crude count; sampling set; lag recurrence | AAL | WL, ZCG, ACS | — |
| B145 | the restricted prime-weighted cofactor sum at a growing isolated mode | AAL [D] | ZCG, BAG, ELT | Π149 |
| B150 | a form factor bounded by `4` on `(1,10/9)` | sub | census | — |
| B173 | a two-sided subexponential bound of the trace on late windows of one length | AAL | ZCG | — |

### Γ — selection, reflection, position
| # | Problem | Strength | Routes | Wall |
|---|---|---|---|---|
| B13, B138, B141 | finite stratum; landing; Deuring–Heilbronn for ζ | sub | whole programme | Γ67, Γ182, Γ184 |
| B83, B170 | AAL; non-attainment for ζ | sub / AAL | BAG, JAS, SC, ZCG, WL | Γ68 |
| B157 | which structure of ζ that a Selberg-type zeta function lacks excludes a finite stratum | method | BAG, ZCG, ELT | Γ219 |
| B191 | a unit-multiplicity fake with subpolynomial defect energy at `β₀≥3/2−Θ`; whether a bounded defect forces the rational primes among unit multiplicities | method | ZCG, BAG | Γ239, Γ242 |
| B190 | the orbit of a zero with irrational real part under the embeddings fixing the prime trace field | method | LA, ZCG | Γ243 |
| B197 | transitivity of `G₊`; no RH yield by itself | method | ZCG | Γ255 |
| B89, B112, B128 | bounded aligned return; the functional equation into vertical transport; replication by another mechanism | sub | BAG, ZCG | — |
| B68, B71 | independent reflection Krein positivity; universal decay and the horizon rates | RH | PM | Γ86 |
| B178, B188 | a relaxation rate beyond the tempered exponent; a mechanism for the scattering resonances whose inputs fail in weight `½` (§2.7) | producer | PM | Γ86 |
| B69, B72 | collision-free descent of the cosine source; cutoff-uniform head-target density | RH | PTR, BAG | — |
| B80, B81 | twins of the functional equation with off-line zeros in the full class; the source-to-receiver step of each candidate | sub; producer | ECP, candidates | — |
| B86, B87 | positivity of the endpoint character at unbounded rank; a count with Tate limit `Q`, defined without `Q` | RH | ECP, ACS, HF, PM | — |
| B114, B117, B147 | partner involution; a regulator with a gap before the limit; Shimura nonvanishing for one eigenform | producer; indep. | PM | — |
| B149, B169 | Bézout from a property of the object; a doubling with a canonical height | RH (producer) | ACS, HF | — |
| B172 | a functional decreasing under projection that is not a function of finitely many linear statistics | producer | ZCG, HF | Γ223 |
| B148 | the transfer of S3 | RH (the strip is `[X]`) | S3 | — |
| — | ZAL | ≥qRH | whole programme | — |

### Settled questions
| # | Question | Answer | Evidence |
|---|---|---|---|
| B193 | Does an off-centre collision exist at a forward time; does the forward monodromy preserve the pairs `{z,−z}`? | a collision with `z≠0` exists at arbitrarily large `Re τ`; some monodromy at every forward base moves a zero outside its pair. The RH criterion is the real-time one | [S] (`exists_forward_multipleZero_ne_zero`, `not_forwardMonodromy_preserves_pairs`; A160); [L*] (`forwardMonodromy_preserves_pairs_iff`) |
| B183, A157 | Is there a fake with count exponent below `½` and a non-real pair alone on top? | yes for `½<β<2/3`, `Θ+2β<2`: the signed grouped edit; with `[X]` for every `β<9/16` [D] | [L*] (`exists_isIntegerNormFakeAt_sEdit_lt_half`) |
| B189 | Do the halves of a window of ratio four glue through their charges? | only at block size one; rank `r` fails for `600(r+1)≤H` | [L*] (`halves_of_ratio_four_glue_iff_eq_one`, `two_le_hermNegIndex_lowered_model_of_rank`) |
| B15 | a pointwise saving past the Vinogradov–Korobov region | `[X]`; verification is A118 | [S] |
| A154, A150 | reciprocity for linear characters of abelian extensions; Brauer induction | every Artin Euler product is a product of integer powers of Hecke `L`-series on `Re s>1`; the Artin symbols of a linear character are the values of a primitive ray class character | [L*] (`brauer_induction`, `exists_rayPrincipal_le_ker_artinMap`, `exists_mulEquiv_quotient_normIdealGroup`, `exists_artinEulerProduct_linearCharacter_eq_heckeL_mul`, `exists_artinEulerProduct_eq_prod_zpow_heckeL`, `exists_primitive_heckeCharacter_artinSymbol`) |
| A155 | the order law of the edits at every multiple | `k!` divides `Σ_{j=2}^k(k!/j)n(js₁)`; prime and isolated multiples | [L*] (`factorial_dvd_sum_order_of_count`) |
| A144 | tangent data of `μ` and `λ` under additive twists in world I | residue numerators are those of `μ` times explicit Ramanujan factors | [L*] (`tangentDatum_ramanujanTwist`, `ramanujanNumerator_div_eq`) |
| A147 | logarithmic two-point Chowla | `(log x)^{−1}Σ_{n≤x}λ(n)λ(n+h)/n→0` for every `h≥1` | [L*] (`tendsto_logAvg_liouville_shift`) |
| A153 | rigidity of the functional equation | unit multiplicities with a decaying defect are the rational primes; positive weights admit arbitrarily slow defects with prescribed off-line zeros | [L*] (`beurlingSystem_rigidity_of_decaying_defect`, `exists_positiveWeighted_beurling_slow_defect`) |
| A159 | the converse exponent law | on the odd two-end states it holds; with a logarithm of the block size it is A163; uniformly in the block size it is B198 | [L*] (`zetaZeroWidth_le_iff_twoEndOdd_rate`); [A1] |
| — | Does continuation of a Weil floor by dilation reach `½log 3`? | no: `a_k<0.3621` | [L*] (`weilFloorApertureTower_lt_half_log_three`) |
| — | Is the certified sign selective? | yes: at aperture `181/500` the Liouville-twisted form is negative on an odd test | [L*] (`exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg`) |
| — | Do the sizes of the contacts, or the floor trees alone, bind a window? | no: weakened and twisted contacts hold two bound states; the trees have zero gap and zero curvature | [KR] `weakened-contact-binding`; [L*] (`dilationForm_le_of_no_gap`, `not_curvature_pos`) |
| — | Can the couplings be mixed areas or pairings of nef classes? | no: with nonnegative self-pairings `−N` has at least two positive squares; index `≤1` forces logarithmic self-pairings | [L*] (`two_le_hermNegIndex_neg_of_couplings`, `sum_selfPairing_ge_of_hermNegIndex_le_one`) |
| — | Is a positive uniform margin available? | no: it is incompatible with RH; a uniform lower margin is RH | [KR] `continuum-doob-margin`; [L*] (`riemannHypothesis_iff_neutralWindow_margin_bddBelow`) |
| — | Does the Liouville twist keep the sign beyond the trivial aperture? | no: at aperture `≥log log q+η` its system form is below `−K‖F‖²` | [L*] (`exists_not_floor`, `exists_systemForm_polar_neg`) |
| — | The group of one Jensen equation | the full signed-permutation group, or a rational relation among the normalized moments | [L*] (`jensenGal_full_or_exists_moment_relation`) |
| — | Is `3/16` improvable by inputs valid in weight `½`? | no | [L*] (`selberg_status`) |

## 2.3 Frankenstein routes

**No assembly closes RH.** One assembly is a theorem (`[X]`). Every other assembly has an open input of RH or AAL strength, a half-plane input, or returns an identity.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F48 | **The overlap recursion with a certified base.** Certificate at `181/500`; transfer to every block size; overlap law; prime-free middle; additive loss below the binding energy of the middle; margin and exponent receivers | RH ⇔ one operator inequality per step; a window of ratio `ρ` is `≈log₂log(ρ/2)+5` steps from the certified range; excesses with sum below `inf_Dμ_D` give RH [L*]/[D] | the conditional coupling (B194); the loss law (B195); A162 | the arithmetic of a step is two contact maps into the slivers of a universal prime-free matrix |
| F49 | **Certificates with transfer.** A fixed-aperture certificate; `groundEnergy_mul_nested_mass_le_packetForm_of_log_lt`; refinement monotonicity of the index | the sign at ratio `<e^{2A}` at every block size from one finite certificate [L*]/[D18] | A140; a certificate per aperture, because the dilation tower is frozen | the conclusions of B194 and B192 at a fixed ratio become just work; no mechanism and no loss law |
| F30 | **Two estimates, fully evaluated.** Frame, vertex of the budget, floor of the exponent models, coupled tower, barrier at every period, coherence, theta-square poles | `[X]`; room `[13/15,7/8]` inside the probe; `2/3` at square-root cancellation in the columns; frame `≥3/5` for every `6r`-periodic pairing [L*]/[KR]/[doc] | A118; B174, B185; B187 | the exact reach of the only producer class, and the three estimates that meet at its vertex |
| F29 | **One scale.** The receivers of §1.2 with `[X]` inserted | every graded receiver is one number; each has a level at `7/8` [D5] | A138, A163; a level below `7/8` | a proposed estimate is placed before work starts |
| F31 | **Half-plane, then line** | rung `κ<4/3`, returns `y^{1/8}` | a step from a strip to the line (B56, B148) | none: every transfer is RH |
| F39 | **The index at three scales.** Finite-scale neutral part, index law in the aperture, verification rate | RH ⇔ no crossing ⇔ the Hodge inequality on every window [L*] | B152 | one exact finite object per window |
| F46 | **Binding as mixing.** Doob chain, cut and share law, two-end binding, pole capacity | RH ⇔ gap of the Doob chain `≥` binding energy `−C`; gap `≤` binding `+c₀`; the trees alone do not mix [L*] | the Doob energy of the jets on waves at the common returns; B195 | the margin as a Poincaré constant |
| F45 | **The critical object.** Thresholds, energy branch, confinement limits, coercivity, compactness, closed domain, barriers | a failure of RH has a unique, outer, cyclic, stable extremal function with exponential bounds [F]/[L*]/[S] | B104; A158, A161 | the place where a contradiction on the Σ side has to act |
| F40 | **Models plus rigidity.** Two-sided edits, positive weights, signed weights, rigidity at any decay, defect energies, count laws | the door of world I: unit multiplicity with the reflection up to a decaying error, or a count below half the real part of the layer [D] | B170, B145, B191 | a proposed AAL argument is tested on the models before work starts |
| F41 | **World I off the scale.** Shell signs, floors at every length, non-attainment, tangent data | AAL from a sign that recurs [L*] | B170, B145, B173 | AAL needs a statement infinitely often, not always |
| F42 | **The lattice with a level.** Index law for number rings; ray class characters at their conductors; Artin Euler products as Hecke products; `[X]` | the zeros right of the line of an Artin Euler product are among the zeros and poles of finitely many ray class `L`-functions, each counted by a Weil index [D13] | A141; virtual configurations with orders | the index of every comb counts zeros in one strip |
| F47 | **The cover with a real structure.** Zero field, Jensen equations, heat cover, forward monodromy, conjugation | RH ⇔ one element of a group of finitely supported signed permutations is trivial at every positive real time [L*] | the real-time criterion itself; B197 | a sign-free exact form; no first lemma below RH |
| F37 | **Verification with a rate.** Height 67; transfers to Li, Hausdorff, heat grid, Jensen, window | finite statements with stated sizes; the window transfer for `a≥1` at double-exponential height [L*] | A1, A142 | none toward ratio three: the height is out of reach |
| F38 | **Mean values, correlations, cameras** | a positive proportion on the line; runs of five simple zeros; logarithmic Chowla; short-interval mean squares; adaptive isolation [F]/[L*] | A18; B59 | the in-law half is native |
| F11 | **Construct, then identify** | index-one approximants give RH [F] | B146, B171 | regulators are excluded |

**Closest to the open core:** F48 (the step of Σ in the form that survives the rank law, with a certified base at every block size), F30 (the producer at its vertex), F45 (the critical object), F40 (the door of world I).

### What a contradiction search may assume in world I
`Θ≤7/8` [X]; an isolated top `β≤7/8` of finitely many zeros; top-residue asymptotics of the Möbius and Liouville signals and of their Ramanujan twists [L*] (`tangentDatum_ramanujanTwist`); the level-one constant-vector sign fails on all late dyadic prime shells [L*] (`not_frequently_jasConstProductPositiveOn_shell_of_maximal_offLine`); at some depth bounding all zeros the spline trace attains its size on all late windows of every length [L*] (contrapositive of `asymptoticAbscissaLaw_of_windowNonAttainment`); every locally uniform limit of scalar-normalized phase returns joining the zero to `Re s>1` is zero [F] (BAG); a finite-`W` critical half-line state exists, unique, outer and cyclic [F]; a positive real branch time exists [L*]; an odd bound state above `½` exists [L*] (`riemannHypothesis_iff_no_odd_bound_state`). No contradiction comes from identities alone, from positivity (positive tempered configurations with deep zeros exist at every aperture [KR] `kr-crt`), from an Euler product over the rational primes with multiplicities `0,1,2` and a count rate, from the functional equation with Gamma factor, order and count, from the functional equation as a growth bound among positive weights, or from a statement in law [L*]/[KR] (§1.6).

## Validation tests for 2.4–2.8 and 2.21

| Test | Requirement |
|---|---|
| T1 | implied by RH (or GRH for the family at hand) and implying neither RH nor AAL; or a method question implied by nothing about ζ's zeros. A half-plane below `7/8` satisfies T1 |
| T2 | answered by proving or refuting a stated inequality, identity, existence or implication |
| T3 | a named consequence for either answer |
| T4 | not decided by a finite rung |
| T5 | false on a corpus model, or calibrated on the models |
| T6 | names an input not refuted in Lean |
| T7 | moves a wall; not a shape answered in Lean |
| T8 | not a named long-standing problem in disguise; a first step in corpus objects with one named obstacle |

**No statement about the zeros of ζ below RH and AAL passes all tests as a door to the line** [A]. Each section below names the conversion theorem, the first lemma, the objects, the yield and the calibration of its opening. The questions were checked against the corpus by sentence queries (log §13, §21, §22).

## 2.4 Breakthrough question below RH and below the half-plane `7/8`: the vertex of the probe (B174), then the long columns (B185)

**Verdict.** The one place in the corpus where a zero-free half-plane below the proved level follows from a single improved estimate with no change of method.

**Conversion.** The exponent budget of the probe is a set of Lean statements between exponents [L*]/[doc] (`FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex`): the low boundary `5/6+M/12−ℓ/6+(M+ℓ−1)₊/2` and the high exponent `endpointExponent` of each bin. Three estimates meet at the published geometry: the low bound, the row count of the bin `δ=79/204`, the dual length of the reflected rows. That bin sits at `−7/30672` (`endpoint_binding_bin`), and no geometry with low boundary `≤7/8−1/4000` passes it with the published count (`endpointExponent_pos_of_lowBoundary_le`). With the count `U^{1−δ}` in every bin the budget reaches `13/15` [doc]. The arithmetic estimates behind the exponents are the source of `[X]` [S]; the conversion to a statement on zeros is A118 with the row count as a parameter.

**Question (B174).** Is the number of nonprincipal rows of top length in the bin `δ=79/204` at full prime amplitude smaller than the published count by a fixed power?

- **First lemma.** The count in that one bin: a large-value estimate for the rows over the sextic twists at amplitude exponent `(1+δ)/2=283/408`.
- **Objects.** `rowCount`, `rowCountAt`, `endpointExponent`, `lowBoundary`; `eisenstein_largeSieve`, `eisenstein_farey_largeSieve` [L*].
- **Yield.** `Θ≤σ₀` with `13/15≤σ₀<7/8` for ζ, every Dirichlet `L`-function and the Hecke family; every receiver of §1.2 moves with it.
- **Calibration and kills.** The count moves by less than `10⁻⁴` for `κ=2β−1∈[11/15,3/4]`: iterating the theorem in the top `β` gains nothing [L*] (`rowCountAt_binding_ge`). Re-optimizing the geometry gains nothing: the published point is a vertex [L*]. Designs with two or more row variables have balanced low boundary `≥1`; rows of conductor exponent `κ` with frequencies of order `n` have corners `8/9`, `25/28`, `49/54` for `(κ,n)=(2,6),(3,4),(4,3)` [doc]. Below `13/15` the count is not the obstacle.

**Continuation (B185).** Below `13/15` the floor bin `δ=0` with the trivial count binds every geometry [doc]; crossing it needs a bilinear saving before Cauchy–Schwarz (`≥1/12` for the boundary `¾`, `≥1/3` for `½`, at `n=6`) [KR] `phase-blind-floor-gram`; a bound for the rows through the twists is no low estimate [doc]. The statement: a power saving in the first moment of the row root numbers against one fixed dual column, then uniformly in the column.

- **Known about the terms.** The row root number is the theta phase times a square; the average row is blind to the target; the short sextic Gram is diagonal; the theta-square series has a double pole at `4/3`; the rotated correlations see only the layers `m≥2` [L*] (§1.5).
- **First lemmas.** A148 (the layers `m=0,1` and the target component of a twisted column); A149 (the floor bin over `𝔽_q[T]`, where the columns are evaluated exactly).
- **Yield.** A half-plane in `(2/3,13/15)`.

**Tests.** T1 passes: estimates for counts and Gauss sums whose consequence is a half-plane below `7/8`. T2, T3, T6 pass. T4 passes: no verified height decides a half-plane. T5: B174 is calibrated on the count `U^{1−δ}` and on the iteration in `β`; B185 on the average row (target-free), the short columns (diagonal Gram) and the untwisted main term (a double pole). T7 moves Π160, Π175. T8: B174 is a large-value estimate for one family at one amplitude; the square-root form of B185 is a conjecture of Patterson type [C], and any power saving uniform in the column is the question.

## 2.5 Breakthrough question for the search for a producer: a pairing whose frame reaches the line (B187)

**Verdict.** The producer class of `[X]` is evaluated in full: every `6r`-periodic Gauss pairing has uncoupled boundary `2/3` and coupled fixed point `(4r−1)/(6r−1)≥3/5` [L*] (`gauss_pairing_6r_thresholds`). A producer for RH is a pairing outside the class. No candidate is in the corpus [A].

**Conversion.** Two estimates for a pairing give a half-plane [L*] (`zetaZeroAbscissa_le_of_two_estimates`, `heckeHalfPlane_of_family_corrected_signal`: conditional transfers); the frame of a pairing `(c,k)` is `c/(k−1)`.

**Question.** Is there a Möbius-signed pairing `(c,k)` with `c/(k−1)<3/5`; for the line, with `c≤(k−1)/2`?

- **Criteria, each from a kill.** (i) The sign is the Möbius sign; Gauss sums carry it at odd order: `g(χ)^n=−|F|` modulo `(μ−1)²` for odd `n>2` [L*] (`exists_gaussSum_pow_orderOf_eq_of_odd`). (ii) `c/(k−1)<3/5`. (iii) The rows have a completed reflection. (iv) The principal twists carry the target with full prime amplitude and the low estimate does not pass through the twists [doc]. (v) The continued correction has no zeros right of the target line: the correction of the cubic frame has infinitely many in `7/12≤Re s<2/3` [KR].
- **First lemma.** Finite algebra: the pairs `(c,k)` of the monomials in Gauss and Jacobi sums of odd order that equal the Möbius sign times a unit character; generators in Lean: `exists_gaussSum_pow_orderOf_eq_of_odd`, `exists_prod_jacobiSum_eq`, `exists_gaussSum_mul_gaussSum_eq`.
- **Yield.** Existence: a frame below `3/5`, and the two estimates for it as the next problem. Non-existence within the monomials: a barrier theorem for the whole class extending the `6r` family; the producer of RH is then not a Gauss-sum pairing.
- **Calibration.** The `6r` family (a theorem); even order (no sign); frequencies of order `n` with balanced floor `1−4/(5n)`; two or more row variables (`≥1`) [doc].

**Tests.** T1: a producer question, implied by nothing about ζ's zeros. T2: an existence statement or a classification theorem. T3 named. T4 passes. T5 calibrated. T6 passes. T7 moves Π174, Π177. T8: not a named problem; the first step is finite algebra in corpus objects.

## 2.6 The same question if positivity, Weil positivity and spectral methods are excluded

**Verdict.** The producer of `[X]` is already of this kind, with one input to examine. As located in its source [S] (statements read; log §22) the inputs are Gauss-sum identities, Cauchy–Schwarz, the large sieve over the Eisenstein integers, Hecke theta functions as Mellin pairs (`HeckeTheta.completed_functional_equation`), and the reflection of the rows through the automorphy of the cubic theta source at the cusps (`completedT_primeCuspRow_reflection`). The two estimates carry no sign condition [L*] (`zetaZeroAbscissa_le_of_two_estimates`).

**Questions under the exclusion.**
1. **B185** as in §2.4: a first moment of root numbers; its tools are reciprocity and completion.
2. **B180**: the reflection of the completed theta row without Eisenstein series: a derivation of the cusp automorphy from reciprocity and finite Fourier inversion alone. First lemma: the reflection of one cusp row of prime conductor. Yield: the frame is available for pairings whose row source is not a residue of an Eisenstein series, which every candidate for B187 outside the cubic cover needs.

**The other sign-free mechanisms and their reach.**
| Mechanism | Reach | Evidence |
|---|---|---|
| conjugation as a monodromy of the heat cover; `K_even⊆ℝ` | exact forms of RH; no door below RH; transitivity (B197) has no RH yield | [L*]; [KR] `zero-field-transitivity` |
| count laws and rigidity of the functional equation | world I only: they constrain fakes, not ζ (B191) | [L*] (§1.6) |
| Stepanov's method | Heilbronn sum `≤5p^{11/12}`; the degree bound on the actual prime windows is open | [F] (ALST) |
| ultrametric dominance | the Goss zeta function; no norm for ξ | [L*] (`gossZeta_riemannHypothesis`) |
| means and correlations | in law; no half-power rate | [F]; [L*] |

**The breakthrough question** is therefore §2.4 below the level and §2.5 for the line; B180 is the method question specific to this section. **Tests** as in §2.4 and §2.5; B180: T1 method, T2 an identity, T5 calibrated on the cubic row [S], T8 not a named problem.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**Verdict.** The horizon is a receiver with one rate, and the rate is imported from the prime side.

**What is proved.** Zeros `≤1−2δ` ⇔ the pulse decays at rate `δ`, `0<δ≤¼`; pulse rate = horocycle rate [L*]. `[X]` is the rate `1/16`; RH is the rate `¼` [D5]. Horocycle exponent `1−Θ/2`, Euler-filtered `1−Θ∞/2`; a mixed cuspidal/Hecke source sees every right resonance, a single eigenform can miss halving pairs [F]. Cuspidal and scattering channels differ, and the scattering spectrum alone supplies no estimate [KR] `kr-sel`. No exceptional eigenvalue below `3/16` on congruence subgroups, with a weight-`½` eigenfunction at `3/16` [L*] (`selberg_status`). Mayer scattering resonances in `0<Re s<½` are characterized by a determinant multiplicity, and the three-term relation holds for the convergent period function [L*] (`mayerResonanceMultiplicity_pos_iff`, `three_term_absolute`). The spectral side of a compact quotient [L*] and compact quaternionic quotients [S].

**Opening.** `X`: a ringdown rate `δ>1/16` from the horizon. Conversion: `zeroFreeStrip_iff_pulse_ringdown`. Yield: the half-plane `1−2δ<7/8`.

**Question (B188).** Which input of the horizon fails in weight `½` and bounds the scattering resonances?

- **Partial answer [A4].** The producer of `[X]` is a mechanism of this kind: its Möbius sign comes from Gauss sums of odd order and is absent on a double cover. Its reading on the horizon is not a declaration. [C]: the theta source of its rows is automorphic on a cubic cover of the Bianchi orbifold of `ℚ(√−3)`, where it is a residual eigenfunction below the continuous spectrum, the analogue of the weight-`½` theta function at `3/16`.
- **First lemmas.** (i) Ringdown ⇔ strip for the Hecke family over `ℚ(√−3)` on the Bianchi orbifold (A54 and the analogue of the modular statement; unverified). (ii) The weight-`½` calibration: the solution of the three-term equation with theta multiplier at the parameter of `3/16`, the model on which every horizon argument for a resonance-free strip has to fail. (iii) A120: the compact calibration, where the rate is a spectral gap.
- **Assessment [A].** No lemma toward a rate beyond `1/16` exists on the horizon side: gaps and mixing act on the cuspidal channel, and the scattering channel is ζ. Under this assumption the producing estimate is B174 read as a ringdown rate (§2.12).

**Tests.** T1 passes as a half-plane for `δ>1/16`. T2, T3, T4 pass. T5 calibrated by `selberg_status` and by the compact quotient. T6 passes. T7 moves Γ86. T8: cancellation in sums of Kloosterman sums over the modulus is a named conjecture [C]; the question asked is the weaker one, whether an input special to weight zero reaches a resonance.

## 2.8 If RH is a problem of topology or geometry

**Verdict.** A topological invariance argument is excluded by rigidity; the geometric steps available are on the critical state and on the dyadic window.

**Rigidity.** The index at an aperture is the number of crossings of the aperture conormals with the graph of Weil's operator [L*] (log §16). The full-positive cone of weights is `{Λ}` under RH and empty otherwise [KR] `kr-apw`; the Liouville twist is negative at aperture `181/500` [L*]. No deformation of the weights keeps the index: an invariance argument has no family to run along.

**Opening A (B104): the critical state.**
- **Conversion.** `riemannHypothesis_or_exists_exponentially_bounded_criticalState` [S]: RH, or a critical half-line ground state with `|F(u)|≤C_βe^{βu}`, `½<β<15/2`.
- **First lemma.** Identification of the localized critical state with the bounded Green solution: the forcing/domain bridge, the first-order cross terms, the collar-energy transfer [F].
- **Objects.** `windowThreshold`, `SoftLogarithmicHalfLineDomain`, `ClosedSoftLogarithmicHalfLineDomain`, the terminal-collar bound, the confinement limits.
- **Yield.** At the first step a boundary-value description of the object of a failure; exclusion of both cases (charged `R_polar<W`, polar-orthogonal `R_polar=W`) is RH on HF, SRT, AIP, SC.
- **Calibration.** Stability, a nonzero polar pairing, outerness and cyclicity hold on both sides of the charge question; `R→0` asymptotics do not settle `R→∞` [F].

**Opening B (B196): a realization, starting from the dyadic window.**
- **Conversion.** An index theorem on a realization of the couplings is the Hodge inequality of §1.1.
- **First lemma.** A geometry whose index theorem is `hermNegIndex_neutralWindow_dyadic`: the neutral part of `(D,2D]` has index exactly one at every block size, unconditionally [L*]; its entries are first and second differences of `n log n` and `log n` [D29].
- **Constraints on every realization [L*].** Self-pairings of size `−log m` per block; nonnegative self-pairings give two positive squares; refinement of blocks does not lower the index (`hermNegIndex_neutralWindow_le_refined`); the realization is rigid at `w=Λ` and fails for the sign twin.
- **Reading [C].** A symmetric matrix with nonpositive off-diagonal entries and one negative square is the Gram matrix of the walls of a convex polytope in hyperbolic space; this is an identity, not a door, and no declaration states it (log §13).
- **Yield.** At the first lemma a geometric proof of a theorem in Lean, which tests the language; with the contacts as correspondences and the overlap law as a gluing theorem, B196.

**Tests.** T1 passes for the first steps (method; under RH the critical state does not exist; the dyadic statement is unconditional). T2, T3, T4 pass. T5 calibrated on narrow windows, on the certified range and on the dyadic window. T6 passes. T7 moves Σ190, Σ191, Σ205. T8: not a named problem.

## 2.9 A new field for RH?

**Verdict [A].** No field is missing at the open core; one calculus is. The fields that the finite-scale picture calls for are built: MixingArithmeticOfTheFloorTrees (Doob chains, binding, cut laws, the overlap law, margin and exponent laws, zero gap and zero curvature of the trees), AbsoluteGeometryOfSpecZ (block matrix, Hodge inequality, index law, gluing kills, self-pairings), GaloisTheoryOfZeros (the heat cover). Not built is the analysis of the mediator of the overlap law: no declaration bounds the inverse of a dyadic neutral window, the conditional energies or the conditional coupling (log §13).

**The calculus: Green calculus of the prime-free window.**
- **What it would be like.** Potential theory on one universal family of matrices. The dyadic middle `(D,2D]` carries no contact [D20]: its neutral part is the archimedean matrix at block size `D` (potential, jets, degrees), the same for every window that contains it; its continuum limit is the prime-free form `W⁰` on an interval of length `log 2`. The primes enter a step only as boundary maps: the contacts `b↦⌊b/k⌋` of the two ends land in the slivers of the middle.
- **Objects.** `G_D`, `μ_D`, `φ_D`, `G₊`; the sliver blocks of `G_D`; the couplings `B` of the ends, jets to the near sliver and the contact of 2 to the far sliver [D12]; the conditional energies and the conditional coupling (`overlapLeftEnergy`, `overlapRightEnergy`, `overlapCoupling`); the excess of a step; the normal form of the one-prime range [D24].
- **Language.** Schur complements as Dirichlet-to-Neumann forms of the middle; composition of windows as composition of these forms; the bound-state channel `(Bφ_D)(Bφ_D)ᵀ/μ_D` against the positive channel `BG₊Bᵀ` [D21].
- **Questions.** (1) Two-sided bounds for the sliver blocks of `G_D`, uniform in `D`. (2) A lower bound for `μ_D` uniform in `D`. (3) The first step: `BG₊Bᵀ⪯N_e+(Bφ_D)(Bφ_D)ᵀ/μ_D` for `a≤3R/100`, `b≤3(R+a)/50`. (4) The excess of step `k` as a function of the ratio. (5) The Green kernel of `W⁰` on `[0,log 2]` in closed form.
- **Tools.** Haynsworth additivity (`hermNegIndex_fromBlocks_transpose`); negativity of the off-diagonal entries (`neutralBlock_neg_of_lt`) with Perron–Frobenius; interlacing; the certified floors as a priori bounds [D4], [D10]; the monotonicity of the shifted Schur complement [D22]; [C] the theory of symmetric matrices with nonpositive off-diagonal entries and one negative eigenvalue.
- **Mechanism.** The jets of an end reach the near sliver and its contact of 2 reaches the far sliver; the mediated coupling is the interference of the two through `G_D`. Under the Liouville twist the mixed jet–contact terms change sign [D30]: this is where a proof separates ζ from its sign twin.
- **Criteria.** C1 uniformity in the block size. C2 it reproves the certified range without the certificate, or bounds its own loss there. C3 it fails for the Liouville twist and for contact multipliers in `[−5/2,19/40]` [KR]. C4 it uses the full rank of the middle: rank-`r` models fail [L*]. C5 it produces an excess per step, not only a sign. C6 each step is checked against a certificate (A140).
- **Yield.** B194; B192 after four steps; with (4) the loss law B195.

**Not proposed as fields** (built, or answered): mixing of the floor trees; Hurwitz arithmetic of the heat cover; geometry of the self-pairings; curvature of the trees.

## 2.10 A new field for a proof or falsification of AAL

**Verdict [A].** The receiver side is built; the producer side of recurrent signs is not.

**What is proved [L*].** Three receivers need a statement infinitely often or on windows of bounded length: the level-one constant-vector sign on infinitely many dyadic prime shells; floors on windows of every length `(k+1)π/67` (one length has models); non-attainment on arbitrarily late windows of one length at every depth bounding the zeros. In world I the shell sign fails on all late shells. Models and the door: §1.6. No declaration: a theorem forcing recurrence of an off-line zero; a logarithmic mean of the shell statistic; a bound for the restricted prime-weighted cofactor sum (log §13, §22).

**The field: arithmetic of recurrent signs.**
- **What it would be like.** A theory of quadratic prime statistics on dyadic shells whose sign is forced infinitely often by the structure of ζ. A failure of AAL is the statement that one explicit quadratic statistic is negative on every late shell.
- **Objects.** `JasConstProductPositiveOn (jasPrimeWindow N (2N)) 1`; the spline trace on windows of bounded length; the tangent data of `μ` and `λ` and of their Ramanujan twists in world I; the restricted prime-weighted cofactor sum.
- **Questions.** (1) The explicit formula of a logarithmic mean of the shell statistic over `N` (an identity; unverified): the sum over pairs of zeros whose sign makes the shell sign recur. (2) B145. (3) B170, B173. (4) B191, as the calibration of what a proof may use.
- **Tools.** The theorems in law (twisted moments, short-interval mean squares of `λ` and `λχ`, logarithmic Chowla) as sources of means; the receivers convert a nonnegative mean of a sign into a recurrent sign.
- **Criteria.** C1 it fails for the two-sided edits and for a Selberg zeta function with a small eigenvalue (A120): it uses unit multiplicity with the reflection up to a decaying error, or the integer count [D]. C2 it needs the sign infinitely often only. C3 a mean of a size at the scale of the top layer is the top layer itself: the mean has to be a mean of a sign [A].
- **Falsification.** World I as listed in §2.3; a disproof of AAL is a disproof of RH with a finite top layer (§2.20).
- **Yield.** AAL: the exceptional coordinate (Γ68) closes and RH ⇔ ZAL.

## 2.11 A new field for RH without positivity and without spectral methods

**Verdict [A].** Sign-free fields are built: GaloisTheoryOfZeros (an exact form; no door below RH), WorldsOfTheZeroConfiguration and EulerFETransportTheory (models and rigidity; world I only), FamilyContinuationTheory with CoherenceTheoryOfReciprocityFamilies and SpectralTheoryOfTheCubicCover (the producer), SignFreePurityMechanisms (a norm for the Goss zeta function, none for ξ), ALST (Stepanov; the degree bound on the actual prime windows is open). One of them produces a pointwise theorem. Not built is the classification behind B187.

**The field: arithmetic of Möbius identities.**
- **What it would be like.** Finite algebra of monomials in Gauss and Jacobi sums: which monomials equal the Möbius sign times a unit character, and with which resonance norm `Q^{c−ks}`.
- **Objects.** Gauss sums of odd order and their Jacobi factors; the cube identity `γ₃³=με` of the normalized cubic Gauss sum; designs (number of row variables, order of the twists); the pair `(c,k)`, its uncoupled boundary and coupled fixed point; corners and floors of the exponent budget.
- **Questions.** (1) All Möbius identities among monomials of order `n`. (2) The map identity ↦ `(c,k)`. (3) Is `inf c/(k−1)` over the class equal to `3/5`? (4) Which identities have completed rows (B180). (5) Which have a correction without zeros right of the target line.
- **Tools.** `exists_gaussSum_pow_orderOf_eq_of_odd`, `exists_prod_jacobiSum_eq`, `exists_gaussSum_mul_gaussSum_eq`, `gauss_pairing_6r_thresholds`, the exponent plane and the vertex [L*]; the relations of Stickelberger and of Hasse and Davenport [C].
- **Mechanisms.** The sign from reciprocity, the size from the absolute values of the sums, the length from the period.
- **Criteria.** Those of §2.5.
- **Yield.** A pairing below `3/5`, or a barrier theorem for the class.

## 2.12 A new field for RH as AdS physics

**Verdict [A].** Built: BlackHoleRingdown, AHMH, ASH, CTH, RIT (ringdown ⇔ strip, the horocycle rate, Mayer resonances), CompactHyperbolicSurfaces, SpectralTheoryOfTheCubicCover. Not built: the horizon reading of the producer. The floor trees are not a holographic bulk: their generator has curvature exactly zero and no gap [L*], and no declaration identifies the window matrices with a horizon form (log §13).

**The field: ringdown of the cubic cover.**
- **What it would be like.** Quasinormal-mode theory on the Bianchi orbifold of `ℚ(√−3)` and its cubic cover, the setting in which the rows of the probe are automorphic [S]; `[X]` covers the Hecke family over `ℚ(√−3)`.
- **Objects.** The theta source and its cusp data (`completedT_primeCuspRow_reflection`); the Kubota multiplier (`kubota_mul`); the theta-square series (`thetaSqDirichlet_double_pole`); the pulse and its rate; Mayer resonances.
- **Questions.** (1) Ringdown ⇔ strip on the Bianchi orbifold (unverified). (2) The two estimates as a balance on the horizon: which physical quantity is the row count of the binding bin. (3) A rate `δ>1/16`, which is B174. (4) The weight-`½` calibration of §2.7. (5) B188.
- **Tools.** The receivers of §1.2; the exponent budget and its vertex; Hecke filters; A120.
- **Mechanism [A].** The bound state of the cover radiating into the scattering channel of the base, as the reading of the theta row against the twists.
- **Criteria.** C1 the mechanism is absent on double covers [A4]. C2 it gives a rate; visibility is proved and decay is not [F]. C3 it reproduces the rate `1/16`.
- **Yield.** No estimate by itself: a dictionary under which an improved count (B174) is a ringdown rate. Its only proof step is (1).

## 2.13 A new field for RH as topology or geometry

**Verdict [A].** Built: AbsoluteGeometryOfSpecZ (the Hodge inequality, the index law as a crossing number, the constraints on a realization), ArithmeticLorentzianGeometry (trickle-down from hyperbolic nonnegative links), HAT (the arithmetic clock; its Robin diagonal is not Weil's degree diagonal [F]), GaloisTheoryOfZeros (the cover). Not built: a realization (B196). The field below is the unbuilt part, with its first object fixed.

**The field: realization geometry of the windows.**
- **What it would be like.** A geometry in which the blocks of a window are classes, the couplings `−N(a,b)` are intersection numbers, the degrees `log((a+1)/a)` are intersections with a polarization, refinement of the blocks is an operation that does not lower the index, and an index theorem holds a priori.
- **First object.** The dyadic window: index exactly one at every block size, unconditionally; entries from differences of `n log n` [L*]/[D29]. The contacts are then correspondences along the floor maps with weights `Λ(k)/k`, and the overlap law is the gluing of two such geometries along their common dyadic part.
- **Questions.** (1) A realization of the dyadic window. (2) The contact of 2 as a correspondence on it; the certified range `ratio≤103/50` is the second calibration. (3) The gluing theorem: the contraction of the conditional coupling. (4) B149, B169.
- **Constraints [L*].** Logarithmic self-pairings; nonnegative self-pairings excluded; rigidity at `w=Λ`; failure for the sign twin; the index of a number ring is the number of right zeros of its zeta function plus one (`exists_le_negIndex_dedekind_sub_poleConfig_iff`).
- **Tools.** The self-pairing law; `weightedTrickleDown_of_links` (its links here have negative self-pairings); Haynsworth additivity as additivity of the signature; the Hodge inequality on positive packets without common blocks.
- **Language.** Hodge index, Castelnuovo–Severi, hyperbolic lattices; [C] polytopes of Vinberg type as a reading.
- **Criteria.** C1 an index theorem a priori, not a restatement. C2 unconditional on the dyadic window and on the certified range. C3 rigidity. C4 compatibility with refinement.
- **Yield.** B196, hence RH on ACS and HF; at the first object a geometric proof of a theorem in Lean.

## 2.14 A research programme to construct `𝔽₁`

**Programme.** AbsoluteGeometryOfSpecZ. The finite-scale picture restates the target: the surface `Spec ℤ × Spec ℤ` is needed only through its windows, each a lattice with the form `N` and the two degrees.

**State [L*].** The block matrix of degrees, potential, jets and floor maps; Weil's form on step packets as charges, a potential and a Dirichlet form; the Hodge inequality form of RH; one bound state at ratio `≤103/50`; the index law in the aperture; the gluing law through charges and its rank kills; weakened and twisted contacts; packet and dilate at ratio three; the self-pairing laws; power and critical combs; the index of number rings and of virtual configurations; ray class characters at their conductors [S].

**What a construction has to supply.**
| Piece | Counterpart at finite scale | Status |
|---|---|---|
| the surface over the dyadic window | the prime-free matrix of index one | index one [L*]; no geometry |
| Frobenius correspondences | the floor maps `b↦⌊b/k⌋` with weights `Λ(k)/k` | entries [L*]; no correspondence calculus |
| the index theorem | one bound state on every window | certified range [L*]; B152 |
| products and gluing | the overlap law through the dyadic middle | identity [L*]; contraction B194 |
| base change | number rings, ray class characters, Artin Euler products | index laws [L*]/[S]; A141 |
| a canonical height | the excess of an overlap step | [D22]; B169, B195 |

**Steps.** (1) A162. (2) A realization of the dyadic window (§2.13). (3) The one-prime range in normal form [D24]: one correspondence of degree two, the reflection of the slivers; the index at ratio below three, checked by A140. (4) The doubling `ρ↦ρ²/2` as an operation on the geometry, with the excess as its height (B169). (5) Base change (A141).

**Criteria.** Those of §2.13, and: the index of a number ring is its zero count plus one; the inequality is asserted only on positive packets without common blocks.

**Kills to respect [L*]/[KR].** Mixed areas and nef classes; gluing of fixed rank or through charges; weights other than `Λ`; a positive uniform margin; the shifted Bézout form (scaled comb Bézout ⇔ `ε=0`, RH and `c≥sup P_δ`).

**Assessment [A].** Every identity of the programme is an equivalent of RH; proof content enters at steps (3) and (4), through the Green calculus of §2.9.

## 2.15 A research programme to close the route WD

**Route.** Cofinal long-mollifier moments, or collision bounds → RH.

**State.** RH ⇔ the fixed-window `ζM_N` second moment is subpolynomial in `N`; a cofinal bound `O_θ(T^K)` with fixed `K` and unbounded `θ` suffices; sparse subpolynomial compact parity energy gives `K=3` [F]. Slope law: bounds `C_θT^{K+2βθ}` for arbitrarily large `θ` on unboundedly many heights give width `≤β`; dyadic law: a bound `O(T)` at length `T^θ`, `θ>½`, confines the high zeros to depth `<1/(2θ)+ε` [L*] (`zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope`, `eventual_depth_bound_of_dyadic_moebius_moment`). Proved: twisted second moments for `θ<½`; a positive critical proportion at `θ=13/50` [F]. Subcritical mollifiers have corridor defect `≥cV` and normalized moment `≥1+1/(8+6θ)` [KR] `subcritical-disc-corridor`, `kr-llm`.

**Grades [D28].** Length `θ` with bound `O(T)` improves on `[X]` exactly for `θ>4/3`; `θ→∞` with a `θ`-independent exponent is RH (B62).

**Steps.** (1) A18: lengths past `½` [C]. (2) The grades as Lean corollaries with `[X]` inserted (A138). (3) The structure of a moment of length `θ>1`: sums of `μ` against ζ on polynomials longer than the height; no estimate of the corpus enters this range. (4) The side entrances: depth density `o(T)` (B57); the pointwise prime cost of the adaptive cameras at their selected centres (B59).

**Kills.** Coefficient bounds, short weights and almost-everywhere corridor control leave finite and shallow exceptions [F]/[KR].

**Assessment [A].** The route closes only by B62. Its first grade below `7/8` starts at `θ>4/3`, beyond the lengths at which twisted moments are proved; the work available is (1) and (2). No proof step toward the line is identified on this route.

## 2.16 A research programme to close the route ACS

**Route.** The Hodge inequality on every window; a uniform lower margin; a bounded two-end family → RH.

**Closing statements [L*].** `riemannHypothesis_iff_forall_overlap_contraction`; `riemannHypothesis_iff_neutralWindow_margin_bddBelow` (the initial windows `(1,2M]` suffice); `riemannHypothesis_iff_twoEndOdd_bddBelow`.

**Steps.**
| Step | Content | Kind | Decision after the step |
|---|---|---|---|
| 1 | A162: the recursion with its shifted form and `μ_D` as Lean statements | just work | — |
| 2 | A163: exponent `3/8` at the matrices with `[X]` | just work (unverified) | the level of the matrices |
| 3 | sliver bounds for `G_D`; the first overlap step (B194) | open; archimedean analysis plus two contact maps | is the loss a factor or an additive excess |
| 4 | A140 at aperture `0.3762`, then above `½log 3` | just work (unverified) | the sign of steps 3 and 5 independently of their proof |
| 5 | steps two to four of the recursion: ratio three (B192) | open | the excess sequence at four ratios |
| 6 | the loss law (B195): `Σ_k e_k<inf_Dμ_D` | RH strength | proof, or a wall with a stated excess |
| 7 | B198; A141 | method; just work | — |

**Kills to respect.** §1.3.

**Assessment [A].** Steps 1, 2 and 4 are work. Step 3 is the first open step with a first lemma in corpus objects. If the excess of step 5 is not summable, the recursion needs input from the zeros and the open estimate of the route is B195 at RH strength.

## 2.17 A research programme to close the route ZCG

**Route.** Exclusion of positive-real-time heat collisions → RH; or ZAL with AAL → RH.

**State.** Both real-time criteria; the structure of the forward monodromy group; `Λ_dBN<1/8`; quadratic detection; the restart law; finiteness of non-real zeros at positive times [L*]; `Λ_dBN≤9/128` with `[X]` [D5]. At the time of ζ the real branch times accumulate at `0` unless zeros escape; `N(t)≤1` at times accumulating at `0` gives RH [F]. Uniformly bounded `N(t)` ⇔ finite off-line support; times `≥1/8` are closed [KR] `kr-cal`. Cameras isolate deep zeros [F].

**Steps.** (1) A160. (2) A138: `Λ_dBN≤9/128`. (3) A19 with A1: an explicit heat horizon. (4) B124, B24: finite initial depth budgets; collisions at small positive time. (5) B197 through fixed-time isolation estimates [D9]. (6) World I: B145, B170 (§2.10).

**Kills.** Size-only heat repairs [KR] `heat-method-floor`; forward control is not uniform as `τ→0` [F]; whole-group pair preservation is false [S]; complex-time collisions do not settle the real-time criterion [F]; Euler and count models and subpower mean-square defects of the functional equation cannot select ζ [KR].

**Assessment [A].** The descent branch has no first lemma below RH: (4) is of RH or half-plane strength, (5) has no RH yield. The branch with a proof-directed step is world I, where the target is AAL.

## 2.18 A research programme to close the route MC/JAS

**Route.** Half-power Möbius cancellation; level-one dressed positivity on large primes; signal cancellation at every `b>½` → RH.

**State.** `Θ≤b` ⇔ the reciprocal-ζ signal is `O(Z^{b′})` for every `b′>b`; an `O(Z^b)` bound gives large-prime dressed positivity at level `b+½+ε` [F]: level `11/8+ε` with `[X]` [D], against the target level `1`. The frame, the vertex, the tower and the barrier: §1.5.

**Steps.**
| Step | Content | Yield |
|---|---|---|
| 1 | A118 | `Θ≤7/8` verified |
| 2 | A138 | the level on every receiver |
| 3 | B174 | a half-plane in `[13/15,7/8)` |
| 4 | A148, A149, then B185 | a half-plane in `(2/3,13/15)` |
| 5 | B187 (with B180) | a frame below `3/5`; for the line a pairing with `c≤(k−1)/2` |
| 6 | B160 | RH |

**Kills.** The coherence kills of §1.5; logarithmic correlation decay gives no half-power rate; the bootstrap of the probe cannot pass `3/5` [F]/[KR].

**Assessment [A].** The only route with a theorem and a graded path. Within its class the path ends at `3/5`; the line needs step 5.

## 2.19 A research programme for a general Galois theory of the zeros

**State.** The zero field: `K_even⊆ℝ` ⇔ RH, no transitivity, maximal arithmetic quotient of rational rank one [KR]. Jensen equations: the full signed-permutation group or a rational relation among the moments [L*]. The heat cover: transport over forward times, homotopy invariance, finite support, generation by turns, independence of the base time, orbits = classes of simple joins, conjugation as an element, both real-time criteria [L*]. Off-centre collisions [S]. The Artin side: Brauer induction, reciprocity for linear characters, Artin Euler products as Hecke products, the index of ray class characters [L*]/[S].

**Objects and language.** The fibre of zeros of `H_τ` over the forward half-plane; branch times; turns and lassos; `forwardMonodromy`, `fibreConj`, `fibreNeg`; the fields `K_even` and the prime trace field; Jensen groups.

**Questions.**
1. B197: transitivity of `G₊`. A proof needs fixed-time isolation estimates along a path from any zero to a reference zero [D9].
2. Independence of the normalized moments: the Jensen groups are then full.
3. B190: orbits of a zero with irrational real part under the embeddings fixing the prime trace field.
4. Conjugation as a word in the turns at a positive real non-branch time: membership is proved, the word is not a declaration.
5. The classical side: the index of an Artin Euler product through virtual configurations with orders (A141).

**Criteria.** Sign-free and exact; it separates real times from complex times; calibrated on the polynomial heat flow and on the Jensen equations.

**Assessment [A].** RH is the triviality of one element at real times, and the group moves pairs: no restriction of the group gives RH. The word of question 4 is the list of real collisions, an identity. The theory yields structure (transitivity, identification of groups, finiteness of non-real zeros at positive times [D6]) and a language for the real-time criterion; it has no first lemma below RH.

## 2.20 A research programme under the assumption that RH is false

**Target.** A proof of the failure by a structural argument that names its object.

**Exact refutation certificates [L*].**
| Certificate | Evidence |
|---|---|
| a window with a positive eigenvector and `poleCapacity R J<−λ` | `not_riemannHypothesis_of_poleCapacity_lt` |
| a window with disjoint nonnegative packets violating the Hodge inequality, or a negative eigenvector with entries of both signs | `riemannHypothesis_iff_forall_wells_bound`, `riemannHypothesis_iff_forall_bound_state_one_sign` |
| a window `(R,2(R+a)+b]`, `R≥34`, whose conditional coupling is not a contraction | `riemannHypothesis_iff_forall_overlap_contraction` |
| an odd bound state above `½`; a defective hard-edge block | `riemannHypothesis_iff_no_odd_bound_state`, `not_riemannHypothesis_iff_exists_defective_hardEdge_block` |
| a positive real branch time of the heat cover | `riemannHypothesis_iff_forall_pos_not_mem_branchTimes` |
| a finite-`W` half-line ground state | [F] |

**Where a failure lives.** `½<Θ≤7/8` [X]; above height 67 [L*]; a window of aperture `a≥1` that fails has an off-line zero below a height `exp(exp(Ca))` [L*] (`exists_doubleExp_windowPositive`). It is world I or world II.

**Laws of a failure [L*].** With width `w>0`: the two-end family is not bounded below by `−Ce^{θv}` for any `θ<w`; `Λ_dBN≥δ²/(200 log γ)` at a zero of depth `δ` and height `γ≥e^{1600}`; the margin of the window matrices is unbounded; the loss of the overlap recursion squares along a sequence of scales [D3]; in world I the list of §2.3.

**Without computation.** A structural counterexample is an Ω-statement of polynomial size for the prime trace. No structure of the corpus forces one: an Euler product with a count rate, the functional equation with Gamma factor and count, and positivity are each realized with off-line zeros in models and are each compatible with their absence.

**Steps with proof content.** (1) A failure is world II: AAL (§2.10). (2) A failure has infinitely many off-line zeros: B13. (3) The converse of the pole-capacity certificate: does a failure of RH produce a window that binds beyond its pole capacity? It is not a declaration; the deficit `poleCapacity−μ` is then a reading of the zeros. (4) The dichotomy of the loss law (B195).

**Assessment [A].** There is no opening for a disproof: each certificate is a finite statement beyond every verified height, and no mechanism produces an Ω-result. The proof-directed content of the programme coincides with AAL and B13.

## 2.21 The one big question: does the prime 2 bind through the prime-free middle with a loss that iterates? (B194 → B192, with B195)

**Statement.** For every block size and every window `(R,2(R+a)+b]` with `a≤3R/100`, `b≤3(R+a)/50`:
1. prove `BG₊Bᵀ⪯N_e+(Bφ_D)(Bφ_D)ᵀ/μ_D` from two-sided bounds for the sliver blocks of the Green matrix of the dyadic middle;
2. record the excess of the step as a function of the ratio;
3. repeat at the ratios `2.25, 2.53, 3.21`: one bound state of `(R,3R]` at every block size.

**Why this one.**
- It is below RH, below AAL and below every half-plane: at each ratio it is a statement at one aperture, implied by RH.
- The conversion to RH is a Lean theorem: the same inequality at every step is RH; the loss law decides between a proof and a wall [D22], [D26].
- The mediator is universal and prime-free [D20]; the arithmetic of a step is two contact maps.
- The first lemma is unconditional archimedean analysis, and no declaration covers it (log §13).
- Every step has an independent check: a certificate at its aperture (A140).

**Yield.**
| Answer | Consequence |
|---|---|
| a structural proof with a summable excess below `inf_Dμ_D` | RH |
| a structural proof with a stated excess per step | B194 and B192; a template for every step; the excess function is the object of B195 |
| the sliver bounds do not give the step uniformly in the block size | the index at ratio three is a certificate statement (A140); the recursion is an identity and not a strategy |

**Calibration.** True on the certified range [L*]; false for the Liouville twist at aperture `181/500` and at every ratio `≥3` [L*]/[KR]; false for contact multipliers in `[−5/2,19/40]` at ratio `≥4` [KR]; not reachable by models of fixed rank [L*]; not reachable by the dilation tower [L*]; not reachable from the certified floors alone [D25].

**Tests.** T1 passes: at each ratio the statement is implied by RH and implies neither RH nor AAL; as a method question it asks for a proof through the middle. T2: an operator inequality on explicit matrices at every block size. T3: named for each answer. **T4 fails in the strict sense**: at each ratio the conclusion is decided by a finite certificate (A140); the question asks for the mechanism and its loss, which no certificate supplies. T5: calibrated as above. T6 passes. T7 moves Σ199, Σ188, Σ202. T8: not a named problem; the first step is in corpus objects and has one named obstacle, the sliver blocks of `G_D`.

### Alternatives considered
| Question | Why it is not the one |
|---|---|
| B174 | the cleanest statement below RH with a half-plane as yield; its room ends at `13/15` and it does not approach the line |
| B185 | needs an estimate that is not a square; its first lemmas are calibrations |
| B187 | of RH strength if a pairing exists; no candidate; the first step is a classification |
| A140 alone | reaches the sign at each fixed ratio; no mechanism and no loss law; the frozen tower shows that certificates do not continue |
| B104 | the first step is method; the exclusion is RH |
| B145, B170 | AAL; no first lemma in corpus objects |
| B188 | no lemma on the horizon side |
| B197 | no RH yield |
| B198 | uniformity in the block size is a count of deep zeros in unit intervals at the block frequency |

### Order of work [A]
1. A118, A138, A163: the level `7/8` verified and stated on every receiver, the matrices included.
2. A162: the recursion, its shifted form and `μ_D` as Lean statements.
3. The sliver bounds for `G_D` and the first overlap step (B194).
4. A140 at aperture `0.3762` and above `½log 3`: the independent check, and the conclusion of B192.
5. B174: the vertex of the probe.
6. The loss law (B195).

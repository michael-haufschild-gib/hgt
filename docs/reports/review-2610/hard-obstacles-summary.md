# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-26, corpus `8765b382d` with the working tree of that day, including `ExteriorAndHeightCoupledQuartetContractions` and `InfiniteDominantConfigurationsAreComplete`. This summary covers the 31 routes, 17 candidates, PW-B and the supporting programmes of the [complete report](hard-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, recorded in `logs/review-2610/working-log-v2.md`. Nothing was compiled. `[L]`, `[S]`, `[P]`, `[R]` as in the complete report.

## 0. The frontier in thirteen statements

1. **Multiplicative symmetry is hyperbolic exactly at the off-line zeros.** At a reflection pair `{ρ, 1 − ρ̄}` the Rosati local form has signature `(1, 1)`. Hecke operators, the archimedean flow and every gauge twist act on it by boosts iff `Re ρ ≠ 1/2`, and by rotations on the line. The successor acts unipotently; the functional equation acts by the reflection swap. Positivity of a carrier invariant under a boost forces isotropy. This is the common origin of every blindness, half-blindness and isotropy theorem in the corpus.
2. **Weil's argument transfers to `ℤ` up to its sign.** Over `ℤ` three layers hold for free, and also hold on the golden datum: the identities (L1), the theorem of the square for normalized graphs (L2) and the budget (L3). Kernel counts (L4) are blind to complex quartets, hence to every strip zero of `ζ`. What is missing is Rosati positivity (L5), equivalently the sufficiency of the free budget, and a base with fixed tensor loss (L6); each is RH.
3. **Hodge index splits into a local part that holds and a Lefschetz part that is RH.** At one prime, every test in `[−η, η]` is Weil positive for `η ≤ 3/10`. RH is the nonnegativity of Weil's form on the differences `g − T_{p^m} g`, equivalently a one-sided Weil inequality at one prime, equivalently at one fixed shift.
4. **Positivity on a carrier certifies blindness, half-blindness or isotropy, never forcing.** The only positivity beyond isotropy in the corpus lives on non-localizing carriers (aperture `≤ 3/10`) and holds for every prime weight.
5. **Multiplicative data and nonnegative tests cannot see the actual source.** Multiplicative observation is projection onto gauge orbits. The Möbius half-power law holds at Haar-almost every gauge point, and at `0` it is RH; the prime source is typical except for its pole. On nonnegative tests `ζ` is the worst member of its sign orbit, so positivity there transfers to every dominated twin.
6. **Every amplification over `ℤ` tested loses linearly.** Gauge moments, family averages, tensor products and relative powers gain on depth exactly as fast as they pay. Zero loss is flatness, which on a curve is unitarity. A rate needs a fixed tensor loss, and that is RH.
7. **No route has a rung between Vinogradov–Korobov and quasi-RH.** Each of these has a fixed strip as its first gain: graded receivers, Vaughan power improvements, admission at fixed damping, power growth of the damped receiver energy, one-sided Lefschetz bounds, multiplicative forcing.
8. **The invariants determine `ζ`, and a complex quartet can only be contracted against a real anchor.** The pole-budget-one completed positive class is exactly `ℝ^× · ζ`. Real off-line pairs contract to the line at no pole cost. A positive contraction removes a complex quartet only together with a real singularity at the same depth carrying at least twice its weight: Landau's theorem for polar sums [S, R]. That anchor is either a boundary pole (the pole tax), an existing real zero, or a collision of conjugate zeros. `ξ` has no real zeros, so inside the class of `ζ` every complex contraction pays pole budget.
9. **Collisions exist over `ℤ` one ordinate at a time, and there they reach only classical strength.** The height-coupled lift `ζ(s)² ζ(s+iγ) ζ(s−iγ)` collides the quartets at height `γ` onto the real axis [S]. It is the Rankin–Selberg square of the Eisenstein series at spectral parameter `γ/2` [R]. It contracts half of each lifted quartet at no pole cost; the Fejér barrier `a₁ < 2a₀` stops every harmonic coupling from removing the rest [R]. It pays a shifted Gamma factor of conductor `log γ`, and its budget is the classical local zero count at `2 + iγ` [R]. A collision of all conjugate pairs at once has no meromorphic carrier, because the differences of zero ordinates accumulate [R]. Over `𝔽_q` the same collision is free: `Λ²H¹` is finite-dimensional and lives on the surface.
10. **Pole order pays only for inserted zeros, budgets pay a hyperbolic pair only on a finite segment, and escape rank counts only the deepest zeros.** `ζ`'s own zeros are paid, if at all, by oscillation of the zero sum. The one oscillatory capacity found, the rank of an escape state, counts the zeros of maximal depth; a capacity uniform in the depth is what RH asserts.
11. **Positivity holds on average over short windows and at almost every zero ordinate.** To exclude an individual zero, the exceptional sets must lie below the zero spacing; a correspondence of length `L` resolves heights only at scale `1/L`.
12. **Escape is classified for every summable dominant configuration, and RH is the visibility of every escape state.**
    - Escape states are phase kernels whose rank is the number of dominant zeros: for finitely many dominant zeros and for power rows [L], for absolutely summable infinite configurations [S].
    - On them, dilation by `p` is the archimedean flow by `log p`, and horizon averages separate the zeros one by one.
    - For `ζ`, completeness is the explicit-formula split of one profile with Laplace form `G(s) = ζ(s)(1/ζ(s+ε) − Re(1/ζ(1+ε)))/s`.
    - RH holds iff every escape state has positive gauge mass [L].
13. **The archimedean–finite coupling never reaches the zeros as a positivity.**
    - Positivity on `ℚ_{>0}` splits into archimedean and Kronecker-null parts.
    - The successor sees continuous archimedean spectra but never atoms.
    - The extensions of Weil's correlation to `Aff(ℚ)` are a box of parameters over the critical zeros and add no constraint.
    - On escape states the coupling is exact, but it lives in a weight and a phase, not in a positivity.

## 1. Just work

Known mathematics suffices for each item, and none crosses a wall. An item's outcome may be unknown; what is known is the method.

| ID | Task | Concrete content | Completion criterion |
|---|---|---|---|
| **W1** | Selectivity battery | Test every mechanism against these models:<br>• pole-order-2 real pairs and refunded quartets as `CompletedPositiveSystem 2 1`;<br>• pole-order-3 and strip-pole quartets;<br>• over-regular Beurling systems;<br>• twisted boundary systems at `κ = 2r + 1`;<br>• the Siegel family `ζ(s)/ζ(s+1−β)`;<br>• double-pole, periodic-pole and half-zero boundary data;<br>• the Liouville twin, sign-flipped and dominated twins, Haar-typical twists;<br>• Hecke and Bost–Connes states;<br>• the golden datum and the complex fake (`q = 16`, roots `±8i, ±2i`);<br>• `Γ_ℝ^d` solutions; signed self-dual combinations;<br>• height-coupled lifts `HeightCoupledSystem (2κ) κ d γ` of all of these;<br>• white noise, reset-origin mixtures and translated-zero eigenstates.<br><br>Calibrations to reproduce:<br>• the `κ = 1` collapse to `ℝ^× · ζ`;<br>• `⌊k/2⌋` capacity;<br>• dlVP optimality and the Fejér barrier;<br>• the `2 : 1` real-anchor law;<br>• Weil for curves with budget `2g`;<br>• exterior-count purity over `𝔽_q`. | Each mechanism records which model defeats it, or that none does, and the local type of its correspondences at off-line pairs. |
| **W2** | Finite identities and certificates | Gram, Hausdorff, Hankel and Jensen blocks; finite heat transforms; schedules, histories and ledgers; finite Robin and Li checks; finite JAS and Vaughan budgets. | Every finite term certified; no cofinal claim. |
| **W3** | Premise checks | Regularity, support, decay, cutoff and domain membership for named tests and families (SZ limits, CHMD domains, candidate sources). | The hypotheses of an existing transfer are discharged. |
| **W4** | Transport of proved inputs | Width functor; RW↔SZ↔CHMD; HF→AIP; Weil margin → heat window; graded Sobolev floors. Restate four theorems in RW, SZ, CHMD, EWU, OWU, ACT, AIP and HF coordinates: the short-window averaged theorem, the off-line-field theorem, the zero-ordinate theorem, and the short-cycle local–global split. | Each conclusion stated at its true strength. |
| **W5** | Certified extensions and constants | Push the pointwise windows beyond `3/10`, `181/500` and `(log 2 + 1/50)/2`. Make `κ₀, C₀, Γ₀`, `sharpCollarConst κ`, `R₀` and `T(λ)` explicit. Compare the κ = 1 collar with dlVP. | Certified finite-aperture theorems. |
| **W6** | Short windows to the classical range | Selberg's near-line density holds on windows `T^{1/2+ε}` [R]. Replace `Γ^{99/100}` by `Γ^{1/2+ε}` in four theorems (averaged, off-line-field, zero-ordinate, positive-measure) and in WL's filtered deficit. | The four theorems on `Γ^{1/2+ε} ≤ H ≤ Γ/8`. |
| **W7** | Corollary assembly | (i) An averaged bounded-energy statement for WL, from the high-zero tail and the filtered deficit.<br>(ii) One rate dictionary for RW, SRT and ACS through `groundRate = polarRate`.<br>(iii) The explicit LA/WD residual region `{|t| ≤ T(λ), λ ≤ λ₀}`.<br>(iv) ACS effectivity as exhaustion: Bézout on the full cone ⇔ blind ideal = ⊤ ⇔ RH.<br>(v) Replace the imported `c/(log|t|)^9` collar in the harmonic module by the MPG dlVP calibration or the SBWF κ = 1 collar.<br>(vi) The conservation identity for infinite reflection-antisymmetric corrections, refunds included.<br>(vii) One capacity law: boundary `2Σm ≤ k`, collar `2Σ ord ≤ κ`, gauge `2Σm ≤ κ`, family `Σm ≤ k`.<br>(viii) The energy-rate law of the damped receiver, `limsup log E_ε(T)/log T = max(0, 2(Θ − ε) − 1)` for all but countably many `ε`. One direction comes from the energy–holomorphy theorem behind `riemannZeta_sub_eq_zero_of_energy_growth`; the other from the classical bound `1/ζ(s) = O(|t|^δ)` in a zero-free half-plane.<br>(ix) One theorem: escape completeness ⇔ the explicit-formula split. It combines the translation Gram, the Laplace form, the phase-kernel classification (finite, power rows, countable), the finite-rank decomposition and the gauge-mass criterion. | Each statement proved from existing theorems. |
| **W8** | The first gauge-charged window | Compute `inf W_{flip}(F)/∫F²` over odd real `C²` tests `F` supported in `[−181/500, 181/500]`. Here `flip` is `Λ` with `Λ(2)` replaced by `−log 2`, which is the Liouville twist on this window. The certificate `re_weilFullFunctional_liouvilleTwist_odd_window` decides every test with `Re(k_F(log 2) + k_F(−log 2)) ≥ 0`. The remaining tests form a finite-aperture eigenvalue problem, to be closed by an explicit negative witness or by a kernel-checked certificate (as for PA order 24). Then find the twin's minimal failure aperture from full-cone selection. | A theorem: either the odd window separates `ζ` from its twin, or it does not, with the least separating aperture. |
| **W9** | Depth homogeneity, remaining classes | The loss law for harmonic twists `n^{−ikt}`, for `k`-level forms and for Følner coupling, each with its positive survivor. Gauge moments, products and finite family averages are proved. | One theorem per class. |
| **W10** | Range-limited growth inputs | State the corpus VK step (`vk_dlvp_contradiction`) as a `δ`-range instance of `exclusion_iff`. | The VK region as an instance of the growth-to-forcing law, with its barrier. |
| **W11** | Closing the contraction calculus | (i) The least pole tax for complex quartets with `1/4 < a < 1/2` (`1` or `2`), from the real-anchor law with the boundary pole as anchor.<br>(ii) A minimum-tax theorem for every finite rational multiplier; the frontier records none.<br>(iii) The Fejér barrier for coupled contraction: for every nonnegative cosine polynomial `P` with nonnegative coefficients, the harmonic lift `Π_k F(s ± ikγ)^{a_k/2}` never removes the whole lifted divisor of a deepest quartet. Its anchors have weight `a₁m < 2a₀m`, and the full deepest-line divisor has scale weight `2m cos θ · P(θ)`, which changes sign.<br>(iv) Non-meromorphy of a global collision: no nonzero meromorphic function near `s = 1/2` vanishes at every conjugate pair sum `1/2 + i(γ_j − γ_k)`, since `N(T+1) − N(T) → ∞`.<br>(v) The height-coupled budget for `ζ`, stated as the Hadamard count at `2` and `2 + iγ`. | The contraction calculus closed: each statement in Lean, each a calibration rather than an exclusion. |
| **W12** | Integration of working sources | `ExteriorAndHeightCoupledQuartetContractions`, `InfiniteDominantConfigurationsAreComplete`, the wide-window prime channel, the cross-block and prime-channel boundary tools. | Each statement at its stated strength in an umbrella. |

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

Each is equivalent to RH or stronger. Solving one closes every route that uses its receiver.

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Any one of: bounded critical deficit energy; a one-sided lag or Abel moment; the history floor; the regularized abscissa `1/2`; the JAS half-power budget; Mertens at square root; the late-lag sign. Gauge forms: typicality of the gauge point `0` for `μ`; for `Λ`, square-root cancellation at `0` after subtraction of the pole. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Any one of: cofinal admission as `ε ↓ 0`; subpower receiver energy at every damping; positive gauge mass of every actual escape state at every damping; signed control of the long-modulus quadrature; a Báez–Duarte residual → 0; exclusion of fixed-origin cofactor escape at every damping. | PM, CTF, BVI, MC, PW-B |
| **B1.3** | **Complete Weil positivity; the Lefschetz part.** All apertures with Gamma, both polar terms and one shared budget. Equivalent forms:<br>• the one-sided Weil inequality for `T_{p^m}` on short cycles at one prime;<br>• `Re W(T_v g, g) ≤ W(g, g)` at one shift;<br>• sufficiency of the free budget (both normalized graphs of `1 ± T` effective);<br>• Rosati positivity (L5);<br>• the nodal inequality; positive Suzuki first variation; odd capacity;<br>• the one-shift reflected collar; global allocation; the `O(L)` ceiling;<br>• Bézout on the exact source cone. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS, SRT |
| **B1.4** | **Selection.** Pass from short-window averages and almost every zero ordinate, for nonnegative tests of bounded shape, to every height, every signed test and every aperture. At `A ≍ log Γ` an exceptional set must lie below the zero spacing, and a localizing correspondence must have length `≳ log Γ`. | WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign.** Any one of: coefficient positivity on the residual heat region; all-rank Hankel positivity at one time; both literal heat grids; rank-uniform Schur decay; the Newton interior margin; order-uniform passivity. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization.** Exhaust the maximal blind ideal with an input outside the exhausted classes.<br><br>Exhausted classes:<br>• invariant (hence hyperbolic) quadratic positivity;<br>• non-localizing positivity;<br>• positivity on nonnegative tests;<br>• finite, coupled or height-coupled multiplicative certificates;<br>• one-variable contractions and harmonic couplings;<br>• linear rigidity in the coefficient measure;<br>• pole order;<br>• gauge-invariant data;<br>• kernel counts.<br><br>The input must:<br>• localize at off-line pairs;<br>• carry a non-hyperbolic local symmetry or an independent polarization there;<br>• use sign-changing (gauge-charged) data.<br><br>Faces: Ward cap vanishing; the sub-unit trace residual; renewal boundary orientation; source effectivity; a section count; a stabilization weld; pre-divisor compactness; a descending potential; a centred Ising limit; a lossless nonlocal port; a certificate stream. | TG, RN, WD, ACS, all candidates, PW-B |
| **B1.7** | **Single-currency endpoints.** Any one of: cofinal contrast equality (BSY); the subexponential Li floor; the eventual Robin tail; recurrence near possible zeros; the global index `D < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **RH with simple zeros.** A faithful positive Meyer degree; RR for the Hilbert–Schmidt reserve; exhaustion of the bounded-orbit carrier. | ACS/Meyer faithful branch |
| **B1.9** | **Fixed tensor loss (the base).** One exponent `L` with `|c(t)|^k ≤ C_k e^{Lt}` for every `k`, for the spline orbit correlation. Equivalently: a sublinear loss law for a zero-forced family; for the one-prime Lefschetz sequence, `|c_m| ≤ c_0`. It cannot come from multiplicative data, family averages, moments or products. | HF, SRT, ACS, AOG |
| **B1.10** | **Rigidity of the height-coupled class.** `HeightCoupledSystem 2 1 1 γ = ℝ^× · ζ_γ` for every `γ`, where `ζ_γ = ζ(s)² ζ(s+iγ) ζ(s−iγ)` [R]. A complex quartet of `ζ` at height `γ` contracts inside this class at no pole cost and produces a second member, so rigidity at `γ` excludes every off-line zero at height `γ`; rigidity at every `γ` is RH or stronger. | ACS, SBWF, ACP |

### 2.2 Tier B2: classical open problems weaker than RH

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | Quasi-RH: a fixed zero-free strip. | The first rung of: every graded cancellation receiver; admission at fixed damping; power growth of the receiver energy; one-sided Lefschetz bounds; multiplicative forcing. |
| **B2.2** | Finite off-line index. | HF/AOG index exit; WD collision masses. |
| **B2.3** | Simplicity of the zeros. | Operator-norm faithful realizations (B1.8). |
| **B2.4** | Density hypothesis; large values beyond Guth–Maynard. | Averaged positivity at larger aperture; the filtered deficit. |
| **B2.5** | At least `3/4` of the zeros on the critical line. | TTPC: signed coalescent surplus `β ≤ 1/18` at the gauge point `0`. |
| **B2.6** | Power-saving sign correlations of `μ`, `λ` (Chowla/Elliott with rates). | MC anti-alignment; SSA constants; BVI rows. |
| **B2.7** | Hardy–Littlewood prime-pair correlations uniform near the square-root band. | TTPC surplus; near-incidence beyond the threshold. |
| **B2.8** | Subconvexity and growth near `Re s = 1`. | KKL horizon; the growth input `G`, the only source of interior gain for multiplicative positivity. |
| **B2.9** | Better de Bruijn–Newman upper bounds. | Shrinks the B1.5 region; corpus has `Λ < 1/8`. |
| **B2.10** | Near-line zero density on windows shorter than `T^{1/2}`. | Averaged positivity on windows `Γ^θ`, `θ < 1/2` (B3.7). |

### 2.3 Tier B3: open problems isolated by this research

No solution is known, and none is proved RH-equivalent.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | Physical-`L²` rate equality `polarRate = Δ`. | `Δ ≤ polarRate = groundRate ≤ 1/2`; form-norm rates equal `Δ`; bounded local off-line depth suffices. |
| **B3.2** | **Escape completeness for `ζ`: the explicit-formula split.** Three parts:<br>(a) Does the cofactor profile split into a dominant configuration of translated zeros plus a remainder of subdominant energy, via a contour shift of `G(s)e^{su}` past the translated zeros?<br>(b) Are the residues of that configuration summable?<br>(c) When the real parts of the zeros accumulate at a supremum that no zero attains, are the escape states limits of translated-zero characters? | Proved:<br>• escape states of finite and power-row configurations are phase kernels of rank the number of dominant zeros [L];<br>• the same for absolutely summable configurations, by Bohr uniqueness [S];<br>• remainders of subdominant energy are invisible [L];<br>• horizon averages are diagonal [L]; dilation is the archimedean flow [L];<br>• rank-one and nonresonant finite-rank escape rows are translated zeros [L].<br><br>(a) needs growth bounds for `1/ζ(s+ε)` on horizontal segments between zeros. This is the input of the explicit formula for `M(x)`, which the standard literature proves under RH with simple zeros [R]. Completeness classifies escape; it does not exclude it. |
| **B3.3** | Quantitative coercivity of residual/trace reconstruction in the receiver norm. | Algebraic injectivity; kernel `ℝ q_ε`; cofactor-graph closedness ⇔ a uniform estimate. |
| **B3.5** | **A section count on the correspondence surface.** An `h⁰` on normalized graphs of the scaling surface that is nonnegative, grows with the class, satisfies Riemann–Roch proved without the sign, and extends the base theta `h⁰`. | Have: the base `h⁰` with RR and Mellin; normalized graphs with degree `δ/2` and the theorem of the square.<br>Fail: Boolean counts and finite readings cannot pay; positive majorants give Bézout without RR. |
| **B3.6** | Signed shell flux along the moving prime-threshold ladder. | Birth jumps vanish; collar bound; frozen finite families fail. |
| **B3.7** | Averaged positivity on windows `H = Γ^θ` below the classical range. | Proved at `θ = 99/100`; `θ > 1/2` is W6; below needs B2.10. |
| **B3.8** | A nonlocal shared-budget calculus; quantitative cofinal two-tower saving. | Frustration and descent laws exact; the Rosati trace form is one budget, frustration its negative index. |
| **B3.9** | Arithmetic input on the residual heat region; source-selective cofactor repair. | Model geometry complete; no universal positive multiplier. |
| **B3.10** | Compatible oriented families; quantitative global-index bounds. | Common-endpoint classification; spline-orbit index ≤ 1 ⇔ RH. |
| **B3.11** | Sub-half-damping signed control of the size-cutoff forward interior. | Exterior paid; `ε = 1/2` bounded for every squarefree support. |
| **B3.12** | Order-uniform PA thresholds; decoupling rank from time (TH, HCF). | Fixed-order thresholds; coupled windows. |
| **B3.13** | Sharp successor constants: complex floor in `[−1/2, −1/3]`; zero-defect signs beyond conductor 3. | Odd shifts `1/3`, lag 2 `1/4`, exact; zero-defect signs have `f(2) = −1`. |
| **B3.16** | Is the paid ideal of `μ_ε` nonzero on escape? | A positive answer excludes white noise, not the translated-zero states. |
| **B3.18** | Equality case of collar capacity: a completed positive system with even `κ` and collar zeros of total multiplicity `κ/2`. | Odd `κ = 2r + 1` sharp. |
| **B3.20** | Signed near-coincidence cancellation at one height beyond aperture `½ log Γ`. | Single-height phase-selective law; near-incidence is gauge charge. |
| **B3.24** | **The gauge point beyond the threshold.** An unconditional estimate, better than the trivial bound, for a gauge-charged statistic of `μ` or `Λ` at the point `0` beyond the square-root threshold. | Haar-typical twists meet every budget; the Möbius boundary separates the Liouville twin at PNT strength; the prime source is atypical only by its pole. |
| **B3.25** | **Elliptic localization.** One of two outcomes:<br>• a localizing arithmetic carrier — one that isolates an off-line reflection pair — whose positivity is unconditional and whose local symmetry there is not hyperbolic;<br>• a theorem that every localizing positive arithmetic carrier is isotropic at off-line pairs. | Multiplicative correspondences are boosts off the line, and separating isometries are boosts. Non-localizing positivity is source-blind. Coupled point-stable carriers are isotropic. The successor is unipotent. |
| **B3.26** | **The gauge-charged window ladder.** Beyond W8: do Weil-positivity certificates through the first `k` primes separate `ζ` from its sign twins, with margins that survive as the aperture grows against the `e^A` cost of the off-line field? | Prime-free windows (`< log 2`) are weight-blind. The odd `181/500` window reads only the atom `2`. Full-cone selection makes every single-atom perturbation fail at some aperture. |
| **B3.27** | **An arithmetic exterior count.** A positive structure that collides each complex quartet of `ζ` into a real off-line pair at no conductor cost, with a nonnegativity proved by counting. Over `𝔽_q` this is the role of kernel counts on `Λ^k H¹`. | Over `𝔽_q`, exterior counts force unitarity in every genus, and `CurveDatum.exterior` is functorial [S].<br><br>Over `ℤ`:<br>• the zero-indexed exterior divisor contracts at `Δκ = 0` for `a < 1/4` [S];<br>• ordinate-local collisions exist (height coupling) [S], with conductor `log γ` and Fejér-limited anchors [R];<br>• no meromorphic object collides all conjugate pairs [R].<br><br>The open case is a non-meromorphic, two-variable structure on the correspondence surface. |
| **B3.28** | **The Rankin–Selberg field.** Identify the polar data of the actual source `Λ ⋆ Λ`, with Gamma and polar terms and infinitely many zeros, with the field `E_j = Σ_{k≠j} m_k/(z_j − z_k)`. Does a positivity of that source constrain `Re E_j` at the deepest off-line zero? | Finite polar sources: `Re E_j = 0` on critical configurations, `> 0` at the deepest off-line point with its reflection. The height-coupled lift is the Rankin–Selberg square of an Eisenstein series, and its positivity is Rankin–Selberg positivity [R]. |
| **B3.29** | **The regular part of the successor.** Quantify the successor defect `D_Λ` in the strip: the near-incidence information that the unipotent successor carries. | `D_Λ` holomorphic on `Re s > 0` with `|D_Λ(s)| ≤ |s| |ζ'/ζ(1 + Re s)|`; principal parts of `−ζ'/ζ` unchanged. |
| **B3.30** | **An arithmetic Stepanov method.** Auxiliary sections over `ℤ` whose forced vanishing bounds a spectral count. | Sparse Hecke annihilators need a lattice and never kill an off-line symbol; a characteristic-zero shifted-subgroup Stepanov lemma exists in `HTGeometry`. |
| **B3.31** | **Probes of coupled rigidity.** Either form is weaker than B1.10:<br>• rigidity of `HeightCoupledSystem 2 1 1 γ` at an ordinate `γ` where `ζ` has no zero;<br>• rigidity of its members with an Euler product.<br><br>Equivalently: a degree-four Hamburger theorem with coefficient positivity and shifted poles, without twists. | Degree one is settled: the κ = 1 class is `ℝ^× · ζ`, by positive-measure Hamburger rigidity.<br><br>The neighbouring class `HeightCoupledSystem 1 0 1 γ` contains the completed `L(s, π × π̃)` of every level-one Maass form with spectral parameter `γ/2` [R]. So rigidity must use the shifted poles.<br><br>A proof at zero-free ordinates that does not use the zeros would prove B1.10. |

### 2.4 Settled questions

- **The theorem of the square over `ℤ`.** Normalized graphs of the correspondence ring obey it, unique modulo fibres, with degree half the defect. It holds on the golden datum and carries no budget. The Hecke scale map obeys none, because scale addition is not ring addition.
- **The budget over `ℤ`.** Free, by the similitude law; its sufficiency at every scale is RH.
- **Positivity beyond isotropy.** It exists on non-localizing carriers, for every prime weight. On localizing multiplicative carriers it is impossible, by hyperbolicity, and the successor forces nothing. What remains open is B3.25.
- **The base at receiver level.** Fixed tensor loss ⇔ RH; linear loss ⇔ the strip.
- **Successor coupling.** No successor prescription couples to Weil's correlation; the extensions of Weil's correlation are a box over the critical zeros. Arithmetic successors and archimedean dilations live in different regularity classes. The successor reads exactly the continuous part of an archimedean dilation spectrum and never its atoms. Whether singular continuous spectra are seen is a side question.
- **The κ = 1 class.** `CompletedPositiveSystem 1 d` is `ℝ^× · ζ`.
- **Zero-tax complex contraction.** A positive finite polar ratio contracting a deepest complex quartet needs a real anchor at the same depth of at least twice its weight; the pure quartet ratio is never positive [S]. The κ = 1 class has no real anchors. Every known complex contraction of `ζ`'s quartets therefore pays pole budget or leaves the class.
- **Height coupling.** It contracts the quartets at one ordinate at no pole cost inside `HeightCoupledSystem (2κ) κ d γ` and eliminates every real off-critical zero of the coupled system [S]. It removes at most half of each lifted quartet. Its budget bounds their multiplicity by `(3/8) log γ + O(1)`, the classical local count [R]. It excludes nothing.
- **Lefschetz receivers.** One prime suffices for one-sided bounds; short cycles suffice; one shift suffices; the local part on short cycles holds.
- **Amplification by family averages and moments.** Linear loss; zero loss iff flatness.
- **Escape in model configurations.** The cofactor Gram is a translation Gram of one profile with Laplace form `G(s)`. Rank-one and finite-rank escape rows are translated zeros. Escape states of every summable dominant configuration are phase kernels of rank the number of zeros. RH ⇔ every escape state has positive gauge mass.
- **Also settled:**
  - spectral synthesis in the blind ideal;
  - coupled scale positivity on point-stable carriers;
  - short-window selection at `Γ^{99/100}`;
  - translated zeros as escape eigenstates on finite windows;
  - depth homogeneity for moments, products and family averages;
  - bare-FE and stable theta rigidity;
  - collar sparsity `⌊κ/2⌋`;
  - the absolute pole-order budget (false);
  - interior multiplicative forcing beyond growth input (excluded);
  - completeness of `ζ`'s invariants.

## 3. The three questions to answer next

**Selection criteria.**

1. The question is weaker than RH, so it can be answered.
2. Either answer changes the frontier: a positive answer adds a mechanism; a negative answer is a sharp no-go naming the missing input.
3. Together the questions cover the three walls, each in its own currency.
4. The question respects the exhaustion map: it does not reduce to a mapped class.
5. The question addresses one of the three conditions a `ζ`-specific positivity must meet (localization; a local symmetry that is not hyperbolic, or an independent polarization; sign-changing data), or the missing layer L5 of Weil's argument.

**Calibration that orders the questions.**

- **How Weil wins over `𝔽_q`.** Frobenius polynomials localize at an impure eigenvalue pair and act there hyperbolically, exactly as Hecke polynomials do over `ℤ`. Weil still wins, because Rosati positivity holds on the whole correspondence ring for an independent reason: a polarization from Riemann–Roch on `C × C`. Hyperbolic localization then turns that positivity into the vanishing of the off-line pair.
- **What `ℤ` lacks.** Every unconditional positivity found over `ℤ` is a consequence of invariance, and therefore isotropic. A forcing law needs a positive structure that is not a consequence of invariance. Two sources are conceivable: a localizer whose local symmetry is not hyperbolic (Q1), or a polarization from counting (Q3). Q2 asks whether any unconditional positivity of `ζ` can carry gauge charge at all.
- **One variable is exhausted.** The contraction and collision results close the one-variable alternative. Completed positive systems, their contractions and their harmonic couplings obey Landau's theorem and the Fejér barrier. The quartet obstruction moves into conductor `log γ`, and the budget returns the classical local zero count. Over `𝔽_q` the collision that removes complex quartets happens in `Λ²H¹`, inside the cohomology of the surface. The counting question Q3 therefore has to be asked on the correspondence surface, not on a one-variable object.

### Q1. Elliptic localization: can an arithmetic carrier isolate an off-line pair without acting on it hyperbolically?

> *Is there an arithmetic operation that isolates one off-line reflection pair `{ρ, 1 − ρ̄}`, on a carrier where Weil's form is unconditionally positive, while its local symmetry at that pair is elliptic (a rotation or the reflection swap) rather than a boost? Or is every localizing positive arithmetic carrier generated by correspondences that are hyperbolic at off-line pairs, hence isotropic there?*

- **Why.**
  - Positivity constrains a fibre only where the carrier localizes.
  - In the corpus, localization comes from polynomials in Hecke operators (Lagrange interpolation on separating symbols). Hecke operators are boosts exactly at off-line pairs, so positivity on such carriers is isotropy.
  - Non-localizing positivity (aperture `≤ 3/10`) has full fibres and holds for every prime weight.
  - Elliptic isometries cannot separate the two points of a pair, because separation is hyperbolic. An elliptic localizer must therefore be non-isometric: an arithmetic operation that changes the local form while respecting the reflection.
- **Ingredients to test.**
  - The functional equation (the reflection swap) combined with a non-isometric arithmetic operation.
  - Poisson and Sonin self-dualities of the archimedean place.
  - The Rankin–Selberg source, whose polar data at a zero are the field of the other zeros (B3.28).
  - The regular part `D_Λ` of the successor (B3.29).
  - Affine correspondences, which have genus zero and act unipotently.
- **Selectivity test.**
  - Fail on the `CompletedPositiveSystem 2 1` models and their height-coupled lifts, the complex fake and the Liouville twin.
  - Reproduce coupled isotropy for multiplicative carriers.
  - State the length of the localizing operation: a separation at distance `δ` costs `≳ 1/(Lδ)`.
- **Outcomes.**
  - *Yes:* the first unconditional positivity that is neither invariant-induced isotropy nor non-localizing, and a forcing input for B1.6 (B3.25).
  - *No:* a universal hyperbolicity theorem. Quadratic positivity is closed as a forcing mechanism over `ℤ`, and a proof must come from counting (Q3) or from rates (U1).

### Q2. Where does unconditional Weil positivity first become gauge charged?

> *For which aperture and which tests does an unconditional Weil-positivity theorem for `ζ` fail for a gauge twin of `ζ` (a sign flip of prime-power atoms, the Liouville twist)? First instance: does the odd window `[−181/500, 181/500]`, which reads only the atom at `2`, separate `ζ` from the twist with `Λ(2)` replaced by `−log 2`? Then: do window certificates through the first `k` primes keep a gauge-charged margin as the aperture grows?*

- **Why.** Every unconditional positivity theorem of the corpus is gauge blind:
  - prime-free windows hold for every weight;
  - positivity on nonnegative tests holds for every dominated twin;
  - carrier positivity is isotropic;
  - averaged positivity is shared by Haar-typical twists.

  A `ζ`-specific sign must live on sign-changing atoms.
- **What is known about the first window.**
  - Below `log 3` the Weil functional reads only the atom at `2`.
  - The certificate holds for every weight with `w(2) = log 2`.
  - For the Liouville twist it is undecided exactly on odd tests with negative correlation at `log 2`.
  - Full-cone selection makes every perturbation of `Λ` at a prime-power atom fail Weil positivity at some finite aperture. So each twin has a finite failure aperture; the question is whether certified positivity of `ζ` reaches it.
- **Route.**
  1. W8: a finite-aperture eigenvalue problem with a certified answer.
  2. The minimal failure aperture of each twin, compared with W5's certified windows for `ζ`.
  3. The scaling of the gauge-charged margin against the `4(A+1)²e^A N² Φ` cost of the off-line field (B3.26).
- **Outcomes.**
  - *Separation at `181/500`:* the first unconditional positivity theorem true for `ζ` and false for a gauge twin, and a calibration point for criterion (iii) of §1.1 of the complete report.
  - *No separation there:* the sign of the first prime is invisible at that aperture. The least separating aperture, and the number of primes it reads, become the measured threshold at which positivity starts to see arithmetic.
  - *Margins that survive growth:* a gauge-charged positivity ladder, the first route into B1.3 that is not gauge blind.
  - *Margins that collapse like `e^{−A}`:* a sharp no-go locating gauge charge beyond bounded apertures.

### Q3. A section count on the correspondence surface

> *Is there a section count `h⁰` on the normalized graphs of the scaling surface of `ℤ` that is nonnegative, grows with the class, extends the base theta `h⁰`, and satisfies Riemann–Roch with a proof that does not use the sign of Weil's form?*

- **Why.**
  - Over `𝔽_q`, Rosati positivity (L5) comes from counting. Riemann–Roch on `C × C` makes a class with positive self-intersection and positive degree effective, and the Hodge index follows.
  - Over `ℤ`, layers L1–L3 are free, so L5 is the whole difficulty.
  - The corpus has every piece of the counting argument except the count:
    - exact source RR as an identity;
    - normalized graphs with degree `δ/2` and the theorem of the square;
    - a base theta `h⁰` with RR and Mellin transform to `ξ`.
  - What fails is the dimension:
    - Boolean section counts (`h⁰ ≤ 1`) cannot pay unbounded fibre intersection;
    - finite readings cannot supply Bézout;
    - positive majorants give Bézout without RR.
  - The contraction and collision results add a negative calibration. Every counting device confined to one variable reduces to Landau positivity, the Fejér barrier and classical local zero counts. Over `𝔽_q` the device that sees complex quartets, `Λ²H¹`, is part of the cohomology of the surface. The count must therefore be two-variable.
- **Weaker-than-RH content.** Three separate statements: nonnegativity of `h⁰`; the RR inequality; vanishing on classes of negative degree. Only their conjunction gives the Hodge index. Each alone is a theorem about a construction, not about the zeros.
- **Calibration.**
  - Reproduce Weil for curves with budget `2g`.
  - On the golden datum and the complex fake, the count must exist and RR must hold while the vanishing statement fails.
  - Reproduce the base theta RR.
  - The exterior part of the count must see complex quartets, as `Λ²H¹` does, without the ordinate-dependent conductor of the height-coupled lifts.
- **Outcomes.**
  - *Yes:* L5 reduces to a vanishing statement on the correspondence surface, an ampleness question with a counting meaning. The arithmetic exterior count (B3.27) becomes the count on its exterior part.
  - *No:* a theorem that every section count on normalized graphs with RR is RH-equivalent, closing Weil's counting route over `ℤ` in this form.

The three questions are the forcing problem in each wall's currency:
- Q1: what positivity can see after localization (Wall 3 face 3.18; Wall 14 face 14.17).
- Q2: whether positivity can carry the arithmetic sign at the gauge point (Wall 1 faces 1.3 and 1.18).
- Q3: whether the missing layer of Weil's argument has a counting construction, and where its exterior part lives (Wall 14 faces 14.4, 14.18 and 14.20).

**Considered and not chosen.**
- **Rigidity of the height-coupled class (B1.10) and its probes (B3.31).** This is the one new closing statement the contraction calculus exposed. It lies in the invariant-rigidity currency, where the corpus has its one unconditional rigidity theorem at this level: the κ = 1 collapse. It fails criterion 1 at ordinates with zeros. At zero-free ordinates it is a degree-four Hamburger problem that cannot reach the zeros unless its proof ignores them, in which case it is B1.10.
- **The explicit-formula split (B3.2).** An analytic input of classical type. Completeness classifies escape states and excludes none; RH remains the positivity of the gauge mass.
- **The arithmetic exterior count (B3.27).** Over `ℤ` a one-variable exterior square is either ordinate-local and classical, or not meromorphic. What remains is part of Q3.
- **The Rankin–Selberg field (B3.28).** An ingredient for Q1.
- **Selection below the zero spacing (B1.4)** is RH-strength; **the gauge point beyond the threshold (B3.24)** is Chowla-strength.

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows that a new field is necessary. The corpus has a complete map of the known forcing mechanisms, each with a sharp limit, and it knows which layer of Weil's argument is missing over `ℤ`:

- **Invariant quadratic positivity certifies blindness, half-blindness or isotropy,** because every multiplicative correspondence is hyperbolic at an off-line pair. Non-localizing positivity has full fibres and is source-blind.
- **One-variable positivity is Landau–Fejér positivity [R].**
  - Multiplicative positivity forces the boundary and its capacity, and nothing more without growth input.
  - Completed systems reach collars of width `1/log T`, and at `κ = 1` the class is `ℝ^× · ζ`.
  - Contractions need a real anchor of twice the weight at the deepest line (Landau); harmonic couplings supply anchors of less than twice the pole weight (Fejér).
  - The height-coupled budget is the classical Hadamard count at `2 + iγ`.
- **Linear rigidity determines `ζ` but does not see zeros.** Zero location is nonlinear in the coefficient measure.
- **Pole order pays only inserted zeros.** Real pairs contract for free; complex quartets cost pole budget or conductor.
- **Multiplicative data see only gauge orbits; nonnegative tests see only the size of the source.**
- **Amplification over `ℤ` loses linearly:** moments, family averages, tensor products, relative powers.
- **Averaging over heights selects windows, not zeros;** a correspondence resolves heights only at the inverse of its length.
- **The successor never reaches the zeros:** it is unipotent on their polar fibres and sees only continuous archimedean spectra.
- **Escape is a classification, not a forcing.** Escape states of dominant configurations are phase kernels; RH is the positivity of their gauge mass.
- **Weil's argument transfers except for its sign.** Identities, the theorem of the square and the budget are free over `ℤ`; kernel counts are blind to complex quartets; Rosati positivity, the sufficiency of the budget and a fixed tensor loss are each RH.

The missing ingredient is a **polarization of the correspondence surface of `Spec ℤ`**. That is a positive structure on the Hecke–archimedean correspondences with three properties: its positivity is a theorem about the structure (counting, or a non-hyperbolic localizing symmetry), not a consequence of invariance; it sees the sign of prime-power atoms; and its exterior part collides conjugate zeros without an ordinate-dependent conductor. Over `𝔽_q` this is supplied by Riemann–Roch and an ample class on `C × C`, with `Λ²H¹` inside its cohomology. Over number fields no existing theory supplies it:
- arithmetic intersection theory works on arithmetic surfaces fibred over `Spec ℤ`, not on a square of `Spec ℤ`;
- the scaling-site geometry has a Riemann–Roch on its base, while its Hodge index on the square is equivalent to RH;
- one-variable positive objects, the subject of the contraction calculus, are exhausted at classical strength.

A new field is therefore likely required [R].

### 4.2 The field: arithmetic polarization

The corpus holds three parts of it:
- **Arithmetic Positive Duality** is the rigidity and capacity theory of positive Poisson pairs, with MPG as its boundary side and SBWF as its strip side.
- **Arithmetic Correlation Geometry** supplies the symmetry: the gauge torus, its charged and invariant statistics, the loss law, and the gauge mass of escape states.
- **Arithmetic Correspondence Positivity** supplies the correspondences: normalized graphs, the budget, determinant and Rosati degrees, local types at reflection pairs, the layer map of Weil's argument, the contraction and collision calculus, and the escape-state classification.

What none has is the object that makes Weil's positivity a theorem: a polarization, with sections to count, on a genuinely two-variable object. The field the B-tier points to is their extension by that object, here called **arithmetic polarization** [R].

- **Phenomena to explain.**
  - Why the positivity of the explicit formula pairs a zero with its reflection `1 − ρ̄` (Rosati, elliptic, the functional equation), rather than with its conjugate (determinants) or its dilates (hyperbolic).
  - Why `ζ` carries no off-line charge, while its gauge twins, its dominated twins and its pole-order-two relaxations can.
  - Why every positivity built from multiplicative invariance is isotropic.
  - Why the collision of conjugate zeros is free over `𝔽_q` but costs conductor over `ℤ`.
- **Scope.** Positive structures on the correspondence surface of `Spec ℤ` and the correspondences acting on it:
  - dilations: gauge invariant, hyperbolic off the line;
  - affine maps and the successor: gauge charged, unipotent;
  - the archimedean flow: hyperbolic;
  - the reflection: elliptic.

  For each structure: its sections, degrees, exterior parts, polarizations and localizing operations; its capacity for intrinsic charge; its selectivity against twins and relaxations.

### 4.3 Criteria the field must meet

| Criterion | Test against the corpus |
|---|---|
| **Selectivity** | Distinguishes `ζ` from the whole battery W1:<br>• `CompletedPositiveSystem 2 1` pairs and quartets, and their height-coupled lifts;<br>• pole-order-3 and strip-pole quartets;<br>• over-regular Beurling systems;<br>• the Siegel family;<br>• twisted boundary systems;<br>• the golden datum and the complex fake;<br>• `Γ_ℝ^d` solutions;<br>• signed self-dual combinations;<br>• dominated and flipped twins.<br><br>Survives every single-node perturbation `Λ + δ·δ_m`. |
| **Gauge charge** | Separates the gauge point `0` from its twins. Uses sign-changing atoms, the archimedean pole or additive structure. Fails on the Liouville twin. |
| **Localization** | Isolates a reflection pair; states the length of its localizing operation. |
| **Local type** | Its positivity is not a consequence of invariance under a symmetry that is hyperbolic at off-line pairs: either its localizer is elliptic, or its positivity comes from counting. |
| **Reflection pairing** | Pairs `ρ` with `1 − ρ̄` (Rosati traces), not `ρ` with `ρ̄` (determinants); sees complex quartets. |
| **Two variables** | Its exterior part collides conjugate zeros at every ordinate at once, at a cost independent of the ordinate. One-variable constructions reduce to Landau's theorem, the Fejér barrier and classical local counts. |
| **Counting origin** | Positivity is a dimension or a cardinality, with a Riemann–Roch identity proved without the sign. |
| **Sublinear loss** | Contains a term that does not scale with its amplification; loses nothing to gauge or family Jensen. |
| **Joint use of invariants** | Uses coefficient positivity, the FE, the simple pole and strip holomorphy together; each proper subset has countermodels. |
| **Sees more than pole order** | Reaches intrinsic charge. Reproduces the conservation identity as its relative case, the free contraction of real pairs, and the `2 : 1` real-anchor law. |
| **Non-circularity** | No interface field or premise contains the conclusion. Objects are constructed before their sign. Zero-free-region transfers are not forcing. |
| **Uniformity** | Tails paid in a graph topology. Aperture, height, rank, damping and window controlled together. Exceptional sets below the zero spacing where individual zeros are concerned. |
| **Calibration** | Reproduces:<br>• Weil for curves with budget `2g` and an ample class;<br>• exterior-count purity;<br>• the theorem of the square in genus one;<br>• boundary forcing and `⌊k/2⌋` capacity;<br>• dlVP optimality and the Fejér barrier;<br>• the κ = 1 collapse and `5d < 9κ`;<br>• the height-coupled budget as the classical local count;<br>• positive-measure rigidity;<br>• the Kronecker split. |
| **New partial results** | Results that are not zero-free strips:<br>• an elliptic localizer or a universal hyperbolicity theorem (Q1);<br>• a gauge-charged positivity (Q2);<br>• a section count with Riemann–Roch (Q3);<br>• a collision without conductor (B3.27);<br>• rigidity of a coupled class (B3.31);<br>• a capacity bound for an infinite class of systems not built by deformation. |

### 4.4 Questions it must answer

1. **What is the polarization?** Which class on the correspondence surface of `Spec ℤ` plays the ample divisor, so that the Rosati trace `τ(ξ ξ')` is positive for a reason other than RH?
2. **What counts sections?** Which `h⁰` on normalized graphs is a genuine dimension with Riemann–Roch (Q3)?
3. **Which localizer is not hyperbolic?** Which non-isometric arithmetic operation isolates a reflection pair with an elliptic local symmetry (Q1)?
4. **Where is the gauge charge?** At which aperture and on which atoms does positivity first separate `ζ` from its twins (Q2)?
5. **What is the exterior square of the spectrum?** Which two-variable structure collides `ρ` with `ρ̄` at every ordinate at once? Its one-variable shadows are the height-coupled lifts, each of which collides one ordinate and pays its conductor (B3.27).
6. **Is a coupled class rigid?** Does `HeightCoupledSystem 2 1 1 γ` contain only `ℝ^× · ζ_γ`, and which invariant would prove it (B1.10, B3.31)?
7. **What pays `ζ`'s own zeros?** A budget pays a hyperbolic pair only on a finite segment, and the escape rank counts only the deepest zeros. Which positive structure measures oscillatory payment uniformly in the depth?
8. **How does the archimedean place enter?** The prime source is atypical only by its pole, and collisions cost a shifted Gamma factor. How does a polarization see the pole and the Gamma factor?
9. **What are escape states of `ζ`?** The explicit-formula split of one profile (B3.2), and an arithmetic reason for their gauge mass.
10. **How does an average become a point?** Which selection principle reaches below the zero spacing with a correspondence of length `≳ log T`?
11. **What is the base?** Which structure has a tensor loss independent of the power?

### 4.5 Tools it would develop

**Built:**
- the Fejér-tent pairing; Hamburger rigidity and its stability;
- lattice and `ℚ_{>0}` Bochner; the Kronecker decomposition; induction from subgroups; sign characters;
- the quantum budget; the critical-jet topology and synthesis; the coupling matrix;
- gauge Jensen and family Jensen; ratio energy and the near-incidence form;
- normalized graphs and the similitude law; determinant and Rosati degrees; exterior counts and the exterior functor over `𝔽_q`;
- the local form with its boost and isometry laws; the resolution law;
- the zero-contraction calculus with the real-anchor law;
- height-coupled systems and their budget;
- the translation-Gram and Laplace forms of the cofactor; phase kernels, Bohr uniqueness and the horizon law for escape states; the gauge mass.

**Not yet built:**
- **Section theory on the correspondence surface.** `h⁰` of normalized graphs; Riemann–Roch; vanishing in negative degree; the extension of the base theta `h⁰`.
- **Polarizations.** Ample-type classes for the Hecke–archimedean correspondence ring; Rosati positivity from ampleness.
- **Elliptic localization.** Non-isometric, reflection-compatible operations that isolate a reflection pair; their positivity laws.
- **Gauge-charged positivity certificates.** Weil-positivity certificates that read sign-changing atoms, with margins as a function of aperture.
- **Arithmetic exterior powers.** A two-variable exterior structure whose collisions cost no conductor, with counts; the height-coupled lifts as its one-variable restrictions.
- **Rigidity in higher degree.** Hamburger-type theorems for positive systems with shifted poles and Gamma factors, without twists.
- **Oscillatory capacity.** A positive structure whose integer counts intrinsic charge uniformly in the depth, keeping dominated and oscillatory payment apart.
- **Escape-state analysis of `ζ`.** The explicit-formula split through the Laplace form `G`.
- **Selection lemmas** at the zero-spacing scale.
- **An arithmetic Stepanov method**: auxiliary sections whose forced vanishing bounds spectral counts.

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | • **The correspondence surface of `Spec ℤ`:** scaling surface; Hecke ring with Rosati involution; normalized graphs; the archimedean flow; affine maps and the successor; the functional-equation reflection.<br>• **Local and global positive structures:** reflection pairs with their local forms; polarizations, section counts and exterior parts; arithmetic Poisson pairs.<br>• **Positive systems:** completed positive systems graded by pole order and degree; height-coupled systems as their one-variable couplings.<br>• **Boundaries and gauge:** boundary divisors and capacities; the gauge torus, gauge orbits and the gauge point `0`; dominated and sign-flipped twins.<br>• **Receivers and carriers:** Lefschetz sequences and short cycles; carriers (blind, half-blind, left-blind, isotropic, non-localizing).<br>• **Escape:** cofactor profiles with their Laplace forms; escape states as phase kernels with gauge mass.<br>• **Bases:** coefficient systems over a base.<br>• **Candidate two-variable carrier [R]:** the continuous spectrum of the modular surface. Its Eisenstein family has Rankin–Selberg squares equal to the height-coupled lifts of `ζ`. The corpus has Eisenstein continuation infrastructure but no study of this carrier. A positivity there must avoid the indefinite form that the reflection pair already shows. |
| **Language** | It must distinguish:<br>• equality, receiver equivalence and directional transfer;<br>• source and receiver;<br>• gauge-invariant and gauge-charged;<br>• the orbit and the point;<br>• hyperbolic, elliptic and unipotent;<br>• localizing and non-localizing;<br>• determinant and Rosati trace;<br>• budget and sufficiency;<br>• local part and Lefschetz part;<br>• blind, half-blind and isotropic;<br>• inserted and intrinsic zeros;<br>• pole tax, real anchor and collision;<br>• one-variable and two-variable;<br>• dominated and oscillatory payment;<br>• boundary and collar capacity;<br>• linear and sublinear loss;<br>• nonnegative and sign-changing atoms;<br>• classification and exclusion;<br>• averages, almost-every statements and individual zeros. |
| **Mechanisms to discover** | • A **polarization law**: positivity of the Rosati trace from a section count.<br>• An **elliptic localization law**: positivity on a carrier that isolates a reflection pair with a non-hyperbolic symmetry.<br>• A **charged positivity law**: Weil positivity that reads the sign of prime-power atoms with a margin that survives aperture growth.<br>• A **collision law**: an exterior structure that collides conjugate zeros at every ordinate without conductor.<br>• A **capacity law for oscillation**: a bound on `ζ`'s own interior zero charge, uniform in the depth.<br>• A **visibility law** for escape: an arithmetic reason for positive gauge mass.<br>• A **base law**: a fixed loss over a base, removed by tensor roots. |
| **First milestones** | (1) W8: the first gauge-charged window, then its ladder (Q2).<br>(2) An elliptic localizer or a universal hyperbolicity theorem (Q1).<br>(3) A section count on normalized graphs with Riemann–Roch, or a no-go (Q3).<br>(4) W11: the closed contraction calculus, including the Fejér barrier for couplings.<br>(5) W9: the loss law for the remaining amplification classes.<br>(6) The explicit-formula split of the cofactor profile (B3.2).<br>(7) A probe of coupled rigidity (B3.31). |

Each milestone is a theorem of a type the corpus does not contain: a polarization, an elliptic localizer, a charged positivity, a collision law or a rigidity law, rather than a blindness or receiver statement. Each standard adds its own requirements:
- **APD:** name the positive side, the spectral side, the gap and the integer.
- **ACG:** name the gauge charge.
- **ACP:** name the layer of Weil's argument, the local type of the correspondences at off-line pairs, and whether the carrier localizes.

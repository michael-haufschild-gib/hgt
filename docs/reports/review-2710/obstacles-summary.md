# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-27, corpus `3fd844e5f` with working tree. This summary covers the 31 routes, 17 candidates, PW-B and the supporting programmes of the [complete report](route-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, recorded in `logs/review-2710-v5-research-log.md`. Nothing was compiled. Labels `[L]`, `[S]`, `[P]`, `[R]` and notation (overlap ratio `K = w/δ_N`, constants `c₀`, `c₁`, `c_full`, local Euler constant `γ_p`, tower deficit `d_p`) as in the complete report.

## 0. The frontier in twenty-two statements

1. **`ζ` has a computed positive form and a computed equivariant form; RH says they are one form.** `W` is Hecke equivariant with finitely many negative directions; the collided form `D` is positive, faithful, the logarithmic Sobolev norm, computed without zero indexing; `Re W = D − Δ`.
2. **The equivariance defect of `D` is a moment of inertia, and every uniform bound on it is a strip** [L/S].
3. **In Lorentzian language RH is hyperbolicity.** Every finite Gram of the scaling surface has at most one positive square iff RH; for Metzler forms with positive row sums and connected support, one positive square is the trickle-down inequality `Q − QD^{−1}Q ≤ 0` [S].
4. **Over `𝔽_q` the content of Weil's theorem is trickle-down.** Bézout makes the Frobenius Gram Metzler; every curve datum is in the trickle-down regime; the golden fake datum is Metzler and connected and fails `(TD_π)` [S].
5. **Over `ℤ` there is no conformal symmetry.** Frobenius acts conformally with factor `q`; Hecke maps are isometries (boosts on the pole plane, factor one); power maps and the successor are not conformal [S].
6. **The archimedean place pays the prime place, and the pole, while atoms are separated.** The self-energy of an atom is exactly `log(1/w) + O(1)`; tilted Schur rows pay the archimedean cross kernel; `M ≥ 0` up to overlap ratio `c₀` for every `N`; `Re W ≥ ‖F‖²` on all independent-profile sections at a smaller fixed fraction, with no pole constraint [L].
7. **Separated positivity is universal.** The same law holds for every real twist `|ω| ≤ 1`, multiplicative or not, and every bump: the separated regime reads nothing arithmetic [L].
8. **`ζ` is the ground state of its gauge orbit.** On `|·|`-closed families every twist dominates `ζ` (diamagnetic inequality); a margin in `ζ`'s favour must come from the pole, signed bumps or overlap [L].
9. **Unbounded overlap is RH.** At every fixed width the atomic spline Grams are positive iff RH; their largest negative index is the number of distinct right zeros [L]. Only bounded overlap is left between a theorem and RH.
10. **The gauge enters through non-ratio lags.** They vanish below the spacing and appear from overlap ratio `≈ 4` (a pair within `4δ_N` of `log 2`) [L].
11. **At the spacing the zeros sample the atomic Dirichlet polynomials at the Nyquist rate.** Below it they oversample, beyond it they undersample; on the line every zero term is a square [L].
12. **The sign hypothesis of Lorentzian theory is a gauge fixing.** At level `N` the coupled atomic kernel of a twin `χ` is entrywise nonnegative in some gauge iff `χ(p) = 1` for every prime `p ≤ N` (`χ(p) = p^{iτ}` with the shifted archimedean kernel); the archimedean kernel fixes the gauge along the successor [S].
13. **No local Lorentzian structure; a blind global closure.** A prime ladder carries two positive squares; the archimedean jump form is a Laplacian; the Euler-product closure is Lorentzian for every nonnegative local datum [S].
14. **The horizon is a covariant regulator with local finite parts.** On `p`-adic classes the counterterm is the tensor product `Σ_j δ_j^{−1}ℓ_j²`, exactly `[p]`-covariant; the finite part is the tower form with local Euler constant `γ_p`; uniform profiles give `−2γ` [S].
15. **The finite part has a one-number sign law per prime.** `F_p + c|·|² ≥ 0` at every depth iff `c ≥ 2d_p`; the prime place pays its own classes for `p ≥ 2^16` (numerically from `47`) and leaves a deficit `2d_p` at the small primes [S].
16. **Divergences cannot select.** Polar matching reads only the density of the gauge: `+1` for `ζ` and every finite-flip twin, `−1` for Liouville [S].
17. **The zero side has a closed quantum.** RH iff `𝓔 ≤ 2` iff the damped source work is cofinally `≤ 2`; every finite Weil index is strictly below the energy and eventually below the work [S].
18. **Short prime polynomials rarely align at zero ordinates, and counting never excludes a zero** [L]; outside the strip a deep zero forces anti-alignment [L].
19. **One currency carries every graded reading** (escaped Möbius decay, receiver rate, `Θ`, Hecke caps, dyadic growth, `Re ξ′/ξ`, prefix readings); unconditionally only VK rates [L].
20. **Statistics improve and exclude nothing.** Simple critical zeros `> 67.250071%`, `≥ 4/5` of ordinates critical, `3/4` of copies within `4/log T` [L].
21. **Unconditional positivity separates `ζ` from the first sign twins on finite windows**, permanently from `23/40` for Liouville [L]; no margin law on growing windows.
22. **Every positive mechanism stops at a threshold [R].** Overlap ratio `c₀`, the Metzler stability regime, the conductor horizon, the Nyquist diagonal `N ≍ T`, the tower deficit at small primes, half damping, certified apertures, VK: below each, positivity is proved and blind; at each, the open problem begins.

## 1. Just work

Known mathematics suffices; none crosses a wall. An item's outcome may be unknown; the method is known.

| ID | Task | Content | Completion criterion |
|---|---|---|---|
| **W1** | Selectivity battery | Test each mechanism against relaxations, the golden datum (Metzler, fails `(TD_π)`), complex fake, sign, Liouville, finite-flip and dominated twins, adversarial non-multiplicative bounded twists, `|·|`-closed and signed families, theta fibres, square-class kernels, regulated forms of each type, synthetic configurations and packets. | Each mechanism records the model that defeats it, its regulator and counterterm rank, its gauge class, its overlap ratio, and whether it is collided, Rosati, local, counterterm-carried, separated, Lorentzian-constructed or zero-side. |
| **W2** | Finite certificates | Gram, Hausdorff, Hankel, Jensen blocks; heat transforms; schedules; budgets; fixed-degree Newton inequalities from Turán data. | Every finite term certified. |
| **W3** | Premise checks | Regularity, support, decay, domains for named tests and families. | Hypotheses discharged. |
| **W4** | Transport | Restate in route coordinates: averaged and zero-ordinate positivity, horizon, forcing gap, log-Sobolev norm, negative index, reserve, census, moment of inertia, field threshold, quantization, closed quantum threshold, spacing law, sections, hyperbolicity equivalences, VK decay, alignment counts, the width currency. | Each conclusion at its true strength. |
| **W5** | Certified constants | Full floor of `ζ` at `23/40`, then past `log 5/2`; odd and primitive windows; explicit constants of the horizon, log-Sobolev, outward and field-threshold laws. | Certified finite-aperture theorems. |
| **W6** | Selectivity tables | At `23/40` the margin of each `{2, 3}` sign pattern; the `{2, 3, 5}` window; successor- and cell-built separating tests. | A margin table per window. |
| **W7** | Short windows | Selberg's near-line density on `U^{1/2+ε}`; averaged and positive-proportion positivity on `Γ^{1/2+ε}`. | The theorems on `Γ^{1/2+ε} ≤ H ≤ Γ/8`. |
| **W8** | Quadrature of readings | Replace the `z`-integrals of the theta readings by finite quadrature with explicit error. | `D`, moments, `M_f` and the detector from finitely many integers. |
| **W9** | Overlap certificates | Certified minimal eigenvalues and negative indices of `Re W + 2S²` and `M` on bump and spline atomic families at overlap ratios `K ∈ [c₀, 16]`, `N ≤ N₀`, for `ζ`, Liouville, finite-flip twins and adversarial bounded twists. | A table locating, for each `N`, the largest `K` at which every bounded twist stays positive and the largest `K` at which `ζ` does; first input of Q1. |
| **W10** | Interior reading of the reserve | Express the outward reserve on a terminal's ray through the explicit formula as a lower bound for a smoothed prime sum at the terminal ordinate. | "An off-line zero of depth `a` forces a smoothed prime sum `≥ c·a·log γ` within `C log γ` of its ordinate"; first input of Q3. |
| **W11** | Counterterm constants | Leading constant of the minimal torsion counterterm in `[3/2, 2]` (continuum model `e/(e − 1)`); optimized `c₀`, `c_full`. | `κ_min = C log N + O(1)` with explicit `C`; sharp separated constants. |
| **W12** | Overlap bookkeeping | Discharge the two summability premises of the non-ratio identity; extend the tilted Schur rows and the cross-kernel row bound to overlapping atoms; compute the non-ratio lag rows at ratio `K`. | The Markov and Weil forms at ratio `K` as explicit row sums with error terms; second input of Q1. |
| **W13** | Electrostatic and index dictionary | `𝓔` versus `𝓔_copy`; index `≤ 𝓔` in PL, HF, ACS, SRT coordinates; field, window energy and `M_f`. | One dictionary theorem per receiver. |
| **W14** | Census assembly | Simple off-line core, TTPC surplus, near-line density, multiplicity exclusion, the disjoint-pair slack. | One census theorem in receiver coordinates. |
| **W15** | Depth homogeneity | Loss law for `k`-level forms and Følner coupling. | One theorem per class. |
| **W16** | Growth inputs | VK and VK-rate escaped decay as range instances of the growth-to-forcing law. | VK as an instance of `exclusion_iff`. |
| **W17** | Contraction calculus | Quartets at depth `1/4 < a < 1/2` at `Δκ = 1`; minimum-tax theorem. | Calibrations in Lean. |
| **W18** | Corollary assembly | Averaged WL energy; rate dictionary; residual heat region; collars; capacity law; ceilings as central nonvanishing; `E_D = E_Δ`; Mertens converse under RH and `J_{−1}(T) ≪ T`; Polymath de Bruijn–Newman import; Gårding instances as finite-rank survival. | Each from existing theorems or the literature. |
| **W19** | Working sources | The `[S]` modules at their stated strength: ALG (including the Hessian identity of the Euler-product closure), AID, RAPT horizon and torsion window, Lévy continuity, the Turán layer. | Each statement completed. |
| **W20** | Charged-cell density | Import Tao's logarithmically averaged two-point Chowla theorem for `λ(a)λ(2a + 1)` (`a₁b₂ − a₂b₁ = 1`) [R, literature]; the analogous Elliott statement for non-pretentious gauges. | Positive logarithmic density of charged cells. |
| **W21** | Alignment accounting | Combine W10 with power-saving alignment counts and zero-density estimates. | A density theorem for deep off-line zeros at aligned ordinates; second input of Q3. |
| **W22** | Lévy synthesis | Quantify how narrow-atom families (refined by a common denominator shift) approximate wider tests in the Lévy norm, and state exactly what positivity at ratio `K` follows from positivity at ratio `c₀`. | A transfer theorem with explicit loss, or a proof that it adds nothing beyond universality. |
| **W23** | Horizon class asymptotics | Source-to-model errors of the class Gram uniform in `N` for fixed `p, J`; extension from step profiles to smooth signed class profiles at fixed `p, J`. | Horizon finite part on fixed class spaces with explicit errors; input of Q2. |
| **W24** | Local trickle-down data | For `N ≤ N₀` and `K ∈ [c₀, 16]`: decide whether `ζ`'s Euler-gauge atomic intersection form with pole plane is Metzler and connected, whether the polar weight has positive image, and compute the `(TD_π)` defect and the gap of quantitative trickle-down. | A certified table; first input of Q2. |
| **W25** | Small-prime deficit table | Certify `d_p ≤ 0` for `47 ≤ p < 2^16` and exact `d_p` for `p < 47`; total deficit on class profiles; archimedean self-energy and pole reserve on the same profiles. | A ledger of who pays each small-prime deficit; input of Q2. |
| **W26** | Universal threshold | Two-sided bounds for `K_univ`, the largest overlap ratio at which `Re W_ω + 2S² ≥ 0` (or a fixed-rank correction) holds for every real twist `\|ω\| ≤ 1` on every atomic family, uniformly in `N`. The extremal twist is `ω(k) = sign` of the lag correlation; on nonnegative families every twist dominates `ζ`, so the threshold is decided on signed families. | `K_univ` bracketed (finite by the class pole vectors [R]); the limit of every universal method; third input of Q1. |

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit; one-sided lag or Abel moments; history floor; regularized abscissa `1/2`; JAS half-power budget; Mertens at square root; one-sided count; Farey sum. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Admission at every damping; positive gauge mass; Báez–Duarte residual `→ 0`. | PM, CTF, BVI, MC, PW-B |
| **B1.3** | **Positivity of the equivariant form.** `W ≥ 0` at all apertures; zero negative index; one shift; Rosati positivity; hyperbolicity of every scaling-surface Gram; `(TD)` for the Metzler atomic families at every overlap ratio; positivity at unbounded overlap. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS, SRT |
| **B1.4** | **Selection** from averages and proportions to every height, test and aperture. | WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign**; all-degree real-rootedness of the Jensen polynomials. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization**, with input outside every exhausted class. | TG, RN, WD, ACS, candidates, PW-B |
| **B1.7** | **Single-currency endpoints.** BSY equality; Li floor; Robin tail; recurrence near zeros; `D_idx < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **RH with simple zeros.** | ACS faithful branch, WL |
| **B1.9** | **Counting forms of the sign.** | HF, ACS, AOG, SRT, WL |
| **B1.10** | **Budget currencies.** | WL, MC |
| **B1.11** | **Equivariance of the positive form.** `D` Hecke invariant; `M_f = 0` ∀`f`; sub-doubly-exponential dyadic defects; subpolynomial prefix readings. | HF, ACS, PM |
| **B1.12** | **Central ceilings and chirality** at every ordinate. | ACS, SBWF |
| **B1.13** | **Field, energy and work forms.** Right-zero field `≤ 1`; `𝓔 ≤ 2`; unit windows `< 2`; no right terminal; cofinal damped source work `≤ 2`; `Re ξ′/ξ > 0` on `Re s > 1/2`. | HF, ACS, OWU, SRT |

### 2.2 Tier B2: classical open problems weaker than RH

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | Quasi-RH: a fixed zero-free strip (e.g. `Θ ≤ 7/8`). | Every graded receiver; the width currency. |
| **B2.2** | Finitely many off-line zeros (`𝓔 < ∞`). | ⇔ bounded damped work ⇔ bounded spline index (AID). |
| **B2.3** | Simplicity of the zeros. | Faithful realizations; budgets; `𝓔` vs `𝓔_copy`. |
| **B2.4** | Density hypothesis; large values beyond Guth–Maynard. | Averaged positivity; exceptional sets of B3.24. |
| **B2.5** | `3/4` of the zeros on the line (present unconditional simple proportion `0.67250071`). | Census; surplus `β ≤ 1/18`; Rosati products beyond the square root. |
| **B2.6** | Power-saving sign correlations of `μ`, `λ`; two-point Chowla in natural density. | MC; SSA; charged-cell density. |
| **B2.7** | Uniform Hardy–Littlewood prime-pair correlations near the square-root band. | TTPC. |
| **B2.8** | Subconvexity and growth near `Re s = 1`. | Growth input of multiplicative forcing. |
| **B2.9** | De Bruijn–Newman bounds beyond the literature. | Shrinks the B1.5 region. |
| **B2.10** | Near-line density on windows shorter than `T^{1/2}`. | Averaged positivity on `Γ^θ`, `θ < 1/2`. |

### 2.3 Tier B3: open problems isolated by this research

No solution is known, and none is proved RH-equivalent.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | `polarRate = Δ` when off-line zeros cluster. | Equality without clustering. |
| **B3.2** | Exclusion of infinite-height escape. | Classification complete [L]. |
| **B3.3** | Quantitative coercivity of residual reconstruction. | Algebraic injectivity. |
| **B3.4** | Signed shell flux on the moving prime-threshold ladder. | Collar bound. |
| **B3.5** | Averaged positivity on windows `Γ^θ` below the classical range. | `θ = 99/100`. |
| **B3.6** | Shared-budget calculus with prime-weighted remainder; the pole-neutralized continuum form. | Raw towers negative `≍ e^A`; joint `2, 3` payment at `23/40`. |
| **B3.7** | Arithmetic input on the residual heat region. | Model geometry complete. |
| **B3.8** | Compatible oriented families. | Spline-orbit index `≤ 1` ⇔ RH. |
| **B3.9** | Sub-half-damping signed control. | `ε = 1/2` bounded. |
| **B3.10** | Order-uniform thresholds; rank decoupled from time. | Fixed-order thresholds. |
| **B3.11** | Sharp successor constants beyond conductor 3. | `1/3`, `1/4`. |
| **B3.12** | Is the paid ideal nonzero on escape? | Excludes white noise only. |
| **B3.13** | Equality case of collar capacity at even `κ`. | Odd `κ` sharp. |
| **B3.14** | Signed near-coincidence beyond aperture `½ log Γ`. | Single-height law. |
| **B3.15** | A gauge-charged estimate for `μ` or `Λ` at `0` beyond the square-root threshold. | Haar-typical twists meet every budget. |
| **B3.16** | **Gauge form-margin.** Positivity of `ζ` separating it from every sign twin on signed tests reading growing prime windows, with a margin bounded below. | Coefficient margin `2 log² p` [L]; separated regime universal [L]; `ζ` the ground state on `\|·\|`-closed families [L]; divergences blind to finite flips [S]; Liouville separated from `23/40` on [L]; non-ratio lags carry the gauge [L]. |
| **B3.17** | Form positivity of the renormalized Rankin–Selberg source beyond isotropy. | Coefficient positivity only. |
| **B3.18** | Lower bounds or arithmetic use of the successor defect. | Mean square exact; successor phase = archimedean gauge field [S]. |
| **B3.19** | Stepanov auxiliaries over `ℤ`. | Need a lattice spectrum; the arithmetic point has no period. |
| **B3.20** | The odd-sector sign beyond the conductor horizon. | Forcing gap at every height [L]. |
| **B3.21** | **A non-uniform bound on the moment of inertia.** | Uniform and one-scale caps are strips [S]. |
| **B3.22** | The full coupled class at the centre. | Positive and rational subclasses settled. |
| **B3.23** | A selective counting polarization. | Soft polarizations; Nyquist rank bounds; inflating majorants. |
| **B3.24** | **Alignment at zero ordinates.** "Off-line zero of depth `a` ⇒ a short prime polynomial `≥ c·a·log γ` near its ordinate" inside the strip; extinction of the exceptional set. | Power-saving counts [L]; exterior law at `σ > 1` [L]. |
| **B3.26** | **Bounded overlap.** For a fixed overlap ratio `K > c₀` — in particular beyond the universal threshold `K_univ` and beyond the first non-ratio lag (`K ≈ 4`) — is `Re W + (bounded-rank correction) ≥ 0` on all atomic families of ratio `≤ K`, uniformly in `N`? What is the largest such `K`, and is positivity there gauge selective? | Proved and universal at `K ≤ c₀` [L]; RH at `K = ∞` [L]; implied by RH at every `K`. |
| **B3.27** | **Terminal or outward upper control off a sparse set.** | Uniform terminal ceiling = strip [S]; reserve and lens [L]. |
| **B3.28** | **Horizon finite part.** A lower bound for the horizon-renormalized Weil form on the class-wise polar-neutral survival space, uniform under class and prime exhaustion and valid for signed profiles, with the small-prime deficits `2d_p` (`p < 47`) paid by the archimedean self-energy and the pole. | Tensor counterterm and covariance [S]; finite part tower form; sign law `c ≥ 2d_p` [S]; `−2γ` on uniform profiles [S]; absolute-coefficient errors on signed profiles. |
| **B3.29** | **Conformal symmetry and the base.** A correspondence over `ℤ` acting conformally with factor `≠ 1` on the completed intersection form, or a positive Hecke-covariant structure across the transverse ladders on which local forms sum with non-scaling loss. | Hecke isometries; power maps, successor not conformal [S]; no common ladder [S]; Euler-product closure blind [S]; successor phase fixes the gauge [S]. |
| **B3.30** | **Trickle-down for `ζ`.** Is `ζ`'s Euler-gauge atomic intersection form, completed by the pole plane, Metzler with connected support and positive image at bounded overlap, and does it satisfy `(TD_π)` — or quantitative trickle-down with a gap — uniformly in `N`? | Stability regime (`Qπ ≤ 0`) = all proved atomic positivity [S]; Metzler only in the Euler gauge at atomic resolution [S]; golden datum fails `(TD_π)` [S]; quantitative `(TD)` + gap ⇒ `μ₋(ε)` [S]. |

### 2.4 Settled questions

- Computation and norm of `D`; the moment of inertia; uniform and one-scale defect caps are strips.
- Electrostatic forms of RH; energy of one zero `O(log γ)`; closed threshold `2` for energy and work; index `< 𝓔`; finite strata of work and index coincide.
- Archimedean payment of the prime place and of the pole at separated widths, with constant one, for every bounded twist; positivity at fixed width is RH.
- Selectivity of separated, section, `|·|`-closed and divergence-level positivity: none.
- Torsion-side, spacing and horizon regulators; partner rank; diagonal covariance; the horizon tensor counterterm and its covariance; finite parts `−2γ` and tower forms; the sign law `d_p`.
- Hodge index as hyperbolicity; Metzler Hodge index as trickle-down; Weil's content over `𝔽_q` as trickle-down; the sign hypothesis as Euler gauge fixing; absence of local Lorentzian structure; blindness of the Euler-product closure; absence of conformal maps among Hecke, power and successor.
- Local Hodge index sums only at the square-root price; no common ladder; self-intersection dominates each tower.
- Gauge-charged couplings; gauge margin of the source; first gauge windows; elliptic rotations are archimedean.
- Forcing gap; escape; deformations; statistics and the `67.250071%` proportion; counting over `𝔽_q`; the width currency.

## 3. The three questions to answer next

**Selection criteria.**

1. Weaker than RH, so it can be answered.
2. Either answer changes the frontier: a positive answer adds a mechanism, a negative one is a sharp no-go naming the missing input.
3. Together the questions cover the three walls.
4. The output is not a strip, a collided positivity, a counting reformulation, a gauge-orbit statement, a one-variable system, a deformation equivalence, a zero-side detection, a prime-only renormalization, a separated (universal) positivity or a constructed form.
5. The question addresses the polarization problem where it now sits: past the point where every universal method stops.

**Why these three.** The previous round asked whether the archimedean place pays the prime place at the spacing. It does, with constant one, and the answer turned out to be universal: it holds for every bounded twist and reads nothing arithmetic. At fixed width the same positivity is RH. Three facts locate the next step. Universal methods stop at a finite overlap ratio `K_univ`, so any further positivity must be arithmetic (Q1). In Lorentzian language every proved atomic positivity is the stability regime of a Metzler form, the Metzler sign holds only for `ζ`, and Weil's theorem over `𝔽_q` is exactly the trickle-down inequality — the one structure that is both positive and selective by hypothesis (Q2). On the zero side the target is now a single number: source work below the quantum `2` (Q3).

### Q1. Beyond universality: how far into bounded overlap does Weil's form stay positive?

> *Positivity holds up to overlap ratio `c₀` for every bounded twist and is RH at unbounded overlap. (i) Determine `K_univ`, the largest ratio at which `Re W_ω + 2S² ≥ 0` for every real twist `|ω| ≤ 1`, uniformly in `N`. (ii) Prove, for some fixed `K > K_univ` — ideally past the first non-ratio lag `K ≈ 4` — that `Re W + (bounded-rank correction) ≥ 0` on all atomic families of `ζ` with ratio `≤ K`, uniformly in `N` (B3.26). (iii) Decide whether positivity there separates `ζ` from its twins.*

- **Why.**
  - The problem is now one parameter between a theorem (`K ≤ c₀`) and RH (`K = ∞`); RH implies positivity at every `K`, and no implication back from a fixed `K` is known.
  - Beyond `K_univ` a proof cannot be universal: it must use `Λ`'s values, multiplicativity or the pole. That is the first place where positivity is forced to read arithmetic. `K_univ` is expected to be finite and computable from `ζ` alone [R]: in the separated regime the infimum over twists of `Re W_ω + 2S²` on a nonnegative-bump family is `M(f_{|x|}) + 2C(f_x)²` (diamagnetism, with the extremal twist aligned to the lag correlations); on class pole vectors corrected to kill `C` the prime form is `≥ (log N − C_{p,J})·mass` while the self-energy is `log(1/w) + O(1)`, so universal positivity needs `log(1/K)` above a fixed constant. On nonnegative families every twist dominates `ζ` (`W_ω ≥ W`), so the threshold is decided on signed families.
  - The gauge becomes visible exactly here (non-ratio lags from `K ≈ 4`), and here the zeros sample the atomic Dirichlet polynomials at the Nyquist rate: zeros up to height `≍ N/K` have local density `log(N/(2πK))/2π` against the Nyquist density `log N/2π` [R]. Bounded overlap is critical sampling; fixed width is undersampling by the factor `log(1/w)/log N → 0`.
  - On class-wise polar-neutral step profiles the horizon-renormalized prime form is `O(1)` per unit absolute coefficient mass [S]; on such profiles the self-energy would keep a margin `≈ log N − log K` that could pay the non-ratio lags [R]. Signed profiles retain absolute-coefficient errors.
- **Route.** W26 (universal threshold); W9 (certified tables for `ζ`, twins and adversarial twists); W12 (non-ratio rows with summability discharged); W22 (Lévy synthesis); then a joint estimate: tilted rows plus the horizon margin against the non-ratio lag rows.
- **Outcomes.**
  - *Positivity at some `K > K_univ`:* the first unconditional positivity that must use arithmetic; if it also fails for twins, the first selective form positivity.
  - *A critical ratio `K*` with failing vectors for every method of a stated class:* a new graded currency, the overlap analogue of the strip width, and an explicit description of what an arithmetic input must pay.
  - *`K_univ` already equals the best provable ratio for every known technique:* a sharp no-go: analysis of coefficient sizes ends at `K_univ`, and the next input is structural (Q2).

### Q2. Trickle-down for `ζ`: does the Euler-gauge intersection form satisfy the Hodge index of a Metzler form?

> *Every proved atomic positivity is the stability regime `Qπ ≤ 0` of the atomic intersection form. Over `𝔽_q` the content of Weil's theorem is the trickle-down inequality `(TD_π)`, which the golden fake datum violates. Is `ζ`'s Euler-gauge atomic intersection form, completed by its pole plane, Metzler with connected support and positive image at bounded overlap, and does it satisfy `(TD_π)` — or quantitative trickle-down with a gap — uniformly in `N` (B3.30)? Can its defect `Q − QD^{−1}Q` be written as a sum of local negative semidefinite pieces: archimedean Laplacians, tower forms with local Euler constants (B3.28), and polar-gluing dispersion?*

- **Why.**
  - Selectivity is in the hypothesis: at level `N` the coupled kernel of a completely multiplicative unimodular twin is Metzler in some gauge iff `χ(p) = 1` for every prime `p ≤ N` (`p^{iτ}` with the shifted archimedean kernel) [S]; Liouville and every twin flipping a prime `≤ N` fail it. A trickle-down proof at level `N` cannot apply to such a twin.
  - Trickle-down converts the failed local-to-global step (hyperbolic forms do not sum) into one that works (negative semidefinite defects sum) [S].
  - The local pieces are computed: the archimedean jump form is a Laplacian [S]; the horizon finite part is the tower form with local Euler constant and sign law `d_p` [S]; polar gluing names the exact cost `V` [S].
  - It is weaker than RH on bounded-overlap families and RH on all of them.
- **Route.** W24 (Metzler property, positive image, `(TD_π)` defect, gap for small `N`); W25 (small-prime deficit ledger); W23 (horizon class asymptotics); then construct links `T_i` from rank-one columns plus the local negative semidefinite pieces and bound the residual by quantitative trickle-down.
- **Outcomes.**
  - *`(TD_π)` with a gap at some bounded overlap:* a Hodge index proved by the mechanism that proves Weil's theorem over `𝔽_q`, selective by construction.
  - *Metzler fails at overlap:* the Lorentzian sign hypothesis holds only at atomic resolution; a gauge in which overlap entries are nonnegative becomes the missing object.
  - *Metzler holds, `(TD_π)` fails:* explicit failing vectors at finite `N`; they locate the missing Frobenius-type input (B3.29) the way the golden datum locates it over `𝔽_q`.

### Q3. The zero-side quantum: does an off-line zero force interior alignment?

> *RH is cofinal source work `≤ 2`; every off-line zero has a terminal within `C log γ` whose outward ray carries a reserve `≥ c·a·log γ`; outside the strip a zero forces anti-alignment of `γ log p`; alignments of short prime polynomials occur at only `T^{1 − 1/C + o(1)}` zero ordinates. Does the reserve force a smoothed prime polynomial of length `(log γ)^{O(1)}` to be `≥ c′·a·log γ` near the ordinate, and can the resulting exceptional set be emptied, or the source work be bounded below the quantum off it (B3.24, B3.27)?*

- **Why.**
  - The counting half and the exterior half are proved [L]; the missing link is the interior implication (W10) and then the step from counts to an individual zero.
  - The target is exact: the quantum `2` is closed and every index is paid by energy [S].
  - Uniform terminal ceilings are strips [S]; only a sparse-set version is non-graded.
- **Route.** W10 (explicit-formula reading of the reserve, moved to discs by Harnack); W21 (density theorem); then quantization (energy `> 2` in any off-line configuration) and the forcing half for a non-isolation law at non-exceptional ordinates.
- **Outcomes.**
  - *Implication holds and the exceptional set empties:* exclusion of isolated deep zeros at non-exceptional ordinates, a non-graded zero-side theorem.
  - *Implication holds, exceptional set persists:* a density estimate plus a sharp description of an exceptional zero.
  - *Implication fails:* zero-side detection cannot become exclusion by Diophantine means.

The three questions are the forcing problem in each wall's currency: Q1 in the overlap ratio (Wall 3, faces 3.25–3.26; Wall 1, face 1.18), Q2 in the Lorentzian signature (Wall 14, faces 14.18, 14.31–14.33; Wall 3, face 3.23), Q3 on the zero side (Wall 1, face 1.21; Wall 3, face 3.19; Wall 14, face 14.26).

**Considered and not chosen.**
- **The horizon finite part alone (B3.28).** Its payoff is as the local defect data of Q2 and as the margin of Q1; posed alone it gives positivity on a survival space where separated positivity already holds.
- **Conformal symmetry and the base (B3.29).** No candidate object; a negative answer to Q2 would name it.
- **A gauge form-margin as a separate question (B3.16).** The no-go theorems place every remaining source of selectivity inside Q1 (non-ratio lags, pole, signed families beyond `K_univ`) or Q2 (the Metzler hypothesis).
- **A bound on `M_f` (B3.21), the field threshold and window energy (B1.13), the full coupled class (B3.22), `3/4` (B2.5), a selective polarization (B3.23), infinite-height escape (B3.2), Stepanov over `ℤ` (B3.19).** Strip-type, RH itself, classical, or without a candidate object.

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows a new field is necessary. The previous proposal — arithmetic harmonic analysis at the spacing scale — was tested and answered by existing tools: an exact Lévy self-energy, a Schur test with weights tilted across scales, and Dirichlet-polynomial bookkeeping reach a fixed fraction of the spacing. The answer is universal: nothing arithmetic happens there. That is informative. Classical analysis controls a form through the sizes of its coefficients, so it is blind to everything a bounded twist shares with `ζ`; it stops at `K_univ`. Classical algebraic geometry controls a form through a conformal symmetry (Frobenius) and a Metzler sign (effectivity); over `ℤ` the symmetry is missing. Every open B3 obstacle sits where neither applies:

| Ingredient over `𝔽_q` | Over `ℤ` | Status |
|---|---|---|
| Positive Hermitian structure | `D` positive, computed; torsion energies positive before the limit | exists [L] |
| Bézout = Metzler sign | atomic kernel Metzler exactly in the Euler gauge | exists at atomic resolution [S]; unknown at overlap |
| Local Hodge index | tower forms bounded; ladders carry two positive squares | exists in absolute value; not Lorentzian [L/S] |
| Finite diagonal | archimedean self-energy pays prime place and pole while separated | exists to ratio `c₀` [L]; RH at fixed width |
| Covariant renormalization | horizon tensor counterterm, local finite parts with `γ_p` | exists on class spaces [S] |
| Trickle-down on one ladder | — | missing |
| Frobenius conformal, factor `q` | Hecke isometries only | missing |
| Spectrum on a lattice; period of the base point | none at the arithmetic point | missing [L] |
| Selection of the base point | Metzler sign at Euler; cells; source margin `2 log² p` | exists structurally, not on forms |

New mathematics is likely required [R]: a Hodge theory of the integers in which positivity is proved by trickle-down rather than by a conformal symmetry, the local data are the renormalized tower forms of the primes and the Laplacian of the archimedean place, the selection of `ζ` is the Metzler sign fixed by the archimedean place along the successor, and the decisive scale is bounded overlap, where the zeros sample the arithmetic Dirichlet polynomials at the Nyquist rate. No existing theory supplies arithmetic trickle-down links or a substitute for Frobenius over `ℤ`. In the corpus this is not a new programme: it is the scope of Arithmetic Lorentzian Geometry, extended.

### 4.2 Home: an extension of ALG

ALG already owns construction and composition of signature certificates for the actual scaling-surface form: degree-two signature calculus, polar gluing and its price, the half-defect repair, links and trickle-down with the Metzler dichotomy, gauge fixing and the successor connection, Frobenius conformality against Hecke isometry, local factors, the Turán layer, and the research questions "signed overlap and exhaustion" and "exceptional extinction". Its own boundary rule — connect the analytic results by source-defined comparison and composition, do not rename the missing overlap or exhaustion theorem — applies here too. The extension changes ALG's scope in four places; the analytic and renormalization inputs keep their owners.

| Extension of ALG | Content | Input owned by |
|---|---|---|
| **Renormalized links** | Links of the atomic intersection form built from the horizon finite parts (tower forms with `γ_p`), the archimedean jump Laplacian and the pole plane; a ledger of who pays the deficits `2d_p` at small primes | RAPT (finite parts, sign law), AIT (tower forms) |
| **The Metzler property beyond atomic resolution** | The sign of overlap entries (overlap Gram, Lévy cross terms, non-ratio prime lags) in the Euler gauge; a gauge making them nonnegative, or its absence | SSHA (overlap calculus), ALG (gauge fixing) |
| **Trickle-down along the overlap ratio** | `(TD_π)` and quantitative trickle-down with a gap as functions of `K`; the stability regime `K ≤ c₀` as the base case; Q2 as the first target | SSHA (separated law, `K_univ`), ALG (Metzler dichotomy) |
| **Universality as a calibration** | Every proposed certificate must fail for some bounded twist beyond `K_univ` and for the golden datum, for a named reason | SSHA (universal law, diamagnetism), ALG (`𝔽_q` calibration) |

Outside ALG: the universal threshold and Lévy synthesis (SSHA, W26, W22); horizon asymptotics (RAPT, W23); the sampling reading (AOT); interior alignment and the source-work quantum (AES, AID; Q3).

### 4.3 The extended programme

**Thesis [R].** Over `𝔽_q`, Frobenius supplies the Hasse–Weil inequality through its conformal factor, and Bézout supplies the sign. Over `ℤ` the sign is present (Euler gauge), the local forms are present (tower forms, archimedean Laplacian, renormalized at the horizon), the symmetry is absent. The extended programme replaces the symmetry by a local-to-global law: the defects `Q − QD^{−1}Q` of the local pieces are negative semidefinite and sum. RH is the statement that this trickle-down survives every overlap.

**Central conjecture [R]: trickle-down at bounded overlap.** For each fixed overlap ratio `K`, `ζ`'s Euler-gauge atomic intersection form of level `N`, completed by its pole plane, is Metzler with connected support and satisfies `(TD_π)` for an explicit weight `π` (the polar weight with a tilt across scales), with a trickle-down defect equal to a sum of archimedean Laplacians, horizon tower forms with local Euler constants and a polar-gluing dispersion, uniformly in `N`. Uniformity in `K` is RH.

**What it would be like.**
- **Like Lorentzian polynomial theory (Brändén–Huh) and Hodge theory of matroids (Adiprasito–Huh–Katz):** hyperbolicity, nonnegative coefficients as the sign, trickle-down from links to the whole.
- **Like Arakelov theory:** Green functions at the archimedean place, self-intersections as discriminants, local Hodge index at each place.
- **Like renormalization in quantum field theory:** regulators, counterterms whose rank is a property of the regulator, covariant tensor counterterms, finite parts as local constants (`γ_p`).
- **Like sampling theory and the large sieve:** frame bounds, Nyquist density, the transition from injective to hiding sampling at the diagonal.
- **Like gauge theory:** square-class (blind) and successor (charged) couplings; the diamagnetic inequality; the archimedean kernel as a gauge field fixing the Euler point.
- **Like logarithmic potential theory:** zeros as charges, quantized energy with a closed threshold.

**Parts already in the corpus.** The ALG core: Lorentzian forms, trickle-down, Metzler dichotomy, `𝔽_q` calibration, gauge fixing, successor gauge field, local factors, conformality, repairs. Inputs from other owners: spacing-scale analysis (SSHA); renormalization and finite parts (RAPT, RBG); intersection theory of the circle and towers (AE, AIT); electrostatics and index descent (AES, AID); gauge geometry (ACG, BGG, RBG, SP); sampling and Nyquist rank bounds (AOT).

### 4.4 Criteria the extended programme must meet

| Criterion | Test against the corpus |
|---|---|
| **Computability** | Forms produced by identities (explicit formula, `ξ` current, log-orders, `Λ ⋆ Λ`), not posited; counting reformulations excluded. |
| **Selectivity by hypothesis** | Its sign hypothesis fails for every sign twin and for the golden datum's trickle-down; it passes the W1 battery; blind exactly where the corpus proves blindness (separated regime, `\|·\|`-closed families, divergences, Euler-product closure). |
| **Beyond universality** | A positivity theorem at overlap ratio `> K_univ`. |
| **Regulator honesty** | States its regulator, counterterm rank, survival cone and finite part; reproduces Abel `{0}`, spacing indefiniteness, horizon tensor covariance, the sign law `d_p`. |
| **Local to global** | Reproduces the failure of sums of hyperbolic forms, the square-root price, two positive squares per ladder, and replaces them by summable semidefinite defects. |
| **Matched constants** | Constant one in self-energy and covariant counterterm; the torsion window; `−2γ`. |
| **Calibration** | Weil for curves as trickle-down; hyperelliptic RH; budget slopes; `κ = 1`; `κ ≥ 3`; conductor horizon; `W = D − Δ`; `E_f ≍ M_f`; the closed quantum `2`; the census. |
| **From detection to bound** | Turns a zero-side reserve or an index into an upper bound on work off a sparse set. |
| **Non-circularity and uniformity** | No premise contains the conclusion; overlap, aperture, height and rank controlled together. |
| **New partial results** | Outputs that are not strips: positivity at a fixed overlap ratio, a trickle-down inequality with a gap, a critical ratio, a non-isolation law. |

### 4.5 Questions it must answer

1. How far beyond `K_univ` does `ζ`'s form stay positive, and what is the critical overlap ratio (Q1)?
2. Is `ζ`'s Euler-gauge intersection form Metzler at overlap, and does it satisfy trickle-down (Q2)?
3. What replaces Frobenius: a correspondence with conformal factor `≠ 1`, or a trickle-down structure that makes one unnecessary (B3.29)?
4. Is the horizon-renormalized prime place bounded below on its survival space, and who pays the small-prime deficits (B3.28)?
5. What is the base over `ℤ`: which positive, Hecke-covariant structure joins the transverse ladders, and is the successor its connection?
6. Does an off-line zero force interior alignment, and can source work be bounded below the quantum off a sparse set (Q3)?
7. What is the arithmetic point and its period?
8. How does a quantized statistic reach every window?
9. Which correspondence acts as conjugation on the zeros, as the power map `−1` does on torsion cycles?
10. Is the coupled class bounded at the centre (B3.22)? What selects the fibre (B3.23)?

### 4.6 Tools

**Built:** capacity identity and Hecke law of `D`; log-Sobolev norm; `ξ` current and theta readings; moment of inertia, dyadic amplification; terminals, rays, lens, Harnack; field, energy, quantization, closed quantum threshold, index–energy inequality; Selberg's source and its margin; log-orders, towers, square-root price, self-intersection dominance; survival, rank dichotomy, coupled survival, covariance, torsion window, Gårding as survival; horizon polar, tensor and covariant counterterms, finite parts `−2γ` and tower forms, sign law `d_p`, polar matching; exact self-energy, tilted rows, spacing law, universality, diamagnetism, section positivity with the pole; non-ratio lag calculus, Dirichlet dictionary, unbounded-overlap theorem, Lévy continuity; hyperbolicity, trickle-down, Metzler dichotomy, `𝔽_q` calibration, gauge fixing, successor gauge field, local factors, conformality, half-defect repair, polar gluing; width currency; counting and budget calculus; Nyquist rank bounds; gauge torus, cells, cell defects.

**Not yet built:**
- **Overlap calculus with constants:** the forms at fixed ratio `K` as explicit row sums (W12) and the universal threshold (W26).
- **Arithmetic trickle-down links:** local links of the atomic intersection form from tower forms, archimedean Laplacians and polar gluing.
- **A Metzler theory at overlap:** a gauge in which overlap entries are nonnegative, or a proof that none exists.
- **A conformal correspondence or its replacement.**
- **Interior anti-alignment** (W10) and exceptional-set extinction.

### 4.7 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | • Atoms `log n` with width `w`, spacing `δ_N`, overlap ratio `K`; atomic and section families as Dirichlet polynomials of length `N`.<br>• The atomic intersection form with its pole plane; its Euler gauge; its row sums, positive weights `π`, links and trickle-down defect.<br>• Tower forms of the primes; `p`-adic classes, class polar functionals, orbit densities; the horizon tensor counterterm; finite parts with local Euler constants `γ_p`; tower deficits `d_p`.<br>• The archimedean self-energy, cross kernel and jump Laplacian; the successor phase as gauge field.<br>• Non-ratio lags; sign twins and bounded twists; cells.<br>• The zero divisor: field, energy, source work, terminals, reserves; Dirichlet polynomials at zero ordinates. |
| **Language** | It must distinguish: separated, bounded-overlap and unbounded-overlap families; oversampling, critical sampling and undersampling; universal and arithmetic estimates; stability and trickle-down regimes; Metzler and hyperbolic; actual, repaired and glued forms; isometric and conformal correspondences; divergence and finite part; ratio and non-ratio lags; coefficient margin and form margin; gauge blind and gauge charged; detected, counted, paid and bounded. |
| **Mechanisms to discover** | • An **overlap law**: positivity at a fixed ratio beyond `K_univ`.<br>• An **arithmetic trickle-down law**: links of `ζ`'s intersection form with summable semidefinite defects.<br>• A **deficit law**: archimedean and polar payment of the small-prime tower deficits.<br>• A **conformal or replacement law** supplying the Hasse–Weil inequality over `ℤ`.<br>• An **interior anti-alignment law** and an **extinction law** for exceptional zeros. |
| **First milestones** | (1) W26, W9: `K_univ` bracketed; certified overlap tables for `ζ` and twins.<br>(2) W12, W22: the forms at ratio `K` as row sums; Lévy synthesis.<br>(3) W24, W25, W23: Metzler and trickle-down tables; small-prime deficit ledger; horizon asymptotics.<br>(4) W10, W21: interior reading of the reserve; density theorem.<br>(5) W5, W6, W20: the `23/40` floor, margin tables, charged-cell density.<br>(6) W13, W18, W19: dictionaries, corollaries, working sources. |

Each milestone is a theorem of a kind the corpus lacks: positivity that cannot be universal, a trickle-down inequality for the actual form, or an implication from a zero to an arithmetic large value — not a receiver, a strip, a blindness theorem, a detection, a constructed form or a counting reformulation. Programme standards: **SSHA** names the overlap ratio and whether an estimate is universal; **ALG** names whether a form is Metzler, in which regime, and whether it is the actual or a constructed form; **RAPT / RBG / AIT** name the regulator, counterterm rank, survival cone and finite part; **AES / AID / CDG / PL** name whether a positivity is collided, Rosati or zero-side and whether a bound is uniform; **ACG / BGG / SP** name the gauge class and whether a margin is on coefficients or on forms.

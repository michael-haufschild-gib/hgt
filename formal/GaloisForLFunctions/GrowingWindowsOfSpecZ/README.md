# Growing Windows of Spec ℤ (GWZ)

Namespace `GaloisForLFunctions.GrowingWindowsOfSpecZ`; umbrella `GrowingWindowsOfSpecZ.lean`.
Every theorem is unconditional; equivalences with RH are labelled as such.

## 1. Motivation

RH is the statement that Weil's form `Q` is nonnegative on every window `W_A` (real `C²` tests
supported in `[−A, 0]`), for every length `A` (CWS `riemannHypothesis_iff_windowForm_nonneg`). The
corpus has classified what does not produce this sign:

- **No slack.** The Weil cone is a point, window margins collapse doubly exponentially, no finite
  identity, finite carrier or lossy estimate survives (RHTower, CWS, ACT).
- **No positive dimension.** Positivity of the counts in Tate dimension `k ≠ 0` does not descend to
  `k = 0` (DZG).
- **No Frobenius inside a window.** The similitudes of `Q` in the window algebra are scalars (DZG).
- **The new fold is a positive source.** The frozen form is indefinite past the first prime, and the
  prime `2` repairs a negative frozen direction (WTZ `exists_first_stage_positive_exit_loan_failure`).

What is left is a statement about **growth**. As `A` increases the form changes only by one
collar-to-collar correlation per prime power, `Q = Q_N − 2w c_H(log(N+1))` (DZG
`weilQuad_eq_stageForm_sub_corr`), and positivity must survive each of these kicks exactly. GWZ is the
exact theory of this growth: the window length is a time, each prime power `n` is an impulse of
strength `w_n = Λ(n)/√n` at time `log n`, the archimedean place and the pole are the free evolution,
and RH is the statement that the evolution never leaves the positive cone.

Krein–Gelfand–Levitan theory says that for a translation-invariant kernel positivity on every
interval is the global existence of a causal evolution in the interval length (a canonical system, a
continuous Schur algorithm). GWZ builds the arithmetic version in exact form, in two registers:

- **continuum**: two-collar forms (infima of the frozen form over interior perturbations), the kick
  law, the reflection sectors, zero modes;
- **lattice**: the translates `φ(· + kh)` of one bump span lattice windows whose Weil Gram forms are
  Toeplitz; their Schur–Levinson evolution is an exact discrete canonical system of Spec ℤ, causal in
  the primes, with margins, Schur parameters, outer ground states and unit-circle zero modes.

The two registers are one tower: a window of length `A` is nonnegative iff every lattice of total
length at most `A` is (`window_nonneg_iff_lattices`, `window_pos_iff_lattices`).

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Window, level, stage | CWS `IsWindowTest`, `windowLevel` | tests in `[−A, 0]`; `N = ⌊e^A⌋`; stage `n`: `log n ≤ A < log(n+1)` |
| Frozen form, kick | WTZ `stageForm N`; `primeJumpWeight`, DZG `corr` | Weil's form with folds `≤ N`; `w = Λ(N+1)/√(N+1)` times `c_H(ℓ)`, `ℓ = log(N+1)` |
| Interior test | `IsInteriorTest A ℓ h` | `C²`, supported in `[−ℓ, ℓ − A]`; collars `[−A, −ℓ]`, `[ℓ − A, 0]` |
| Two-collar form | `twoCollarForm N A H` | `S^N_A(H) = inf_h Q_N(H + h) ∈ [−∞, ∞)` over interior tests |
| Window involution, collar reflection | CWS `windowInvolution A`; `collarReflection A ℓ` | `σ_AH(u) = H(−A − u)`; `Ru = −A − ℓ − u` on the left collar |
| Even/odd parts | `evenPart A H`, `oddPart A H` | `(H ± σ_AH)/2` |
| Toeplitz form | `toeplitzForm κ n x` | `Σ_{i,j<n} κ(i − j)x_ix_j`, `κ` even (`IsEvenSeq`) |
| Predictor, margin | `IsPredictor`, `predErr` | normal equations `Σ_k κ(j − k)a_k = −κ(j+1)`; `E = κ(0) + Σ κ(k+1)a_k` |
| Levinson evolution | `levinson κ n`, `levinsonErr`, `levinsonPred` | `E_0 = κ(0)`, `E_{n+1} = E_n − β_n²/E_n`, `a' = (a − γJa, −γ)` |
| Schur parameter, reflection coefficient | `schurParam κ n`, `reflCoeff κ n` | `β_n = κ(n+1) + Σ κ(k+1)a_{n−1−k}`, `γ_n = β_n/E_n` |
| Frozen prediction | `frozenPrediction κ n a` | `π_n`, with `β_n = κ(n+1) − π_n` |
| Levinson vector | `levinsonVec κ n` | `(1, a^{(n)})`: the ground state of the corner problem; at a critical length the zero mode |
| Lattice translates, lattice tests | `latticeTranslate φ h k`, `latticeTest φ h x` | `φ(· + kh)`; `Σ x_kφ(· + kh)` |
| Weil sequence | `weilSeq φ h d`; `weilSeqW λ φ h d` | `κ(d) = W(φ, φ(· + dh))`; the same with prime weights `λ` |
| Lattice lag | `latticeLag φ h d x` | `k_d(x) = ∫ φ(u)φ(u − x + dh)`: what a jump of length `x` sees at site `d` |
| Hermitian form, polynomial of a vector | `hform κ N p q`, `vecPoly v` | `Σ κ(j − k)p_j\overline{q_k}` on `ℂ[z]_{≤N}`; `Σ v_kz^k` |
| Cofactor of an angle | `cofactor V w` | `V/(z − w)`: the eigenvector of the shift `z·` modulo the zero mode |
| Pole coordinates, local pairing | ACS `poleA`, `poleB`, `localPair` | `∫fe^{±u/2}`; Weil's pairing minus its polar part |

## 3. Language

- **Time** is the window length `A` (continuum) or the lattice size `n` (lattice). **Free evolution**:
  the archimedean place with the pole (`λ = 0`). **Kicks**: the prime powers.
- **Collar data**: a test modulo interior tests. **Frozen / complete**: before / after the kick.
- **Positive source / cost**: collar data on which the kick raises / lowers `Q`.
- **Sector**: a `σ_A`-parity combined with an `R`-parity of the left-collar datum.
- **Margin** `E_n`: the energy of the new site after projection onto the old window.
  **Prediction interval** of a stage: `(π_n − E_n, π_n + E_n)`, where the newest datum must land.
- **Ground state** of a lattice window: its Levinson vector; **outer**: no zero of its polynomial in
  the closed unit disc.
- **First critical length**: positive definite before, degenerate at it; the radical is the **zero
  mode**. **Angles**: arguments of the zeros of a zero-mode polynomial on the unit circle.
- **Soft / selective**: true for data with off-line zeros (flip twins, `ζ(s)ζ(s−ε)`, Epstein, golden
  curve) / false on them.

## 4. Mechanisms

**A. Criticality (ground states).** On the lattice the ground state of each corner problem is the
Levinson vector, and a window is positive definite exactly when every margin on the way is positive
(`toeplitzForm_posDef_iff`); a positive window has an outer ground state, whose polynomial has no
zero in the closed unit disc (`norm_gt_one_of_predictor_root`). In the continuum the ground-state
representation passes each stage by a collar correction in every gauge (DZG
`weilQuad_eq_groundState`).

**B. Causal evolution (kicks).** The kick reads collar data only (`corr_add_interior`), so the infimum
over interior perturbations commutes with it: `inf_h Q(H + h) = S^N_A(H) − 2w c_H(ℓ)`
(`iInf_weilQuad_add_interior`), and a window is nonnegative iff `2w c_H ≤ S^N_A(H)` on every collar
class (`stage_criterion`). On the lattice the two-collar form is a `2×2` matrix,
`T_{n+2}(x₀, x, x₁) = E_nx₀² + 2β_nx₀x₁ + E_nx₁² + T_n(x − x₀a − x₁Ja)`
(`toeplitzForm_two_collar`, `twoCollar_isLeast`), the stage criterion is `|β_n| < E_n`
(`posDef_succ_iff_abs_schur_lt`), and the evolution is the discrete Riccati law
`E_{n+1} = E_n − β_n²/E_n = E_n(1 − γ_n²)` (`levinsonErr_succ_eq_mul`).

**C. Reflection.** `σ_A` swaps the collars and fixes the interior, the frozen form and the kick
(`twoCollarForm_windowInvolution`). The kick pairs a test with its Rosati image through the collar
reflection, `c_H(ℓ) = ∫_L H·(σ_AH)∘R` (`corr_eq_collar_windowInvolution`); on `σ_A`-even tests it is
`¼∫_L(H + H∘R)² − ¼∫_L(H − H∘R)²`, on odd tests the negative (`corr_eq_of_even`, `corr_eq_of_odd`).
Positivity splits by parity (`window_nonneg_iff_sectors`).

**D. Locality and selection in the primes.** `κ^λ(d)` reads only the weights of `n` with `log n ≤ |dh| + r`
(`weilSeqW_congr`), so the `n`-th margin reads only `m ≤ e^{nh + r}` (`levinson_weilSeqW_congr`). A
change of one weight is a single kick: it leaves the evolution up to its stage untouched and moves
one Schur parameter by `−δλ(n₀)n₀^{−1/2}k_{m+1}(log n₀)` (`schurParam_single_kick`), so the
admissible weights of `n₀` at a stage form an interval of length `2√n₀E_m/|k_{m+1}(log n₀)|`
(`posDef_update_iff`). Over all lattices only `Λ` survives (`lattice_selects_vonMangoldt`): the
evolution is prime-blind in its form and selects the arithmetic by positivity alone.

**E. Angles.** A degenerate lattice window has a one-dimensional radical spanned by a palindrome up to
sign with nonzero ends (`toeplitzForm_kernel_of_first_critical`, `levinsonVec_rev_of_sq_eq_one`), whose
polynomial has `n + 1` simple zeros on the unit circle (`norm_eq_one_of_critical_root`,
`zeroMode_roots`), and the frozen data are the power sums of these angles with positive weights
(`degenerate_window_is_curve`): at its first failure a window is the window of a curve over `𝔽_q`.
Conversely a curve with `|S|` angles closed under conjugation is positive definite through size `|S|`
and degenerates exactly at margin index `|S|` (`curve_first_critical`): the first critical index of a
window is the number of its angles, `2g` for a curve of genus `g` with distinct angles. Under RH
Spec ℤ is such a curve on every lattice, with infinitely many angles: the lattice window of `φ` at
step `h` is `T_N(x) = Σ_ρ m_ρ|φ̂(γ_ρ)|²|Σ_k x_ke^{ikγ_ρh}|²`, the window of the zero ordinates folded
to `e^{iγ_ρh}`, and RH is this identity (`toeplitzForm_weilSeq_eq_tsum`,
`riemannHypothesis_iff_folded_curve`). Its margins dominate those of every finite piece of the curve
(`levinsonErr_truncation_le`).
The pole is the pair of hyperbolic angles `e^{±h/2}` of every lattice, carrying exactly one negative
square (`toeplitzForm_polar_eq_hyperbolic`, `polarSeq_signature`). Off RH some lattice degenerates
exactly, so RH is the absence of such curve-like edges (`riemannHypothesis_iff_no_degenerate_lattice`).

## 5. Questions and answers

| Question (review-0311 §2.7) | Answer |
|---|---|
| What is the two-collar form of a stage, and what law carries it across a prime kick (2.5.1)? | **Continuum:** the infimum `S^N_A` of the frozen form over interior tests; it depends only on collar data (`twoCollarForm_add_interior`), is `σ_A`-invariant (`twoCollarForm_windowInvolution`), and the kick subtracts `2w c_H(ℓ)` from it exactly (`iInf_weilQuad_add_interior`); the window is nonnegative iff `2w c_H ≤ S^N_A` (`stage_criterion`). Within the stage both sides are born zero — `S^N_ℓ ≡ 0` and `c_H(ℓ) = 0` on `W_ℓ` (`twoCollarForm_birth`, `corr_birth`) — and the two-collar form grows with the collar width (`twoCollarForm_mono`): positivity is a race between two collar functionals, restarted at every prime power. The closed form of the frozen datum on stage tests `x_L + y + x_R` — trivial-divisor moments and earlier-fold transports, explicit at the first two stages — and the growth law of a window as a translation contraction (the Carathéodory disk of a stage) are CSWT's (`frozenTwoCollar_eq_transmitted`, `stage_nonneg_iff_disk`). **Lattice (closed form):** the two-collar form of a stage is `[[E_n, β_n], [β_n, E_n]]` (`toeplitzForm_two_collar`, `twoCollar_isLeast`), the equal diagonal coming from the reflection; across the stage the law is `E_{n+1} = E_n − β_n²/E_n` with the new predictor `(a − γJa, −γ)` (`isPredictor_snoc`, `predErr_snoc`); the newest datum enters `β_n` with coefficient one, `β_n = κ(n+1) − π_n` (`schurParam_eq`), and a prime kick moves exactly one Schur parameter (`schurParam_single_kick`). **Continuum limit of the closed form:** refining a lattice lowers its margin (`levinsonErr_refine_le`), and under RH the dyadic margins converge to the continuum corner margin (`tendsto_levinsonErr_dyadic_contMargin`). That limit is degenerate: translates arbitrarily close to the corner are admissible, so the corner margin is `≤ 0` unconditionally and `= 0` under RH (`contMargin_nonpos`, `contMargin_eq_zero`, `tendsto_levinsonErr_dyadic_zero`). The continuum invariants are the margins rescaled by the step: under RH the first margin is born at order `h²`, `E_1(φ, h)/h² → M₂(φ) = Σ_ρ m_ργ_ρ²|φ̂(γ_ρ)|²`, the zero energy of `φ'` (`tendsto_levinsonErr_one_div_sq`, `zeroSecondMoment_eq_deriv`). **First prime stage:** the two-collar form of the stage of `2` dominates the kick on every collar class for `log 2 ≤ A ≤ 181/250`, and the prime-free frozen form dominates the kick of `2` there (`firstStage_criterion_of_le`, `firstStage_kick_le_frozen`); a finite closed form does not exist — at the first prime no identity "jump count + fold data + finitely many squares" represents the window form (CWS `not_exists_countIdentity`). **What converges:** the Schur data at a fixed index coalesce under refinement (`γ_0(φ, h) → 1`, `E_n(φ, h) → 0`; `tendsto_reflCoeff_zero`, `tendsto_levinsonErr_of_rh`), and so do the margins at fixed total length; what survives is the rate, `h⁻²E_1 → M₂(φ)`: the continuum limit of the lattice canonical system is a jet system in the derivatives of the bump. At second order it is complete: `h⁻²E_n → 0` for `n ≥ 2`, since the `n`-th margin is at most the zero energy of the `n`-th Frobenius difference, `E_n ≤ Σ_ρ w_ρ(2 − 2cos γ_ρh)^n` (`levinsonErr_le_tsum_diff`, `tendsto_levinsonErr_div_sq`). |
| Does the window jump process have a positive ground state at every length, and how does it pass a stage (2.6.1)? | **Lattice: yes, exactly when the window is positive.** Positive definiteness of a lattice window is the positivity of every margin of its Levinson evolution (`toeplitzForm_posDef_iff`); the ground state (Levinson vector) is then outer (`norm_gt_one_of_predictor_root`), and it passes a stage by the Levinson step. **RH-equivalent for Spec ℤ:** RH iff every lattice margin of every bump at every step is positive (`riemannHypothesis_iff_levinsonErr_pos`); unconditionally every lattice is positive while its total length stays below `181/250`, past the first prime (`levinsonErr_pos_of_short`). **Selection:** for an arbitrary prime weight, all margins stay positive iff RH and the weight is `Λ` (`lattice_selects_vonMangoldt`); deleting one prime power or all of them makes some lattice degenerate (`exists_lattice_failure_of_delete`, `exists_free_lattice_failure`). Continuum: the passage is exact in every gauge (DZG); existence at every length is RH. |
| Is there a unique-continuation principle forbidding a zero mode with full mass on both collars? | **Lattice: the zero mode is rigid.** At a first critical length the radical is one line (`toeplitzForm_kernel_of_first_critical`), spanned by a palindrome up to the sign `−γ_n` with end coefficients `1` and `−γ_n = ∓1` (`levinsonVec_rev_of_sq_eq_one`, `reflCoeff_sq_of_critical`), its polynomial has exactly `n + 1` simple zeros, all on the unit circle (`zeroMode_roots`), and the frozen window is the Toeplitz form of the power sums of these angles with positive weights (`degenerate_window_is_curve`); for Spec ℤ such a window refutes RH (`not_riemannHypothesis_of_first_critical`). **Continuum: unique continuation from an end collar holds.** At a first critical length a zero mode vanishing on an end collar of any width vanishes, and two zero modes agreeing on one end collar coincide (`eq_zero_of_zeroMode_vanish_collar`, `zeroMode_eq_of_eq_on_collar`); the radical is `σ_A`-invariant, every edge has a reflection parity (`exists_parity_zeroMode`), and a zero mode vanishing on an interior gap is a balanced split (`gap_law`). Continuation across interior gaps is not structural: the curve with three angles at the cube roots of unity has a first critical window whose unique zero mode `(1, 0, 0, −1)` vanishes on both interior sites (`curveThree_first_critical`), so collar continuation is the exact structural principle. **Forbidding the zero modes is RH:** RH holds iff no lattice window of Spec ℤ degenerates (`riemannHypothesis_iff_no_degenerate_lattice`); off RH a short generic bump has an exactly degenerate two-site lattice (`exists_degenerate_lattice_of_not_riemannHypothesis`, via the continuity of orbit correlations and AOG's one-orbit criterion). So the principle asked for exists in its collar form, and in its forbidding form it is equivalent to RH. **The interior is never needed:** every first failure of Spec ℤ is realized on two sites, where the zero mode `(1, ∓1)` has no interior; RH holds iff every two-site lattice window is positive definite, iff the orbit correlation satisfies the strict Cauchy–Schwarz inequality `|W(φ, φ(· + t))| < W(φ, φ)` for every nonzero bump and `t ≠ 0` (`riemannHypothesis_iff_two_site_posDef`, `riemannHypothesis_iff_abs_weilOrbitCorr_lt`). |
| Which positive involution on two-collar data makes `σ_A` a Rosati positivity? | **The collar reflection `R`.** The kick is the collar Rosati form `c_H = ∫_L H·(σ_AH)∘R` (`corr_eq_collar_windowInvolution`), and on the two `σ_A`-sectors it is `±` the signature form of `R` (`corr_eq_of_even`, `corr_eq_of_odd`). The kick is a positive source exactly on the even–`R`-antisymmetric and odd–`R`-symmetric collar data; on a nonnegative window every frozen-negative even (odd) test is forced into the `R`-antisymmetric (symmetric) sector (`collar_antisymmetric_of_frozen_negative_even`, `collar_symmetric_of_frozen_negative_odd`). Positivity of the stage is the domination of this Rosati form by the frozen two-collar form. |
| What is the `ℤ`-analogue of the trivial Frobenius angle, and what weight does Weil's form carry there (2.6.4)? | **Lattice reading:** a lattice of step `h` folds the zero ordinates to angles `hγ mod 2π`. The trivial Frobenius eigenvalues are the pole: on every lattice it is the hyperbolic pair of angles `e^{±h/2}`, contributing the pole plane `2A(φ)B(φ)·V(e^{h/2})V(e^{−h/2})` (`weilSeq_eq_polar_sub_local`, `toeplitzForm_polar`, `toeplitzForm_polar_eq_hyperbolic`), exactly as `1` and `q` normalized by `√q` over `𝔽_q`. A degenerate lattice window has finitely many simple unitary angles with positive weights (`degenerate_window_is_curve`): it is a curve window. **The weight there:** for `A(φ)B(φ) > 0` the trivial angles carry exactly an indefinite plane — positive on one site, negative on the first difference (`4ab(1 − cosh(h/2)) < 0`), zero on the pole hyperplane (`polarSeq_signature`); the Weil sequence is this polar sequence minus the local one (`weilSeq_eq_polarSeq_sub`). Weil's form carries the trivial angles with one negative square, and it is nonnegative on every lattice iff the archimedean place and the primes pay that square everywhere, i.e. iff RH (`riemannHypothesis_iff_levinsonErr_pos`); then no lattice degenerates (`riemannHypothesis_iff_no_degenerate_lattice`) and Spec ℤ has infinitely many unitary angles on every lattice. In AHD's complete family the corresponding statement is the horizon criterion (the sign of the untwisted horizon windows), likewise RH. |
| How do the soft horizons `≍ e^{−A/2}` become the exact doubly exponential margins? | **Margins are products of Schur factors:** `E_n = κ(0)∏_{k<n}(1 − γ_k²)` (`levinsonErr_eq_prod`). Exact collapse of margins is the accumulation of the Schur parameters at `±1`; each kick is admissible only in an interval of length `2√n₀E_m/|k_{m+1}(log n₀)|` (`posDef_update_iff`), which shrinks with the margin, and no value other than `Λ(n₀)` survives every lattice (`exists_lattice_failure_of_ne`): the exact form of the rigidity of the fold weights and of the Weil cone being a point. Margins only decrease (`levinsonErr_succ_le`) and are bounded by the recurrence defect of the orbit correlation, `E_p(φ, h) ≤ Q(φ − φ(· + ph)) = 2(κ(0) − κ(p))` (`levinsonErr_le_recurrence`, `levinsonErr_weilSeq_le`): exact collapse is recurrence of the orbit. **Under RH every lattice of Spec ℤ has no slack:** the Frobenius difference is the cosine series `Σ_ρ m_ρ|φ̂(γ_ρ)|²·2(1 − cos(γ_ρph))` (`weilQuad_frobeniusDiff_eq`), which simultaneous Dirichlet approximation makes arbitrarily small (`exists_frobeniusDiff_lt`), so the margins tend to `0` (`tendsto_levinsonErr_of_riemannHypothesis`), and RH is equivalent to every lattice evolution being positive and singular (`riemannHypothesis_iff_singular_lattices`). **The exact rate is the `ℓ²` threshold (Szegő–Verblunsky):** for a positive evolution the margins tend to `0` iff `Σ_k γ_k² = ∞` and stay above a positive constant iff `Σ_k γ_k² < ∞` (`tendsto_levinsonErr_zero_iff`, `levinsonErr_bounded_below_iff`); under RH the reflection coefficients of every lattice of Spec ℤ are not square-summable, and RH is equivalent to this together with positivity (`not_summable_reflCoeff_sq_of_riemannHypothesis`, `riemannHypothesis_iff_not_summable`). **The growth of `Σγ²`:** the Lyapunov functional satisfies `log(κ(0)/E_n) = −Σ_{k<n}log(1 − γ_k²)` and `Σ_{k<n}γ_k² ≤ log(κ(0)/E_n) ≤ Σ_{k<n}γ_k²/(1 − γ_k²)`, and for Spec ℤ it is at least `log(Q(φ)/Q(φ − φ(· + nh)))` (`log_div_levinsonErr_eq`, `sum_sq_le_log_le`, `log_le_sum_of_recurrence`): the Schur parameters accumulate at `±1` at least as fast as the orbit recurs; the soft regime is the initial segment where every kick lands in its interval for every lattice (`abs_schurParam_lt_of_short`, total length `≤ 181/250`). |

## 6. Tools

**Developed.**
- Two-collar calculus on Weil's form: interior tests, collar locality of the kick
  (`mul_shift_add_interior`), the two-collar form with values in `EReal`, the order isomorphism
  `x ↦ x − c` of `EReal` (`subRealOrderIso`) that moves the kick through the infimum.
- Reflection calculus: collar reflection, polarization of the collar form, even/odd parts,
  `Q`-orthogonality of the sectors, isometry of `σ_A` on Weil's pairing (`weilPair_windowInvolution`).
- Schur–Levinson theory without inverses: one-collar decomposition (`toeplitzForm_cons`), mirror
  decomposition (`toeplitzForm_snoc`), reflection symmetry (`toeplitzForm_comp_rev`), Levinson step,
  positivity criterion, causality (`levinson_congr`), margins as products, degeneration.
- Hermitian Toeplitz calculus on polynomials: sesquilinearity, sums, monomials (`hform_X_pow`),
  `z·` as an isometry (`hform_X_mul`), radical rows (`toeplitz_rows_eq_zero`), root factorization
  arguments for outer ground states, unit-circle and simple zero modes; orthogonality of the
  eigenvectors of the shift modulo the radical and Lagrange interpolation by cofactors, which
  diagonalize a degenerate window (Carathéodory–Fejér).
- Recurrence of orbit correlations: the Frobenius difference as a nonnegative cosine series over
  the zeros under RH, simultaneous Dirichlet approximation of finitely many ordinates
  (HTGeometry `exists_simultaneous_dirichlet`).
- Lattice tests of Spec ℤ: Toeplitz identity (`weilQuad_latticeTest`), independence of translates
  (`latticeTest_ne_zero`), supports and the window–lattice dictionary (`isWindowTest_latticeTest`,
  `window_nonneg_iff_lattices`), weighted Weil sequences, their evenness for every weight
  (`weilSeqW_isEven`), lattice lags and their band (`latticeLag_eq_zero`), the single-kick formula
  (`weilSeqW_single_kick`), the polar/local splitting (`weilSeq_eq_polar_sub_local`).

**Used from the corpus.** CWS (window tests, level, window criterion, window involution); WTZ (stage
form); DZG (stage identity, correlation on the left collar, zero modes, plane identity); ACS (Weil
pairing, `realTests`, positive definiteness under RH, pole coordinates and `localPair`); AHD
(RH ⇔ `Q ≥ 0`); RHTower (full Weil functional, its Hermitian symmetry, cross-correlation formula,
uniqueness of the Weil cone, the zero sum under RH, translates in the transform); SPATL and LST
(coercivity of tests of support length `181/250`); HTGeometry (simultaneous Dirichlet approximation).

**Developed beyond the lattice.**
- Continuity of orbit correlations (`continuous_weilOrbitCorr`, via the lag structure of SRT/AOG) and
  the density of dyadic translates; the corner margin is degenerate (`contMargin_eq_zero`), and the
  first rescaled margin converges to the second zero moment (`tendsto_levinsonErr_one_div_sq`, by
  dominated convergence over the zeros with the `C²` decay `|φ̂(γ)| ≤ K/(1 + |γ|)²`).
- The Szegő–Verblunsky dichotomy for infinite products `∏(1 − x_k)` (`tendsto_prod_one_sub_zero_iff`).
- Short generic bumps (`exists_short_generic`) and the intermediate value argument in the lattice step
  that produces exact degenerations off RH.

## 7. Open research topics

The questions of review-0311 §2.7 are answered in §5, each by a theorem, a labelled equivalence or a
no-go with its survivor. The topics below are the research that the answers open.

1. **Strict orbit Cauchy–Schwarz.** Each prime power must land in an interval of length
   `2√n₀E_m/|k_{m+1}(log n₀)|`; the intervals collapse at the `ℓ²` threshold and only `Λ` survives
   them all. A stage-uniform law of this kind is RH (`riemannHypothesis_iff_levinsonErr_pos`), and its
   first index already decides: RH is `|c_φ(t)| < Q(φ)` for all nonzero bumps and `t ≠ 0`
   (`riemannHypothesis_iff_abs_weilOrbitCorr_lt`). This is the programme's central problem, stated in
   its own language: the translation flow on Weil's form never returns to a bump up to sign.
2. **The first-stage minimization as a moment inequality.** The minimized first-stage form admits no
   finite count identity; CSWT's moment representation of the frozen datum turns the first-stage race
   into an inequality between trivial-divisor moments.
3. **The jet system.** Fixed-scale lattice data coalesce, the first margin is born at order `h²` with
   coefficient `M₂(φ)`, every higher margin is `o(h²)`, and `E_n ≤ h^{2n}Σ_ρ w_ργ_ρ^{2n}`
   (`tendsto_levinsonErr_div_sq`, `levinsonErr_le_tsum_diff`). The higher margins `h^{−2n}E_n(φ, h)`
   should converge to the margins of the
   Hankel (Jacobi) system of the zero measure `Σ_ρ m_ρ|φ̂(γ_ρ)|²δ_{γ_ρ}` on the line — the continuum
   canonical system of a bump, for bumps smooth enough that the moments `M_{2n}` converge.
4. **Asymptotics of the Lyapunov functional.** Under RH the lattice window is the window of the folded
   zero curve (`toeplitzForm_weilSeq_eq_tsum`), so `E_n` is squeezed between the margins of its finite
   pieces (`levinsonErr_truncation_le`) and the recurrence bound; the rate of `log(κ(0)/E_n)` along a
   lattice is governed by the Diophantine properties of the angles `hγ`.

## 8. Pillar theorems

| Theorem | Lean |
|---|---|
| The kick reads collar data only | `mul_shift_add_interior`, `corr_add_interior`, `weilQuad_add_interior` |
| Two-collar form, kick law, stage criterion | `twoCollarForm`, `twoCollarForm_add_interior`, `iInf_weilQuad_add_interior`, `stage_criterion` |
| Reflection invariance of the two-collar form | `corr_windowInvolution`, `stageForm_windowInvolution`, `twoCollarForm_windowInvolution` |
| The two-collar form is born zero and grows | `twoCollarForm_mono`, `corr_birth`, `twoCollarForm_birth` |
| The kick is the collar reflection | `corr_eq_collar_windowInvolution`, `corr_eq_of_even`, `corr_eq_of_odd`, `weilQuad_eq_of_even`, `weilQuad_eq_of_odd` |
| Parity splitting; pre-installed sign | `weilPair_even_odd`, `window_nonneg_iff_sectors`, `collar_antisymmetric_of_frozen_negative_even`, `collar_symmetric_of_frozen_negative_odd` |
| Zero modes have reflection parity; gap law | `weilPair_windowInvolution`, `zeroMode_evenPart`, `zeroMode_oddPart`, `exists_parity_zeroMode`, `parity_zeroMode_collars`, `gap_law` |
| Unique continuation from an end collar | `eq_zero_of_zeroMode_vanish_collar`, `zeroMode_eq_of_eq_on_collar` |
| Gap continuation is not structural | `curveThree`, `curveThree_isEven`, `toeplitzForm_curveThree_four`, `curveThree_first_critical` |
| Lattice Schur data coalesce under refinement | `reflCoeff_zero_eq`, `tendsto_reflCoeff_zero`, `tendsto_levinsonErr_one`, `tendsto_levinsonErr_of_rh` |
| The first prime stage opens positive | `weilQuad_nonneg_of_short`, `windowLevel_eq_two`, `firstStage_criterion_of_le`, `firstStage_kick_le_frozen` |
| One- and two-collar decompositions of a lattice stage | `toeplitzForm_cons`, `toeplitzForm_snoc`, `toeplitzForm_two_collar`, `twoCollar_isLeast` |
| Levinson evolution | `isPredictor_snoc`, `predErr_snoc`, `levinson_isPredictor`, `predErr_levinson`, `levinsonErr_succ_eq_mul` |
| Positivity is the evolution; prediction interval | `posDef_succ_iff`, `toeplitzForm_posDef_iff`, `posDef_succ_iff_abs_schur_lt`, `levinsonErr_pos_iff` |
| Kick law, causality, margins | `schurParam_eq`, `levinson_congr`, `levinsonErr_eq_prod`, `levinsonErr_succ_le` |
| Degeneration | `toeplitzForm_kernel_of_first_critical`, `levinsonVec_rev_of_sq_eq_one`, `reflCoeff_sq_of_critical` |
| Outer ground states; angles on the circle | `norm_gt_one_of_predictor_root`, `toeplitz_rows_eq_zero`, `norm_eq_one_of_critical_root` |
| The angles are simple and number `n + 1` | `hform_zeroMode_eq_zero`, `natDegree_zeroMode`, `not_sq_dvd_zeroMode`, `zeroMode_roots` |
| A degenerate window is a curve (Carathéodory–Fejér) | `hform_orth_of_eigen`, `eq_sum_cofactor`, `hform_eq_sum_diag`, `degenerate_window_is_curve` |
| A curve degenerates at its number of angles | `curveData`, `curveData_isEven`, `toeplitzForm_curveData`, `curveData_posDef`, `curveData_not_posDef`, `curve_first_critical` |
| The higher margins are born later | `diffVec`, `sum_diffVec_mul_pow`, `levinsonErr_le_tsum_diff`, `tendsto_levinsonErr_div_sq_of_two_le`, `tendsto_levinsonErr_div_sq` |
| RH is decided on two sites | `abs_weilOrbitCorr_lt`, `exists_abs_weilOrbitCorr_eq`, `riemannHypothesis_iff_abs_weilOrbitCorr_lt`, `riemannHypothesis_iff_two_site_posDef` |
| Spec ℤ is a curve on every lattice | `weilOrbitCorr_eq_tsum`, `toeplitzForm_weilSeq_eq_tsum`, `riemannHypothesis_iff_folded_curve`, `levinsonErr_ge_of_le`, `toeplitzForm_truncation_le`, `levinsonErr_truncation_le` |
| The pole is a hyperbolic pair of angles | `weilSeq_eq_polar_sub_local`, `toeplitzForm_polar`, `toeplitzForm_polar_eq_hyperbolic` |
| The trivial angles carry one negative square | `polarSeq_single`, `polarSeq_firstDiff`, `polarSeq_signature`, `weilSeq_eq_polarSeq_sub` |
| Forbidding lattice zero modes is RH | `weilOrbitCorr_neg`, `levinsonErr_one`, `zeta_orbitCorr_eq`, `exists_short_generic`, `exists_degenerate_lattice_of_not_riemannHypothesis`, `riemannHypothesis_iff_no_degenerate_lattice` |
| Szegő–Verblunsky law; the rate for Spec ℤ | `tendsto_prod_one_sub_zero_iff`, `tendsto_levinsonErr_zero_iff`, `levinsonErr_bounded_below_iff`, `not_summable_reflCoeff_sq_of_riemannHypothesis`, `riemannHypothesis_iff_not_summable` |
| The Lyapunov functional and the growth of `Σγ²` | `log_div_levinsonErr_eq`, `sum_sq_le_log_le`, `log_le_sum_of_recurrence` |
| The continuum margin is the dyadic limit | `continuous_weilOrbitCorr`, `weilQuad_sum_scaleShift`, `continuous_weilQuad_cornerCombo`, `contMargin`, `tendsto_levinsonErr_dyadic_contMargin` |
| The corner margin is degenerate | `weilQuad_cornerCombo_single`, `contMargin_nonpos`, `contMargin_eq_zero`, `tendsto_levinsonErr_dyadic_zero` |
| The first margin is born quadratically | `zeroSecondMoment`, `summable_zeroTerm_mul_sq`, `zeroSecondMoment_eq_deriv`, `tendsto_one_sub_cos_div_sq`, `tendsto_levinsonErr_one_div_sq` |
| Margins are bounded by recurrence | `toeplitzForm_recurrence`, `levinsonErr_le_recurrence`, `two_mul_weilSeq_sub`, `levinsonErr_weilSeq_le` |
| Refining the lattice lowers the margin; dyadic limits | `toeplitzForm_levinsonVec`, `levinsonErr_le_toeplitzForm`, `latticeTest_refineVec`, `levinsonErr_refine_le`, `levinsonErr_dyadic_antitone`, `tendsto_levinsonErr_dyadic` |
| No slack: lattices of Spec ℤ are singular (RH-equivalence) | `weilQuad_frobeniusDiff_eq`, `exists_frobeniusDiff_lt`, `tendsto_levinsonErr_of_riemannHypothesis`, `riemannHypothesis_iff_singular_lattices` |
| Lattice windows of Spec ℤ | `weilPair_latticeTranslate`, `weilSeq_isEven`, `weilQuad_latticeTest`, `latticeTest_ne_zero` |
| A window is the union of its lattices | `latticeTest_eq_zero_of_not_mem`, `isWindowTest_latticeTest`, `window_nonneg_iff_lattices`, `window_pos_iff_lattices` |
| RH as a causal evolution (equivalences) | `toeplitzPosDef_of_riemannHypothesis`, `riemannHypothesis_iff_levinsonErr_pos`, `riemannHypothesis_iff_abs_reflCoeff_lt_one`, `not_riemannHypothesis_of_first_critical` |
| Locality, causality and kicks in the primes | `weilSeqW_isEven`, `latticeLag_eq_zero`, `weilSeqW_congr`, `levinson_weilSeqW_congr`, `weilSeqW_single_kick`, `schurParam_single_kick` |
| Rigidity interval of a prime-power weight | `posDef_update_iff` |
| The evolution starts positive | `weilQuad_pos_of_short`, `toeplitzPosDef_of_short`, `levinsonErr_pos_of_short`, `abs_schurParam_lt_of_short` |
| The lattice selects `Λ`; every kick is necessary | `lattice_selects_vonMangoldt`, `exists_lattice_failure_of_ne`, `exists_lattice_failure_of_delete`, `exists_free_lattice_failure` |

## 9. Traps

| Trap | Truth |
|---|---|
| The new fold is a cost the frozen form must pay | It is the collar Rosati form: a positive source on two of four sectors; frozen-negative tests are forced into those sectors (`collar_antisymmetric_of_frozen_negative_even`) |
| The two-collar form needs resolvents | It is an infimum over interior perturbations; the kick commutes with it (`iInf_weilQuad_add_interior`) |
| The stage step starts with a gap to spend | At the birth of a stage the two-collar form and the kick are both zero (`twoCollarForm_birth`, `corr_birth`); everything is decided by their growth in the collar width |
| A lattice window can decide RH | One bump and one step see a slice; RH is every lattice of every bump at every step (`riemannHypothesis_iff_levinsonErr_pos`), and window `W_A` is exactly the lattices of total length `≤ A` (`window_nonneg_iff_lattices`) |
| A finite lattice is a finite carrier, hence useless | It is a carrier of the evolution, not of the sign: its margins are exact, causal and multiplicative, and its degenerations are rigid |
| The kick of a prime power changes the whole lattice evolution | It moves one Schur parameter at its stage; everything before is frozen (`schurParam_single_kick`) |
| Positivity of a window is a condition on all of its data | Given the frozen window, it is one inequality `|β_n| < E_n` for the newest datum |
| A degenerate window has an arbitrary zero mode | It is a single palindrome up to sign with nonzero ends and `n + 1` simple zeros on the unit circle; the window is then a curve window with positive weights |
| The pole is a nuisance term of the lattice form | It is the hyperbolic pair of angles `e^{±h/2}`, the trivial Frobenius eigenvalues of the lattice |
| The continuum zero mode can be cut along a gap into independent pieces | The pieces have equal energy and equal Weil orbit correlations across the gap (`gap_law`) |
| Unique continuation of zero modes is a soft property | Only from the collars; across interior gaps it fails for curves (`curveThree_first_critical`) |
| The lattice Schur parameters converge to a continuous Schur function | At fixed index they coalesce (`tendsto_reflCoeff_zero`) |
| The lattice margins converge to a meaningful continuum margin | The corner margin is `0` under RH (`contMargin_eq_zero`); only rescaled margins survive (`tendsto_levinsonErr_one_div_sq`) |
| Zero modes are a separate phenomenon from RH | Off RH some lattice degenerates exactly; forbidding lattice zero modes is RH (`riemannHypothesis_iff_no_degenerate_lattice`) |
| Margin collapse needs a quantitative rate to be meaningful | Its exact content is the `ℓ²` threshold of the Schur parameters (`tendsto_levinsonErr_zero_iff`) |
| A canonical-system formulation removes the wall | It changes the toolset, not the wall: margins are products `∏(1 − γ_k²)` that the arithmetic must keep away from zero at every stage |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| WTZ (`WindowTowerOfSpecZ`) | window algebra, stages, stage form and transfer; GWZ studies how positivity passes the stages |
| DZG (`DimensionZeroGeometryOfSpecZ`) | the dimension-zero chapter of the same theory (negative); stage identity in every gauge; zero modes as radical |
| CWS (`CohomologyOfWindowsOfSpecZ`) | single windows; window criterion; curve windows (Toeplitz forms of power sums, saturation at the number of distinct Frobenius values) — the degenerate lattice windows of GWZ are of this kind |
| ACT (`ArithmeticCriticalityTheory`) | whole-line ground states and Doob transforms; GWZ works on windows and stages, where ground states are the Levinson vectors |
| AOG, HKT | orbit correlations, orbit Hodge index, Krein–Langer index on groups; GWZ adds the causal Schur evolution of the orbit correlation sampled on a lattice |
| AHD | complete family at the critical curve; the trivial additive angle (2.6.4) |
| CSWT (`CanonicalSystemOfTheWindowTower`) | the continuum register of the same recursion: stage tests split into collar and interior pieces, the frozen two-collar form in closed form (trivial-divisor moments, earlier-fold transports), window growth as a translation contraction with a Carathéodory disk per stage. GWZ's two-collar form is the infimum of CSWT's frozen form over the interior; GWZ's lattice prediction interval `|β_n| < E_n` is the discrete form of CSWT's stage disk |
| SZ (RHTower `Suzuki`) | screw functions and Krein–Schur blocks; the nearest carrier of the continuum canonical system |
| F1/F2 (pipeline) | tower and reflection assemblies; GWZ supplies their exact stage-step language |

## 11. Success criteria and criteria for contributions

The programme succeeds when each question of §5 has a theorem as answer — an identity, a labelled
equivalence, a classification, or a no-go with its strongest positive survivor — and the stage step
is reduced to an exact statement about collar data alone. In the lattice register this is achieved:
the stage step is `|β_n| < E_n` for one new datum, with the frozen data closed under the Levinson law.
In the continuum the stage step is the stage criterion on collar classes, the lattice margins of a
bump are born at order `h²` with coefficient its second zero moment, zero modes of a degenerate
lattice continue uniquely from either end collar, and forbidding them is RH. Every question of review-0311 §2.7 has a theorem as answer (§5).

The criteria that review-0311 §2.7 sets for the field, and where they are met:

| Criterion | Met by |
|---|---|
| Locality and causality | `weilSeqW_congr`, `levinson_weilSeqW_congr`, `levinson_congr`; continuum: `corr_add_interior` |
| Exactness (unbounded rank, no lossy payments) | Levinson evolution and one/two-collar decompositions are identities; `toeplitzForm_posDef_iff`, `stage_criterion` |
| Signed kicks; the pre-installed sign | `corr_eq_of_even`, `corr_eq_of_odd`, `collar_antisymmetric_of_frozen_negative_even`, `collar_symmetric_of_frozen_negative_odd`, `schurParam_single_kick` |
| Reflection of Rosati type | `corr_eq_collar_windowInvolution`, `twoCollarForm_windowInvolution`, `window_nonneg_iff_sectors` |
| Selection by positivity; curves reproduced; node criticality | `lattice_selects_vonMangoldt`, `degenerate_window_is_curve`, `curve_first_critical`, `exists_lattice_failure_of_delete`, `exists_free_lattice_failure` |
| Prime-blind output | the lattice evolution is defined for every weight (`weilSeqW`) and selects `Λ` (`lattice_selects_vonMangoldt`, `exists_lattice_failure_of_ne`) |
| Dimension | DZG: positivity on the imaginary Tate line, none in real dimension |

The first tests that review-0311 §2.7 names, and their status here:

| Test | Status |
|---|---|
| A8 (first two-collar form) | Stage criterion and dominance of the kick of `2` for `log 2 ≤ A ≤ 181/250` (`firstStage_criterion_of_le`, `firstStage_kick_le_frozen`); no finite count identity represents the first-stage form (CWS `not_exists_countIdentity`); its closed form is open |
| A5 (first prime stage to `log 3`) | Proved on `[log 2, 181/250]`; the range `(181/250, log 3)` is a certified computation, outside this programme |
| 2.5.1 at the second stage | Lattice: closed form at every stage (`toeplitzForm_two_collar`, Levinson law); continuum: open |
| A10 (function-field calibration) | Curves calibrated: a degenerate window is a curve and a curve first degenerates at its number of angles (`degenerate_window_is_curve`, `curve_first_critical`); twisted horizon layers and higher-genus fakes are AHD's |
| A6 (odd unit window) | Not addressed here (OWU) |

A contribution must:
1. concern the passage of positivity through the growth of the window (two-collar forms, kicks,
   canonical systems, ground states, zero modes, angles, margins), not re-prove single-window facts;
2. be exact: an identity, an equivalence, a classification, a rigidity law, never an estimate that
   loses a factor;
3. be local and causal: say which primes and which lengths it reads;
4. say what it does on fakes and on curves over `𝔽_q`;
5. be unconditional; RH-equivalent statements are labelled and count only when they move the
   problem to an object with new structure.

## 12. Big picture

A window grows by one correlation per prime power, and that correlation reads only the two collars
of the window. GWZ makes this exact: in the continuum the frozen form, minimized over the interior,
is a two-collar form; the kick subtracts from it exactly and is, on each reflection sector, the
signature form of the collar reflection. Positivity of a stage is the domination of this collar
Rosati form by the frozen two-collar form, and every frozen-negative test is forced into the sector
where the kick is a positive source.

On a lattice of translates the same structure closes into an exact canonical system. The two-collar
form of a stage is `[[E, β], [β, E]]`; a new site is admitted iff the newest Weil datum lands within
`E` of the frozen prediction; margins multiply by `1 − γ²`; a prime power acts as one kick on one
Schur parameter at its stage, and its weight is pinned to an interval of length proportional to the
margin. A positive lattice window has an outer ground state; a degenerate one has a unique zero mode
with simple angles on the unit circle and is the window of a curve with positive multiplicities, the
pole being the hyperbolic pair `e^{±h/2}`. A window of length `A` is exactly its lattices of total
length `≤ A`. RH is the statement that, for every bump and every step, Spec ℤ never degenerates:
every margin of its causal evolution stays positive — equivalently, no lattice ever degenerates into
a curve — and only the weight `Λ` can achieve this. Under RH these margins also tend to zero along
every lattice, exactly at the `ℓ²` threshold of the Schur parameters: the evolution is singular,
with no slack anywhere. Refining the lattice, the first margin is born at order `h²` with coefficient
the second zero moment of the bump, and zero modes of a degenerate lattice continue uniquely from
either end collar.

What GWZ does not supply is a reason for the kicks to land in their prediction intervals. The
evolution is exact and causal, the margins are products that collapse, and the prime-power weights
are pinned more tightly at every stage; the sign must come from an arithmetic statement about all
kicks at once, made in this language.

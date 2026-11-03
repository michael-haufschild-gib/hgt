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
The pole is the pair of hyperbolic angles `e^{±h/2}` of every lattice (`toeplitzForm_polar_eq_hyperbolic`).

## 5. Questions and answers

| Question (review-0311 §2.7) | Answer |
|---|---|
| What is the two-collar form of a stage, and what law carries it across a prime kick (2.5.1)? | **Continuum:** the infimum `S^N_A` of the frozen form over interior tests; it depends only on collar data (`twoCollarForm_add_interior`), is `σ_A`-invariant (`twoCollarForm_windowInvolution`), and the kick subtracts `2w c_H(ℓ)` from it exactly (`iInf_weilQuad_add_interior`); the window is nonnegative iff `2w c_H ≤ S^N_A` (`stage_criterion`). Within the stage both sides are born zero — `S^N_ℓ ≡ 0` and `c_H(ℓ) = 0` on `W_ℓ` (`twoCollarForm_birth`, `corr_birth`) — and the two-collar form grows with the collar width (`twoCollarForm_mono`): positivity is a race between two collar functionals, restarted at every prime power. The closed form of the frozen datum on stage tests `x_L + y + x_R` — trivial-divisor moments and earlier-fold transports, explicit at the first two stages — and the growth law of a window as a translation contraction (the Carathéodory disk of a stage) are CSWT's (`frozenTwoCollar_eq_transmitted`, `stage_nonneg_iff_disk`). **Lattice (closed form):** the two-collar form of a stage is `[[E_n, β_n], [β_n, E_n]]` (`toeplitzForm_two_collar`, `twoCollar_isLeast`), the equal diagonal coming from the reflection; across the stage the law is `E_{n+1} = E_n − β_n²/E_n` with the new predictor `(a − γJa, −γ)` (`isPredictor_snoc`, `predErr_snoc`); the newest datum enters `β_n` with coefficient one, `β_n = κ(n+1) − π_n` (`schurParam_eq`), and a prime kick moves exactly one Schur parameter (`schurParam_single_kick`). |
| Does the window jump process have a positive ground state at every length, and how does it pass a stage (2.6.1)? | **Lattice: yes, exactly when the window is positive.** Positive definiteness of a lattice window is the positivity of every margin of its Levinson evolution (`toeplitzForm_posDef_iff`); the ground state (Levinson vector) is then outer (`norm_gt_one_of_predictor_root`), and it passes a stage by the Levinson step. **RH-equivalent for Spec ℤ:** RH iff every lattice margin of every bump at every step is positive (`riemannHypothesis_iff_levinsonErr_pos`); unconditionally every lattice is positive while its total length stays below `181/250`, past the first prime (`levinsonErr_pos_of_short`). **Selection:** for an arbitrary prime weight, all margins stay positive iff RH and the weight is `Λ` (`lattice_selects_vonMangoldt`); deleting one prime power or all of them makes some lattice degenerate (`exists_lattice_failure_of_delete`, `exists_free_lattice_failure`). Continuum: the passage is exact in every gauge (DZG); existence at every length is RH. |
| Is there a unique-continuation principle forbidding a zero mode with full mass on both collars? | **Lattice: the zero mode is rigid.** At a first critical length the radical is one line (`toeplitzForm_kernel_of_first_critical`), spanned by a palindrome up to the sign `−γ_n` with end coefficients `1` and `−γ_n = ∓1` (`levinsonVec_rev_of_sq_eq_one`, `reflCoeff_sq_of_critical`), its polynomial has exactly `n + 1` simple zeros, all on the unit circle (`zeroMode_roots`), and the frozen window is the Toeplitz form of the power sums of these angles with positive weights (`degenerate_window_is_curve`); for Spec ℤ such a window refutes RH (`not_riemannHypothesis_of_first_critical`). **Continuum:** the radical is `σ_A`-invariant, every edge has a reflection parity (`exists_parity_zeroMode`), and a zero mode vanishing on an interior gap splits into two pieces of equal energy with equal Weil orbit correlations across the gap (`gap_law`). A continuum UCP excluding the balanced split is open. |
| Which positive involution on two-collar data makes `σ_A` a Rosati positivity? | **The collar reflection `R`.** The kick is the collar Rosati form `c_H = ∫_L H·(σ_AH)∘R` (`corr_eq_collar_windowInvolution`), and on the two `σ_A`-sectors it is `±` the signature form of `R` (`corr_eq_of_even`, `corr_eq_of_odd`). The kick is a positive source exactly on the even–`R`-antisymmetric and odd–`R`-symmetric collar data; on a nonnegative window every frozen-negative even (odd) test is forced into the `R`-antisymmetric (symmetric) sector (`collar_antisymmetric_of_frozen_negative_even`, `collar_symmetric_of_frozen_negative_odd`). Positivity of the stage is the domination of this Rosati form by the frozen two-collar form. |
| What is the `ℤ`-analogue of the trivial Frobenius angle, and what weight does Weil's form carry there (2.6.4)? | **Lattice reading:** a lattice of step `h` folds the zero ordinates to angles `hγ mod 2π`. The trivial Frobenius eigenvalues are the pole: on every lattice it is the hyperbolic pair of angles `e^{±h/2}`, contributing the pole plane `2A(φ)B(φ)·V(e^{h/2})V(e^{−h/2})` (`weilSeq_eq_polar_sub_local`, `toeplitzForm_polar`, `toeplitzForm_polar_eq_hyperbolic`), exactly as `1` and `q` normalized by `√q` over `𝔽_q`. A degenerate lattice window has finitely many simple unitary angles with positive weights (`degenerate_window_is_curve`): it is a curve window. Under RH no lattice of Spec ℤ degenerates (`toeplitzPosDef_of_riemannHypothesis`): Spec ℤ has infinitely many angles on every lattice. The weight of the untwisted horizon window at the trivial additive angle is AHD's question (2.6.4) and is not decided here. |
| How do the soft horizons `≍ e^{−A/2}` become the exact doubly exponential margins? | **Margins are products of Schur factors:** `E_n = κ(0)∏_{k<n}(1 − γ_k²)` (`levinsonErr_eq_prod`). Exact collapse of margins is the accumulation of the Schur parameters at `±1`; each kick is admissible only in an interval of length `2√n₀E_m/|k_{m+1}(log n₀)|` (`posDef_update_iff`), which shrinks with the margin, and no value other than `Λ(n₀)` survives every lattice (`exists_lattice_failure_of_ne`): the exact form of the rigidity of the fold weights and of the Weil cone being a point. Margins only decrease (`levinsonErr_succ_le`) and are bounded by the recurrence defect of the orbit correlation, `E_p(φ, h) ≤ Q(φ − φ(· + ph)) = 2(κ(0) − κ(p))` (`levinsonErr_le_recurrence`, `levinsonErr_weilSeq_le`): exact collapse is recurrence of the orbit. **Under RH every lattice of Spec ℤ has no slack:** the Frobenius difference is the cosine series `Σ_ρ m_ρ|φ̂(γ_ρ)|²·2(1 − cos(γ_ρph))` (`weilQuad_frobeniusDiff_eq`), which simultaneous Dirichlet approximation makes arbitrarily small (`exists_frobeniusDiff_lt`), so the margins tend to `0` (`tendsto_levinsonErr_of_riemannHypothesis`), and RH is equivalent to every lattice evolution being positive and singular (`riemannHypothesis_iff_singular_lattices`); the soft regime is the initial segment where every kick lands in its interval for every lattice (`abs_schurParam_lt_of_short`, total length `≤ 181/250`). |

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

**To develop.**
- The continuum limit `h → 0` of the lattice canonical system (Krein's continuous Schur algorithm with
  atoms at `log n`); its first step — monotonicity of margins under refinement and existence of the
  dyadic limits under RH — is proved.
- Szegő's limit law in full (a positive a.c. part gives a positive limit margin); for Spec ℤ the
  singular half is proved under RH (`tendsto_levinsonErr_of_riemannHypothesis`).
- A continuum unique-continuation principle for the window Euler–Lagrange equation.

## 7. Open research topics

1. **The continuum two-collar form at the first prime** (A8). CSWT reduces the frozen datum at the
   first stage to `Q(x_L) + Q(x_R) + Φ_ε(μ(x_L), ν(x_R))`, a function of the trivial-divisor moments;
   open is `Φ_ε` itself, i.e. the minimization over the interior. On the lattice the minimization is
   done: `[[E, β], [β, E]]`.
2. **Ground states at every length (2.6.1).** Lattice: outer Levinson vectors exist exactly as long
   as the margins are positive. Open: a stage-uniform construction for Spec ℤ, i.e. a reason why each
   kick lands in its prediction interval.
3. **Continuum unique continuation.** Exclude the balanced split of `gap_law`; on the lattice the
   zero mode is already rigid.
4. **The continuum limit.** Refining a lattice lowers its margin, `E_{kn}(φ, h/k) ≤ E_n(φ, h)`
   (`levinsonErr_refine_le`), and under RH the dyadic refinements of a fixed total length converge
   (`levinsonErr_dyadic_antitone`, `tendsto_levinsonErr_dyadic`). Open: identify the limit with the
   continuum two-collar margin, and the limits of Schur parameters and predictors — the Krein system
   of Weil's distribution with jumps at `log n`.
5. **Exact margins.** Under RH the margins of every lattice tend to `0`
   (`tendsto_levinsonErr_of_riemannHypothesis`); open is the rate — how fast the Schur parameters of
   Spec ℤ accumulate at `±1` along a lattice, and the corresponding collapse of the rigidity
   intervals of the prime-power weights.
6. **The trivial angle.** Combine the lattice angle reading with AHD's additive-frequency
   decomposition of the horizon layer.

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
| One- and two-collar decompositions of a lattice stage | `toeplitzForm_cons`, `toeplitzForm_snoc`, `toeplitzForm_two_collar`, `twoCollar_isLeast` |
| Levinson evolution | `isPredictor_snoc`, `predErr_snoc`, `levinson_isPredictor`, `predErr_levinson`, `levinsonErr_succ_eq_mul` |
| Positivity is the evolution; prediction interval | `posDef_succ_iff`, `toeplitzForm_posDef_iff`, `posDef_succ_iff_abs_schur_lt`, `levinsonErr_pos_iff` |
| Kick law, causality, margins | `schurParam_eq`, `levinson_congr`, `levinsonErr_eq_prod`, `levinsonErr_succ_le` |
| Degeneration | `toeplitzForm_kernel_of_first_critical`, `levinsonVec_rev_of_sq_eq_one`, `reflCoeff_sq_of_critical` |
| Outer ground states; angles on the circle | `norm_gt_one_of_predictor_root`, `toeplitz_rows_eq_zero`, `norm_eq_one_of_critical_root` |
| The angles are simple and number `n + 1` | `hform_zeroMode_eq_zero`, `natDegree_zeroMode`, `not_sq_dvd_zeroMode`, `zeroMode_roots` |
| A degenerate window is a curve (Carathéodory–Fejér) | `hform_orth_of_eigen`, `eq_sum_cofactor`, `hform_eq_sum_diag`, `degenerate_window_is_curve` |
| The pole is a hyperbolic pair of angles | `weilSeq_eq_polar_sub_local`, `toeplitzForm_polar`, `toeplitzForm_polar_eq_hyperbolic` |
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
In the continuum the stage step is the stage criterion on collar classes; the continuum canonical
system and unique continuation remain.

The criteria that review-0311 §2.7 sets for the field, and where they are met:

| Criterion | Met by |
|---|---|
| Locality and causality | `weilSeqW_congr`, `levinson_weilSeqW_congr`, `levinson_congr`; continuum: `corr_add_interior` |
| Exactness (unbounded rank, no lossy payments) | Levinson evolution and one/two-collar decompositions are identities; `toeplitzForm_posDef_iff`, `stage_criterion` |
| Signed kicks; the pre-installed sign | `corr_eq_of_even`, `corr_eq_of_odd`, `collar_antisymmetric_of_frozen_negative_even`, `collar_symmetric_of_frozen_negative_odd`, `schurParam_single_kick` |
| Reflection of Rosati type | `corr_eq_collar_windowInvolution`, `twoCollarForm_windowInvolution`, `window_nonneg_iff_sectors` |
| Selection by positivity; curves reproduced; node criticality | `lattice_selects_vonMangoldt`, `degenerate_window_is_curve`, `exists_lattice_failure_of_delete`, `exists_free_lattice_failure` |
| Prime-blind output | the lattice evolution is defined for every weight (`weilSeqW`) and selects `Λ` (`lattice_selects_vonMangoldt`, `exists_lattice_failure_of_ne`) |
| Dimension | DZG: positivity on the imaginary Tate line, none in real dimension |

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
every margin of its causal evolution stays positive — and only the weight `Λ` can achieve this.
Under RH these margins also tend to zero along every lattice: the evolution is singular, with no
slack anywhere.

What GWZ does not supply is a reason for the kicks to land in their prediction intervals. The
evolution is exact and causal, the margins are products that collapse, and the prime-power weights
are pinned more tightly at every stage; the sign must come from an arithmetic statement about all
kicks at once, made in this language.

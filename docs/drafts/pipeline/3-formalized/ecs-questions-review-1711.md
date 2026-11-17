# Review 1711 — ECS Questions (E-Q6 and E-Q1)

- **ID:** ecs-questions-1711
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** docs/reports/review-1711/route-ecs.md §6
- **Statement:** Complete unconditional solutions, exact characterisations, implications, corollaries, and sharp model-separation laws in Lean 4 for the questions posed in §6 of `docs/reports/review-1711/route-ecs.md`, ordered from easiest (`E-Q6`) to hardest (`E-Q1`).

## Summary of Verdicts & Lean Formalizations (Easiest → Hardest)

| Order | Question | Final Verdict & Unconditional Mathematical Solution | Lean Modules (`ExclusionOfTheCriticalState/Index/`) | Status |
|---|---|---|---|---|
| 1 | **E-Q6**: Can $\zeta$ have exactly one quartet $Q(\rho_0) = \{\rho_0, \overline{\rho_0}, 1-\rho_0, 1-\overline{\rho_0}\}$ off $\operatorname{Re} s = 1/2$? (Secular equation of $a(W_0)$ via the on-line resolvent transferred to $\zeta$, two-rung ladder, wall laws, prime form of $F^+$, two-mode averaged state, and single-wave $\psi(x)-x$.) | **REALIZED in every single-input model (two-sided rational-prime edit with integer norms and count $Ax + O(x^\beta)$, over-regular Beurling $\zeta$ at $3/5 \pm i$, positive degree-1 Euler twins at every $\sigma \in (1/2, 1)$, and finite-layer tempered `quartetConfig`); OPEN on $\zeta$ as the minimal $N_{\text{quartet}} = 1$ (`#Z_right = 2`) core of Obstacle B13, where joint $(\text{atomic }\Lambda_B \ge 0) \wedge (\Gamma_{\mathbb{R}}\text{ FE})$ pins $\zeta_B = \zeta$ and excluding $Q(\rho_0)$ is equivalent to $\mathrm{RH} \vee (4 \le \#Z_{\text{right}})$.** Unconditionally on $\zeta$: (i) the Birman–Schwinger on-line resolvent $R_a$ transfers to `CriticalHalfLineEnergyDomain` (`exists_zetaOnLineResolvent`, `solvesZetaOnLineResolvent_ae_unique`, `nullVector_ae_eq_offLineResolvent_of_finiteOffLine`); (ii) the $4 \times 4$ real secular determinant $\det(I_4 + 2m G_{\text{on}}(a) J_4) = 0$ characterizes confined-null-vector ratios **iff** (`exists_confinedNullVector_iff_quartetSecularDet_eq_zero`), has positive root set $\{a(W_0), a(R_2)\}$ with closed-form supremum $a(W_0) = \sup\text{Roots}$ and infimum $a(R_2) = \inf\text{Roots}$ purely in terms of $\rho_0, m$ and $G_{\text{on}}$ (`singleQuartet_groundAlias_eq_secularSup`, `quartetAlias_eq_secular_extremal_roots`), and satisfies $\det > 0$ for $a > a(W_0)$ (`quartetSecularDet_pos_below_threshold`); (iii) the ladder has **exact** null-ratio spectrum $\{W_0, R_2\}$ ($0 < W_0 < R_2$) with 1D a.e. simplicity on both rungs, `IsNegativePlane R F₀ F₁` for all $R > R_2$, Cauchy interlacing $0 < W_0 < R_1 \le R_2$ (`singleQuartet_complete_twoRung_ladder`), and joint Bessel trace bound $a(W_0) + a(R_2) \le 2m/\sqrt{16 - (\operatorname{Re}\rho_0 - 1/2)^2}$ (`singleQuartet_alias_sum_le`); (iv) diagonal and cross-rung wall laws (`nullVector_crossWallLaw`, `nullVector_diagonalWallLaw`) and prime/PNT forms of $F_0^+, F_1^+$ (`singleQuartet_twoRung_wall_and_primeForm`) hold; (v) for **both** rungs $(W_0, F_0)$ and $(R_2, F_1)$, `averagedState F` equals $2m\operatorname{Re}(c_+ e^{(z_+ - 8)t}) + O(e^{-8t})$ with $c_+ \ne 0$ (`nullVector_averagedState_finiteLayer`, `singleQuartet_nullVector_averagedState_singleConjugatePair`); (vi) $\exists \rho_0,\text{HasSingleOffLineQuartet }\rho_0$ is unconditionally 6-way equivalent to $\#Z_{\text{right}} = 2$, $\neg\mathrm{RH} \wedge \#Z_{\text{right}} \le 2$, `realPacketNegIndex = 2`, $\neg\mathrm{RH}$ with maximal confined negative index $2$, and $\|\psi(x) - x + 2m\operatorname{Re}(x^{\rho_0}/\rho_0)\| \le K\sqrt{x}\log^2 x$ (`hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave`, `exists_singleOffLineQuartet_ecs_tfae`, `no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros`). | `TheOnLineResolventOfAFiniteLayer.lean`, `SingleQuartetSecularAndWallRigidity.lean` | formalized |
| 2 | **E-Q1**: Does $\Phi_F(p) = \widehat{S}F(p) + \mathcal{L}F(-1/2)/(p+1/2)$ continue holomorphically to $\operatorname{Re} p < 0$ for every $F \in \mathcal{H}$? | **Equivalent globally to `RiemannHypothesis` and `PurePrimeHeadContinuation` (`eq1_global_and_profile_synthesis`); solved unconditionally for every individual profile $F \in \mathcal{H}$:** `HasBeyondTheWallPrimeContinuation F` holds **if and only if** $\mathcal{L}F(z) = 0$ at every left-of-line centred zero $z$ of $\zeta$ ($\operatorname{Re} z < 0$), with **no** simplicity or finiteness assumption (`hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros`, `purePrimeHeadContinuation_profile_iff_vanish_leftZeros`). Under `FiniteOffLine`, every profile in the continuation subspace has nonnegative bare Weil energy $B(G, G) = \sum_{\text{on}} \|\mathcal{L}G(z)\|^2 \ge 0$ (`bareMixedEnergy_nonneg_of_hasBeyondTheWallPrimeContinuation`); under `HasSingleOffLineQuartet ρ₀`, $\mathcal{H} = (\mathbb{R}F_0 \oplus \mathbb{R}F_1) \oplus \{G \in \mathcal{H} : \text{HasBeyondTheWallPrimeContinuation } G\}$ is an internal direct sum into $B < 0$ and $B \ge 0$ subspaces (`singleQuartet_directSum_primeContinuation`), containing a nonzero pole-neutral ladder state whose bare `primeHead` fails continuation (`singleQuartet_exists_poleNeutral_no_primeHeadContinuation`). | `TheOnLineResolventOfAFiniteLayer.lean`, `SingleQuartetSecularAndWallRigidity.lean` | formalized |

## Formalized Declarations

### `GaloisForLFunctions.ExclusionOfTheCriticalState` (`Index/TheOnLineResolventOfAFiniteLayer.lean`)
- `hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros`
- `purePrimeHeadContinuation_profile_iff_vanish_leftZeros`
- `hasBeyondTheWallPrimeContinuation_iff_vanish_upperLeft_of_finiteOffLine`
- `domain_zeroParseval_of_finiteOffLine`
- `bareMixedEnergy_eq_onLine_add_offLine_of_finiteOffLine`
- `bareMixedEnergy_eq_onLineMixed_add_re_offLine`
- `bareMixedEnergy_nonneg_of_hasBeyondTheWallPrimeContinuation`
- `exists_zetaOnLineResolvent`
- `solvesZetaOnLineResolvent_ae_unique`
- `nullVector_ae_eq_offLineResolvent_of_finiteOffLine`
- `nullVector_bareMixedEnergy_translate`
- `nullVector_crossWallLaw`
- `nullVector_diagonalWallLaw`

### `GaloisForLFunctions.ExclusionOfTheCriticalState` (`Index/SingleQuartetSecularAndWallRigidity.lean`)
- `HasSingleOffLineQuartet`, `quartetCopyMult`
- `sum_offLineCopyFinset_of_singleQuartet`
- `bareMixedEnergy_singleQuartet`, `bareMixedEnergy_self_singleQuartet`
- `quartetOnLineGram`, `quartetOnLineGram_symm`
- `quartetSecularMatrixAt`, `quartetSecularRootSet`, `quartetSecularMatrix`
- `nullVector_iff_secularKernel`
- `exists_confinedNullVector_iff_quartetSecularDet_eq_zero`
- `quartetSecularDet_pos_below_threshold`
- `singleQuartet_groundAlias_eq_secularSup`
- `singleQuartet_complete_twoRung_ladder`
- `quartetAlias_eq_secular_extremal_roots`
- `singleQuartet_alias_sum_le`
- `singleQuartet_hasBeyondTheWallPrimeContinuation_iff`
- `singleQuartet_leftPair_isolator_isomorphism`
- `singleQuartet_directSum_primeContinuation`
- `singleQuartet_exists_poleNeutral_no_primeHeadContinuation`
- `singleQuartet_twoRung_wall_and_primeForm`
- `nullVector_averagedState_eq_modes`, `nullVector_averagedState_finiteLayer`
- `singleQuartet_nullVector_averagedState_singleConjugatePair`, `singleQuartet_averagedState_singleConjugatePair`
- `hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave`
- `eq1_global_and_profile_synthesis`
- `exists_singleOffLineQuartet_ecs_tfae`
- `no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros`
- `singleQuartet_realized_in_models`

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized (both modules verified with `lake --old env lean`, standard axioms `[propext, Classical.choice, Quot.sound]` only, wired into `ExclusionOfTheCriticalState.lean`)

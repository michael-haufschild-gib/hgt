# Localized real-rooted Weil eigenvectors force RH

- **ID:** RW-LOC-HURWITZ (loop rows 436, 438)
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), receiver for the RW/CCM route
- **Statement:** If even real eigenvectors of the restricted Weil forms at apertures `a_j → ∞` have
  real-rooted Fourier transforms, unit mass, bounded `L¹` norm and bounded second moment, then RH.

## Goal
The CCM route's recorded open step is convergence of the (real-rooted) ground-state transforms to
`Ξ` (corpus `ConnesXiGroundStateLimitWall`, "source-locked comparison with the prolate seed").
This theorem removes the identification: any subsequential limit works, and the only input is a
two-number a-priori bound. It is a receiver, not a producer: under ¬RH the ground states delocalize,
and in unstructured form (no compact support) the hypothesis is satisfied by `Φ/Ξ(0)` iff RH.

## Theorem
Notation: `F = f̂`, `f̂(z) = ∫ f(x)e^{izx}dx` (corpus `paperFT`); `W` the Weil functional
(pole − primes + archimedean), so that the restricted form is `W_a(f,k) = W(f ⋆ k̃)` for `f, k`
supported in `[−a,a]`; zeros `γ_ρ = (ρ−½)/i` with multiplicity.

Let `a_j → ∞`, and let `f_j ∈ C²` be even, real, supported in `[−a_j,a_j]`, with scalars `μ_j` such
that `W(f_j ⋆ k̃) = μ_j⟨f_j,k⟩` for all `k ∈ C_c^∞(−a_j,a_j)`. Assume
1. every zero of `F_j` is real;
2. `∫f_j = 1` and `‖f_j‖₁ ≤ C`;
3. `∫x²f_j(x)dx ≤ C`.

Then every nontrivial zero of `ζ` has real part `½`.

## Proof
**Step 1 (normal family).** `F_j` is even, real on `ℝ`, of exponential type, with real zeros and
`F_j(0)=1`; by Hadamard `F_j(z) = ∏(1 − z²/x_k²)`, and `−F_j''(0) = 2Σ1/x_k² = ∫x²f_j ≤ C`.
Hence `|F_j(z)| ≤ exp(C|z|²/2)`, and `|F_j(t)| ≤ C` on `ℝ`. By Montel a subsequence converges
locally uniformly to an entire `F_∞` with `F_∞(0)=1`; by Hurwitz every zero of `F_∞` is real.

**Step 2 (Gaussian tests).** Fix `σ > C/2` and `ψ(z) = e^{−σ(z+ω)²+is(z+ω)}` (`ω, s ∈ ℝ`), the
function `conj ĥ(z̄)` of a Gaussian-modulated `h`. Split `h = χ_jh + (1−χ_j)h`, `χ_j` a cutoff equal
to 1 on `[−a_j+1, a_j−1]`. With `‖f_j‖₁ ≤ C` and Chebyshev's bound, the pole, prime and
archimedean parts of `W(f_j ⋆ ((1−χ_j)h)~)` are `O(e^{a_j}e^{−(a_j−1)²/(8σ)})`, and
`|⟨f_j,(1−χ_j)h⟩| = O(e^{−(a_j−1)²/(4σ)})`. The explicit formula gives
`W(f_j ⋆ h̃) = Σ_ρ F_j(γ_ρ)ψ(γ_ρ)`, dominated by `e^{(C/2−σ)(Re γ_ρ)²+O(1)}` uniformly in `j`, so
it is bounded. Also `⟨f_j,h⟩ = (1/2π)∫F_jψ → (1/2π)∫F_∞ψ`. Choosing `h` with `∫F_∞ψ ≠ 0`
(Gaussian-modulated `ψ` are total) shows that `μ_j` is bounded; pass to `μ_j → μ_∞`. Dominated
convergence over the zeros gives, for all such `ψ`,

`Σ_ρ F_∞(γ_ρ)ψ(γ_ρ) = κ ∫_ℝ F_∞ψ dt`, with `κ = μ_∞/2π`.

**Step 3 (contour form).** Let `η = ½ + ε`, `L_± = ℝ ± iη`, `A = F_∞Ξ'/Ξ`. Rectangles over good
heights, where `Ξ'/Ξ = O(log²T)`, together with the Gaussian decay of `F_∞ψ` in the strip
`|Im z| ≤ η`, give `Σ_ρ F_∞ψ(γ_ρ) = (1/2πi)(∫_{L₋} − ∫_{L₊})Aψ dz`. Shifting `∫_ℝF_∞ψ` to `L₊`:

`∫_{L₋} Aψ dz = ∫_{L₊} (A + 2πiκF_∞)ψ dz`.

**Step 4 (one-sided Paley–Wiener).** Take `ψ_s(z) = e^{−σz²}e^{isz}`. Put `a₋(t) = (Aψ₀)(t − iη)`
and `b₊(t) = ((A+2πiκF_∞)ψ₀)(t + iη)`; both are integrable with Gaussian decay. Step 3 reads
`e^{sη}â₋(s) = e^{−sη}b̂₊(s)` for all real `s`, so `|â₋(s)| ≤ ‖b₊‖₁e^{−2ηs}`. Hence
`E(t+iy) = (1/2π)∫â₋(s)e^{sy}e^{−ist}ds` is holomorphic on `0 < y < 2η` with `L²` boundary
value `a₋` at `y = 0`. The function `(Aψ₀)(·−iη)` is holomorphic near `y = 0` (no zero of `Ξ` has
`|Im| ≥ ½`) with the same boundary value, so the two agree. Therefore `Aψ₀` continues
holomorphically to the whole strip `|Im z| < η`. Since `ψ₀` has no zeros, `F_∞Ξ'/Ξ` has no poles
there: `F_∞(γ_ρ) = 0` for every nontrivial zero.

**Step 5.** All zeros of `F_∞` are real (Step 1), so every `γ_ρ` is real, i.e. RH. ∎

## Dependencies
Classical only: Hadamard factorization (order ≤ 1), Montel, Hurwitz, the Weil explicit formula for
the test functions `f ⋆ h̃` (`f ∈ C²_c`, `h` Gaussian-modulated), `Ξ'/Ξ = O(log² T)` on good
horizontal segments, Chebyshev's bound `ψ(x) ≪ x`, and the `L²` Paley–Wiener theorem for a strip.

## No-go closure (CCM / RW ground-state convergence)
- **Exact killing mechanism:** zero flips make extremal states real-rooted only inside flip-closed
  classes. Those classes are translation-invariant up to their tails, so no flip-invariant functional
  can pin position (loop rows 430–437).
- **Strongest positive survivor:** this theorem. The CCM open step reduces to *bounded mass and
  second moment of the ground states* (no escape to the aperture boundary); the limit need not be
  identified with `Ξ`.
- **New insight:** real-rootedness (flip extremality) and localization (`Φ`-like decay) are each
  available separately. Under ¬RH real-rooted ground states delocalize, because the off-line
  resonance `e^{(Θ−½)|x|}` drives mass to `±a`, and localized near-null vectors (`Φ` truncations)
  are not extremal. RH is exactly their conjunction along one sequence.
- **Status:** paper proof complete. Lean: not formalized; it needs the explicit formula for
  Gaussian-decay tests (the corpus has compactly supported and Cauchy-kernel test classes) and
  one-sided Paley–Wiener on a strip.

## Log
- 2026-10-06 — created at stage 2 (Opus), loop rows 436 and 438.

## Lean status (2026-10-08, Opus loop row 556)
- **Steps 3–5 formalized; the proof is new.** The contour and one-sided Paley–Wiener steps are
  replaced by a one-sided Cauchy-transform argument. Shift the line to `Im z = −Y`, `Y ∈ (½, ½+η)`,
  and lift the zeros to `p_ρ = γ_ρ + iY` in the upper half-plane. For `Im w` above all atoms,
  `1/(z−w) = i∫₀^∞e^{−iu(z−w)}du`, so the identity at `u > 0` gives
  `Σ c_ρ/(p_ρ−w) = ∫h(t)/(t−w)dt`. The right side is holomorphic on the whole upper half-plane.
  The upper half-plane minus a countable set is connected, so the identity theorem carries the
  equality down to the atoms, where boundedness forces `c_ρ = 0`.
  Only positive frequencies `u` are used, and no `Ξ'/Ξ` estimate enters.
- Lean (standard axioms, `lake --old build` green, wired):
  - `GaloisForLFunctions.HTGeometry.eq_zero_of_oneSidedLaplace_eq` (module
    `HTGeometry/OneSidedLaplaceAtomRigidity`). Statement: summable atoms at distinct,
    non-accumulating points of the upper half-plane with bounded imaginary parts; if the one-sided
    Laplace transform equals that of an `L¹(ℝ)` function for every `u > 0`, every atom vanishes.
  - `RHTower.riemannHypothesis_of_gaussianOneSidedZeroIdentity` and the exact form
    `riemannHypothesis_iff_exists_gaussianOneSidedZeroIdentity` (module
    `RHTower/XiGaussianOneSidedIdentityRH`). Statement: `F` holomorphic on `|Im z| < ½+η`, with
    `‖F‖ ≤ Me^{A(Re z)²}` and only real zeros there; `σ > A ≥ 0`; and for every `u > 0`,
    `Σ_q F(γ_q)e^{−σγ_q²−iuγ_q} = κ∫F(t)e^{−σt²−iut}dt`. Then RH. Conversely, under RH `F = Ξ`
    with `κ = 0` satisfies the hypotheses.
- **Remaining for the full card:** Steps 1–2, the passage from actual eigenvectors to this
  identity:
  1. the normal family under bounded mass and second moment (Hadamard product), together with
     Hurwitz;
  2. the Gaussian-test explicit formula for `f_j ⋆ h̃` with the cutoff error at `±a_j`.
- Corollary of the proof: in the limit, `κ = 0`. Indeed `F(γ_ρ) = 0` makes the left side vanish.
  Then, if `κ ≠ 0`, the transform of `Fe^{−σt²}` vanishes on `u > 0`, which forces `F ≡ 0`.
  So localized real-rooted eigenvector limits force the eigenvalues to tend to 0.
- **B1 done (2026-10-08):** `RHTower.riemannHypothesis_of_tendsto_gaussianOneSidedIdentity` (module
  `RHTower/XiGaussianOneSidedIdentityLimitRH`, standard axioms, wired). Hypotheses: `F_j → F`
  locally uniformly on the strip, with `F ≢ 0`; `‖F_j‖ ≤ M`; real zeros in the strip; and the
  identity holds asymptotically with `κ_j → κ`. Conclusion: RH. It reuses the corpus local Hurwitz
  `RHTower.CCMXiStrip.zero_mem_closed_of_tendstoLocallyUniformlyOn`.
- **Remaining plan:**
  - B2: Montel on the strip, by a diagonal argument over discs; the corpus has
    `Bottcher.montel_subseq` for one disc only.
  - B3: from the zero-side eigen-equation for compactly supported tests at aperture `a_j` to the
    asymptotic Gaussian identity. The cutoff error is `O(M·tail)`. Bounded `κ_j` is automatic,
    since `∫Fψ_u = 0` for all `u > 0` forces `F ≡ 0`.
  - B4: actual eigenvectors of the full restricted form satisfy that zero-side equation. This is
    the explicit formula on the form domain, by density from
    `ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution`.
- **B2 and B3 done (2026-10-08).** B2 is
  `GaloisForLFunctions.HTGeometry.exists_tendstoLocallyUniformlyOn_subseq_of_bounded` (Montel
  on any open set, by a diagonal argument over a Lindelöf disc cover). B3 is replaced by a
  cutoff-free route.
  - `RHTower.eq_zero_of_xiOneSidedIdentity` (module `XiOneSidedAtomRigidity`): for `A`, `B`
    holomorphic on the strip with `‖·‖ ≤ K/(1+|z|²)`, if `Σ_q A(γ_q)e^{−iuγ_q} = ∫B(t)e^{−iut}dt`
    for `u > 0`, then `A(γ_q) = 0`.
  - **Theorem C:** `RHTower.riemannHypothesis_of_realRootedEigen` (module
    `XiRealRootedEigenLimitRH`).
    - Hypotheses: apertures `a_j → ∞`; `G_j` holomorphic on `|Im| < ½+η`, uniformly bounded,
      real-rooted there, `G_j(0) = 1`; and the zero-side eigen-equation
      `Σ_q G_j(γ_q)ŵ(−γ_q) = κ_j∫G_j(s)ŵ(−s)ds` for every smooth test `w` supported in
      `[−R,R]`, `R < a_j`. Conclusion: RH.
    - Proof: tests are exact right translates of modulated bumps, with no cutoff error.
      Eigenvalues are bounded because `∫G b̂(−·)e^{−iu·} = 0` for all `u` would force
      `G(0)b̂(0) = 0` (Fourier inversion). A choice of modulation avoids the zeros of `b̂`.
  - All modules use standard axioms, are wired, and have been collision-scanned.
- **Remaining (B4):** actual full-form ground states (`IsFullGround`, real-rooted by
  `exists_realRooted_fullGround`) satisfy Theorem C's eigen-equation. This needs:
  - Euler–Lagrange from `ccmRestrictedWeilGroundEnergy_mem_lowerBounds`;
  - the explicit formula on the form domain, by density from smooth interior sources;
  - Parseval for smooth tests, to put the right side in Fourier form.
- **B4 done, capstone formalized (2026-10-09).** Module `RHTower/CCMFullGroundZeroSideEigen`
  (standard axioms, `lake --old build` green, wired).
  - `zeroSide_eigen_of_isFullGround`: every full ground state `u` satisfies
    `Σ_q Ĝ_u(γ_q)v̂(−γ_q) = (μ_a/2π)∫Ĝ_u(σ)v̂(−σ)dσ` for all smooth interior sources `v`, where
    `Ĝ_u(z) = ∫conj(u)e^{izt}`. Proof:
    - Euler–Lagrange via the nonnegative shifted Hermitian form;
    - a Plancherel representer of `Q(·,v)`, together with the zero kernel
      `Σ_q v̂(−γ_q)e^{iγ_q t}`, whose difference is annihilated by real smooth tests on
      `(−a,a)`; this extends the explicit formula to the whole form domain without form-norm
      density;
    - Parseval through Zeta23's `paper_inversion`.
  - **Capstone `riemannHypothesis_of_localizedFullGrounds`:** RH follows from real-rooted full
    ground states `u_j` at apertures `a_j → ∞` with `∫u_j ≠ 0` and
    `∫|u_j|e^{(½+η)|t|} ≤ C|∫u_j|`. Real-rooted full grounds exist at every aperture
    (`exists_realRooted_fullGround`), so the localization bound is the only open input.
  - **Scope versus the card's statement:** formalized is the exponential-moment variant (loop
    row 436). The card's sharper second-moment variant (row 438: `‖f‖₁ ≤ C`, `∫x²f ≤ C`)
    additionally needs the Hadamard product for even real-rooted exponential-type transforms,
    which is not in the corpus.
- **Strip-bounded and Poisson-balanced forms (2026-10-09, loop row 564).**
  - `riemannHypothesis_of_stripBoundedFullGrounds`: the only analytic input is
    `‖Ĝ_{u_j}(z)‖ ≤ C|∫u_j|` on `|Im z| < ½+η`. The moment capstone is now a corollary.
  - `RHTower/PaleyWienerPoissonMajorant`: Poisson majorant
    `log|F(x±iy)| ≤ a y + (y/π)∫log|F(u)|/((u−x)²+y²)du` for every L¹ function supported in
    `[−a,a]`. It is proved by boundary Jensen on the disc; no inner–outer factorization is needed.
  - `RHTower/CCMFullGroundPoissonBalanceRH.riemannHypothesis_of_poissonBalancedFullGrounds`:
    the strip bound is replaced by a real-line condition on `log|F_j|`.
- **Second-moment variant formalized in zero-sum form (2026-10-09, loop row 565, MUST-833).**
  - `RHTower/XiRealRootedApproxEigenLimitRH`: Theorem C with asymptotic eigen-equations.
  - `RHTower/XiRealRootedEigenGaussianGrowthRH.riemannHypothesis_of_realRootedEigen_gaussianGrowth`:
    the Steps 1–2 Gaussian-test limit of this card, with uniform Gaussian growth replacing
    boundedness. Smearing the exact shift identities over `|v| ≤ a_j − 2` against a Gaussian removes
    the cutoff estimates and the explicit formula for non-compact tests.
  - `RHTower/CCMFullGroundGaussianGrowthRH.riemannHypothesis_of_gaussianGrowthFullGrounds`.
  - `RHTower/CCMEvenFullGroundZeroSumRH.riemannHypothesis_of_evenFullGrounds_zeroSum`: even
    real-rooted grounds with `∫|u_j| ≤ Me^{a_j}|∫u_j|` and `Σ_ρ 1/|ρ|² ≤ S` force RH. This is
    weaker than the card's hypothesis 2, which asks for `‖f_j‖₁ ≤ C`.
  - Remaining gap to the card's literal hypothesis 3 (`∫x²f_j ≤ C`): the classical identity
    `Σ_ρ 1/ρ² = ∫x²f/∫f`, the second Taylor coefficient of the even canonical product. It is not
    in the corpus.

## Lean certificate (2026-10-09)

Main theorems, in `formal/GaloisForLFunctions/RHTower/CCMEvenFullGroundSecondMomentRH.lean`:

- `RHTower.CCMFullGroundEigen.riemannHypothesis_of_evenEigenvectors_secondMoment`: the card's
  Theorem.
- `RHTower.CCMFullGroundEigen.riemannHypothesis_of_evenFullGrounds_secondMoment`: the same theorem
  for full ground states, with `μ_j` the ground energy (the case the CCM route uses).

Claim → declaration:

| Card claim | Lean |
|-|-|
| `f_j` even, supported in `[−a_j,a_j]` | `u_j : CCMArchimedeanFormDomain (a j)` (support from `supportedIn_timeRep`), `heven`; `C²` and reality are not needed |
| `W(f_j ⋆ k̃) = μ_j⟨f_j,k⟩` for `k ∈ C_c^∞(−a_j,a_j)` | `heig : ccmRestrictedWeilForm (a j) (u j) s = μ_j ∫ conj(u_j) s` for every `CCMComplexSmoothInteriorSource`; ground states supply it via `formEigen_of_isFullGround` |
| hyp. 1: zeros of `F_j` real | `hreal` (zeros of `unitaryLaplace (timeRep …)`) |
| hyp. 2: `∫f_j = 1`, `‖f_j‖₁ ≤ C` | `hmass`, `hl1 : ‖u_j‖₁ ≤ M e^{a_j} \|∫u_j\|` (weaker: `M = C` works) |
| hyp. 3: `∫x²f_j ≤ C` | `hmom : \|∫t²u_j\| ≤ S\|∫u_j\|`. The two are the same, since `∫t²u/∫u = Σ_ρ 1/ρ² ≥ 0` for real zeros: `integral_sq_mul_conj_eq_of_realZeros` (`∫t²conj f = conj(∫f)·Σ_ρ1/\|ρ\|²`) |
| Literal card statement (hyps. 1–3, `∫f_j = 1`, `‖f_j‖₁ ≤ C`, `Re∫t²f_j ≤ C`, eigen-equation, even, real zeros) | `RHTower.CCMFullGroundEigen.riemannHypothesis_of_card_hypotheses` (η := 1, M = S = C; `hl1` from `C ≥ 0`, `e^{a_j} ≥ 1`; `hmom` because `∫t²f_j` is a nonnegative real) |
| Step 1: Hadamard, `−F''(0) = 2Σ1/x_k² = ∫x²f`, `\|F(z)\| ≤ e^{C\|z\|²}` | `tsum_inv_sq_zeroCopyPoint_conjTransform`, `hasDerivAt_deriv_conjTransform_zero`, `hasDerivAt_deriv_canonicalProductE1Indexed_zero` (`CanonicalProductE1SecondDerivative`), `norm_le_mul_exp_zeroSum_of_even`, even Hadamard `eq_const_mul_hadamardProduct_of_even` |
| Step 1: Montel, Hurwitz, `F_∞(0)=1` | inside `riemannHypothesis_of_realRootedApproxEigen` (`exists_tendstoLocallyUniformlyOn_subseq_of_bounded`, `CCMXiStrip.zero_mem_closed_of_tendstoLocallyUniformlyOn`) |
| Step 2: Gaussian tests, cutoff errors, `μ_j` bounded | replaced by smearing the exact shift identities against a Gaussian: `eigenDefect_shiftSmear_eq_zero`, `integral_gaussShiftWeight_mul`, `norm_gaussWeightedDefect_le`, `tendsto_exp_mul_gaussShiftTail`, `riemannHypothesis_of_realRootedEigen_gaussianGrowth`; κ-boundedness in `riemannHypothesis_of_realRootedApproxEigen` |
| Step 2: explicit formula `W(f ⋆ h̃) = Σ_ρ F(γ_ρ)ψ(γ_ρ)` | `zeroSide_eigen_of_formEigen` (Plancherel representer plus zero kernel; `tsum_mul_integral_eq_integral_zeroKernel`, `integral_timeRep_formRepresenter_eq`, `integral_conj_mul_eq_parseval`) |
| Steps 3–4: contour form, one-sided Paley–Wiener | `eq_zero_of_xiOneSidedIdentity` (`XiOneSidedAtomRigidity`), `GaloisForLFunctions.HTGeometry.eq_zero_of_oneSidedLaplace_eq` |
| Step 5: real zeros of `F_∞` force RH | end of `riemannHypothesis_of_realRootedApproxEigen` (`riemannHypothesis_of_xiSpectralPoint_real`) |

Audit (2026-10-09, run from `formal/`):

- `lake env lean GaloisForLFunctions/RHTower/<M>.lean` reports no errors and no warnings for each `M`
  in: `XiRealRootedEigenLimitRH`, `CCMFullGroundZeroSideEigen`, `XiRealRootedApproxEigenLimitRH`,
  `XiRealRootedEigenGaussianGrowthRH`, `CCMFullGroundGaussianGrowthRH`, `CCMEvenFullGroundZeroSumRH`,
  `CanonicalProductE1SecondDerivative`, `CCMEvenFullGroundSecondMomentRH`.
- `lake --old build +GaloisForLFunctions.RHTower.CCMEvenFullGroundSecondMomentRH` succeeds.
- All modules are wired into `GaloisForLFunctions/RHTower.lean`.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for:
  - `riemannHypothesis_of_card_hypotheses` and `integral_sq_mul_conj_eq_of_realZeros` (added later on 2026-10-09; `lake env lean` and `lake --old build` re-run clean);
  - `riemannHypothesis_of_evenEigenvectors_secondMoment` and `riemannHypothesis_of_evenFullGrounds_secondMoment`;
  - `tsum_inv_sq_zeroCopyPoint_conjTransform`, `riemannHypothesis_of_evenEigenvectors_zeroSum` and `riemannHypothesis_of_gaussianGrowthEigenvectors`;
  - `zeroSide_eigen_of_formEigen`, `RHTower.riemannHypothesis_of_realRootedEigen_gaussianGrowth` and `RHTower.hasDerivAt_deriv_canonicalProductE1Indexed_zero`.
- `scripts/formal_tools.py lint`: its 7 errors all concern unrelated unreachable modules. None
  involves these modules, and none of them contains `sorry`, `axiom` or `opaque`.

Scope: the Lean theorem is stronger than the card. Hypothesis 2 is weakened to `‖f_j‖₁ ≤ Me^{a_j}|∫f_j|`, reality and `C²` are dropped, and Step 2 needs no explicit formula for non-compact tests.

## Log (promotion)

- 2026-10-09: certificate checked independently: `lake env lean` clean on the 8 chain modules
  (`CCMEvenFullGroundSecondMomentRH`, `CanonicalProductE1SecondDerivative`, `CCMEvenFullGroundZeroSumRH`,
  `CCMFullGroundGaussianGrowthRH`, `XiRealRootedEigenGaussianGrowthRH`, `XiRealRootedApproxEigenLimitRH`,
  `CCMFullGroundZeroSideEigen`, `XiRealRootedEigenLimitRH`); axiom audit over all 122 declarations of
  these modules: only `propext`, `Classical.choice`, `Quot.sound`; all wired once.  The literal
  statement `riemannHypothesis_of_card_hypotheses` takes exactly the card's hypotheses (eigen
  equation, real zeros, evenness, `∫ f_j = 1`, `‖f_j‖₁ ≤ C`, `∫ x² f_j ≤ C`).  Promoted to stage 3.

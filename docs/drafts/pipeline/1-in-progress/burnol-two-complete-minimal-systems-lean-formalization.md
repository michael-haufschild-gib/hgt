# Burnol, "Two complete and minimal systems associated with the zeros of the Riemann zeta function" — full Lean formalization

- **ID:** burnol-2cms-lean
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** arXiv:math/0203120v7 (J. Théor. Nombres Bordeaux 16 (2004) 65–94)
- **Statement:** Formalize unconditionally in Lean 4 every lemma / proposition / theorem of the
  paper that is not already owned by mathlib or by this corpus.

## Goal
The paper links the co-Poisson (Duffin–Weinberger dualized Poisson) formula, the de Branges
Sonine spaces `K_a` / extended spaces `L_a`, and the Hilbert-space completeness/minimality of the
evaluator system attached to the Riemann zeros.  The corpus already owns a large `Burnol*` /
`*CoPoisson*` / `sonin*` layer (572 modules in `RHTower/`) but **no** abstract
minimal/complete/dual-system theory, **no** Mellin–Plancherel unitary, **no** Hardy space `H²` of
a half-plane with Paley–Wiener, **no** Nevanlinna/Krein mean-type theory, **no** Levin
completely-regular-growth theory.  These are the real gaps.

## Paper inventory (every statement, with disposition)

| # | Statement | Content | Disposition |
|---|---|---|---|
| (1)(2) | Poisson summation | classical | mathlib/corpus |
| (3)(8) | functional equation of ζ | classical | corpus |
| (4)(9) | co-Poisson intertwining | Duffin–Weinberger | corpus `BurnolCoPoissonIntertwining*` |
| (5) | Müntz formula | ζ(s)∫φ tˢ⁻¹ = ∫(modified Poisson sum)tˢ⁻¹ | **corpus-owned**: zero-mean case on `Re s > 1` `CCMBVMuntzSummation.mellin_arithmeticSum_eq_zeta_mul`, continued to `{Re s>0}\{1}` by `CCMConnesConsaniRapidMuntz.mellin_ccmFourierTruncatedPoissonValue_eq_zeta_mul_of_re_pos`; the `∫φ ≠ 0` correction is the co-Poisson chart, row (6) |
| (6) | Müntz applied to g(1/t)/t | co-Poisson Mellin | **corpus-owned**: `BurnolCoPoissonGeneralSeedMellin.soninMellinEvaluation_burnolCoPoissonSource` — `M(coPoisson seed)(w) = Γ-factor · ζ(w) · M(seed)(w)` on `1/2 < Re w < 1`, where `burnolCoPoissonRightSum g t = Σ_n g(t/n)/n − ∫g(1/y)/y dy` is exactly `t·(Σφ(nt) − (1/t)∫φ)` under `φ(t) = g(1/t)/t` |
| (7) | `F₊(f)^(s) = χ(s) f^(1-s)`; χ = ζ(s)/ζ(1−s) | Mellin diagonalization | **corpus-owned**: `CCMArchimedeanFourierMellinScattering.archimedeanMellinUnitary_evenFourierTransform` — for *every* even `f`, `M(F₊f) = R(χ · M f)` with the archimedean scattering phase |
| Thm 2.1 | de Branges: `M(f)` entire on `K_a`, evaluations continuous | **DONE**: `RHTower/SoninEntireMellin.differentiable_soninEntireMellin` (+ the functional equation `soninEntireMellin_eq_soninChiSide` on `Re s < 1`, and `soninMellinExtension_functional_equation` on the strip) | |
| Prop 2.2 | `M(f)` meromorphic (poles ⊂ {0,1}) on `L_a`; `M(F₊f)(s)=M(f)(1−s)` | **DONE**: `RHTower/SoninExtendedMeromorphic.exists_entire_extendedMellin` (`s(1−s)·M(f)(s)` is entire) and `RHTower/SoninExtendedFunctionalEquation.extendedFullMellin_functional_equation` | |
| Def 3,4 | `Y_a` (zero span), co-Poisson subspace `P_a` | | corpus (`burnolCoPoissonSourceSpace`) |
| Thm 3.1 | `Y^a_{ρ,k}` minimal iff a ≤ 1, complete iff a ≥ 1; `Y_a^⊥ = P_a` (a<1) | capstone | **TODO** |
| Thm 3.2 | `Z^a_{ρ,k}` minimal not complete a<1; a=1 not minimal, omit 2 → minimal+complete; a>1 complete after finite omission | capstone | **TODO** |
| Thm 3.3 | `ζ(s)/(s−ρ)^l` minimal and complete in `L̂₁`; dual system | capstone | **TODO** |
| Prop 4.1 | characterization of `L̂_a` inside `s/(s−1)·A^s H²` | **DONE**: `RHTower/MellinHeadHardyEquiv.isMellinHeadHardy_iff` (`IsMellinHeadHardy a F ↔ F = headTailMellin a c g` on `Re s > 1/2`, `s ≠ 1`), with the `K_a` companion `isMellinTailHardy_iff`; converse direction in `RHTower/MellinHeadHardyConverse.exists_head_tail_of_isMellinHeadHardy` | |
| Prop 4.2 | `ζ(s)/(s−ρ)^l ∈ L̂₁` | **DONE**: `RHTower/ZetaMellinHeadHardy.isMellinHeadHardy_zetaQuotient` (for any `ρ ≠ 0, 1` with `analyticOrderAt ζ ρ ≥ l ≥ 1`) | |
| Prop 4.3 | division by `(s−w)` stays in `L̂_a` / `K̂_a` | **corpus-owned for `L_a`**: `BurnolSoninDividedShift.burnolShift_mem_soninExtendedSpace`; `K_a` half **DONE**: `RHTower/MellinHardyClasses.IsMellinTailHardy.div_sub` | |
| Lem 4.4 | `F ∈ K̂_a ⇒ F/s ∈ L̂_a` | **DONE**: `RHTower/MellinHardyClasses.IsMellinTailHardy.div_id` and `.div_one_sub` | |
| Prop 4.5 | `dim(L_a/K_a) = 2` | **DONE, literal**: `RHTower/SoninExtendedCodimensionTwo.finrank_centralSoninExtendedCarrier_inf_orthogonal_carrier` (`finrank (L_a ⊓ K_aᗮ) = 2`), dualising `SoninBandCodimensionTwo.finrank_soninBandComplement_eq_two` | |
| Prop 4.6 | `∪_{b>a}K_b` dense in `K_a` (same for `L`) — via the general lattice identity | **DONE**: `RHTower.topologicalClosure_iSup_centralSoninCarrier` (K) and `RHTower/SoninExtendedApertureChain.topologicalClosure_iSup_centralSoninExtendedCarrier` (L) | |
| Prop 4.7 | `∪_{b>a}K_b ⊊ K_a`, also for Fourier-(skew-)invariant parts | **DONE**: `RHTower/SoninApertureStrict.iSup_centralSoninCarrier_lt` and `RHTower/SoninApertureStrictEigen.iSup_centralSoninCarrier_inf_eigen_lt` (+ the `ε = ±1` corollaries) | |
| Def 10 | L-Property | **DONE**: `RHTower/LPropertyStrips.HasLProperty` (+ `.add`, `.const_mul`) | |
| Thm 4.8 | functions of `L̂_a` have the L-Property | **DONE**: `RHTower/SoninLPropertyTheorem.hasLProperty_extendedMellinContinuation` (+ the packaged `exists_hasLProperty_extendedMellin`) | |
| Def 12 | `𝓛¹` (quick decrease in vertical strips) | **DONE**: `RHTower/LPropertyStrips.HasStripRapidDecrease` (+ `.add`, `.hasLProperty`) | |
| Thm 4.9 | `𝓛¹` dense in `L¹` | **DONE**: `RHTower/SoninRapidMellinDense.mem_closure_hasRapidMellin` (with `HasRapidMellin` = Def 12 in `SoninMellinMultiplier`) | |
| Lem 4.10 | rapid-decrease class stable under `F₊` | **DONE, unconditional**: `RHTower/ZetaChiStripGrowth.hasStripRapidDecrease_zetaChi_mul_reflect`, from `LPropertyStrips.hasStripRapidDecrease_chi_mul_reflect` + `hasStripPolyGrowthOffReal_zetaChi` | |
| Prop 5.1 | Titchmarsh IX.7: `|ζ(s)|⁻¹ < |s|^A` on `|Im s| = T_n`, `−1≤Re s≤2` | **DONE**: `RHTower/ZetaInverseHorizontal.exists_zeta_inv_horizontal_bound` | |
| Thm 5.2 | residue series `Σ_ρ G(ρ)/ζ'(ρ) · ζ(Z)/(Z−ρ) = G(Z)` | | **TODO** |
| Cor 5.3 | `ζ(s)/(s−ρ)^l` complete in `L̂₁` | | **TODO** |
| Prop 5.4 | `Σ_ρ G(ρ)/ζ'(ρ) = 0` | | **TODO** |
| Rem 15 | Ramanujan `√a Σμ(n)/n e^{−(a/n)²} − …` | | **TODO** |
| Prop 6.1 | a ≥ 1 ⇒ `Y^a_{ρ,k}` complete in `L_a` (Krein) | | **TODO** |
| Prop 6.2 | a > 1 ⇒ not minimal, complete after finite omission | | **TODO** |
| Thm 6.3 | a = 1 ⇒ minimal and complete | | **TODO** |
| Prop 6.4 | a < 1 ⇒ minimal, not complete | | **TODO** |
| Prop 6.5 | `Z^1_{ρ,k}` not minimal; shortened system minimal + complete | | **PARTIAL [LEAN-PROVED]**: completeness half and a coefficient-faithful, source-budgeted `K₁` finite-defect witness are formalized. Open: derive its selected exact order from an arbitrary retained jet and identify the order witness with the literal shortened evaluator-system predicate. |
| Prop 6.6 | a > 1 ⇒ `Z^a_{ρ,k}` span `K_a` after finite omission | | **TODO** |
| Thm 6.7 | a < 1 ⇒ `Z^a_{ρ,k}` minimal | | **TODO** |
| Thm 7.1 | `a₁(Z) = a₂(Z)` | | **TODO** |
| Thm 7.2 | `a < a(Z)` ⇒ not complete, minimal, after adding finitely many | | **TODO** |
| Thm 7.3 | `a > a(Z)` ⇒ complete, not minimal, after omitting finitely many | | **TODO** |
| Lem 7.4 | not complete ⇒ minimal | | **TODO** |
| Lem 7.5 | minimal in `K_a` ⇒ not complete in `K_b`, `b<a` | | **TODO** |
| Lem 7.6 | 7.5 + finitely many extra evaluators | | **TODO** |
| Thm 7.7 | `𝒢(s)` normal type for `r log r`, indicator `½|cos θ|`, CRG, zero density `T/2π·log T` | | **TODO** (Levin) |
| Thm 7.8 | `a(Z_g) = a(g)` | | **TODO** |
| Prop 7.9 | `Z_g ⊂ Z_f` ⇒ `F/G` of finite exponential type, `a(f) ≤ a(g)` | | **TODO** |
| Prop 7.10 | `Z_f = Z_g` ⇒ `f`, `g` multiplicative translates (Wiener causal gain) | | **TODO** |
| §3 Remark | minimal+complete ⇒ unique dual system; dual is minimal, need not be complete (Hardy-disc example `1−zⁿ`) | **DONE**: `HTGeometry/MinimalCompleteSystem.lean` | |
| §2 chain | `K = ∪_{a>0}K_a`, `{0} = ∩_{a>0}K_a` | **DONE**: `RHTower/SoninCarrierApertureLimits.lean` (K) and `RHTower/SoninExtendedApertureChain.lean` (L: `topologicalClosure_iSup_pos_centralSoninExtendedCarrier`, `iInf_pos_centralSoninExtendedCarrier`) | |
| §7 indices | `a₁(Z)`, `a₂(Z)` well defined; minimality downward closed, completeness upward closed | **DONE**: `HTGeometry/MinimalCompleteSystemChain.lean` | |
| §4.5/4.6 input | `L²(0,a) + F₊(L²(0,a))` closed (Burnol [6]) | **DONE**: `RHTower/SoninForbiddenClosedSum.lean` | |

## Layer plan (build order)

1. **LAYER 1 — abstract minimal / complete / dual systems in a Hilbert space.**
   `HTGeometry/MinimalCompleteSystem.lean`.  Not in mathlib, not in the corpus.
   `IsCompleteSystem`, `IsMinimalSystem`, biorthogonal dual, existence/uniqueness, dual is minimal,
   pull-back of minimality along a continuous linear map, push-forward of completeness along a
   dense-range map (these are exactly the arguments of Prop 6.4 and Prop 6.6), plus the
   counterexample of the §3 Remark (`u_n = e₀ − eₙ`, dual `−eₙ`, complete+minimal but dual not
   complete) — the orthonormal-basis model of `1 − zⁿ ∈ H²(𝔻)`.
2. **LAYER 2 — the intersection/sum lattice identity of Prop 4.6.**
   `⨅ᵢ (Aᵢ ⊔ Bᵢ) = (⨅ᵢ Aᵢ) ⊔ (⨅ᵢ Bᵢ)` for monotone submodule families over a linear order with
   `Aᵢ ⊓ Bᵢ = ⊥`.  Mathlib gap.
3. **LAYER 3 — Mellin–Plancherel unitary** `L²(0,∞;dt) ≃ L²(Re s = ½)` and the `χ` multiplier (7).
4. **LAYER 4 — Hardy space `H²` of the right half-plane** + Paley–Wiener (`L²(1,∞)` ≃ `H²`),
   mean type, `A^s H²`, `s/(s−1) A^s H²`.
5. **LAYER 5 — Nevanlinna class + Krein's theorem** (entire + Nevanlinna in two complementary
   half-planes ⇒ finite exponential type = max of mean types).
6. **LAYER 6 — Levin CRG theory** (proximate order `r log r`, indicator, CRG rays, zero-density).
7. **LAYER 7 — the ζ-specific §5/§6** (Titchmarsh 5.1, residue series, capstones 3.1/3.2/3.3).

## The Theorem 2.1 route (de Branges entirety) — FROZEN PLAN

The corpus already owns the **two de Branges bricks** (`RHTower/SoninDeBrangesCarrier.lean`):
`soninDeBrangesTransform f` is holomorphic on `Re z > 1/2` and `soninDeBrangesDualTransform f`
(i.e. `M(F₊f)(1−z)`) on `Re z < 1/2`.  What is missing is the **weld** across the critical line.
Do *not* attempt a boundary-value / edge-of-the-wedge argument.  Use this instead:

1. **Truncated kernel.**  `K_{a,T}(s)(u) := F₊(1_{(a,T)} t^{-s})(u) = 2∫_a^T cos(2πtu) t^{-s} dt`.
   For each `T` this is *entire* in `s` (finite interval, bounded kernel).
2. **Parseval.**  For `f ∈ K_a` with `g := F₊f` (both vanishing on `(0,a)`),
   `∫_a^T f(t) t^{-s} dt = ∫_a^∞ g(u) K_{a,T}(s)(u) du`.
3. **One integration by parts** gives, for `Re s > 0`,
   `K_{a,T}(s)(u) = (sin(2πTu)T^{-s} − sin(2πau)a^{-s})/(πu) + (s/(πu))∫_a^T sin(2πtu) t^{-s-1} dt`,
   hence `|K_{a,T}(s)(u)| ≤ C(s)/u` **uniformly in `T`**, with `C` locally bounded on `Re s > 0`,
   and `‖K_{a,T}(s) − C_a(s)‖_{L²(a,∞)} ≤ C(s) T^{-Re s} ‖1/u‖_{L²(a,∞)} → 0`, locally uniformly.
4. **Weierstrass.**  `F_T(s) := ∫_a^T f(t)t^{-s}dt` is entire and converges locally uniformly on
   `Re s > 0`; the limit `F` is therefore holomorphic on `Re s > 0` and equals `f̂` on `Re s > 1/2`.
   So `M(f)` continues holomorphically to `Re s > 0` — **only one** integration by parts is needed,
   no `k`-fold iteration and no explicit `χ(s)u^{s-1}` series.
5. **Glue.**  By the same argument `M(F₊f)(1−·)` is holomorphic on `Re s < 1`.  On the critical line
   the two agree (functional equation `M(F₊f)(s) = M(f)(1−s)`; corpus candidate
   `CCMArchimedeanFourierMellinScattering.archimedeanMellinUnitary_evenFourierTransform`).  Both are
   continuous on the open strip `0 < Re s < 1`, so a.e. agreement on the line upgrades to agreement
   on the line and then, by the identity theorem, on the strip.  Gluing the two half-planes gives an
   entire function: **Theorem 2.1**, and with the pole bookkeeping of `L_a`, **Prop. 2.2**.

### Brick list for the Theorem 2.1 route

| Brick | Statement | Status |
|---|---|---|
| B1 | `s ↦ ∫_a^b φ(t)t^{-s}dt` entire for `0 < a ≤ b`, `φ ∈ L¹(a,b)` | **DONE** `HTGeometry/TruncatedMellinEntire.differentiable_truncatedMellin` |
| B2 | Parseval `⟪h, f⟫ = ⟪𝓕h, 𝓕f⟫` (mathlib `inner_map_map`) plus the `L¹∩L²` agreement of the unitary `L²` Fourier transform with the Fourier integral | **corpus-owned**: `RHTower/L2FourierIntegralBridge.l2_fourier_coeFn_eq_l1_fourier_of_integrable` |
| B3 | `𝓕(1_{(T,T')}t^{-s})(u) = ∫_T^{T'}e^{-2πiut}t^{-s}dt` | **DONE** `HTGeometry/TruncatedPowerFourierBound.fourierIntegral_truncPower` |
| B4 | integration by parts: `‖∫_a^T e^{ilt}t^{-s}dt‖ ≤ (2a^{-σ} + ‖s‖a^{-σ}/σ)/|l|` **uniformly in `T`** | **DONE** `HTGeometry/OscillatoryPowerIntegral.norm_oscPowerIntegral_le` |
| B5 | Cauchy estimate `‖∫_T^{T'} t^{-s}f(t)dt‖ ≤ T^{-σ}·((2+‖s‖/σ)/2π)·N(a)·‖f‖` | **DONE** `RHTower/SoninTruncatedMellinCauchy.norm_truncMellin_le` (+ tail kernel `HTGeometry/InvAbsTailL2`) |
| B6 | Weierstrass: the truncations converge locally uniformly on `Re s > 0`; the limit is holomorphic there and equals `f̂` on `Re s > 1/2` | **DONE** `RHTower/SoninMellinHalfPlaneExtension.differentiableOn_soninMellinExtension` + `soninMellinExtension_eq_soninMellinIntegral` |
| B7 | glue with the reflected brick across `0 < Re s < 1` | **DONE** (see the frozen chain below; capstone `RHTower/SoninEntireMellin.differentiable_soninEntireMellin`) |

### B7 — the weld, fully reduced to a computation (FROZEN PLAN)

`tendsto_integral_powerOsc_ne` (`HTGeometry/PowerFourierGamma`) is now available for **every**
nonzero real frequency.  With it the weld is the following chain, with no L²-unitary normalisation
bridge needed:

1. `soninTruncMellin f a T s = ⟪W_{a,T}, f⟫ = ⟪𝓕W_{a,T}, g⟫` where `W_{a,T} = 1_{(a,T)}t^{-s̄}`
   and `g = 𝓕f` — **done** (`SoninTruncatedMellinCauchy.inner_truncPowerVector_eq_truncMellin`
   + `fourierUnitary.inner_map_map`).
2. `conj(𝓕W_{a,T}(u)) = ∫_a^T e^{2πiut}t^{-s}dt` — conjugate of
   `TruncatedPowerFourierBound.fourierIntegral_truncPower`.
3. Pointwise in `u ≠ 0`, `∫_a^T e^{2πiut}t^{-s}dt → C_a(u,s) := Γ(1−s)(−(2πu)i)^{s−1} − E_a(u,s)`
   with `E_a(u,s) = ∫_0^a e^{2πiut}t^{-s}dt` (absolutely convergent for `Re s < 1`).
   The first term is `tendsto_integral_powerOsc_ne`.
4. `|conj(𝓕W_{a,T}(u))| ≤ C(s,a)/|u|` uniformly in `T` — `norm_fourierIntegral_truncPower_le`.
   Dominated convergence against `g ∈ L²(|u|>a)` (Cauchy–Schwarz makes `C/|u| · |g|` integrable)
   gives `soninMellinExtension f a s = ∫ C_a(u,s) g(u) du`.
   **DONE**: `RHTower/SoninKernelPairing.soninMellinExtension_eq_kernel_pairing`.
5. `∫ E_a(u,s) g(u) du = ⟪h_s, f⟫ = ∫_0^a t^{-s} f(t) dt = 0` because `f` **vanishes** on `(0,a)`
   (`h_s = 1_{(0,a)}t^{-s̄} ∈ L²` exactly when `Re s < 1/2`).
   **DONE**: `RHTower/SoninNearZeroKernelVanishing.integral_nearZeroKernel_mul_fourier_eq_zero`
   (with `HTGeometry/NearZeroTruncatedPower` supplying the `L¹`/`L²` facts at the origin).
   Combining 4 and 5: **DONE** `RHTower/SoninPureChiKernel.soninMellinExtension_eq_chi_pairing`
   — `f̂(s) = ∫ Γ(1−s)(−2πui)^{s−1} 𝓕f(u) du` on `0 < Re s < 1/2`.  Integrability of the
   `χ`-part comes from `HTGeometry/PowerTailL2` (`1_{|u|>a}|u|^r ∈ L²` for `2r < −1`).
6. By evenness of `g`, `Γ(1−s)∫(−(2πu)i)^{s−1}g(u)du = 2(2π)^{s−1}Γ(1−s)sin(πs/2) · ĝ(1−s)`,
   and `Re(1−s) > 1/2` there, so `ĝ(1−s)` is the absolutely convergent integral.
7. Hence `f̂(s) = c(s)·ĝ(1−s)` on `0 < Re s < 1/2` with `c(s) = 2(2π)^{s−1}Γ(1−s)sin(πs/2)`
   **manifestly holomorphic on `Re s < 1`**.  Gluing `f̂` (holomorphic on `Re s > 0`) with
   `c(s)·ĝ(1−s)` (holomorphic on `Re s < 1`) via the identity theorem gives **`f̂` entire** —
   Theorem 2.1.  The identification `c = Γ_ℝ(1−s)/Γ_ℝ(s)` is *not needed for entirety*; it is only
   needed to state the Γ-completed form, and then follows from mathlib's `riemannZeta_one_sub`
   plus the corpus's `zetaChi_eq_pi_cpow_mul_gamma_ratio`.

Steps 6 and 7 are now closed as well:
* step 6 — `RHTower/SoninFunctionalEquation.lean`: `chiKernel_of_pos` / `chiKernel_of_neg` give the
  two branch values `(∓i)^{s−1}`, `HTGeometry/ReflectionSplitIntegral.integral_eq_add_reflect`
  splits the pairing into the two half-lines, evenness of `𝓕f` folds them together, and
  `HTGeometry/ImaginaryAxisCpow.I_cpow_add_neg_I_cpow` turns the two branch values into
  `2cos(π(s−1)/2)`.  Capstone `soninMellinExtension_functional_equation`:
  `f̂(s) = burnolChiFactor s · ĝ(1−s)` on `0 < Re s < 1/2`, with
  `burnolChiFactor s = Γ(1−s)(2π)^{s−1}·2cos(π(s−1)/2)` (Riemann's `χ(s)`).
* step 7 — `RHTower/SoninEntireMellin.lean`: `soninChiSide` is holomorphic on `Re s < 1`
  (`differentiableOn_soninChiSide`), and `HTGeometry/CauchyTransformGluingVertical.glueVert`
  with `c₁ = 0`, `c₂ = 1/2` glues it to `soninMellinExtension` — **no identity theorem needed for
  entirety**.  The identity theorem is used only afterwards, to propagate the functional equation
  from `Re s < 1/2` to the whole half-plane `Re s < 1` (`soninEntireMellin_eq_soninChiSide`).

The prerequisite `fourierUnitary` preserves `centralSoninCarrier a` is closed:
`RHTower/SoninCarrierFourierInvariance.fourierUnitary_mem_centralSoninCarrier`.

## LAYER 4 — Hardy `H²` of a half-plane and Paley–Wiener (FROZEN PLAN)

Neither mathlib nor the corpus has a Hardy space of a half-plane, a Laplace transform of `L²`, or
Paley–Wiener.  §4 of the paper is entirely phrased in `H²`, `A^s H²`, `s/(s−1)A^s H²`, so this is
the gateway layer for Prop. 4.1, 4.2, 4.3, Lem. 4.4, Thm. 4.8, and much of §6/§7.

### Normalisation
`w = σ + iy`, half-plane `Re w > 0`.  For `φ ∈ L²(0,∞)`,
`𝓛φ(w) := ∫_0^∞ φ(x)e^{-wx}dx`.  With mathlib's `𝓕g(ξ)=∫g(x)e^{-2πixξ}dx`,
`𝓛φ(σ+iy) = 𝓕(e^{-σ·}φ)(y/2π)`, so `∫_ℝ|𝓛φ(σ+iy)|²dy = 2π‖e^{-σ·}φ‖²`.
Burnol's `H²` on `Re s > 1/2` with `|ds|/2π` is this after `s = 1/2 + w` and `t = e^x`:
`f̂(s) = ∫_0^∞ f(t)t^{-s}dt`, `φ(x) = f(e^x)e^{x/2}`, `f` supported in `[1,∞) ⟺ φ` supported in
`[0,∞)`; `‖φ‖_{L²(ℝ)} = ‖f‖_{L²(0,∞)}`.

### STATUS: LAYER 4 CORE IS CLOSED (2026-08-22), axiom-clean

| Brick | Module | Contents |
|---|---|---|
| exponential ray kernel | `HTGeometry/ExpRayL2` | `expRay`, its modulus, ray integrability, `∫_T^∞ e^{-2σx}dx` |
| `𝓛` and its holomorphy | `HTGeometry/HalfLineLaplaceL2` | `laplaceRay`, entire truncations, tail bound, `differentiableOn_laplaceRay`, `norm_laplaceRay_le` |
| line = Fourier | `HTGeometry/HalfLineLaplaceFourier` | `rayLine`, `rayDamp`, `fourierIntegral_rayDamp`, `coeFn_fourierTransform_rayDamp`, `memLp_two_laplaceRay_line`, `integral_norm_sq_laplaceRay_line` |
| the class + PW-A | `HTGeometry/HalfPlaneHardy` | `IsHalfPlaneHardy`, `isHalfPlaneHardy_laplaceRay`, `tendsto_integral_norm_sq_laplaceRay_line` |
| line rescaling | `HTGeometry/LineScalingL2` | `memLp_two_comp_const_mul`, `integral_norm_sq_comp_const_mul` |
| L¹∩L² Fourier bridge | `HTGeometry/L2FourierIntegralBridge` | moved out of `RHTower` (which now delegates) |
| test multiplier | `HTGeometry/ExpTestTransform` | `expTestTransform = testTransform ψ (-(i w))`, quadratic decay on strips, `memLp_two_expTestTransform_line` |
| sequence contour shift | `HTGeometry/VerticalStripContourShiftSeq` | the corpus contour shift along a sequence of heights |
| strip mass | `HTGeometry/HardyLineMass` | `memLp_two_hardyLine`, `stripMass`, `stripClamp`, Tonelli finiteness, `exists_seq_stripMass_tendsto_zero` |
| line independence | `HTGeometry/HardyLineIndependence` | `integral_hardyMulTest_line_indep` |
| the datum | `HTGeometry/HardyDatum` | `hardyPreimage`, `testSchwartz`, `integral_schwartz_mul_fourier`, `hardyPreimage_weight_ae_eq` |
| **PW-B** | `HTGeometry/PaleyWienerHalfPlane` | `hardyDatum`, `hardyDatum_ae_zero_of_neg`, `memLp_two_hardyDatum`, **`isHalfPlaneHardy_eq_laplaceRay`** |

Still open in LAYER 4: the exact isometry constant on the `w = σ + iy` parametrisation
(`∫_ℝ‖F(σ+iy)‖²dy = 2π‖φ‖²`, i.e. Burnol's `|ds|/2π`), and the Mellin bridge
`RHTower/MellinHardyBridge` (`L²(a,∞;dt) ≅ A^sH²`, `ℂ·1_{0<t<a}+L²(a,∞) ≅ s/(s−1)A^sH²`).

### PW-A (easy direction) — `HTGeometry/HalfLineLaplaceL2.lean`
1. `laplaceL2 φ w` is absolutely convergent for `Re w > 0` (Cauchy–Schwarz, `‖e^{-σ·}‖_{L²(0,∞)} = (2σ)^{-1/2}`).
2. Truncations `∫_0^T` are entire (`HTGeometry/HalfPlaneGapApproximation.differentiable_integral_kernel`);
   the tail is `≤ ‖φ‖e^{-σT}/√(2σ)`, so convergence is locally uniform on `Re w > 0` and
   `TendstoLocallyUniformlyOn.differentiableOn` gives holomorphy.
3. `laplaceL2 φ (σ + y·I) = 𝓕(e^{-σ·}φ)(y/2π)` and `∫_ℝ‖·‖²dy = 2π∫_0^∞e^{-2σx}|φ|²dx ↑ 2π‖φ‖²`.

### PW-B (hard direction) — the frozen chain
Hypothesis: `F` holomorphic on `Re w > 0`, `F(σ+i·) ∈ L²` for each `σ>0` with
`∫_ℝ‖F(σ+iy)‖²dy ≤ M`.
1. **Test transform.**  For `θ : ℝ → ℝ` smooth with compact support put
   `Θ(w) := ∫ θ(x)e^{wx}dx`.  `Θ` is entire; on a strip `c ≤ Re w ≤ d` it is bounded, and one
   integration by parts gives `‖Θ(w)‖ ≤ C/‖w‖`, hence `Θ(c+i·) ∈ L²`.
2. **Contour shift.**  `Φ := F·Θ` is holomorphic on `Re w>0` and `Φ(σ+i·) ∈ L¹`
   (Cauchy–Schwarz).  Horizontal edges: with `g(T) := ∫_c^d‖F(σ+iT)‖²dσ ∈ L¹(ℝ)`, choose
   `T_n → ∞` with `g(T_n)+g(-T_n) → 0`; then
   `‖∫_c^d Φ(σ±iT_n)dσ‖ ≤ √(g(±T_n))·(∫_c^d‖Θ‖²dσ)^{1/2} → 0`.
   A **sequence** version of `HTGeometry/VerticalStripContourShift.integral_vertical_line_eq_of_horizontal_tendsto`
   is needed (the corpus version demands the full `atTop` filter).  Conclusion:
   `J(σ) := ∫_ℝ Φ(σ+iy)dy` is independent of `σ > 0`.
3. **Parseval bridge.**  With `h_σ := 𝓕⁻¹_{L²}(y ↦ F(σ+2πiy))` one has
   `∫_ℝ h_σ(x)e^{σx}θ(x)dx = (1/2π)J(σ)`, using `∫ f g = ∫ 𝓕f(-ξ)𝓕g(ξ)dξ` for `f,g ∈ L²` and
   `𝓕(e^{σ·}θ)(ξ) = Θ(σ − 2πiξ)`.
4. **σ-independence.**  Hence `∫ θ·(e^{α·}h_α) = ∫ θ·(e^{β·}h_β)` for every smooth compactly
   supported `θ`, and `mathlib`'s `ae_eq_of_integral_contDiff_smul_eq` gives
   `e^{α·}h_α = e^{β·}h_β` a.e.  Put `φ := e^{1·}h_1`, so `h_σ = e^{-σ·}φ` for every `σ>0`.
5. **Support and membership.**  `∫e^{-2σx}|φ|²dx = ‖h_σ‖² ≤ M/2π` for all `σ>0`;
   `σ→∞` forces `φ = 0` a.e. on `(-∞,0)`, `σ→0` (monotone convergence) gives `φ ∈ L²(0,∞)` with
   `2π‖φ‖² ≤ M`.
6. **Conclusion.**  `F(σ+iy) = 𝓛φ(σ+iy)` a.e. on each line, and both sides are continuous, so
   `F = 𝓛φ` on the whole half-plane.

Consequence (free, and needed for Thm 4.8): `‖F(w)‖ ≤ ‖φ‖(2 Re w)^{-1/2}`, i.e. elements of `H²`
are bounded on `Re w ≥ ε > 0`.

### Then
* `RHTower/MellinHardyBridge.lean` — transport to `f̂(s)=∫_0^∞f(t)t^{-s}dt`:
  `L²(a,∞;dt) ≅ A^sH²` and `ℂ·1_{0<t<a} + L²(a,∞;dt) ≅ s/(s−1)·A^sH²`.
* Prop. 4.1, 4.2, 4.3 (`K` half), Lem. 4.4, Thm. 4.8, Def. 12/Thm. 4.9/Lem. 4.10.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven on paper (the paper itself supplies the proofs)
- [ ] 2 → 3  formalized: all layers Lean-closed, no `sorry`/`axiom`
- [ ] 3 → 4  publication-ready

## Corpus assets REUSED (do not rebuild)

| Need | Corpus/mathlib owner |
|---|---|
| Mellin--Plancherel unitary `L²(ℝ₊,dˣx) ≃ L²(ℝ)` | `RHTower/L2MellinUnitary.lean` (`mellinUnitary`) |
| Extended Sonine space `L_a`, aperture monotonicity, closedness | `BurnolSoninEvenCosineAperture`, `BurnolSoninApertureMonotone`, `BurnolSoninRieszVector` |
| Completed right Mellin evaluator `M(f)(w)` | `BurnolSoninEvaluationAperture.soninMellinEvaluation` |
| Sonine carrier `K_a` (full line) | `SoninEulerCornerConcrete.centralSoninCarrier` |
| `K_a` antitone | `SoninApertureRestrictionDefect.centralSoninCarrier_antitone` |
| Time/frequency band transversality | `SoninL2ShellNull.physicalForbidden_inf_fourierForbidden_eq_bot` |
| Band-product compactness, strict alternating block | `SoninEulerCornerConcrete.norm_centralSoninAlternatingBlock_lt_one` |
| Friedrichs angle ⇔ closed sum | `HTGeometry/FriedrichsClosedSum.lean` |
| co-Poisson source space, quotient, intertwining | 572 `Burnol*`/`*CoPoisson*` modules in `RHTower/` |

## Duplicate guard
`scripts/lean_dupcheck.py <new files...>` reports any declaration name in the new files that
already exists elsewhere in the tree (a collision breaks the area umbrella even though
`lake build <module>` of the new file alone succeeds).  One collision was caught this way:
`centralSoninCarrier_antitone`.

## Log
- 2026-08-22 — created; paper inventory extracted; layer plan fixed.
- 2026-08-22 — LAYER 1 (`MinimalCompleteSystem`), LAYER 2 (`MonotoneDisjointInfiSup`), §7 index
  framework (`MinimalCompleteSystemChain`), the closed-band-sum bridge (`SoninForbiddenClosedSum`),
  **Prop. 4.6** (`SoninCarrierApertureChain`) and the §2 chain ends
  (`SoninCarrierApertureLimits`) are Lean-closed and umbrella-wired; axioms clean.
- 2026-08-22 — **Theorem 2.1 CLOSED**, axiom-clean.  Chain: `SoninTruncatedMellinCauchy` →
  `SoninMellinHalfPlaneExtension` → `SoninKernelPairing` → `SoninNearZeroKernelVanishing` →
  `SoninPureChiKernel` → `SoninFunctionalEquation` → `SoninEntireMellin`.  New reusable
  `HTGeometry` bricks: `ImaginaryAxisCpow`, `ReflectionSplitIntegral`, `PowerFourierGamma`,
  `DampedPowerOscillation`, `OscillatoryPowerIntegral`, `TruncatedPowerFourierBound`,
  `TruncatedPowerFourierLimit`, `NearZeroTruncatedPower`, `PowerTailL2`, `InvAbsTailL2`,
  `TruncatedMellinEntire`.
- 2026-08-22 — **LAYER 4 core CLOSED**: Paley–Wiener for the Hardy space of the right half-plane,
  both directions, axiom-clean (`HTGeometry/PaleyWienerHalfPlane.isHalfPlaneHardy_eq_laplaceRay`).
  Twelve new `HTGeometry` modules (table above).  The proof avoids the area mean-value bound: the
  horizontal edges are killed along a sequence of heights extracted from Tonelli, and the
  `L²`-vs-`L¹` mismatch is repaired by the corpus's `CompactTestTransform` multiplier.
- 2026-08-22 — **Mellin dictionary CLOSED**: `RHTower/MellinHardyBridge.lean`.  The substitution
  `t = a e^x` (`integral_Ioi_expScale`, `integrableOn_Ioi_expScale`,
  `quasiMeasurePreserving_expScale`, `quasiMeasurePreserving_logScale`) transports
  `L²((a,∞); dt)` onto `L²((0,∞); dx)` through `logChart a f x = √a e^{x/2} f(a e^x)`, with
  `integral_norm_sq_logChart` the isometry of masses, `logChartInv` the inverse chart, and
  `mellinTail_eq_laplaceRay`:
  `∫_a^∞ f(t)t^{-s}dt = a^{1/2-s} · 𝓛(logChart a f)(s − 1/2)`.
  Both directions of Burnol's `A^s H²` description are then
  `isHalfPlaneHardy_mellinTail` and `exists_tail_datum_of_isHalfPlaneHardy`.
- 2026-08-22 — `HTGeometry/HalfPlaneHardyMul.lean`: the multiplier calculus for `H²` —
  `isHalfPlaneHardy_mul_of_bounded` (bounded holomorphic multiplier) and
  `isHalfPlaneHardy_mul_of_bounded_off_ball` (multiplier bounded only away from one point, with the
  product bounded near it).  The second is exactly Burnol's mechanism for Prop. 4.2/4.3
  (`s^l/(s-ρ)^l` bounded away from `ρ`, the product holomorphic at `ρ`).
- 2026-08-22 — `HTGeometry/HalfPlaneHardyShift.lean`: the Cauchy kernel `(w+c)⁻¹` is the Laplace
  transform of `e^{-cx}` (`laplaceRay_expRay`), hence lies in `H²` with mass `(2 Re c)⁻¹`
  (`isHalfPlaneHardy_inv_shift`), is bounded by `(Re c)⁻¹` there, and multiplying by it preserves
  `H²` (`isHalfPlaneHardy_mul_inv_shift` — Burnol's Lem. 4.4 mechanism).  Plus the linear algebra
  `IsHalfPlaneHardy.congr`, `isHalfPlaneHardy_const_mul`, `isHalfPlaneHardy_add`.
- 2026-08-22 — `RHTower/MellinHeadHardy.lean`: `∫_0^a t^{-s}dt = a^{1-s}/(1-s)`
  (`integral_head_cpow`), the renormalising multiplier `(w-1/2)/(w+1/2)` is bounded by `3` on the
  half-plane, and the renormalised Mellin transform of `c·1_{(0,a)} + g` splits as
  `-c a^{1/2}/s + ((s-1)/s)·𝓛(logChart a g)(s-1/2)` (`renormalised_mellin_headTail`), which is a
  Hardy function (`isHalfPlaneHardy_renormalisedHeadTail`).  This is Burnol's identification of
  `ℂ·1_{(0,a)} + L²(a,∞)` with `s/(s−1)A^sH²`.
- 2026-08-22 — `RHTower/ZetaHardyQuotient.lean`: `{t}/t ∈ L²(1,∞)` (`memLp_two_fractOverId`),
  Abel summation in the Hardy chart `ζ(s)/s = 1/(s-1) − 𝓛(logChart 1 ({t}/t))(s−1/2)`
  (`zeta_div_eq_laplaceRay`), and `(s−1)ζ(s)/s²` is a Hardy function
  (`isHalfPlaneHardy_zetaCore`).  This is the analytic input of Prop. 4.2.

### Prop. 4.2 — Hardy half CLOSED
`RHTower/ZetaHardyQuotientPow.lean`: `zetaHardyCore` is the Hardy representative of
`(s−1)ζ(s)/s²` (`zetaHardyCore_eq`), `zetaHardyPow_eq` identifies
`zetaHardyCore·((w+1/2)⁻¹)^l` with `(s−1)ζ(s)/s^{l+2}`, and **`isHalfPlaneHardy_zetaQuotient`**:
any `H` holomorphic on the half-plane, continuous at `ρ − 1/2`, with
`H·(w − (ρ−1/2))^l = zetaHardyCore·((w+1/2)⁻¹)^l` off `ρ − 1/2`, is a Hardy function.
The only remaining ζ-specific input for the *literal* Prop. 4.2 is producing that `H` from the
order of vanishing of `ζ` at `ρ` (mathlib `natCast_le_analyticOrderAt` gives the factorization).
- 2026-08-22 — `HTGeometry/HalfPlaneHardyMul.lean` generalised:
  `isHalfPlaneHardy_of_bounded_off_ball` now takes the *product* `H` with its own holomorphy and
  only needs `H = F·g` away from the bad ball, so the multiplier may have a pole inside the
  half-plane; and `isHalfPlaneHardy_of_div_pow` packages the case `H·(w−w₀)^l = F` with `H`
  continuous at `w₀` — dividing a Hardy function by a zero of the required order.
- 2026-08-22 — Prop. 4.2, Hardy half, in both forms:
  `RHTower/ZetaHardyQuotientPow.isHalfPlaneHardy_zetaQuotient` (interior zero, via
  `ContinuousAt`) and `isHalfPlaneHardy_zetaQuotient_bounded` (the zero may sit on the boundary
  `Re ρ = 1/2`, only a one-sided bound is needed).  Supporting general lemmas in
  `HTGeometry/HalfPlaneHardyMul`: `isHalfPlaneHardy_of_div_pow_bounded`,
  `isHalfPlaneHardy_of_div_pow`, and `exists_isHalfPlaneHardy_div_pow` (removable singularity from
  `natCast_le_analyticOrderAt`).
  **Note on mathlib's `riemannZeta 1`:** it is a junk value, so the formula
  `(s−1)·riemannZeta s` is *wrong* at `s = 1` while the true continuous value is `1`.  All the
  Hardy statements are therefore phrased through `zetaHardyCore` (the honest Laplace
  representative), with `zetaHardyCore_eq` / `zetaHardyPow_eq` giving the ζ-meaning away from
  `s = 1`.  Do not try to state them with `riemannZeta` alone.
- 2026-08-22 — `RHTower/MellinHardyClasses.lean`: `IsMellinTailHardy` (`A^sH²`) and
  `IsMellinHeadHardy` (`s/(s−1)A^sH²`, defined through a Hardy representative so a pole at `s=1` is
  allowed); `isMellinTailHardy_mellinTail` and `exists_memLp_of_isMellinTailHardy` (both directions
  of the Paley–Wiener identification); **Lemma 4.4** (`div_id`, `div_one_sub`) and **Prop. 4.3's
  `K_a` half** (`div_sub`).
- 2026-08-22 — `RHTower/SoninExtendedApertureChain.lean`: the extended chain.  Reuses the corpus's
  `meanZeroBand` (do **not** redefine it) and adds `centralMeanZeroFourier`,
  `centralSoninExtendedCarrier`.  **Prop. 4.6 for `L_a`**
  (`topologicalClosure_iSup_centralSoninExtendedCarrier`) and the **§2 chain for `L`**
  (`topologicalClosure_iSup_pos_centralSoninExtendedCarrier`,
  `iInf_pos_centralSoninExtendedCarrier`; the latter by "constant on every band ⇒ constant ⇒ 0 in
  `L²`", using `memLp_const_iff`).
- 2026-08-22 — `RHTower/LPropertyStrips.lean`: **Definition 10** (`HasLProperty`, with the estimate
  asked for `1 ≤ |Im s|` so the finitely many poles at `s = 0, 1` are avoided) and **Definition 12**
  (`HasStripRapidDecrease`), their stability under sums and scalars, `HasStripRapidDecrease →
  HasLProperty`, stability under multiplication by anything of polynomial vertical growth
  (reusing the corpus's `GaloisForLFunctions.HasStripPolyGrowth`), stability under `s ↦ 1-s`, and
  hence **Lemma 4.10** in the form `hasStripRapidDecrease_chi_mul_reflect`.  The only input left for
  the literal Lemma 4.10 is `HasStripPolyGrowth χ` (Titchmarsh IV.12.3).
  Refined the same day: `mul_stripPolyGrowth` and `hasStripRapidDecrease_chi_mul_reflect` now take
  `HasStripPolyGrowthOffReal` (polynomial vertical growth asked only for `1 ≤ |Im s|`).  This is the
  *correct* hypothesis: `χ = Γ_ℝ(1−s)/Γ_ℝ(s)` has poles at `s = 1, 3, 5, …`, all on the real axis,
  so the corpus's `GaloisForLFunctions.HasStripPolyGrowth χ` is false while the off-real version is
  true.  `HasStripPolyGrowth.offReal` records the implication.

### Thm 4.8 - the sharp `χ` input, CLOSED (2026-08-23)

`RHTower/ZetaChiLineSharp`.  `ZetaChiStripGrowth` only gives `‖χ(s)‖ ≤ C(1+|t|)^N` with an `N` coming
from the Gamma recurrence; Theorem 4.8 needs Titchmarsh's *sharp* exponent
`‖χ(σ+it)‖ ≤ C|t|^{1/2-σ}` on the vertical lines bounding the Phragmen-Lindelof strip.

The corpus already owns the parameter-uniform vertical Gamma law
`GaloisForLFunctions.RHTower.exists_twoSided_gamma_vertical_ratio` (in `GammaVerticalRatioUniform` —
a module that ALREADY EXISTED; a first draft of it was written here and discarded once the search
tool surfaced it).  `exists_norm_Gamma_quotient_line` shifts the two abscissae `σ/2` and `(1-σ)/2`
into its parameter box with `n = ⌈|σ|⌉ + 1` Gamma recurrences — large enough that the shifted
abscissa always sits to the right of `(1-σ)/2`, so the *upper* half of the two-sided law applies —
and the `n` shift factors contribute exactly the `τ^n` the recurrence removed.  Combining with the
extracted `norm_zetaChi_eq` (the `Γ_ℝ` quotient modulus, pulled out of `ZetaChiStripGrowth`) and the
conjugate symmetry `norm_Gamma_line_abs` gives `exists_norm_zetaChi_line_le`.

### Thm 4.8 - the crude interior bound, CLOSED (2026-08-23)
`RHTower/SoninExtendedMellinCrude`.  `extendedMellinRight a c d f s = extendedTailMellin + d·a^{1-s}/(1-s)`
is the continued Mellin transform right of the imaginary axis; it agrees with the honest integral on
`1/2 < Re s < 1` (`extendedMellinRight_eq`) and is holomorphic on `{Re s > 0} \ {1}`.  The corpus's
uniform Cauchy estimate `norm_soninMellinExtension_le` bounds the Sonine part by
`a^{-σ}((2+‖s‖/σ)/2π)N(a)‖g‖`, the sinc part by `norm_sincTail_le`, and the head by `‖d‖a^{1-σ}`
once `|t| ≥ 1`, giving `exists_norm_extendedMellinRight_le`: `O(1+‖s‖)` on every closed substrip of
the open right half-plane — *including the critical line*, which is exactly where the two Hardy
representatives fail and where Phragmen-Lindelof needs a growth hypothesis.

### Thm 4.8 - the Phragmen-Lindelof machinery, CLOSED (2026-08-23)
* `HTGeometry/StripLineBound` — `exists_line_bound_of_high`, `exists_line_bound_weighted`,
  `exists_strip_bound_of_high`: a continuous function bounded above a fixed height on a line (or a
  strip) is bounded on the whole line (strip), by compactness of the remaining segment.  PL demands
  the edge bounds for *every* height, while the analytic estimates only reach large heights.
* `HTGeometry/PhragmenLindelofPower` — `norm_le_mul_rpow_of_vertical_strip`: an entire function
  bounded by `C‖s-c₀‖^ν` on the two edges of a strip lying strictly right of `c₀`, with at worst
  polynomial vertical growth inside, obeys the same bound throughout.  Dividing by `(s-c₀)^ν` makes
  the edges genuinely bounded; the growth hypothesis of mathlib's `PhragmenLindelof.vertical_strip`
  is met with `B = N/c` because `1 + x ≤ exp x`.
* `RHTower/SoninLProperty` — the numerator identities
  `extendedMellinNumeratorRight_eq : Right s = s(1-s)·extendedMellinRight s` and
  `extendedMellinNumeratorLeft_eq`, which turn every estimate for the continuations into one for the
  entire numerator, plus the right edge bound `exists_norm_numerator_right_line`
  (`≤ C(1+|t|)²`, from the Hardy bound `exists_norm_mellinTail_bounded`).

### Thm 4.8 - the one remaining gap: `burnolChiFactor = zetaChi`
The corpus's functional equation is stated with
`burnolChiFactor s = Γ(1-s)·(2π)^{s-1}·2cos(π(s-1)/2)`, while the new sharp line bound
`exists_norm_zetaChi_line_le` is stated for `zetaChi s = Γ_ℝ(1-s)/Γ_ℝ(s)`.  These are the same
function — `χ(s) = 2^s π^{s-1} sin(πs/2) Γ(1-s)` — but the corpus has no lemma identifying them.
Two routes:
1. prove `burnolChiFactor = zetaChi` from Legendre duplication (`RHTower.gamma_duplication_one_sub`)
   and Euler reflection; or
2. prove the sharp bound for `burnolChiFactor` directly, anchoring the Gamma modulus at the critical
   line: `‖Γ((1-σ)+iτ)‖ = (‖Γ((1-σ)+iτ)‖/‖Γ(1/2+iτ)‖)·‖Γ(1/2+iτ)‖`, where the ratio is the corpus's
   uniform law and `|Γ(1/2+iτ)|² = π/cosh(πτ)` is exact (see `HTGeometry/GammaCriticalLineModulus`),
   together with `e^{|y|}/4 ≤ ‖cos(x+iy)‖ ≤ e^{|y|}` for `|y| ≥ 1`.
Route 1 is preferable: it makes the sharp bound available to the whole functional-equation chain.

### Thm 4.8 - remaining plan
With the sharp line bound in hand the proof is:
* right edge `σ = b' > 1/2`: `‖F‖` bounded by `HardyLineIsometry.norm_le_of_isHalfPlaneHardy`;
* left edge `σ = a' < 1/2`: `F(s) = χ(s)·G(1-s)` with `Re(1-s) > 1/2`, so
  `‖F(a'+it)‖ ≤ C|t|^{1/2-a'}` by the new bound;
* interior: `exists_norm_extendedMellinRight_le` (`O(1+‖s‖)`, done);
* `PhragmenLindelof.vertical_strip` (mathlib) applied to `G(s)/(s-c)^{μ+2}` with
  `G(s) = s(1-s)M(f)(s)` entire (Prop. 2.2) and `μ = max(1/2-a,0)+ε`.
Choosing the enlarged strip `[min(a,1/2)-ε/2, max(b,1/2)+1]` keeps the exponent at
`max(1/2-a,0)+ε/2` and puts both edges strictly off the critical line.

Items 1 and 2 are done: `SoninExtendedMellinEdge` proves
`exists_norm_mellinTail_bounded` (the Hardy bound, uniform in the height),
`exists_norm_extendedMellinRight_bounded` and the agreement lemma `extendedMellinRight_eq_left`.
What is left is the left edge bound (blocked only on `burnolChiFactor = zetaChi`), the crude strip
bound for the numerator (immediate from `exists_norm_extendedMellinRight_le` through the two
numerator identities), and the final `norm_le_mul_rpow_of_vertical_strip` assembly with
`A' = min A (1/2) - ε/2`, `B' = max B (1/2) + 1`, `ν = max(1/2-A,0) + ε + 2`, `c₀ = A' - 1`.

### Prop. 2.2 - FULLY CLOSED (2026-08-23)

The reflected half needed the functional equation on `L_a`.  Five more modules, plus a second corpus
generalisation.

**Corpus generalisation.**  The whole `χ`-pairing chain also only used the Fourier condition.
`SoninNearZeroKernelVanishing` now proves the head-carrying
`integral_nearZeroKernel_mul_fourier_eq` (Plancherel for the truncated power on `(0,a)`, no Sonine
hypothesis) with the old vanishing statement as its corollary; `SoninKernelPairing`,
`SoninPureChiKernel` and `SoninFunctionalEquation` take `f ∈ (centralFourierForbidden a)ᗮ`, and the
head-carrying versions `soninMellinExtension_add_head_eq_chi_pairing` and
`soninMellinExtension_add_head_functional_equation` are the new primitives, with the `K_a` forms
recovered from `integral_nearZeroHead_eq_zero`.

**`RHTower/SoninDecayTailMellin`** (generalising the sinc module, which is now a thin wrapper):
`HasInverseDecay g C` (`‖g(t)‖ ≤ C/|t|`) makes the Mellin tail `∫_T^∞ g(t)t^{-s}dt` absolutely
convergent and holomorphic on `Re s > 0`.

**`RHTower/SoninDecayTailIdentity`**: for such a `g` in `(centralFourierForbidden a)ᗮ` the corpus's
continuation *is* that convergent integral — both are holomorphic on the connected half-plane and
agree on `Re s > 1/2`, so the identity theorem finishes.

**`RHTower/SoninSincFullMellin`**: the value `∫_0^∞ sin(2πat)/(πt) · t^{-s} dt = χ(s)·a^s/s`, proved
*without* the sine Mellin transform.  For `0 < a ≤ b` the difference
`fourierBandIndicator b - fourierBandIndicator a` has Fourier transform vanishing on the band of
aperture `a`, so the head-carrying functional equation evaluates the difference of the two full
Mellin transforms as `χ(s)(b^s - a^s)/s`; the dilation law `sincFullMellin c s = c^s · sincFullMellin 1 s`
(change of variables) then forces `sincFullMellin 1 s = χ(s)/s` by comparing `a = 1, b = 2`, since
`2^s ≠ 1` for `Re s > 0`.

**`RHTower/SoninExtendedFunctionalEquation`**: splitting `f = h + c·fourierBandIndicator a` and
adding the two previous results gives
`extendedFullMellin a c f s = χ(s)·M(F₊f)(1-s)` on `0 < Re s < 1/2`.

**`RHTower/SoninExtendedMeromorphic`**: right of the critical line
`R(s) = s(1-s)·extendedTailMellin + s·d·a^{1-s}` is holomorphic on `Re s > 0`; left of it
`L(s) = (1-s)χ(s)(c·a^s + s·(tail of F₊f at 1-s))` is holomorphic on `Re s < 1`; they agree on
`0 < Re s < 1/2` by the extended functional equation, and `glueVert` makes the result entire.  That
is Proposition 2.2: the only possible poles of `M(f)` are simple ones at `s = 0` and `s = 1`.

### Prop. 2.2, right half - CLOSED (2026-08-23)

Four new modules, plus one corpus generalisation.

**Corpus generalisation (no duplication).**  The uniform Cauchy estimate behind Theorem 2.1 never
used the *physical* Sonine condition — only that the Fourier transform vanishes on the band.  The
hypothesis `f ∈ centralSoninCarrier a` was therefore weakened to `f ∈ (centralFourierForbidden a)ᗮ`
throughout the chain (`SoninDeBrangesCarrier.fourier_indicator_ae_zero_of_mem_fourierOrthogonal`,
`SoninTruncatedMellinCauchy.norm_truncMellin_le`,
`SoninTruncatedMellinFamily.norm_soninTruncMellin_sub_le`, and the seven theorems of
`SoninMellinHalfPlaneExtension` up to `differentiableOn_soninMellinExtension`); the five call sites
now pass `hf.2`.  `soninMellinExtension_eq_soninMellinIntegral` keeps the full hypothesis, since
dropping the band from the integral does need the physical vanishing.

**`RHTower/SoninBandSinc`.**  `𝓕(1_{[-a,a]})(u) = sin(2πau)/(πu)` (`fourierIntegral_centralIndicator`,
by `integral_exp_mul_complex`), transported through the `L²` Fourier bridge and the reflection
identity `𝓕⁻¹ = R ∘ 𝓕` to `coeFn_fourierBandIndicator_ae`, with the decay
`‖fourierBandIndicator a (t)‖ ≤ 1/(π|t|)`.

**`RHTower/SoninSincTailMellin`.**  Because of that `1/|t|` decay the Mellin tail
`sincMellin a s = ∫_a^∞ (fourierBandIndicator a)(t) t^{-s} dt` converges *absolutely* on `Re s > 0`;
truncations are entire (`differentiable_truncatedMellin`) and converge locally uniformly with the
explicit remainder `(1/π)·T^{-σ}/σ`, so `differentiableOn_sincMellin` holds on the whole half-plane.

**`RHTower/SoninExtendedMellinExtension`.**  `centralMeanZeroFourier a` is the `𝓕`-pullback of
`meanZeroBand a` (`mem_centralMeanZeroFourier_iff`), so a vector of `L_a` has a *constant* Fourier
head `c` (`ae_fourier_eq_of_mem_extended`), and `f - c • fourierBandIndicator a` has Fourier
transform vanishing on the band (`sub_smul_fourierBandIndicator_mem`).  Hence
`exists_differentiableOn_extendedTailMellin`: the Mellin tail of any vector of `L_a` continues
holomorphically to `Re s > 0`, as `soninMellinExtension (f - c•v) + c·sincMellin`.

**`RHTower/SoninExtendedMellinPole`.**  The physical head is constant too, so on `1/2 < Re s < 1`
the full Mellin integral splits as `c·a^{1-s}/(1-s) + tail`.  Multiplying by `1-s` gives a function
holomorphic on `Re s > 0`: Proposition 2.2's right half.

*Still open for Prop. 2.2*: the reflected half.  `L_a` is cosine invariant, so the same theorem
applies to `F₊f`; what is missing is the `L_a` analogue of
`SoninFunctionalEquation.soninMellinExtension_functional_equation`, which would turn
`M(F₊f)` on `Re s > 0` into `M(f)` on `Re s < 1` and produce the pole at `s = 0`.

### Prop. 4.2 - CLOSED (2026-08-23)
`RHTower/ZetaMellinHeadHardy`.  The renormalised transform of `ζ(s)/(s-ρ)^l` is
`(w+1/2)·zetaHardyCore(w)/(w-w₀)^l` with `w₀ = ρ - 1/2`, and multiplying a Hardy function by
`w + 1/2` is illegal.  The splitting `w + 1/2 = (w - w₀) + (w₀ + 1/2)` (`div_pow_split`) rewrites it
as `zetaHardyCore/(w-w₀)^{l-1} + (w₀+1/2)·zetaHardyCore/(w-w₀)^l`: two divisions of ONE Hardy
function by powers of one of its own zeros.

`exists_isHalfPlaneHardy_zetaCore_div` performs either division, splitting on whether `ρ` lies
strictly right of the critical line:
* interior (`0 < Re(ρ-1/2)`): `zetaHardyCore` is analytic at `w₀`, and the order transfer
  `analyticOrderAt zetaHardyCore w₀ ≥ k` comes from the `ζ` factorization through
  `zetaCoreFactor g w = (w-1/2)g(w+1/2)/(w+1/2)²`; then `exists_isHalfPlaneHardy_div_pow`.
* boundary or left (`Re ρ ≤ 1/2`, in particular every zero on the critical line): the quotient is
  already holomorphic on the open half-plane, and `isHalfPlaneHardy_of_div_pow_bounded` only needs
  the local bound `‖zetaCoreFactor g‖ ≤ ‖zetaCoreFactor g w₀‖ + 1` on a small ball, which is
  continuity of the analytic factor.

The output is stated existentially, `∃ G, IsMellinHeadHardy 1 G ∧ ∀ s, … s ≠ ρ → G s = ζ(s)/(s-ρ)^l`,
because Lean's `x/0 = 0` makes the literal quotient junk at `s = ρ` while the true object there is
the value of the analytic continuation.

### LAYER 4 isometry constant - CLOSED (2026-08-23)
`HTGeometry/HardyLineIsometry`.  `hardyVerticalLine σ y = σ + iy`, and the change of variables
`y = 2πξ` (`LineScalingL2.integral_norm_sq_comp_const_mul`) turns the Fourier normalisation of
`HalfLineLaplaceFourier` into Burnol's arclength one:
`∫ ‖F(σ+iy)‖² dy = 2π ∫_0^∞ e^{-2σx}‖φ(x)‖² dx`, increasing to `2π‖φ‖²` as `σ ↓ 0`
(`integral_norm_sq_laplaceRay_vertical`, `tendsto_integral_norm_sq_laplaceRay_vertical`, and the
same two through the Paley-Wiener datum of an arbitrary Hardy function).  The module also records
`norm_le_of_isHalfPlaneHardy`, the pointwise bound `‖F(w)‖ ≤ ‖φ‖(2 Re w)^{-1/2}` that Theorem 4.8
feeds into Phragmen-Lindelof.

### Prop. 4.1 - CLOSED (2026-08-23)
`RHTower/MellinHeadHardyConverse` + `RHTower/MellinHeadHardyEquiv`.

*Converse (the new half).*  Write `w = s - 1/2`, `u = w - 1/2 = s - 1`, `v = w + 1/2 = s`, so
`v - u = 1`.  If `G` is the Hardy representative of `F`, i.e. `G = (u/v)·a^w F(s)`, put
`κ := -G(1/2)` and `Ψ := G + κ/v`.  `Ψ` is Hardy (a constant multiple of `1/(w+1/2)` is the Laplace
transform of `e^{-x/2}`) and vanishes at `w = 1/2`, so `Q := Ψ/u` is Hardy by
`exists_isHalfPlaneHardy_div_pow`.  The partial-fraction collapse

`G + Q + κ/v = (G + κ/v)(1 + 1/u) = (G + κ/v)·v/u = a^w F(s) + κ/u`

shows `a^w F(s)` is a Hardy function minus the explicit simple pole `κ/(s-1)`.  Paley-Wiener turns
the Hardy part into an `L²(a,∞)` tail and the pole into the constant head, giving
`F(s) = c·a^{1-s}/(1-s) + ∫_a^∞ g(t)t^{-s}dt` on `Re s > 1/2`, `s ≠ 1`, with `c = κ a^{-1/2}`.

*Equivalence.*  `headTailMellin a c g s := c·a^{1-s}/(1-s) + ∫_a^∞ g t^{-s}dt` (equal to the honest
Mellin integral for `Re s < 1`, `headTailMellin_eq_mellin`), and
`isMellinHeadHardy_iff : IsMellinHeadHardy a F ↔ ∃ c g, MemLp g 2 … ∧ F = headTailMellin a c g` on
`Re s > 1/2` off `s = 1`.  The `K_a` companion is `isMellinTailHardy_iff`.

### Prop. 4.5 and Prop. 4.7 - CLOSED (2026-08-23)

**Prop. 4.5, literal form.**  `SoninBandCodimensionTwo` measured the drop between `A ⊔ B` and the
sum of the two mean-zero halves.  Since `K_a = (A ⊔ B)ᗮ` and `L_a = (A' ⊔ B')ᗮ` with both sums
closed, `L_a ⊓ K_aᗮ = (A ⊔ B) ⊓ (A' ⊔ B')ᗮ`, so the same number is the codimension of `K_a` in
`L_a`.  Module `RHTower/SoninExtendedCodimensionTwo`.

**Prop. 4.7.**  Two independent steps.

*Strictness.*  `A_b ⊓ (A_a ⊔ B_a) = A_a`: split `g = u + v`, then `v = g - u ∈ A_b ⊓ B_a = ⊥`
because a nonzero vector cannot be time-limited and band-limited at once (corpus
`physicalForbidden_inf_fourierForbidden_eq_bot`, monotonicity of the frequency band supplying the
unequal apertures).  The shell indicator of `[a,b]` lies in `A_b` and not in `A_a`, so
`A_a ⊔ B_a < A_b ⊔ B_b` and, taking perpendiculars, `K_b < K_a`.

*Baire.*  The apertures `a + 1/(n+1)` are cofinal, the carriers are a directed family, and each is
closed; the corpus's `RelativeShellBaireWall.shellBaire_exists_stage` applied to the inclusion
`K_a ↪ L²` produces a single stage `K_a ≤ K_{a + 1/(N+1)}`, contradicting strictness.  So the union
is proper even though Prop. 4.6 makes it dense.

*Eigen-parts.*  `𝓕` maps `A_c` into `B_c` and `B_c` into `A_c` (via `𝓕² = reflection`), so
`S_c = A_c ⊔ B_c` and `K_c` are `𝓕`-stable and reflection-stable.  For `ε = ±1` and `g` the *even*
shell indicator, `h = g + ε • 𝓕 g` is an `ε`-eigenvector in `S_b \ S_a` by the same splitting
argument.  The eigen-projection `f ↦ (evenProjection f + ε • 𝓕 (evenProjection f))/2` keeps `K_a`
invariant and does not change the pairing with `h`, which converts the obstruction into
`K_b ⊓ E_ε < K_a ⊓ E_ε`; Baire then runs verbatim.  Module `RHTower/SoninApertureStrictEigen`.

### `χ` input for Lemma 4.10 - CLOSED
`RHTower/ZetaChiStripGrowth.hasStripPolyGrowthOffReal_zetaChi : HasStripPolyGrowthOffReal zetaChi`,
on an arbitrary strip, above height two.  Proof: the modulus splits as
`pi^(sigma-1/2) * norm (Gamma ((1-s)/2)) * norm (Gamma (s/2))^{-1}` (`norm_Gammaℝ_eq`), and then the
sharp Gamma decay `C1*|tau/2|^N1*exp(-pi|tau|/4)` and the matching reciprocal growth
`C2*|tau/2|^N2*exp(+pi|tau|/4)` cancel their exponentials, leaving a power of the height.
Hence **Lemma 4.10 is unconditional**: `hasStripRapidDecrease_zetaChi_mul_reflect`.

New supporting layer `HTGeometry/GammaStripSharpDecay`:
`norm_Gamma_le_norm_Gamma_add_nat` (off-axis: every recurrence factor has modulus at least 1),
`exists_sharp_bound_norm_Gamma_strip` (arbitrary strip, `C|tau|^N exp(-pi|tau|/2)`) and
`exists_bound_norm_inv_Gamma_strip` (arbitrary strip, `C|tau|^N exp(+pi|tau|/2)`, via Euler
reflection).  Deduplication pass:
`RHTower/SelbergClass/BarnesHorizontalEdges.exists_bound_norm_Gamma_vertical_strip_arbitrary`
already held the same content one layer up; its 38-line proof now delegates to the HTGeometry
version, and `norm_sin_le_exp_abs_im` is an alias of the corpus's
`HTGeometry.norm_csin_le_exp_abs_im`.

### Thm 4.8 - CLOSED (2026-08-23)

`RHTower/SoninLPropertyTheorem`.  `extendedMellinContinuation a c d f = extendedMellinNumerator/(s(1-s))`
and `hasLProperty_extendedMellinContinuation` is the literal Definition 10 estimate.  The assembly is
the frozen plan: enlarged strip `A' = min A (1/2) - ε/2`, `B' = max B 1`, `c₀ = A' - 1`,
`ν = 2 + (1/2 - A')`; the two edges are pushed from "large height" to "every height" by
`exists_line_bound_weighted` (`(1+|t|)^ν ≤ 2^ν‖z-c₀‖^ν` once `σ - c₀ ≥ 1`, `rpow_one_add_abs_le_weight`),
the interior by `exists_strip_bound_of_high`, and `norm_le_mul_rpow_of_vertical_strip` interpolates.
Dividing by `s(1-s)` costs exactly two powers: `‖s‖‖1-s‖ ≥ |τ|² ≥ (1+|τ|)²/4`, and the exponent
bookkeeping is `1/2 - min A (1/2) = max (1/2 - A) 0` (`half_sub_min`), leaving `ε/2` to spare.

Also closed on the way: `exists_norm_numerator_strip` (the crude interior bound; the right branch
uses the Hardy representative, the left branch the functional equation through
`burnolChiFactor_eq_zetaChi` and `hasStripPolyGrowthOffReal_zetaChi`), and
`BurnolChiFactorIdentity.burnolChiFactor_eq_zetaChi` itself (Legendre duplication + Euler reflection;
`cos(π(s-1)/2) = sin(πs/2)`), which unblocked the left edge.

**Trap:** in these strip proofs `set` leaves the local abbreviations as *let-values*, and `ring` /
`positivity` / `nlinarith` then unfold them and blow the heartbeat budget.  `clear_value` immediately
after the `set` block (keeping the defining equations as ordinary hypotheses) is what makes the
Phragmén-Lindelöf assembly compile.

### Thm 4.9 - CLOSED (2026-08-23).  §4 IS NOW COMPLETE

Burnol's smoothing, done on the *function* side (the paper multiplies `G` by `θ(ε(s-1/2)+1/2)`;
here the same operator is the multiplicative convolution it comes from, which avoids needing the
Mellin-Plancherel unitary at all).

Five new modules.

**`HTGeometry/ExpMultiplierRapidDecay`** — `logSmoothMultiplier k w = ∫ k(x)e^{wx}dx` for a smooth
weight vanishing off `[-R,R]`.  `intervalIntegral_expByParts_of_vanishing` (one integration by
parts; the antiderivative `e^{wx}/w` has no branch, unlike the Mellin weight `x^s/s`) iterates to
`intervalIntegral_expByParts_iterate`, giving `w^n K(w) = ±∫k^{(n)}(x)e^{wx}dx`, hence
`exists_bound_pow_norm_logSmoothMultiplier` and `exists_bound_norm_logSmoothMultiplier_strip`
(`‖K‖ ≤ C(1+|τ|)^{-n}` on every strip, from `‖w‖ ≥ |τ| ≥ (1+|τ|)/2`).

**`HTGeometry/ExpMultiplierEntire`** — `differentiable_logSmoothMultiplier`, via the corpus's
`differentiable_integral_kernel`.  That criterion demands the kernel bound at *every* point of the
ambient measure space, so the exponent is composed with `expKernelClamp` first — the same device as
`TruncatedMellinEntire`'s `mellinClamp`.

**`RHTower/SoninExtendedDilation`** — `mem_centralSoninExtendedCarrier_iff` (a vector of `L_a` is
exactly one that is constant on the band and whose Fourier transform is too — the missing converse
half of `ae_fourier_eq_of_mem_extended`, obtained from `Submodule.inf_orthogonal`), and the three
transports: `dilation_mem_centralSoninExtendedCarrier` (`L_a → L_{min(a/r, ar)}`, using
`fourierUnitary_dilation`), `l2Reflection_mem_centralSoninExtendedCarrier`,
`evenProjection_mem_centralSoninExtendedCarrier`, plus `centralSoninExtendedCarrier_antitone`.

**`RHTower/SoninDilationAverage`** — `dilationAverage k f = ∫ k(x)·U_{e^x}f dx` as a Bochner
integral in `L²`, built on the corpus's `rayDilate` and its strong continuity
(`SoninDilationContinuity`).  `dilationAverage_mem_orthogonal` (via `integral_inner`: the average
inherits every orthogonality condition), `dilationAverage_mem_evenSubspace`, `apply_dilationAverage`
(a CLM passes through), and `norm_dilationAverage_sub_smul_le`.

**`RHTower/SoninMellinFunctional`** — the Mellin transform on the strip `1/2 < Re s < 1` is the
restriction of a *continuous linear functional* on all of `L²(ℝ)`:
`mellinFunctional a ha hs = (a^{1-s}/((1-s)·2a))·⟪1_{[-a,a]}, ·⟫ + ⟪1_{(a,∞)}t^{-s̄}, ·⟫`.
The tail vector exists precisely because `Re s > 1/2`, and the head is read off the band indicator.
This is what lets the Mellin transform commute with the Bochner integral.

**`RHTower/SoninMellinMultiplier`** — `integral_cpow_dilation` (the character `r^{s-1/2}`, from the
corpus's `mellin_coe_dilation`), `mellinFunctional_dilationAverage` (the multiplier identity on the
strip), `HasRapidMellin` (**Definition 12**), and `hasRapidMellin_dilationAverage`.  The transfer
from the strip to the whole plane is the identity theorem applied to the two *entire numerators*
(Prop. 2.2), after which `HasStripRapidDecrease.mul_stripPolyGrowth` combines the rapidly decreasing
multiplier with `HasLProperty.stripPolyGrowthOffReal` of Theorem 4.8.

**`RHTower/SoninRapidMellinDense`** — Theorem 4.9.  Prop. 4.6 gives a nearby vector of some `L_b`,
`b > 1`; `Submodule.mem_iSup_of_directed` turns the supremum into a union (the family is directed
because `L` is antitone); the even projection symmetrises it without increasing the distance; a
`ContDiffBump` of radius `δ = min(δ₀/2, log b)` smooths it, and `exp δ ≤ b` is exactly what keeps
every dilate in `L_1`.

Note the aperture bookkeeping: a dilation by `r` moves `L_a` to `L_{a/r}` physically and to
`L_{ar}` on the Fourier side, so only `1/b ≤ r ≤ b` keeps `L_b` inside `L_1` — that, and nothing
else, is why the smoothing must start from `b > 1`.

## §5 LAYER PLAN (opened 2026-08-23)

Prop. 5.1 is Titchmarsh IX.7: *there are `A` and a strictly increasing `T_n > n` with
`|ζ(s)|^{-1} < |s|^A` on `Im s = ±T_n`, `-1 ≤ Re s ≤ 2`.*  A **fixed** power is essential (Thm 5.2
kills the horizontal edges with `G = O(|s|^{-N})` for one fixed `N > A`), and a fixed power is only
reachable with the *averaged* choice of height: a min-gap choice `|T-γ| ≫ 1/log T` gives each of the
`O(log T)` nearby zeros a factor `log log T` and only yields `exp(C log T log log T)`.  Averaging
`Σ_{|γ-T|≤2} log(3/|T-γ|)` over `T ∈ [n,n+1]` gives mean `O(log n)` because
`∫_n^{n+1} log(3/|T-γ|)dT = O(1)` per zero — hence *some* `T` with the whole sum `O(log n)`.

Bricks (status):

| # | Brick | Status |
|---|---|---|
| L5.1 | symmetrised partial fraction `2 logDeriv xi s = Σ'_ρ (1/(s-ρ) + 1/(s-1+ρ))`, both families with positive real part right of the strip; `Re logDeriv xi (2+it) = O(log t)`; `N(t+1)-N(t) = O(log t)` | **DONE** `RHTower/XiLocalZeroDensity` |
| L5.2 | weighted density `Σ_ρ 1/(1+(t-γ)²) = O(log t)` | **DONE** same module |
| L5.3 | **DONE** `RHTower/XiHorizontalLog`: `log‖xi(x+iT)‖ = log‖xi(x₀+iT)‖ + Re ∫_{x₀}^x logDeriv xi`, mirroring the corpus's `ZetaHorizontalArgument` for `ζ` | TODO |
| L5.4 | **DONE** `RHTower/XiSegmentEstimate` + `HTGeometry/PoissonKernelSegmentIntegral`; term-by-term integration of the pair sum across `σ ∈ [-1,2]` (`MeasureTheory.integral_tsum`; far zeros `≤ 9/(2(T-γ)²)`, near zeros `log(3/|T-γ|)`) | |
| L5.5 | the averaging choice of `T ∈ [n,n+1]` | **DONE** `RHTower/XiHeightSelection` |
| L5.6 | **DONE** `RHTower/ZetaInverseHorizontal`; Γ-ratio conversion `xi → ζ` (corpus `exists_twoSided_gamma_vertical_ratio`) and **Prop 5.1** | |
| L5.7 | **Thm 5.2** residue series (rectangles `1/2 ± A ± iT_n`, telescoping bands, `L²` convergence on the critical line) | TODO |
| L5.8 | **Cor 5.3**, **Prop 5.4**, Rem 15 | TODO |

Corpus assets for §5 (do not rebuild): `XiExplicitFormulaLogDeriv.logDeriv_xi_eq_partialFraction`
(multiplicity-exact, absolutely convergent), `logDeriv_xi_split`,
`XiHadamardFactorization.xiZeroCopyReflectEquiv` (`ρ ↦ 1-ρ` on divisor copies),
`XiWardInteriorTraceSplit.logDeriv_riemannZeta_eq_neg_LSeries` and `logDeriv_Gammaℝ_eq`,
`DigammaValuationBoundary.norm_digamma_vertical_le_two_log`,
`CentralReciprocalMoments.xi_divisor_support_re_mem_open_unit`, `RHLadderTheory.xi_ne_zero_of_one_le_re`,
`ZetaHorizontalArgument.exp_zetaHorizontalLog` (the model for L5.3),
`GammaVerticalRatioUniform.exists_twoSided_gamma_vertical_ratio`.

Also noted: Burnol's **(5)** (Müntz) is corpus-owned for zero-mean compactly supported BV sources
(`CCMBVMuntzSummation.mellin_arithmeticSum_eq_zeta_mul`, and on the punctured right half-plane
`CCMConnesConsaniRapidMuntz.mellin_ccmFourierTruncatedPoissonValue_eq_zeta_mul_of_re_pos`); what is
missing for the literal (5) is the `∫φ ≠ 0` correction term `-(1/t)∫φ`.

### Prop 5.1 - CLOSED (2026-08-23)

Six modules, in dependency order.

**`RHTower/XiLocalZeroDensity`** — reindexing the corpus's partial fraction by the reflection
`ρ ↦ 1−ρ` (its `xiZeroCopyReflectEquiv`) cancels the centring terms and leaves
`2·logDeriv xi s = Σ'_ρ (1/(s−ρ) + 1/(s−1+ρ))`, whose *both* families have positive real part right
of the strip.  At `s = 2+it` a zero with `|γ−t| ≤ 1` contributes `≥ 1/5`, giving
`N(t+1)−N(t) = O(log t)` (`exists_card_near_xi_zeros_le`), and the same comparison with the Cauchy
weight gives `Σ_ρ 1/(1+(t−γ)²) = O(log t)` (`exists_tsum_weighted_density_le`).  The `O(log t)` on
the right comes from `logDeriv_xi_split` plus the corpus's digamma vertical bound and the von
Mangoldt series.

**`RHTower/XiZeroBandFinite`** — the divisor is locally finite and lies in the strip, so a horizontal
band carries finitely many copies (`finite_xiZeroCopy_band`, via the corpus's
`xiC_zeros_closedRectangle_finite`); and the Cauchy weight is summable at *every* real height, not
only at the large ones where the density bound was proved.

**`RHTower/XiHorizontalLog`** — the ζ-version in `ZetaHorizontalArgument` transplanted to `xi`:
`exp(Λ(x)) = xi(x+iT)` and hence
`log‖xi(x+iT)‖ = log‖xi(x₀+iT)‖ + Re ∫_{x₀}^x logDeriv xi`.

**`HTGeometry/PoissonKernelSegmentIntegral` + `RHTower/XiSegmentEstimate`** — `∫|v|/(v²+c²)dv` over a
subsegment of `[-3,3]` is at most `log(1+9/c²)`; summing over the divisor
(`MeasureTheory.integral_tsum_of_summable_integral_norm`, with the near/far split supplying the
summability) bounds `|2 Re ∫_σ^2 logDeriv xi|` by `Σ_ρ [log(1+9/(T−γ)²) + log(1+9/(T+γ)²)]`.

**`RHTower/XiHeightSelection`** — the averaging.  `∫_n^{n+1} log(1+9/(T−γ)²)dT` is bounded by an
absolute constant *uniformly in γ* (majorant `log45 + 2|log v| + 1`), only `O(log n)` zeros lie
within distance 5 of the segment (the weighted density again), and a far zero contributes
`≤ 18/(1+(T−γ)²)` at every height.  A measure-theoretic pigeonhole (`exists_height_le_average`)
then produces a height avoiding every ordinate and its negative with the whole sum `O(log n)`.

**`RHTower/ZetaInverseHorizontal`** — reflection identifies the two families
(`tsum_logKernel_reflect`), so the segment estimate gives `log‖xi(σ+iT)‖ ≥ log‖xi(2+iT)‖ − O(log n)`;
`xi = s(s−1)/2·Γ_ℝ·ζ` converts this to `ζ` at a cost of `O(1)`, because the Gamma quotient across
the strip at a fixed height is *bounded* — `exists_gamma_half_ratio_bound` feeds the corpus's
uniform two-sided vertical ratio law with `τ^{-δ} ≤ 1`, using one Gamma recurrence to move a
negative abscissa into the law's parameter box.  With `‖ζ(2+iT)‖ ≥ 1/4` (corpus) the result is
`‖ζ(σ+iT)‖ ≥ T^{-A}`.

**Why the averaging is essential** (recorded so it is not re-litigated): a minimal-gap height, the
usual `|T−γ| ≫ 1/log T`, gives each of the `O(log T)` near zeros a factor `log log T` and only
`exp(C log T log log T)` — not a fixed power.  Averaging replaces the worst case by the mean, which
is `O(1)` per zero.

### Items (5), (6), (7) — resolved as corpus-owned (2026-08-23)

The three §1 formulas do not need new work:

* **(7)** is `archimedeanMellinUnitary_evenFourierTransform` (Connes–Consani chart): the Mellin
  unitary conjugates the even Fourier transform into reflection ∘ multiplication by the scattering
  phase, for *every* even vector — this is `M(F₊f)(s) = χ(s)M(f)(1−s)` in `L²` normalisation.
* **(6)** is `soninMellinEvaluation_burnolCoPoissonSource`.  Note the chart:
  `burnolCoPoissonRightSum g t = Σ_{n≥1} g(t/n)/n − ∫_0^∞ g(1/y)dy/y`, which under `φ(t) = g(1/t)/t`
  is exactly `t·(Σ_n φ(nt) − (1/t)∫φ)`; the substitution `u = 1/τ` turns the corpus identity into
  Burnol's (5) on `1/2 < Re s < 1`.
* **(5)** for zero-mean sources is `mellin_arithmeticSum_eq_zeta_mul` (on `Re s > 1`) continued by
  `mellin_ccmFourierTruncatedPoissonValue_eq_zeta_mul_of_re_pos` to `{Re s > 0} \ {1}` — the
  `CCMFourierTruncatedInput` structure carries `∫_{Ioi 0} f = 0` exactly because the corrected sum is
  what converges.  The only content beyond that is the single normalisation
  `∫_0^∞ {u}u^{-s-1}du = −ζ(s)/s`, which the corpus owns in tail form (`FractionalPartZeta`,
  `mellin_fractTailKernel`, with `isPreconnected_puncturedRightHalfPlane` for the continuation).

So §1 and §2 of the paper are fully accounted for.

## Thm 5.2 — the contour analysis (bricks landed 2026-08-23)

Burnol integrates `G(s)ζ(Z)/(ζ(s)(Z−s))` around the rectangle `1/2 ± A ± iT_n`, lets `n → ∞`
(horizontal edges die) and then `A → ∞` (vertical edges die).  The poles inside are the nontrivial
zeros of `ζ` and the point `Z`; the paper notes that *the trivial zeros and `s = 1` are not
singularities* — at `s = 1` the pole of `G` is cancelled by the zero of `1/ζ`, and at `s = −2k` the
zero of `ζ` is cancelled by the zero of `G` (which comes from `χ(−2k) = 0` in the functional
equation).  Definition 12's class has no pole at `s = 0`.

| Brick | Statement | Status |
|---|---|---|
| E1 | `1/ζ` polynomially bounded on the *whole* horizontal segment at the selected heights: right of the strip by the Dirichlet series, left of it by `1/ζ(s) = χ(1−s)/ζ(1−s)` and the polynomial growth of `χ` | **DONE** `RHTower/ZetaInverseWideHorizontal.exists_seq_zeta_inv_horizontal` (also packages Prop 5.1's heights as a strictly increasing sequence) |
| E2 | horizontal edges → 0 along the selected heights, for any `G` of Definition 12 | **DONE** `RHTower/ResidueContourEdges.tendsto_norm_horizontal_edge_zero` |
| E3 | `L²` mass of the Cauchy kernel on a vertical line is `π/(σ−Re Z)`; Cauchy–Schwarz pairing bound | **DONE** `HTGeometry/CauchyKernelLineMass` |
| E4 | uniform `L²` mass of the continued Mellin transform on `Re s = σ ≥ 2` (Hardy tail + explicit head) | **DONE** `RHTower/MellinLineMass.exists_integral_norm_sq_extendedMellin_line_le` |
| E5 | right-hand vertical edge → 0 as `σ → ∞` | **DONE** `RHTower/MellinLineMass.tendsto_vertical_edge_zero` |
| R1 | `G(−2k) = 0` and `G` regular at `0` for `G` the continued Mellin transform of a vector of `L_1` (from the extended functional equation continued to `ℂ`) | **DONE** `RHTower/MellinContinuationOrder` |
| R1' | `M(f)` vanishes at every trivial zero and its numerator vanishes at `0` (so `M(f)` is regular there) | **DONE** `RHTower/MellinTrivialZeros` |
| R2 | the rectangle residue identity for `G(s)ζ(Z)/(ζ(s)(Z−s))` | TODO — **the engine already exists**: `HTGeometry/RectangleResidueTheorem.rectangleIntegral'_eq_sum_laurentCoeff` is the residue theorem on a rectangle *for poles of arbitrary order* (`RectangleIntegral' f z w = ∑_{p ∈ P} laurentCoeff f p (-1)`), so Burnol's multiplicity remark is already covered.  What remains: the finite pole set (finiteness of ζ-zeros in a rectangle — corpus-owned), `MeromorphicAt` of the integrand at each point, `AnalyticAt` off `P`, and the identification of each `laurentCoeff`.  Putting `0`, `1` and the trivial zeros into `P` and showing their coefficients vanish is easier than proving analyticity there — note `M(f) = N/(s(1-s))` is literally junk-valued at `0` and `1` in Lean, so it is *not* `AnalyticAt` there even though the singularity is removable. |
| R3 | assembly: absolute convergence of the residue series and **Theorem 5.2** | **DONE (pointwise)** `RHTower/BurnolResidueSeries.tendsto_residueSum_extendedMellin` |
| R4 | **Cor 5.3**, **Prop 5.4**, Rem 15 | **Cor 5.3 DONE** (`extendedMellinContinuation_eq_zero_of_dvd`); Prop 5.4 and Rem 15 TODO |

**Search note (2026-08-23).**  `HTGeometry/RectangleResidueTheorem` (general-order rectangle residue
theorem, `laurentCoeff`, `principalPart`, the four-edge FTC `rectangleIntegral_eq_zero_of_primitive`,
`rectangleIntegral_inv_pow_eq_zero`) already existed; a duplicate of its first two lemmas was written
here and deleted.  The earlier search only surfaced `PNTPlus/ResidueCalcOnRectangles`, whose residue
theorem is explicitly a *simple-pole stopgap* — searching for the words of the statement
("arbitrary order", "Laurent coefficient") finds the right module.

## Theorem 5.2 — CLOSED (pointwise), 2026-08-23

`RHTower/BurnolResidueSeries.tendsto_residueSum_extendedMellin`, axiom-clean:

```
Tendsto (fun k => ∑ ρ ∈ nontrivialZeroFinset (T k),
    laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1))
  atTop (𝓝 (extendedMellinContinuation a c d f Z))
```

for every `Z` with `ζ(Z) ≠ 0`, `Z ≠ 1`, `Z ≠ 0`, where `T` is the height sequence of Prop. 5.1.
Packaged versions: `exists_seq_tendsto_residueSum_extendedMellin` (one sequence of heights for all
`Z` at once, as in Note 13) and `exists_tendsto_residueSum_of_hasRapidMellin` (hypothesis =
Definition 12).  **The residue at `ρ` is its Laurent coefficient**, so no hypothesis is made on the
multiplicities — this is exactly Burnol's Note 13 convention, and it makes his "symbolic
representation" remark literally true rather than approximate.

New modules, in dependency order:

| Module | Content |
|---|---|
| `RHTower/ZetaTrivialZeroSimple` | **mathlib gap**: `meromorphicOrderAt ζ (-2k) = 1` — every trivial zero is simple.  Via `Γ_ℝ = π^{-s/2}Γ(s/2)`, the corpus's affine Gamma pole lattice at `b = 1/2`, and `ζ = Λ/Γ_ℝ` read on a punctured neighbourhood (`Λ(-2k) = Λ(1+2k) ≠ 0`). |
| `RHTower/BurnolRectangleResidue` | the rectangle residue identity for `burnolIntegrand`; `meromorphicOrderAt_burnolIntegrand = ord G − ord ζ`; the vanishing criterion `laurentCoeff_burnolIntegrand_eq_zero_of_order_ge`. |
| `RHTower/MellinContinuationOrder` | orders of `M(f) = N/(s(1−s))`: meromorphic everywhere, analytic off `{0,1}`, `ord ≥ 1` at every trivial zero, `≥ 0` at `0`, `≥ −1` at `1`.  Hence **`0`, `1` and the trivial zeros contribute no residue** — the paper's remark, proved. |
| `RHTower/MellinReflectionEquation` | `χ(s) = chiFE(1−s)`, `ζ(s) = χ(s)ζ(1−s)` off `ℤ`, `χ ≠ 0` off `ℤ`, and the *definitional* functional equation `N_a(c,d,f)(s) = χ(s)·N_a(d,c,F f)(1−s)`; `burnolEdgeIntegrand` and **the reflection** `edge(f,Z)(s) = −edge(F f, 1−Z)(1−s)`. |
| `RHTower/BurnolEdgeIntegrability` | integrability of the edge integrand on `Re s = σ ≥ 2` (Hardy `L²` × Cauchy kernel, AM–GM majorant) and, through the reflection, on `Re s = 1−σ`; `∫` on the left line `= −∫` on the reflected right line. |
| `RHTower/BurnolRectangleSum` | `nontrivialZeroFinset T`; the rectangle corners; **the residue identity**: rectangle integral `= −M(f)(Z) + ∑_{|Im ρ| < T}`. |
| `RHTower/BurnolContourLimits` | the four edges in the limit: horizontal → `0` (E2 at *both* signs of the height), vertical → the line integrals; the rectangle integral → `(1/2π)ζ(Z)(∫_R − ∫_L)`. |
| `RHTower/BurnolResidueSeries` | conjugate symmetry of the height selection, the `A → ∞` vanishing of both lines, **Theorem 5.2**, and **Corollary 5.3**. |

Two existing modules were generalized in place: `ResidueContourEdges.tendsto_norm_horizontal_edge_zero`
now takes an arbitrary subinterval `[x₁,x₂] ⊆ [-b,b]` and a signed height `ε·T k` (`|ε| = 1`), and
`ZetaInverseWideHorizontal.exists_seq_zeta_inv_horizontal` now also returns
`ζ(σ + iT_k) ≠ 0` for `-1 ≤ σ ≤ 2` (the inverse-norm bound alone does *not* give nonvanishing —
`‖0⁻¹‖ = 0` satisfies it).

**The structural discovery.**  Burnol's `G(1−s)/ζ(1−s) = F₊(G)(s)/ζ(s)`, which he uses to reduce
the left vertical edge to the right one, is *definitional* in the corpus's model: the left half of
`extendedMellinNumerator` is literally `χ(s)` times the right half of the numerator of the
Fourier-transformed datum with the two band constants swapped.  So the whole left edge costs one
`ring` plus the `ζ` functional equation, and — crucially — **Lemma 4.10 (stability of `L₁` under
`F₊`) is not needed for Theorem 5.2**: the reflected datum enters only through the `L²` edge
estimate `tendsto_vertical_edge_zero`, which asks for no rapid decrease at all.

**Cor 5.3** is formalized as: if `M(f)` vanishes at every nontrivial zero to at least the order of
`ζ` (`ζ ∣ M(f)`, i.e. `f ⊥` all the evaluators `ζ(s)/(s−ρ)^l`), then `M(f) ≡ 0` off `{0,1}`.

Still open in §5: the `L²`-in-`Z` convergence on the critical line (Thm 5.2's second half), the
absolute convergence in Note 13's grouped sense, **Prop 5.4** (`Σ G(ρ)/ζ'(ρ) = 0`, which needs
Mellin inversion on the critical line, `Res₁(G) = −c` and the `μ`-Dirichlet series), and Rem 15.

## §6 — Proposition 6.1 for `a > 1`, without Krein (2026-08-23)

`RHTower/BurnolCompletenessLarge.eq_zero_of_zeta_dvd_extendedMellin`, axiom-clean: a vector of
`L_b` with `b > 1` whose continued Mellin transform is divisible by `ζ` at every nontrivial zero
(i.e. which is orthogonal to every evaluator `Y^b_{ρ,k}`) is zero.

**The route avoids Krein's theorem entirely.**  The smoothing of Theorem 4.9 acts on the Mellin side
as multiplication by the *entire* multiplier `logSmoothMultiplier k (s−1/2)`
(`SoninMellinMultiplier.extendedMellinContinuation_dilationAverage`, extracted from the proof of
`hasRapidMellin_dilationAverage`), so it *preserves* the vanishing order at each zero.  Every
smoothed vector therefore lies in the dense subspace of Definition 12 and is still orthogonal to all
the evaluators, so Corollary 5.3 kills its Mellin transform, and the new injectivity theorem kills
the vector; letting the smoothing width tend to `0` gives the original vector.

`RHTower/SoninMellinInjective.eq_zero_of_extendedMellinContinuation_eq_zero` — **the continued
Mellin transform is injective on `L_a`** — is new and elementary:
* the head `d·a^{1−s}/(1−s)` would give the Laplace transform of the tail datum a pole at `w = 1/2`,
  and the `L²` mass of `1/(1/2−w)` on `Re w = σ` blows up like `1/(2(1/2−σ))` while the mass of a
  genuine Laplace transform stays `≤ ‖φ‖²` — hence `d = 0`;
* then the Laplace transform vanishes on a whole line and Plancherel
  (`HalfLineLaplaceFourier.integral_norm_sq_laplaceRay_line`) kills the datum;
* the band constant and evenness finish the two remaining pieces of the line.

**Why `a = 1` is different** (recorded so it is not re-attempted): every dilation lowers the
aperture (`min(a/r, ar) ≤ a`), so *no* smoothing of an `L_1` vector stays in `L_1`, and the argument
above has no room.  That is exactly the place where Burnol invokes Krein's theorem (an entire
function of bounded characteristic in two complementary half-planes has finite exponential type) —
which mathlib and this corpus do not own; the "Nevanlinna" modules in `HTGeometry` are about the
moment problem, not the class of bounded characteristic.

## Lemma 4.10 — CLOSED (2026-08-23)

`RHTower/BurnolReflectionStability`, axiom-clean:

* `burnolChiFactor_mul_one_sub` — the cocycle `χ(s)χ(1−s) = 1` off the real axis (from the corpus's
  `zetaChi_mul_one_sub` and `gammaR_ne_zero_of_im_ne`);
* `extendedMellinContinuation_reflect_of_im_ne` — `M(F₊f)(w) = χ(w)·M(f)(1−w)` for **every** `w` off
  the real axis: definitional left of the critical line, the cocycle right of it, and continuity on
  the line itself (approach `w` along `w − 1/n`);
* `hasStripRapidDecrease_reflect` — **Lemma 4.10**, and `hasRapidMellin_fourierUnitary`: Definition
  12's class is stable under `F₊`.  The only analytic input is the corpus's
  `hasStripPolyGrowthOffReal_zetaChi` (polynomial vertical growth of `χ` on every strip above height
  two), which is exactly Titchmarsh IV.12.3 as cited by Burnol.

With this, **§4 of the paper is complete**: Prop. 4.1–4.7, Def. 10, Thm 4.8, Def. 12, Thm 4.9,
Lem. 4.10.

## Proposition 5.4 — CLOSED (2026-08-23)

`RHTower/BurnolPropFiveFour.exists_seq_tendsto_residueSum_quotient`, axiom-clean:

```
Tendsto (fun n => ∑ ρ ∈ nontrivialZeroFinset (T n),
    laurentCoeff (burnolQuotient (extendedMellinContinuation a c d f)) ρ (-1)) atTop (𝓝 0)
```

i.e. Burnol's `0 = Σ_ρ G(ρ)/ζ'(ρ)`, again with the residue *defined* as the Laurent coefficient.

The chain, in dependency order:

| Module | Content |
|---|---|
| `RHTower/SoninMellinInversion` | `MellinConvergent` on `0 < σ < 1/2` (band + Cauchy--Schwarz tail), `VerticalIntegrable` from Definition 12, the chart identity `mellin f w = M(f)(1−w)`, and — via mathlib's `mellinInv_mellin_eq` — **the inverse transform equals the band constant on the closed band**, the endpoint by continuity of `mellinInv` (dominated convergence). |
| `RHTower/BurnolPowerLineIntegral` | `(1/2π)∫ M(f)(σ+iτ)k^{-(σ+iτ)}dτ = d/k` for `1/2 < σ < 1`: the line integral *is* the inverse Mellin transform at `1/k`, after `y ↦ −y` and `(1/k)^z = k^{-z}`. |
| `RHTower/BurnolPowerLineShift` | the rectangle `[σ,2]×[−T,T]` for `M(f)(s)k^{-s}`: one simple pole at `s = 1` with residue `−d/k` (because `N(1) = d`), horizontal sides killed by quick decrease, hence **the `Re s = 2` integral vanishes**.  Also the reusable `integrable_line_of_stripRapidDecrease`. |
| `RHTower/BurnolMoebiusLine` | `1/ζ = Σ μ(k)k^{-s}` on `Re s = 2` (mathlib's `LSeries_zeta_mul_Lseries_moebius`) and the term-by-term integration (`integral_tsum_of_summable_integral_norm`, majorant `k^{-2}·∫‖M‖`): **`∫_{Re s = 2} M/ζ = 0`**. |
| `RHTower/BurnolQuotientContour` | the integrand `M/ζ`, its order (`ord M − ord ζ`), the rectangle `[−1,2]×[−T,T]` — which meets **no trivial zero at all** — and the horizontal-edge estimate without the Cauchy factor. |
| `RHTower/BurnolPropFiveFour` | the reflection `M(s)/ζ(s) = M(F₊f)(1−s)/ζ(1−s)` on `Re s = −1` (**this is where Lemma 4.10 is needed**), integrability on both lines, and the assembly. |

With this, **§5 is complete** except for the `L²`-in-`Z` half of Theorem 5.2.  Remark 15 is a
citation of Ramanujan's formula, not a claim proved in the paper.

## Proposition 6.2 for `a > 1` — CLOSED (2026-08-23), again without Krein

`RHTower/BurnolCompletenessOmit.eq_zero_of_zeta_dvd_off_finite`, axiom-clean: a vector of `L_b`
(`b > 1`) whose continued Mellin transform is divisible by `ζ` at every nontrivial zero **outside an
arbitrary finite set `R`** is zero.  So the evaluators stay complete after omitting arbitrarily
finitely many — Burnol's Proposition 6.2, and with it the "not minimal" half of the `a > 1` picture.

Where Burnol invokes Krein's theorem (an entire function of bounded characteristic in two
half-planes has finite exponential type, and its type is `log A < 0`, so it vanishes), the route
here is elementary:

1. `BurnolResidueShape` — the residue of Burnol's integrand at `ρ` is `ζ(Z)` times the **principal
   part of `M(f)/ζ` at `ρ`, evaluated at `Z`** (this is Burnol's own parenthetical remark in
   Theorem 5.2, now a theorem).  It rests on the new `HTGeometry/CauchyKernelResidue`:
   `Res_{s=ρ} H(s)/(Z−s) = (principal part of H at ρ)(Z)`.
2. `BurnolFiniteExceptional` — with only finitely many exceptional zeros, Theorem 5.2's series is
   eventually a *fixed finite sum*, so `M(f)(Z) = ζ(Z)·(sum of principal parts)(Z)`: the transform
   is `ζ` times a **rational** function.
3. `HTGeometry/PrincipalPartPolynomial` — clearing denominators turns that rational function into a
   genuine `Polynomial ℂ`; a polynomial whose values along the real axis tend to `0` is `0`.
4. `RHTower/MellinRealDecay` — `‖M(g)(σ)‖ ≤ C·b^{-σ}` for `σ ≥ 2` (head plus Cauchy--Schwarz tail),
   and `RHTower/MultiplierRealBound` — the smoothing multiplier costs at most `e^{Rσ}`, so choosing
   the smoothing width `R < log b` keeps the decay: base `e^R/b < 1`.
5. `HTGeometry/PolyTimesGeometricDecay` — `(σ+M)^N A^σ → 0` for `A < 1`.

**This is the reason the `a = 1` case is genuinely different**: there the aperture decay base is
`1`, so step 4 gives nothing, and no amount of contour work replaces Krein.

## §6 further — Prop 6.6 and the second half of Prop 6.4 (2026-08-23)

* `RHTower/BurnolSonineCompleteness` — `K_a ⊆ L_a` restricts Props 6.1/6.2 to the Sonine space, so
  for `a > 1` the evaluators span `K_a`, and still do after omitting finitely many: **Proposition
  6.6** (`eq_zero_of_zeta_dvd_off_finite_soninCarrier`).
* `RHTower/SoninModelBridge` — the two models of `L_a` agree: an *even* vector with constant head on
  `(0,a)` for itself and its cosine transform lies in `centralSoninExtendedCarrier a`.  This is what
  lets the co-Poisson machinery (stated in `soninExtendedSpace`) feed the residue machinery (stated
  in `centralSoninExtendedCarrier`).
* `RHTower/BurnolCoPoissonNotComplete.exists_nonzero_zeta_dvd_of_aperture_lt_one` — **Proposition
  6.4, second half**: for `0 < a < 1` the explicit co-Poisson vector is nonzero, lies in `L_a`, and
  its continued Mellin transform is `(a^{-w} − a^{w})·ζ(w)/w`, hence divisible by `ζ` at every
  nontrivial zero.  So the evaluators are **not** complete below aperture one.

Together with Prop 6.1/6.2 this pins the threshold: complete for `a > 1`, not complete for `a < 1`.
The value `a = 1` itself remains gated on Krein's theorem.

**Name-collision note.**  `ofReal_inv_cpow` already existed in `RHTower/ArchimedeanMellinFourier`;
the copy introduced here was renamed `ofReal_one_div_cpow_eq_neg`.  `lean_dupcheck.py` did not catch
it because the two modules were not in each other's import closure at the time — a global grep over
the theorem area is the reliable check.

## Proposition 6.1 at the critical aperture `a = 1` — CLOSED (2026-08-23), Krein eliminated

`RHTower/BurnolCompletenessUnit.eq_zero_of_zeta_dvd_extendedMellin_one_le`, axiom-clean:

> for **every** `b ≥ 1`, a vector of `L_b` whose continued Mellin transform is divisible by `ζ` at
> every nontrivial zero is `0`.

This closes the last gate of §6's completeness half, and with it the completeness half of
Theorem 6.3.  Burnol's Krein input ("an entire function of bounded characteristic in two
complementary half-planes has finite exponential type") is **not used**.  The replacement is a
Phragmén–Lindelöf-free rectangle argument:

| step | module | content |
|---|---|---|
| 1 | `RHTower/MellinHalfPlaneBound` | `‖M(g)(s)‖ ≤ C·b^{-Re s}` on `Re s ≥ 2`; at `b = 1` this is *boundedness*, which is all that is needed. |
| 2 | `RHTower/BurnolQuotientGrowth.exists_bound_burnolQuotientNF_right` | `θ = M/ζ` is bounded on `Re s ≥ 2` (step 1 plus `‖1/ζ‖ ≤ 4`). |
| 3 | `…exists_bound_burnolQuotientNF_left` | `θ` is bounded on `Re s ≤ −1`: off the real axis by the functional equation `θ(s) = θ_{F₊g}(1−s)` (`burnolQuotient_reflect_of_im_ne`), on the axis by continuity along `s + i/(n+1)`. |
| 4 | `…exists_bound_burnolQuotientNF_horizontal` | `‖θ‖ ≤ C(1+T_k)^D` on the selected heights `Im s = ±T_k`, `−1 ≤ Re s ≤ 2`: Theorem 4.8's L-property for `M` times Proposition 5.1 for `1/ζ`. |
| 5 | `HTGeometry/RectangleMaxModulus.norm_le_of_mem_rectangle` | maximum modulus on `[−1,2]×[−T_k,T_k]`; `exists_height_between` supplies a selected height just above `|Im z|` (this is why `ZetaInverseWideHorizontal` was strengthened with `T(k+1) ≤ T k + 3`). |
| 6 | `…exists_polyGrowth_burnolQuotientNF` | hence `‖θ(z)‖ ≤ M(‖z‖+1)^D` on all of `ℂ`. |
| 7 | `RHTower/EntireAutomorphism.exists_polynomial_of_polyGrowth` | `θ` **is** a polynomial. |
| 8 | `RHTower/MellinRealVanishing` | `M(g)(σ) → 0` as `σ → +∞` for every aperture `b ≥ 1` — the tail is paired by Cauchy–Schwarz against *itself*, giving `‖g‖/√(2σ−1)` instead of the lossy `b^{1-σ}·b^{-1/2}‖g‖`; the head is `‖d‖/(σ−1)`. |
| 9 | `HTGeometry/PrincipalPartPolynomial.polynomial_eq_zero_of_tendsto_zero` | a polynomial vanishing at `+∞` along `ℝ` is `0`, so `θ ≡ 0`, so `M ≡ 0`, so `g = 0`. |

Two supporting bridges landed with it:

* `meromorphicOrderAt_riemannZeta_le_extendedMellin` — divisibility at the *nontrivial* zeros
  upgrades to divisibility at **every** point: at a trivial zero because `χ` vanishes there
  (`MellinTrivialZeros`), at `s = 1` because `M` has at worst a simple pole, at `s = 0` because the
  numerator vanishes.
* `zero_le_meromorphicOrderAt_burnolQuotient_extendedMellin` — hence `M/ζ` has nonnegative order
  everywhere, which is exactly the hypothesis of `differentiable_burnolQuotientNF`.

Note that Proposition 6.2 genuinely **cannot** be extended to `a = 1` by this route: multiplying
`θ` by `∏(s−ρ)^{m_ρ}` costs a polynomial factor, while step 8 only gives `σ^{-1/2}` — consistent
with Theorem 6.3, which asserts that at `a = 1` the system *is* minimal.

## LAYER H — the two-sided Hardy gateway (needed for every *minimality* statement)

Every remaining minimality item (Thm 6.3's second half, Prop 6.4's first half, Prop 6.5, Thm 6.7,
and §7's Thms 7.1–7.3) needs one and the same missing brick: **realise a prescribed element of
`L̂_a` as an actual vector of `L_a`** — the two-sided converse of Proposition 4.1.  Completeness
never needed it (it is phrased as "the jets vanish ⟹ the vector is 0"), minimality does.

Why a *witness* is unavoidable: minimality at `(ρ,k)` asks for `h ∈ L_1` whose continued Mellin
transform vanishes to order `m_{ρ'}` at every other nontrivial zero and to order exactly `k` at `ρ`,
i.e. `M(h) = ζ(s)/(s−ρ)^{m_ρ−k}`.  Proposition 4.2 (`ZetaMellinHeadHardy.isMellinHeadHardy_zetaQuotient`,
already owned) says that function is in the *head* Hardy class; its reflection
`χ(s)·ζ(1−s)/(1−s−ρ)^l = (−1)^l ζ(s)/(s−(1−ρ))^l` is again of the same shape, so Proposition 4.2 at
`1−ρ` supplies the second half.  What is missing is the passage back to a vector.

### H1 — CLOSED (2026-08-23): `HTGeometry/TwoSidedLaplaceVanishing.eq_zero_of_two_sided_laplace`

> Let `ψ₁, ψ₂ ∈ L²(0,∞)` and let `G` be **continuous** on a strip `|Re w| < r` with
> `G w = 𝓛(ψ₁)(w)` for `0 < Re w < r` and `G w = 𝓛(ψ₂)(−w)` for `−r < Re w < 0`.  Then `ψ₁ = ψ₂ = 0`.

This is the elementary replacement for "an entire function of bounded characteristic in two
complementary half-planes"; it says the two half-plane Hardy spaces meet only in `0`, and it needs
no analyticity at all — only continuity across the axis.  Proof: on `Re w = σ > 0` the Laplace
transform is the Fourier transform of the damped datum `1_{x>0}ψ₁(x)e^{-σx}`
(corpus `HalfLineLaplaceFourier.fourierIntegral_rayDamp`); the damped datum converges in `L²` to
`1_{x>0}ψ₁` as `σ ↓ 0`, so along a subsequence the `L²` Fourier transforms converge a.e., while the
values `G(σ_n + 2πiξ)` converge to `G(2πiξ)` by continuity.  Hence `𝓕(1_{x>0}ψ₁)` is the restriction
of `G` to the axis.  The same computation on the left, run on the *reflected* damped datum
`x ↦ 1_{x<0}ψ₂(−x)e^{σx}` (new `rayDampRefl`, with `fourierIntegral_rayDampRefl`), gives
`𝓕(1_{x<0}ψ₂(−·))` = the same restriction.  Fourier injectivity then identifies two data with
disjoint supports.

New reusable lemmas in that module: `rayDampRefl`, `memLp_two_rayDampRefl`,
`integrable_rayDampRefl`, `fourierIntegral_rayDampRefl`, `coeFn_fourierTransform_toLp`,
`tendsto_integral_norm_sq_rayDamp_sub`, `tendsto_toLp_of_integral_norm_sq`, `tendsto_toLp_rayDamp`,
`tendsto_toLp_rayDampRefl`.

### H2 — TODO: the Mellin instance

With `u := F₊v`, `Tail(s) := extendedTailMellin a c₁ u s` (analytic on `Re s > 0`) and
`Head(s) := ∫_{(0,a)} t^{-s}u` (analytic on `Re s < 1/2`), Burnol's functional equation
(`SoninExtendedFunctionalEquation.extendedFullMellin_functional_equation`, whose only hypotheses are
evenness and *one* constant head) gives `Tail + Head = χ(s)F(1−s)` on `0 < Re s < 1/2`, while the
second Hardy hypothesis gives `χ(s)F(1−s) = c₂a^{1-s}/(1−s) + ∫_{(a,∞)}t^{-s}g₂` on `1/2 < Re s < 1`.
Set `w := s − 1/2` and

  `G(w) := a^{w-1/2}·(χ(1/2+w)F(1/2−w) − Tail(1/2+w)) − c₂/(1/2−w)`.

Then `G = 𝓛(ψ₁)` on the right with `ψ₁(x) = e^{-x/2}(g₂−u)(ae^{x})`, and `G = 𝓛(ψ₂)(−w)` on the left
with `ψ₂(x) = e^{-x/2}u(ae^{-x}) − c₂e^{-x/2}`.  H1 kills both: `u = c₂` a.e. on `(0,a)` — the head
constancy that puts `v` in `L_a` — and `u = g₂` a.e. on `(a,∞)` as a bonus.

### H3 — TODO: Proposition 4.1, two-sided converse, and the `ζ(s)/(s−ρ)^l` witnesses.
### H4 — TODO: Theorem 6.3 minimality, then Props 6.4/6.5 and Theorem 6.7.

### H2/H3/H4 — CLOSED (2026-08-23): Theorem 6.3 and Proposition 6.4 in full

| brick | module | statement |
|---|---|---|
| H2 | `RHTower/MellinHeadChart` | `logChartHead`, `mellinHead_eq_laplaceRay`: the head `(0,a)` Mellin transform is `a^{1/2−s}·𝓛(√a e^{-x/2}f(ae^{-x}))(1/2−s)` — a Laplace transform on the *opposite* half-plane from the tail chart. |
| H2 | `RHTower/MellinTwoSidedGlue.ae_eq_of_two_sided_mellin` | one continuous `Ψ` on `0 < Re s < 1` equal to the head transform of `u` on the left and to `c·a^{1−s}/(1−s) + ` tail of `g−u` on the right forces `u = c` on `(0,a)` and `u = g` on `(a,∞)`. |
| H3 | `RHTower/HeadTailVector` | the even vector attached to a head constant and an `L²` tail, and its Mellin transform. |
| H3 | `RHTower/SoninFromHardyData.headTailVector_mem_centralSoninExtendedCarrier` | **Proposition 4.1, two-sided converse**: `F ∈ L̂_a` and `χ(s)F(1−s) ∈ L̂_a` ⟹ the head/tail vector lies in `L_a`, with the reflected head constant as its cosine-transform aperture constant. |
| H4 | `RHTower/ZetaZeroOrderReflection` | `analyticOrderAt ζ (1−ρ) = analyticOrderAt ζ ρ` in the strip (via the corpus's `xi_orderAt_one_sub` and `xi_analyticOrderAt_eq_riemannZeta_of_mem_strip`). |
| H4 | `RHTower/ZetaDivPowRepresentative` | `zetaDivPowNF ρ l` — the meromorphic-normal-form representative of `ζ(s)/(s−ρ)^l`, analytic off `s = 1` once `l ≤ m_ρ`. |
| H4 | `RHTower/HeadTailMellinAnalytic` | `headTailMellin` is holomorphic on `Re s > 1/2`, `s ≠ 1`; plus "two functions continuous at a point and equal off it are equal at it". |
| H4 | `RHTower/ZetaDivPowHeadTail` | head/tail descriptions of `zetaDivPowNF ρ l` **and** of its reflection `χ(s)·(·)(1−s) = (−1)^l zetaDivPowNF (1−ρ) l`. |
| H4 | `RHTower/BurnolMinimalWitness.exists_extendedSonin_zetaDivPow` | the vector of `L₁` whose continued Mellin transform is `ζ(s)/(s−ρ)^l` on the whole open strip. |
| H4 | `RHTower/BurnolMinimalitySystem.exists_minimality_witness` | **Theorem 6.3, minimality half**: for `k < m_ρ` a vector of `L₁` whose transform has order `m_{ρ'}` at every other nontrivial zero and order **exactly `k`** at `ρ`. |
| H4 | `RHTower/MellinApertureIndependence` | the continued transform does not depend on the aperture (same band constants), on the whole open strip. |
| H4 | `RHTower/BurnolMinimalityAperture.exists_minimality_witness_aperture` | **Proposition 6.4, minimality half**: the same witness works at every aperture `a ≤ 1`. |

With these:

* **Theorem 6.3 is closed** — completeness at `a = 1` from `eq_zero_of_zeta_dvd_extendedMellin_one_le`,
  minimality from `exists_minimality_witness`.
* **Proposition 6.4 is closed** — minimality from `exists_minimality_witness_aperture`, non-completeness
  from `exists_nonzero_zeta_dvd_of_aperture_lt_one`.

Still open in §6: Proposition 6.5 (the shortened `Z¹` system) and Theorem 6.7 (`Z^a` minimal for
`a < 1`); in §5, the `L²`-in-`Z` half of Theorem 5.2; and all of §7.

**Method note.** `analyticOrderAt_comp_one_sub` and `xi_orderAt_one_sub` were rebuilt by accident and
then discarded — `RHTower/Reflection` already owned both.  Run
`scripts/formal_tools.py research "<query>"` before every new brick.

## Theorem 3.1, Proposition 4.3 at every strip point, and Lemma 7.4 — CLOSED (2026-08-23)

* `RHTower/BurnolTheoremThreeOne.burnol_theorem_three_one` — **Theorem 3.1** as one statement:
  complete for `a ≥ 1`, not complete for `a < 1`, minimal for `a ≤ 1`, not minimal for `a > 1`.
  The predicates `IsExtendedSonineDatum` and `AnnihilatesEvaluators` package the jet dictionary
  ("`v ⊥ Y^a_{ρ,k}` for all `k < m_ρ`" = "`ζ` divides `M(v)` at `ρ`").
* `RHTower/MellinApertureIndependence` — the continued transform is aperture-independent
  (`extendedMellinContinuation_eq_soninMellinIntegral` on the convergence strip, then the identity
  theorem); this is what carries the `a = 1` minimality witness down to every `a ≤ 1`.
* `RHTower/ExtendedSoninDivision.exists_divided_extendedSonin` — **Proposition 4.3 for `L_a` at
  *every* point of the open critical strip**, the critical line included.  The corpus previously
  owned it only for `1/2 < Re ρ < 1` (`BurnolSoninDividedShift`), which cannot reach the zeros.
  The new ingredient is the **canonical Hardy representative**
  `soninHardyRep a c d v w = -a^w·N(w+1/2)/(w+1/2)^2` (`RHTower/SoninHardyRepresentative`):
  substituting `M(v) = N/(s(1−s))` into `((w−1/2)/(w+1/2))a^w M(v)(w+1/2)` collapses the whole
  expression to something visibly analytic on `w ≠ −1/2`, hence analytic at `ρ − 1/2` for *every*
  strip `ρ`.  It agrees with any `IsMellinHeadHardy` witness on `Re w > 0` (they are continuous and
  agree off `w = 1/2`), so it is itself Hardy, and `exists_isHalfPlaneHardy_div_pow` then divides it
  at a boundary point.  Both sides of the functional equation are divided — at `ρ` and at `1−ρ` —
  and `SoninFromHardyData` reassembles the vector.
* `RHTower/DivShiftRepresentative` — the generic normal-form representative `divShiftNF G ρ`.
* `RHTower/ExtendedMellinHeadHardy` — `IsMellinHeadHardy a (M v)` for every vector of `L_a`, and
  `χ(s)M(v)(1−s) = M(F₊v)(s)` on the whole strip `0 < Re s < 1` (the real points filled in by
  approaching along `s + i/(n+1)`).
* `RHTower/ExtendedSoninOrderDrop` — one division lowers the order at `ρ` by exactly one and
  preserves every other order (`exists_order_drop`); iterating gives
  `exists_order_eq_of_add`, which is **Burnol's Lemma 7.4** in jet form: from one vector vanishing
  to order `k + j` at `ρ` one manufactures a vector vanishing to order *exactly* `k` at `ρ` with all
  the other orders unchanged.  This is the "not complete ⟹ minimal" mechanism, and it is what
  gives `a₂(Z) ≤ a₁(Z)` in Theorem 7.1.

Remaining: Proposition 6.5, Theorem 6.7, the `L²`-in-`Z` half of Theorem 5.2, Lemmas 7.5/7.6 and
Theorems 7.1–7.3 (the abstract index bookkeeping plus the smoothing argument), Theorems 7.7–7.10
(Levin), and the capstones 3.2/3.3.

## §7 Lemmas 7.4–7.6 and Theorems 7.1–7.3 — CLOSED (2026-08-23)

The whole first half of §7 is Lean-closed, in the jet dictionary
(`IsCompleteEvaluatorSystem`, `IsMinimalEvaluatorSystem` in `RHTower/BurnolEvaluatorSystemZ`).

| item | module / name |
|---|---|
| **Lemma 7.4** (not complete ⟹ minimal) | `BurnolEvaluatorSystemZ.isMinimal_of_not_isComplete` |
| **Lemma 7.5** (minimal at `a` ⟹ not complete below `a`) | `BurnolLemmaSevenFive.exists_nonzero_annihilating_of_lt` |
| **Theorem 7.1** (`a₁(Z) = a₂(Z)`) | `BurnolTheoremSevenOne.burnol_theorem_seven_one` |
| **Lemma 7.6** (iterate along a finite list) | `BurnolTheoremSevenTwoThree.exists_nonzero_annihilating_list` |
| **Theorem 7.2** (add finitely many) | `BurnolTheoremSevenTwoThree.not_isComplete_add_of_lt` |
| **Theorem 7.3** (omit finitely many) | `BurnolTheoremSevenTwoThree.isComplete_omit_of_lt` |

**The dilation replaces Burnol's bump.**  Burnol multiplies a Sonine transform by the Mellin
transform `θ(s)` of a smooth bump supported near `1`, then by `(s−ρ)` to force `θ(ρ)=0`.  Here the
same effect comes from a single dilation: `rayDilate v f (t) = √v f(vt)` has Mellin transform
`v^{s-1/2}·M(f)(s)` (`SoninDilationMellin.soninMellinIntegral_rayDilate`), so

  `U_r v − r^{ρ-1/2} v`   has transform   `(r^{s-1/2} − r^{ρ-1/2})·M(v)(s)`,

an entire multiplier vanishing at `ρ` and not identically zero (`dilationDifferenceMultiplier`);
and dilating by `r > 1` carries `L_a` into `L_{a/r}`.  Taking `r = a/b` lands exactly in `L_b`.
`BurnolLemmaSevenFive.exists_dilationShift` is this step in isolation; Lemma 7.6 iterates it along a
list of points, halving the remaining aperture gap at each step, so the multiplier becomes the
*product* of the dilation-difference factors — Burnol's `P(s)θ(s)`.

Theorem 7.1's content in this form: completeness is an up-set in the aperture
(`isComplete_of_lt`), minimality is a down-set (`isMinimal_of_lt`), and the two cover every positive
aperture (Lemma 7.4) — i.e. the two thresholds coincide.

Remaining: Proposition 6.5, Theorem 6.7, the `L²`-in-`Z` half of Theorem 5.2, Theorems 7.7–7.10
(Levin's completely-regular-growth theory), and the capstones 3.2/3.3.

## Theorem 6.7 and Theorem 3.2 — CLOSED (2026-08-23); the `L → K` bridge

`RHTower/SoninCarrierFromExtended.exists_soninCarrier_of_extended`: **two dilation shifts carry any
vector of `L_a` to a vector of `K_b` (`b < a`) with exactly the same Mellin orders on the open
critical strip.**

The shift `soninShift r lam v = U_r v − λ v` multiplies the two aperture constants by explicit
scalars: the physical one by `√r − λ` and the cosine one by `1/√r − λ`
(`soninShift_ae_phys`, `soninShift_ae_fourier`, from the corpus's `ae_const_dilation` and
`fourierUnitary_dilation`).  Taking `λ = √r` kills the physical constant, and a second shift with
`λ = 1/√r` kills the cosine one while — by linearity — leaving the physical one `0`.  Both Mellin
multipliers `r^{s-1/2} − √r` and `r^{s-1/2} − 1/√r` have all their zeros on `Re s = 1` and
`Re s = 0` respectively, i.e. **outside the open critical strip**, so no order in the strip moves.
With `r = √(a/b)` the two shifts land exactly at aperture `b`.
`mem_centralSoninCarrier_of_ae_zero` (both constants zero ⟺ Sonine) closes the loop.

Consequences:

* `RHTower/BurnolSonineMinimality.exists_soninCarrier_minimality_witness` — **Theorem 6.7**: for
  `a < 1` the evaluators are minimal in `K_a`.
* `…exists_nonzero_soninCarrier_zeta_dvd` — the `K_a` half of Proposition 6.4: not complete for `a < 1`.
* `RHTower/BurnolTheoremThreeTwo.burnol_theorem_three_two` — **Theorem 3.2** (all parts except the
  `a = 1` "omit two" statement, which is Proposition 6.5): complete for `a ≥ 1`, complete after
  arbitrary finite omission for `a > 1` (hence not minimal), not complete and minimal for `a < 1`.

Remaining: Proposition 6.5 (the `a = 1` shortened `Z¹` system), the `L²`-in-`Z` half of Theorem 5.2,
Theorems 7.7–7.10 (Levin), and capstone 3.3's minimality half.

## The evaluator layer — started (2026-08-23): `RHTower/SoninStripEvaluator`

Burnol's evaluators are the Riesz vectors of `f ↦ M(f)^{(k)}(w)` on `L_a`.  Everything so far has
been phrased in the *jet* dictionary precisely because those vectors were missing; they are what
Theorem 3.3's minimality half (and the abstract `IsMinimalSystem`/`IsCompleteSystem` restatements)
still need.

**The plan that makes them cheap.**  The head/tail estimate bounds `|M(f)(w)|` by `C(w)‖f‖` with
`C(w) ∼ (2 Re w − 1)^{-1/2}` — fine for `Re w > 1/2`, useless on the critical line, which is exactly
where the zeros sit.  Instead of the circle-average argument (which needs the integrability of
`|cos θ|^{-1/2}`), use **Banach–Steinhaus**: `L_a` is a closed subspace of `L²`, hence complete; the
functionals `Λ_{w+1/n}` are bounded; and `Λ_{w+1/n} f = M(f)(w + 1/n) → M(f)(w)` for every fixed `f`
because `M(f)` is analytic.  `continuousLinearMapOfTendsto` then hands over boundedness of the limit
functional for free.  Left of the line, `Λ_w = χ(1−w)^{-1}·Λ_{1−w} ∘ F₊` by
`chi_mul_extendedMellinContinuation_one_sub`.  Jets follow by the same trick from difference
quotients.

Landed so far (all axiom-clean):

* `soninEvenExtended a` — the even part of `L_a` as a submodule, with `isClosed_soninEvenExtended`
  and the `CompleteSpace` instance (the Banach–Steinhaus prerequisite);
* `soninBandConst a f` — the band average, `= d` on `L_a` (`soninBandConst_eq`), with
  `norm_soninBandConst_le`;
* `norm_tail_cpow_le` — the complex-exponent tail Cauchy–Schwarz bound
  `‖∫_b^∞ t^{-w}g‖ ≤ (b^{1−2Re w}/(2Re w−1))^{1/2}‖g‖` for `Re w > 1/2`;
* `soninMellinIntegral_split`, `norm_soninMellinIntegral_le` — the head/tail split and the explicit
  bound `|M(f)(w)| ≤ C(a,w)·‖f‖` on `1/2 < Re w < 1`.

### The evaluator layer is CLOSED (2026-08-23)

* `soninEval a f w` — the continued Mellin transform of `f ∈ L_a` with the aperture constants read
  off the vector itself (`soninBandConst`, `soninFourierBandConst`), analytic on the open strip.
* `soninEvaluatorRight` — the bounded functional for `1/2 < Re w < 1`, from the explicit head/tail
  bound `norm_soninMellinIntegral_le`.
* `exists_soninEvaluator_mid` — **the critical line**, by Banach–Steinhaus: the functionals at
  `w + δ/(n+2)` are bounded and converge pointwise (analyticity of `soninEval a f`), so
  `continuousLinearMapOfTendsto` hands over boundedness of the limit.  This is where the
  `(2 Re w − 1)^{-1/2}` estimate dies and where the corpus had stopped.
* `soninEval_reflect`, `soninFourierCLM`, `exists_soninEvaluator` — the left half by the functional
  equation `χ(1−w)·M(f)(w) = M(F₊f)(1−w)`, so the evaluator is bounded at **every** point of the
  open critical strip.  This is Burnol's Theorem 2.1 continuity statement in the extended space.
* `analyticOnNhd_iteratedDeriv_soninEval`, `exists_soninEvaluatorJet` — **all jet orders**, by the
  same Banach–Steinhaus trick applied to the difference quotients of the previous jet.

Next: the biorthogonal dual family.  The right functional for Theorem 3.3 is not the bare jet but
the Laurent coefficient of `M(f)/ζ` at `ρ`: writing `ζ(s) = (s−ρ)^m u(s)`, the coefficient of
`(s−ρ)^{-l}` is the `(m−l)`-th Taylor coefficient of `M(f)·h` with `h = (s−ρ)^m/ζ`, a *finite*
combination of the jet functionals — and on the witnesses `M(v_{ρ,l'})·h = (s−ρ)^{m−l'}` exactly, so
the pairing is `δ_{l,l'}` on the nose.

## Session log — Theorem 3.3, minimality half CLOSED

New modules (all built, wired, dupcheck-clean, `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

* `HTGeometry/ShiftedMonomialJet.lean`
  - `iterate_deriv_const_mul_sub_pow` — `deriv^[k] (c·(s−ρ)^n) = c·(n descFactorial k)·(s−ρ)^{n−k}`.
  - `iteratedDeriv_sub_const_pow` — the jets of `(s−ρ)^n` at `ρ`: `n!` at `k = n`, else `0`.
  - `iteratedDeriv_eq_zero_of_eventuallyEq_sub_pow_mul` — flat factor of order `m` kills jets below `m`
    (centred at an arbitrary `ρ`, unlike the corpus versions which sit at `0`).
* `RHTower/SoninStripEvaluator.lean` (appended)
  - `analyticOnNhd_iteratedDeriv_mul`
  - `exists_soninEvaluatorJetMul` — for any multiplier `h` analytic on an open `U ⊆` strip, the map
    `f ↦ (M(f)·h)^{(k)}(w)` is a bounded functional at every `w ∈ U`.  Same Banach–Steinhaus
    induction as `exists_soninEvaluatorJet`, with the multiplier carried through.
* `RHTower/BurnolBiorthogonalJet.lean`
  - `eventuallyEq_of_eventuallyEq_punctured`
  - `exists_zetaLocalUnit` — on a neighbourhood of a zero `ρ` of order `m` inside the strip there is
    an analytic `h` with `ζ·h = (s−ρ)^m` (take `h = 1/g` from the factorisation of `ζ`).
  - `exists_zetaJetFunctional` — **the biorthogonal functional**: `Λ f = ((m−l)!)⁻¹·(M(f)·h)^{(m−l)}(ρ)`
    returns `1` on the vector with transform `ζ/(s−ρ)^l` and `0` on every other `ζ/(s−ρ')^{l'}`.
    Same zero: the germ is exactly the monomial `(s−ρ)^{m−l'}`, so the jet is `(m−l)!·δ_{l,l'}`.
    Other zero: the germ carries the flat factor `(s−ρ)^m` and `m−l < m`.
* `RHTower/BurnolTheoremThreeThree.lean`
  - `isMinimalSystem_of_exists_functional` — separating bounded functionals give minimality.
  - `IsZetaQuotientSystem`, `IsZetaQuotientSystem.isMinimalSystem`, `exists_zetaQuotientSystem`
  - `burnol_theorem_three_three_minimal` — **Theorem 3.3, minimality half.**

The functional is literally Burnol's "triangular linear combination of the evaluators `Y_{ρ,k}`,
`0 ≤ k < m_ρ`": the Taylor coefficients of the local unit `h` supply the triangular coefficients.

### Remaining
1. Theorem 5.2's `L²`-in-`Z` half → Corollary 5.3 → Theorem 3.3's completeness half.
2. Proposition 6.5 (a = 1, omit two top-order evaluators).  Route settled:
   `θ = (M f/ζ)·(s−ρ₁)(s−ρ₂)/(s(s−1))` is entire once `order(M f/ζ) ≥ 1` at `0` and at `1`
   (both hold when the two aperture constants vanish, i.e. on `K₁`), polynomially bounded by the
   same three boundary estimates of `BurnolQuotientGrowth` times a bounded rational factor, and
   `θ(σ) → 0` because the rational factor tends to `1`.  Minimality half needs `K₁` realisations of
   `s(s−1)ζ(s)/((s−ρ₁)(s−ρ₂)(s−ρ)^l)`.
3. Theorems 7.7–7.10 (Levin completely-regular growth).

## Session log — Proposition 6.5, completeness half CLOSED

New modules (built, wired, dupcheck-clean, axioms `[propext, Classical.choice, Quot.sound]`):

* `RHTower/SoninCarrierMellinOrder.lean` — the two order improvements that hold on `K_a` but not on
  `L_a`: `one_le_meromorphicOrderAt_extendedMellinContinuation_zero` (the transform *vanishes* at
  `s = 0`, because the left numerator is `(1−s)·χ(s)·s·T(1−s)` and `χ(0) = 0`) and
  `zero_le_meromorphicOrderAt_extendedMellinContinuation_one` (no pole at `s = 1`, because the
  residue is the physical aperture constant).  Also `burnolChiFactor_zero`,
  `analyticAt_burnolChiFactor_zero`, `two_le_analyticOrderAt_extendedMellinNumerator_zero`.
* `RHTower/TwoPointShiftFactor.lean` — `twoPointShift ρ₁ ρ₂ = (s−ρ₁)(s−ρ₂)/(s(s−1))`, its order
  decomposition, and `exists_bound_twoPointShift`: it is bounded on `‖s‖ ≥ 1, ‖s−1‖ ≥ 1`, which is
  exactly the region containing the boundary of every rectangle `[−1,2] × [−T,T]` with `T ≥ 1`.
* `RHTower/BurnolTwoPointCompleteness.lean` — `soninTwoPointMellin`, the order bookkeeping
  (`meromorphicOrderAt_riemannZeta_le_soninTwoPointMellin`,
  `zero_le_meromorphicOrderAt_burnolQuotient_soninTwoPointMellin`), the three boundary estimates
  (`exists_bound_twoPointNF_right/left/horizontal`), `exists_polyGrowth_twoPointNF`, and
  **`eq_zero_of_zeta_dvd_twoPoint`** — Proposition 6.5's completeness half, for every aperture
  `a ≥ 1`, with `ρ₁ = ρ₂` allowed (Burnol's second case, a zero of multiplicity ≥ 2).

The divisibility hypothesis is stated as
`order ζ ρ ≤ order (M f) ρ + order ((s−ρ₁)(s−ρ₂)) ρ`, which is exactly "orthogonal to the shortened
evaluator list": one unit of slack at `ρ₁` and at `ρ₂`, none anywhere else.

### Route settled for Proposition 6.5's minimality half
Realise `G_{ρ,l}(s) = s(s−1)ζ(s)/((s−ρ₁)(s−ρ₂)(s−ρ)^l)` in `K̂₁`.  In the half-plane variable
`s = w + 1/2` this is `(w+1/2)³·zetaHardyCore(w)/((w−w₁)(w−w₂)(w−w₀)^l)`, `w₁ = ρ₁ − 1/2` etc.
Build it in three steps, each of which splits one factor of `w + 1/2` against one divisor:

* `B₁ = (w+1/2)·zetaHardyCore/(w−w₁) = zetaHardyCore + ρ₁·(zetaHardyCore/(w−w₁))`;
* `B₂ = (w+1/2)·B₁/(w−w₂) = B₁ + ρ₂·(B₁/(w−w₂))` — needs `ord B₁ (w₂) ≥ 1`, which is
  `m_{ρ₂} − [ρ₁ = ρ₂] ≥ 1`, i.e. exactly Burnol's `m_ρ ≥ 2` in the coincident case;
* `K = (w+1/2)·B₂/(w−w₀)^l = B₂/(w−w₀)^{l−1} + ρ·(B₂/(w−w₀)^l)` — needs
  `l ≤ m_ρ − #{i : ρ_i = ρ}`, i.e. "the remaining multiplicities".

Each division uses `exists_isHalfPlaneHardy_div_pow` (no `Re w₀ > 0` hypothesis) after replacing the
existential quotient by the concrete normal form `divShiftNF`, so that the next step has an honest
`AnalyticAt`.  Then `isMellinTailHardy_iff` gives the pure tail datum (head constant `0`), and
`headTailVector_mem_centralSoninExtendedCarrier` with `c₁ = c₂ = 0` plus
`mem_centralSoninCarrier_of_ae_zero` lands the vector in `K₁`.

## Session log — Hardy machinery for Proposition 6.5's minimality half

Reusable modules built (all compile, wired, no `sorry`):

* `HTGeometry/HalfPlaneHardyCongr.lean` — `IsHalfPlaneHardy.congr_right`: Hardy membership sees only
  the values on `Re w > 0`.  This is what lets the anonymous quotient produced by a division lemma
  be replaced by a concrete analytic representative, which the *next* division step can then
  differentiate.
* `RHTower/DivPowRepresentative.lean` — `divPowNF G ρ k` (the meromorphic normal form of
  `G/(w−ρ)^k`), its analyticity, its order, and `exists_isHalfPlaneHardy_divPowNF`.
* `RHTower/ZetaShiftCore.lean` — `zetaShiftCoreNF`, the normal form of `(s−1)ζ(s)/s²` in the
  half-plane variable.  Unlike `zetaHardyCore` (a Laplace transform, holomorphic only on `Re w > 0`)
  it is analytic on all of `ℂ ∖ {−1/2}`, and it agrees with `zetaHardyCore` on the half-plane, so it
  is Hardy.  This is the object one may divide by zeros lying left of the critical line.
* `RHTower/HardyListDivision.lean` — **`exists_isHalfPlaneHardy_listDiv`**: for a list `L` of zeros
  of a Hardy `C` (counted with multiplicity) and any `j ≤ L.length`,
  `(w+1/2)^j·C(w)/∏(w−z_i)` is Hardy, analytic wherever `C` is, and has order
  `ord C z − L.count z` at every `z ≠ −1/2`.  The induction absorbs one `w + 1/2` per divisor via
  `(w+1/2)G/(w−z) = G + (z+1/2)G/(w−z)`, or none when `j` is exhausted.
* `RHTower/ZetaTripleTail.lean` — `exists_isHalfPlaneHardy_zetaTriple`: the instance
  `L = [ρ₁−1/2, ρ₂−1/2] ++ replicate l (ρ−1/2)`, `j = 3`, giving the Hardy function behind
  `s(s−1)ζ(s)/((s−ρ₁)(s−ρ₂)(s−ρ)^l)`.  The three hypotheses `hb₀, hb₁, hb₂` are exactly
  "list count ≤ order of `ζ`" at the three points, i.e. the remaining multiplicities.

### Remaining exact core for 6.5's minimality half
1. From a literal retained jet `k`, choose `l` and prove the selected equality
   `ord_ρ ζ − (1_{ρ=ρ₁}+1_{ρ=ρ₂}+l) = k`, uniformly including `ρ₁ = ρ₂`.
   The source-budget carrier and its strip regularity no longer need independent hypotheses.
2. Prove that `IsTwoPointOmittedEvaluatorWitness` is exactly a witness annihilating every retained
   evaluator functional in Burnol's shortened system, and transfer that into the existing
   minimal-system language.  This is an evaluator/derivative identification, not a Hardy, Gamma,
   reflection, or analyticity gap.

## Session close — state of the tree

Everything below is built, wired into `GaloisForLFunctions.RHTower` / `GaloisForLFunctions.HTGeometry`,
free of warnings, globally collision-scanned, and audited: every capstone depends only on
`[propext, Classical.choice, Quot.sound]`.  `scripts/formal_tools.py lint --check-generated` is clean
and the three generated indexes are regenerated.

Closed this session:
* **Theorem 3.3, minimality half** — `RHTower.burnol_theorem_three_three_minimal`.
* **Proposition 6.5, completeness half** — `RHTower.eq_zero_of_zeta_dvd_twoPoint`
  (every aperture `a ≥ 1`, with `ρ₁ = ρ₂` allowed).

Landed toward **Proposition 6.5's minimality half** (the remaining half):
* `RHTower.exists_isHalfPlaneHardy_listDiv` — divide a Hardy function by a list of its zeros,
  absorbing `j ≤ |L|` factors of `w + 1/2`.
* `RHTower.exists_isHalfPlaneHardy_zetaTriple` — the Hardy function behind
  `s(s−1)ζ(s)/((s−ρ₁)(s−ρ₂)(s−ρ)^l)`.
* `RHTower.soninTripleNF`, `analyticAt_soninTripleNF`, `exists_tail_soninTripleNF` — the analytic
  representative on the strip and its pure-tail datum at aperture one (head constant `0`).
* `RHTower.soninTripleNF_reflect` — `χ(s)·(that)(1−s) = (−1)^l·(same at the mirror zeros)`.

The carrier, exact order transport, and a finite-defect predicate are now completed by
`BurnolTwoPointMinimality.lean`.  The remaining step for 6.5's minimality half is to derive the
selected-order equality from a retained jet and prove that this order predicate is the literal
shortened evaluator-system assertion.  The original `IsMinimalEvaluatorSystem` records an
unshortened multiset and cannot express the two omitted top jets directly.

Remaining paper items: Proposition 6.5's minimality half (as above); Theorem 5.2's `L²`-in-`Z` half,
hence Corollary 5.3 and Theorem 3.3's completeness half; Theorems 7.7–7.10 (Levin's
completely-regular-growth theory).

## Session log — literal `K₁` two-omission carrier assembled

New unconditional module:
`formal/GaloisForLFunctions/RHTower/BurnolTwoPointMinimality.lean`.

This closes the previously unassembled `L₁ → K₁` realization, source-budgeted strip regularity,
and exact jet-order transport, without asserting RH or the full minimality-system statement. Its
principal theorems are deliberately layered:

* `exists_centralSonin_soninTriple_of_twoSidedTail` turns two literal pure Hardy tails into one
  vector of `centralSoninCarrier 1`, with both physical/Fourier aperture constants zero and exact
  completed Mellin continuation on the whole open critical strip.
* `exists_centralSonin_soninTriple_of_reflectedTail` derives the left tail coefficient-faithfully
  from the reflected quotient via `soninTripleNF_reflect`; the exact scale is `(-1)^l`.
* `exists_centralSonin_soninTriple` consumes the three named multiplicity budgets and creates the
  actual carrier.
* `exists_centralSonin_soninTriple_of_symmetricBudget` derives every reflected multiplicity budget
  from the original one using the zeta functional equation.  No independent mirror bookkeeping is
  an assumption any more.
* `meromorphicOrderAt_extendedMellin_soninTriple_of_eq` transports the exact continuation identity
  to every strip jet: zeta order minus the two omitted top jets and the selected jet.
* `analyticAt_soninTripleNF_of_threePointBudget` proves that the three literal divisor budgets
  already imply strip analyticity, including every collision pattern among `ρ₁`, `ρ₂`, and `ρ`.
* `exists_centralSonin_soninTriple_of_sourceBudget` removes both former analyticity hypotheses
  from the `K₁` carrier construction.
* `IsTwoPointOmittedEvaluatorWitness` records the exact finite-defect carrier: evenness, both
  aperture vanishings, every non-selected strip order, and the selected retained order.
* `exists_twoPointOmittedEvaluatorWitness_of_sourceBudget` constructs that literal witness from
  only the source budgets plus the one remaining selected-order equality.

Consequently this assembly discharges six distinct prerequisites of the Proposition 6.5 minimality
witness: both Hardy orientations, literal `K₁`/zero-head membership, full-strip continuation,
exact multiplicity accounting, strip regularity from source budgets, and finite-defect packaging.
It is not a new RH route and does not establish evaluator minimality. The remaining two formal
obligations are selected-order arithmetic and literal evaluator/derivative identification. The
separate Burnol completeness frontier remains Theorem 5.2's `L²`-in-`Z` input, Corollary 5.3,
Theorem 3.3 completeness, and Levin's growth package.

Targeted validation (no umbrella build):

* `lake env lean GaloisForLFunctions/RHTower/BurnolTwoPointMinimality.lean`;
* `lake build GaloisForLFunctions.RHTower.BurnolTwoPointMinimality` only;
* `#print axioms` for every exported theorem in this module reports only
  `[propext, Classical.choice, Quot.sound]`.

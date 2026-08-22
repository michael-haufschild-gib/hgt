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
| (5) | Müntz formula | ζ(s)∫φ tˢ⁻¹ = ∫(modified Poisson sum)tˢ⁻¹ | **TODO** |
| (6) | Müntz applied to g(1/t)/t | co-Poisson Mellin | **TODO** |
| (7) | `F₊(f)^(s) = χ(s) f^(1-s)`; χ = ζ(s)/ζ(1−s) | Mellin diagonalization | **TODO** (needs Mellin unitary) |
| Thm 2.1 | de Branges: `M(f)` entire on `K_a`, evaluations continuous | **DONE**: `RHTower/SoninEntireMellin.differentiable_soninEntireMellin` (+ the functional equation `soninEntireMellin_eq_soninChiSide` on `Re s < 1`, and `soninMellinExtension_functional_equation` on the strip) | |
| Prop 2.2 | `M(f)` meromorphic (poles ⊂ {0,1}) on `L_a`; `M(F₊f)(s)=M(f)(1−s)` | | **TODO** |
| Def 3,4 | `Y_a` (zero span), co-Poisson subspace `P_a` | | corpus (`burnolCoPoissonSourceSpace`) |
| Thm 3.1 | `Y^a_{ρ,k}` minimal iff a ≤ 1, complete iff a ≥ 1; `Y_a^⊥ = P_a` (a<1) | capstone | **TODO** |
| Thm 3.2 | `Z^a_{ρ,k}` minimal not complete a<1; a=1 not minimal, omit 2 → minimal+complete; a>1 complete after finite omission | capstone | **TODO** |
| Thm 3.3 | `ζ(s)/(s−ρ)^l` minimal and complete in `L̂₁`; dual system | capstone | **TODO** |
| Prop 4.1 | characterization of `L̂_a` inside `s/(s−1)·A^s H²` | | **TODO** (Hardy) |
| Prop 4.2 | `ζ(s)/(s−ρ)^l ∈ L̂₁` | | **TODO** |
| Prop 4.3 | division by `(s−w)` stays in `L̂_a` / `K̂_a` | **corpus-owned for `L_a`**: `BurnolSoninDividedShift.burnolShift_mem_soninExtendedSpace`; `K_a` half **DONE**: `RHTower/MellinHardyClasses.IsMellinTailHardy.div_sub` | |
| Lem 4.4 | `F ∈ K̂_a ⇒ F/s ∈ L̂_a` | **DONE**: `RHTower/MellinHardyClasses.IsMellinTailHardy.div_id` and `.div_one_sub` | |
| Prop 4.5 | `dim(L_a/K_a) = 2` | **DONE (full-line model)**: `RHTower/SoninBandCodimensionTwo.finrank_soninBandComplement_eq_two`, from the abstract `HTGeometry/CodimensionTwoOrthogonalSum.finrank_inf_orthogonal_sub_sup_eq_two` + the `L_a` description `RHTower/SoninExtendedOrthogonalBand.mem_soninExtendedSpace_iff_orthogonal_meanZeroBand` | even-subspace restatement TODO (all pieces present: `A'`,`B'` are reflection-invariant so the 2-dim complement already lies in `evenSubspace`) |
| Prop 4.6 | `∪_{b>a}K_b` dense in `K_a` (same for `L`) — via the general lattice identity | **DONE**: `RHTower.topologicalClosure_iSup_centralSoninCarrier` (K) and `RHTower/SoninExtendedApertureChain.topologicalClosure_iSup_centralSoninExtendedCarrier` (L) | |
| Prop 4.7 | `∪_{b>a}K_b ⊊ K_a`, also for Fourier-(skew-)invariant parts | | **TODO** |
| Def 10 | L-Property | **DONE**: `RHTower/LPropertyStrips.HasLProperty` (+ `.add`, `.const_mul`) | |
| Thm 4.8 | functions of `L̂_a` have the L-Property | | **TODO** |
| Def 12 | `𝓛¹` (quick decrease in vertical strips) | **DONE**: `RHTower/LPropertyStrips.HasStripRapidDecrease` (+ `.add`, `.hasLProperty`) | |
| Thm 4.9 | `𝓛¹` dense in `L¹` | | **TODO** |
| Lem 4.10 | `𝓛¹` stable under `F₊` | **DONE** (modulo the classical `χ` strip bound as an input): `RHTower/LPropertyStrips.hasStripRapidDecrease_chi_mul_reflect`, from `.mul_stripPolyGrowth` and `.comp_one_sub` | |
| Prop 5.1 | Titchmarsh IX.7: `|ζ(s)|⁻¹ < |s|^A` on `|Im s| = T_n`, `−1≤Re s≤2` | classical | **TODO** |
| Thm 5.2 | residue series `Σ_ρ G(ρ)/ζ'(ρ) · ζ(Z)/(Z−ρ) = G(Z)` | | **TODO** |
| Cor 5.3 | `ζ(s)/(s−ρ)^l` complete in `L̂₁` | | **TODO** |
| Prop 5.4 | `Σ_ρ G(ρ)/ζ'(ρ) = 0` | | **TODO** |
| Rem 15 | Ramanujan `√a Σμ(n)/n e^{−(a/n)²} − …` | | **TODO** |
| Prop 6.1 | a ≥ 1 ⇒ `Y^a_{ρ,k}` complete in `L_a` (Krein) | | **TODO** |
| Prop 6.2 | a > 1 ⇒ not minimal, complete after finite omission | | **TODO** |
| Thm 6.3 | a = 1 ⇒ minimal and complete | | **TODO** |
| Prop 6.4 | a < 1 ⇒ minimal, not complete | | **TODO** |
| Prop 6.5 | `Z^1_{ρ,k}` not minimal; shortened system minimal + complete | | **TODO** |
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

### Remaining `χ` input for Lemma 4.10
`HasStripPolyGrowthOffReal zetaChi` on an arbitrary strip.  The corpus owns pieces:
`RHTower/ZetaChiVerticalGrowth.exists_bound_norm_zetaChi_vertical` (one fixed line,
`σ ∈ [-1,1/2] \ {0}`) and `RHTower/TitchmarshZetaInputs.norm_zetaChi_le_negative_one_strip`
(uniform on `-1 ≤ σ ≤ -1/2`, above ordinate 2).  A general strip needs the Gamma recurrence to
step the abscissa, plus `HTGeometry/GammaVerticalStripDecay.exists_bound_norm_Gamma_vertical_strip`.

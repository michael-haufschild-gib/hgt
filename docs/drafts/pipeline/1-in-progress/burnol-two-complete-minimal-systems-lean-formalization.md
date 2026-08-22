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
| Thm 2.1 | de Branges: `M(f)` entire on `K_a`, evaluations continuous | analytic half **DONE** (continuation to `Re s > 0`, `SoninMellinHalfPlaneExtension`); weld = brick B7 | |
| Prop 2.2 | `M(f)` meromorphic (poles ⊂ {0,1}) on `L_a`; `M(F₊f)(s)=M(f)(1−s)` | | **TODO** |
| Def 3,4 | `Y_a` (zero span), co-Poisson subspace `P_a` | | corpus (`burnolCoPoissonSourceSpace`) |
| Thm 3.1 | `Y^a_{ρ,k}` minimal iff a ≤ 1, complete iff a ≥ 1; `Y_a^⊥ = P_a` (a<1) | capstone | **TODO** |
| Thm 3.2 | `Z^a_{ρ,k}` minimal not complete a<1; a=1 not minimal, omit 2 → minimal+complete; a>1 complete after finite omission | capstone | **TODO** |
| Thm 3.3 | `ζ(s)/(s−ρ)^l` minimal and complete in `L̂₁`; dual system | capstone | **TODO** |
| Prop 4.1 | characterization of `L̂_a` inside `s/(s−1)·A^s H²` | | **TODO** (Hardy) |
| Prop 4.2 | `ζ(s)/(s−ρ)^l ∈ L̂₁` | | **TODO** |
| Prop 4.3 | division by `(s−w)` stays in `L̂_a` / `K̂_a` | **corpus-owned for `L_a`**: `BurnolSoninDividedShift.burnolShift_mem_soninExtendedSpace` (range `1/2 < Re ρ < 1`) | `K_a` half TODO |
| Lem 4.4 | `F ∈ K̂_a ⇒ F/s ∈ L̂_a` | | **TODO** |
| Prop 4.5 | `dim(L_a/K_a) = 2` | **DONE (full-line model)**: `RHTower/SoninBandCodimensionTwo.finrank_soninBandComplement_eq_two`, from the abstract `HTGeometry/CodimensionTwoOrthogonalSum.finrank_inf_orthogonal_sub_sup_eq_two` + the `L_a` description `RHTower/SoninExtendedOrthogonalBand.mem_soninExtendedSpace_iff_orthogonal_meanZeroBand` | even-subspace restatement TODO (all pieces present: `A'`,`B'` are reflection-invariant so the 2-dim complement already lies in `evenSubspace`) |
| Prop 4.6 | `∪_{b>a}K_b` dense in `K_a` (same for `L`) — via the general lattice identity | **DONE (K side)**: `RHTower.topologicalClosure_iSup_centralSoninCarrier` | `L` side TODO |
| Prop 4.7 | `∪_{b>a}K_b ⊊ K_a`, also for Fourier-(skew-)invariant parts | | **TODO** |
| Def 10 | L-Property | | **TODO** |
| Thm 4.8 | functions of `L̂_a` have the L-Property | | **TODO** |
| Def 12 | `𝓛¹` (quick decrease in vertical strips) | | **TODO** |
| Thm 4.9 | `𝓛¹` dense in `L¹` | | **TODO** |
| Lem 4.10 | `𝓛¹` stable under `F₊` | | **TODO** |
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
| §2 chain | `K = ∪_{a>0}K_a`, `{0} = ∩_{a>0}K_a` | **DONE (K side)**: `RHTower/SoninCarrierApertureLimits.lean` | `L` side TODO |
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
| B7 | glue with the reflected brick across `0 < Re s < 1` using the corpus scattering identity | **TODO — the only remaining brick.** Needs: (i) `fourierUnitary` preserves `centralSoninCarrier a`; (ii) the pointwise functional equation `f̂(s) = χ(s)·(F₊f)^(1−s)` a.e. on the critical line, bridged from `CCMArchimedeanFourierMellinScattering`; (iii) the identity theorem on the strip `0 < Re s < 1`. |

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

# Semilocal Prime-Two Logarithmic Trace Identity, Positivity Obstructions, and Intrinsic Gluing Law Through `½ log 3`

- **ID:** `semilocal-prime-two-trace-obstruction-and-gluing-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) | FALSIFIED (semilocal positive tensor-trace mechanism) + POSITIVE SURVIVORS
- **Source:** `docs/reports/review-0111/fable.md` §2.2 (Candidate A), §7 (Q6)
- **Statement:** On `ℓ²(ℤ)`, the `2`-adic valuation-shell Wiener–Hopf defect `K₂(m) = (log 2)(P_{ℤ₂} − U₂^m P_{ℤ₂} U₂^{−m})` is positive and trace-class with `opTrace(K₂(m)) = m log 2`, giving an exact `{∞, 2}` operator-trace identity for the restricted Weil form on `(0, ½ log 3]`; nevertheless, rewriting Weil positivity through `½ log 3` as the trace of a positive `{∞, 2}` tensor or semilocal scaling operator is unconditionally impossible (pure-tensor trace vanishing/homogeneity obstruction, bilateral prime-`2` indefiniteness, and exponential ground-energy collapse to `−∞` with forced zero crossing of both `primeFreeFamily` and `primeSingleSemilocalFamily p` along `L_M = ((2M + 1)/4) log p`), while intrinsic positivity of `ccmRestrictedWeilZeroFormOperator` gives the exact rank-one trace characterization of window positivity (unconditionally certified through `181/500 > ½ log 2` and equivalent at `½ log 3` to all-test Weil positivity, Hodge index, and Künneth effectivity).

## Goal
Resolve Question Q6 of `docs/reports/review-0111/fable.md` unconditionally, separating the exact semilocal trace-identity half (which holds through closed aperture `½ log 3`) from the positive-operator half (which fails for exact operator-theoretic and Krein-index reasons), and formalize both the obstructions and the exact positive survivors.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean modules in `GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace`, `--old env lean` green, `#print axioms` clean

## Mathematical Results and Paper Proofs `[PROVED HERE]`

### 1. Local `p`-adic Valuation-Shell Wiener–Hopf Operator and Logarithmic Trace Law

Let `ℓ²(ℤ) := lp (fun _ : ℤ => ℂ) 2` represent unramified valuation shells `p^n ℤ_p^×`, let `U : ℓ²(ℤ) →L[ℂ] ℓ²(ℤ)` be the unitary right shift `(U x)_n = x_{n − 1}`, and let `P_{ℤ_p}` be the orthogonal projection onto `{n : ℤ | 0 ≤ n}`. For any prime `p` (in particular `p = 2`) and `m : ℕ`, define the valuation-shell Wiener–Hopf defect

```text
K_p(m) := (log p) • ∑_{k = 0}^{m − 1} |e_k⟩⟨e_k| = (log p) • (P_{ℤ_p} − U^m P_{ℤ_p} U^{−m}),
```

where `e_k = lp.single 2 (k : ℤ) 1`.

**Proof.**
1. For each `x ∈ ℓ²(ℤ)` and `n ∈ ℤ`, `(P_{ℤ_p} x)_n = [0 ≤ n] x_n` and `(U^m P_{ℤ_p} U^{−m} x)_n = [m ≤ n] x_n`. Their difference is nonzero precisely for `0 ≤ n < m`, coinciding coordinatewise with `∑_{k ∈ Finset.range m} |e_k⟩⟨e_k| x`.
2. Each `|e_k⟩⟨e_k|` is self-adjoint, `IsPositive` (`⟪|e_k⟩⟨e_k| x, x⟫ = ‖⟪e_k, x⟫‖² ≥ 0`), and rank one (`HasRankLE _ 1`). Since `log p > 0`, `K_p(m)` is self-adjoint, `IsPositive`, and satisfies `HasRankLE (K_p(m)) m`, hence `MemSchattenClass 1 (K_p(m))` and `IsTraceClass (K_p(m))`.
3. By linearity of `opTrace` on `MemSchattenClass 1` and `opTrace(|e_k⟩⟨e_k|) = ⟪e_k, e_k⟫ = 1`,

```text
opTrace(K_p(m)) = (log p) · m = log(p^m).
```

4. Multiplying by the unsquared Euler-factor logarithmic coefficient `c_p(m + 1) = p^{−(m + 1)/2} / (m + 1)` (`soninSemilocalLogPrimePowerCoefficient`) gives

```text
c_p(m + 1) · opTrace(K_p(m + 1)) = (log p) / p^{(m + 1)/2} = Λ(p^{m + 1}) / √(p^{m + 1}),
```

bypassing `not_soninSemilocalFluxNormalization` (`SoninSemilocalTraceObstruction`): the Hilbert–Schmidt projection-defect pairing had uniformly bounded scale response, whereas the valuation-shell Wiener–Hopf defect `K_p(m)` supplies the exact `m log p` trace growth.

### 2. Closed-Endpoint Prime Cutoff Laws at `½ log 2` and `½ log 3`, and the `{∞, 2}` Trace Identity

Define `halfLogTwoAperture := ⟨(log 2)/2, _⟩` and `halfLogThreeAperture := ⟨(log 3)/2, _⟩`.

1. **Boundary transport vanishing (`ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log`).** If `2a ≤ log n`, then for any `f, g ∈ suzukiApertureHilbert a`, `f` vanishes a.e. outside `[−a, a]` and `logTranslationCLM (±log n) f` vanishes a.e. outside `[−a ∓ log n, a ∓ log n]`. The intersection `[−a, a] ∩ [−a ∓ log n, a ∓ log n]` contains at most one boundary point `{±a}` when `log n = 2a` and is empty when `log n > 2a`, hence has Lebesgue measure zero. Thus `⟪ccmPrimeTransportOperator a n f, g⟫ = 0` for all `f, g`, so `ccmPrimeTransportOperator a n = 0`.
2. **Closed prime-free window `(0, ½ log 2]`.** For every `a` with `a.1 ≤ (log 2)/2`, every `n ≥ 2` has `2a.1 ≤ log 2 ≤ log n`, so `ccmPrimeTransportOperator a n = 0` and `ccmFinitePrimeOperator a = 0` (even at `a = halfLogTwoAperture`, where `⌊e^{2a}⌋ = 2`).
3. **Closed prime-`2` window `(½ log 2, ½ log 3]`.** For every `a` with `(log 2)/2 < a.1 ≤ (log 3)/2`, `e^{2a.1} ≤ 3` so `⌊e^{2a.1}⌋ ≤ 3`, while `2 ≤ ⌊e^{2a.1}⌋` because `2 < e^{2a.1}`. Every `n ∈ Icc 2 ⌊e^{2a.1}⌋` is either `2` or `3`; when `n = 3`, `2a.1 ≤ log 3` gives `ccmPrimeTransportOperator a 3 = 0`. Hence

```text
ccmFinitePrimeOperator a = (log 2 : ℂ) • ccmPrimeTransportOperator a 2
  = (c_2(1) : ℂ) * opTrace(K_2(1)) • ccmApertureCompression a (ccmSymmetricLogTranslation (log 2)).
```

4. **Single-prime `{∞, p}` semilocal remainder family (`primeSingleSemilocalFamily p`).** Retaining in the prime sum only integers `n ≥ 2` that are prime powers of `p` (`∃ m ≥ 1, n = p^m`) defines a self-adjoint aperture-compatible family `primeSingleSemilocalFamily p : CCMRemainderFamily`. For `p = 2` and every `a.1 ≤ (log 3)/2`, the only prime power `≤ 3` not of the form `2^m` is `3`, whose transport operator vanishes on `(0, ½ log 3]`; hence `(primeSingleSemilocalFamily 2).B a = ccmRestrictedWeilBoundedRemainder a`, `(primeSingleSemilocalFamily 2).Q a = ccmRestrictedWeilSourceQuadratic a`, and `(primeSingleSemilocalFamily 2).energy a = ccmRestrictedWeilGroundEnergy a` identically on `(0, ½ log 3]`.
5. **Exact `{∞, 2}` operator-trace identity through `½ log 3`.** For every `a` with `a.1 ≤ (log 3)/2` and every smooth interior source `g : CCMComplexSmoothInteriorSource a` with physical vector `f = J_a g.toCCMFormVector`,

```text
ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector
  = opTrace(ccmSoninCutoffDeficitOp g) + (opTrace(ccmPolarOperator a ∘L |f⟩⟨f|)).re
    − c_2(1) · (opTrace(K_2(1)) * opTrace(ccmApertureCompression a (ccmSymmetricLogTranslation (log 2)) ∘L |f⟩⟨f|)).re,
```

where the first term equals `−ccmArchimedeanWeilDistribution(g^* ⋆ g)` by `neg_ccmArchimedeanWeilDistribution_ccmSoninGramTest` (and `opTrace(ccmIntegratedScaling(g^* ⋆ g) ∘ geometricScatteringLogDifferential)` on intrinsic Schwartz tests).

### 3. Four Exact Operator-Theoretic Obstructions Answering Q6 in the Negative

#### Obstruction A — Multiplicative Pure-Tensor Trace Obstruction
1. **Against the pole-free archimedean trace (`archPart`).** By `not_ccmSoninTraceDomination_of_nonneg` (`CCMArchimedeanSoninSmallSupportDomination`), on `(−3/10, 3/10)` there exists a nonzero smooth interior source `g_−` with `archPart a g_−.toCCMFormVector ≤ 0` (indeed `< 0`), while on any nonzero pole-vanishing smooth interior source `g_+` (`exists_polarConstrained_smooth_ne_zero`), `polarPart = 0` and `ccmFinitePrimeOperator = 0`, so `archPart a g_+.toCCMFormVector = Q_a(g_+) ≥ (1/5000) ‖J_a g_+‖² > 0`. Along a path joining `g_−` and `g_+` (or directly if `archPart(g_−) = 0`, otherwise on the real span where `g_−` and `g_+` are linearly independent because their `archPart` signs are opposite), the continuous quadratic form `archPart` vanishes on a nonzero form vector `u_0` whereas `Q_a(u_0) ≥ (1/5000) ‖J_a u_0‖² > 0` (`u_0 ≠ 0 ⟹ J_a u_0 ≠ 0`). Thus no functional `τ_2` can satisfy `archPart(u) · τ_2(u) = Q_a(u)` even at `a = 3/10`.
2. **Against the pole-glued archimedean factor (`primeFreeFamily.Q`).** On every `a ∈ (½ log 2, ½ log 3]`:
   - No test-independent scalar `c ∈ ℝ` can satisfy `Q_a(u) = c · primeFreeFamily.Q a u` for all `u`: on narrow nonzero sources supported in `(−¼ log 2, ¼ log 2)`, `Q_a(u) = primeFreeFamily.Q a u ≠ 0` forces `c = 1`, whereas on a smooth two-bump source separated by `log 2` inside `(−a, a)`, `Q_a(u) − primeFreeFamily.Q a u = −(log 2 / √2) · 2 ∫ φ² ≠ 0`, contradiction.
   - No positive-degree homogeneous factor `τ_2(λ u) = |λ|^{2d} τ_2(u)` (`d ≥ 1`) can satisfy `primeFreeFamily.Q a u · τ_2(u) = Q_a(u)` because `Q_a(λ u) = |λ|² Q_a(u)` whereas the product scales as `|λ|^{2 + 2d}`.

#### Obstruction B — Unglued Negativity and Bilateral Indefiniteness of the Prime-`2` Operator
At every aperture `a` with `(log 2)/2 < a.1`:
1. Take `r > 0` with `r < min ((log 2)/4, a.1 − (log 2)/2)` and let `φ± = bumpInteriorSource a (±(log 2)/2) r`. On the nonnegative even sum `u_+ = φ_+ + φ_−`, `⟪ccmPrimeTransportOperator a 2 (J_a u_+), J_a u_+⟫.re = (2 / √2) ∫ (polarBumpFn 0 r)² > 0`, so the Weil prime-`2` summand `−(log 2) ⟪ccmPrimeTransportOperator a 2 (J_a u_+), J_a u_+⟫.re < 0` is strictly negative.
2. On the odd difference `u_− = φ_+ − φ_−`, `⟪ccmPrimeTransportOperator a 2 (J_a u_−), J_a u_−⟫.re = −(2 / √2) ∫ (polarBumpFn 0 r)² < 0`, so the Weil prime-`2` summand is strictly positive.
3. Hence neither `ccmPrimeTransportOperator a 2` nor `−ccmPrimeTransportOperator a 2` is `IsPositive` on `suzukiApertureHilbert a` (and for `a.1 ≤ (log 3)/2`, neither `ccmFinitePrimeOperator a` nor `−ccmFinitePrimeOperator a` is `IsPositive`).

#### Obstruction C — Exponential Ground-Energy Collapse and Forced Zero Crossing of `primeFreeFamily` and `primeSingleSemilocalFamily p`
Fix any prime `p` (in particular `p = 2`). Set `a_0 := ⟨1/8, _⟩` and let `u_0 := (polarCenterBump a_0).toCCMFormVector`, whose physical representative is `polarBumpFn 0 (1/64)` supported in `(−1/64, 1/64)` with positive polar moments `m_+ := polarBumpMoment 0 (1/64) (1/2) > 0` and `m_− := polarBumpMoment 0 (1/64) (−1/2) > 0`.

For every `M : ℕ`, define the half-integer logarithmic shift and aperture

```text
L_M := ((2M + 1 : ℝ) / 4) * log p,        b_M := ⟨1/8 + L_M, _⟩,
v_M := ccmArchimedeanFormTranslate (−L_M) _ u_0 − ccmArchimedeanFormTranslate L_M _ u_0 ∈ CCMArchimedeanFormDomain b_M.
```

1. **Uniform archimedean bound.** By `norm_ccmArchimedeanFormTranslate` and `norm_ccmArchimedeanFormTranslate_physical`, `‖v_M‖ ≤ 2 ‖u_0‖` and `‖J_{b_M} v_M‖ ≤ 2 ‖J_{a_0} u_0‖`, so `‖v_M‖² + |2 γ'(0) − 1| ‖J_{b_M} v_M‖² ≤ C_0` with `C_0` independent of `M`. Moreover `v_M` evaluates at `x = L_M` to `1 − 0 = 1`, so `J_{b_M} v_M ≠ 0`.
2. **Exact evasion of the entire `p`-adic tower `{p^k : k ≥ 1}`.** Since `p ≥ 2` and `e < 4`, `log p ≥ log 2 > 1/2`. For every `k ≥ 1`:
   - `k log p ≥ log p > 1/2 > 1/32`;
   - `|k log p − 2 L_M| = |k − M − 1/2| · log p ≥ (1/2) log p > 1/4 > 1/32`.
   Because `J_{b_M} v_M` is supported a.e. in `[L_M − 1/64, L_M + 1/64] ∪ [−L_M − 1/64, −L_M + 1/64]`, the support of `logTranslationCLM (±k log p) (J_{b_M} v_M)` is disjoint from that of `J_{b_M} v_M`. Hence `⟪ccmPrimeTransportOperator b_M (p^k) (J_{b_M} v_M), J_{b_M} v_M⟫ = 0` for every `k ≥ 1`.
3. **Exponentially negative odd polar energy.** By `inner_polar_ccmArchimedeanFormTranslate`,
   - `⟪h_+(b_M), J_{b_M} v_M⟫ = (e^{L_M/2} − e^{−L_M/2}) m_+`,
   - `⟪h_−(b_M), J_{b_M} v_M⟫ = −(e^{L_M/2} − e^{−L_M/2}) m_−`,
   so `polarPart b_M v_M = −2 (e^{L_M/2} − e^{−L_M/2})² m_+ m_− → −∞` as `M → ∞`.
4. **Consequence.** For sufficiently large `M`, `primeFreeFamily.Q b_M v_M = (primeSingleSemilocalFamily p).Q b_M v_M ≤ C_0 − 2 (e^{L_M/2} − e^{−L_M/2})² m_+ m_− < 0`, so `primeFreeFamily.energy b_M < 0` and `(primeSingleSemilocalFamily p).energy b_M < 0` (and in fact both tend to `−∞` as `a → ∞`). Since both families agree with `ccmRestrictedWeilGroundEnergy` at small apertures (`> 0`), `CCMRemainderFamily.exists_energy_eq_zero` and `exists_kernel_of_energy_eq_zero` yield an unconditional zero-crossing aperture `a_*` with a nonzero Friedrichs kernel element for both `primeFreeFamily` and `primeSingleSemilocalFamily p` (in particular for `p = 2`).

#### Obstruction D — Impossibility of Any Positive Semilocal `{∞, 2}` Operator-Trace Carrier
For any Hilbert space `H`, any `ContinuousLinearMap.IsPositive M` (`M : H →L[ℂ] H`), and any aperture-indexed assignment `Θ_a(u) : K_a →L[ℂ] H` of Hilbert–Schmidt operators, `ContinuousLinearMap.IsPositive (Θ_a(u)^* ∘L M ∘L Θ_a(u))` gives `0 ≤ (opTrace (Θ_a(u)^* ∘L M ∘L Θ_a(u))).re`. Because `(primeSingleSemilocalFamily 2).Q b_M v_M < 0` (and by smooth-core density there is a smooth interior source `g` with `(primeSingleSemilocalFamily 2).Q b_M g.toCCMFormVector < 0`), no such positive operator-trace carrier can realize `(primeSingleSemilocalFamily 2).Q` across compactly supported tests — even though `(primeSingleSemilocalFamily 2).Q` equals `ccmRestrictedWeilSourceQuadratic` identically on `(0, ½ log 3]`.

### 4. Positive Survivor — Intrinsic Operator-Trace Equivalence, Parity-Chirality Polar Split, and Window Corollaries

1. **Exact rank-one trace representation.** On `CCMArchimedeanFormDomain a`, `|u⟩⟨u| = InnerProductSpace.rankOne ℂ u u` satisfies `MemSchattenClass 1` and `IsTraceClass`, and

```text
opTrace(ccmRestrictedWeilZeroFormOperator a ∘L |u⟩⟨u|) = ccmRestrictedWeilForm a u u,
(opTrace(ccmRestrictedWeilZeroFormOperator a ∘L |u⟩⟨u|)).re = ccmRestrictedWeilSourceQuadratic a u.
```

2. **Exact Krein `(+1, −1)` parity-chirality decomposition of `ccmPolarOperator a`.** With `h_cosh(a) = (1/2 : ℂ) • (h_+(a) + h_−(a))` and `h_sinh(a) = (1/2 : ℂ) • (h_+(a) − h_−(a))`,

```text
ccmPolarOperator a = (2 : ℂ) • |h_cosh(a)⟩⟨h_cosh(a)| − (2 : ℂ) • |h_sinh(a)⟩⟨h_sinh(a)|,
```

exhibiting `ccmPolarOperator a` as the difference of two positive rank-one trace-class operators supported on the even and odd sectors.
3. **Intrinsic operator-positivity equivalence at every aperture (in particular `½ log 2` and `½ log 3`).** For every `a : SuzukiPositiveAperture`, the following are unconditionally equivalent:
   - `(i)` `ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator a)`;
   - `(ii)` `∀ u : CCMArchimedeanFormDomain a, 0 ≤ (opTrace (ccmRestrictedWeilZeroFormOperator a ∘L InnerProductSpace.rankOne ℂ u u)).re`;
   - `(iii)` `0 ≤ ccmRestrictedWeilGroundEnergy a`.
   When `a.1 ≤ (log 3)/2`, `(i)–(iii)` are also equivalent to `0 ≤ (primeSingleSemilocalFamily 2).energy a`; when `a.1 ≤ (log 2)/2`, also to `0 ≤ primeFreeFamily.energy a`.
4. **Unconditional certified operator-trace positivity past `½ log 2` and equivalences at `½ log 3`.**
   - Unconditionally for every `a` with `a.1 ≤ 181/500` (which strictly exceeds `(log 2)/2`, hence includes `halfLogTwoAperture` and enters the selective prime-`2` window!), `1/5000 ≤ ccmRestrictedWeilGroundEnergy a` and `ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator a)` hold, together with `(scalingSubsurface zetaZeroConfig (realTestsAt a.1)).HodgeIndex`, `hodgeDefectAt zetaZeroConfig a.1 = 0`, `IsEffectivityFunction (scalingSubsurface zetaZeroConfig (realTestsAt a.1)) kunnethCount`, and `Real.log 2 / 2 < 181 / 500 ≤ zetaContactAperture` (when `¬ RiemannHypothesis`).
   - At `a = halfLogThreeAperture` (`½ log 3`), `IsPositive (ccmRestrictedWeilZeroFormOperator halfLogThreeAperture)` implies strict ground-energy positivity `0 < ccmRestrictedWeilGroundEnergy b` (and `ker (ccmRestrictedWeilOperator b) = ⊥`) for every `b < halfLogThreeAperture`, window positivity `ZetaWindowPositive B` for every `0 < B < (log 3)/2`, `¬ RiemannHypothesis → (log 3)/2 ≤ zetaContactAperture`, and is implied by `ZetaWindowPositive ((log 3)/2)` (which in turn yields `HodgeIndex` and `IsEffectivityFunction _ kunnethCount` on `realTestsAt ((log 3)/2)`).

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Four joint obstructions kill rewriting small-aperture Weil positivity through `½ log 3` as the trace of a positive `{∞, 2}` tensor/semilocal operator: (1) pure-tensor trace multiplicativity fails already on `(−3/10, 3/10)` because `archPart` vanishes on a nonzero vector where `Q_a > 0`, and fails on `(½ log 2, ½ log 3]` even with polar gluing by narrow-vs-wide support comparison and degree-2 scaling; (2) `-ccmPrimeTransportOperator a 2` is bilaterally indefinite on `(½ log 2, ∞)`; (3) along the half-integer lattice `L_M = ((2M + 1)/4) log p`, odd translated bumps evade every prime power `p^k` (`k ≥ 1`) while polar energy diverges to `−∞`, forcing negative ground energy and a Friedrichs zero crossing for both `primeFreeFamily` and `primeSingleSemilocalFamily p` (`p = 2`); (4) positivity of `opTrace(Θ^* M Θ)` for `M ≥ 0` therefore refutes any Hilbert–Schmidt `{∞, 2}` operator-trace realization.
- **Strongest positive survivor:** (S1) Exact positive trace-class valuation-shell operator `K_p(m)` on `ℓ²(ℤ)` with `opTrace(K_p(m)) = m log p`, resolving the bounded-response obstruction locally and yielding an exact `{∞, 2}` operator-trace identity for `ccmRestrictedWeilSourceQuadratic` through the closed endpoint `½ log 3` (`ccmFinitePrimeOperator_eq_of_le_halfLogThree`, `primeSingleSemilocalFamily`); (S2) exact rank-one trace equivalence `IsPositive (ccmRestrictedWeilZeroFormOperator a) ↔ 0 ≤ ccmRestrictedWeilGroundEnergy a` plus Krein `(+1, −1)` polar rank-one split, unconditionally positive through `181/500 > ½ log 2` (`halfLogTwoAperture` included).
- **New insight:** Local logarithmic trace growth at `p = 2` is completely constructive (`K_2(m) ≥ 0` of rank `m`), so the obstruction to Candidate A is **not** local trace normalization at `2`: it is the minus sign of the explicit-formula prime block coupled to the `−2|⟪sinh, f⟫|²` odd polar mode, which any finite-place `{∞, p}` truncation leaves uncompensated along `((2M + 1)/4) log p`. Any positive operator-trace certificate at `½ log 3` must therefore either act intrinsically on the Paley–Wiener compressed aperture space (`ccmRestrictedWeilZeroFormOperator`) or incorporate non-`{∞, 2}` Krein-extension mass at primes `q ≥ 3`.
- **Status:** Dependency-closed paper proof above; Lean 4 formalization in `GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace`.

## Log
- 2026-11-01 — created in `2-fully-proven` with complete paper proofs of the local `2`-adic logarithmic trace operator, closed-endpoint `½ log 2` and `½ log 3` cutoff laws, four semilocal positivity obstructions, and intrinsic positive-trace survivors.

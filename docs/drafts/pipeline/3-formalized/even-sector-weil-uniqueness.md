# Even-sector Weil uniqueness: RH ⟺ prime-blind positivity on even tests

- **ID:** even-sector-uniqueness
- **Stage:** 3-formalized
- **Type:** THEOREM, fully formalized [L] (MUST-1482, 1488, 1489, 1491, 1492, 1493, 1494, 1495)
- **Source:** rh-goal-loop-opus-2026-09-29.md rows 1213, 1213′, 1218, 1219; STATUS MUST-1472, MUST-1482
- **Statement:** If real weights `lam` make the Weil functional (pole weight 1) nonnegative on every
  autocorrelation of an EVEN compactly supported C² test, then RH holds and `lam = Λ` on `n ≥ 2`.
  With the even Farkas law (MUST-1482): RH ⟺ PBAP_even (prime-blind positivity on the even cone).

## Goal
Sharpen RH ⟺ PBAP (full cone) to the even cone. Even tests have pole term 2|f̂(i/2)|² ≥ 0, so the even
sector is the "pole-nonnegative" half of the problem. Row 1213′ predicted that G₀ (the twisted-arc blind
null function) is not even-type and that the even cone might be fat. This card shows the obstruction sits
only at |Im| > 3/2, beyond the range the a priori growth of even-positive weights can reach.

## Paper proof

Notation. `W = W_{1,lam}`, `P` its kernel distribution, `k_f = f ⋆ f̃`, `f = f_e + f_o` the parity split.
`W(k(−·)) = W(k)` (pole, archimedean and prime terms are reflection symmetric), so W kills odd functions.

1. **Parity split.** For every test f: `k_f = k_{f_e} + k_{f_o} + (odd)`, hence
   `W(k_f) = W(k_{f_e}) + W(k_{f_o})`. Full positivity ⟺ even ∧ odd positivity. Odd f = h′ with h even
   and compactly supported (h = ∫_{−∞}^x f, using ∫f = 0), and `k_{h′} = −k_h″`, `k̂_{h′} = r²|ĥ|²`.
2. **A priori growth.** If lam is even-positive, then `|lam_n| ≤ C√n log n`. Use the even two-bump tests
   at the node log n (`evenPlus`, `evenMinus`, profile width ≍ 1/n): node value `±2‖p‖²/√n`, pole
   `O(√n δ²)`, archimedean `O(δ log(1/δ))`.
3. **Relative odd positivity at c = 2.** For even smooth compactly supported v:
   `W(k_{v′}) + 2W(k_v) ≥ 0`. The even function u with `û = √(r²+2)·v̂` decays like `e^{−(√2−ε)|x|}`,
   and `k_u = k_{v′} + 2k_v`. Truncations u_R are admissible even tests. The pole term converges (√2 > ½),
   the archimedean term converges in L², and the prime sum converges by step 2 (√2 > 1).
4. **Transmutation.** For c ∈ ℝ put `K_c(t,x) = (ct/2)·E(c(t²−x²))` with
   `E(w) = Σ_m (w/4)^m/(m!(m+1)!)` (= 2I₁(√w)/√w). Then for t ≥ 0:
   `cos(t√(ρ²−c)) = cos(ρt) + ∫_0^t K_c(t,x) cos(ρx) dx`, as entire functions of ρ².
   Proof: compare coefficients of ρ^{2n} using `∫_0^t (t²−x²)^m x^{2n} dx = t^{2m+2n+1}·m!2^m/∏_{i=0}^{m}(2n+2i+1)`,
   by induction on m. Define `(𝒯_c g)(x) = g(x) + ∫_{|x|}^∞ K_c(t,|x|) g(t) dt` on even functions. It
   preserves the support [−R,R] and C² regularity, and `(𝒯_c g)^(ρ) = ĝ(√(ρ²−c))`. So it is
   multiplicative on convolutions, and `𝒯_c 𝒯_{−c} = id`.
5. **ρ-world positive definiteness.** `T̃(G) := W(𝒯_{−2} G_e)`. For any test G and y_i, c_i:
   `Σ c_i c̄_j T̃(τ_{y_i−y_j} k_G) = T̃(k_U)` with U = Σ c_i τ_{y_i} G, which equals
   `W(k_{𝒯_{−2}U_e}) + [W(k_{v′}) + 2W(k_v)]` (v = 𝒯_{−2}V, V′ = U_o). Both terms are ≥ 0 by
   even positivity and step 3. So T̃ is positive definite, and Bochner (corpus,
   `HTGeometry/BochnerPositiveDefiniteReal`) with spectral consistency gives a positive tempered μ̃ with
   `T̃(k_G) = ∫|Ĝ|² dμ̃`.
6. **TMP Laplace positivity.** Twisted-arc weights `w_j = 4√2 m_j/(j!(½)_j)`,
   `m_j = ∫√(y_u/2) u^{2j} dν`, ν a probability measure on [−½,½]. Then
   `Ĝ₀(iy)/Ξ(iy)² = 4√2∫√(y_u/2)·₂F₁(¼−y/2, ¼+y/2; ½; u²) dν(u)`. For |y| ≤ 3/2 and |u| ≤ ½,
   `|(a)_j| ≤ j!` and `(b)_j ≤ j!`, so the j-th term is at most `1/C(2j,j)` in absolute value.
   `Σ_{j≥1} 1/C(2j,j) ≤ ¾` (since C(2j,j) ≥ 2·3^{j−1}), so `₂F₁ ≥ ¼`. With Ξ(iy) = ξ(½−y) > 0,
   **Ĝ₀(iy) > 0 for |y| ≤ 3/2**, for every twisted-arc measure ν.
7. **Null evaluation.** `W(G₀) = Σ_j w_j W(k_{F_j}) = W_Λ(G₀) − Σ_n (lam_n − Λ_n)ℓ_n(G₀) = 0`. This uses
   Ξ-divisibility, joint blindness, and absolute convergence by step 2. Through the parity split and 𝒯₂:
   `W(G₀) = ∫ Ĝ₀(√(ρ²−2)) dμ̃(ρ)`. The integrand is ≥ 0 on ℝ, and > 0 for |ρ| ≤ √2 (imaginary argument
   of modulus ≤ √2 ≤ 3/2, step 6). Hence μ̃ has no mass on [−√2, √2].
8. **Odd positivity.** For odd f = h′: `W(k_f) = ∫(ρ²−2)|(𝒯₂h)^(ρ)|² dμ̃ ≥ 0`.
9. With step 1, lam is full-cone Weil-positive, so `lam = Λ` and RH
   (`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`).

Reading. Even positivity is positivity of a spectral measure on the cross ℝ ∪ iℝ, i.e. on the whole real
λ-line, λ = ¼ + r² = s(1−s). Odd positivity is the Stieltjes condition λ ≥ ¼. The growth bound confines
imaginary spectrum to |Im r| ≤ 1. On that range G₀ is strictly positive, so G₀ kills it. Row 1213′'s
negative Legendre moments live at y = 2m + ½ ≥ 5/2, outside the reachable range.

## Lean programme
- A1 `RHTower/TwistedArcNullLaplacePositivity`: ₂F₁ lower bound and Ĝ₀(iy) > 0 for |y| ≤ 3/2.
- A2 `RHTower/WeilParitySplit`: W(k_f) = W(k_{f_e}) + W(k_{f_o}); full ⟺ even ∧ odd.
- A3 `RHTower/EvenSectorWeightGrowth`: |lam_n| ≤ C√n log n for even-positive lam.
- B `HTGeometry/CosineTransmutation`: K_c, 𝒯_c, Fourier identity, support, regularity.
- C relative odd positivity; ρ-world Bochner and global measure.
- D assembly: `eq_vonMangoldt_of_weilPositiveEvenAt`, `riemannHypothesis_iff_primeBlindPositiveEvenAt`.

## Log
- 2026-10-14 — created in 1-in-progress (loop row 1219); paper proof complete; Lean stage A next.
- 2026-10-15 — A1 done [L] MUST-1488 (`RHTower/TwistedArcNullLaplacePositivity`). A3 done [L] MUST-1489 (`RHTower/EvenSectorWeightGrowth`). A2 is partly covered by another module (`re_weilFullFunctional_ofReal_eq_even_add_odd`, real tests, β = 1). Next: B (transmutation).
- 2026-10-15 — Strip-world route (no Bessel kernels).
  - DONE [L] `RHTower/EvenSectorStripPositivity`: even positivity extends to even real tests with decay rate b > 1 (`archPoleEnergy_sub_atomPairing_nonneg`). Spectral form `evenWeilDensity_specSq_nonneg`: L(ΦΦ^#) ≥ 0 for even strip functions of width > 1. Here L(K) = Re(K(i/2)+K(−i/2)) + (1/2π)∫Re K γ − Σ_n (lam_n/√n)(1/π)∫Re K cos(r log n).
  - DONE [L] `RHTower/EvenSectorCosineBochner`: ρ(z) = (z²+2)^{1/2} on |Im z| < √2, with |Im ρ| ≤ |Im z|. L is linear on good densities. φ_Φ(y) = L(cos(yρ)ΦΦ^#) is positive definite via ΣΣ c_i c_j cos((t_j−t_i)ρ)ΦΦ^# = AA^# + BB^#, and continuous; Bochner gives ν_Φ (`exists_cosineShift_measure`).
  - REMAINING:
    - (R1) Even analytic ∘ √ is analytic (HTGeometry).
    - (R2) σ_h(ρ) = (hh^#)(√(ρ²−2)) is a ρ-strip function, and κ_h = stripTest σ_h. Consistency ν_{Φh} = σ_h ν_Φ: Fubini inside L, then `Measure.ext_of_charFun`.
    - (R3) Global ν := ν_G/σ_G with a Gaussian reference G(z) = e^{−z²}, so that ν_Φ = σ_Φ ν.
    - (R4) TMP family: Σ_j w_j L(Ξ²Q_jQ_j^#) = 0 (blindness, Ξ-divisibility, exchange). Split Q_j = E_j(z²) + iz P_j(−z²). Integrand Ĝ₀(√(ρ²−2)) > 0 on |ρ| ≤ √2 (MUST-1488), hence ν([−√2,√2]) = 0.
    - (R5) Odd positivity L(z²ΨΨ^#) = ∫(ρ²−2)σ_Ψ dν ≥ 0. Gaussian smoothing passes to compactly supported tests. Then full positivity, lam = Λ, RH ⟺ PBAP_even.
- 2026-10-15 — Refined plan (route A: prove full positivity, then the corpus cone theorem).
  - (F) τ-Fubini. For an even strip function Φ with measure ν_Φ, and κ continuous with |κ(t)| ≤ C e^{−b|t|}, b > 5/4:
    L(ΦΦ^#·τ(ρ)) = ∫ τ dν_Φ, where τ(ρ) = ∫ κ(t) cos(tρ) dt. Proof: Fubini in each part of L, then Fubini against ν_Φ.
    Every even τ that is holomorphic and decaying on |Im ρ| ≤ b' (b' > 5/4) has this form, with κ = stripTest τ.
  - (R2) Consistency for multipliers: ν_{Φh} = σ_h ν_Φ. Use the shifted kernel κ_y(t) = ½(κ(t−y)+κ(t+y)), and the fact that a real
    characteristic function forces a symmetric measure, so the sine part vanishes.
  - (R3) Global ν = ν_G/σ_G. For every multiplier h: L(hh^#) = ∫σ_h dν.
    Odd forms: L(z²·(G_a g)(G_a g)^#) = ∫(ρ²−2)σ_g σ_{G_a} dν by (F) with τ = (ρ²−2)σ_g, no limit needed.
    For a general multiplier C (C = ΞP), pass to the limit in L(z² (C G_ε)(C G_ε)^#) as ε → 0: on the L side through uniform strip bounds,
    on the ν side through monotone convergence on |ρ| ≥ √2 and bounded convergence on |ρ| < √2.
  - (R4) F_j = stripTest(ΞQ_j); ΞQ_j = A_j + iz C_j with A_j, C_j even multipliers (Ξ decays on wide strips, MUST-1492).
    Σ_j w_j L(F̂_jF̂_j^#) = 0 by blindness, with absolute convergence from the growth bound (rate 5/4 > 1).
    The integrand is Σ_j w_j(σ_{A_j} + (ρ²−2)σ_{C_j}) = Ξ(iy)² Σ_j w_j p_j(y) > 0 for ρ = √(2−y²) (MUST-1488), so ν([−√2,√2]) = 0.
  - (R5) Real tests suffice (`weilPositiveFull_of_real`), and real tests split into parts (`re_weilFullFunctional_ofReal_eq_even_add_odd`).
    For an odd compact f = h′: f_ε = stripTest(f̂ e^{−εz²}). Then W(k_{f_ε}) = ∫(ρ²−2)σ dν ≥ 0, and W(k_{f_ε}) → W(k_f) by spectral dominated
    convergence plus a uniform contour bound |k_{f_ε}(x)| ≤ C e^{−b|x|}. This gives WeilPositiveFull, hence lam = Λ and RH
    (`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`).
- 2026-10-15 — R2 DONE [L] MUST-1493 (`RHTower/EvenSectorSpectralConsistency`: kernel identity and consistency; `HTGeometry/EvenSqrtHolomorphy`).
  - SIMPLIFIED ROUTE. This supersedes R3–R5 above.
  - (K) For an even strip Φ with measure ν_Φ and every multiplier T: L(ΦΦ^#·T) = ∫ T̃ dν_Φ, where T̃(ρ) = T((ρ²−2)^{1/2}). This is the kernel identity with κ = stripTest T̃.
  - Reference S(z) = sech(z/2). It is even and strip-decaying, and has no zeros. So 1/(SS^#) = cosh²(z/2) is entire, |cosh²(z/2)| ≤ e^{|Re z|}, and |cosh(z/2)| ≥ cos(Im z/2)·cosh(Re z/2).
    For any Ψ with T_Ψ := ΨΨ^#·cosh²(z/2) a multiplier: L(ΨΨ^#) = ∫ T̃_Ψ dν_S.
  - (N) Take T_j = Ξ²Q_j(z)Q_j(−z)cosh²(z/2). This is a multiplier because Ξ decays at a rate δ ∈ (1/2, π/4) on |Im| ≤ 9/4 (MUST-1492).
    Σ_j w_j L(F̂_jF̂_j^#) = 0: archPoleEnergy F_j = abelPrimePairing Λ F_j, which vanishes jointly; atomPairing vanishes by blindness after exchange.
    This needs uniform strip-5/4 bounds for ΞQ_j (Ξ rate 3/4 > (log 3)/2).
    On A' = {ρ² ≤ 2}: T̃_j = Ξ(iy)² p_j(y) cos²(y/2), with |p_j| ≤ (j!)² (dominated) and Σ_j w_j p_j ≥ √2 m₀ > 0 (MUST-1488). Ξ(iy) ≠ 0 by `XiC_I_mul_ne_zero`.
    On {ρ² > 2}: T̃_j = |ΞQ_j(r)|² cosh²(r/2) ≥ 0. Hence ν_S(A') = 0.
  - (P) For every real test with F̂ decaying faster than e^{−|x|/2} on |Im| ≤ 9/4: L(F̂F̂^#) = ∫ T̃ dν_S ≥ 0, since T̃ = |F̂(r)|² cosh²(r/2) ≥ 0 off A'. No parity split is needed.
  - (L) For compact real C² f: f_ε = stripTest(f̂ e^{−εz²}), so W(k_{f_ε}) ≥ 0 by (P). Let ε → 0 by dominated convergence:
    the pole and archimedean terms directly; the prime terms with the uniform contour bound |(1/π)∫|f̂|² e^{−2εr²} cos(r log n)| ≤ D n^{−b}, using |z² f̂(z)| ≤ ‖f″‖₁ e^{R|Im z|}.
    Then `weilPositiveFull_of_real` and `weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`.
  - Modules: M1 `EvenSectorSechRepresentation` (K, S); M2 `EvenSectorTwistedArcNull` (N, ν_S(A') = 0, P); M3 `EvenSectorFullPositivity` (L, final).
- 2026-10-15 — M1 + M2 DONE [L] MUST-1494 (`RHTower/EvenSectorSechRepresentation`, `RHTower/EvenSectorTwistedArcNull`).
  `evenWeilDensity_specSq_nonneg_of_multiplier_sechWeight`: even positivity ⟹ L(ΨΨ^#) ≥ 0 whenever ΨΨ^#cosh²(z/2) is a multiplier.
  Next: M3 (smoothing limit; WeilPositiveFull; final theorems).
- 2026-10-15 — M3 DONE [L] MUST-1495 (`RHTower/EvenSectorFullPositivity`). `weilPositiveFull_of_weilPositiveEvenAt`, `weilPositiveEvenAt_one_iff`, `riemannHypothesis_iff_primeBlindPositiveEvenAt`. Standard axioms. PROGRAMME CLOSED → 3-formalized.

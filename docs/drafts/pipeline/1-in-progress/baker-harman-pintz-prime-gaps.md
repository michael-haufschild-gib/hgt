# Baker–Harman–Pintz: primes in [x − x^{0.525}, x) (formalization programme)

- **ID:** `PRIME-GAPS-BHP-0525`
- **Stage:** 1-in-progress (scoped 2026-09-28; dependency map audited against the corpus 2026-09-28)
- **Type:** THEOREM (Lean) programme — classical theorem, formal frontier only
- **Source:** R. C. Baker, G. Harman, J. Pintz, *The difference between consecutive primes II*,
  Proc. LMS 83 (2001) 532–562 (read in full; page images in the session tool-results).
- **Statement (count form, BHP p. 562):** for large x, π(x) − π(x − x^{0.525}) ≥ (9/100)·x^{0.525}/log x.
- **Consumer:** `PrimeDeletionGreedyConstruction.greedy_chebyshev_expansion`.
  - It takes any window bound θ(y+L) − θ(y) ≥ (L − (y+L)^α)/c and needs α < 1 − κ/2.
  - With the corpus exponent (α > 0.701299) it already covers κ ∈ (½, 0.5974). So κ > ½ does **not** need BHP.
  - BHP (α = 0.525 + ε) would extend the range to κ < 0.95; a count-form Huxley 7/12 to κ < 5/6.

## Goal
Formalize BHP unconditionally, then chain windows (as in `ShortIntervalThetaEveryWindow`) into the
consumer's hypothesis at every α > 0.525.

## Gates
- [x] 0 → 1  in-progress: proof map audited against the corpus (below)
- [ ] 1 → 2  fully-proven: paper proof dependency-closed (all inputs owned or proved here)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready (not applicable: classical theorem)

## Setup (BHP §1)
- L = log x, y₁ = x·exp(−3L^{1/3}), y = x^{θ+ε}, A = [x − y, x) ∩ ℤ, B = [x − y₁, x) ∩ ℤ.
- T = x^{1−θ−ε/2}, T₀ = exp(L^{1/3}).
- Parallel Buchstab decompositions of S(A, x^{1/2}) and S(B, x^{1/2}).
- Pieces with an asymptotic formula (1.3) are kept. Positive pieces without one are discarded.
- §6 checks that the total discarded ω-integral is < 1.

## Proof map with corpus status (audited 2026-09-28)
| # | BHP item | Input | Corpus status |
|---|---|---|---|
| 1 | Lemma 1: Heath-Brown reduction of type-(2.4) polynomials | HB identity | owned: `Sieve/HeathBrownIdentity`, Maynard/Menon Heath–Brown box modules |
| 2 | Lemma 2: ∫_{U/2}^{U}\|M\|²\|K\|⁴ ≪ U^{1+ε}(1+M²U^{−1/2}) | Watt 1995 ⇐ Deshouillers–Iwaniec ⇐ Kuznetsov formula + spectral large sieve | **NOT owned; the deep core.** It is the same missing input as MT Lemma 3.5 (`matomaki-teravainen-e3-lean-programme.md`, "intermediate range N < T < 2AN'²"). The elementary ranges are owned there: `MatomakiTeravainenWattDIOverHeight`, `…WattDivisorEnergy`, `…WattDivisorRange`, `…Lemma35OverHeight`. |
| 3 | Lemmas 3–5: mean values of MN₁N₂K | Lemma 2 + MVT + sup-norm | MVT owned (`Sieve/DirichletMVT`, `DirichletMeanValueSharp`) |
| 3a | Lemma 3, case K > 4U | ‖K‖_∞ ≪ K^{1/2}/U plus sup-norm of M | **The sup-norm is not needed here.** With ∫_{U/2}^{U}\|N\| ≤ U^{1/2}(U+x/K)^{1/2}L^B (MVT), the case gives (K^{1/2} + x^{1/2}U^{−1/2})L^B ≪ x^{1/2}L^{−A} for U ≥ T₀. Same for Lemma 4's zeta-factor case. |
| 4 | Lemma 6: mean value ⇒ A-vs-B asymptotic | truncated Perron, two windows | ~owned: `MatomakiTeravainenLemma31PerronComparison` (exact two-window comparison with explicit endpoint errors), `PerronCompareLowFreq` |
| 5 | Lemma 7: Rankin tail Σ_{d\|P(w), d>D} 1/d | Mertens | to build (short) |
| 6 | Lemma 8: fundamental-lemma asymptotic (2.2) | HB 1985 Lemma 15 + Lemma 5 | to build |
| 7 | Lemma 9: large values (variant of BHP97 Thm 4, g ≤ B) | Huxley–Halász + the sup-norm hypothesis (3.11) | large values owned (`Sieve/Huxley*`, `HalaszMontgomeryDyadic`) |
| 7a | (3.11): sup_{t∈[T₀,T]} \|L(½+it)\| ≪ L^{1/2}L^{−A} for prime-type L of length ≥ x^ε | needs a zero-free region wider than Littlewood's | **owned in substance**: see "Zero-free region" below |
| 8 | Lemmas 10–11: exponent combinatorics | — | to build (pure arithmetic) |
| 9 | Lemmas 12–13: asymptotic formula (1.3) for ν ≤ ν(α) | 1–8 | to build |
| 10 | Lemmas 14–17: two-dimensional sieve | Lemma 2, MVT | to build |
| 11 | Lemma 18: region where (5.1) holds | BHP97 Lemma 1 | to build |
| 12 | §6: Buchstab decompositions, rôle reversals, regions A–F, bounds on 2–6-dimensional ω-integrals (losses 0.3, 0.06, 0.21, 0.34; margin 0.09) | certified numerics | Buchstab identity owned (`Sieve/BuchstabIdentity`, `HarmanMinorant`), MT Harman cell modules; certified integration NOT owned |

## Zero-free region: VK is not needed
Hypothesis (3.11) needs the prime-polynomial saving L^{−A} for every A at heights up to x. That
requires a zero-free width w(t) with w(t)·log t / log log t → ∞, so Littlewood's width is not
enough. The corpus already has more:
- `RouteTZetaZeroFree` / `RouteTZetaZeroFreeAbs`: an unconditional region of width
  ≍ (log t)^{−9/10}/(log log t)^{O(1)} (Chudakov strength). It is built on the corpus VMVT
  (`VinogradovMeanValueBound`) and the MV24 receivers.
- `RouteTZetaInverseBound`: 1/ζ on a fixed fraction of that width.
- `RouteTMoebiusPowerSaving`: the dyadic Möbius atom saving N^{−s/3} at every height.
- `VonMangoldtTwistUniformHeight`: ‖Σ_{n≤K} Λ(n) n^{−iτ}‖ bounded for every τ.

**Parameter change forced by the weaker exponent.** BHP's y₁ = x·exp(−3L^{1/3}) needs PNT in B with
error ≪ y₁L^{−A}. That is VK strength (error exp(−cL^{3/5−})); the corpus region gives only
exp(−cL^{1/10−}). So take instead
- T₀ = exp(L^{1/20}) and y₁ = x·exp(−3L^{1/20}).
- The Lemma 6 kernel comparison (\|t\|y₁/x ≤ L^{−A} on \|t\| ≤ T₀) still holds.
- PNT in B and in every B_{p₁…p_n} (scale ≥ x^{0.05}) holds with error exp(−cL^{1/10−}) ≪ exp(−3L^{1/20})L^{−A}.
- The sup-norm on [T₀, x] saves exp(−cεL^{1/10−}), which is super-polylogarithmic.
- Nothing else in BHP depends on T₀.
- One caveat: `VonMangoldtTwistUniformHeight`'s second term (1 + (3K)^{2w/3})/(1+\|τ\|) comes from balanced
  smoothing and is poor at low heights. The sup-norm lemma should use an unbalanced smoothing width at
  heights near T₀.

## Critical path
1. **Kuznetsov ⇒ Deshouillers–Iwaniec ⇒ Watt ⇒ Lemma 2.** No spectral-free route is known:
   - Iwaniec (Weil bound only) reaches twists of length T^{1/10}.
   - DI (Kuznetsov) reaches T^{1/5}; Watt reaches T^{1/4}, and BHP needs the full T^{1/4}.
   - Source: Bettin–Bui–Li–Radziwiłł, JEMS 22 (2020), introduction. Their Lemma 3.2 quotes Watt's
     Kloosterman-fraction bound in the form used downstream.
   - Shared with the MT programme (Lemma 3.5).
   - The Kuznetsov track is the corpus Selberg programme, `selberg-eisenstein-gamma-n-continuation.md`:
     Γ(N) Eisenstein continuation, Maass–Selberg in a region, 3/16 closed; spectral decomposition next.
   - mathlib now has the compact self-adjoint spectral theorem
     (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`, `finite_dimensional_eigenspace`).
     Its discrete-spectrum half is therefore within reach via compact automorphic kernel operators.
   - Γ₀(q) Kuznetsov can be read off Γ(q)'s spectral decomposition on the Γ₀(q)/Γ(q)-fixed subspace.
2. **Certified §6 numerics.** These are integrals of ω over polytopes. The plan:
   - bound ω piecewise (exact on [1,3], two-sided rational bounds beyond);
   - reduce to integrals of explicit elementary functions;
   - certify rational upper bounds. Any certificate generation runs on the pod.
3. **Assembly:** Lemmas 6–18 on top of the MT sieve modules.

## Kuznetsov track (K-steps; each is a multi-module project)
- K1 L²(Γ\ℍ) for finite-index Γ ⊂ SL₂(ℤ) as unions of level-one cells (the Selberg `cellP` coset model generalises).
- K2 Compact automorphic kernel operators on the cuspidal subspace (point-pair invariants, truncated kernels Hilbert–Schmidt).
- K3 Orthonormal Maass cusp basis (mathlib compact spectral theorem + simultaneous eigenfunctions).
- K4 Continuous spectrum: incomplete Eisenstein series, Eisenstein on Re s = ½ (Selberg programme), Plancherel.
- K5 Parseval for Poincaré series ⇒ Kuznetsov pre-formula (the Kloosterman side is unfolding; owned pieces: `SelbergPoincare*`, Weil bound `WeilKloostermanBound`).
- K6 Kuznetsov for general h.
- K7 Spectral large sieve with level (DI Thm 2).
- K8 DI bilinear Kloosterman estimates.
- K9 Watt's Kloosterman-fraction bound.
- K10 Twisted fourth moment (Lemma 2).

## M1a: count-form windows at every α > 5/8 (κ < 3/4), paper proof
This is the first sprint. It is independent of Kuznetsov and uses only general-coefficient large
values.

**Step 1: third-order Euler–Maclaurin.** For Re s > 0, s ≠ 1, N ≥ 1:
ζ(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − N^{−s}/2 + (s/12)N^{−s−1} − s(s+1)(s+2)·R₃(N,s),
with R₃ = Σ_{m≥N} ∫_m^{m+1} P₃(x−m) x^{−s−3} dx and P₃(u) = u³/6 − u²/4 + u/12, so \|P₃\| ≤ 1/100 on [0,1].
- Derivation: start from the corpus `zeta_eq_emCarrier_sub`, where s·emTail = s·Σ∫(x−m)x^{−s−1}.
  - Split x − m = ½ + P₂′.
  - Integrate by parts twice. P₂(u) = (u²−u)/2 and P₃ vanish at u = 0, 1, and P₂ + 1/12 = P₃′.
- Bound: \|s(s+1)(s+2)R₃\| ≤ \|s(s+1)(s+2)\|·N^{−σ−2}/(100(σ+2)).

**Step 2: detection.** Put T ≥ T₀, X = ⌊T^{1/20}⌋, N = ⌈T^{61/50}⌉. Let ρ = β+iγ be a zero with β ≥ ½ and γ ∈ [T,2T].
- The four explicit terms and R₃ in Step 1 are ≤ C T^{−1/20} at ρ, since 3 − (5/2)(61/50) = −1/20.
- \|M_X(ρ)\| ≤ 2X^{1/2} ≤ 2T^{1/40}.
- Hence 1 + Σ_{X<k≤XN} c_k k^{−ρ} = M_X(ρ)·Σ_{n≤N}n^{−ρ} has modulus ≤ ½, where
  c_k = Σ_{m\|k, m≤X, k/m≤N} μ(m), \|c_k\| ≤ d(k), and c_k = 0 for 1 < k ≤ X.
- So \|Σ_{X<k≤XN} c_k k^{−ρ}\| ≥ ½, and some dyadic block K ∈ [X, XN] (≤ 2 log T blocks) carries ≥ 1/(4 log T).

**Step 3: fixed abscissa via Taylor, not Fourier.** Split [σ,1] into slabs of width 1/log T.
- Inside the slab starting at σ_j, k^{−β} = k^{−σ_j}·Σ_i (−(β−σ_j) log k)^i/i!.
- With (β−σ_j) log k ≤ C and a truncation at i ≤ C′ log T, some polynomial
  D_{K,i}(s) = Σ_{k∼K} c_k (log k/(C log T))^i k^{−s} satisfies \|D_{K,i}(σ_j+iγ)\| ≥ e^{−C}/(8 log T).
- Coefficients stay divisor-bounded, so every loss is polylogarithmic.

**Step 4: large values** at abscissa σ, with 1-separated γ (a unit window holds O(log T) zeros).
Write K = T^κ′ and G = Σ\|a\|² ≪ K^{1−2σ}(log)^{C}.
- MVT (owned): R ≪ (T+K)K^{1−2σ}(log)^C.
- Huxley (owned, `huxley_large_values_finset_explicit_energy`): R ≪ (K^{2−2σ} + TK^{4−6σ})(log)^C, where its
  threshold holds.
- Power trick: D^ℓ has range [K^ℓ,(2K)^ℓ); use the range forms and divisor moments (owned).
- Band analysis: for every κ′ ∈ [1/20, 1.27] some power ℓ ≤ 20 lands where the bound is ≤ T^{A(1−σ)} with
  A = max(2.54, min(2/σ, 4/(3−2σ))) + ε ≤ 8/3 + ε.
- Here 2/σ (Huxley) and 4/(3−2σ) (MVT) meet at σ = ¾ with value 8/3.

**Step 5: density.** #{ρ : β ≥ σ, T < γ ≤ 2T} ≤ C T^{(8/3+ε)(1−σ)}(log T)^B uniformly for σ ∈ [½,1].
- The logarithmic, not T^ε, form matters near σ = 1.

**Step 6: transfer** via the corpus `lag_explicit_formula` (absolutely convergent ξ-zero sum). Use two adjacent
u^{−2}-weighted window averages of ψ and monotonicity of ψ:
- ψ(x+h) − ψ(x) ≥ (h − h′) − h·Σ_ρ x^{β−1} min(1, 4x²/(hh′\|ρ\|²)) − O(x^{1/2}).
- The zero sum → 0 for h = x^α, α > 5/8, by the density bound (T^{8/3+ε} ≤ x^{1−δ}), the corpus region
  (x^{−δw(T)} beats every log power), and N(T) ≪ T log T.
- Chaining windows (as in `ShortIntervalThetaEveryWindow`) and removing prime powers gives the consumer's hypothesis
  with any α > 5/8.

**Step 7:** `greedy_chebyshev_expansion` then gives κ ∈ (½, ¾).

## Milestones
- **M1a: count-form windows at α > 5/8** (paper proof above), κ < 3/4.
- **M1: count-form Huxley 7/12.** Huxley density (σ ≥ 3/4) plus Ingham density (σ ≤ 3/4), fed through a
  density-to-windows transfer. Route T's `InghamUniformDetector*` stack currently stops at σ ≥ 7/10;
  that is exactly what pins the corpus at 0.701. This milestone extends κ to < 5/6 and is independent
  of Kuznetsov.
- M2: the sup-norm lemma (3.11) at T₀ = exp(L^{1/20}) from the corpus region.
- M3: K1–K10 (shared with MT and Selberg).
- M4: BHP assembly and §6 numerics.

## Log
- 2026-09-28 — scoped in 0-backlog after `PrimeDeletionGreedyConstruction` closed κ ∈ (½, 0.5974) without BHP.
- 2026-09-28 — moved to 1-in-progress.
  - Audited every BHP lemma against the corpus (table above).
  - Findings:
    - VK is not needed: the corpus Chudakov-strength region suffices after moving T₀ to exp(L^{1/20}).
    - Lemma 3's long-zeta case needs no sup-norm.
    - Lemma 6 is MT Lemma 3.1.
    - The single deep missing input is Watt's theorem, i.e. Kuznetsov. It is shared with MT Lemma 3.5
      and is the Selberg programme's stated target.
- 2026-09-28 — M1a Lean bricks 1–3, all unconditional and wired:
  - `RHTower/ZetaEulerMaclaurinThirdOrder`: ζ(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − N^{−s}/2 + (s/12)N^{−s−1}
    − s(s+1)(s+2)∫_N^∞ P₃({u})u^{−s−3}du, with remainder ≤ \|s(s+1)(s+2)\|N^{−σ−2}/(48(σ+2)).
    It extends the corpus second-order `zeta_eq_centredTruncated_of_re_pos`.
  - `RHTower/ZetaZeroDetectionThirdOrder`: for T ≥ 2^{120}, 1 ≤ y ≤ T^{1/40} and T^{61/50} ≤ N ≤ 2T^{61/50},
    every zero with ½ ≤ β ≤ 1 and T ≤ \|γ\| ≤ 2T has \|D_N M_y(ρ) − 1\| ≥ ½ (`half_le_norm_detPolyC_of_height`).
  - `RHTower/Sieve/DirichletAbscissaTaylorSelection`: a large value V at σ₀+δ+iγ (δΛ ≤ 1) forces V/6 for a
    companion polynomial with weights (log k/Λ)^i, i < J, at σ₀+iγ, once the Taylor tail is ≤ V/2.
  - Refined Step 4. With A = 8/3 + ε₀, raise short blocks to land in [T^{2/3}, T^{4/3}] (ℓ ≤ 28).
    - On that range MVT gives T^{(5−4σ)/3} and K^{2−2σ} ≤ T^{(8/3)(1−σ)} for σ ≤ ¾ + c(ε₀).
    - Huxley gives K^{2−2σ} + T^{(11−12σ)/3} ≤ T^{(8/3)(1−σ)} for σ ≥ ¾, and its threshold holds for σ ≥ ¾ + c(ε₀)/2.
  - Next: zero-copy selection (1-separated ordinates, `ncard_xiOrdinateWindow_one_le_log`); block powers
    (`dirPoly_convPow`, `sum_card_divisors_pow_le_polylog`); density; transfer.

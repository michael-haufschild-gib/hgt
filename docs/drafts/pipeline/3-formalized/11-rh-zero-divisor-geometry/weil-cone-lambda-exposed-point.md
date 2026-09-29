# Λ is an exposed point of the full Weil cone (Riemann-kernel supporting hyperplane)

- **ID:** weil-lambda-exposed-point
- **Stage:** 3-formalized (paper and Lean, 2026-09-29)
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/mc-conjecture-loop-2026-09-28.md`, cycles 143–146; strengthens `weil-cone-lambda-extreme-point.md` (MUST-524) and MUST-527(a)
- **Statement:** Let `K = Φ ⋆ Φ̃ > 0` be the autocorrelation of Riemann's kernel, and `ℓ(v) = Σ_{n≥2} v(n) n^{−½}(K(log n) + K(−log n))`.
  - (a) Every Weil-positive `lam` (full cone: pole weight 1, all `C²` compactly supported tests) satisfies `ℓ(lam) ≤ ℓ(Λ)`, unconditionally and with no growth hypothesis.
  - (b) If `Σ|lam(n) − Λ(n)| n^{−σ} < ∞` for every `σ > 1` and `ℓ(lam) = ℓ(Λ)`, then `lam = Λ` on `n ≥ 2`.

## Goal
Λ uniquely maximizes the explicit linear functional `ℓ` over the Weil cone. So the cone lies in a half-space whose boundary it touches only at Λ.
- Majorant rigidity follows at once: `K > 0`, so a majorant direction has `ℓ(w) > 0` unless `w = 0`.
- So does extremality: `ℓ(w) ≤ 0` and `ℓ(−w) ≤ 0` force `ℓ(w) = 0`.
- **Non-circularity.** (a) holds whether or not RH does.
  - (a) and (b) combine to give RH ⟺ some Weil-positive `lam` in the class has `ℓ(lam) = ℓ(Λ)`, in which case `lam = Λ`.
  - The weights `K(log n)` decay like `e^{−2πn}`, so `ℓ` sees essentially `lam(2), lam(3), lam(4), …` with super-exponentially decreasing weights. Matching Λ's value of this one number forces all of `lam` to equal Λ.

## Proof
- **(a)** Take `u = Φχ_L`, the truncated kernel.
  - The explicit formula gives `0 ≤ Re W(u,u) − T_w(u)`, with `T_w(u) = Σ w(n)n^{−½}(k_u(log n) + k_u(−log n))` and `w = lam − Λ`.
  - `Φ̂ = Ξ` vanishes at every zero, so `|W(u,u)| ≤ (5/4)S_Z E_L² → 0`.
  - The truncated autocorrelation converges: `|T_w(u) − ℓ(w)| ≤ K₀e^{−2(L−1)}`, using `Σ|w(n)|/n² < ∞`. That sum is finite by the level-wise box `|lam(n)| ≤ √n(log n + C₀)`, since full-cone positivity implies polar positivity.
  - Hence `ℓ(w) ≤ 0`.
- **(b)** Take `f = u + εH`, `H` smooth and compactly supported.
  - Expand: `T_w(f) = T_0 + 2εT_1 + ε²T_2 ≤ (5/4)S(E_L + |ε|E_H)²`.
  - `T_0 → ℓ(w) = 0` and `T_1 → T_w(Φ, H)`, for both signs of `ε`. So `T_w(Φ, H) = 0` for all `H`, i.e. `∫ H G_w = 0`.
  - Hence `G_w(s) = Σ w(n)n^{−½}(Φ(s+log n) + Φ(s−log n)) ≡ 0`, and the Riemann-kernel transform is injective (odd theta relation plus Hamburger). So `w = 0`.

## Lean
- `RHTower/WeilFullConeExposedPoint` (519 lines), standard axioms, wired:
  - `weilFullCone_exposed_at_vonMangoldt` ((a) and (b));
  - `atomPairing_riemannKernelAutocorr_nonpos_of_weilPositiveFull` ((a) with no hypothesis);
  - `eq_vonMangoldt_of_weilPositiveFull_of_atomPairing_eq_zero` ((b));
  - `weilPositive_of_weilPositiveFull` (full ⇒ polar positivity);
  - `riemannKernelAutocorr_pos`.
- Built on `RHTower/WeilFullConeExtremePoint` (859 lines) and `RHTower/RiemannKernelTransformInjectivity` (530 lines).

## Novelty
- The free-weight Weil cone is not studied in the literature.
- The corpus had extremality (MUST-524, paper; formalized in cycle 145) and constant-sign rigidity (MUST-527), but no supporting hyperplane.
- The exposing functional is explicit and built from Riemann's own kernel. The mechanism (the first variation at a positive near-null vector) is new.

## Limits
- (b) needs `Σ|lam − Λ|n^{−σ} < ∞` for `σ > 1` because the formal Hamburger lemma needs it. The box bound gives only `σ > 3/2`.
- Does not touch existence (PBAP, MUST-523) or the RH-hard producer side.

## Gates
- [x] 0 → 1, 1 → 2: paper proof above.
- [x] 2 → 3: Lean (above).

## Log
- 2026-09-29 — cycle 146: conjectured, proved and formalized in one pass.

# GHS inequality for Riemann's Ξ

- **ID:** xi-magnetization-ghs-concavity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** goal-loop row 963 · MUST-1249 · route-candidates rows 608, 706 (Griffiths–Simon lane)
- **Statement:** `m(w) = (ξ'/ξ)(½ + w)` is concave on `[0, ∞)`, unconditionally. Equivalently, every rightward exponential tilt of Riemann's measure `Φ(u)du` has nonpositive third cumulant.

## Goal
GHS is a necessary condition for `Φ` to be a Griffiths–Simon limit of ferromagnetic block spins. A failure would kill the Lee–Yang producer lane unconditionally. The theorem shows it passes. The corpus previously had the sign only at `w = 1` (`thetaCuspSafeTiltThirdCumulant_neg`).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: zero side + Gamma–prime side, below
- [x] 2 → 3  formalized: `RHTower.concaveOn_xiRealLogDeriv`, module `RHTower/XiMagnetizationGHSConcavity`, standard axioms, wired
- [ ] 3 → 4  not pursued (no stage 4)

## Approach (as formalized)
- **`0 < w ≤ √120`:** `m'' = 2w(−3 Re M₁ + 4w² Re M₂)` with `M_n(y) = Σ_q (y + ρ_c²)^{−(n+1)}`. Each atom obeys `4y Re s³ < 3 Re s²`. With `A = y + Re ρ_c² > y + 42` and `B² < A + ¼`, the polynomial inequality `4yA(A² − 3B²) < 3(A⁴ − B⁴)` follows from `3A − 4y ≥ 6`. Inputs are the height gap `γ² > 9769/231` and `|β| < ½`.
- **`w ≥ 17/2`:** `m = [1/(s−1) − Σ_{k=1}^{7} 1/(s+2k)] − log π/2 + ½ψ(s/2 + 8) + ζ'/ζ(s)`, with `s = ½ + w`.
  - The finite part has `f'' ≤ 0` for `s ≥ 9`, because `Σ_{k=1}^{7} (8/(9+2k))³ > 1`.
  - `ψ` is concave via the Mittag-Leffler series.
  - `ζ'/ζ = −Σ Λ(n) n^{−s}` is concave.
- **Glue:** antitone derivative on `[0, 9]` and on `[9, ∞)`.

## Reusable Lean
`concaveOn_tsum`, `concaveOn_re_digamma`, `concaveOn_re_logDeriv_riemannZeta`, `deriv2_xiRealLogDeriv_eq` (all `w > 0`), `hasDerivAt_deriv_xiRealLogDeriv`, `xiRealLogDeriv_eq_ghsGammaPrimeForm`.

## Reading
- Real-axis convexity is unconditional and cannot by itself detect zeros.
- Every single-variable Griffiths–Simon necessary condition tested so far holds for `Φ`: Lee–Yang is RH, while Lebowitz `κ₄ < 0` and GHS both hold. So the GS lane's open core is constructive only.
- Under RH, `m'' ≈ −12wΣγ^{−4}` for `w ≪ γ₁`. Asymptotically `m'' ≈ −1/(2w²)` (Gamma).

## Log
- 2026-10-11 — created at stage 3 (MUST-1249).
- 2026-10-11 — value correlation: the corpus already shows that the theta source `Φ` (in the log variable) has `(log Φ)''' < 0` on `(0, ∞)` and `(log Φ)'''' < 0` everywhere (`thetaCuspLogCurvatureJet_pos_of_pos`, `thetaCuspLogCurvatureJetTwo_pos_all`). So `V = −log Φ` has `V'` convex on `[0, ∞)`, which is the Ellis–Newman sufficient condition for GHS. Riemann's `Φ` is therefore an Ellis–Newman (GHS-class) single-spin measure, and every ferromagnetic system of `Φ`-spins satisfies GHS. MUST-1249 is a direct `ξ`-side proof of the single-site case that does not use Ellis–Newman's theorem (which is not formalized).

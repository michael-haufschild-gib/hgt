# Even pole-weight window: does even positivity at some β force RH?

- **ID:** even-window-c892
- **Stage:** 1-in-progress (Lean: MUST-1504, 1509, 1510)
- **Type:** CONJECTURE
- **Source:** producer-loop-opus-2026-10-12.md C892, rows 1067–1070; rh-goal-loop-opus-2026-09-29.md rows 1252–1261
- **Statement:** If real weights lam are Weil-positive at some pole weight β on every autocorrelation of an EVEN compactly supported C² test, then RH holds and lam = Λ on n ≥ 2. Equivalently RH ⟺ ∃β PBAP_even(β), i.e. the even window is empty without RH.

## Goal
MUST-1500 shows the even window lies in [1, ∞), and that without RH it is empty or a half-line strictly to the right of 1. C892 rules out the half-line. At β = 1 the statement is MUST-1495. For β > 1 even positivity is strictly weaker than full positivity, because the pole term of a non-even test has no sign.

## Proved [L]
- MUST-1504: Λ is even-positive at β iff RH and β ≥ 1.
- MUST-1509: at every β, even positivity gives
  - growth `|lam(n)| ≤ C√n log n`;
  - pole-free strip positivity;
  - cosine-shift measures of pole-free strip functions;
  - positivity on every resonator `Σ c_k g(· − x_k)` with `c_k ≥ 0` and an even polar-free profile `g`;
  - the log-density ceiling of Λ.
  No representation at general β is needed (pole-free bypass).
- MUST-1510: majorants are pinned. If lam ≥ Λ is even-positive at some β, then lam = Λ. Hence RH ⟺ some majorant of Λ is even-positive at some β.

## Open cores
- [OPEN CORE A] Super-pole / minorant side. Exclude weights with a real pole of `L_lam` in (1, 3/2] of negative residue (`lam ≈ Λ − m n^{s₁−1}` on average), together with a residue excess at s = 1 (row 1257). This is a crystalline-absorber statement: a Dirichlet series with such a pole and critical-line real part ≤ πZ.
- [OPEN CORE B] Atom identification. In the β-representation the pole points ±i/2 map to `ρ_P = √7/2`. The atom of the representing measure there should be `(β − r)κ`, with r the residue of `L_lam` at s = 1 (Stieltjes inversion of the even Herglotz function). With r ≤ 1 and no super-pole, rows 1253–1254 give C892.
- [OPEN CORE C] Riesz profile step (row 1258 (3)), for the far-bump route. It is needed only if B is bypassed.

## Approach
- Minorant side: combine the ceiling with lower information. Low-frequency pole-free even tests see the negative archimedean symbol, which forces lam to carry Λ's mass at low frequency.
- Try to show that an even-positive minorant deviation `v = lam − Λ ≤ 0` (or one with a negative-residue real pole) contradicts pole-free positivity on Ξ-divisible even tests.

## Log
- 2026-10-15 — created (rows 1260–1261) after MUST-1509/1510.
- 2026-10-15 (row 1262) — Minorant side analysed; it reduces to super-pole exclusion.
  - Exact identity [P]: Σ_{j≥1} w_j W_lam(F_j) = 2w₀ Σ v(n) n^{−½} k₀(log n). Its left side uses the pole-free shifted-Gamma members `ΞQ_j`, j ≥ 1.
  - The combined lift `S₁` is negative exactly on the super-pole region `½ < |y| ≤ √2`. So every even-positive minorant carries super-pole mass.
  - Polar second differences detect only isolated deficits, never deficit densities.
  - Even tests are blind to positive segment atoms in principle, so arithmetic (the crystalline absorber) is required.
- 2026-10-15 (loop row 1266, plan) — **Abel pinning: C892 for every even-positive system without super-pole or negative double pole.**
  - Statement: lam even-positive at some β, with (H1) `Σ|lam(n)|n^{−σ} < ∞` for all σ > 1 and (H2) `liminf_{s→0⁺} s²F(s) ≥ 0`, `F(s) = Σ_{n≥2} lam(n)n^{−1−s}`, then lam is even-positive at β = 1, so RH ∧ lam = Λ (MUST-1495). Nonnegative weights satisfy H1 (ceiling, MUST-1509) and H2. So RH ⟺ ∃β ∃lam ≥ 0 even-positive at β. Every fake must violate H1 (super-pole) or H2 (negative double pole at s = 1).
  - Proof: for a real even test g with `P = ∫g e^{−x/2}`, the test `G_a = g − c_a e_a` (`e_a = φ(·−a) + φ(·+a)`, `c_a = P/((e^{a/2}+e^{−a/2})J)`) is pole-free, so even positivity at β gives `W₁(G_a) ≥ 0`. Expand: `W₁(g) ≥ 2P² − 4c_aT(a) + 2c_a²S(a) − O(|c_a|)`, where `T(a) = Σ lam(n)n^{−1/2}h(log n − a)` (`h = g ⋆ φ̃`) and `S(a) = Σ lam(n)n^{−1/2}k(log n − 2a)` (`k = φ ⋆ φ̃`). Average against `s e^{−sa}(1+e^{−a})²`. The Laplace transforms factor, `∫T e^{−(1/2+s)a} = H(s)F(s)` and `∫S e^{−(1+s)a} = ½K(s/2)F(s/2)`, with `H(0) = PJ`, `K(0) = J²`. So the profile drops out in Abel means (this closes row 1258 (3)): `W₁(g) ≥ P²(2 − 4X(s) + 2X(s/2)) − o(1)` with `X(s) = sF(s)`. The ceiling gives `limsup X ≤ 1`. If `W₁(g) < 0`, then `2X(s) − X(s/2) ≥ 1 + η` near 0, and iterating along `s₂/2^k` gives `s_kX(s_k) ≤ −c < 0`, which contradicts H2.

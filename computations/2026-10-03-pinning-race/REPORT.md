# Pinning race: joint widths of the finite-level Weil cone W_L (2026-10-03)

## CORRECTION (read first)
The joint widths below are values of a log-barrier path. They are **not verified suprema**:
- Coordinates near the support edge (n ≈ e^L) are nearly free, so the barrier never centres (it drifts along them).
- At L = 2.0 (order 8) a full-space iterate is verified feasible (min eigenvalue 3e-32 > 0) with δ₂ = 1.85e-14, which exceeds the "relaxation width" of 1.79e-14 below.
- So the numbers are neither upper bounds nor converged. Only the cubic-spline boxes that match the Arb-certified dual certificates (L = 2, n = 2, 3) are trustworthy.
- **Box scan result.** With `|y_n| ≤ B` on the other coordinates, the L = 2.0 order-8 δ₂ supremum is 4.6e-15 (B = 1e4, box active), then 1.876e-14, 1.851e-14, 1.851e-14 (B = 1e6, 1e8, 1e10; box inactive, centring capped).
  - So the supremum is finite (≈ 1.87e-14), and the table values are 3–10% underestimates. Orders of magnitude and L-trends stand.
  - The values are still not certified upper bounds.

## What was computed
- `W_L = {lam : Q_lam(f) ≥ 0 for every test f = Σc_iB_i}`, with `B_i` B-splines of order `P` and spacing `hk` on `supp f ⊂ [−L/2, L/2]`. Here `Q_lam` = pole + archimedean (x-space digamma formula) − `2Σ lam(n) n^{−1/2} g(log n)`. Coordinates are `δ_n = Λ(n) − lam(n)`, `n ≤ e^L`.
- **Method (`pinrace.py`, `hpweil.py`).** All matrices are built in mpmath at 60–80 digits.
  - Eigendecompose `Q_Λ`. Keep its `k` lowest eigen-directions and rescale them to the identity: `I + Σ δ_n A_n ⪰ 0`.
  - Run a high-precision log-barrier Newton method for `max ±δ_{n0}`. This is the "joint" width, with all other `δ_n` free.
  - The "single" width is the same with all other `δ_n = 0`.
- **Validity.** Dropping eigen-directions or test functions only enlarges `W_L`. So every number below is an **upper bound** on the true `W_L` width, hence a pinning bound for every producer (full-cone Weil-positive `lam`, including any real-rooted twin `Λ_F/k`). The numbers are high-precision floating point, not interval-certified.
- **Calibration.** `P = 4, hk = 0.05, L = 2` reproduces the Arb-certified boxes of `certified-producer-pinning.md` exactly (n = 2: `[−3.48e-10, 2.43e-9]`).

## Results (joint widths `[lo, hi]` of `δ_n`)
| L | basis (P, hk, m) | λ_min(Q_Λ) | n=2 | n=3 | n=4 | n=5 | n=7 |
|---|---|---|---|---|---|---|---|
| 2.0 | 4, .05, 37 | 6.0e-12 | [−3.5e-10, 2.4e-9] | [−3.8e-8, 1.3e-8] | [−3.4e-7, 8.6e-7] | [−2.8e-5, 1.2e-5] | edge |
| 2.0 | 8, .05, 33 | 2.2e-19 | [−2.7e-16, 1.8e-14] | [−6.6e-12, 1.3e-13] | [−9.5e-11, 3.9e-9] | [−5.4e-6, 2.6e-7] | edge |
| 2.4 | 4, .05, 45 | 1.5e-12 | [−1.9e-10, 1.5e-9] | [−1.6e-8, 4.6e-9] | [−6.6e-8, 1.9e-7] | [−1.7e-6, 7.4e-7] | [−1.5e-4, 1.3e-4] |
| 2.4 | 4, .025, 93 | 7.2e-15 | [−7.9e-13, 6.9e-12] | [−5.7e-11, 1.9e-11] | [−2.5e-10, 5.8e-10] | [−5.1e-9, 2.5e-9] | [−2.7e-7, 2.3e-7] |
| 2.4 | 6, .05, 43 | 4.6e-17 | [−4.5e-14, 1.8e-13] | [−4.5e-12, 3.1e-12] | [−1.3e-10, 1.4e-10] | [−5.2e-9, 4.6e-9] | [−1.6e-5, 1.8e-5] |
| 2.4 | 6, .035, 64 | 9.0e-19 | [−4.0e-16, 1.7e-15] | [−3.4e-14, 2.6e-14] | … | … | … |
| 2.4 | 8, .05, 41 | 7.3e-21 | [−2.8e-17, 3.7e-16] | [−1.9e-14, 4.6e-15] | [−6.4e-13, 1.4e-12] | [−1.75e-10, 1.1e-10] | [−1.4e-5, 1.1e-5] |
| 2.8 | 8, .05, 49 | 4.4e-22 | [−7.6e-18, 4.4e-17] | [−3.5e-15, 8.6e-16] | [−6.5e-14, 1.8e-13] | [−9.1e-12, 3.8e-12] | [−2.1e-8, 1.1e-8] |
| 2.8 | 4, .05, 53 | 4.7e-13 | [−2.8e-10, 1.8e-9] | [−1.6e-8, 5.6e-9] | [−8.2e-8, 1.5e-7] | [−1.7e-6, 9.4e-7] | [−1.1e-4, 1.3e-4] |

## Interpretation
- **Basis-limited, not converged.** At fixed L, every basis upgrade shrinks the widths by about 10²–10⁴, and `λ_min(Q_Λ)` keeps falling. At L = 2.8 with cubic splines the widths do not improve over L = 2.4: the basis caps them, not the mathematics. The true W_L widths are smaller than every number here.
- **Pinning wins the race at accessible L.** With order-8 splines at fixed basis, L = 2.0 → 2.4 shrinks the joint widths by 50 (n = 2), 350 (n = 3), 2800 (n = 4) and 3·10⁴ (n = 5).
- **Cross-talk.** The amplification (joint width / single-coordinate width) is 10²–10⁶. It grows with n and with basis quality. Single-coordinate pinning is easy (near-null energy). Joint pinning pays a large but finite cross-talk factor, and joint widths still fall quickly with L.
- **Profile in n.** At L = 2.4, P = 8, `log₁₀ w_n ≈ −15.4, −13.7, −11.8, −9.8, (−4.9 at n = 7)`, about +1.8 decades per unit n. This is consistent with Riemann-kernel visibility `K(log n) ~ e^{−2πn}` (2.7 decades per unit n).
- **Twins (ℤ/3 torsion locks).** Every real-rooted `F ∈ V₃` has `|Λ_F(n)/3 − Λ(n)| ≤ 3.7e-16, 1.9e-14, 1.4e-12, 1.75e-10, 1.4e-5` for n = 2, 3, 4, 5, 7 (not certified).

## Order-8 series (fixed basis `hk = 0.05`), max |δ_n|
| n | L = 2.0 | 2.4 | 2.8 |
|---|---|---|---|
| 2 | 1.8e-14 | 3.7e-16 | 4.4e-17 |
| 3 | 6.6e-12 | 1.9e-14 | 3.5e-15 |
| 4 | 3.9e-9 | 1.4e-12 | 1.8e-13 |
| 5 | 5.3e-6 | 1.75e-10 | 9.1e-12 |
| 7 | edge | 1.4e-5 | 2.1e-8 |

The gain per +0.4 in L shrinks for small n (×50 then ×8 at n = 2), which points to the fixed basis as the limit. Larger n keep large gains.

## Dual certificate (S30)
The n0 = 2 certificate at L = 2.4 (P = 8): ĝ* dips at ζ-zeros (14.13, 21.0, 30.4, 48.0) but decays like a spline transform, and ĝ*/Ξ² grows by ~10²⁸ on [10, 80]. Finite-level certificates are not Riemann-kernel based (forced by compact support). Code: `dualcert.py`. Its central-path dual was not fully centred.

## Combined basis (cubic ∪ order-8 LMIs, block-diagonal; `pinrace_dump.py` + `pinrace_comb.py`, flint log-barrier)
Here the cubic block bounds the edge coordinates, so the barrier centres. L = 2.0: all converged. L = 2.4 and 2.8: some final centring steps capped; the values are feasible near-suprema.

| L | log₁₀ max\|δ_n\| for n = 2, 3, 4, … |
|---|---|
| 2.0 | −14.7 −12.7 −10.3 −7.5 −3.7 +0.5 |
| 2.4 | −15.8 −14.4 −12.6 −10.9 −9.0 −7.0 −4.8 −2.2 +1.3 (n = 11 free) |
| 2.8 | −16.9 −15.1 −13.5 −12.1 −10.8 −9.5 −8.3 −7.1 −6.0 −4.8 −3.7 −2.0 +0.5 +3.4 +7.1 |

- **Pinned fraction** n*/e^L: 0.68/0.64/0.61 (θ = 1e-6), 0.81/0.73/0.73 (θ = 1e-3), 0.81/0.82/0.79 (θ = 1).
- **Self-similar profile.** `log₁₀ w(n, L) ≈ −19.5 + s(L)·n/e^L`, with s = 18, 20, 22. The intercept is the basis floor (λ_min(Q_Λ) 2e-19 → 4e-22).
- The unpinned edge layer has log-width ≈ 0.2, the cubic-spline support (4·hk). It is a basis effect: refinement shrinks it.
- **Reading.** At accessible L the race is won with a stable margin. Each fixed n is pinned once `e^L ≳ 1.3n`, and its width then falls to the basis floor. Twin consequence (numerical): `|Λ_F(n)/3 − Λ(n)|` ≤ 1.6e-16 (n = 2), 4.3e-15 (n = 3), 2.6e-13 (n = 4), 1.2e-11 (n = 5), 9.7e-10 (n = 6), 9.4e-8 (n = 7) at L = 2.4.

## L = 3.2 (combined basis, 36/38 runs not fully centred, so the values are feasible near-suprema)
log₁₀ max|δ_n|, n = 2..20: −16.7 −15.4 −13.9 −12.6 −11.3 −10.2 −9.1 −8.1 −7.1 −6.2 −5.3 −4.4 −3.5 −2.6 −1.7 −0.8 +0.2 +1.0 +1.5.

- Pinned fraction: 0.45 (θ = 1e-6), 0.57 (1e-3), 0.69 (1), **down** from 0.61/0.73/0.79 at L = 2.8.
- The n = 2 width did not improve (−16.7 vs −16.9): the fixed hk = 0.05 basis has hit its floor.
- **Verdict on S34: not established.** At fixed basis the fraction declines, because the profile steepens while the floor stays put. Deciding the race needs hk → 0 jointly with L. The earlier "stable fraction" reading (L ≤ 2.8) was premature.

## Refinement hk = 0.05 → 0.035 (combined basis)
log₁₀ max|δ_n| drops by ≈ 2.5–3 decades uniformly in n:
- L = 2.4: n = 2 −15.8 → −18.8, n = 7 −7.0 → −10.1;
- L = 2.8: n = 2 −16.9 → −19.4, n = 10 −6.0 → −8.5;
- L = 3.2: n = 2 −16.7 → −19.4, n = 15 −2.6 → −5.6.

| L | pinned fraction θ = 1e-6 | θ = 1e-3 | θ = 1 |
|---|---|---|---|
| 2.4 | 0.64 → 0.73 | 0.73 → 0.82 | 0.82 → 0.91 |
| 2.8 | 0.61 → 0.67 | 0.73 → 0.79 | 0.79 → 0.91 |
| 3.2 | 0.45 → 0.57 | 0.57 → 0.73 | 0.69 → 0.82 |

**Final verdict for this method.**
- Widths scale roughly like `hk^{16–19}`, i.e. (order-8 approximation error)². They are entirely basis-limited.
- At fixed hk the pinned fraction declines with L, because the small-n widths hit the floor. Refinement raises it everywhere.
- Spline SDPs cannot decide the asymptotic race. That needs spectral bases tuned to the near-null space (Riemann-kernel functions) or an analytic argument.
- Numerical twin constraint (refined, L = 2.8): `|Λ_F(n)/3 − Λ(n)| ≲ 10^{−19.4}, 10^{−17.7}, 10^{−16.2}, 10^{−14.7}` for n = 2..5. Not certified.

# Multi-prime Putnam: Lee–Yang zero sets are not contained in the zeros of ζ

- **ID:** mpp-lee-yang
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Bohr card rows 63–64 (MUST-719, MUST-722); Kurasov–Sarnak / Lee–Yang zero sets
- **Statement:** For real `a` with `|a| < 1` let `P_a(s) = 1 + a(2·4^{−s} + 3·9^{−s}) + 6·36^{−s}`. Every zero of `P_a` lies on `Re s = ½`, and some zero `ρ` of `P_a` has `ord_ρ ζ < ord_ρ P_a`.

## Goal
A Putnam-type theorem for quasi-periodic sets: the zero set of `P_a` is the set of times `t` at which the Kronecker line `(2t log 2, 2t log 3)` meets a smooth curve on the 2-torus. For `a ≠ 0` it is not a finite union of arithmetic progressions, so Putnam's theorem (corpus `XiNoArithmeticProgression`) does not apply. This is an unconditional statement about ζ.

## Proof (paper)
1. **Lee–Yang.** With `u = 4^{½−s}`, `v = 9^{½−s}`: `P_a = 1 + a(u + v) + uv`. On `Q(u,v) = 0` we have `v = −(1+au)/(a+u)`, and `|1+au|² − |a+u|² = (1−a²)(1−|u|²)`. Hence `|u| < 1 ⇒ |v| > 1` and `|u| > 1 ⇒ |v| < 1`. But `|u| = 4^{½−σ}` and `|v| = 9^{½−σ}` lie on the same side of 1. So `P_a ≠ 0` off `σ = ½`.
2. **Self-reciprocity.** `6^s P_a(s) = 6^s + 6^{1−s} + a(2(3/2)^s + 3(2/3)^s)` is invariant under `s ↦ 1−s`.
3. Suppose `ord_ρ ζ ≥ ord_ρ P_a` at every zero `ρ` of `P_a`. Then `F(s) := 6^{−s} ζ(s)/P_a(s)` is meromorphic on `ℂ` with poles only at `s = 0, 1` after completion. Write `1/P_a = Σ e_n n^{−s}`, a geometric series for large `Re s`. Then `F = Σ_n (1∗e)(n) (6n)^{−s}` is an ordinary Dirichlet series, absolutely convergent for large `Re s`.
4. **Functional equation.** `Γ_ℝ(s)F(s) = ξ_ζ(s)/(6^s P_a(s))` is symmetric under `s ↦ 1−s`, i.e. the completed functional equation of ζ, with conductor 1.
5. **Decay on the strip.** `s(s−1)Γ_ℝ(s)F(s) = 2ξ(s)/(6^s P_a(s))` is an entire quotient of order-one functions, so it has order ≤ 1. Bound it on `Re s = −½` and `3/2`: there `|P_a| ≥ c > 0` (step 1 and compactness of the torus) and `ξ` decays like `e^{−π|t|/4}`. Phragmén–Lindelöf on the strip, after twisting by `e^{∓iπs/4}`, gives `O(|t|^k e^{−π|t|/4})` inside. Hence `E = Γ_ℝF − αΓ_ℝ(s) − βΓ_ℝ(s−1)` is `O(1/(1+t²))` on `−½ ≤ Re s ≤ 3/2`.
6. **Hamburger** (corpus `HTGeometry.coeff_eq_of_completed_functional_equation`) gives `F = cζ`. Then `6^{−s} = c P_a(s)`, but `P_a` has constant term 1 and `6^{−s}` has none, so `c = 0` and `F = 0`. That contradicts `Res_{s=1} F = 1/(6 P_a(1)) ≠ 0`, since `P_a(1) = 1 + a(½ + ⅓) + ⅙ > 0`.

## Lean plan
Corpus assets: Hamburger (above), `OrderOneEntireQuotient`, `GammalessStripRigidity.orderOneGrowth_phragmenLindelof_strip`, `RectangleResidue`, xi strip decay (`SelbergThetaHorizontalBoundary.xi_strip_decay`). New: the Lee–Yang lemma, the self-reciprocity identity, the Dirichlet expansion of `1/P_a`, and the order-one envelope of `ξ/(6^s P_a)` (the quotient has zeros, so `OrderOneEnvelope.of_entire_quotient` needs the zero-carrying version, or the finite-order variant `FiniteOrderEnvelope.of_entire_quotient`).

## Relation to the RH program
No RH leverage. It is the ζ-side complement of MUST-719/722: the critical zeros carry no crystalline structure on `log ℕ`. Kept in backlog because the producer cores (Q_ann, PBAP) take priority.

## Lean status (2026-10-03)
- [L] `RHTower/ZetaZerosLeeYangQuasicrystal.lean`: Lee–Yang zero location (`re_eq_half_of_leeYang_eq_zero`), edge bounds `|Y_a| ≥ 11/6` on `Re s ∈ {3/2, −½}` and `|Y_a| ≥ 1−|a|` at `Im s = 2πk/log 6`. Standard axioms only. Wired into `RHTower.lean`.
- Not formalized: steps 3–6 (Dirichlet inverse, strip bound, Hamburger). Verdict on the full statement: BRIDGE — a corollary of Hamburger's theorem (equivalently the conductor-1 case of Kaczorowski–Perelli's degree-1 classification). No RH leverage; parked.

## Lean status (2026-10-03, complete)
- `RHTower.LeeYang.exists_analyticOrderAt_xi_lt_leeYang` (`|a| < 1`): some zero `ρ` of `Y_a` has `Re ρ = ½` and `ord_ρ ξ < ord_ρ Y_a`.
- `RHTower.LeeYang.exists_cos_add_cos_eq_zero_riemannZeta_ne_zero` (`|a| ≤ 4/5`): some real `t` has `cos(t log 6) + a cos(t log(3/2)) = 0` and `ζ(½+it) ≠ 0`. Zeros are simple there because `L₁ ≥ 1`, `L₂ ≤ ½`, `|sin(tL₁)| ≥ 3/5`.
- Modules (standard axioms; wired in `RHTower.lean` after `ZetaZerosLeeYangQuasicrystal`):
  - `RHTower/ZetaZerosLeeYangQuasicrystal` (Lee–Yang zero location, edge bounds).
  - `RHTower/ZetaZerosLeeYangDirichletSeries` (495 lines). It contains the inverse recursion `e(n) = −2a e(n/4) − 3a e(n/9) − 6e(n/36)`, the partial-sum bound `Σ|e(n)|n^{−σ} ≤ 1/(1−θ(σ))`, the identity `6^sP_a = 2√6 Y_a`, and `exists_coeff_dirichlet_zeta_div_leeYang`.
  - `RHTower/ZetaZerosLeeYangPutnam` (790 lines). It contains the strip decay of `ξ/Y_a` by maximum modulus on the bands `[2πk, 2π(k+1)]/log 6`, Γ_ℝ strip decay via `Γ(w) = Γ(w+1)/w`, the stripped quotient `E` with the poles at `0, 1` removed by `dslope`, and the Hamburger contradiction `c(1) = 0 = −2α`.
- Reusable: `exists_quotient_bound_strip` turns edge lower bounds of a divisor of `ξ` into strip decay of the quotient, and `exists_pow_mul_exp_le` gives `x^N e^{−πx/4} ≤ B/(1+x²)`.
- Verdict unchanged: BRIDGE (corollary of Hamburger). No RH leverage.

## Generalisation (2026-10-14, MUST-1406 [L])
- `RHTower.StablePutnam.exists_zero_stableDirichlet_riemannZeta_ne_zero`: for every real multiaffine `Q` in any number `k ≥ 1` of variables, stable on the open polydisc, self-reciprocal, with `Σ_{S≠∅}|q_S/q_∅|Π_{j∈S}n_j^{−1} < 1`, the critical zeros of `P(s) = Q(n^{½−s})` are not all zeros of `ζ`. Instance `exists_zero_leeYang_riemannZeta_ne_zero`: bases `2, 3`, all `|a| < 1`.
- Route (the one proposed at Bohr-card row 64): `H = Σ log n_j(½ − z_j∂_jQ/Q)` is Herglotz by stability, has `Re H = 0` on the line off the zeros of `P` by self-reciprocity, and is a Dirichlet series with constant `½Σ log n_j`. The general Herglotz carrier theorem `RHTower.AtomDomination.eq_zero_of_herglotz_dirichlet_criticalCarrier` (Herglotz explicit formula + MUST-722 + Poisson support lemma) then gives the contradiction. No Bohr heights, no band-wise maximum modulus, no Hamburger.
- Verdict unchanged: BRIDGE.

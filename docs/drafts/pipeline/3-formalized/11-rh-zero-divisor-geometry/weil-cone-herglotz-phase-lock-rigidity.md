# Phase-locked Herglotz producers are Λ, and RH follows

- **ID:** weil-cone-herglotz-phase-lock-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** krein-producer-loops L237 · STATUS MUST-617
- **Statement.** Let `Σ_n |lam(n)| n^{−σ} < ∞` for `σ > 1`, and let `Φ` be the Herglotz form of `lam`:
  - `Φ` is holomorphic on `Re s > ½`, with `Re Φ ≥ 0` there;
  - `Φ = Γ̃ + 1/(s−1) − Σ_{n≥2} lam(n)n^{−s}` on `Re s > 1`.

  Let `G` solve `G' = ΦG` on `Re s > ½`, be continuous on `Re s ≥ ½`, and satisfy `G(2) = 2Γ_ℝ(2)exp(Σ lam(n)n^{−2}/log n)`.
  If `G(½ − iy) = κG(½ + iy)` for all `y > Y` (some `Y ≥ 0`, `κ ≠ 0`), then `lam(n) = Λ(n)` for every `n ≥ 2`, and RH holds.
  - For real `lam`, `G(s̄) = conj G(s)`. So the hypothesis says that **the phase of the producer's exponential on the critical line is eventually constant mod π**.
  - **Approximate lock** (`phase_lock_rigidity_of_defect`): it suffices that `G(1−s) = κ^{−1}G(s) + s(s−1)Γ_ℝ(s)e(Im s/2)` on the lower half-line `s = ½ + 2iτ`, `τ < −Y`, with `e` polynomially bounded and Abel-sublinear (`δ∫‖e‖e^{−δ|t|} → 0`). With `κ = 1` this is the producer corollary of MUST-603 (phase defect `o(T)` ⇒ `Λ`), now formal for every Herglotz producer.
  - Nothing is assumed about the boundary (Weil) measure — atomic, absolutely continuous or singular — beyond continuity of `G` up to the line.

## Goal
State the uniqueness mechanism of MUST-608/612/613 for an arbitrary Herglotz producer, not only atomic ones. Then the atomic and fractional theorems are instances: there `G` is an explicit product.

## Gates
- [x] 0 → 1
- [x] 1 → 2: L237.
- [x] 2 → 3: `RHTower.PhaseLockRigidity.phase_lock_rigidity` (module `RHTower/WeilHerglotzPhaseLockRigidity.lean`, 671 lines; also `phase_lock_rigidity_of_defect`).
  - `lake env lean` is clean; `#print axioms` gives propext, Classical.choice, Quot.sound; the module is wired into the RHTower umbrella.
- [ ] 3 → 4

## Proof (as formalized)
1. **`G = s(s−1)Γ_ℝ(s)exp(Σ lam(n)n^{−s}/log n)` on `Re s > 1`.** Equal logarithmic derivatives and equal value at `2` (`G_eq_bigG`).
2. **No zeros on `Re s > ½`.** On a disc around a point of the half-plane, `Φ` has a primitive `F` (Morera, `DifferentiableOn.isExactOn_ball`). Then `G e^{−F}` is constant, so a zero would kill `G` on the disc and, by the identity theorem, on the half-plane, contradicting `G(2) ≠ 0` (`G_ne_zero`).
3. **Growth.** `Re Φ ≥ 0` gives `|G(σ+iτ)| ≤ |G(2+iτ)|` (`norm_G_le_two`). With Stirling at `σ = 2` and the lower bound for `Γ_ℝ` on the line, this gives decay of `E` and polynomial bounds on the boundary value and the reflection defect.
4. **Twisted Hamburger** (MUST-612): on the lower half-line `G(1−s) = κ^{−1}G(s)`. So the coefficients of `exp(Σ lam(n)n^{−s}/log n)` all equal `2κβ = 1`, the series is `ζ`, and `lam = Λ`.
5. **RH.** `G = s(s−1)Λ(s)` on `Re s > ½` (identity theorem), and `G` has no zero there.

## Reading
- **Must:** a full-cone producer other than `Λ`, with continuous boundary values, has an exponential whose critical-line phase never settles mod π.
- With L224 Lemma C (`∫e^{2πiN_ν}|F|²w = 2πΣ(b⋆b)w(2πn)`): such a producer's phase decorrelates from `|F|²`, or its mean square is super-Lindelöf.
- This is the strongest uniqueness statement reachable without the Ω input.

## Log
- 2026-10-01 — created at stage 3

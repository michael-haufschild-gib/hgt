# Almost-periodic locks force the true producer

- **ID:** ap-lock-true-producer
- **Stage:** 1-in-progress
- **Type:** THEOREM (unconditional), HF uniqueness half, lock classification
- **Parent:** `3-formalized/almost-periodic-lock-closure.md` (MUST-1391: weighted AP locks force RH)
- **Loop row:** 1154 (Opus RH goal loop)

## Statement
Let `G` be a Herglotz producer for the weights `lam` with lower-line lock
`G(1 − s) = V(s) G(s)`, `s = ½ − iy`, `y > 0`, `V(s) = Σ_j c_j u_j^{−(s−½)}`, with
- (W) `Σ_j |c_j| max(1, u_j^{−1}) K(u_j) < ∞` (the MUST-1391 weight), and
- (L) `Σ_j |c_j| |log u_j| < ∞` (log moment; makes the line lock `C¹`).

Then `lam(n) = Λ(n)` for all `n ≥ 2`, and RH holds.

So the only Herglotz producer with a weighted almost-periodic lock is the true one. This answers the
frontier-map item "two-sided rational spectra with positive mean motion remain": no lock in the
weighted AP class has positive mean motion.

## Proof (paper)
Write `Z(s) = s(s−1)Γ_ℝ(s)ζ(s)` (entire, `Z(1 − s) = Z(s)`), `v(y) = V(½ − iy)`, and `g = Im(v' v̄)`
for the lock velocity.

0. **Factorization.** The MUST-1391 chain (M1 → rational part → MUST-1385) gives `A`,
   holomorphic on `Re s > ½`, continuous on `Re s ≥ ½`, `|A| ≤ W` there, with `G = Z A` on
   `Re s > ½`, `s ≠ 1`. (`A` is the trivial-class series; the bound is `Σ_q 8^{ω(q+1)} B_q`.)
1. **Anchor.** On `Re s > 1`, `F = ζ A` with `F = exp(Σ lam(n) n^{−s}/log n)`. So there is
   `σ₀ > 1` with `|A − 1| ≤ ½` on `Re s ≥ σ₀`.
2. **A-lock.** `G = Z A` extends to the line by continuity. Dividing the lock by `Z(½ − iy) ≠ 0`
   (true off a discrete set) and using continuity gives `A(½ + iy) = V(½ − iy) A(½ − iy)` for all
   `y > 0`.
3. **Gluing.** `E(z) = A(z)` for `Re z ≥ ½` and `E(z) = V(1 − z) A(1 − z)` for `Re z < ½` is
   continuous on `Ω = {−½ < Re z < 3/2, Im z > 0}` by step 2, holomorphic off the line, hence
   holomorphic on `Ω` (Painlevé). `|E| ≤ W max(1, C_V)` with `C_V = Σ |c_j| max(1, u_j^{−1})`.
4. **Choice of ε.** `δ(ε) = Σ |c_j| |u_j^{−ε} − 1| → 0`. Fix `ε ≤ ¼` with `δ(ε) ≤ ½`. Since
   `|v| = 1`, `V_ε(y) = V(½ + ε − iy)` has `|V_ε − v| ≤ ½`, so `|V_ε| ≥ ½`. Hence `E` has no zero on
   the line `Re z = ½ − ε`, where `E = V_ε A(½ + ε − i·)`.
5. **Backlund–Jensen.** For heights `Y` with no zero of `E` on `[½ − ε, σ₀] + iY`:
   `|∫ Im(E'/E)(x + iY) dx| ≤ (N₀ + 1)π`, with `N₀` independent of `Y`. Use the auxiliary
   function `g_Y(z) = (E(z + iY) + conj E(z̄ + iY))/2`, which equals `Re E(x + iY)` on the real
   axis, is bounded by `W_E`, and has `g_Y(σ₀) ≥ ½`. Jensen counts the zeros of `g_Y`, and the
   Backlund step finishes. The same holds for `A` on `[½ + ε, σ₀] − iY`, with a ball inside
   `Re > ½`.
6. **Two rectangles.**
   - `E` on `[½ − ε, σ₀] × [Y₀, Y]`, by the argument principle with `N ≥ 0` zeros:
     `∫ Re(E'/E)(left) = ∫ Re(E'/E)(right) + Bot − Top − 2πN`.
     On the left edge, `E'/E(½ − ε + iy) = −(V'/V + A'/A)(½ + ε − iy)`.
   - `A` on `[½ + ε, σ₀] × [−Y, −Y₀]`, which is zero-free: Cauchy.
   - Combining the two:
     `∫_{Y₀}^{Y} Im(V_ε'/V_ε) = S⁺ + S⁻ + Bot − Top + Bot' − Top' − 2πN ≤ C₁`,
     where `|S^±| < π` because `Re A > 0` on `Re = σ₀`.
7. **Comparison.** `h = v · conj V_ε` has `Re h ≥ ½`. So
   `∫_{Y₀}^{Y} g = [Im log h] + ∫ Im(V_ε'/V_ε) ≤ π + C₁`.
8. **End.**
   - `g ≥ 0` (positivity law), and good heights are cofinal (`E` has finitely many zeros in each
     compact box). So `∫_0^T g` is bounded, and the window means of `g` tend to `0`.
   - `g` is almost periodic, so `g ≡ 0` and `v` is constant.
   - `phase_lock_rigidity` then gives `lam = Λ` and RH.

**Mechanism.** Herglotz positivity pushes the lock phase up (`g ≥ 0`). The zeros of the glued
function near the line push it down (`−2πN`). The anchor `A → 1` makes every other term bounded.
So the mean motion is `0`.

## Lean plan
- Refactor MUST-1385/1391: export the factorization (`limitPeriodic_producer_factor`,
  `almostPeriodicLock_factor`).
- New module (generic): local rectangle argument principle (non-entire), vertical Painlevé,
  Backlund–Jensen bound for conjugate-symmetrized auxiliaries.
- New module: the gluing `E`, the phase bound, and the theorem
  `almostPeriodicLock_trueProducer`.

## Log
- 2026-10-13: card created; paper proof complete (steps 0–8). Lean started.

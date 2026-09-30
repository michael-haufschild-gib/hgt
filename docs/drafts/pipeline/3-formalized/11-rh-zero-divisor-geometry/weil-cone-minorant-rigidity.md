# No Weil-positive completion minorizes Λ (full cone, Herglotz-free)

- **ID:** L156 / weil-cone-minorant-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** hf-positive-hodge-attack/krein-producer-loops.md (L156); frontier map row "Downward uniqueness `lam=Λ` remains Lean-open"
- **Statement:** If `lam` is full-cone Weil-positive and `lam(n) ≤ Λ(n)` for every `n ≥ 2`, then `lam = Λ` on `n ≥ 2`. No sign, growth or summability condition on `lam` is needed.

## Goal
This closes the downward half of order rigidity in the full Weil cone, with no Herglotz representation. With upward rigidity (`eq_vonMangoldt_of_weilPositiveFull_of_ge`), `Λ` is order-isolated: no Weil-positive system is comparable with `Λ` unless it equals it. Corollary: RH ⟺ some full-cone Weil-positive `lam ≤ Λ` exists. The earlier minorant criterion needed `0 ≤ lam`.

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven (paper proof below)
- [x] 2 → 3 formalized: `RHTower.eq_vonMangoldt_of_weilPositiveFull_of_le` and `RHTower.riemannHypothesis_iff_exists_weilPositiveFull_le` in `formal/GaloisForLFunctions/RHTower/WeilFullConeMinorantRigidity.lean`. `lake build` is green, axioms are `[propext, Classical.choice, Quot.sound]`, and the module is lint-clean and wired into `RHTower.lean`.
- [ ] 3 → 4 (not pursued: no-stage-4 directive)

## Paper proof

**Notation.**
- `Φ` is Riemann's kernel; `φ₁(u) = e^{5u/2}(4π²e^{2u} − 6π)e^{−πe^{2u}}` is its lead cusp term.
- `K(y) = ∫Φ(t)Φ(t−y)dt`. `u_L = Φχ_L`, and `K_L` is the autocorrelation of `u_L`.

1. **Sandwich** (`riemannKernelReal_sandwich`). For `u ≥ 0`, `φ₁(u) ≤ Φ(u) ≤ (101/100)φ₁(u)`.
   - The cusp term `m ≥ 2` is at most `2m⁴e^{−π(m²−1)}φ₁(u) ≤ 32e^{−9}2^{−(m−2)}φ₁(u)`.
   - The tail is therefore at most `64e^{−9}φ₁ ≤ φ₁/100`.
   - The bound extends to all real `u` because `Φ` is even.
2. **Exact shift law for `φ₁`** (`riemannLeadTerm_shift_mul_le`). For `x = e^{2h} ≥ 2`, `φ₁(|s+h|)φ₁(|s−h|) ≤ R(x)φ₁(|s|)²`, where `R(x) = e^{−π(x−1)}((4π²x−6π)/(4π²−6π))²`. Write `Z = e^{2s}`.
   - Case `s ≥ h`, with `Y₁Y₂ = Z²`. AM–GM gives `(pY₁−q)(pY₂−q) ≤ (pZ−q)²`, and `Y₁+Y₂−2Z = Z(x−1)²/x ≥ (x−1)²`.
   - Case `s < h`, with `Y₁Y₂ = x²`. AM–GM gives `(pY₁−q)(pY₂−q) ≤ (px−q)²`, and `(pZ−q)² ≥ (p−q)²`.
   - In the second case the exponent obeys `5(h−s) − πe^{2(h−s)} − π(x−2)Z ≤ −π(x−1)`, since `π(e^{2d}−1) ≥ 2πd ≥ 5d`.
3. **Kernel inequality** (`sum_riemannAutocorr_log_le`). By the change of variables `t = s + h` and steps 1–2, `K(log n) ≤ (101/100)²R(n)K(0)`.
   - Bernoulli, `π > 3.14` and `e^π ≥ 22.5` give `R(n) ≤ (19/50)8^{2−n}`.
   - Hence `Σ_{2≤n≤N}K(log n) ≤ (101/100)²(19/50)(8/7)K(0) ≤ (23/50)K(0)`.
4. **Test** (`logShiftRiemannDifference`). Take `f = u_L − u_L(·−c)` with `c = log m`.
   - Its transform is `(1−e^{izc})û_L`. Since `|1−e^{izc}| ≤ 1+√m` on the strip, `‖W(f,f)‖ ≤ (1+√m)²·(5/4)S·E_L²`.
   - Its autocorrelation is `2K_L(y) − K_L(y+c) − K_L(y−c)`.
5. **Window.** `K_L` vanishes for `|y| ≥ 2L`, so the atoms that matter are `2 ≤ n ≤ N = ⌊e^{2L}⌋`.
   - Let `v(n) = (Λ(n)−lam(n))/√n ≥ 0`, and let `m` maximize `v` on the window.
   - Positivity gives `0 ≤ ‖W‖ + Σ_n v(n)[4K_L(log n) − 2K_L(log n+c) − 2K_L(log n−c)]`.
   - Hence `2v(m)K_L(0) ≤ ‖W‖ + 4v(m)(23/50)K(0)`.
6. **Limit.**
   - `K_L(0) ≥ (24/25)K(0)` for large `L` (Gaussian tail of `Φ`).
   - `e^{2L}·(5/4)S·E_L² → 0` (`exists_exp_mul_nearRadicalEnergy_le`: `E_L² ≲ e^{−e^{2L−2}}`).
   - With `v(m) ≥ v(n₀) > 0` this gives `(2/25)v(m)K(0) ≤ v(n₀)K(0)/25`, a contradiction.

## What is new
- **The kernel inequality.** `Σ_{n≥2}K(log n) < K(0)/2` for Riemann's kernel. `Φ` is incoherent against the prime lattice `log ℕ`: its log-integer shifts carry under half of its energy. This is proved pointwise via an exact shift law for the lead cusp term, with no lower bound on `∫Φ²`.
- **The window-argmax device.** It removes every sign or growth hypothesis on `lam`. The zero-side cost `(1+√m)²` is paid by the super-exponential near-radical decay.
- **The downward uniqueness itself.** It was listed as Lean-open, and the paper route went through regular rigidity (HF-F54).

## Log
- 2026-09-30 — L156: conjecture, paper proof and Lean module in one cycle; moved straight to 3-formalized.

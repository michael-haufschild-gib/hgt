# Certified pinning of every Weil-positive integer weight system at small primes

- **ID:** certified-producer-pinning
- **Stage:** 1-in-progress (computer-assisted proof complete for `L = 13/10, 8/5`; Lean not started)
- **Type:** THEOREM (computer-assisted, interval arithmetic)
- **Source:** spark loop S4/S9 (`spark-conjecture-loop-2026-10-03.md`). Complements `R:WeilPositivityBeurlingPerturbationRigidity` [L], which excludes only finite-mass perturbations of `Λ`.
- **Statement.**
  - Let `L > 0`, `hk = L/(m+3)`, and let `B_i` (`i = 0..m−1`) be the cubic B-splines with knot spacing `hk` centred at `x_i = −L/2 + 2hk + i·hk`. They are `C²` with support in `[−L/2, L/2]`.
  - For `λ : ℕ_{≥2} → ℝ` and `f = Σ c_i B_i`, put `g = f*f̃` and `h = |f̂|²`, and define
    `Q_λ(f) = h(i/2) + h(−i/2) − g(0) log π + (1/2π)∫ h(r) Re ψ(1/4 + ir/2) dr − 2 Σ_{n≥2} λ(n) n^{−1/2} g(log n)`.
  - If `Q_λ(f) ≥ 0` for all such `f`, then `δ_n := λ(n) − Λ(n)` lies in the certified box:

    | L | m | n | certified range of δ_n |
    |---|---|---|---|
    | 13/10 | 23 | 2 | [−5.077e-6, 7.522e-8] |
    | 13/10 | 23 | 3 | [−5.515e-4, 5.954e-3] |
    | 8/5 | 29 | 2 | [−6.197e-9, 3.135e-9] |
    | 8/5 | 29 | 3 | [−5.567e-7, 3.747e-7] |
    | 8/5 | 29 | 4 | [−1.581e-4, 2.964e-4] |
    | 9/5 | 33 | 2 | [−1.063e-8, 8.65e-10] |
    | 9/5 | 33 | 3 | [−5.81e-8, 3.54e-7] |
    | 9/5 | 33 | 4 | [−2.91e-5, 9.96e-6] |
    | 9/5 | 33 | 5 | [−1.10e-2, 1.55e-2] |

    | 2 | 37 | 2 | [−2.427e-9, 4.20e-10] |
    | 2 | 37 | 3 | [−1.278e-8, 3.79e-8] |
    | 2 | 37 | 4 | [−8.56e-7, 3.43e-7] |
    | 2 | 37 | 5 | [−1.162e-5, 3.078e-5] |
    | 2 | 37 | 6 | [−4.21e-3, 1.275e-3] |

  At `L = 9/5`, λ(6) sits at the support edge and is unconstrained. Every producer satisfies every box, so the boxes intersect.

## Goal
- **First non-perturbative pinning.** Every producer (integer-supported, full-cone Weil-positive weight system for ζ's archimedean datum with the pole) agrees with the von Mangoldt function at 2, 3 and 4 to the stated precision. No smallness or finite-mass assumption on `λ − Λ` is made, so infinite-mass deviations are covered.
- **Twins.** For any real-rooted `F ∈ V_k` (functional equation of ζᵏ, pole order k, conductor 1, `f_1 = 1`), `Λ_F/k` is a producer (C394 R1). Hence `|Λ_F(2) − k log 2| ≤ 6.2e-9·k`, `|Λ_F(3) − k log 3| ≤ 5.6e-7·k`, `|Λ_F(4) − k log 2| ≤ 3e-4·k`.
- Quantitative evidence for C-PIN (`W ⊆ {Λ}`), whose truth would imply C329 and RH ⟺ PBAP.

## Proof (computer-assisted)
1. **Validity of the functional.**
   - `Q_Λ(f) = Σ_γ h(γ)` (explicit formula) was checked numerically to 1e-13 with 2000 zeros. Only the definition above is used in the proof; the explicit formula is not used.
   - **Archimedean term.** It is evaluated in x-space by `(1/2π)∫ h Re ψ(1/4+ir/2) dr = −γ g(0) + 2∫_0^∞ [g(0)e^{−2x} − e^{−x/2} g(x)]/(1 − e^{−2x}) dx`.
     - This follows from `ψ(z) = −γ + ∫_0^∞ (e^{−t} − e^{−zt})/(1 − e^{−t}) dt` (Re z > 0) and Fubini.
     - `g` is piecewise polynomial (order-8 B-splines). Each knot interval is integrated with `acb.integral` (Arb, 256 bits).
     - The removable singularity at 0 is handled by `[0, 10^{−30}·hk]` with the explicit bound `|integrand| ≤ 2 + 4/hk`.
     - The tail beyond the support is `−(g(0)/2) log(1 − e^{−2X})`.
2. **Certificates.**
   - PSD `X = Σ_k w_k v_k v_kᵀ` with rational `w_k ≥ 0` and rational `v_k`: rounded SDP dual matrices plus near-null eigenvectors.
   - For a producer, `0 ≤ Σ_k w_k Q_λ(v_k) = q(X) − Σ_n δ_n m_n(X)` with `m_n(X) = Σ w_k (2/√n) g_{v_k}(log n)`, all evaluated in Arb.
3. **Elimination.** Rational LP multipliers combine the inequalities into `δ_{n0}·C_{n0} + Σ_{n≠n0} δ_n C_n ≤ Q`. Each cross-coefficient is below 1e-12 relative.
   - Bootstrap: `M := max_n |δ_n| ≤ max |Q|/(|C_{n0}| − Σ_{n≠n0}|C_n|)`, valid whenever every denominator is positive (checked in Arb).
   - Then `±δ_{n0} ≤ (Q + Σ_{n≠n0}|C_n| M)/|C_{n0}|`.
4. All quantities are Arb intervals. The asserted inequalities are checked on interval endpoints. Code: `computations/2026-10-03-certified-pinning/certpin.py`.

## Gates
- [x] 0 → 1 in-progress
- [ ] 1 → 2 fully proven: independent re-run with a second spline family.
  - Convention audit done: `EF.gammaBracket r = Re ψ(1/4 + ir/2) − log π` (`R:WeilFullConeHerglotzRightHalfPlane.gammaBracket_eq`). `weilFullFunctional` has exactly the pole, prime and archimedean terms of `Q_λ`, so `WeilPositiveFull λ` implies every certificate inequality.
- [ ] 2 → 3 formalized: certified Weil-functional evaluation for explicit spline tests in Lean (corpus precedent: `R:PoleVanishingWeilTraceCertificate`).

## Log
- 2026-10-03 — certified boxes for `L = 13/10, 8/5, 9/5, 2`. The composite weight is certified: every producer has `|λ(6)| ≤ 4.3e-3`, so positivity forces the Euler-product support at 6.
- 2026-10-03 — Lean plan (gate 2 → 3), queued.
  - Coarse target: `WeilPositiveFull λ → |λ 2 − log 2| ≤ 1/20` from two explicit spline tests at `L = 1`.
  - Needs certified upper bounds on `Q_Λ(f±)`, via the x-space archimedean formula and series of `poly·e^{−cx}` with rational tail bounds; reuse `R:DigammaVerticalMinimum` and `R:PoleVanishingWeilTraceCertificate`.
  - The fine boxes above need Arb-level precision and stay computer-assisted.
- 2026-10-03 — Next-cycle check: a semigroup/divisibility attack on PBAP is blocked by the gate "Mellin-diagonal inputs are blind" (KR-R2; the Hecke semigroup acts by characters).
- 2026-10-03 — **v2 (computations/2026-10-03-certified-pinning-v2).** Combined cubic + order-8 test spaces at L = 2, high-precision flint-barrier duals, Arb verification at 400 bits.
  - Certified δ_n = λ(n) − Λ(n): n = 2 [−2.13e-15, 1.74e-16]; n = 3 [−5.54e-14, 2.11e-13]; n = 4 [−4.83e-11, 2.41e-11]; n = 5 [−2.22e-8, 3.29e-8]; n = 6 [−1.80e-4, 1.31e-4]; n = 7 [−2.27, 2.85].
  - This is 5–6 orders tighter than v1 at n = 2, 3, and matches the barrier optimum, so the certificates are sharp for this basis.
  - Twins: `|Λ_F(2) − 3 log 2| ≤ 6.4e-15`. Integer-coefficient twins have f₂..f₆ = d₃(n).

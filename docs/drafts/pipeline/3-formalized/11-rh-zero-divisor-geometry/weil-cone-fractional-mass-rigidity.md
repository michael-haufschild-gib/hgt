# Finitely many non-integer spectral masses force Λ and the Riemann hypothesis

- **ID:** weil-cone-fractional-mass-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** krein-producer-loops L235, L236 · STATUS MUST-613
- **Statement.** Let `Σ_n |lam(n)| n^{−σ} < ∞` for `σ > 1`. Suppose that on `Re s > 1`
  `Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n)n^{−s} = 2(s−½)Σ_j m_j/((s−½)² + t_j²) + Σ_{k<J} c_k·2(s−½)/((s−½)² + u_k²)`,
  with integers `m_j ≥ 0` at ordinates `t_j ≥ 1` (`Σ m_j/t_j² < ∞`) and finitely many real masses `c_k ≥ 0` at ordinates `u_k ≥ 1`.
  Then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann hypothesis holds.
  - The real masses may be irrational, and their sum need not be an integer.
  - So an atomic producer other than `Λ` needs **infinitely many** non-integer masses, and in fact non-integer cumulative mass at arbitrarily large heights.

## Goal
Extend MUST-608 (every mass an integer) to "integer outside a bounded set". This closes the "finitely many irrational masses" part of the irrational-mass door of the producer map.

## Gates
- [x] 0 → 1
- [x] 1 → 2: L235 paper proof (Corollary B).
- [x] 2 → 3: `RHTower.FractionalMassRigidity.fractional_mass_rigidity` (module `RHTower/WeilFractionalMassAtomicRigidity.lean`, 1157 lines), on top of `RHTower/WeilIntegerMassAtomicRigidity` and `RHTower/HamburgerTwistedCriticalLine`.
  - `lake env lean` is clean; `#print axioms` gives propext, Classical.choice, Quot.sound; the module is wired into the RHTower umbrella.
  - Reusable: `exists_lower_bound_Gammaℝ_half_line` (`c e^{−π|v|/4} ≤ (1+|v|)^M ‖Γ_ℝ(½+iv)‖`, by the reflection formula and Stirling for `Γ(¾ − iv/2)`), `norm_sin_le_exp_abs_im`, `cpow_I_mul_ofReal`.
- [ ] 3 → 4

## Proof (as formalized)
1. **Real-mass factor.** For each real atom take `((s − ½ + iu)/u)^c((s − ½ − iu)/u)^c` with principal powers. Both bases lie in the closed right half-plane on `Re s ≥ ½`. So the factor is holomorphic on `Re s > ½` and continuous on `Re s ≥ ½`, including at the atom (`c ≥ 0`). Its logarithmic derivative is `c·2(s−½)/((s−½)² + u²)`. It satisfies `R(s̄) = conj R(s)` (`fracPair_conj`).
2. **`G = KQR`.** `G(s) = s(s−1)Γ_ℝ(s)exp(Σ lam(n)n^{−s}/log n)` has the same logarithmic derivative as `QR` on `Re s > 1`, where `Q` is the integer-mass product of MUST-608 (`bigG_eq_ghatF`).
3. **Phase.** On the line above every `u_k` both bases are positive multiples of `i`, so `conj R(½+iy) = e^{−2πiC}R(½+iy)` with `C = Σc_k` (`conj_fracProd_of_gt`). Below every atom the factor is `e^{2πiC}`. With `Q(1−s) = Q(s)` and `1 − s = s̄` on the line: `Ĝ(1−s) = κĜ(s)`, `κ = e^{−2πiC}`, above; `κ^{−1}` below.
4. **Growth.** `Re Φ ≥ 0` gives `|Ĝ(σ+iτ)| ≤ |Ĝ(2+iτ)|` on `½ ≤ σ ≤ 2` (continuity up to the line suffices). Stirling at `σ = 2` and the lower bound for `Γ_ℝ` on the line then give the decay of `E` and polynomial bounds for the boundary value `Φ` and the defect `g`.
5. **Twisted Hamburger** (MUST-612) makes the coefficients of `exp(Σ lam(n)n^{−s}/log n)` equal to `2κβ`, hence all equal to `1`. So this series is `ζ` and `lam = Λ`.
6. **RH.** `KQR = s(s−1)Λ(s)` on the connected half-plane `Re s > ½` (identity theorem from `Re s > 1`), and `QR` has no zero there.

## No-go closure
- **Killing mechanism:** finitely many fractional atoms change the phase of the completed function by an eventually constant amount, which the twisted Hamburger theorem cannot see.
- **Strongest positive survivor:** the theorem itself. Quantitative form [P]: with a remainder in the twisted theorem, fractional tails with `Σ_{t_j>T}dist(c_j, ℤ) = O(T^{−3/4−η})` are covered, using `|F(½+it)| ≪ |t|^{3/4}` from positivity.
- **New insight:** a non-Λ atomic producer must have phase `e^{2πiN_ν(t)}` that keeps moving at large heights. By L224 Lemma C it must then decorrelate from `|F|²` (no phase locking) or have super-Lindelöf mean square.
- **Status:** Lean complete. Remaining atomic door: infinitely many non-integer masses with non-converging cumulative phase.

## Log
- 2026-10-01 — created at stage 3

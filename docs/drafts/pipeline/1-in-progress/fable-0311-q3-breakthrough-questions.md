# Review-0311 fable §4 (Q3): breakthrough questions below RH

- **ID:** F0311-Q3
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** `docs/reports/review-0311/fable.md` §4.1–4.5
- **Statement:** Give a complete, Lean-formalized answer to each §4 question.

## Questions

| # | Question | Owner folder | Status |
|---|---|---|---|
| 4.1 | First prime stage: Weil positivity on windows `A ∈ [2·enlargedWeilFloorAperture, log 3)` (contraction form) | `GrowingWindowsOfSpecZ/` / `WindowTowerOfSpecZ/` | open |
| 4.2 | PM: sign of the retained `T₂` boundary coefficient read off `Re s − ¼` | `RenormalizedIntersectionTheory/MayerScattering/` | answered, Lean: `3-formalized/retained-hecke-channel-reads-the-quarter-line.md` |
| 4.3 | MC: explicit gauge point, not Dirichlet, not Tate, with Möbius exponent `½` | `ArithmeticGaugeTheory/` | answered, Lean: `3-formalized/explicit-gauge-point-with-exponent-one-half.md` |
| 4.4 | WD: `D_win` at fixed depth | `RHTower/WD/` | open (see `r0311-breakthrough-questions.md` ledger rows 3–24) |
| 4.5a | HF: inputs on `mp`, `m` fixed, `p ∤ m` growing: is `e_m` retained with vanishing energies? | `CriticalScaleArithmeticRigidity/` | test answered (yes, every `m`), Lean: `3-formalized/fibre-charges-survive-vanishing-energy.md`; complete-form evaluation (scalar: `ReceivingCharges/PrimeChargeCompleteEnergy`, fibres: `ReceivingCharges/CoprimePrimeCharge*`) is being written by a non-Claude agent on the Q6 card; do not edit that folder |
| 4.5b | HF: whole-space PD at `c = 2K(log N)^{1/8}` for every `(2K)^8 < R₀` | `CriticalArithmeticCorrelationTheory/` | open |
| 4.5c | HF: quantitative window threshold `R₁(A)` beyond the proved lengths | `ArithmeticHodgeTheoryOfDegenerations/` | framework answered (R₁ = exact critical multiple, order, floors, RH ⟺ R₁ ≡ ⊤), Lean: `3-formalized/the-critical-threshold-of-a-window.md`; `R₁(A) = ⊤` beyond `2·enlargedWeilFloorAperture` is 4.1 (open) |

## 4.3 — answer (paper)

Base `y₀ = dirichletGauge χ₄ + ℓ` (Liouville twin of `χ₄`): Möbius exponent `≤ ½`
(`gaugeExponent_moebius_liouvilleTwin_dirichletGauge_le_half`).

1. **Sparse invariance.** If `x, x'` agree off a prime `p`, then
   `S_{x'}(N) = S_x(N) − (χ_{x'}(p) − χ_x(p)) A_x(⌊N/p⌋)` and `A_x(0) = 0`, so a bound
   `|S_x| ≤ C(N+1)^θ` gives `|S_{x'}| ≤ C(1 + K_θ p^{−θ})(N+1)^θ`, `K_θ = 2·4^θ/(1 − 2^{−θ})`.
   Iterating over the primes `≤ N` of a set `P` with `Σ_{p∈P} p^{−θ} ≤ B`: factor `≤ exp(K_θ B)`.
   Hence agreement off a `θ`-summable set transports power bounds of exponent `θ`.
2. **Blocks.** `P_k` = the first `2^k` primes in `(4^k, 2·4^k]` (all of them if fewer). For
   `θ > ½`, `Σ_{p∈P_k} p^{−θ} ≤ (2^{1−2θ})^k`: geometric.
3. **Signs.** At `N_k = 2·4^k` every squarefree `n ≤ N_k` divisible by `p ∈ P_k` equals `p`. With the
   blocks `< k` set and the base on `P_k`, `S_{new}(N_k) = A_k − u_k#P_k`,
   `A_k = S_{old}(N_k) + Σ_{p∈P_k} χ_{old}(p)`. Choose `u_k = −i·sgn(Im A_k)`: `|S(N_k)| ≥ #P_k`.
4. **Exponent.** Eventually `#P_k = 2^k` (`N/(2log N)` primes in `(N, 2N]`), so `|S(N_k)| ≥ √(N_k/2)`:
   exponent `≥ ½`; by 1–2 exponent `≤ ½`.
5. **Not special.** At every prime `p ≡ 1 (mod 4q)` the point takes a value in `{−1, ±i}`, while
   `dirichletGauge ψ + verticalShift t` takes `p^{it}`. Two such primes force `p^{4it} = 1` for both,
   hence `t = 0`, hence value `1`: contradiction at infinitely many primes.

## Ledger

| # | Conjecture | Result |
|---|---|---|
| 1 | 4.3 via the Liouville twin of a Dirichlet point | exponent `≤ ½` proved, but `≤ 5/12` under RH: not `½` |
| 2 | 4.3 non-adaptive: fixed phase `i` on sparse blocks | needs explicit base constants and tower growth; replaced by adaptive signs (no constant enters the definition) |
| 3 | 4.2: sign from the full-core defect `D_s(ψ_s)` | sign-blind: `≤ 0` on both sides, `= 0` iff `Re s = ¼` (corpus); the side is carried only by the retained `T₂` channel, `D_s(u_s) = |core_s(2)|² Φ(Re s)` |
| 4 | 4.2: sign from `|core_s(2)|` vs `|core_{½−s̄}(2)|` | no exact law: `ζ(ρ − 1)` and `ζ(−ρ̄)` are related by the functional equation only through `ζ(2 − ρ)`, `ζ(1 + ρ)`; abandoned for the defect formulation |
| 5 | 4.1 by perturbation from the strict floor `1/8000` at `2·enlargedWeilFloorAperture` | fails: dilation or translation moves the archimedean (log-kernel) and lag terms by amounts controlled only by `‖H'‖`, which `Q` does not dominate; no openness of window positivity in `A` |
| 6 | 4.1 as the `{∞,2}` semilocal form below its death length | the semilocal family dies at length `≈ 1.115` (`e^{A}≈3.05`, corpus numerics), margin at `log 3` is `≈ 5.6·10⁻⁸` (even) / `1.5·10⁻⁵` (odd): any certificate must be exact to that order; no structural slack |
| 6b | 4.1 via index ≤ 1 (cosh hyperplane) plus one Schur direction | numerics (Legendre basis K=22, `uv`+scipy): min normalized eigenvalue of `W` on windows of length `L`: `5.1e−4` (0.75), `1.9e−4` (0.80), `1.7e−5` (0.90), `1.0e−6` (1.00), `3.7e−7` (1.04), `1.2e−7` (1.08), `6.2e−8` (1.098); on the cosh hyperplane `3.2e−2`, `1.5e−2`, `2.5e−3`, `2.1e−4`, `6.7e−5`, `2.6e−5`, `1.7e−5`. Even the hyperplane margin collapses below `10⁻⁴` past `L = 1`: no slack-based certificate (perturbative, Kron, floor + kick) can reach `log 3`; only an exact identity can |
| 6c | 4.1 by comparison with Weil RH for the elliptic curve `E: y²+y = x³+x+1` over `𝔽₂` (`#E(𝔽₂) = 1`, `Z = (1−2T+2T²)/((1−T)(1−2T))`): genus 1 kills the archimedean term, and `Λ_E(2) = N₁ log 2 = Λ(2)`, so on windows of length `< log 4` the prime terms coincide and `Q_ζ = W_E + D`, `W_E = Σ_{zeros of E}|Ĥ|² ≥ 0` (Hasse), `D = arch_ζ − Σ_{k≠0}[ĝ(ωk+i/2) + ĝ(ωk−i/2)]`, `ω = 2π/log 2` | explicit formula of `E` verified numerically (rel. err. `10⁻⁹`); `min W_E ≈ 0.41` on every window `0.72–1.098`, but `min D ≈ −1.4 … −2.36`: fails. Lesson: a comparison form `P ≤ Q_ζ` must be as critical as `Q_ζ` (`min ≈ 6·10⁻⁸` at `log 3`); curve forms keep an `O(1)` margin. Survivor: on first-stage windows (`< log 4`) Weil's form is a curve zero-sum plus a prime-free archimedean form — an exact identity, not a sign |
| 7 | 4.5(b) from the window pencil alone | whole-space vectors are not window tests; the capstone's smallest eigenvalue is `≍ c⁻⁷` (seventh-power collar reserve), a different scale from the `c`-scale pencil; needs the bulk second order (AHD open) |

## Log
- 2026-11-03 — created

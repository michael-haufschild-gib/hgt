# Diamond–Pintz: oscillation of Mertens' product

Stage: 3-formalized (2026-10-04). Loop cycles 239–241.

## Target (unconditional)
`log Π_{p≤x}(1−1/p)^{−1} − γ − log log x` takes both signs, with amplitude
`Ω±(logloglog x/(√x log x))` (Diamond–Pintz 2009). Prime-power version first:
`R₃(x) := A(x) − log log x − γ`, `A(x) = Σ_{n≤x} Λ(n)/(n log n)`.

## Plan (paper)
1. Laplace: `∫_0^∞ R₃(e^t)e^{−st}dt = log((s)ζ(1+s))/s = log ZRU(1+s)/s` (Re s > 0); removable at 0.
   Pieces: `∫ A(e^t)e^{−st} = CEL(1+s)/s` (as `integral_primePowerCount_exp_mul` with weight `1/n`),
   `∫ log t·e^{−st} = −(γ + log s)/s`.
2. Landau receiver: `±R₃(x) ≤ K x^{b−1}` eventually (`½ < b ≤ 1`) ⇒ `(z−1)ζ(z) ≠ 0` on `Re z > b`
   (analytic continuation along `(b−1, ∞)`; `ZRU(1+s) > 0` there). ⇒ `R₃ = Ω±(x^{b−1})`, `b < Θ`.
3. RH branch: `A` by Abel summation from `B(x) = Σ Λ(n)/n = log x − γ + R(x)`, `R = E/x − I`
   (`mertensDeviation_eq`): `R₃(x) = R(x)/log x − ∫_x^∞ R(t)/(t log²t)dt`; under RH
   `I = O(t^{−1/2})`, `∫ E/(t² log²t) = O(x^{−1/2}/log²x)` (by parts with `I`), so
   `R₃ = E(x)/(x log x) + O(1/(√x log x))`; Littlewood (MUST-723) gives `Ω±(L₃/(√x log x))`.
4. Product: `S = A + Δ`, `0 ≤ Δ ≤ Σ_{p>√x}1/p² ≪ 1/(√x log x)`: same Ω± for `S − γ − log log x`.

## Lean status
- [x] 1. Laplace identity (`integral_mertensPowerSum_exp_mul`, `integral_einCompare_mul_exp`).
- [x] 2. Landau receivers (both signs), `Ω±(x^{b−1})` ∀ b < Θ, `R = O(x^{−1/2})` ⇒ RH (MUST-737).
- [x] 3. RH branch: `exists_abs_mertensError_sub_le_of_riemannHypothesis`; final `mertensError_omega_pm_littlewood` (MUST-740).
- [x] 4. Product version: `mertensProductError_omega_pm_littlewood`, sign changes of `∏(1−1/p)^{−1} − e^γ log x` (`mertensProduct_inv_sub_exp_gamma_log_sign_changes`), MUST-742.

## Log
- 2026-10-03: card opened (cycle 239).
- 2026-10-03: steps 1–2 formal (MertensProductLaplace.lean, MUST-737). Comparison `Ein` replaces `log t + γ` (bounded at 0); `M e^{−t}` replaces the constant (pole at `−1`).
- 2026-10-03: step 3 formal (MertensErrorLittlewoodOmega.lean). The constant `c₀ − ∫_{log 2}^∞ f w` is never evaluated: Cauchy bound + sign changes of `R` force the remainder to `O(1/(√x log x))`.
- 2026-10-04: step 4 formal (MertensProductDiamondPintz.lean, MUST-742). Constants: upper `c/28`, lower `c/56`, `c = 1/(70π³)`.

## Lean modules (all `[propext, Classical.choice, Quot.sound]`, wired in RHTower.lean)
- MertensProductLaplace.lean — Laplace identity, Landau receivers, `R = O(x^{−1/2})` ⇒ RH, `Ω±(x^{b−1})` ∀ b < Θ (MUST-737).
- MertensErrorLittlewoodOmega.lean — RH remainder bound, `R = Ω±(L₃/(√x log x))` (MUST-740).
- MertensProductDiamondPintz.lean — product transfer, Diamond–Pintz (MUST-742).

## No-go / positive-survivor note
Not a no-go card. Reusable survivor: the constant-free Cauchy trick (an Abel remainder with a Cauchy bound
plus infinitely many sign changes of the main function is bounded by the Cauchy bound itself).

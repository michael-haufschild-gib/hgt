# Window pinning of the Weil cone: every Weil-positive system obeys a square-root PNT

- **ID:** MC-WEIL-WINDOW-PINNING
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** MC conjecture loop, cycle 159 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`). It follows from the pair tests of `weil-cone-one-sided-criterion.md`.
- **Statement.** Fix a real `C²` bump `g` supported in `[−¼, ¼]`, with autocorrelation `ρ(x) = ∫g(t)g(t−x)dt` and `P_± = ∫g(u)e^{∓u/2}du`. Put `S_L(lam) = Σ_{n≥2} lam(n)(ρ(log n−L) + ρ(log n+L))/√n`. Then there is a constant `C_g` such that every full-cone Weil-positive `lam` satisfies `|S_L(lam) − 2P₊P₋cosh(L/2)| ≤ C_g` for all `L ∈ ℝ`.

## Goal
- **PNT form.** Put `w = e^{−u/2}ρ`. Then every member of the Weil cone `C` satisfies `Σ_n lam(n) w(log n − L) = e^{L}∫w(u)e^{u}du + O_g(e^{L/2})`. This is a smoothed prime number theorem with square-root error, uniform over all of `C`.
  - For `Λ` this is the classical consequence of RH, since `Λ ∈ C ⟺ RH`.
  - For a general `lam` it is a necessary condition for membership in `C`, independent of `ζ`.
- **Tube.** `C` lies in a tube of width `2C_g` around the PNT main term, in every smoothed window. Any two members differ by a deviation with bounded smoothed log-windows.
- **Nonemptiness question.** If RH fails, `Λ`'s windows deviate by `≫ e^{(β₀−½)L}`, so every member of `C` stays exponentially far from `Λ`. Whether `C` is then empty is the open question "`C ≠ ∅ ⇒ RH`". By one-sided duality it is equivalent to prime-blind positivity (see the one-sided card).

## Paper proof
- **Autocorrelation of the shift pair.** For `f_σ = g + σg(·−L)`, `k_σ = f_σ ⋆ f̃_σ = (1+σ²)ρ + σ(ρ(·+L) + ρ(·−L))`.
  - Since `ρ` vanishes on `|x| > ½` and `log n ≥ log 2 > ½`, the `ℓ`-vector of `f_σ` is `2σ` times the window vector.
- **Pole term.** `paperFT f_σ(i/2) = P₊(1 + σe^{−L/2})` and `paperFT f_σ(−i/2) = P₋(1 + σe^{L/2})`, so the pole term is `2P₊P₋(1+σe^{−L/2})(1+σe^{L/2})`.
- **Archimedean term.** `|f̂_σ| ≤ 2|ĝ|` on `ℝ`. Hence the term is at most `4B`, with `B = ∫|ρ̂ μ|` (integrable by `EF.integrable_paperFT_mul_mu`).
- **Conclusion.** Weil positivity at `σ = ±1` gives
  - `2S_L ≤ 2P₊P₋(2 + 2cosh(L/2)) + 4B`;
  - `−2S_L ≤ 2P₊P₋(2 − 2cosh(L/2)) + 4B`.

## Lean
- `formal/GaloisForLFunctions/RHTower/WeilFullConeWindowPinning.lean` (namespace `RHTower.WeilOneSided`):
  - main theorem `exists_abs_windowSum_sub_le`;
  - pieces: `weilTest_shiftPair`, `logValue_shiftPair`, `pole_shiftPair`, `abs_arch_shiftPair_le`.
- Wired into `RHTower.lean`. `#print axioms`: `propext, Classical.choice, Quot.sound`.

## No-go recorded here
- **Prime-free sufficient condition.** `A ≥ 0` on `P₋` would imply RH, where `A` is the pole plus archimedean part. This condition is **false**.
  - For `g ≥ 0`, `ρ ≥ 0`, so `f₋ = g − g(·−L)` has nonpositive `ℓ`-values. Hence `k₋ ∈ P₋`.
  - Yet `A(k₋) ≤ 2P₊P₋(2 − 2cosh(L/2)) + 4B → −∞`, from `pole_shiftPair` and `abs_arch_shiftPair_le`.
- **Positive survivor.** This theorem: on `P₋` the prime sum must absorb an exponentially large pole deficit, and it does so exactly to within `O(1)` in every smoothed window, for every member of `C`.

## Log
- 2026-09-30 — created at stage 3 (MC cycle 159). The paper proof and the Lean proof were done together.
- 2026-09-30 — (MC cycle 163) **Compactness and the finite-prefix criterion.** Module `WeilFullConeCompactness`.
  - **Uniform coordinate bounds** (`exists_abs_le_of_weilPositiveFull`). Window pinning with a bump of radius `1/(4(n+1))` at `L = log n` isolates coordinate `n`, giving `|lam(n)| ≤ b_n` uniformly over the cone.
  - **Compactness** (`isClosed_setOf_weilPositiveFull`, `isCompact_normalizedWeilCone`). The cone is closed in the product topology and the normalized cone is compact (Tychonoff).
  - **Finite-prefix criterion** (`riemannHypothesis_iff_forall_prefix`). RH ⟺ for every `N` some full-cone Weil-positive sequence agrees with `Λ` on `2 ≤ n ≤ N`.
  - By one-sided duality, each prefix statement is a positivity statement on combinations that are blind to `log n` for `n > N`. It involves only the primes `≤ N`, with no support restriction on the tests.
- **Literature note (cycle 163 audit).** Bondarenko–Radchenko–Seip (Constr. Approx. 57 (2023) 405–461) give a Fourier interpolation basis from the values at the zeta zeros and `f̂` at `log n/(4π)`, i.e. frequencies `log √m` for all `m ≥ 1`. The Weil pairing sees only `log n` (`m = n²`), a much sparser set. So their uniqueness does not decide (P2), uniqueness of the Weil cone. (P2) under RH is equivalent to: no nonzero almost-periodic distribution `T = Σ_n b_n 2cos(t log n)` satisfies `T ≥ −Σ_γ δ_γ`.

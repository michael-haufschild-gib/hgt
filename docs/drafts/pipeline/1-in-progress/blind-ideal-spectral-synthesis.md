# Spectral synthesis for divisor-order ideals of the Meyer source (B3.4)

- **ID:** blind-ideal-spectral-synthesis
- **Stage:** 1-in-progress
- **Type:** THEOREM
- **Source:** `docs/reports/review-2510/hard-obstacles-summary.md` B3.4; APD README §9 topic 10.
- **Statement:** In the natural Fréchet topology of the Meyer source `S`, every ideal defined by
  vanishing orders at the Xi divisor is the closed span of the jet sources it contains plus the
  Poisson boundary `R`. In particular the closure of (critical jet sources) ⊔ `R` is the
  full-jet blind ideal; it equals the value-blind ideal `meyerTraceBoundedIdeal` iff every
  off-line zero is simple; and RH holds iff it is everything.

## Goal
Answer B3.4: "Is the span of critical-jet sources dense in the blind ideal for its natural
Fréchet topology?"

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Setting
`ĝ(s) = ∫ e^{st} g(t) dt`; `jet_j(ρ, g) = ĝ^{(j)}(ρ)`; `m(ρ)` the multiplicity; jet sources
`e_{ρ,j}` (`meyerSingleJetSource`) have `jet_i(σ, e_{ρ,j}) = [σ = ρ ∧ i = j]`.
`R = range(Poisson) = {g : every divisor jet vanishes}` (`meyerSource_boundary_iff_jets_zero`).
For `k : support → ℕ`, `I_k = {g : jet_j(ρ, g) = 0 for j < k(ρ)}` and
`E_k = span{e_{ρ,j} : k(ρ) ≤ j}`.

## Theorem
`closure(E_k ⊔ R) = I_k` for every `k`.

## Paper proof
`⊆`: generators lie in `I_k`; `I_k` is an intersection of kernels of continuous jets.

`⊇`. Fix `g ∈ I_k`.

1. *Gaussian removal.* `g_ε = invMellin(e^{εs²} ĝ) → g` (`deningerMeyerGaussianSource_tendsto`);
   `I_k`-closure is closed, so it suffices to put each `g_ε` in the closure.
2. *Tail products.* Spectral points `a_q = (ρ_q − ½)(−i)` over multiplicity copies,
   `Σ |a_q|^{-2} < ∞`. For a finite copy set `T`, `P_T(z) = ∏'_{q ∉ T} E₁(z/a_q)`.
   - `P_T` is entire; `P_T(z) = (∏_{q∈U} E₁(z/a_q)) P_{T∪U}(z)` for finite `U` disjoint from `T`.
   - *Uniform Gaussian bound:* `‖E₁(w)‖ ≤ e^{2|w|}` and `‖E₁(w)‖ ≤ e^{2|w|²}`. Given `δ > 0`
     choose `L` with `Σ_{|a|≥L} |a|^{-2} ≤ δ/4`, `c = Σ_{|a|<L} |a|^{-1}` (finite). Then for all
     `T, z`: `log‖P_T(z)‖ ≤ 2c|z| + (δ/2)|z|² ≤ δ|z|² + 2c²/δ`.
   - *Locally uniform convergence to 1:* if `‖z‖ ≤ r` and `T ⊇ {|a_q| < r}`, then
     `‖P_T(z) − 1‖ ≤ exp(r² Σ_{q∉T}|a_q|^{-2}) − 1`, using `‖E₁(w) − 1‖ ≤ |w|²` (`|w| ≤ 1`) and
     `‖∏(1+u_i) − 1‖ ≤ exp(Σ‖u_i‖) − 1`; the tail sum tends to `0` along finite sets.
3. *Approximants.* For finite `F ⊆ support`, `T = copies over F`,
   `A_F = invMellin(e^{εs²} ĝ(s) P_T(ζ(s)))`, `ζ(s) = (s − ½)(−i)`. Regularity: write the datum as
   `(e^{εs²/2} ĝ)·(e^{εs²/2} P_T∘ζ)`; the second factor is bounded on vertical strips by the
   Gaussian bound with `δ = ε/4`.
4. *Jets of `A_F`.* At `ρ ∉ F`: `P_T∘ζ = E₁(ζ/a_ρ)^{m(ρ)} · P_{T∪copies(ρ)}∘ζ`, and
   `1 − ζ(s)/a_ρ` has a simple zero at `s = ρ`; so the datum has order `≥ m(ρ)` at `ρ` and every
   jet vanishes. At `ρ ∈ F`: `ĝ` has order `≥ k(ρ)`, hence so does the datum.
   Therefore `A_F − Σ_{ρ∈F} Σ_{k(ρ)≤j<m(ρ)} jet_j(ρ, A_F) e_{ρ,j}` has all divisor jets zero,
   i.e. lies in `R`; so `A_F ∈ E_k ⊔ R`.
5. *Convergence.* `‖gauge_{n,κ}(A_F − g_ε)‖ ≤ (2π)^{-1} ∫ ‖s^n e^{εs²} ĝ(s) (P_T(ζ(s)) − 1)‖ dy`
   on `s = κ + iy` (`deningerMeyerStrongLogGauge_le_mellin`). The integrand tends to `0`
   pointwise as `F → ∞` and is dominated by `C_κ ‖s^n e^{εs²/2} ĝ(s)‖`, integrable. Dominated
   convergence along `atTop` (countably generated: the support is countable) gives
   `A_F → g_ε`. ∎

## Corollaries
- `k = m` off the line, `0` on it: `closure(critical jet span ⊔ R)` = full-jet blind ideal.
- This equals `meyerTraceBoundedIdeal` iff every off-line zero is simple: if an off-line `ρ`
  has `m(ρ) ≥ 2`, `e_{ρ,1}` is value-blind but has `jet_1(ρ) = 1`.
- RH ⇔ `closure(critical jet span ⊔ R) = ⊤` (if an off-line zero exists, `e_{ρ,0}` is outside).

## Lean
- `HTGeometry/TailCanonicalProducts.lean` (step 2).
- `ArithmeticPositiveDuality/SpectralSynthesisInTheBlindIdeal.lean` (steps 1, 3–5, corollaries).

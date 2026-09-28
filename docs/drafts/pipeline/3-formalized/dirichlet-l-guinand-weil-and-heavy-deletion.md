# Dirichlet-L Guinand–Weil formula and heavy-deletion rigidity

- **ID:** dirichlet-l-guinand-weil-and-heavy-deletion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** HF card `krein-producer-loops.md`, L48; STATUS MUST-357 open core (heavy perturbations)
- **Statement:** The Weil form with weights `(Λ + Λχ₄)/2` (same archimedean and pole terms as `ζ`) is not positive semidefinite at some finite aperture.

## Goal
Resolve MUST-357's heavy-perturbation open core for character-defined deletions. The mechanism is
new: real shifts of the pole-free radical kernel `F₁ = (¼−∂²)Φ` isolate the zeros of `L(s,χ₄)`,
which enter with a negative sign, against a positive archimedean mismatch.

## Gates
- [x] 0 → 1 in-progress: well-posed, attack idea (L48)
- [ ] 1 → 2 fully-proven: paper proof below, given the standard explicit formula for `L(s,χ₄)`
- [ ] 2 → 3 formalized: needs the Guinand–Weil formula for `L(s,χ₄)` in Lean
- [ ] 3 → 4 publication-ready

## Paper proof
1. `Σ_n Λ(n)χ(n)n^{−½}(g(log n)+g(−log n)) = Arch_χ(g) − Σ_{ρ_χ}ĝ(γ_χ)` (explicit formula for primitive odd `χ₄`, no pole).
2. For `f = Σ_j c_j F₁(·+v_j)`, the transform is `E(t)G(t)` with `E = Σ c_j e^{iv_j t}` and `G = ξ(½+it)(t²+¼)`, which vanishes at every zero of `ζ` and at `t = ±i/2`. So `W_ζ(f) = 0`.
3. `W_{Λ+w}(f) = W_ζ(f) − S_w(E)`, where `S_w(E) = ½∫|E|²G²(Arch_{χ₄}−Arch_ζ)dt/2π − ½Σ_{ρ_χ}E(γ_χ)conj E(γ̄_χ)G(γ_χ)conj G(γ̄_χ)`.
4. The mismatch density `Re ψ(3/4+it/2) − Re ψ(1/4+it/2) + log 4` is positive for all real `t` (to be verified in full: it equals `π` minus a decaying term at `t = 0`, and tends to `log 4`).
5. Choose `E` (trigonometric polynomial) with `E(γ_χ) = 0` at the finitely many `L(χ₄)`-zeros with `|γ_χ| ≤ T₀`. The tail `Σ_{|γ_χ|>T₀}|E G|²` is at most `‖E‖²_∞ Σ_{|γ|>T₀}|G(γ)|²`, which tends to `0` as `T₀ → ∞`, while the mismatch integral stays `≥ c > 0` (fixed normalization of `E`). Then `S_w(E) > 0`, so `W_{Λ+w}(f) < 0`. Truncation at a large aperture keeps the sign.

## Log
- 2026-09-28 — created from L48.
- 2026-09-28 — **Formalized (L51) with χ₈ in place of χ₄.** Moved to 3-formalized.
  - Unblocked by the Zeta23 package's proved explicit formula for `L(s,χ)` (`Zeta23.ThmE.EF_lit_chi_L`, primitive `χ`, `q > 1`) and the corpus theta kernel of `χ₈` (`thetaPowerXiC_half_eq_completedLFunction`).
  - Lean module `RHTower/WeilPositivityConductorObstruction.lean` (~1000 lines).
    - Built with no diagnostics. Axioms: propext, Classical.choice, Quot.sound. Wired into `RHTower.lean`.
  - **Theorem** `RHTower.chiEightMix_weilAtomSymbol_not_nonneg`: for every `t > 0`, the weights `Λ(1−t+tχ₈)` break Weil positivity.
    - `t = ½` deletes the primes `p ≡ ±3 (mod 8)` together with their odd powers, and halves the weights on powers of 2.
    - `t = 1` gives the twisted weights `Λχ₈`.
  - **Exact identity** `integral_weilAtomSymbol_chiEightMix`: `∫|h|²S = 2π(1−t)Re W_ζ + t(2π Re W_{χ₈} − log 8 ∫|h|²)`.
    - `W_{χ₈}` is the zero side of `L(s,χ₈)`.
    - For an even character the archimedean mismatch is exactly `log q` (the conductor).
  - **Proof.**
    - The double radical test `g_R = f_R ⋆ K_{≤4R}` has both zero sides `O(Re^{−R/2})` and `∫|h_{g_R}|² ≥ c`.
    - The lower bound uses the identity theorem on `|Im z| < 1` with the nonvanishing point `z = −3i/4` (`ξ(5/4)`, `κ̂(−3i/4) > 0`, `Λ(5/4,χ₈) ≠ 0`).
  - **Why χ₈ and not χ₄.** χ₈ is even, so the mismatch is the constant `−t log 8`. For χ₄ the mismatch is `−t(π sech(πr) + log 4)`, also negative.
- 2026-09-28 — **Generalized (L53) to every even real primitive character.**
  - Lean modules `RHTower/DirichletEvenThetaAxisKernel.lean` and `RHTower/WeilPositivityQuadraticConductorLaw.lean`. Built, wired. Axioms: propext, Classical.choice, Quot.sound.
  - **Kernel.** `Φ_χ(u) = e^{u/2} Σ_j χ(j) evenKernel(j/q)(e^{2u})`, built from mathlib's Hurwitz theta kernels.
    - It decays faster than every exponential at both ends (`exists_norm_dirichletAxisKernel_le`).
    - Its transform is `q^s Λ(s,χ)` with `s = ½+iz` (`paperFT_dirichletAxisKernel`), so it lies in the radical of `L(s,χ)`.
  - **Theorem** `RHTower.dirichletMix_weilAtomSymbol_not_nonneg`: for every even real primitive `χ` mod `q > 1` and every `t > 0`, the weights `Λ(1−t+tχ)` break Weil positivity.
    - The defect is `t log q ∫|h|²`.
    - `t = ½` deletes the inert primes of the real quadratic field (with their odd powers) and halves the ramified ones.
  - **Exact identity** `integral_weilAtomSymbol_dirichletMix`.
  - **Still open.** The odd characters (imaginary quadratic fields) need `oddKernel` and the digamma reflection: the defect becomes `log q + π sech(πr)`.
- 2026-09-28 — **L54: odd characters, so every quadratic field.** `RHTower.quadraticMix_weilAtomSymbol_not_nonneg` covers all real primitive `χ`. L48's original `χ₄` deletion is now formal.
  - Modules: `DirichletOddThetaAxisKernel` and `WeilPositivityImaginaryQuadraticConductorLaw`. The second has a generic joint-radical section reusable for any L-function with a decaying radical kernel.
  - Paper: two-sided isolation via distinct zeros (arXiv 2607.22930). Lean for that step is not started.

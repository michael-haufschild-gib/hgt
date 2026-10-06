# Localized real-rooted Weil eigenvectors force RH

- **ID:** RW-LOC-HURWITZ (loop rows 436, 438)
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), receiver for the RW/CCM route
- **Statement:** If even real eigenvectors of the restricted Weil forms at apertures `a_j → ∞` have
  real-rooted Fourier transforms, unit mass, bounded `L¹` norm and bounded second moment, then RH.

## Goal
The CCM route's recorded open step is convergence of the (real-rooted) ground-state transforms to
`Ξ` (corpus `ConnesXiGroundStateLimitWall`, "source-locked comparison with the prolate seed").
This theorem removes the identification: any subsequential limit works, and the only input is a
two-number a-priori bound. It is a receiver, not a producer: under ¬RH the ground states delocalize,
and in unstructured form (no compact support) the hypothesis is satisfied by `Φ/Ξ(0)` iff RH.

## Theorem
Notation: `F = f̂`, `f̂(z) = ∫ f(x)e^{izx}dx` (corpus `paperFT`); `W` the Weil functional
(pole − primes + archimedean), so that the restricted form is `W_a(f,k) = W(f ⋆ k̃)` for `f, k`
supported in `[−a,a]`; zeros `γ_ρ = (ρ−½)/i` with multiplicity.

Let `a_j → ∞`, and let `f_j ∈ C²` be even, real, supported in `[−a_j,a_j]`, with scalars `μ_j` such
that `W(f_j ⋆ k̃) = μ_j⟨f_j,k⟩` for all `k ∈ C_c^∞(−a_j,a_j)`. Assume
1. every zero of `F_j` is real;
2. `∫f_j = 1` and `‖f_j‖₁ ≤ C`;
3. `∫x²f_j(x)dx ≤ C`.

Then every nontrivial zero of `ζ` has real part `½`.

## Proof
**Step 1 (normal family).** `F_j` is even, real on `ℝ`, of exponential type, with real zeros and
`F_j(0)=1`; by Hadamard `F_j(z) = ∏(1 − z²/x_k²)`, and `−F_j''(0) = 2Σ1/x_k² = ∫x²f_j ≤ C`.
Hence `|F_j(z)| ≤ exp(C|z|²/2)`, and `|F_j(t)| ≤ C` on `ℝ`. By Montel a subsequence converges
locally uniformly to an entire `F_∞` with `F_∞(0)=1`; by Hurwitz every zero of `F_∞` is real.

**Step 2 (Gaussian tests).** Fix `σ > C/2` and `ψ(z) = e^{−σ(z+ω)²+is(z+ω)}` (`ω, s ∈ ℝ`), the
function `conj ĥ(z̄)` of a Gaussian-modulated `h`. Split `h = χ_jh + (1−χ_j)h`, `χ_j` a cutoff equal
to 1 on `[−a_j+1, a_j−1]`. With `‖f_j‖₁ ≤ C` and Chebyshev's bound, the pole, prime and
archimedean parts of `W(f_j ⋆ ((1−χ_j)h)~)` are `O(e^{a_j}e^{−(a_j−1)²/(8σ)})`, and
`|⟨f_j,(1−χ_j)h⟩| = O(e^{−(a_j−1)²/(4σ)})`. The explicit formula gives
`W(f_j ⋆ h̃) = Σ_ρ F_j(γ_ρ)ψ(γ_ρ)`, dominated by `e^{(C/2−σ)(Re γ_ρ)²+O(1)}` uniformly in `j`, so
it is bounded. Also `⟨f_j,h⟩ = (1/2π)∫F_jψ → (1/2π)∫F_∞ψ`. Choosing `h` with `∫F_∞ψ ≠ 0`
(Gaussian-modulated `ψ` are total) shows that `μ_j` is bounded; pass to `μ_j → μ_∞`. Dominated
convergence over the zeros gives, for all such `ψ`,

`Σ_ρ F_∞(γ_ρ)ψ(γ_ρ) = κ ∫_ℝ F_∞ψ dt`, with `κ = μ_∞/2π`.

**Step 3 (contour form).** Let `η = ½ + ε`, `L_± = ℝ ± iη`, `A = F_∞Ξ'/Ξ`. Rectangles over good
heights, where `Ξ'/Ξ = O(log²T)`, together with the Gaussian decay of `F_∞ψ` in the strip
`|Im z| ≤ η`, give `Σ_ρ F_∞ψ(γ_ρ) = (1/2πi)(∫_{L₋} − ∫_{L₊})Aψ dz`. Shifting `∫_ℝF_∞ψ` to `L₊`:

`∫_{L₋} Aψ dz = ∫_{L₊} (A + 2πiκF_∞)ψ dz`.

**Step 4 (one-sided Paley–Wiener).** Take `ψ_s(z) = e^{−σz²}e^{isz}`. Put `a₋(t) = (Aψ₀)(t − iη)`
and `b₊(t) = ((A+2πiκF_∞)ψ₀)(t + iη)`; both are integrable with Gaussian decay. Step 3 reads
`e^{sη}â₋(s) = e^{−sη}b̂₊(s)` for all real `s`, so `|â₋(s)| ≤ ‖b₊‖₁e^{−2ηs}`. Hence
`E(t+iy) = (1/2π)∫â₋(s)e^{sy}e^{−ist}ds` is holomorphic on `0 < y < 2η` with `L²` boundary
value `a₋` at `y = 0`. The function `(Aψ₀)(·−iη)` is holomorphic near `y = 0` (no zero of `Ξ` has
`|Im| ≥ ½`) with the same boundary value, so the two agree. Therefore `Aψ₀` continues
holomorphically to the whole strip `|Im z| < η`. Since `ψ₀` has no zeros, `F_∞Ξ'/Ξ` has no poles
there: `F_∞(γ_ρ) = 0` for every nontrivial zero.

**Step 5.** All zeros of `F_∞` are real (Step 1), so every `γ_ρ` is real, i.e. RH. ∎

## Dependencies
Classical only: Hadamard factorization (order ≤ 1), Montel, Hurwitz, the Weil explicit formula for
the test functions `f ⋆ h̃` (`f ∈ C²_c`, `h` Gaussian-modulated), `Ξ'/Ξ = O(log² T)` on good
horizontal segments, Chebyshev's bound `ψ(x) ≪ x`, and the `L²` Paley–Wiener theorem for a strip.

## No-go closure (CCM / RW ground-state convergence)
- **Exact killing mechanism:** zero flips make extremal states real-rooted only inside flip-closed
  classes. Those classes are translation-invariant up to their tails, so no flip-invariant functional
  can pin position (loop rows 430–437).
- **Strongest positive survivor:** this theorem. The CCM open step reduces to *bounded mass and
  second moment of the ground states* (no escape to the aperture boundary); the limit need not be
  identified with `Ξ`.
- **New insight:** real-rootedness (flip extremality) and localization (`Φ`-like decay) are each
  available separately. Under ¬RH real-rooted ground states delocalize, because the off-line
  resonance `e^{(Θ−½)|x|}` drives mass to `±a`, and localized near-null vectors (`Φ` truncations)
  are not extremal. RH is exactly their conjunction along one sequence.
- **Status:** paper proof complete. Lean: not formalized; it needs the explicit formula for
  Gaussian-decay tests (the corpus has compactly supported and Cauchy-kernel test classes) and
  one-sided Paley–Wiener on a strip.

## Log
- 2026-10-06 — created at stage 2 (Opus), loop rows 436 and 438.

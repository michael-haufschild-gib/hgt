# General data, cusp channel and spin two on the modular horizon

- **ID:** modular-horizon-general-data-cusp-spin-two
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** extends `3-formalized/modular-horizon-full-field-ringdown.md`
- **Statement:** On the massless topological AdS₄ black hole with horizon `PSL₂(ℤ)\ℍ`: every compact pulse gives an exact smooth solution by the method of images, with the same echo identity and ringdown; every cusp form gives undamped horizon modes at the universal rate `D`; and every master field reconstructs to a vacuum linearized metric, so each zeta zero is a gravitational quasinormal mode.

## Goal
Replace Gaussian amplitudes by general data, add the discrete channel, and pass from the conformal scalar to the metric. Not an RH route.

## Gates
- [x] 0 → 1 in-progress: corpus read (Schläfli shift, deck spectral theorem, Selberg at level one, vector and scalar stream Einstein tables, joint smoothness of the Fourier–Bessel family)
- [ ] 1 → 2 fully-proven
- [ ] 2 → 3 formalized

## Claims and paper proofs

### Part I: sharp decay and the image field

**I.1 Sharp decay in the order.** For `x > 0`, `ν = η + iξ`, `0 ≤ θ < π/2`: `‖K_x(ν)‖ ≤ e^{-|ξ|θ} K_{x cos θ}(η)`. Proof: shift the Schläfli line to `Im t = θ` (`integral_besselOrderExpKernel_eq_shifted`), where the modulus is `exp(-x cos θ cosh t + ηt - ξθ)`. Take `θ = π/2 - 1/(1+|ξ|)`: this gives `e·e^{-π|ξ|/2}` and argument `x sin(1/(1+|ξ|)) ≥ 2x/(π(1+|ξ|))`. With `K_w(η) ≤ C_η (1+1/w)^B e^{-w/2}` the Fourier sum over `n` costs a power of `1+|ξ|`, so the Whittaker tail and its jets are `O((1+|Im u|)^M e^{-π|Im u|/2})` on vertical strips.

**I.2 Polynomial bounds for `E`.** `|1/ξ(1+2iξ)| ≲ (1+|ξ|)^N e^{π|ξ|/2}`, which cancels the exponential of I.1. So `E(iξ; x, Y)` and its jets are `O((1+|ξ|)^M)`, locally uniformly. The same holds on `Re u = -A`, on `Re u = c > ½` by the inner bound, and on horizontal segments at the good heights.

**I.3 Compact pulses.** For `h ∈ C_c^∞(ℝ)`, `a(w) = (2π)⁻¹ ∫ h(S) e^{-iwS} dS` is entire, and `‖w^k a(w)‖ ≤ C_k e^{A|Im w|}` by integration by parts. Fourier inversion applied to `e^{-cS} h(S)` gives `h(S) = ∫ a(-iu) e^{uS} dy` on every line `u = c + iy`.

**I.4 Image field.** `Π_h(τ, z) = ½ Σ_{(c,d)=1} y_γ^{½} h(τ + log y_γ)`, `y_γ = Y/|cz+d|²`. For `τ, z` in a compact set only finitely many rows are nonzero, because `y_γ ≥ a` bounds `(c, d)`. Each term solves the wave equation: `y_γ` is harmonic with `Y²|∇y_γ|² = y_γ²`, so `Y²Δ_e[F(y_γ)] = y_γ²F''(y_γ)`, and for `F(y) = y^{½} h(τ + log y)` this is `y^{½}(h'' - h/4)`. So `Π_h` is `C^∞`, `SL₂(ℤ)`-invariant, and solves `𝓕_ττ = Δ𝓕 + 𝓕/4`, by elementary means.

**I.5 Bridge.** For `c > ½`, inserting I.3 in each term and summing gives `Π_h(τ, z) = ∫ a(-iu) e^{uτ} E(u; z) dy` on `Re u = c`, by `eisensteinLineModel_eq_rowSum`. Moving the line to `Re u = 0` crosses `u = ½`, residue `(3/π) a(-i/2) e^{τ/2}`. So `Π_h = 𝓕_h + 6 a(-i/2) e^{τ/2}`, where `𝓕_h(τ, z) = ∫ a(ξ) E(iξ; z) e^{iξτ} dξ` and `6a(-i/2) = (3/π) ∫ h(S) e^{-S/2} dS`.

**I.6 Echo and wavefront.** `𝒮 = h ∗ (K - (3/π) e^{·/2})`. Since `K = 0` on `τ ≤ 0`, `h ∗ K` vanishes before `inf supp h`: the reflected signal is exactly the mean term before the first echo arrives.

**I.7 Ringdown.** The contour argument of the Gaussian case runs with the polynomial bound of I.2 against the rapid decay of `a`, at the good heights.

### Part II: the cusp channel

**II.1 Basis.** `cuspEigenBasis 0` is a Hilbert basis of the level-one cuspidal space, of `C²` Laplace eigenfunctions `u_j`.

**II.2 Reality.** `λ_j ≥ 0` (`cuspEigenBasis_lam_nonneg`), `λ_j ≠ 0` (orthogonal to constants), and no `λ_j ∈ (0, ¼)` (`no_exceptional_of_principal_le` at `N = 1`). So `λ_j = ¼ + t_j²` with `t_j` real.

**II.3 Modes.** `e^{±it_jτ} u_j` solves the modular wave equation. Its lifts solve the wave equation of the metric, with `ω = ±t_j - iD`: both branches occur, at rate exactly `D`, with no dependence on any zero. The horocycle mean vanishes, so the echo channel does not see the cusp channel.

**II.4 General cuspidal data.** For `f` in the cuspidal space, `C(τ) f = Σ_j cos(t_jτ) ⟨u_j, f⟩ u_j` is a contractive cosine family.

### Part III: spin two

**III.1 Vector sector, modes.** Let `y²Δ_e Y = λY`, `V₀ = ∂_y Y`, `V₁ = -∂_x Y`, so `V` is divergence-free. Then `D₀ = y²(U+Z) + 2y(Q-R) = ∂_y(y²Δ_e Y) = λV₀` and `D₁ = λV₁`. With `H = rΨ`, `r²f H'' + 2r H' - (w²r²/f + 2)H = (r³/f)(Ψ_** - w²Ψ)`. So `master = 0` is exactly the radial equation `Ψ_** - w²Ψ = -λ sech²x_* Ψ`, and `cosmological_component` gives a vacuum solution for `h_{ti} = f H' V_i`, `h_{ri} = (wH/f) V_i`.

**III.2 Scalar sector, modes.** From `ScalarStreamEinstein` and `master_identity`, with a reconstruction `(F0, F1, F2, H)` linear in `Φ, Φ'`, all coefficients vanish on the same radial equation.

**III.3 Every zero.** At a pole `p`, `N(p; ·)` is a nonzero `SL₂(ℤ)`-invariant eigenfunction with `λ = p² - ¼`. III.1 gives an exact vacuum metric mode with rate `D - Re p`, a gravitational quasinormal mode for each zero.

**III.4 Packets.** `h[Π_h] = Σ_rows ∫ a(ξ) h^ξ[y_γ^{½+iξ}] dξ`, a locally finite sum of integrals with explicit integrands. The constant term of `Π_h` has zero horizon gradient, so it does not enter the vector sector. Differentiating under the integral and linearity of the Einstein operator give a vacuum metric.

**III.5 Metric ringdown.** The contour argument for numerators with first jets of `N` gives the expansion of `h_{ti}`, `h_{ri}` in the modes of III.3.

## Status of the parts
See the Lean certificate when each part closes. Existence of cusp forms at level one needs the Weyl law, which the corpus does not have, so Part II is a statement about every element of the basis, possibly vacuous in Lean.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** pending

## Log

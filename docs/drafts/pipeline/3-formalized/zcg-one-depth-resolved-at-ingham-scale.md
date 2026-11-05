# Configurations of one depth are resolved at the Ingham scale

- **ID:** zcg-one-depth-resolved-at-ingham-scale
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** formal/GaloisForLFunctions/ZeroConfigurationGeometry/README.md §6 Q2 · card `zcg-deep-hiding-at-ingham-scale`
- **Statement:** Let `Z, Z'` be tempered, with union `g`-separated apart from FE partners and lying at
  one depth `|Re ρ − ½| = δ`. If `Z.W f f = Z'.W f f` for every `C²` window `f` supported in
  `[−a, a]`, with `a > π/(2g)`, then `Z = Z'` with multiplicity.

## Goal
Half of the factor 2 between the Ingham scale `π/(2g)` and the any-depth threshold `π/g`, at every
depth. Shallow configurations (`eq_of_weil_eq_of_shallow`) and deep columns (`deepColumn_mimic_iff`)
were the previously known cases at the Ingham scale.

## Proof
Write `c = multDiff Z Z'`, `γ_z = Im z − i(Re z − ½)`, and `h_b = b ⋆ b̃` for a bump `b` of width
`w = (a − π/(2g))/2`.
1. **Modulated lag identity.** `b_τ,s(u) = b(u + s)e^{iτ(u + s)}` has `b̂_τ,s(ζ) = e^{−iζs} b̂(ζ + τ)`.
   The pair `(b_τ,−x/2, b_τ,x/2)` consists of windows of aperture `a` when `|x|/2 + w ≤ a`. Its point
   image is `e^{iγx} ĥ_b(γ + τ)`. Polarized mimicry gives `Σ_z c(z) e^{iγ_z x} ĥ_b(γ_z + τ) = 0` for
   every `τ ∈ ℝ`.
2. **Averaging.** For `φ` continuous with `|φ(τ)| ≤ C(1 + |τ|)^{−4}`, Fubini gives
   `∫ φ(τ) ĥ_b(γ + τ) dτ = (h_b φ̂)^(γ)`. Peetre's inequality
   `(1 + |t + τ|)^{−2} ≤ (1 + |τ|)²(1 + |t|)^{−2}` and `|ĥ_b(ζ)| ≲ (1 + |Re ζ|)^{−2}` on the strip
   dominate the double sum and integral by `Σ |c(z)|/(1 + |γ_z|²) < ∞`. So
   `Σ_z c(z) e^{iγ_z x} (h_b φ̂)^(γ_z) = 0`.
3. **Inverse weight.** For `ψ ∈ C_c^∞`, `φ = (2π)^{−1} ψ̂(−·)` has `φ̂ = ψ` by Fourier inversion, and
   `φ` decays faster than any power.
4. **FE fold.** Choose `ψ = χ/(2cosh(δ(· + x)))` with `χ ∈ C_c^∞`. For an FE pair `t ∓ iδ`,
   `e^{i(t−iδ)x} κ̂(t − iδ) + e^{i(t+iδ)x} κ̂(t + iδ) = e^{itx} (κ · 2cosh(δ(· + x)))^(t)`, and
   `κ · 2cosh(δ(· + x)) = h_b χ` for `κ = h_b ψ`. An on-line point (then `δ = 0`) gives half of
   this. Splitting the sum into on-line points and right-half-plane FE pairs gives
   `Σ_k e^{it_k x} m_k (h_b χ)^(t_k) = 0` over the sites `k` (`Re k ≥ ½`). Here `m_k = c(k)/2` on the
   line and `c(k)` off it, for all `|x| ≤ V = 2(a − w)`.
5. **Ingham.** The heights `t_k` are `g`-separated, the coefficients are summable, and
   `V = a + π/(2g) > π/g`. The infinite Ingham inequality at depth zero (`inghamConst_mul_normSq_le`
   with vanishing remainder constant) gives `m_k (h_b χ)^(t_k) = 0` at every site.
6. **Conclusion.** If `c(k₀) ≠ 0`, take `χ = ζ e^{−it₀u}` with `t₀ = Im k₀`. Then `∫ ζ h_b = 0` for
   every real `ζ ∈ C_c^∞`, so `h_b = 0` (du Bois-Reymond and continuity). But
   `ĥ_b(0) = |b̂(0)|² > 0` for the corpus bump. ∎

The depth enters only through the weight `cosh(δ(u + x))`, which is the same for every site and so
can be divided out of the test function. With several depths no single test function divides out
all the weights; that is the open mixed-depth case.

## Lean
`formal/GaloisForLFunctions/ZeroConfigurationGeometry/ConfigurationsOfOneDepthAreResolvedAtTheInghamScale.lean`:
`modBump`, `bumpWeight`, `paperFT_modBump`, `pointImage_modBump`, `tsum_modLag_eq_zero`,
`integral_mul_bumpWeight`, `inv_one_add_abs_sq_le`, `tsum_averaged_lag_eq_zero`, `invWeight`,
`paperFT_invWeight`, `invWeight_props`, `depthWeight`, `pair_term_eq`, `siteMass`,
`tsum_sites_oneDepth_eq_zero`, `coeff_eq_zero_of_tsum_exp_eq_zero`, `eq_of_mimic_of_oneDepth`.
`#print axioms eq_of_mimic_of_oneDepth`: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Log
- 2026-11-05 — created; formalized

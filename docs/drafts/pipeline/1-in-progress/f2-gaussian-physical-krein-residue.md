# F2 — Gaussian physical realization of complete Weil energy

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** Extend the finite physical cusp-energy residue to the existing Gaussian-damped zero coordinates, then recover complete Weil energy as damping vanishes.

## Exact target

For `ε>0` and `x∈ℓ²(zetaZeroConfig.carrier,ℂ)`, use the existing damping

`c_s=exp(−ε(Im s)²)x(upperMayerZero s)`.

Set `κ_s=−core_s/b_s`, `b_s=2ζ(2s−1)/(2s−1)`, and

`Ψ(u)=exp(u/2) Σ_s c_s κ_s(exp(−u))`, `λ_st=2s+2 conjugate(t)−1`.

Prove absolute convergence of the physical packet and the finite-depth counterterm, and

`lim_(T→∞) [∫_0^T |Ψ(u)|²du − Re Σ_(λ_st≠0) c_s conjugate(c_t)(exp(λ_st T)−1)/λ_st]/T`

`= Re Σ_s c_s conjugate(c_(s♯))`.

For the existing real-window zero coordinates, twice this residue should tend to complete Weil energy as `ε→0+`. This is a literal physical realization of the signed form. Subtracting growing counterterms supplies no positivity by itself.

## Analytic gates

The finite-packet argument uses a positive exponent below every spectral gap. There need not be a common gap for an infinite packet. Replace that argument by the exact lower-cusp estimate

`|κ_s(a)−a^(1−2s)|≤C_s a`,

with `C_s` bounded by a polynomial times an exponential linear in `Im s`. This estimate is a required conclusion, not an assumption on the packet.

The actual kernel satisfies `|k_w(t)|≤|averagingFactor(w)|⁻¹t^(−1−Re w)`. At resonance, `r_w(a)=fieldCore_w(a)+B_w/a=normalizedTail_w(a)`. The existing small-axis bound and exponential tail make `∫_0^∞u^(Re w)|r_w(u)|du` finite. Substitution `u=a/t` in the literal convolution then gives an outgoing error `O(a^(−1−Re w))`; inversion gives `O(a)` at zero.

Uniform spectral control requires a sharper tail estimate than the existing parameter-dependent `tailConst`. The actual Bessel integral and `|cosh z|≤cosh(Re z)` give `|K_ν(y)|≤K_(Re ν)(y)`. The Whittaker coefficient satisfies the corresponding comparison with its real-parameter value. When `|Re ν|≤1/2`, that real parameter belongs to the unit ball about zero. Applying the existing local term majorant at center zero, then summing, yields the proposed uniform bound `|cuspTail_ν(x,Y)|≤tailConst(0)exp(−2πY)` for `Y≥1/2`. Charge normalization should be estimated after cancellation. With `A_w=averagingFactor(w)` and `Λ(z)=ΓR(z)ζ(z)`, the source formulas and functional equation give

`1/(A_w ΓR(w)b_s)=w/Λ(2−w)`, `B_w/(A_w b_s)=w`, where `w=2s`.

Thus the needed constants reduce to inverse Gamma bounds on `1<Re(2−w)<2`, the Euler-region bound for `ζ(2−w)⁻¹`, and the audited reciprocal strip-gap bounds. A separate estimate of the unnormalized charge is unnecessary. The existing `exists_bound_norm_div_Gammaℝ`, applied to the constant function on `[1,2]`, bounds the reciprocal Gamma factor by `C exp(π|Im w|/2)`. Together these estimates should give a uniform polynomial-exponential constant in the exact `O(a)` remainder.

## Passage to infinite packets

With the required uniform bound proved, each normalized logarithmic error is bounded by `C_s exp(−u/2)`. Its cross integral with mode `t` costs `C_s/(1−2 Re t)`. The audited reflected zero-free bound gives `(1−2 Re t)⁻¹≤116 Im t`; existing Gaussian spectral summability then controls both cross terms and error squares.

At fixed `T`, the bound `|(exp(λT)−1)/λ|≤T exp(T)` for `T≥0` avoids any zero-separation premise. Integrate the absolutely convergent model sum before taking the depth limit. Zero exponents pair exactly reflected resonances; the integrable physical error disappears after division by `T`.

## Status

Finite-packet physical residue: [separate formalization](f2-physical-cusp-krein-residue.md). Infinite formula and uniform estimates are conjectural. No complete-Weil positivity claim.

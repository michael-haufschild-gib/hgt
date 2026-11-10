# All-order Gaussian type-I error

- **ID:** b13-all-order-gaussian-typeI-error
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); unconditional
- **Obstacle:** B13
- **Scope:** actual first Vaughan type-I term; centred type-II cancellation remains open.

## Statement

Let `r≥1`, `0≤σ<1`, `t≥1`, `Re ε=α>0`, `|ε|≤4αt`, and `αX²=2`.
Set `s=σ+it`, `p=2r`,

`F_r(x)=(ε/t)^r x^(p−s)exp(−εx²)`,
`P_r=(ε/t)^r Γ((p−s+1)/2) ε^(−(p−s+1)/2)/2`.

For every `b>0`,

`|Σ_{n≥1}F_r(bn)−P_r/b| ≤ K_r,σ b^(p−1)t^p X^(1−σ−p)`.

For `c=Λ_≤U*μ_≤V` and `UV≥1`, the actual arithmetic convolution satisfies

`|Σ_n(1*c)(n)F_r(n)−(Σ_{b≤UV}c(b)/b)P_r|`
` ≤ K_r,σ (UV)^p t^p X^(1−σ−p)log(UV)`.

Here `1` denotes the arithmetic zeta coefficient, not the convolution unit.
The signed reciprocal coefficient mass is preserved exactly.

## Explicit constants

Define

`C_0(a)=Γ((a+1)/2)/2`,
`C_{k+1}(a)=(|a|+1)C_k(a−1)+8C_k(a+1)`.

Then

`K_r,σ=4^r |B_(2r)| C_(2r)(2r−σ) 2^((2r+σ−1)/2)/(2r)!`.

Every Gamma argument appearing in `C_(2r)(2r−σ)` is positive, since its
minimum is `(1−σ)/2`. Thus the constants are finite and nonnegative.

## Proof

Write `G_w(x)=x^w exp(−εx²)` and define its explicit derivative tower by

`D_0(w)=G_w`,
`D_(k+1)(w)=w D_k(w−1)−2ε D_k(w+1)`.

Induction proves that `D_k` is the `k`th derivative on `(0,∞)`, is continuous
and zero at the origin for `k<Re w`, and is integrable for `k−1<Re w`.
Each positive-lattice sample sequence is absolutely summable: a large
integer power dominates its real Mellin power, and Gaussian decay supplies
summability. Consequently all endpoint derivatives tend to zero at infinity.

The integral norm has the recursive bound `V_k(w,ε)`, with

`V_0=α^(−(Re w+1)/2)Γ((Re w+1)/2)/2`,
`V_(k+1)=|w|V_k(w−1,ε)+2|ε|V_k(w+1,ε)`.

If `|Im w|≤t`, `t≥1`, and `|ε|≤4αt`, induction gives

`V_k(w,ε)≤C_k(Re w)t^k α^((k−Re w−1)/2)`.

Indeed `|w|≤(|Re w|+1)t`; the two shifted damping powers agree after
multiplying the second term by `α`.

On cell `[bn,b(n+1)]`, use
`Q_k(x)=b^k B_k(x/b−n)/k!`, so `Q'_(k+1)=Q_k`.
Integration by parts requires only continuity of `D_k` and integrability of
`D_(k+1)`, and therefore remains valid on the first cell at zero. Summing
cells telescopes every boundary term. Their limits vanish for `k<p` because
`Re w=p−σ>p−1`. At even order `p`,
`|B_p(u)|≤|B_p|` on `[0,1]` bounds the remaining integral, giving

`|Σ_{n≥1}G_w(bn)−b⁻¹∫₀∞G_w|≤b^(p−1)|B_p|V_p(w,ε)/p!`.

Take `w=p−σ−it` and multiply by `|(ε/t)^r|≤(4α)^r`.
The total damping power is `α^((p+σ−1)/2)`, which equals
`2^((p+σ−1)/2)X^(1−σ−p)`. The complex-rate Gamma integral evaluates
the continuous main term as `P_r`.

For the arithmetic assertion, finite support of `c` and Gaussian absolute
convergence justify reindexing `Σ_n(1*c)(n)F_r(n)` as
`Σ_{b≤UV}c(b)Σ_aF_r(ab)`. The corpus bound `|c(b)|≤log b` gives
`Σ_{b≤UV}|c(b)|b^(p−1)≤(UV)^p log(UV)`. Apply the fibre estimate.

## Improvement and boundary

Each increment of moment order gains two powers of `UV t/X` in this
actual arithmetic remainder. The first type-I term therefore permits
cutoffs approaching `X^(1−(1−σ)/(2r))`, subject to polynomial height costs.
The complete unfiltered reduction, using a first-variation logarithmic
remainder, is proved in
[the higher-moment centred Vaughan theorem](b13-higher-moment-centred-vaughan.md).
Selected-mode transfer and the spacing-preserving damping filter remain
open. No independent centred-current cancellation is claimed.

## Lean theorem inventory

All declarations are in `GaloisForLFunctions.ExceptionalLayerTheory`.

- `GaussianHigherDerivatives.lean`: `hasDerivAt_gaussianMellinJet`,
  `gaussianMellinJet_zero`, `integrableOn_gaussianMellinJet`,
  `integral_norm_gaussianMellinJet_le`, `summable_gaussianMellinJet_lattice`,
  `gaussianMellinJetVariation_le`.
- `GaussianHigherLatticeError.lean`:
  `norm_tsum_gaussianMellinWeight_sub_main_higher_le`.
- `GaussianHigherMomentLattice.lean`:
  `norm_tsum_gaussianHigherMoment_sub_pole_le`,
  `norm_tsum_gaussianHigherMoment_sub_pole_physical_le`.
- `GaussianHigherMomentTypeIPole.lean`:
  `norm_tsum_gaussianHigherPrimeMomentWeight_dilate_sub_pole_le`,
  `norm_tsum_gaussianHigherMoment_zeta_trunc_conv_sub_pole_le`.

This is an explicit arithmetic remainder improvement using classical
Euler–Maclaurin cancellation; no standalone novelty claim is made for the
summation formula or Gaussian derivative recurrence.

## Verification

All four modules pass direct `lake --old env lean` source checks without
warnings. Eleven transitive `#print axioms` audits report only
`propext`, `Classical.choice`, and `Quot.sound`. No placeholders,
trusted computation or limit increases occur. All modules are imported
by `ExceptionalLayerTheory.lean`; the umbrella was not compiled.

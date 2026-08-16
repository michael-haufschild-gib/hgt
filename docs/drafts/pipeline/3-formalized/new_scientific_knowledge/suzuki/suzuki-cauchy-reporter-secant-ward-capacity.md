# Suzuki Cauchy reporter-secant Ward capacity and negative interscale law

- **Status:** Formalized; targeted source check passes
- **Routes:** CCM-UR, CCM-FU, CCM-HG, Route O, Suzuki reflected-wall assembly
- **Labels:** `[NEW]` `[SOURCE-SPECIFIC]` `[UNCONDITIONAL]` `[FINITE-TO-COFINAL-INFRASTRUCTURE]`
- **Lean module:** `GaloisForLFunctions.RHTower.SuzukiCauchyReporterSecantWardCapacity`

## Corpus-first frontier audit

Before conjecturing, exact corpus searches were run for positive-definite exponential kernels,
finite Cauchy Grams, anchored Gram capacity, Suzuki reporter secants, and two-lag sign laws. Corpus
already contained:

- generic anchored capacity for normalized even positive-definite kernels;
- finite depth-one and all-depth Cauchy Grams;
- the Cauchy-height wall/coherent isometry;
- the lower-Hardy realization of Suzuki's reporter as a two-depth wall secant;
- many source-fusion and bounded-polarization no-go theorems.

No declaration or paper card contained the exact Cauchy Gram of two Suzuki reporter secants, its
far-lag factorization, or its factor-two sign classification. Targeted inspection also found no
such identity in Suzuki's 2023 screw-function paper or June-2026 Weil-form synthesis. Generic
Bochner positivity and Cauchy--Schwarz are known infrastructure and are not claimed as novel.

## New theorem

For the normalized Cauchy kernel

```text
K(x) = exp(-|x|/2)
```

and the two-depth secant at lag `p`, the cross-Gram is

```text
G(p,q) = K(p-q) - K(p-2q) - K(2p-q) + K(2p-2q).
```

At every `p,r >= 0`, the exact far-scale factorization is

```text
G(p, 2p+r)
  = (exp(-p/2)-1) exp(-r/2) (1-exp(-(2p+r)/2)) <= 0.
```

If `p` is nonzero, inequality is strict. Thus positive Suzuki reporter coefficients interact
negatively across a factor-two lag separation. This is not generic Gram positivity: it is a
source-selected negative off-diagonal law exposed by the forced `p,2p` reporter depths.

Summing the exact factorization gives an arbitrary rectangular far-block theorem: any finite
nonnegative shallower packet paired with nonnegative deeper coefficients at pairwise lags
`2p_i+r_ij` has total cross-energy `<= 0`. This is the usable dyadic localization law, not merely a
two-atom observation.

For the literal natural Suzuki source, set

```text
p_k = log(N/k),                 c_k = Λ(k)/sqrt(k),        2 <= k <= N.
```

The lag inequality `p_j >= 2 p_k` is exactly the multiplicative hyperbola

```text
N*j <= k^2                         (j <= k).
```

The formal source-energy theorem partitions the full ordered critical-Mellin double sum across this
hyperbola. Every term in the symmetric far region

```text
N*min(j,k) <= max(j,k)^2
```

is nonpositive. Consequently the full literal prime reporter-secant energy is bounded above by
the restricted near-hyperbola sum

```text
max(j,k)^2 < N*min(j,k).
```

This is stronger than a dyadic heuristic: the deleted region and its favorable sign are exact at
every natural aperture, with no asymptotic error and no hypotheses. It identifies the sole region
where a positive contribution can survive **inside the prime--prime block**. It does not classify
prime--polar, prime--Gamma, or continuum--continuum blocks.

The same module proves finite Ward capacity. For arbitrary finite real coefficients and
nonnegative lags, literal lower-Hardy reporter amplitude is origin correlation of the signed
doubled-node packet, hence

```text
reporterAmplitude^2 <= exactCauchySecantGramEnergy.
```

## Scientific consequence

Naive estimates treated all positive prime light as mutually reinforcing and therefore faced a
nonsummable cofinal mass. Far-scale reporter interactions are instead strictly negative. Any valid
cofinal estimate should dyadically localize the energy and retain these negative interscale blocks;
taking absolute values or diagonalizing first destroys the newly exposed cancellation.

The prime--prime part of the remaining analytic target has therefore narrowed. It is not a bound on
the original square of total prime light mass: only the multiplicative band
`max(j,k)^2 < N*min(j,k)` can contribute positively within that block. Completed-source closure is
strictly harder because mixed prime--polar and prime--Gamma terms may be positive outside this band;
their signed sewing remains part of the open theorem.

This advances mechanism but does not close RH. Remaining hard theorem is source-specific: extend
factor-two negativity through the literal prime--polar--Gamma completed current and prove a
uniform cofinal bound for the surviving same-scale/adjacent-scale blocks.

## Lean certificate

Formal declarations include:

- `charFun_standardCauchy_eq_exp_neg_abs`
- `positiveDefiniteOnReal_cauchyHalfExponentialKernel`
- `suzukiReporterSecantPacketCauchyEnergy_eq_sum_gram`
- `suzukiReporterSecantCauchyGram_two_mul_add_eq`
- `suzukiReporterSecantCauchyGram_two_mul_add_nonpos`
- `suzukiReporterSecantCauchyGram_two_mul_add_neg`
- `suzukiReporterSecantFarBlockEnergy_nonpos`
- `SuzukiNaturalApertureHyperbolaPair.two_mul_shallowLag_le_deepLag`
- `SuzukiNaturalApertureHyperbolaPair.reporterSecantCauchyGram_nonpos`
- `suzukiNaturalApertureFarHyperbolaCauchyEnergy_nonpos`
- `suzukiNaturalApertureCauchyEnergy_le_nearHyperbola`
- `suzukiReporterSecantPacket_anchorCorrelation_eq`
- `suzukiReporterSecantPacket_lowerHardy_sq_le_cauchyEnergy`

All proofs are unconditional and contain no project axioms, `sorry`, `admit`, `opaque`, or
`unsafe` declarations.

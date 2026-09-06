# Literal odd source Gram identification

**Status:** This specific identification is false for the complete theta source. The all-degree logarithmic Hankel route remains open. Positive survivor: arbitrary geometric lower raw-moment bounds and divergence of consecutive raw-moment ratios, proved in Lean without numerical inputs.

## Candidate and exact boundary

Let `m_j=2∫₀∞ x^(2j)Φ(x)dx`, `μ_j=m_j/m_0`, and `F(q)=Σ(-1)^j μ_j q^j/(2j)!`. The logarithmic Hankel kernel is `K(q,r)=(qG(q)-rG(r))/(q-r)`, where `G=-2F'/F`. Clearing denominators gives

`B(q,r)=F(q)F(r)K(q,r)=-2(qF'(q)F(r)-rF'(r)F(q))/(q-r)`.

At every finite degree, multiplication by `F` is an invertible lower triangular congruence since `F(0)=1`. A diagonal sign congruence gives the explicit coefficients

`B⁺_ij=2Σ_(k=0)^min(i,j) (i+j+1-2k) μ_(i+j+1-k) μ_k / ((2(i+j+1-k))! (2k)!)`.

The direct positive source Gram matrix is

`D⁺_ij=μ_(i+j+1)/((2i+1)!(2j+1)!)`.

It is the integral Gram of `x^(2i+1)/(2i+1)!`. Its first row equals the first row of `B⁺`. The conjecture `B⁺=D⁺` in every degree is false. Entrywise positivity of `B⁺` does not imply positivity of its quadratic forms.

## Dependency-closed paper proof and positive survivor

The corpus proves positivity, half-line integrability of every polynomial moment, strict log-concavity, and reflection of the complete source. These imply that `Φ` decreases on the nonnegative half-line. On every interval `[A,A+1]`, with `A≥0`, integration gives the exact bound

`m_n ≥ 2Φ(A+1) A^(2n)` for every `n`.

The coefficient is strictly positive. If `m_n≤C R^n` held for every `n` with `R≥0`, choose `A=R+2`. Division by `A^(2n)` and passage to the geometric limit would imply `2Φ(A+1)≤0`, a contradiction. This proves absence of any fixed geometric upper envelope.

The corpus also proves that `m_(n+1)/m_n` is nondecreasing. If these ratios were bounded, induction would give a geometric upper envelope for `m_n`. Consequently

`m_(n+1)/m_n → +∞`.

For row `1`, column `n+1`, write

`b_n=μ_(n+3)/(2n+5)! + (n+1)μ_1 μ_(n+2)/(2n+4)!`,

`d_n=μ_(n+3)/(6(2n+3)!)`.

The exact identity is

`3(2n+5)!(d_n-b_n)=(n+1)((2n+7)μ_(n+3)-3(2n+5)μ_1 μ_(n+2))`.

Ratio divergence implies `μ_(n+3)>3μ_1 μ_(n+2)` eventually, so `d_n>b_n` eventually. In particular these rows cannot agree at every column. The positive survivor is stronger than a single unequal entry: an all-order growth law and an eventual strict direction for the row deficit.

## Lean status and scope

Module: `GaloisForLFunctions.RHTower.ThetaRawGramGrowthObstruction`.

- `thetaCuspRawEvenMoment_lower_window`
- `thetaCuspRawEvenMoment_no_geometric_upper_bound`
- `tendsto_thetaCuspRawEvenMoment_ratio_atTop`
- `thetaCuspOddRawGramRow_sub_cleared`
- `eventually_thetaCuspOddRawGramRow_gt_cleared`
- `not_thetaCuspClearedOddGramRow_eq_raw`

Lean formalizes the complete-source growth facts, the two explicit coefficient-row expressions, their exact difference, and their eventual strict inequality. The general generating-function/congruence derivation above is a paper identity; this module does not add a formal bridge from the entire two-variable kernel to the existing logarithmic Hankel definition. The row obstruction uses no conjectural positivity hypothesis.

Scratch and source checks, the named leaf audit, and formal lint pass. The module is wired into `RHTower.lean`; no umbrella build is used. All six listed conclusions depend only on `propext`, `Classical.choice`, and `Quot.sound`. No new axiom or numerical premise is used.

## Surviving producer problem

Other source-derived Gram representations remain possible. In particular `B⁺` might be represented by a positive contraction relative to `D⁺`. [Runpod diagnostics](../2-fully-proven/computations/theta-source-gram-comparison-2026-09-06/REPORT.md) support the finite six-shell comparison through degree 12, but neither its infinite-source upper bound nor its lower bound is proved. An upper bound alone does not establish positivity. This card retires only literal equality with the odd-monomial source Gram matrix.

# Growing moments and polynomial cofactor localization

- **ID:** b13-growing-moment-polynomial-cofactors
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean).
- **Obstacle:** B13 / B134.

## Statement

Let `a,κ>0`, `κ≤a/32`, `J≥4`, and `(2J−7)κ≥2a`. Set

`X=exp(at)`, `r=⌊κt/log t⌋`, `U=⌊X/t^(J+1)⌋`, `V=⌊t⌋`,
`W=⌈2t^(J+3)⌉`.

Write `F_r(n)=(ε/t)^r n^(2r−1/2−it)exp(−εn²)`,
`M_r=ΣΛ(n)F_r(n)`, `P_r=∫F_r`, and `L_r=∫log(x)F_r(x)`.
Let `c=Λ_≤U*μ_≤V`, `A=Σ_(b≤UV)c(b)/b`,
`B=Σ_(b≤V)μ(b)/b`, and `D=Σ_(b≤V)μ(b)log b/b`. Define the
actual centred cofactor current

`C_r,U,V,W = Σ_n [(Λ−Λ_≤U)*trunc_≤W(δ−1*μ_≤V)](n)F_r(n)`
`             + B L_r − (1+A+D)P_r`.

For all sufficiently large real `t`, uniformly over `ε∈ℂ` with
`Re ε>0`, `|ε|≤4 Re ε t`, and `Re ε X²=2`,

`|(M_r−P_r)−C_r,U,V,W| ≤ (C+784)exp(−at/4)`,

where `C=1+Γ(1/4)+58[Γ(1/4)+Γ(3/4)]`. Moreover,
`W≤3t^(J+3)`. No hypothesis about zeros enters this reduction.

## Proof

The derivative recursion
`C_0(b)=Γ((b+1)/2)/2`,
`C_(k+1)(b)=(|b|+1)C_k(b−1)+8C_k(b+1)` has envelope

`C_k(k+2j−1/2)≤Γ(1/4)p^p(2p+9)^k/2`

for `p≥1`, `k+j≤p`. Gamma recurrence bounds each terminal value;
each recursive step costs at most `2p+9`. The even Bernoulli bound
then gives `K_r,1/2≤Γ(1/4)(8192r^4)^r`. The logarithmic Gamma
moments give `L_r,1/2≤58[Γ(1/4)+Γ(3/4)](16r^3)^r`.
For `t≥8192`, `1≤r≤t`, these are bounded by the corresponding
constants times `t^(5r)` and `t^(4r)`.

Consequently, when `UVt^J≤X` and `V≤t`, the complete Vaughan error
is at most

`C [X^(1/2)/t^((2J−7)r)+t^(4r+2)X^(−1/2)](1+log X)`.

Eventually the rounded order satisfies
`κt≤2r log t≤2κt`, and the rounded cutoffs satisfy
`UVt^J≤X`, `U≥X/(2t^(J+1))`, and `UW≥Xt²`.
The parameter inequalities reduce the displayed error to
`C(1+t²)(1+at)exp(−3at/8)≤C exp(−at/4)` eventually.

The complementary cofactor coefficient vanishes for `n≤UW` and
has modulus at most `2n²`. Extracting half the Gaussian at `UW`
and estimating the remaining moment at scale `2X` gives the uniform bound

`|tail_r|≤784·32^r(r+1)! X³ exp(−(UW/X)²)`.

For `32≤t`, `r≤t`, one has `32^r(r+1)!≤t^(3r+2)`.
If also `3a≤t`, the tail is at most `784 exp(−t²)`, hence at most
`784 exp(−at/4)`. Absolute convergence identifies the difference
between the complete and truncated centred currents with this tail.
The two signed continuum corrections are identical in both currents.

## Lean declarations

All modules belong to `GaloisForLFunctions.ExceptionalLayerTheory`.

- `GaussianHigherMomentConstants`: uniform derivative, lattice and
  logarithmic constants; five transitive axiom audits passed.
- `GaussianGrowingMomentReduction`:
  `eventually_gaussianGrowingMomentReduction` and explicit order/cutoff
  bounds; final direct source check passed, with four standard-axiom audits.
- `GaussianHigherCofactorTail`:
  `norm_gaussianHigherVaughanCofactorTail_le_gaussian`,
  `norm_gaussianHigherVaughanCofactorTail_le_exp_neg_sq`, and
  `gaussianHigherCentredVaughan_sub_cofactorCurrent_eq`; source and first
  importer olean checks passed; final direct source check passed, with
  three standard-axiom audits.
- `GaussianGrowingCofactorLocalization`:
  `eventually_gaussianGrowingCofactorCutoff_bounds` and
  `eventually_gaussianGrowingMomentCofactorReduction`; final source check passed,
  with two standard-axiom audits.

All four modules passed direct source checks. Their fourteen transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The umbrella imports all four modules; no umbrella build was run.

## Remaining obstacle

The cofactor count is polynomial, but the prime variable remains long.
No bound for the surviving centred current below an exceptional-mode
rate is proved. The growing-order selected-mode/filter transfer also
requires a uniform contour-remainder estimate; fixed-order asymptotics
cannot supply it. B13 remains unresolved. Cancellation is pursued in
`../1-in-progress/b13-centred-cofactor-cancellation.md`.

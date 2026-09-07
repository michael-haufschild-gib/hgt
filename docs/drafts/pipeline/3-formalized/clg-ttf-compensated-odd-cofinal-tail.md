# CLG/TTF compensated odd determinant on the cofinal source tail

- **Stage:** 3-formalized
- **Scope:** Unconditional complete-source cofinal positivity of the odd rank-three determinant, with every fixed compensation coefficient.
- **Full chain:** Literal theta source → every signed center-mixed Hankel section nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.
- **Remaining:** A compact center interval for the next odd block, then a complete all-order positivity argument. Neither global rank-six positivity nor RH is proved.

## Exact infinite-source tail control

Write `q(x)=π exp(2x)`, `φ(x)=thetaCuspSourceTerm x 1`, and `Φ` for the complete source. The corpus gives the exact factorization `Φ=φ(1+R)` on the positive ray, with `R` the Laplace transform of the fixed higher-likelihood measure at coordinate `q−3/2`. Its support gap is three.

Let `M_m` be its tilted moments and `T_m=q^m M_m(q−3/2)`. Every `q^k T_m` tends to zero at infinity. The exact derivative recurrence

`T_m′=2m T_m−2T_(m+1)`

proves the same statement after every fixed number of source derivatives. Consequently, for all natural `k,n`,

`q^k D^n R → 0`.

The first atom's exact derivative polynomial gives a polynomial bound for `|φ^(n)/φ|`. Leibniz expansion of `Φ−φ=φR` therefore proves

`q^k (Φ^(n)−φ^(n))/φ → 0`

for all fixed `k,n`. Expanding each reflected product and its finite Leibniz sum then gives

`q^k (j_n−j_n^first)/φ² → 0`.

These statements retain the entire infinite source. No numerical truncation or derivative-order cutoff is an input.

## Exact positive determinant limit

After extracting `exp(x/2−q)`, the first-atom polynomials satisfy

`P₀(q)=4q²−6q`, `P_(n+1)=(1/2−2q)P_n+2q P_n′`.

Their symbolic reflection identities through order ten give the Gaussian limits

`(-1)^k j_(2k)/(φ² q^k) → 8, 192, 7680, 430080, 30965760`

for `k=1,2,3,4,5`, respectively. Infinite-source error transport proves these limits for the actual native jets. Thus the strict odd leading minor `Δ` and odd rank-three determinant `H` satisfy

`Δ/(φ⁴ q⁴) → 24576`,

`H/(φ⁶ q⁹) → 96636764160 > 0`.

The actual source mass and slope also satisfy `Φ/φ→1` and `Φ′/(φq)→−2`. Since `x/q⁴→0`, the compensation source `G=3Φ²+2xΦΦ′` obeys `G/(φ²q⁵)→0`. Hence, for every fixed real `K`,

`[H+KΔG]/(φ⁶q⁹) → 96636764160 > 0`.

The denominator is strictly positive on the physical ray. Therefore the actual compensated determinant is strictly positive for all sufficiently large centers. The threshold may depend on `K`.

For the canonical source-selected `K_*`, the existing exact seam margin supplies positivity on `0<x<δ`. The cofinal theorem supplies positivity on `x≥X`, with `0<δ<X`. The remaining global comparison is only on `[δ,X]`. These existential endpoints are proved; no explicit finite interval certificate is supplied here.

## Lean landing

- `ThetaCuspAllOrderLikelihoodCooling`: all-order derivative recurrence and polynomial cooling.
- `ThetaCuspFirstAtomAllOrderApproximation`: complete-source relative derivative error.
- `ThetaCuspFirstAtomReflectionJets`: exact first-atom derivative polynomials and reflected jets through order ten.
- `ThetaCuspNativeJetFirstAtomApproximation`: all-order reflection-error transport.
- `ThetaCuspFirstAtomGaussianJetLimits`: five exact rational inverse-scale limits.
- `ThetaCuspNativeOddSchurFarTail`: actual Gaussian jet limits, positive determinant limit, lower-order compensation, and `exists_thetaCuspNativeOddCompensatedDet_positive_ends`.

Each module is checked individually and wired into the RHTower umbrella. Fixed-order asymptotics do not give uniform control over all derivative orders and do not establish the complete RH-equivalent Hankel cone.

Verification: six targeted module checks passed; eight new capstones report only `propext`, `Classical.choice`, and `Quot.sound`. No axioms were added. Formal lint passes, and all 46 new public declaration names have no outside conflicts. No full or umbrella build was run.

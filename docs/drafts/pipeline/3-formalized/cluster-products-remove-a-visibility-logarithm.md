# Cluster products remove a visibility logarithm

- **Stage:** 3-formalized.
- **Type:** THEOREM.
- **Wall:** Π8.
- **Statement:** For a zero of depth `≥δ>0`, height `|γ|≥2`, and at most `n` distinct zeros in `(γ−101,γ+101]`, the level-`R` Hodge index fails whenever `R≥max(e⁶,1/δ)` and `100((n+1)log R + log(A₀(|γ|+4)))≤R`. For ζ, a smooth negative test on `[-(R+1),R+1]` detects depth `≥1/R` at every height `2≤|γ|≤exp(R/(10⁵A₀log R))−306`.

## New mechanism

The existing halving selection gives a smallest killing distance of order `r/(Cn)^(log₂n)`, then charges that smallest distance to every killed root. Retaining the product avoids this loss.

For a finite point set `P`, `#P≤n`, `p∈P`, `0<r≤1` and `λ≥1`, there exist a centre `c∈P` and `0<t≤r` with `‖c−p‖≤r/2`, empty annulus `[t/(2λ),t/2)`, and

`∏_(q∈P, ‖q−c‖≥t/2) min(1,‖q−c‖) ≥ (r/(16λ)²)^(2n)`.

If the annulus around `p` is occupied, take a point at distance `d∈[r/(4λ),r/4)`. The two disjoint balls of radius `d/2` contain at most half the points in one ball. Recurse there with radius `d/4`. Outside that ball every final distance is at least `d/4`; only the retained half pays the next contraction. Induction gives the displayed product bound.

At `r=lowHeightEps0 δ N₀`, `λ=100(n+1)`, the two reflected root products then give a squared profile floor

`unitWeightFloor^(2N₀) · (r/(16λ)²)^(8n) · (δ/2)^4`.

For `R≥e⁶`, `1/δ≤R`, `N₀≤R`, `n+1≤R`, the product base is at least `exp(−8log R)`. The existing split tail estimate therefore costs `O(n log R)` instead of `O(n log²R)`. No separation or multiplicity assumption is added.

## Finite product proof

Put `b=1/(16λ)`. Strong induction on `n`. If `[r/(4λ),r/4)` around `p` is empty, choose `c=p,t=r/2`. Each exterior clipped factor is at least `r/4`, so the product is at least `(r/4)^n ≥ (rb²)^(2n)`.

Otherwise choose `q` at distance `d∈[r/(4λ),r/4)`. The disjoint open balls of radius `d/2` around `p,q` have total cardinality at most `n`. Choose the smaller ball `Q`, centre `c₀`, with `2m≤n`, where `m=#Q<n`. Recurse on `Q` at radius `s=d/4≥rb`. Its selected centre satisfies `|c−c₀|≤d/8`, hence `|c−p|≤9d/8<r/2`. Every point outside `Q` is at distance at least `3d/8≥s` from `c`, so it cannot enter the selected annulus. Its product contributes at least `s^n`; the inner product contributes at least `(sb²)^(2m)≥(sb²)^n`. Multiplying gives `(sb)^(2n)≥(rb²)^(2n)`.

## Reflected products and the complete form

Apply the finite lemma to the distinct transformed zeros in the original height window of half-width `H+1`, with `r=lowHeightEps0 δ N₀` and `λ=100(n+1)`. The chosen zero has depth `δ₁≥δ/2` and height displacement at most `r/2`. The recentered window of half-width `H` lies inside the original window. Both windows are reflection-closed.

Set `η=t/2`, `ε=t/(2λ)`, and kill precisely the recentered-window zeros at distance at least `η` from both `±iδ₁`. The empty annulus puts every other zero within `ε` of one of these centres. Each of the killed-root images, and each reflected image, is an injective subset of the original point set outside the selected annulus. Removing clipped factors increases their product, and removing the clipping increases it again. Thus each distance product is at least `F=(r/(16λ)²)^(2n)`.

The existing phase root makes the central profile value purely imaginary. Its two factors have modulus at least `δ₁`; the polar factors have modulus at least one because the recentered height has modulus at least one. The unit-weight transform has modulus at least `U=unitWeightFloor`. Squaring the profile product gives

`|profile(−iδ₁)|² ≥ U^(2N₀) F⁴ (δ/2)^4`.

The unchanged phase-variation bound is `N₀·4ε+2n·ε/η+2ε+2ε/δ₁≤1/20`. Hence the existing complete Weil-form estimate applies with the new floor and the unchanged split tail constant. This includes every zero and the poles; no discarded cluster or separation premise remains.

## Horizon inequalities

Take `H=100`, `N₀=⌊R⌋`, `ℓ=log R`, `Λ=log(A₀(|γ|+4))`, `R≥e⁶`, `1/δ≤R`, and `100((n+1)ℓ+Λ)≤R`. Then `ℓ≥6`, `Λ≥0`, `n+1≤R`, and `2n+7≤N₀`.

The denominator of `r/(16λ)²` is at most `1536000000 R³≤R⁷`: indeed `R≥400` and `400⁴>1536000000`. Since `δ≥1/R`, this gives `r/(16λ)²≥R⁻⁸=exp(−8ℓ)`. The squared product floor therefore loses at most `64nℓ`, and the depth factor at most `4ℓ+4`.

The existing tail estimates give a gain `4N₀`, overhead `(8n+15)·5+4+5Λ`, and

`(8n+15)·5+4+5Λ < 4N₀−64nℓ−4ℓ−4`.

Subtracting the left side, the size condition bounds the difference below by `336nℓ+396ℓ+395Λ−40n−87>0`. Thus the complete Weil form is negative on a pole-killed test supported in `[-R,R]`.

For ζ, the proved local count gives `n≤202A₀L`, `L=log(|γ|+306)≥1`, and `Λ≤2A₀L`. Hence `10⁵A₀L·log R≤R` implies the required general size condition. Smoothing the negative test increases the aperture by one and gives a `C∞` detector.

## Dependencies and novelty

`ClusterRobustHodgeExclusion`: phase rotation, recentering identities, split tail, complete Weil-form comparison, local ζ count. `SmoothWeilDetectorPolynomialAperture`: smoothing a negative `C²` detector. The previous smallest-distance halving bound costs `n log²R`; the retained product costs `n log R`.

## Lean

Namespace `SquareRootThreshold`; files in `formal/GaloisForLFunctions/SquareRootThreshold/`:

- `ClusterDistanceProducts.lean`: `exists_empty_annulus_with_product`.
- `ReflectedClusterProducts.lean`: `cluster_selection_with_products`.
- `ClusterProductWeilDetector.lean`: `norm_sq_lowHeightProfile_product_ge`, `exists_hodge_violation_cluster_product`.
- `ClusterProductHorizon.lean`: `not_hodgeIndex_below_cluster_product_horizon`, `zeta_hodge_index_cluster_product_horizon`, `zeta_smooth_detector_below_product_horizon`.

All four canonical checks pass; all seven transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Integrated into the SRT umbrella.

## Remaining precision

Π8 partially solved. A logarithmic gap remains between this sufficient aperture and the linear-count Nyquist obstruction; the sharp threshold for arbitrary clusters is open.

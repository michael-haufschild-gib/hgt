# Sharp weighted bounds of a reflected pair

- **ID:** reflected-zero-pair-weighted-spectrum
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For positive decay rates `a,b`, the reflected form on complex `L²(0,∞)` has optimal lower and upper coefficients
  `1/(a+b) ± 1/(2√(ab))`. It is nonnegative on every vector exactly when `a=b`. With `a=p/2+δ`, `b=p/2−δ`, these coefficients are
  `1/p ± 1/√(p²−4δ²)` for `p>2|δ|`. At `0<p≤2|δ|`, compact square-integrable packets of squared mass `2` make the integral pairing arbitrarily negative, at every common ordinate.

## Proof

Write `u_a(t)=exp(-(a+iγ)t)` and
`Q(f)=2 Re(⟨u_a,f⟩ conjugate(⟨u_b,f⟩))`.
The Gram entries are `⟨u_a,u_b⟩=1/(a+b)` and `‖u_a‖²=1/(2a)`.
For normalized vectors `v_a=√(2a)u_a`, the overlap is
`r=2√(ab)/(a+b)`. Polarization and Cauchy–Schwarz give bounds `r−1` and `r+1`; `v_a−v_b` and `v_a+v_b` attain them. Rescaling gives the stated coefficients. Unequal rates give `r<1`, hence a negative direction. At equal rates,
`u_(2a)−(2/3)u_a` is a null vector with squared norm `1/(36a)`, so the zero lower coefficient is also optimal.

For `a>0`, `b≤0`, take
`g_k=1_(0,1]−k⁻¹1_(1,1+k²]`.
Its squared mass is `2`; it vanishes on the nonpositive ray. Its moments obey
`L_a(g_k)≥exp(-a)−1/(ak)` and `L_b(g_k)≤exp(-b)−k`.
Thus their product is arbitrarily negative. Multiplication by `exp(-iγt)` cancels the common phase and preserves squared mass. Compact support makes every real-rate Laplace moment integrable. Interchanging the rates covers both signs of `δ`.

## Lean

Namespace: `GaloisForLFunctions.ArithmeticCorrespondencePositivity.WeightedReflectedPair`.

- `TheWeightedSpectrumOfAReflectedPair.lean`: `weightedPairForm_bounds`, `weightedPairForm_nonneg_iff`, `pairForm_lower_optimal`, `pairForm_upper_optimal`.
- `NondecayingReflectedPairsHaveNoLowerBound.lean`: `exists_compact_packet_below`, `exists_modulated_compact_packet_below`, `exists_weighted_boundary_packet`.

Both production modules passed direct `lake --old env lean` checking without warnings. All seven capstones have exactly `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Both modules are imported by `ArithmeticCorrespondencePositivity.lean`.

## Scope and AAL

These are statements about one reflected pair. The boundary witnesses are compact `L²` packets; no smooth-test approximation or estimate for the complete zeta zero sum is asserted.

Every actual zero has `2|δ|<1`. Therefore existence of some finite `p>1` lower floor is compatible with any finite collection of reflected pairs. The theorem does not compare its sharp constants with a particular arithmetic floor. The proposed gap argument still needs an arithmetic estimate below the exceptional layer's threshold. AAL remains unresolved.

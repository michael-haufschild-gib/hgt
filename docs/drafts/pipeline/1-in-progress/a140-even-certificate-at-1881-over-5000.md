# Even Weil certificate at `1881/5000`

- **ID:** A140-even-1881/5000
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** A positive Weil floor for every even real compact `C²` test on
  `[-1881/5000,1881/5000]`, completing the certified odd sector.

## Formalized ingredients

Direct project checks and standard-only axiom audits passed for:

- `gamma_eq_logarithmic_lag_correlation_moments_and_remainder`:
  `Gamma=L_r+[gammaBracket(0)+r/2−r²/48−r³/48+2Ω(r)]M−mean²/4+C₁/24+C₂/16+∫₀ʳR(t)(A₀−Aₜ)dt`.
  Dropping the nonnegative remainder gives the corresponding lower bound.
- `gamma_mass_constant_at_aperture_1881_over_5000`:
  the bracket above, plus `log 2`, is at least `−14379/10000`
  at `r=1881/2500`, by seven positive exponential modes.
- `even_autocorr_first_moment`, `even_autocorr_second_moment`:
  for `H(x)=∫₀ˣF`, `C₁=a mean²/2−∫₋ₐᵃH²` and `C₂=mean·∫x²F`.
- `even_cosh_pole_ge_two_moments`: the first two Legendre moments retain
  the cosh pole with mass loss `1/50000`.
- `primitive_mass_le_variance_and_two_moments` and its rational form:
  `∫H²≤π⁻²M+(1/3−π⁻²)m₀²−(2/3)m₀m₂` on `[0,1]`.
  Replacing `π⁻²` by `5/49` charges only `M−m₀²≥0`.
- `regionalLogEnergy_ge_gap_sub_low_moments` retains every lower Legendre
  charge at any harmonic cutoff. Its sixth-gap specialization has even
  charges `49/20,19/4,33/10`; Bessel gives mass weights `1/2,5/2,9/2`
  on `[-1,1]`.
- `local_gamma_remainder_ge_half_window_reserve` retains
  `(a⁴/512+31a⁵/1920)M` from disjoint half-windows. At `a=1881/5000`,
  `local_gamma_remainder_ge_at_aperture_1881_over_5000` gives `M/6250`.
- `logarithmic_lag_and_boundary` and `even_logarithmic_lag_and_exterior`:
  every supported `C²` source has the exact regional/boundary decomposition;
  for even sources, `L₂/2=E_reg/4+∫₀¹G²[log 2−log(1−x²)/2]`.

`TheEvenFirstOverlapHasPolynomialReciprocalBounds.lean` passed its direct check.
The two reciprocal bounds and the logarithmic-potential comparison have only
`propext`, `Classical.choice`, `Quot.sound` as transitive axioms.

`firstOverlapEvenCharge_le_energy` passed its direct check and standard-only
axiom audit. For continuous `G`, it proves

`mᵀDm ≤ ∫₀¹U G² − w∫_b¹G(x)G(b+1−x)dx + 10⁻⁶∫₀¹G²`,

with the actual logarithmic `b,w` and the matrix below. This closes the
three-moment capacity estimate; the actual Weil transfer remains open.

## Positive rational capacity matrix

Put `a=1881/5000`, `b=log(2)/a−1`, `w=log(2)/sqrt(2)` and
`G(u)=F(au)`. Use potential
`U(x)=3029/3000+Σ_{j=1}^{32}x^{2j}/(2j)` and reflection energy
`∫₀¹UG²−w∫_b¹G(x)G(b+1−x)`.

Let `ρ=97/50000`, `p₀=1+a²/24+a⁴/1920`, and `p₂=a²/12+a⁴/672`.
The charge matrix is

`D₀₀=49/20+a/2−a²/24−a³/24−4ap₀²−ρ+a²(1/3−5/49)/24`,
`D₂₂=19/4−4ap₂²−5ρ`, `D₄₄=33/10−9ρ`,
`D₀₂=−4ap₀p₂−a³/24−a²/72`, with other off-diagonal entries zero.

Outside the reflected strip set
`V=3029/3000+Σ_{j=1}^{16}x^{2j}/(2j)`,
`q=3000/3029−2449x²/5000−x⁶/20−3x⁸/100`,
`q_out=q(201−100Vq)/101`.
If `1≤Vq≤101/100`, then `q_out≥1/V`. The homogeneous polynomial
certificates for both inequalities passed Lean on `0≤x²≤71/100`;
the pointwise conversion is formalized.
The degree-12 homogeneous certificates using the degree-eight Taylor lower
bounds at `84249/100000`, `9/10`, and `47/50` also passed Lean. The generic
Taylor lower bound and its pointwise conversion are formalized. On the strip use
`q_strip=309/500−21(x−337/400)/20−18(x−337/400)²/5
−150(x−337/400)²(x−23/25)²`.

For `y=b+1−x`, `z=w²q_strip(x)q_strip(y)≤1/10`, the pair inverse is bounded by
`(1+z+z²+1/900)[q_strip(x)p(x)²+2wq_strip(x)q_strip(y)p(x)p(y)+q_strip(y)p(y)²]`.
The bracket is nonnegative and retains the signed mixed term.

At `b_ref=1684993/2000000`, `w_ref=49013/100000`, the inverse charge matrix
dominates the polynomial capacity by `10⁻⁶I`. The reciprocal's shift stays
`337/400`. The bounds `0≤b_ref−b≤10⁻⁸` and
`0≤w_ref−w≤10⁻⁶` are formalized.

The strip integrand is bounded by `6‖v‖²` and its parameter derivative by
`53‖v‖²`. Hence `C_b≤C_ref+10⁻⁷I`; the outside contribution to this
difference is nonpositive. Integrating the pairwise square completion and
applying the positive rational matrix proves the charge estimate above.

## Remaining proof obligations

The rational mass budget leaves a candidate floor `1/50000` after paying
the prime-weight error `≤10⁻⁶`. The even Weil assembly and its transfer to
all block sizes have Lean drafts awaiting checks. The transfer reaches
every window of ratio at most `53/25`, since `log(53/25)<1881/2500`.

The rational matrix alone is not a Weil certificate.

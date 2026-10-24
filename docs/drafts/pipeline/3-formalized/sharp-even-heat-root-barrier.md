# Sharp heat-root barrier and even Hermite extremizers

- **ID:** sharp-even-heat-root-barrier
- **Stage:** 3-formalized
- **Type:** THEOREM (boundary, attainment, asymptotics and exact Xi source bridge formalized in Lean 4)
- **Source:** Arithmetic Local Divisor Geometry; universal finite-degree root obstruction
- **Statement:** The sharp positive-root barrier for a nonnegative real polynomial of degree `2d` whose forward heat has nonnegative coefficients is the largest zero of the probabilists' Hermite polynomial `He_(2d−1)`, in Gaussian units. Evenness is not required; equality forces an even shifted `He_(2d)` extremizer.

## Existing input and scope

`RHTower/XiWardGlobalCapAndFiniteHeadArithmetic` proves heat inversion and the universal obstruction `4λ deg P≤δ²`, using positivity of the inverse-heat Hermite weights. Do not repackage that theorem. The proposed refinement uses the additional double-root condition forced by real-axis nonnegativity, identifies the exact finite-degree boundary, and classifies equality. It does not produce arithmetic positivity for the actual Xi head.

## Precise result

Let `d≥2`, `λ>0`, and let `h_d` be the largest real zero of `He_(2d−1)`. If `P` is a nonzero real polynomial of degree `2d`, `P(x)≥0` for all real `x`, and every coefficient of `E_(λ/2)P` is nonnegative, then every positive root `δ` of `P` obeys

`δ≤sqrt(λ) h_d`.

At equality, necessarily

`P(X)=c λ^d [He_(2d)(X/sqrt(λ))−He_(2d)(h_d)]`, `c>0`.

This polynomial attains the boundary: its heat is `c[X^(2d)−λ^d He_(2d)(h_d)]`, with two positive coefficients. Its only real roots are the double pair `±sqrt(λ)h_d`, and its first nonnegative heat cone occurs exactly at `λ/2`.

## Dependency-closed paper proof

Use the probabilists' normalization `H_n=He_n`, so `H'_n=nH_(n−1)` and `H''_n−xH'_n+nH_n=0`. Its leading coefficient is one, its parity is `n`, and its `n` real roots are simple. These facts already have corpus proofs in `HermiteRealRoots`, `HermitePerturbationRealRoots` and `SpurHermite`; they are inputs, not new contributions.

The largest zero increases strictly with `n≥1`. Indeed `g_n(x)=(-1)^n H_n(x) exp(-x²/2)` vanishes at the largest zero of `H_n` and tends to zero at positive infinity. Rolle's theorem on that half-line gives a zero of `g'_n=g_(n+1)` strictly farther right. Thus every lower-degree `H_j` is strictly positive at the largest zero of `H_n`, and all `H_j`, `j≤n`, are strictly positive beyond it. For `n≥2` the largest zero is positive: `H_1` has largest zero zero, and the same argument applies.

Write `Q=E_(λ/2)P=Σ_(j=0)^(2d) q_j X^j` and `σ=sqrt(λ)`. Heat preserves degree and leading coefficient. Therefore all `q_j≥0`, with `q_(2d)=c>0`. Polynomial heat inversion gives

`P(x)=Σ_(j=0)^(2d) q_j σ^j H_j(x/σ)`.

At a positive zero `δ` of the globally nonnegative `P`, its derivative vanishes. With `x=δ/sqrt λ`,

`0=P'(δ)=Σ_(j=1)^(2d) j q_j σ^(j−1) H_(j−1)(x)`.

For `x>h_d` every term is nonnegative and the leading term is positive, a contradiction. At `x=h_d`, every lower nonconstant summand has a strictly positive Hermite weight. Thus all `q_j=0`, `1≤j<2d`, including every odd coefficient. The root equation then gives `q_0=−c λ^d H_(2d)(h_d)` and the claimed unique polynomial up to `c>0`. Evenness is forced at equality, rather than assumed.

The same argument gives a stronger algebraic engine. For any degree `N≥2`, if `E_(λ/2)P` has nonnegative coefficients, then every real stationary point of `P` lies at or below `sqrt(λ)` times the largest zero of `He_(N−1)`. A stationary point at that boundary forces the heated polynomial to have only constant and leading terms. Requiring that point also to be a root fixes the constant exactly as above. Global nonnegativity is used only to make a positive root stationary and to specify the class in which the even extremizer must attain the bound. A further targeted literature search for the stationary-root formulation did not locate this exact statement; no worldwide novelty claim is made. Non-even polynomials are not claimed to enter the heat cone eventually: their highest odd coefficient may remain negative at every heat.

It remains to prove attainment rather than assume the extremizer is nonnegative. Put `H=H_(2d)`, `n=2d`, and `h=h_d`. At `h`, `H'(h)=0` and `H''(h)=n(n−1)H_(n−2)(h)>0`; the ODE gives `H(h)<0`. The Sonin quantity

`S(x)=H(x)^2+H'(x)^2/n`

satisfies `S'(x)=2x H'(x)^2/n≥0` for `x≥0`. Consequently, for `0≤x≤h`, `H(x)^2≤S(x)≤S(h)=H(h)^2`, so `H(x)≥H(h)`. For `x≥h`, `H'(x)≥0`, hence again `H(x)≥H(h)`. Evenness covers the negative axis. Therefore the displayed extremizer is globally nonnegative, and its heat is the two-term polynomial stated above, with positive constant and leading coefficients.

Moreover `S` increases strictly on every nondegenerate positive interval: its derivative is nonnegative, and the nonzero polynomial `H'` cannot vanish throughout an interval. Thus `H(x)>H(h)` for `0≤x<h`; strict positivity of `H'` gives the same conclusion for `x>h`. The only real roots of the extremizer are `±sqrt(λ)h`, each exactly double since the second derivative there is positive. This yields an exact squared-pair factor times a strictly positive even real cofactor.

The extremizer's first nonnegative heat cone occurs exactly at `λ/2`. An earlier positive heat would violate the root bound just proved, while at heat zero a polynomial with nonnegative coefficients cannot have its positive root. A negative heat cannot be admissible either: applying the compensating positive heat would put the unheated polynomial in the cone, again contradicting its positive root. Positive-time cone preservation gives every later time. Thus its entire admissible set is exactly `[λ/2,∞)`. At first contact its constant coefficient is positive and every nonleading positive even order vanishes. This family complements the unique middle-order contact of the centrally masked pair.

## Actual local-divisor interface

For a pairing-stable Xi radius head `H`, the unnormalized divisor polynomial in `Y` is monic of degree `N=card H`. Its expansion in horizontal displacement, `P(X)=P_(t,H)(X²)`, is even, monic of degree `2N`, and nonnegative on the real axis. These properties retain every central copy. At the ordinate of an off-line pair of depth `δ`, a radius containing that pair gives `P(δ)=0` and `N≥2`. Therefore any coefficient-positive forward heat of this exact polynomial obeys

`δ²≤λ h_N²`.

The positive canonical scalar leaves this inequality unchanged. In contrast, deleting central factors before heat changes the threshold, as the exact masked-pair family proves. The unnormalized source interface is therefore necessary when interpreting an estimate for the actual finite canonical head at a central-zero height. With `N=O(log|t|)`, the barrier has the existing quadratic depth/height scale. Its exact finite-degree constant and equality structure are refined, but real-axis nonnegativity alone cannot improve the limiting constant `4`. A better uniform arithmetic estimate requires a restriction beyond these generic polynomial properties. No such source restriction is proved here.

## Literature and sharpness accounting

The monotonicity of Hermite critical-value magnitudes is classical: [DLMF §18.14(iii)](https://dlmf.nist.gov/18.14.iii) attributes it to Szegő, Theorem 7.6.3. The proof above includes the elementary ODE argument rather than treating that fact as an extra premise. [DLMF §18.16(v)](https://dlmf.nist.gov/18.16.v) gives the largest-zero asymptotic in the physicists' normalization. Rescaling `He_n(x)=2^(−n/2)H_n(x/sqrt 2)` yields `h_d²/(2d)→4`. Thus the existing constant `4` is asymptotically optimal even for even nonnegative polynomials. `tendsto_hermiteDerivativeEdge_sq_div_even_degree` now formalizes this limit by the elementary recurrence proof below, without importing Airy asymptotics as an unproved input.

### Elementary asymptotic proof

There is a direct recurrence proof using the same positive lower Hermite weights as the sharp barrier. Let `a_n` be the largest zero of `He_n`, `n≥2`, and put `r_j=He_j(a_n)/He_(j−1)(a_n)`, `1≤j≤n`. Then `r_j>0` for `j<n`, `r_n=0`, and the three-term recurrence gives `a_n=r_j+(j−1)/r_(j−1)` for `2≤j≤n`. For `1≤k<n`, sum these identities over `j=n−k+1,...,n`. Grouping the interior ratios gives

`k a_n = Σ_(i=n−k+1)^(n−1)(r_i+i/r_i)+(n−k)/r_(n−k)`.

Each interior summand is at least `2sqrt(i)`, because `(r_i−sqrt(i))²≥0` and `r_i>0`. Consequently

`a_n≥2(k−1)sqrt(n−k+1)/k`.

The existing corpus theorem `pow_half_le_aeval_hermite` gives `He_n(x)≥(x/2)^n>0` whenever `x≥2sqrt(n)`, so `a_n<2sqrt(n)`. After squaring and dividing by `n`, first letting `n→∞` with fixed `k` and then `k→∞` proves `a_n²/n→4`. This recurrence proof is the preferred Lean route: it reuses the positivity and recurrence already needed for the exact boundary and introduces no matrix representation.

For an independent paper check, the same lower bound follows from the finite Jacobi matrix:

Let `A_n` be the real symmetric `n×n` matrix with zero diagonal and entries `sqrt(j)` between coordinates `j−1,j`, for `1≤j<n`. Expanding its characteristic determinant at an endpoint gives `D_n(x)=xD_(n−1)(x)−(n−1)D_(n−2)(x)`, with `D_0=1,D_1=x`. Hence `D_n=He_n`, and its largest eigenvalue is the largest Hermite zero `a_n`.

For any real vector `v`,

`vᵀA_nv=2Σ_(j=1)^(n−1)sqrt(j)v_(j−1)v_j ≤ 2sqrt(n−1)‖v‖²`,

using `2uv≤u²+v²` termwise. Consequently `a_n≤2sqrt(n−1)`. For `1≤k≤n`, take `v=1` on the last `k` coordinates and zero elsewhere. Its Rayleigh quotient is

`(2/k)Σ_(j=n−k+1)^(n−1)sqrt(j) ≥ 2(k−1)sqrt(n−k+1)/k`.

Therefore

`4((k−1)/k)²(1−(k−1)/n) ≤ a_n²/n ≤ 4(1−1/n)`.

First let `n→∞` with fixed `k`, then let `k→∞`. This proves `a_n²/n→4`. Taking `n=2d−1` gives `h_d²/(2d)→4`. The spectral variational inequality used here follows directly by diagonalizing the real symmetric matrix. No zero approximations or numerical experiments enter the argument. Together with the explicit extremizers, this proves that any smaller universal coefficient than `4` in a depth-squared/degree obstruction fails within the even nonnegative class.

The possible contribution is the exact heat-cone barrier, equality rigidity and sharp extremizing family, not the classical root asymptotic, heat inversion or Sonin monotonicity. Initial searches did not locate this exact combined statement; that is not proof of worldwide novelty. All arithmetic source inequalities remain open.

## Central masking is not extremal at fixed degree

Fix positive squared depth `a` and degree `2m+4`. Among all even nonnegative polynomials of that degree with a root at `sqrt(a)`, the smallest possible first polynomial heat time is

`a/(2h_(m+2)²)`.

The barrier proves the lower bound, and the scaled Hermite extremizer attains it. A first time exists for each polynomial in this class: the positive leading coefficient eventually dominates every even heat coefficient, of which there are finitely many; the cone is closed and preserved by further positive heat, and the positive root excludes nonpositive admissible times. By contrast, `X^(2m)(X²−a)²` has exact first time `aτ_m`. Their ratio is `2h_(m+2)²τ_m→2`, from `h_(m+2)²/(2m+4)→4` and `(8m)τ_m→1`. Thus concentration of the remaining degree at the center costs asymptotically twice the optimal heat budget. Degree and depth alone do not identify the centrally masked model as extremal; the complete cofactor matters. The Lean proofs are `isLeast_fixed_depth_heat` and `tendsto_central_to_optimal_heat_times` in `HermiteOptimalHeat.lean`.

## Lean implementation

All modules below belong to `formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/`.
Declarations share the namespace `GaloisForLFunctions.ArithmeticLocalDivisorGeometry`.
Here `hermiteEdge n` is the largest zero of `He_(n+1)`, so the paper's
`h_d=hermiteEdge (2d−2)`. The family parameter is `m=d−2`, its degree is
`2m+4`, and its edge is `hermiteEdge (2m+2)`. The Gaussian standard deviation
is `r=sqrt(λ)`.

| Module | Verified declarations |
|---|---|
| `HermiteHeatNormalization.lean` | `forwardPolyHeat_neg_half_X_pow`, `forwardPolyHeat_half_hermite` |
| `HermiteRootEdge.lean` | `hermiteEdge_strictMono`, `hermite_eval_pos_at_edge`, `hermite_second_derivative_edge_pos` |
| `PolynomialHeatDilation.lean` | `forwardPolyHeat_comp_dilation`, `coeffNonneg_heat_dilation_iff` |
| `HermiteSonin.lean` | `hermiteSonin_strictMonoOn`, `hermite_edge_strict_min_nonneg` |
| `HermiteHeatRootBarrier.lean` | `nonnegative_root_le_sqrt_mul_hermiteEdge`, `scaled_nonnegative_edge_root_rigidity` |
| `HermiteExtremizers.lean` | `hermiteExtremizer_nonneg`, `scaledHermiteExtremizer_eval_eq_zero_iff`, `coeffNonneg_heat_scaledHermiteExtremizer_iff`, `nonnegative_boundary_eq_scaledHermiteExtremizer` |
| `HermiteExtremizerFactorization.lean` | `scaledHermiteExtremizer_positive_cofactor`, `scaledHermiteExtremizer_rootMultiplicity` |
| `HermiteEdgeAsymptotics.lean` | `hermiteEdge_block_lower`, `tendsto_hermiteEdge_sq_div_degree`, `tendsto_hermiteDerivativeEdge_sq_div_even_degree` |
| `EvenPolynomialHeatCone.lean` | `eventually_coeffNonneg_heat_of_even`, `exists_first_heat_time_of_even_nonnegative_root` |
| `HermiteOptimalHeat.lean` | `isLeast_fixed_depth_heat`, `hermite_degree_constant_optimal`, `tendsto_central_to_optimal_heat_times` |
| `SourceDivisorGeometry.lean` | `localDivisorPolynomial_degree`, `horizontalDivisorPolynomial_monic`, `horizontalDivisorPolynomial_even`, `horizontalDivisorPolynomial_nonneg`, `radiusHead_depth_sq_le_hermite_edge` |

The asymptotic proof sums the quotient recurrence over a terminal block, obtaining
`2k sqrt(n+2) ≤ (k+1) hermiteEdge(n+k+1)`. With `c_k=4(k/(k+1))²`, an eventual
lower bound for `hermiteEdge(j)²/(j+1)` tends to `c_k`, while `c_k→4`; the power
bound supplies the upper bound `4`. The order characterization of convergence
finishes the proof without spectral or Airy inputs. Dilation and Sonin monotonicity
are proved internally, rather than passed as assumptions.

## Verification gates

- [x] Corpus and targeted primary-literature audit; classical ingredients identified, no worldwide novelty claim.
- [x] Dependency-closed paper proof of the boundary, attainment, equality, exact divisor and asymptotics.
- [x] All eleven modules above passed final plain `lake --old env lean <module>.lean` checks from `formal/`.
- [x] Transitive axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] All eleven modules are wired into the programme umbrella; no umbrella build was run.
- [x] Temporary audit commands, duplicate drafts and scratch proof files removed. No numerical experiments, placeholders, added analytic assumptions or proof-limit overrides.
- [x] Exact actual-source degree, multiplicity and own-ordinate Hermite obstruction verified in `SourceDivisorGeometry.lean`.

Boundary, attainment, asymptotics and source-bridge verification are complete. Audit evidence includes
`/tmp/hgt_<module>_final.log`, the clean factorization/optimality logs, and
`/tmp/aldg_<module>_check4.log`. The final source check and transitive audits are in
`/tmp/aldg_SourceDivisorGeometry_final2.log`, with exit status zero. The radius-head
theorem retains its stated heat-cone premise; no arithmetic source-sign estimate is asserted.

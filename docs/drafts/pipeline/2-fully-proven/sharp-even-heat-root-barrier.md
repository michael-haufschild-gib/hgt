# Sharp heat-root barrier and even Hermite extremizers

- **ID:** sharp-even-heat-root-barrier
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean formalization pending)
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

The monotonicity of Hermite critical-value magnitudes is classical: [DLMF §18.14(iii)](https://dlmf.nist.gov/18.14.iii) attributes it to Szegő, Theorem 7.6.3. The proof above includes the elementary ODE argument rather than treating that fact as an extra premise. [DLMF §18.16(v)](https://dlmf.nist.gov/18.16.v) gives the largest-zero asymptotic in the physicists' normalization. Rescaling `He_n(x)=2^(−n/2)H_n(x/sqrt 2)` yields `h_d²/(2d)→4`. Thus the existing constant `4` is asymptotically optimal even for even nonnegative polynomials. This asymptotic corollary is not yet Lean-formalized here; the elementary proof below avoids importing Airy asymptotics as an unproved input.

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

The barrier proves the lower bound, and the scaled Hermite extremizer attains it. A first time exists for each polynomial in this class: the positive leading coefficient eventually dominates every even heat coefficient, of which there are finitely many; the cone is closed and preserved by further positive heat, and the positive root excludes nonpositive admissible times. By contrast, `X^(2m)(X²−a)²` has exact first time `aτ_m`. Their ratio is `2h_(m+2)²τ_m→2`, from `h_(m+2)²/(2m+4)→4` and `(8m)τ_m→1`. Thus concentration of the remaining degree at the center costs asymptotically twice the optimal heat budget. Degree and depth alone do not identify the centrally masked model as extremal; the complete cofactor matters. This corollary depends on the exact barrier, its attainment and both established paper asymptotics. Its Lean proof must wait for the Hermite edge limit.

## Lean implementation route

- `HermiteHeatNormalization.lean` is a corrected, still unchecked draft of the unit identities `E_(-1/2)X^n=He_n` and `E_(1/2)He_n=X^n`. It uses the existing three-term/derivative recurrence and the checked local heat semigroup. These are classical support identities, not a novelty claim.
- Define `hermiteEdge n` as the largest root of `He_(n+1)`, using `gaussianDerivZeros` and `card_roots_toFinset_hermite` from `HermiteRealRoots`. The existing half-line Rolle theorem gives strict increase; `hermiteEdge 0=0`. The polynomial sign theorem beyond all roots gives all lower Hermite weights positive at an edge. API checks are prepared in `/tmp/aldg_edge_api.lean` and must pass before using new mathlib names in the implementation.
- Reuse `hermiteReal`, `derivative_hermiteReal_succ`, parity and the recurrence from `HermitePerturbationRealRoots`. The ODE is already in `SpurHermite`; the power lower bound is in `HermiteGaussianMomentBounds`. Do not claim these classical ingredients as new.
- For asymptotics, avoid matrix formalization. With `N=n+k+2`, sum the quotient recurrence at the largest zero of `He_N` over the last `k+1` rows. The result is `(k+1)·hermiteEdge(n+k+1)≥2k sqrt(n+2)`. This parametrization avoids subtraction in the finite sums; use `sum_range_succ` and `sum_range_succ'` to expose the two boundary terms.
- For the limit, the weaker squared bound with `n` instead of `n+2` suffices. Put `c_k=4(k/(k+1))²`. For the full edge sequence `f_j=hermiteEdge(j)²/(j+1)`, eventually in `j`, `c_k[(k+2)j/(j+1)−(k+1)]≤f_j<4`. For fixed `k` the lower function tends to `c_k`, and `c_k→4`. Both limits use the already verified `tendsto_natCast_div_add_atTop 1`. Apply the order characterization of convergence. This gives the classical largest-root asymptotic without an imported unproved analytic premise.
- General Gaussian scale follows from polynomial heat dilation: `E_s(P(rX))=(E_(sr²)P)(rX)`. A corpus search found translation commutation and monomial scaling, but no generic real dilation lemma. A short proof should use polynomial induction and the `X` commutator, with `D(P(rX))=rP'(rX)`. Positive dilation preserves the coefficient cone by the checked `coeffNonneg_positive_rescale_iff`.

## Verification gates

- [x] Corpus and targeted primary-literature audit; classical ingredients identified, no worldwide novelty claim.
- [x] Verify root monotonicity, ODE, global-minimum and equality arguments without extra premises.
- [x] Dependency-closed paper proof of the exact finite-degree theorem, including normalization. For `d=2`, `h_2=sqrt 3` and the extremizer is `c(X²−3λ)²`.
- [ ] Lean formalization in the programme folder and transitive axiom audit.

No numerical experiments or source-sign hypotheses are used. Formalization must prove the finite-degree boundary, attainment and equality law, rather than inserting Hermite positivity or the global minimum as a new premise.

## Interrupted formalization state

The user cleared the goal before this theorem's Lean gates closed. Complete unchecked drafts
`HermiteRootEdge.lean`, `HermiteSonin.lean`, `PolynomialHeatDilation.lean` and
`HermiteHeatRootBarrier.lean` are preserved in the programme folder and are not wired into
the umbrella. The barrier draft includes the stationary bound, all intermediate coefficient
vanishing at equality, root rigidity and arbitrary Gaussian scale. `HermiteExtremizers` and
`HermiteEdgeAsymptotics` are not yet written. The programme card records exact verification
state and the resumption sequence. No full sharp-barrier result is claimed formalized.

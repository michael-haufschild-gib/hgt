# Quadratic Hausdorff shift region

- **ID:** hausdorff-quadratic-saddle-region
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Σ73, `docs/reports/review-0511/walls-ledger.md`
- **Statement:** There is a constant `C > 0` such that the actual calibrated Hausdorff entry `D(k,r)` is nonnegative whenever `r ≥ C(k+1)²`.

## Mathematical target

Write `p=k+1`, `R=primeArchEndpointHausdorffRadius` and
`f(z)=z^(−2p)(R−z^(−2))^r`. The existing explicit shift is cubic in `p`.
A quadratic bound certifies a new infinite region of the actual array.
Full row positivity remains stronger.

The real saddle is `s²=(p+r)/(pR)`, with width `w=s/√p`.
The logarithmic derivative is

`f′(z)/f(z)=−2[pRz²−(p+r)]/[z(Rz²−1)]`.

Thus the two factor phases cancel at `s`. For a zero `s+t+iδ`, `|δ|<1/2`,
the phase near the saddle is of order `|t|/w²`, while the real profile
decays on scale `w`. When `r/p²` is sufficiently large, the phase-positive
band contains the mass-bearing band with exponentially small tails.

## Proof [PROVED HERE]

All constants below are independent of `p,r`. They may depend on the fixed
radius `R` and the unconditional zero-count remainder. Put
`M=f(s)>0`, `w=s/√p`, and assume initially that `p,w` exceed fixed constants.
It suffices to prove positivity under those assumptions and `r≥200p`.

1. **Normalized logarithm.** For `u=(z−s)/s` and `a=p/r`,
   `f(z)/M=exp H(u)`, where
   `H(u)=−2p log(1+u)+r log(1+a[1−(1+u)⁻²])`.
   If `a≤1/8` and `|u|≤1/4`, the logarithms are in the right half-plane.
   The identity `1−(1+u)⁻²−2u=−u²(3+2u)/(1+u)²` gives
   `|H(u)|≤11p|u|²`, using `|log(1+v)−v|≤|v|²` for `|v|≤1/2`.
   Differentiation gives
   `H′(u)=−2p(1+a)u(2+u)/[(1+u)³(1+a[1−(1+u)⁻²])]`.
   The denominator has modulus at least `(3/4)³(7/8)`; hence
   `|H′(u)|≤16p|u|`.

2. **Positive band.** Write a centered zero as `γ+iδ`, replacing it by its
   negative if necessary so `γ>0`; the atom is even and `|δ|<1/2`.
   Integrating `H′` vertically from its real argument gives
   `|Im H|≤8|γ−s|/w²+4/w²` when `|γ−s|≤s/8` and `s≥4`.
   Thus the atom has nonnegative real part whenever
   `|γ−s|≤h=min(s/8,w²/64)` and `w≥4`.
   On the smaller band `|γ−s|≤w/10`, `w≥32`, the quadratic bound gives
   `|H|≤11(1/100+1/(4w²))<1/4`, so `Re f(γ+iδ)≥M/2`.

3. **Real profile and transverse modulus.** For `t=γ/s≥1/4`,
   `log(f(γ)/M)≤−p Φ(t)`, where `Φ(t)=2log t+t⁻²−1`:
   apply `log(1+x)≤x` to `x=(p/r)(1−t⁻²)`; `1+x>0` follows from `r≥200p`.
   Since `log t≥1−1/t`, `Φ(t)≥(t−1)²/t²`.
   Consequently `f(γ)≤M exp(−(γ−s)²/(16w²))` for `γ≤4s`.
   For `t≥4`, `log t≥1`, giving `f(γ)≤Mt⁻p`.
   If `γ²≥2/R` and `δ²≤γ²`, direct expansion gives
   `|R−(γ+iδ)⁻²|²/(R−γ⁻²)²≤1+32δ²/(Rγ⁴)`.
   Also `|γ+iδ|⁻²p≤γ⁻²p`. Therefore, for `γ≥s/4`,
   `|f(γ+iδ)|≤exp(1024/w²)f(γ)≤e f(γ)` once `w≥32`.

4. **Low ordinates.** Apply
   `norm_hausdorffAtomTerm_le_of_threshold_lt` with `K=10p` and
   `T²=r/(10pR)`. Its hypotheses hold once `r≥200p` and `T≥500`.
   Every `γ≤s/4` lies above the thermal threshold: the contrary would give
   `γ≥(97/100)T>s/4` by `ordinate_ge_of_xiThermalNode_le_inv_sq`.
   The resulting norm bound, divided by `M`, is at most
   `41^p(1+p/r)^(p+r)exp(−99p/10)≤exp(−4p)`.
   Here `log 41<4`, `log(1+p/r)≤p/r`, and `p/r≤1/8` suffice.

5. **Counting and summation.** The theorem
   `exists_xiZeroCount_routeKSmoothRVMCount_log_remainder`, together with
   `xiSymmetricMass_diff_eq_card`, gives the following bounds for large `s`:
   the band `|γ−s|≤w/10` contains at least `c w log s` multiplicity copies
   when `w` exceeds a fixed constant; every interval of length `w` inside
   `[s/8,5s]` contains at most `Cw log s` copies. These follow by subtracting
   the counting formula: its smooth derivative is comparable to `log s`
   there, and the two remainders total `O(log s)`.
   The total count below `s` is `O(s log s)`.

   Partition `[s/4,4s]` by `n=floor(|γ−s|/w)`. Each shell has at most
   `C(n+1)w log s` copies. Outside the positive band,
   `(|γ−s|/w)²≥min(p,w²)/4096`. Splitting the Gaussian exponent extracts
   `exp(−min(p,w²)/131072)` and leaves at most `exp(−n²/32)≤exp(−n/32)`.
   Since `(n+1)exp(−n/32)≤64exp(−n/64)`, summation gives a possible negative
   contribution at most `CMw log s · exp(−min(p,w²)/131072)`.
   For `γ≥4s`, group by `n=floor(γ/s)≥4`. The global count gives at most
   `2(n+1)²s log s` copies per shell. For `p≥4`,
   `n⁻p≤256·4⁻p n⁻4`; the inverse-square sum therefore bounds this tail by
   `CMs log s · 4⁻p`.
   Low ordinates contribute at most `CMs log s · exp(−4p)`.

   Thus the real zero sum divided by `Mw log s` is bounded below by
   `c−C exp(−c min(p,w²))−Cp(4⁻p+exp(−4p))`, using `s/w=√p≤p`.
   Choose fixed lower bounds for `p` and `w` making this positive.
   Absolute convergence is supplied by `summable_xiCentralScaledHausdorffTerm`;
   `scaledHausdorffMomentDifference_eq_re_xiCentralSum` identifies the sum
   with the actual calibrated source entry.

6. **Uniform quadratic threshold.** Since `w²=(p+r)/(p²R)`, increasing a
   constant `C` makes `r≥Cp²` ensure every required lower bound for `w,s,T`
   and `r/p`. Only finitely many positive integer `p` remain below the chosen
   lower bound. Increase `C` again to dominate their existing fixed-order
   thresholds `explicitPrimeArchHausdorffShift(p−1)/p²`. Those rows are
   nonnegative by `scaledHausdorffMomentDifference_nonneg_of_explicit_shift_le`.

## Lean theorem

`GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle.exists_quadratic_scaledHausdorffMomentDifference_nonneg`
in `formal/GaloisForLFunctions/SquareRootThreshold/EffectiveHorizons/HausdorffQuadraticRegion.lean`.
The complete complementary sum is bounded in `HausdorffZeroSum.lean`; the final theorem
has no analytic premises. `C` is the closed form `hausdorffQuadraticConstant`
(`scaledHausdorffMomentDifference_nonneg_of_quadratic_le`): the zero counts of step 5 are the absolute-constant
bounds of `ZeroConfigurationGeometry/EffectiveHeights/TwoSidedZetaCount.lean`. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates

- [x] Corpus novelty and exact-source identification.
- [x] Dependency-closed paper proof.
- [x] Lean proof and transitive axiom audit.

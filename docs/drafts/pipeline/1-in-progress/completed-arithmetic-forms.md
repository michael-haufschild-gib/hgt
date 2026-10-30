# Completed arithmetic forms

- **ID:** completed-arithmetic-forms
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../reports/review-2910/astra.md
- **Statement:** Quantitative source comparison preserving radicals, domains, cross terms, and
  endpoint precision under the required limits.

## Mathematical scope

1. Native signed theta successors from rank seven to arbitrary rank.
2. Completed macroscopic Weil overlap comparison and profile-compatible exhaustion.
3. Actual signed coalescent surplus at most \(N/18+o(N)\) in compatible windows.
4. Euler-deletion cumulative covariance and infinite-tail control at inner-cutoff scale.
5. Complete Suzuki rectangular and CCM first-clock source lower bounds.
6. Universal exclusion of actual theta-clock guarded zeros.
7. Arithmetic upper control of the complete Hecke defect or index.
8. Actual Chebyshev energy or detector Gram improvements yielding specified zero strips.
9. Quantitative source transfers without assuming the missing signs.

## Arithmetic comparison metric

For the exact divisor-conductor kernel
\[
B_Q(i,j)=\sum_{m\mid Q,\ m\ne1}G_m(i,j)=Q\min(i,j)-ij,
\qquad 0\le i,j\le Q,
\]
the completed energy satisfies
\[
4E_Q(a)=Q\bigl[(\sum_i a_i)^2+\sum_i a_i^2\bigr]+R_Q(a),\qquad R_Q(a)\ge0.
\]
The interior radical is zero. The inverse is the Dirichlet second difference divided by `Q`.
For a coupling extended by zero at both endpoints, its exact Schur cost is
`Σ_(0≤i<Q)(b_(i+1)-b_i)²/Q`, attained at the inverse coefficient vector.

Lean: `CompletedArithmeticForms/CyclotomicCoercivity.lean` and
`CompletedArithmeticForms/DirichletSchurCost.lean`.

The arithmetic estimate still required for the overlap problem identifies the actual mixed
coupling in these coordinates and controls its Dirichlet cost together with the complete residual.

A conditional complete-Weil comparison does not discharge the actual source remainder estimate.

For a neutral prime packet in `(P,2P]`, `P≥2`, odd support gives the complete-source
bound `Σ a_p²≤2 primePacketBilinear(S,S,a,a)`. Nonadjacent support has exact
coefficient variation `D(C)=2ΣC²`; the arithmetic Schur inequality at `C/2`
transfers this half reserve through the actual first-jump source comparison.

Lean: `CompletedArithmeticForms/SeparatedPacketReserve.lean`,
`primePacket_odd_coefficient_reserve`.

For increasing nodes `0=k₀<…<k_N=Q`, restriction has exact minimum extension
cost `min D_Q(u)=Σ_i (b_(i+1)−b_i)²/(k_(i+1)−k_i)` with all node values fixed
and both endpoints zero. The minimizing extension is the normalized complete
conductor potential of the irregular slope difference. If the nodes contain a
neutral prime block and `Q=2P+2`, this same gap energy pays the actual prime coupling.

Lean: `CompletedArithmeticForms/OptimalInterpolation.lean`,
`meshDirichletEnergy_isLeast_extension` and `primePacket_mesh_schur_bound`.

The mixed gap pairing defines exact constraint projections
`P_g b=b−(<b,g>_D/D(g))g`. For `v=P_g h`, `u=P_v(P_g b)`, the constrained
conductor supremum is attained at `L_k u` and equals
`D(u)=D(b)−<b,g>_D²/D(g)−<P_g b,v>_D²/D(v)`.
Zero-energy profiles contribute zero; dependent constraints require no exception.
The radical consists exactly of interior couplings in `span{g,h}`.
For `g=1`, `h=log k_i` with zero endpoints, the actual neutral prime source pays
its unchanged coupling by `D(u)≤D(b)`.

Lean: `CompletedArithmeticForms/NeutralPacketDual.lean`,
`meshDoubleNeutralSchurCost_isGreatest`, `meshDoubleProjection_energy_eq_zero_iff`,
and `primePacket_neutral_mesh_schur_bound`.

## Accumulation and simultaneous truncation

For arbitrary increments, `a_j=c_j/j` identifies cumulative covariance with
`E_(T+1)(a)/(T+1)`. Its exact positive remainder controls both the weighted mass square
and weighted coefficient square mass. A coupling `b_j` has local variation payment
`D_(T+1)(j b_j)` with zero boundary values.

For actual Euler-deletion increments,
`0≤fullErrorEnergy−cumulativeEnergy≤(M+1)²/(T+1)` simultaneously in `X`, `M`, and `T`.
This bounds the literal omitted tail; the source upper estimate at the inner cutoff remains.

Lean: `CompletedArithmeticForms/DivisorCovariance.lean`.

## Native source error scale

At source scale `q≥2k+6` and `x>0`, the complete Gaussian-normalized signed moment
and its first-atom value satisfy

`|σ_k(x)−σ_k^(1)(x)|≤27·24^(2k) q^k ε(x)`,

where `ε(x)=regimeOneLikelihoodScale x` has an explicit exponentially decreasing
upper envelope. This is an all-order bound with visible order dependence, rather
than an assertion about a truncated theta source.

Lean: `RHTower/ThetaCusp/ThetaCuspEffectiveTailScale.lean`,
`RHTower.abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective`.

The complete balanced source has exact fixed-rank successor limit
`C_(N,s)=16^(s+2N)(1/2)_s N!(s+1/2)_N`. On a rank-dependent ray its entire
head lies strictly between one half and three halves of the Gamma head.
Its successor-to-diagonal ratio tends to `N!/(s+1/2+N)_N≤(2/3)^N`.
No positive diagonal-relative reserve survives uniformly in rank, even with
rank-dependent horizons. The full Gamma norm and the exact `C_(N,s)` are the
positive comparison objects.

Lean: `CompletedArithmeticForms/GammaSuccessorReserve.lean` and
`CompletedArithmeticForms/NativeTailReserve.lean`.

For an odd-zero sequence `s(2k)=m_k`, the full head is exactly the orthogonal sum
of the unshifted head of dimension `ceil(N/2)` and the once-shifted head of dimension
`floor(N/2)`. Determinants multiply; strictness and semidefiniteness require exactly
both blocks. Every fixed full signed complete-native head is consequently positive
definite on a rank-dependent cofinal source ray.

Lean: `CompletedArithmeticForms/SignedParityTransfer.lean`,
`finiteHankelMatrix_parity` and `nativeSignedHead_posDef_eventually`.

For every first-atom center, some signed reflection moment is negative and a finite
full signed Hankel head fails positive semidefiniteness. Its entire imaginary-axis
profile satisfies `g(π/2)>g(π)`, contrary to the monotonicity forced by nonnegative
Taylor coefficients. The least negative moment order `ν(x)` is finite everywhere
and tends to infinity along the source tail. Every fixed shifted balanced head is
positive definite on a rank-dependent ray. Thus the obstruction has an escaping
order, while no common ray gives first-atom positivity at every order.

Lean: `CompletedArithmeticForms/FirstAtomRankBoundary.lean`,
`exists_firstAtom_signed_head_not_posSemidef` and `firstAtomNegativeOrder_tendsto`.

The least full signed Hankel dimension failing semidefiniteness, `κ(x)`, is finite
at every center, satisfies `κ(x)≤ν(x)+1`, and tends to infinity. All smaller full
heads are semidefinite at that center; every fixed full head is strictly positive
on its own cofinal ray. This invariant detects mixed failure before a negative
diagonal is required to appear.

Lean: `firstAtomSignedHead_posDef_eventually`,
`firstAtomSignedHead_posSemidef_below_failureRank`, and `firstAtomFailureRank_tendsto`.

With `H=exp(4π)` and `q=π exp(2x)`, the exact all-center estimate is
`2^(2ν(x))≤exp(2q(H+1))*((2q−3)²+12q(H+1))/(6q)`.
For `x≥0`, both ranks have the explicit ceilings
`ν(x)≤C_*q`, `κ(x)≤1+C_*q`, where `C_*=(9exp(4π)+2)/(2log 2)`.
Cauchy's coefficient bound on radius `2π` makes a nonnegative Taylor head
incompatible with the literal decrease `g(π/2)−g(π)≥24qC` unless this order bound holds.
The constant is coarse; sharp lower growth and compact-center compensation remain.

Lean: `CompletedArithmeticForms/FirstAtomEffectiveRankBoundary.lean`,
`firstAtomNegativeOrder_pow_bound` and `exists_firstAtom_signed_head_failure_le_scale`.

With `D=exp(4+2exp 2)*(24+10exp 2)`, the literal first-atom normalized moments obey
`|σ_k^(1)(x)−γ_k|≤(2k)!D/q` for every `k` at `q≥3`, where
`γ_k=16^k(1/2)_k=4^k(2k)!/k!`. Thus `q>D K!` implies `K<ν(x)`.
The sufficient center `max(0, log((D K!+1)/π)/2)` is explicit.

For every positive definite matrix `G`, `Σv_i²≤tr(G⁻¹) vᵀGv`.
An entrywise perturbation bounded by `ε` therefore has relative cost `N ε tr(G⁻¹)`.
For `G_(N,s)=[γ_(i+j+s)]`, its inverse trace `T_(N,s)` is the diagonal cofactor
sum divided by the exact Gamma determinant. The first-atom shifted head has
relative error at most `N T_(N,s) (2(s+2N))!D/q`.
With `E=ceil(R/2)`, `O=floor(R/2)`,
`q≥3+2D[E T_(E,0)(4E)!+O T_(O,1)(2+4O)!]` implies `R<κ(x)`.

Lean: `FirstAtomGaussianHorizon.lean`, `InverseTraceStability.lean`, and
`FirstAtomMixedHorizon.lean` in `CompletedArithmeticForms`.

The complete native moments satisfy the simultaneous bound
`|σ_k(x)−γ_k|≤C_L/q` for `k≤L`, `q≥2L+6`, where
`C_L=(2L)!D+27·24^(2L)·(exp(3π)/399)·(L+1)!`.
This retains the literal infinite theta remainder through its exponential likelihood scale.
The complete shifted head has relative cost `N T_(N,s) C_(s+2N)/q`.
Every full signed native rank `R` is strictly positive whenever
`q≥2(R+1)+6+2[E T_(E,0) C_(2E)+O T_(O,1) C_(1+2O)]`.
The corresponding half-logarithmic source horizon is explicit; the integrated compact-center
contribution remains a separate signed source estimate.

Lean: `CompletedArithmeticForms/NativeGaussianHorizon.lean`,
`nativeScaledEvenJet_gaussian_error_le_through`, `nativeBalancedHead_relative_error_le`,
and `nativeSignedHead_posDef_of_horizon`.

An ordering of complete successor Hankel forms orders their exact Schur reserves,
provided the preceding heads are strict. A relative full-form error `η<1` gives
the same relative error in the successor, without an additional inverse cost.
For `M=N+1`, `L=s+2M`, and `A=M T_(M,s) C_L`, the literal native reserve obeys
`|S_N(σ_s(x))−C_(N,s)|≤(A/q) C_(N,s)` at `q≥2L+6` and `q>A`.
Thus `q≥2L+6+2A` places it strictly between `C_(N,s)/2` and `3C_(N,s)/2`.

Lean: `CompletedArithmeticForms/SuccessorComparison.lean` and
`CompletedArithmeticForms/NativeSuccessorHorizon.lean`,
`successorSchur_relative_error` and `nativeBalancedSuccessor_half_bounds_of_horizon`.

The exact coordinate `u=arsinh(t/√q)` transforms the literal first-atom pair into
`ρ_x(t)=C exp(−4t²)(B−24t²)`, with `B=(2q−3)²` and `C=4q²exp(x−2q)`.
Its signed moments are `C[(B−3)γ_k+(3/8)γ_(k+1)]=Cγ_k(B+6k)`.
For `B≥3`, every shifted and full signed head is positive definite at this same
center. Every `x≥0` satisfies this range. The inverse nonlinear pullback
`ρ_x(√q sinh u)` is exactly the physical first atom, which has finite failing
rank at every center. Invertible nonlinear source clocks therefore need not
preserve the all-order signed Hankel cone.

Lean: `CompletedArithmeticForms/HyperbolicClock.lean`,
`firstAtomGaussianClockProfile_eq`, `firstAtomGaussianClockProfile_signed_even_jet`,
and `firstAtomGaussianClock_positive_pullback_fails`.

The adjacent-Gamma sequence `s(2k)=aγ_k+bγ_(k+1)`, `s(2k+1)=0`, has every finite
head positive semidefinite exactly when `a,b≥0`, and every finite head strict exactly
when also `a+b>0`. The bounded Gaussian density `(a+by²)exp(−y²/32)` represents
these moments against `exp(−y²/32)dy` up to positive mass; polynomial test closure
forces both coefficient signs. Hence the actual clock is positive at every rank
exactly when `B≥3`. If `B<3`, a finite mixed head fails although all individual
signed even moments remain nonnegative.

Lean: `CompletedArithmeticForms/GaussianClockCone.lean`,
`affineGamma_all_head_posSemidef_iff`, `affineGamma_all_head_posDef_iff`, and
`firstAtomGaussianClock_mixed_failure_of_shape_lt_three`.

For the literal Gaussian factor `g(q,t)=exp(−2q(cosh(2t)−1))`, its signed jets
`H_k(q)=(-1)^k ∂_t^(2k)g(q,0)` satisfy, at every order and scale,
`H_0=1`, `H_(k+1)=8qH_k+(16q²−4q)H'_k−4q²H''_k`.
The actual first-atom moment is exactly `C[BH_k+6qH'_k]`. Joint smoothness
proves every required mixed derivative commutation before evaluation at the origin.

Lean: `CompletedArithmeticForms/ScaleJetTransport.lean`,
`sourceReflectionJet_scalePartial`, `gaussianScaleSignedJet_succ`, and
`firstAtomSignedMoment_eq_scaleJet`.

The exact positive coefficient envelope satisfies
`P_0=1`, `P_(k+1)=8X P_k+16X E(P_k)+4E²(P_k)`, `E=X∂_X`,
and `H_k(q)=(-1)^k P_k(-q)`. Its top coefficient is `γ_k`.
The complete first-atom polynomial is `B P_k+6E(P_k)`, retaining every lower-order term.
At `q≥max(3,k²)`, the literal signed moment is at least
`(6/7)C(B+6k)γ_k q^k`, and its normalized Gaussian error is at most `3k²γ_k/q`.
Thus `√q<ν(x)` for `q≥3`; `max(0, log((3+K²)/π)/2)` suffices for `K<ν(x)`.

Lean: `GaussianScalePolynomial.lean` and `FirstAtomPolynomialHorizon.lean`,
`firstAtomSignedMoment_polynomial_error_le`,
`firstAtomScaledEvenJet_quadratic_error_le`, and `sqrt_scale_lt_firstAtomNegativeOrder`.

For `A=27exp(3π)/399` and `Q_L=max(L²,8L,2L+6)`, the complete native moments obey
`|σ_k−γ_k|≤(3L²+A)γ_k/q` simultaneously for `k≤L`, `q≥Q_L`.
The infinite remainder costs `Aγ_k/q`; its factorial is paid by `8^k k!≤γ_k`.
For a positive comparison matrix `G`, define `V(G)=Σ_i G_ii(G⁻¹)_ii`.
Relative entry errors `|A_ij−G_ij|≤ε|G_ij|` have full-form cost `N ε V(G)`.
The cost is a finite variance-weighted cofactor sum divided by `det G`, and `N≤V(G)`.

Lean: `NativePolynomialHorizon.lean` and `WeightedInverseStability.lean`,
`nativeScaledEvenJet_quadratic_relative_error_le_through` and
`relative_entry_error_le_varianceInverseCost`.

For `G_(N,s)=[γ_(i+j+s)]`, `L=s+2N`, and
`B_(N,s)=N V(G_(N,s))(3L²+A)`, the actual native head has relative form cost `B_(N,s)/q`
on `q≥Q_L`. The condition `q>2B_(N,s)` leaves a strict half-Gamma head.
The exact native successor has the same relative cost at dimension `N+1`.
Thus `q≥Q_(s+2(N+1))+2B_(N+1,s)` gives strict half/three-halves Gamma successor bounds.
The variance cost still carries its rank dependence.

Lean: `CompletedArithmeticForms/NativeVarianceHorizon.lean`,
`nativeBalancedHead_polynomial_relative_error_le` and
`nativeBalancedSuccessor_half_bounds_of_polynomial_horizon`.

The first-atom kernel in Gaussian polynomial coordinates satisfies
`|exp(-4z²-4w²)F_q(z+w)−exp(8zw)|≤50e exp(2e) R⁴ exp(8|z||w|)/q`
for `R≥1`, `q≥max(3,4R²,R⁴)`, and `|z+w|≤R`.
Its exact relative exponent is the quartic remainder
`−2q(cosh u−1−u²/2)`, `u=2i(z+w)/√q`.
The mixed Gaussian exponential remains intact before the absolute bound.

Lean: `CompletedArithmeticForms/GaussianRelativeKernel.lean`,
`gaussianRelativeProfile_error_le` and `firstAtomWickKernel_error_le`.

Separate Cauchy radii give mixed jet error
`i!j! D R⁴ exp(8rs)/(q r^i s^j)` for `r+s≤R`.
For `r_n=√((n+1)/8)` and `w_n=√(n!/(n+1)^n)`,
`n!/r_n^n=w_n√(8^n n!)` and
`w_i w_j exp(8r_i r_j)≤exp(2)(N+1)` for `i,j≤N`, including zero degree.
Also `r_i+r_j≤√(N+2)`.

Lean: `CompletedArithmeticForms/WickCauchyPayment.lean` and
`CompletedArithmeticForms/HermiteRadiusPayment.lean`,
`firstAtomWickError_mixed_jet_le` and `hermiteContourPairWeight_le`.

The literal Hermite matrix is
`T_nk=choose(n,k) (d^(n−k)/dt^(n−k))exp(−4t²)|_0`.
It has determinant one and bijective transpose action at every finite rank.
For every entire source, the complete real mixed kernel head equals
`T_N [Re F^(i+j)(0)] T_N^transpose`; the Gaussian comparison is exactly
`diag(8^i i!)`. The coefficient envelope is `|T_nk|≤n!exp(4)`.

Lean: `CompletedArithmeticForms/HermiteJetCongruence.lean`,
`realWickJetMatrix_eq_congruence` and `hermiteJetCoefficient_abs_le`.

For `C_N=D exp(2)(N+1)(N+2)²`, the first-atom Hermite form has relative error
`N C_N/q` on `q≥4(N+2)²`. Both finite coefficient sums of the complete native
remainder cost at most `N²(N!)² exp(8) A24^(2N)q^N exp(−3q)`, which is at most
`A exp(8)/q` on `q≥16(N+2)²`; here `A=27 exp(3π)/399`.
The complete native signed moment head therefore obeys
`|vᵀ(H_native−G)v|≤P_N/q vᵀGv`,
`P_N=N(C_N+A exp(8))`, on that quadratic domain.
If also `q>2P_N`, `H_native−G/2` is positive definite.
The exact Hermite congruence returns the same relative bound to all original
moment directions, without an inverse-matrix penalty.

The exact Gaussian contraction kernel has dimension-independent row bound four.
Falling-factorial normalization at radius `4√((N+1)/8)` gives the complete native
relative bound `J_N/q`, where `J_N=16D(N+1)²+N A exp(8)`, on `q≥16(N+2)²`.
This estimate retains every original mixed moment direction and every native atom.
Lean: `CompletedArithmeticForms/NativeQuadraticRank.lean`,
`nativeBalancedFullHead_quadratic_rank_error_le`.

Lean: `CompletedArithmeticForms/HermiteSourceBound.lean`,
`CompletedArithmeticForms/HermiteNativeTail.lean`, and
`CompletedArithmeticForms/NativeHermiteHorizon.lean`.
Capstones: `firstAtomHermiteHead_relative_error_le`,
`nativeHermiteHead_firstAtom_error_le`, and
`nativeBalancedFullHead_polynomial_rank_error_le`.

The complete integer-labelled complex theta series is summable exactly where
`cos(2 Im z)>0`. A continuous full logarithmic turn crosses a nonsummable sector.
This classifies the original series representation, without excluding other analytic
continuations. The finite first atom's entire periodic argument cannot identify the
complete series across those sectors.

Lean: `RHTower/ThetaCusp/ThetaCuspComplexClockSector.lean`,
`thetaCuspComplexSourceTerm_summable_iff_cos` and `no_summable_theta_source_logarithmic_turn`.

## Complete theta seam and tail regions

Every finite derivative packet of the complete theta source has zero radical.
Polynomial moments recover its coefficients through the nonzero triangular diagonal
`(-1)^k k! ∫Φ`. The exact seam Gram therefore gives `S_N=[U_(i+j)(0)]>0` at every rank.

For `K_k=thetaCuspNativeJetDecayConstant k`, `D_N=Σ_(k≤2N)K_k`, and
`A_N=N D_N tr(S_N⁻¹)`, the literal tail satisfies
`|U_k(r)−U_k(0)|≤rK_k` and relative head cost at most `rA_N`.
Thus `0≤r≤1/[2(1+A_N)]` leaves the strict half-seam reserve
`H_N(U(r))−S_N/2>0`. Also `r≥2 nativeMixedHorizon(N)` implies `H_N(U(r))>0`
by integration of strict complete native heads. Compensation through the compact
interval between these regions remains necessary for the all-center tail cone.

Lean: `CompletedArithmeticForms/SeamCoercivity.lean`,
`nativeTailHead_zero_posDef`, `nativeTailHead_half_posDef_of_seam_radius`, and
`nativeTailHead_posDef_of_horizon`.

## Complete Weil prefix index

For each fixed `1≤d<c_*`, the actual complete Weil form at overlap `c` and
length `N` has negative-subspace dimension at most `N−M` whenever `M` is
sufficiently large, `M≤N`, and `cM=dN`. Tail restriction is injective on
every negative subspace because the exact principal prefix is the complete
positive source at overlap `d`. The normalized ceiling is `1−d/c`.
The certified Young boundary `c_*` describes the proved prefix range, not
the sign of the actual operator beyond that range.

Lean: `CompletedArithmeticForms/WeilPrefixIndex.lean`,
`eventually_completeWeil_negative_subspace_dim_le_young_tail`.

## Gauge variance and the actual census point

Distinct ordered unequal prime pairs have distinct ratios. Consequently the gauge
mean of the twisted coalescent source vanishes and its gauge variance is exactly
the sum of squared pair weights. At bandwidth `4/3` the normalized variance obeys

`∫|S_T(x)|² dx ≤ (1536/π²)(log T)³ T^(1+η) = o(N(T,2T)²)` for `η<1`.

The actual prime surplus is the value `S_T(0)`. Haar-small exceptional sets do not
bound this prescribed point. The missing arithmetic information must distinguish
the actual additive prime correlations from multiplicative gauge twists.

Lean: `ArithmeticCorrelationGeometry/TheCoalescentSurplusIsPureGaugeCharge.lean`,
`integral_normSq_twistedPrimeCoalSum`,
`twistedPrimeCoalescentSurplus_meanSquare_isLittleO`, and
`twistedPrimeCoalescentSurplus_zero`.

## Source boundaries

- The literal Suzuki transition core is at least `n/288` at apertures `8n`; its
  available Xi curvature is bounded by a source constant times `√n`. Any correction
  producing an eventually lower-semibounded Ward defect must cancel every fixed
  fraction `1−ε` of that core eventually. A merely positive linear correction is
  insufficient. The source problem concerns the signed residual after this cancellation.
  Lean: `RHTower/Suzuki/SuzukiTransitionCoreAsymptoticSaturation.lean`.
- Fixed-modulus averaging controls all residue packets; growing conductors and cross-annulus
  transport require further estimates.
- Fixed-overlap successor fibers grow logarithmically.
- The all-order signed theta hierarchy is RH-equivalent.
- Unrestricted positive extension of the sharp critical prime source is impossible.
- The Euler-deletion current criterion measures growth at the inner cutoff.

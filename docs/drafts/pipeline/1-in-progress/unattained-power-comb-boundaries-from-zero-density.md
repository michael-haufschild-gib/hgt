# Unattained power-comb boundaries from zero density

- **Stage:** 1-in-progress
- **Target:** A82; exact ordinary convergence at a subcritical endpoint.
- **Statement:** For `0<a<1/2`, `PowerCombTailConverges a` iff every zeta zero satisfies `Re ρ<1-a`.
- **Status:** Necessity established. Complete sufficient direction written in Lean; dependency checks pending. Endpoint theorem not yet claimed or counted.

## Mathematical connection

Put `β=1-a`. A sufficiently narrow fixed band `σ≤Reρ≤β`, with `σ>1/2`,
has a summable subunit ordinate moment. This supplies both the complete
zero trace and the rate needed to transport it through harmonic convolution.
No common gap below β is required.

1. For `θ=min((σ-1/2)/2,1/4)`, the density estimate gives
   `Σ |γ|^-p<∞` whenever `p>1-θ/3`. Choose `0<p<1`.
   Exact height cutoffs have `#F_Y≤CY^p` and complete reciprocal tail
   at most `CY^(p-1)`, with all multiplicities.
2. Short-window prime estimates at `H=Y=x^(1/8)` give
   `ψ(x)-x+Re Q₀(x)=O(x^κ)` for some `σ<κ<β`, where
   `Q_b(x)=Σ_(Reρ≥σ) x^(ρ-b)/(ρ-b)`. A finite initial interval pays
   the same envelope on all `x≥1`.
3. Exact weighted Abel summation yields
   `A_a(x)+Re Q_a(x)=O(x^(κ-a))`, where
   `A_a(x)=Σ_(n≤x)(Λ(n)-1)n^-a`. The trace integral is genuinely
   integrable and termwise integration retains `Q_a(1)-Q₀(1)`.
4. The harmonic convolution of this remainder is a right Riemann mesh
   of `t^-2a [A_a(1/t)+Re Q_a(1/t)]`. Its envelope is `t^(-(a+κ))`,
   with `a+κ<1`. The arithmetic staircase and continuous trace are treated
   together; neither needs separate endpoint integrability. The mesh
   tends to its integral, which need not vanish.
5. THIM `norm_cpowPartialSum_sub_le` has a rate linear in the ordinate.
   Dividing by `ρ-a` cancels this growth. Each normalized finite zero mode
   is
   `N^(ρ-β) ζ(ρ+a)/(ρ-a) + 1/((ρ-a)(1-ρ-a))`
   with error at most `14/N`.
6. Set `Y=N`. The finite-mode error is `O(N^(p-1))`; the complete omitted
   convolution costs at most `2(1+log N)` times the reciprocal tail.
   Thus the total error tends to zero as `O((1+log N)N^(p-1))`.
7. Choose `σ=1-a-(1/2-a)/100`. Uniform zeta growth up to `Re s=1`
   makes `Σ |ζ(ρ+a)/(ρ-a)|` finite in this band. When no zero lies on β,
   every oscillating mode vanishes under this summable majorant. The
   constant terms have a reciprocal-ordinate majorant, and their finite
   height sums tend to the complete sum.

The exact finite identity is
`normalized contacts = remainder mesh - Re(full zero convolution)`.
`powerCombTailConverges_iff_normalizedPowerContacts_converges` then transfers
the limit to the literal comb. Necessity combines the established width
bound with `powerCombTailConverges_excludes_boundary_zeros`.

## Verified inputs

`ZeroConfigurationGeometry`:
- `TheRightSubstripsHaveSubunitMoments`;
- `RightSubstripCutoffsHavePowerTails`;
- `ThePrimeErrorHasAPowerSavingRightTrace`;
- `TheRightSubstripTraceIsContinuous`;
- `ThePrimeRightTraceHasAGlobalPowerRemainder`;
- `TheRightSubstripTraceCanBeIntegrated`.

`AbsoluteGeometryOfSpecZ`:
- `PowerTailWeightedPrimeAbel`;
- `PowerTailPrimeErrorKeepsItsRightTrace`;
- `PowerTailRiemannSumsAcrossJumps`;
- `PowerTailRightRemaindersHaveConvergentMeshes`;
- `PowerTailZetaMultiplierBound`;
- `PowerTailZeroTraceIsAbsolutelySummable`;
- `PowerTailZeroPrefixHasAUniformRemainder`.

Required oleans and umbrella imports are present for these inputs.

## Written chain awaiting checks

All in `AbsoluteGeometryOfSpecZ`:
- Finite modes: `PowerTailZeroConvolutionModes`.
- Complete exterior: `PowerTailRightZeroCutoffs`, `PowerTailRightZeroConvolutionTails`.
- Main-part limit: `PowerTailRightTraceCutoffsHaveTheirLimit`, `TheRightZeroConvolutionHasItsLimit`.
- Arithmetic bridge: `PowerContactsSplitIntoRightTraceAndRemainder`.
- Final classifier: `PowerCombConvergenceHasTheExactPointwiseBoundary`, theorem `powerCombTailConverges_iff_forall_zero_re_lt`.

The critical case `a=1/2` is excluded: the right-substrip density deficit
vanishes there, and ordinary critical convergence is already disproved.
No canonical limit is recomputed here; the existing forced-limit theorem
identifies every convergent subcritical comb with `powerTailZeroPairing a`.

# Prefix–collar decoupling, confinement, and critical thresholds

- **ID:** critical-ratio-window-confinement-and-threshold-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Critical thresholds and onset aperture](../../../reports/review-0611/q6work.md).
- **Statement:** `R_c=R_c^{nn}=R_c^{polar}`, `R_c^⊥=R_c^{high}=inf_{A≥0} windowThreshold A`, with exponential onset lower bounds and the infinite-threshold/RH equivalences.

## Definitions

Put `a*=onsetAperture zetaZeroConfig`. Fix `φ=tiltedUnitSpline`, `L=log N`, `c_N≥1`,
and `c_N⁸/L→R>0`.
Put `Q=floor(L^(13/32))`, `X=floor(exp(√L))`, `θ=(1+log L)^(-5)`,
`Y=floor(N^θ)`, and `M=N/linearDefectCutoff(c_N)`.
Write `x=Σ_{m≤Q}b_m v_m+u₀+u₁+w`, with complement bands ending at `X,Y,N`.
Let `U` be the normalized atomic profile of the collar of `w`.

## Formalized statements

1. **Sharp prefix–collar boundary.** The least-prime quasimode above `Q` has Schur ratio
   tending to `4/13`. Keeping conductors through `Y` whole restores arbitrarily small
   prefix–collar payment. Sources: `PrefixCollarSchurObstructionAndFarDecoupling`,
   `FiniteConductorCollarReductionAndPolarDecoupling`.
2. **Gårding and confinement.** Unrestricted atomic Gårding fails; collar Gårding holds.
   Whole-space Gårding retains packet, complement, prefix, seventh-mass, eighth-mass, and
   Lévy reserves, with sole scalar loss `C c_N b₁²/L`. Its terminal window satisfies
   `A≤¼log(R+1)+C`. Sources: `UnrestrictedAtomicGardingFailsAndCollarGardingHolds`,
   `NegativeDirectionsCannotEscapeLogarithmicWindows`, `WholeSpaceCollarGarding`.
3. **Nonpolar cancellation.** For fixed `m≥2`, `(L/c_N²)D₇(r_m)→0`; the growing packet has
   `(c_N⁷/L)Σ_{2≤m≤Q}D₇(r_m)/E_m→0`, uniformly on positive compact critical bands.
   Sources: `NonpolarCollarResidualsVanish`, `AllRatioDeepConductorPairings`,
   `LowConductorCollarPairingsAndWindowLocalizedGarding`.
4. **Primitive threshold.** `R_c^⊥=R_c^{high}=inf_{A≥0} windowThreshold A`, with
   `R_c^⊥≥c₀exp(6a)` for `0≤a≤a*` and the finite-threshold logarithmic consequence.
   Source: `PrimitiveCriticalThresholdEqualsWindowThreshold`.
5. **Whole-space threshold.** `R_c=R_c^{nn}=R_c^{polar}≥c₁exp(c₂a)` for universal
   `c₁,c₂>0` and every finite `0≤a≤a*`, with the finite-threshold logarithmic consequence.
   All five global thresholds are infinite iff `a*=∞` iff RH.
   Source: `WholeSpaceCriticalThresholdEqualsPolarThreshold`.

## Proof mechanisms

For the primitive equality, split each nonpolar residual at `floor(δN)`. The lower dual mass
is `O_m(δ)`; top-window cancellation makes the upper mass vanish. Finite-conductor tail
reduction sums the growing packet. Three-band payment and the primitive coordinate bound
absorb the remaining pole-square loss. Unit-normalized nonpositive collar profiles would
then contradict strong compactness and the critical alias lower bound below the window infimum.

For the whole-space equality, retain the exact pole energy and signed polar collar pairing
with arbitrarily small packet-diagonal loss. Normalize by joint collar–pole mass.
The explicit strong polar row, endpoint tightness, and sampled Lipschitz approximation give
uniform transfer to strong physical limits. Polar payment at a larger ratio leaves a strict
reserve in both limit coordinates, contradicting their preserved unit joint mass.
Compact-band lifting and suprema give the threshold identity.

The explicit polar transfer and charged limit argument are recorded in
[whole-space threshold and onset](cact-whole-space-threshold-onset.md).

All statements have Lean proofs with transitive axiom audits using only
`propext, Classical.choice, Quot.sound`.
